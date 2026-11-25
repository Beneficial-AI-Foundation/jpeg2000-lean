#!/usr/bin/env python3
"""Extract the JPXDecode image streams of the PDF corpus (Plan.md section 8.3; docs/corpus.md).

Run from anywhere as:   python3 -I scripts/extract-pdf-jpx.py [options]

The source PDFs are ordinary `corpus/manifest.json` `files` entries with role `pdf-source`
(fetched and SHA-256-verified by `scripts/fetch-corpus.py`).  The extracted streams are the
manifest's `pdf_jpx` list (role `pdf-jpx`; they have no URL, so they are not in `files`):
each names its source PDF (`source_pdf`, a `files` path) and object (`object`: [num, gen]).

  (no options)   for every `pdf_jpx` entry whose file under corpus/files/ is missing or wrong,
                 re-extract it from its source PDF and verify size and SHA-256; then verify
                 all.  Idempotent: a second run touches nothing.
  --check        verify only (no extraction); exit 1 on any missing or wrong file.
  --scan         list every JPXDecode stream of every present source PDF as JSON manifest
                 entries on stdout (used to (re)build the `pdf_jpx` list; nothing written).
  --only TEXT    restrict to entries whose path or source contains TEXT (repeatable).
  --root DIR     files directory (default corpus/files).

Extraction: `qpdf --show-object=N,G --raw-stream-data` (decrypted, still encoded), then every
filter *before* `/JPXDecode` in the `/Filter` chain is undone (only `/FlateDecode` without a
predictor is supported; anything else is reported).  The result is the JPX file (JP2 or raw
codestream) exactly as a PDF reader hands it to its JPEG 2000 decoder.  Facts relevant to
rendering are read from the image dictionary (`qpdf --json=2`).

Standard library + `qpdf` only.  Skips cleanly (exit 0, message) when qpdf or the source
PDFs are absent.  PDF bytes are only handed to qpdf and hashed, never executed.
"""
import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import zlib

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
MANIFEST = os.path.join(REPO, "corpus", "manifest.json")
DEFAULT_ROOT = os.path.join(REPO, "corpus", "files")
JPX_DIR = "pdf-jpx"
MAX_STREAM = 256 << 20  # refuse to inflate a stream beyond 256 MiB


def sha256_bytes(b):
    return hashlib.sha256(b).hexdigest()


def safe_join(root, rel):
    parts = rel.split("/")
    if rel.startswith("/") or "\\" in rel or any(p in ("", ".", "..") for p in parts):
        raise ValueError("unsafe path in manifest: %r" % rel)
    return os.path.join(root, *parts)


def run_qpdf(args):
    r = subprocess.run(["qpdf"] + args, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                       timeout=300)
    # qpdf exit 3 = success with warnings
    if r.returncode not in (0, 3):
        raise RuntimeError("qpdf %s: exit %d: %s" % (" ".join(args[:2]), r.returncode,
                                                       r.stderr.decode("utf-8", "replace")[:300]))
    return r.stdout


def pdf_objects(pdf):
    """The `obj:N G R` map of qpdf's JSON v2 (stream data omitted)."""
    out = run_qpdf(["--json=2", "--json-key=qpdf", "--json-stream-data=none", pdf])
    q = json.loads(out)["qpdf"]
    return q[1]


def as_list(v):
    if v is None:
        return []
    return v if isinstance(v, list) else [v]


def resolve(objs, v, depth=0):
    """Resolve indirect references (depth-limited); streams become their dictionary."""
    if depth > 4:
        return v
    if isinstance(v, str) and v.endswith(" R") and ("obj:" + v) in objs:
        o = objs["obj:" + v]
        if "stream" in o:
            d = o["stream"]["dict"]
            return {"stream": {k: resolve(objs, d[k], depth + 1) for k in ("/N", "/Alternate")
                               if k in d}}
        return resolve(objs, o.get("value"), depth + 1)
    if isinstance(v, list):
        return [resolve(objs, x, depth + 1) for x in v]
    if isinstance(v, dict):
        return {k: resolve(objs, x, depth + 1) for k, x in v.items()}
    return v


def jpx_streams(objs):
    """[(num, gen, dict)] of every stream whose filter chain ends in /JPXDecode."""
    res = []
    for key, o in objs.items():
        if not key.startswith("obj:") or "stream" not in o:
            continue
        d = o["stream"]["dict"]
        filters = [resolve(objs, f) for f in as_list(resolve(objs, d.get("/Filter")))]
        if filters and filters[-1] == "/JPXDecode":
            num, gen, _ = key[4:].split()
            res.append((int(num), int(gen), d, filters))
    res.sort()
    return res


def undo_filters(raw, filters, parms):
    """Undo the filters before /JPXDecode; returns bytes or raises ValueError."""
    data = raw
    parms = as_list(parms)
    for i, f in enumerate(filters[:-1]):
        p = parms[i] if i < len(parms) and isinstance(parms[i], dict) else {}
        if f in ("/FlateDecode", "/Fl") and p.get("/Predictor", 1) in (1, None):
            z = zlib.decompressobj()
            data = z.decompress(data, MAX_STREAM)
            if z.unconsumed_tail:
                raise ValueError("inflated stream exceeds %d bytes" % MAX_STREAM)
        else:
            raise ValueError("unsupported filter before /JPXDecode: %s %s" % (f, p))
    return data


def jpx_format(b):
    if b[:12] == b"\x00\x00\x00\x0cjP  \r\n\x87\n":
        return "jp2"
    if b[:4] == b"\xff\x4f\xff\x51":
        return "j2k"
    return "unknown"


def codestream_of(b):
    """The contiguous codestream: the `jp2c` box payload of a JP2 file, or the bytes."""
    if jpx_format(b) != "jp2":
        return b
    p = 0
    while p + 8 <= len(b):
        lbox = int.from_bytes(b[p:p + 4], "big")
        tbox = b[p + 4:p + 8]
        hdr = 8
        if lbox == 1:
            if p + 16 > len(b):
                break
            lbox = int.from_bytes(b[p + 8:p + 16], "big")
            hdr = 16
        elif lbox == 0:
            lbox = len(b) - p
        if lbox < hdr:
            break
        if tbox == b"jp2c":
            return b[p + hdr:p + lbox]
        p += lbox
    return None


def siz_summary(cs):
    """Main-header SIZ and COD facts (T.800 A.5.1, A.6.1), or None."""
    if cs is None or cs[:4] != b"\xff\x4f\xff\x51":
        return None
    try:
        lsiz = int.from_bytes(cs[4:6], "big")
        s = cs[6:4 + lsiz]
        u32 = lambda o: int.from_bytes(s[o:o + 4], "big")
        xs, ys, xo, yo = u32(2), u32(6), u32(10), u32(14)
        xt, yt, xto, yto = u32(18), u32(22), u32(26), u32(30)
        nc = int.from_bytes(s[34:36], "big")
        comps = [s[36 + 3 * i:39 + 3 * i] for i in range(nc)]
        out = {
            "width": xs - xo, "height": ys - yo, "components": nc,
            "bit_depths": [(c[0] & 0x7F) + 1 for c in comps],
            "signed": [bool(c[0] & 0x80) for c in comps],
            "subsampling": ["%dx%d" % (c[1], c[2]) for c in comps],
            "tiles": (-(-(xs - xto) // xt)) * (-(-(ys - yto) // yt)) if xt and yt else 0,
        }
        p = 4 + lsiz
        while p + 4 <= len(cs):
            m = int.from_bytes(cs[p:p + 2], "big")
            ln = int.from_bytes(cs[p + 2:p + 4], "big")
            if m == 0xFF52:
                c = cs[p + 4:p + 2 + ln]
                out["progression"] = ["LRCP", "RLCP", "RPCL", "PCRL", "CPRL"][c[1]] if c[1] < 5 else c[1]
                out["layers"] = int.from_bytes(c[2:4], "big")
                out["mct"] = c[4]
                out["levels"] = c[5]
                out["wavelet"] = "5-3 reversible" if c[9] == 1 else "9-7 irreversible"
                break
            if m in (0xFF90, 0xFF93) or ln < 2:
                break
            p += 2 + ln
        return out
    except (IndexError, ValueError):
        return None


PDF_FACTS = ("/Width", "/Height", "/ColorSpace", "/BitsPerComponent", "/SMaskInData",
             "/Decode", "/ImageMask", "/SMask", "/Matte", "/Intent", "/DecodeParms")


def image_facts(objs, d):
    out = {}
    for k in PDF_FACTS:
        if k in d:
            v = d[k]
            if k == "/SMask":
                out["SMask"] = "present"
                continue
            out[k[1:]] = resolve(objs, v)
    return out


def stem_of(pdf_path):
    s = os.path.basename(pdf_path)
    return s[:-4] if s.lower().endswith(".pdf") else s


def extract_one(pdf, num, gen, filters, parms):
    raw = run_qpdf(["--show-object=%d,%d" % (num, gen), "--raw-stream-data", pdf])
    return undo_filters(raw, filters, parms)


def scan(root, sources):
    entries, seen = [], {}
    for src in sources:
        pdf = safe_join(root, src["path"])
        if not os.path.isfile(pdf):
            print("absent, not scanned: %s" % src["path"], file=sys.stderr)
            continue
        try:
            objs = pdf_objects(pdf)
        except (RuntimeError, ValueError) as e:
            print("cannot read %s: %s" % (src["path"], e), file=sys.stderr)
            continue
        for num, gen, d, filters in jpx_streams(objs):
            try:
                b = extract_one(pdf, num, gen, filters, resolve(objs, d.get("/DecodeParms")))
            except (RuntimeError, ValueError) as e:
                print("skip %s obj %d %d: %s" % (src["path"], num, gen, e), file=sys.stderr)
                continue
            h = sha256_bytes(b)
            ref = {"source_pdf": src["path"], "object": [num, gen]}
            if h in seen:
                seen[h].setdefault("also_in", []).append(ref)
                continue
            e = {
                "path": "%s/%s-%d.jpx" % (JPX_DIR, stem_of(src["path"]), num),
                "sha256": h, "size": len(b), "roles": ["pdf-jpx"],
                "source_pdf": src["path"], "object": [num, gen],
                "filters": filters, "format": jpx_format(b),
                "pdf_image": image_facts(objs, d),
                "codestream": siz_summary(codestream_of(b)),
            }
            seen[h] = e
            entries.append(e)
    return entries


def verify(path, e):
    if not os.path.isfile(path):
        return "missing"
    with open(path, "rb") as f:
        b = f.read()
    if len(b) != e["size"]:
        return "size %d, expected %d" % (len(b), e["size"])
    if sha256_bytes(b) != e["sha256"]:
        return "sha256 mismatch"
    return None


def main(argv):
    ap = argparse.ArgumentParser(description="Extract the PDF corpus's JPX streams.")
    ap.add_argument("--check", action="store_true", help="verify only")
    ap.add_argument("--scan", action="store_true", help="print manifest entries for all JPX streams")
    ap.add_argument("--only", action="append", metavar="TEXT")
    ap.add_argument("--root", metavar="DIR")
    args = ap.parse_args(argv)
    root = os.path.abspath(args.root) if args.root else DEFAULT_ROOT
    with open(MANIFEST, encoding="utf-8") as f:
        manifest = json.load(f)
    sources = [e for e in manifest["files"] if "pdf-source" in e.get("roles", ())]
    jpx = manifest.get("pdf_jpx", [])
    if args.only:
        keep = lambda e: any(t in e["path"] or t in e.get("source_pdf", "") for t in args.only)
        sources = [e for e in sources if keep(e)]
        jpx = [e for e in jpx if keep(e)]

    if not args.check and shutil.which("qpdf") is None:
        print("skip: qpdf not found")
        return 0
    if args.scan:
        json.dump(scan(root, sources), sys.stdout, indent=1)
        print()
        return 0

    by_path = {e["path"]: e for e in sources}
    missing_src = [p for p in {e["source_pdf"] for e in jpx}
                   if not os.path.isfile(safe_join(root, p))]
    if missing_src and not args.check:
        print("skip: %d source PDFs absent (run scripts/fetch-corpus.py): %s"
              % (len(missing_src), ", ".join(sorted(missing_src)[:3])))
        return 0

    failures, extracted, verified, total = [], 0, 0, 0
    if not args.check:
        objs_cache = {}
        for e in jpx:
            dest = safe_join(root, e["path"])
            if verify(dest, e) is None:
                continue
            src = e["source_pdf"]
            if src not in by_path:
                failures.append((e["path"], "source %s not a pdf-source entry" % src))
                continue
            pdf = safe_join(root, src)
            try:
                if src not in objs_cache:
                    objs_cache[src] = pdf_objects(pdf)
                objs = objs_cache[src]
                num, gen = e["object"]
                d = objs["obj:%d %d R" % (num, gen)]["stream"]["dict"]
                b = extract_one(pdf, num, gen, e["filters"], resolve(objs, d.get("/DecodeParms")))
            except (RuntimeError, ValueError, KeyError) as ex:
                failures.append((e["path"], "extraction failed: %s" % ex))
                continue
            if len(b) != e["size"] or sha256_bytes(b) != e["sha256"]:
                failures.append((e["path"], "extracted bytes differ from the manifest"))
                continue
            os.makedirs(os.path.dirname(dest), exist_ok=True)
            tmp = dest + ".part"
            with open(tmp, "wb") as f:
                f.write(b)
            os.replace(tmp, dest)
            extracted += 1
    bad_paths = {p for p, _ in failures}
    for e in jpx:
        if e["path"] in bad_paths:
            continue
        why = verify(safe_join(root, e["path"]), e)
        if why is None:
            verified += 1
            total += e["size"]
        else:
            failures.append((e["path"], why))
    for p, why in failures:
        print("FAIL %s: %s" % (p, why))
    print("%s: %d pdf-jpx files verified (%d bytes) from %d source PDFs; %d extracted; %d failed"
          % ("check" if args.check else "extract", verified, total,
             len({e["source_pdf"] for e in jpx}), extracted, len(failures)))
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
