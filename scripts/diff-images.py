#!/usr/bin/env python3
"""Decoded-image differential for M6 (Plan.md sections 1, 7–9; T.800 Annex I).

Run from the repository root (or anywhere) as:   python3 -I scripts/diff-images.py [options]

For every `pdf-jpx` entry of corpus/manifest.json (the JPX streams extracted from PDFs by
scripts/extract-pdf-jpx.py) -- and with `--jp2` also the T.803 JP2 files (role `jp2`) --
two comparisons are made, each per component, sample by sample:

  codestream  the contiguous codestream (the `jp2c` payload of a JP2 file) decoded by
              `opj_decompress -i x.j2k -o x.pgx` against our `image-dump` raw components
              (`decodeCodestream`).  OpenJPEG converts a space-less 3-component stream whose
              component 1 is horizontally sub-sampled from sYCC to RGB even here; then our
              `JPEG2000.decode` channels (which apply the same heuristic) are compared.
  jp2         JP2 files only: `opj_decompress -i x.jp2` (palette, cmap/cdef, sYCC) against
              our `JPEG2000.decode` channels. For enumerated CMYK, convert our four consumer
              channels to RGB and compare directly to OpenJPEG's RGB PGX. The reference
              CMYK TIFF and PGX select the native converter's rounding. The conformance
              suite separately checks the nine JP2 TIFF references, applying ICC via lcms2.

The SHA-256 in each manifest entry is verified before decoding. A `recorded_plane` entry
checks both our raw and consumer output against a single constant plane at tolerance zero.
Only our decoder reads that fixture.

Tolerances (peak = max |ours - OpenJPEG| per component; MSE reported):
  reversible 5/3, no colour conversion ......... 0 (bit-exact)
  irreversible 9/7 (and/or ICT) ................ 1 (fixed-point vs OpenJPEG's float 9/7:
                                                  measured +-1 on every T.803 stream, task 5.5)
  sYCC -> RGB conversion ....................... +1 (exact truncation of OpenJPEG's
                                                  double formula; +-1 on boundary pixels, 6.1)
A component that is reversible only in some tiles counts as irreversible.

A level listed in the entry's `known_deviations` (manifest; each with its explanation) that
is outside tolerance is reported as `known` and not counted as a failure; a recorded
deviation that no longer occurs is reported as a `note`.

An entry may carry `"reduce": k` (task 6.5): both decoders then discard the k finest
resolution levels (`opj_decompress -r k`, `image-dump <file> <prefix> k`), and the size
check below uses the reduced area (area / 4^k).  `issue19517-8` (212 Mpx) is compared at
reduce 2 this way.

Files above --max-mpx (default 40, at the reduced resolution) and missing corpus files
are skipped. Comparisons require image-dump (`lake build image-dump`), and live references
also require opj_decompress. Exit status 1 on hash mismatch, decoding error or comparison
outside tolerance at a level not recorded as a known deviation.
"""
import argparse
import hashlib
import json
import os
from runpy import run_path
import shutil
import struct
import subprocess
import sys
import tempfile

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
MANIFEST = os.path.join(REPO, "corpus", "manifest.json")
DEFAULT_ROOT = os.path.join(REPO, "corpus", "files")
IMAGE_DUMP = os.path.join(REPO, ".lake", "build", "bin", "image-dump")
TIMEOUT = 1200


def safe_join(root, rel):
    parts = rel.split("/")
    if rel.startswith("/") or "\\" in rel or any(p in ("", ".", "..") for p in parts):
        raise ValueError("unsafe path in manifest: %r" % rel)
    return os.path.join(root, *parts)


def read_pgx(path):
    """(width, height, depth, signed, samples) of a PGX file (OpenJPEG or ours)."""
    with open(path, "rb") as f:
        b = f.read()
    nl = b.index(b"\n")
    toks = b[:nl].decode("ascii").replace("\r", " ").split()
    if toks[0] != "PG" or toks[1] not in ("ML", "LM"):
        raise ValueError("bad PGX header in %s" % path)
    rest = toks[2:]
    if rest[0] in ("+", "-"):
        sign, rest = rest[0], rest[1:]
        depth = int(rest[0])
    elif rest[0][0] in "+-":
        sign, depth = rest[0][0], int(rest[0][1:])
    else:
        sign, depth = "+", int(rest[0])
    w, h = int(rest[1]), int(rest[2])
    bps = 1 if depth <= 8 else 2 if depth <= 16 else 4 if depth <= 32 else 8
    data = b[nl + 1:]
    if len(data) != w * h * bps:
        raise ValueError("PGX size mismatch in %s" % path)
    order = "big" if toks[1] == "ML" else "little"
    signed = sign == "-"
    if bps == 1:
        s = list(data)
        if signed:
            s = [v - 256 if v >= 128 else v for v in s]
    else:
        s = [int.from_bytes(data[i:i + bps], order, signed=signed)
             for i in range(0, len(data), bps)]
    return w, h, depth, signed, s


def compare(a, b):
    """(peak, mse) of two PGX tuples, or a mismatch string."""
    if a[:2] != b[:2]:
        return "size %dx%d vs %dx%d" % (a[0], a[1], b[0], b[1])
    if a[2:4] != b[2:4]:
        return "depth/sign %s vs %s" % (a[2:4], b[2:4])
    sa, sb = a[4], b[4]
    peak, sq = 0, 0
    for x, y in zip(sa, sb):
        d = x - y
        if d:
            d = -d if d < 0 else d
            sq += d * d
            if d > peak:
                peak = d
    return peak, (sq / len(sa) if sa else 0.0)


def codestream_of(b):
    if b[:12] != b"\x00\x00\x00\x0cjP  \r\n\x87\n":
        return b
    p = 0
    while p + 8 <= len(b):
        lbox = int.from_bytes(b[p:p + 4], "big")
        hdr = 8
        if lbox == 1:
            lbox = int.from_bytes(b[p + 8:p + 16], "big")
            hdr = 16
        elif lbox == 0:
            lbox = len(b) - p
        if lbox < hdr:
            return None
        if b[p + 4:p + 8] == b"jp2c":
            return b[p + hdr:p + lbox]
        p += lbox
    return None


def run(cmd):
    try:
        r = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=TIMEOUT)
    except subprocess.TimeoutExpired:
        return None, "timeout"
    return r.returncode, r.stdout.decode("utf-8", "replace") + r.stderr.decode("utf-8", "replace")


def opj_planes(src, tmp, tag, reduce=0):
    """Decode src with opj_decompress (`-r reduce`) into PGX; list of PGX tuples or an error
    string."""
    out = os.path.join(tmp, tag + ".pgx")
    rc, log = run(["opj_decompress", "-i", src, "-o", out] + (["-r", str(reduce)] if reduce else []))
    if rc != 0:
        return "opj_decompress failed (%s): %s" % (rc, log.strip().splitlines()[-1:] if log else "")
    planes, k = [], 0
    while os.path.exists(os.path.join(tmp, "%s_%d.pgx" % (tag, k))):
        planes.append(read_pgx(os.path.join(tmp, "%s_%d.pgx" % (tag, k))))
        k += 1
    if not planes and os.path.exists(out):
        planes.append(read_pgx(out))
    return planes or "opj_decompress wrote no PGX"


def ours(src, tmp, tag, reduce=0):
    """Run image-dump (at `reduce`); returns (info dict, raw planes, img planes) or an error
    string."""
    pre = os.path.join(tmp, tag)
    rc, log = run([IMAGE_DUMP, src, pre] + ([str(reduce)] if reduce else []))
    info = {"raw": [], "img": [], "error": None}
    for line in (log or "").splitlines():
        t = line.split()
        if not t:
            continue
        if t[0] in ("space", "icc", "declared", "sycc_converted"):
            info[t[0]] = t[1]
        elif t[0] == "raw":
            info["raw"].append({"rev": t[6] == "true"})
        elif t[0] == "img":
            info["img"].append({"role": t[2]})
        elif t[0] == "error":
            info["error"] = line
    if info["error"] or rc != 0:
        return info["error"] or "image-dump failed (%s): %s" % (rc, log.strip()[-200:])
    raw = [read_pgx("%s_raw_%d.pgx" % (pre, k)) for k in range(len(info["raw"]))]
    img = [read_pgx("%s_img_%d.pgx" % (pre, k)) for k in range(len(info["img"]))]
    return info, raw, img


def judge(name, level, theirs, mine, tols, lines):
    """Compare plane lists; appends report lines; True if within tolerance."""
    if isinstance(theirs, str) or isinstance(mine, str):
        lines.append("FAIL %s [%s]: %s" % (name, level, theirs if isinstance(theirs, str) else mine))
        return False
    if len(theirs) != len(mine):
        lines.append("FAIL %s [%s]: %d reference components, %d ours"
                     % (name, level, len(theirs), len(mine)))
        return False
    ok = True
    parts = []
    for k, (a, b) in enumerate(zip(theirs, mine)):
        r = compare(b, a)
        if isinstance(r, str):
            parts.append("c%d %s" % (k, r))
            ok = False
            continue
        peak, mse = r
        good = peak <= tols[k]
        ok &= good
        parts.append("c%d peak %d mse %.4f (tol %d)%s" % (k, peak, mse, tols[k], "" if good else " !"))
    lines.append("%s %s [%s]: %s" % ("ok  " if ok else "FAIL", name, level, "; ".join(parts)))
    return ok


def recorded_comparison(name, reference, raw, img, lines):
    """Check the single recorded plane against both outputs of the original bare codestream."""
    w, h = reference["width"], reference["height"]
    plane = (w, h, reference["depth"], reference["signed"], [reference["constant"]] * (w * h))
    failed = set()
    for level, planes in (("codestream", raw), ("image", img)):
        if not judge(name, level + " recorded", [plane], planes, [0], lines):
            failed.add(level)
    return failed


def cmyk_to_rgb(planes, fused):
    """OpenJPEG color_cmyk_to_rgb for unsigned 8-bit CMYK, with or without contraction."""
    def f32(x):
        return struct.unpack("=f", struct.pack("=f", x))[0]

    scale = f32(1 / 255)
    # v * scale is exact in binary64 for these 8-bit samples. A fused 1 - v * scale
    # rounds once, while the non-fused C expression first rounds the product to binary32.
    inv = [f32(1 - (v * scale if fused else f32(v * scale))) for v in range(256)]
    ink = [f32(255 * v) for v in inv]
    w, h = planes[0][:2]
    black = planes[3][4]
    return [(w, h, 8, False, bytes(int(f32(ink[v] * inv[k])) for v, k in zip(p[4], black)))
            for p in planes[:3]]


def check_cmyk(name, src, tmp, red, info, img, tol, lines):
    """Compare the JP2 consumer and OpenJPEG TIFF channels before and after RGB rendering."""
    out = os.path.join(tmp, "opj_cmyk.tif")
    rc, log = run(["opj_decompress", "-i", src, "-o", out] + (["-r", str(red)] if red else []))
    if rc != 0:
        lines.append("FAIL %s [jp2 CMYK]: opj_decompress failed (%s) %s" % (name, rc, log[-200:]))
        return False
    read_tiff = run_path(os.path.join(REPO, "scripts", "icc-apply.py"))["read_tiff"]
    try:
        w, h, nc, bits, data = read_tiff(out)
    except (OSError, ValueError, KeyError, struct.error) as exc:
        lines.append("FAIL %s [jp2 CMYK]: invalid OpenJPEG TIFF: %s" % (name, exc))
        return False
    if (nc, bits) != (4, 8):
        lines.append("FAIL %s [jp2 CMYK]: expected four 8-bit TIFF samples per pixel" % name)
        return False
    if (info.get("space") != "enumerated-12" or info.get("declared") != "enumerated-12"
            or [c["role"] for c in info["img"]] != ["colour"] * 4):
        lines.append("FAIL %s [jp2 CMYK]: expected four enumerated CMYK colour channels" % name)
        return False
    theirs = [(w, h, bits, False, data[k::nc]) for k in range(nc)]
    if not judge(name, "jp2 CMYK", theirs, img, [tol] * nc, lines):
        return False
    native_rgb = opj_planes(src, tmp, "opj_rgb", red)
    if isinstance(native_rgb, str):
        lines.append("FAIL %s [jp2 RGB PGX]: %s" % (name, native_rgb))
        return False
    # Select the compiler's rounding using only the two OpenJPEG decodes. The TIFF
    # rendering must match PGX exactly before that renderer is applied to our image.
    mismatches = []
    for fused in (True, False):
        mode = "fused" if fused else "non-fused"
        level = "jp2 OpenJPEG TIFF->RGB vs PGX " + mode
        result = []
        if judge(name, level, native_rgb, cmyk_to_rgb(theirs, fused), [0] * 3, result):
            lines.extend(result)
            return judge(name, "jp2 CMYK->RGB vs PGX", native_rgb, cmyk_to_rgb(img, fused),
                         [tol] * 3, lines)
        mismatches.extend(result)
    lines.extend(mismatches)
    return False


def check_file(e, root, tmp, lines):
    """Return the failed comparisons for this manifest entry."""
    path = safe_join(root, e["path"])
    name = e["path"]
    red = int(e.get("reduce", 0))
    rtag = " r%d" % red if red else ""
    failed = set()
    with open(path, "rb") as f:
        data = f.read()
    if hashlib.sha256(data).hexdigest() != e["sha256"]:
        lines.append("FAIL %s: SHA-256 differs from manifest" % name)
        return {"sha256"}
    cs = codestream_of(data)
    if cs is None:
        lines.append("FAIL %s: no codestream box" % name)
        return {"codestream"}
    csf = os.path.join(tmp, "cs.j2k")
    with open(csf, "wb") as f:
        f.write(cs)
    # codestream level
    r = ours(csf, tmp, "ours_cs", red)
    if isinstance(r, str):
        lines.append("FAIL %s [codestream%s]: %s" % (name, rtag, r))
        return {"codestream"}
    info, raw, img = r
    if "recorded_plane" in e:
        return recorded_comparison(name, e["recorded_plane"], raw, img, lines)
    theirs = opj_planes(csf, tmp, "opj_cs", red)
    rev = [c["rev"] for c in info["raw"]]
    sycc = info.get("sycc_converted") == "true"
    if sycc:
        mine = img
        tols = [(0 if all(rev[:3]) else 1) + 1 for _ in img]
    else:
        mine = raw
        tols = [0 if rv else 1 for rv in rev]
    if not judge(name, "codestream" + rtag + (" sYCC->RGB" if sycc else ""), theirs, mine, tols, lines):
        failed.add("codestream")
    if data[:12] != b"\x00\x00\x00\x0cjP  \r\n\x87\n":
        return failed
    # jp2 level
    jf = os.path.join(tmp, "f.jp2")
    with open(jf, "wb") as f:
        f.write(data)
    r = ours(jf, tmp, "ours_jp2", red)
    if isinstance(r, str):
        lines.append("FAIL %s [jp2%s]: %s" % (name, rtag, r))
        failed.add("jp2")
        return failed
    info, raw, img = r
    rev = [c["rev"] for c in info["raw"]]
    tol = 0 if all(rev) else 1
    if e.get("jp2_boxes", {}).get("colr") == "enumerated:12":
        if not check_cmyk(name, jf, tmp, red, info, img, tol, lines):
            failed.add("jp2")
        return failed
    space = info.get("declared", "?")
    if space == "icc" and "jp2" in e["roles"]:
        lines.append("skip %s [jp2 ICC]: covered by the colour-managed TIFF reference in lake exe tests" % name)
        return failed
    theirs = opj_planes(jf, tmp, "opj_jp2", red)
    sycc = info.get("sycc_converted") == "true"
    tols = [tol + (1 if sycc else 0) for _ in img]
    if not judge(name, "jp2 %s%s" % (space, rtag), theirs, img, tols, lines):
        failed.add("jp2")
    return failed


def main(argv):
    ap = argparse.ArgumentParser(description="JPEG2000.decode vs opj_decompress, per component.")
    ap.add_argument("--jp2", action="store_true", help="also the T.803 JP2 files (role jp2)")
    ap.add_argument("--only", action="append", metavar="TEXT", help="paths containing TEXT")
    ap.add_argument("--max-mpx", type=float, default=40.0, help="skip larger images (default 40)")
    ap.add_argument("--root", metavar="DIR")
    ap.add_argument("--verbose", action="store_true", help="print every comparison")
    args = ap.parse_args(argv)
    root = os.path.abspath(args.root) if args.root else DEFAULT_ROOT

    if not os.path.isfile(IMAGE_DUMP):
        print("skip: %s missing (run `lake build image-dump`)" % os.path.relpath(IMAGE_DUMP, REPO))
        return 0
    with open(MANIFEST, encoding="utf-8") as f:
        manifest = json.load(f)
    entries = list(manifest.get("pdf_jpx", []))
    if args.jp2:
        entries += [e for e in manifest["files"] if "jp2" in e.get("roles", ())]
    if args.only:
        entries = [e for e in entries if any(t in e["path"] for t in args.only)]
    if shutil.which("opj_decompress") is None:
        recorded = [e for e in entries if "recorded_plane" in e]
        if len(recorded) < len(entries):
            print("skip: opj_decompress not found (%d live references)" % (len(entries) - len(recorded)))
        if not recorded:
            return 0
        entries = recorded
    present = [e for e in entries if os.path.isfile(safe_join(root, e["path"]))]
    if not present:
        print("skip: no corpus files present (run scripts/fetch-corpus.py and "
              "scripts/extract-pdf-jpx.py)")
        return 0

    n_ok, n_fail, n_known, skipped = 0, 0, 0, []
    for e in present:
        cs = e.get("codestream") or {}
        mpx = cs.get("width", 0) * cs.get("height", 0) / 1e6 / 4 ** int(e.get("reduce", 0))
        if mpx > args.max_mpx:
            skipped.append("%s (%.1f Mpx > --max-mpx %g)" % (e["path"], mpx, args.max_mpx))
            continue
        lines = []
        with tempfile.TemporaryDirectory(prefix="diff-images-") as tmp:
            failed = check_file(e, root, tmp, lines)
        known = e.get("known_deviations", {})
        for l in lines:
            if args.verbose or not l.startswith("ok  "):
                print(l, flush=True)
        for level in sorted(failed & set(known)):
            print("known %s [%s]: %s" % (e["path"], level, known[level]))
        for level in sorted(set(known) - failed):
            print("note %s [%s]: recorded known deviation did not occur" % (e["path"], level))
        if failed - set(known):
            n_fail += 1
        elif failed:
            n_known += 1
        else:
            n_ok += 1
            if not args.verbose:
                print("ok   %s" % e["path"], flush=True)
    for s in skipped:
        print("skip %s" % s)
    missing = len(entries) - len(present)
    print("diff-images: %d/%d files within tolerance; %d known deviations (recorded in the "
          "manifest); %d failed; %d skipped (size); %d absent"
          % (n_ok, n_ok + n_known + n_fail, n_known, n_fail, len(skipped), missing))
    return 1 if n_fail else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
