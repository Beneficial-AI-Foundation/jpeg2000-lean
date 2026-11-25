#!/usr/bin/env python3
"""Per-code-block differential against an instrumented OpenJPEG (task 4.6b; Plan.md section 8).

Run from the repository root, after `lake build segment-dump`:

    python3 -I scripts/diff-segments.py [--only TEXT ...] [--root DIR] [--show N]

For every T.803 conformance stream and conformance JP2 file (manifest roles
`conformance-stream` and `jp2`) this

  * runs the instrumented OpenJPEG decoder (`scripts/build-opj-instrumented.sh` builds it
    into `.lake/opj-instrumented/bin/opj_decompress_dump` when needed) with
    `OPJ_DUMP_FILE=<scratch>/x.dump` on the whole image (output: a `.pgx` in a scratch
    directory, deleted afterwards);
  * runs `.lake/build/bin/segment-dump <file>` (our Tier-2 segments and fast Tier-1
    coefficients in the same text format, docs/differential.md);
  * parses both, matches records by key `(tile, comp, res, band, prec, cblk)` (OpenJPEG emits
    tiles in its decode order, not index order) and compares
      - the `cb` records (Tier-2: geometry, style, Mb, zero bit-planes, passes, segment
        lengths/passes/hashes; milestone M4 "same per-code-block segments"), and
      - the `coef` records (Tier-1 coefficients before ROI descaling: w, h, roi, nz, hash;
        milestone M3 "code-blocks decode identically").

It prints one line per file (`OK` or `DIFF` with the first differing records and field names,
or `FAIL` when a tool fails) and the summaries `N/M files identical (segments)` and
`N/M files identical (coefficients)`.  Exit status: 0 when every file is identical (or when
the check is skipped), 1 otherwise, 2 on bad usage or a missing segment-dump binary.

Skips cleanly (message, exit 0) when the instrumented OpenJPEG cannot be built (no cmake, C
compiler, ...: the build script says "skipping") or the corpus directory is absent.

Exceptions (justified OpenJPEG-vs-T.800 deviations): EXCEPTIONS below; currently none is
needed — on the whole corpus both sides agree exactly.

Python standard library only.  Both tools get the file path as an argument; their output is
only parsed as text.
"""
import argparse
import json
import os
import shutil
import subprocess
import sys
import tempfile
import time

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
MANIFEST = os.path.join(REPO, "corpus", "manifest.json")
DEFAULT_ROOT = os.path.join(REPO, "corpus", "files")
SEGMENT_DUMP = os.path.join(REPO, ".lake", "build", "bin", "segment-dump")
BUILD_SCRIPT = os.path.join(REPO, "scripts", "build-opj-instrumented.sh")
ROLES = ("conformance-stream", "jp2")
TIMEOUT = 600

KEY_FIELDS = ("tile", "comp", "res", "band", "prec", "cblk")
CB_FIELDS = ("x0", "y0", "x1", "y1", "sty", "Mb", "numbps", "zbp", "passes", "segs", "len",
             "corrupt", "seglens", "segpasses", "seghash", "hash")
COEF_FIELDS = ("w", "h", "roi", "nz", "hash")

# Justified deviations: (file substring, record kind "cb"/"coef", field) -> reason.  A
# difference matching an entry is reported as "excused" and does not fail the run.  Empty:
# on every T.803 stream and conformance JP2 file our segments and coefficients agree with
# OpenJPEG 2.5.3 exactly.  (OpenJPEG's plain-mode cap of 109 passes per codeword segment is
# implemented on our side too since task 4.9 (kodak_2layers_lrcp.j2c, a benchmark file, has a
# 172-pass block).  Known difference that could matter here but does not occur in the
# corpus: the packet ORDER deviation for sub-sampling factors that are not powers of two of
# each other (progress.md 4.3) changes the order of packets, not which bytes belong to a
# code-block.)
# Not an exception: OpenJPEG prints `numbps` (Mb - zero bit-planes) as an unsigned 32-bit
# value; with ROI the zero bit-planes can exceed Mb (p0_06: 4294967288 = -8), and
# segment-dump prints the same wrapped value.
EXCEPTIONS = {}


def run(cmd, env=None, cwd=None):
    """(exit status, stdout, stderr) of a command; status None on timeout."""
    try:
        p = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                           timeout=TIMEOUT, check=False, env=env, cwd=cwd)
    except subprocess.TimeoutExpired:
        return None, "", "timeout"
    return (p.returncode, p.stdout.decode("utf-8", "replace"),
            p.stderr.decode("utf-8", "replace"))


def parse_dump(text):
    """{"cb": {key: fields}, "coef": {key: fields}}, plus a list of format problems."""
    recs = {"cb": {}, "coef": {}}
    problems = []
    lines = text.splitlines()
    if lines and lines[0] == "opjdump 1":
        lines = lines[1:]
    elif lines:
        problems.append("missing `opjdump 1` header: %r" % lines[0][:80])
    for n, line in enumerate(lines, 2):
        parts = line.split(" ")
        kind = parts[0]
        if kind in ("data", "vals"):
            continue
        if kind not in recs:
            problems.append("line %d: unknown record %r" % (n, kind))
            continue
        fields = {}
        for p in parts[1:]:
            k, sep, v = p.partition("=")
            if not sep:
                problems.append("line %d: bad field %r" % (n, p))
                continue
            fields[k] = v
        try:
            key = tuple(int(fields[k]) for k in KEY_FIELDS)
        except (KeyError, ValueError):
            problems.append("line %d: bad key" % n)
            continue
        if key in recs[kind]:
            problems.append("line %d: duplicate %s record %s" % (n, kind, key))
        recs[kind][key] = fields
    return recs, problems


def fmt_key(key):
    return " ".join("%s=%d" % kv for kv in zip(KEY_FIELDS, key))


def compare(kind, fields, opj, ours, name):
    """List of (key, description, excused) differences of one record kind."""
    diffs = []
    for key in sorted(set(opj) | set(ours)):
        a, b = opj.get(key), ours.get(key)
        if a is None:
            diffs.append((key, "only in segment-dump", False))
            continue
        if b is None:
            diffs.append((key, "only in OpenJPEG", False))
            continue
        bad = [f for f in fields if a.get(f) != b.get(f)]
        if bad:
            excused = all(any(s in name and k == kind and fld == f
                              for (s, k, fld) in EXCEPTIONS) for f in bad)
            desc = ", ".join("%s: opj=%s ours=%s" % (f, a.get(f), b.get(f)) for f in bad)
            diffs.append((key, desc, excused))
    return diffs


def selected_files(root, only):
    with open(MANIFEST, encoding="utf-8") as f:
        manifest = json.load(f)
    seen = []
    for entry in manifest["files"]:
        if not set(entry.get("roles", ())) & set(ROLES):
            continue
        rel = entry["path"]
        parts = rel.split("/")
        if rel.startswith("/") or any(p in ("", ".", "..") for p in parts):
            raise ValueError("unsafe path in manifest: %r" % rel)
        if only and not any(t in rel for t in only):
            continue
        if rel not in seen:
            seen.append(rel)
    return [(rel, os.path.join(root, *rel.split("/"))) for rel in seen]


def build_opj():
    """Path of the instrumented decoder, or None when its build was skipped."""
    st, out, err = run(["bash", BUILD_SCRIPT])
    if st != 0:
        print("diff-segments: building the instrumented OpenJPEG failed (exit %s):\n%s"
              % (st, (out + err).strip()[-2000:]))
        sys.exit(1)
    lines = out.strip().splitlines()
    if any("skipping" in l for l in lines) or not lines:
        print("diff-segments: %s; skipped" % (lines[-1] if lines else "no output"))
        return None
    path = lines[-1].strip()
    if not os.access(path, os.X_OK):
        print("diff-segments: %s not executable after the build" % path)
        sys.exit(1)
    return path


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--only", action="append", default=[], metavar="TEXT",
                    help="only files whose manifest path contains TEXT (repeatable)")
    ap.add_argument("--root", default=DEFAULT_ROOT, help="corpus directory")
    ap.add_argument("--show", type=int, default=5,
                    help="differing records shown per file and kind")
    args = ap.parse_args()

    if not os.path.isdir(args.root):
        print("diff-segments: corpus directory %s absent; skipped "
              "(run python3 -I scripts/fetch-corpus.py)" % args.root)
        return 0
    if not os.access(SEGMENT_DUMP, os.X_OK):
        print("diff-segments: %s missing; run `lake build segment-dump` first" % SEGMENT_DUMP)
        return 2
    opj = build_opj()
    if opj is None:
        return 0

    files = selected_files(args.root, args.only)
    if not files:
        print("diff-segments: no corpus file selected")
        return 2
    t0 = time.monotonic()
    same_cb = same_coef = 0
    total_blocks = 0
    for rel, path in files:
        name = rel
        if not os.path.isfile(path):
            print("MISSING %s" % name)
            continue
        scratch = tempfile.mkdtemp(prefix="diff-segments-")
        try:
            dump = os.path.join(scratch, "x.dump")
            env = dict(os.environ)
            env["OPJ_DUMP_FILE"] = dump
            env.pop("OPJ_DUMP_DATA_FULL", None)
            env.pop("OPJ_DUMP_COEF_FULL", None)
            os.mkdir(os.path.join(scratch, "out"))
            st_o, _, err_o = run([opj, "-i", path, "-o", os.path.join(scratch, "out", "x.pgx"),
                                  "-quiet"], env=env, cwd=scratch)
            if st_o != 0:
                print("FAIL %s: OpenJPEG exit %s: %s" % (name, st_o, err_o.strip()[:300]))
                continue
            text_o = ""
            if os.path.exists(dump):  # no code-blocks: no file
                with open(dump, encoding="utf-8") as f:
                    text_o = f.read()
        finally:
            shutil.rmtree(scratch, ignore_errors=True)
        st_l, text_l, err_l = run([SEGMENT_DUMP, path])
        if st_l != 0:
            print("FAIL %s: segment-dump exit %s: %s" % (name, st_l, err_l.strip()[:300]))
            continue
        ro, po = parse_dump(text_o)
        rl, pl = parse_dump(text_l)
        if po or pl:
            print("FAIL %s: malformed dump: %s" % (name, "; ".join((po + pl)[:3])))
            continue
        dcb = compare("cb", CB_FIELDS, ro["cb"], rl["cb"], name)
        dco = compare("coef", COEF_FIELDS, ro["coef"], rl["coef"], name)
        hard_cb = [d for d in dcb if not d[2]]
        hard_co = [d for d in dco if not d[2]]
        same_cb += not hard_cb
        same_coef += not hard_co
        n = len(ro["cb"])
        total_blocks += n
        if not hard_cb and not hard_co:
            extra = (" (%d excused differences)" % (len(dcb) + len(dco))) if dcb or dco else ""
            print("OK   %s (%d code-blocks)%s" % (name, n, extra))
        else:
            print("DIFF %s (%d code-blocks; %d segment, %d coefficient records differ)"
                  % (name, n, len(hard_cb), len(hard_co)))
            for kind, ds in (("cb", hard_cb), ("coef", hard_co)):
                for key, desc, _ in ds[:args.show]:
                    print("    %-4s %s: %s" % (kind, fmt_key(key), desc))
    print("%d/%d files identical (segments)" % (same_cb, len(files)))
    print("%d/%d files identical (coefficients)" % (same_coef, len(files)))
    print("%d code-blocks compared in %.1f s" % (total_blocks, time.monotonic() - t0))
    ok = same_cb == len(files) and same_coef == len(files)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
