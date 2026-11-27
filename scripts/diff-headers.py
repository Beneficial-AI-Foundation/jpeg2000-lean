#!/usr/bin/env python3
"""Differential header check against OpenJPEG's opj_dump (task 1.7; Plan.md section 8).

Run from the repository root, after `lake build header-dump`:

    python3 -I scripts/diff-headers.py [--only TEXT ...] [--root DIR] [--context N]

For every corpus file with a codestream role (conformance-stream, jp2, benchmark; see
corpus/manifest.json and docs/corpus.md) this runs `opj_dump -i <file>` and
`.lake/build/bin/header-dump <file>`, normalises both outputs, and compares them line by
line.  It prints one line per file (OK, DIFF with the first differing lines, or FAIL when
either tool fails) and a summary `N/M files identical`.  Exit status: 0 when every file is
identical (or when the check is skipped), 1 otherwise, 2 on bad usage or a missing
header-dump binary.

Skips cleanly (message, exit 0) when `opj_dump` is not on PATH or the corpus directory is
absent.  A selected file missing from an existing corpus is a failure.

Normalisation (both sides):
  * surrounding whitespace is stripped and blank lines are dropped;
  * hex numbers `0x...` become decimal (opj_dump prints csty/prg/cblksty with `%#x`);
  * the lines of SKIP_LINES are dropped: opj_dump diagnostics about things our header does
    not model (JP2 colour boxes, unknown markers).  Each pattern is justified below;
  * the fields of MASK_FIELDS are masked to `<masked>`.

Python standard library only; opj_dump and header-dump get the file path as an argument
and their output is only compared as text.
"""
import argparse
import json
import os
import re
import shutil
import subprocess
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
MANIFEST = os.path.join(REPO, "corpus", "manifest.json")
DEFAULT_ROOT = os.path.join(REPO, "corpus", "files")
HEADER_DUMP = os.path.join(REPO, ".lake", "build", "bin", "header-dump")
CODESTREAM_ROLES = ("conformance-stream", "jp2", "benchmark")
TIMEOUT = 120

# opj_dump output lines that header-dump does not reproduce, because they report on things
# outside the merged codestream header.  Matched against the stripped line.
SKIP_LINES = [
    # JP2 colour-box diagnostics (file5, file7: a second `colr` box; issue208: `colr` METH 3;
    # issue559: a `colr` box of bad size).  Our Box parser keeps every `colr` box and the
    # header dump prints no JP2 box information at all.
    re.compile(r"^\[INFO\] A conforming JP2 reader shall ignore all Colour Specification "
               r"boxes after the first"),
    re.compile(r"^\[INFO\] COLR BOX meth value is not a regular value"),
    re.compile(r"^\[WARNING\] Bad COLR header box"),
    # p0_02: OpenJPEG warns on a main-header marker it does not know; the marker itself is
    # still listed in its marker index, which we compare.
    re.compile(r"^\[WARNING\] Unknown marker$"),
]

# Fields whose value is masked on both sides: (regex on the stripped line, replacement).
MASK_FIELDS = [
    # Tile index, `end_header`: OpenJPEG 2.5.3 builds the tile index of `opj_dump -i` from
    # the TLM segments only and never fills in the end of the tile-part header, so it
    # always prints 0; header-dump prints the real SOD data offset.
    (re.compile(r"end_header=\d+"), "end_header=<masked>"),
]

HEX = re.compile(r"\b0x([0-9a-fA-F]+)\b")


def normalise(text):
    """The comparable lines of a dump."""
    out = []
    for line in text.splitlines():
        line = line.strip()
        if not line or any(p.search(line) for p in SKIP_LINES):
            continue
        line = HEX.sub(lambda m: str(int(m.group(1), 16)), line)
        for pat, repl in MASK_FIELDS:
            line = pat.sub(repl, line)
        line = re.sub(r"\s+", " ", line)
        out.append(line)
    return out


def run(cmd):
    """(exit status, stdout, stderr) of a command; status None on timeout."""
    try:
        p = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                           timeout=TIMEOUT, check=False)
    except subprocess.TimeoutExpired:
        return None, "", "timeout"
    return (p.returncode, p.stdout.decode("utf-8", "replace"),
            p.stderr.decode("utf-8", "replace"))


def first_diff(a, b, context):
    """Lines describing the first difference between two line lists."""
    n = min(len(a), len(b))
    i = next((k for k in range(n) if a[k] != b[k]), n)
    lines = ["    first difference at normalised line %d:" % (i + 1)]
    for k in range(i, min(i + context, max(len(a), len(b)))):
        oa = a[k] if k < len(a) else "<end>"
        ob = b[k] if k < len(b) else "<end>"
        if oa != ob:
            lines.append("      opj_dump   : %s" % oa)
            lines.append("      header-dump: %s" % ob)
    return lines


def selected_files(root, only):
    with open(MANIFEST, encoding="utf-8") as f:
        manifest = json.load(f)
    seen = []
    for entry in manifest["files"]:
        if not set(entry.get("roles", ())) & set(CODESTREAM_ROLES):
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


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--only", action="append", default=[], metavar="TEXT",
                    help="only files whose manifest path contains TEXT (repeatable)")
    ap.add_argument("--root", default=DEFAULT_ROOT, help="corpus directory")
    ap.add_argument("--context", type=int, default=4,
                    help="normalised lines shown after the first difference")
    args = ap.parse_args()

    opj = shutil.which("opj_dump")
    if opj is None:
        print("diff-headers: opj_dump not found on PATH; skipped")
        return 0
    if not os.path.isdir(args.root):
        print("diff-headers: corpus directory %s absent; skipped "
              "(run python3 -I scripts/fetch-corpus.py)" % args.root)
        return 0
    if not os.access(HEADER_DUMP, os.X_OK):
        print("diff-headers: %s missing; run `lake build header-dump` first" % HEADER_DUMP)
        return 2

    files = selected_files(args.root, args.only)
    if not files:
        print("diff-headers: no corpus file selected")
        return 2
    same = 0
    for rel, path in files:
        name = rel
        if not os.path.isfile(path):
            print("MISSING %s" % name)
            continue
        st_o, out_o, err_o = run([opj, "-i", path])
        st_h, out_h, err_h = run([HEADER_DUMP, path])
        if st_o != 0:
            print("FAIL %s: opj_dump exit %s: %s" % (name, st_o, err_o.strip()[:200]))
            continue
        if st_h != 0:
            print("FAIL %s: header-dump exit %s: %s" % (name, st_h, err_h.strip()[:300]))
            continue
        a, b = normalise(out_o), normalise(out_h)
        if a == b:
            same += 1
            print("OK   %s (%d lines)" % (name, len(a)))
        else:
            print("DIFF %s" % name)
            for line in first_diff(a, b, args.context):
                print(line)
    print("%d/%d files identical" % (same, len(files)))
    return 0 if same == len(files) else 1


if __name__ == "__main__":
    sys.exit(main())
