#!/usr/bin/env bash
# OpenJPEG baseline benchmark: opj_decompress wall time (median of N runs) over
# the corpus files with role "benchmark", 1 thread and all cores.
#
# Usage: scripts/bench-openjpeg.sh [--runs N] [--csv] [--threads M]
#   --runs N     timed runs per file and thread count (default 5; plus 1 warm-up)
#   --csv        print CSV instead of the Markdown table
#   --threads M  "many" thread count (default: nproc / sysctl hw.ncpu)
#
# What is measured: whole-process wall time of `opj_decompress -i FILE -o OUT`
# (process start, parse, decode, output write). OpenJPEG has no decode-only
# flag; the output goes to a temp dir (deleted at exit). Raw (.raw) is tried
# first as the cheapest writer, then .tif, then .pgx, per file (the first that
# the warm-up run accepts); the chosen format is part of the output.
# Exits 0 with a message if opj_decompress is missing.
set -euo pipefail

runs=5; csv=0; threads=""
while [ $# -gt 0 ]; do
  case "$1" in
    --runs) runs="${2:?--runs needs a value}"; shift 2 ;;
    --csv) csv=1; shift ;;
    --threads) threads="${2:?--threads needs a value}"; shift 2 ;;
    -h|--help) sed -n '2,15p' "$0"; exit 0 ;;
    *) echo "unknown argument: $1" >&2; exit 2 ;;
  esac
done
case "$runs" in ''|*[!0-9]*|0) echo "--runs must be a positive integer" >&2; exit 2 ;; esac

if ! command -v opj_decompress >/dev/null 2>&1; then
  echo "bench-openjpeg: opj_decompress not found; skipping (install OpenJPEG tools, e.g. libopenjp2-tools)"
  exit 0
fi

root="$(cd "$(dirname "$0")/.." && pwd)"
if [ -z "$threads" ]; then
  threads="$(nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 1)"
fi

work="$(mktemp -d "${TMPDIR:-/tmp}/bench-opj.XXXXXX")"
trap 'rm -rf "$work"' EXIT

export BENCH_ROOT="$root" BENCH_WORK="$work" BENCH_RUNS="$runs" BENCH_CSV="$csv" BENCH_THREADS="$threads"
python3 -I -c '
import json, os, platform, statistics, subprocess, sys, time

root, work = os.environ["BENCH_ROOT"], os.environ["BENCH_WORK"]
runs, csv, many = int(os.environ["BENCH_RUNS"]), os.environ["BENCH_CSV"] == "1", int(os.environ["BENCH_THREADS"])

def out(cmd):
    try:
        return subprocess.run(cmd, capture_output=True, text=True).stdout
    except OSError:
        return ""

def cpu_model():
    try:
        for l in open("/proc/cpuinfo"):
            if l.startswith("model name"):
                return l.split(":", 1)[1].strip()
    except OSError:
        pass
    lc = {l.split(":", 1)[0].strip(): l.split(":", 1)[1].strip() for l in out(["lscpu"]).splitlines() if ":" in l}
    name = " ".join(x for x in (lc.get("Vendor ID"), lc.get("Model name")) if x and x != "-")
    if name:
        return name + " (model name not exposed)" if "Model name" in lc and lc["Model name"] == "-" else name
    return out(["sysctl", "-n", "machdep.cpu.brand_string"]).strip() or "unknown"

ver = (out(["opj_decompress", "-h"]).split("openjp2 library v") + [""])[1].split()[0:1]
ver = ver[0].rstrip(".") if ver else "unknown"
info = [("machine", platform.machine()), ("kernel", platform.system() + " " + platform.release()),
        ("cpu", cpu_model()), ("cores (nproc)", str(os.cpu_count())),
        ("many-thread count", str(many)), ("opj_decompress", "OpenJPEG " + ver),
        ("runs per cell", str(runs) + " (+1 warm-up), median")]

m = json.load(open(os.path.join(root, "corpus", "manifest.json")))
files = [f for f in m["files"] if "benchmark" in f["roles"]]

def run(path, ext, nthreads):
    o = os.path.join(work, "out." + ext)
    t = time.perf_counter()
    r = subprocess.run(["opj_decompress", "-i", path, "-o", o, "-threads", str(nthreads)],
                       capture_output=True, text=True)
    dt = (time.perf_counter() - t) * 1000
    for n in os.listdir(work):
        os.unlink(os.path.join(work, n))
    return r.returncode, dt, (r.stdout + r.stderr).strip().splitlines()[-1:] 

rows = []
for f in files:
    cs = f["codestream"]
    p = os.path.join(root, "corpus", "files", f["path"])
    row = dict(file=os.path.basename(f["path"]), mpx=cs["megapixels"], comps=cs["components"],
               bits=str(cs["bit_depths"][0]) + ("s" if cs["signed"] else "u"),
               wavelet="5-3" if cs["wavelet"].startswith("5-3") else "9-7",
               tiles=cs["tiles"], layers=cs["layers"], fmt="", t1=None, tn=None, err="")
    if not os.path.exists(p):
        row["err"] = "file missing"; rows.append(row); continue
    msgs = []
    for ext in ("raw", "tif", "pgx"):
        rc, _, tail = run(p, ext, 1)   # warm-up (also format probe)
        if rc == 0:
            row["fmt"] = ext; break
        msgs.append(ext + ": " + " ".join(tail))
    if not row["fmt"]:
        row["err"] = "decode failed (" + "; ".join(msgs)[:120] + ")"; rows.append(row); continue
    for key, n in (("t1", 1), ("tn", many)):
        run(p, row["fmt"], n)           # warm-up for this thread count
        ts = []
        for _ in range(runs):
            rc, dt, tail = run(p, row["fmt"], n)
            if rc != 0:
                row["err"] = "run failed"; break
            ts.append(dt)
        if ts:
            row[key] = statistics.median(ts)
    rows.append(row)

def f0(x): return "-" if x is None else "%.0f" % x
def mps(r):
    return "-" if not r["t1"] else "%.1f" % (r["mpx"] / (r["t1"] / 1000))
hdr = ["file", "Mpx", "comps", "bits", "wavelet", "tiles", "layers", "out fmt",
       "1-thread ms", "%d-thread ms" % many, "Mpx/s (1 thread)", "note"]
tab = [[r["file"], "%.2f" % r["mpx"], r["comps"], r["bits"], r["wavelet"], r["tiles"], r["layers"],
        r["fmt"] or "-", f0(r["t1"]), f0(r["tn"]), mps(r), r["err"]] for r in rows]
if csv:
    print("# " + "; ".join(k + "=" + v for k, v in info))
    print(",".join(hdr))
    for t in tab:
        print(",".join(str(c).replace(",", ";") for c in t))
else:
    print("Machine:")
    for k, v in info:
        print("- %s: %s" % (k, v))
    print()
    print("| " + " | ".join(hdr) + " |")
    print("|" + "|".join(["---"] * len(hdr)) + "|")
    for t in tab:
        print("| " + " | ".join(str(c) for c in t) + " |")
'
