#!/usr/bin/env bash
# Fuzz harness (task 9.1, Plan.md 8.6): builds `fuzz` and runs a deterministic mutation campaign
# through `JPEG2000.decode` (corpus seeds: T.803 / JP2 / benchmark / PDF-JPX streams).
#
# Usage: scripts/fuzz.sh [--iters N] [--seed S] [--limits tight|default] [--opj] [--jobs J] [...]
#   --iters N        cases per job (default 2000)
#   --seed S         campaign seed (default 20260101; job j uses S+j)
#   --limits L       tight (Limits.strict, default) or default
#   --opj            differential against opj_decompress on accepted inputs
#   --jobs J         J parallel processes with seeds S, S+1, ... (default 1)
# Any other flag is passed to `fuzz` (see Fuzz/Main.lean: --start, --replay, --slow-factor, ...).
# Findings (limit escapes, slow / disagreeing inputs, crash inputs) go to Fuzz/findings/
# (git-ignored). Exit status is non-zero on a limit escape or a crash.
set -uo pipefail
cd "$(dirname "$0")/.."
iters=2000; seed=20260101; jobs=1; pass=()
while [ $# -gt 0 ]; do
  case "$1" in
    --iters) iters="$2"; shift 2 ;;
    --seed) seed="$2"; shift 2 ;;
    --jobs) jobs="$2"; shift 2 ;;
    *) pass+=("$1"); shift ;;
  esac
done
lake build fuzz >&2 || exit 1
mkdir -p Fuzz/findings
rc=0
if [ "$jobs" -le 1 ]; then
  .lake/build/bin/fuzz --iters "$iters" --seed "$seed" "${pass[@]}" || rc=$?
else
  pids=()
  for ((j = 0; j < jobs; j++)); do
    mkdir -p "Fuzz/findings/job$j"
    .lake/build/bin/fuzz --iters "$iters" --seed $((seed + j)) --findings "Fuzz/findings/job$j" \
      "${pass[@]}" > "Fuzz/findings/job$j/summary.txt" 2>&1 &
    pids+=($!)
  done
  for ((j = 0; j < jobs; j++)); do
    st=0; wait "${pids[$j]}" || st=$?
    [ "$st" -gt "$rc" ] && rc=$st
    echo "=== job $j (seed $((seed + j))) exit $st ==="
    sed -n '/== summary ==/,$p' "Fuzz/findings/job$j/summary.txt"
  done
fi
# A process that died left its input in inflight.bin: keep it as a crash finding.
for f in Fuzz/findings/inflight.bin Fuzz/findings/job*/inflight.bin; do
  if [ -e "$f" ]; then
    dst="Fuzz/findings/crash-$(date +%s)-$(basename "$(dirname "$f")").bin"
    mv "$f" "$dst"
    echo "CRASH: input saved to $dst" >&2
    rc=1
  fi
done
exit $rc
