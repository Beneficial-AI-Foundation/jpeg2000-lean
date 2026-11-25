#!/usr/bin/env bash
# Decoder benchmark (task 8.1): builds `bench` and prints a Markdown table (median of N runs,
# one thread) of decode / interleaved8 / per-stage times against the OpenJPEG baseline in
# docs/performance.md, preceded by machine info.
#
# Usage: scripts/bench.sh [--runs N] [--files a.j2k,b.jp2]
#   --runs N    timed runs per file (default 5; plus 1 warm-up)
#   --files L   comma-separated base names instead of the manifest role "benchmark"
set -euo pipefail
cd "$(dirname "$0")/.."
echo "- date: $(date -u +%Y-%m-%d)"
echo "- commit: $(git rev-parse --short HEAD 2>/dev/null || echo unknown)$(git diff --quiet 2>/dev/null || echo ' (+uncommitted changes)')"
echo "- machine: $(uname -m), $(uname -sr), nproc $(nproc 2>/dev/null || echo ?), $(grep -m1 'model name' /proc/cpuinfo 2>/dev/null | cut -d: -f2 | sed 's/^ //' || true)"
echo
lake build bench >&2
lake exe bench "$@"
