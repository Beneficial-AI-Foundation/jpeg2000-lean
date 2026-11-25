#!/usr/bin/env bash
# Proof-hygiene guard (Plan.md section 3 rule 1, section 4 S1/S4; task 0.3). The CI gate.
#   scripts/check-hygiene.sh [--root DIR] [--no-axioms]
# --root DIR   scan DIR instead of the repository (for testing the guard itself)
# --no-axioms  skip the `#print axioms` check (it needs the libraries built in the repository)
# Step 1: python3 -I scripts/hygiene.py scan  (forbidden constructs, theorem listing)
# Step 2: lake env lean scripts/axioms.lean | hygiene.py axioms  (only standard axioms)
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo="$(dirname "$here")"
root="$repo"
axioms=1
while [ $# -gt 0 ]; do
  case "$1" in
    --root) root="${2:?--root needs a directory}"; shift 2 ;;
    --no-axioms) axioms=0; shift ;;
    *) echo "usage: $0 [--root DIR] [--no-axioms]" >&2; exit 2 ;;
  esac
done

status=0
python3 -I "$here/hygiene.py" scan --root "$root" || status=1

if [ "$axioms" = 1 ]; then
  if out="$(cd "$root" && lake env lean scripts/axioms.lean 2>&1)"; then
    printf '%s\n' "$out" | python3 -I "$here/hygiene.py" axioms --root "$root" || status=1
  else
    printf '%s\n' "$out" >&2
    echo "scripts/axioms.lean: failed to elaborate" >&2
    status=1
  fi
fi

if [ "$status" = 0 ]; then
  echo "hygiene: all checks passed"
else
  echo "hygiene: FAILED" >&2
fi
exit $status
