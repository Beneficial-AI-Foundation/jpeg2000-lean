# Fuzz findings

Written by `lake exe fuzz` / `scripts/fuzz.sh` (task 9.1). Everything here except this file
is git-ignored. Files are named `<kind>-s<seed>-i<case>.bin` with a `.txt` description:

* `escape-*` — an accepted image breaks `Limits` (or peak memory above the cap): a decoder bug.
* `slow-*`, `slow-*-min` — slower than the threshold; `-min` is the chunk-deleted minimisation.
* `diff-*`, `diff-*-min` — we and `opj_decompress` both accept but the raw planes differ.
* `opj-crash-*` — OpenJPEG crashed or timed out (not our failure).
* `crash-*` — the fuzzer process died while decoding that input (impossible by construction).

Replay: `lake exe fuzz --replay <file> [--opj] [--limits default]`; or regenerate the case with
`lake exe fuzz --seed S --start I --iters 1`.
