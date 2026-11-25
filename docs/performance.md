# Performance baseline and targets

## Purpose

Plan section 6 sets the speed target for the decoder, measured on the benchmark set (the 15
corpus files with role `benchmark`, see `docs/corpus.md`):

* single-threaded decode within **2x** of OpenJPEG's single-threaded time;
* faster than OpenJPEG with parallel tasks on a multi-core machine.

This file turns that into numbers: the OpenJPEG 2.5.3 baseline below, and per file a
single-thread budget of 2x the baseline (column "Target 1-thread ms") plus the OpenJPEG
multi-thread time to beat. Milestone M8 is judged against these numbers.

## Machine

* aarch64, Linux 7.0.14 sandbox, 8 cores (nproc = 8), CPU vendor Apple, model name not
  exposed by the VM.
* `opj_decompress` from OpenJPEG 2.5.3 (Debian package `libopenjp2-tools`), threads set
  with `-threads N`.
* The other cores were not idle: another agent ran light Lean single-file checks in the same
  checkout during the measurement, so the timings carry some noise (the median of 5 runs
  damps it, it does not remove it). The multi-thread column is the most exposed.

## Command

```
scripts/bench-openjpeg.sh            # Markdown table, median of 5 runs (+1 warm-up) per cell
scripts/bench-openjpeg.sh --runs 9   # more runs
scripts/bench-openjpeg.sh --csv      # CSV
```

For each file: one warm-up run, then N runs with 1 thread and with `nproc` threads; the
reported value is the median wall time of `opj_decompress -i FILE -o OUT -threads T`
(process start, parse, decode and output write, measured with `time.perf_counter`). The script
exits 0 with a message if `opj_decompress` is not installed. Run it on a quiet machine to
refresh the numbers; the file list comes from `corpus/manifest.json`.

## Baseline (OpenJPEG 2.5.3, wall time in ms)

"bits" is the bit depth with `u`nsigned or `s`igned. "out fmt" is the output format that
`opj_decompress` accepted (`.raw` is tried first, it is the cheapest writer; `.tif`, then
`.pgx` are the fallbacks; `p1_03.j2k` has subsampled components, which `.raw` rejects, so it
is written as `.pgx`, one file per component).

| file | Mpx | comps | bits | wavelet | tiles | layers | out fmt | 1-thread ms | 8-thread ms | Mpx/s (1 thread) | note |
|---|---|---|---|---|---|---|---|---|---|---|---|
| p0_07.j2k | 4.19 | 3 | 12s | 5-3 | 256 | 8 | raw | 824 | 428 | 5.1 |  |
| p0_08.j2k | 1.58 | 3 | 12s | 5-3 | 1 | 30 | raw | 402 | 87 | 3.9 |  |
| p1_03.j2k | 1.05 | 4 | 8u | 9-7 | 1 | 10 | pgx | 120 | 24 | 8.8 |  |
| zoo1.jp2 | 10.16 | 3 | 8u | 9-7 | 1 | 6 | raw | 648 | 274 | 15.7 |  |
| Bretagne2.j2k | 5.04 | 3 | 8u | 5-3 | 25 | 3 | raw | 720 | 223 | 7.0 |  |
| kodak_2layers_lrcp.j2c | 3.19 | 3 | 12u | 9-7 | 1 | 2 | raw | 349 | 124 | 9.1 |  |
| 123.j2c | 3.24 | 1 | 16u | 5-3 | 1 | 1 | raw | 267 | 58 | 12.1 |  |
| movie_00000.j2k | 2.07 | 3 | 8u | 5-3 | 1 | 1 | raw | 73 | 52 | 28.4 |  |
| _00042.j2k | 2.07 | 3 | 12u | 9-7 | 1 | 1 | raw | 77 | 60 | 27.0 |  |
| test_lossless.j2k | 1.05 | 1 | 12u | 5-3 | 1 | 1 | raw | 87 | 22 | 12.0 |  |
| pacs.ge.j2k | 0.26 | 1 | 16s | 5-3 | 1 | 16 | raw | 21 | 7 | 12.4 |  |
| buxI.j2k | 0.26 | 1 | 16u | 9-7 | 1 | 2 | raw | 17 | 6 | 15.2 |  |
| issue208.jp2 | 1.05 | 4 | 8u | 9-7 | 20 | 1 | raw | 47 | 65 | 22.1 |  |
| issue559-eci-090-CIELab.jp2 | 0.09 | 3 | 16u | 9-7 | 8 | 6 | raw | 22 | 18 | 4.1 |  |
| cthead1.j2k | 0.07 | 1 | 8u | 5-3 | 1 | 1 | raw | 4 | 3 | 17.5 |  |

## Derived targets

Single-thread budget = 2 x the single-thread median; the parallel target is to beat the
8-thread median of OpenJPEG on the same machine. The last column shows how much OpenJPEG
itself gains from 8 threads.

| file | OpenJPEG 1-thread ms | Target 1-thread ms (2x) | OpenJPEG 8-thread ms (parallel target: below) | OpenJPEG speed-up |
|---|---|---|---|---|
| p0_07.j2k | 824 | 1648 | 428 | 1.9x |
| p0_08.j2k | 402 | 804 | 87 | 4.6x |
| p1_03.j2k | 120 | 240 | 24 | 5.0x |
| zoo1.jp2 | 648 | 1296 | 274 | 2.4x |
| Bretagne2.j2k | 720 | 1440 | 223 | 3.2x |
| kodak_2layers_lrcp.j2c | 349 | 698 | 124 | 2.8x |
| 123.j2c | 267 | 534 | 58 | 4.6x |
| movie_00000.j2k | 73 | 146 | 52 | 1.4x |
| _00042.j2k | 77 | 154 | 60 | 1.3x |
| test_lossless.j2k | 87 | 174 | 22 | 4.0x |
| pacs.ge.j2k | 21 | 42 | 7 | 3.0x |
| buxI.j2k | 17 | 34 | 6 | 2.8x |
| issue208.jp2 | 47 | 94 | 65 | 0.7x |
| issue559-eci-090-CIELab.jp2 | 22 | 44 | 18 | 1.2x |
| cthead1.j2k | 4 | 8 | 3 | 1.3x |

## Caveats

* The wall time includes writing the output file (a temp directory, deleted afterwards) and
  process start-up. OpenJPEG has no decode-only flag. For small files (under about 1 Mpx,
  times of a few ms to 25 ms) start-up and writing are a large part of the time and the
  numbers are coarse; judge the targets mainly on the larger files.
* Our decoder will be measured the same way (whole process, a file output) so the ratio is
  fair, but any change of method must be applied to both sides and noted in History.
* No file is 20 Mpx or larger (largest: `zoo1.jp2`, 10.2 Mpx); behaviour on very large
  images is not covered.
* Multi-thread speed-up is small for files with a single small tile and few code-blocks
  (`movie_00000`, `_00042`, `cthead1`, `issue559-eci-090-CIELab`), and for `issue208.jp2` the
  8-thread run (65 ms) is slower than the 1-thread run (47 ms), probably thread
  start-up cost on a small image. A parallel target of "faster than OpenJPEG" is therefore
  measured per file against the better of the two OpenJPEG columns.
* Sandbox noise as noted above; the numbers are a baseline for orders of magnitude and
  ratios, not a precise benchmark. Re-run the script to reproduce.
* Every benchmark file decoded without error; no flags (reduced resolution, region) were
  used.

## History

(Empty. Later waves append dated entries: our decoder's numbers against these targets,
changes of method, re-baselines.)

### 2026-11-25: first decoder numbers (task 8.1, `scripts/bench.sh`, based on `e422128`)

Command: `scripts/bench.sh` (= `lake build bench && lake exe bench`, source `Bench/Decode.lean`).
Same aarch64 sandbox as above (8 cores, other agents building in parallel, so some noise).
Method: one warm-up, then 5 runs per file, median wall time (`IO.monoNanosNow`), one thread,
no output write, no process start-up. "decodeCodestream" = planes only; "decode" =
`JPEG2000.decode`; "interleaved8" = `Image.interleaved8` of that image; "total" = decode +
interleaved8; Mpx/s = Mpx / total. Stage columns come from a measurement-only replica of the
pipeline (`stagedDecode`: same stage functions, a clock around each call; Tier-2 includes the
header parse; "glue" = layout, allocation, tile placement). "sum/cs" is the stage sum over the
real `decodeCodestream` time (0.99-1.01 everywhere, so the split is faithful). The last column
divides our total by the OpenJPEG 1-thread time above (which also includes start-up and the
output write, so it slightly favours us); the 2x budget needs <= 2.00.

| file | Mpx | decodeCodestream ms | decode ms | interleaved8 ms | total ms | Mpx/s | Tier-2 ms | Tier-1 ms | dequant ms | DWT ms | MCT+DC ms | glue ms | sum/cs | OpenJPEG 1-thread ms | total / OpenJPEG |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| p0_07.j2k | 4.19 | 3905.6 | 3905.6 | 87.4 | 3992.9 | 1.0 | 56.9 | 2663.9 | 311.5 | 675.3 | 53.0 | 158.1 | 1.00 | 824 | 4.85 |
| p0_08.j2k | 1.58 | 1752.2 | 1731.7 | 32.4 | 1764.1 | 0.8 | 26.8 | 1280.6 | 120.2 | 254.6 | 21.6 | 59.1 | 1.01 | 402 | 4.39 |
| p1_03.j2k | 1.05 | 635.3 | 664.0 | 26.2 | 690.2 | 1.5 | 12.1 | 341.6 | 64.6 | 175.0 | 11.4 | 32.3 | 1.00 | 120 | 5.75 |
| zoo1.jp2 | 10.16 | 3122.8 | 3502.1 | 189.0 | 3691.1 | 2.7 | 13.0 | 1425.5 | 368.5 | 1059.5 | 66.0 | 181.7 | 1.00 | 648 | 5.70 |
| Bretagne2.j2k | 5.04 | 3153.8 | 3137.9 | 95.0 | 3232.9 | 1.5 | 36.5 | 1589.7 | 389.9 | 797.1 | 157.4 | 185.4 | 1.00 | 720 | 4.49 |
| kodak_2layers_lrcp.j2c | 3.19 | ERROR (tier1: more coding passes than 3K - 2 for K coded bit-planes) | | | | | | | | | | | | | |
| 123.j2c | 3.24 | 1088.6 | 1088.2 | 24.8 | 1113.1 | 2.9 | 2.3 | 788.5 | 77.8 | 168.7 | 13.4 | 38.2 | 1.00 | 267 | 4.17 |
| movie_00000.j2k | 2.07 | 545.8 | 544.6 | 38.2 | 582.8 | 3.5 | 1.0 | 57.2 | 24.6 | 322.9 | 63.8 | 72.7 | 0.99 | 73 | 7.98 |
| _00042.j2k | 2.07 | 616.4 | 615.3 | 41.0 | 656.3 | 3.1 | 2.7 | 37.9 | 13.1 | 423.5 | 65.7 | 71.1 | 1.00 | 77 | 8.52 |
| test_lossless.j2k | 1.05 | ERROR (tier1: more coding passes than 3K - 2 for K coded bit-planes) | | | | | | | | | | | | | |
| pacs.ge.j2k | 0.26 | 85.8 | 85.9 | 1.9 | 87.8 | 2.9 | 0.5 | 61.5 | 6.0 | 13.8 | 1.1 | 3.1 | 1.00 | 21 | 4.18 |
| buxI.j2k | 0.26 | 75.5 | 75.5 | 2.0 | 77.5 | 3.3 | 0.2 | 46.5 | 6.2 | 18.0 | 1.1 | 3.0 | 1.00 | 17 | 4.56 |
| issue208.jp2 | 1.05 | 432.3 | 433.1 | 25.7 | 458.8 | 2.2 | 4.6 | 30.6 | 18.5 | 293.4 | 36.8 | 49.7 | 1.00 | 47 | 9.76 |
| issue559-eci-090-CIELab.jp2 | 0.09 | 70.1 | 70.4 | 1.8 | 72.2 | 1.2 | 2.5 | 37.1 | 7.1 | 19.2 | 1.1 | 3.5 | 1.01 | 22 | 3.28 |
| cthead1.j2k | 0.07 | 15.1 | 15.0 | 0.5 | 15.4 | 4.5 | 0.1 | 8.9 | 1.6 | 3.4 | 0.3 | 0.8 | 1.00 | 4 | 3.86 |

Findings:

* Ratio vs OpenJPEG 1-thread is 3.3x to 9.8x (13 files decoded); none meets the 2x budget
  yet. Best: `issue559` 3.3x, `cthead1` 3.9x, `123.j2c` 4.2x; worst: `issue208.jp2` 9.8x,
  `_00042.j2k` 8.5x, `movie_00000.j2k` 8.0x (all dominated by the inverse DWT).
* Two benchmark files do not decode: `kodak_2layers_lrcp.j2c` and `test_lossless.j2k` fail
  with `malformed at tier1: more coding passes than 3K - 2 for K coded bit-planes` (a decoder
  defect or an over-strict check in `Tier1`, to be triaged; not a benchmark issue). They are
  reported as errors, not skipped silently.
* Where the time goes: Tier-1 is 40-70% on most files (p0_07 2.66 s of 3.99 s); the inverse
  DWT is 15-25% on lossy/large files and 55-75% on `movie_00000`, `_00042`, `issue208`
  (few coded bits, so Tier-1 is cheap there); dequantisation 3-10%; MCT + DC shift 1-4%
  (5% on Bretagne2); interleaving 2-3%; Tier-2 under 2% except the many-tile files; glue
  (allocation, tile blit) 3-5%.

Profile of the slowest file (`p0_07.j2k`, 4.2 Mpx, 256 tiles, 5-3, 3.9 s), sampled with
`gdb -p PID -batch -ex "thread apply all bt 12"` 60 times, 0.2 s apart, on the worker thread
(50 samples with Lean frames; leaf = innermost frame). By stage (any frame in the stack):
Tier-1 40, inverse DWT 13 (the 5-3 lifting in `DWT53`), dequantisation 5, other 2. Top-10
leaf frames (count of 50):

1. `Tier1.colRowsU` in `sigPropPass` (specialised): 7
2. `MQ.Dec.decode`: 7
3. `lean_dec_ref_cold` (runtime refcount drop): 5
4. `lean_alloc_small_object_core` (runtime allocation): 4
5. `Tier1.scanCols` in `scanStripes` in `sigPropPass`: 3
6. `Tier1.scanCols` in `scanStripes` in `magRefPass`: 3
7. `Tier1.colRowsU` in `cleanupPass`: 3
8. `MQ.renormLoop`: 3
9. `DWT53.storeCols`: 3 (with `DWT53.liftPass` 3 and `DWT53.storeRow` 2: the DWT row/column
   stores and lifting passes are 8 of 50 together)
10. `mi_free`: 3 (with `lean_free_object` 2)

Allocation and freeing (items 3, 4, 10 and `lean_free_object`) are 14 of 50 samples (28%):
the Tier-1 passes and the DWT allocate per column/row or box values in the hot loops. For
Phase 8 the first candidates are Tier-1 (sigProp/magRef/cleanup passes and the MQ decode,
allocation-free column loops), then the DWT column pass layout (store/lift), then the
dequantisation and tile blit. The sample is small (50 samples), so only the order of
magnitude is reliable.

### 2026-11-25: allocation-free MQ decisions (task 8.2a, based on `aeebe86`)

Command: `scripts/bench.sh --runs 3` before (at `aeebe86`) and after, same sandbox, other
agents building in parallel (load average 1.2-2.9, so +-3% noise). Method as in 8.1.

| file | Tier-1 ms before | Tier-1 ms after | Tier-1 speed-up | total ms before | total ms after | total / OpenJPEG before | total / OpenJPEG after |
|---|---|---|---|---|---|---|---|
| p0_07.j2k | 2492.7 | 2137.4 | 1.17x | 3729.5 | 3430.1 | 4.53 | 4.16 |
| p0_08.j2k | 1203.1 | 989.3 | 1.22x | 1688.6 | 1489.8 | 4.20 | 3.71 |
| p1_03.j2k | 331.2 | 305.2 | 1.09x | 668.2 | 644.1 | 5.57 | 5.37 |
| zoo1.jp2 | 1375.1 | 1158.5 | 1.19x | 3448.3 | 3288.1 | 5.32 | 5.07 |
| Bretagne2.j2k | 1539.0 | 1299.5 | 1.18x | 3152.7 | 2990.8 | 4.38 | 4.15 |
| kodak_2layers_lrcp.j2c | 717.9 | 603.3 | 1.19x | 1861.9 | 1771.3 | 5.33 | 5.08 |
| 123.j2c | 771.8 | 654.4 | 1.18x | 1112.0 | 985.4 | 4.16 | 3.69 |
| movie_00000.j2k | 55.5 | 47.7 | 1.16x | 574.3 | 571.9 | 7.87 | 7.83 |
| _00042.j2k | 37.0 | 32.0 | 1.16x | 640.9 | 664.2 | 8.32 | 8.63 |
| test_lossless.j2k | 240.5 | 207.1 | 1.16x | 345.8 | 305.1 | 3.97 | 3.51 |
| pacs.ge.j2k | 60.0 | 50.2 | 1.20x | 85.7 | 77.0 | 4.08 | 3.67 |
| buxI.j2k | 46.0 | 38.3 | 1.20x | 75.8 | 69.6 | 4.46 | 4.09 |
| issue208.jp2 | 29.7 | 25.9 | 1.15x | 446.3 | 450.1 | 9.50 | 9.58 |
| issue559-eci-090-CIELab.jp2 | 36.0 | 31.1 | 1.16x | 69.8 | 66.1 | 3.17 | 3.00 |
| cthead1.j2k | 8.8 | 7.2 | 1.22x | 15.5 | 13.8 | 3.87 | 3.45 |

What changed (`JPEG2000/MQ.lean`; proofs in `Spec/MQEquiv.lean`):

* `MQ.Dec.decode` allocated a fresh `Dec` on 4 of its 5 paths (the compiler only reused the
  record on one branch) plus a `Bool × Dec` pair per decision, and `RENORMD` updated the
  record once per shift. Now `decode` is an `@[inline]` wrapper `(d.step i).bit, d.step i`
  around `Dec.step`, which stores the decision in a new field `Dec.bit` (so the pair is
  built and destructured at every call site and the compiler removes it); `step` folds the
  five flowchart paths into scalar selections and calls `Dec.renormS`, which runs `RENORMD`
  (with `BYTEIN`, reading bytes only when `CT = 0`) on unboxed local registers as a C loop
  and ends with one in-place record update (registers, context byte, decision). The
  generated C of `step`/`renormS` has no allocation on any path (only the `reuseFailAlloc`
  fallbacks for a shared `Dec`), and the Tier-1 hot functions no longer allocate per
  decision. C2: `renormS_eq` (scalar loop = `renormLoop` on the updated record) and
  `step_eq_ref` (`step` = the path-by-path `stepRef`, i.e. the old `decode`); `decode_sim`
  is reproved through them with its statement unchanged; Tier-1 proofs (C3, Tier1Wire, C9)
  build unchanged.
* MQ throughput (`lake exe bench-mq`, same data as the 2.6 table below): 135.6 / 102.6 /
  80.8 / 72.8 M decisions/s at p(LPS) 0.02 / 0.1 / 0.3 / 0.5 and 180.2 M/s on T.88 H.2
  (2.6: 85.8 / 73.3 / 62.0 / 51.0 / 93.2). `lake exe tests`: Tier-1 fast throughput
  3.9 M coefficients/s, 43 M MQ decisions/s on dense 64x64 K=12 (3.4a: 3.1 M, 34 M).

Tried and reverted (measured slower): `@[inline]` on `step` (no gain, more code);
`clearVisFrom` writing only words with `VIS` set (+4% Tier-1, branch cost); passing the
Tier-1 state `St` through `colRows` instead of its three components (+8%: the compiler then
allocates per coefficient, as noted in 3.4a).

Where Tier-1 time still goes (callgrind on `pacs.ge.j2k`, instruction counts): the MQ
decoder is now ~1/3 of Tier-1; the rest is the pass loops (`scanCols`/`colRowsU`
specialisations), `clearVisFrom` (~11% of Tier-1: a full sweep of boxed `Array UInt32` per
bit-plane) and one `St` allocation + free per stripe column (`colRowsU` returns the state;
~7%). These are inherent to the current representation: flag words and magnitudes as boxed
`Array UInt32` with `Nat` indices (every `fset` checks ownership and drops the old element),
and the column loop returning a 3-field state. The next steps (larger, proof-affecting):
flags/magnitudes in a `ByteArray`-backed `UInt32` buffer with `USize` indices (the
`fget`/`fset` lemma interface in `Spec/Tier1Equiv/Basic.lean` is the seam), a fused
stripe loop (columns and rows in one tail-recursive function) so no state record is returned
per column, and clearing `VIS` inside the cleanup pass. Tier-1 is still 2.1 s of 3.4 s on
`p0_07`; the inverse DWT (outside this task) is the other large stage.

## MQ decoder throughput

Task 2.6, 2026-11-25, on top of `182e722` (phase-1-headers), same machine as above
(aarch64 sandbox, 8 cores, other agents building in parallel: expect some noise).
Command: `lake build bench-mq && lake exe bench-mq` (source `Bench/MQ.lean`; the target is
not in the default build).

Method: the input is produced by the reference encoder `Encode.MQ.encodeAll`, never random
bytes (random bytes soon hit a marker and the decoder stops consuming input). Four data sets
of random decisions over the 19 Tier-1 contexts in their T.800 Table D.7 initial states,
`p(LPS)` ∈ {0.02, 0.1, 0.3, 0.5}, in segments of 16 384 decisions (about one 64×64
code-block), at most 1 MB of coded bytes or 8 M decisions per set (2.68 MB in total); and
the T.88 H.2 vector (30 bytes, 256 decisions) repeated 20 000 times with one `Dec.init` per
copy, which shows the per-segment overhead. The fast decoder (`JPEG2000.MQ.Dec.decode` in a
tail-recursive loop, one `Dec.init` per segment) decodes each set 5 times; the table gives
the median. Every run checks the number of `1` decisions against the generated data. The
last two rows compare the flowchart spec `Spec.MQ.decodeAll` (lists and `Nat`; its `byteAt`
is linear in the position, so it degrades on long segments) with the fast decoder's list
API on one 20 000-decision segment. MB = 10^6 coded bytes.

| data | decisions | coded bytes | bits/decision | ms | M decisions/s | MB/s |
|---|---|---|---|---|---|---|
| fast, p(LPS) 0.02, 19 ctx | 8011776 | 213665 | 0.21 | 93.3 | 85.8 | 2.3 |
| fast, p(LPS) 0.1, 19 ctx | 8011776 | 538438 | 0.54 | 109.4 | 73.3 | 4.9 |
| fast, p(LPS) 0.3, 19 ctx | 8011776 | 926654 | 0.93 | 129.2 | 62.0 | 7.2 |
| fast, p(LPS) 0.5, 19 ctx | 7634944 | 1001640 | 1.05 | 149.7 | 51.0 | 6.7 |
| fast, T.88 H.2 x 20000 (init per segment) | 5120000 | 600000 | 0.94 | 54.9 | 93.2 | 10.9 |
| spec `Spec.MQ.decodeAll`, p(LPS) 0.1, 1 segment | 20000 | 1307 | 0.52 | 4.2 | 4.8 | 0.3 |
| fast list API `MQ.decodeAll`, same segment | 20000 | 1307 | 0.52 | 0.4 | 45.2 | 3.0 |

Reading: the fast decoder runs at 51–86 M decisions/s on realistic skewed data (the slower
rows have more LPS and renormalisation work per decision), about 15–18× the spec decoder on
a small segment (the spec gets relatively slower as segments grow). The MB/s figures are
low because skewed data packs many decisions per byte; decisions/s is the figure that
matters for Tier-1. The reference encoder generates data at about 7 M decisions/s. The
10^6-case random round-trip run (`JPEG2000_MQ_ROUNDTRIPS=1000000 lake exe tests`, suite
`mq-roundtrip`: encoder → spec and fast decoders, 113 M decisions) takes about 46 s.
