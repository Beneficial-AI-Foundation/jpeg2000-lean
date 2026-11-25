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
