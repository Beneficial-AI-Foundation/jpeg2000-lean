import Lake

open Lake DSL

/-!
# jpeg2000-lean build configuration

No Lake dependencies by rule (Plan.md §9, §10): safe-pdf depends on this library and must
not inherit anything transitive. `autoImplicit` and `relaxedAutoImplicit` are off for every
library.
-/

package jpeg2000 where
  version := v!"0.1.0"
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

/-- The decoder (Plan.md §3): pure, total, no `IO`. -/
@[default_target]
lean_lib JPEG2000 where
  roots := #[`JPEG2000]

/-- Executable specifications and theorems (Plan.md §5.1). -/
@[default_target]
lean_lib Spec where
  roots := #[`Spec]

/-- Reference encoder, for tests and proofs only (Plan.md §5.3). -/
@[default_target]
lean_lib Encode where
  roots := #[`Encode]

/-- Test suites: every module under `Tests/` (new modules need no lakefile line). -/
lean_lib Tests where
  globs := #[.submodules `Tests]

/-- The test runner: `lake exe tests`. -/
lean_exe tests where
  root := `Tests.Main

/-- Benchmarks: every module under `Bench/` (not a default target). -/
lean_lib Bench where
  globs := #[.submodules `Bench]

/-- MQ decoder throughput benchmark (task 2.6): `lake exe bench-mq`. -/
lean_exe «bench-mq» where
  root := `Bench.MQ

/-- Decoder benchmark with per-stage timing (task 8.1): `lake exe bench`
(see `scripts/bench.sh`). Not a default target. -/
lean_exe bench where
  root := `Bench.Decode

/-- Header dump in `opj_dump -i` form (task 1.7): `lake exe header-dump <file>`, compared
with OpenJPEG by `scripts/diff-headers.py`. Not a default target. -/
lean_exe «header-dump» where
  root := `Tests.HeaderDump

/-- Per-code-block segments and Tier-1 coefficients in the instrumented-OpenJPEG dump format
(task 4.6b): `lake exe segment-dump <file>`, compared with OpenJPEG by
`scripts/diff-segments.py`. Not a default target. -/
lean_exe «segment-dump» where
  root := `Tests.SegmentDump

/-- T.803 conformance runner (task 5.6b): every profile-0/1 stream against the reference
decodes at the class-0 and class-1 thresholds: `lake exe conformance`. Not a default target. -/
lean_exe conformance where
  root := `Tests.ConformanceMain

/-- Decoded planes as PGX files (task 6.3b): `lake exe image-dump <file> <outprefix>` writes
the raw codestream components and the `JPEG2000.decode` image channels, compared with
`opj_decompress` by `scripts/diff-images.py`. Not a default target. -/
lean_exe «image-dump» where
  root := `Tests.ImageDump
