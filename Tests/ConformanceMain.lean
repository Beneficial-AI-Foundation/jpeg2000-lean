import Tests.Conformance

/-!
# `lake exe conformance` entry point (task 5.6b)

Plan.md §8.1; T.803 §C (Tables C.1, C.4, C.6, C.7). The runner is `Tests.Conformance`, which
`Tests.Main` also imports for its test-suite hook `run`; the top-level `main` lives in this
separate module so that the `tests` and `conformance` executables do not clash.
-/

open JPEG2000.Tests.Conformance in
/-- `lake exe conformance [--gate-class0]`: every profile-0/1 reference entry, both classes.
Exit 1 on any class-1 failure (the M5 criterion; class 1 includes the reversible bit-exact
check), any compared JP2 TIFF failure (task 6.3a), or when the corpus is missing. Class 0 is
always run and reported; it gates the exit
code only with `--gate-class0` (OpenJPEG's class-0 block is commented out and OpenJPEG
itself fails the same class-0 entries). -/
def main (args : List String) : IO UInt32 := do
  let gating := if args.contains "--gate-class0" then [0, 1] else [1]
  if !(← haveCorpus) then
    IO.eprintln "conformance: corpus/files missing (run python3 -I scripts/fetch-corpus.py)"
    return 1
  let t0 ← IO.monoMsNow
  let t ← JPEG2000.Tests.ConformanceData.load
  let os ← evaluate t
  let fails ← report os (gating := gating)
  IO.println s!"conformance: {fails} failure(s), {(← IO.monoMsNow) - t0} ms"
  return if fails == 0 then 0 else 1
