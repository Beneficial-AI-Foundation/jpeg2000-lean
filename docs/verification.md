# What "formally verified" means here

This decoder is written in Lean 4. Some of its properties are **proved**: the Lean kernel
checked a proof that holds for every input. Others are **tested**: we ran the decoder on
real files and compared the results with other decoders and with reference images. This
page lists which is which.

The short version:

* **Proved:** the decoder never crashes or reads out of bounds, and it always returns. Its
  memory use and output size are capped by the limits you pass in. It computes the same
  result as a direct, line-by-line transcription of the JPEG 2000 standard (ITU-T T.800).
  That match is exact for lossless images and within a stated error bound for lossy ones.
  Decoding what the project's reference encoder produces gives back the original image
  exactly.
* **Tested, not proved:** that the transcription of the standard is itself correct, that
  the output matches OpenJPEG and the official conformance images, colour management for
  ICC-profiled files, speed, and behaviour under random corruption (fuzzing).
* **Assumed:** the Lean kernel, compiler and runtime.

The proofs are checked on every build. `scripts/check-hygiene.sh` runs `#print axioms` on
every listed theorem (1,756 at the time of writing, in `scripts/axioms.lean`) and fails if
any of them depends on something other than Lean's three standard axioms (`propext`,
`Classical.choice`, `Quot.sound`). In particular, nothing depends on `sorry`, an unproved
placeholder.

## The two decoders

The repository contains two decoders for the same format:

* **The specification** (`Spec/`). Each stage is written to be read side by side with the
  standard. It uses whole numbers of any size (`Int`) and exact fractions (`Rat`), and it is
  very slow. It is never used to decode images in production.
* **The implementation** (`JPEG2000/`). This is the decoder you call. It uses 32- and 64-bit
  integers, in-place buffers and lookup tables, and contains no floating point.

Most of the proofs show that the implementation computes what the specification computes.
So the guarantee is "the fast decoder does exactly what this readable transcription of the
standard says". Whether the transcription matches the standard is checked by reading and by
testing (see below), not by proof.

## What is proved

The IDs (S1–S6, C1–C10) are the properties listed in `Plan.md` §4.

### Safety (S1–S6)

| Property | What it means | How it is established |
|---|---|---|
| S1 memory safety | No out-of-bounds reads or writes, no unsafe code | Every array access is checked or carries a proof that the index is in range. `scripts/hygiene.py` rejects `unsafe`, `partial`, `panic!`, `!`-indexing, `sorry`, FFI and floating point in `JPEG2000/`, `Spec/` and `Encode/`. |
| S2 totality | `decode` returns a result for every byte string | Lean only accepts terminating definitions. Every loop is structural or uses fuel derived from a checked size. `scripts/closure.lean` walks everything the four public entry points depend on and rejects hidden `partial`, `unsafe`, `extern` or overridden implementations. |
| S3 bounded resources | Output size, memory and work are bounded by `Limits`; going over is a `limitExceeded` error | `Spec/Resources.lean` and `Spec/Resources/*`. Proved bounds include input size, declared image size, output planes and bytes, display buffers, per-tile working memory, packet visits and coding passes. See `docs/resources.md` for the full list. |
| S4 no ambient authority | The library cannot do I/O | No `IO` in `JPEG2000/` (hygiene guard). |
| S5 local failure | A corrupt stream yields an error value | Errors are ordinary return values (`Except Error`). |
| S6 determinism | Same input, same output | Pure functions only. |

### Correctness (C1–C10)

| Property | Statement | Main theorem |
|---|---|---|
| C1 MQ round trip | Decoding the reference MQ encoder's output returns the original decisions | `Spec.MQRoundTrip.roundTrip` |
| C2 MQ conformance | The fast arithmetic decoder equals the Annex C flowchart decoder on every input | `Spec.MQEquiv.decodeAll_eq`, `decode_init_eq` |
| C3 Tier-1 conformance | The fast bit-plane decoder equals the Annex D specification, coefficient by coefficient, for all 64 code-block style combinations | `Spec.Tier1EquivM.c3_all`, `Spec.Tier1Equiv.c3_plain` |
| C4 tag trees | Tag-tree decoding inverts encoding, values are monotone, fast equals spec | `Spec.TagTree.decode_encode`, `value_monotone`, `fast_decode_eq` |
| C5 progression | Every progression order, with and without POC, visits each packet exactly once | `Spec.Progression.c5`, `c5_poc`, `forPackets_eq_spec` |
| C6 lossless wavelet | Inverse 5/3 undoes forward 5/3 exactly, any size, any number of levels | `Spec.DWT53.srMulti_sdMulti` |
| C7 lossless colour | Inverse RCT undoes forward RCT on all integer triples | `Spec.MCT.rctInv_rctFwd` |
| C8 lossy error bounds | The fixed-point 9/7 wavelet and ICT stay within an explicit per-sample distance of the exact rational computation | `DWT97.qsrMulti_err_frac`, `MCT.ict_c8` |
| C9 implementation = spec | End to end, `decodeCodestream` and `Spec.Decode.decode` both reject or both succeed with the same image geometry; reversible samples are equal, irreversible samples are within the C8 bound plus 1 | `Spec.C9.c9`; carried to `JPEG2000.decode` by `Spec.ColorResources.image_native_spec` |
| C10 lossless round trip | For every image the reference encoder encodes losslessly, the public decoder returns exactly that image | `Spec.RoundTrip.encode_native_roundtrip`, `Spec.RoundTrip.encode_image_roundtrip` |

The packet layer (Tier-2), the header merge, the wavelet plane loops and the dequantisation
loop also have their own equivalence proofs, which C9 is built from.

`docs/c9.md` gives the exact statement of C9 and C10, the meaning of every condition, and a
table of the irreversible error bound. Two points matter when reading these results:

* **Lossy images are not proved bit-exact.** For 9/7 images C9 bounds the distance from the
  exact rational result. At 8-bit depth with up to 5 decomposition levels the bound is about
  ±1 sample. At 16-bit depth or with many levels the proved bound is much looser than the
  error actually observed (which is at most 1 in the conformance tests).
* **Diagnostics can differ.** When both decoders reject a stream, they may report different
  error messages or offsets.

## What is tested, not proved

| Area | What is checked | Where |
|---|---|---|
| The specification matches T.800 | Read against the standard. All of the checks below also exercise it indirectly. | `Spec/` module docs cite the clauses they transcribe |
| Header parsing | Headers of 44 corpus codestreams match `opj_dump -i` field by field. The marker parsers have proved serialise-then-parse round trips. | `scripts/diff-headers.py` (CI) |
| Per-code-block data | Segments and decoded coefficients of 54,061 code-blocks in 32 files are identical to an instrumented OpenJPEG 2.5.3 | `scripts/diff-segments.py` (CI) |
| ISO/IEC 15444-4 (T.803) conformance | Every profile-0 and profile-1 stream passes the class-1 thresholds (52/52), and all 29 lossless components are bit-exact. Class 0 passes 12/26; every failing entry fails the same way with OpenJPEG. | `lake exe conformance` (CI) |
| JP2 files | All 9 conformance JP2 files match their reference images. The three with ICC profiles are compared after applying the profile with lcms2 in the test harness; the library itself never applies ICC profiles. | `Tests/JP2.lean` (CI) |
| Images from real PDFs | 42 JPEG 2000 streams extracted from public PDFs, compared with `opj_decompress`. Differences are recorded per file in `corpus/manifest.json`. | `scripts/diff-images.py` (CI) |
| Fuzzing | About 22,000 mutated inputs showed no crashes and no limit escapes. CI runs a 300-case smoke test. | `lake exe fuzz`, `scripts/fuzz.sh` |
| Speed | Measured against OpenJPEG on a fixed benchmark set | `lake exe bench`, `docs/performance.md` |
| Unit and property tests | 36 suites, including 10⁶ random MQ round trips and random code-block, packet and wavelet round trips | `lake exe tests` |

## Known limitations

These are recorded in `progress.md`:

* **Work is not bounded in time.** S3 bounds memory, output and the number of packets and
  coding passes, but there is no proved bound on total running time. Fuzzing found a family
  of corrupted streams that decode correctly but take 20 seconds to several minutes (task
  9.6, open). Callers that need a time bound should run the decoder under their own timeout,
  as safe-pdf does in its confined worker.
* **Speed.** Single-threaded decoding is 3–10× slower than OpenJPEG on the benchmark set
  (Phase 8, in progress).
* **Hardening (Phase 9) is not finished.** Crafted streams for each known OpenJPEG/JasPer
  CVE class, a lenient mode with a proof that it agrees with strict mode on valid streams,
  and an independent re-check of the proofs with a second kernel (lean4lean) are still to
  do.
* **Scope.** JPEG 2000 Part 1, JP2 and the JPX subset PDF needs. HTJ2K (Part 15) and the
  rest of Part 2 are not supported.

## What you have to trust

* **The Lean kernel.** It checks every proof. It is small and widely used. An independent
  re-check with lean4lean is planned (task 9.4).
* **The Lean compiler and runtime.** The proofs are about the Lean definitions, but the
  program you run is compiled to C. Compiler bugs, and the runtime's implementations of
  primitives such as `ByteArray` and fixed-width integer operations, are outside the proofs.
* **The specification.** A proof that the decoder matches the specification is only as good
  as the specification. Its correctness rests on review against T.800 and on the
  conformance and differential tests above.
* **The statements.** Each theorem says exactly what is listed above and in `docs/c9.md` and
  `docs/resources.md`. A property not stated there is not claimed.

## Checking it yourself

```sh
lake build                     # builds the decoder and checks every proof
scripts/check-hygiene.sh       # forbidden constructs + #print axioms on every listed theorem
lake build tests && lake exe tests
python3 -I scripts/fetch-corpus.py      # download the test corpus (verified by SHA-256)
lake build conformance && .lake/build/bin/conformance
```
