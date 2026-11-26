# jpeg2000-lean — Project Plan

**A formally verified, fast JPEG 2000 decoder, written in Lean 4.**

JPEG 2000 decoders are large C programs that parse attacker-controlled bit streams with many
interacting size fields. OpenJPEG and JasPer both have long CVE histories (heap overflows in
tile and code-block handling, integer overflows in size arithmetic, unbounded allocations). No
formally verified JPEG 2000 decoder exists. This project builds one that is **total, memory
safe, resource bounded and proved equivalent to an executable specification of the
standard**, and it is **fast enough to be the decoder a PDF viewer actually ships**.

The first consumer is [safe-pdf](https://github.com/Beneficial-AI-Foundation/safe-pdf), whose
`/JPXDecode` images render as placeholder boxes today (safe-pdf `Plan.md` §3 rule 4: no C
parser of untrusted data in the trusted path). The decoder is a standalone library, so other
consumers (image viewers, archives, medical imaging) can use it too.

---

## 1. Scope

### What we build

```
bytes → Except Error Image          -- decode a JP2/JPX file or a raw codestream (J2K)
```

* **ISO/IEC 15444-1 (ITU-T T.800), JPEG 2000 Part 1, the full decoder**: every marker
  segment, all five progression orders plus `POC`, precincts, quality layers, all six
  code-block modes, both wavelets (reversible 5/3, irreversible 9/7), scalar quantisation
  (derived and expounded), ROI max-shift, RCT/ICT, sub-sampled components, tiles and
  tile-parts, `PPM`/`PPT`/`PLT`/`TLM`, decoding at reduced resolution.
* **The JP2 file format (Annex I)** and the **JPX baseline subset of Part 2** that PDF
  requires (ISO 32000-2 §7.4.9): colour specification (enumerated sRGB/greyscale/sYCC, ICC
  passed through), palette (`pclr`), component mapping (`cmap`), channel definitions
  (`cdef`, alpha/opacity), resolution boxes ignored.
* **PDF specifics** exposed for the consumer: `/SMaskInData`, the image's own colour space
  when the PDF gives none, bit depths up to 38 scaled for display.
* Output: per-component sample planes plus an interleaved 8- or 16-bit buffer, with the
  colour information needed to convert.

### What we deliberately leave out (initially)

* **Encoding**, except a small reference encoder used **only by tests and proofs** (§5.3).
* Part 2 beyond the JPX baseline: arbitrary wavelet kernels, multi-component transforms,
  trellis-coded quantisation, non-linear point transforms.
* HTJ2K (Part 15, the high-throughput block coder): Tier 2 (§7), once Part 1 is done and only
  if consumers meet it.
* Motion JPEG 2000, JPIP, Part 9/10/11.
* Any `IO`, FFI, `unsafe` or floating point in the decoder.

---

## 2. Prior art and what we take from each

| Project | What it is | What we take |
|---|---|---|
| **ITU-T T.800 / ISO 15444-1** | The standard: syntax (Annex A), ordering and tag trees (B), MQ coder (C), bit-plane coding (D), quantisation (E), DWT (F), component transforms (G), ROI (H), JP2 (I) | The specification itself: the Lean spec transcribes its flowcharts and equations, annex by annex |
| **ITU-T T.803 / ISO 15444-4** | Conformance test streams and reference decodes (profiles 0/1, classes 0/1/2) | The acceptance bar (§8) |
| **OpenJPEG** (BSD, C) | The reference open-source codec; used by MuPDF, pdfium, poppler; compiled to WebAssembly in pdf.js | Differential oracle; its T1 flag layout and stripe-oriented code-block decoding as performance ideas; its CVE list as the adversarial test agenda |
| **Kakadu** (proprietary, C++) | The fastest Part 1 decoder; fixed-point 9/7 | Proof that fixed-point lossy decoding is industrially acceptable; a second differential oracle (demo binaries) |
| **Grok** (AGPL, C++) | A modern, heavily parallel fork of OpenJPEG | Parallelism strategy (code-block and tile parallelism); third oracle |
| **JasPer** (C) | An older reference implementation | Second opinion on edge cases; another CVE source |
| **pdf.js `jpx.js`** (JS, historical) | A compact pure-JavaScript decoder (a few thousand lines) for the PDF subset, shipped for years before pdf.js moved to OpenJPEG/WASM | Evidence that the PDF-relevant subset is tractable in a high-level language; its known gaps as a checklist |
| **safe-pdf** (Lean 4, this organisation) | A verified PDF reader with pure-Lean JPEG, Flate and CCITT decoders | The methodology (spec first, fast implementation with an equivalence theorem, `Limits`, fuel, hygiene guard, ledger and `/next-wave` loop) and concrete fast-Lean techniques (§6) |

---

## 3. Architecture

```
            ┌───────────────────────────────────────────────────────────────┐
 bytes ───► │ Box     JP2/JPX boxes → codestream + colour info  (Annex I)   │
            │ Marker  main/tile headers, tile-parts → Header    (Annex A)   │
            │ Tier2   packets: tag trees, progression, layers  (Annex B)    │
            │         → per code-block coding-pass segments                 │
            │ MQ      arithmetic decoder                       (Annex C)    │
            │ Tier1   EBCOT bit-plane decoding per code-block  (Annex D)    │
            │         → quantised wavelet coefficients                      │
            │ Quant   dequantisation, ROI max-shift            (Annex E, H) │
            │ DWT     inverse 5/3 / 9/7, multi-level           (Annex F)    │
            │ MCT     inverse RCT / ICT, DC shift, clamp       (Annex G)    │
            │ Assemble tiles, sub-sampling, palette, channels  (Annex B, I) │
            └───────────────────────────────────────────────────────────────┘
                                         │
                                         ▼
                              Image (planes + colour info)
```

Every stage is a pure, total function with an explicit `Limits` argument. Stages
communicate through plain data (headers, segment lists, coefficient planes), which keeps each
equivalence proof local.

### Ground rules (the same as safe-pdf's core)

1. **No `IO`, no `partial`, no `unsafe`, no `panic!`, no `!` indexing, no `sorry`** in
   `JPEG2000/`. A hygiene guard greps for them in CI and checks `#print axioms` of every
   top-level theorem (only `propext`, `Classical.choice`, `Quot.sound`).
2. **Every loop is structurally recursive or carries a measure/fuel** justified by the input
   size or a `Limits` field: code-block passes, packet iteration, tag-tree descent,
   decomposition levels, tile-parts.
3. **Every size the stream declares is checked against `Limits` before anything is
   allocated.** Exceeding a limit returns `Error.limitExceeded`, never slows down
   unboundedly.
4. **No floating point.** The 9/7 wavelet and the ICT run in fixed point; their error
   against the exact rational model is proved (§5.4).
5. **Spec first.** Each stage has a simple executable specification in `Spec/` and an
   efficient implementation in `JPEG2000/`, with an equivalence theorem (§5).

---

## 4. The properties (what "verified" means here)

### Security — proved

| # | Property | Statement sketch |
|---|---|---|
| S1 | Memory safety | No `unsafe`, no FFI; every array access is bounds-checked or carries a proof (the fast paths use `uget`/`uset` with proved indices, so the proofs *remove* checks) |
| S2 | Totality | `decode` is a total function, accepted by the termination checker, on **every** byte string |
| S3 | Bounded resources | Output size, intermediate allocation and work are bounded by explicit functions of `Limits` and the input length; excess is `Error.limitExceeded` |
| S4 | No ambient authority | The library's types contain no `IO` |
| S5 | Local, visible failure | A corrupt code-block, packet or tile yields an error value; in lenient mode it decodes as missing data (zero coefficients) for that region only, as the standard's error-resilience modes intend, and the result says so |
| S6 | Determinism | Pure functions; no data races (parallelism is through pure `Task`s, §6) |

### Correctness — proved

| # | Property | Statement sketch |
|---|---|---|
| C1 | MQ round trip | For every symbol sequence and context sequence, `mqDecode (mqEncode s) = s` (reference encoder, Annex C) |
| C2 | MQ conformance | The fast MQ decoder equals the Annex C flowchart decoder (`Spec.MQ`) on every input |
| C3 | Tier-1 conformance | The fast EBCOT decoder equals the spec decoder (Annex D, coefficient by coefficient, pass by pass) for every mode combination |
| C4 | Tag trees | Tag-tree decoding inverts encoding; values are monotone down the tree |
| C5 | Progression | For each progression order (and `POC` change lists), the packet sequence visits every (layer, resolution, component, precinct) exactly once — a bijection onto the packet set |
| C6 | Lossless wavelet | Inverse 5/3 ∘ forward 5/3 = identity on every integer signal, every length (incl. odd and length 1), every level; multi-level and 2-D by composition |
| C7 | Lossless colour | Inverse RCT ∘ forward RCT = identity on all integer triples |
| C8 | Lossy error bounds | The fixed-point 9/7 inverse and ICT differ from the exact rational model by at most an explicit bound per sample (a function of levels and bit depth), proved |
| C9 | Implementation = spec | End to end, `decode = Spec.decode` (exact for reversible paths; within C8's bound for irreversible ones) |
| C10 | Lossless round trip | For every image the reference encoder can encode losslessly (5/3 + RCT), `decode (encode img) = img` — the headline theorem of the project |

### Tested, not proved

* Conformance to ISO 15444-4 (T.803): profile-0 and profile-1 streams at the class
  thresholds (peak error and MSE against the reference decodes); bit-exact on the reversible
  streams.
* Differential agreement with OpenJPEG (and Kakadu/Grok where available) on generated and
  real streams.
* Robustness under fuzzing (§8).
* Speed (§6).

---

## 5. Specification strategy

### 5.1 Two implementations per stage

Each stage gets a **spec** and an **implementation** (the EverParse/safe-pdf pattern):

* **Spec (`Spec/`)** — a near-literal transcription of the standard's flowcharts and
  equations over `List`, `Nat`, `Int`, `Rat`: obviously right by reading it next to the
  annex, slow, never used in production.
* **Implementation (`JPEG2000/`)** — fixed-width integers, `ByteArray`-backed typed buffers,
  in-place updates, tables, stripes, parallel tasks.
* **Equivalence theorem** per stage (C2, C3, …), composed into C9.

safe-pdf proved this pattern on its Inflate: a 9-bit lookup table carries a proof field, the
bit-by-bit decoder stays the spec, and `decodeSym_eq` links them. The same structure fits the
MQ decoder (state tables), Tier-1 (neighbourhood flag words) and the DWT (in-place lifting).

### 5.2 Hard parts and how we stage them

* **MQ decoder** (small, sharp): spec = Annex C flowcharts (`INITDEC`, `DECODE`, `RENORMD`,
  `BYTEIN` with the `0xFF` stuffing rule). Implementation = 32-bit `C`/`A`/`CT` registers in a
  tight loop. Proofs: C1, C2, termination of `RENORMD` (bounded shifts), bounded byte reads
  (never past the segment, synthetic `0xFF` padding as the standard says).
* **Tier-1 / EBCOT** (the largest proof): spec = per-coefficient state (significance,
  refinement, visited, sign) and the three passes as written in Annex D with the context
  tables D.1–D.3 as data. Implementation = one 32-bit flag word per coefficient caching the
  neighbourhood (as OpenJPEG's `T1` flags), stripe-of-four scanning, run-length mode. Proof
  by a simulation relation between the flag words and the spec state, preserved by each
  pass; each of the six mode flags handled as a separate lemma. Staged: plain mode first
  (covers most PDF images), then reset/termall/vertically-causal/segmentation symbols, then
  bypass (raw) mode.
* **Tier-2** (most adversarial): packet-header parsing with tag trees, zero-length packets,
  code-block inclusion, `Lblock` growth, layer accumulation of segments. Progression orders
  are written as explicit iterators with C5 proved once per order.
* **DWT**: spec = Annex F one-dimensional filtering with periodic symmetric extension,
  stated over `Int` (5/3) and `Rat` (9/7). Implementation = in-place lifting on `Int32`
  rows and column batches.

### 5.3 A reference encoder, for tests and proofs only

A deliberately simple Lean encoder (one tile, one layer, LRCP, plain code-block mode, 5/3 +
RCT, and a 9/7 variant) gives: the round-trip theorems C1, C4, C10; an endless supply of
valid streams for property-based tests; and fuzzing seeds. It never ships in the library's
public API.

### 5.4 Numbers

* All sample, coefficient and transform arithmetic is fixed width with **proved
  no-overflow conditions**, derived from the header (bit depth, guard bits, number of
  decomposition levels). A stream outside the proved range takes the checked `Int`/`Int64`
  slow path (exactly as safe-pdf's fast polygon filler falls back), never wraps silently.
* 9/7 and ICT: fixed-point lifting with fractional bits chosen per bit depth; theorem C8
  gives the per-sample error bound against the `Rat` model, and the conformance thresholds
  of T.803 are checked against that bound on paper, then by test.

---

## 6. Performance strategy ("fast")

**Target** (measured, not assumed): on the benchmark set (§8.4), single-threaded decode
within **2×** of OpenJPEG's single-threaded time, and faster than it with parallel tasks on a
multi-core machine. Phase 0 measures OpenJPEG on the benchmark set so the targets are
concrete numbers, not adjectives.

Techniques (each one with its equivalence proof, so speed never costs correctness):

1. **No GMP in hot loops.** `Nat`/`Int` arithmetic is arbitrary precision; compiled `<<<`
   and `^` on `Nat` call GMP (a safe-pdf gotcha). Hot code uses `UInt32`, `UInt64`, `Int32`,
   `Int64` (all in core Lean 4.36) and tables.
2. **Unboxed buffers.** Coefficients live in `ByteArray`-backed `Int32` planes (little-endian
   4-byte cells, `uget`/`uset` with proved bounds), not `Array Int` (boxed). Unique ownership
   keeps updates in place; the code is written so the compiler sees uniqueness.
3. **Proved bounds remove checks.** Loop invariants carry `i < size` proofs, so the compiled
   inner loops of MQ, Tier-1 and the DWT have no bounds checks.
4. **Tier-1 data layout.** One flag word per coefficient with the 8-neighbourhood
   significance and sign bits pre-merged (context lookup = one table index), stripe-oriented
   traversal, skipping all-zero stripes.
5. **DWT.** Lifting in place, row pass then column pass over batches of columns to stay in
   cache; 5/3 in `Int32`, 9/7 in `Int32`/`Int64` fixed point.
6. **Parallelism.** Code-blocks are independent after Tier-2: decode them with
   `Task.spawn` over pure functions, then tiles and components for the DWT. No locks, no
   `IO`; the result is deterministic (S6).
7. **Reduced-resolution decoding.** A PDF viewer at 30 % zoom can skip the finest
   resolution levels entirely (Part 1 allows it): `decode (maxResolution := r)`.
8. **Profiling loop.** macOS `sample` / Linux `perf` on the compiled benchmark binary every
   performance wave; the benchmark history is kept in the ledger.

---

## 7. Phased roadmap

Each phase ends at a milestone with a checkable exit criterion; each phase is one PR.

| Phase | Content | Milestone (exit criterion) |
|---|---|---|
| **0 — Infrastructure** | Lake project (Lean v4.36.0, no dependencies), `CLAUDE.md`, ledger, hygiene guard, CI (Linux + macOS), test runner, conformance and benchmark corpora fetched by SHA-256, OpenJPEG baseline timings, `Limits` and `Error` | **M0**: CI green; `scripts/fetch-corpus.py` verifies every file; OpenJPEG baseline numbers recorded |
| **1 — Containers and headers** | Byte/bit readers; JP2/JPX boxes; codestream markers (SIZ, COD/COC, QCD/QCC, RGN, POC, PPM/PPT, PLT, TLM, COM, SOT/SOD/EOC); tile-part assembly; header validation against `Limits` | **M1**: every T.803 stream and every corpus file parses to a header identical to OpenJPEG's dump; parse ∘ serialise round trip proved for marker segments |
| **2 — MQ coder** | Spec (Annex C), fast decoder, reference encoder | **M2**: C1 and C2 proved; 10⁶ random round trips; decoder throughput measured |
| **3 — Tier-1** | Spec and fast EBCOT decoder, all six modes, reference encoder for the plain mode | **M3**: C3 proved for plain mode; other modes tested against the spec; code-blocks extracted from T.803 streams decode identically to OpenJPEG |
| **4 — Tier-2** | Tag trees, packet headers, five progression orders + POC, layers, precincts, PPM/PPT | **M4**: C4, C5 proved; every T.803 stream yields the same per-code-block segments as OpenJPEG |
| **5 — Reconstruction** | Dequantisation, ROI, inverse DWT 5/3 + 9/7, RCT/ICT, DC shift, clamping, tiles, sub-sampling, reduced resolution | **M5**: C6, C7, C8 proved; T.803 profile 0 and 1 pass (reversible bit-exact, irreversible within class thresholds) |
| **6 — JP2/JPX output** | Colour spaces, palette, component mapping, channel definitions, alpha, bit-depth scaling, the consumer API | **M6**: the JP2 conformance files and the PDF-extracted corpus render identically to OpenJPEG + colour management to within tolerance |
| **7 — Equivalence end to end** | C9 composed from the stage theorems; C10 with the reference encoder; S3 resource theorem | **M7**: C9, C10, S2, S3 proved; `#print axioms` clean |
| **8 — Speed** | The techniques of §6, profiled; parallel code-block decoding | **M8**: the §6 targets met on the benchmark set, with numbers in the ledger |
| **9 — Hardening** | Fuzzing (mutation of T.803 and corpus streams, the OpenJPEG OSS-Fuzz corpus as seeds, crafted streams for every OpenJPEG/JasPer CVE class), lenient-mode conservativity (lenient = strict on valid streams, proved), independent kernel re-check (lean4lean, as safe-pdf) | **M9**: no crash or limit escape in N CPU-hours of fuzzing; every CVE-class stream rejected or bounded |
| **10 — safe-pdf integration** | Lake dependency of safe-pdf (pinned commit; a safe-pdf Decisions entry), `Quarantine.JPX` adapter (`/SMaskInData`, colour space precedence, `/Decode`), worker path, safe-pdf corpus with JPX-bearing PDFs | **M10**: safe-pdf renders every JPX image of its corpus, matches MuPDF/pdf.js within the image tolerance, no placeholder boxes for JPX |

**Tier 2 / later**: HTJ2K block decoder (Part 15), Part 2 extensions beyond the JPX baseline,
a verified encoder, region-of-interest decoding for viewers (decode only the visible
precincts — pairs well with safe-pdf deep zoom).

Phases 2 (MQ) and 1 (headers) are independent and can run in parallel; phase 3 needs 2;
phase 4 needs 1; phase 5 needs 3 and 4. Phase 8 can start on any stage once its equivalence
theorem exists.

**Current delivery order (2026-11-26).** M10 follows the verified M7 decoder.
The remaining M8 performance work and M9 hardening campaign are deferred. Both
keep their existing exit criteria. safe-pdf pins a packaging-only child of M7 while
the other branches evolve independently.

---

## 8. Testing and evaluation

1. **Conformance (ISO 15444-4 / T.803)**: the published profile-0 and profile-1 codestreams
   and their reference decodes (available, for example, in OpenJPEG's `openjpeg-data`
   repository), downloaded by SHA-256 into a git-ignored `corpus/` with a committed manifest;
   licence checked before any file is committed.
2. **Differential**: `opj_decompress` (and `kdu_expand` / Grok where installed; skipped
   cleanly when missing) on every corpus stream, comparing headers, code-block segments,
   coefficients (via debug dumps) and final samples stage by stage — a mismatch is localised
   to one stage.
3. **PDF corpus**: JPX images extracted from real PDFs (publisher and archive PDFs, scanned
   documents) — the reason this library exists; built together with safe-pdf's corpus.
4. **Benchmark set**: a fixed list of streams covering lossless/lossy, 8/12/16-bit, 1/3/4
   components, small and large (≥ 20 Mpx), single and multi tile, few and many layers.
5. **Property tests**: random images through the reference encoder (all parameter
   combinations it supports) → decode → compare (exact for reversible).
6. **Fuzzing**: mutation fuzzing of all corpora through the compiled decoder with
   `Limits` tight and loose; crashes are impossible by construction (S1, S2), so the fuzzer
   hunts for limit escapes, slow paths and disagreements with OpenJPEG.
7. **Adversarial streams**: one crafted stream per historical CVE class of OpenJPEG and
   JasPer (huge tile counts, zero-sized precincts, overflowing code-block sizes, malformed
   tag trees, truncated tile-parts, `POC` loops) — each must be rejected or decoded within
   limits.

---

## 9. Integration with safe-pdf

* safe-pdf's filter pipeline already stops at `/JPXDecode` and returns
  `Decoded.image .jpx parms bytes` (safe-pdf `Core/Filter.lean`, F5); its `Raster/Image.lean`
  decodes DCT and CCITT through `SafePdf.Quarantine.*`. A new `Quarantine.JPX` adapter calls
  `JPEG2000.decode limits bytes`, applies the PDF rules (ISO 32000-2 §7.4.9: the PDF's
  `/ColorSpace` overrides the file's colour information; `/SMaskInData` 1/2 selects the alpha
  channel as a soft mask; `/BitsPerComponent` not used), re-validates dimensions against the
  image dictionary, and returns pixels.
* safe-pdf's `Limits` map onto this library's `Limits` (image area, total decoded bytes).
* The decode runs inside safe-pdf's confined worker like every other render.
* Record the decoder as safe-pdf's first Lake dependency in its Decisions ledger.
  Both packages use `leanprover/lean4:v4.36.0`. The decoder has no transitive
  Lake dependencies. The consumer selects `libraryOnly` to keep its own test
  module namespace.

### Integration checks

1. Start from safe-pdf main. Pin the decoder by full Git revision, lock it with
   Lake and record the dependency decision. Exercise the public API from the consumer.
2. Route image XObjects, inline images and JPX mask streams through the pure
   adapter in the existing worker. Validate the full image dictionary dimensions
   against the codestream before using reduced output. Carry safe-pdf's image
   area and byte budgets through decoding, interleaving and compositing.
3. Test PDF-specified and embedded colour, palette indices, JPX sample precision,
   embedded straight and premultiplied opacity, and external masks. In particular,
   exercise Indexed colour before scaling indices and avoid applying opacity twice.
4. Feed the existing pinned **source PDFs** to the safe-pdf worker. The 81 PDFs
   surveyed in safe-pdf contained zero JPX images. The decoder corpus supplies
   19 JPX-bearing PDFs, including two differently filtered uses of the same
   codestream. Check each placement against the page reference at a fixed view
   and tolerance, including masks or repeated streams with different dictionaries.
   Record reference versions, fixture coverage and any mismatch. An extracted
   stream comparison alone cannot establish M10.

---

## 10. Decisions and open questions

**Decided (confirmed by the human, 2026-11-25):**
- Lean 4.36.0, no Lake dependencies (the same toolchain as safe-pdf, so safe-pdf can depend
  on this library without anything transitive); same hygiene rules as safe-pdf's core.
- No floating point; fixed-point lossy paths with proved error bounds.
- Part 1 complete + JP2 + the JPX baseline first; HTJ2K and the rest of Part 2 later.
- Spec-first with per-stage equivalence theorems; a reference encoder for round-trip proofs.
- Strict and lenient modes; lenient is conservative (= strict on valid streams).

**Open — revisit at the marked milestone:**
- *Fixed-point precision for 9/7* (M5): enough fractional bits for the T.803 class
  thresholds at 16-bit depth without `Int64` everywhere.
- *How much of Tier-1 to prove vs test* (M3): the plain mode certainly; bypass mode may be
  staged as tested-then-proved.
- *Licensing of conformance files* (M0): fetch-only unless their licence allows committing.
- *Parallelism granularity* (M8): per code-block tasks may be too fine; batch per precinct
  or per sub-band.
- *Does any PDF producer emit HTJ2K?* (M10): decides whether Part 15 moves up.

---

## 11. Risks

| Risk | Mitigation |
|---|---|
| The Tier-1 equivalence proof is long | Simulation relation designed up front; one mode at a time; tested equivalence first, proof second |
| Lean code too slow in the bit-plane coder | Profile from Phase 2 on; flag-word layout and proved-bounds loops; parallel code-blocks; reduced-resolution decoding for viewers |
| Fixed-point 9/7 misses conformance thresholds | Choose fractional bits from the C8 bound before coding; `Int64` path for high bit depths |
| Real files violate the standard (encoder bugs) | Lenient mode with a conservativity theorem; the PDF corpus decides which deviations to accept, each recorded in `docs/deviations-from-spec.md` |
| Scope creep into Part 2 | The JPX baseline is the line; anything else needs a Decisions entry |
| Conformance data licence | Fetch by hash; commit only manifests |

---

## 12. Repository layout

```
jpeg2000-lean/
  Plan.md  progress.md  CLAUDE.md  README.md
  lakefile.lean  lean-toolchain
  JPEG2000.lean                -- umbrella
  JPEG2000/
    Limits.lean  Error.lean  Bytes.lean (bit/byte readers, Int32 planes)
    Box.lean  Marker.lean  Header.lean
    MQ.lean  Tier1/  Tier2/  TagTree.lean  Progression.lean
    Quant.lean  DWT.lean  MCT.lean  Assemble.lean  Color.lean
    Decode.lean                -- the public API
  Spec/                        -- executable specs + theorems (same rules)
  Encode/                      -- reference encoder (tests and proofs only)
  Tests/  Bench/  Fuzz/
  scripts/                     -- hygiene guard, corpus fetch, differential, benchmarks
  corpus/manifest.json         -- files fetched by SHA-256, git-ignored
  docs/                        -- proof patterns, deviations, performance log
```

---

## 13. How the work runs

The same machinery as safe-pdf: a `CLAUDE.md` with the commands and rules, a `progress.md`
ledger (tasks with `Needs`/`Owns`, gotchas, decisions, log) and the `/next-wave` loop running
parallel subagents in worktrees, one PR per phase. Realistic size: comparable to several
safe-pdf phases — expect on the order of 20–30 waves to M9, with Tier-1 (Phase 3) and
end-to-end equivalence (Phase 7) the longest.

### First steps (Phase 0)

1. Agree this plan (scope, the properties, no-deps/no-float decisions).
2. `CLAUDE.md`, `lean-toolchain`, `lakefile.lean`, hygiene guard and CI copied and adapted
   from safe-pdf.
3. Corpus manifest: T.803 streams + reference decodes, a benchmark set, first JPX images
   extracted from PDFs; fetch script with SHA-256 checks.
4. OpenJPEG baseline timings on the benchmark set → the §6 targets as numbers.
5. Ledger with Phases 1–10 broken into tasks of at most a few files each.
