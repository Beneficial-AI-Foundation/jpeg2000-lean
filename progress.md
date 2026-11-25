# jpeg2000-lean progress ledger

Maintained by `/next-wave`. The orchestrator is the only writer of this file.
Parallel limit: 4
Usage gate: 95%
Design document: Plan.md

## How to read this file
* Status: `todo` · `doing (date)` · `done (date)` · `blocked (why)` · `split (into …)`.
* Needs: task IDs that must be `done` before this one starts.
* Owns: the files or directories this task may create or modify. Tasks whose Owns
  overlap never run in the same wave unless both are `wt`.
* Par: `new` (creates only new files; shared checkout; single-file checks only) ·
  `wt` (edits existing files; own git worktree; builds and tests there) ·
  `solo` (the orchestrator does it alone).
* Later phases are deliberately coarse; each task is split (size check) when its phase
  becomes current. Proof tasks name their theorem IDs from Plan.md §4 (S1–S6, C1–C10).

## Current wave

## Branches and PRs
| Phase | Branch | Base | PR | State |
|---|---|---|---|---|
| 0 | `phase-0-infra` | `origin/main` | [#1](https://github.com/Beneficial-AI-Foundation/jpeg2000-lean/pull/1) | draft |
| 1 | `phase-1-headers` | `phase-0-infra` | — | none |
| 2 | `phase-2-mq` | `phase-1-headers` | — | none |
| 3 | `phase-3-tier1` | `phase-2-mq` | — | none |
| 4 | `phase-4-tier2` | `phase-3-tier1` | — | none |
| 5 | `phase-5-reconstruction` | `phase-4-tier2` | — | none |
| 6 | `phase-6-jp2-output` | `phase-5-reconstruction` | — | none |
| 7 | `phase-7-equivalence` | `phase-6-jp2-output` | — | none |
| 8 | `phase-8-speed` | `phase-7-equivalence` | — | none |
| 9 | `phase-9-hardening` | `phase-8-speed` | — | none |
| 10 | `phase-10-safe-pdf` | `phase-9-hardening` | — | none |
States: none · draft · awaiting-ci · ready (<date>) · changes-requested · merged · closed.

## Phase 0 — Infrastructure
Plan.md §7 row 0, §3 ground rules, §8, §12, §13 "First steps". Exit: **M0**: CI green; `scripts/fetch-corpus.py` verifies every file; OpenJPEG baseline numbers recorded.
| ID | Task | Needs | Owns | Par | Status |
|---|---|---|---|---|---|
| 0.1 | Lake skeleton adapted from safe-pdf: `lean-toolchain` (v4.36.0), `lakefile.lean` (lib `JPEG2000`, lib `Spec`, lib `Encode`, lib `Tests` by globs, exe `tests`; `autoImplicit = false`), umbrella `JPEG2000.lean`/`Spec.lean`/`Encode.lean`, `Tests/Main.lean` runner (suite list, nonzero exit on failure), `.gitignore` (`.lake/`, `corpus/*` except manifest), `CLAUDE.md` (commands, concurrency, registries, conventions, Lean MCP rule, attribution), `.mcp.json` | — | `lean-toolchain`, `lakefile.lean`, `JPEG2000.lean`, `Spec.lean`, `Encode.lean`, `Tests/Main.lean`, `.gitignore`, `CLAUDE.md`, `.mcp.json` | solo | done (2026-11-25) |
| 0.2 | `Limits` (image area, components, tiles, tile-parts, code-blocks, layers, decomposition levels, bytes, per-stage work) with documented defaults, and `Error` (`truncated`, `malformed`, `unsupported`, `limitExceeded`, … with a location/stage) + a unit suite | 0.1 | `JPEG2000/Limits.lean`, `JPEG2000/Error.lean`, `Tests/Basic.lean` | new | done (2026-11-25) |
| 0.3 | Hygiene guard adapted from safe-pdf: forbidden constructs in `JPEG2000/`, `Spec/` (Plan §3 rule 1), `sorry` anywhere; `#print axioms` check over the theorems listed in `scripts/axioms.lean` | 0.1 | `scripts/check-hygiene.sh`, `scripts/hygiene.py`, `scripts/axioms.lean` | new | done (2026-11-25) |
| 0.4 | CI on Linux + macOS: pinned actions and elan, build, tests, hygiene guard, Python lint; corpus fetch + verify as a separate cached job | 0.1 | `.github/workflows/ci.yml` | new | done (2026-11-25) |
| 0.5 | Corpus: `corpus/manifest.json` (T.803 profile-0/1 codestreams + reference decodes from `openjpeg-data`, pinned commit, SHA-256 per file, licence noted; a benchmark set per Plan §8.4), `scripts/fetch-corpus.py` (stdlib only, verifies every hash, `--check`), `docs/corpus.md` (sources, licences, what is committed) | — | `corpus/manifest.json`, `scripts/fetch-corpus.py`, `docs/corpus.md` | new | done (2026-11-25) |
| 0.6 | OpenJPEG baseline: `scripts/bench-openjpeg.sh` (single- and multi-threaded `opj_decompress` timings over the benchmark set, median of N runs, machine info), first numbers recorded in `docs/performance.md` as the Plan §6 targets | 0.5 | `scripts/bench-openjpeg.sh`, `docs/performance.md` | new | | done (2026-11-25) |
| 0.7 | M0 check: CI green on the PR, `fetch-corpus.py --check` passes, baselines in `docs/performance.md` | 0.1–0.6 | — | solo | todo |
Exit criterion checked: [ ]

## Phase 1 — Containers and headers
Plan.md §7 row 1, §3, Annex A/I. Exit: **M1**: every T.803 stream and every corpus file parses to a header identical to OpenJPEG's dump; parse ∘ serialise round trip proved for marker segments.
| ID | Task | Needs | Owns | Par | Status |
|---|---|---|---|---|---|
| 1.1 | (landed on `phase-0-infra`, PR #1) Byte reader (big-endian, bounds-proved), packet-header bit reader with the `0xFF` bit-stuffing rule, `ByteArray`-backed `Int32` plane type with proved-bounds `uget`/`uset` | 0.2 | `JPEG2000/Bytes.lean`, `Tests/Bytes.lean` | new | | done (2026-11-25) |
| 1.2 | JP2/JPX box parser (Annex I): box headers incl. XL boxes, signature/ftyp/jp2h (ihdr, colr, pclr, cmap, cdef, bpcc, res ignored)/jp2c; raw J2K detection | 1.1 | `JPEG2000/Box.lean`, `Tests/Box.lean` | new | todo |
| 1.3 | Main-header marker segments (Annex A): SIZ, COD/COC, QCD/QCC, RGN, POC, COM, CAP/CRG tolerated; typed records | 1.1 | `JPEG2000/Marker.lean`, `Tests/Marker.lean` | new | todo |
| 1.4 | Tile-part markers SOT/SOD/EOC, PPM/PPT/PLT/TLM, tile-part assembly into tiles (Psot=0, out-of-order parts, TNsot) | 1.3 | `JPEG2000/TilePart.lean`, `Tests/TilePart.lean` | new | todo |
| 1.5 | `Header`: main + per-tile headers merged (COD/COC/QCD/QCC precedence, tile overrides), validation against `Limits` before allocation; `parseCodestream` | 1.3, 1.4 | `JPEG2000/Header.lean`, `Tests/Header.lean` | new | todo |
| 1.6 | Marker-segment serialiser (`Encode/Marker.lean`) and the round-trip theorem `parse (serialise m) = m` for every marker segment type (`Spec/MarkerRoundTrip.lean`) | 1.3 | `Encode/Marker.lean`, `Spec/MarkerRoundTrip.lean` | new | todo |
| 1.7 | Header dump exe + `scripts/diff-headers.py` comparing against `opj_dump` on every corpus stream | 1.2, 1.5, 0.5 | `Tests/HeaderDump.lean`, `scripts/diff-headers.py` | new | todo |
| 1.8 | M1 check | 1.1–1.7 | — | solo | todo |
Exit criterion checked: [ ]

## Phase 2 — MQ coder
Plan.md §7 row 2, §5.2 "MQ decoder", Annex C. Exit: **M2**: C1 and C2 proved; 10⁶ random round trips; decoder throughput measured.
| ID | Task | Needs | Owns | Par | Status |
|---|---|---|---|---|---|
| 2.1 | `Spec.MQ`: Qe table (C.2) as data, `INITDEC`/`DECODE`/`RENORMD`/`BYTEIN` transcribed over `Nat`/`List UInt8` with synthetic `0xFF` padding past the end | 0.2 | `Spec/MQ.lean` | new | todo |
| 2.2 | Reference MQ encoder (Annex C encoder flowcharts, `FLUSH`) | 2.1 | `Encode/MQ.lean` | new | todo |
| 2.3 | Fast MQ decoder: `UInt32` `C`/`A`/`CT`, context state array, no GMP, bounded reads | 2.1, 1.1 | `JPEG2000/MQ.lean` | new | todo |
| 2.4 | C1: `mqDecode (mqEncode s) = s` | 2.1, 2.2 | `Spec/MQRoundTrip.lean` | new | todo |
| 2.5 | C2: fast decoder = `Spec.MQ` on every input; termination of `RENORMD` | 2.3 | `Spec/MQEquiv.lean` | new | todo |
| 2.6 | Tests (10⁶ random round trips, fixed vectors) + throughput bench | 2.2, 2.3 | `Tests/MQ.lean`, `Bench/MQ.lean` | new | todo |
| 2.7 | M2 check | 2.1–2.6 | — | solo | todo |
Exit criterion checked: [ ]

## Phase 3 — Tier-1 (EBCOT)
Plan.md §7 row 3, §5.2 "Tier-1", Annex D. Exit: **M3**: C3 proved for plain mode; other modes tested against the spec; code-blocks extracted from T.803 streams decode identically to OpenJPEG.
| ID | Task | Needs | Owns | Par | Status |
|---|---|---|---|---|---|
| 3.1 | Spec context tables D.1–D.3 (zero coding, sign coding, magnitude refinement) as data | 2.1 | `Spec/Tier1/Context.lean` | new | todo |
| 3.2 | Spec Tier-1 decoder, plain mode: per-coefficient state, significance propagation / magnitude refinement / cleanup passes, run-length coding | 3.1 | `Spec/Tier1/Decode.lean` | new | todo |
| 3.3 | Spec modes: reset, termall, vertically causal, segmentation symbols, predictable termination, bypass (raw) | 3.2 | `Spec/Tier1/Modes.lean` | new | todo |
| 3.4 | Fast Tier-1: 32-bit flag word per coefficient, stripe scan, zero-stripe skipping, all modes | 3.2, 2.3 | `JPEG2000/Tier1/` | new | todo |
| 3.5 | Reference Tier-1 encoder, plain mode | 3.2, 2.2 | `Encode/Tier1.lean` | new | todo |
| 3.6 | C3 for plain mode: simulation relation flag words ↔ spec state, preserved by each pass | 3.4 | `Spec/Tier1Equiv.lean` | new | todo |
| 3.7 | Tests: every mode combination fast = spec on random code-blocks; T.803 code-blocks vs OpenJPEG | 3.3, 3.4, 3.5, 4.4 | `Tests/Tier1.lean`, `scripts/diff-codeblocks.py` | new | todo |
| 3.8 | M3 check | 3.1–3.7 | — | solo | todo |
Exit criterion checked: [ ]

## Phase 4 — Tier-2
Plan.md §7 row 4, §5.2 "Tier-2", Annex B. Exit: **M4**: C4, C5 proved; every T.803 stream yields the same per-code-block segments as OpenJPEG.
| ID | Task | Needs | Owns | Par | Status |
|---|---|---|---|---|---|
| 4.1 | Tag trees (B.10.2): decoder, reference encoder, C4 | 1.1 | `JPEG2000/TagTree.lean`, `Spec/TagTree.lean` | new | todo |
| 4.2 | Geometry (B.5–B.7): tile-components, resolutions, sub-bands, precincts, code-blocks, with `Limits` checks | 1.5 | `JPEG2000/Tier2/Geometry.lean` | new | todo |
| 4.3 | Progression orders LRCP/RLCP/RPCL/PCRL/CPRL + POC as explicit iterators; C5 (bijection onto the packet set) | 4.2 | `JPEG2000/Progression.lean`, `Spec/Progression.lean` | new | todo |
| 4.4 | Packet headers (B.10): zero-length packets, inclusion, zero bit-planes, passes, `Lblock`, segment lengths per mode; layer accumulation into per-code-block segments; SOP/EPH | 4.1, 4.2, 4.3 | `JPEG2000/Tier2/Packet.lean` | new | todo |
| 4.5 | PPM/PPT header sourcing and tile-part ordering | 4.4 | `JPEG2000/Tier2/Headers.lean` | new | todo |
| 4.6 | Differential: per-code-block segments vs OpenJPEG on every T.803 stream | 4.5, 0.5 | `Tests/Tier2.lean`, `scripts/diff-segments.py` | new | todo |
| 4.7 | M4 check | 4.1–4.6 | — | solo | todo |
Exit criterion checked: [ ]

## Phase 5 — Reconstruction
Plan.md §7 row 5, §5.2 "DWT", §5.4, Annexes E–H. Exit: **M5**: C6, C7, C8 proved; T.803 profile 0 and 1 pass (reversible bit-exact, irreversible within class thresholds).
| ID | Task | Needs | Owns | Par | Status |
|---|---|---|---|---|---|
| 5.1 | Dequantisation (derived/expounded/none, guard bits) and ROI max-shift | 1.5 | `JPEG2000/Quant.lean`, `Spec/Quant.lean` | new | todo |
| 5.2 | 5/3 inverse DWT: Annex F spec over `Int` with symmetric extension, in-place lifting on `Int32` planes, C6 | 1.1 | `Spec/DWT53.lean`, `JPEG2000/DWT53.lean` | new | todo |
| 5.3 | 9/7 inverse DWT: `Rat` spec, fixed-point lifting (fractional bits chosen from the C8 bound; Plan §10 open question), C8 for DWT | 5.2 | `Spec/DWT97.lean`, `JPEG2000/DWT97.lean` | new | todo |
| 5.4 | RCT/ICT, DC shift, clamping; C7, C8 for ICT | 1.1 | `JPEG2000/MCT.lean`, `Spec/MCT.lean` | new | todo |
| 5.5 | Assembly and pipeline: tiles, sub-sampling, reduced resolution, `JPEG2000.decodeCodestream` | 3.4, 4.5, 5.1–5.4 | `JPEG2000/Assemble.lean`, `JPEG2000/Decode.lean` | new | todo |
| 5.6 | T.803 conformance runner (peak error / MSE per class) | 5.5, 0.5 | `Tests/Conformance.lean`, `scripts/conformance.py` | new | todo |
| 5.7 | M5 check | 5.1–5.6 | — | solo | todo |
Exit criterion checked: [ ]

## Phase 6 — JP2/JPX output
Plan.md §7 row 6, §1 "What we build", Annex I. Exit: **M6**: the JP2 conformance files and the PDF-extracted corpus render identically to OpenJPEG + colour management to within tolerance.
| ID | Task | Needs | Owns | Par | Status |
|---|---|---|---|---|---|
| 6.1 | Colour: enumerated spaces, ICC pass-through, palette (`pclr`), component mapping (`cmap`), channel definitions (`cdef`, alpha) | 1.2 | `JPEG2000/Color.lean` | new | todo |
| 6.2 | Consumer API: `decode : Limits → ByteArray → Except Error Image`, planes + interleaved 8/16-bit, bit-depth scaling, PDF info (`/SMaskInData`) | 5.5, 6.1 | `JPEG2000/Image.lean`, `JPEG2000/Decode.lean` | wt | todo |
| 6.3 | JP2 conformance + PDF-extracted corpus comparison | 6.2, 0.5 | `Tests/JP2.lean`, `scripts/diff-images.py`, `corpus/manifest.json` | wt | todo |
| 6.4 | M6 check | 6.1–6.3 | — | solo | todo |
Exit criterion checked: [ ]

## Phase 7 — Equivalence end to end
Plan.md §7 row 7, §4, §5.3. Exit: **M7**: C9, C10, S2, S3 proved; `#print axioms` clean.
| ID | Task | Needs | Owns | Par | Status |
|---|---|---|---|---|---|
| 7.1 | `Spec.decode` composed from the stage specs; C9 from the stage theorems | 6.2 | `Spec/Decode.lean`, `Spec/Equiv.lean` | new | todo |
| 7.2 | Reference encoder end to end (one tile, one layer, LRCP, plain mode, 5/3 + RCT; 9/7 variant) | 3.5, 4.1, 1.6 | `Encode/Encode.lean` | new | todo |
| 7.3 | C10: `decode (encode img) = img` for the lossless encoder | 7.1, 7.2 | `Spec/RoundTrip.lean` | new | todo |
| 7.4 | S2 totality and S3 resource bounds as theorems over `Limits` | 7.1 | `Spec/Resources.lean` | new | todo |
| 7.5 | M7 check (axioms) | 7.1–7.4 | — | solo | todo |
Exit criterion checked: [ ]

## Phase 8 — Speed
Plan.md §7 row 8, §6. Exit: **M8**: the §6 targets met on the benchmark set, with numbers in the ledger.
| ID | Task | Needs | Owns | Par | Status |
|---|---|---|---|---|---|
| 8.1 | Benchmark harness over the benchmark set vs the 0.6 baselines | 6.2, 0.6 | `Bench/`, `scripts/bench.sh` | new | todo |
| 8.2 | Profile and optimise (split per hot stage when current) | 8.1 | — | wt | todo |
| 8.3 | Parallel code-block / tile decoding with pure `Task`s | 8.1 | `JPEG2000/Parallel.lean` | new | todo |
| 8.4 | M8 check | 8.1–8.3 | — | solo | todo |
Exit criterion checked: [ ]

## Phase 9 — Hardening
Plan.md §7 row 9, §8.6–8.7. Exit: **M9**: no crash or limit escape in N CPU-hours of fuzzing; every CVE-class stream rejected or bounded.
| ID | Task | Needs | Owns | Par | Status |
|---|---|---|---|---|---|
| 9.1 | Fuzz harness (mutation of corpus/T.803 streams, tight and loose `Limits`) | 6.2 | `Fuzz/`, `scripts/fuzz.sh` | new | todo |
| 9.2 | Adversarial stream per OpenJPEG/JasPer CVE class | 6.2 | `Tests/adversarial/`, `Tests/Adversarial.lean` | new | todo |
| 9.3 | Lenient mode + conservativity theorem (lenient = strict on valid streams) | 7.1 | `JPEG2000/Lenient.lean`, `Spec/Lenient.lean` | new | todo |
| 9.4 | Independent kernel re-check (lean4lean, as safe-pdf) | 7.5 | `scripts/lean4lean-check.sh` | new | todo |
| 9.5 | M9 check (fuzz campaign) | 9.1–9.4 | — | solo | todo |
Exit criterion checked: [ ]

## Phase 10 — safe-pdf integration
Plan.md §7 row 10, §9. Exit: **M10**: safe-pdf renders every JPX image of its corpus, matches MuPDF/pdf.js within the image tolerance, no placeholder boxes for JPX.
| ID | Task | Needs | Owns | Par | Status |
|---|---|---|---|---|---|
| 10.1 | Library packaging for consumers (stable API doc, version tag) | 9.5 | `README.md`, `docs/api.md` | new | todo |
| 10.2 | safe-pdf side (separate repo, its own PR): Lake dependency (Decisions entry there), `Quarantine.JPX` adapter, corpus | 10.1 | (safe-pdf) | solo | todo |
| 10.3 | M10 check | 10.2 | — | solo | todo |
Exit criterion checked: [ ]

## Gotchas (append-only; read before every wave, pasted into every brief)
* From safe-pdf (same toolchain, same rules): compiled `<<<` and `^` on `Nat` call GMP — hot code uses `UInt32`/`UInt64`/`Int32`/`Int64` (Plan §6.1).
* Sandbox: egress is limited to GitHub and the Lean release host (+ Debian apt mirrors); loogle/leansearch are blocked — use `lean_local_search` and `exact?`. OpenJPEG tools come from apt (`libopenjp2-tools`).

* A new module importing another new, unbuilt module can't be checked alone with `lake env lean` (missing `.olean`); concatenate the files (drop the `import` lines) into one scratch file and check that.
* `Except` has no `BEq`; tests compare results through a helper like `err? : Except ε α → Option ε`.
* Hygiene guard: every non-private `theorem` in `JPEG2000/` and `Spec/` must be listed in `scripts/axioms.lean` or the guard fails — subagents report the `#print axioms` lines, the orchestrator adds them. `axiom` and `native_decide` are forbidden (in v4.36 `native_decide` adds `<thm>._native.native_decide.ax_1_1`). `lake env lean` exits 0 on `sorry` (warning only); the axioms parse is what catches it.
* Lean MCP (`lean_*`) tools were not available to subagents in this session (server not registered for this checkout yet); they fall back to `lake env lean`.
* Corpus: raw.githubusercontent.com and `gh api` work through the sandbox proxy. `p0_03` = `p0_15` byte-identical (T.803 erratum); `p0_13` has 257 components (OpenJPEG compares only 4). Class-0 thresholds in OpenJPEG's conformance CMake are commented out (it only runs class 1).

* OpenJPEG bench: `.raw` output is refused for sub-sampled streams (`p1_03`); `scripts/bench-openjpeg.sh` falls back to `.tif` then `.pgx`. `exec python3` at a script's end skips its `trap` cleanup — call it plainly. `lscpu` shows no model name in this VM (aarch64, 8 cores).
* Lean v4.36 `ByteArray`: `uget` needs `i.toNat < a.size` on `USize` and core has no `ByteArray.size < USize.size` lemma, so `Plane` uses `get`/`set` with `Nat` index + proof (compiled to unchecked `fget`/`fset`). Core lacks `ByteArray.size_set`/`get_set`/`getElem_push`: prove via `cases a; simp [ByteArray.set, ByteArray.size]` + `Array.getElem_set`/`Array.getElem_push`. `(ByteArray.emptyWithCapacity n).size = 0` is `rfl`.
* Byte split/join proofs: `UInt32.toNat_inj.mp`, then `simp [UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow]`, then `omega`; write constants as `(256 : UInt32)`. Combining bytes with `+`/`*` (not `|||`/`<<<`) keeps proofs in `omega`.
* `if_pos`/`if_neg`/`dif_pos`/`if_true` are deprecated in v4.36: use `↓reduceIte`/`↓reduceDIte` or `simp (disch := omega)`. `bv_decide` is unusable (relies on `Lean.ofReduceBool`).
* `JPEG2000.Bytes.BitReader` (B.10.1): after `0xFF` the next byte gives 7 bits; `align` after a `0xFF` byte also consumes the stuffed byte (as `opj_bio_inalign`); reading past the end is `truncated` (OpenJPEG reads zeros).

## Decisions and deviations from the design document
* 0.1: three libraries (`JPEG2000`, `Spec`, `Encode`) with one umbrella each, all default targets; `Tests` is a separate lib built only via `lake build tests`. `.mcp.json` pins `lean-lsp-mcp==0.33.0` with `lean_build` disabled (as bib-lean).

* 0.2: `Error.Stage` gains `decode` (argument checks before any stage). Defaults that are judgement calls, not T.800 bounds: image side 2^17, 2^22 code-blocks/precincts, 255 passes per code-block, box nesting 8 — revisit against the corpus.
* 0.3: the guard also forbids `axiom` declarations and `native_decide`, and fails on unlisted theorems in `JPEG2000/`, `Spec/` (not `Encode/`).
* 0.5 (Plan §10 open question "Licensing of conformance files", resolved for M0): fetch-only. The T.803 files carry a 2002 non-assertion notice limited to conformance testing (not an open licence; `COPYRIGHT` is fetched alongside); openjpeg-data nonregression files have no stated licence. Only `corpus/manifest.json` is committed. Source pinned at `uclouvain/openjpeg-data@39524bd`, thresholds from `uclouvain/openjpeg@8314119` `tests/conformance/CMakeLists.txt`.

* 1.1: `Plane` cells via `ByteArray.get`/`set` with proofs, not `uget`/`uset` (Plan §6.2 says `uget`/`uset`); revisit in Phase 8 with a `data.size < USize.size` invariant if profiling shows it matters.
* 0.6: OpenJPEG baseline times include process start-up and output write (no decode-only flag); see `docs/performance.md`.

## Blocked / questions for the human

* Benchmark set (Plan §8.4) lacks a ≥ 20 Mpx stream: openjpeg-data has none that decodes. Where may one come from (a licensable large JP2, or one we generate with `opj_compress` from a public-domain image)? Proceeding with the 15-file set meanwhile.

## Log (append-only; one line per integrated wave)
* 2026-11-25 — wave 0 (phase 0, PR #1): ledger bootstrapped from Plan.md §7; draft PR #1 opened; commit "wave 0: ledger"
* 2026-11-25 — wave 1 (phase 0, PR #1): 0.1 done (solo: Lake skeleton, CLAUDE.md, test runner; `lake build && lake build tests && lake exe tests` green); commit "wave 1: 0.1 — Lake skeleton and CLAUDE.md"
* 2026-11-25 — wave 2 (phase 0, PR #1): 0.2, 0.3, 0.4, 0.5 done (Limits/Error + 4 theorems, hygiene guard, CI Linux+macOS, corpus 132 files verified); commit "wave 2: 0.2–0.5 — limits, guard, CI, corpus"
* 2026-11-25 — wave 3 (phase 0, PR #1): 0.6 done (OpenJPEG 2.5.3 baseline, 15/15 files), 1.1 done (Bytes: Reader/BitReader/Plane, 20 theorems; landed on phase-0 branch); commit "wave 3: 0.6, 1.1 — OpenJPEG baseline, byte/bit readers"
