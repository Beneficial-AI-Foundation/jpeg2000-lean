# S2 (totality) and S3 (bounded resources): what is proved

Task 7.4 (Plan.md §4 S2, S3; §3 rules 2–3). Theorems are in `Spec/Resources.lean`
(namespace `JPEG2000.Spec.Resources`). Every theorem depends only on `propext`,
`Classical.choice`, `Quot.sound`.

## S2 — totality

> `decode` is a total function, accepted by the termination checker, on every byte string.

In Lean every `def` the kernel accepts denotes a total function, so the literal statement
(`decode_total : ∀ L data opts, ∃ r, decode L data opts = r`) is proved by `⟨_, rfl⟩` and
carries no information. S2's real content is that **the kernel definition is what runs** and
that it is a genuine definition:

| Obligation | How it is discharged |
|---|---|
| No `partial` (opaque constant with a hidden recursive implementation), `unsafe`, `implemented_by`, `extern` in the decoder | `scripts/hygiene.py` (textual, every file under `JPEG2000/`, `Spec/`, `Encode/`); and the closure audit below (semantic, on the constants `decode` actually uses) |
| No `panic!`, `get!`, `xs[i]!` | `scripts/hygiene.py` |
| No `sorry` in the definitions | `#print axioms JPEG2000.decode` and `#print axioms JPEG2000.decodeCodestream` print `[propext, Classical.choice, Quot.sound]` (`#print axioms` works on definitions; add both lines to `scripts/axioms.lean`) |
| Every loop terminates | kernel: structural recursion or fuel; each fuel is a size already checked against `Limits` (Plan.md §3 rule 2) |

**Closure audit** (run 2026-11-25, scratch file, `lake env lean`): walking the types and
values of all constants reachable from `JPEG2000.decode` (3236 constants, 1843 in
`JPEG2000.*`), there is no `unsafe` constant, and no project constant that is opaque
(`partial`), `implemented_by` or `extern`, apart from the compiler-generated `T.ctorIdx` of
enumerations (6 of them, `implemented_by T.toCtorIdx` by Lean itself). The only opaque constant
in the closure is core's `String.Internal.append` (error messages). Same result for
`decodeCodestream` (2950), `Image.interleaved8/16` (584 each). A self-test with a `partial def`
in `JPEG2000.*` is reported. Proposed as a guard (`scripts/closure.lean`, outside the
libraries, run like `scripts/axioms.lean`; `partial` is fine there):

```lean
import JPEG2000
import Lean
open Lean Elab Command

partial def reach (env : Environment) (todo : List Name) (seen : NameSet) : NameSet :=
  match todo with
  | [] => seen
  | n :: rest =>
    if seen.contains n then reach env rest seen
    else
      let seen := seen.insert n
      match env.find? n with
      | none => reach env rest seen
      | some ci =>
        let cs := ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants) |>.getD #[])
        reach env (cs.toList ++ rest) seen

elab "#check_closure " id:ident : command => do
  let env ← getEnv
  let all := reach env [id.getId] {}
  let mut bad : Array String := #[]
  for n in all.toList do
    let some ci := env.find? n | continue
    if ci.isUnsafe then bad := bad.push s!"unsafe {n}"
    if n == ``sorryAx then bad := bad.push "sorryAx"
    -- `T.ctorIdx` of an enumeration is compiler-generated (implemented_by `T.toCtorIdx`)
    if (`JPEG2000).isPrefixOf n && n.getString! != "ctorIdx" then
      if (Compiler.implementedByAttr.getParam? env n).isSome then bad := bad.push s!"implemented_by {n}"
      if isExtern env n then bad := bad.push s!"extern {n}"
      if ci matches .opaqueInfo _ then bad := bad.push s!"opaque/partial {n}"
  if bad.isEmpty then logInfo m!"{id.getId}: closure OK ({all.size} constants)"
  else logError m!"{id.getId}: {bad}"

#check_closure JPEG2000.decode
#check_closure JPEG2000.Image.interleaved8
#check_closure JPEG2000.Image.interleaved16
```

## S3 — bounded resources

> Output size, intermediate allocation and work are bounded by explicit functions of `Limits`
> and the input length; excess is `Error.limitExceeded`.

All S3 theorems are about a successful run and bound **the quantities the code checks**; the
headline ones:

| Quantity | Bound | Theorem |
|---|---|---|
| input length | `maxInputBytes` | `parse_within`, `decode_size` |
| image side, area, tiles, `tiles × Csiz`, declared samples / output bytes | `maxImageSide`, `maxImageArea`, `maxTiles`, `maxCodeBlocks`, `maxWorkSamples`, `maxDecodedBytes` | `checkGeometry_ok_iff` (`GeometryWithin`), `parse_within` |
| code-blocks, precincts, packets of the whole tile grid (exact totals, `Header.checkWork`) | `maxCodeBlocks`, `maxPrecincts`, `maxPackets` | `checkWork_within` |
| `reduce` | `maxDecompLevels` | `decodeCodestream_resources` |
| output component planes (cells / bytes at `bytesPerSample`); each plane exactly `width × height` | `maxWorkSamples` / `maxDecodedBytes` | `allocOutput_ok`, `decodeCodestream_resources` |
| `decode`: image area | `maxImageArea` | `decode_resources`, `decode_size` |
| `decode`: up-sampled channels (fresh cells / bytes; every channel, alpha and other channel is one of them, `w × h`) | `maxWorkSamples` / `maxDecodedBytes` | `decode_resources` (`ImageWithin`) |
| interleaved 8/16-bit buffer (exact size `w·h·n·(1|2)`) | `maxDecodedBytes` | `interleave_size`, `interleaved8_size`, `interleaved16_size` |
| per tile: all tile-component planes held until the MCT; each tile-component plane | `maxWorkSamples` | `decodeTile_work`, `reconstructTileComp_work` |
| per tile: packet iteration work (`iterationWork`, ≥ packets visited) | `maxPackets` | `decodeTilePacketsWith_ok`, `decodeWithStream_ok` |
| coding passes of all tiles | `maxCodingPasses` | `decodeAllTileCodeBlocks_passes` |

**Excess ⇒ `limitExceeded`.** `checkGeometry_limitOnly`: the geometry check fails only with
`limitExceeded` (value > bound). `decode_limitExceeded_of_geometry` (and the `_of_area`,
`_of_bytes` corollaries): if the container (`Box.parseFile`) and the main header
(`parseMainHeader`) parse and the declared geometry violates `GeometryWithin` — e.g. area >
`maxImageArea` or declared output bytes > `maxDecodedBytes` — then `decode L data opts =
.error (.limitExceeded loc k v b)` with `b < v`, for every `opts`. The precondition is needed:
a stream malformed before the end of its main header fails with `malformed`/`truncated`
first. (A too-large `reduce` is also `limitExceeded`, checked first.)

### Robustness to task 6.5

The statements name checked quantities (`GeometryWithin` mirrors `checkGeometry`;
`allocOutput_ok` the reduced output grids; `tileCells` the per-tile set), so when 6.5 changes
*what* is checked (reduced grids, per-tile working sets) the statements keep their shape, but
the proofs unfold `decodeCodestream`, `Decode.allocOutput`, `decode`, `Assemble.decodeTile`,
`reconstructTileComp`, `Header.checkGeometry`/`checkWork`, `Tier2.Packet.decodeTilePacketsWith`
and `Tier2.Headers.decodeAllTileCodeBlocks`: an edit there must re-check
`lake env lean Spec/Resources.lean` (as with the C9 skeletons). If 6.5 drops the full-resolution
`workSamples`/`decodedBytes` checks from `checkGeometry`, `GeometryWithin` must drop them too
(and `decode_limitExceeded_of_bytes` would then rest on `allocOutput`'s check instead).

### Not proved (gaps, stated precisely)

1. **Work as a step count.** Lean has no cost semantics, so "work ≤ f(Limits, input length)"
   needs instrumentation. Proposed formulation: make the hot loops monad-generic (as
   `Progression.forPackets` already is) and run them in `CountM := StateT Nat (Except Error)`
   with a `tick` per unit of work (packet, coding pass × code-block cell, DWT lifting step per
   cell, MCT/up-sampling per cell, output byte); prove the instrumented decoder equals the
   plain one after erasing ticks, and
   `ticks ≤ c₁·maxPackets + c₂·4096·maxCodingPasses + c₃·(maxDecompLevels+1)·maxWorkSamples·maxTiles' + c₄·maxDecodedBytes + c₅·data.size`
   (packets, Tier-1 with ≤ 4096 cells per code-block, DWT per tile, colour/interleave, byte
   readers). Needed: the per-stage bounds (Tier-1 work per pass ≤ code-block cells; DWT levels
   ≤ `maxDecompLevels`; packet header bytes ≤ input length) and the loop-bound lemmas already
   used here (`forPackets_inv`, `forIn_inv`).
2. **Whole-image passes in `decodeCodestream`**: its running pass count is not returned
   (`DecodedImage` has no `passes` field), so only the per-tile statement
   (`decodeWithStream_ok` with `passesBefore` = earlier tiles) and the Tier-2 driver
   (`decodeAllTileCodeBlocks_passes`) are proved. Adding the count to `DecodedImage` (6.5
   touches `Decode.lean`) would make the image-wide bound a short loop-invariant proof.
3. **`maxPassesPerCodeBlock` is never checked** (only declared in `Limits`/`LimitKind`):
   per-code-block passes are bounded only through `maxCodingPasses` and Tier-1's bit-plane
   limits. Either check it in Tier-2 (`decodePacket`) or remove the field (Decisions entry).
4. Not stated here: `Box` limits (`maxBoxes`, `maxBoxDepth`, `maxPaletteEntries`), `Color`
   palette/sYCC planes, Tier-1 concatenated segment buffers (`Assemble.tier1Input`, bounded by
   the input length), `TagTree`/`Geometry` per-band checks, `ppmChunkIndex`. Each is checked in
   code; the theorems would follow the same pattern (`bind_ok` + `check_ok`).
5. Excess ⇒ `limitExceeded` is proved for the geometry checks only; for later checks
   (work totals, per-tile planes, passes) another error may legitimately come first.
