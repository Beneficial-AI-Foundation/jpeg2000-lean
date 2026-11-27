import JPEG2000.Assemble
import JPEG2000.Tier1.WideSegments
import JPEG2000.WideQuant

/-!
# Wide tile-component coefficients (Plan.md §§4, 5.1, 5.4, 7; T.800 B.6–B.10, D, E, H)

The packet store supplies the codeword and band geometry. One checked, zero-initialised
Mallat plane is threaded through the retained code-blocks up to the inverse DWT boundary.
-/

namespace JPEG2000.WideAssembly

open Header Tier2.Geometry Tier2.Packet

/-- Gather the packet pieces in codeword order and decode their exact pass counts in
the signalled style. Check the original ranges before gathering a fragmented segment. -/
def decodeBlock (data : ByteArray) (p : CompParams) (r : Nat) (b : Band) (cb : CodeBlock) :
    Except Error (Array Tier1.WidePlain.Cell) := do
  if !cb.segments.all (fun s => s.ranges.all (fun rg => rg.offset + rg.length ≤ data.size)) then
    throw (.malformed Tier1.tier1Loc "code-block data range outside the buffer")
  let (buf, segs) := Assemble.tier1Input data cb
  Tier1.WideSegments.decodeCodeBlockSegs buf segs cb.geom.rect.width cb.geom.rect.height b
    p.cbStyle (bandMb p r b + p.roiShift) (if cb.included then cb.zeroBitPlanes else 0)

/-- Traverse retained packet blocks in the order of tile reconstruction. Missing precincts,
empty rectangles and blocks without coding passes leave the accumulator untouched. -/
@[inline] def visitBlocks {α : Type} (nl : Nat) (precs : Array (Array PrecinctOut)) (init : α)
    (step : α → Nat → Band → CodeBlock → Except Error α) : Except Error α := do
  let mut acc := init
  for r in [0:min (nl + 1) precs.size] do
    for prec in precs.getD r #[] do
      for bo in prec.bands do
        for cb in bo.blocks do
          if cb.numPasses != 0 && !rectEmpty cb.geom.rect then
            acc ← step acc r bo.band cb
  return acc

/-- Wide coefficient assembly for one component of the parsed Tier-2 tile store.
`F` is the tile's irreversible working precision. The reversible kernel uses integers.
The returned rectangle, level count `tc.params.levels - reduce` and sample array are the
inputs to the inverse wavelet transform. -/
def tileComp (L : Limits) (data : ByteArray) (tc : TileCompGeom) (depth F reduce : Nat)
    (precs : Array (Array PrecinctOut)) : Except Error WideQuant.Plane := do
  let p := tc.params
  if reduce > p.levels then
    throw (.unsupported Assemble.loc
      s!"resolution reduction {reduce} exceeds the {p.levels} decomposition levels of a tile-component")
  L.check Assemble.loc .decompLevels p.levels
  let rect := Assemble.reduceRect tc.rect reduce
  L.check Assemble.loc .workSamples (rectArea rect)
  let plane ← WideQuant.zeroChecked L rect
  visitBlocks (p.levels - reduce) precs plane fun dst r b cb => do
    let cells ← decodeBlock data p r b cb
    WideQuant.dequantBlock L dst p depth reduce r b cb.geom.rect F cells

/-- Select the component and its packets from the parsed tile layout. A missing tile has
an empty packet store. Components participating in the ICT share the working precision
of their largest depth, as in the tile reconstruction loop. -/
def component (L : Limits) (data : ByteArray) (siz : Marker.SIZ) (layout : Progression.Layout)
    (coding : Coding) (store : Option TileCodeBlocks) (c : Fin layout.numComps) (reduce : Nat) :
    Except Error WideQuant.Plane :=
  let tc := layout.comp c
  let depth := (siz.components.getD c default).depth.toNat
  let F := Assemble.fracBitsOf siz (coding.mctApplies siz) c
  let precs := match store with
    | some tile => tile.comps.getD c #[]
    | none => #[]
  tileComp L data tc depth F reduce precs

end JPEG2000.WideAssembly
