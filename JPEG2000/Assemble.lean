import JPEG2000.Tier2.Headers
import JPEG2000.Tier1.Modes
import JPEG2000.Quant
import JPEG2000.DWT53
import JPEG2000.DWT97
import JPEG2000.MCT

/-!
# Per-tile reconstruction: Tier-1 → dequantisation → inverse DWT → MCT → DC shift
(Plan.md §3 "Assemble", §6 item 7 (reduced resolution); T.800 B.3, B.5, B-12, B-14, Annex D,
E.1, F.3.1, G.1–G.3, H)

Task 5.5. The stages of the pipeline communicate through plain data (Plan.md §3):

1. **Tier-2** (`Tier2.Headers.headerStreamAt` + `decodeWithStream`, task 4.5) gives every
   code-block of a tile with its zero bit-planes, passes and codeword segments (lists of
   absolute byte ranges of the input).
2. **Tier-1** (`Tier1.decodeCodeBlockSegs`, task 3.4b) per code-block, with
   `numBitPlanes = Mb + roiShift` (E-2 plus the ROI shift, Annex H) and the tag-tree zero
   bit-planes. Segments held in one range point straight into the input; when some segment
   of a code-block spans several ranges (several packets or tile-parts), all segments of
   that code-block are concatenated into a fresh buffer (`tier1Input`). Code-blocks with no
   coding pass are skipped: their coefficients are 0 and dequantise to 0.
3. **Dequantisation** (`Quant.dequantBlock`, task 5.1) writes each code-block into the
   tile-component plane in the Mallat layout of `JPEG2000.DWT53` (ROI unshift included).
   Irreversible components use `F` fractional bits (`DWT97.fracBits depth = 26 − depth`).
4. **Inverse DWT** (`DWT53.idwt53` for the 5/3 reversible transform, `DWT97.idwt97` for the
   9/7) with the tile-component's `NL` (minus the reduction).
5. **Inverse MCT** (`MCT.rctInverse` / `MCT.ictInverse`, G.2/G.3) on components 0–2 when
   `Coding.mctApplies` (the header validated equal sub-sampling and transform on them). With
   the ICT the three components share one `F`: `fracBits` of their largest depth.
6. **DC shift and clamp** (`MCT.dcShiftClampRev` / `dcShiftClampIrrev`, G.1; the latter
   also rounds the fixed point).

## Reduced resolution (Plan.md §6 item 7)

With `reduce = k` only resolutions `0 … NL − k` are used: the tile-component plane is the
resolution-`(NL − k)` rectangle `⌈tc / 2^k⌉` (B-14) and the inverse DWT runs `NL − k`
levels on it. This is consistent with the Mallat layout of the full plane: the band
rectangles of `⌈tc / 2^k⌉` at level `nb − k` equal those of `tc` at level `nb` (nested
ceilings, B-15), and code-block rectangles are in band coordinates. Tier-2 still parses
every packet (it must, to find the later packets); Tier-1 skips the discarded code-blocks.
`k > NL` for some tile-component is an error (`unsupported`; OpenJPEG also refuses a
reduction of at least the number of resolutions).

## Missing tiles

A tile without tile-parts (T.800 allows it; `Header.tiles` lists only present tiles) is
reconstructed from zero coefficients with the main-header parameters: every sample is the
DC offset (mid-grey for unsigned components, 0 for signed), as OpenJPEG.

## Limits (Plan.md §3 rule 3)

Every tile-component plane goes through `Plane.zeroChecked` (`maxWorkSamples`), and the
sum over the components of a tile is checked as well; code-block planes are at most
2^12 cells (T.800 code-block size bound, enforced by the header parser). All loops are
`for` over bounded ranges/arrays or structural recursion on a count.
-/

namespace JPEG2000.Assemble

open JPEG2000 JPEG2000.Bytes JPEG2000.Marker JPEG2000.Header JPEG2000.TilePart JPEG2000.Tier2.Geometry
  JPEG2000.Tier2.Packet

/-- The error location of this module. -/
def loc : Location := .at .assemble

/-- A rectangle at resolution reduction `k`: every coordinate `⌈· / 2^k⌉` (B-14). -/
def reduceRect (r : Rect) (k : Nat) : Rect :=
  { x0 := cdivPow r.x0 k, y0 := cdivPow r.y0 k, x1 := cdivPow r.x1 k, y1 := cdivPow r.y1 k }

/-! ## Tier-1 input -/

/-- A Tier-1 segment for a segment held in at most one range of `data` (an empty segment
gives an empty range). -/
def directSeg (s : Segment) : Tier1.Seg :=
  match s.ranges[0]? with
  | some r => { start := r.offset, stop := r.offset + r.length, passes := s.passes }
  | none => { start := 0, stop := 0, passes := s.passes }

/-- The buffer and Tier-1 segments of a code-block: the input itself when every segment is
held in one range, otherwise a fresh buffer with all segments concatenated
(`Segment.bytes`). -/
def tier1Input (data : ByteArray) (cb : CodeBlock) : ByteArray × Array Tier1.Seg :=
  if cb.segments.all (·.ranges.size ≤ 1) then (data, cb.segments.map directSeg)
  else
    cb.segments.foldl (fun (acc : ByteArray × Array Tier1.Seg) s =>
      let bs := s.bytes data
      let off := acc.1.size
      (acc.1 ++ bs, acc.2.push { start := off, stop := off + bs.size, passes := s.passes }))
      (ByteArray.empty, #[])

/-- Tier-1 decoding of one code-block of band `b` of resolution `r` of a tile-component with
parameters `p`: `Mb + roiShift` bit-planes, the tag-tree zero bit-planes (0 if never
included). -/
def decodeBlock (data : ByteArray) (p : CompParams) (r : Nat) (b : Band) (cb : CodeBlock) :
    Except Error Tier1.CodeBlockOut :=
  let rc := cb.geom.rect
  let (buf, segs) := tier1Input data cb
  let zbp := if cb.included then cb.zeroBitPlanes else 0
  Tier1.decodeCodeBlockSegs buf segs rc.width rc.height b p.cbStyle
    (bandMb p r b + p.roiShift) zbp

/-! ## One tile-component: coefficients → samples before the MCT -/

/-- Reconstructs one tile-component up to (and including) the inverse DWT: Tier-1 on every
code-block of resolutions `0 … NL − reduce` (`precs[r][k]` from Tier-2; empty for a missing
tile), dequantisation into the plane of `reduceRect tc.rect reduce` (`F` fractional bits
when irreversible), inverse 5/3 or 9/7 with `NL − reduce` levels. Returns the plane and the
number of code-blocks in which dequantisation saturated. -/
def reconstructTileComp (L : Limits) (data : ByteArray) (tc : TileCompGeom) (depth F reduce : Nat)
    (precs : Array (Array PrecinctOut)) : Except Error (Plane × Nat) := do
  let p := tc.params
  let nl := p.levels
  if reduce > nl then
    throw (.unsupported loc
      s!"resolution reduction {reduce} exceeds the {nl} decomposition levels of a tile-component")
  let nl' := nl - reduce
  let rect := reduceRect tc.rect reduce
  let mut plane ← Plane.zeroChecked L loc rect.width rect.height
  let mut sat := 0
  for r in [0:min (nl' + 1) precs.size] do
    let ps := precs.getD r #[]
    for prec in ps do
      for bo in prec.bands do
        for cb in bo.blocks do
          if cb.numPasses != 0 && !rectEmpty cb.geom.rect then
            let o ← decodeBlock data p r bo.band cb
            let q := Spec.Quant.bandQuant p depth r bo.band
            let (pl, ok) ← Quant.dequantBlock plane rect nl' r bo.band cb.geom.rect q F o
            plane := pl
            if !ok then sat := sat + 1
  let out ← if p.transform == .reversible53 then DWT53.idwt53 plane rect nl'
    else DWT97.idwt97 plane rect nl'
  return (out, sat)

/-! ## Copying a tile-component into a component plane -/

/-- Copies `k` cells from index `si` of `src` to index `di` of `dst` (cells out of range are
skipped; the caller checks the geometry). -/
def blitRow (src : Plane) : Nat → Nat → Nat → Plane → Plane
  | 0, _, _, dst => dst
  | k + 1, si, di, dst =>
    let dst :=
      if h1 : si < src.width * src.height then
        if h2 : di < dst.width * dst.height then dst.set di (src.get si h1) h2 else dst
      else dst
    blitRow src k (si + 1) (di + 1) dst

/-- Copies rows `y, y + 1, …` (`k` of them) of `src` to `dst` at offset `(ox, oy)`. -/
def blitRows (src : Plane) (ox oy : Nat) : Nat → Nat → Plane → Plane
  | 0, _, dst => dst
  | k + 1, y, dst =>
    let dst := blitRow src src.width (y * src.width) ((oy + y) * dst.width + ox) dst
    blitRows src ox oy k (y + 1) dst

/-- Copies the whole of `src` into `dst` with its top-left cell at `(ox, oy)`; `malformed`
when it does not fit. -/
def blit (dst src : Plane) (ox oy : Nat) : Except Error Plane :=
  if ox + src.width ≤ dst.width ∧ oy + src.height ≤ dst.height then
    .ok (blitRows src ox oy src.height 0 dst)
  else .error (.malformed loc
    s!"tile-component {src.width}×{src.height} at ({ox}, {oy}) outside the component plane {dst.width}×{dst.height}")

/-! ## One tile -/

/-- A reconstructed tile: per component, its samples on the component grid (DC-shifted and
clamped) and the rectangle they cover there (at the resolution reduction). -/
structure TileOut where
  /-- Tile index. -/
  tile : Nat
  /-- Per component: the rectangle (component grid, reduced) and its samples. -/
  comps : Array (Rect × Plane)
  /-- Code-blocks whose dequantisation saturated to `Int32` (0 for valid streams). -/
  saturated : Nat

/-- The fractional bits of component `c`'s irreversible path: `fracBits` of its depth, or of
the largest depth of components 0–2 when they are combined by the ICT. -/
def fracBitsOf (s : SIZ) (mct : Bool) (c : Nat) : Nat :=
  let d := fun i => (s.components.getD i default).depth.toNat
  if mct ∧ c < 3 then DWT97.fracBits (max (d 0) (max (d 1) (d 2)))
  else DWT97.fracBits (d c)

/-- Applies the inverse RCT/ICT (G.2/G.3) to planes 0–2 (the transform of component 0). -/
def inverseMct (rev : Bool) (planes : Array Plane) : Except Error (Array Plane) := do
  let z := Plane.zero 0 0
  let p0 := planes.getD 0 z
  let p1 := planes.getD 1 z
  let p2 := planes.getD 2 z
  let planes := ((planes.setIfInBounds 0 z).setIfInBounds 1 z).setIfInBounds 2 z
  let (q0, q1, q2) ← if rev then MCT.rctInverse p0 p1 p2 else MCT.ictInverse p0 p1 p2
  return ((planes.setIfInBounds 0 q0).setIfInBounds 1 q1).setIfInBounds 2 q2

/-- **Reconstructs tile `t`** from its Tier-2 result (`none` for a tile without tile-parts:
all coefficients zero): per component `reconstructTileComp`, then the inverse MCT when
`Coding.mctApplies`, then DC shift and clamp per component (G.1). -/
def decodeTile (L : Limits) (h : Header) (data : ByteArray) (t : Nat) (reduce : Nat)
    (tcb : Option TileCodeBlocks) : Except Error TileOut := do
  let (g, coding) ← Progression.Layout.ofHeader h t
  let s := h.siz
  let mct := coding.mctApplies s
  -- Work memory of the tile: every tile-component plane is held until the MCT.
  let cells := g.comps.foldl (fun a tc => a + (reduceRect tc.rect reduce).width *
    (reduceRect tc.rect reduce).height) 0
  L.check loc .workSamples cells
  let mut planes : Array Plane := #[]
  let mut sat := 0
  for c in [0:g.numComps] do
    let tc := g.comp c
    let comp := s.components.getD c default
    let precs := match tcb with
      | some x => x.comps.getD c #[]
      | none => #[]
    let (pl, n) ← reconstructTileComp L data tc comp.depth.toNat (fracBitsOf s mct c) reduce precs
    planes := planes.push pl
    sat := sat + n
  if mct then
    planes ← inverseMct ((g.comp 0).params.transform == .reversible53) planes
  let mut out : Array (Rect × Plane) := #[]
  for c in [0:g.numComps] do
    let tc := g.comp c
    let comp := s.components.getD c default
    let rev := tc.params.transform == .reversible53
    let F := if rev then 0 else fracBitsOf s mct c
    let dc ← MCT.DcShift.make comp.signed comp.depth.toNat F
    let pl := planes.getD c (Plane.zero 0 0)
    planes := planes.setIfInBounds c (Plane.zero 0 0)
    let pl := if rev then MCT.dcShiftClampRev dc pl else MCT.dcShiftClampIrrev dc pl
    out := out.push (reduceRect tc.rect reduce, pl)
  return { tile := t, comps := out, saturated := sat }

end JPEG2000.Assemble
