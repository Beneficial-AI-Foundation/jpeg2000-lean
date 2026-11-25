import JPEG2000.Decode
import Spec.Tier1Equiv

/-!
# `Spec.decode`: the end-to-end specification decoder

Plan.md §4 (C9: "end to end, `decode = Spec.decode`"), §5.1 (two implementations per stage,
equivalence theorems composed into C9); T.800 Annex B (B.3, B-12, B-14, B.10), Annex D,
Annex E (E.1.1.2), Annex F (F.3.1), Annex G (G.1–G.3), Annex H. Task 7.1a.

`Spec.Decode.decode L data reduce` decodes a codestream with the **specification** of every
stage that has one, composed in the order of the fast decoder `JPEG2000.decodeCodestream`:

| stage | what `Spec.decode` uses |
|---|---|
| headers (Annex A) | the fast `Header.parse` — it *is* the header spec: its correctness story is the marker-segment round trips (`Spec.MarkerRoundTrip`, `Spec.TilePartRoundTrip`, C-level `parse ∘ serialise = id`); no second header parser is written |
| output geometry, limits | `Decode.allocOutput` (B-12/B-14 rectangles and the S3 limit checks; no samples) |
| Tier-2 (B.9–B.12) | **placeholder** `Tier2Spec` = the fast `Tier2.Headers.decodeWithStream` and the fast segment gathering; task 7.1b replaces the two definitions of `namespace Tier2Spec` by a spec over bit lists (the rest of this file only uses `Tier2Spec.decode` and `Tier2Spec.segments`) |
| Tier-1 (Annex D) | `Spec.Tier1.decodeCodeBlock` (every code-block style, `Mode.ofStyle`) |
| dequantisation, ROI (E.1.1.2, H) | `Spec.Quant.dequantRev` / `dequantIrrev` (exact `Int` / `Rat`) |
| sub-band grids | each code-block's dequantised coefficients at its band coordinates (`bandGrid`) |
| inverse DWT (F.3.1) | `Spec.DWT53.srMulti` over `Int` (5/3), `Spec.DWT97.srMulti` over `Rat` (9/7) |
| inverse MCT (G.2, G.3) | `Spec.MCT.rctInv` (`Int`), `Spec.MCT.ictInv` (`Rat`) |
| DC shift, clamp (G.1) | `Spec.MCT.reconRev`; irreversible: round half up (`roundHalf`) then `reconRev` |

## Shape: shared pipeline skeletons

The composition is written as three **skeletons** — `codestreamWith`, `tileWith`,
`tileCompWith` — which are the fast decoder's own control flow (`decodeCodestream`,
`Assemble.decodeTile`, `Assemble.reconstructTileComp`, copied verbatim) with every stage
call turned into a parameter. Instantiated with the fast stages they are *definitionally*
the fast decoder (`Spec.Equiv.*_eq_with`, proved by `rfl`); instantiated with the spec stages
below they are `Spec.decode`. So the two decoders iterate the same tiles, components,
resolutions, precincts, bands and code-blocks in the same order and make the same limit and
geometry checks; they differ exactly in the stages. That is what makes C9 a composition of
one equivalence per stage (`Spec/Equiv.lean`).

## Output

Per component, on its own grid (as `DecodedImage`), one `SpecSample` per sample: the final
integer sample (`value`), the exact value before rounding and DC shift (`exact`: an integer
for the reversible path, a rational for the irreversible one), and a small **trace** used to
state C9 (`peers`: the inverse-DWT outputs the sample was computed from; `levels`: their
decomposition levels; `mct`: an inverse component transform was applied). Samples not
covered by any tile keep `SpecSample.blank` (value 0, as the fast decoder's zero planes).

Executable but slow (functions as grids, lists of code-blocks searched per coefficient):
meant for tiny streams (`Tests/SpecDecode.lean`).
-/

namespace JPEG2000.Spec.Decode

open JPEG2000 JPEG2000.Bytes JPEG2000.Marker JPEG2000.Header JPEG2000.TilePart
  JPEG2000.Tier2.Geometry JPEG2000.Tier2.Packet
open JPEG2000.Decode (allocOutput)
open JPEG2000.Spec.Tier1 (Coeff)
open JPEG2000.Spec.Quant (BandQuant)

/-! ## The skeletons (the fast decoder's control flow, stages as parameters) -/

/-- **One tile-component** (`Assemble.reconstructTileComp` with its stages as parameters):
`init w h` allocates the coefficient store (with the `maxWorkSamples` check), `dec` decodes a
code-block (Tier-1), `write` dequantises it into the store (returning `false` on
saturation), `fin rev store rect nl' sat` runs the inverse DWT. The iteration (resolutions
`0 … NL − reduce`, precincts, bands, code-blocks with passes and a non-empty rectangle) and
the reduction check are the fast decoder's. -/
def tileCompWith {σ β O : Type} (init : Nat → Nat → Except Error σ)
    (dec : CompParams → Nat → Band → CodeBlock → Except Error β)
    (write : σ → Rect → Nat → Nat → Band → Rect → BandQuant → Nat → β → Except Error (σ × Bool))
    (fin : Bool → σ → Rect → Nat → Nat → Except Error (O × Nat))
    (tc : TileCompGeom) (depth F reduce : Nat)
    (precs : Array (Array PrecinctOut)) : Except Error (O × Nat) := do
  let p := tc.params
  let nl := p.levels
  if reduce > nl then
    throw (.unsupported Assemble.loc
      s!"resolution reduction {reduce} exceeds the {nl} decomposition levels of a tile-component")
  let nl' := nl - reduce
  let rect := Assemble.reduceRect tc.rect reduce
  let mut plane ← init rect.width rect.height
  let mut sat := 0
  for r in [0:min (nl' + 1) precs.size] do
    let ps := precs.getD r #[]
    for prec in ps do
      for bo in prec.bands do
        for cb in bo.blocks do
          if cb.numPasses != 0 && !rectEmpty cb.geom.rect then
            let o ← dec p r bo.band cb
            let q := Spec.Quant.bandQuant p depth r bo.band
            let (pl, ok) ← write plane rect nl' r bo.band cb.geom.rect q F o
            plane := pl
            if !ok then sat := sat + 1
  fin (p.transform == .reversible53) plane rect nl' sat

/-- **One tile** (`Assemble.decodeTile` with its stages as parameters): `recon` per
tile-component (`tileCompWith`), `mctF` the inverse MCT on components 0–2, `dcPrep` /
`dcApply` the DC shift and clamp, `mk` the result record. -/
def tileWith {α β P D R : Type} (mk : Nat → Array (Rect × β) → Nat → R)
    (recon : TileCompGeom → Nat → Nat → Nat → P → Except Error (α × Nat))
    (precsOf : TileCodeBlocks → Nat → P) (noPrecs : P) (z : α)
    (mctF : Bool → Array α → Except Error (Array α))
    (dcPrep : Component → Bool → Nat → Except Error D) (dcApply : D → Bool → α → β)
    (L : Limits) (h : Header) (t : Nat) (reduce : Nat)
    (tcb : Option TileCodeBlocks) : Except Error R := do
  let (g, coding) ← Progression.Layout.ofHeader h t
  let s := h.siz
  let mct := coding.mctApplies s
  let cells := g.comps.foldl (fun a tc => a + (Assemble.reduceRect tc.rect reduce).width *
    (Assemble.reduceRect tc.rect reduce).height) 0
  L.check Assemble.loc .workSamples cells
  let mut planes : Array α := #[]
  let mut sat := 0
  for c in [0:g.numComps] do
    let tc := g.comp c
    let comp := s.components.getD c default
    let precs := match tcb with
      | some x => precsOf x c
      | none => noPrecs
    let (pl, n) ← recon tc comp.depth.toNat (Assemble.fracBitsOf s mct c) reduce precs
    planes := planes.push pl
    sat := sat + n
  if mct then
    planes ← mctF ((g.comp 0).params.transform == .reversible53) planes
  let mut out : Array (Rect × β) := #[]
  for c in [0:g.numComps] do
    let tc := g.comp c
    let comp := s.components.getD c default
    let rev := tc.params.transform == .reversible53
    let F := if rev then 0 else Assemble.fracBitsOf s mct c
    let dc ← dcPrep comp rev F
    let pl := planes.getD c z
    planes := planes.setIfInBounds c z
    let pl := dcApply dc rev pl
    out := out.push (Assemble.reduceRect tc.rect reduce, pl)
  return mk t out sat

/-- **The codestream** (`decodeCodestream` with its stages as parameters): `tier2` decodes
the packets of a present tile (given its header stream and the passes counted so far),
`decTile` reconstructs a tile, `place` copies it into the component stores (initialised by
`conv` from the fast decoder's zero planes, of which only the sizes are used by the spec),
`fin` builds the result. Header parsing, the output geometry and limits, the `PPM` chunk
assignment, the header streams and the tile iteration are shared. -/
def codestreamWith {T TO ST R : Type}
    (tier2 : Limits → Header → ByteArray → TileParams → Option Tier2.Headers.HeaderStream → Nat →
      Except Error T)
    (passesOf : T → Nat) (decTile : Header → Nat → Option T → Except Error TO)
    (satOf : TO → Nat) (conv : Array Plane → ST)
    (place : Array DecodedComponent → ST → TO → Except Error ST)
    (fin : Header → Array DecodedComponent → ST → Nat → R)
    (L : Limits) (data : ByteArray) (reduce : Nat) : Except Error R := do
  L.check Decode.loc .decompLevels reduce
  let h ← Header.parse L data
  let s := h.siz
  let (info, planes0) ← allocOutput L s reduce
  let mut planes := conv planes0
  let idx ← if h.ppm.segments.isEmpty then pure #[] else Tier2.Headers.ppmChunkIndex L h
  let mut passes := 0
  let mut sat := 0
  let mut j := 0
  for t in [0:numTiles s] do
    let present := match h.tiles[j]? with
      | some tp => if tp.index = t then some tp else none
      | none => none
    let tcb ← match present with
      | some tp => do
        let hs ← Tier2.Headers.headerStreamAt h data tp (idx.getD j #[])
        let x ← tier2 L h data tp hs passes
        pure (some x)
      | none => pure none
    if present.isSome then j := j + 1
    if let some x := tcb then passes := passes + passesOf x
    let out ← decTile h t tcb
    sat := sat + satOf out
    planes ← place info planes out
  return fin h info planes sat

/-! ## Tier-2 (placeholder for task 7.1b) -/

namespace Tier2Spec

/-- **Placeholder (task 7.1b replaces it).** The Tier-2 specification of one tile's packets:
for now the fast `Tier2.Headers.decodeWithStream` itself. 7.1b defines a B.10 packet-header
spec over bit lists (with `Spec.TagTree`) producing the same `TileCodeBlocks` and proves it
equal to the fast decoder (hypothesis `Spec.Equiv.Tier2Equiv`). -/
abbrev decode : Limits → Header → ByteArray → TileParams → Option Tier2.Headers.HeaderStream →
    Nat → Except Error TileCodeBlocks :=
  Tier2.Headers.decodeWithStream

/-- **Placeholder (task 7.1b replaces it).** The codeword segments of a code-block (B.10.7,
D.4) as a buffer and byte ranges in it: for now the fast gathering `Assemble.tier1Input`
(the input itself when every segment is one range, else the segments concatenated). -/
abbrev segments : ByteArray → CodeBlock → ByteArray × Array Tier1.Seg :=
  Assemble.tier1Input

end Tier2Spec

/-! ## Tier-1 -/

/-- The spec code-block of a Tier-2 code-block of band `b` of resolution `r` (parameters
`p`): size from its rectangle, orientation, style `Mode.ofStyle`, `Mb + roiShift` bit-planes
(E-2, Annex H), the tag-tree zero bit-planes (0 if never included) and its codeword segments
as byte lists. `malformed` when a segment range lies outside the buffer. -/
def specCodeBlock (data : ByteArray) (p : CompParams) (r : Nat) (b : Band) (cb : CodeBlock) :
    Except Error Spec.Tier1.CodeBlock := do
  let (buf, segs) := Tier2Spec.segments data cb
  if segs.any fun sg => sg.start > sg.stop || sg.stop > buf.size then
    throw (.malformed Spec.Tier1.tier1Loc "code-block data range outside the buffer")
  let rc := cb.geom.rect
  return { width := rc.width, height := rc.height, orient := Spec.Tier1Equiv.orientOf b,
           mode := Spec.Tier1.Mode.ofStyle p.cbStyle.toNat,
           numBitPlanes := bandMb p r b + p.roiShift,
           zeroBitPlanes := if cb.included then cb.zeroBitPlanes else 0,
           segments := segs.toList.map fun sg =>
             { data := Spec.MQEquiv.segment buf sg.start sg.stop, passes := sg.passes } }

/-- Tier-1 (T.800 Annex D, every code-block style): the spec coefficient states of a
code-block in raster order. -/
def decodeBlock (data : ByteArray) (p : CompParams) (r : Nat) (b : Band) (cb : CodeBlock) :
    Except Error (Array Coeff) := do
  Spec.Tier1.decodeCodeBlock (← specCodeBlock data p r b cb)

/-! ## Dequantisation and the sub-band grids -/

/-- A decoded code-block with what dequantisation needs: resolution, band, rectangle (band
coordinates), the band's quantisation parameters and the coefficients (raster order). -/
structure Entry where
  /-- Resolution level. -/
  r : Nat
  /-- Sub-band. -/
  band : Band
  /-- Code-block rectangle in band coordinates. -/
  rect : Rect
  /-- Quantisation parameters of the band (E.1). -/
  q : BandQuant
  /-- Tier-1 coefficient states, raster order. -/
  coeffs : Array Coeff

/-- Collecting code-blocks: the newest first (so that a lookup finds the last code-block
written at a position, as the fast decoder's in-place writes; code-blocks of a band do not
overlap, B.7, so the choice does not matter for a valid stream). -/
def collect (st : List Entry) (_rect : Rect) (_nl r : Nat) (b : Band) (cbr : Rect) (q : BandQuant)
    (_F : Nat) (cs : Array Coeff) : Except Error (List Entry × Bool) :=
  pure ({ r, band := b, rect := cbr, q, coeffs := cs } :: st, true)

/-- `(u, v)` (band coordinates) lies in the code-block's rectangle. -/
def Entry.covers (e : Entry) (u v : Int) : Bool :=
  decide ((e.rect.x0 : Int) ≤ u ∧ u < e.rect.x1 ∧ (e.rect.y0 : Int) ≤ v ∧ v < e.rect.y1)

/-- The code-block covering band position `(u, v)` of band `b` at decomposition level `lvl`
(of `nl` levels), if any. -/
def entryAt (es : List Entry) (nl lvl : Nat) (b : Band) (u v : Int) : Option Entry :=
  es.find? fun e => e.band == b && bandLevel nl e.r == lvl && e.covers u v

/-- The coefficient at band position `(u, v)` of a code-block. -/
def Entry.coeff (e : Entry) (u v : Int) : Coeff :=
  e.coeffs.getD ((v - e.rect.y0).toNat * e.rect.width + (u - e.rect.x0).toNat) {}

/-- Sub-band `b` of level `lvl` as an integer grid (band coordinates): reversible
dequantisation (E.1.1.2 with ROI, `Spec.Quant.dequantRev`) of the covering code-block's
coefficient, `0` where no code-block was decoded. -/
def bandGrid53 (es : List Entry) (nl lvl : Nat) (b : Band) : Spec.DWT53.Grid :=
  ⟨fun u v => match entryAt es nl lvl b u v with
    | some e => Spec.Quant.dequantRev e.q.roiShift (e.coeff u v)
    | none => 0⟩

/-- Sub-band `b` of level `lvl` as a rational grid: irreversible dequantisation (E-6 with
`r = 1/2`, `Δb` of E-3, ROI; `Spec.Quant.dequantIrrev`). -/
def bandGrid97 (es : List Entry) (nl lvl : Nat) (b : Band) : Spec.DWT97.Grid :=
  ⟨fun u v => match entryAt es nl lvl b u v with
    | some e => Spec.Quant.dequantIrrev e.q.roiShift e.q.delta (e.coeff u v)
    | none => 0⟩

/-- The `nl`-level decomposition (5/3): LL of level `nl`, `(HL, LH, HH)` of levels `1 … nl`
(finest first). -/
def dec53 (es : List Entry) (nl : Nat) : Spec.DWT53.Dec :=
  { ll := bandGrid53 es nl nl .LL,
    details := (List.range nl).map fun i =>
      (bandGrid53 es nl (i + 1) .HL, bandGrid53 es nl (i + 1) .LH, bandGrid53 es nl (i + 1) .HH) }

/-- The `nl`-level decomposition (9/7, exact rationals). -/
def dec97 (es : List Entry) (nl : Nat) : Spec.DWT97.Dec :=
  { ll := bandGrid97 es nl nl .LL,
    details := (List.range nl).map fun i =>
      (bandGrid97 es nl (i + 1) .HL, bandGrid97 es nl (i + 1) .LH, bandGrid97 es nl (i + 1) .HH) }

/-! ## Inverse DWT, MCT, DC shift -/

/-- One reconstructed sample of a tile-component before the DC shift: the reversible
integer `ival` or the irreversible rational `rval`, with the C9 trace (`peers`: the
inverse-DWT outputs it depends on; `levels`: their decomposition levels; `mct`: an inverse
MCT was applied). -/
structure SpecCell where
  /-- Reversible path (5/3, RCT). -/
  rev : Bool
  /-- Value on the reversible path. -/
  ival : Int
  /-- Value on the irreversible path. -/
  rval : Rat
  /-- Inverse-DWT outputs this value was computed from. -/
  peers : List Rat
  /-- Decomposition levels of those inverse DWTs. -/
  levels : List Nat
  /-- An inverse component transform was applied. -/
  mct : Bool
  deriving Inhabited

/-- A tile-component as a plane of `SpecCell`s (`width × height`, row-major). -/
structure CellPlane where
  /-- Width. -/
  width : Nat
  /-- Height. -/
  height : Nat
  /-- Cells, row-major. -/
  cells : Array SpecCell
  deriving Inhabited

/-- The cell of an inverse-DWT output: reversible `x` (an integer) or irreversible `x`. -/
def SpecCell.ofRev (x : Int) (nl : Nat) : SpecCell :=
  { rev := true, ival := x, rval := x, peers := [(x : Rat)], levels := [nl], mct := false }

/-- See `ofRev`. -/
def SpecCell.ofIrrev (x : Rat) (nl : Nat) : SpecCell :=
  { rev := false, ival := 0, rval := x, peers := [x], levels := [nl], mct := false }

/-- `IDWT` (F.3.1) of the collected code-blocks of a tile-component on rectangle `rect` with
`nl` levels: `Spec.DWT53.srMulti` of `dec53` (reversible) or `Spec.DWT97.srMulti` of `dec97`
(irreversible), read on the rectangle row by row. -/
def idwt (rev : Bool) (es : List Entry) (rect : Rect) (nl : Nat) : CellPlane :=
  let w := rect.width
  let h := rect.height
  let r := DWT53.specRect rect
  if rev then
    let g := Spec.DWT53.memo r (Spec.DWT53.srMulti r nl (dec53 es nl))
    { width := w, height := h,
      cells := Array.ofFn (n := w * h) fun j =>
        SpecCell.ofRev (g.get (rect.x0 + (j.val % w : Nat)) (rect.y0 + (j.val / w : Nat))) nl }
  else
    let g := Spec.DWT97.memo r (Spec.DWT97.srMulti r nl (dec97 es nl))
    { width := w, height := h,
      cells := Array.ofFn (n := w * h) fun j =>
        SpecCell.ofIrrev (g.get (rect.x0 + (j.val % w : Nat)) (rect.y0 + (j.val / w : Nat))) nl }

/-- The `fin` stage of `tileCompWith` for the spec: the inverse DWT. -/
def finSpec (rev : Bool) (es : List Entry) (rect : Rect) (nl sat : Nat) :
    Except Error (CellPlane × Nat) :=
  pure (idwt rev es rect nl, sat)

/-- The store of the spec: the code-blocks collected so far, after the `maxWorkSamples`
check of the plane the fast decoder allocates. -/
def initSpec (L : Limits) (w h : Nat) : Except Error (List Entry) := do
  L.check Assemble.loc .workSamples (w * h)
  return []

/-- **Spec reconstruction of one tile-component** up to the inverse DWT: spec Tier-1,
collection, `idwt`. -/
def tileComp (L : Limits) (data : ByteArray) (tc : TileCompGeom) (depth F reduce : Nat)
    (precs : Array (Array PrecinctOut)) : Except Error (CellPlane × Nat) :=
  tileCompWith (initSpec L) (decodeBlock data) collect finSpec tc depth F reduce precs

/-- Inverse RCT (G.2) on three reversible cells. -/
def rctCells (a b c : SpecCell) : SpecCell × SpecCell × SpecCell :=
  let (i0, i1, i2) := Spec.MCT.rctInv (a.ival, b.ival, c.ival)
  let peers := a.peers ++ b.peers ++ c.peers
  let levels := a.levels ++ b.levels ++ c.levels
  ({ rev := a.rev, ival := i0, rval := i0, peers, levels, mct := true },
   { rev := b.rev, ival := i1, rval := i1, peers, levels, mct := true },
   { rev := c.rev, ival := i2, rval := i2, peers, levels, mct := true })

/-- Inverse ICT (G.3) on three irreversible cells (exact rationals). -/
def ictCells (a b c : SpecCell) : SpecCell × SpecCell × SpecCell :=
  let (x0, x1, x2) := Spec.MCT.ictInv (a.rval, b.rval, c.rval)
  let peers := a.peers ++ b.peers ++ c.peers
  let levels := a.levels ++ b.levels ++ c.levels
  ({ a with rval := x0, peers, levels, mct := true },
   { b with rval := x1, peers, levels, mct := true },
   { c with rval := x2, peers, levels, mct := true })

/-- The empty cell plane (the default of the component list). -/
def CellPlane.empty : CellPlane := { width := 0, height := 0, cells := #[] }

/-- **Inverse MCT** (G.2 when `rev`, G.3 otherwise) on components 0–2, cell by cell; the
three planes must have equal sizes (`malformed` otherwise, as the fast decoder). -/
def mctSpec (rev : Bool) (planes : Array CellPlane) : Except Error (Array CellPlane) := do
  let z := CellPlane.empty
  let p0 := planes.getD 0 z
  let p1 := planes.getD 1 z
  let p2 := planes.getD 2 z
  if p1.width = p0.width ∧ p1.height = p0.height ∧ p2.width = p0.width ∧
      p2.height = p0.height then
    let n := p0.width * p0.height
    let t := Array.ofFn (n := n) fun j =>
      let a := p0.cells.getD j default
      let b := p1.cells.getD j default
      let c := p2.cells.getD j default
      if rev then rctCells a b c else ictCells a b c
    let q0 := { p0 with cells := t.map (·.1) }
    let q1 := { p1 with cells := t.map (·.2.1) }
    let q2 := { p2 with cells := t.map (·.2.2) }
    return ((planes.setIfInBounds 0 q0).setIfInBounds 1 q1).setIfInBounds 2 q2
  else throw (.malformed MCT.loc
    s!"component transform on planes {p0.width}×{p0.height}, {p1.width}×{p1.height}, {p2.width}×{p2.height}")

/-- One output sample of the spec decoder. -/
structure SpecSample where
  /-- The sample (DC-shifted, clamped to the component's range; irreversible: rounded). -/
  value : Int
  /-- The exact value before rounding and DC shift. -/
  exact : Rat
  /-- Reversible path. -/
  reversible : Bool
  /-- Inverse-DWT outputs it depends on (C9 trace). -/
  peers : List Rat
  /-- Their decomposition levels (C9 trace). -/
  levels : List Nat
  /-- An inverse MCT was applied (C9 trace). -/
  mct : Bool
  deriving Inhabited

/-- A sample not covered by any tile (the fast decoder's zero planes). -/
def SpecSample.blank : SpecSample :=
  { value := 0, exact := 0, reversible := true, peers := [], levels := [], mct := false }

/-- A reconstructed tile-component on its component grid. -/
structure SamplePlane where
  /-- Width. -/
  width : Nat
  /-- Height. -/
  height : Nat
  /-- Samples, row-major. -/
  samples : Array SpecSample
  deriving Inhabited

/-- Round half up: `⌊x + 1/2⌋`. -/
def roundHalf (x : Rat) : Int := (x + 1 / 2).floor

/-- G.1 for one cell: reversible `reconRev` (DC shift, clamp); irreversible: round to the
nearest integer (ties up), then `reconRev`. -/
def SpecCell.toSample (signed : Bool) (depth : Nat) (rev : Bool) (c : SpecCell) : SpecSample :=
  if rev then
    { value := Spec.MCT.reconRev signed depth c.ival, exact := c.ival, reversible := true,
      peers := c.peers, levels := c.levels, mct := c.mct }
  else
    { value := Spec.MCT.reconRev signed depth (roundHalf c.rval), exact := c.rval,
      reversible := false, peers := c.peers, levels := c.levels, mct := c.mct }

/-- The `dcApply` stage of the spec (the component's signedness and depth come from
`dcPrep`). -/
def dcSpec (sd : Bool × Nat) (rev : Bool) (p : CellPlane) : SamplePlane :=
  { width := p.width, height := p.height, samples := p.cells.map (SpecCell.toSample sd.1 sd.2 rev) }

/-- A reconstructed tile of the spec: per component its rectangle (component grid, reduced)
and samples. -/
structure TileOut where
  /-- Tile index. -/
  tile : Nat
  /-- Per component. -/
  comps : Array (Rect × SamplePlane)

/-- **Spec reconstruction of tile `t`**: `tileComp` per component, `mctSpec`, G.1. -/
def decodeTile (L : Limits) (h : Header) (data : ByteArray) (t reduce : Nat)
    (tcb : Option TileCodeBlocks) : Except Error TileOut :=
  tileWith (fun t comps _ => ({ tile := t, comps } : TileOut))
    (fun tc d F r p => tileComp L data tc d F r p) (fun x c => x.comps.getD c #[]) #[]
    CellPlane.empty mctSpec (fun comp _ _ => pure (comp.signed, comp.depth.toNat)) dcSpec
    L h t reduce tcb

/-! ## Placement and the result -/

/-- Copies `k` samples (as `Assemble.blitRow`). -/
def blitRow (src : SamplePlane) : Nat → Nat → Nat → Array SpecSample → Array SpecSample
  | 0, _, _, dst => dst
  | k + 1, si, di, dst =>
    let dst := match src.samples[si]? with
      | some v => dst.setIfInBounds di v
      | none => dst
    blitRow src k (si + 1) (di + 1) dst

/-- Copies `k` rows (as `Assemble.blitRows`). -/
def blitRows (src : SamplePlane) (dw ox oy : Nat) : Nat → Nat → Array SpecSample → Array SpecSample
  | 0, _, dst => dst
  | k + 1, y, dst =>
    let dst := blitRow src src.width (y * src.width) ((oy + y) * dw + ox) dst
    blitRows src dw ox oy k (y + 1) dst

/-- Copies a tile-component into a component plane at `(ox, oy)` (as `Assemble.blit`). -/
def blit (dst src : SamplePlane) (ox oy : Nat) : Except Error SamplePlane :=
  if ox + src.width ≤ dst.width ∧ oy + src.height ≤ dst.height then
    .ok { dst with samples := blitRows src dst.width ox oy src.height 0 dst.samples }
  else .error (.malformed Assemble.loc
    s!"tile-component {src.width}×{src.height} at ({ox}, {oy}) outside the component plane {dst.width}×{dst.height}")

/-- Copies a reconstructed tile into the component planes (as `Decode.place`). -/
def place (info : Array DecodedComponent) (planes : Array SamplePlane) (t : TileOut) :
    Except Error (Array SamplePlane) := do
  let mut planes := planes
  for c in [0:t.comps.size] do
    let some (r, pl) := t.comps[c]? | throw (.malformed Decode.loc "tile component out of range")
    let some dc := info[c]? | throw (.malformed Decode.loc "component out of range")
    if r.x0 < dc.x0 ∨ r.y0 < dc.y0 then
      throw (.malformed Decode.loc s!"tile {t.tile} component {c} starts before the image")
    let dst := planes.getD c default
    let dst ← blit dst pl (r.x0 - dc.x0) (r.y0 - dc.y0)
    planes := planes.setIfInBounds c dst
  return planes

/-- One component of the spec result (geometry as `DecodedComponent`). -/
structure SpecComponent where
  /-- Geometry, depth and signedness (the fast record; its `plane` is unused, empty). -/
  info : DecodedComponent
  /-- Samples, `info.width × info.height`, row-major. -/
  samples : Array SpecSample

instance : Inhabited SpecComponent := ⟨{ info := default, samples := #[] }⟩

/-- The result of `Spec.decode`. -/
structure SpecImage where
  /-- The parsed header. -/
  header : Header
  /-- One entry per codestream component. -/
  comps : Array SpecComponent

/-- The initial component stores: every sample `blank`. -/
def initPlanes (ps : Array Plane) : Array SamplePlane :=
  ps.map fun p => { width := p.width, height := p.height,
                    samples := Array.replicate (p.width * p.height) SpecSample.blank }

/-- **`Spec.decode`**: the codestream decoded with the specification of every stage (module
doc), in the fast decoder's order. -/
def decode (L : Limits) (data : ByteArray) (reduce : Nat := 0) : Except Error SpecImage :=
  codestreamWith Tier2Spec.decode (·.passes) (fun h t tcb => decodeTile L h data t reduce tcb)
    (fun _ => 0) initPlanes place
    (fun h info planes _ =>
      { header := h, comps := info.zipWith (fun m p => { info := m, samples := p.samples }) planes })
    L data reduce

end JPEG2000.Spec.Decode
