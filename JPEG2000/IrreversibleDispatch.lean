import JPEG2000.WideAssembly
import JPEG2000.WideDWT97
import JPEG2000.WideICT
import JPEG2000.NativeOutput

/-!
# Checked irreversible reconstruction (Plan.md §§4, 5.1, 5.4, 7; T.800 B, D, E, F.3, G.3)

Each component tries the compact coefficient and lifting kernels on its retained packets.
A precision failure restarts that component from its packets. The ICT consumes the resulting
unclamped spatial planes and rounds each complete decimal matrix row once at their common scale.
-/

namespace JPEG2000.IrreversibleDispatch

open Bytes Header Tier2.Geometry Tier2.Packet

/-- A centred tile-component retained at its working precision, before G.1. -/
inductive Spatial where
  /-- A successful checked narrow kernel, retaining the component-grid origin. -/
  | compact (rect : Rect) (bits : Nat) (p : Plane) (hw : p.width = rect.width)
      (hh : p.height = rect.height)
  /-- An arbitrary-magnitude plane at the same binary scale as its coefficients. -/
  | wide (p : WideICT.Component)

/-- Component-grid rectangle, including its origin. -/
def Spatial.rect : Spatial → Rect
  | .compact r .. => r
  | .wide p => p.rect

/-- Number of fractional bits actually used during reconstruction. -/
def Spatial.bits : Spatial → Nat
  | .compact _ f .. => f
  | .wide p => p.fracBits

/-- Borrow either backing directly for native output. -/
def Spatial.source : Spatial → NativeOutput.Source
  | .compact _ _ p .. => .plane p
  | .wide p => .exact p.rect.width p.rect.height p.samples.get

/-- Promote only the compact peers of a wide ICT. -/
def Spatial.toWide : Spatial → WideICT.Component
  | .wide p => p
  | .compact r f p hw hh =>
    ⟨⟨r, Vector.ofFn fun i => (p.get i.val (by rw [hw, hh]; exact i.isLt)).toInt⟩, f⟩

/-- Checked compact coefficient traversal. Stop on the first overflowing dequantisation
or refused Tier-1 precision. Fragmented codewords are validated before gathering. -/
def compactBands (L : Limits) (data : ByteArray) (tc : TileCompGeom) (depth F reduce : Nat)
    (ps : Array (Array PrecinctOut)) : Except Error Plane := do
  L.check Assemble.loc .decompLevels (max reduce tc.params.levels)
  let r := Assemble.reduceRect tc.rect reduce
  let nl := tc.params.levels - reduce
  let p ← Plane.zeroChecked L Assemble.loc r.width r.height
  WideAssembly.visitBlocks nl ps p fun dst res b cb => do
    if !cb.segments.all (fun s => s.ranges.all (fun rg => rg.offset + rg.length ≤ data.size)) then
      throw (.malformed Tier1.tier1Loc "code-block data range outside the buffer")
    let block ← Assemble.decodeBlock data tc.params res b cb
    let q := Spec.Quant.bandQuant tc.params depth res b
    let (out, ok) ← Quant.dequantBlock dst r nl res b cb.geom.rect q F block
    if ok then return out
    throw (.unsupported Assemble.loc "dequantised coefficient exceeds compact precision")

/-- Attempt only the checked 9/7 implementation. Its failure discards the entire compact
attempt, so a saturated spatial sample can never become an ICT input. -/
def compactSpatial (p : Plane) (r : Rect) (nl F : Nat) : Option Spatial := do
  let q ← DWT97.idwt97Fast p r nl
  if h : q.width = r.width ∧ q.height = r.height then
    return .compact r F q h.1 h.2
  none

/-- Attempt the packet and lifting stages together, leaving definitive packet validation and
error reporting to wide assembly whenever the packed attempt fails. -/
def tryCompact (L : Limits) (data : ByteArray) (tc : TileCompGeom) (depth F reduce : Nat)
    (ps : Array (Array PrecinctOut)) : Except Error (Option Spatial) :=
  match compactBands L data tc depth F reduce ps with
  | .error _ => .ok none
  | .ok p => .ok (compactSpatial p (Assemble.reduceRect tc.rect reduce) (tc.params.levels - reduce) F)

/-- Reconstruct one irreversible component from the tile's actual packet store. Setting
`allowCompact` to false selects the arbitrary-magnitude kernels from the outset. -/
def component (L : Limits) (data : ByteArray) (tc : TileCompGeom) (depth F reduce : Nat)
    (ps : Array (Array PrecinctOut)) (allowCompact : Bool := true) : Except Error Spatial := do
  if tc.params.transform != .irreversible97 then
    throw (.unsupported Assemble.loc "irreversible reconstruction requires the 9/7 transform")
  if reduce > tc.params.levels then
    throw (.unsupported Assemble.loc "resolution reduction exceeds tile-component levels")
  L.check Assemble.loc .decompLevels tc.params.levels
  let r := Assemble.reduceRect tc.rect reduce
  if r.x1 < r.x0 ∨ r.y1 < r.y0 then throw (.malformed Assemble.loc "inverted component rectangle")
  let nl := tc.params.levels - reduce
  let attempt ← (if allowCompact then tryCompact L data tc depth F reduce ps else pure none)
  if let some q := attempt then return q
  let bands ← WideAssembly.tileComp L data tc depth F reduce ps
  let q ← WideDWT97.idwt97 L bands nl
  return .wide ⟨q, F⟩

/-- Fill a compact plane backwards, stopping before any out-of-range row result is stored. -/
def packRows {N : Nat} (f : Nat → Int) (n : Nat) (hn : n ≤ N) (p : DWT53.Buf N) :
    Option (DWT53.Buf N) :=
  match n with
  | 0 => some p
  | k + 1 =>
    let z := f k
    let v := z.toInt32
    if v.toInt = z then packRows f k (Nat.le_of_lt hn) (p.set k v hn) else none

/-- Materialise an ICT channel only when all its rounded fixed-point values fit Int32. -/
def pack (r : Rect) (F : Nat) (f : Nat → Int) : Option Spatial := do
  let q ← packRows f (rectArea r) (Nat.le_refl _) ⟨Plane.zero r.width r.height, rfl⟩
  if h : q.val.width = r.width ∧ q.val.height = r.height then
    return .compact r F q.val h.1 h.2
  none

/-- Fixed-point input for a decimal ICT row, indexed in the local raster. -/
@[inline] def Spatial.fixed (p : Spatial) (j : Nat) : Int :=
  (p.source.get? j).getD 0

/-- Evaluate the decimal G.3 rows directly on three compact rasters. -/
def compactICT (y cb cr : Spatial) : Option (Spatial × Spatial × Spatial) := do
  let .compact .. := y | none
  let .compact .. := cb | none
  let .compact .. := cr | none
  let r ← pack y.rect y.bits fun i => WideICT.red (y.fixed i) (cr.fixed i)
  let g ← pack cb.rect y.bits fun i => WideICT.green (y.fixed i) (cb.fixed i) (cr.fixed i)
  let b ← pack cr.rect y.bits fun i => WideICT.blue (y.fixed i) (cb.fixed i)
  return (r,g,b)

/-- Dispatch the ICT after verifying its three grids and scales. On overflow, the wide
matrix reads the retained pre-colour inputs of all three participating components. -/
def ict (L : Limits) (y cb cr : Spatial) : Except Error (Spatial × Spatial × Spatial) := do
  L.check (.at .mct) .workSamples (rectArea y.rect + rectArea cb.rect + rectArea cr.rect)
  if WideReversible.SameShape y.rect cb.rect cr.rect ∧ WideICT.Ordered y.rect ∧
      WideICT.Ordered cb.rect ∧ WideICT.Ordered cr.rect ∧ cb.bits = y.bits ∧ cr.bits = y.bits then
    match compactICT y cb cr with
    | some out => return out
    | none =>
      let (r,g,b) ← WideICT.ictInverse L y.toWide cb.toWide cr.toWide
      return (.wide r, .wide g, .wide b)
  else throw (.malformed (.at .mct) "incompatible ICT component grids or fractional bits")

/-- Prepare post-MCT sources for a tile. Channels after the first three pass through at
their own precision, as do all channels when there is no MCT. -/
def sources (L : Limits) (mct : Bool) (ps : Array Spatial) : Except Error (Array NativeOutput.Source) := do
  if !mct then return ps.map Spatial.source
  let some y := ps[0]? | throw (.malformed (.at .mct) "missing ICT luma")
  let some cb := ps[1]? | throw (.malformed (.at .mct) "missing ICT blue chroma")
  let some cr := ps[2]? | throw (.malformed (.at .mct) "missing ICT red chroma")
  let (r,g,b) ← ict L y cb cr
  return (((ps.map Spatial.source).setIfInBounds 0 r.source).setIfInBounds 1 g.source).setIfInBounds 2 b.source

/-- Irreversible tile-loop entry point, using each component's reduced level count and
the binary precision expected by `NativeOutput.writeTile`. For a tile with mixed wavelet
kernels the caller can dispatch each component separately before the colour stage. -/
def tile (L : Limits) (data : ByteArray) (siz : Marker.SIZ) (g : Progression.Layout)
    (coding : Coding) (store : Option TileCodeBlocks) (reduce : Nat) (allowCompact : Bool := true) :
    Except Error (Array NativeOutput.Source) := do
  L.check Assemble.loc .decompLevels reduce
  let mct := coding.mctApplies siz
  L.check Assemble.loc .workSamples (g.comps.foldl (fun n tc =>
    n + rectArea (Assemble.reduceRect tc.rect reduce)) 0)
  let ps ← g.comps.mapFinIdxM fun c tc _ =>
    component L data tc (siz.components.getD c default).depth.toNat
      (Assemble.fracBitsOf siz mct c) reduce ((store.map (·.comps.getD c #[])).getD #[]) allowCompact
  sources L mct ps

end JPEG2000.IrreversibleDispatch
