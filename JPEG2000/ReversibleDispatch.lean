import JPEG2000.NativeOutput
import JPEG2000.WideAssembly
import JPEG2000.WideReversible

/-!
# Reversible tile reconstruction (Plan.md §§4, 5.1, 5.4, 7; T.800 Annexes B, D, E, F, G)

Keep the ordinary packed raster when coefficient reconstruction and lifting both succeed at
its precision. On a precision miss, reconstruct from the original packet ranges.
-/

namespace JPEG2000.ReversibleDispatch

open Bytes Header Tier2.Geometry Tier2.Packet NativeOutput

/-- Validate original ranges before compact Tier-1 gathers the pieces and checks the
actual block's coded-plane count. -/
def checkedBlock (data : ByteArray) (p : CompParams) (r : Nat) (b : Band) (cb : CodeBlock) :
    Except Error Tier1.CodeBlockOut :=
  if cb.segments.all (fun s => s.ranges.all (fun rg => rg.offset + rg.length ≤ data.size)) then
    Assemble.decodeBlock data p r b cb
  else .error (.malformed Tier1.tier1Loc "code-block data range outside the buffer")

/-- Run the packed coefficient loop and checked lifting. Either dequantisation saturation
or lifting overflow requests a wider reconstruction. -/
def narrow (L : Limits) (data : ByteArray) (tc : TileCompGeom) (depth F reduce : Nat)
    (precs : Array (Array PrecinctOut)) : Except Error (Option Plane × Nat) := do
  let p := tc.params
  if reduce > p.levels then
    throw (.unsupported Assemble.loc
      s!"resolution reduction {reduce} exceeds the {p.levels} decomposition levels of a tile-component")
  let nl := p.levels - reduce
  let rect := Assemble.reduceRect tc.rect reduce
  let plane ← Plane.zeroChecked L Assemble.loc rect.width rect.height
  let (pl, sat) ← WideAssembly.visitBlocks nl precs (plane, 0) fun (dst, sat) r b cb => do
    let o ← checkedBlock data p r b cb
    let q := Spec.Quant.bandQuant p depth r b
    let (pl, ok) ← Quant.dequantBlock dst rect nl r b cb.geom.rect q F o
    return (pl, if ok then sat else sat+1)
  return (if sat = 0 then DWT53.idwt53Fast pl rect nl else none, sat)

/-- Borrow the wide spatial array on its reduced rectangle. -/
def wideSource (L : Limits) (p : WideQuant.Plane) (nl : Nat) : Except Error Source := do
  let q ← WideReversible.idwt53 L p.rect nl p.samples.toArray
  if h : q.size = p.rect.width * p.rect.height then
    return .exact p.rect.width p.rect.height (fun i => q[i.val]'(by rw [h]; exact i.isLt))
  else throw (.malformed DWT53.loc "invalid spatial raster size")

/-- Admit the compact attempt at an ordered reduced rectangle and within the level budget.
Otherwise leave error reporting to wide assembly, which validates the original inputs in order. -/
def compactPlane? (L : Limits) (data : ByteArray) (tc : TileCompGeom) (depth F reduce : Nat)
    (precs : Array (Array PrecinctOut)) : Option Plane := do
  guard (reduce ≤ tc.params.levels && tc.params.levels ≤ L.maxDecompLevels)
  let r := Assemble.reduceRect tc.rect reduce
  guard (r.x0 ≤ r.x1 && r.y0 ≤ r.y1)
  let (p, _) ← (narrow L data tc depth F reduce precs).toOption
  p

/-- Reconstruct a reversible component before G.1. A failed compact attempt goes back
to the original packet store so wide Tier-1 and dequantisation retain their validation. -/
def tileComp (L : Limits) (data : ByteArray) (tc : TileCompGeom) (depth F reduce : Nat)
    (precs : Array (Array PrecinctOut)) : Except Error Source := do
  if tc.params.transform != .reversible53 then
    throw (.malformed Assemble.loc "expected a reversible tile-component")
  match compactPlane? L data tc depth F reduce precs with
  | some p => return .plane p
  | none =>
    let p ← WideAssembly.tileComp L data tc depth F reduce precs
    wideSource L p (tc.params.levels - reduce)

/-- Parsed-layout entry point for the tile loop. A missing tile supplies zero bands. -/
def component (L : Limits) (data : ByteArray) (siz : Marker.SIZ) (g : Progression.Layout)
    (coding : Coding) (store : Option TileCodeBlocks) (c : Fin g.numComps) (reduce : Nat) :
    Except Error Source :=
  let precs := match store with
    | some tile => tile.comps.getD c #[]
    | none => #[]
  tileComp L data (g.comp c) (siz.components.getD c default).depth.toNat
    (Assemble.fracBitsOf siz (coding.mctApplies siz) c) reduce precs

/-- G-6/G-7 at a common row-major position in the three centred spatial sources. -/
@[inline] def rgbAt (y cb cr : Source) (i : Nat) : Int × Int × Int :=
  Spec.MCT.rctInv ((y.get? i).getD 0, (cb.get? i).getD 0, (cr.get? i).getD 0)

/-- Test a reconstructed colour triple against the packed cell interval. -/
def fitsRGB (rgb : Int × Int × Int) : Bool :=
  let fits := fun z : Int => decide (-2147483648 ≤ z ∧ z ≤ 2147483647)
  fits rgb.1 && fits rgb.2.1 && fits rgb.2.2

/-- Scan compact spatial planes for RGB overflow before the in-place transform. -/
def colourFits (y cb cr : Source) : Nat → Bool
  | 0 => true
  | n + 1 => fitsRGB (rgbAt y cb cr n) && colourFits y cb cr n

/-- Borrow the spatial rasters through three centred RGB accessors. -/
def views (y cb cr : Source) : Source × Source × Source :=
  let atIdx := rgbAt y cb cr
  (.exact y.width y.height (fun i => (atIdx i).1),
   .exact cb.width cb.height (fun i => (atIdx i).2.1),
   .exact cr.width cr.height (fun i => (atIdx i).2.2))

/-- Reconstruct centred RGB for the native writer. Equal shapes pair local positions at
the respective component origins. Exact views need no additional colour rasters. -/
def colour (L : Limits) (y cb cr : Source) : Except Error (Source × Source × Source) := do
  L.check (.at .mct) .workSamples
    (y.width * y.height + cb.width * cb.height + cr.width * cr.height)
  if cb.width = y.width ∧ cb.height = y.height ∧ cr.width = y.width ∧ cr.height = y.height then
    match y, cb, cr with
    | .plane a, .plane b, .plane c =>
      if colourFits (.plane a) (.plane b) (.plane c) (a.width * a.height) then
        let (r, g, blue) ← MCT.rctInverse a b c
        return (.plane r, .plane g, .plane blue)
      else return views (.plane a) (.plane b) (.plane c)
    | a, b, c => return views a b c
  else throw (.malformed (.at .mct)
    s!"component transform on planes {y.width}×{y.height}, {cb.width}×{cb.height}, {cr.width}×{cr.height}")

end JPEG2000.ReversibleDispatch
