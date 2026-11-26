import JPEG2000.Assemble
import JPEG2000.WideOutput

/-!
# Native component output (Plan.md §§4, 5.1, 5.4, 7; T.800 B.2, B-12, B-14, G.1)

Allocate the reduced component images together. After inverse MCT, write each tile on
its own component grids. The SIZ format selects exactly one backing buffer. Centred
inputs may be ordinary reconstructed planes or exact integers at a common binary scale.
-/

namespace JPEG2000.NativeOutput

open Bytes Header Marker

/-- A post-MCT tile-component, before G.1. The integer accessor can borrow a
wider reconstruction buffer without converting it to a second sample plane. -/
inductive Source where
  /-- Ordinary 32-bit integer or fixed-point cells from tile reconstruction. -/
  | plane (p : Plane)
  /-- Exact centred samples at the component's chosen binary scale. -/
  | exact (w h : Nat) (read : Fin (w * h) → Int)

/-- Width of the reconstructed tile-component. -/
def Source.width : Source → Nat
  | .plane p => p.width
  | .exact w _ _ => w

/-- Height of the reconstructed tile-component. -/
def Source.height : Source → Nat
  | .plane p => p.height
  | .exact _ h _ => h

/-- Read a centred source cell at full precision. -/
def Source.read : (s : Source) → Fin (s.width * s.height) → Int
  | .plane p, i => (p.get i.val i.isLt).toInt
  | .exact _ _ f, i => f i

/-- Checked, row-major observation before DC reconstruction. -/
def Source.get? (s : Source) (i : Nat) : Option Int :=
  if h : i < s.width * s.height then some (s.read ⟨i, h⟩) else none

/-- Physical output storage, selected once from the SIZ sample interval. -/
inductive Storage where
  /-- Four physical bytes per native sample. -/
  | narrow (p : Plane)
  /-- Eight physical bytes per native sample. -/
  | wide (p : WidePlane)

/-- The native interval fits a signed 32-bit cell. -/
def compact (c : Component) : Bool :=
  Spec.MCT.sampleMin c.signed c.depth.toNat ≥ -2147483648 &&
  Spec.MCT.sampleMax c.signed c.depth.toNat ≤ 2147483647

/-- Check backing dimensions and format against image-grid metadata. -/
def Storage.matches (r : Rect) (c : Component) : Storage → Bool
  | .narrow p => p.width == r.width && p.height == r.height && compact c
  | .wide p => p.width == r.width && p.height == r.height &&
      p.range.signed == c.signed && p.range.depth == c.depth.toNat && !compact c

/-- A reduced component image with its original SIZ descriptor and a single backing buffer. -/
structure OutputComponent where
  /-- Image rectangle on this component's reduced grid. -/
  rect : Rect
  /-- Original signedness, precision and horizontal/vertical separation. -/
  format : Component
  /-- The SIZ precision is admitted by Part 1. -/
  precision : 1 ≤ format.depth.toNat ∧ format.depth.toNat ≤ 38
  /-- The compact or wide native plane. -/
  storage : Storage
  /-- The backing has precisely the declared shape and sample representation. -/
  valid : storage.matches rect format

/-- Exact integer sample access on the reduced component grid, in row-major order. -/
def OutputComponent.get? (d : OutputComponent) (i : Nat) : Option Int :=
  match d.storage with
  | .narrow p => (p.get? i).map Int32.toInt
  | .wide p => p.get? i

/-- Physical geometry and format for every component, in SIZ order. -/
def layout (s : SIZ) (reduce : Nat) : Array (Rect × Component) :=
  s.components.map fun c => (Assemble.reduceRect (compRect (imageRect s) c) reduce, c)

/-- Total sample cells across reduced component grids. -/
def cells (rs : Array (Rect × Component)) : Nat :=
  rs.foldl (fun n (r, _) => n + r.width * r.height) 0

/-- Declared output bytes across all components (each uses its own precision). -/
def decodedBytes (rs : Array (Rect × Component)) : Nat :=
  rs.foldl (fun n (r, c) => n + r.width * r.height * bytesPerSample c.depth.toNat) 0

/-- Allocate one zero backing after the aggregate limit checks. -/
def allocOne (r : Rect) (c : Component) : Except Error OutputComponent :=
  if hd : 1 ≤ c.depth.toNat ∧ c.depth.toNat ≤ 38 then
    if hc : compact c then
      .ok ⟨r, c, hd, .narrow (Plane.zero r.width r.height), by simp [Storage.matches, Plane.zero, hc]⟩
    else
      .ok ⟨r, c, hd, .wide (WidePlane.zero r.width r.height c.depth.toNat c.signed hd), by
        simp [Storage.matches, WidePlane.zero, hc]⟩
  else .error (.malformed (.at .decode) "native sample precision outside 1 to 38")

/-- Check reduction and both aggregate budgets before allocating any plane. -/
def allocOutput (L : Limits) (s : SIZ) (reduce : Nat) : Except Error (Array OutputComponent) := do
  L.check (.at .decode) .decompLevels reduce
  let rs := layout s reduce
  L.check (.at .decode) .workSamples (cells rs)
  L.check (.at .decode) .decodedBytes (decodedBytes rs)
  rs.mapFinIdxM fun _ (r, c) _ => allocOne r c

/-- Fill the first `n` cells of a temporary compact tile after exact reconstruction. -/
def fill {N : Nat} (f : Fin N → Int32) (n : Nat) (hn : n ≤ N) (b : DWT53.Buf N) :
    DWT53.Buf N :=
  match n with
  | 0 => b
  | k + 1 => fill f k (Nat.le_of_lt hn) (b.set k (f ⟨k, hn⟩) hn)

/-- Reconstruct exact centred input into a tile whose final interval fits compact storage. -/
def exactTile (src : Source) (r : NativeSampleRange)
    (_fits : -2147483648 ≤ r.lo ∧ r.hi ≤ 2147483647) (F : Nat) : Plane :=
  let kernel := WideOutput.prepare r F
  let f := fun i => Int32.ofInt (kernel.sample (src.read i)).val
  (fill f _ (Nat.le_refl _) ⟨Plane.zero src.width src.height, rfl⟩).1

/-- Use the ordinary fixed-width G.1 kernel when its checked preconditions hold. -/
def narrowTile (src : Source) (r : NativeSampleRange)
    (fits : -2147483648 ≤ r.lo ∧ r.hi ≤ 2147483647) (F : Nat) : Plane :=
  match src with
  | .plane p =>
    match MCT.DcShift.make r.signed r.depth F with
    | .ok dc => if F = 0 then MCT.dcShiftClampRev dc p else MCT.dcShiftClampIrrev dc p
    | .error _ => exactTile (.plane p) r fits F
  | .exact .. => exactTile src r fits F

/-- Package a backing only when its shape and sample representation match the metadata. -/
def finish (r : Rect) (c : Component) (hd : 1 ≤ c.depth.toNat ∧ c.depth.toNat ≤ 38)
    (b : Storage) : Except Error OutputComponent :=
  if h : b.matches r c then .ok ⟨r, c, hd, b, h⟩
  else .error (.malformed (.at .decode) "native component backing disagrees with grid or format")

/-- The absolute tile rectangle is ordered, contained and exactly the shape of its source. -/
def fitsTile (d r : Rect) (src : Source) : Bool :=
  d.x0 ≤ r.x0 && r.x0 ≤ r.x1 && r.x1 ≤ d.x1 &&
  d.y0 ≤ r.y0 && r.y0 ≤ r.y1 && r.y1 ≤ d.y1 &&
  src.width == r.width && src.height == r.height

/-- Write one reconstructed component at its absolute reduced tile rectangle.
Reject inconsistent extents and offsets before allocating or reading any tile cell. -/
def writeComponent (L : Limits) (dst : OutputComponent) (r : Rect) (F : Nat) (src : Source) :
    Except Error OutputComponent := do
  let d := dst.rect
  if !fitsTile d r src then
    throw (.malformed (.at .decode) "tile-component shape or offset outside the reduced image")
  let ox := r.x0 - d.x0
  let oy := r.y0 - d.y0
  match hs : dst.storage with
  | .wide p =>
    let q ← WideOutput.blit L (.at .decode) p src.width src.height ox oy F src.read
    finish d dst.format dst.precision (.wide q)
  | .narrow p =>
    L.check (.at .decode) .workSamples (d.width * d.height)
    L.check (.at .decode) .decodedBytes (d.width * d.height * bytesPerSample dst.format.depth.toNat)
    let c := dst.format
    let range : NativeSampleRange := ⟨_, c.signed, dst.precision, _, _, rfl, rfl⟩
    have fits : -2147483648 ≤ range.lo ∧ range.hi ≤ 2147483647 := by
      have hv := dst.valid
      simp only [hs, Storage.matches, Bool.and_eq_true] at hv
      simpa [compact] using hv.2
    let q ← Assemble.blit p (narrowTile src range fits F) ox oy
    finish d c dst.precision (.narrow q)

/-- Write all post-MCT planes of one tile. Use the layout and coding already obtained
from `Progression.Layout.ofHeader`; the ICT uses the shared scale of the first three
components. Reconstruction at a different fixed-point scale supplies the actual number
of fractional bits per irreversible component. Reversible inputs always have scale one.
The indexed traversal consumes each destination backing in place. -/
def writeTile (L : Limits) (s : SIZ) (reduce : Nat) (g : Progression.Layout) (coding : Coding)
    (dst : Array OutputComponent) (planes : Array Source)
    (irrevBits : Nat → Nat := Assemble.fracBitsOf s (coding.mctApplies s)) :
    Except Error (Array OutputComponent) := do
  L.check (.at .decode) .decompLevels reduce
  if h : dst.size = s.components.size ∧ dst.size = g.numComps ∧ dst.size = planes.size then
    dst.mapFinIdxM fun i d hi => do
      let tc := g.comp i
      let c := s.components[i]'(h.1 ▸ hi)
      if d.format != c || d.rect != Assemble.reduceRect (compRect (imageRect s) c) reduce then
        throw (.malformed (.at .decode) "output component disagrees with SIZ or reduction")
      if reduce > tc.params.levels then
        throw (.unsupported (.at .decode) "resolution reduction exceeds tile-component levels")
      let F := if tc.params.transform == .reversible53 then 0 else irrevBits i
      writeComponent L d (Assemble.reduceRect tc.rect reduce) F (planes[i]'(h.2.2 ▸ hi))
  else throw (.malformed (.at .decode) "tile and output component counts disagree")

end JPEG2000.NativeOutput
