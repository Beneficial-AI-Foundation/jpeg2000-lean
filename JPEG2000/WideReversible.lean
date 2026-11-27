import JPEG2000.DWT53

/-!
# Wide reversible reconstruction (Plan.md §§4, 5.1, 5.4 and 7; T.800 F.3 and G.2)

The input is the Mallat rectangle at the requested reduction. Detail bands retain
the original row stride throughout synthesis. Each completed resolution, including
the row-pass intermediate, is a packed raster. All arithmetic through the inverse
RCT is signed integer arithmetic. G.1 consumes these centred output samples.
-/

namespace JPEG2000.WideReversible

open Header (Rect)
open DWT53 (halfRect srcIdx passVal)

/-- Materialise a row-major raster of local coordinates. -/
def raster (w h : Nat) (sample : Nat → Nat → Int) : Array Int :=
  Array.ofFn (n := w * h) fun i => sample (i.val % w) (i.val / w)

/-- One output of a 5/3 synthesis line. F-5 and F-6 use the mirrored
neighbours from the ordinary kernel, with exact integer sums and floor division. -/
def lift (start n : Nat) (read : Nat → Int) (k : Nat) : Int :=
  if n ≤ 1 then
    if start % 2 = 0 then read k else read k / 2
  else
    let even := fun i => if (start + i) % 2 = 0 then passVal true n read i else read i
    if (start + k) % 2 = 0 then even k else passVal false n even k

/-- Recursively reconstruct the packed LL raster, then lift the rows and columns
of this resolution. The original Mallat plane supplies the three detail bands. -/
def synthesize (p : Array Int) (stride : Nat) (r : Rect) : Nat → Array Int
  | 0 => raster r.width r.height fun x y => p.getD (y * stride + x) 0
  | n + 1 =>
    let low := halfRect r
    let ll := synthesize p stride low n
    let interleaved := fun x y =>
      let col := srcIdx r.x0 low.width x
      let row := srcIdx r.y0 low.height y
      if (r.x0 + x) % 2 = 0 ∧ (r.y0 + y) % 2 = 0 then
        ll.getD (row * low.width + col) 0
      else p.getD (row * stride + col) 0
    let rows := raster r.width r.height fun x y =>
      lift r.x0 r.width (fun k => interleaved k y) x
    raster r.width r.height fun x y =>
      lift r.y0 r.height (fun k => rows.getD (k * r.width + x) 0) y

/-- A plane has ordered endpoints and exactly one cell per local coordinate. -/
def Fits (r : Rect) (p : Array Int) : Prop :=
  r.x0 ≤ r.x1 ∧ r.y0 ≤ r.y1 ∧ p.size = r.width * r.height

instance (r : Rect) (p : Array Int) : Decidable (Fits r p) := by
  unfold Fits; infer_instance

/-- Checked inverse 5/3 on a reduced tile-component and its remaining levels.
An empty or zero-level component already holds its final spatial samples. -/
def idwt53 (L : Limits) (r : Rect) (nl : Nat) (p : Array Int) : Except Error (Array Int) := do
  L.check DWT53.loc .decompLevels nl
  L.check DWT53.loc .workSamples (r.width * r.height)
  if Fits r p then
    return if nl = 0 ∨ p.isEmpty then p else synthesize p r.width r nl
  else throw (.malformed DWT53.loc "invalid wide Mallat rectangle or plane length")

/-- The three RCT components must have equal dimensions. Their local row-major
coordinates correspond, even if their component-grid origins differ. -/
def SameShape (r s t : Rect) : Prop :=
  s.width = r.width ∧ s.height = r.height ∧ t.width = r.width ∧ t.height = r.height

instance (r s t : Rect) : Decidable (SameShape r s t) := by
  unfold SameShape; infer_instance

/-- G-6 and G-7 on equally sized component rasters. Materialise green once and
add the two chroma differences back to it. -/
def colour (y cb cr : Array Int) : Array Int × Array Int × Array Int :=
  let green := Array.ofFn (n := y.size) fun i =>
    y[i] - (cr.getD i.val 0 + cb.getD i.val 0) / 4
  (Array.zipWith (· + ·) cr green, green, Array.zipWith (· + ·) cb green)

/-- Checked inverse RCT on three reconstructed wide components. The tile work
budget counts the samples of all three planes. Results are centred G.2 values. -/
def rctInverse (L : Limits) (r s t : Rect) (y cb cr : Array Int) :
    Except Error (Array Int × Array Int × Array Int) := do
  let n := r.width * r.height
  L.check (.at .mct) .workSamples (n + s.width * s.height + t.width * t.height)
  if SameShape r s t ∧ Fits r y ∧ Fits s cb ∧ Fits t cr then
    return colour y cb cr
  else throw (.malformed (.at .mct) "wide RCT component dimensions or lengths differ")

end JPEG2000.WideReversible
