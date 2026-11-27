import JPEG2000.WideQuant
import JPEG2000.WideReversible

/-!
# Wide inverse ICT (Plan.md §§4, 5.1, 5.4, 7; T.800 G.3, G-11 to G-13)

The three reconstructed tile-components carry the binary precision selected before
dequantisation. The decimal matrix is exact at denominator 100000. Rounding each
complete row once leaves its output at the same binary precision for G.1.
-/

namespace JPEG2000.WideICT

open Tier2.Geometry (rectArea)
open WideReversible (SameShape)

/-- A spatial plane whose integer cells denote multiples of `2⁻ᶠ`. -/
structure Component extends WideQuant.Plane where
  /-- Binary fractional bits of every cell. -/
  fracBits : Nat

/-- Round a signed numerator over 100000 to nearest, with ties towards positive infinity. -/
@[inline] def roundRow (n : Int) : Int := (n + 50000) / 100000

/-- Red row of G.3 on fixed-point luma and red chroma. -/
@[inline] def red (y cr : Int) : Int := roundRow (100000 * y + 140200 * cr)

/-- Green row of G.3, rounding after both chroma contributions. -/
@[inline] def green (y cb cr : Int) : Int := roundRow (100000 * y - 34413 * cb - 71414 * cr)

/-- Blue row of G.3 on fixed-point luma and blue chroma. -/
@[inline] def blue (y cb : Int) : Int := roundRow (100000 * y + 177200 * cb)

/-- An ordered rectangle can represent an empty or nonempty component. -/
def Ordered (r : Header.Rect) : Prop := r.x0 ≤ r.x1 ∧ r.y0 ≤ r.y1

instance (r : Header.Rect) : Decidable (Ordered r) := by unfold Ordered; infer_instance

/-- Corresponding local coordinates have equal dimensions and all inputs use the same
binary scale. Each plane's vector already enforces its own raster length. -/
def Compatible (y cb cr : Component) : Prop :=
  SameShape y.rect cb.rect cr.rect ∧ Ordered y.rect ∧ Ordered cb.rect ∧ Ordered cr.rect ∧
    cb.fracBits = y.fracBits ∧ cr.fracBits = y.fracBits

instance (y cb cr : Component) : Decidable (Compatible y cb cr) := by
  unfold Compatible; infer_instance

/-- Materialise the three output rasters. Each retains its own component-grid origin,
and all carry the luma plane's common binary scale. -/
def colour (y cb cr : Component) (h : SameShape y.rect cb.rect cr.rect) :
    Component × Component × Component :=
  let hb : rectArea cb.rect = rectArea y.rect := by simp only [rectArea, h.1, h.2.1]
  let hr : rectArea cr.rect = rectArea y.rect := by simp only [rectArea, h.2.2.1, h.2.2.2]
  let r := Vector.ofFn fun i : Fin (rectArea y.rect) =>
    red y.samples[i] (cr.samples[i.val]'(by simpa only [hr] using i.isLt))
  let g := Vector.ofFn fun i : Fin (rectArea cb.rect) =>
    green (y.samples[i.val]'(by simpa only [hb] using i.isLt)) cb.samples[i]
      (cr.samples[i.val]'(by rw [hr, ← hb]; exact i.isLt))
  let b := Vector.ofFn fun i : Fin (rectArea cr.rect) =>
    blue (y.samples[i.val]'(by simpa only [hr] using i.isLt)) (cb.samples[i.val]'(by rw [hb, ← hr]; exact i.isLt))
  (⟨⟨y.rect, r⟩, y.fracBits⟩, ⟨⟨cb.rect, g⟩, y.fracBits⟩, ⟨⟨cr.rect, b⟩, y.fracBits⟩)

/-- Apply the wide ICT after checking the combined work budget, grid dimensions and
fixed-point precisions. The result is centred and ready for native G.1 output. -/
def ictInverse (L : Limits) (y cb cr : Component) : Except Error (Component × Component × Component) := do
  L.check (.at .mct) .workSamples (rectArea y.rect + rectArea cb.rect + rectArea cr.rect)
  if h : Compatible y cb cr then return colour y cb cr h.1
  else throw (.malformed (.at .mct) "incompatible wide ICT component grids or fractional bits")

end JPEG2000.WideICT
