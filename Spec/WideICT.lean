import JPEG2000.WideICT
import JPEG2000.MCT

/-!
# Wide inverse ICT error (Plan.md §§4, 5.1, 5.4, 7; T.800 G.3, G-11 to G-13)

Compare each checked output cell in physical units with the rational Annex G transform
of three independent reference samples. Each row propagates its own input errors and
adds at most half of one fixed-point unit, for every signed input magnitude.
-/

namespace JPEG2000.Spec.WideICT

open JPEG2000.WideICT
open Tier2.Geometry (rectArea)
open JPEG2000.Spec.DWT97 (abs_le_iff abs_mul_le)
open JPEG2000.Spec.MCT (ki0 ki1 ki2 ki3 ictInv Triple)
open JPEG2000.MCT (ictGain ictRnd)

/-- All three componentwise absolute errors are at most the corresponding bounds. -/
def Close (a b e : Triple Rat) : Prop :=
  (a.1 - b.1).abs ≤ e.1 ∧ (a.2.1 - b.2.1).abs ≤ e.2.1 ∧ (a.2.2 - b.2.2).abs ≤ e.2.2

/-- In physical units each row propagates the absolute coefficients of G.3 and adds
one half-ulp at the common precision. -/
def rowErrors (D : Rat) (e : Triple Rat) : Triple Rat :=
  (e.1 + ki0 * e.2.2 + 1 / 2 / D,
   e.1 + ki1 * e.2.1 + ki2 * e.2.2 + 1 / 2 / D,
   e.1 + ki3 * e.2.1 + 1 / 2 / D)

private theorem roundRow_err (n : Int) (D : Rat) (hp : 0 < D) :
    ((roundRow n : Rat) / D - (n : Rat) / 100000 / D).abs ≤ 1 / 2 / D := by
  have h₁ : -50000 ≤ 100000 * roundRow n - n := by unfold roundRow; omega
  have h₂ : 100000 * roundRow n - n ≤ 50000 := by unfold roundRow; omega
  have lo := Rat.intCast_le_intCast.mpr h₁
  have hi := Rat.intCast_le_intCast.mpr h₂
  push_cast at lo hi
  have err : ((roundRow n : Rat) - (n : Rat) / 100000).abs ≤ 1 / 2 := by
    apply abs_le_iff.mpr
    constructor <;> grind
  have scaled := abs_mul_le _ D⁻¹ _ err
  rw [Rat.abs_of_nonneg (Rat.le_of_lt (Rat.inv_pos.mpr hp))] at scaled
  rw [show (roundRow n : Rat) / D - (n : Rat) / 100000 / D =
    ((roundRow n : Rat) - (n : Rat) / 100000) * D⁻¹ by grind, Rat.div_def (1/2 : Rat) D]
  exact scaled

private theorem sample_err (y cb cr : Int) (D : Rat) (hp : 0 < D) (ref e : Triple Rat)
    (h : Close ((y : Rat) / D, (cb : Rat) / D, (cr : Rat) / D) ref e) :
    Close ((red y cr : Rat) / D, (green y cb cr : Rat) / D, (blue y cb : Rat) / D)
      (ictInv ref) (rowErrors D e) := by
  obtain ⟨a, b, c⟩ := ref
  obtain ⟨ea, eb, ec⟩ := e
  have r := roundRow_err (100000 * y + 140200 * cr) D hp
  have g := roundRow_err (100000 * y - 34413 * cb - 71414 * cr) D hp
  have u := roundRow_err (100000 * y + 177200 * cb) D hp
  push_cast at r g u
  simp only [Close, ictInv, rowErrors, red, green, blue, ki0, ki1, ki2, ki3,
    abs_le_iff, Rat.div_def] at *
  exact ⟨⟨by grind, by grind⟩, ⟨by grind, by grind⟩, ⟨by grind, by grind⟩⟩

/-- The exact success domain includes the three-plane work budget, valid dimensions and
equal precisions. The successful rasters retain each component's rectangle. -/
theorem ictInverse_ok (L : Limits) (y cb cr : Component) (out : Component × Component × Component) :
    ictInverse L y cb cr = .ok out ↔
      rectArea y.rect + rectArea cb.rect + rectArea cr.rect ≤ L.maxWorkSamples ∧
      ∃ h : Compatible y cb cr, out = colour y cb cr h.1 := by
  by_cases hw : rectArea y.rect + rectArea cb.rect + rectArea cr.rect ≤ L.maxWorkSamples
  · by_cases h : Compatible y cb cr <;>
      simp [ictInverse, Limits.check, Limits.checkLe, Limits.bound, hw, h, bind, Except.bind,
        pure, Except.pure, throw, eq_comm]
  · simp [ictInverse, Limits.check, Limits.checkLe, Limits.bound, hw, bind, Except.bind]

/-- Read a stored integer (in ulps) by its local raster index. -/
def fixed (p : Component) (i : Nat) : Int := p.samples.toArray.getD i 0

/-- The physical value of a fixed-point cell at a local raster index. -/
def physical (p : Component) (i : Nat) : Rat :=
  (fixed p i : Rat) / ((2 ^ p.fracBits : Nat) : Rat)

private theorem colour_get (y cb cr : Component) (shape : WideReversible.SameShape y.rect cb.rect cr.rect)
    (i : Nat) (hi : i < rectArea y.rect) :
    let out := colour y cb cr shape
    fixed out.1 i = red (fixed y i) (fixed cr i) ∧
    fixed out.2.1 i = green (fixed y i) (fixed cb i) (fixed cr i) ∧
    fixed out.2.2 i = blue (fixed y i) (fixed cb i) := by
  obtain ⟨bw, bh, rwid, rh⟩ := shape
  have hb : i < rectArea cb.rect := by simpa only [rectArea, bw, bh] using hi
  have hr : i < rectArea cr.rect := by simpa only [rectArea, rwid, rh] using hi
  simp [fixed, colour, Array.getD_eq_getD_getElem?, hi, hb, hr]

/-- In stored fixed-point units the three row errors are the propagated input errors
plus half a unit. Both the reference triple and its input error bounds are in ulps. -/
theorem ictInverse_fixed_error {L : Limits} {y cb cr : Component} {out : Component × Component × Component}
    (ok : ictInverse L y cb cr = .ok out) (i : Nat) (hi : i < rectArea y.rect)
    (ref e : Triple Rat) (h : Close (fixed y i, fixed cb i, fixed cr i) ref e) :
    Close (fixed out.1 i, fixed out.2.1 i, fixed out.2.2 i) (ictInv ref) (rowErrors 1 e) := by
  obtain ⟨_, fit, rfl⟩ := (ictInverse_ok ..).mp ok
  obtain ⟨r, g, b⟩ := colour_get y cb cr fit.1 i hi
  rw [r, g, b]
  have unit (x : Rat) : x / 1 = x := by grind
  simpa only [unit] using
    sample_err (fixed y i) (fixed cb i) (fixed cr i) 1 (by decide) ref e (by simpa only [unit] using h)

/-- **Wide C8, row by row.** At every index of the checked rasters, the actual red,
green and blue samples meet their individual G.3 bounds against the exact reference. -/
theorem ictInverse_error {L : Limits} {y cb cr : Component} {out : Component × Component × Component}
    (ok : ictInverse L y cb cr = .ok out) (i : Nat) (hi : i < rectArea y.rect)
    (ref e : Triple Rat) (h : Close (physical y i, physical cb i, physical cr i) ref e) :
    Close (physical out.1 i, physical out.2.1 i, physical out.2.2 i)
      (ictInv ref) (rowErrors ((2 ^ y.fracBits : Nat) : Rat) e) := by
  obtain ⟨_, fit, rfl⟩ := (ictInverse_ok ..).mp ok
  obtain ⟨shape, _, _, _, fb, fr⟩ := fit
  obtain ⟨r, g, b⟩ := colour_get y cb cr shape i hi
  have hp : (0 : Rat) < ((2 ^ y.fracBits : Nat) : Rat) := by exact_mod_cast Nat.two_pow_pos _
  simp only [physical, fb, fr] at h
  simp only [physical, r, g, b]
  exact sample_err (fixed y i) (fixed cb i) (fixed cr i) _ hp ref e h

/-- The existing C8 constants suffice in physical units with the largest of the three
independent error bounds, including zero input error. -/
theorem ictInverse_c8 {L : Limits} {y cb cr : Component} {out : Component × Component × Component}
    (ok : ictInverse L y cb cr = .ok out) (i : Nat) (hi : i < rectArea y.rect)
    (ref e : Triple Rat) (h : Close (physical y i, physical cb i, physical cr i) ref e) :
    let D : Rat := ((2 ^ y.fracBits : Nat) : Rat)
    let E := ictGain * max e.1 (max e.2.1 e.2.2) + ictRnd / D
    Close (physical out.1 i, physical out.2.1 i, physical out.2.2 i) (ictInv ref) (E, E, E) := by
  have rows := ictInverse_error ok i hi ref e h
  let m := max e.1 (max e.2.1 e.2.2)
  have hm : e.1 ≤ m ∧ e.2.1 ≤ m ∧ e.2.2 ≤ m := by dsimp [m]; grind
  have hn : 0 ≤ m := Rat.le_trans (Rat.le_trans Rat.abs_nonneg h.1) hm.1
  have hp : (0 : Rat) < ((2 ^ y.fracBits : Nat) : Rat) := by exact_mod_cast Nat.two_pow_pos _
  have inv := Rat.le_of_lt (Rat.inv_pos.mpr hp)
  change Close _ _ (ictGain * m + _, ictGain * m + _, ictGain * m + _)
  simp only [Close, rowErrors, ki0, ki1, ki2, ki3, ictGain, ictRnd, Rat.div_def] at rows ⊢
  exact ⟨by grind, by grind, by grind⟩

private def strip (x F : Nat) (a : Array Int) : Component :=
  ⟨⟨⟨x, 0, x + a.size, 1⟩, ⟨a, by simp [rectArea, Header.Rect.width, Header.Rect.height]⟩⟩, F⟩

private def observed (L : Limits) (y cb cr : Component) :=
  (ictInverse L y cb cr).toOption.map fun (r, g, b) =>
    ((r.fracBits, r.samples.toArray), (g.fracBits, g.samples.toArray), (b.fracBits, b.samples.toArray))

-- Both signed red/blue ties, and green remainders 49999, 50000, 50001.
-- Distinct origins and the exact aggregate budget are admissible.
example : observed { Limits.default with maxWorkSamples := 15 }
    (strip 0 7 #[2, -2, 0, 0, 0]) (strip 8 7 #[125, -125, 95477, 50000, 4523])
    (strip 3 7 #[250, -250, 0, 0, 0]) =
    some ((7, #[353, -352, 0, 0, 0]), (7, #[-220, 220, -32857, -17206, -1556]),
          (7, #[224, -223, 169185, 88600, 8015])) := by decide +kernel

-- Signed inputs and outputs beyond machine-word range, with non-integral chroma terms.
example : let t : Int := 2^80
    observed Limits.default (strip 0 0 #[-100000*t]) (strip 0 0 #[100000*t + 125])
      (strip 0 0 #[-100000*t - 250]) =
    some ((0, #[-240200*t - 350]), (0, #[-62999*t + 136]), (0, #[77200*t + 222])) := by decide +kernel

-- Green cancels two individually sub-unit contributions before rounding.
example : green 0 1 (-1) = 0 := by decide

example : (ictInverse Limits.default (strip 0 7 #[1]) (strip 0 7 #[1, 2])
    (strip 0 7 #[1])).toOption.isNone := by decide

-- Equal areas but different row strides cannot be paired cellwise.
example : (ictInverse Limits.default (strip 0 7 #[0, 0]) ⟨⟨⟨0, 0, 1, 2⟩, #v[0, 0]⟩, 7⟩
    (strip 1 7 #[0, 0])).toOption.isNone := by decide

example : (ictInverse Limits.default (strip 0 6 #[]) (strip 0 7 #[])
    (strip 0 6 #[])).toOption.isNone := by decide

example : (ictInverse Limits.default (strip 0 0 #[]) (strip 1 0 #[])
    ⟨⟨⟨2, 0, 1, 1⟩, #v[]⟩, 0⟩).toOption.isNone := by decide

example : (ictInverse { Limits.default with maxWorkSamples := 2 }
    (strip 0 0 #[1]) (strip 0 0 #[2]) (strip 0 0 #[3])).toOption.isNone := by decide

end JPEG2000.Spec.WideICT
