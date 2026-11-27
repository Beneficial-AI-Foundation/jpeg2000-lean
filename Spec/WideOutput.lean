import JPEG2000.WideOutput
import Spec.Decode

/-!
# Native reconstruction and tile placement (Plan.md §§4, 5.4, 7; T.800 B-12, B-14, G.1)

Observe a tile write at a destination coordinate on the component's reduced grid.
Its sample comes from the translated source coordinate inside the rectangle and
from the original plane everywhere else. Source integers have a common binary
scale for the component, with zero fractional bits on the reversible path.
-/

namespace JPEG2000.Spec.WideOutput

open Bytes
open JPEG2000.WideOutput

/-- The destination coordinate lies inside this translated tile-component rectangle. -/
def Inside (w h ox oy x y : Nat) : Prop :=
  ox ≤ x ∧ x < ox + w ∧ oy ≤ y ∧ y < oy + h

/-- With integer input the prepared kernel performs exactly the G.1 shift and clamp. -/
theorem sample_rev (r : NativeSampleRange) (x : Int) :
    ((prepare r 0).sample x).val = MCT.reconRev r.signed r.depth x := by
  simp [prepare, MCT.reconRev, r.lo_eq, r.hi_eq]

/-- For every binary scale the prepared kernel rounds and clamps as in Annex G. -/
theorem sample_irrev (r : NativeSampleRange) (F : Nat) (z : Int) :
    ((prepare r F).sample z).val = MCT.reconIrrev r.signed r.depth F z := by
  by_cases hf : F = 0 <;>
    simp [prepare, hf, MCT.reconIrrev, MCT.reconRev, MCT.roundFix, r.lo_eq, r.hi_eq]

private theorem floorDiv (P z : Int) (hp : 0 < P) : z / P = ((z : Rat) / P).floor := by
  have hpq : (0 : Rat) < P := by exact_mod_cast hp
  apply Int.le_antisymm
  · apply Int.not_lt.mp
    intro h
    have h' := (Rat.div_lt_iff hpq).mp (Rat.floor_lt_iff.mp h)
    have h'' : z < z / P * P := by exact_mod_cast h'
    exact (Int.not_lt.mpr (Int.ediv_mul_le _ (by omega))) h''
  · have h : ((z : Rat) / P).floor < z / P + 1 := by
      apply Rat.floor_lt_iff.mpr
      apply (Rat.div_lt_iff hpq).mpr
      have hb : z < (z / P + 1) * P := by
        rw [Int.add_mul, Int.one_mul, Int.mul_comm (z / P)]
        exact Int.lt_mul_ediv_self_add hp
      exact_mod_cast hb
    omega

/-- The integer rounding used by the kernel agrees exactly with the rational
`roundHalf` in the reference decoder, including signed ties and zero fractional bits. -/
theorem roundFix_eq_roundHalf (F : Nat) (z : Int) :
    MCT.roundFix F z = Decode.roundHalf ((z : Rat) / ((2 ^ F : Int) : Rat)) := by
  cases F with
  | zero =>
    have h : (z : Rat) / 1 = z := by
      simpa using Rat.div_mul_cancel (a := (z : Rat)) (by decide : (1 : Rat) ≠ 0)
    have half : (1/2 : Rat).floor = 0 := (floorDiv 2 1 (by decide)).symm
    simp [MCT.roundFix, Decode.roundHalf, h, Rat.add_comm _ (1/2), Rat.floor_add_intCast,
      half]
  | succ k =>
    let P := (2 : Int) ^ (k + 1)
    have hp : 0 < P := Int.pow_pos (by decide)
    have hpq : (0 : Rat) < P := by exact_mod_cast hp
    change (z + P / 2) / P = ((z : Rat) / P + 1/2).floor
    rw [floorDiv _ _ hp]
    congr 1
    have even : P / 2 * 2 = P := by simp [P, Int.pow_succ]
    have half : ((P / 2 : Int) : Rat) * 2 = (P : Rat) := by exact_mod_cast even
    have ha := Rat.div_mul_cancel (a := ((z + P / 2 : Int) : Rat)) (b := (P : Rat)) (by grind)
    have hb := Rat.div_mul_cancel (a := (z : Rat)) (b := (P : Rat)) (by grind)
    push_cast at ha
    grind

/-- Every native value is recovered from its centred integer at any fixed-point
scale, including scale one for the reversible transform. -/
theorem sample_recovers (r : NativeSampleRange) (F : Nat) (v : Int)
    (hv : r.lo ≤ v ∧ v ≤ r.hi) :
    ((prepare r F).sample ((v - MCT.dcOffset r.signed r.depth) * 2^F)).val = v := by
  rw [sample_irrev]
  let P := (2 : Int)^F
  have hp : 0 < P := Int.pow_pos (by decide)
  let off := MCT.dcOffset r.signed r.depth
  have h : MCT.roundFix F ((v - off) * P) = v - off := by
    change ((v - off) * P + P / 2) / P = v - off
    rw [Int.add_comm, Int.add_mul_ediv_right _ _ (by omega : P ≠ 0)]
    have : P / 2 / P = 0 := Int.ediv_eq_zero_of_lt (by omega) (by omega)
    omega
  change MCT.clamp _ _ (MCT.roundFix F ((v - off) * P) + off) = v
  rw [h, Int.sub_add_cancel, ← r.lo_eq, ← r.hi_eq]
  exact MCT.clamp_of_mem _ _ _ hv.1 hv.2

private theorem get?_set (dst : Bytes.WidePlane) (i j : Nat) (v : Int)
    (hi : i < dst.width * dst.height) (hv : dst.range.lo ≤ v ∧ v ≤ dst.range.hi) :
    (dst.set i v hi hv).get? j = if i = j then some v else dst.get? j := by
  by_cases hj : j < dst.width * dst.height
  · have hj' : j < (dst.set i v hi hv).width * (dst.set i v hi hv).height := hj
    simp only [Bytes.WidePlane.get?, hj, hj', ↓reduceDIte, Bytes.WidePlane.get_set dst i j v hi hj hv]
    split <;> rfl
  · have hj' : ¬j < (dst.set i v hi hv).width * (dst.set i v hi hv).height := hj
    simp only [Bytes.WidePlane.get?, hj, hj', show i ≠ j by omega, dite_false, ite_false]

private theorem coords_eq {dw x y x' y' : Nat} (hx : x < dw) (hx' : x' < dw)
    (e : dw*y + x = dw*y' + x') : x = x' ∧ y = y' := by
  have hd : 0 < dw := by omega
  constructor
  · simpa only [Nat.mul_add_mod, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hx'] using
      congrArg (· % dw) e
  · simpa only [Nat.mul_add_div hd, Nat.div_eq_of_lt hx, Nat.div_eq_of_lt hx', Nat.add_zero]
      using congrArg (· / dw) e

private theorem destIndex_inj {dw w h ox oy i j : Nat} (hx : ox + w ≤ dw)
    (hi : i < w*h) (hj : j < w*h)
    (e : destIndex dw w ox oy i = destIndex dw w ox oy j) : i = j := by
  have hw : 0 < w := by cases w <;> simp_all
  have hmi := Nat.mod_lt i hw
  have hmj := Nat.mod_lt j hw
  obtain ⟨ec, er⟩ := coords_eq (x := ox + i % w) (x' := ox + j % w) (by omega) (by omega) e
  have ec' : i % w = j % w := by omega
  have er' : i / w = j / w := by omega
  have hi' := Nat.div_add_mod i w
  rw [ec', er', Nat.div_add_mod] at hi'
  exact hi'.symm

private theorem blitCells_spec {w h : Nat} (ox oy : Nat) (r : NativeSampleRange)
    (kernel : Kernel r) (read : Fin (w * h) → Int)
    (n : Nat) (hn : n ≤ w * h) (dst : Bytes.WidePlane)
    (hx : ox + w ≤ dst.width) (hy : oy + h ≤ dst.height) (hr : dst.range = r) :
    let q := blitCells ox oy r kernel read n hn dst hx hy hr
    let di := destIndex dst.width w ox oy
    q.width = dst.width ∧ q.height = dst.height ∧ q.range = dst.range ∧
      (∀ i (hi : i < n), q.get? (di i) = some (kernel.sample (read ⟨i, Nat.lt_of_lt_of_le hi hn⟩)).val) ∧
      (∀ j, (∀ i < n, di i ≠ j) → q.get? j = dst.get? j) := by
  induction n generalizing dst with
  | zero => exact ⟨rfl, rfl, rfl, fun _ hi => by omega, fun _ _ => rfl⟩
  | succ k ih =>
    simp only [blitCells]
    let next := dst.set (destIndex dst.width w ox oy k) (kernel.sample (read ⟨k, hn⟩)).val
      (destIndex_lt hx hy hn) (hr ▸ (kernel.sample (read ⟨k, hn⟩)).property)
    specialize ih (Nat.le_of_lt hn) next hx hy hr
    refine ⟨ih.1, ih.2.1, ih.2.2.1, ?_, ?_⟩
    · intro i hi
      by_cases hik : i < k
      · exact ih.2.2.2.1 i hik
      · have : i = k := by omega
        subst i
        have he : ∀ i < k, destIndex dst.width w ox oy i ≠ destIndex dst.width w ox oy k := by
          intro i hi he
          have := destIndex_inj hx (Nat.lt_trans hi hn) hn he
          omega
        exact (ih.2.2.2.2 _ he).trans ((get?_set ..).trans (ite_eq_left rfl))
    · intro j hj
      exact (ih.2.2.2.2 j (fun i hi => hj i (by omega))).trans
        ((get?_set ..).trans (ite_eq_right (hj k (by omega))))

private theorem blit_result (L : Limits) (loc : Location) (dst : Bytes.WidePlane)
    (w h ox oy F : Nat) (read : Fin (w*h) → Int) (q : Bytes.WidePlane) :
    blit L loc dst w h ox oy F read = .ok q ↔
      dst.width * dst.height ≤ L.maxWorkSamples ∧
      dst.width * dst.height * Header.bytesPerSample dst.range.depth ≤ L.maxDecodedBytes ∧
      ∃ fit : ox + w ≤ dst.width ∧ oy + h ≤ dst.height,
        q = blitCells ox oy dst.range (prepare dst.range F) read (w*h) (Nat.le_refl _)
          dst fit.1 fit.2 rfl := by
  by_cases hw : dst.width * dst.height ≤ L.maxWorkSamples <;>
    by_cases hb : dst.width * dst.height * Header.bytesPerSample dst.range.depth ≤
        L.maxDecodedBytes <;>
    by_cases hf : ox + w ≤ dst.width ∧ oy + h ≤ dst.height <;>
    simp [blit, Limits.check, Limits.checkLe, Limits.bound, hw, hb, hf, bind, Except.bind,
      throw, pure, Except.pure, eq_comm]

/-- Blitting succeeds precisely for a contained rectangle on a destination within
both inclusive resource budgets. Empty tiles follow the same geometry checks. -/
theorem blit_succeeds (L : Limits) (loc : Location) (dst : Bytes.WidePlane)
    (w h ox oy F : Nat) (read : Fin (w*h) → Int) :
    (∃ q, blit L loc dst w h ox oy F read = .ok q) ↔
      dst.width * dst.height ≤ L.maxWorkSamples ∧
      dst.width * dst.height * Header.bytesPerSample dst.range.depth ≤ L.maxDecodedBytes ∧
      ox + w ≤ dst.width ∧ oy + h ≤ dst.height := by
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨hw, hb, hf, _⟩ := (blit_result ..).mp hq
    exact ⟨hw, hb, hf⟩
  · rintro ⟨hw, hb, hf⟩
    exact ⟨_, (blit_result ..).mpr ⟨hw, hb, hf, rfl⟩⟩

private theorem srcIndex_lt {w h x y : Nat} (hx : x < w) (hy : y < h) : y*w + x < w*h := by
  have := Nat.mul_le_mul_right w hy
  rw [Nat.succ_mul] at this
  rw [Nat.mul_comm w h]
  omega

/-- Successful placement preserves the component's geometry and format. Each
translated tile coordinate reads as its reconstructed source sample. Every valid
destination coordinate outside the rectangle keeps its previous sample. -/
theorem blit_spec {L : Limits} {loc : Location} {dst q : Bytes.WidePlane}
    {w h ox oy F : Nat} {read : Fin (w*h) → Int}
    (ok : blit L loc dst w h ox oy F read = .ok q) :
    q.width = dst.width ∧ q.height = dst.height ∧ q.range = dst.range ∧
    (∀ x y (hx : x < w) (hy : y < h),
      q.get? ((oy + y) * dst.width + (ox + x)) =
        some (MCT.reconIrrev dst.range.signed dst.range.depth F
          (read ⟨y*w + x, srcIndex_lt hx hy⟩))) ∧
    (∀ x y, x < dst.width → y < dst.height → ¬Inside w h ox oy x y →
      q.get? (y * dst.width + x) = dst.get? (y * dst.width + x)) := by
  obtain ⟨_, _, fit, rfl⟩ := (blit_result ..).mp ok
  obtain ⟨hw, hh, hr, inner, frame⟩ := blitCells_spec ox oy dst.range (prepare dst.range F)
    read (w*h) (Nat.le_refl _) dst fit.1 fit.2 rfl
  refine ⟨hw, hh, hr, ?_, ?_⟩
  · intro x y hx hy
    have hwpos : 0 < w := by omega
    have e : destIndex dst.width w ox oy (y*w + x) = (oy+y)*dst.width + (ox+x) := by
      simp only [destIndex, Nat.mul_comm y w, Nat.mul_add_mod, Nat.mod_eq_of_lt hx,
        Nat.mul_add_div hwpos, Nat.div_eq_of_lt hx, Nat.add_zero, Nat.mul_comm dst.width]
    rw [← e, inner _ (srcIndex_lt hx hy), sample_irrev]
  · intro x y hx _ outside
    apply frame
    intro i hi hit
    have hwpos : 0 < w := by cases w <;> simp_all
    have hcol := Nat.mod_lt i hwpos
    have hrow := Nat.div_lt_of_lt_mul hi
    rw [Nat.mul_comm y dst.width] at hit
    obtain ⟨ec, er⟩ := coords_eq (x := ox + i % w) (by have := fit.1; omega) hx hit
    apply outside
    simp [Inside, ← ec, ← er, hcol, hrow]

private def observed (signed : Bool) (dw dh w h ox oy F : Nat) (src : Array Int)
    (L : Limits := Limits.default) : Option (List Int) := do
  let dst ← (Bytes.WidePlane.zeroChecked Limits.default (.at .decode) dw dh 38 signed).toOption
  let dst ← dst.set? 0 1
  if hs : src.size = w*h then
    let q ← (blit L (.at .decode) dst w h ox oy F (fun i => src[i.val]'(by rw [hs]; exact i.isLt))).toOption
    (List.range (dw*dh)).mapM q.get?
  else none

-- Unequal strides, offsets on both axes, a nonzero untouched sample, unsigned
-- midpoint and maximum, and clipping in both directions before narrowing.
set_option maxRecDepth 4096 in
example : observed false 4 3 2 2 1 1 0 #[0, 137438953471, -(2^80), 2^80] =
    some [1, 0, 0, 0, 0, 137438953472, 274877906943, 0, 0, 0, 274877906943, 0] := by decide

example : observed true 4 1 4 1 0 0 0 #[-137438953472, 137438953471, -(2^80), 2^80] =
    some [-137438953472, 137438953471, -137438953472, 137438953471] := by decide

-- Fixed-point neighbours of a negative tie, both half-unit ties, and +1.5.
example : observed true 6 1 6 1 0 0 2 #[-7, -6, -5, -2, 2, 6] =
    some [-2, -1, -1, 0, 1, 2] := by decide

example : observed false 1 1 1 1 1 0 0 #[0] = none := by decide
example : observed false 1 1 1 1 0 0 0 #[0] { Limits.default with maxWorkSamples := 0 } =
    none := by decide
example : observed false 1 1 1 1 0 0 0 #[0] { Limits.default with maxDecodedBytes := 0 } =
    none := by decide

end JPEG2000.Spec.WideOutput
