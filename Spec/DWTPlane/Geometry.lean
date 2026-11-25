import Spec.Equiv

/-!
# Band geometry of the Mallat layout (B-14, B-15)

Plan.md §4 (C9), §5.2 "DWT"; T.800 Annex B.5 (B-14 resolution rectangles `⌈tc / 2^(NL−r)⌉`,
B-15 sub-band rectangles `⌈(tc − 2^(nb−1)·o) / 2^nb⌉`), Annex F.3.3 (`2D_INTERLEAVE`).
Task 7.1d.

The arithmetic facts behind the Mallat layout of `JPEG2000.DWT53`:

* `halfN_coords`: the iterated halving `DWT53.halfN tc k` is `⌈tc / 2^k⌉` (`cdivPow`);
* `bandCoord_high` / `bandCoord_low`: a B-15 band coordinate is `⌊⌈c / 2^(nb−1)⌉ / 2⌋` for a
  high-pass direction and `⌈c / 2^nb⌉` for a low-pass one;
* `cdivPow_add`: `⌈⌈c / 2^a⌉ / 2^b⌉ = ⌈c / 2^(a+b)⌉` — the reduced-resolution identity
  (`bandRect_reduce`: band `b` of level `nb` of the reduced tile-component is band `b` of
  level `nb + reduce` of the full one);
* `specRect_halfN`: the spec rectangles `Spec.DWT53.Rect.half` iterated (`rhalf`) are the
  fast `halfN` rectangles.
-/

namespace JPEG2000.Spec.DWTPlane

open JPEG2000 JPEG2000.Header JPEG2000.Tier2.Geometry

/-- `⌈⌈c / 2^k⌉ / 2⌉ = ⌈c / 2^(k+1)⌉`. -/
theorem cdivPow_succ (c k : Nat) : cdivPow c (k + 1) = (cdivPow c k + 1) / 2 := by
  unfold cdivPow cdiv
  have hP : 0 < 2 ^ k := Nat.two_pow_pos k
  generalize hp : 2 ^ k = P at hP
  rw [Nat.pow_succ, hp, ← Nat.div_div_eq_div_mul]
  have : c + P * 2 - 1 = (c + P - 1) + P * 1 := by
    have : 1 ≤ P := hP
    rw [Nat.mul_one]; omega
  rw [this, Nat.add_mul_div_left _ _ hP]

/-- `⌈c / 2^0⌉ = c`. -/
theorem cdivPow_zero (c : Nat) : cdivPow c 0 = c := by
  simp [cdivPow, cdiv]

/-- `⌈⌈c / 2^a⌉ / 2^b⌉ = ⌈c / 2^(a+b)⌉`. -/
theorem cdivPow_add (c a b : Nat) : cdivPow (cdivPow c a) b = cdivPow c (a + b) := by
  induction b with
  | zero => simp [cdivPow_zero]
  | succ b ih => rw [cdivPow_succ, ih, ← Nat.add_assoc, cdivPow_succ]

/-- `halfN tc k` is `⌈tc / 2^k⌉` on every coordinate (B-14). -/
theorem halfN_coords (tc : Rect) (k : Nat) :
    (DWT53.halfN tc k).x0 = cdivPow tc.x0 k ∧ (DWT53.halfN tc k).y0 = cdivPow tc.y0 k ∧
    (DWT53.halfN tc k).x1 = cdivPow tc.x1 k ∧ (DWT53.halfN tc k).y1 = cdivPow tc.y1 k := by
  induction k with
  | zero => simp [DWT53.halfN, cdivPow_zero]
  | succ k ih =>
    simp only [DWT53.halfN, DWT53.halfRect, ih.1, ih.2.1, ih.2.2.1, ih.2.2.2, cdivPow_succ,
      and_self]

/-- A high-pass band coordinate (B-15 with `o = 1`, level `k + 1`) is `⌊⌈c / 2^k⌉ / 2⌋`. -/
theorem bandCoord_high (c k : Nat) : bandCoord c (k + 1) 1 = cdivPow c k / 2 := by
  unfold bandCoord
  simp only [show ¬ (1 = 0 ∨ k + 1 = 0) by omega, ↓reduceIte, Nat.add_sub_cancel]
  unfold cdivPow cdiv
  have hP : 0 < 2 ^ k := Nat.two_pow_pos k
  rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
  generalize 2 ^ k = P at hP ⊢
  by_cases hc : P ≤ c
  · congr 1; omega
  · rw [Nat.div_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega)]

/-- A low-pass band coordinate (B-15 with `o = 0`) is `⌈c / 2^nb⌉`. -/
theorem bandCoord_low (c nb : Nat) : bandCoord c nb 0 = cdivPow c nb := by
  simp [bandCoord]

/-- Band coordinates at level 0 are the coordinates themselves. -/
theorem bandCoord_zero (c o : Nat) : bandCoord c 0 o = c := by
  simp [bandCoord, cdivPow_zero]

/-- B-15 on a reduced tile-component: a band coordinate of level `nb` of `⌈c / 2^red⌉` is the
band coordinate of level `nb + red` of `c` (for `nb ≥ 1`, or `o = 0`). -/
theorem bandCoord_reduce (c red nb o : Nat) (h : 1 ≤ nb ∨ o = 0) (ho : o ≤ 1) :
    bandCoord (cdivPow c red) nb o = bandCoord c (nb + red) o := by
  rcases (by omega : o = 0 ∨ o = 1) with ho | ho <;> subst ho
  · rw [bandCoord_low, bandCoord_low, cdivPow_add, Nat.add_comm]
  · obtain ⟨k, rfl⟩ : ∃ k, nb = k + 1 := ⟨nb - 1, by omega⟩
    rw [show k + 1 + red = (k + red) + 1 by omega, bandCoord_high, bandCoord_high, cdivPow_add,
      Nat.add_comm red k]

/-- `xob` is 0 or 1. -/
theorem Band.xob_le (b : Band) : b.xob ≤ 1 := by cases b <;> decide
/-- `yob` is 0 or 1. -/
theorem Band.yob_le (b : Band) : b.yob ≤ 1 := by cases b <;> decide

/-- **Reduced-resolution band identity** (B-15): band `b` of decomposition level `nb` of the
tile-component reduced by `red` levels (`Assemble.reduceRect`) is band `b` of level
`nb + red` of the full tile-component, when `nb ≥ 1` or `b = LL`. -/
theorem bandRect_reduce (tc : Rect) (red nb : Nat) (b : Band) (h : 1 ≤ nb ∨ b = .LL) :
    bandRect (Assemble.reduceRect tc red) nb b = bandRect tc (nb + red) b := by
  have hx : 1 ≤ nb ∨ b.xob = 0 := by
    rcases h with h | h
    · exact .inl h
    · subst h; exact .inr rfl
  have hy : 1 ≤ nb ∨ b.yob = 0 := by
    rcases h with h | h
    · exact .inl h
    · subst h; exact .inr rfl
  simp only [bandRect, Assemble.reduceRect,
    bandCoord_reduce _ _ _ _ hx (Band.xob_le b), bandCoord_reduce _ _ _ _ hy (Band.yob_le b)]

/-! ## Spec rectangles -/

/-- `Rect.half` iterated `k` times (outermost last: `rhalf r (k+1) = rhalf r.half k`). -/
def rhalf : Spec.DWT53.Rect → Nat → Spec.DWT53.Rect
  | r, 0 => r
  | r, k + 1 => rhalf r.half k

/-- `rhalf` peeled from the other end. -/
theorem rhalf_succ (r : Spec.DWT53.Rect) (k : Nat) : rhalf r (k + 1) = (rhalf r k).half := by
  induction k generalizing r with
  | zero => rfl
  | succ k ih => simp only [rhalf] at ih ⊢; exact ih r.half

/-- The spec rectangle of `halfRect r` is the spec halving. -/
theorem specRect_halfRect (r : Rect) : DWT53.specRect (DWT53.halfRect r) = (DWT53.specRect r).half := by
  simp only [DWT53.specRect, DWT53.halfRect, Spec.DWT53.Rect.half, Spec.DWT53.Rect.mk.injEq]
  omega

/-- The spec rectangle of `halfN tc k` is `rhalf (specRect tc) k`. -/
theorem specRect_halfN (tc : Rect) (k : Nat) :
    DWT53.specRect (DWT53.halfN tc k) = rhalf (DWT53.specRect tc) k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [DWT53.halfN, specRect_halfRect, ih, rhalf_succ]

/-- Halving keeps the width monotone. -/
theorem halfN_mono (tc : Rect) (k : Nat) :
    (DWT53.halfN tc (k + 1)).x1 - (DWT53.halfN tc (k + 1)).x0 ≤
      (DWT53.halfN tc k).x1 - (DWT53.halfN tc k).x0 ∧
    (DWT53.halfN tc (k + 1)).y1 - (DWT53.halfN tc (k + 1)).y0 ≤
      (DWT53.halfN tc k).y1 - (DWT53.halfN tc k).y0 := by
  simp only [DWT53.halfN, DWT53.halfRect]; omega

end JPEG2000.Spec.DWTPlane
