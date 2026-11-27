import Spec.DWT97

/-!
# Multiple-component transforms, DC level shift and clamping: specification

Plan.md §4 (C7, C8), §5.4; T.800 Annex G:

* G.2 reversible component transform (RCT). Forward (G-4/G-5):
  `Y0 = ⌊(I0 + 2·I1 + I2)/4⌋`, `Y1 = I2 − I1`, `Y2 = I0 − I1`; inverse (G-6/G-7):
  `I1 = Y0 − ⌊(Y2 + Y1)/4⌋`, `I0 = Y2 + I1`, `I2 = Y1 + I1` (component 0 = R / luminance,
  `Y1` = Cb-like `I2 − I1`, `Y2` = Cr-like `I0 − I1`). Integer division is floor division
  (`Int./` is Euclidean, which is floor for the positive divisor 4).
* G.3 irreversible component transform (ICT). Inverse (G-11..G-13):
  `I0 = Y0 + 1.402·Y2`, `I1 = Y0 − 0.34413·Y1 − 0.71414·Y2`, `I2 = Y0 + 1.772·Y1`; forward
  (G-8..G-10, reference encoder and tests): `Y0 = 0.299·I0 + 0.587·I1 + 0.114·I2`,
  `Y1 = −0.16875·I0 − 0.33126·I1 + 0.5·I2`, `Y2 = 0.5·I0 − 0.41869·I1 − 0.08131·I2`.
  **The decimal constants printed in T.800, read as exact rationals, define the
  transform** (as the Table F.4 constants do for the 9/7, `Spec.DWT97`).
* G.1 DC level shift (G-1..G-3, inverse direction): an unsigned component of bit depth `B`
  gets `+2^(B−1)` after the inverse component transform; a signed one is unchanged.
* Clamping to the component's range (`[0, 2^B − 1]` unsigned, `[−2^(B−1), 2^(B−1) − 1]`
  signed) is not specified by T.800 for reconstruction; it is the decoder's practical choice
  (OpenJPEG `opj_tcd_dc_level_shift_decode`). Irreversible paths first round the fixed-point
  value to the nearest integer (`roundFix`, ties up; OpenJPEG `opj_lrintf` rounds ties to
  even — they differ only on exact halves).

## Results

* **C7** `rctInv_rctFwd`: inverse RCT ∘ forward RCT = identity on every integer triple; also
  `rctFwd_rctInv`: the RCT is a bijection of `ℤ³` (forward ∘ inverse = identity too).
* ICT: with the decimal constants the two matrices are **not** exact inverses:
  `ictInv_ictFwd` gives the composite matrix exactly (off-diagonal entries ≤ 2.5·10⁻⁵) and
  `ictInv_ictFwd_ne` a triple it moves. C8 for the ICT (fixed point vs `ictInv`) is in
  `JPEG2000.MCT`.
* `clamp_mem`, `clamp_of_mem`, `reconRev_mem`, `reconRev_unsigned` (no clamping inside
  the range), `roundFix_err` (`|roundFix F z − z/2^F| ≤ 1/2`).
-/

namespace JPEG2000.Spec.MCT

open JPEG2000.Spec.DWT97 (abs_le_iff)

/-- Three component samples (components 0, 1, 2). -/
abbrev Triple (α : Type) := α × α × α

/-! ## RCT (G.2) -/

/-- Forward RCT (G-4/G-5): `(⌊(I0 + 2·I1 + I2)/4⌋, I2 − I1, I0 − I1)`. -/
def rctFwd : Triple Int → Triple Int
  | (i0, i1, i2) => ((i0 + 2 * i1 + i2) / 4, i2 - i1, i0 - i1)

/-- Inverse RCT (G-6/G-7): `I1 = Y0 − ⌊(Y2 + Y1)/4⌋`, `I0 = Y2 + I1`, `I2 = Y1 + I1`. -/
def rctInv : Triple Int → Triple Int
  | (y0, y1, y2) =>
    let i1 := y0 - (y2 + y1) / 4
    (y2 + i1, i1, y1 + i1)

/-- **C7 (lossless colour)**: the inverse RCT undoes the forward RCT on every integer
triple. -/
theorem rctInv_rctFwd (t : Triple Int) : rctInv (rctFwd t) = t := by
  obtain ⟨a, b, c⟩ := t
  simp only [rctFwd, rctInv, Prod.mk.injEq]
  omega

/-- The forward RCT undoes the inverse RCT on every integer triple (the RCT is a bijection
of `ℤ³`). -/
theorem rctFwd_rctInv (t : Triple Int) : rctFwd (rctInv t) = t := by
  obtain ⟨a, b, c⟩ := t
  simp only [rctFwd, rctInv, Prod.mk.injEq]
  omega

/-! ## ICT (G.3), constants read as exact rationals -/

/-- `1.402` (G-11). -/
def ki0 : Rat := 1.402
/-- `0.34413` (G-12). -/
def ki1 : Rat := 0.34413
/-- `0.71414` (G-12). -/
def ki2 : Rat := 0.71414
/-- `1.772` (G-13). -/
def ki3 : Rat := 1.772

/-- Inverse ICT (G-11..G-13): `(Y0 + 1.402·Y2, Y0 − 0.34413·Y1 − 0.71414·Y2,
Y0 + 1.772·Y1)`. -/
def ictInv : Triple Rat → Triple Rat
  | (y0, y1, y2) => (y0 + ki0 * y2, y0 - ki1 * y1 - ki2 * y2, y0 + ki3 * y1)

/-- Forward ICT (G-8..G-10). -/
def ictFwd : Triple Rat → Triple Rat
  | (i0, i1, i2) =>
    (0.299 * i0 + 0.587 * i1 + 0.114 * i2,
     -0.16875 * i0 - 0.33126 * i1 + 0.5 * i2,
     0.5 * i0 - 0.41869 * i1 - 0.08131 * i2)

/-- The composite `ictInv ∘ ictFwd` with T.800's decimal constants, exactly: close to, but
not, the identity matrix. -/
theorem ictInv_ictFwd (a b c : Rat) :
    ictInv (ictFwd (a, b, c)) =
      (a - 169 / 50000000 * b + 169 / 50000000 * c,
       31 / 16000000 * a + 2499999451 / 2500000000 * b + 8617 / 5000000000 * c,
       -1 / 40000 * a + 91 / 12500000 * b + c) := by
  simp only [ictInv, ictFwd, ki0, ki1, ki2, ki3, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> grind

/-- `ictInv ∘ ictFwd` is not the identity: it moves `(1, 0, 0)`. -/
theorem ictInv_ictFwd_ne : ictInv (ictFwd (1, 0, 0)) ≠ (1, 0, 0) := by
  rw [ictInv_ictFwd]
  intro h
  simp only [Prod.mk.injEq] at h
  have := h.2.2
  grind

/-! ## DC level shift and clamping (G.1) -/

/-- The DC offset added after the inverse transform (G-1..G-3): `2^(B−1)` for an unsigned
component of bit depth `B`, `0` for a signed one. -/
def dcOffset (signed : Bool) (depth : Nat) : Int :=
  if signed then 0 else (2 : Int) ^ (depth - 1)

/-- Smallest sample value of a component: `−2^(B−1)` signed, `0` unsigned. -/
def sampleMin (signed : Bool) (depth : Nat) : Int :=
  if signed then -((2 : Int) ^ (depth - 1)) else 0

/-- Largest sample value of a component: `2^(B−1) − 1` signed, `2^B − 1` unsigned. -/
def sampleMax (signed : Bool) (depth : Nat) : Int :=
  if signed then (2 : Int) ^ (depth - 1) - 1 else (2 : Int) ^ depth - 1

/-- Clamp `x` to `[lo, hi]`. -/
def clamp (lo hi x : Int) : Int :=
  if x < lo then lo else if hi < x then hi else x

/-- The clamp lands in `[lo, hi]` when `lo ≤ hi`. -/
theorem clamp_mem (lo hi x : Int) (h : lo ≤ hi) : lo ≤ clamp lo hi x ∧ clamp lo hi x ≤ hi := by
  unfold clamp; repeat' split
  all_goals omega

/-- The clamp does not change a value already in range. -/
theorem clamp_of_mem (lo hi x : Int) (h1 : lo ≤ x) (h2 : x ≤ hi) : clamp lo hi x = x := by
  unfold clamp; repeat' split
  all_goals omega

/-- Reversible reconstruction of one sample: DC shift, then clamp to the component's
range. -/
def reconRev (signed : Bool) (depth : Nat) (x : Int) : Int :=
  clamp (sampleMin signed depth) (sampleMax signed depth) (x + dcOffset signed depth)

/-- Round to nearest (ties up) of the fixed-point value `z / 2^F`:
`⌊(z + ⌊2^F/2⌋) / 2^F⌋`. -/
def roundFix (F : Nat) (z : Int) : Int := (z + (2 : Int) ^ F / 2) / (2 : Int) ^ F

/-- Irreversible reconstruction of one sample from a fixed-point value with `F` fractional
bits: round to the nearest integer, DC shift, clamp. -/
def reconIrrev (signed : Bool) (depth F : Nat) (z : Int) : Int :=
  reconRev signed depth (roundFix F z)

/-- `2^(B−1) ≥ 1` and `2^B = 2·2^(B−1)` for `B ≥ 1`. -/
private theorem pow_facts (depth : Nat) (h : 1 ≤ depth) :
    (1 : Int) ≤ 2 ^ (depth - 1) ∧ (2 : Int) ^ depth = 2 * 2 ^ (depth - 1) := by
  constructor
  · have : (0 : Int) < 2 ^ (depth - 1) := Int.pow_pos (by decide)
    omega
  · rw [show depth = (depth - 1) + 1 by omega, Int.pow_succ]
    simp only [Nat.add_sub_cancel]
    exact Int.mul_comm _ _

/-- The component range is non-empty for every bit depth `B ≥ 1`. -/
theorem sampleMin_le_max (signed : Bool) (depth : Nat) (h : 1 ≤ depth) :
    sampleMin signed depth ≤ sampleMax signed depth := by
  have ⟨h1, h2⟩ := pow_facts depth h
  unfold sampleMin sampleMax
  cases signed <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

/-- Every reconstructed sample lies in the component's range. -/
theorem reconRev_mem (signed : Bool) (depth : Nat) (h : 1 ≤ depth) (x : Int) :
    sampleMin signed depth ≤ reconRev signed depth x ∧
      reconRev signed depth x ≤ sampleMax signed depth :=
  clamp_mem _ _ _ (sampleMin_le_max signed depth h)

/-- An unsigned sample whose centred value is in `[−2^(B−1), 2^(B−1) − 1]` is shifted by
`2^(B−1)` and not clamped. -/
theorem reconRev_unsigned (depth : Nat) (h : 1 ≤ depth) (x : Int)
    (h1 : -(2 ^ (depth - 1)) ≤ x) (h2 : x < 2 ^ (depth - 1)) :
    reconRev false depth x = x + 2 ^ (depth - 1) := by
  have ⟨_, hp⟩ := pow_facts depth h
  unfold reconRev
  apply clamp_of_mem <;> simp only [sampleMin, sampleMax, dcOffset, Bool.false_eq_true,
    ↓reduceIte] <;> omega

/-- A signed sample in `[−2^(B−1), 2^(B−1) − 1]` is unchanged. -/
theorem reconRev_signed (depth : Nat) (x : Int)
    (h1 : -(2 ^ (depth - 1)) ≤ x) (h2 : x < 2 ^ (depth - 1)) :
    reconRev true depth x = x := by
  unfold reconRev
  rw [clamp_of_mem] <;> simp only [sampleMin, sampleMax, dcOffset, ↓reduceIte] <;> omega

/-- `roundFix F z` is a nearest integer to `z / 2^F`. -/
theorem roundFix_err (F : Nat) (z : Int) :
    (((roundFix F z : Int) : Rat) - (z : Rat) / ((2 ^ F : Nat) : Rat)).abs ≤ 1 / 2 := by
  have hP : (0 : Int) < 2 ^ F := Int.pow_pos (by decide)
  have hP2 : (2 : Int) ^ F = 1 ∨ 2 ∣ (2 : Int) ^ F := by
    cases F with
    | zero => left; rfl
    | succ k => right; exact ⟨2 ^ k, by rw [Int.pow_succ, Int.mul_comm]⟩
  unfold roundFix
  generalize hq : (z + 2 ^ F / 2) / 2 ^ F = r
  have hN : (((2 ^ F : Nat) : Int)) = (2 : Int) ^ F := by simp
  have e : ((2 ^ F : Nat) : Rat) = (((2 ^ F : Int)) : Rat) := by
    rw [← hN]; rfl
  rw [e]
  generalize hPP : (2 : Int) ^ F = P at hP hP2 hq
  -- integer bounds: `P·r ≤ z + h < P·r + P`, `h = ⌊P/2⌋`
  have h1 : P * r ≤ z + P / 2 := by rw [← hq]; exact Int.mul_ediv_self_le (by omega)
  have h2 : z + P / 2 < P * r + P := by
    rw [← hq]; have := Int.lt_mul_ediv_self_add (x := z + P / 2) hP; omega
  have l1 : 2 * (P * r) ≤ 2 * z + P := by omega
  have l2 : 2 * z ≤ 2 * (P * r) + P := by rcases hP2 with h | h <;> omega
  have hPq : (0 : Rat) < (P : Rat) := by exact_mod_cast hP
  have l1' := Rat.intCast_le_intCast.mpr l1
  have l2' := Rat.intCast_le_intCast.mpr l2
  push_cast at l1' l2'
  apply abs_le_iff.mpr
  have hz : (z : Rat) / (P : Rat) * (P : Rat) = (z : Rat) := Rat.div_mul_cancel (by grind)
  generalize (z : Rat) / (P : Rat) = w at hz ⊢
  rw [← hz] at l1' l2'
  -- `P·r ≤ w·P + P/2` and `w·P ≤ P·r + P/2`, divided by `P > 0`
  have a1 : ((r : Rat) - w - 1 / 2) * (P : Rat) ≤ 0 := by grind
  have a2 : (w - (r : Rat) - 1 / 2) * (P : Rat) ≤ 0 := by grind
  have b1 : (r : Rat) - w - 1 / 2 ≤ 0 := by
    apply Rat.not_lt.mp; intro hlt
    have := Rat.mul_pos hlt hPq; grind
  have b2 : w - (r : Rat) - 1 / 2 ≤ 0 := by
    apply Rat.not_lt.mp; intro hlt
    have := Rat.mul_pos hlt hPq; grind
  exact ⟨by grind, by grind⟩

end JPEG2000.Spec.MCT
