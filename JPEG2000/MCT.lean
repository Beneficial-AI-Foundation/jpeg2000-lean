import JPEG2000.Bytes
import JPEG2000.Error
import JPEG2000.DWT53
import JPEG2000.DWT97
import Spec.MCT

/-!
# Inverse component transforms, DC level shift and clamping (fast, `Int32` planes)

Plan.md §4 (C7, C8), §5.4, §6; T.800 Annex G (G.1 DC level shift, G.2 RCT, G.3 ICT). The
specification is `Spec.MCT`.

## Number formats

* Reversible path: cells are the integer samples (`Int32`), as produced by the 5/3
  (`JPEG2000.DWT53`).
* Irreversible path: cells are fixed point, `z` standing for `z / 2^F` with
  `F = DWT97.fracBits depth` (as produced by `JPEG2000.DWT97.idwt97`). The ICT keeps the
  format; `dcShiftClampIrrev` rounds to the nearest integer (ties up), shifts and clamps.

## Kernels and what is proved

* `rctSample`: inverse RCT on three `Int32` cells in `Int64`, results saturated to `Int32`.
  `rctSample_eq`: it equals `Spec.MCT.rctInv` followed by the saturation, exactly;
  `rctSample_exact`: with inputs `|y| < 2^29` nothing saturates, so fast = spec exactly.
* `ictSample`: inverse ICT with the constants at `C = 30` fractional bits (`q0 … q3`,
  each `round(c · 2^30)`), one rounding per output (`rnd`, `Int64` intermediates proved
  exact), saturated to `Int32`. `ictSample_eq`: it equals the integer model `ictQ` followed
  by the saturation.
* **C8 (ICT)** `ict_c8`: if each fixed-point input `z_i / 2^F` (any `|z_i| ≤ 2^31`) is
  within `e` of an exact value `y_i`, every output of `ictQ`, divided by `2^F`, is within
  `ictGain · e + ictRnd / 2^F` of `Spec.MCT.ictInv y`, with `ictGain = 2.772` (the largest
  row sum of absolute coefficients, `1 + 1.772`) and `ictRnd = 5/2` (one rounding `1/2`
  plus at most one ulp per constant from the 30-bit constants at `|z| ≤ 2^31`). The row
  lemma `ictRow_err` gives the sharper per-row form (gain `1 + |a| + |b|`, rounding
  `1/2 + Σ|ĉ/2^30 − c|·M` for inputs bounded by `M`). Composition with the 9/7: the DWT
  output carries `e = En nl 0 / 2^F` (`DWT97.qsrMulti_err_frac`), so the ICT output is
  within `(2.772 · En nl 0 + 2.5) / 2^F`.
* Saturation is harmless after reconstruction: `reconIrrev_sat` shows that for `F + B ≤ 32`
  (true for `F = fracBits B`, `B ≤ 26`), saturating a fixed-point value to `Int32` does not
  change the reconstructed sample.
* `DcShift`: per-component constants (offset, range, rounding) computed once
  (`DcShift.make`, checks that the range fits `Int32`, else `unsupported`: components
  deeper than 31 bits unsigned / 32 bits signed need a wider output than our `Int32` planes).
  `DcShift.rev_eq` / `DcShift.irrev_eq`: the per-sample kernels equal `Spec.MCT.reconRev` /
  `Spec.MCT.reconIrrev` exactly.
* The plane loops (`map3`, `map1`) apply the kernels to every cell; `map3_get` / `map1_get`
  prove that each output cell is the kernel applied to the input cells.
-/

namespace JPEG2000.MCT

open JPEG2000.Bytes
open JPEG2000.Spec.MCT
open JPEG2000.Spec.DWT97 (abs_le_iff abs_add_le abs_mul_le)
open JPEG2000.DWT97 (rnd rnd_err rnd64 scaleStep_exact)
open JPEG2000.DWT53 (Buf)

/-- The error location of this module. -/
def loc : Location := .at .mct

/-! ## `Int64` helpers -/

/-- `Int32` range clamp on integers. -/
def clamp32 (x : Int) : Int := clamp (-2147483648) 2147483647 x

/-- Saturating narrowing `Int64 → Int32`. -/
@[inline] def sat (v : Int64) : Int32 :=
  if v < -2147483648 then -2147483648 else if 2147483647 < v then 2147483647 else v.toInt32

/-- `smod 64` is the identity on shift amounts below 64. -/
private theorem smodK (k : Nat) (hk : k < 64) : ((BitVec.ofNat 64 k).smod 64#64).toNat = k := by
  have hmsb : (BitVec.ofNat 64 k).msb = false := by
    rw [BitVec.msb_eq_false_iff_two_mul_lt]; simp; omega
  have hmsb2 : (64#64 : BitVec 64).msb = false := by decide
  rw [BitVec.smod, hmsb, hmsb2]
  show ((BitVec.ofNat 64 k) % 64#64).toNat = k
  rw [BitVec.toNat_umod]
  simp; omega

/-- Arithmetic shift right by `k < 64` is floor division by `2^k`. -/
theorem shrK (x : Int64) (k : Nat) (hk : k < 64) :
    (x >>> (Int64.ofNat k)).toInt = x.toInt / 2 ^ k := by
  show (Int64.shiftRight x _).toInt = _
  simp only [Int64.shiftRight, BitVec.sshiftRight']
  rw [← Int64.toInt_toBitVec]
  show (BitVec.sshiftRight _ _).toInt = _
  rw [BitVec.toInt_sshiftRight, Int64.toInt_toBitVec, Int.shiftRight_eq_div_pow]
  congr
  exact smodK k hk

/-- `bmod 2^64` is the identity on `[−2^63, 2^63)`. -/
private theorem bm64 (z : Int) (h1 : -9223372036854775808 ≤ z) (h2 : z < 9223372036854775808) :
    z.bmod (2^64) = z := by
  apply Int.bmod_eq_of_le <;> omega

/-- Narrowing an `Int64` in the `Int32` range is exact. -/
private theorem toInt32_exact (a : Int64) (h : -2147483648 ≤ a.toInt) (h2 : a.toInt < 2147483648) :
    a.toInt32.toInt = a.toInt := by
  simp only [Int64.toInt_toInt32]
  apply Int.bmod_eq_of_le <;> omega

/-- `sat` is the `Int32` clamp. -/
theorem sat_toInt (v : Int64) : (sat v).toInt = clamp32 v.toInt := by
  unfold sat clamp32 clamp
  have e1 : (-2147483648 : Int64).toInt = -2147483648 := rfl
  have e2 : (2147483647 : Int64).toInt = 2147483647 := rfl
  by_cases h1 : v < -2147483648
  · have h1' := Int64.lt_iff_toInt_lt.mp h1
    rw [e1] at h1'
    simp only [h1, h1', ↓reduceIte]; rfl
  · have h1' : ¬ v.toInt < -2147483648 := fun h => h1 (Int64.lt_iff_toInt_lt.mpr (by rw [e1]; exact h))
    simp only [h1, h1', ↓reduceIte]
    by_cases h2 : 2147483647 < v
    · have h2' := Int64.lt_iff_toInt_lt.mp h2
      rw [e2] at h2'
      simp only [h2, h2', ↓reduceIte]; rfl
    · have h2' : ¬ 2147483647 < v.toInt :=
        fun h => h2 (Int64.lt_iff_toInt_lt.mpr (by rw [e2]; exact h))
      simp only [h2, h2', ↓reduceIte]
      exact toInt32_exact v (by omega) (by omega)

/-- `|c| ≤ A`, `0 ≤ s ≤ B` ⇒ `|c·s| ≤ A·B`. -/
private theorem mul_bound_nn (c s A B : Int) (hA : 0 ≤ A) (hc1 : -A ≤ c) (hc2 : c ≤ A)
    (hs : 0 ≤ s) (hs2 : s ≤ B) : -(A * B) ≤ c * s ∧ c * s ≤ A * B := by
  have h1 := Int.mul_le_mul_of_nonneg_right hc2 hs
  have h2 := Int.mul_le_mul_of_nonneg_left hs2 hA
  have h3 := Int.mul_le_mul_of_nonneg_right hc1 hs
  rw [Int.neg_mul] at h3
  omega

/-- `|c| ≤ A`, `|s| ≤ B` ⇒ `|c·s| ≤ A·B`. -/
private theorem mul_bound (c s A B : Int) (hA : 0 ≤ A) (hc1 : -A ≤ c) (hc2 : c ≤ A)
    (hs1 : -B ≤ s) (hs2 : s ≤ B) : -(A * B) ≤ c * s ∧ c * s ≤ A * B := by
  by_cases hs : 0 ≤ s
  · exact mul_bound_nn c s A B hA hc1 hc2 hs hs2
  · have h := mul_bound_nn c (-s) A B hA hc1 hc2 (by omega) (by omega)
    rw [Int.mul_neg] at h
    omega

/-! ## Inverse RCT (G.2) -/

/-- Inverse RCT on one triple of `Int32` cells: `I1 = Y0 − ((Y2 + Y1) >> 2)`, `I0 = Y2 + I1`,
`I2 = Y1 + I1` in `Int64`, saturated to `Int32`. -/
@[inline] def rctSample (y0 y1 y2 : Int32) : Int32 × Int32 × Int32 :=
  let a := y0.toInt64
  let b := y1.toInt64
  let c := y2.toInt64
  let i1 := a - ((c + b) >>> 2)
  (sat (c + i1), sat i1, sat (b + i1))

/-- The fast inverse RCT is the specification `Spec.MCT.rctInv` followed by the `Int32`
clamp, exactly, for all `Int32` inputs. -/
theorem rctSample_eq (y0 y1 y2 : Int32) :
    let s := rctSample y0 y1 y2
    let t := rctInv (y0.toInt, y1.toInt, y2.toInt)
    s.1.toInt = clamp32 t.1 ∧ s.2.1.toInt = clamp32 t.2.1 ∧ s.2.2.toInt = clamp32 t.2.2 := by
  have ha1 := y0.toInt_lt; have ha2 := y0.le_toInt
  have hb1 := y1.toInt_lt; have hb2 := y1.le_toInt
  have hc1 := y2.toInt_lt; have hc2 := y2.le_toInt
  have hsh : ∀ x : Int64, (x >>> 2).toInt = x.toInt / 4 := fun x => shrK x 2 (by decide)
  have hi1 : (y0.toInt64 - ((y2.toInt64 + y1.toInt64) >>> 2)).toInt
      = y0.toInt - (y2.toInt + y1.toInt) / 4 := by
    rw [Int64.toInt_sub, hsh, Int64.toInt_add, Int32.toInt_toInt64, Int32.toInt_toInt64,
      Int32.toInt_toInt64, bm64 (y2.toInt + y1.toInt) (by omega) (by omega)]
    exact bm64 _ (by omega) (by omega)
  simp only [rctSample, rctInv, sat_toInt]
  refine ⟨?_, ?_, ?_⟩
  · rw [Int64.toInt_add, hi1, Int32.toInt_toInt64, bm64 _ (by omega) (by omega)]
  · rw [hi1]
  · rw [Int64.toInt_add, hi1, Int32.toInt_toInt64, bm64 _ (by omega) (by omega)]

/-- With inputs `|y| < 2^29` (far beyond any reversible sample range) nothing saturates:
the fast inverse RCT equals `Spec.MCT.rctInv` exactly. -/
theorem rctSample_exact (y0 y1 y2 : Int32)
    (h0 : -536870912 < y0.toInt ∧ y0.toInt < 536870912)
    (h1 : -536870912 < y1.toInt ∧ y1.toInt < 536870912)
    (h2 : -536870912 < y2.toInt ∧ y2.toInt < 536870912) :
    let s := rctSample y0 y1 y2
    let t := rctInv (y0.toInt, y1.toInt, y2.toInt)
    s.1.toInt = t.1 ∧ s.2.1.toInt = t.2.1 ∧ s.2.2.toInt = t.2.2 := by
  have ⟨e1, e2, e3⟩ := rctSample_eq y0 y1 y2
  simp only at e1 e2 e3 ⊢
  rw [e1, e2, e3]
  simp only [rctInv, clamp32]
  refine ⟨?_, ?_, ?_⟩ <;> apply clamp_of_mem <;> omega

/-! ## Inverse ICT (G.3), fixed point -/

/-- `round(1.402 · 2^30)`. -/
def q0 : Int := 1505386037
/-- `round(0.34413 · 2^30)`. -/
def q1 : Int := 369506774
/-- `round(0.71414 · 2^30)`. -/
def q2 : Int := 766801986
/-- `round(1.772 · 2^30)`. -/
def q3 : Int := 1902670512

/-- The integer model of the fixed-point inverse ICT (what `ictSample` computes before
saturation): `(Y0 + rnd(q0·Y2), Y0 + rnd(−q1·Y1 − q2·Y2), Y0 + rnd(q3·Y1))`, one rounding
`rnd t = ⌊(t + 2^29)/2^30⌋` per output. -/
def ictQ : Triple Int → Triple Int
  | (y0, y1, y2) => (y0 + rnd (q0 * y2), y0 + rnd (-q1 * y1 + -q2 * y2), y0 + rnd (q3 * y1))

/-- `q0` as `Int64`. -/ def q0_64 : Int64 := 1505386037
/-- `−q1` as `Int64`. -/ def mq1_64 : Int64 := -369506774
/-- `−q2` as `Int64`. -/ def mq2_64 : Int64 := -766801986
/-- `q3` as `Int64`. -/ def q3_64 : Int64 := 1902670512

/-- Inverse ICT on one triple of fixed-point `Int32` cells (`Int64` intermediates), outputs
saturated to `Int32`. -/
@[inline] def ictSample (y0 y1 y2 : Int32) : Int32 × Int32 × Int32 :=
  let a := y0.toInt64
  let b := y1.toInt64
  let c := y2.toInt64
  (sat (a + rnd64 (q0_64 * c)), sat (a + rnd64 (mq1_64 * b + mq2_64 * c)),
   sat (a + rnd64 (q3_64 * b)))

/-- `rnd` of a value bounded by `2^62` is bounded by `2^33`. -/
private theorem rnd_small (t : Int) (h1 : -4611686018427387904 ≤ t) (h2 : t ≤ 4611686018427387904) :
    -8589934592 ≤ rnd t ∧ rnd t ≤ 8589934592 := by
  unfold rnd; omega

/-- One-term output row `a + rnd64(q·c)` in `Int64` is exact. -/
private theorem row1_exact (q : Int64) (hq1 : -2147483647 ≤ q.toInt) (hq2 : q.toInt ≤ 2147483647)
    (a c : Int32) :
    (a.toInt64 + rnd64 (q * c.toInt64)).toInt = a.toInt + rnd (q.toInt * c.toInt) := by
  have ha1 := a.toInt_lt; have ha2 := a.le_toInt
  have hc1 := c.toInt_lt; have hc2 := c.le_toInt
  rw [Int64.toInt_add, scaleStep_exact q hq1 hq2 c, Int32.toInt_toInt64]
  have hm := mul_bound q.toInt c.toInt 2147483647 2147483648 (by omega) hq1 hq2 (by omega) (by omega)
  have hr := rnd_small (q.toInt * c.toInt) (by omega) (by omega)
  exact bm64 _ (by omega) (by omega)

/-- The two-term row `a + rnd64(m1·b + m2·c)` in `Int64` is exact for `|m1| + |m2| ≤ 2^31`. -/
private theorem row2_exact (m1 m2 : Int64) (A1 A2 : Int) (hA : A1 + A2 ≤ 2147483648)
    (h1a : 0 ≤ A1) (h2a : 0 ≤ A2)
    (h11 : -A1 ≤ m1.toInt) (h12 : m1.toInt ≤ A1) (h21 : -A2 ≤ m2.toInt) (h22 : m2.toInt ≤ A2)
    (a b c : Int32) :
    (a.toInt64 + rnd64 (m1 * b.toInt64 + m2 * c.toInt64)).toInt
      = a.toInt + rnd (m1.toInt * b.toInt + m2.toInt * c.toInt) := by
  have ha1 := a.toInt_lt; have ha2 := a.le_toInt
  have hb1 := b.toInt_lt; have hb2 := b.le_toInt
  have hc1 := c.toInt_lt; have hc2 := c.le_toInt
  have hm1 := mul_bound m1.toInt b.toInt A1 2147483648 h1a h11 h12 (by omega) (by omega)
  have hm2 := mul_bound m2.toInt c.toInt A2 2147483648 h2a h21 h22 (by omega) (by omega)
  have hsum : -(A1 * 2147483648) - A2 * 2147483648 ≥ -4611686018427387904 ∧
      A1 * 2147483648 + A2 * 2147483648 ≤ 4611686018427387904 := by omega
  have hsh : ∀ x : Int64, (x >>> 30).toInt = x.toInt / 1073741824 :=
    fun x => shrK x 30 (by decide)
  unfold rnd64
  rw [Int64.toInt_add, hsh, Int64.toInt_add, Int64.toInt_add, Int64.toInt_mul, Int64.toInt_mul,
    Int32.toInt_toInt64, Int32.toInt_toInt64, Int32.toInt_toInt64]
  have h5 : (536870912 : Int64).toInt = 536870912 := rfl
  rw [h5]
  generalize m1.toInt * b.toInt = u at hm1 ⊢
  generalize m2.toInt * c.toInt = v at hm2 ⊢
  rw [bm64 u (by omega) (by omega), bm64 v (by omega) (by omega),
    bm64 (u + v) (by omega) (by omega), bm64 (u + v + 536870912) (by omega) (by omega)]
  have hr := rnd_small (u + v) (by omega) (by omega)
  unfold rnd at hr
  exact bm64 _ (by omega) (by omega)

/-- The fast inverse ICT is the integer model `ictQ` followed by the `Int32` clamp, for all
`Int32` inputs (the `Int64` intermediates never overflow). -/
theorem ictSample_eq (y0 y1 y2 : Int32) :
    let s := ictSample y0 y1 y2
    let t := ictQ (y0.toInt, y1.toInt, y2.toInt)
    s.1.toInt = clamp32 t.1 ∧ s.2.1.toInt = clamp32 t.2.1 ∧ s.2.2.toInt = clamp32 t.2.2 := by
  simp only [ictSample, ictQ, sat_toInt]
  refine ⟨?_, ?_, ?_⟩
  · rw [row1_exact q0_64 (by decide) (by decide)]; rfl
  · rw [row2_exact mq1_64 mq2_64 369506774 766801986 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)]; rfl
  · rw [row1_exact q3_64 (by decide) (by decide)]; rfl

/-! ## C8 for the ICT -/

/-- Error of one fixed-point output row `z0 + rnd(qa·za + qb·zb)` against the exact row
`y0 + a·ya + b·yb`, in sample units (`D = 2^F`): with inputs within `e` of the exact values
and `|za|, |zb| ≤ M`, the error is at most `(1 + |a| + |b|)·e` (propagation) plus
`(1/2 + (|qa/2^30 − a| + |qb/2^30 − b|)·M) / D` (one rounding and the constants'
quantisation). -/
theorem ictRow_err (D : Rat) (hD : 0 < D) (z0 za zb qa qb : Int) (y0 ya yb a b e M : Rat)
    (h0 : ((z0 : Rat) / D - y0).abs ≤ e) (ha : ((za : Rat) / D - ya).abs ≤ e)
    (hb : ((zb : Rat) / D - yb).abs ≤ e)
    (hza : ((za : Int) : Rat).abs ≤ M) (hzb : ((zb : Int) : Rat).abs ≤ M) :
    ((((z0 + rnd (qa * za + qb * zb) : Int) : Rat) / D) - (y0 + a * ya + b * yb)).abs
      ≤ (1 + a.abs + b.abs) * e
        + (1 / 2 + (((qa : Rat) / 1073741824 - a).abs + ((qb : Rat) / 1073741824 - b).abs) * M)
          / D := by
  have hD0 : D ≠ 0 := by grind
  have hiD : (0 : Rat) ≤ 1 / D := by
    have := Rat.le_of_lt (Rat.inv_pos.mpr hD)
    rw [Rat.div_def, Rat.one_mul]; exact this
  generalize hT : qa * za + qb * zb = T
  generalize hA : ((rnd T : Int) : Rat) - (T : Rat) / 1073741824 = A
  have hAb : A.abs ≤ 1 / 2 := by rw [← hA]; exact rnd_err T
  generalize hea : (qa : Rat) / 1073741824 - a = ea
  generalize heb : (qb : Rat) / 1073741824 - b = eb
  have hid : (((z0 + rnd T : Int) : Rat) / D) - (y0 + a * ya + b * yb)
      = ((z0 : Rat) / D - y0) + A * (1 / D) + (za * ea) * (1 / D) + (zb * eb) * (1 / D)
        + ((za : Rat) / D - ya) * a + ((zb : Rat) / D - yb) * b := by
    rw [← hA, ← hea, ← heb, ← hT]; push_cast; grind
  rw [hid]
  have t2 := abs_mul_le A (1 / D) (1 / 2) hAb
  have t3 := abs_mul_le ((za : Rat) * ea) (1 / D) (M * ea.abs) (by
    have := abs_mul_le (za : Rat) ea M hza; exact this)
  have t4 := abs_mul_le ((zb : Rat) * eb) (1 / D) (M * eb.abs) (by
    have := abs_mul_le (zb : Rat) eb M hzb; exact this)
  have t5 := abs_mul_le _ a e ha
  have t6 := abs_mul_le _ b e hb
  rw [Rat.abs_of_nonneg hiD] at t2 t3 t4
  have s1 := abs_add_le ((z0 : Rat) / D - y0) (A * (1 / D))
  have s2 := abs_add_le ((z0 : Rat) / D - y0 + A * (1 / D)) ((za * ea) * (1 / D))
  have s3 := abs_add_le ((z0 : Rat) / D - y0 + A * (1 / D) + (za * ea) * (1 / D))
    ((zb * eb) * (1 / D))
  have s4 := abs_add_le ((z0 : Rat) / D - y0 + A * (1 / D) + (za * ea) * (1 / D)
    + (zb * eb) * (1 / D)) (((za : Rat) / D - ya) * a)
  have s5 := abs_add_le ((z0 : Rat) / D - y0 + A * (1 / D) + (za * ea) * (1 / D)
    + (zb * eb) * (1 / D) + ((za : Rat) / D - ya) * a) (((zb : Rat) / D - yb) * b)
  have ef : (1 / 2 + (ea.abs + eb.abs) * M) / D
      = 1 / 2 * (1 / D) + M * ea.abs * (1 / D) + M * eb.abs * (1 / D) := by grind
  rw [ef]
  grind

/-- The ICT error gain: the largest row sum of absolute inverse-ICT coefficients,
`max(1 + 1.402, 1 + 0.34413 + 0.71414, 1 + 1.772) = 2.772`. -/
def ictGain : Rat := 2.772

/-- The ICT rounding term in ulps (units of `2^−F`) for inputs `|z| ≤ 2^31`: one rounding
(`1/2`) plus at most `2^−31 · 2^31 = 1` per 30-bit constant (two in the middle row). -/
def ictRnd : Rat := 5 / 2

/-- The 30-bit constants are within `2^−31` of the decimal constants. -/
private theorem q_close :
    ((q0 : Rat) / 1073741824 - ki0).abs ≤ 1 / 2147483648 ∧
    ((-q1 : Int) / 1073741824 - -ki1 : Rat).abs ≤ 1 / 2147483648 ∧
    ((-q2 : Int) / 1073741824 - -ki2 : Rat).abs ≤ 1 / 2147483648 ∧
    ((q3 : Rat) / 1073741824 - ki3).abs ≤ 1 / 2147483648 := by
  simp only [q0, q1, q2, q3, ki0, ki1, ki2, ki3]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply abs_le_iff.mpr <;> push_cast <;> constructor <;> grind

/-- `|0/2^30 − 0| = 0`. -/
private theorem zero_close : (((0 : Int) : Rat) / 1073741824 - 0).abs = 0 := by
  have : (((0 : Int) : Rat) / 1073741824 - 0) = 0 := by grind
  rw [this]; rfl

/-- `|c| = c` for the positive constants, `|−c| = c`. -/
private theorem k_abs : ki0.abs = ki0 ∧ (-ki1).abs = ki1 ∧ (-ki2).abs = ki2 ∧ ki3.abs = ki3 ∧
    (0 : Rat).abs = 0 := by
  refine ⟨?_, ?_, ?_, ?_, rfl⟩
  · apply Rat.abs_of_nonneg; unfold ki0; grind
  · rw [Rat.abs_of_nonpos (by unfold ki1; grind)]; grind
  · rw [Rat.abs_of_nonpos (by unfold ki2; grind)]; grind
  · apply Rat.abs_of_nonneg; unfold ki3; grind

/-- **C8 for the inverse ICT.** Fixed-point inputs `z_i` (`F` fractional bits, `D = 2^F`,
`|z_i| ≤ 2^31`, e.g. any `Int32` cells) within `e` of exact values `y_i` (`|z_i/D − y_i| ≤ e`)
give outputs `ictQ z` (the arithmetic of `ictSample`) within `ictGain · e + ictRnd / D` of
the exact `Spec.MCT.ictInv y`, component by component. -/
theorem ict_c8 (D : Rat) (hD : 0 < D) (z0 z1 z2 : Int) (y0 y1 y2 e : Rat)
    (hz1 : ((z1 : Int) : Rat).abs ≤ 2147483648) (hz2 : ((z2 : Int) : Rat).abs ≤ 2147483648)
    (h0 : ((z0 : Rat) / D - y0).abs ≤ e) (h1 : ((z1 : Rat) / D - y1).abs ≤ e)
    (h2 : ((z2 : Rat) / D - y2).abs ≤ e) :
    let o := ictQ (z0, z1, z2)
    let x := ictInv (y0, y1, y2)
    (((o.1 : Int) : Rat) / D - x.1).abs ≤ ictGain * e + ictRnd / D ∧
    (((o.2.1 : Int) : Rat) / D - x.2.1).abs ≤ ictGain * e + ictRnd / D ∧
    (((o.2.2 : Int) : Rat) / D - x.2.2).abs ≤ ictGain * e + ictRnd / D := by
  have he : 0 ≤ e := by have := abs_le_iff.mp h0; grind
  have hiD : (0 : Rat) < 1 / D := by
    have := Rat.inv_pos.mpr hD
    rw [Rat.div_def, Rat.one_mul]; exact this
  obtain ⟨c0, c1, c2, c3⟩ := q_close
  obtain ⟨a0, a1, a2, a3, az⟩ := k_abs
  have k0 : (0 : Rat) ≤ ki0 := by unfold ki0; grind
  have k1 : (0 : Rat) ≤ ki1 := by unfold ki1; grind
  have k2 : (0 : Rat) ≤ ki2 := by unfold ki2; grind
  have g0 : 1 + ki0 ≤ ictGain := by unfold ki0 ictGain; grind
  have g1 : 1 + ki1 + ki2 ≤ ictGain := by unfold ki1 ki2 ictGain; grind
  have g3 : 1 + ki3 ≤ ictGain := by unfold ki3 ictGain; grind
  have hfin : ∀ (g r : Rat), g ≤ ictGain → 0 ≤ r → r ≤ ictRnd →
      ∀ x : Rat, x ≤ g * e + r / D → x ≤ ictGain * e + ictRnd / D := by
    intro g r hg hr0 hr x hx
    have := Rat.mul_le_mul_of_nonneg_right hg he
    have h2 : r * (1 / D) ≤ ictRnd * (1 / D) := Rat.mul_le_mul_of_nonneg_right hr (Rat.le_of_lt hiD)
    have e1 : r / D = r * (1 / D) := by grind
    have e2 : ictRnd / D = ictRnd * (1 / D) := by grind
    grind
  have hzz : (((0 : Int) : Int) : Rat).abs ≤ 2147483648 := by
    have : (((0 : Int) : Int) : Rat) = 0 := rfl
    rw [this, az]; grind
  simp only [ictQ, ictInv]
  refine ⟨?_, ?_, ?_⟩
  · have r := ictRow_err D hD z0 0 z2 0 q0 y0 0 y2 0 ki0 e 2147483648 h0
      (by have : (((0 : Int) : Rat) / D - 0) = 0 := by grind
          rw [this, az]; exact he) h2
      hzz hz2
    rw [zero_close, az, a0] at r
    have ex : z0 + rnd (0 * 0 + q0 * z2) = z0 + rnd (q0 * z2) := by simp
    rw [ex, show y0 + 0 * 0 + ki0 * y2 = y0 + ki0 * y2 by grind] at r
    apply hfin (1 + 0 + ki0) (1 / 2 + (0 + ((q0 : Rat) / 1073741824 - ki0).abs) * 2147483648)
      (by grind) (by have := Rat.abs_nonneg (x := (q0 : Rat) / 1073741824 - ki0); grind) _ _ r
    have := Rat.mul_le_mul_of_nonneg_right c0 (show (0 : Rat) ≤ 2147483648 by decide)
    unfold ictRnd; grind
  · have r := ictRow_err D hD z0 z1 z2 (-q1) (-q2) y0 y1 y2 (-ki1) (-ki2) e 2147483648 h0 h1 h2
      hz1 hz2
    rw [a1, a2] at r
    rw [show y0 - ki1 * y1 - ki2 * y2 = y0 + -ki1 * y1 + -ki2 * y2 by grind]
    have n1 := Rat.abs_nonneg (x := ((-q1 : Int) : Rat) / 1073741824 - -ki1)
    have n2 := Rat.abs_nonneg (x := ((-q2 : Int) : Rat) / 1073741824 - -ki2)
    generalize (((-q1 : Int) : Rat) / 1073741824 - -ki1).abs = u1 at c1 r n1
    generalize (((-q2 : Int) : Rat) / 1073741824 - -ki2).abs = u2 at c2 r n2
    apply hfin (1 + ki1 + ki2) (1 / 2 + (u1 + u2) * 2147483648) g1 (by grind) _ _ r
    have := Rat.mul_le_mul_of_nonneg_right c1 (show (0 : Rat) ≤ 2147483648 by decide)
    have := Rat.mul_le_mul_of_nonneg_right c2 (show (0 : Rat) ≤ 2147483648 by decide)
    unfold ictRnd; grind
  · have r := ictRow_err D hD z0 z1 0 q3 0 y0 y1 0 ki3 0 e 2147483648 h0 h1
      (by have : (((0 : Int) : Rat) / D - 0) = 0 := by grind
          rw [this, az]; exact he)
      hz1 hzz
    rw [zero_close, az, a3] at r
    have ex : z0 + rnd (q3 * z1 + 0 * 0) = z0 + rnd (q3 * z1) := by simp
    rw [ex, show y0 + ki3 * y1 + 0 * 0 = y0 + ki3 * y1 by grind] at r
    apply hfin (1 + ki3 + 0) (1 / 2 + (((q3 : Rat) / 1073741824 - ki3).abs + 0) * 2147483648)
      (by grind) (by have := Rat.abs_nonneg (x := (q3 : Rat) / 1073741824 - ki3); grind) _ _ r
    have := Rat.mul_le_mul_of_nonneg_right c3 (show (0 : Rat) ≤ 2147483648 by decide)
    unfold ictRnd; grind

/-! ## Saturation is invisible after reconstruction -/

/-- `2^a ≤ 2^b` for `a ≤ b` (integers). -/
private theorem pow2_mono (a b : Nat) (h : a ≤ b) : (2 : Int) ^ a ≤ 2 ^ b := by
  have := Nat.pow_le_pow_right (by decide : 0 < 2) h
  exact_mod_cast this

/-- `clamp lo hi x = hi` when `hi ≤ x`. -/
private theorem clamp_hi (lo hi x : Int) (h : lo ≤ hi) (hx : hi ≤ x) : clamp lo hi x = hi := by
  unfold clamp; repeat' split
  all_goals omega

/-- `clamp lo hi x = lo` when `x ≤ lo`. -/
private theorem clamp_lo (lo hi x : Int) (h : lo ≤ hi) (hx : x ≤ lo) : clamp lo hi x = lo := by
  unfold clamp; repeat' split
  all_goals omega

/-- `roundFix` is monotone. -/
private theorem roundFix_mono (F : Nat) (a b : Int) (h : a ≤ b) : roundFix F a ≤ roundFix F b := by
  unfold roundFix
  exact Int.ediv_le_ediv (Int.pow_pos (by decide)) (by omega)

/-- Saturating a fixed-point value to `Int32` before `reconIrrev` changes nothing when
`F + B ≤ 32` (`B ≥ 1`): a value beyond `±2^31` lies at least `2^(31−F) ≥ 2^(B−1)` samples
from zero, so it is clamped to the same end of the range either way. With
`F = DWT97.fracBits B = 26 − B` this holds for every `B ≤ 26`; it justifies the saturation
in `ictSample` (and in `DWT97.idwt97`). -/
theorem reconIrrev_sat (signed : Bool) (depth F : Nat) (hd : 1 ≤ depth) (hF : F + depth ≤ 32)
    (v : Int) : reconIrrev signed depth F (clamp32 v) = reconIrrev signed depth F v := by
  have hle := sampleMin_le_max signed depth hd
  have hP : (0 : Int) < 2 ^ F := Int.pow_pos (by decide)
  have hQ : (2 : Int) ^ (depth - 1) ≤ 2 ^ (31 - F) := pow2_mono _ _ (by omega)
  have hPQ : (2 : Int) ^ F * 2 ^ (31 - F) = 2147483648 := by
    rw [← Int.pow_add, show F + (31 - F) = 31 by omega]; rfl
  have hd2 : (2 : Int) ^ depth = 2 * 2 ^ (depth - 1) := by
    rw [show depth = (depth - 1) + 1 by omega, Int.pow_succ]
    simp only [Nat.add_sub_cancel]; exact Int.mul_comm _ _
  have hh : (0 : Int) ≤ (2 : Int) ^ F / 2 ∧ (2 : Int) ^ F / 2 < 2 ^ F := by omega
  unfold clamp32 clamp
  by_cases h1 : v < -2147483648
  · simp only [h1, ↓reduceIte]
    -- both round to at most `−2^(31−F)`, at or below the range's lower end
    have hr : roundFix F (-2147483648) ≤ -(2 ^ (31 - F)) := by
      unfold roundFix
      rw [← hPQ]
      have : (-(2 ^ F * 2 ^ (31 - F)) + 2 ^ F / 2) / 2 ^ F = -(2 ^ (31 - F)) := by
        rw [show -(2 ^ F * 2 ^ (31 - F)) + 2 ^ F / 2 = 2 ^ F / 2 + 2 ^ F * (-(2 ^ (31 - F)))
          by rw [Int.mul_neg]; omega]
        rw [Int.add_mul_ediv_left _ _ (by omega), Int.ediv_eq_zero_of_lt hh.1 hh.2]; omega
      omega
    have hm := roundFix_mono F v (-2147483648) (by omega)
    unfold reconIrrev reconRev
    rw [clamp_lo _ _ _ hle, clamp_lo _ _ _ hle] <;>
      simp only [sampleMin, dcOffset] <;> cases signed <;>
      simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  · by_cases h2 : 2147483647 < v
    · simp only [h1, h2, ↓reduceIte]
      have hr : (2 : Int) ^ (31 - F) - 1 ≤ roundFix F 2147483647 := by
        unfold roundFix
        apply Int.le_ediv_of_mul_le hP
        have : ((2 : Int) ^ (31 - F) - 1) * 2 ^ F = 2147483648 - 2 ^ F := by
          rw [Int.sub_mul, Int.one_mul, Int.mul_comm, hPQ]
        omega
      have hm := roundFix_mono F 2147483647 v (by omega)
      unfold reconIrrev reconRev
      rw [clamp_hi _ _ _ hle, clamp_hi _ _ _ hle] <;>
        simp only [sampleMax, dcOffset] <;> cases signed <;>
        simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
    · simp only [h1, h2, ↓reduceIte]

/-! ## DC level shift and clamping (G.1) -/

/-- Per-component constants of the DC shift and clamp, computed once (`make`); the sample
kernels `rev`/`irrev` use only `Int64` arithmetic. -/
structure DcShift where
  /-- Signed component. -/
  signed : Bool
  /-- Bit depth `B`. -/
  depth : Nat
  /-- Fractional bits of the irreversible input. -/
  F : Nat
  /-- `dcOffset signed depth`. -/
  off : Int64
  /-- `sampleMin signed depth`. -/
  lo : Int64
  /-- `sampleMax signed depth`. -/
  hi : Int64
  /-- `⌊2^F / 2⌋` (rounding offset). -/
  half : Int64
  /-- `F` as a shift amount. -/
  sh : Int64

/-- The constants for a component (signedness, bit depth `B`, fractional bits `F`):
`unsupported` unless `1 ≤ B`, `F ≤ 31` and the sample range fits `Int32` (unsigned
`B ≤ 31`, signed `B ≤ 32`). -/
def DcShift.make (signed : Bool) (depth F : Nat) : Except Error DcShift :=
  let off := dcOffset signed depth
  let lo := sampleMin signed depth
  let hi := sampleMax signed depth
  let half : Int := (2 : Int) ^ F / 2
  if 1 ≤ depth ∧ F ≤ 31 ∧ -2147483648 ≤ lo ∧ hi ≤ 2147483647 ∧ 0 ≤ off ∧ off ≤ 1073741824 ∧
      0 ≤ half ∧ half ≤ 1073741824 then
    .ok { signed, depth, F, off := Int64.ofInt off, lo := Int64.ofInt lo, hi := Int64.ofInt hi,
          half := Int64.ofInt half, sh := Int64.ofNat F }
  else .error (.unsupported loc
    s!"component range (signed {signed}, {depth} bits, {F} fractional bits) exceeds Int32")

/-- The invariant `make` establishes. -/
def DcShift.WF (p : DcShift) : Prop :=
  p.off.toInt = dcOffset p.signed p.depth ∧ p.lo.toInt = sampleMin p.signed p.depth ∧
  p.hi.toInt = sampleMax p.signed p.depth ∧ p.half.toInt = (2 : Int) ^ p.F / 2 ∧
  p.sh = Int64.ofNat p.F ∧ p.F ≤ 31 ∧ 1 ≤ p.depth ∧
  -2147483648 ≤ p.lo.toInt ∧ p.hi.toInt ≤ 2147483647 ∧ 0 ≤ p.off.toInt ∧
  p.off.toInt ≤ 1073741824 ∧ 0 ≤ p.half.toInt ∧ p.half.toInt ≤ 1073741824

/-- `make` returns well-formed constants. -/
theorem DcShift.make_wf (signed : Bool) (depth F : Nat) (p : DcShift)
    (h : DcShift.make signed depth F = .ok p) : p.WF := by
  simp only [DcShift.make] at h
  split at h
  · rename_i hc
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hc
    have hle := sampleMin_le_max signed depth h1
    simp only [Except.ok.injEq] at h
    subst h
    have c1 := Int64.toInt_ofInt_of_le (n := dcOffset signed depth) (by omega) (by omega)
    have c2 := Int64.toInt_ofInt_of_le (n := sampleMin signed depth) (by omega) (by omega)
    have c3 := Int64.toInt_ofInt_of_le (n := sampleMax signed depth) (by omega) (by omega)
    have c4 := Int64.toInt_ofInt_of_le (n := (2 : Int) ^ F / 2) (by omega) (by omega)
    simp only [DcShift.WF]
    rw [c1, c2, c3, c4]
    exact ⟨rfl, rfl, rfl, rfl, trivial, h2, h1, h3, h4, h5, h6, h7, h8⟩
  · simp at h

/-- Clamp an `Int64` to `[lo, hi]` and narrow. -/
@[inline] def DcShift.clampTo (p : DcShift) (v : Int64) : Int32 :=
  if v < p.lo then p.lo.toInt32 else if p.hi < v then p.hi.toInt32 else v.toInt32

/-- `clampTo` is `Spec.MCT.clamp`. -/
private theorem DcShift.clampTo_eq (p : DcShift) (hp : p.WF) (v : Int64) :
    (p.clampTo v).toInt = clamp p.lo.toInt p.hi.toInt v.toInt := by
  obtain ⟨-, hlo, hhi, -, -, -, hd, l1, l2, -⟩ := hp
  have hle := sampleMin_le_max p.signed p.depth hd
  rw [← hlo, ← hhi] at hle
  unfold DcShift.clampTo clamp
  by_cases h1 : v < p.lo
  · have h1' := Int64.lt_iff_toInt_lt.mp h1
    simp only [h1, h1', ↓reduceIte]
    exact toInt32_exact _ (by omega) (by omega)
  · have h1' : ¬ v.toInt < p.lo.toInt := fun h => h1 (Int64.lt_iff_toInt_lt.mpr h)
    simp only [h1, h1', ↓reduceIte]
    by_cases h2 : p.hi < v
    · have h2' := Int64.lt_iff_toInt_lt.mp h2
      simp only [h2, h2', ↓reduceIte]
      exact toInt32_exact _ (by omega) (by omega)
    · have h2' : ¬ p.hi.toInt < v.toInt := fun h => h2 (Int64.lt_iff_toInt_lt.mpr h)
      simp only [h2, h2', ↓reduceIte]
      exact toInt32_exact _ (by omega) (by omega)

/-- Reversible reconstruction of one sample (`Int32` integer cell): DC shift, clamp. -/
@[inline] def DcShift.rev (p : DcShift) (x : Int32) : Int32 := p.clampTo (x.toInt64 + p.off)

/-- Irreversible reconstruction of one fixed-point cell (`F` fractional bits): round to
nearest (`(z + ⌊2^F/2⌋) >> F`), DC shift, clamp. -/
@[inline] def DcShift.irrev (p : DcShift) (z : Int32) : Int32 :=
  p.clampTo (((z.toInt64 + p.half) >>> p.sh) + p.off)

/-- The fast reversible kernel equals `Spec.MCT.reconRev` exactly. -/
theorem DcShift.rev_eq (p : DcShift) (hp : p.WF) (x : Int32) :
    (p.rev x).toInt = reconRev p.signed p.depth x.toInt := by
  have hp' := hp
  obtain ⟨hoff, hlo, hhi, -, -, -, -, -, -, o1, o2, -⟩ := hp'
  have hx1 := x.toInt_lt; have hx2 := x.le_toInt
  unfold DcShift.rev reconRev
  rw [DcShift.clampTo_eq p hp, Int64.toInt_add, Int32.toInt_toInt64, bm64 _ (by omega) (by omega),
    hoff, hlo, hhi]

/-- `|t / P| ≤ B` when `|t| ≤ B` and `P ≥ 1`. -/
private theorem ediv_bound (t P B : Int) (hP : 1 ≤ P) (hB : 0 ≤ B) (h1 : -B ≤ t) (h2 : t ≤ B) :
    -B ≤ t / P ∧ t / P ≤ B := by
  constructor
  · apply Int.le_ediv_of_mul_le (by omega)
    have := Int.mul_le_mul_of_nonneg_left hP hB
    rw [Int.neg_mul]; omega
  · have := Int.ediv_le_ediv (c := P) (by omega) h2
    have := Int.ediv_le_self P hB
    omega

/-- The fast irreversible kernel equals `Spec.MCT.reconIrrev` exactly. -/
theorem DcShift.irrev_eq (p : DcShift) (hp : p.WF) (z : Int32) :
    (p.irrev z).toInt = reconIrrev p.signed p.depth p.F z.toInt := by
  have hp' := hp
  obtain ⟨hoff, hlo, hhi, hhalf, hsh, hF, -, -, -, o1, o2, h1, h2⟩ := hp'
  have hz1 := z.toInt_lt; have hz2 := z.le_toInt
  have hP : (1 : Int) ≤ 2 ^ p.F := by have : (0 : Int) < 2 ^ p.F := Int.pow_pos (by decide); omega
  have hs : ((z.toInt64 + p.half) >>> p.sh).toInt = (z.toInt + 2 ^ p.F / 2) / 2 ^ p.F := by
    rw [hsh, shrK _ _ (by omega), Int64.toInt_add, Int32.toInt_toInt64,
      bm64 _ (by omega) (by omega), hhalf]
  have hb := ediv_bound (z.toInt + 2 ^ p.F / 2) (2 ^ p.F) 4294967296 hP (by decide)
    (by omega) (by omega)
  unfold DcShift.irrev reconIrrev reconRev roundFix
  rw [DcShift.clampTo_eq p hp, Int64.toInt_add, hs, bm64 _ (by omega) (by omega), hoff, hlo, hhi]

/-! ## Plane loops -/

/-- Applies `f` to cells `i, i + 1, …` of three buffers in place. -/
@[specialize] def map3 {N : Nat} (f : Int32 → Int32 → Int32 → Int32 × Int32 × Int32)
    (b0 b1 b2 : Buf N) (i : Nat) : Buf N × Buf N × Buf N :=
  if hi : i < N then
    let o := f (b0.get i hi) (b1.get i hi) (b2.get i hi)
    map3 f (b0.set i o.1 hi) (b1.set i o.2.1 hi) (b2.set i o.2.2 hi) (i + 1)
  else (b0, b1, b2)
termination_by N - i

/-- Applies `f` to cells `i, i + 1, …` of a buffer in place. -/
@[specialize] def map1 {N : Nat} (f : Int32 → Int32) (b : Buf N) (i : Nat) : Buf N :=
  if hi : i < N then map1 f (b.set i (f (b.get i hi)) hi) (i + 1) else b
termination_by N - i

/-- Each output cell of `map1` is `f` of the input cell (cells before `i` unchanged). -/
theorem map1_get {N : Nat} (f : Int32 → Int32) (b : Buf N) (i j : Nat) (hj : j < N) :
    (map1 f b i).get j hj = if j < i then b.get j hj else f (b.get j hj) := by
  unfold map1
  split
  · rename_i hi
    rw [map1_get f _ (i + 1) j hj, DWT53.Buf.get_set]
    by_cases h : j < i
    · simp only [show ¬ i = j by omega, show j < i + 1 by omega, h, ↓reduceIte]
    · by_cases h' : i = j
      · subst h'; simp
      · simp only [h', h, show ¬ j < i + 1 by omega, ↓reduceIte]
  · rename_i hi; simp only [show j < i by omega, ↓reduceIte]
termination_by N - i

/-- Each output cell of `map3` is `f` of the three input cells (cells before `i`
unchanged). -/
theorem map3_get {N : Nat} (f : Int32 → Int32 → Int32 → Int32 × Int32 × Int32)
    (b0 b1 b2 : Buf N) (i j : Nat) (hj : j < N) :
    let r := map3 f b0 b1 b2 i
    let o := f (b0.get j hj) (b1.get j hj) (b2.get j hj)
    r.1.get j hj = (if j < i then b0.get j hj else o.1) ∧
    r.2.1.get j hj = (if j < i then b1.get j hj else o.2.1) ∧
    r.2.2.get j hj = (if j < i then b2.get j hj else o.2.2) := by
  unfold map3
  split
  · rename_i hi
    have ih := map3_get f (b0.set i (f (b0.get i hi) (b1.get i hi) (b2.get i hi)).1 hi)
      (b1.set i (f (b0.get i hi) (b1.get i hi) (b2.get i hi)).2.1 hi)
      (b2.set i (f (b0.get i hi) (b1.get i hi) (b2.get i hi)).2.2 hi) (i + 1) j hj
    simp only at ih ⊢
    rw [ih.1, ih.2.1, ih.2.2]
    simp only [DWT53.Buf.get_set]
    by_cases h : j < i
    · simp only [show ¬ i = j by omega, show j < i + 1 by omega, h, ↓reduceIte, and_self]
    · by_cases h' : i = j
      · subst h'; simp
      · simp only [h', h, show ¬ j < i + 1 by omega, ↓reduceIte, and_self]
  · rename_i hi; simp only [show j < i by omega, ↓reduceIte, and_self]
termination_by N - i

/-- Applies a three-cell kernel to three planes of equal dimensions (`malformed`
otherwise). -/
def apply3 (f : Int32 → Int32 → Int32 → Int32 × Int32 × Int32) (p0 p1 p2 : Plane) :
    Except Error (Plane × Plane × Plane) :=
  if h : p1.width = p0.width ∧ p1.height = p0.height ∧ p2.width = p0.width ∧
      p2.height = p0.height then
    let r := map3 f (N := p0.width * p0.height) ⟨p0, rfl⟩ ⟨p1, by rw [h.1, h.2.1]⟩
      ⟨p2, by rw [h.2.2.1, h.2.2.2]⟩ 0
    .ok (r.1.1, r.2.1.1, r.2.2.1)
  else .error (.malformed loc
    s!"component transform on planes {p0.width}×{p0.height}, {p1.width}×{p1.height}, {p2.width}×{p2.height}")

/-- Inverse RCT (G.2) in place on components 0, 1, 2 (integer cells). -/
def rctInverse (p0 p1 p2 : Plane) : Except Error (Plane × Plane × Plane) :=
  apply3 rctSample p0 p1 p2

/-- Inverse ICT (G.3) in place on components 0, 1, 2 (fixed-point cells, the format kept). -/
def ictInverse (p0 p1 p2 : Plane) : Except Error (Plane × Plane × Plane) :=
  apply3 ictSample p0 p1 p2

/-- DC level shift and clamp of a reversible component (integer cells), in place. -/
def dcShiftClampRev (p : DcShift) (pl : Plane) : Plane :=
  (map1 p.rev (N := pl.width * pl.height) ⟨pl, rfl⟩ 0).1

/-- Rounding, DC level shift and clamp of an irreversible component (fixed-point cells with
`p.F` fractional bits → integer samples), in place. -/
def dcShiftClampIrrev (p : DcShift) (pl : Plane) : Plane :=
  (map1 p.irrev (N := pl.width * pl.height) ⟨pl, rfl⟩ 0).1

end JPEG2000.MCT
