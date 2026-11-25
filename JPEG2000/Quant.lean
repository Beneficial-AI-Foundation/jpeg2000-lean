import JPEG2000.Bytes
import JPEG2000.Header
import JPEG2000.Tier1.Decode
import JPEG2000.Tier2.Geometry
import JPEG2000.DWT53
import Spec.Quant

/-!
# Fast dequantisation and ROI max-shift on `Int32` planes

Plan.md §4 (C8, C9), §5.4 (fixed width, checked saturation), §6 item 1 (no GMP in hot
loops); T.800 Annex E (E.1, E-2…E-7) and Annex H (max-shift). Task 5.1. The exact model is
`Spec.Quant` (read its module doc for the formulas and the conventions).

## What it does

`dequantBlock` takes one decoded code-block (`Tier1.CodeBlockOut`: the `Int32` plane of
`±mag`, bit-plane `p` weighing `2^p`, and the per-coefficient `lsbPlane`), applies the ROI
unshift and the reconstruction of E.1.1.2, and writes the result into the tile-component
plane at the code-block's place in the *Mallat layout* of `JPEG2000.DWT53` (LL of the
coarsest level top-left; at decomposition level `nb` the HL band starts at column `sn`, LH
at row `sv`, HH at `(sn, sv)`, where `sn × sv` is the size of `DWT53.halfN tc nb`; each band
is stored from its first band coordinate, `Tier2.Geometry.bandRect`).

* **Reversible (5/3)**: `revCoeff` gives `Spec.Quant.dequantRev` exactly, saturated to
  `Int32` (`DWT53.sat32`); proved: `revCoeff_eq` (with the flag telling whether no
  saturation happened). With `K ≤ 31` coded planes (the fast Tier-1 bound) the result is
  `< 2^31 + 2^30` in magnitude, and for a valid stream (`Mb ≤ 30` after ROI) never
  saturates.
* **Irreversible (9/7)**: fixed point with `F` fractional bits (a parameter, chosen by the
  9/7 of task 5.3): the output `z` approximates `Spec.Quant.dequantIrrev s Δb c · 2^F`. With
  `n = (2·mag + 2^lsb)·(2^11 + μb)`, `a = Rb + F`, `b = εb + 12`, the exact value is
  `±n · 2^a / 2^b`: when `a ≥ b` the kernel computes `n·2^(a−b)` exactly; otherwise it
  rounds `n / 2^(b−a)` half up on the magnitude (symmetric about 0). Proved
  (`irrevCoeff_bound`): whenever the flag is `true` (no saturation),
  `|z − dequantIrrev s Δb c · 2^F| ≤ 1/2`, i.e. an error of at most `2^−(F+1)` in sample
  units (the test suite also checks that there is no error at all when `a ≥ b`).

All arithmetic is `UInt64` on magnitudes `< 2^47` (no wrap; the bounds are in the proofs)
and the result is narrowed with an explicit saturation (`satSigned`), never wrapped. The
block loop (placement in the Mallat layout) is tested against the spec
(`Tests/Quant.lean`), not proved.
-/

namespace JPEG2000.Quant

open JPEG2000 JPEG2000.Bytes
open JPEG2000.Header (Rect)
open JPEG2000.Tier2.Geometry (Band bandRect bandLevel)
open JPEG2000.Spec.Quant (BandQuant)
open JPEG2000.Spec.Tier1 (Coeff)

/-- The error location of this module. -/
def loc : Location := .at .quant

/-! ## Per-coefficient kernels -/

/-- `|v|` as a `UInt64` (exact for every `Int32`, including `−2^31`). -/
@[inline] def absU (v : Int32) : UInt64 :=
  let x := v.toInt64
  (if x < 0 then -x else x).toUInt64

/-- Annex H on a magnitude and its last decoded plane: a magnitude `≥ 2^s` is shifted down
by `s` (plane lowered by `s`, saturating at 0); a smaller one is kept. -/
@[inline] def unshift (s : Nat) (m : UInt64) (lsb : Nat) : UInt64 × Nat :=
  if s < 64 ∧ (m >>> s.toUInt64) != 0 then (m >>> s.toUInt64, lsb - s) else (m, lsb)

/-- Narrows a sign and a magnitude `r` to `Int32`, saturating: `(±r, true)` when it fits,
otherwise the nearest bound with `false`. -/
@[inline] def satSigned (neg : Bool) (r : UInt64) : Int32 × Bool :=
  if neg then
    if r ≤ 2147483648 then ((Int64.ofNat r.toNat).neg.toInt32, true)
    else (Int32.ofInt (-2147483648), false)
  else
    if r ≤ 2147483647 then ((Int64.ofNat r.toNat).toInt32, true)
    else (Int32.ofInt 2147483647, false)

/-- Reversible dequantisation of one coefficient `v = ±mag` whose last decoded plane is
`lsb`, with ROI shift `s`: `±(mag' + ⌊2^lsb' / 2⌋)` after the unshift, saturated to `Int32`
(the flag is `false` iff it saturated). Spec: `Spec.Quant.dequantRev` (`revCoeff_eq`). -/
@[inline] def revCoeff (s : Nat) (v : Int32) (lsb : Nat) : Int32 × Bool :=
  let ml := unshift s (absU v) lsb
  let m := ml.1
  let l := ml.2
  if m == 0 then (0, true)
  else
    let half : UInt64 :=
      if l == 0 then 0 else if l ≤ 33 then (1 : UInt64) <<< (l - 1).toUInt64 else 0x200000000
    satSigned (v < 0) (m + half)

/-- Per-band constants of the irreversible kernel for `F` fractional bits: the multiplier
`2^11 + μb`, the direction and the amount of the final power-of-two scaling (`a = Rb + F`,
`b = εb + 12`: `up` with shift `a − b` when `a ≥ b`, otherwise a rounded right shift by
`b − a`). -/
structure IrrevConsts where
  /-- `2^11 + μb`. -/
  mult : UInt64
  /-- `Rb + F ≥ εb + 12`. -/
  up : Bool
  /-- `|Rb + F − (εb + 12)|`. -/
  sh : Nat
  deriving Repr, Inhabited

/-- The constants of band `q` for `F` fractional bits. -/
def irrevConsts (q : BandQuant) (F : Nat) : IrrevConsts :=
  let a := q.range + F
  let b := q.exponent + 12
  { mult := (2048 + q.mantissa % 2048).toUInt64, up := decide (b ≤ a),
    sh := if b ≤ a then a - b else b - a }

/-- The magnitude of the irreversible kernel from `n = (2·mag + 2^lsb)·mult`: `n·2^sh`
(upwards; `2^40`, a saturating value, if that exceeds `2^31 − 1`) or
`⌊(n + 2^(sh−1)) / 2^sh⌋` (downwards; `0` once `sh ≥ 48`, as then `n < 2^(sh−1)`). -/
@[inline] def scaleMag (k : IrrevConsts) (n : UInt64) : UInt64 :=
  if k.up then
    if k.sh < 64 ∧ n ≤ (0x7FFFFFFF : UInt64) >>> k.sh.toUInt64 then n <<< k.sh.toUInt64
    else 0x10000000000
  else if k.sh ≥ 48 then 0
  else (n + (1 : UInt64) <<< (k.sh - 1).toUInt64) >>> k.sh.toUInt64

/-- Irreversible dequantisation of one coefficient in fixed point with the constants `k`
(`irrevConsts q F`) and ROI shift `s`: approximately `dequantIrrev s Δb c · 2^F`
(`irrevCoeff_bound`). The flag is `false` when the value saturated or `lsb' > 33`
(impossible for a Tier-1 output, which has `lsb ≤ 30`). -/
@[inline] def irrevCoeff (k : IrrevConsts) (s : Nat) (v : Int32) (lsb : Nat) : Int32 × Bool :=
  let ml := unshift s (absU v) lsb
  let m := ml.1
  let l := ml.2
  if m == 0 then (0, true)
  else if l > 33 then (0, false)
  else
    let t := (m <<< (1 : UInt64)) + (1 : UInt64) <<< l.toUInt64
    satSigned (v < 0) (scaleMag k (t * k.mult))

/-! ## Block placement (Mallat layout of `JPEG2000.DWT53`) -/

/-- Plane position of the first band coordinate of band `b` of resolution `r` (decomposition
level `nb = bandLevel NL r`) of the tile-component `tc`: `(0, 0)` for LL; otherwise the
size `sn × sv` of `DWT53.halfN tc nb` offsets the high-pass directions. -/
def bandOrigin (tc : Rect) (nl r : Nat) (b : Band) : Nat × Nat :=
  if r = 0 then (0, 0)
  else
    let L := DWT53.halfN tc (bandLevel nl r)
    (if b.xob = 1 then L.x1 - L.x0 else 0, if b.yob = 1 then L.y1 - L.y0 else 0)

/-- Writes row `y` of a code-block: `k` cells from column `x`, the kernel `f` applied to the
value and the last decoded plane; destination index `d` (consecutive). Returns the plane and
the conjunction of the kernel flags. -/
@[specialize] def blockRow (f : Int32 → Nat → Int32 × Bool) (o : Tier1.CodeBlockOut) (y : Nat) :
    Nat → Nat → Nat → Plane → Bool → Plane × Bool
  | 0, _, _, p, ok => (p, ok)
  | k + 1, x, d, p, ok =>
    let v := (o.plane.get? (y * o.plane.width + x)).getD 0
    let r := f v (o.lsbPlane x y)
    let p := if h : d < p.width * p.height then p.set d r.1 h else p
    blockRow f o y k (x + 1) (d + 1) p (ok && r.2)

/-- Writes rows `y, y + 1, …` (`k` of them) of a code-block whose cell `(0, y)` goes to
plane position `(px, py + y)`. -/
@[specialize] def blockRows (f : Int32 → Nat → Int32 × Bool) (o : Tier1.CodeBlockOut)
    (px py : Nat) : Nat → Nat → Plane → Bool → Plane × Bool
  | 0, _, p, ok => (p, ok)
  | k + 1, y, p, ok =>
    let (p, ok) := blockRow f o y o.plane.width 0 ((py + y) * p.width + px) p ok
    blockRows f o px py k (y + 1) p ok

/-- Dequantise one decoded code-block of band `b` of resolution `r` and write it into the
tile-component plane `dst` (Mallat layout, size of `tc`). `cb` is the code-block rectangle
in band coordinates (`Tier2.Geometry.CodeBlockGeom.rect`), `q` the band's parameters
(`Spec.Quant.bandQuant`), `F` the fractional bits of the irreversible path (ignored for
5/3). Returns the plane and `true` iff no value saturated. Errors (`malformed`) when `dst`
does not have `tc`'s size, `r > NL`, the code-block plane does not have `cb`'s size or `cb`
is not inside the band. -/
def dequantBlock (dst : Plane) (tc : Rect) (nl r : Nat) (b : Band) (cb : Rect) (q : BandQuant)
    (F : Nat) (o : Tier1.CodeBlockOut) : Except Error (Plane × Bool) := do
  if dst.width ≠ tc.x1 - tc.x0 ∨ dst.height ≠ tc.y1 - tc.y0 then
    throw (.malformed loc "dequantisation: plane size differs from the tile-component")
  if r > nl then throw (.malformed loc s!"dequantisation: resolution {r} > NL = {nl}")
  let band := bandRect tc (bandLevel nl r) b
  if o.plane.width ≠ cb.x1 - cb.x0 ∨ o.plane.height ≠ cb.y1 - cb.y0 then
    throw (.malformed loc "dequantisation: code-block plane size differs from its rectangle")
  if cb.x0 < band.x0 ∨ cb.y0 < band.y0 ∨ band.x1 < cb.x1 ∨ band.y1 < cb.y1 then
    throw (.malformed loc "dequantisation: code-block outside its band")
  let (ox, oy) := bandOrigin tc nl r b
  let px := ox + (cb.x0 - band.x0)
  let py := oy + (cb.y0 - band.y0)
  let s := q.roiShift
  if q.reversible then
    return blockRows (revCoeff s) o px py o.plane.height 0 dst true
  else
    let k := irrevConsts q F
    return blockRows (irrevCoeff k s) o px py o.plane.height 0 dst true

/-! ## Proofs: the kernels against `Spec.Quant` -/

/-- `absU` is the absolute value. -/
theorem absU_toNat (v : Int32) : (absU v).toNat = v.toInt.natAbs := by
  have h1 := v.toInt_lt
  have h2 := v.le_toInt
  unfold absU
  simp only
  split
  · rename_i hn
    rw [Int64.lt_iff_toInt_lt] at hn
    simp only [Int32.toInt_toInt64, Int64.toInt_zero] at hn
    have hle : (0 : Int64) ≤ -v.toInt64 := by
      rw [Int64.le_iff_toInt_le, Int64.toInt_neg]
      simp only [Int32.toInt_toInt64, Int64.toInt_zero]
      rw [Int.bmod_eq_of_le (by omega) (by omega)]; omega
    rw [Int64.toNat_toUInt64_of_le hle, Int64.toNatClampNeg, Int64.toInt_neg]
    simp only [Int32.toInt_toInt64]
    rw [Int.bmod_eq_of_le (by omega) (by omega)]; omega
  · rename_i hn
    rw [Int64.lt_iff_toInt_lt] at hn
    simp only [Int32.toInt_toInt64, Int64.toInt_zero] at hn
    have hle : (0 : Int64) ≤ v.toInt64 := by
      rw [Int64.le_iff_toInt_le]; simp only [Int32.toInt_toInt64, Int64.toInt_zero]; omega
    rw [Int64.toNat_toUInt64_of_le hle, Int64.toNatClampNeg]
    simp only [Int32.toInt_toInt64]; omega

/-- `m >>> s` on `UInt64` for `s < 64` is division by `2^s`. -/
theorem shr_toNat (m : UInt64) (s : Nat) (hs : s < 64) :
    (m >>> s.toUInt64).toNat = m.toNat / 2 ^ s := by
  rw [UInt64.toNat_shiftRight, Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt
    (by omega : s < 2 ^ 64), Nat.mod_eq_of_lt hs, Nat.shiftRight_eq_div_pow]

/-- `1 <<< k` on `UInt64` for `k < 64` is `2^k`. -/
theorem shl1_toNat (k : Nat) (hk : k < 64) : ((1 : UInt64) <<< k.toUInt64).toNat = 2 ^ k := by
  rw [UInt64.toNat_shiftLeft, Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt
    (by omega : k < 2 ^ 64), Nat.mod_eq_of_lt hk, Nat.shiftLeft_eq, UInt64.toNat_one, Nat.one_mul]
  exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hk)

/-- `unshift` is `Spec.Quant.roiUnshift` on (magnitude, last plane), for magnitudes
`< 2^63`. -/
theorem unshift_spec (s : Nat) (m : UInt64) (lsb : Nat) (hm : m.toNat < 2 ^ 63) :
    (unshift s m lsb).1.toNat = (if 2 ^ s ≤ m.toNat then m.toNat / 2 ^ s else m.toNat) ∧
    (unshift s m lsb).2 = (if 2 ^ s ≤ m.toNat then lsb - s else lsb) := by
  unfold unshift
  by_cases hs : s < 64
  · have hd : (m >>> s.toUInt64 != 0) = decide (2 ^ s ≤ m.toNat) := by
      have := shr_toNat m s hs
      by_cases h : 2 ^ s ≤ m.toNat
      · have hpos : 0 < m.toNat / 2 ^ s := Nat.div_pos h (Nat.two_pow_pos s)
        have hne : m >>> s.toUInt64 ≠ 0 := by
          intro h0; rw [h0] at this; simp at this; omega
        simp [hne, h]
      · have hz : m.toNat / 2 ^ s = 0 := Nat.div_eq_of_lt (by omega)
        have : m >>> s.toUInt64 = 0 := UInt64.toNat_inj.mp (by rw [this, hz]; rfl)
        simp [this, h]
    simp only [hs, true_and, hd, decide_eq_true_eq]
    split
    · exact ⟨shr_toNat m s hs, rfl⟩
    · simp
  · have hlt : m.toNat < 2 ^ s :=
      Nat.lt_of_lt_of_le hm (Nat.pow_le_pow_right (by decide) (by omega))
    have hn : ¬ 2 ^ s ≤ m.toNat := by omega
    simp [hs, hn]

/-- The spec coefficient `±|v|` with last plane `lsb` (sign of a zero is irrelevant). -/
def coeffOf (v : Int32) (lsb : Nat) : Coeff :=
  { sig := v ≠ 0, sign := decide (v.toInt < 0), mag := v.toInt.natAbs, lsbPlane := lsb }

/-- `coeffOf` has the signed value `v`. -/
theorem coeffOf_value (v : Int32) (lsb : Nat) : (coeffOf v lsb).value = v.toInt := by
  unfold coeffOf Spec.Tier1.Coeff.value
  by_cases h : v.toInt < 0 <;> simp [h] <;> omega

/-- `satSigned` is `DWT53.sat32` of the signed magnitude, with the flag "in range". -/
theorem satSigned_spec (neg : Bool) (r : UInt64) (R : Nat)
    (hR : r.toNat = R ∨ (2 ^ 31 < r.toNat ∧ 2 ^ 31 < R)) :
    (satSigned neg r).1 = DWT53.sat32 (if neg then -(R : Int) else R) ∧
    ((satSigned neg r).2 = true ↔
      (-2 ^ 31 ≤ (if neg then -(R : Int) else R) ∧ (if neg then -(R : Int) else R) < 2 ^ 31)) := by
  have hr := r.toNat_lt
  unfold satSigned DWT53.sat32
  cases neg
  · simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases h : r ≤ 2147483647
    · have h' : r.toNat ≤ 2147483647 := by rw [UInt64.le_iff_toNat_le] at h; exact h
      have hRr : r.toNat = R := by omega
      simp only [h, ↓reduceIte]
      refine ⟨?_, by simp; omega⟩
      have hn1 : ¬ ((R : Int) < -2147483648) := by omega
      have hn2 : ¬ ((2147483647 : Int) < R) := by omega
      simp only [hn1, hn2, ↓reduceIte]
      apply Int32.toInt_inj.mp
      rw [Int64.toInt_toInt32, Int64.toInt_ofNat_of_lt (by omega),
        Int32.toInt_ofInt_of_le (by omega) (by omega)]
      rw [Int.bmod_eq_of_le (by omega) (by omega)]; omega
    · have h' : ¬ r.toNat ≤ 2147483647 := by rw [UInt64.le_iff_toNat_le] at h; exact h
      have hR2 : 2147483647 < R := by omega
      simp only [h, ↓reduceIte]
      have hn1 : ¬ ((R : Int) < -2147483648) := by omega
      have hn2 : ((2147483647 : Int) < R) := by omega
      simp only [hn1, hn2, ↓reduceIte]
      exact ⟨trivial, by simp; omega⟩
  · simp only [↓reduceIte]
    by_cases h : r ≤ 2147483648
    · have h' : r.toNat ≤ 2147483648 := by rw [UInt64.le_iff_toNat_le] at h; exact h
      have hRr : r.toNat = R := by omega
      simp only [h, ↓reduceIte]
      refine ⟨?_, by simp; omega⟩
      have hn1 : ¬ (-(R : Int) < -2147483648) := by omega
      have hn2 : ¬ ((2147483647 : Int) < -(R : Int)) := by omega
      simp only [hn1, hn2, ↓reduceIte]
      apply Int32.toInt_inj.mp
      have e1 : (-(r.toNat : Int)).bmod (2 ^ 64) = -(r.toNat : Int) :=
        Int.bmod_eq_of_le (by omega) (by omega)
      have e2 : (-(r.toNat : Int)).bmod (2 ^ 32) = -(r.toNat : Int) :=
        Int.bmod_eq_of_le (by omega) (by omega)
      rw [Int64.toInt_toInt32, show (Int64.ofNat r.toNat).neg = -(Int64.ofNat r.toNat) from rfl,
        Int64.toInt_neg, Int64.toInt_ofNat_of_lt (by omega), e1, e2,
        Int32.toInt_ofInt_of_le (by omega) (by omega)]
      omega
    · have h' : ¬ r.toNat ≤ 2147483648 := by rw [UInt64.le_iff_toNat_le] at h; exact h
      have hR2 : 2147483648 < R := by omega
      simp only [h, ↓reduceIte]
      have hn1 : (-(R : Int) < -2147483648) := by omega
      simp only [hn1, ↓reduceIte]
      exact ⟨trivial, by simp; omega⟩

/-- **Reversible kernel = spec.** `revCoeff s v lsb` is `Spec.Quant.dequantRev s c`
saturated to `Int32`, for every spec coefficient `c` with value `v` and last plane `lsb`
(e.g. the Tier-1 spec coefficient at the same position, by C3); the flag says that no
saturation happened. -/
theorem revCoeff_eq (s : Nat) (v : Int32) (c : Coeff) (hv : c.value = v.toInt) :
    (revCoeff s v c.lsbPlane).1 = DWT53.sat32 (Spec.Quant.dequantRev s c) ∧
    ((revCoeff s v c.lsbPlane).2 = true ↔
      (-2 ^ 31 ≤ Spec.Quant.dequantRev s c ∧ Spec.Quant.dequantRev s c < 2 ^ 31)) := by
  rw [Spec.Quant.dequantRev_congr s c (coeffOf v c.lsbPlane) (by rw [hv, coeffOf_value]) rfl]
  have hab := absU_toNat v
  have h1 := v.toInt_lt
  have h2 := v.le_toInt
  have hmlt : (absU v).toNat < 2 ^ 63 := by omega
  obtain ⟨hu1, hu2⟩ := unshift_spec s (absU v) c.lsbPlane hmlt
  have hcs : (Spec.Quant.roiUnshift s (coeffOf v c.lsbPlane)).sign = decide (v.toInt < 0) := by
    unfold Spec.Quant.roiUnshift coeffOf; split <;> rfl
  unfold revCoeff Spec.Quant.dequantRev
  generalize hml : unshift s (absU v) c.lsbPlane = ml at hu1 hu2
  obtain ⟨m, l⟩ := ml
  simp only at hu1 hu2 ⊢
  rw [hab] at hu1
  have hcm : (Spec.Quant.roiUnshift s (coeffOf v c.lsbPlane)).mag = m.toNat := by
    rw [hu1]; unfold Spec.Quant.roiUnshift coeffOf; split <;> rfl
  have hcl : (Spec.Quant.roiUnshift s (coeffOf v c.lsbPlane)).lsbPlane = l := by
    rw [hu2, hab]; unfold Spec.Quant.roiUnshift coeffOf; split <;> rfl
  generalize Spec.Quant.roiUnshift s (coeffOf v c.lsbPlane) = c' at hcs hcm hcl
  unfold Spec.Quant.reconstructRev
  rw [hcs, hcm, hcl]
  have hmb : m.toNat ≤ 2 ^ 31 := by
    rw [hu1]; split
    · exact Nat.le_trans (Nat.div_le_self _ _) (by omega)
    · omega
  by_cases hm0 : m = 0
  · have : m.toNat = 0 := by rw [hm0]; rfl
    simp only [hm0, beq_self_eq_true, ↓reduceIte]
    constructor <;> simp [DWT53.sat32]
  · have hmn : m.toNat ≠ 0 := fun h => hm0 (UInt64.toNat_inj.mp (by rw [h]; rfl))
    simp only [beq_iff_eq, hm0, ↓reduceIte, hmn]
    have hneg : (v < 0) = decide (v.toInt < 0) := by
      simp [Int32.lt_iff_toInt_lt]
    -- the half term
    have key : ∀ (half : UInt64), (m + half).toNat = m.toNat + 2 ^ l / 2 ∨
        (2 ^ 31 < (m + half).toNat ∧ 2 ^ 31 < m.toNat + 2 ^ l / 2) →
        (satSigned (decide (v < 0)) (m + half)).1 =
          DWT53.sat32 (if decide (v.toInt < 0) = true then -((m.toNat + 2 ^ l / 2 : Nat) : Int)
            else ((m.toNat + 2 ^ l / 2 : Nat) : Int)) ∧
        ((satSigned (decide (v < 0)) (m + half)).2 = true ↔
          (-2 ^ 31 ≤ (if decide (v.toInt < 0) = true then -((m.toNat + 2 ^ l / 2 : Nat) : Int)
            else ((m.toNat + 2 ^ l / 2 : Nat) : Int)) ∧
           (if decide (v.toInt < 0) = true then -((m.toNat + 2 ^ l / 2 : Nat) : Int)
            else ((m.toNat + 2 ^ l / 2 : Nat) : Int)) < 2 ^ 31)) := by
      intro half hh
      have hs := satSigned_spec (decide (v < 0)) (m + half) (m.toNat + 2 ^ l / 2) hh
      have hd : decide (v < 0) = decide (v.toInt < 0) := by
        simp [Int32.lt_iff_toInt_lt]
      rw [hd] at hs
      exact hs
    have hcast : ∀ b : Bool, (if b = true then -((m.toNat : Int) + ((2 ^ l / 2 : Nat) : Int))
        else (m.toNat : Int) + ((2 ^ l / 2 : Nat) : Int)) =
        (if b = true then -((m.toNat + 2 ^ l / 2 : Nat) : Int)
          else ((m.toNat + 2 ^ l / 2 : Nat) : Int)) := by
      intro b; push_cast; rfl
    rw [hcast]
    apply key
    by_cases hl0 : l = 0
    · left
      subst hl0
      simp
    · simp only [hl0, ↓reduceIte]
      by_cases hl : l ≤ 33
      · left
        simp only [hl, ↓reduceIte, UInt64.toNat_add]
        rw [shl1_toNat _ (by omega)]
        have hp : 2 ^ l / 2 = 2 ^ (l - 1) := by
          obtain ⟨k, hk⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
          rw [hk, Nat.pow_succ, Nat.mul_div_cancel _ (by decide)]; rfl
        have : 2 ^ (l - 1) ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) (by omega)
        rw [hp]; exact Nat.mod_eq_of_lt (by omega)
      · right
        simp only [hl, ↓reduceIte, UInt64.toNat_add]
        have : 2 ^ 33 ≤ 2 ^ l / 2 := by
          obtain ⟨k, hk⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
          rw [hk, show 2 ^ (k + 1) = 2 ^ k * 2 by rw [Nat.pow_succ], Nat.mul_div_cancel _ (by decide)]
          exact Nat.pow_le_pow_right (by decide) (by omega)
        have h8 : (8589934592 : UInt64).toNat = 8589934592 := rfl
        rw [h8, Nat.mod_eq_of_lt (by omega)]
        omega

/-- `DWT53.sat32` is the identity on the `Int32` range. -/
theorem sat32_toInt (z : Int) (h1 : -2 ^ 31 ≤ z) (h2 : z < 2 ^ 31) : (DWT53.sat32 z).toInt = z := by
  unfold DWT53.sat32
  simp only [show ¬ z < -2147483648 by omega, show ¬ ((2147483647 : Int) < z) by omega,
    ↓reduceIte]
  exact Int32.toInt_ofInt_of_le (by omega) (by omega)

/-- A rounding bound in `Rat`: `|r − n/P| ≤ 1/2` from `|r·P − n| ≤ P/2`. -/
theorem half_bound (r n P : Rat) (hP : 0 < P) (h1 : r * P ≤ n + P / 2)
    (h2 : n - P / 2 ≤ r * P) : r - n / P ≤ 1 / 2 ∧ -(1 / 2) ≤ r - n / P := by
  have hx : (r - n / P) * P = r * P - n := by
    rw [Rat.sub_eq_add_neg, Rat.add_mul, Rat.neg_mul, Rat.div_mul_cancel (Rat.ne_of_gt hP),
      ← Rat.sub_eq_add_neg]
  constructor
  · apply Rat.not_lt.mp
    intro hlt
    have := (Rat.mul_lt_mul_right hP).mpr hlt
    grind
  · apply Rat.not_lt.mp
    intro hlt
    have := (Rat.mul_lt_mul_right hP).mpr hlt
    grind

/-- `(a·c)/(b·c) = a/b` for `c ≠ 0`. -/
theorem mul_div_mul_right' (a b c : Rat) (hc : c ≠ 0) : (a * c) / (b * c) = a / b := by grind

/-- The exact fixed-point value: `(M + 2^l/2)·Δ·2^F = n·2^(R+F) / 2^(ε+12)` with
`n = (2M + 2^l)(2^11 + μ)` (E-3 with gain folded into `R`). -/
theorem scaled_value (M l R F e mu : Nat) :
    ((M : Rat) + ((2 ^ l : Nat) : Rat) / 2) * Spec.Quant.stepSize R 0 e mu * ((2 ^ F : Nat) : Rat) =
      (((2 * M + 2 ^ l) * (2048 + mu) * 2 ^ (R + F) : Nat) : Rat) / ((2 ^ (e + 12) : Nat) : Rat) := by
  unfold Spec.Quant.stepSize
  have h1 : ((2 ^ (e + 12) : Nat) : Rat) = ((2 ^ (e + 11) : Nat) : Rat) * 2 := by
    rw [show e + 12 = (e + 11) + 1 from rfl, Nat.pow_succ]; push_cast; rfl
  have hp : ((2 ^ (e + 11) : Nat) : Rat) ≠ 0 := by
    have : 0 < 2 ^ (e + 11) := Nat.two_pow_pos _
    exact_mod_cast Nat.ne_of_gt this
  rw [h1, Nat.add_zero, Nat.pow_add 2 R F]
  push_cast
  generalize ((2 : Rat) ^ (e + 11)) = P at hp ⊢
  grind

/-- **Irreversible kernel error bound (C8 for dequantisation).** For every spec coefficient
`c` with value `v` and last plane `lsb` (by C3, the Tier-1 spec coefficient at the same
position), if the kernel reports no saturation, its output differs from the exact
`dequantIrrev s Δb c · 2^F` by at most `1/2` (one half unit in the last place of the
`F`-bit fixed point). -/
theorem irrevCoeff_bound (q : BandQuant) (F s : Nat) (v : Int32) (c : Coeff)
    (hv : c.value = v.toInt) (hmu : q.mantissa < 2048)
    (hok : (irrevCoeff (irrevConsts q F) s v c.lsbPlane).2 = true) :
    ((irrevCoeff (irrevConsts q F) s v c.lsbPlane).1.toInt : Rat) -
        Spec.Quant.dequantIrrevScaled s q.delta F c ≤ 1 / 2 ∧
      -(1 / 2) ≤ ((irrevCoeff (irrevConsts q F) s v c.lsbPlane).1.toInt : Rat) -
        Spec.Quant.dequantIrrevScaled s q.delta F c := by
  unfold Spec.Quant.dequantIrrevScaled
  rw [Spec.Quant.dequantIrrev_congr s q.delta c (coeffOf v c.lsbPlane)
    (by rw [hv, coeffOf_value]) rfl]
  have hab := absU_toNat v
  have h1 := v.toInt_lt
  have h2 := v.le_toInt
  have hmlt : (absU v).toNat < 2 ^ 63 := by omega
  obtain ⟨hu1, hu2⟩ := unshift_spec s (absU v) c.lsbPlane hmlt
  have hcs : (Spec.Quant.roiUnshift s (coeffOf v c.lsbPlane)).sign = decide (v.toInt < 0) := by
    unfold Spec.Quant.roiUnshift coeffOf; split <;> rfl
  unfold irrevCoeff at hok ⊢
  unfold Spec.Quant.dequantIrrev
  generalize hml : unshift s (absU v) c.lsbPlane = ml at hu1 hu2 hok
  obtain ⟨m, l⟩ := ml
  simp only at hu1 hu2 hok ⊢
  rw [hab] at hu1
  have hcm : (Spec.Quant.roiUnshift s (coeffOf v c.lsbPlane)).mag = m.toNat := by
    rw [hu1]; unfold Spec.Quant.roiUnshift coeffOf; split <;> rfl
  have hcl : (Spec.Quant.roiUnshift s (coeffOf v c.lsbPlane)).lsbPlane = l := by
    rw [hu2, hab]; unfold Spec.Quant.roiUnshift coeffOf; split <;> rfl
  generalize Spec.Quant.roiUnshift s (coeffOf v c.lsbPlane) = c' at hcs hcm hcl
  unfold Spec.Quant.reconstructIrrev
  rw [hcs, hcm, hcl]
  have hmb : m.toNat ≤ 2 ^ 31 := by
    rw [hu1]; split
    · exact Nat.le_trans (Nat.div_le_self _ _) (by omega)
    · omega
  by_cases hm0 : m = 0
  · have : m.toNat = 0 := by rw [hm0]; rfl
    simp only [hm0, beq_self_eq_true, ↓reduceIte]
    simp only [Int32.toInt_zero]
    constructor <;> grind
  · have hmn : m.toNat ≠ 0 := fun h => hm0 (UInt64.toNat_inj.mp (by rw [h]; rfl))
    simp only [beq_iff_eq, hm0, ↓reduceIte, hmn] at hok ⊢
    by_cases hl : l > 33
    · simp [hl] at hok
    · simp only [hl, ↓reduceIte] at hok ⊢
      -- the integer `n`
      have ht : ((m <<< (1 : UInt64)) + (1 : UInt64) <<< l.toUInt64).toNat = 2 * m.toNat + 2 ^ l := by
        have e1 : (m <<< (1 : UInt64)).toNat = 2 * m.toNat := by
          rw [UInt64.toNat_shiftLeft]
          simp only [UInt64.toNat_one, Nat.one_mod, Nat.shiftLeft_eq, Nat.pow_one]
          omega
        rw [UInt64.toNat_add, shl1_toNat l (by omega), e1]
        have : 2 ^ l ≤ 2 ^ 33 := Nat.pow_le_pow_right (by decide) (by omega)
        exact Nat.mod_eq_of_lt (by omega)
      have hmult : (irrevConsts q F).mult.toNat = 2048 + q.mantissa := by
        simp only [irrevConsts, Nat.toUInt64_eq, UInt64.toNat_ofNat']
        rw [Nat.mod_eq_of_lt hmu]; exact Nat.mod_eq_of_lt (by omega)
      generalize hT : (m <<< (1 : UInt64)) + (1 : UInt64) <<< l.toUInt64 = t at ht hok ⊢
      have hN : (t * (irrevConsts q F).mult).toNat = (2 * m.toNat + 2 ^ l) * (2048 + q.mantissa) := by
        rw [UInt64.toNat_mul, ht, hmult]
        have : 2 ^ l ≤ 2 ^ 33 := Nat.pow_le_pow_right (by decide) (by omega)
        exact Nat.mod_eq_of_lt (by
          have : (2 * m.toNat + 2 ^ l) * (2048 + q.mantissa) ≤ (2 ^ 32 + 2 ^ 33) * 4096 :=
            Nat.mul_le_mul (by omega) (by omega)
          omega)
      have hNb : (2 * m.toNat + 2 ^ l) * (2048 + q.mantissa) < 2 ^ 46 := by
        have : 2 ^ l ≤ 2 ^ 33 := Nat.pow_le_pow_right (by decide) (by omega)
        have : (2 * m.toNat + 2 ^ l) * (2048 + q.mantissa) ≤ (2 ^ 32 + 2 ^ 33) * 4095 :=
          Nat.mul_le_mul (by omega) (by omega)
        omega
      generalize hn : t * (irrevConsts q F).mult = n at hN hok ⊢
      generalize hNdef : (2 * m.toNat + 2 ^ l) * (2048 + q.mantissa) = N at hN hNb
      -- the satSigned step
      generalize hr : scaleMag (irrevConsts q F) n = r at hok ⊢
      obtain ⟨hs1, hs2⟩ := satSigned_spec (decide (v < 0)) r r.toNat (Or.inl rfl)
      have hin := hs2.mp hok
      have hz : ((satSigned (decide (v < 0)) r).1.toInt : Int) =
          (if decide (v < 0) = true then -(r.toNat : Int) else r.toNat) := by
        rw [hs1]; exact sat32_toInt _ hin.1 hin.2
      rw [hz]
      have hd : decide (v < 0) = decide (v.toInt < 0) := by simp [Int32.lt_iff_toInt_lt]
      rw [hd]
      -- the exact value
      have hX : ((m.toNat : Rat) + ((2 ^ l : Nat) : Rat) / 2) * q.delta * ((2 ^ F : Nat) : Rat) =
          ((N * 2 ^ (q.range + F) : Nat) : Rat) / ((2 ^ (q.exponent + 12) : Nat) : Rat) := by
        unfold Spec.Quant.BandQuant.delta
        rw [scaled_value, ← hNdef]
      -- magnitude bound: |r − X| ≤ 1/2
      have hmag : (r.toNat : Rat) - ((N * 2 ^ (q.range + F) : Nat) : Rat) /
            ((2 ^ (q.exponent + 12) : Nat) : Rat) ≤ 1 / 2 ∧
          -(1 / 2) ≤ (r.toNat : Rat) - ((N * 2 ^ (q.range + F) : Nat) : Rat) /
            ((2 ^ (q.exponent + 12) : Nat) : Rat) := by
        have hin' := hin
        unfold scaleMag irrevConsts at hr
        simp only at hr
        by_cases hup : q.exponent + 12 ≤ q.range + F
        · simp only [hup, decide_true, ↓reduceIte] at hr
          by_cases hc : q.range + F - (q.exponent + 12) < 64 ∧
              n ≤ (0x7FFFFFFF : UInt64) >>> (q.range + F - (q.exponent + 12)).toUInt64
          · simp only [hc, and_self, ↓reduceIte] at hr
            have hsh := shr_toNat (0x7FFFFFFF : UInt64) _ hc.1
            have hle := hc.2
            rw [UInt64.le_iff_toNat_le, hsh, hN] at hle
            have h7 : (0x7FFFFFFF : UInt64).toNat = 2147483647 := rfl
            rw [h7] at hle
            have hrN : r.toNat = N * 2 ^ (q.range + F - (q.exponent + 12)) := by
              rw [← hr, UInt64.toNat_shiftLeft, hN, Nat.toUInt64_eq, UInt64.toNat_ofNat',
                Nat.mod_eq_of_lt (by omega : q.range + F - (q.exponent + 12) < 2 ^ 64),
                Nat.mod_eq_of_lt hc.1, Nat.shiftLeft_eq]
              apply Nat.mod_eq_of_lt
              have := (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mp hle
              omega
            have hexp : ((N * 2 ^ (q.range + F) : Nat) : Rat) / ((2 ^ (q.exponent + 12) : Nat) : Rat)
                = (r.toNat : Rat) := by
              generalize he : q.range + F - (q.exponent + 12) = e at hrN
              have hsum : q.range + F = e + (q.exponent + 12) := by omega
              rw [hrN, hsum, Nat.pow_add, ← Nat.mul_assoc]
              have hp : ((2 ^ (q.exponent + 12) : Nat) : Rat) ≠ 0 := by
                have : 0 < 2 ^ (q.exponent + 12) := Nat.two_pow_pos _
                exact_mod_cast Nat.ne_of_gt this
              rw [Rat.natCast_mul]
              exact Rat.mul_div_cancel hp
            rw [hexp]; constructor <;> grind
          · simp only [hc, ↓reduceIte] at hr
            have : r.toNat = 0x10000000000 := by rw [← hr]; rfl
            simp only [this] at hin; omega
        · simp only [hup, decide_false, Bool.false_eq_true, ↓reduceIte] at hr
          have hP : (0 : Rat) < ((2 ^ (q.exponent + 12 - (q.range + F)) : Nat) : Rat) := by
            have : 0 < 2 ^ (q.exponent + 12 - (q.range + F)) := Nat.two_pow_pos _
            exact_mod_cast this
          have hdiv : ((N * 2 ^ (q.range + F) : Nat) : Rat) / ((2 ^ (q.exponent + 12) : Nat) : Rat)
              = (N : Rat) / ((2 ^ (q.exponent + 12 - (q.range + F)) : Nat) : Rat) := by
            generalize he : q.exponent + 12 - (q.range + F) = e at hP ⊢
            have hsum : q.exponent + 12 = e + (q.range + F) := by omega
            rw [hsum, Nat.pow_add 2 e (q.range + F), Rat.natCast_mul, Rat.natCast_mul]
            have hp1 : ((2 ^ (q.range + F) : Nat) : Rat) ≠ 0 := by
              have : 0 < 2 ^ (q.range + F) := Nat.two_pow_pos _
              exact_mod_cast Nat.ne_of_gt this
            exact mul_div_mul_right' _ _ _ hp1
          rw [hdiv]
          generalize hdd : q.exponent + 12 - (q.range + F) = d at hP hr
          have hd1 : 1 ≤ d := by omega
          apply half_bound _ _ _ hP
          · by_cases h48 : 48 ≤ d
            · simp only [h48, ↓reduceIte] at hr
              rw [← hr]
              have : 2 ^ 47 ≤ 2 ^ (d - 1) := Nat.pow_le_pow_right (by decide) (by omega)
              have hh : ((2 ^ d : Nat) : Rat) / 2 = ((2 ^ (d - 1) : Nat) : Rat) := by
                rw [show d = (d - 1) + 1 by omega, Nat.pow_succ, Nat.add_sub_cancel]; push_cast; grind
              rw [hh]; simp
              have : (0 : Rat) ≤ (N : Rat) := by exact_mod_cast Nat.zero_le N
              have : (0 : Rat) ≤ ((2 ^ (d - 1) : Nat) : Rat) := by exact_mod_cast Nat.zero_le _
              grind
            · simp only [h48, ↓reduceIte] at hr
              have hrv : r.toNat = (N + 2 ^ (d - 1)) / 2 ^ d := by
                rw [← hr, shr_toNat _ _ (by omega), UInt64.toNat_add, shl1_toNat _ (by omega), hN]
                have : 2 ^ (d - 1) ≤ 2 ^ 46 := Nat.pow_le_pow_right (by decide) (by omega)
                rw [Nat.mod_eq_of_lt (by omega)]
              have hh : ((2 ^ d : Nat) : Rat) / 2 = ((2 ^ (d - 1) : Nat) : Rat) := by
                rw [show d = (d - 1) + 1 by omega, Nat.pow_succ, Nat.add_sub_cancel]; push_cast; grind
              rw [hh, hrv]
              have := Nat.div_mul_le_self (N + 2 ^ (d - 1)) (2 ^ d)
              have : (((N + 2 ^ (d - 1)) / 2 ^ d * 2 ^ d : Nat) : Rat) ≤
                  ((N + 2 ^ (d - 1) : Nat) : Rat) := by exact_mod_cast this
              push_cast at this ⊢
              exact this
          · by_cases h48 : 48 ≤ d
            · simp only [h48, ↓reduceIte] at hr
              rw [← hr]
              have : N < 2 ^ (d - 1) := by
                have : 2 ^ 47 ≤ 2 ^ (d - 1) := Nat.pow_le_pow_right (by decide) (by omega)
                omega
              have hh : ((2 ^ d : Nat) : Rat) / 2 = ((2 ^ (d - 1) : Nat) : Rat) := by
                rw [show d = (d - 1) + 1 by omega, Nat.pow_succ, Nat.add_sub_cancel]; push_cast; grind
              rw [hh]
              have : (N : Rat) ≤ ((2 ^ (d - 1) : Nat) : Rat) := by exact_mod_cast Nat.le_of_lt this
              simp; grind
            · simp only [h48, ↓reduceIte] at hr
              have hrv : r.toNat = (N + 2 ^ (d - 1)) / 2 ^ d := by
                rw [← hr, shr_toNat _ _ (by omega), UInt64.toNat_add, shl1_toNat _ (by omega), hN]
                have : 2 ^ (d - 1) ≤ 2 ^ 46 := Nat.pow_le_pow_right (by decide) (by omega)
                rw [Nat.mod_eq_of_lt (by omega)]
              have hh : ((2 ^ d : Nat) : Rat) / 2 = ((2 ^ (d - 1) : Nat) : Rat) := by
                rw [show d = (d - 1) + 1 by omega, Nat.pow_succ, Nat.add_sub_cancel]; push_cast; grind
              rw [hh, hrv]
              have hlt := Nat.lt_div_mul_add (a := N + 2 ^ (d - 1)) (Nat.two_pow_pos d)
              have h2d : 2 ^ d = 2 * 2 ^ (d - 1) := by
                rw [show d = (d - 1) + 1 by omega, Nat.pow_succ, Nat.add_sub_cancel, Nat.mul_comm]
              have : N ≤ (N + 2 ^ (d - 1)) / 2 ^ d * 2 ^ d + 2 ^ (d - 1) := by omega
              have : ((N : Nat) : Rat) ≤ (((N + 2 ^ (d - 1)) / 2 ^ d * 2 ^ d + 2 ^ (d - 1) : Nat) : Rat) := by
                exact_mod_cast this
              push_cast at this ⊢
              grind
      cases decide (v.toInt < 0)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [hX]; push_cast at hmag ⊢; exact hmag
      · simp only [↓reduceIte]
        rw [show -(((m.toNat : Rat) + ((2 ^ l : Nat) : Rat) / 2) * q.delta) * ((2 ^ F : Nat) : Rat) =
          -(((m.toNat : Rat) + ((2 ^ l : Nat) : Rat) / 2) * q.delta * ((2 ^ F : Nat) : Rat)) by grind,
          hX]
        push_cast at hmag ⊢
        constructor <;> grind

end JPEG2000.Quant
