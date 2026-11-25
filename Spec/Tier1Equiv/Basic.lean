import JPEG2000.Tier1.Decode
import Spec.Tier1.Decode
import Spec.MQEquiv

/-!
# C3 (plain mode), part 1: bits, bordered indices, spec coefficient access, look-up tables

Plan.md §4 (C3), §5.1, §5.2 "Tier-1 / EBCOT"; T.800 Annex D (D.3.1–D.3.4, Tables D.1–D.4).
Task 3.6.

Basic facts used by the simulation between the fast Tier-1 decoder `JPEG2000.Tier1` and the
spec `JPEG2000.Spec.Tier1`:

* `bt f j` — bit `j` of a flag word; how `|||`, `&&&`, `~~~` and masks act on bits; the
  "`f &&& M == 0`" tests as bit statements.
* `bidx w x y` — the bordered index `(y + 1)(w + 2) + x + 1` of interior position `(x, y)`
  and the injectivity of bordered coordinates.
* `Geom.coeffAt` / `Geom.setCoeff` read-after-write lemmas.
* **The look-up tables equal the spec tables**: `zcCtx_eq` (Table D.1, all orientations,
  through `zcOf` and `zcTable`), `scEntry_eq` (Tables D.2/D.3 through `scLut`), proved from
  finite `decide` checks over the in-range inputs (256 sign indices; all neighbour counts).
-/

namespace JPEG2000.Spec.Tier1Equiv

open JPEG2000
open JPEG2000.Tier2.Geometry (Band)
open JPEG2000.Spec.Tier1 (Coeff Geom DecState Orientation NeighbourSign)

/-! ## Orientation of a band -/

/-- The spec orientation of a fast-decoder band (same four names). -/
def orientOf : Band → Orientation
  | .LL => .LL
  | .HL => .HL
  | .LH => .LH
  | .HH => .HH

/-! ## Bits of flag words -/

/-- Bit `j` of the word `f`. -/
def bt (f : UInt32) (j : Nat) : Bool := f.toNat.testBit j

/-- `testBit` of a numeral, evaluated by `simp` once the bit index is a numeral too. -/
theorem testBit_lit (n i : Nat) : Nat.testBit (no_index (OfNat.ofNat n)) i =
    decide ((OfNat.ofNat n : Nat) / 2 ^ i % 2 = 1) :=
  Nat.testBit_eq_decide_div_mod_eq

/-- `if` with a true condition (non-deprecated `if_pos`). -/
theorem ite_pos' {α : Type} {c : Prop} [Decidable c] (h : c) {a b : α} :
    (if c then a else b) = a := by simp [h]

/-- `if` with a false condition (non-deprecated `if_neg`). -/
theorem ite_neg' {α : Type} {c : Prop} [Decidable c] (h : ¬c) {a b : α} :
    (if c then a else b) = b := by simp [h]

/-- Bits of an OR. -/
@[simp] theorem bt_or (a b : UInt32) (j : Nat) : bt (a ||| b) j = (bt a j || bt b j) := by
  simp [bt, UInt32.toNat_or, Nat.testBit_or]

/-- Bits of an AND. -/
@[simp] theorem bt_and (a b : UInt32) (j : Nat) : bt (a &&& b) j = (bt a j && bt b j) := by
  simp [bt, UInt32.toNat_and, Nat.testBit_and]

/-- Bits of a word above 31 are clear. -/
theorem bt_ge32 (f : UInt32) (j : Nat) (hj : 32 ≤ j) : bt f j = false := by
  unfold bt
  apply Nat.testBit_lt_two_pow
  have h1 := f.toNat_lt
  have h2 : 2 ^ 32 ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) hj
  have : UInt32.size = 2 ^ 32 := rfl
  omega

/-- A word is zero iff all its bits are clear. -/
theorem eq_zero_iff_bt (f : UInt32) : f = 0 ↔ ∀ j, bt f j = false := by
  constructor
  · intro h j; rw [h]; exact Nat.zero_testBit j
  · intro h
    apply UInt32.toNat_inj.mp
    apply Nat.eq_of_testBit_eq
    intro j; simpa [bt] using h j

/-- A word below `2^16` has no bit from 16 on. -/
theorem bt_hi (f : UInt32) (hf : f.toNat < 2 ^ 16) (j : Nat) (hj : 16 ≤ j) : bt f j = false := by
  unfold bt
  apply Nat.testBit_lt_two_pow
  have h2 : 2 ^ 16 ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) hj
  omega

/-- A masked test against a 16-bit mask only depends on the low 16 bits. -/
theorem and_eq_zero_iff (f M : UInt32) (hM : M.toNat < 2 ^ 16) :
    (f &&& M == 0) = !((List.range 16).any fun j => bt M j && bt f j) := by
  have key : (f &&& M = 0) ↔ ¬ ((List.range 16).any fun j => bt M j && bt f j) = true := by
    rw [eq_zero_iff_bt]
    simp only [bt_and, List.any_eq_true, List.mem_range, Bool.and_eq_true, not_exists,
      not_and]
    constructor
    · intro h j hj h1 h2; have := h j; rw [h1, h2] at this; simp at this
    · intro h j
      by_cases hj : j < 16
      · cases h1 : bt f j <;> cases h2 : bt M j <;> simp_all
      · rw [bt_hi M hM j (by omega)]; simp
  by_cases h : f &&& M = 0
  · rw [h]; have := key.mp h; simp only [Bool.not_eq_true] at this; simp [this]
  · have h' : (f &&& M == 0) = false := by simpa using h
    rw [h']
    have := (not_congr key).mp h
    simp only [Bool.not_eq_true, Bool.not_eq_false] at this
    simp [this]

/-- `n % 256` as its eight low bits. -/
theorem bitOf_lt8 (n i : Nat) (hi : i < 8) :
    Tier1.bitOf (n % 256) i = if n.testBit i then 1 else 0 := by
  unfold Tier1.bitOf
  have : (n % 256).testBit i = n.testBit i := by
    rw [show (256 : Nat) = 2 ^ 8 from rfl, Nat.testBit_mod_two_pow]; simp [hi]
  rw [← this, Nat.testBit_eq_decide_div_mod_eq]
  split <;> simp_all <;> omega

/-! ## Bordered indices -/

/-- Bordered index of interior position `(x, y)` in a block of width `w`. -/
def bidx (w x y : Nat) : Nat := (y + 1) * (w + 2) + x + 1

/-- Bordered coordinates are unique: `Y·st + X` with `X < st` determines `X` and `Y`. -/
theorem rowcol_inj {st X Y X' Y' : Nat} (hX : X < st) (hX' : X' < st)
    (h : Y * st + X = Y' * st + X') : X = X' ∧ Y = Y' := by
  have h1 : (Y * st + X) / st = Y := by
    rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hX]
    simp
  have h2 : (Y' * st + X') / st = Y' := by
    rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hX']
    simp
  have hY : Y = Y' := by rw [← h1, ← h2, h]
  subst hY
  exact ⟨by omega, rfl⟩

/-- The bordered array has room for every neighbour of an interior position. -/
theorem nb_lt_size {w h x y : Nat} (hx : x < w) (hy : y < h) (dx dy : Nat) (hdx : dx ≤ 2)
    (hdy : dy ≤ 2) : (y + dy) * (w + 2) + (x + dx) < (w + 2) * (h + 2) := by
  have : (y + dy + 1) * (w + 2) ≤ (h + 2) * (w + 2) := Nat.mul_le_mul_right _ (by omega)
  rw [Nat.add_mul, Nat.one_mul] at this
  rw [Nat.mul_comm (w + 2)]
  omega

/-! ## Checked array access -/

/-- `fset` keeps the size. -/
@[simp] theorem fset_size (a : Array UInt32) (i : Nat) (v : UInt32) :
    (Tier1.fset a i v).size = a.size := by
  unfold Tier1.fset; split <;> simp

/-- `fadd` keeps the size. -/
@[simp] theorem fadd_size (a : Array UInt32) (i : Nat) (m : UInt32) :
    (Tier1.fadd a i m).size = a.size := by
  simp [Tier1.fadd]

/-- Reading after `fset`. -/
theorem fget_fset (a : Array UInt32) (i k : Nat) (v : UInt32) (hi : i < a.size) :
    Tier1.fget (Tier1.fset a i v) k = if i = k then v else Tier1.fget a k := by
  unfold Tier1.fget Tier1.fset
  simp only [hi, ↓reduceDIte]
  by_cases hk : k < a.size
  · simp only [Array.size_set, hk, ↓reduceDIte, Array.getElem_set]
  · have : i ≠ k := by omega
    simp [hk, this]

/-- Reading after `fadd`. -/
theorem fget_fadd (a : Array UInt32) (i k : Nat) (m : UInt32) (hi : i < a.size) :
    Tier1.fget (Tier1.fadd a i m) k = if i = k then Tier1.fget a k ||| m else Tier1.fget a k := by
  unfold Tier1.fadd; rw [fget_fset _ _ _ _ hi]; split <;> simp_all

/-! ## Spec coefficient access -/

/-- Reading an in-block coefficient. -/
theorem coeffAt_nat (g : Geom) (cs : Array Coeff) (x y : Nat) (hx : x < g.width)
    (hy : y < g.height) : g.coeffAt cs x y = cs.getD (g.idx x y) {} := by
  simp [Geom.coeffAt, hx, hy]

/-- Raster indices of in-block positions are in range. -/
theorem idx_lt (g : Geom) {x y : Nat} (hx : x < g.width) (hy : y < g.height) :
    g.idx x y < g.width * g.height := by
  unfold Geom.idx
  have : (y + 1) * g.width ≤ g.height * g.width := Nat.mul_le_mul_right _ hy
  rw [Nat.add_mul, Nat.one_mul] at this
  rw [Nat.mul_comm g.width]; omega

/-- Read after write of spec coefficients (any integer position; `(x, y)` in the block). -/
theorem coeffAt_setCoeff (g : Geom) (cs : Array Coeff) (hs : cs.size = g.width * g.height)
    (x y : Nat) (hx : x < g.width) (hy : y < g.height) (c : Coeff) (X Y : Int) :
    g.coeffAt (g.setCoeff cs x y c) X Y =
      if X = x ∧ Y = y then c else g.coeffAt cs X Y := by
  unfold Geom.coeffAt Geom.setCoeff
  have hsz : (cs.setIfInBounds (g.idx x y) c).size = cs.size := by simp
  by_cases hin : 0 ≤ X ∧ X < g.width ∧ 0 ≤ Y ∧ Y < g.height
  · simp only [hin, and_self, ↓reduceIte]
    have hl : g.idx X.toNat Y.toNat < cs.size := by
      rw [hs]; exact idx_lt g (by omega) (by omega)
    rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem (by rw [hsz]; exact hl), Array.getElem?_eq_getElem hl]
    simp only [Option.getD_some]
    rw [Array.getElem_setIfInBounds hl]
    by_cases he : X = x ∧ Y = y
    · obtain ⟨rfl, rfl⟩ := he
      simp
    · have hne : g.idx x y ≠ g.idx X.toNat Y.toNat := by
        intro hh
        unfold Geom.idx at hh
        obtain ⟨a, b⟩ := rowcol_inj (st := g.width) hx (by omega) hh
        omega
      simp [hne, he]
  · have : ¬ (X = x ∧ Y = y) := by omega
    simp [hin, this]

/-- `setCoeff` keeps the size. -/
@[simp] theorem setCoeff_size (g : Geom) (cs : Array Coeff) (x y : Nat) (c : Coeff) :
    (g.setCoeff cs x y c).size = cs.size := by
  simp [Geom.setCoeff]

/-! ## Look-up tables = spec tables (Tables D.1–D.3) -/

/-- The fast transcription of Table D.1 (LL/LH column) agrees with the spec on all in-range
counts. -/
theorem zcLLLH_eq : ∀ h < 3, ∀ v < 3, ∀ d < 5,
    Tier1.zcLLLH h v d = Spec.Tier1.zcTableLLLH h v d := by decide

/-- The fast transcription of Table D.1 (HH column) agrees with the spec on all in-range
counts. -/
theorem zcHHcol_eq : ∀ hv < 5, ∀ d < 5, Tier1.zcHHcol hv d = Spec.Tier1.zcTableHH hv d := by
  decide

/-- `zcOf` from the eight neighbour bits equals the spec's Table D.1 context. -/
theorem zcOf_eq (b : Band) (n : Nat) :
    Tier1.zcOf b n = Spec.Tier1.zcContext (orientOf b)
      (Tier1.bitOf n 1 + Tier1.bitOf n 2) (Tier1.bitOf n 0 + Tier1.bitOf n 3)
      (Tier1.bitOf n 4 + Tier1.bitOf n 5 + Tier1.bitOf n 6 + Tier1.bitOf n 7) := by
  have hb : ∀ i, Tier1.bitOf n i < 2 := fun i => Nat.mod_lt _ (by decide)
  have h0 := hb 0; have h1 := hb 1; have h2 := hb 2; have h3 := hb 3
  have h4 := hb 4; have h5 := hb 5; have h6 := hb 6; have h7 := hb 7
  cases b <;> simp only [Tier1.zcOf, orientOf, Spec.Tier1.zcContext]
  · exact zcLLLH_eq _ (by omega) _ (by omega) _ (by omega)
  · exact zcLLLH_eq _ (by omega) _ (by omega) _ (by omega)
  · exact zcLLLH_eq _ (by omega) _ (by omega) _ (by omega)
  · exact zcHHcol_eq _ (by omega) _ (by omega)

/-- Every zero-coding table entry is at most 8. -/
theorem zcOf_le (b : Band) (n : Nat) : Tier1.zcOf b n ≤ 8 := by
  rw [zcOf_eq]; exact Spec.Tier1.zcContext_le _ _ _ _

/-- The zero-coding look-up of a flag word is `zcOf` of its low byte. -/
theorem zcCtx_eq (b : Band) (f : UInt32) :
    Tier1.zcCtx (Tier1.zcFor b) (Tier1.zcFor_size b) f = Tier1.zcOf b (f.toNat % 256) := by
  have hle := zcOf_le b (f.toNat % 256)
  have e : f.toUInt8.toNat = f.toNat % 256 := by simp [UInt32.toNat_toUInt8]
  unfold Tier1.zcCtx
  have : ∀ (t : ByteArray) (ht : t.size = 256), t = Tier1.zcTable b →
      (t.get f.toUInt8.toNat (by rw [ht]; exact UInt8.toNat_lt _)).toNat =
        Tier1.zcOf b (f.toNat % 256) := by
    intro t ht htb
    subst htb
    simp only [Tier1.zcTable, ByteArray.get, Array.getElem_ofFn, e]
    simp only [Nat.toUInt8, UInt8.toNat_ofNat']
    omega
  exact this _ (Tier1.zcFor_size b) (Tier1.zcFor_eq b)

/-- The spec sign-coding entry (context `* 2 + XORbit`) from the significance and sign bits of
the four horizontal/vertical neighbours (N, W, E, S). -/
def scSpec (sN sW sE sS nN nW nE nS : Bool) : Nat :=
  let r := Spec.Tier1.scContext
    (Spec.Tier1.signContribution (NeighbourSign.ofBits sW nW) (NeighbourSign.ofBits sE nE))
    (Spec.Tier1.signContribution (NeighbourSign.ofBits sN nN) (NeighbourSign.ofBits sS nS))
  r.1 * 2 + if r.2 then 1 else 0

/-- Table D.2/D.3 transcription `scOf` = spec, for all 256 sign indices. -/
theorem scOf_eq_all : ∀ n < 256, Tier1.scOf n = scSpec
    (Tier1.bitOf n 0 == 1) (Tier1.bitOf n 1 == 1) (Tier1.bitOf n 2 == 1) (Tier1.bitOf n 3 == 1)
    (Tier1.bitOf n 4 == 1) (Tier1.bitOf n 5 == 1) (Tier1.bitOf n 6 == 1)
    (Tier1.bitOf n 7 == 1) := by
  decide +kernel

/-- Every `scOf` entry is below 32. -/
theorem scOf_lt : ∀ n < 256, Tier1.scOf n < 32 := by decide +kernel

/-- Bits of the sign index of a flag word: N, W, E, S significance (bits 0–3) then their sign
bits (flag bits 8–11). -/
theorem scIndex_bit (f : UInt32) (i : Nat) (hi : i < 8) :
    (Tier1.scIndex f).toNat.testBit i = if i < 4 then bt f i else bt f (i + 4) := by
  simp only [Tier1.scIndex, UInt32.toNat_toUInt8]
  rw [Nat.testBit_mod_two_pow]
  simp only [UInt32.toNat_or, UInt32.toNat_and, UInt32.toNat_shiftRight, Nat.testBit_or,
    Nat.testBit_and, Nat.testBit_shiftRight, bt]
  have h8 : decide (i < 8) = true := by simp [hi]
  rw [h8, Bool.true_and]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [testBit_lit, Nat.add_comm]

/-- `bitOf` as a bit test. -/
theorem bitOf_eq (n i : Nat) : (Tier1.bitOf n i == 1) = n.testBit i := by
  rw [Nat.testBit_eq_decide_div_mod_eq]; simp only [Tier1.bitOf]
  by_cases h : n / 2 ^ i % 2 = 1 <;> simp [h]

/-- The sign-coding look-up of a flag word equals the spec entry on its bits 0–3 and 8–11. -/
theorem scEntry_eq (f : UInt32) :
    (Tier1.scEntry f).toNat = scSpec (bt f 0) (bt f 1) (bt f 2) (bt f 3)
      (bt f 8) (bt f 9) (bt f 10) (bt f 11) := by
  have hlt := UInt8.toNat_lt (Tier1.scIndex f)
  have hs := scOf_lt _ hlt
  have he := scOf_eq_all _ hlt
  simp only [bitOf_eq] at he
  rw [scIndex_bit f 0 (by decide), scIndex_bit f 1 (by decide), scIndex_bit f 2 (by decide),
    scIndex_bit f 3 (by decide), scIndex_bit f 4 (by decide), scIndex_bit f 5 (by decide),
    scIndex_bit f 6 (by decide), scIndex_bit f 7 (by decide)] at he
  simp only [Nat.reduceLT, ↓reduceIte, Nat.lt_irrefl, Nat.reduceAdd] at he
  rw [← he]
  simp only [Tier1.scEntry, Tier1.scLut, ByteArray.get, Array.getElem_ofFn]
  simp only [Nat.toUInt8, UInt8.toNat_ofNat']
  omega

end JPEG2000.Spec.Tier1Equiv
