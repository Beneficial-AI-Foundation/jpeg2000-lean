import JPEG2000.Header
import Spec.MCT

/-!
# Wide native component samples (Plan.md §§4, 5.4, 6; T.800 A.5.1 and G.1)

A final, DC-shifted component sample fits in a signed 64-bit cell for every Part 1
precision. Each cell occupies two consecutive little-endian words in a single
`Bytes.Plane` buffer. Its linear index is in samples, including on a reduced component grid.
The work limit counts those samples and the decoded-byte limit uses the component's
`Header.bytesPerSample`, as in `Decode.allocOutput`. Callers allocating a group of
planes also check its aggregate budgets.
-/

namespace JPEG2000.Bytes

open Spec.MCT

/-- The admitted SIZ sample format and its cached inclusive G.1 endpoints. -/
structure NativeSampleRange where
  /-- Precision in bits. -/
  depth : Nat
  /-- Signedness from SIZ. -/
  signed : Bool
  /-- Part 1 admits precisions 1 through 38. -/
  valid : 1 ≤ depth ∧ depth ≤ 38
  /-- Smallest native sample. -/
  lo : Int
  /-- Largest native sample. -/
  hi : Int
  /-- The lower endpoint follows G.1. -/
  lo_eq : lo = sampleMin signed depth
  /-- The upper endpoint follows G.1. -/
  hi_eq : hi = sampleMax signed depth

private theorem exactInt64 (r : NativeSampleRange) (v : Int) (hv : r.lo ≤ v ∧ v ≤ r.hi) :
    (Int64.ofInt v).toInt = v := by
  have powBound (k : Nat) (hk : k ≤ 38) : (2 : Int) ^ k ≤ 2 ^ 38 := by
    exact_mod_cast Nat.pow_le_pow_right (by decide : 0 < 2) hk
  have hd := r.valid.2
  have := powBound r.depth hd
  have := powBound (r.depth - 1) (by omega)
  rw [r.lo_eq, r.hi_eq] at hv
  unfold sampleMin sampleMax at hv
  cases hs : r.signed <;> simp only [hs, Bool.false_eq_true, ↓reduceIte] at hv <;>
    apply Int64.toInt_ofInt_of_le <;> omega

private abbrev WordBound (p : Plane) (i : Nat) := 2 * i + 1 < p.width * p.height

@[inline] private def readCell (p : Plane) (i : Nat) (h : WordBound p i) : Int64 :=
  let lo := (p.get (2 * i) (Nat.lt_of_succ_lt h)).toUInt32.toUInt64
  let hi := (p.get (2 * i + 1) h).toUInt32.toUInt64
  (lo + hi * 4294967296).toInt64

@[inline] private def writeCell (p : Plane) (i : Nat) (v : Int64) (h : WordBound p i) : Plane :=
  let u := v.toUInt64
  let p := p.set (2 * i) u.toUInt32.toInt32 (Nat.lt_of_succ_lt h)
  p.set (2 * i + 1) (u >>> 32).toUInt32.toInt32 h

private theorem joinWords (u : UInt64) :
    u.toUInt32.toInt32.toUInt32.toUInt64 +
      (u >>> 32).toUInt32.toInt32.toUInt32.toUInt64 * 4294967296 = u := by
  apply UInt64.toNat_inj.mp
  have := u.toNat_lt
  simp [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  omega

private theorem read_write (p : Plane) (i j : Nat) (v : Int64)
    (hi : WordBound p i) (hj : WordBound (writeCell p i v hi) j) :
    readCell (writeCell p i v hi) j hj = if i = j then v else readCell p j hj := by
  let lo := v.toUInt64.toUInt32.toInt32
  let hiWord := (v.toUInt64 >>> 32).toUInt32.toInt32
  let lowWritten := p.set (2 * i) lo (Nat.lt_of_succ_lt hi)
  have highFrame (k : Nat) (hk : k < p.width * p.height) (hne : 2 * i + 1 ≠ k) :
      (writeCell p i v hi).get k hk = lowWritten.get k hk :=
    Plane.get_set_ne lowWritten _ _ hiWord hi hk hne
  have lowFrame (k : Nat) (hk : k < p.width * p.height) (hne : 2 * i ≠ k) :
      lowWritten.get k hk = p.get k hk :=
    Plane.get_set_ne p _ _ lo _ hk hne
  have hj' : WordBound p j := hj
  by_cases hij : i = j
  · subst j
    have hLo := (highFrame _ (Nat.lt_of_succ_lt hi) (by omega)).trans
      (Plane.get_set_self p (2 * i) lo _ _)
    have hHi : (writeCell p i v hi).get (2 * i + 1) hi = hiWord :=
      Plane.get_set_self lowWritten _ hiWord hi hi
    simp only [readCell, hLo, hHi, lo, hiWord, joinWords, Int64.toInt64_toUInt64, ↓reduceIte]
  · have hLo := (highFrame _ (Nat.lt_of_succ_lt hj') (by omega)).trans
      (lowFrame _ (Nat.lt_of_succ_lt hj') (by omega))
    have hHi := (highFrame _ hj' (by omega)).trans (lowFrame _ hj' (by omega))
    simp only [readCell, hLo, hHi, hij, ite_false]

/-- A row-major native sample plane backed by one byte buffer, with eight bytes per sample. -/
structure WidePlane where
  /-- Width on the component grid. -/
  width : Nat
  /-- Height on the component grid. -/
  height : Nat
  /-- Signedness, precision and sample bounds. -/
  range : NativeSampleRange
  /-- Consecutive low and high 32-bit words of each signed 64-bit cell. -/
  words : Plane
  /-- The buffer contains exactly two words per sample. -/
  words_eq : words.width * words.height = 2 * (width * height)
  /-- Every stored cell lies in the component's native sample interval. -/
  samples_valid : ∀ i (h : WordBound words i),
    range.lo ≤ (readCell words i h).toInt ∧ (readCell words i h).toInt ≤ range.hi

namespace WidePlane

/-- The backing buffer occupies exactly eight bytes per component sample. -/
theorem size_eq (p : WidePlane) : p.words.data.size = 8 * (p.width * p.height) := by
  rw [p.words.size_eq, p.words_eq]; omega

/-- Allocates an all-zero plane after the caller has checked the dimensions and budgets. -/
def zero (width height depth : Nat) (signed : Bool) (hd : 1 ≤ depth ∧ depth ≤ 38) : WidePlane :=
  { width, height, range := ⟨depth, signed, hd, sampleMin signed depth, sampleMax signed depth,
      rfl, rfl⟩
    words := Plane.zero 2 (width * height), words_eq := rfl
    samples_valid := by
      intro i h
      have hz : readCell (Plane.zero 2 (width * height)) i h = 0 := by
        simp only [readCell, Plane.get_zero]; rfl
      rw [hz]
      have : (0 : Int) < 2 ^ depth := Int.pow_pos (by decide)
      have : (0 : Int) < 2 ^ (depth - 1) := Int.pow_pos (by decide)
      cases signed <;> simp [sampleMin, sampleMax] <;> omega }

/-- Checks precision, work samples and decoded output bytes before allocating a zero plane. -/
def zeroChecked (L : Limits) (loc : Location) (width height depth : Nat) (signed : Bool) :
    Except Error WidePlane := do
  if hd : 1 ≤ depth ∧ depth ≤ 38 then
    let cells := width * height
    L.check loc .workSamples cells
    L.check loc .decodedBytes (cells * Header.bytesPerSample depth)
    return zero width height depth signed hd
  else
    throw (.malformed loc "native sample precision outside 1 to 38")

private theorem wordBound (p : WidePlane) (i : Nat) (h : i < p.width * p.height) :
    WordBound p.words i := by unfold WordBound; rw [p.words_eq]; omega

/-- Reads a native sample exactly, sign-extending the stored cell to an integer. -/
@[inline] def get (p : WidePlane) (i : Nat) (h : i < p.width * p.height) : Int :=
  (readCell p.words i (wordBound p i h)).toInt

/-- Reads a component-grid coordinate using the plane's row stride. -/
@[inline] def getXY (p : WidePlane) (x y : Nat) (hx : x < p.width) (hy : y < p.height) : Int :=
  p.get (y * p.width + x) (by
    have := Nat.mul_le_mul_right p.width hy
    rw [Nat.succ_mul] at this; rw [Nat.mul_comm p.width]; omega)

/-- Checked read at a linear sample index. -/
def get? (p : WidePlane) (i : Nat) : Option Int :=
  if h : i < p.width * p.height then some (p.get i h) else none

/-- Stores a native integer with proofs of the index and sample bounds. -/
@[inline] def set (p : WidePlane) (i : Nat) (v : Int) (h : i < p.width * p.height)
    (hv : p.range.lo ≤ v ∧ v ≤ p.range.hi) : WidePlane :=
  { p with words := writeCell p.words i (Int64.ofInt v) (wordBound p i h)
           words_eq := p.words_eq
           samples_valid := by
             intro j hj
             rw [read_write]
             split
             · rw [exactInt64 p.range v hv]; exact hv
             · exact p.samples_valid j hj }

/-- Checked write. Rejects out-of-bounds indices and values before narrowing to 64 bits. -/
def set? (p : WidePlane) (i : Nat) (v : Int) : Option WidePlane :=
  if h : i < p.width * p.height then
    if hv : p.range.lo ≤ v ∧ v ≤ p.range.hi then some (p.set i v h hv) else none
  else none

/-- Every in-bounds read satisfies the component's G.1 interval. -/
theorem get_range (p : WidePlane) (i : Nat) (h : i < p.width * p.height) :
    sampleMin p.range.signed p.range.depth ≤ p.get i h ∧
      p.get i h ≤ sampleMax p.range.signed p.range.depth := by
  rw [← p.range.lo_eq, ← p.range.hi_eq]; exact p.samples_valid i _

/-- Every sample of the new plane reads as zero. -/
theorem get_zero (w h depth : Nat) (signed : Bool) (hd : 1 ≤ depth ∧ depth ≤ 38)
    (i : Nat) (hi : i < w * h) : (zero w h depth signed hd).get i hi = 0 := by
  simp only [get, zero, readCell, Plane.get_zero]; rfl

/-- A write replaces precisely the addressed sample, preserving its exact integer value. -/
theorem get_set (p : WidePlane) (i j : Nat) (v : Int) (hi : i < p.width * p.height)
    (hj : j < p.width * p.height) (hv : p.range.lo ≤ v ∧ v ≤ p.range.hi) :
    (p.set i v hi hv).get j hj = if i = j then v else p.get j hj := by
  unfold get set
  rw [read_write]
  split <;> simp_all only [exactInt64 p.range v hv]

end WidePlane
end JPEG2000.Bytes
