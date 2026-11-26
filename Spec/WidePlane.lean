import JPEG2000.WidePlane

/-!
# Checked wide native planes (Plan.md §§4, 5.1, 5.4; T.800 A.5.1 and G.1)

Model a component plane by its observable samples, a function from row-major indices
to optional integers. A write at one valid index replaces that observation and preserves
all others. The checked plane operations implement this model for the full SIZ interval.
-/

namespace JPEG2000.Spec.WidePlane

open Bytes

/-- The integer model of a checked write at one sample index. -/
def write? (w h depth : Nat) (signed : Bool) (samples : Nat → Option Int) (i : Nat) (v : Int) :
    Option (Nat → Option Int) :=
  if i < w * h ∧ MCT.sampleMin signed depth ≤ v ∧ v ≤ MCT.sampleMax signed depth then
    some (fun j => if i = j then some v else samples j)
  else none

/-- Allocation succeeds exactly at legal precision and within both inclusive budgets.
The result is the zero plane of the requested dimensions and format. -/
theorem zeroChecked_spec (L : Limits) (loc : Location) (w h depth : Nat) (signed : Bool)
    (p : Bytes.WidePlane) :
    Bytes.WidePlane.zeroChecked L loc w h depth signed = .ok p ↔
      ∃ hd : 1 ≤ depth ∧ depth ≤ 38, w * h ≤ L.maxWorkSamples ∧
        w * h * Header.bytesPerSample depth ≤ L.maxDecodedBytes ∧
        p = Bytes.WidePlane.zero w h depth signed hd := by
  by_cases hd : 1 ≤ depth ∧ depth ≤ 38
  · by_cases hw : w * h ≤ L.maxWorkSamples <;>
      by_cases hb : w * h * Header.bytesPerSample depth ≤ L.maxDecodedBytes <;>
      simp [Bytes.WidePlane.zeroChecked, hd, Limits.check, Limits.checkLe, Limits.bound, hw, hb,
        bind, Except.bind, pure, Except.pure, eq_comm]
  · simp [Bytes.WidePlane.zeroChecked, hd, throw]

/-- A successfully allocated plane has the requested geometry, format and physical byte size. -/
theorem zeroChecked_layout {L : Limits} {loc : Location} {w h depth : Nat} {signed : Bool}
    {p : Bytes.WidePlane} (hp : Bytes.WidePlane.zeroChecked L loc w h depth signed = .ok p) :
    p.width = w ∧ p.height = h ∧ p.range.depth = depth ∧ p.range.signed = signed ∧
      p.words.data.size = 8 * (w * h) := by
  obtain ⟨hd, _, _, rfl⟩ := (zeroChecked_spec ..).mp hp
  exact ⟨rfl, rfl, rfl, rfl, Bytes.WidePlane.size_eq _⟩

/-- A checked read fails exactly beyond the last row-major sample. -/
theorem get?_eq_none_iff (p : Bytes.WidePlane) (i : Nat) :
    p.get? i = none ↔ p.width * p.height ≤ i := by
  by_cases hi : i < p.width * p.height <;> simp [Bytes.WidePlane.get?, hi] <;> omega

/-- A successful checked write preserves both grid dimensions and the native sample format. -/
theorem set?_layout {p q : Bytes.WidePlane} {i : Nat} {v : Int} (hw : p.set? i v = some q) :
    q.width = p.width ∧ q.height = p.height ∧ q.range = p.range := by
  unfold Bytes.WidePlane.set? at hw
  split at hw
  · split at hw
    · cases hw; exact ⟨rfl, rfl, rfl⟩
    · cases hw
  · cases hw

/-- Checked storage implements the integer write model, including rejection, exact
read-after-write and preservation of every other observation. -/
theorem set?_spec (p : Bytes.WidePlane) (i : Nat) (v : Int) :
    (p.set? i v).map (fun q => q.get?) =
      write? p.width p.height p.range.depth p.range.signed p.get? i v := by
  simp only [write?, ← p.range.lo_eq, ← p.range.hi_eq]
  by_cases hi : i < p.width * p.height
  · by_cases hv : p.range.lo ≤ v ∧ v ≤ p.range.hi
    · simp only [Bytes.WidePlane.set?, hi, hv, ↓reduceDIte, true_and, ↓reduceIte,
        Option.map_some, Option.some.injEq]
      funext j
      by_cases hj : j < p.width * p.height
      · have hj' : j < (p.set i v hi hv).width * (p.set i v hi hv).height := hj
        simp only [Bytes.WidePlane.get?, hj, hj', ↓reduceDIte,
          Bytes.WidePlane.get_set p i j v hi hj hv]
        split <;> rfl
      · have hj' : ¬j < (p.set i v hi hv).width * (p.set i v hi hv).height := hj
        have hij : i ≠ j := by omega
        simp only [Bytes.WidePlane.get?, hj, hj', hij, dite_false, ite_false]
    · simp [Bytes.WidePlane.set?, hi, hv]
  · simp [Bytes.WidePlane.set?, hi]

private def readPair (signed : Bool) (depth : Nat) (a b : Int) : Option (Int × Int) := do
  let p ← (Bytes.WidePlane.zeroChecked Limits.default (.at .decode) 1 2 depth signed).toOption
  let p ← p.set? 0 a
  let p ← p.set? 1 b
  return (← p.get? 0, ← p.get? 1)

-- 38-bit signed endpoints, unsigned DC midpoint and maximum, and values that would
-- wrap into range if narrowed before checking. Precision 1 exercises the opposite endpoint.
example : readPair true 38 (-137438953472) 137438953471 =
    some (-137438953472, 137438953471) := by decide
example : readPair false 38 137438953472 274877906943 =
    some (137438953472, 274877906943) := by decide
example : readPair false 38 0 (2 ^ 64) = none := by decide
example : readPair true 38 (-(2 ^ 64)) 0 = none := by decide
example : readPair true 1 (-1) 0 = some (-1, 0) := by decide
example : readPair false 1 0 1 = some (0, 1) := by decide

end JPEG2000.Spec.WidePlane
