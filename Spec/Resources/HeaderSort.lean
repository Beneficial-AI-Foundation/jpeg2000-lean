module

public import Init.Data.Array.Perm
import all Init.Data.Array.InsertionSort

/-!
# Pointer marker sorting (Plan.md §4 S3, §7 M7; T.800 A.7)

The decoder sorts pointer segments with the pinned core array insertion sort.
-/

namespace JPEG2000.Spec.Resources.HeaderWork

/-- Sorting by the byte index in TLM/PPM/PPT/PLT preserves every element and its multiplicity. -/
public theorem insertionSort_perm {α : Type} (lt : α → α → Bool) (xs : Array α) :
    (xs.insertionSort lt).Perm xs := by
  have swapLoop (a : Array α) (j : Nat) (hj : j < a.size) :
      (Array.insertionSort.swapLoop lt a j hj).Perm a := by
    induction j generalizing a with
    | zero => exact Array.Perm.refl _
    | succ j ih =>
      rw [Array.insertionSort.swapLoop]
      split
      · exact (ih _ _).trans (Array.swap_perm ..)
      · exact Array.Perm.refl _
  have traverse (a : Array α) (i n : Nat) : (Array.insertionSort.traverse lt a i n).Perm a := by
    induction n generalizing a i with
    | zero => exact Array.Perm.refl _
    | succ n ih =>
      rw [Array.insertionSort.traverse]
      split
      · exact (ih _ _).trans (swapLoop ..)
      · exact Array.Perm.refl _
  exact traverse ..

private def measuredSwap {α : Type} (lt : α → α → Bool) (xs : Array α) :
    (j : Nat) → j < xs.size → Array α × Nat
  | 0, _ => (xs, 0)
  | j+1, h =>
    if lt xs[j+1] xs[j] then
      let r := measuredSwap lt (xs.swap (j+1) j) j (by simp; omega)
      (r.1, r.2+1)
    else (xs, 1)

private theorem swap_checks {α : Type} (lt : α → α → Bool) (xs : Array α) (j : Nat)
    (h : j < xs.size) :
    let m := measuredSwap lt xs j h
    m.1 = Array.insertionSort.swapLoop lt xs j h ∧ m.1.size = xs.size ∧ m.2 ≤ j := by
  induction j generalizing xs with
  | zero => simp [measuredSwap, Array.insertionSort.swapLoop]
  | succ j ih =>
    simp only [measuredSwap, Array.insertionSort.swapLoop]
    split
    · obtain ⟨erase, size, bound⟩ := ih (xs.swap (j+1) j) (by simp; omega)
      exact ⟨erase, by simpa using size, Nat.succ_le_succ bound⟩
    · exact ⟨rfl, rfl, by omega⟩

private def measuredTraverse {α : Type} (lt : α → α → Bool) (xs : Array α) (i : Nat) :
    Nat → Array α × Nat
  | 0 => (xs, 0)
  | fuel+1 =>
    if h : i < xs.size then
      let row := measuredSwap lt xs i h
      let rest := measuredTraverse lt row.1 (i+1) fuel
      (rest.1, row.2 + rest.2)
    else (xs, 0)

private theorem traverse_checks {α : Type} (lt : α → α → Bool) (xs : Array α) (i fuel : Nat) :
    let m := measuredTraverse lt xs i fuel
    m.1 = Array.insertionSort.traverse lt xs i fuel ∧ m.2 ≤ fuel * xs.size := by
  induction fuel generalizing xs i with
  | zero => simp [measuredTraverse, Array.insertionSort.traverse]
  | succ n ih =>
    simp only [measuredTraverse, Array.insertionSort.traverse]
    split
    · rename_i h
      obtain ⟨row, size, checks⟩ := swap_checks lt xs i h
      obtain ⟨restore, limit⟩ := ih (measuredSwap lt xs i h).1 (i+1)
      rw [size] at limit
      exact ⟨restore.trans (by rw [row]), by rw [Nat.succ_mul]; omega⟩
    · exact ⟨rfl, Nat.zero_le _⟩

/-- The pinned insertion sort paired with its number of comparator invocations. -/
public def measuredSort {α : Type} (lt : α → α → Bool) (xs : Array α) : Array α × Nat :=
  measuredTraverse lt xs 0 xs.size

/-- Sorting preserves the complete output and performs at most the square of the
input length in key comparisons, including inputs with repeated keys. -/
public theorem measuredSort_work {α : Type} (lt : α → α → Bool) (xs : Array α) :
    (measuredSort lt xs).1 = xs.insertionSort lt ∧
      (measuredSort lt xs).2 ≤ xs.size * xs.size :=
  traverse_checks lt xs 0 xs.size

end JPEG2000.Spec.Resources.HeaderWork
