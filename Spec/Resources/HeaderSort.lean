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

end JPEG2000.Spec.Resources.HeaderWork
