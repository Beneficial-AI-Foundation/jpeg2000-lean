module

import all Init.Data.List.Sort.Impl
public import Init

/-!
# Sorting the precinct position table

Plan.md §§3–5, 7 (S3), T.800 B.12.1.3–5. The pinned Lean compiler uses
mergeSortTR₂ and its two mutually recursive sort directions.
-/

namespace JPEG2000.Spec.Resources.PacketSortWork

open List.MergeSort.Internal

private def mergeRun {α : Type} (le : α → α → Bool) : List α → List α → List α → List α × Nat
  | [], ys, acc => (acc.reverseAux ys, acc.length)
  | x::xs, [], acc => (acc.reverseAux (x::xs), acc.length)
  | x::xs, y::ys, acc =>
    let tail := if le x y then mergeRun le xs (y::ys) (x::acc) else mergeRun le (x::xs) ys (y::acc)
    (tail.1, 1 + tail.2)
termination_by xs ys _ => xs.length + ys.length

private theorem merge_spec {α : Type} (le : α → α → Bool) (x y acc : List α) :
    (mergeRun le x y acc).1 = mergeTR.go le x y acc ∧
      (mergeRun le x y acc).2 ≤ 2*(x.length+y.length)+acc.length := by
  induction x generalizing y acc with
  | nil => simp [mergeRun,mergeTR.go]
  | cons x xs ih =>
    induction y generalizing acc with
    | nil => simp [mergeRun,mergeTR.go]
    | cons y ys ih' =>
      simp only [mergeRun,mergeTR.go]
      split
      · obtain ⟨er,h⟩ := ih (y::ys) (x::acc)
        exact ⟨er,by simp only [List.length_cons] at *; omega⟩
      · obtain ⟨er,h⟩ := ih' (y::acc)
        exact ⟨er,by simp only [List.length_cons] at *; omega⟩

private structure SortRun {α : Type} (out : List α) (n : Nat) where
  result : List α
  erase : result = out
  size : result.length = n
  work : Nat
  bound : work ≤ 8*(n*n)+1

private def sortRef {α : Type} (le : α → α → Bool) (rev : Bool) {n : Nat} (xs : { l : List α // l.length = n }) :=
  if rev then mergeSortTR₂.run' le xs else mergeSortTR₂.run le xs

private theorem split_cost {a b n : Nat} (ha : 1 ≤ a) (hb : 1 ≤ b) (eq : n = a+b) :
    n + (8*(a*a)+1) + (8*(b*b)+1) + 2*n + 1 ≤ 8*(n*n)+1 := by
  subst n
  have h1 := Nat.mul_le_mul_left a hb
  have h2 := Nat.mul_le_mul_right b ha
  simp only [Nat.one_mul,Nat.mul_one] at *
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_comm b a]
  omega

private def mergeResults {α : Type} (le : α → α → Bool) {a b n : Nat} {x y : List α}
    (l : SortRun x a) (r : SortRun y b) (ha : 1 ≤ a) (hb : 1 ≤ b) (eq : n = a+b)
    (splitAt : Nat) (hs : splitAt ≤ n) : SortRun (mergeTR x y le) n :=
  let m := mergeRun le l.result r.result []
  have er : m.1 = mergeTR l.result r.result le := (merge_spec le l.result r.result []).1
  ⟨m.1, by rw [er,l.erase,r.erase],
    by rw [er,← merge_eq_mergeTR,List.length_merge,l.size,r.size,eq],
    1 + splitAt + l.work + r.work + m.2, by
      have h : m.2 ≤ 2*(l.result.length+r.result.length)+0 := (merge_spec le l.result r.result []).2
      rw [l.size,r.size,← eq] at h
      have := l.bound
      have := r.bound
      have := split_cost ha hb eq
      omega⟩

private def sortRun {α : Type} (le : α → α → Bool) (rev : Bool) :
    {n : Nat} → (xs : {l : List α // l.length = n}) → SortRun (sortRef le rev xs) n
  | 0, ⟨[],_⟩ => ⟨[],by cases rev <;> simp [sortRef,mergeSortTR₂.run,mergeSortTR₂.run'],rfl,1,by decide⟩
  | 1, ⟨[x],_⟩ => ⟨[x],by cases rev <;> simp [sortRef,mergeSortTR₂.run,mergeSortTR₂.run'],rfl,1,by decide⟩
  | n+2, xs => by
    cases rev
    · let p := splitRevInTwo xs
      let l := sortRun le true p.1
      let r := sortRun le false p.2
      simp only [sortRef,Bool.false_eq_true,↓reduceIte,mergeSortTR₂.run]
      exact mergeResults le l r (by omega) (by omega) (by omega) ((n+2+1)/2) (by omega)
    · let p := splitRevInTwo' xs
      let l := sortRun le true p.2
      let r := sortRun le false p.1
      simp only [sortRef,↓reduceIte,mergeSortTR₂.run']
      exact mergeResults le l r (by omega) (by omega) (by omega) ((n+2)/2) (by omega)
termination_by n _ => n


/-- Run the pinned sorter, counting key comparisons, reversal cells, split visits and calls. -/
public def measured {α : Type} (le : α → α → Bool) (xs : List α) : List α × Nat :=
  let s := sortRun le false ⟨xs,rfl⟩
  (s.result,s.work)

/-- Erasing the counter gives the sorted list. The quadratic price covers both
sort directions of the runtime implementation and the initial length scan. -/
public theorem sort_work {α : Type} (le : α → α → Bool) (xs : List α) :
    (measured le xs).1 = xs.mergeSort le ∧ xs.length + (measured le xs).2 ≤ xs.length + 8*(xs.length*xs.length)+1 := by
  rw [mergeSort_eq_mergeSortTR₂]
  exact ⟨(sortRun le false ⟨xs,rfl⟩).erase,by have := (sortRun le false ⟨xs,rfl⟩).bound; change xs.length + (sortRun le false ⟨xs,rfl⟩).work ≤ _; omega⟩

end JPEG2000.Spec.Resources.PacketSortWork
