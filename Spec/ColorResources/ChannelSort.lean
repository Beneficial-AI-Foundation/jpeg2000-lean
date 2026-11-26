module

import all Init.Data.Array.QSort.Basic

/-!
# Comparisons in the JP2 channel-definition sort

Plan.md §§4, 7 (S3), T.800 I.5.3.6. The alpha selector sorts the channel
definitions with the pinned core array quicksort before scanning for opacity.
-/

namespace JPEG2000.Spec.ColorResources

private structure Counted {α : Type} (x : α) (cap : Nat) where
  value : α
  comparisons : Nat
  erase : value = x
  within : comparisons ≤ cap

private def addChecks {α : Type} {x : α} {cap limit : Nat} (n : Nat) (m : Counted x cap)
    (h : n+cap ≤ limit) : Counted x limit :=
  ⟨m.value,n+m.comparisons,m.erase,Nat.le_trans (Nat.add_le_add_left m.within n) h⟩

private def scan {α : Type} {n : Nat} (lt : α → α → Bool) (lo hi : Nat) (hh : hi < n)
    (pivot : α) (a : Vector α n) (i k : Nat) (li : lo ≤ i) (ik : i ≤ k) (kh : k ≤ hi) :
    Counted (Array.qpartition.loop lt lo hi hh pivot a i k li ik kh) (hi-k) := by
  rw [Array.qpartition.loop]
  split
  · split
    · exact addChecks 1 (scan lt lo hi hh pivot _ _ _ _ _ _) (by omega)
    · exact addChecks 1 (scan lt lo hi hh pivot _ _ _ _ _ _) (by omega)
  · exact ⟨_,0,rfl,Nat.zero_le _⟩
termination_by hi-k

private def partition {α : Type} {n : Nat} (lt : α → α → Bool) (a : Vector α n)
    (lo hi : Nat) (lh : lo ≤ hi) (hl : lo < n) (hh : hi < n) :
    Counted (Array.qpartition a lt lo hi lh hl hh) (3+(hi-lo)) := by
  unfold Array.qpartition
  exact addChecks 3 (scan ..) (Nat.le_refl _)

private def sortRun {α : Type} {n : Nat} (lt : α → α → Bool) (a : Vector α n)
    (lo hi : Nat) (lh : lo ≤ hi) (hl : lo < n) (hh : hi < n) : Vector α n × Nat :=
  if h : lo < hi then
    let p := partition lt a lo hi lh hl hh
    let mid := p.value.1.val
    let v := p.value.2
    have bounds := p.value.1.property
    if splitAt : mid < hi then
      have leftLt : mid-lo < hi-lo := by omega
      have rightLt : hi-(mid+1) < hi-lo := by omega
      let left := sortRun lt v lo mid bounds.1 (by omega) (by omega)
      let right := sortRun lt left.1 (mid+1) hi (by omega) (by omega) hh
      (right.1, p.comparisons + left.2 + right.2)
    else (v,p.comparisons)
  else (a,0)
termination_by hi-lo
decreasing_by all_goals first | exact leftLt | exact rightLt

private theorem sort_spec {α : Type} {n : Nat} (lt : α → α → Bool) (a : Vector α n)
    (lo hi : Nat) (lh : lo ≤ hi) (hl : lo < n) (hh : hi < n) :
    let r := sortRun lt a lo hi lh hl hh
    r.1 = Array.qsort.sort lt a lo hi lh hl hh ∧ r.2 ≤ (hi-lo)*(n+3) := by
  rw [sortRun,Array.qsort.sort]
  by_cases small : lo < hi
  · simp only [small, ↓reduceDIte]
    let p := partition lt a lo hi lh hl hh
    let mid := p.value.1.val
    let v := p.value.2
    have lower : lo ≤ mid := p.value.1.property.1
    have upper : mid ≤ hi := p.value.1.property.2
    simp only [← p.erase]
    by_cases splitAt : mid < hi
    · have leftLt : mid-lo < hi-lo := by omega
      have rightLt : hi-(mid+1) < hi-lo := by omega
      have low : ¬ hi ≤ mid := by omega
      obtain ⟨leftEq,lc⟩ := sort_spec lt v lo mid lower hl (by omega)
      obtain ⟨rightEq,rc⟩ := sort_spec lt (sortRun lt v lo mid lower hl (by omega)).1
        (mid+1) hi (by omega) (by omega) hh
      have parts : (mid-lo)+(hi-(mid+1))+1 = hi-lo := by omega
      have budget := congrArg (·*(n+3)) parts
      simp only [Nat.add_mul,Nat.one_mul] at budget
      have pc := p.within
      change (partition lt a lo hi lh hl hh).value.1.val < hi at splitAt
      change ¬ hi ≤ p.value.1.val at low
      simp only [splitAt,low,↓reduceDIte]
      exact ⟨rightEq.trans (by rw [leftEq]),by simp only [mid,p,v] at lc rc pc budget ⊢; omega⟩
    · have large : hi ≤ mid := by omega
      change ¬ (partition lt a lo hi lh hl hh).value.1.val < hi at splitAt
      change hi ≤ p.value.1.val at large
      simp only [splitAt,large,↓reduceDIte]
      refine ⟨rfl,Nat.le_trans p.within ?_⟩
      show 3+(hi-lo) ≤ (hi-lo)*(n+3)
      have := Nat.le_mul_of_pos_left (n+3) (show 0 < hi-lo by omega)
      omega
  · simp [small]
termination_by hi-lo
decreasing_by all_goals first | exact leftLt | exact rightLt

/-- Sort a whole array with the pinned partition and subarray recursion, counting
all three pivot comparisons and every remaining comparator call per partition. -/
public def channelSort {α : Type} (lt : α → α → Bool) (xs : Array α) : Array α × Nat :=
  if h : xs.size = 0 then (xs,0)
  else
    let r := sortRun lt xs.toVector 0 (xs.size-1) (by omega) (by omega) (by omega)
    (r.1.toArray,r.2)

/-- The channel sort gives the same array as the production sort. For `n` channel
definitions it performs at most `(n-1)*(n+3)` comparisons, including equal keys. -/
public theorem channelSort_work {α : Type} (lt : α → α → Bool) (xs : Array α) :
    (channelSort lt xs).1 = xs.qsort lt ∧ (channelSort lt xs).1.size = xs.size ∧
      (channelSort lt xs).2 ≤ (xs.size-1)*(xs.size+3) := by
  simp only [channelSort, Array.qsort]
  split
  · exact ⟨rfl,rfl,Nat.zero_le _⟩
  · rename_i h
    obtain ⟨eq,cap⟩ := sort_spec lt xs.toVector 0 (xs.size-1) (by omega) (by omega) (by omega)
    exact ⟨by simpa using congrArg Vector.toArray eq,Vector.size_toArray _,cap⟩

end JPEG2000.Spec.ColorResources
