import Spec.NativePlacement.Blit

/-!
# Specification component placement (Plan.md §§4, 5, 7, T.800 B.2–B.3)

The loop visits components in SIZ order. At each step its destination still
contains that component's incoming plane, even after earlier component writes.
-/

namespace JPEG2000.Spec.NativePlacement

open JPEG2000.Spec.Decode

private theorem range_states {α : Type} {f : Nat → α → Except Error (ForInStep α)}
    (state : Nat → α) (n : Nat) (step : ∀ i < n, f i (state i) = .ok (.yield (state (i+1)))) :
    forIn [0:n] (state 0) f = .ok (state n) := by
  have aux (k : Nat) : ∀ i, i + k ≤ n →
      forIn (List.range' i k) (state i) f = .ok (state (i+k)) := by
    induction k with
    | zero => intro i _; rfl
    | succ k ih =>
      intro i hi
      rw [List.range'_succ, List.forIn_cons, step i (by omega)]
      exact (ih (i + 1) (by omega)).trans (by rw [show i + 1 + k = i + (k + 1) by omega])
  simpa [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size] using aux n 0 (by simp)

/-- The actual spec loop returns the pointwise blit results in component order.
The array of witnesses can carry any postcondition established for those blits. -/
theorem place_components (info : Array DecodedComponent) (ps : Array SamplePlane) (tile : TileOut)
    (ni : info.size = tile.comps.size) (np : ps.size = tile.comps.size)
    (result : Fin tile.comps.size → SamplePlane)
    (component : ∀ i : Fin tile.comps.size,
      let r := tile.comps[i.val].1
      let src := tile.comps[i.val].2
      let dc := info[i.val]'(ni.symm ▸ i.isLt)
      dc.x0 ≤ r.x0 ∧ dc.y0 ≤ r.y0 ∧
        blit (ps[i.val]'(np.symm ▸ i.isLt)) src (r.x0 - dc.x0) (r.y0 - dc.y0) = .ok (result i)) :
    place info ps tile = .ok (Array.ofFn result) := by
  let state (k : Nat) := Array.ofFn fun i : Fin tile.comps.size =>
    if i.val < k then result i else ps[i.val]'(np.symm ▸ i.isLt)
  have zero : ps = state 0 := by
    apply Array.ext (by simp [state, np])
    intros; simp [state]
  have last : state tile.comps.size = Array.ofFn result := by
    apply Array.ext (by simp [state])
    intros; simp [state]
  unfold place
  dsimp only
  rw [zero, range_states state tile.comps.size]
  · exact congrArg Except.ok last
  · intro i hi
    obtain ⟨hx, hy, write⟩ := component ⟨i, hi⟩
    have hii : i < info.size := ni.symm ▸ hi
    have hs : i < (state i).size := by simpa [state] using hi
    rw [Array.getElem?_eq_getElem hi, Array.getElem?_eq_getElem hii]
    dsimp only
    change info[i].x0 ≤ tile.comps[i].1.x0 at hx
    change info[i].y0 ≤ tile.comps[i].1.y0 at hy
    rw [ite_eq_right (show ¬(_ ∨ _) from fun h => h.elim (Nat.not_lt.mpr hx) (Nat.not_lt.mpr hy))]
    have dest : (state i).getD i default = ps[i]'(np.symm ▸ hi) := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hs]
      simp [state]
    rw [dest, write]
    suffices (state i).setIfInBounds i (result ⟨i, hi⟩) = state (i+1) by
      exact congrArg (fun a => Except.ok (ForInStep.yield a)) this
    apply Array.ext (by simp [state])
    intro j _ hj
    have hj' : j < (state i).size := by simpa [state] using hj
    rw [Array.getElem_setIfInBounds hj']
    by_cases eq : i = j
    · subst j; simp [state]
    · simp [state, eq, show j < i + 1 ↔ j < i by omega]

end JPEG2000.Spec.NativePlacement
