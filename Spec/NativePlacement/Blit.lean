import Spec.NativeSample

/-!
# Rectangular specification blits (Plan.md §§4, 5, 7, T.800 B.2 and B.3)

Rows use the source stride for reads and the destination stride for writes.
The translated rectangle may be empty on either axis.
-/

namespace JPEG2000.Spec.NativePlacement

open JPEG2000.Spec.Decode

private theorem row_reads (s : SamplePlane) (k si di : Nat) (a : Array SpecSample)
    (hs : si + k ≤ s.samples.size) (hd : di + k ≤ a.size) :
    (blitRow s k si di a).size = a.size ∧ ∀ j, (blitRow s k si di a)[j]? =
      if di ≤ j ∧ j < di + k then s.samples[si + (j - di)]? else a[j]? := by
  induction k generalizing si di a with
  | zero => simp [blitRow]; omega
  | succ k ih =>
    have hsi : si < s.samples.size := by omega
    have hdi : di < a.size := by omega
    simp only [blitRow, Array.getElem?_eq_getElem hsi]
    obtain ⟨sz, read⟩ := ih (si + 1) (di + 1) (a.setIfInBounds di s.samples[si])
      (by omega) (by simp; omega)
    refine ⟨sz.trans (by simp), fun j => ?_⟩
    rw [read, Array.getElem?_setIfInBounds]
    by_cases eq : di = j
    · subst j
      simp [hdi, hsi, show ¬di + 1 ≤ di by omega]
    · simp only [eq, ite_false]
      split
      · rename_i inside
        rw [ite_eq_left (by omega), show si + 1 + (j - (di + 1)) = si + (j - di) by omega]
      · rw [ite_eq_right (by omega)]

private theorem rows_reads (s : SamplePlane) (dw dh ox oy k start : Nat) (a : Array SpecSample)
    (hs : s.samples.size = s.width * s.height) (hd : a.size = dw * dh)
    (hx : ox + s.width ≤ dw) (hy : oy + s.height ≤ dh) (hk : start + k ≤ s.height) :
    (blitRows s dw ox oy k start a).size = a.size ∧
    ∀ x y, x < dw → (blitRows s dw ox oy k start a)[y * dw + x]? =
      if oy + start ≤ y ∧ y < oy + start + k ∧ ox ≤ x ∧ x < ox + s.width
      then s.samples[(y - oy) * s.width + (x - ox)]? else a[y * dw + x]? := by
  induction k generalizing start a with
  | zero => simp [blitRows]; omega
  | succ k ih =>
    let base := (oy + start) * dw + ox
    let next := blitRow s s.width (start * s.width) base a
    have sb := Nat.mul_le_mul_right s.width (show start + 1 ≤ s.height by omega)
    have db := Nat.mul_le_mul_right dw (show oy + start + 1 ≤ dh by omega)
    rw [Nat.succ_mul, Nat.mul_comm s.height] at sb
    rw [Nat.succ_mul, Nat.mul_comm dh] at db
    obtain ⟨sz, row⟩ := row_reads s s.width (start * s.width) base a
      (by omega) (by dsimp [base]; omega)
    obtain ⟨sz', read⟩ := ih (start + 1) next (sz.trans hd) (by omega)
    refine ⟨sz'.trans sz, fun x y col => ?_⟩
    change (blitRows s dw ox oy k (start + 1) next)[y * dw + x]? = _
    rw [read x y col, show next[y * dw + x]? = _ from row _]
    by_cases eq : y = oy + start
    · subst y
      simp only [show ¬oy + (start + 1) ≤ oy + start by omega, false_and, ↓reduceIte,
        Nat.le_refl, true_and, show oy+start < oy+start+(k+1) by omega,
        show oy + start - oy = start by omega]
      dsimp only [base]
      split <;> split <;> first | rfl | congr 2 <;> omega | omega
    · have miss : ¬(base ≤ y * dw + x ∧ y * dw + x < base + s.width) := by
        dsimp [base]
        rcases Nat.lt_or_gt_of_ne eq with lt | gt
        · have := Nat.mul_le_mul_right dw lt; rw [Nat.succ_mul] at this; omega
        · have := Nat.mul_le_mul_right dw gt; rw [Nat.succ_mul] at this; omega
      rw [ite_eq_right miss]
      congr 1
      apply propext
      omega

/-- A specification blit copies every local sample to its translated destination
coordinate and preserves every other lookup. It keeps both dimensions and the
complete length of the destination, including when either rectangle is empty. -/
theorem blit_reads (d s : SamplePlane) (ox oy : Nat)
    (hs : s.samples.size = s.width * s.height) (hd : d.samples.size = d.width * d.height)
    (hx : ox + s.width ≤ d.width) (hy : oy + s.height ≤ d.height) :
    ∃ p, blit d s ox oy = .ok p ∧ p.width = d.width ∧ p.height = d.height ∧
      p.samples.size = d.samples.size ∧
      (∀ x y, x < s.width → y < s.height →
        p.samples[(oy + y) * d.width + (ox + x)]? = s.samples[y * s.width + x]?) ∧
      (∀ x y, x < d.width → ¬WideOutput.Inside s.width s.height ox oy x y →
        p.samples[y * d.width + x]? = d.samples[y * d.width + x]?) := by
  obtain ⟨sz, rd⟩ := rows_reads s d.width d.height ox oy s.height 0 d.samples hs hd hx hy (by omega)
  refine ⟨_, ite_eq_left ⟨hx, hy⟩, rfl, rfl, sz, fun x y xlt ylt => ?_, fun x y xlt miss => ?_⟩
  · simpa [xlt, ylt] using rd (ox + x) (oy + y) (by omega)
  · have h := rd x y xlt
    simp only [Nat.add_zero] at h
    rwa [ite_eq_right (by unfold WideOutput.Inside at miss; omega)] at h

end JPEG2000.Spec.NativePlacement
