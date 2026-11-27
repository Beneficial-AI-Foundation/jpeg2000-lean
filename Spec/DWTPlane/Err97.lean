import Spec.DWTPlane.Local

/-!
# C8 with band locality: the 9/7 error bounds on the band positions read

Plan.md §4 (C8, C9), §5.4; T.800 Annex F.3 (F-7, Table F.4). Task 7.1d.

`DWT97.qsrMulti_err` assumes the fixed-point inputs within `ε` of the exact ones *everywhere*;
the decoder only knows them on the band positions the transform reads (`Spec.Equiv.BandsClose`).
This file proves the local versions:

* `qsrMulti_err_loc`: the fixed-point model is within `En n ε` of `Spec.DWT97.srMulti` when the
  inputs are within `ε` on the read positions (`DecCloseR`) and no pass overflows;
* `srMulti_lip`: the exact transform moves by at most `En n ε` when its inputs move by at most
  `ε` on the read positions (the slow path rounds the exact transform of the fixed-point
  inputs), from the 1-D bound `sr1d_lip` (linearity of the lifting chain, `chain_bound`, and
  `E1 ε ≥ B1 ε ≥` the propagated part).
-/

namespace JPEG2000.Spec.DWTPlane

open JPEG2000
open JPEG2000.Spec.DWT97 (Sig chain invSteps ext add smul pb gb gb_mod chain_bound chain_add
  chain_smul abs_le_iff abs_add_le injBound wsum)
open JPEG2000.DWT97 (E1 B1 En rmax ηInv qη M32)

/-! ## Small facts about the bounds -/

/-- `a ≤ rmax a b`. -/
theorem rmax_l (a b : Rat) : a ≤ rmax a b := by unfold rmax; split <;> grind
/-- `b ≤ rmax a b`. -/
theorem rmax_r (a b : Rat) : b ≤ rmax a b := by unfold rmax; split <;> grind

/-- `ε + 1/2 ≤ E1 ε`. -/
theorem le_E1' (ε : Rat) : ε + 1 / 2 ≤ E1 ε := rmax_r _ _

/-- `B1` at a parity is at most `E1`. -/
theorem B1_le_E1' (j : Int) (ε : Rat) : B1 (j % 2) ε ≤ E1 ε := by
  unfold E1
  have h1 := rmax_l (rmax (B1 0 ε) (B1 1 ε)) (ε + 1 / 2)
  rcases (by omega : j % 2 = 0 ∨ j % 2 = 1) with h | h <;> rw [h]
  · exact Rat.le_trans (rmax_l _ _) h1
  · exact Rat.le_trans (rmax_r _ _) h1

/-- `ε ≤ En n ε`. -/
theorem le_En' (n : Nat) (ε : Rat) : ε ≤ En n ε := by
  cases n with
  | zero => exact Rat.le_refl
  | succ n =>
    simp only [En]
    have a := le_E1' (rmax (En n ε) ε)
    have b := le_E1' (E1 (rmax (En n ε) ε))
    have c := rmax_r (En n ε) ε
    grind

/-- Window sums of non-negative terms are non-negative. -/
theorem wsum_nonneg (h : Int → Rat) (a : Int) (H : ∀ k, 0 ≤ h k) : ∀ n, 0 ≤ wsum h a n := by
  intro n
  induction n with
  | zero => exact Rat.le_refl
  | succ n ih => simp only [wsum]; have := H (a + n); grind

/-- `gb` with a non-negative bound is non-negative. -/
theorem gb_nonneg (l : List Spec.DWT97.Step) (j : Int) (bnd : Int → Rat) (H : ∀ k, 0 ≤ bnd k) :
    0 ≤ gb l j bnd := by
  unfold gb
  apply wsum_nonneg
  intro k
  exact Rat.mul_nonneg (H k) Rat.abs_nonneg

/-- `injBound` with non-negative bounds is non-negative. -/
theorem injBound_nonneg (l : List Spec.DWT97.Step) : ∀ (ηs : List (Int → Rat)) (j : Int),
    (∀ η ∈ ηs, ∀ k, 0 ≤ η k) → 0 ≤ injBound l ηs j := by
  induction l with
  | nil => intro ηs j _; cases ηs <;> exact Rat.le_refl
  | cons s l ih =>
    intro ηs j H
    cases ηs with
    | nil => exact Rat.le_refl
    | cons η ηs =>
      simp only [injBound]
      have a := gb_nonneg l j η (H η List.mem_cons_self)
      have b := ih ηs j (fun η' h => H η' (List.mem_cons_of_mem _ h))
      grind

/-- The per-step residual bounds are non-negative. -/
theorem qη_nonneg (s : DWT97.QStep) : 0 ≤ (qη s M32).1 ∧ 0 ≤ (qη s M32).2 := by
  have hM : (0 : Rat) ≤ M32 := by unfold M32; decide
  cases s with
  | lifting p c cq =>
    have := Rat.mul_nonneg (Rat.abs_nonneg (x := (cq : Rat) / 1073741824 - c))
      (show (0 : Rat) ≤ 2 * M32 by grind)
    simp only [qη]
    split <;> constructor <;> grind
  | scaling ce co qe qo =>
    have h1 := Rat.mul_nonneg (Rat.abs_nonneg (x := (qe : Rat) / 1073741824 - ce)) hM
    have h2 := Rat.mul_nonneg (Rat.abs_nonneg (x := (qo : Rat) / 1073741824 - co)) hM
    simp only [qη]
    constructor <;> grind

/-- The injected-error bound of the inverse 9/7 is non-negative. -/
theorem injInv_nonneg (j : Int) : 0 ≤ injBound invSteps (ηInv.map fun e => pb e.1 e.2) j := by
  apply injBound_nonneg
  intro η hη k
  simp only [List.mem_map] at hη
  obtain ⟨e, he, rfl⟩ := hη
  simp only [ηInv, List.mem_map] at he
  obtain ⟨s, -, rfl⟩ := he
  obtain ⟨a, b⟩ := qη_nonneg s
  simp only [pb]; split <;> assumption

/-! ## The exact transform is `E1`-Lipschitz per pass -/

/-- **1-D**: inputs within `ε` on the range give `1D_SR` outputs within `E1 ε`. -/
theorem sr1d_lip (i0 i1 : Int) (x x' : Sig) (ε : Rat)
    (hx : ∀ k, i0 ≤ k → k < i1 → (x k - x' k).abs ≤ ε) (j : Int) (h0 : i0 ≤ j) (h1 : j < i1) :
    (Spec.DWT97.sr1d i0 i1 x j - Spec.DWT97.sr1d i0 i1 x' j).abs ≤ E1 ε := by
  have hE := le_E1' ε
  have hnn : 0 ≤ ε := Rat.le_trans Rat.abs_nonneg (hx j h0 h1)
  unfold Spec.DWT97.sr1d
  by_cases h2 : i1 = i0 + 1
  · subst h2
    have hj : j = i0 := by omega
    subst hj
    have hxe := abs_le_iff.mp (hx j h0 h1)
    simp only [show ¬ j + 1 ≤ j by omega, ↓reduceIte]
    apply abs_le_iff.mpr
    by_cases hp : j % 2 = 0
    · simp only [hp, ↓reduceIte]; constructor <;> grind
    · simp only [hp, ↓reduceIte]; constructor <;> grind
  · have hl : i0 + 2 ≤ i1 := by omega
    simp only [show ¬ i1 ≤ i0 by omega, h2, ↓reduceIte]
    have hlin : chain invSteps (ext i0 i1 x) j - chain invSteps (ext i0 i1 x') j
        = chain invSteps (add (ext i0 i1 x) (smul (-1) (ext i0 i1 x'))) j := by
      rw [chain_add, chain_smul]; simp only [add, smul]; grind
    rw [hlin]
    have hb := chain_bound invSteps (add (ext i0 i1 x) (smul (-1) (ext i0 i1 x'))) j (pb ε ε) (by
      intro k
      have := hx _ (Spec.DWT53.pse_mem hl k).1 (Spec.DWT53.pse_mem hl k).2
      have e : add (ext i0 i1 x) (smul (-1) (ext i0 i1 x')) k
          = x (Spec.DWT53.pse i0 i1 k) - x' (Spec.DWT53.pse i0 i1 k) := by
        simp only [add, smul, ext]; grind
      rw [e]; simp only [pb]; split <;> exact this)
    rw [gb_mod] at hb
    have hB := B1_le_E1' j ε
    have hI := injInv_nonneg (j % 2)
    unfold B1 at hB
    generalize (chain invSteps (add (ext i0 i1 x) (smul (-1) (ext i0 i1 x'))) j).abs = a at hb ⊢
    generalize gb invSteps (j % 2) (pb ε ε) = g at hb hB
    generalize injBound invSteps (List.map (fun e => pb e.1 e.2) ηInv) (j % 2) = i at hB hI
    grind

open JPEG2000.Spec.DWT53 (Rect)

/-- **2-D, one level**: inputs within `ε` on the rectangle give `2D_SR` outputs within
`E1 (E1 ε)`. -/
theorem sr2d_lip (r : Rect) (g g' : Spec.DWT97.Grid) (ε : Rat)
    (hx : ∀ u v, r.mem u v → (g.get u v - g'.get u v).abs ≤ ε) (u v : Int) (h : r.mem u v) :
    ((Spec.DWT97.sr2d r g).get u v - (Spec.DWT97.sr2d r g').get u v).abs ≤ E1 (E1 ε) := by
  simp only [Spec.DWT97.sr2d, Spec.DWT97.memo_eq, Spec.DWT97.verSR]
  obtain ⟨h0, h1, h2, h3⟩ := h
  apply sr1d_lip _ _ _ _ _ _ v h2 h3
  intro k hk0 hk1
  simp only [Spec.DWT97.horSR]
  apply sr1d_lip _ _ _ _ _ _ u h0 h1
  intro m hm0 hm1
  exact hx m k ⟨hm0, hm1, hk0, hk1⟩

/-! ## Closeness on the read band positions -/

/-- Two rational decompositions within `ε` on every band position an `n`-level inverse
transform to `r` reads (the positions of `DecAgree`). -/
def DecCloseR (ε : Rat) (r : Rect) (n : Nat) (d1 d2 : Spec.DWT97.Dec) : Prop :=
  (∀ u v, (rhalf r n).mem u v → (d1.ll.get u v - d2.ll.get u v).abs ≤ ε) ∧
  ∀ i b1 b2, i < n → d1.details[i]? = some b1 → d2.details[i]? = some b2 →
    (∀ u v, Hx (rhalf r i) u → Ly (rhalf r i) v → (b1.1.get u v - b2.1.get u v).abs ≤ ε) ∧
    (∀ u v, Lx (rhalf r i) u → Hy (rhalf r i) v → (b1.2.1.get u v - b2.2.1.get u v).abs ≤ ε) ∧
    (∀ u v, Hx (rhalf r i) u → Hy (rhalf r i) v → (b1.2.2.get u v - b2.2.2.get u v).abs ≤ ε)

/-- **The exact multi-level transform on locally close inputs** (`En n ε`). -/
theorem srMulti_lip (n : Nat) : ∀ (r : Rect) (d1 d2 : Spec.DWT97.Dec) (ε : Rat),
    d1.details.length = n → d2.details.length = n → DecCloseR ε r n d1 d2 → ∀ u v, r.mem u v →
    ((Spec.DWT97.srMulti r n d1).get u v - (Spec.DWT97.srMulti r n d2).get u v).abs ≤ En n ε := by
  induction n with
  | zero => intro r d1 d2 ε _ _ h u v hm; exact h.1 u v hm
  | succ n ih =>
    intro r d1 d2 ε l1 l2 h u v hm
    obtain ⟨ll1, det1⟩ := d1
    obtain ⟨ll2, det2⟩ := d2
    cases det1 with
    | nil => simp at l1
    | cons e1 t1 =>
    cases det2 with
    | nil => simp at l2
    | cons e2 t2 =>
    obtain ⟨hl1, lh1, hh1⟩ := e1
    obtain ⟨hl2, lh2, hh2⟩ := e2
    obtain ⟨hll, hdet⟩ := h
    simp only [Spec.DWT97.srMulti, En]
    obtain ⟨a1, a2, a3⟩ := hdet 0 _ _ (by omega) rfl rfl
    have hrec : DecCloseR ε r.half n ⟨ll1, t1⟩ ⟨ll2, t2⟩ :=
      ⟨hll, fun i b1 b2 hi h1 h2 => hdet (i + 1) b1 b2 (by omega) h1 h2⟩
    apply sr2d_lip _ _ _ _ _ u v hm
    intro u' v' ⟨h0, h1, h2, h3⟩
    have m1 := rmax_l (En n ε) ε
    have m2 := rmax_r (En n ε) ε
    simp only [Spec.DWT97.interleave]
    by_cases hu : u' % 2 = 0 <;> by_cases hv : v' % 2 = 0 <;> simp only [hu, hv, ↓reduceIte]
    · exact Rat.le_trans (ih r.half _ _ ε (by simpa using l1) (by simpa using l2) hrec _ _
        (by simp only [Spec.DWT53.Rect.half, Spec.DWT53.Rect.mem]; omega)) m1
    · exact Rat.le_trans (a2 _ _ (by simp only [Lx, rhalf]; omega) (by simp only [Hy, rhalf]; omega)) m2
    · exact Rat.le_trans (a1 _ _ (by simp only [Hx, rhalf]; omega) (by simp only [Ly, rhalf]; omega)) m2
    · exact Rat.le_trans (a3 _ _ (by simp only [Hx, rhalf]; omega) (by simp only [Hy, rhalf]; omega)) m2

/-- **C8 with band locality**: the fixed-point model on inputs within `ε` of the exact ones on
the read positions, without overflow, is within `En n ε` of `Spec.DWT97.srMulti`. -/
theorem qsrMulti_err_loc (n : Nat) : ∀ (r : Rect) (dq : Spec.DWT53.Dec) (dx : Spec.DWT97.Dec)
    (ε : Rat), dq.details.length = n → dx.details.length = n →
    DecCloseR ε r n (DWT97.castDec dq) dx → DWT97.OkMulti r n dq → ∀ u v, r.mem u v →
    ((((DWT97.qsrMulti r n dq).get u v : Int) : Rat) - (Spec.DWT97.srMulti r n dx).get u v).abs
      ≤ En n ε := by
  induction n with
  | zero => intro r dq dx ε _ _ h _ u v hm; exact h.1 u v hm
  | succ n ih =>
    intro r dq dx ε l1 l2 h hok u v hm
    obtain ⟨llq, detq⟩ := dq
    obtain ⟨llx, detx⟩ := dx
    cases detq with
    | nil => simp at l1
    | cons e1 t1 =>
    cases detx with
    | nil => simp at l2
    | cons e2 t2 =>
    obtain ⟨hlq, lhq, hhq⟩ := e1
    obtain ⟨hlx, lhx, hhx⟩ := e2
    obtain ⟨hll, hdet⟩ := h
    obtain ⟨hok1, hok2⟩ := hok
    simp only [DWT97.qsrMulti, Spec.DWT97.srMulti, En]
    obtain ⟨a1, a2, a3⟩ := hdet 0 _ _ (by omega) rfl rfl
    have hrec : DecCloseR ε r.half n (DWT97.castDec ⟨llq, t1⟩) ⟨llx, t2⟩ :=
      ⟨hll, fun i b1 b2 hi h1 h2 => hdet (i + 1) b1 b2 (by omega) (by simpa [DWT97.castDec] using h1) h2⟩
    apply DWT97.qsr2d_err _ _ _ _ _ hok2 u v hm
    intro u' v' ⟨h0, h1, h2, h3⟩
    have m1 := rmax_l (En n ε) ε
    have m2 := rmax_r (En n ε) ε
    simp only [Spec.DWT53.interleave, Spec.DWT97.interleave]
    by_cases hu : u' % 2 = 0 <;> by_cases hv : v' % 2 = 0 <;> simp only [hu, hv, ↓reduceIte]
    · exact Rat.le_trans (ih r.half _ _ ε (by simpa using l1) (by simpa using l2) hrec hok1 _ _
        (by simp only [Spec.DWT53.Rect.half, Spec.DWT53.Rect.mem]; omega)) m1
    · exact Rat.le_trans (a2 _ _ (by simp only [Lx, rhalf]; omega) (by simp only [Hy, rhalf]; omega)) m2
    · exact Rat.le_trans (a1 _ _ (by simp only [Hx, rhalf]; omega) (by simp only [Ly, rhalf]; omega)) m2
    · exact Rat.le_trans (a3 _ _ (by simp only [Hx, rhalf]; omega) (by simp only [Hy, rhalf]; omega)) m2

end JPEG2000.Spec.DWTPlane
