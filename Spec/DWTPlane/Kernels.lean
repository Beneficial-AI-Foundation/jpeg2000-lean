import Spec.DWTPlane.Levels

/-!
# The 5/3 and 9/7 kernels satisfy the kernel contract; `gMulti` is the spec / model

Plan.md §4 (C6, C8, C9), §5.2 "DWT"; T.800 Annex F.3.6–F.3.8 (`1D_SR`, F-4 … F-7). Task 7.1d.

* `kspec53 : KSpec lift1d sr1d (fun _ _ _ => True)` from `DWT53.lift1d_eq_sr1d`;
* `kspec97 : KSpec lift1d97 qsr1d Ok1d` from `DWT97.lift1d97_eq`;
* frame lemmas of the in-place passes (cells outside the range are untouched);
* `gMulti_sr1d : gMulti sr1d = Spec.DWT53.srMulti`, `gMulti_qsr1d : gMulti qsr1d = qsrMulti`,
  `gOk_okMulti : gOk qsr1d Ok1d → OkMulti`.
-/

namespace JPEG2000.Spec.DWTPlane

open JPEG2000 JPEG2000.Bytes
open JPEG2000.DWT53 (Buf)
open JPEG2000.Spec.DWT53 (Grid Dec interleave)

/-! ## 5/3 -/

/-- A 5/3 lifting pass leaves the cells outside its range unchanged. -/
theorem liftPass_frame {N : Nat} (upd : Bool) (off n : Nat) (hN : off + n ≤ N) (hn : 2 ≤ n)
    (b : Buf N) (i : Nat) (ok : Bool) (j : Nat) (hj : j < off ∨ off + n ≤ j) :
    rd (DWT53.liftPass upd off n hN hn b i ok).1 j = rd b j := by
  rw [DWT53.liftPass]
  split
  · rename_i hi
    rw [liftPass_frame upd off n hN hn _ (i + 2) _ j hj, rd_set, if_f (by omega)]
  · rfl
termination_by n - i

/-- **The 5/3 kernel contract**: `lift1d` computes `Spec.DWT53.sr1d` (`lift1d_eq_sr1d`). -/
theorem kspec53 : KSpec (fun off n par hN b ok => DWT53.lift1d off n par hN b ok)
    Spec.DWT53.sr1d (fun _ _ _ => True) where
  mono := by
    intro N off n par hN b ok h
    simp only [DWT53.lift1d] at h
    split at h
    · exact DWT53.liftPass_ok _ _ _ _ _ _ _ _ (DWT53.liftPass_ok _ _ _ _ _ _ _ _ h)
    · split at h
      · split at h <;> exact h
      · exact h
  frame := by
    intro N off n par hN b ok j hj
    simp only [DWT53.lift1d]
    split
    · rename_i hn
      rw [liftPass_frame _ _ _ _ _ _ _ _ j hj, liftPass_frame _ _ _ _ _ _ _ _ j hj]
    · split
      · split
        · rw [rd_set, if_f (by omega)]
        · rfl
      · rfl
  val := by
    intro N off n par hN b ok i0 hpar y hy hok
    refine ⟨fun k hk => ?_, trivial⟩
    rw [rd_get _ _ (by omega)]
    exact DWT53.lift1d_eq_sr1d off n par hN b ok i0 hpar y
      (fun k hk => by rw [← rd_get _ _ (by omega)]; exact hy k hk) hok k hk
  triv := fun _ _ _ _ => trivial
  loc := fun i0 i1 y y' h => ⟨fun j h0 h1 => Spec.DWT53.sr1d_local i0 i1 y y' h j h0 h1, fun _ => trivial⟩

/-- `2D_SR` of the spec is `g2d sr1d`. -/
theorem sr2d_eq (r : Spec.DWT53.Rect) (g : Grid) : Spec.DWT53.sr2d r g = g2d Spec.DWT53.sr1d r g := by
  simp only [Spec.DWT53.sr2d, Spec.DWT53.memo_eq]; rfl

/-- **`gMulti sr1d` is `Spec.DWT53.srMulti`.** -/
theorem gMulti_sr1d (n : Nat) : ∀ (r : Spec.DWT53.Rect) (d : Dec),
    gMulti Spec.DWT53.sr1d r n d = Spec.DWT53.srMulti r n d := by
  induction n with
  | zero => intro r d; rfl
  | succ n ih =>
    intro r d
    obtain ⟨ll, det⟩ := d
    cases det with
    | nil => rfl
    | cons b rest =>
      obtain ⟨hl, lh, hh⟩ := b
      simp only [gMulti, Spec.DWT53.srMulti, ih, sr2d_eq]

/-! ## 9/7 -/

/-- A 9/7 lifting pass leaves the cells outside its range unchanged. -/
theorem liftPass97_frame {N : Nat} (cq : Int64) (off n : Nat) (hN : off + n ≤ N) (hn : 2 ≤ n)
    (b : Buf N) (i : Nat) (ok : Bool) (j : Nat) (hj : j < off ∨ off + n ≤ j) :
    rd (DWT97.liftPass97 cq off n hN hn b i ok).1 j = rd b j := by
  rw [DWT97.liftPass97]
  split
  · rw [liftPass97_frame cq off n hN hn _ (i + 2) _ j hj, rd_set, if_f (by omega)]
  · rfl
termination_by n - i

/-- A 9/7 scaling pass leaves the cells outside its range unchanged. -/
theorem scalePass97_frame {N : Nat} (qe qo : Int64) (par off n : Nat) (hN : off + n ≤ N)
    (b : Buf N) (i : Nat) (ok : Bool) (j : Nat) (hj : j < off ∨ off + n ≤ j) :
    rd (DWT97.scalePass97 qe qo par off n hN b i ok).1 j = rd b j := by
  rw [DWT97.scalePass97]
  split
  · rw [scalePass97_frame qe qo par off n hN _ (i + 1) _ j hj, rd_set, if_f (by omega)]
  · rfl
termination_by n - i

/-- The 9/7 lifting pass's flag only goes from `true` to `false`. -/
theorem liftPass97_ok {N : Nat} (cq : Int64) (off n : Nat) (hN : off + n ≤ N) (hn : 2 ≤ n)
    (b : Buf N) (i : Nat) (ok : Bool) (h : (DWT97.liftPass97 cq off n hN hn b i ok).2 = true) :
    ok = true := by
  rw [DWT97.liftPass97] at h
  split at h
  · have := liftPass97_ok cq off n hN hn _ _ _ h
    simp only [Bool.and_eq_true] at this
    exact this.1
  · exact h
termination_by n - i

/-- The 9/7 scaling pass's flag only goes from `true` to `false`. -/
theorem scalePass97_ok {N : Nat} (qe qo : Int64) (par off n : Nat) (hN : off + n ≤ N)
    (b : Buf N) (i : Nat) (ok : Bool) (h : (DWT97.scalePass97 qe qo par off n hN b i ok).2 = true) :
    ok = true := by
  rw [DWT97.scalePass97] at h
  split at h
  · have := scalePass97_ok qe qo par off n hN _ _ _ h
    simp only [Bool.and_eq_true] at this
    exact this.1
  · exact h
termination_by n - i

/-- `qsr1d` and `Ok1d` read their signal only on the range. -/
theorem qsr1d_local (i0 i1 : Int) (y y' : Int → Int) (h : ∀ k, i0 ≤ k → k < i1 → y k = y' k) :
    (∀ j, i0 ≤ j → j < i1 → DWT97.qsr1d i0 i1 y j = DWT97.qsr1d i0 i1 y' j) ∧
    (DWT97.Ok1d i0 i1 y → DWT97.Ok1d i0 i1 y') := by
  have he : i0 + 2 ≤ i1 → DWT97.qext i0 i1 y = DWT97.qext i0 i1 y' := by
    intro hl
    funext k; simp only [DWT97.qext]
    exact h _ (Spec.DWT53.pse_mem hl k).1 (Spec.DWT53.pse_mem hl k).2
  refine ⟨fun j h0 h1 => ?_, fun hok hl => ?_⟩
  · unfold DWT97.qsr1d
    by_cases h2 : i1 = i0 + 1
    · subst h2
      simp only [show ¬ i0 + 1 ≤ i0 by omega, ↓reduceIte, h j h0 h1]
    · simp only [show ¬ i1 ≤ i0 by omega, h2, ↓reduceIte, he (by omega)]
  · rw [← he hl]; exact hok hl

/-- **The 9/7 kernel contract**: `lift1d97` computes the fixed-point model `qsr1d`, with
`Ok1d` (`lift1d97_eq`). -/
theorem kspec97 : KSpec (fun off n par hN b ok => DWT97.lift1d97 off n par hN b ok)
    DWT97.qsr1d DWT97.Ok1d where
  mono := by
    intro N off n par hN b ok h
    simp only [DWT97.lift1d97] at h
    split at h
    · exact scalePass97_ok _ _ _ _ _ _ _ _ _ (liftPass97_ok _ _ _ _ _ _ _ _
        (liftPass97_ok _ _ _ _ _ _ _ _ (liftPass97_ok _ _ _ _ _ _ _ _
          (liftPass97_ok _ _ _ _ _ _ _ _ h))))
    · split at h
      · split at h <;> exact h
      · exact h
  frame := by
    intro N off n par hN b ok j hj
    simp only [DWT97.lift1d97]
    split
    · rw [liftPass97_frame _ _ _ _ _ _ _ _ j hj, liftPass97_frame _ _ _ _ _ _ _ _ j hj,
        liftPass97_frame _ _ _ _ _ _ _ _ j hj, liftPass97_frame _ _ _ _ _ _ _ _ j hj,
        scalePass97_frame _ _ _ _ _ _ _ _ _ j hj]
    · split
      · split
        · rw [rd_set, if_f (by omega)]
        · rfl
      · rfl
  val := by
    intro N off n par hN b ok i0 hpar y hy hok
    obtain ⟨h1, h2⟩ := DWT97.lift1d97_eq off n par hN b ok i0 hpar y
      (fun k hk => by rw [← rd_get _ _ (by omega)]; exact hy k hk) hok
    refine ⟨fun k hk => ?_, h2⟩
    rw [rd_get _ _ (by omega)]
    exact h1 k hk
  triv := fun i0 i1 y h hl => absurd hl (by omega)
  loc := qsr1d_local

/-- `qsr2d` is `g2d qsr1d`. -/
theorem qsr2d_eq (r : Spec.DWT53.Rect) (g : Grid) : DWT97.qsr2d r g = g2d DWT97.qsr1d r g := by
  simp only [DWT97.qsr2d, Spec.DWT53.memo_eq]; rfl

/-- **`gMulti qsr1d` is the fixed-point model `qsrMulti`.** -/
theorem gMulti_qsr1d (n : Nat) : ∀ (r : Spec.DWT53.Rect) (d : Dec),
    gMulti DWT97.qsr1d r n d = DWT97.qsrMulti r n d := by
  induction n with
  | zero => intro r d; rfl
  | succ n ih =>
    intro r d
    obtain ⟨ll, det⟩ := d
    cases det with
    | nil => rfl
    | cons b rest =>
      obtain ⟨hl, lh, hh⟩ := b
      simp only [gMulti, DWT97.qsrMulti, ih, qsr2d_eq]

/-- `gOk qsr1d Ok1d` is the no-overflow hypothesis `OkMulti` of C8. -/
theorem gOk_okMulti (n : Nat) : ∀ (r : Spec.DWT53.Rect) (d : Dec),
    gOk DWT97.qsr1d DWT97.Ok1d r n d → DWT97.OkMulti r n d := by
  induction n with
  | zero => intro r d _; trivial
  | succ n ih =>
    intro r d h
    obtain ⟨ll, det⟩ := d
    cases det with
    | nil => trivial
    | cons b rest =>
      obtain ⟨hl, lh, hh⟩ := b
      obtain ⟨h1, h2⟩ := h
      refine ⟨ih _ _ h1, ?_⟩
      rw [← gMulti_qsr1d]
      exact h2

end JPEG2000.Spec.DWTPlane
