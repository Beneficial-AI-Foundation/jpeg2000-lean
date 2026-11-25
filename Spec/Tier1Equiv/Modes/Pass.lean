import Spec.Tier1Equiv.Modes.Steps

/-!
# C3 (all code-block styles), part 4: stripe columns, scan, whole passes

Plan.md §4 (C3), §5.2 "Tier-1 / EBCOT"; T.800 D.1 (scan order), D.3.1–D.3.4, D.6 (raw
passes). Task 7.1c.

* `colRows_relG`, `scanBlock_relG` — the fast column and stripe loops simulate the spec folds
  for *any* relation preserved by the step (the plain lemmas of task 3.6, generalised).
* `skipCol_rel` — a column with a zero-column skip test (`spSkip`, `mrSkip`) whose spec steps
  are all no-ops when the test holds.
* One stripe column of each mode-aware pass (`spColM_rel`, `mrCol_relM`, `cuColM_rel`,
  `rawSpCol_rel`, `rawMrCol_rel`) and the whole passes (`sigPropPassM_rel`,
  `magRefPass_relM`, `cleanupPassM_rel` with `clearVis_relM`, `rawSigPropPass_rel`,
  `rawMagRefPass_rel`).
-/

namespace JPEG2000.Spec.Tier1EquivM

open JPEG2000
open JPEG2000.Tier2.Geometry (Band)
open JPEG2000.Spec.Tier1 (Coeff Geom DecState RawState)
open JPEG2000.Spec.Tier1Equiv

/-! ## Generic column and scan lemmas -/

section generic
variable {w h : Nat} {b : Band} (Q : JPEG2000.Tier1.St → DecState → Prop)

/-- **Rows of a column** for any relation `Q` preserved by the step at in-block positions. -/
theorem colRows_relG (stepF : JPEG2000.Tier1.St → Nat → JPEG2000.Tier1.St)
    (stepS : DecState → Nat × Nat → DecState)
    (hstep : ∀ s d x y, Q s d → x < w → y < h → Q (stepF s (bidx w x y)) (stepS d (x, y))) :
    ∀ k s d x y0, Q s d → x < w → y0 + k ≤ h →
      Q (JPEG2000.Tier1.colRows stepF (w + 2) k s (bidx w x y0))
        (((List.range k).map fun r => (x, y0 + r)).foldl stepS d) := by
  intro k
  induction k with
  | zero => intro s d x y0 R _ _; rw [colRows_zero]; exact R
  | succ k ih =>
    intro s d x y0 R hx hk
    rw [colRows_succ, List.range_succ_eq_map, List.map_cons, List.foldl_cons, List.map_map]
    have e : ((fun r => (x, y0 + r)) ∘ Nat.succ) = fun r => (x, (y0 + 1) + r) := by
      funext r; simp only [Function.comp, Nat.succ_eq_add_one]; congr 1; omega
    rw [e, show bidx w x y0 + (w + 2) = bidx w x (y0 + 1) by
      have := bidx_down w x y0 1; rw [Nat.one_mul] at this; exact this]
    simp only [Nat.add_zero]
    exact ih _ _ x (y0 + 1) (hstep s d x y0 R hx (by omega)) hx (by omega)

variable (colF : JPEG2000.Tier1.St → Nat → Nat → JPEG2000.Tier1.St)
  (colS : DecState → List (Nat × Nat) → DecState)
  (hcol : ∀ s d x y0, Q s d → x < w → y0 < h →
    Q (colF s (bidx w x y0) (min 4 (h - y0))) (colS d (Spec.Tier1.stripeColumn h x y0)))
include hcol

/-- The columns of one stripe. -/
theorem scanCols_relG (y0 : Nat) (hy : y0 < h) :
    ∀ k s d x0, Q s d → x0 + k ≤ w →
      Q (JPEG2000.Tier1.scanCols colF (min 4 (h - y0)) k s (bidx w x0 y0))
        (((List.range k).map fun x => Spec.Tier1.stripeColumn h (x0 + x) y0).foldl colS d) := by
  intro k
  induction k with
  | zero => intro s d x0 R _; exact R
  | succ k ih =>
    intro s d x0 R hk
    simp only [JPEG2000.Tier1.scanCols]
    rw [List.range_succ_eq_map, List.map_cons, List.foldl_cons, List.map_map, bidx_right]
    have e : ((fun x => Spec.Tier1.stripeColumn h (x0 + x) y0) ∘ Nat.succ) =
        fun x => Spec.Tier1.stripeColumn h ((x0 + 1) + x) y0 := by
      funext r; simp only [Function.comp, Nat.succ_eq_add_one]; congr 1; omega
    rw [e]
    simp only [Nat.add_zero]
    exact ih _ _ (x0 + 1) (hcol s d x0 y0 R (by omega) hy) (by omega)

/-- The stripes `j, …, j + k − 1`. -/
theorem scanStripes_relG :
    ∀ k s d j, Q s d → j + k ≤ (h + 3) / 4 →
      Q (JPEG2000.Tier1.scanStripes colF (fgeo w h b) k s (4 * j))
        (((List.range' j k).flatMap fun t =>
          (List.range w).map fun x => Spec.Tier1.stripeColumn h x (4 * t)).foldl colS d) := by
  intro k
  induction k with
  | zero => intro s d j R _; exact R
  | succ k ih =>
    intro s d j R hk
    simp only [JPEG2000.Tier1.scanStripes]
    rw [List.range'_succ, List.flatMap_cons, List.foldl_append]
    have hy : 4 * j < h := by omega
    have hs := scanCols_relG Q colF colS hcol (4 * j) hy w s d 0 R (by omega)
    simp only [Nat.zero_add] at hs
    have e1 : (4 * j + 1) * (fgeo w h b).st + 1 = bidx w 0 (4 * j) := bidx_zero w (4 * j)
    simp only [fgeo] at e1 ⊢
    rw [e1, show 4 * j + 4 = 4 * (j + 1) by omega]
    exact ih _ _ (j + 1) hs (by omega)

/-- **D.1 scan** for any relation: `scanBlock` simulates the fold over `stripeColumns`. -/
theorem scanBlock_relG (s : JPEG2000.Tier1.St) (d : DecState) (R : Q s d) :
    Q (JPEG2000.Tier1.scanBlock colF (fgeo w h b) s)
      ((Spec.Tier1.stripeColumns w h).foldl colS d) := by
  have := scanStripes_relG (b := b) Q colF colS hcol ((h + 3) / 4) s d 0 R (by omega)
  simp only [Nat.mul_zero] at this
  simp only [JPEG2000.Tier1.scanBlock, Spec.Tier1.stripeColumns]
  rw [List.range_eq_range' (n := (h + 3) / 4)]
  exact this

end generic

/-! ## Columns with a zero-column skip -/

section cols
variable {w h : Nat} {b : Band} {vc : Bool} {start : Nat}

/-- **A column with a skip test**: `if rows = 4 ∧ colOr &&& M = 0 then s else colRows …`
simulates the spec fold when the spec step is a no-op at every position whose word passes
the `M` test. -/
theorem skipCol_rel {raw : Bool} (M : UInt32)
    (stepF : JPEG2000.Tier1.St → Nat → JPEG2000.Tier1.St) (stepS : DecState → Nat × Nat → DecState)
    (hstep : ∀ s d x y, RelM w h b vc start raw s d → x < w → y < h →
      RelM w h b vc start raw (stepF s (bidx w x y)) (stepS d (x, y)))
    (hfix : ∀ s d x y, RelM w h b vc start raw s d → x < w → y < h →
      JPEG2000.Tier1.fget s.flags (bidx w x y) &&& M = 0 → stepS d (x, y) = d)
    (s : JPEG2000.Tier1.St) (d : DecState) (R : RelM w h b vc start raw s d) (x y0 : Nat)
    (hx : x < w) (hy : y0 < h) :
    RelM w h b vc start raw
      (if (min 4 (h - y0) == 4 &&
          JPEG2000.Tier1.colOr (fgeo w h b) s.flags (bidx w x y0) &&& M == 0) = true then s
       else JPEG2000.Tier1.colRows stepF (fgeo w h b).st (min 4 (h - y0)) s (bidx w x y0))
      ((Spec.Tier1.stripeColumn h x y0).foldl stepS d) := by
  rw [stripeColumn_eq]
  split
  · rename_i hskip
    simp only [Bool.and_eq_true, beq_iff_eq] at hskip
    obtain ⟨h4, hc⟩ := hskip
    rw [h4, range4]
    obtain ⟨c0, c1, c2, c3⟩ := colOr_test' w h b s.flags x y0 _ hc
    have nb : ∀ r, r < 4 → JPEG2000.Tier1.fget s.flags (bidx w x (y0 + r)) &&& M = 0 →
        stepS d (x, y0 + r) = d := fun r hr hz => hfix s d x (y0 + r) R hx (by omega) hz
    rw [foldl_fix _ _ _ (by
      intro a ha
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl
      · exact nb 0 (by omega) (by simpa using c0)
      · exact nb 1 (by omega) c1
      · exact nb 2 (by omega) c2
      · exact nb 3 (by omega) c3)]
    exact R
  · exact colRows_relG _ _ _ hstep _ s d x y0 R hx (by omega)

/-- Significance propagation, one stripe column (D.3.1). -/
theorem spColM_rel (one : UInt32) (p : Nat) (hone : HOne one p) (s : JPEG2000.Tier1.St)
    (d : DecState) (R : RelM w h b vc start false s d) (x y0 : Nat) (hx : x < w) (hy : y0 < h) :
    RelM w h b vc start false
      (JPEG2000.Tier1.spColM (fgeo w h b) vc one s (bidx w x y0) (min 4 (h - y0)))
      ((Spec.Tier1.stripeColumn h x y0).foldl (Spec.Tier1.sigPropStep (gV w h b vc) p) d) := by
  unfold JPEG2000.Tier1.spColM JPEG2000.Tier1.spSkip
  refine skipCol_rel JPEG2000.Tier1.SIG_NBRS _ _ (fun s d x y R hx hy => spStepM_rel R hx hy one p hone)
    (fun s d x y R hx hy hz => ?_) s d R x y0 hx hy
  have hn := nbrTest_relM R hx hy
  rw [hz] at hn
  have : (gV w h b vc).anySigNeighbour d.coeffs x y = false := by rw [← hn]; rfl
  simp [Spec.Tier1.sigPropStep, this]

/-- Raw significance propagation, one stripe column (D.6). -/
theorem rawSpCol_rel (one : UInt32) (p : Nat) (hone : HOne one p) (s : JPEG2000.Tier1.St)
    (d : DecState) (R : RelM w h b vc start true s d) (x y0 : Nat) (hx : x < w) (hy : y0 < h) :
    RelM w h b vc start true
      (JPEG2000.Tier1.rawSpCol (fgeo w h b) vc one s (bidx w x y0) (min 4 (h - y0)))
      ((Spec.Tier1.stripeColumn h x y0).foldl (Spec.Tier1.rawSigPropStep (gV w h b vc) p) d) := by
  unfold JPEG2000.Tier1.rawSpCol JPEG2000.Tier1.spSkip
  refine skipCol_rel JPEG2000.Tier1.SIG_NBRS _ _
    (fun s d x y R hx hy => rawSpStep_rel R hx hy one p hone)
    (fun s d x y R hx hy hz => ?_) s d R x y0 hx hy
  have hn := nbrTest_relM R hx hy
  rw [hz] at hn
  have : (gV w h b vc).anySigNeighbour d.coeffs x y = false := by rw [← hn]; rfl
  simp [Spec.Tier1.rawSigPropStep, this]

/-- The "not significant" spec fact from a zero `SIG` test. -/
theorem sig_false_of {raw : Bool} {s : JPEG2000.Tier1.St} {d : DecState}
    (R : RelM w h b vc start raw s d) {x y : Nat} (hx : x < w) (hy : y < h)
    (hz : JPEG2000.Tier1.fget s.flags (bidx w x y) &&& JPEG2000.Tier1.SIG = 0) :
    ((gV w h b vc).coeffAt d.coeffs ↑x ↑y).sig = false := by
  have hn := sigTest_relM R hx hy
  rw [hz] at hn
  cases hh : ((gV w h b vc).coeffAt d.coeffs ↑x ↑y).sig <;> simp_all

/-- Magnitude refinement, one stripe column (D.3.3). -/
theorem mrCol_relM (one : UInt32) (p : Nat) (hone : HOne one p) (s : JPEG2000.Tier1.St)
    (d : DecState) (R : RelM w h b vc start false s d) (x y0 : Nat) (hx : x < w) (hy : y0 < h) :
    RelM w h b vc start false
      (JPEG2000.Tier1.mrCol (fgeo w h b) one s (bidx w x y0) (min 4 (h - y0)))
      ((Spec.Tier1.stripeColumn h x y0).foldl (Spec.Tier1.magRefStep (gV w h b vc) p) d) := by
  unfold JPEG2000.Tier1.mrCol JPEG2000.Tier1.mrSkip
  refine skipCol_rel JPEG2000.Tier1.SIG _ _ (fun s d x y R hx hy => mrStep_relM R hx hy one p hone)
    (fun s d x y R hx hy hz => ?_) s d R x y0 hx hy
  have := sig_false_of R hx hy hz
  simp [Spec.Tier1.magRefStep, this]

/-- Raw magnitude refinement, one stripe column (D.6). -/
theorem rawMrCol_rel (one : UInt32) (p : Nat) (hone : HOne one p) (s : JPEG2000.Tier1.St)
    (d : DecState) (R : RelM w h b vc start true s d) (x y0 : Nat) (hx : x < w) (hy : y0 < h) :
    RelM w h b vc start true
      (JPEG2000.Tier1.rawMrCol (fgeo w h b) one s (bidx w x y0) (min 4 (h - y0)))
      ((Spec.Tier1.stripeColumn h x y0).foldl (Spec.Tier1.rawMagRefStep (gV w h b vc) p) d) := by
  unfold JPEG2000.Tier1.rawMrCol JPEG2000.Tier1.mrSkip
  refine skipCol_rel JPEG2000.Tier1.SIG _ _ (fun s d x y R hx hy => rawMrStep_rel R hx hy one p hone)
    (fun s d x y R hx hy hz => ?_) s d R x y0 hx hy
  have := sig_false_of R hx hy hz
  simp [Spec.Tier1.rawMagRefStep, this]

/-- The spec's run-length condition on a column given as a list of rows. -/
theorem runLength_eqM (d : DecState) (x y0 k : Nat) :
    Spec.Tier1.runLengthColumn (gV w h b vc) d.coeffs ((List.range k).map fun r => (x, y0 + r)) =
      (k == 4 && ((List.range k).all fun r =>
        !((gV w h b vc).coeffAt d.coeffs x (y0 + r)).sig &&
        !((gV w h b vc).coeffAt d.coeffs x (y0 + r)).visited &&
        !(gV w h b vc).anySigNeighbour d.coeffs x (y0 + r))) := by
  simp [Spec.Tier1.runLengthColumn, List.all_map, Function.comp_def]

/-- **Cleanup, one stripe column** (D.3.4), run-length mode included. -/
theorem cuColM_rel (one : UInt32) (p : Nat) (hone : HOne one p) (s : JPEG2000.Tier1.St)
    (d : DecState) (R : RelM w h b vc start false s d) (x y0 : Nat) (hx : x < w) (hy : y0 < h) :
    RelM w h b vc start false
      (JPEG2000.Tier1.cuColM (fgeo w h b) vc one s (bidx w x y0) (min 4 (h - y0)))
      (Spec.Tier1.cleanupColumn (gV w h b vc) p d (Spec.Tier1.stripeColumn h x y0)) := by
  rw [stripeColumn_eq]
  have hcu := colRows_relG (w := w) (h := h) (RelM w h b vc start false)
    (JPEG2000.Tier1.cuStepM (fgeo w h b) vc one) (Spec.Tier1.cleanupStep (gV w h b vc) p)
    (fun s d x y R hx hy => cuStepM_rel R hx hy one p hone)
  have hrl : JPEG2000.Tier1.rlCond (fgeo w h b) s (bidx w x y0) (min 4 (h - y0)) =
      Spec.Tier1.runLengthColumn (gV w h b vc) d.coeffs
        ((List.range (min 4 (h - y0))).map fun r => (x, y0 + r)) := by
    rw [runLength_eqM]
    simp only [JPEG2000.Tier1.rlCond]
    by_cases h4 : min 4 (h - y0) = 4
    · rw [h4, colOr_test]
      have hy3 : y0 + 3 < h := by omega
      rw [rlTest_relM R hx hy, rlTest_relM R hx (by omega : y0 + 1 < h),
        rlTest_relM R hx (by omega : y0 + 2 < h), rlTest_relM R hx hy3]
      simp [List.range, List.range.loop, Bool.and_assoc]
    · rw [beq_eq_false_iff_ne.mpr h4]; simp
  unfold JPEG2000.Tier1.cuColM Spec.Tier1.cleanupColumn
  rw [hrl]
  split
  · rename_i hc
    rw [runLength_eqM] at hc
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hc
    obtain ⟨h4, hall⟩ := hc
    have hy3 : y0 + 3 < h := by omega
    rw [h4, range4]
    obtain ⟨mq, fl, mags⟩ := s
    simp only
    obtain ⟨e1, R1⟩ := decode_relM R 17
    generalize mq.decode 17 = rf at e1 R1 ⊢
    have hc17 : Spec.Tier1.ctxRunLength = 17 := rfl
    rw [hc17]
    generalize hrs : d.decodeBit 17 = rs at e1 R1 ⊢
    obtain ⟨bf, mq1⟩ := rf
    obtain ⟨bs, d1⟩ := rs
    have hcs1 : d1.coeffs = d.coeffs := by rw [← decodeBit_coeffs d _, hrs]
    simp only at e1 R1 ⊢
    subst e1
    cases bf
    · simp only [Bool.not_false, ↓reduceIte]; exact R1
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      have hc18 : Spec.Tier1.ctxUniform = 18 := rfl
      rw [hc18]
      obtain ⟨e2, R2⟩ := decode_relM R1 18
      generalize mq1.decode 18 = rf at e2 R2 ⊢
      generalize hrs2 : d1.decodeBit 18 = rs at e2 R2 ⊢
      obtain ⟨b1, mq2⟩ := rf
      obtain ⟨bs2, d2⟩ := rs
      have hcs2 : d2.coeffs = d.coeffs := by rw [← hcs1, ← decodeBit_coeffs d1 _, hrs2]
      simp only at e2 R2 ⊢
      subst e2
      obtain ⟨e3, R3⟩ := decode_relM R2 18
      generalize mq2.decode 18 = rf at e3 R3 ⊢
      generalize hrs3 : d2.decodeBit 18 = rs at e3 R3 ⊢
      obtain ⟨b0, mq3⟩ := rf
      obtain ⟨bs3, d3⟩ := rs
      have hcs3 : d3.coeffs = d.coeffs := by rw [← hcs2, ← decodeBit_coeffs d2 _, hrs3]
      simp only at e3 R3 ⊢
      subst e3
      have insig : ∀ r : Nat, r < 4 →
          ((gV w h b vc).coeffAt d3.coeffs x ((y0 + r : Nat) : Int)).sig = false := by
        intro r hr
        have := hall r (by omega)
        rw [hcs3, Int.natCast_add]
        simpa using this.1.1
      have go : ∀ r, r ≤ 3 →
          RelM w h b vc start false
            (JPEG2000.Tier1.colRows (JPEG2000.Tier1.cuStepM (fgeo w h b) vc one) (fgeo w h b).st (3 - r)
              (JPEG2000.Tier1.becomeSigM (fgeo w h b) vc one false ⟨mq3, fl, mags⟩
                (bidx w x y0 + r * (fgeo w h b).st))
              (bidx w x y0 + (r + 1) * (fgeo w h b).st))
            (((List.range (3 - r)).map fun k => (x, (y0 + r + 1) + k)).foldl
              (Spec.Tier1.cleanupStep (gV w h b vc) p)
              (Spec.Tier1.becomeSignificant (gV w h b vc) p false d3 x (y0 + r))) := by
        intro r hr
        simp only [fgeo]
        rw [bidx_down, bidx_down, show y0 + (r + 1) = y0 + r + 1 by omega]
        exact hcu (3 - r) _ _ x (y0 + r + 1)
          (becomeSigM_rel R3 hx (by omega) (insig r (by omega)) one p hone false) hx (by omega)
      cases b1 <;> cases b0 <;>
        simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add, Nat.add_zero] <;>
        simp [List.drop, List.range, List.range.loop]
      · have := go 0 (by omega); simpa [List.range, List.range.loop] using this
      · have := go 1 (by omega); simpa [List.range, List.range.loop, Nat.add_assoc] using this
      · have := go 2 (by omega); simpa [List.range, List.range.loop, Nat.add_assoc] using this
      · have := go 3 (by omega); simpa [List.range, List.range.loop, Nat.add_assoc] using this
  · exact hcu _ s d x y0 R hx (by omega)

end cols

/-! ## Clearing the visited marks -/

/-- **Clearing the visited marks**: `clearVis` simulates `clearVisited` under `RelM`. -/
theorem clearVis_relM {w h : Nat} {b : Band} {vc : Bool} {start : Nat} {raw : Bool}
    {s : JPEG2000.Tier1.St} {d : DecState} (R : RelM w h b vc start raw s d) :
    RelM w h b vc start raw (JPEG2000.Tier1.clearVis s)
      { d with coeffs := Spec.Tier1.clearVisited d.coeffs } := by
  obtain ⟨mq, fl, mags⟩ := s
  have hm : ∀ X Y, (gV w h b vc).coeffAt (Spec.Tier1.clearVisited d.coeffs) X Y =
      { (gV w h b vc).coeffAt d.coeffs X Y with visited := false } :=
    fun X Y => coeffAt_map _ _ _ rfl X Y
  refine ⟨R.coder, by simp [JPEG2000.Tier1.clearVis, clearVisFrom_size, R.fsize], R.msize,
    by simp [Spec.Tier1.clearVisited, R.csize], ?_, ?_⟩
  · intro x y j hx hy hj
    have hk : bidx w x y < fl.size := by rw [R.fsize]; exact bidx_lt hx hy
    simp only [JPEG2000.Tier1.clearVis]
    rw [clearVisFrom_get _ _ _ _ hk, ite_pos' ⟨Nat.zero_le _, by omega⟩, bt_and, bt_notVIS j hj,
      R.flag x y j hx hy hj]
    simp only [specBitV, Geom.nbAt, hm]
    by_cases hj12 : j < 12
    · have : ¬ (14 = j) := by omega
      simp only [hj12, ↓reduceIte, this, decide_false, Bool.not_false, Bool.and_true]
      cases (gV w h b vc).hidden y (nbPos j ↑x ↑y).snd <;> split <;> rfl
    · rcases (by omega : j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15) with rfl | rfl | rfl | rfl <;>
        simp [ownBit]
  · intro x y hx hy
    simp only [JPEG2000.Tier1.clearVis]
    rw [R.mag x y hx hy, hm]

/-! ## Whole passes -/

section passes
variable {w h : Nat} {b : Band} {vc : Bool} {start : Nat}

/-- **Significance propagation pass** (D.3.1), mode-aware. -/
theorem sigPropPassM_rel (one : UInt32) (p : Nat) (hone : HOne one p) (s : JPEG2000.Tier1.St)
    (d : DecState) (R : RelM w h b vc start false s d) :
    RelM w h b vc start false (JPEG2000.Tier1.sigPropPassM (fgeo w h b) vc one s)
      (Spec.Tier1.sigPropPass (gV w h b vc) p d) := by
  unfold JPEG2000.Tier1.sigPropPassM Spec.Tier1.sigPropPass Spec.Tier1.scanOrder
  rw [List.foldl_flatten]
  exact scanBlock_relG (RelM w h b vc start false) _
    (fun d col => col.foldl (Spec.Tier1.sigPropStep (gV w h b vc) p) d)
    (fun s d x y0 R hx hy => spColM_rel one p hone s d R x y0 hx hy) s d R

/-- **Magnitude refinement pass** (D.3.3) under `RelM`. -/
theorem magRefPass_relM (one : UInt32) (p : Nat) (hone : HOne one p) (s : JPEG2000.Tier1.St)
    (d : DecState) (R : RelM w h b vc start false s d) :
    RelM w h b vc start false (JPEG2000.Tier1.magRefPass (fgeo w h b) one s)
      (Spec.Tier1.magRefPass (gV w h b vc) p d) := by
  unfold JPEG2000.Tier1.magRefPass Spec.Tier1.magRefPass Spec.Tier1.scanOrder
  rw [List.foldl_flatten]
  exact scanBlock_relG (RelM w h b vc start false) _
    (fun d col => col.foldl (Spec.Tier1.magRefStep (gV w h b vc) p) d)
    (fun s d x y0 R hx hy => mrCol_relM one p hone s d R x y0 hx hy) s d R

/-- **Cleanup pass** (D.3.4), mode-aware, including the clearing of the visited marks. -/
theorem cleanupPassM_rel (one : UInt32) (p : Nat) (hone : HOne one p) (s : JPEG2000.Tier1.St)
    (d : DecState) (R : RelM w h b vc start false s d) :
    RelM w h b vc start false (JPEG2000.Tier1.cleanupPassM (fgeo w h b) vc one s)
      (Spec.Tier1.cleanupPass (gV w h b vc) p d) := by
  unfold JPEG2000.Tier1.cleanupPassM Spec.Tier1.cleanupPass
  exact clearVis_relM (scanBlock_relG (RelM w h b vc start false) _
    (Spec.Tier1.cleanupColumn (gV w h b vc) p)
    (fun s d x y0 R hx hy => cuColM_rel one p hone s d R x y0 hx hy) s d R)

/-- **Raw significance propagation pass** (D.6). -/
theorem rawSigPropPass_rel (one : UInt32) (p : Nat) (hone : HOne one p) (s : JPEG2000.Tier1.St)
    (d : DecState) (R : RelM w h b vc start true s d) :
    RelM w h b vc start true (JPEG2000.Tier1.rawSigPropPass (fgeo w h b) vc one s)
      (Spec.Tier1.rawSigPropPass (gV w h b vc) p d) := by
  unfold JPEG2000.Tier1.rawSigPropPass Spec.Tier1.rawSigPropPass Spec.Tier1.scanOrder
  rw [List.foldl_flatten]
  exact scanBlock_relG (RelM w h b vc start true) _
    (fun d col => col.foldl (Spec.Tier1.rawSigPropStep (gV w h b vc) p) d)
    (fun s d x y0 R hx hy => rawSpCol_rel one p hone s d R x y0 hx hy) s d R

/-- **Raw magnitude refinement pass** (D.6). -/
theorem rawMagRefPass_rel (one : UInt32) (p : Nat) (hone : HOne one p) (s : JPEG2000.Tier1.St)
    (d : DecState) (R : RelM w h b vc start true s d) :
    RelM w h b vc start true (JPEG2000.Tier1.rawMagRefPass (fgeo w h b) one s)
      (Spec.Tier1.rawMagRefPass (gV w h b vc) p d) := by
  unfold JPEG2000.Tier1.rawMagRefPass Spec.Tier1.rawMagRefPass Spec.Tier1.scanOrder
  rw [List.foldl_flatten]
  exact scanBlock_relG (RelM w h b vc start true) _
    (fun d col => col.foldl (Spec.Tier1.rawMagRefStep (gV w h b vc) p) d)
    (fun s d x y0 R hx hy => rawMrCol_rel one p hone s d R x y0 hx hy) s d R

end passes

end JPEG2000.Spec.Tier1EquivM
