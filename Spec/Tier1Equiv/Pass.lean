import Spec.Tier1Equiv.Steps

/-!
# C3 (plain mode), part 3c: columns, scan order, passes

Plan.md §4 (C3), §5.2 "Tier-1 / EBCOT"; T.800 D.1 (scan order), D.2 (pass sequence),
D.3.1–D.3.4 (the three passes, run-length mode). Task 3.6.

* `colRows_rel` — a stripe column coded row by row (`colRows`) simulates the spec fold over
  the column's positions.
* `spCol_rel`, `mrCol_rel`, `cuCol_rel` — one stripe column of each pass, including the
  zero-column skips of the fast decoder (`spSkip`, `mrSkip`: every spec step is then a no-op)
  and the run-length path of the cleanup pass (`rlCond` = `runLengthColumn`).
* `scanBlock_rel` — the fast stripe/column loops (`scanStripes`, `scanCols`) visit the stripe
  columns of `Spec.Tier1.stripeColumns` in order.
* `sigPropPass_rel`, `magRefPass_rel`, `cleanupPass_rel` (with `clearVis` =
  `clearVisited`), `runPass_rel`, `runPasses_rel` — whole passes and pass sequences.
-/

namespace JPEG2000.Spec.Tier1Equiv

open JPEG2000
open JPEG2000.Tier2.Geometry (Band)
open JPEG2000.Spec.Tier1 (Coeff Geom DecState)

/-! ## Index and list helpers -/

/-- Moving down `r` rows in the bordered array. -/
theorem bidx_down (w x y r : Nat) : bidx w x y + r * (w + 2) = bidx w x (y + r) := by
  unfold bidx
  have e : (y + 1 + r) * (w + 2) = (y + 1) * (w + 2) + r * (w + 2) := Nat.add_mul _ _ _
  rw [show y + r + 1 = (y + 1) + r by omega, e]
  omega

/-- Moving right one column in the bordered array. -/
theorem bidx_right (w x y : Nat) : bidx w x y + 1 = bidx w (x + 1) y := by
  unfold bidx; omega

/-- The first in-block position of stripe row `y0`. -/
theorem bidx_zero (w y : Nat) : (y + 1) * (w + 2) + 1 = bidx w 0 y := by
  unfold bidx; omega

/-- A stripe column as a `map` over its rows. -/
theorem stripeColumn_eq (h x y0 : Nat) :
    Spec.Tier1.stripeColumn h x y0 = (List.range (min 4 (h - y0))).map fun r => (x, y0 + r) := by
  unfold Spec.Tier1.stripeColumn
  congr 1
  have key : ∀ n, (List.range n).filter (fun r => decide (y0 + r < h)) =
      List.range (min n (h - y0)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [List.range_succ, List.filter_append, ih]
      by_cases hn : y0 + n < h
      · simp [hn, show min n (h - y0) = n by omega, show min (n + 1) (h - y0) = n + 1 by omega,
          List.range_succ]
      · simp [hn, show min n (h - y0) = h - y0 by omega,
          show min (n + 1) (h - y0) = h - y0 by omega]
  exact key 4

/-- A fold whose every step is the identity. -/
theorem foldl_fix {α β : Type} (f : β → α → β) (d : β) (l : List α) (h : ∀ a ∈ l, f d a = d) :
    l.foldl f d = d := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.foldl_cons]
    rw [h a (by simp)]
    exact ih (fun a' ha' => h a' (by simp [ha']))

/-- One more row of `colRows`. -/
theorem colRows_succ (step : Tier1.St → Nat → Tier1.St) (st k : Nat) (s : Tier1.St) (i : Nat) :
    Tier1.colRows step st (k + 1) s i = Tier1.colRows step st k (step s i) (i + st) := by
  obtain ⟨mq, fl, mags⟩ := s
  simp only [Tier1.colRows, Tier1.colRowsU]
  all_goals (generalize step { mq := mq, flags := fl, mags := mags } i = t; obtain ⟨_, _, _⟩ := t; rfl)

/-- No row of `colRows`. -/
theorem colRows_zero (step : Tier1.St → Nat → Tier1.St) (st : Nat) (s : Tier1.St) (i : Nat) :
    Tier1.colRows step st 0 s i = s := by
  obtain ⟨_, _, _⟩ := s; rfl

/-! ## A stripe column, row by row -/

section col
variable {w h : Nat} {b : Band} {start : Nat}

/-- **Rows of a column**: if a fast step simulates a spec step at every in-block position,
`colRows` over `k` rows from `(x, y0)` simulates the spec fold over `(x, y0), …,
(x, y0 + k − 1)`. -/
theorem colRows_rel (stepF : Tier1.St → Nat → Tier1.St)
    (stepS : DecState → Nat × Nat → DecState)
    (hstep : ∀ s d x y, Rel w h b start s d → x < w → y < h →
      Rel w h b start (stepF s (bidx w x y)) (stepS d (x, y))) :
    ∀ k s d x y0, Rel w h b start s d → x < w → y0 + k ≤ h →
      Rel w h b start (Tier1.colRows stepF (w + 2) k s (bidx w x y0))
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

end col

/-! ## Word tests over a whole column -/

/-- An OR of words passes a masked zero test iff both do. -/
theorem or_test (a c M : UInt32) :
    ((a ||| c) &&& M == 0) = ((a &&& M == 0) && (c &&& M == 0)) := by
  have hiff : ((a ||| c) &&& M = 0) ↔ (a &&& M = 0 ∧ c &&& M = 0) := by
    simp only [eq_zero_iff_bt, bt_and, bt_or]
    constructor
    · intro hh
      constructor <;> intro j <;> have := hh j <;> revert this <;>
        cases bt a j <;> cases bt c j <;> cases bt M j <;> simp
    · intro ⟨h1, h2⟩ j
      have := h1 j; have := h2 j
      revert this; revert this
      cases bt a j <;> cases bt c j <;> cases bt M j <;> simp
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, beq_iff_eq]
  exact hiff

/-- The column test of a full stripe column is the conjunction of the four word tests. -/
theorem colOr_test (w h : Nat) (b : Band) (fl : Array UInt32) (x y0 : Nat) (M : UInt32) :
    (Tier1.colOr (fgeo w h b) fl (bidx w x y0) &&& M == 0) =
      ((Tier1.fget fl (bidx w x y0) &&& M == 0) &&
       (Tier1.fget fl (bidx w x (y0 + 1)) &&& M == 0) &&
       (Tier1.fget fl (bidx w x (y0 + 2)) &&& M == 0) &&
       (Tier1.fget fl (bidx w x (y0 + 3)) &&& M == 0)) := by
  simp only [Tier1.colOr, fgeo, or_test]
  rw [← bidx_down w x y0 1, ← bidx_down w x y0 2, ← bidx_down w x y0 3, Nat.one_mul]

/-- `colOr_test` as propositions. -/
theorem colOr_test' (w h : Nat) (b : Band) (fl : Array UInt32) (x y0 : Nat) (M : UInt32)
    (hc : Tier1.colOr (fgeo w h b) fl (bidx w x y0) &&& M = 0) :
    Tier1.fget fl (bidx w x y0) &&& M = 0 ∧ Tier1.fget fl (bidx w x (y0 + 1)) &&& M = 0 ∧
    Tier1.fget fl (bidx w x (y0 + 2)) &&& M = 0 ∧ Tier1.fget fl (bidx w x (y0 + 3)) &&& M = 0 := by
  have := colOr_test w h b fl x y0 M
  rw [hc] at this
  simp only [beq_self_eq_true] at this
  have t := this.symm
  simp only [Bool.and_eq_true, beq_iff_eq] at t
  exact ⟨t.1.1.1, t.1.1.2, t.1.2, t.2⟩

/-- The four positions of a full stripe column. -/
theorem range4 (x y0 : Nat) : ((List.range 4).map fun r => (x, y0 + r)) =
    [(x, y0), (x, y0 + 1), (x, y0 + 2), (x, y0 + 3)] := by
  simp [List.range, List.range.loop]

/-! ## One stripe column of each pass -/

section cols
variable {w h : Nat} {b : Band} {start : Nat}

/-- The weight of a bit-plane as a word. -/
def HOne (one : UInt32) (p : Nat) : Prop := one.toNat = 2 ^ p % 2 ^ 32

/-- **Significance propagation, one stripe column** (with the zero-column skip). -/
theorem spCol_rel (one : UInt32) (p : Nat) (hone : HOne one p) (s : Tier1.St) (d : DecState)
    (R : Rel w h b start s d) (x y0 : Nat) (hx : x < w) (hy : y0 < h) :
    Rel w h b start (Tier1.spCol (fgeo w h b) one s (bidx w x y0) (min 4 (h - y0)))
      ((Spec.Tier1.stripeColumn h x y0).foldl (Spec.Tier1.sigPropStep (sgeom w h b) p) d) := by
  rw [stripeColumn_eq]
  unfold Tier1.spCol
  split
  · rename_i hskip
    simp only [Tier1.spSkip, Bool.and_eq_true, beq_iff_eq] at hskip
    obtain ⟨h4, hc⟩ := hskip
    rw [h4, range4]
    obtain ⟨c0, c1, c2, c3⟩ := colOr_test' w h b s.flags x y0 _ hc
    have nb : ∀ r, r < 4 → Tier1.fget s.flags (bidx w x (y0 + r)) &&& Tier1.SIG_NBRS = 0 →
        Spec.Tier1.sigPropStep (sgeom w h b) p d (x, y0 + r) = d := by
      intro r hr hz
      have hn := nbrTest_rel R hx (show y0 + r < h by omega)
      rw [hz] at hn
      have : (sgeom w h b).anySigNeighbour d.coeffs x (y0 + r) = false := by rw [← hn]; rfl
      simp [Spec.Tier1.sigPropStep, this]
    rw [foldl_fix _ _ _ (by
      intro a ha
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl
      · exact nb 0 (by omega) (by simpa using c0)
      · exact nb 1 (by omega) c1
      · exact nb 2 (by omega) c2
      · exact nb 3 (by omega) c3)]
    exact R
  · exact colRows_rel _ _ (fun s d x y R hx hy => spStep_rel R hx hy one p hone) _ s d x y0 R hx
      (by omega)

/-- **Magnitude refinement, one stripe column** (with the zero-column skip). -/
theorem mrCol_rel (one : UInt32) (p : Nat) (hone : HOne one p) (s : Tier1.St) (d : DecState)
    (R : Rel w h b start s d) (x y0 : Nat) (hx : x < w) (hy : y0 < h) :
    Rel w h b start (Tier1.mrCol (fgeo w h b) one s (bidx w x y0) (min 4 (h - y0)))
      ((Spec.Tier1.stripeColumn h x y0).foldl (Spec.Tier1.magRefStep (sgeom w h b) p) d) := by
  rw [stripeColumn_eq]
  unfold Tier1.mrCol
  split
  · rename_i hskip
    simp only [Tier1.mrSkip, Bool.and_eq_true, beq_iff_eq] at hskip
    obtain ⟨h4, hc⟩ := hskip
    rw [h4, range4]
    obtain ⟨c0, c1, c2, c3⟩ := colOr_test' w h b s.flags x y0 _ hc
    have nb : ∀ r, r < 4 → Tier1.fget s.flags (bidx w x (y0 + r)) &&& Tier1.SIG = 0 →
        Spec.Tier1.magRefStep (sgeom w h b) p d (x, y0 + r) = d := by
      intro r hr hz
      have hn := sigTest_rel R hx (show y0 + r < h by omega)
      rw [hz] at hn
      simp only [Spec.Tier1.magRefStep]
      have : ((sgeom w h b).coeffAt d.coeffs ↑x ↑(y0 + r)).sig = false := by
        cases hh : ((sgeom w h b).coeffAt d.coeffs ↑x ↑(y0 + r)).sig <;> simp_all
      have this' : ((sgeom w h b).coeffAt d.coeffs ↑x ((y0 : Int) + r)).sig = false := by
        rw [← Int.natCast_add]; exact this
      simp [this']
    rw [foldl_fix _ _ _ (by
      intro a ha
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl
      · exact nb 0 (by omega) (by simpa using c0)
      · exact nb 1 (by omega) c1
      · exact nb 2 (by omega) c2
      · exact nb 3 (by omega) c3)]
    exact R
  · exact colRows_rel _ _ (fun s d x y R hx hy => mrStep_rel R hx hy one p hone) _ s d x y0 R hx
      (by omega)

/-- The run-length word test: insignificant, not visited, no significant neighbour. -/
theorem rlTest_rel {s : Tier1.St} {d : DecState} (R : Rel w h b start s d) {x y : Nat}
    (hx : x < w) (hy : y < h) :
    (Tier1.fget s.flags (bidx w x y) &&& (Tier1.SIG ||| Tier1.VIS ||| Tier1.SIG_NBRS) == 0) =
      (!((sgeom w h b).coeffAt d.coeffs x y).sig && !((sgeom w h b).coeffAt d.coeffs x y).visited &&
        !(sgeom w h b).anySigNeighbour d.coeffs x y) := by
  have e : (Tier1.SIG ||| Tier1.VIS ||| Tier1.SIG_NBRS) = (Tier1.SIG ||| Tier1.VIS) ||| Tier1.SIG_NBRS := rfl
  have key : ∀ f M N : UInt32, (f &&& (M ||| N) == 0) = ((f &&& M == 0) && (f &&& N == 0)) := by
    intro f M N
    have : f &&& (M ||| N) = (f &&& M) ||| (f &&& N) := by
      apply UInt32.toNat_inj.mp; simp [UInt32.toNat_and, UInt32.toNat_or, Nat.and_or_distrib_left]
    rw [this]
    have k2 := or_test (f &&& M) (f &&& N) 0xFFFFFFFF
    have : ∀ u : UInt32, u &&& 0xFFFFFFFF = u := by
      intro u; apply UInt32.toNat_inj.mp
      rw [UInt32.toNat_and]
      have := u.toNat_lt
      have h' : (0xFFFFFFFF : UInt32).toNat = 2 ^ 32 - 1 := rfl
      rw [h', Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_eq_of_lt this
    simp only [this] at k2; exact k2
  rw [e, key, sigVisTest_rel R hx hy]
  have hn := nbrTest_rel R hx hy
  rw [show (Tier1.fget s.flags (bidx w x y) &&& Tier1.SIG_NBRS != 0) =
    !(Tier1.fget s.flags (bidx w x y) &&& Tier1.SIG_NBRS == 0) from rfl] at hn
  rw [← hn, Bool.not_not]

/-- The spec's run-length condition on a column given as a list of rows. -/
theorem runLength_eq (d : DecState) (x y0 k : Nat) :
    Spec.Tier1.runLengthColumn (sgeom w h b) d.coeffs ((List.range k).map fun r => (x, y0 + r)) =
      (k == 4 && ((List.range k).all fun r =>
        !((sgeom w h b).coeffAt d.coeffs x (y0 + r)).sig &&
        !((sgeom w h b).coeffAt d.coeffs x (y0 + r)).visited &&
        !(sgeom w h b).anySigNeighbour d.coeffs x (y0 + r))) := by
  simp [Spec.Tier1.runLengthColumn, List.all_map, Function.comp_def]

/-- **Cleanup, one stripe column** (D.3.4), run-length mode included. -/
theorem cuCol_rel (one : UInt32) (p : Nat) (hone : HOne one p) (s : Tier1.St) (d : DecState)
    (R : Rel w h b start s d) (x y0 : Nat) (hx : x < w) (hy : y0 < h) :
    Rel w h b start (Tier1.cuCol (fgeo w h b) one s (bidx w x y0) (min 4 (h - y0)))
      (Spec.Tier1.cleanupColumn (sgeom w h b) p d (Spec.Tier1.stripeColumn h x y0)) := by
  rw [stripeColumn_eq]
  have hcu := colRows_rel (w := w) (h := h) (b := b) (start := start) (Tier1.cuStep (fgeo w h b) one)
    (Spec.Tier1.cleanupStep (sgeom w h b) p)
    (fun s d x y R hx hy => cuStep_rel R hx hy one p hone)
  -- the run-length condition agrees
  have hrl : Tier1.rlCond (fgeo w h b) s (bidx w x y0) (min 4 (h - y0)) =
      Spec.Tier1.runLengthColumn (sgeom w h b) d.coeffs
        ((List.range (min 4 (h - y0))).map fun r => (x, y0 + r)) := by
    rw [runLength_eq]
    simp only [Tier1.rlCond]
    by_cases h4 : min 4 (h - y0) = 4
    · rw [h4, colOr_test]
      have hy3 : y0 + 3 < h := by omega
      rw [rlTest_rel R hx hy, rlTest_rel R hx (by omega : y0 + 1 < h),
        rlTest_rel R hx (by omega : y0 + 2 < h), rlTest_rel R hx hy3]
      simp [List.range, List.range.loop, Bool.and_assoc]
    · rw [beq_eq_false_iff_ne.mpr h4]; simp
  unfold Tier1.cuCol Spec.Tier1.cleanupColumn
  rw [hrl]
  split
  · rename_i hc
    rw [runLength_eq] at hc
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hc
    obtain ⟨h4, hall⟩ := hc
    have hy3 : y0 + 3 < h := by omega
    rw [h4, range4]
    obtain ⟨mq, fl, mags⟩ := s
    simp only
    obtain ⟨e1, R1⟩ := decode_rel R 17
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
      obtain ⟨e2, R2⟩ := decode_rel R1 18
      generalize mq1.decode 18 = rf at e2 R2 ⊢
      generalize hrs2 : d1.decodeBit 18 = rs at e2 R2 ⊢
      obtain ⟨b1, mq2⟩ := rf
      obtain ⟨bs2, d2⟩ := rs
      have hcs2 : d2.coeffs = d.coeffs := by rw [← hcs1, ← decodeBit_coeffs d1 _, hrs2]
      simp only at e2 R2 ⊢
      subst e2
      obtain ⟨e3, R3⟩ := decode_rel R2 18
      generalize mq2.decode 18 = rf at e3 R3 ⊢
      generalize hrs3 : d2.decodeBit 18 = rs at e3 R3 ⊢
      obtain ⟨b0, mq3⟩ := rf
      obtain ⟨bs3, d3⟩ := rs
      have hcs3 : d3.coeffs = d.coeffs := by rw [← hcs2, ← decodeBit_coeffs d2 _, hrs3]
      simp only at e3 R3 ⊢
      subst e3
      have insig : ∀ r : Nat, r < 4 →
          ((sgeom w h b).coeffAt d3.coeffs x ((y0 + r : Nat) : Int)).sig = false := by
        intro r hr
        have := hall r (by omega)
        rw [hcs3, Int.natCast_add]
        simpa using this.1.1
      have go : ∀ r, r ≤ 3 →
          Rel w h b start
            (Tier1.colRows (Tier1.cuStep (fgeo w h b) one) (fgeo w h b).st (3 - r)
              (Tier1.becomeSig (fgeo w h b) one false ⟨mq3, fl, mags⟩
                (bidx w x y0 + r * (fgeo w h b).st))
              (bidx w x y0 + (r + 1) * (fgeo w h b).st))
            (((List.range (3 - r)).map fun k => (x, (y0 + r + 1) + k)).foldl
              (Spec.Tier1.cleanupStep (sgeom w h b) p)
              (Spec.Tier1.becomeSignificant (sgeom w h b) p false d3 x (y0 + r))) := by
        intro r hr
        simp only [fgeo]
        rw [bidx_down, bidx_down, show y0 + (r + 1) = y0 + r + 1 by omega]
        exact hcu (3 - r) _ _ x (y0 + r + 1)
          (becomeSig_rel R3 hx (by omega) (insig r (by omega)) one p hone false) hx (by omega)
      cases b1 <;> cases b0 <;>
        simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add, Nat.add_zero] <;>
        simp [List.drop, List.range, List.range.loop]
      · have := go 0 (by omega); simpa [List.range, List.range.loop] using this
      · have := go 1 (by omega); simpa [List.range, List.range.loop, Nat.add_assoc] using this
      · have := go 2 (by omega); simpa [List.range, List.range.loop, Nat.add_assoc] using this
      · have := go 3 (by omega); simpa [List.range, List.range.loop, Nat.add_assoc] using this
  · exact hcu _ s d x y0 R hx (by omega)

end cols

end JPEG2000.Spec.Tier1Equiv
