import Spec.Resources.Tier1Schedule

/-!
# Tier-1 raster storage and clearing loops (Plan.md §§3–5, 7, S3; T.800 D.1–D.7)

The wide raster and the two bordered compact arrays keep their allocation domains across
every pass and restart. These sizes also bound the full-array cleanup scans.
-/

namespace JPEG2000.Spec.Resources.Tier1Work

open JPEG2000 JPEG2000.Tier1 JPEG2000.Tier2.Geometry

private theorem fold_keep {σ α β : Type} (size : σ → β) (step : σ → α → σ)
    (same : ∀ s a, size (step s a) = size s) (xs : List α) (s : σ) :
    size (xs.foldl step s) = size s := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => exact (ih _).trans (same s x)

private abbrev wideSize (s : WidePlain.State) := s.cells.size

private theorem put_size (s : WidePlain.State) (w : Nat) (pos : Nat × Nat) (c : WidePlain.Cell) :
    wideSize (WidePlain.put s w pos c) = wideSize s := by simp [wideSize, WidePlain.put]

private theorem bit_size (s : WidePlain.State) (cx : Nat) : wideSize (WidePlain.bit s cx).2 = wideSize s := rfl

private theorem become_size (w h p : Nat) (v : Bool) (s : WidePlain.State) (pos : Nat × Nat) :
    wideSize (WidePlain.become w h p v s pos) = wideSize s := by
  simp only [WidePlain.become, put_size, bit_size]

private theorem zero_size (w h : Nat) (b : Band) (p : Nat) (v : Bool) (s : WidePlain.State)
    (pos : Nat × Nat) : wideSize (WidePlain.zeroCode w h b p v s pos) = wideSize s := by
  unfold WidePlain.zeroCode; dsimp only; split <;> simp only [become_size, put_size, bit_size]

private theorem wcu_size (w h : Nat) (b : Band) (p : Nat) (s : WidePlain.State) (pos : Nat × Nat) :
    wideSize (WidePlain.cleanupCell w h b p s pos) = wideSize s := by
  unfold WidePlain.cleanupCell; dsimp only; split <;> first | exact zero_size .. | rfl

private theorem wcol_size (w h : Nat) (b : Band) (p : Nat) (s : WidePlain.State)
    (col : List (Nat × Nat)) : wideSize (WidePlain.cleanupColumn w h b p s col) = wideSize s := by
  have ord := fold_keep wideSize _ (wcu_size w h b p)
  unfold WidePlain.cleanupColumn; dsimp only
  split
  · split
    · rfl
    · split <;> simp only [ord, become_size, bit_size]
  · exact ord _ _

private theorem wprop_size (raw : Bool) (w h : Nat) (b : Band) (p : Nat) (s : WidePlain.State)
    (pos : Nat × Nat) :
    wideSize ((if raw then WideModes.rawPropagate w h p else WidePlain.propagate w h b p) s pos) =
      wideSize s := by
  cases raw <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · unfold WidePlain.propagate; split <;> first | exact zero_size .. | rfl
  · unfold WideModes.rawPropagate; dsimp only
    split
    · split <;> rw [put_size] <;> rfl
    · rfl

private theorem wref_size (raw : Bool) (w h p : Nat) (s : WidePlain.State) (pos : Nat × Nat) :
    wideSize ((if raw then WideModes.rawRefine w h p else WidePlain.refineCell w h p) s pos) =
      wideSize s := by
  cases raw <;> simp only [WideModes.rawRefine, WidePlain.refineCell, Bool.false_eq_true, ↓reduceIte]
  all_goals split <;> first | rw [put_size]; rfl | rfl

private theorem wbody_size (vc raw : Bool) (w h : Nat) (b : Band) (K : Nat)
    (cols : List (List (Nat × Nat))) (s : WidePlain.State) (i : Nat) :
    wideSize (WideModes.passBody vc raw w h b K cols s i) = wideSize s := by
  unfold WideModes.passBody
  split
  · exact fold_keep _ _ (fun t col => fold_keep _ _ (wprop_size raw w _ b _) col t) cols s
  · exact fold_keep _ _ (fun t col => fold_keep _ _ (wref_size raw w _ _) col t) cols s
  · simp only [wideSize, Array.size_map]
    exact fold_keep wideSize _ (fun t col => wcol_size w _ b _ t col) cols s

private theorem wplain_size (w h : Nat) (b : Band) (K : Nat)
    (cols : List (List (Nat × Nat))) (s : WidePlain.State) (i : Nat) :
    wideSize (WidePlain.runPass w h b K cols s i) = wideSize s := by
  unfold WidePlain.runPass
  split
  · exact fold_keep _ _ (fun t col => fold_keep _ _ (wprop_size false w h b _) col t) cols s
  · exact fold_keep _ _ (fun t col => fold_keep _ _ (wref_size false w h _) col t) cols s
  · simp only [wideSize, Array.size_map]
    exact fold_keep wideSize _ (wcol_size w h b _) cols s

private theorem wmode_size (m : Style) (w h : Nat) (b : Band) (K : Nat)
    (cols : List (List (Nat × Nat))) (s : WideModes.State) (i : Nat) :
    wideSize (WideModes.runPass m w h b K cols s i).block = wideSize s.block := by
  unfold WideModes.runPass; dsimp only
  split <;> split <;> exact wbody_size ..

/-- Both wide segment drivers preserve the backing raster length at every event. -/
theorem wide_storage (data : ByteArray) (w h : Nat) (b : Band) (K : Nat) (m : Style)
    (events : List Event) (s : WidePlain.State) (t : WideModes.State) :
    ((events.foldl (plainEvent data w h b K) s).cells.size = s.cells.size) ∧
      ((events.foldl (wideEvent m data w h b K) t).block.cells.size = t.block.cells.size) := by
  constructor
  · exact fold_keep wideSize _ (fun a e => by cases e <;> first | rfl | exact wplain_size ..) _ _
  · exact fold_keep (fun a : WideModes.State => wideSize a.block) _
      (fun a e => by cases e <;> first | rfl | exact wmode_size ..) _ _

private abbrev compactSize (s : St) := (s.flags.size, s.mags.size)

private theorem set_size (a : Array UInt32) (i : Nat) (v : UInt32) :
    (fset a i v).size = a.size := by unfold fset; split <;> simp

private theorem add_size (a : Array UInt32) (i : Nat) (v : UInt32) :
    (fadd a i v).size = a.size := set_size ..

private theorem setSig_size (g : Geo) (vc : Bool) (one : UInt32) (vis neg : Bool)
    (mq : JPEG2000.MQ.Dec) (fl mags : Array UInt32) (i : Nat) :
    compactSize (setSig g vc one vis neg mq fl mags i) = (fl.size, mags.size) := by
  simp only [setSig, compactSize, add_size, set_size]
  split <;> first | rfl | simp only [add_size, set_size]

private theorem sig_size (g : Geo) (one : UInt32) (v : Bool) (s : St) (i : Nat) :
    compactSize (becomeSig g one v s i) = compactSize s := by
  simp only [becomeSig, compactSize, add_size, set_size]

private theorem sigM_size (g : Geo) (vc : Bool) (one : UInt32) (v : Bool) (s : St) (i : Nat) :
    compactSize (becomeSigM g vc one v s i) = compactSize s := setSig_size ..

private theorem c_zero (g : Geo) (one : UInt32) (v : Bool) (s : St) (i : Nat) :
    compactSize (zeroCode g one v s i) = compactSize s := by
  unfold zeroCode; dsimp only; split
  · exact sig_size ..
  · split <;> first | rfl | simp only [compactSize, set_size]

private theorem c_zeroM (g : Geo) (vc : Bool) (one : UInt32) (v : Bool) (s : St) (i : Nat) :
    compactSize (zeroCodeM g vc one v s i) = compactSize s := by
  unfold zeroCodeM; dsimp only; split
  · exact sigM_size ..
  · split <;> first | rfl | simp only [compactSize, set_size]

private theorem row_size (step : St → Nat → St)
    (same : ∀ s i, compactSize (step s i) = compactSize s) (st : Nat) (k : Nat) (s : St) (i : Nat) :
    compactSize (colRows step st k s i) = compactSize s := by
  induction k generalizing s i with
  | zero => rfl
  | succ k ih => exact (ih (step s i) (i + st)).trans (same s i)

private theorem scan_size (g : Geo) (col : St → Nat → Nat → St)
    (same : ∀ s i r, compactSize (col s i r) = compactSize s) (s : St) :
    compactSize (scanBlock col g s) = compactSize s := by
  have cols (r k : Nat) (t : St) (i : Nat) : compactSize (scanCols col r k t i) = compactSize t := by
    induction k generalizing t i with
    | zero => rfl
    | succ k ih => exact (ih _ _).trans (same t i r)
  have stripes (k : Nat) (t : St) (y : Nat) : compactSize (scanStripes col g k t y) = compactSize t := by
    induction k generalizing t y with
    | zero => rfl
    | succ k ih => exact (ih _ _).trans (cols _ _ _ _)
  exact stripes _ s 0

private theorem clear_size (s : St) : compactSize (clearVis s) = compactSize s := by
  have from_ (k : Nat) (fl : Array UInt32) (i : Nat) : (clearVisFrom fl k i).size = fl.size := by
    induction k generalizing fl i with
    | zero => rfl
    | succ k ih => exact (ih _ _).trans (set_size ..)
  simp only [compactSize, clearVis, from_]

private theorem refine_storage (one : UInt32) (s : St) (i : Nat) :
    compactSize (mrStep one s i) = compactSize s ∧ compactSize (rawMrStep one s i) = compactSize s := by
  constructor <;> simp only [mrStep, rawMrStep] <;> split <;> try rfl
  all_goals simp only [compactSize, set_size]; split <;> first | rfl | simp only [set_size]

private theorem raw_storage (g : Geo) (vc : Bool) (one : UInt32) (s : St) (i : Nat) :
    compactSize (rawSpStep g vc one s i) = compactSize s := by
  unfold rawSpStep; dsimp only; split <;> try rfl
  split
  · exact setSig_size ..
  · exact Prod.ext (set_size ..) rfl

private theorem compact_pass_storage (g : Geo) (m : Style) (K : Nat) (s : St) (bad i : Nat) :
    compactSize (JPEG2000.Tier1.runPass g K s i) = compactSize s ∧
      compactSize (runPassM m g K s bad i).1 = compactSize s := by
  let one := (1 : UInt32) <<< (passPlane K i).toUInt32
  have prop : ∀ t, compactSize (sigPropPass g one t) = compactSize t := by
    apply scan_size
    intro t j r; unfold spCol; split <;> try rfl
    apply row_size
    intro a x; unfold spStep; dsimp only; split <;> first | exact c_zero .. | rfl
  have propM : ∀ t, compactSize (sigPropPassM g m.vertCausal one t) = compactSize t := by
    apply scan_size
    intro t j r; unfold spColM; split <;> try rfl
    apply row_size
    intro a x; unfold spStepM; dsimp only; split <;> first | exact c_zeroM .. | rfl
  have rawP : ∀ t, compactSize (rawSigPropPass g m.vertCausal one t) = compactSize t := by
    apply scan_size
    intro t j r; unfold rawSpCol; split <;> try rfl
    exact row_size _ (raw_storage g m.vertCausal one) _ _ _ _
  have ref : ∀ t, compactSize (magRefPass g one t) = compactSize t := by
    apply scan_size
    intro t j r; unfold mrCol; split <;> try rfl
    exact row_size _ (fun a x => (refine_storage one a x).1) _ _ _ _
  have rawR : ∀ t, compactSize (rawMagRefPass g one t) = compactSize t := by
    apply scan_size
    intro t j r; unfold rawMrCol; split <;> try rfl
    exact row_size _ (fun a x => (refine_storage one a x).2) _ _ _ _
  have clean : ∀ t, compactSize (cleanupPass g one t) = compactSize t := by
    intro t; rw [cleanupPass, clear_size]; apply scan_size
    intro a j r
    have step (z : St) (x : Nat) : compactSize (cuStep g one z x) = compactSize z := by
      unfold cuStep; dsimp only; split <;> first | exact c_zero .. | rfl
    unfold cuCol; dsimp only
    split
    · split <;> first | rfl | exact (row_size _ step ..).trans (sig_size ..)
    · exact row_size _ step ..
  have cleanM : ∀ t, compactSize (cleanupPassM g m.vertCausal one t) = compactSize t := by
    intro t; rw [cleanupPassM, clear_size]; apply scan_size
    intro a j r
    have step (z : St) (x : Nat) : compactSize (cuStepM g m.vertCausal one z x) = compactSize z := by
      unfold cuStepM; dsimp only; split <;> first | exact c_zeroM .. | rfl
    unfold cuColM; dsimp only
    split
    · split <;> first | rfl | exact (row_size _ step ..).trans (sigM_size ..)
    · exact row_size _ step ..
  constructor
  · unfold JPEG2000.Tier1.runPass; split <;> first | exact prop s | exact ref s | exact clean s
  · unfold runPassM; dsimp only; split <;> split <;> split <;> split <;>
      first | exact propM s | exact rawP s | exact ref s | exact rawR s | exact cleanM s

/-- Both bordered arrays retain their allocation domains at each compact pass and restart. -/
theorem compact_storage (m : Style) (g : Geo) (K : Nat) (data : ByteArray) (events : List Event)
    (passes : List Nat) (s : St) (bad : Nat) :
    compactSize (passes.foldl (JPEG2000.Tier1.runPass g K) s) = compactSize s ∧
      compactSize ((events.foldl (compactEvent m g K data) (s, bad)).1) = compactSize s := by
  constructor
  · exact fold_keep _ _ (fun t i => (compact_pass_storage g m K t 0 i).1) _ _
  · exact fold_keep (fun t : St × Nat => compactSize t.1) _ (fun t e => by
      cases e with
      | restart => rfl
      | pass i => exact (compact_pass_storage g m K t.1 t.2 i).2) _ _

end JPEG2000.Spec.Resources.Tier1Work
