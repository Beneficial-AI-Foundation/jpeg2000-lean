import Spec.Resources.Tier1Storage

/-!
# Metered Tier-1 segment execution (Plan.md §§3–5, 7, S3; T.800 D.1–D.7)

The meter threads the production state and charges the trace built from each actual pass.
It also charges the D.1 column/position domains, pass dispatch, cleanup array slots and
reader restarts. A charge is a structural operation, independent of machine timings.
-/

namespace JPEG2000.Spec.Resources.Tier1Work

open JPEG2000 JPEG2000.Tier1 JPEG2000.Tier2.Geometry

/-- Stripe, column and raster slots generated when the wide decoder materialises its scan.
The stripe term also covers zero width. -/
def columnSetup (w h : Nat) := (h + 3) / 4 + w * ((h + 3) / 4) + w * h

/-- Charge for one pass, including its range-list entry, dispatch, compact stripe loop
(even at zero width), and the clearing scan. -/
def passCharge (w h clearSlots : Nat) := passBudget w h + 7 + (h + 3) / 4 + clearSlots

/-- State, with the work charged along the actual absolute-pass schedule. -/
def measureEvents {σ : Type} (step : σ → Event → σ) (charge : σ → Event → Nat) :
    List Event → σ → σ × Nat
  | [], s => (s, 0)
  | e :: es, s =>
    let (t, n) := measureEvents step charge es (step s e)
    (t, charge s e + n)

private theorem measure_value {σ : Type} (step : σ → Event → σ) (charge : σ → Event → Nat)
    (es : List Event) (s : σ) : (measureEvents step charge es s).1 = es.foldl step s := by
  induction es generalizing s with
  | nil => rfl
  | cons e es ih => exact ih _

private def allowance (restart pass : Nat) : Event → Nat
  | .restart .. => restart
  | .pass _ => pass

private theorem measure_le {σ : Type} (step : σ → Event → σ) (charge : σ → Event → Nat)
    (keep : σ → Prop) (stable : ∀ s e, keep s → keep (step s e)) (r p : Nat)
    (hb : ∀ s e, keep s → charge s e ≤ allowance r p e) (es : List Event) (s : σ) (hs : keep s) :
    (measureEvents step charge es s).2 ≤ (es.map (allowance r p)).sum := by
  induction es generalizing s with
  | nil => exact Nat.le_refl _
  | cons e es ih => exact Nat.add_le_add (hb s e hs) (ih _ (stable s e hs))

private theorem schedule_allowance (segs : List Seg) (first r p : Nat) :
    ((schedule segs first).map (allowance r p)).sum =
      r * segs.length + p * (segs.map (·.passes)).sum := by
  induction segs generalizing first with
  | nil => simp [schedule]
  | cons sg rest ih =>
    simp only [schedule, List.map_cons, List.sum_cons, List.length_cons, List.map_append,
      List.sum_append, ih, List.map_map, Function.comp_def, allowance, List.map_const',
      List.sum_replicate_nat, List.length_range', Nat.mul_add, Nat.mul_succ]
    rw [Nat.mul_comm sg.passes p]; omega

private def costOf {n : Nat} {a b : JPEG2000.MQ.Dec} (t : Reads n a b) := t.operations + t.slots

private def clearSlots (i size : Nat) := if passKind i == 2 then size else 0

private theorem clear_le (i n : Nat) : clearSlots i n ≤ n := by unfold clearSlots; split <;> omega

private def plainCost (w h : Nat) (b : Band) (K : Nat) (s : WidePlain.State) : Event → Nat
  | .restart .. => 1 + columnSetup w h
  | .pass i => costOf (plainPassReads w h b K (WidePlain.columns w h) s i) + 2 + clearSlots i s.cells.size

private def wideCost (m : Style) (w h : Nat) (b : Band) (K : Nat) (s : WideModes.State) : Event → Nat
  | .restart .. => 1
  | .pass i => costOf (widePassReads m w h b K (WidePlain.columns w h) s i) + 2 + clearSlots i s.block.cells.size

private def compactCost (m : Style) (g : Geo) (K : Nat) (s : St × Nat) : Event → Nat
  | .restart .. => 1
  | .pass i => costOf (compactModeReads m g K s.1 s.2 i) + 2 + (g.h + 3) / 4 + clearSlots i s.1.flags.size

/-- Production plain wide loop, metered with a column setup for each segment. -/
def measurePlain (data : ByteArray) (w h : Nat) (b : Band) (K : Nat) (segs : List Seg)
    (first : Nat) (s : WidePlain.State) : WidePlain.State × Nat :=
  measureEvents (plainEvent data w h b K) (plainCost w h b K) (schedule segs first) s

/-- Production all-style wide loop, metered with the once-per-block column setup. -/
def measureWide (m : Style) (data : ByteArray) (w h : Nat) (b : Band) (K : Nat) (segs : List Seg)
    (first : Nat) (s : WideModes.State) : WideModes.State × Nat :=
  let (out, n) := measureEvents (wideEvent m data w h b K) (wideCost m w h b K) (schedule segs first) s
  (out, columnSetup w h + n)

/-- Production segmented compact loop, metered against its two bordered arrays. -/
def measureCompact (m : Style) (g : Geo) (K : Nat) (data : ByteArray) (segs : Array Seg)
    (first : Nat) (s : St × Nat) : (St × Nat) × Nat :=
  measureEvents (compactEvent m g K data) (compactCost m g K) (schedule segs.toList first) s

/-- The meter follows the plain wide segment loop for every starting state and pass. -/
theorem plain_work (data : ByteArray) (w h : Nat) (b : Band) (K : Nat) (segs : List Seg)
    (first : Nat) (s : WidePlain.State) :
    let v := measurePlain data w h b K segs first s
    v.1.cells = WidePlain.runSegments data w h b K segs first s ∧
      v.2 ≤ (1 + columnSetup w h) * segs.length + passCharge w h s.cells.size * (segs.map (·.passes)).sum := by
  dsimp only [measurePlain]
  refine ⟨by rw [measure_value, plain_schedule], ?_⟩
  rw [← schedule_allowance segs first]
  apply measure_le _ _ (fun t => t.cells.size = s.cells.size) _ _ _ _ _ _ rfl
  · intro t e ht
    exact ((wide_storage data w h b K {} [e] t ⟨t, 0⟩).1).trans ht
  · intro t e ht; cases e with
    | restart => exact Nat.le_refl _
    | pass i =>
      have H := (plainPassReads w h b K (WidePlain.columns w h) t i).work_le
      have := column_budget w h
      have := clear_le i t.cells.size
      simp only [plainCost, allowance, passCharge, costOf]
      omega

/-- The mode-aware wide meter covers each visited segment, including raw/MQ restarts. -/
theorem wide_work (m : Style) (data : ByteArray) (w h : Nat) (b : Band) (K : Nat) (segs : List Seg)
    (first : Nat) (s : WideModes.State) :
    let v := measureWide m data w h b K segs first s
    v.1 = WideSegments.runSegments m data w h b K (WidePlain.columns w h) segs first s ∧
      v.2 ≤ columnSetup w h + (segs.length + passCharge w h s.block.cells.size * (segs.map (·.passes)).sum) := by
  dsimp only [measureWide]
  refine ⟨by rw [measure_value, wide_schedule], Nat.add_le_add_left ?_ _⟩
  rw [← Nat.one_mul segs.length, ← schedule_allowance segs first]
  apply measure_le _ _ (fun t => t.block.cells.size = s.block.cells.size) _ _ _ _ _ _ rfl
  · intro t e ht
    exact ((wide_storage data w h b K m [e] t.block t).2).trans ht
  · intro t e ht; cases e with
    | restart => exact Nat.le_refl _
    | pass i =>
      have H := (widePassReads m w h b K (WidePlain.columns w h) t i).work_le
      have := column_budget w h
      have := clear_le i t.block.cells.size
      simp only [wideCost, allowance, passCharge, costOf]
      omega

/-- The segmented compact meter returns the actual pass state and D.5 count. -/
theorem compact_work (m : Style) (g : Geo) (K : Nat) (data : ByteArray) (segs : Array Seg)
    (first : Nat) (s : St × Nat) :
    let v := measureCompact m g K data segs first s
    v.1 = runSegs m g K data segs segs.size 0 s.1 s.2 first ∧
      v.2 ≤ segs.size + passCharge g.w g.h s.1.flags.size * segsPasses segs := by
  dsimp only [measureCompact]
  refine ⟨by rw [measure_value, compact_schedule], ?_⟩
  rw [Tier1EquivM.segsPasses_eq, ← Array.length_toList, ← Nat.one_mul segs.toList.length,
    ← schedule_allowance segs.toList first]
  apply measure_le _ _ (fun t => t.1.flags.size = s.1.flags.size) _ _ _ _ _ _ rfl
  · intro t e ht
    exact (congrArg Prod.fst (compact_storage m g K data [e] [] t.1 t.2).2).trans ht
  · intro t e ht; cases e with
    | restart => exact Nat.le_refl _
    | pass i =>
      have H := (compactModeReads m g K t.1 t.2 i).work_le
      have := clear_le i t.1.flags.size
      simp only [compactCost, allowance, passCharge, costOf]
      omega

/-- Meter of the compact plain recursion, following the same `i+1` tail calls. -/
def measureFast (g : Geo) (K : Nat) : Nat → St → Nat → St × Nat
  | 0, s, _ => (s, 0)
  | n + 1, s, i =>
    let (out, rest) := measureFast g K n (JPEG2000.Tier1.runPass g K s i) (i + 1)
    (out, costOf (compactPlainReads g K s i) + 2 + (g.h + 3) / 4 + clearSlots i s.flags.size + rest)

/-- The compact single-codeword meter returns the fast-loop result and bounds every pass. -/
theorem fast_work (g : Geo) (K n : Nat) (s : St) (first : Nat) :
    let v := measureFast g K n s first
    v.1 = runPasses g K n s first ∧ v.2 ≤ passCharge g.w g.h s.flags.size * n := by
  induction n generalizing s first with
  | zero => simp [measureFast, runPasses]
  | succ n ih =>
    obtain ⟨eq, le⟩ := ih (JPEG2000.Tier1.runPass g K s first) (first + 1)
    have H : (JPEG2000.Tier1.runPass g K s first).flags.size = s.flags.size :=
      congrArg Prod.fst (compact_storage {} g K default [] [first] s 0).1
    rw [H] at le
    refine ⟨eq, ?_⟩
    dsimp only [measureFast]; rw [Nat.mul_succ]
    have hread := (compactPlainReads g K s first).work_le
    have hclear := clear_le first s.flags.size
    unfold passCharge costOf at *
    omega

end JPEG2000.Spec.Resources.Tier1Work
