import Spec.Resources.Tier1CompactWork

/-!
# Segment and pass traversal (Plan.md §§3–5, 7, S3; T.800 A.6.1, D.1–D.7)

An explicit schedule records each reader restart and absolute pass number. Folding the
production kernels over it gives the original wide and compact loops, including the
compact single-codeword loop. Truncation is applied once to the entire block.
-/

namespace JPEG2000.Spec.Resources.Tier1Work

open JPEG2000 JPEG2000.Tier1 JPEG2000.Tier2.Geometry

/-- A D.4 reader restart or one D.2 pass. Both carry the absolute pass number. -/
inductive Event where
  | restart (seg : Seg) (first : Nat)
  | pass (i : Nat)

/-- Events for the supplied pass prefix, starting at the given absolute pass number. -/
def schedule : List Seg → Nat → List Event
  | [], _ => []
  | sg :: rest, first => .restart sg first ::
      ((List.range' first sg.passes).map Event.pass ++ schedule rest (first + sg.passes))

/-- The exact sequence of pass indices and the number of reader restarts. -/
theorem schedule_counts (segs : List Seg) (first : Nat) :
    ((schedule segs first).filterMap fun | .pass i => some i | _ => none) =
      List.range' first (segs.map (·.passes)).sum ∧
    (schedule segs first).length = segs.length + (segs.map (·.passes)).sum := by
  induction segs generalizing first with
  | nil => simp [schedule]
  | cons sg rest ih =>
    obtain ⟨H, L⟩ := ih (first + sg.passes)
    simp only [schedule, List.filterMap_cons, List.filterMap_append, List.filterMap_map,
      List.length_cons, List.length_append, List.length_map, List.length_range',
      List.map_cons, List.sum_cons, H, L]
    constructor
    · simp [Function.comp_def]
    · omega

/-- Steps for the plain wide codeword sequence. Restart carries coefficients and contexts. -/
def plainEvent (data : ByteArray) (w h : Nat) (b : Band) (K : Nat) (s : WidePlain.State) :
    Event → WidePlain.State
  | .restart sg _ => { s with mq := JPEG2000.MQ.Dec.init data sg.start sg.stop s.mq.cx }
  | .pass i => WidePlain.runPass w h b K (WidePlain.columns w h) s i

/-- Steps for the wide decoder with any Table A.19 style. -/
def wideEvent (m : Style) (data : ByteArray) (w h : Nat) (b : Band) (K : Nat)
    (s : WideModes.State) : Event → WideModes.State
  | .restart sg first => WideSegments.restart m data sg first s
  | .pass i => WideModes.runPass m w h b K (WidePlain.columns w h) s i

/-- Steps for the segmented compact decoder, including its D.5 error counter. -/
def compactEvent (m : Style) (g : Geo) (K : Nat) (data : ByteArray)
    (s : St × Nat) : Event → St × Nat
  | .restart sg first => (startSegment m data s.1 first sg, s.2)
  | .pass i => runPassM m g K s.1 s.2 i

/-- The scheduled fold is the plain wide production loop, including the final cell array. -/
theorem plain_schedule (data : ByteArray) (w h : Nat) (b : Band) (K : Nat) (segs : List Seg)
    (first : Nat) (s : WidePlain.State) :
    WidePlain.runSegments data w h b K segs first s =
      ((schedule segs first).foldl (plainEvent data w h b K) s).cells := by
  induction segs generalizing first s with
  | nil => rfl
  | cons sg rest ih =>
    simp only [WidePlain.runSegments, schedule, List.foldl_cons, List.foldl_append, List.foldl_map, ih]
    rfl

/-- The scheduled fold is the wide mode-aware production loop. -/
theorem wide_schedule (m : Style) (data : ByteArray) (w h : Nat) (b : Band) (K : Nat)
    (segs : List Seg) (first : Nat) (s : WideModes.State) :
    WideSegments.runSegments m data w h b K (WidePlain.columns w h) segs first s =
      (schedule segs first).foldl (wideEvent m data w h b K) s := by
  induction segs generalizing first s with
  | nil => rfl
  | cons sg rest ih =>
    simp only [WideSegments.runSegments, schedule, List.foldl_cons, List.foldl_append, List.foldl_map, ih]
    rfl

/-- The compact plain fast loop runs exactly the absolute indices in its supplied prefix. -/
theorem compact_plain_schedule (g : Geo) (K n : Nat) (s : St) (first : Nat) :
    runPasses g K n s first = (List.range' first n).foldl (JPEG2000.Tier1.runPass g K) s := by
  induction n generalizing first s with
  | zero => rfl
  | succ n ih => simp only [runPasses, List.range'_succ, List.foldl_cons, ih]

private theorem compact_passes (m : Style) (g : Geo) (K n : Nat) (s : St × Nat) (i : Nat) :
    runPassesM m g K n s.1 s.2 i =
      (List.range' i n).foldl (fun t j => runPassM m g K t.1 t.2 j) s := by
  induction n generalizing i s with
  | zero => rfl
  | succ n ih =>
    simpa only [runPassesM, List.range'_succ, List.foldl_cons] using
      ih (runPassM m g K s.1 s.2 i) (i + 1)

private theorem compact_from (m : Style) (g : Geo) (K : Nat) (data : ByteArray) (segs : Array Seg)
    (xs : List Seg) (j first : Nat) (s : St × Nat) (hj : segs.toList.drop j = xs) :
    runSegs m g K data segs xs.length j s.1 s.2 first =
      (schedule xs first).foldl (compactEvent m g K data) s := by
  induction xs generalizing first j s with
  | nil => rfl
  | cons sg rest ih =>
    obtain ⟨hd, ht⟩ := Tier1EquivM.getD_of_drop _ _ _ _ hj
    simp only [List.length_cons, runSegs, hd, schedule, List.foldl_cons, List.foldl_append,
      List.foldl_map, compactEvent]
    let t := (startSegment m data s.1 first sg, s.2)
    rw [← compact_passes m g K sg.passes t first]
    exact ih _ _ _ ht

/-- The production indexed array loop restarts exactly once for each retained segment. -/
theorem compact_schedule (m : Style) (g : Geo) (K : Nat) (data : ByteArray) (segs : Array Seg)
    (first : Nat) (s : St × Nat) :
    runSegs m g K data segs segs.size 0 s.1 s.2 first =
      (schedule segs.toList first).foldl (compactEvent m g K data) s := by
  exact compact_from m g K data segs _ 0 first s (by simp)

private theorem trunc_shape (segs : List Seg) (n : Nat) :
    ((truncSegs segs n).map (·.passes)).sum = min n (segs.map (·.passes)).sum ∧
      (truncSegs segs n).length ≤ segs.length := by
  induction segs generalizing n with
  | nil => simp [truncSegs]
  | cons sg rest ih =>
    have := ih (n - sg.passes)
    simp only [truncSegs, List.map_cons, List.sum_cons, List.length_cons]
    split
    · simp [*]
    · split <;> simp only [List.length_cons, List.length_nil, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil] <;> omega

/-- Exact global pass prefix and segment-visit bound, including discarded and zero-pass
segments on malformed input. This holds before segment-style validation succeeds. -/
theorem clamp_shape (segs : Array Seg) (K : Nat) :
    segsPasses (clampSegs segs K) = min (segsPasses segs) (3 * K - 2) ∧
      (clampSegs segs K).size ≤ segs.size := by
  unfold clampSegs
  split
  · simp [Nat.min_eq_left (by assumption : segsPasses segs ≤ _)]
  · have ⟨hp, hs⟩ := trunc_shape segs.toList (3 * K - 2)
    simpa only [Tier1EquivM.segsPasses_eq, List.toList_toArray, List.size_toArray,
      Array.length_toList, Nat.min_comm (3 * K - 2)] using And.intro hp hs

private theorem stripe_shape (w h first n : Nat) :
    let cols := (List.range' first n).flatMap fun s =>
      (List.range w).map fun x => (List.range (min 4 (h - 4 * s))).map fun r => (x, 4 * s + r)
    cols.flatten.length = w * min (4 * n) (h - 4 * first) ∧ cols.length = w * n := by
  induction n generalizing first with
  | zero => simp
  | succ n ih =>
    have ⟨hc, hl⟩ := ih (first + 1)
    simp only [List.range'_succ, List.flatMap_cons, List.flatten_append, List.length_append,
      List.length_flatten, List.length_map, List.length_range, List.map_map, Function.comp_def,
      List.map_const', List.sum_replicate_nat] at hc ⊢
    rw [hc, hl, ← Nat.mul_add]
    constructor
    · congr 1; omega
    · rw [Nat.mul_succ, Nat.add_comm]

/-- Exact structural domains of the wide stripe scans, including a short bottom stripe. -/
theorem stripe_domains (w h : Nat) :
    (WidePlain.columns w h).flatten.length = w * h ∧
      (WidePlain.columns w h).length = w * ((h + 3) / 4) := by
  unfold WidePlain.columns
  rw [List.range_eq_range' (n := (h + 3) / 4)]
  simpa only [Nat.mul_zero, Nat.sub_zero, Nat.min_eq_right (by omega : h ≤ 4 * ((h + 3) / 4))]
    using stripe_shape w h 0 ((h + 3) / 4)

private theorem column_sum (cols : List (List (Nat × Nat))) :
    columnBudget cols = cols.flatten.length * 6 + cols.length * 8 := by
  induction cols with
  | nil => rfl
  | cons c cs ih =>
    change c.length * 6 + 8 + columnBudget cs = _
    simp only [ih, List.flatten_cons, List.length_append, List.length_cons]; omega

/-- The two representations share a pass budget for reader operations and cell/column
visits. It also covers the short last stripe and interrupted cleanup runs. -/
theorem column_budget (w h : Nat) : columnBudget (WidePlain.columns w h) = passBudget w h := by
  obtain ⟨hc, hs⟩ := stripe_domains w h
  rw [column_sum, hc, hs, passBudget, Nat.mul_add, Nat.mul_assoc, Nat.mul_assoc]

end JPEG2000.Spec.Resources.Tier1Work
