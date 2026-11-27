import Spec.Resources.Tier1Schedule

/-!
# Tier-1 preflight and rejection (Plan.md §§3–5, 7, S3; T.800 A.6.1, D.2, D.4)

Count range predicates until the first invalid range, segment traversal until the last
retained pass, and iterations of the prescribed D.4 partition. Charge full lengths for
array/list conversions, pass-count sums and comparison. A rejected call ends here.
-/

namespace JPEG2000.Spec.Resources.Tier1Work

open JPEG2000 JPEG2000.Tier1

private def rangeScan (data : ByteArray) : List Seg → Bool × Nat
  | [] => (false, 0)
  | sg :: rest => if sg.start > sg.stop || sg.stop > data.size then (true, 1)
    else let t := rangeScan data rest; (t.1, 1 + t.2)

private theorem range_spec (data : ByteArray) (xs : List Seg) :
    (rangeScan data xs).1 = xs.any (fun sg => sg.start > sg.stop || sg.stop > data.size) ∧
      (rangeScan data xs).2 ≤ xs.length := by
  induction xs with
  | nil => exact ⟨rfl, Nat.le_refl _⟩
  | cons x xs ih =>
    simp only [rangeScan, List.any_cons, List.length_cons]
    split <;> simp_all <;> omega

private def cut : List Seg → Nat → List Seg × Nat
  | [], _ => ([], 0)
  | sg :: rest, n =>
    if n = 0 then ([], 1)
    else if n ≤ sg.passes then ([{sg with passes := n}], 1)
    else let t := cut rest (n - sg.passes); (sg :: t.1, 1 + t.2)

private theorem cut_spec (xs : List Seg) (n : Nat) :
    (cut xs n).1 = truncSegs xs n ∧ (cut xs n).2 ≤ xs.length := by
  induction xs generalizing n with
  | nil => exact ⟨rfl, Nat.le_refl _⟩
  | cons sg xs ih =>
    simp only [cut, truncSegs, List.length_cons]
    have ⟨a, b⟩ := ih (n - sg.passes)
    by_cases z : n = 0 <;> by_cases k : n ≤ sg.passes <;> simp [z, k, a] <;> omega

private def clamp (segs : Array Seg) (K : Nat) : Array Seg × Nat :=
  if segsPasses segs ≤ 3 * K - 2 then (segs, segs.size)
  else let t := cut segs.toList (3 * K - 2)
       (t.1.toArray, 2 * segs.size + t.2 + t.1.length)

private theorem clamp_spec (segs : Array Seg) (K : Nat) :
    (clamp segs K).1 = clampSegs segs K ∧ (clamp segs K).2 ≤ 4 * segs.size := by
  have H := (clamp_shape segs K).2
  unfold clamp clampSegs at *
  split <;> simp_all only [↓reduceIte, List.size_toArray]
  · exact ⟨trivial, by omega⟩
  · obtain ⟨a, b⟩ := cut_spec segs.toList (3 * K - 2)
    simp only [Array.length_toList] at b
    rw [a]; exact ⟨rfl, by omega⟩

private def runs (m : Style) : (n i cur : Nat) → List Nat × Nat
  | 0, _, cur => (if cur = 0 then [] else [cur], 0)
  | n + 1, i, cur =>
    if passEndsSegment m i then
      let t := runs m n (i + 1) 0; ((cur + 1) :: t.1, 1 + t.2)
    else let t := runs m n (i + 1) (cur + 1); (t.1, 1 + t.2)

private theorem runs_spec (m : Style) (n i cur : Nat) :
    (runs m n i cur).1 = segmentRuns m n i cur ∧ (runs m n i cur).2 = n ∧
      (runs m n i cur).1.length ≤ n + (if cur = 0 then 0 else 1) := by
  induction n generalizing i cur with
  | zero => simp only [runs, segmentRuns]; split <;> simp
  | succ n ih =>
    simp only [runs, segmentRuns]; split
    · obtain ⟨eq, len, hlen⟩ := ih (i + 1) 0
      simp_all; omega
    · obtain ⟨eq, len, hlen⟩ := ih (i + 1) (cur + 1)
      simp_all; omega

private def malformed {α : Type} (msg : String) : Except Error α := .error (.malformed tier1Loc msg)

/-- Measured validation of a retained segment list. The second range check belongs only
to the compact decoder. Wide plain styles use the plain D.4 partition. -/
def checkKept (wide : Bool) (data : ByteArray) (kept : Array Seg) (w h : Nat) (m : Style) (K : Nat) :
    Except Error Unit × Nat :=
  let n := segsPasses kept
  let base := kept.size + 4
  if w > 1024 ∨ h > 1024 ∨ w * h > 4096 then
    (malformed "code-block larger than 1024 x 1024 or 4096 coefficients", base)
  else
  if wide && 0 < n && WidePlain.maxCodedPlanes < K then
    (malformed "coded bit-plane count exceeds the E-2 and RGN header fields", base)
  else
  if 0 < n ∧ 3 * K - 2 < n then
    (malformed "more coding passes than 3K - 2 for K coded bit-planes", base)
  else
  let mode := if wide && m.decodesAsPlain then {} else m
  let shape := runs mode n 0 0
  let bill := base + 3 * kept.size + shape.2 + shape.1.length
  if kept.toList.map (·.passes) != shape.1 then
    (malformed "codeword segments do not match the code-block style", bill)
  else
  if wide then (.ok (), bill) else
  let rg := rangeScan data kept.toList
  if rg.1 then (malformed "code-block data range outside the buffer", bill + rg.2) else
  if 0 < n ∧ 31 < K then
    (.error (.unsupported tier1Loc "more than 31 coded bit-planes"), bill + rg.2)
  else
  (.ok (), bill + rg.2)

private theorem kept_compact (data : ByteArray) (kept : Array Seg) (w h : Nat) (m : Style) (K : Nat) :
    (checkKept false data kept w h m K).1 = validateSegs data kept w h m K := by
  simp only [checkKept, validateSegs, bind, pure, Except.bind, Except.pure, throw, throwThe, MonadExceptOf.throw,
     Bool.false_and, Bool.false_eq_true, ↓reduceIte, (runs_spec ..).1,
    (range_spec ..).1, Array.any_toList, segmentPasses]
  repeat' first | rfl | contradiction | split
  all_goals simp only [*, ↓reduceIte, malformed]

private theorem kept_wide (data : ByteArray) (kept : Array Seg) (w h : Nat) (m : Style) (K : Nat)
    (sz : ¬ (w > 1024 ∨ h > 1024 ∨ w * h > 4096)) :
    (checkKept true data kept w h m K).1 =
      WideSegments.validatePasses (if m.decodesAsPlain then {} else m) kept K := by
  simp only [checkKept, WideSegments.validatePasses, sz, bind, pure, Except.bind, Except.pure, throw, throwThe, MonadExceptOf.throw,
     Bool.true_and, Bool.and_eq_true, decide_eq_true_eq, ↓reduceIte, (runs_spec ..).1,
    segmentPasses]
  repeat' first | rfl | contradiction | split

private theorem kept_cost (wide : Bool) (data : ByteArray) (kept : Array Seg) (w h : Nat) (m : Style) (K : Nat) :
    (checkKept wide data kept w h m K).2 ≤ 5 * kept.size + 2 * segsPasses kept + 4 := by
  have ⟨_, H, P⟩ := runs_spec (if wide && m.decodesAsPlain then {} else m) (segsPasses kept) 0 0
  have R := (range_spec data kept.toList).2
  simp only [Array.length_toList] at R
  simp only [↓reduceIte, Nat.add_zero] at P
  unfold checkKept
  dsimp only
  generalize (if (wide && m.decodesAsPlain) = true then {} else m) = mode at *
  repeat' first | omega | split

/-- Preflight from the original segment array. An invalid discarded range is still seen.
Wide geometry failure precedes clamping. Compact clamping precedes its geometry check. -/
def preflight (wide : Bool) (data : ByteArray) (segs : Array Seg) (w h : Nat) (m : Style) (K : Nat) :
    Except Error (Array Seg) × Nat :=
  let rg := rangeScan data segs.toList
  if rg.1 then (malformed "code-block data range outside the buffer", rg.2) else
  if wide && (w > 1024 || h > 1024 || w * h > 4096) then
    (malformed "code-block larger than 1024 x 1024 or 4096 coefficients", rg.2 + 1)
  else
  let kept := clamp segs K
  let test := checkKept wide data kept.1 w h m K
  (test.1.map (fun _ => kept.1), rg.2 + kept.2 + test.2 + 1)

/-- A reversed or out-of-buffer original range stops the call after at most one range
test per supplied segment, including when the offending range would have been discarded. -/
theorem bad_range_work {data : ByteArray} {segs : Array Seg} (bad : badRange data segs = true)
    (wide : Bool) (w h : Nat) (m : Style) (K : Nat) :
    (preflight wide data segs w h m K).1 =
      .error (.malformed tier1Loc "code-block data range outside the buffer") ∧
    (preflight wide data segs w h m K).2 ≤ segs.size := by
  obtain ⟨v, n⟩ := range_spec data segs.toList
  rw [Array.any_toList] at v
  have stop : (rangeScan data segs.toList).1 = true := v.trans bad
  simp only [preflight, stop, ↓reduceIte, malformed, true_and]
  simpa only [Array.length_toList] using n

/-- On a compact call preflight reproduces the checks preceding its first raster allocation. -/
theorem compact_preflight (data : ByteArray) (segs : Array Seg) (w h : Nat) (m : Style) (K : Nat) :
    (preflight false data segs w h m K).1 =
      if badRange data segs then malformed "code-block data range outside the buffer"
      else (validateSegs data (clampSegs segs K) w h m K).map (fun _ => clampSegs segs K) := by
  simp only [preflight, badRange, (range_spec ..).1, Array.any_toList,
    Bool.false_and, Bool.false_eq_true, ↓reduceIte, (clamp_spec ..).1, kept_compact]
  split <;> simp only [*, ↓reduceIte, Bool.false_eq_true]

/-- The wide preflight preserves the original error order and selects the plain partition
on the specialised path. -/
theorem wide_preflight (data : ByteArray) (segs : Array Seg) (w h : Nat) (m : Style) (K : Nat) :
    (preflight true data segs w h m K).1 =
      (do
        if badRange data segs then return ← malformed "code-block data range outside the buffer"
        WidePlain.validateSize w h
        let kept := clampSegs segs K
        WideSegments.validatePasses (if m.decodesAsPlain then {} else m) kept K
        return kept) := by
  simp only [preflight, WidePlain.validateSize, bind, pure, Except.bind,
    Except.pure, badRange, (range_spec ..).1, Array.any_toList, Bool.true_and, Bool.or_eq_true,
    decide_eq_true_eq, (clamp_spec ..).1]
  split <;> simp only [*, ↓reduceIte]
  by_cases sz : w > 1024 ∨ h > 1024 ∨ w * h > 4096
  · have H : (w > 1024 ∨ h > 1024) ∨ w * h > 4096 := by omega
    simp only [sz, H, ↓reduceIte]; rfl
  · have H : ¬ ((w > 1024 ∨ h > 1024) ∨ w * h > 4096) := by omega
    simp only [sz, H, ↓reduceIte, kept_wide _ _ _ _ _ _ sz]
    cases WideSegments.validatePasses (if m.decodesAsPlain then {} else m) (clampSegs segs K) K <;> rfl

/-- Structural validation charge, valid on all rejection paths. The only pass-driven
validation recursion uses the globally retained prefix, even if the style is malformed. -/
theorem preflight_work (wide : Bool) (data : ByteArray) (segs : Array Seg) (w h : Nat) (m : Style) (K : Nat) :
    (preflight wide data segs w h m K).2 ≤ 10 * segs.size + 2 * min (segsPasses segs) (3 * K - 2) + 5 := by
  have R := (range_spec data segs.toList).2
  simp only [Array.length_toList] at R
  obtain ⟨E, C⟩ := clamp_spec segs K
  obtain ⟨P, S⟩ := clamp_shape segs K
  have B := kept_cost wide data (clampSegs segs K) w h m K
  simp only [preflight, E]
  repeat' first | omega | split

/-- A successful preflight identifies the exact retained array and proves the geometry
and active-plane checks used by both allocation and pass-loop estimates. -/
theorem preflight_ok {wide : Bool} {data : ByteArray} {segs kept : Array Seg} {w h K : Nat}
    {m : Style} (ok : (preflight wide data segs w h m K).1 = .ok kept) :
    kept = clampSegs segs K ∧ w ≤ 1024 ∧ h ≤ 1024 ∧ w * h ≤ 4096 ∧
      (0 < segsPasses kept → K ≤ if wide then 292 else 31) := by
  simp only [preflight, (clamp_spec ..).1] at ok
  split at ok <;> try contradiction
  split at ok <;> try contradiction
  cases hv : (checkKept wide data (clampSegs segs K) w h m K).1 with
  | error e => simp [hv, Except.map] at ok
  | ok a =>
    simp only [hv, Except.map, Except.ok.injEq] at ok
    subst kept
    refine ⟨rfl, ?_⟩
    unfold checkKept at hv
    dsimp only at hv
    split at hv <;> try contradiction
    rename_i sz
    refine ⟨by omega, by omega, by omega, ?_⟩
    intro positive
    cases wide
    · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hv ⊢
      repeat' split at hv <;> try contradiction
      all_goals omega
    · simp only [Bool.true_and, Bool.and_eq_true, decide_eq_true_eq, positive, true_and,
        ↓reduceIte, WidePlain.maxCodedPlanes] at hv ⊢
      split at hv <;> try contradiction
      rename_i bound
      exact Nat.le_of_not_gt (fun hk => bound (decide_eq_true hk))

private theorem kept_segments {wide : Bool} {data : ByteArray} {kept : Array Seg} {w h K : Nat}
    {m : Style} (ok : (checkKept wide data kept w h m K).1 = .ok ()) :
    kept.size ≤ segsPasses kept := by
  let mode := if wide && m.decodesAsPlain then {} else m
  obtain ⟨_, _, hlen⟩ := runs_spec mode (segsPasses kept) 0 0
  simp only [↓reduceIte, Nat.add_zero] at hlen
  have shape : kept.toList.map (·.passes) = (runs mode (segsPasses kept) 0 0).1 := by
    unfold checkKept at ok
    dsimp only at ok
    split at ok <;> try contradiction
    split at ok <;> try contradiction
    split at ok <;> try contradiction
    by_cases H : kept.toList.map (·.passes) = (runs mode (segsPasses kept) 0 0).1
    · exact H
    · simp [mode] at H
      simp [H, malformed] at ok
  simpa only [← shape, List.length_map, Array.length_toList] using hlen

/-- Exact pass prefix and allocation domains after validation. The total restart count of the
accepted D.4 partition is bounded by its pass count. Compact active blocks use at most 91
passes and wide blocks at most 874. The compact border includes narrow or empty rasters. -/
theorem preflight_domains {wide : Bool} {data : ByteArray} {segs kept : Array Seg}
    {w h K : Nat} {m : Style} (ok : (preflight wide data segs w h m K).1 = .ok kept) :
    segsPasses kept = min (segsPasses segs) (3 * K - 2) ∧
    kept.size ≤ segs.size ∧ kept.size ≤ segsPasses kept ∧
    segsPasses kept ≤ (if wide then 874 else 91) ∧
    w * h ≤ 4096 ∧ (w + 2) * (h + 2) ≤ 8196 := by
  obtain ⟨rfl, hw, hh, ha, active⟩ := preflight_ok ok
  have ⟨n, s⟩ := clamp_shape segs K
  refine ⟨n, s,?_,?_, ha,?_⟩
  · simp only [preflight, (clamp_spec ..).1] at ok
    split at ok <;> try contradiction
    split at ok <;> try contradiction
    cases H : (checkKept wide data (clampSegs segs K) w h m K).1 with
    | error e => simp [H, Except.map] at ok
    | ok u => exact kept_segments H
  · cases wide <;> simp only [Bool.false_eq_true, ↓reduceIte] at active ⊢ <;> omega
  · simp only [Nat.add_mul, Nat.mul_add]; omega

/-- The compact plain dispatch sees either an empty list or a single codeword with the
entire retained prefix. Its zero-pass fallback cannot discard a second admitted segment. -/
theorem compact_plain_prefix {data : ByteArray} {segs kept : Array Seg} {w h K : Nat}
    {style : UInt8} (hp : (Style.ofByte style).decodesAsPlain = true)
    (ok : (preflight false data segs w h (Style.ofByte style) K).1 = .ok kept) :
    kept.toList.map (·.passes) = if segsPasses kept = 0 then [] else [segsPasses kept] := by
  have cap := (preflight_domains ok).2.2.2.1
  obtain ⟨rfl, _, _, _, _⟩ := preflight_ok ok
  rw [compact_preflight] at ok
  split at ok <;> try contradiction
  let kept := clampSegs segs K
  have val : validateSegs data kept w h (Style.ofByte style) K = .ok () := by
    cases E : validateSegs data kept w h (Style.ofByte style) K with
    | error e =>
      change (validateSegs data kept w h (Style.ofByte style) K).map _ = _ at ok
      simp [E, Except.map] at ok
    | ok => rfl
  have shape : kept.toList.map (·.passes) = segmentPasses (Style.ofByte style) (segsPasses kept) 0 := by
    by_cases H : kept.toList.map (·.passes) = segmentPasses (Style.ofByte style) (segsPasses kept) 0
    · exact H
    · unfold validateSegs at val
      simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw, bne_iff_ne] at val
      repeat' first | contradiction | split at val
  let rel := Tier1EquivM.styleRel_ofByte style
  simp only [Style.decodesAsPlain, Bool.not_eq_true', Bool.or_eq_false_iff] at hp
  obtain ⟨⟨⟨⟨b, _⟩, t⟩, _⟩, _⟩ := hp
  have n : 0 + segsPasses kept ≤ 109 := by change segsPasses kept ≤ 91 at cap; omega
  exact shape.trans ((Tier1EquivM.segmentPasses_eq rel _ _).trans
    (Spec.Tier1.segmentPasses_plain _ (rel.termAll ▸ t) (rel.bypass ▸ b) _ _ n))

end JPEG2000.Spec.Resources.Tier1Work
