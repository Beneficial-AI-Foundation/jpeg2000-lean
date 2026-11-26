import Spec.Resources.Tier1Checks
import Spec.Resources.Tier1Meter

/-!
# Tier-1 call bounds (Plan.md §§3–5, 7, S3; T.800 A.6.1 and D.1–D.7)

Meter both public segmented decoders through their original error and output values.
The compact single-codeword path performs a second constant-size validation. Strict
segmentation-symbol rejection occurs after the scan and retains its charge.
-/

namespace JPEG2000.Spec.Resources.Tier1Work

open JPEG2000 JPEG2000.Tier1 JPEG2000.Tier2.Geometry

private def wideBody (m : Style) (data : ByteArray) (w h : Nat) (b : Band) (K : Nat)
    (strict : Bool) (kept : Array Seg) : Except Error (Array WidePlain.Cell) × Nat :=
  let initial : WidePlain.State := ⟨JPEG2000.MQ.Dec.init data 0 0 JPEG2000.MQ.tier1Contexts,
    Array.replicate (w * h) {}⟩
  if m.decodesAsPlain then
    let v := measurePlain data w h b K kept.toList 0 initial
    (.ok v.1.cells, 2 + w * h + kept.size + v.2)
  else
    let v := measureWide m data w h b K kept.toList 0 ⟨initial, 0⟩
    let out := if strict && v.1.badSegSymbols != 0 then
      .error (.malformed tier1Loc "bad segmentation symbol") else .ok v.1.block.cells
    (out, 3 + w * h + kept.size + v.2)

private def geo (w h : Nat) (b : Band) : Geo := ⟨w, h, w + 2, zcFor b, zcFor_size b⟩

private def start (data : ByteArray) (lo hi w h : Nat) : St :=
  let n := (w + 2) * (h + 2)
  ⟨JPEG2000.MQ.Dec.init data lo hi JPEG2000.MQ.tier1Contexts, Array.replicate n 0, Array.replicate n 0⟩

private def finish (g : Geo) (K n : Nat) (s : St) : CodeBlockOut :=
  ⟨fillRows g s.flags s.mags g.h (Bytes.Plane.zero g.w g.h) 0, s.flags, K, n⟩

private def setupFast (w h : Nat) := 8 + 2 * ((w + 2) * (h + 2)) + 2 * (w * h) + h

private def oneFast (data : ByteArray) (w h : Nat) (b : Band) (K : Nat) (sg : Seg) :
    Except Error (CodeBlockOut × Nat) × Nat :=
  match validate data sg.start sg.stop w h K sg.passes with
  | .error e => (.error e, 5)
  | .ok _ =>
    let g := geo w h b
    let v := measureFast g K sg.passes (start data sg.start sg.stop w h) 0
    (.ok (finish g K sg.passes v.1, 0), setupFast w h + v.2)

private def compactBody (m : Style) (data : ByteArray) (w h : Nat) (b : Band) (K : Nat)
    (kept : Array Seg) : Except Error (CodeBlockOut × Nat) × Nat :=
  if m.decodesAsPlain then
    let sg := match kept.toList with | [s] => s | _ => ⟨0, 0, 0⟩
    let v := oneFast data w h b K sg
    (v.1, kept.size + v.2)
  else
    let g := geo w h b
    let v := measureCompact m g K data kept 0 (start data 0 0 w h, 0)
    (.ok (finish g K (segsPasses kept) v.1.1, v.1.2), setupFast w h + kept.size + v.2)

private def checked {α : Type} (pre : Except Error (Array Seg) × Nat)
    (run : Array Seg → Except Error α × Nat) : Except Error α × Nat :=
  match pre.1 with
  | .error e => (.error e, pre.2)
  | .ok kept => let v := run kept; (v.1, pre.2 + v.2)

private theorem checked_value {α : Type} (pre : Except Error (Array Seg) × Nat)
    (run : Array Seg → Except Error α × Nat) :
    (checked pre run).1 = pre.1.bind (fun kept => (run kept).1) := by
  unfold checked; cases pre.1 <;> rfl

/-- Meter the wide segmented block decoder, including validation and strict rejection. -/
def wideCall (data : ByteArray) (segs : Array Seg) (w h : Nat) (b : Band) (style : UInt8)
    (Mb zbp : Nat) (strict : Bool) : Except Error (Array WidePlain.Cell) × Nat :=
  let m := Style.ofByte style
  checked (preflight true data segs w h m (Mb - zbp)) (wideBody m data w h b (Mb - zbp) strict)

private def compactCore (data : ByteArray) (segs : Array Seg) (w h : Nat) (b : Band) (style : UInt8)
    (Mb zbp : Nat) : Except Error (CodeBlockOut × Nat) × Nat :=
  let m := Style.ofByte style
  checked (preflight false data segs w h m (Mb - zbp)) (compactBody m data w h b (Mb - zbp))

/-- Meter the compact segmented block decoder, including its plain fast path. -/
def compactCall (data : ByteArray) (segs : Array Seg) (w h : Nat) (b : Band) (style : UInt8)
    (Mb zbp : Nat) (strict : Bool) : Except Error CodeBlockOut × Nat :=
  let v := compactCore data segs w h b style Mb zbp
  (v.1.bind fun (o, bad) => if strict && bad != 0 then
      .error (.malformed tier1Loc "bad segmentation symbol") else .ok o, v.2 + 1)

private theorem one_value (data : ByteArray) (w h : Nat) (b : Band) (Mb zbp : Nat) (sg : Seg) :
    (oneFast data w h b (Mb - zbp) sg).1 =
      (decodeCodeBlockExact data sg.start sg.stop w h b Mb zbp sg.passes).map (fun x => (x, 0)) := by
  unfold oneFast decodeCodeBlockExact
  simp only [bind, Except.bind, pure, Except.pure]
  cases validate data sg.start sg.stop w h (Mb - zbp) sg.passes with
  | error e => rfl
  | ok u => simp only [(fast_work ..).1]; rfl

private theorem compact_body_value (data : ByteArray) (kept : Array Seg) (w h : Nat) (b : Band)
    (style : UInt8) (Mb zbp : Nat) :
    (validateSegs data kept w h (Style.ofByte style) (Mb - zbp)).bind
      (fun _ => (compactBody (Style.ofByte style) data w h b (Mb - zbp) kept).1) =
      decodeSegsCore data kept w h b style Mb zbp := by
  unfold decodeSegsCore
  simp only [bind, Except.bind, pure, Except.pure]
  cases validateSegs data kept w h (Style.ofByte style) (Mb - zbp) <;> try rfl
  unfold compactBody
  cases hp : (Style.ofByte style).decodesAsPlain
  · simp only [Bool.false_eq_true, ↓reduceIte, (compact_work ..).1]; rfl
  · simp only [↓reduceIte]
    cases hlist : kept.toList with
    | nil => rw [one_value]; cases decodeCodeBlockExact data 0 0 w h b Mb zbp 0 <;> rfl
    | cons sg rest =>
      cases rest with
      | nil => rw [one_value]; dsimp only; cases decodeCodeBlockExact data sg.start sg.stop w h b Mb zbp sg.passes <;> rfl
      | cons => rw [one_value]; cases decodeCodeBlockExact data 0 0 w h b Mb zbp 0 <;> rfl

/-- Removing the wide meter gives the exact public result, including every rejection. -/
theorem wide_value (data : ByteArray) (segs : Array Seg) (w h : Nat) (b : Band) (style : UInt8)
    (Mb zbp : Nat) (strict : Bool) :
    (wideCall data segs w h b style Mb zbp strict).1 =
      WideSegments.decodeCodeBlockSegs data segs w h b style Mb zbp strict := by
  unfold wideCall WideSegments.decodeCodeBlockSegs
  rw [checked_value, wide_preflight]
  cases hp : (Style.ofByte style).decodesAsPlain <;>
    simp only [hp, WidePlain.decodeCodeBlockSegs, bind, Except.bind, pure, Except.pure,
      Bool.false_eq_true, ↓reduceIte, throw, throwThe, MonadExceptOf.throw]
  all_goals
    cases badRange data segs <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> try rfl
    cases WidePlain.validateSize w h <;> try rfl
  · cases WideSegments.validatePasses (Style.ofByte style) (clampSegs segs (Mb - zbp)) (Mb - zbp) <;> try rfl
    simp only [wideBody, hp, Bool.false_eq_true, ↓reduceIte, (wide_work ..).1]
  · simp only [WideSegments.validatePasses, bind, Except.bind, pure, Except.pure,
      throw, throwThe, MonadExceptOf.throw]
    simp only [wideBody, hp, ↓reduceIte, (plain_work ..).1]
    repeat' first | rfl | contradiction | split
    all_goals simp_all
    all_goals have := (clamp_shape segs (Mb - zbp)).1; omega

private theorem compact_core_value (data : ByteArray) (segs : Array Seg) (w h : Nat) (b : Band)
    (style : UInt8) (Mb zbp : Nat) :
    (compactCore data segs w h b style Mb zbp).1 =
      if badRange data segs then .error (.malformed tier1Loc "code-block data range outside the buffer")
      else decodeSegsCore data (clampSegs segs (Mb - zbp)) w h b style Mb zbp := by
  unfold compactCore; rw [checked_value, compact_preflight]
  cases badRange data segs <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> try rfl
  rw [← compact_body_value]
  cases validateSegs data (clampSegs segs (Mb - zbp)) w h (Style.ofByte style) (Mb - zbp) <;> rfl

/-- Removing the compact meter gives either public error policy. -/
theorem compact_value (data : ByteArray) (segs : Array Seg) (w h : Nat) (b : Band) (style : UInt8)
    (Mb zbp : Nat) (strict : Bool) :
    (compactCall data segs w h b style Mb zbp strict).1 =
      (if strict then decodeCodeBlockSegsStrict else decodeCodeBlockSegs) data segs w h b style Mb zbp := by
  simp only [compactCall, compact_core_value]
  cases strict <;> cases hr : badRange data segs <;>
    simp only [decodeCodeBlockSegs, decodeCodeBlockSegsStrict, hr, Bool.false_eq_true, ↓reduceIte] <;> try rfl
  all_goals cases decodeSegsCore data (clampSegs segs (Mb - zbp)) w h b style Mb zbp <;> rfl

private theorem one_flags (data : ByteArray) (w h : Nat) (b : Band) (K : Nat) (sg : Seg)
    (out : CodeBlockOut × Nat) (ok : (oneFast data w h b K sg).1 = .ok out) :
    out.1.flags.size = (w + 2) * (h + 2) := by
  unfold oneFast at ok
  split at ok <;> try contradiction
  cases ok
  change (measureFast (geo w h b) K sg.passes (start data sg.start sg.stop w h) 0).1.flags.size = _
  rw [(fast_work ..).1, compact_plain_schedule]
  have H := (compact_storage {} (geo w h b) K data [] (List.range' 0 sg.passes)
    (start data sg.start sg.stop w h) 0).1
  exact (congrArg Prod.fst H).trans Array.size_replicate

private theorem body_flags (m : Style) (data : ByteArray) (w h : Nat) (b : Band) (K : Nat)
    (kept : Array Seg) (out : CodeBlockOut × Nat) (ok : (compactBody m data w h b K kept).1 = .ok out) :
    out.1.flags.size = (w + 2) * (h + 2) := by
  unfold compactBody at ok
  split at ok
  · exact one_flags _ _ _ _ _ _ _ ok
  · cases ok
    change (measureCompact m (geo w h b) K data kept 0 (start data 0 0 w h, 0)).1.1.flags.size = _
    rw [(compact_work ..).1, compact_schedule m (geo w h b) K data kept 0 (start data 0 0 w h, 0)]
    have H := (compact_storage m (geo w h b) K data (schedule kept.toList 0) [] (start data 0 0 w h) 0).2
    exact (congrArg Prod.fst H).trans Array.size_replicate

/-- On a successful compact call the returned flag array has exactly the initial
bordered size. The decoder allocated the same number of magnitude words. -/
theorem compact_buffers (data : ByteArray) (segs : Array Seg) (w h : Nat) (b : Band)
    (style : UInt8) (Mb zbp : Nat) (strict : Bool) (o : CodeBlockOut)
    (ok : (if strict then decodeCodeBlockSegsStrict else decodeCodeBlockSegs)
      data segs w h b style Mb zbp = .ok o) :
    w * h ≤ 4096 ∧ o.flags.size = (w + 2) * (h + 2) ∧ o.flags.size ≤ 8196 := by
  rw [← compact_value] at ok
  unfold compactCall compactCore checked at ok
  cases E : (preflight false data segs w h (Style.ofByte style) (Mb - zbp)).1 with
  | error e => simp [E, Except.bind] at ok
  | ok kept =>
    have D := preflight_domains E
    simp only [E] at ok
    cases B : (compactBody (Style.ofByte style) data w h b (Mb - zbp) kept).1 with
    | error e => simp [B, Except.bind] at ok
    | ok out =>
      simp only [B, Except.bind] at ok
      split at ok <;> try contradiction
      cases ok
      have size := body_flags _ _ _ _ _ _ _ _ B
      exact ⟨D.2.2.2.2.1, size, size ▸ D.2.2.2.2.2⟩

/-- A wide success can only have constructed a raster of at most 4096 cells. -/
theorem wide_area (data : ByteArray) (segs : Array Seg) (w h : Nat) (b : Band)
    (style : UInt8) (Mb zbp : Nat) (strict : Bool) (cs : Array WidePlain.Cell)
    (ok : WideSegments.decodeCodeBlockSegs data segs w h b style Mb zbp strict = .ok cs) :
    w * h ≤ 4096 := by
  rw [← wide_value] at ok
  unfold wideCall checked at ok
  cases E : (preflight true data segs w h (Style.ofByte style) (Mb - zbp)).1 with
  | error e => simp [E] at ok
  | ok kept => exact (preflight_ok E).2.2.2.1

private theorem geometry (w h : Nat) (hw : w ≤ 1024) (hh : h ≤ 1024) (ha : w * h ≤ 4096) :
    columnSetup w h ≤ 8448 ∧ setupFast w h ≤ 25616 ∧
      passCharge w h (w * h) ≤ 66000 ∧ passCharge w h ((w + 2) * (h + 2)) ≤ 66000 := by
  have cols : w * ((h + 3) / 4) ≤ w * h := Nat.mul_le_mul_left w (by omega)
  have border : (w + 2) * (h + 2) ≤ 8196 := by
    simp only [Nat.add_mul, Nat.mul_add]; omega
  have pb : passBudget w h = w * h * 6 + (w * ((h + 3) / 4)) * 8 := by
    rw [passBudget, Nat.mul_add, Nat.mul_assoc, Nat.mul_assoc]
  simp only [columnSetup, setupFast, passCharge, pb]
  omega

private def bodyLimit (segs : Array Seg) := 26000 + 8500 * segs.size + 66000 * segsPasses segs

private theorem wide_body_cost (m : Style) (data : ByteArray) (w h : Nat) (b : Band) (K : Nat)
    (strict : Bool) (kept : Array Seg) (hw : w ≤ 1024) (hh : h ≤ 1024) (ha : w * h ≤ 4096) :
    (wideBody m data w h b K strict kept).2 ≤ bodyLimit kept := by
  obtain ⟨setup, _, lim, _⟩ := geometry w h hw hh ha
  let s : WidePlain.State := ⟨JPEG2000.MQ.Dec.init data 0 0 JPEG2000.MQ.tier1Contexts, Array.replicate (w * h) {}⟩
  have sz : s.cells.size = w * h := Array.size_replicate
  unfold wideBody bodyLimit
  split
  · have H := (plain_work data w h b K kept.toList 0 s).2
    rw [sz, Array.length_toList, ← Tier1EquivM.segsPasses_eq] at H
    have R := Nat.mul_le_mul_right kept.size (Nat.add_le_add_left setup 1)
    have P := Nat.mul_le_mul_right (segsPasses kept) lim
    change 2 + w * h + kept.size + (measurePlain data w h b K kept.toList 0 s).2 ≤ _
    omega
  · have H := (wide_work m data w h b K kept.toList 0 ⟨s, 0⟩).2
    rw [sz, Array.length_toList, ← Tier1EquivM.segsPasses_eq] at H
    have P := Nat.mul_le_mul_right (segsPasses kept) lim
    change 3 + w * h + kept.size + (measureWide m data w h b K kept.toList 0 ⟨s, 0⟩).2 ≤ _
    omega

private theorem one_cost (data : ByteArray) (w h : Nat) (b : Band) (K : Nat) (sg : Seg)
    (hw : w ≤ 1024) (hh : h ≤ 1024) (ha : w * h ≤ 4096) :
    (oneFast data w h b K sg).2 ≤ 25616 + 66000 * sg.passes := by
  obtain ⟨_, setup, _, lim⟩ := geometry w h hw hh ha
  unfold oneFast
  cases validate data sg.start sg.stop w h K sg.passes <;> try (dsimp only; omega)
  have H := (fast_work (geo w h b) K sg.passes (start data sg.start sg.stop w h) 0).2
  have sz : (start data sg.start sg.stop w h).flags.size = (w + 2) * (h + 2) := Array.size_replicate
  rw [sz] at H
  exact Nat.add_le_add setup (Nat.le_trans H (Nat.mul_le_mul_right sg.passes lim))

private theorem compact_body_cost (m : Style) (data : ByteArray) (w h : Nat) (b : Band) (K : Nat)
    (kept : Array Seg) (hw : w ≤ 1024) (hh : h ≤ 1024) (ha : w * h ≤ 4096) :
    (compactBody m data w h b K kept).2 ≤ bodyLimit kept := by
  unfold compactBody bodyLimit
  split
  · let sg : Seg := match kept.toList with | [s] => s | _ => ⟨0, 0, 0⟩
    have hs : sg.passes ≤ segsPasses kept := by
      simp only [sg, Tier1EquivM.segsPasses_eq]
      split <;> simp_all
    have := one_cost data w h b K sg hw hh ha
    change kept.size + (oneFast data w h b K sg).2 ≤ _
    omega
  · obtain ⟨_, setup, _, lim⟩ := geometry w h hw hh ha
    have H := (compact_work m (geo w h b) K data kept 0 (start data 0 0 w h, 0)).2
    have sz : (start data 0 0 w h).flags.size = (w + 2) * (h + 2) := Array.size_replicate
    rw [sz] at H
    have P : passCharge (geo w h b).w (geo w h b).h ((w + 2) * (h + 2)) * segsPasses kept ≤ _ :=
      Nat.mul_le_mul_right (segsPasses kept) lim
    dsimp only
    omega

/-- Per attempted call, in structural units. The parameters are the original segment
and pass counts, and the coded planes after subtraction of leading zero planes.
For 292 planes the kept-pass factor is at most 874. -/
def callBound (segments passes K : Nat) := 26006 + 8510 * segments + 66002 * min passes (3 * K - 2)

private theorem checked_cost {α : Type} (wide : Bool) (data : ByteArray) (segs : Array Seg)
    (w h : Nat) (m : Style) (K : Nat) (run : Array Seg → Except Error α × Nat)
    (bound : ∀ kept, w ≤ 1024 → h ≤ 1024 → w * h ≤ 4096 → (run kept).2 ≤ bodyLimit kept) :
    (checked (preflight wide data segs w h m K) run).2 + 1 ≤ callBound segs.size (segsPasses segs) K := by
  have A := preflight_work wide data segs w h m K
  unfold checked callBound
  cases E : (preflight wide data segs w h m K).1 with
  | error e => dsimp only; omega
  | ok kept =>
    obtain ⟨rfl, hw, hh, ha, _⟩ := preflight_ok E
    have B := bound (clampSegs segs K) hw hh ha
    obtain ⟨P, S⟩ := clamp_shape segs K
    unfold bodyLimit at B
    dsimp only
    omega

/-- Per-call structural bounds for both public decoders on successes and all errors.
One compact attempt followed by a wide retry costs at most twice this bound. -/
theorem call_work (data : ByteArray) (segs : Array Seg) (w h : Nat) (b : Band) (style : UInt8)
    (Mb zbp : Nat) (strict : Bool) :
    let budget := callBound segs.size (segsPasses segs) (Mb - zbp)
    (wideCall data segs w h b style Mb zbp strict).2 ≤ budget ∧
      (compactCall data segs w h b style Mb zbp strict).2 ≤ budget := by
  have W := checked_cost true data segs w h (Style.ofByte style) (Mb - zbp) _
    (wide_body_cost (Style.ofByte style) data w h b (Mb - zbp) strict)
  have C := checked_cost false data segs w h (Style.ofByte style) (Mb - zbp) _
    (compact_body_cost (Style.ofByte style) data w h b (Mb - zbp))
  exact ⟨Nat.le_of_succ_le W, C⟩

/-- If preflight fails, no pass, restart, raster construction, filling or clearing is
charged. Every original range is eligible for the preliminary validity scan. -/
theorem refusal_work (wide strict : Bool) (data : ByteArray) (segs : Array Seg) (w h : Nat)
    (b : Band) (style : UInt8) (Mb zbp : Nat) (e : Error)
    (reject : (preflight wide data segs w h (Style.ofByte style) (Mb - zbp)).1 = .error e) :
    (if wide then (wideCall data segs w h b style Mb zbp strict).2
     else (compactCall data segs w h b style Mb zbp strict).2) ≤
      10 * segs.size + 2 * min (segsPasses segs) (3 * (Mb - zbp) - 2) + 6 := by
  have H := preflight_work wide data segs w h (Style.ofByte style) (Mb - zbp)
  cases wide <;> simp only [compactCall, compactCore, wideCall, checked, reject,
    Bool.false_eq_true, ↓reduceIte] <;> omega

end JPEG2000.Spec.Resources.Tier1Work
