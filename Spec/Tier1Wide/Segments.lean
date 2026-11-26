import JPEG2000.Tier1.WideSegments
import Spec.Tier1Wide.Modes

/-!
# Wide codeword segment equivalence (Plan.md §§4, 5.1, 5.4, 7; T.800 Annex D)

The independent Annex D partition determines the active coder throughout each segment.
Only the MQ contexts, raster and segmentation-symbol count must agree at a restart.
Both segmentation-symbol policies compare the complete result, including validation errors.
-/

namespace JPEG2000.Spec.Tier1Wide.Segments

open JPEG2000.Tier2.Geometry (Band)
open JPEG2000.Tier1
open Spec.Tier1 (CodeBlock DecState Mode)
open Tier1EquivM (gV specBlockM)

private theorem segments_sim {m : Style} {md : Mode} (hm : Tier1EquivM.StyleRel m md)
    (data : ByteArray) (w h : Nat) (b : Band) (K : Nat) (segs : List Seg) (first : Nat)
    (s : WideModes.State) (d : DecState) (partition : Tier1EquivM.Homog md (segs.map (·.passes)) first)
    (hx : MQEquiv.CxRel s.block.mq.cx d.cxs) (hc : s.block.cells = d.coeffs.map cellOf)
    (hb : s.badSegSymbols = d.badSegSymbols) :
    let t := WideSegments.runSegments m data w h b K (WidePlain.columns w h) segs first s
    let z := Spec.Tier1.decodeSegments md (gV w h b md.vertCausal) K
      (segs.map (Tier1EquivM.segOf data)) first d
    t.block.cells = z.coeffs.map cellOf ∧ t.badSegSymbols = z.badSegSymbols := by
  induction segs generalizing first s d with
  | nil => exact ⟨hc, hb⟩
  | cons sg rest ih =>
    let t := WideSegments.restart m data sg first s
    let z := Spec.Tier1.startSegment md d first (MQEquiv.segment data sg.start sg.stop)
    have init : Modes.Sim sg.start (Spec.Tier1.isRawPass md first) t z := by
      simp only [t, z, WideSegments.restart, Spec.Tier1.startSegment, Tier1EquivM.isRawPass_eq hm]
      cases Spec.Tier1.isRawPass md first <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · exact ⟨⟨MQEquiv.init_sim _ _ _ _ _ hx, hc⟩, hb⟩
      · exact ⟨⟨⟨Tier1EquivM.rawInit_sim _ _ _ _, hx⟩, hc⟩, hb⟩
    obtain ⟨head, tail⟩ := partition
    have passes := List.foldl_rel (l := List.range' first sg.passes) init
      (f := WideModes.runPass m w h b K (WidePlain.columns w h))
      (g := Spec.Tier1.runPassM md (gV w h b md.vertCausal) K) (by
        intro i hi a d R
        obtain ⟨q, hq, rfl⟩ := List.mem_range'.mp hi
        simp only [Nat.one_mul]
        have eq := head q hq
        rw [← eq] at R ⊢
        exact Modes.runPass_equiv hm _ _ _ _ _ _ _ _ R)
    exact ih _ _ _ tail (Tier1EquivM.coder_cx passes.core.coder) passes.core.cells passes.bad

private theorem passChecks_eq (data : ByteArray) (kept : Array Seg) (w h : Nat) (b : Band)
    (style : UInt8) (Mb zbp : Nat) (size : ¬(w > 1024 ∨ h > 1024 ∨ w * h > 4096))
    (budget : ¬(0 < segsPasses kept ∧ Mb - zbp > WidePlain.maxCodedPlanes)) :
    WideSegments.validatePasses (Style.ofByte style) kept (Mb - zbp) =
      (specBlockM data kept w h b style Mb zbp).validate := by
  unfold WideSegments.validatePasses CodeBlock.validate
  rw [Tier1EquivM.specBlockM_numPasses, ← Tier1EquivM.segsPasses_eq]
  simp only [specBlockM, CodeBlock.codedPlanes, size, budget, ↓reduceIte, List.map_map,
    Tier1EquivM.segmentPasses_eq (Tier1EquivM.styleRel_ofByte style)]
  rfl

private theorem plain_policy (cb : CodeBlock) (style : UInt8)
    (mode : cb.mode = Mode.ofStyle style.toNat) (plain : (Style.ofByte style).decodesAsPlain)
    (strict : Bool) :
    (if strict then Spec.Tier1.decodeCodeBlockStrictExact cb else Spec.Tier1.decodeCodeBlockExact cb) =
      Spec.Tier1.decodeCodeBlockExact { cb with mode := .plain } := by
  have hm := Tier1EquivM.styleRel_ofByte style
  simp only [Style.decodesAsPlain, Bool.not_eq_true', Bool.or_eq_false_iff, hm.bypass, hm.reset,
    hm.termAll, hm.vertCausal, hm.segSymbols, ← mode] at plain
  obtain ⟨⟨⟨⟨hb, hr⟩, ht⟩, hv⟩, hs⟩ := plain
  rw [← Tier1EquivM.decodeCodeBlock_plainLike cb hb hr ht hv hs]
  cases strict
  · rfl
  · have bad : (Spec.Tier1.decodeState cb).badSegSymbols = 0 :=
      Tier1EquivM.decodeSegments_bad_noSeg cb.geom cb.mode hs _ _ _ _
    simp [Spec.Tier1.decodeCodeBlockStrictExact, Spec.Tier1.decodeCodeBlockExact, bad]

/-- On in-buffer slices with a header-representable coded-plane count, both D.5 policies
give exactly the independent Annex D result, including the error on an invalid block or
segment partition. A successful result agrees on all six fields of every coefficient. -/
theorem decodeCodeBlockSegs_equiv (data : ByteArray) (segs : Array Seg) (w h : Nat) (b : Band)
    (style : UInt8) (Mb zbp : Nat) (strict : Bool)
    (ranges : ∀ sg ∈ segs.toList, sg.start ≤ sg.stop ∧ sg.stop ≤ data.size)
    (header : 0 < segsPasses segs → Mb - zbp ≤ WidePlain.maxCodedPlanes) :
    let cb := specBlockM data segs w h b style Mb zbp
    WideSegments.decodeCodeBlockSegs data segs w h b style Mb zbp strict =
      (if strict then Spec.Tier1.decodeCodeBlockStrict cb else Spec.Tier1.decodeCodeBlock cb).map
        (·.map cellOf) := by
  let kept := clampSegs segs (Mb - zbp)
  let cb := specBlockM data kept w h b style Mb zbp
  dsimp only
  simp only [Spec.Tier1.decodeCodeBlockStrict, Spec.Tier1.decodeCodeBlock, Tier1EquivM.specBlockM_clamp]
  change _ = (if strict then Spec.Tier1.decodeCodeBlockStrictExact cb else Spec.Tier1.decodeCodeBlockExact cb).map _
  unfold WideSegments.decodeCodeBlockSegs
  by_cases hp : (Style.ofByte style).decodesAsPlain = true
  · rw [plain_policy cb style rfl hp strict]
    have H := Tier1Wide.decodeCodeBlockSegs_equiv data segs w h b Mb zbp ranges header
    rw [Spec.Tier1.decodeCodeBlock, Tier1EquivM.specBlockM_clamp] at H
    have block : { cb with mode := Mode.plain } = specBlockM data kept w h b 0 Mb zbp := rfl
    rw [block]
    simpa only [hp, ↓reduceIte] using H
  · simp only [hp, Tier1EquivM.badRange_false _ _ ranges, Bool.false_eq_true, ↓reduceIte]
    have le : segsPasses kept ≤ segsPasses segs := by
      simp only [Tier1EquivM.segsPasses_eq]
      exact Tier1EquivM.clampSegs_sum_le ..
    have budget : ¬(0 < segsPasses kept ∧ Mb - zbp > WidePlain.maxCodedPlanes) :=
      fun ⟨hn, big⟩ => Nat.not_lt.mpr (header (Nat.lt_of_lt_of_le hn le)) big
    by_cases size : w > 1024 ∨ h > 1024 ∨ w * h > 4096
    · have invalid : cb.validate = .error (.malformed tier1Loc
          "code-block larger than 1024 x 1024 or 4096 coefficients") := by
        simp [cb, specBlockM, CodeBlock.validate, size, tier1Loc, Spec.Tier1.tier1Loc,
          bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
      cases strict <;> simp [WidePlain.validateSize, size, Spec.Tier1.decodeCodeBlockStrictExact,
        Spec.Tier1.decodeCodeBlockExact, invalid, bind, Except.bind, Except.map]
    · simp only [WidePlain.validateSize, size, ↓reduceIte]
      rw [passChecks_eq data kept w h b style Mb zbp size budget]
      cases val : cb.validate with
      | error e =>
        cases strict <;> simp [Spec.Tier1.decodeCodeBlockExact, Spec.Tier1.decodeCodeBlockStrictExact,
          val, bind, Except.bind, Except.map]
      | ok u =>
        have shape := (Tier1EquivM.validate_ok_facts cb u val).2
        have counts : cb.segments.map (·.passes) = kept.toList.map (·.passes) := by
          simp [cb, specBlockM, List.map_map, Function.comp_def]
        have part : Tier1EquivM.Homog cb.mode (kept.toList.map (·.passes)) 0 := by
          rw [← counts, shape]
          exact Tier1EquivM.segmentPasses_homog ..
        let init : WideModes.State :=
          ⟨⟨JPEG2000.MQ.Dec.init data 0 0 JPEG2000.MQ.tier1Contexts, Array.replicate (w * h) {}⟩, 0⟩
        let t := WideSegments.runSegments (Style.ofByte style) data w h b (Mb - zbp)
          (WidePlain.columns w h) kept.toList 0 init
        have agree : t.block.cells = (Spec.Tier1.decodeState cb).coeffs.map cellOf ∧
            t.badSegSymbols = (Spec.Tier1.decodeState cb).badSegSymbols :=
          segments_sim (Tier1EquivM.styleRel_ofByte style) data w h b _ kept.toList 0 init
            (DecState.init cb.geom []) part Tier1EquivM.tier1Contexts_rel
            (by simp [init, DecState.init, cb, specBlockM, CodeBlock.geom, cellOf]) rfl
        cases strict <;> simp only [Spec.Tier1.decodeCodeBlockExact, Spec.Tier1.decodeCodeBlockStrictExact,
          val, bind, Except.bind, pure, Except.pure, Bool.false_and, Bool.true_and,
          Bool.false_eq_true, ↓reduceIte, Except.map]
        · exact congrArg Except.ok agree.1
        · change (if t.badSegSymbols != 0 then _ else Except.ok t.block.cells) = _
          rw [agree.2, agree.1]
          split <;> rfl

/-- Read Tier-2 slices into the Annex D reference decoder. The slice check includes the
discarded suffix. For synthetic calls beyond the E-2 and RGN header fields, apply the
same pre-allocation bound as for a block received from the wire. -/
def decodeRanges (data : ByteArray) (segs : Array Seg) (w h : Nat) (b : Band)
    (style : UInt8) (Mb zbp : Nat) (strict : Bool) : Except Error (Array Spec.Tier1.Coeff) :=
  if segs.toList.all (fun sg => sg.start ≤ sg.stop && sg.stop ≤ data.size) then
    let cb := specBlockM data segs w h b style Mb zbp
    if 0 < cb.numPasses ∧ 7 + 31 - 1 + 255 < cb.codedPlanes then
      if w > 1024 ∨ h > 1024 ∨ w * h > 4096 then
        .error (.malformed Spec.Tier1.tier1Loc "code-block larger than 1024 x 1024 or 4096 coefficients")
      else .error (.malformed Spec.Tier1.tier1Loc "coded bit-plane count exceeds the E-2 and RGN header fields")
    else if strict then Spec.Tier1.decodeCodeBlockStrict cb else Spec.Tier1.decodeCodeBlock cb
  else .error (.malformed Spec.Tier1.tier1Loc "code-block data range outside the buffer")

private theorem trunc_count (segs : List Seg) (n : Nat) :
    ((truncSegs segs n).map (·.passes)).sum = min n (segs.map (·.passes)).sum := by
  induction segs generalizing n with
  | nil => simp [truncSegs]
  | cons sg rest ih =>
    simp only [truncSegs, List.map_cons, List.sum_cons]
    split
    · simp [*]
    · split
      · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
        omega
      · simp only [List.map_cons, List.sum_cons, ih]
        omega

/-- The production block entry point equals the checked Annex D decoder for every byte
buffer, range, pass count, geometry, style, plane count and D.5 policy. Equality of the
entire `Except` value preserves the first error as well as all coefficient fields. -/
theorem decodeRanges_equiv (data : ByteArray) (segs : Array Seg) (w h : Nat) (b : Band)
    (style : UInt8) (Mb zbp : Nat) (strict : Bool) :
    WideSegments.decodeCodeBlockSegs data segs w h b style Mb zbp strict =
      (decodeRanges data segs w h b style Mb zbp strict).map (·.map cellOf) := by
  let valid := segs.toList.all (fun sg => sg.start ≤ sg.stop && sg.stop ≤ data.size)
  have good : valid = true ↔ ∀ sg ∈ segs.toList, sg.start ≤ sg.stop ∧ sg.stop ≤ data.size := by
    simp only [valid, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  have rangeEq : badRange data segs = !valid := by
    unfold badRange
    rw [← Array.any_toList]
    rw [show valid = _ from rfl, List.not_all_eq_any_not]
    congr 1
    funext sg
    simp [Bool.not_and, ← decide_not, Nat.not_le]
  unfold decodeRanges
  by_cases ranges : valid = true
  · have count : (specBlockM data segs w h b style Mb zbp).numPasses = segsPasses segs := by
      rw [Tier1EquivM.specBlockM_numPasses, Tier1EquivM.segsPasses_eq]
    change _ = Except.map _ (if valid then _ else _)
    simp only [ranges, ↓reduceIte, count]
    by_cases budget : 0 < segsPasses segs ∧ WidePlain.maxCodedPlanes < Mb - zbp
    · have kept : 0 < segsPasses (clampSegs segs (Mb - zbp)) := by
        unfold clampSegs
        split
        · exact budget.1
        · rw [Tier1EquivM.segsPasses_eq, List.toList_toArray, trunc_count, ← Tier1EquivM.segsPasses_eq]
          have big := budget.2
          unfold WidePlain.maxCodedPlanes at big
          omega
      have hbud : 0 < segsPasses (clampSegs segs (Mb - zbp)) ∧ Mb - zbp > WidePlain.maxCodedPlanes :=
        ⟨kept, budget.2⟩
      have specBudget : 0 < segsPasses segs ∧ 7 + 31 - 1 + 255 <
          (specBlockM data segs w h b style Mb zbp).codedPlanes := budget
      unfold WideSegments.decodeCodeBlockSegs
      cases hp : (Style.ofByte style).decodesAsPlain <;>
        by_cases size : w > 1024 ∨ h > 1024 ∨ w * h > 4096 <;>
        simp [WidePlain.decodeCodeBlockSegs, WideSegments.validatePasses, WidePlain.validateSize,
          size, hbud, rangeEq, ranges, specBudget, hp, bind, Except.bind, throw, throwThe,
          MonadExceptOf.throw, Except.map, tier1Loc, Spec.Tier1.tier1Loc]
    · have specBudget : ¬(0 < segsPasses segs ∧ 7 + 31 - 1 + 255 <
          (specBlockM data segs w h b style Mb zbp).codedPlanes) := budget
      simp only [specBudget, ↓reduceIte]
      exact decodeCodeBlockSegs_equiv data segs w h b style Mb zbp strict (good.mp ranges)
        (fun positive => Nat.le_of_not_gt (fun big => budget ⟨positive, big⟩))
  · have invalid := Bool.eq_false_iff.mpr ranges
    change _ = Except.map _ (if valid then _ else _)
    unfold WideSegments.decodeCodeBlockSegs
    cases hp : (Style.ofByte style).decodesAsPlain <;>
      simp only [hp, WidePlain.decodeCodeBlockSegs, rangeEq, invalid, Bool.not_false,
        Bool.false_eq_true, ↓reduceIte] <;> rfl

-- Both raw refinement segments begin with eight ones. Skipping the stuffed bit gives
-- a one for the ninth cell in the first segment and a zero in the second.
example : ((WideSegments.decodeCodeBlockSegs ⟨#[2, 157, 255, 85, 255, 127, 255, 21, 255, 127]⟩
    #[⟨0, 2, 10⟩, ⟨2, 4, 2⟩, ⟨4, 6, 1⟩, ⟨6, 8, 2⟩, ⟨8, 10, 1⟩] 9 1 .LL 1 38 0).toOption.map
    (·.map fun c => (c.value, c.lsbPlane))) =
      some ((Array.replicate 8 ((35 * 2 ^ 32 : Int), 32)).push (34 * 2 ^ 32, 32)) := by decide +kernel

-- A negative wide coefficient followed by 1110 instead of 1010 in UNIFORM.
example :
    (let read (strict : Bool) :=
       WideSegments.decodeCodeBlockSegs ⟨#[9, 159]⟩ #[⟨0, 2, 1⟩] 1 1 .LL 32 38 0 strict
     ((read false).toOption.map (·.map WidePlain.Cell.value),
       match read true with | .error e => some e | .ok _ => none)) =
      (some #[-(2 ^ 37)], some (.malformed tier1Loc "bad segmentation symbol")) := by decide +kernel

-- The plain-like PTERM style carries MQ contexts over pass 109 and drops four surplus passes.
example : ((WideSegments.decodeCodeBlockSegs ⟨#[5, 63, 7]⟩ #[⟨0, 2, 109⟩, ⟨2, 3, 7⟩]
    1 1 .LL 16 38 0 true).toOption.map (·.map fun c => (c.value, c.lsbPlane))) =
      some #[(2 ^ 37 + 1, 0)] := by decide +kernel

end JPEG2000.Spec.Tier1Wide.Segments
