import Spec.WideHeaderBounds
import Spec.Resources.Tier1Calls

/-!
# Tier-1 coefficient bounds (Plan.md §§3–5, 7, S3, T.800 A.6.1, D.1–D.7, E-2, H)

For a gathered block with S segments and P supplied passes, each compact or wide attempt
costs at most 26006 + 8510*S + 66002*min(P,874) structural units on an admitted header.
Preflight rejection costs at most 10*S + 2*min(P,3*K-2) + 6. The meter charges reader
decisions, resets and restarts, slots in scans and validation loops, and raster setup,
clearing and filling. A slot can involve a fixed group of neighbour accesses. The unit
is a structural count at the Tier-1 kernel interface.

C3 transfers the pass invariant to the exact arrays returned on both output paths.
-/

namespace JPEG2000.Spec.Resources.Tier1Work

open JPEG2000 JPEG2000.Tier1 JPEG2000.Tier2.Geometry
open JPEG2000.Spec.Tier1 (Coeff DecState CodeBlock)
open Spec.Tier1Equiv Spec.Tier1EquivM

private theorem pre_bounds {K n : Nat} {c : Coeff} (hn : n ≤ 3 * K - 2) (H : Pre K n c) :
    c.mag < 2 ^ K ∧ c.lsbPlane ≤ K - 1 ∧ (c.sig = false → c.mag = 0 ∧ c.lsbPlane = 0) := by
  have finish (hb : Base K c) (hl : c.sig = true → c.lsbPlane ≤ K - 1) :
      c.mag < 2 ^ K ∧ c.lsbPlane ≤ K - 1 ∧ (c.sig = false → c.mag = 0 ∧ c.lsbPlane = 0) := by
    refine ⟨?_, ?_, hb.1⟩ <;> cases hs : c.sig
    · rw [(hb.1 hs).1]; exact Nat.two_pow_pos _
    · exact (hb.2 hs).1
    · rw [(hb.1 hs).2]; exact Nat.zero_le _
    · exact hl hs
  unfold Pre at H
  split at H
  · exact finish H.1 (fun hs => Nat.le_of_eq (H.2 hs))
  · rename_i hn0
    unfold Post at H
    split at H
    · rename_i hk
      apply finish H.1
      intro hs
      cases hv : c.visited
      · rw [H.2.2 hs hv]
        have hi : n - 1 ≠ 0 := by intro he; simp [he, Spec.Tier1.passKind] at hk
        unfold Spec.Tier1.passPlane
        omega
      · rw [H.2.1 hs hv]; exact Nat.sub_le _ _
    · exact finish H.1 (fun hs => H.2 hs ▸ Nat.sub_le _ _)
    · exact finish H.1.1 (fun hs => H.1.2 hs ▸ Nat.sub_le _ _)

private theorem state_bounds (cb : CodeBlock) (b : Band) (ho : cb.orient = orientOf b)
    (val : cb.validate = .ok ()) :
    (Spec.Tier1.decodeState cb).coeffs.size = cb.width * cb.height ∧
      ∀ c ∈ (Spec.Tier1.decodeState cb).coeffs, c.mag < 2 ^ cb.codedPlanes ∧
        c.lsbPlane ≤ cb.codedPlanes - 1 ∧ (c.sig = false → c.mag = 0 ∧ c.lsbPlane = 0) := by
  let g := gV cb.width cb.height b cb.mode.vertCausal
  have hg : cb.geom = g := by simp [CodeBlock.geom, g, gV, ho]
  have H0 : AllPV cb.width cb.height b cb.mode.vertCausal (Pre cb.codedPlanes 0)
      (DecState.init g []).coeffs := by
    refine ⟨by simp [DecState.init, g, gV], fun x y _ _ => ?_⟩
    change Pre _ 0 (g.coeffAt (Array.replicate (g.width * g.height) {}) x y)
    rw [coeffAt_replicate]
    exact ⟨⟨fun _ => ⟨rfl, rfl⟩, fun h => by cases h⟩, fun h => by cases h⟩
  have hn : cb.numPasses ≤ 3 * cb.codedPlanes - 2 := by
    have := (validate_ok_facts cb () val).1
    omega
  have inv := decodeSegments_inv cb.mode cb.codedPlanes cb.segments 0 _ (by
    simpa only [Nat.zero_add, CodeBlock.numPasses] using hn) H0
  change AllPV _ _ _ _ (Pre _ (0 + cb.numPasses)) (Spec.Tier1.decodeSegments cb.mode g _ _ 0 (DecState.init g [])).coeffs at inv
  rw [← hg, Nat.zero_add] at inv
  change AllPV _ _ _ _ (Pre _ cb.numPasses) (Spec.Tier1.decodeState cb).coeffs at inv
  refine ⟨inv.1, fun c hc => ?_⟩
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hc
  have harea : i < cb.width * cb.height := inv.1 ▸ hi
  have hw : 0 < cb.width := by
    cases hz : cb.width <;> simp_all
  have hx := Nat.mod_lt i hw
  have hy := (Nat.div_lt_iff_lt_mul hw).mpr (Nat.mul_comm cb.width cb.height ▸ harea)
  have hit := inv.2 (i % cb.width) (i / cb.width) hx hy
  rw [coeffAt_nat _ _ _ _ hx hy] at hit
  simpa only [Spec.Tier1.Geom.idx, gV, Nat.mul_comm (i / cb.width), Nat.div_add_mod, Array.getD_eq_getD_getElem?,
    Array.getElem?_eq_getElem hi, Option.getD_some] using pre_bounds hn hit

/-- Every wide raster returned by the segmented decoder, at any truncation and in any
style, has one cell per sample. Both sign choices have the same magnitude bound.
An insignificant cell retains zero magnitude and plane. -/
theorem wide_cells (data : ByteArray) (segs : Array Seg) (w h : Nat) (b : Band)
    (style : UInt8) (Mb zbp : Nat) (strict : Bool) (cs : Array WidePlain.Cell)
    (ok : WideSegments.decodeCodeBlockSegs data segs w h b style Mb zbp strict = .ok cs) :
    cs.size = w * h ∧ ∀ c ∈ cs, c.mag < 2 ^ (Mb - zbp) ∧ c.lsbPlane ≤ Mb - zbp - 1 ∧
      (c.sig = false → c.mag = 0 ∧ c.lsbPlane = 0) := by
  rw [Tier1Wide.Segments.decodeRanges_equiv] at ok
  unfold Tier1Wide.Segments.decodeRanges at ok
  split at ok <;> try contradiction
  dsimp only at ok
  split at ok
  · split at ok <;> contradiction
  simp only [Spec.Tier1.decodeCodeBlockStrict, Spec.Tier1.decodeCodeBlock, specBlockM_clamp] at ok
  let cb := specBlockM data (clampSegs segs (Mb - zbp)) w h b style Mb zbp
  change (if strict then Spec.Tier1.decodeCodeBlockStrictExact cb else
    Spec.Tier1.decodeCodeBlockExact cb).map _ = .ok cs at ok
  have ⟨val, hout⟩ : cb.validate = .ok () ∧ cs = (Spec.Tier1.decodeState cb).coeffs.map
      Tier1Wide.cellOf := by
    cases hv : cb.validate with
    | error e => cases strict <;> simp [Spec.Tier1.decodeCodeBlockStrictExact,
                   Spec.Tier1.decodeCodeBlockExact, hv, bind, Except.bind, Except.map] at ok
    | ok u =>
      refine ⟨rfl, ?_⟩
      cases strict <;> simp only [Bool.false_eq_true, ↓reduceIte, Spec.Tier1.decodeCodeBlockExact,
        Spec.Tier1.decodeCodeBlockStrictExact, hv, bind, Except.bind, pure, Except.pure] at ok
      · exact (Except.ok.inj ok).symm
      · split at ok <;> first | contradiction | exact (Except.ok.inj ok).symm
  obtain ⟨sz, bounds⟩ := state_bounds cb b rfl val
  subst cs
  refine ⟨by rw [Array.size_map]; exact sz, fun c hc => ?_⟩
  obtain ⟨a, ha, rfl⟩ := Array.mem_map.mp hc
  exact bounds _ ha

/-- Arithmetic inputs to wide dequantisation at the parsed packet-block entry point.
The signed-magnitude index has at most 292 bits and the reconstruction shift is at most 291. -/
theorem parsed_cells {L : Limits} {p : Header.CompParams}
    (bounds : WideHeaderBounds.ComponentBounds L p) (data : ByteArray) (r : Nat) (b : Band)
    (cb : Tier2.Packet.CodeBlock) (cs : Array WidePlain.Cell)
    (ok : WideAssembly.decodeBlock data p r b cb = .ok cs) :
    cs.size = cb.geom.rect.width * cb.geom.rect.height ∧
      ∀ c ∈ cs, c.mag < 2 ^ 292 ∧ c.lsbPlane ≤ 291 ∧ c.value.natAbs < 2 ^ 292 := by
  unfold WideAssembly.decodeBlock at ok
  dsimp only at ok
  split at ok <;> try contradiction
  have ⟨sz, hb⟩ := wide_cells _ _ _ _ _ _ _ _ _ _ ok
  refine ⟨sz, fun c hc => ?_⟩
  obtain ⟨hm, hl, _⟩ := hb c hc
  have H := bounds.block_planes r b
  have mag := Nat.lt_of_lt_of_le hm (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_trans (Nat.sub_le _ _) H))
  refine ⟨mag, by omega, ?_⟩
  unfold WidePlain.Cell.value; split <;> simpa only [Int.natAbs_neg, Int.natAbs_natCast] using mag

private theorem compact_lenient (data : ByteArray) (segs : Array Seg) (w h : Nat) (b : Band)
    (style : UInt8) (Mb zbp : Nat) (strict : Bool) (o : CodeBlockOut)
    (ok : (if strict then decodeCodeBlockSegsStrict else decodeCodeBlockSegs)
      data segs w h b style Mb zbp = .ok o) :
    decodeCodeBlockSegs data segs w h b style Mb zbp = .ok o := by
  cases strict <;> try exact ok
  simp only [↓reduceIte, decodeCodeBlockSegsStrict, decodeCodeBlockSegs, decodeCodeBlockSegsStrictExact,
    decodeCodeBlockSegsExact, bind, Except.bind, pure, Except.pure] at ok ⊢
  split at ok <;> try contradiction
  rename_i hr
  simp only [hr]
  cases eq : decodeSegsCore data (clampSegs segs (Mb - zbp)) w h b style Mb zbp with
  | error e => simp [eq] at ok
  | ok p =>
    simp only [eq] at ok
    split at ok <;> first | contradiction | exact ok

/-- All actual compact output coordinates obey the same magnitude and last-plane bounds,
including the all-zero block when no passes survive. -/
theorem compact_cells (data : ByteArray) (segs : Array Seg) (w h : Nat) (b : Band)
    (style : UInt8) (Mb zbp : Nat) (strict : Bool) (o : CodeBlockOut)
    (ok : (if strict then decodeCodeBlockSegsStrict else decodeCodeBlockSegs)
      data segs w h b style Mb zbp = .ok o) :
    o.plane.width = w ∧ o.plane.height = h ∧ o.plane.data.size = 4 * (w * h) ∧
    o.plane.data.size ≤ 16384 ∧ ∀ x y, x < w → y < h →
      o.lsbPlane x y ≤ Mb - zbp - 1 ∧ ∃ v, o.plane.get? (y * w + x) = some v ∧
        v.toInt.natAbs < 2 ^ (Mb - zbp) ∧
        (o.sig x y = false → v.toInt = 0 ∧ o.lsbPlane x y = 0) := by
  have success := compact_lenient data segs w h b style Mb zbp strict o ok
  have hr : badRange data segs = false := by
    cases E : badRange data segs <;> simp_all [decodeCodeBlockSegs]
  have ranges : ∀ sg ∈ segs.toList, sg.start ≤ sg.stop ∧ sg.stop ≤ data.size := by
    simp only [badRange, ← Array.any_toList, List.any_eq_false, Bool.or_eq_true, decide_eq_true_eq] at hr
    intro sg hsg; have := hr sg hsg; omega
  have agree := c3_all_unsup data segs w h b style Mb zbp ranges
  rw [success, Spec.Tier1.decodeCodeBlock, specBlockM_clamp] at agree
  let cb := specBlockM data (clampSegs segs (Mb - zbp)) w h b style Mb zbp
  rw [show specBlockM data (clampSegs segs (Mb - zbp)) w h b style Mb zbp = cb from rfl] at agree
  unfold Spec.Tier1.decodeCodeBlockExact at agree
  cases val : cb.validate with
  | error e => simp [val, bind, Except.bind] at agree
  | ok u =>
    simp only [val, bind, Except.bind, pure, Except.pure] at agree
    have bytes := o.plane.size_eq
    rw [agree.2.1, agree.2.2.1] at bytes
    have area := (compact_buffers data segs w h b style Mb zbp strict o ok).1
    refine ⟨agree.2.1, agree.2.2.1, bytes, by omega, fun x y hx hy => ?_⟩
    obtain ⟨vo, so, lo⟩ := agree.2.2.2 x y hx hy
    let cs := (Spec.Tier1.decodeState cb).coeffs
    have sz : cs.size = w * h := agree.1
    have idx : y * w + x < cs.size := by rw [sz]; exact idx_lt (gV w h b false) hx hy
    have mem : cs.getD (y * w + x) {} ∈ cs := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem idx]; exact Array.getElem_mem idx
    obtain ⟨hm, hl, hz⟩ := (state_bounds cb b rfl val).2 _ mem
    rcases he : o.plane.get? (y * w + x) with _ | v
    · simp [he] at vo
    · simp only [he, Option.map_some, Option.some.injEq] at vo
      change v.toInt = (cs.getD (y * w + x) {}).value at vo
      refine ⟨lo ▸ hl, v, rfl, ?_, ?_⟩
      · have absMag (c : Coeff) : c.value.natAbs = c.mag := by
          unfold Coeff.value; split <;> simp only [Int.natAbs_neg, Int.natAbs_natCast]
        rw [vo, absMag]; exact hm
      · intro hs
        obtain ⟨m, l⟩ := hz (so ▸ hs)
        rw [vo, lo]
        exact ⟨by simp only [Coeff.value, m, Int.natCast_zero, Int.neg_zero, ite_self], l⟩

/-- Parsed compact samples and their reconstruction shifts obey the same numerical
bound as the wide raster, at the packet-block API used during an actual compact attempt. -/
theorem parsed_compact_cells {L : Limits} {p : Header.CompParams}
    (bounds : WideHeaderBounds.ComponentBounds L p) (data : ByteArray) (r : Nat) (b : Band)
    (cb : Tier2.Packet.CodeBlock) (o : CodeBlockOut) (ok : Assemble.decodeBlock data p r b cb = .ok o) :
    ∀ x y, x < cb.geom.rect.width → y < cb.geom.rect.height →
      o.lsbPlane x y ≤ 291 ∧ ∃ v, o.plane.get? (y * cb.geom.rect.width + x) = some v ∧
        v.toInt.natAbs < 2 ^ 292 := by
  unfold Assemble.decodeBlock at ok
  dsimp only at ok
  have ⟨_, _, _, _, C⟩ := compact_cells _ _ _ _ _ _ _ _ false _ ok
  have H := bounds.block_planes r b
  intro x y hx hy
  obtain ⟨hl, v, he, hm, _⟩ := C x y hx hy
  have mag := Nat.lt_of_lt_of_le hm (Nat.pow_le_pow_right (by decide : 0 < 2)
    (Nat.le_trans (Nat.sub_le _ _) H))
  exact ⟨by omega, v, he, mag⟩

private theorem input_passes (data : ByteArray) (cb : Tier2.Packet.CodeBlock) :
    ((Assemble.tier1Input data cb).2.toList.map (·.passes)) =
      cb.segments.toList.map (·.passes) := by
  unfold Assemble.tier1Input
  split
  · simp only [Array.toList_map, List.map_map]
    apply List.map_congr_left
    intro sg _; unfold Function.comp Assemble.directSeg; split <;> rfl
  · have fold (xs : List Tier2.Packet.Segment) (a : ByteArray × Array Seg) :
        ((xs.foldl (Equiv.concatStep data) a).2.toList.map (·.passes)) =
          a.2.toList.map (·.passes) ++ xs.map (·.passes) := by
      induction xs generalizing a with
      | nil => simp
      | cons sg xs ih => simp [ih, Equiv.concatStep]
    rw [← Array.foldl_toList]
    change ((cb.segments.toList.foldl (Equiv.concatStep data) (ByteArray.empty, #[])).2.toList.map _) = _
    simpa only [List.map_nil, List.nil_append] using fold cb.segments.toList (ByteArray.empty, #[])

/-- Stage-local bound as a function of the packet block's actual number of segments and
passes. Gathering their bytes precedes these two Tier-1 calls. -/
theorem parsed_call_work {L : Limits} {p : Header.CompParams}
    (bounds : WideHeaderBounds.ComponentBounds L p) (data : ByteArray) (r : Nat) (b : Band)
    (cb : Tier2.Packet.CodeBlock) (strict : Bool) :
    let input := Assemble.tier1Input data cb
    let rc := cb.geom.rect
    let Mb := Tier2.Packet.bandMb p r b + p.roiShift
    let zbp := if cb.included then cb.zeroBitPlanes else 0
    let n := (cb.segments.toList.map (·.passes)).sum
    let limit := 26006 + 8510 * cb.segments.size + 66002 * min n 874
    (wideCall input.1 input.2 rc.width rc.height b p.cbStyle Mb zbp strict).2 ≤ limit ∧
      (compactCall input.1 input.2 rc.width rc.height b p.cbStyle Mb zbp strict).2 ≤ limit := by
  dsimp only
  have H := call_work (Assemble.tier1Input data cb).1 (Assemble.tier1Input data cb).2
    cb.geom.rect.width cb.geom.rect.height b p.cbStyle (Tier2.Packet.bandMb p r b + p.roiShift)
    (if cb.included then cb.zeroBitPlanes else 0) strict
  have E := input_passes data cb
  have sz := congrArg List.length E
  simp only [List.length_map, Array.length_toList] at sz
  have cap := bounds.block_planes r b
  simp only [callBound, Tier1EquivM.segsPasses_eq, E, sz] at H
  constructor <;> omega

end JPEG2000.Spec.Resources.Tier1Work
