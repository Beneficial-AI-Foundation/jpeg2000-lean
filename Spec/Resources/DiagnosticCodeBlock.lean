import Spec.Resources.DiagnosticCost
import Spec.Resources.NativeCost

/-!
# Native code-block reader diagnostics (Plan.md §§3–5, 7, S3)

T.800 B.10.7 supplies codeword segments to the Annex C and D readers. Both native
callers check the original packet ranges before borrowing the input or gathering
fragmented segments. Each decoder constructs its diagnostic only in a failing branch.
The scan kernels and the D.5 bad-symbol counter return ordinary values. In particular,
the native wide caller selects the lenient symbol policy.
-/

namespace JPEG2000.Spec.Resources.DiagnosticCodeBlock

open JPEG2000.Header JPEG2000.Tier2.Geometry JPEG2000.Tier2.Packet
open JPEG2000.Tier1 DiagnosticCost

noncomputable section

-- The constructors mirror the two throws at this boundary. The text argument is
-- instantiated at the throw site, where its literal and UTF-8 size are known.
private inductive Observation {α : Type} : Except Error α → Type where
  | ok (a : α) : Observation (.ok a)
  | malformed (s : String) (size : s.utf8ByteSize ≤ 128) :
    Observation (.error (.malformed tier1Loc s))
  | unsupported (s : String) (size : s.utf8ByteSize ≤ 128) :
    Observation (.error (.unsupported tier1Loc s))

private def Observation.trace {α : Type} {r : Except Error α} (obs : Observation r) :
    Trace 0 r 1 := by
  cases obs with
  | ok a => exact doneTrace a
  | malformed s size | unsupported s size =>
    let msg := (⟨s, oneFixed s size⟩ : Σ t, Built 0 t)
    exact ⟨[msg], by simp, by intro e eq; cases eq; exact ⟨Nat.le_refl 0, msg, by simp, rfl⟩⟩

private def next {α β : Type} {r : Except Error α} {f : α → Except Error β}
    (obs : Observation r) (k : ∀ a, Observation (f a)) : Observation (r >>= f) := by
  cases obs with
  | ok a => exact k a
  | malformed s h => exact .malformed s h
  | unsupported s h => exact .unsupported s h

private def mapped {α β : Type} {r : Except Error α} (obs : Observation r) (f : α → β) :
    Observation (r.map f) := by
  cases obs with
  | ok a => exact .ok (f a)
  | malformed s h => exact .malformed s h
  | unsupported s h => exact .unsupported s h

-- Reduce the successive guards of a validator. Successful guards pass Unit
-- without evaluating the throw branch, even when the next guard rejects.
local macro "observeGuards" : tactic => `(tactic|
  (simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
   repeat' first | exact .ok _ | exact .malformed _ (by decide) |
     exact .unsupported _ (by decide) | split))

private def singleValidation (data : ByteArray) (lo hi w h K n : Nat) :
    Observation (validate data lo hi w h K n) := by
  unfold validate
  observeGuards

private def compactValidation (data : ByteArray) (segs : Array Seg) (w h : Nat)
    (m : Style) (K : Nat) : Observation (validateSegs data segs w h m K) := by
  unfold validateSegs
  observeGuards

private def wideValidation (m : Style) (kept : Array Seg) (K : Nat) :
    Observation (WideSegments.validatePasses m kept K) := by
  unfold WideSegments.validatePasses
  observeGuards

private def sizeValidation (w h : Nat) : Observation (WidePlain.validateSize w h) := by
  unfold WidePlain.validateSize
  split
  · exact .malformed _ (by decide)
  · exact .ok ()

private def singleBlock (data : ByteArray) (lo hi w h : Nat) (b : Band) (Mb zbp n : Nat) :
    Observation (decodeCodeBlockExact data lo hi w h b Mb zbp n) := by
  unfold decodeCodeBlockExact
  exact next (singleValidation ..) (fun _ => .ok _)

private def compactSegments (data : ByteArray) (segs : Array Seg) (w h : Nat)
    (b : Band) (style : UInt8) (Mb zbp : Nat) :
    Observation (decodeCodeBlockSegs data segs w h b style Mb zbp) := by
  unfold decodeCodeBlockSegs
  split
  · exact .malformed _ (by decide)
  unfold decodeCodeBlockSegsExact
  apply mapped
  unfold decodeSegsCore
  apply next (compactValidation ..)
  intro _
  split
  · split <;> exact next (singleBlock ..) (fun _ => .ok _)
  · exact .ok _

private def plainSegments (data : ByteArray) (segs : Array Seg) (w h : Nat)
    (b : Band) (Mb zbp : Nat) :
    Observation (WidePlain.decodeCodeBlockSegs data segs w h b Mb zbp) := by
  unfold WidePlain.decodeCodeBlockSegs
  split
  · exact .malformed _ (by decide)
  apply next (sizeValidation ..)
  intro _
  observeGuards

private def wideSegments (data : ByteArray) (segs : Array Seg) (w h : Nat)
    (b : Band) (style : UInt8) (Mb zbp : Nat) :
    Observation (WideSegments.decodeCodeBlockSegs data segs w h b style Mb zbp false) := by
  unfold WideSegments.decodeCodeBlockSegs
  dsimp only
  split
  · exact plainSegments ..
  split
  · exact .malformed _ (by decide)
  apply next (sizeValidation ..)
  intro _
  exact next (wideValidation ..) (fun _ => .ok _)

private def compactBlock (data : ByteArray) (p : CompParams) (r : Nat) (b : Band) (cb : CodeBlock) :
    Observation (JPEG2000.ReversibleDispatch.checkedBlock data p r b cb) := by
  unfold JPEG2000.ReversibleDispatch.checkedBlock
  split
  · exact compactSegments ..
  · exact .malformed _ (by decide)

private def wideBlock (data : ByteArray) (p : CompParams) (r : Nat) (b : Band) (cb : CodeBlock) :
    Observation (JPEG2000.WideAssembly.decodeBlock data p r b cb) := by
  unfold JPEG2000.WideAssembly.decodeBlock
  cases hr : cb.segments.all (fun s => s.ranges.all (fun rg => rg.offset + rg.length ≤ data.size)) <;>
    simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  · exact .malformed _ (by decide)
  · exact wideSegments ..

/-- Trace the compact reader on any packet record. A rejected original range
precedes gathering. Plain-mode validation includes the second, single-codeword
check, using the zero-length codeword when the retained list is empty. -/
def compactTrace (data : ByteArray) (p : CompParams) (r : Nat) (b : Band) (cb : CodeBlock) :
    Trace 0 (JPEG2000.ReversibleDispatch.checkedBlock data p r b cb) 1 :=
  (compactBlock data p r b cb).trace

/-- Trace the wide reader independently on the original packet record, so a
retry can retain an earlier compact diagnostic. Both plain-like and mode-aware
readers validate the full input ranges before clamping and checking the style. -/
def wideTrace (data : ByteArray) (p : CompParams) (r : Nat) (b : Band) (cb : CodeBlock) :
    Trace 0 (JPEG2000.WideAssembly.decodeBlock data p r b cb) 1 :=
  (wideBlock data p r b cb).trace

/-- The emitted expression for each textual Tier-1 refusal. Range endpoints,
dimensions, pass indices and plane counts only control branches here. -/
def literalMessages {α : Type} : Except Error α → List Text
  | .error (.malformed _ s) | .error (.unsupported _ s) => [.fixed s]
  | _ => []

private theorem Observation.messages {α : Type} {run : Except Error α} (obs : Observation run) :
    (obs.trace.messages.map fun m => m.2.tree) = literalMessages run := by
  cases obs <;> rfl

/-- Exact message trees for either native attempt, including a compact error
that a caller discards. A successful pass or reader restart emits no messages. -/
theorem reader_messages (data : ByteArray) (p : CompParams) (r : Nat) (b : Band) (cb : CodeBlock) :
    ((compactTrace data p r b cb).messages.map fun m => m.2.tree) =
      literalMessages (JPEG2000.ReversibleDispatch.checkedBlock data p r b cb) ∧
    ((wideTrace data p r b cb).messages.map fun m => m.2.tree) =
      literalMessages (JPEG2000.WideAssembly.decodeBlock data p r b cb) :=
  ⟨(compactBlock ..).messages, (wideBlock ..).messages⟩

open Tier1Work

-- Array.all visits the failing element and skips its suffix. At the outer
-- level a segment with no byte ranges still contributes one segment visit.
private def tested {α : Type} (p : α → Bool) : List α → List α
  | [] => []
  | x :: xs => x :: (if p x then tested p xs else [])

private theorem tested_spec {α : Type} (p : α → Bool) (xs : List α) (weight : α → Nat) :
    (tested p xs).all p = xs.all p ∧ (tested p xs).length ≤ xs.length ∧
      ((tested p xs).map weight).sum ≤ (xs.map weight).sum := by
  induction xs with
  | nil => simp [tested]
  | cons x xs ih =>
    cases hx : p x <;> simp [tested, hx, ih.1, ih.2.1, ih.2.2]

private def fits (data : ByteArray) (rg : JPEG2000.TilePart.ByteRange) :=
  decide (rg.offset + rg.length ≤ data.size)

/-- Source ranges examined by each reached segment predicate, in packet order.
The last row includes the first invalid range if validation stops there. -/
def testedRanges (data : ByteArray) (cb : CodeBlock) : List (List JPEG2000.TilePart.ByteRange) :=
  (tested (fun s : Segment => s.ranges.all (fits data)) cb.segments.toList).map
    fun s => tested (fits data) s.ranges.toList

private theorem source_spec (data : ByteArray) (cb : CodeBlock) :
    let rows := testedRanges data cb
    rows.all (fun rs => rs.all (fits data)) = cb.segments.all (fun s => s.ranges.all (fits data)) ∧
    rows.length ≤ cb.segments.size ∧ rows.flatten.length ≤ AssemblyCost.rangeCount cb := by
  let p := fun s : Segment => s.ranges.all (fits data)
  have outer := tested_spec p cb.segments.toList (·.ranges.size)
  have inner (s : Segment) := tested_spec (fits data) s.ranges.toList (fun _ => 0)
  have sum (xs : List Segment) :
      (xs.map (fun s => (tested (fits data) s.ranges.toList).length)).sum ≤
      (xs.map (·.ranges.size)).sum := by
    induction xs with
    | nil => exact Nat.le_refl 0
    | cons s xs ih => exact Nat.add_le_add (by simpa using (inner s).2.1) ih
  refine ⟨?_, by simpa [testedRanges, p] using outer.2.1, ?_⟩
  · simpa only [testedRanges, List.all_map, Function.comp_def, (inner _).1, Array.all_toList, p]
      using outer.1
  · simp only [testedRanges, List.length_flatten, List.map_map, Function.comp_def]
    exact Nat.le_trans (sum _) outer.2.2

/-- Both readers use the short-circuit source scan. Only a successful scan
enters the indicated metered segmented calls on the actual gathered input.
A rejection at either level of the scan constructs the fixed range diagnostic. -/
theorem reader_calls (data : ByteArray) (p : CompParams) (r : Nat) (b : Band) (cb : CodeBlock) :
    let rows := testedRanges data cb
    let compact := JPEG2000.ReversibleDispatch.checkedBlock data p r b cb
    let wide := JPEG2000.WideAssembly.decodeBlock data p r b cb
    rows.length ≤ cb.segments.size ∧ rows.flatten.length ≤ AssemblyCost.rangeCount cb ∧
    if rows.all (fun rs => rs.all fun rg => rg.offset + rg.length ≤ data.size) then
      let input := Assemble.tier1Input data cb
      let rc := cb.geom.rect
      let Mb := bandMb p r b + p.roiShift
      let zbp := if cb.included then cb.zeroBitPlanes else 0
      compact = (compactCall input.1 input.2 rc.width rc.height b p.cbStyle Mb zbp false).1 ∧
      wide = (wideCall input.1 input.2 rc.width rc.height b p.cbStyle Mb zbp false).1
    else
      let err := Error.malformed tier1Loc "code-block data range outside the buffer"
      compact = .error err ∧ wide = .error err := by
  obtain ⟨eq, n, k⟩ := source_spec data cb
  refine ⟨n, k, ?_⟩
  dsimp only
  change ((testedRanges data cb).all fun rs => rs.all fun rg => rg.offset + rg.length ≤ data.size) =
    (cb.segments.all fun s => s.ranges.all fun rg => rg.offset + rg.length ≤ data.size) at eq
  rw [eq]
  unfold JPEG2000.ReversibleDispatch.checkedBlock JPEG2000.WideAssembly.decodeBlock
  cases hr : cb.segments.all (fun s => s.ranges.all fun rg => rg.offset + rg.length ≤ data.size) <;>
    simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
  · exact ⟨trivial, rfl⟩
  · exact ⟨(compact_value _ _ _ _ _ _ _ _ false).symm, (wide_value ..).symm⟩

private theorem keptRanges {wide : Bool} {data : ByteArray} {segs kept : Array Seg}
    {w h K : Nat} {m : Style} (ok : (preflight wide data segs w h m K).1 = .ok kept) :
    ∀ sg ∈ kept.toList, sg.start ≤ sg.stop ∧ sg.stop ≤ data.size := by
  have valid : badRange data segs = false := by
    cases hr : badRange data segs with
    | false => rfl
    | true => rw [(bad_range_work hr wide w h m K).1] at ok; contradiction
  rw [(preflight_ok ok).1]
  apply Tier1EquivM.clampSegs_range
  simp only [badRange, ← Array.any_toList, List.any_eq_false, Bool.or_eq_true,
    decide_eq_true_eq] at valid
  intro sg hs
  have := valid sg hs
  omega

/-- Validation work through the first rejection, then the callback domains
when the code-block decoder reaches its retained pass prefix. The schedule
counts actual D.4 codewords and D.2 passes. Compact plain uses one initial
reader even for its zero-pass fallback. -/
def ScanBounds (L : Limits) (wide : Bool) (buf : ByteArray) (segs : Array Seg)
    (w h : Nat) (style : UInt8) (K : Nat) : Prop :=
  let m := Style.ofByte style
  let pre := preflight wide buf segs w h m K
  pre.2 ≤ 10 * SegmentHistory.segmentLimit L + 2 * 874 + 5 ∧
  ∀ kept, pre.1 = .ok kept →
    segsPasses kept = min (segsPasses segs) (3*K-2) ∧
    kept.size ≤ SegmentHistory.segmentLimit L ∧
    segsPasses kept ≤ (if wide then 874 else 91) ∧
    (schedule kept.toList 0).length = kept.size + segsPasses kept ∧
    w*h ≤ 4096 ∧ (w+2)*(h+2) ≤ 8196 ∧
    (∀ sg ∈ kept.toList, sg.start ≤ sg.stop ∧ sg.stop ≤ buf.size) ∧
    (schedule kept.toList 0).filterMap (fun | .pass j => some j | _ => none) =
      List.range' 0 (segsPasses kept) ∧
    (wide = false → m.decodesAsPlain = true →
      kept.toList.map (·.passes) = if segsPasses kept = 0 then [] else [segsPasses kept])

private theorem scanBounds {L : Limits} (wide : Bool) (buf : ByteArray) (segs : Array Seg)
    (w h : Nat) (style : UInt8) (K : Nat) (planes : K ≤ 292)
    (segments : segs.size ≤ SegmentHistory.segmentLimit L) : ScanBounds L wide buf segs w h style K := by
  have work := preflight_work wide buf segs w h (Style.ofByte style) K
  refine ⟨by omega, ?_⟩
  intro kept ok
  obtain ⟨passes, count, _, n, area, border⟩ := preflight_domains ok
  obtain ⟨indices, length⟩ := schedule_counts kept.toList 0
  refine ⟨passes, Nat.le_trans count segments, n, ?_, area, border, keptRanges ok, ?_, ?_⟩
  · simpa only [Array.length_toList, Tier1EquivM.segsPasses_eq] using length
  · rw [Tier1EquivM.segsPasses_eq, ← indices]
    congr 1
  · rintro rfl plain
    exact compact_plain_prefix plain ok

/-- Bounds at a native block callback. The segment and range counts cover
the original packet scan even on its first invalid range. The two Tier-1
meters include the actual MQ/raw reads, all scan callbacks and the compact
plain recheck. Each bound is for one invocation. -/
def ReaderBounds (L : Limits) (data : ByteArray) (p : CompParams) (r : Nat) (b : Band)
    (cb : CodeBlock) : Prop :=
  let input := Assemble.tier1Input data cb
  let rc := cb.geom.rect
  let Mb := bandMb p r b + p.roiShift
  let zbp := if cb.included then cb.zeroBitPlanes else 0
  let bound := 26006 + 8510 * SegmentHistory.segmentLimit L + 66002 * 874
  cb.segments.size ≤ SegmentHistory.segmentLimit L ∧
  AssemblyCost.rangeCount cb ≤ SegmentHistory.rangeLimit L ∧
  input.1.size ≤ max 1 (SegmentHistory.rangeLimit L) * data.size ∧
  input.2.size ≤ SegmentHistory.segmentLimit L ∧
  (∀ wide, ScanBounds L wide input.1 input.2 rc.width rc.height p.cbStyle (Mb-zbp)) ∧
  (compactCall input.1 input.2 rc.width rc.height b p.cbStyle Mb zbp false).2 ≤ bound ∧
  (wideCall input.1 input.2 rc.width rc.height b p.cbStyle Mb zbp false).2 ≤ bound

private theorem selectedBounds {L : Limits} {data : ByteArray} {g : Progression.Layout}
    {a : Option TileCodeBlocks} (storage : NativeCost.BlockStorage L data g a)
    (stores : (ReconstructionCost.storeCaps L).Holds g a) (i : Fin g.numComps)
    (params : WideHeaderBounds.ComponentBounds L (g.comp i).params)
    (r : Nat) {pr : PrecinctOut} (hp : pr ∈ (AssemblyCost.selected a i).getD r #[])
    {bo : BandOut} (hb : bo ∈ pr.bands) {cb : CodeBlock} (hc : cb ∈ bo.blocks) :
    ReaderBounds L data (g.comp i).params r bo.band cb := by
  obtain ⟨descriptors, gather, _⟩ := storage i r pr hp bo hb cb hc
  obtain ⟨segs, ranges⟩ := (((stores i r).2 pr hp).2 bo hb).2 cb hc
  change cb.segments.size ≤ SegmentHistory.segmentLimit L at segs
  have bytes : (Assemble.tier1Input data cb).1.size ≤ max 1 (SegmentHistory.rangeLimit L)*data.size := by
    split at gather
    · rw [gather]
      simpa only [Nat.one_mul] using
        Nat.mul_le_mul_right data.size (Nat.le_max_left 1 (SegmentHistory.rangeLimit L))
    · exact Nat.le_trans gather.2.1 (Nat.mul_le_mul_right _ (Nat.le_max_right ..))
  have planes := params.block_planes r bo.band
  obtain ⟨wide, packed⟩ := parsed_call_work params data r bo.band cb false
  exact ⟨segs, ranges, bytes, descriptors, fun wide =>
    scanBounds wide _ _ _ _ _ _ (by omega) descriptors, by omega, by omega⟩

/-- At any block of an admitted, visited tile, both reader budgets come
from the actual ranked packet store, including when a reader rejects. When
wide decoding succeeds, every cell passed to the next callback satisfies the
parsed quantisation operand bound for this component and band. -/
theorem public_readers {L : Limits} {data : ByteArray} {red : Nat} {v : PacketTraversal.TileVisit}
    (hit : v ∈ (PublicPacketWork.measure L data red).1) {h dst idx a g coding}
    (entry : PublicPacketWork.prepareTiles L data red = .ok (h,dst))
    (ranks : NativeCost.ranks L h = .ok idx)
    (store : SegmentHistory.packetStore L h data idx v.tile v.cursor v.passesBefore = .ok a)
    (layout : Progression.Layout.ofHeader h v.tile = .ok (g,coding))
    (admitted : tileCells g red ≤ L.maxWorkSamples) (i : Fin g.numComps)
    (r : Nat) {pr : PrecinctOut} (hp : pr ∈ (AssemblyCost.selected a i).getD r #[])
    {bo : BandOut} (hb : bo ∈ pr.bands) {cb : CodeBlock} (hc : cb ∈ bo.blocks) :
    ReaderBounds L data (g.comp i).params r bo.band cb ∧
    ∀ cs, JPEG2000.WideAssembly.decodeBlock data (g.comp i).params r bo.band cb = .ok cs →
      ∀ z ∈ cs, WideArithmetic.QuantOperands
        (Spec.Quant.bandQuant (g.comp i).params (h.siz.components.getD i default).depth.toNat r bo.band)
        (Assemble.fracBitsOf h.siz (coding.mctApplies h.siz) i) z WideArithmetic.part1QuantLimit ∧
        WideArithmetic.part1QuantLimit ≤ 2^372 := by
  obtain ⟨_, _, _, oldEntry, oldRanks, resources⟩ := NativeCost.reconstruction_storage L data red v hit
  rw [entry] at oldEntry
  cases oldEntry
  rw [ranks] at oldRanks
  cases oldRanks
  simp only [NativeCost.ReconstructionStorage, store, layout, admitted, ↓reduceIte] at resources
  unfold PublicPacketWork.prepareTiles at entry
  obtain ⟨_, _, tail⟩ := Tier2Equiv.bind_ok entry
  obtain ⟨_, parsed, tail⟩ := Tier2Equiv.bind_ok tail
  obtain ⟨_, _, ret⟩ := Tier2Equiv.bind_ok tail
  cases ret
  exact ⟨selectedBounds resources.2.1 resources.1 i (WideHeaderBounds.parsed_component_bounds
    parsed layout i red).1 r hp hb hc, fun _ ok => ReconstructionCost.block_operands parsed layout i
    r bo.band cb ok⟩

end

end JPEG2000.Spec.Resources.DiagnosticCodeBlock
