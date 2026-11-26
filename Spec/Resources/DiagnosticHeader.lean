import Spec.Resources.DiagnosticCoding
import Spec.Resources.DiagnosticGeometry
import Spec.Resources.DiagnosticTilePart

/-!
# Ordered public header diagnostics (Plan.md §§3–5, 7, S3)

T.800 A.3–A.7, B.2–B.9 and I.5.4. Follow the contiguous codestream in its
original buffer, starting with the raw/JP2 probe and ending at the geometry
work check. The trace counts diagnostic expression trees. Header payloads,
override tables, tile rectangles and work folds have their own resource meters.
-/

namespace JPEG2000.Spec.Resources.DiagnosticHeader

open Bytes Marker TilePart Header DiagnosticCost
open Tier2Equiv (bind_ok)

/-- Common bound for offsets and internally computed operands at the header sites. -/
def scalarCap (L : Limits) (n : Nat) : Nat :=
  max (DiagnosticBox.scalarCap L n) <| max (DiagnosticMarker.scalarCap L n) <|
  max (2^78) <| max (DiagnosticCoding.scalarCap L n) <| max (DiagnosticPointers.scalarCap L n) <|
  max (DiagnosticTilePart.scalarCap L n) (DiagnosticGeometry.scalarCap L)

/-- The container/main prefix, pointer and tile-part walks, main merge, repeated
overrides and tile map. The entire map can contribute at most one coding refusal. -/
def eventBudget (L : Limits) (n : Nat) : Nat :=
  DiagnosticBox.eventBound L + (DiagnosticMarker.mainBudget L n + 2) +
  DiagnosticPointers.eventBudget L n + DiagnosticTilePart.eventBudget L n + 3

private def mapResult {α β : Type} {cap k : Nat} {run : Except Error α}
    (t : Trace cap run k) (f : α → β) : Trace cap (run >>= fun a => pure (f a)) k :=
  widen (bindTrace (j := 0) t (fun _ _ => doneTrace _)) (by omega)

-- A successful coding merge has no messages. Thus an entire short-circuiting
-- map fits one slot, even if its last element is the only one that fails.
private def afterMerge {α β : Type} {cap n pos : Nat} {run : Except Error α}
    {f : α → Except Error β} (t : DiagnosticCoding.MergeTrace cap n pos run)
    (next : ∀ a, Trace cap (f a) 1) : Trace cap (run >>= f) 1 := by
  let both := bindTrace t.toTrace (fun a _ => next a)
  refine ⟨both.messages, ?_, both.origin⟩
  cases run with
  | error => exact t.countBound
  | ok a =>
    change (t.messages ++ (next a).messages).length ≤ 1
    have silent : t.messages = [] := t.events
    simpa only [silent, List.nil_append] using (next a).countBound

private def tileListTrace {L : Limits} {data : ByteArray} {rg : ByteRange}
    {r tail : Reader} {mh : MainHeader} (range : rangeReader data rg = .ok r)
    (main : parseMainHeader L r = .ok (mh,tail)) {tiles : Array Tile}
    (parsed : parseTileParts L mh tail = .ok tiles) (ov : Overrides) (defaults : Coding)
    (xs : List Tile) (member : ∀ t ∈ xs, t ∈ tiles) :
    Trace (DiagnosticCoding.scalarCap L data.size) (xs.mapM (DiagnosticGeometry.mergeTile mh ov defaults)) 1 := by
  cases xs with
  | nil => exact doneTrace _
  | cons t ts =>
    rw [List.mapM_cons]
    simp only [DiagnosticGeometry.mergeTile, bind_assoc, pure_bind]
    apply afterMerge (DiagnosticCoding.tileTrace range main parsed (member t (.head _)) ov defaults)
    intro coding
    exact mapResult (tileListTrace range main parsed ov defaults ts
      (fun x hx => member x (.tail _ hx))) _

private def tileMapTrace {L : Limits} {data : ByteArray} {rg : ByteRange}
    {r tail : Reader} {mh : MainHeader} (range : rangeReader data rg = .ok r)
    (main : parseMainHeader L r = .ok (mh,tail)) {tiles : Array Tile}
    (parsed : parseTileParts L mh tail = .ok tiles) (ov : Overrides) (defaults : Coding) :
    Trace (DiagnosticCoding.scalarCap L data.size)
      (tiles.mapM (DiagnosticGeometry.mergeTile mh ov defaults)) 1 := by
  rw [Array.mapM_eq_mapM_toList]
  exact mapResult (tileListTrace range main parsed ov defaults tiles.toList (by simp)) _

private def finishHeader (L : Limits) (data : ByteArray) (c : Box.Container)
    (mh : MainHeader) (tail : Reader) : Except Error Header := do
  checkGeometry L mh
  let defaults ← mainCoding mh
  let (tlm,ppm) ← parsePointers L mh data
  let tiles ← parseTileParts L mh tail
  let ov ← mkOverrides mh.endPos mh.siz.csiz mh.coc mh.qcc mh.rgn
  let tps ← tiles.mapM (DiagnosticGeometry.mergeTile mh ov defaults)
  let _ ← checkWork L mh.siz defaults tps
  return { siz := mh.siz, numTilesX := numTilesX mh.siz, numTilesY := numTilesY mh.siz,
           defaults, tiles := tps, tlm, ppm, main := mh, codestream := c.codestream,
           container := if c.fileType.isSome then some c else none }

private theorem parse_split (L : Limits) (data : ByteArray) :
    Header.parse L data = (DiagnosticMarker.throughMain L data >>= fun (c,mh,tail) =>
      finishHeader L data c mh tail) := by
  simp only [Header.parse, parseCodestreamIn, DiagnosticMarker.throughMain, DiagnosticMarker.inRange,
    bind_assoc, pure_bind, finishHeader]
  rfl

private theorem main_facts {L : Limits} {data : ByteArray} {c : Box.Container}
    {mh : MainHeader} {tail : Reader} (ok : DiagnosticMarker.throughMain L data = .ok (c,mh,tail)) :
    Box.parseFile L data = .ok c ∧ ∃ r, rangeReader data ⟨c.codestream.start,c.codestream.len⟩ = .ok r ∧
      parseMainHeader L r = .ok (mh,tail) := by
  unfold DiagnosticMarker.throughMain at ok
  obtain ⟨_,box,ok⟩ := bind_ok ok
  obtain ⟨⟨_,_⟩,inside,ok⟩ := bind_ok ok
  cases ok
  exact ⟨box,bind_ok inside⟩

/-- The complete ordered trace indexed by the production parser on arbitrary bytes.
The evidence for the final work trace comes from the actual successful tile map,
including when the immediately following work guard refuses. -/
def headerTrace (L : Limits) (data : ByteArray) :
    Trace (scalarCap L data.size) (Header.parse L data) (eventBudget L data.size) := by
  rw [parse_split]
  let prefixTrace := DiagnosticMarker.throughMainTrace L data
    (cap := scalarCap L data.size) (by unfold scalarCap; omega) (by unfold scalarCap; omega)
  let rest := DiagnosticPointers.eventBudget L data.size + DiagnosticTilePart.eventBudget L data.size + 3
  apply widen (bindTrace (j := rest) prefixTrace ?_) (by unfold rest eventBudget; omega)
  rintro ⟨c,mh,tail⟩ reached
  have facts := main_facts reached
  cases range : rangeReader data ⟨c.codestream.start,c.codestream.len⟩ with
  | error e =>
    exact False.elim (by obtain ⟨_,hr,_⟩ := facts.2; rw [hr] at range; contradiction)
  | ok r =>
    have main : parseMainHeader L r = .ok (mh,tail) := by
      obtain ⟨r',hr,read⟩ := facts.2
      cases hr.symm.trans range
      exact read
    have geo : DiagnosticGeometry.geometryInput L data = .ok (mh,tail) := by
      simp only [DiagnosticGeometry.geometryInput, facts.1, range, main, bind, Except.bind]
    unfold finishHeader
    have codingCap : DiagnosticCoding.scalarCap L data.size ≤ scalarCap L data.size := by
      unfold scalarCap; omega
    apply widen (bindTrace (j := 1 + 1 + DiagnosticTilePart.eventBudget L data.size +
      DiagnosticPointers.eventBudget L data.size + 1)
      ((DiagnosticGeometry.geometryTrace main).raiseCap (by unfold scalarCap; omega)) ?_) (by unfold rest; omega)
    rintro ⟨⟩ grid
    apply bindTrace ((DiagnosticCoding.mainTrace range main).toTrace.raiseCap codingCap)
    intro defaults made
    apply bindTrace ((DiagnosticPointers.pointerTrace range main).raiseCap (by unfold scalarCap; omega))
    rintro ⟨tlm,ppm⟩ pointers
    apply bindTrace ((DiagnosticTilePart.tilePartsTrace range main grid).raiseCap (by unfold scalarCap; omega))
    intro tiles assembled
    apply bindTrace ((DiagnosticCoding.overridesTrace range main).toTrace.raiseCap codingCap)
    intro ov overrides
    apply bindTrace ((tileMapTrace range main assembled ov defaults).raiseCap codingCap)
    intro tps mapped
    have work : DiagnosticGeometry.workInput L data = .ok (mh,defaults,tps) := by
      simp only [DiagnosticGeometry.workInput, geo, grid, made, pointers, assembled,
        overrides, mapped, bind, Except.bind, pure, Except.pure]
    exact mapResult ((DiagnosticGeometry.workTrace work).raiseCap (by unfold scalarCap; omega)) _

/-- The common prefix of the native and image decoders, ending before native tile admission. -/
def publicPrefix (L : Limits) (data : ByteArray) (red : Nat) : Except Error Header := do
  L.check Decode.loc .decompLevels red
  Header.parse L data

/-- The native entry point and its packet-work observation share this prefix
on either outcome. The next operation of tile preparation allocates native
destinations from the admitted header, before the shared PPM rank check. -/
theorem public_placement (L : Limits) (data : ByteArray) (red : Nat) :
    decodeCodestream L data red =
      (publicPrefix L data red >>= fun h => Decode.nativeFromHeader L h data red) ∧
    PublicPacketWork.prepareTiles L data red = (publicPrefix L data red >>= fun h => do
      let dst ← JPEG2000.NativeOutput.allocOutput L h.siz red
      return (h,dst)) := by
  simp only [decodeCodestream, PublicPacketWork.prepareTiles, publicPrefix, bind_assoc, and_self]

/-- Trace of the public prefix. The extra capacity accommodates the borrowed
caller value on early reduction refusal. All header trees use the header cap. -/
def publicTrace (L : Limits) (data : ByteArray) (red : Nat) :
    Trace (max red (scalarCap L data.size)) (publicPrefix L data red) (eventBudget L data.size) :=
  bindTrace (i := 0) (j := eventBudget L data.size) (checkedTrace L Decode.loc .decompLevels red (Nat.zero_le _) (Nat.le_max_left ..))
    (fun _ _ => (headerTrace L data).raiseCap (Nat.le_max_right ..))

private theorem gate_messages {α : Type} {cap k : Nat} {gate : Except Error Unit} {run : Except Error α}
    (g : Trace cap gate 0) (t : Trace cap run k) :
    (bindTrace g (fun _ _ => t)).messages = (match (generalizing := false) gate with
      | .error _ => []
      | .ok _ => t.messages) := by
  have silent : g.messages = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp g.countBound)
  cases gate <;> simp [bindTrace, silent]

/-- Both public callers reach exactly the parser's original strings and trees
when reduction is admitted, including on later refusals. An excessive reduction
constructs no header text. -/
theorem public_events (L : Limits) (data : ByteArray) (red : Nat) :
    ((publicTrace L data red).messages.map fun m => (m.1,m.2.tree)) =
      if red ≤ L.maxDecompLevels then ((headerTrace L data).messages.map fun m => (m.1,m.2.tree))
      else [] := by
  unfold publicTrace
  rw [gate_messages]
  by_cases h : red ≤ L.maxDecompLevels
  · have ok := (Limits.check_eq_ok_iff L Decode.loc .decompLevels red).2 h
    simp only [ok, ite_eq_left h, Trace.raiseCap_events]
  · have bad : L.check Decode.loc .decompLevels red =
        .error (.limitExceeded Decode.loc .decompLevels red L.maxDecompLevels) := by
      simp [Limits.check, Limits.checkLe, Limits.bound, h]
    simp only [bad, ite_eq_right h, List.map_nil]

/-- Diagnostic construction work and cumulative temporary storage for the
public header prefix on all inputs, independently of the caller's reduction. -/
theorem public_cost (L : Limits) (data : ByteArray) (red : Nat) :
    let ms := (publicTrace L data red).messages
    let budget := eventBudget L data.size * Text.workBound (scalarCap L data.size) 128 24
    (ms.map (fun m => m.2.tree.work)).sum ≤ budget ∧
      (ms.map (fun m => m.2.tree.storage)).sum ≤ budget := by
  have events := public_events L data red
  have work := congrArg (List.sum ∘ List.map (fun m : String × Text => m.2.work)) events
  have store := congrArg (List.sum ∘ List.map (fun m : String × Text => m.2.storage)) events
  dsimp only
  by_cases h : red ≤ L.maxDecompLevels
  · simp only [ite_eq_left h, Function.comp_apply, List.map_map, Function.comp_def] at work store
    rw [work, store]
    exact ⟨(trace_cost (headerTrace L data)).1, trace_storage (headerTrace L data)⟩
  · simp only [ite_eq_right h, Function.comp_apply, List.map_map, Function.comp_def,
      List.map_nil, List.sum_nil] at work store
    rw [work, store]
    exact ⟨Nat.zero_le _, Nat.zero_le _⟩

/-- A refusal of the shared prefix is the exact stored error, including its
location, in both public results. A header refusal retains bounded internal
fields. A reduction refusal borrows both caller naturals and occupies seven slots. -/
theorem public_refusal {L : Limits} {data : ByteArray} {opts : DecodeOptions} {e : Error}
    (bad : publicPrefix L data opts.reduce = .error e) :
    let cap := scalarCap L data.size
    decodeCodestream L data opts.reduce = .error e ∧ JPEG2000.decode L data opts = .error e ∧
      (if opts.reduce ≤ L.maxDecompLevels then
        Header.parse L data = .error e ∧ e.offset?.getD 0 ≤ cap ∧
        storedPayload false e ≤ 6 + Text.byteBound cap 128 24 + 2*bits cap
       else e = .limitExceeded Decode.loc .decompLevels opts.reduce L.maxDecompLevels ∧
        storedPayload true e = 7) := by
  have raw : decodeCodestream L data opts.reduce = .error e := by
    rw [(public_placement ..).1, bad]; rfl
  refine ⟨raw, by simp only [JPEG2000.decode, raw, bind, Except.bind], ?_⟩
  by_cases admitted : opts.reduce ≤ L.maxDecompLevels
  · rw [ite_eq_left admitted]
    have gate := (Limits.check_eq_ok_iff L Decode.loc .decompLevels opts.reduce).2 admitted
    have header : Header.parse L data = .error e := by
      simpa only [publicPrefix, gate, bind, Except.bind] using bad
    exact ⟨header, ((headerTrace L data).origin e header).1, trace_retained (headerTrace L data) header⟩
  · rw [ite_eq_right admitted]
    have gate := DiagnosticCost.reduction_storage (d := data) (opts := opts) (Nat.lt_of_not_ge admitted)
    have eq := Except.error.inj (raw.symm.trans gate.1)
    exact ⟨eq, eq ▸ gate.2.2⟩

end JPEG2000.Spec.Resources.DiagnosticHeader
