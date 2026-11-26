import Spec.Resources.PacketSchedule
import Spec.Equiv
import Spec.Tier2Equiv.Tile

/-!
# The executed Tier-2 prefix

Plan.md §§3–5, 7, T.800 A.7.4–5 and B.9–12. A physical position is
recorded even when a previous POC volume contains the packet. A first
occurrence records the outcome of the production packet callback. Passes
are charged when its cumulative check admits the packet. A rejecting
callback costs an attempt and transfers no passes to Tier-1.
-/

namespace JPEG2000.Spec.Resources.PacketTraversal

open JPEG2000.Header JPEG2000.Bytes JPEG2000.TilePart JPEG2000.Progression
open JPEG2000.Tier2.Packet JPEG2000.Tier2.Headers

/-- What happened at a physical position in one progression volume. -/
inductive PacketAction where
  | skip
  | rejected
  | accepted (newPasses : Nat)

/-- The exact physical positions visited in order, including the final failed attempt. -/
abbrev PacketLog := List (Position × PacketAction)

/-- Number of newly admitted passes at this position. -/
def PacketAction.passes : PacketAction → Nat
  | .accepted n => n
  | _ => 0

/-- A packet-header callback was entered at this position. -/
def PacketAction.attempted : PacketAction → Bool
  | .skip => false
  | _ => true

/-- Total pass charge of the admitted packets. -/
def passSum (xs : PacketLog) : Nat := (xs.map (fun x => x.2.passes)).sum

/-- First-occurrence packet callbacks, including a possible rejecting callback. -/
def attempts (xs : PacketLog) : Nat := xs.countP (fun x => x.2.attempted)

/-- A computation that retains the log even when its result is an error. -/
abbrev Measured (log α : Type) := List log × Except Error α

private def prepend {log α : Type} (x : log) (r : Measured log α) : Measured log α :=
  (x :: r.1, r.2)

/-- The production callback from the streaming packet loop. -/
def packetStep (L : Limits) (coding : Coding) (base : Array (Array Nat)) (same : Bool)
    (pb : Nat) (s : LoopState) (p : PacketId) : Except Error LoopState := do
  let idx := ((base.getD p.comp #[]).getD p.res 0) + p.prec
  let some st := s.precs[idx]? | throw (.malformed JPEG2000.Tier2.Packet.loc "precinct index out of range")
  let precs := s.precs.setIfInBounds idx default
  let (st, info, hdr, body) ← decodePacket L coding.sop coding.eph s.seq p.layer st same s.hdr s.body
  let passes := s.passes + info.newPasses
  L.check JPEG2000.Tier2.Packet.loc .codingPasses (pb + passes)
  return { precs := precs.setIfInBounds idx st, hdr, body, seq := s.seq + 1,
           empty := s.empty + (if info.empty then 1 else 0),
           sops := s.sops + (if info.sop then 1 else 0),
           hdrBytes := s.hdrBytes + info.headerBytes, bodyBytes := s.bodyBytes + info.bodyBytes, passes }

private theorem bind_ok {α β : Type} {x : Except Error α} {f : α → Except Error β} {b : β} :
    (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp [bind, Except.bind]

private theorem branches {α β : Type} (c : Prop) [Decidable c] (x y : Except Error α)
    (f : α → Except Error β) :
    (if c then x >>= f else y >>= f) = (if c then x else y) >>= f := by split <;> rfl

/-- The reported new passes sum the actual segment-piece pass counts supplied to
the successful body read. This applies to both inline and packed headers. -/
theorem decodePacket_contributions {L : Limits} {sop eph seq layer st same hdr body st' info hdr' body'}
    (ok : decodePacket L sop eph seq layer st same hdr body = .ok (st', info, hdr', body')) :
    ∃ found body1 nonEmpty br pre cs bits aligned head,
      (if sop then readSop seq body else pure (false, body)) = .ok (found, body1) ∧
      readBit (BitReader.ofReader (if same then body1 else hdr)) = .ok (nonEmpty, br) ∧
      (if nonEmpty then headerBands L layer st br else pure (st, #[], br)) = .ok (pre, cs, bits) ∧
      bits.align = .ok aligned ∧
      (if eph then readEph (aligned.toReader .tier2) else pure (aligned.toReader .tier2)) = .ok head ∧
      readBody pre cs (if same then head else body1) = .ok (st', body') ∧
      info.newPasses = cs.foldl (fun a c => c.pieces.foldl (fun n p => n + p.1) a) 0 := by
  simp only [decodePacket, branches, bind_ok] at ok
  obtain ⟨⟨found, body1⟩, sopRead, ⟨nonEmpty, br⟩, bitRead, ⟨pre, cs, bits⟩, bands,
    aligned, align, head, ephRead, ⟨_, _⟩, read, ok⟩ := ok
  cases ok
  exact ⟨found, body1, nonEmpty, br, pre, cs, bits, aligned, head,
    sopRead, bitRead, bands, align, ephRead, read, rfl⟩

/-- Every charged difference comes from the actual packet read on the current precinct
and readers. The callback checks the new cumulative count before returning. -/
theorem packetStep_passes {L : Limits} {c base same pb s p s'}
    (ok : packetStep L c base same pb s p = .ok s') :
    ∃ st st' info hdr body,
      s.precs[((base.getD p.comp #[]).getD p.res 0) + p.prec]? = some st ∧
      decodePacket L c.sop c.eph s.seq p.layer st same s.hdr s.body = .ok (st', info, hdr, body) ∧
      s'.passes = s.passes + info.newPasses ∧ s'.seq = s.seq + 1 ∧
      pb + s'.passes ≤ L.maxCodingPasses := by
  simp only [packetStep] at ok
  split at ok
  · rename_i st selected
    simp only [bind_ok] at ok
    obtain ⟨⟨st', info, hdr, body⟩, read, u, checked, ok⟩ := ok
    cases ok
    exact ⟨st, st', info, hdr, body, selected, read, rfl, rfl, (Limits.check_eq_ok_iff ..).1 checked⟩
  · cases ok

/-- Visit the physical schedule until the first error, retaining the accepted pass
deltas of the actual packet-step states. -/
def walk (f : LoopState → PacketId → Except Error LoopState) :
    List Position → LoopState → Measured (Position × PacketAction) LoopState
  | [], s => ([], .ok s)
  | p :: ps, s =>
    if p.previous.any (·.contains p.packet) then prepend (p, .skip) (walk f ps s)
    else match f s p.packet with
      | .error e => ([(p, .rejected)], .error e)
      | .ok s' => prepend (p, .accepted (s'.passes - s.passes)) (walk f ps s')

private theorem walk_erase (f : LoopState → PacketId → Except Error LoopState) (ps : List Position)
    (s : LoopState) : (walk f ps s).2 = ps.foldlM (dispatch f) s := by
  induction ps generalizing s with
  | nil => rfl
  | cons p ps ih =>
    simp only [walk, List.foldlM_cons, dispatch]
    split
    · exact ih s
    · cases e : f s p.packet <;> simp [prepend, ih, bind, Except.bind]

/-- The charged positions are a prefix of the actual physical schedule. -/
theorem walk_prefix (f : LoopState → PacketId → Except Error LoopState) (ps : List Position)
    (s : LoopState) : ((walk f ps s).1.map Prod.fst) <+: ps := by
  induction ps generalizing s with
  | nil => exact List.prefix_refl _
  | cons p ps ih =>
    simp only [walk]
    split
    · exact List.cons_prefix_cons.2 ⟨rfl, ih s⟩
    · cases e : f s p.packet with
      | error => exact List.cons_prefix_cons.2 ⟨rfl, List.nil_prefix⟩
      | ok s' => exact List.cons_prefix_cons.2 ⟨rfl, ih s'⟩

/-- On completion all physical positions were visited. On rejection the last
logged position is the failing call, reached from the initial state by exactly
the preceding physical prefix. No suffix callback is run. -/
theorem walk_outcome (f : LoopState → PacketId → Except Error LoopState) (ps : List Position)
    (s : LoopState) :
    let r := walk f ps s
    match r.2 with
    | .ok _ => r.1.map Prod.fst = ps
    | .error e => ∃ before bad tail reached, r.1 = before ++ [(bad, .rejected)] ∧
        ps = before.map Prod.fst ++ bad :: tail ∧
        (before.map Prod.fst).foldlM (dispatch f) s = .ok reached ∧
        bad.previous.any (·.contains bad.packet) = false ∧ f reached bad.packet = .error e := by
  induction ps generalizing s with
  | nil => rfl
  | cons p ps ih =>
    by_cases skip : p.previous.any (·.contains p.packet) = true
    · simp only [walk, skip, ite_true, prepend]
      specialize ih s
      cases e : (walk f ps s).2 with
      | ok => simp only [e] at ih; exact congrArg (List.cons p) ih
      | error err =>
        simp only [e] at ih
        obtain ⟨pre, bad, tail, reached, log, ids, run, first, failed⟩ := ih
        exact ⟨(p, .skip) :: pre, bad, tail, reached, by simp [log],
          by simp [ids], by simpa [dispatch, skip] using run, first, failed⟩
    · have first := skip
      simp only [walk, skip]
      cases action : f s p.packet with
      | error err =>
        exact ⟨[], p, ps, s, rfl, rfl, rfl, by simpa using first, action⟩
      | ok s' =>
        simp only [prepend]
        specialize ih s'
        cases e : (walk f ps s').2 with
        | ok => simp only [e] at ih; exact congrArg (List.cons p) ih
        | error err =>
          simp only [e] at ih
          obtain ⟨pre, bad, tail, reached, log, ids, run, unused, failed⟩ := ih
          exact ⟨(p, .accepted (s'.passes - s.passes)) :: pre, bad, tail, reached,
            by simp [log], by simp [ids],
            by simpa [dispatch, first, action, bind, Except.bind] using run, unused, failed⟩

private theorem walk_read (f : LoopState → PacketId → Except Error LoopState) (ps : List Position)
    (s : LoopState) (p : Position) (n : Nat) (hit : (p, .accepted n) ∈ (walk f ps s).1) :
    ∃ pre tail a b, ps = pre ++ p :: tail ∧ pre.foldlM (dispatch f) s = .ok a ∧
      p.previous.any (·.contains p.packet) = false ∧ f a p.packet = .ok b ∧ b.passes - a.passes = n := by
  induction ps generalizing s with
  | nil => cases hit
  | cons q qs ih =>
    simp only [walk] at hit
    split at hit
    · rename_i skipped
      obtain ⟨pre, tail, a, b, ids, run, first, step, count⟩ :=
        ih s (by simpa [prepend] using hit)
      exact ⟨q :: pre, tail, a, b, by simp [ids], by simpa [dispatch, skipped] using run, first, step, count⟩
    · rename_i first
      cases e : f s q.packet with
      | error => simp [e] at hit
      | ok s' =>
        simp only [e, prepend, List.mem_cons] at hit
        rcases hit with eq | mem
        · cases eq
          exact ⟨[], qs, s, s', rfl, rfl, by simpa using first, e, rfl⟩
        · obtain ⟨pre, tail, a, b, ids, run, fresh, step, count⟩ := ih s' mem
          exact ⟨q :: pre, tail, a, b, by simp [ids],
            by simpa [dispatch, first, e, bind, Except.bind] using run, fresh, step, count⟩

private theorem prefix_charge {ps qs : List Position} (h : ps <+: qs) : charge ps ≤ charge qs := by
  obtain ⟨tail, rfl⟩ := h
  simp [charge]

private theorem length_charge (ps : List Position) : ps.length ≤ charge ps := by
  induction ps with
  | nil => simp [charge]
  | cons p ps ih => simp only [charge, List.map_cons, List.sum_cons, List.length_cons] at *; omega

private theorem walk_passes (L : Limits) (c base same pb) (ps : List Position) (s : LoopState)
    (start : pb + s.passes ≤ L.maxCodingPasses) :
    let r := walk (packetStep L c base same pb) ps s
    pb + s.passes + passSum r.1 ≤ L.maxCodingPasses ∧
      ∀ z, r.2 = .ok z → z.passes = s.passes + passSum r.1 ∧ z.seq = s.seq + attempts r.1 := by
  induction ps generalizing s with
  | nil => exact ⟨by simpa [walk, passSum] using start, fun z hz => by cases hz; simp [walk, passSum, attempts]⟩
  | cons p ps ih =>
    simp only [walk]
    split
    · simpa [prepend, passSum, attempts, PacketAction.passes, PacketAction.attempted] using ih s start
    · cases e : packetStep L c base same pb s p.packet with
      | error err => simp [passSum, PacketAction.passes, start]
      | ok s' =>
        obtain ⟨_, _, info, _, _, _, _, passes, seq, bound⟩ := packetStep_passes e
        obtain ⟨hb, he⟩ := ih s' bound
        simp only [prepend, passSum, List.map_cons, List.sum_cons, PacketAction.passes,
          attempts, List.countP_cons, PacketAction.attempted, ite_true] at *
        constructor
        · omega
        · intro z ok
          obtain ⟨a, b⟩ := he z ok
          exact ⟨by omega, by omega⟩

/-- Lift an unmeasured setup stage. Its error has an empty log. -/
def before {log α β : Type} (x : Except Error α) (k : α → Measured log β) : Measured log β :=
  match x with
  | .error e => ([], .error e)
  | .ok a => k a

/-- Postprocessing preserves the log, including on rejection. -/
def afterRun {log α β : Type} (x : Measured log α) (k : α → Except Error β) : Measured log β :=
  (x.1, x.2 >>= k)

private theorem before_erase {log α β : Type} (x : Except Error α) (k : α → Measured log β) :
    (before x k).2 = x >>= fun a => (k a).2 := by cases x <;> rfl

private def outputTile (tp : TileParams) (same : Bool) (buf : ByteArray) (parts : List (Nat × Nat × Nat))
    (spans : Array (Array (Nat × Nat))) (s : LoopState) : TileCodeBlocks :=
  let comps := spans.map fun si => si.map fun (start, n) =>
    (Array.range n).map fun k => (s.precs.getD (start + k) default).out parts k
  { tile := tp.index, comps, packets := s.seq, emptyPackets := s.empty,
    sopPackets := s.sops, headerBytes := s.hdrBytes, bodyBytes := s.bodyBytes,
    dataLength := buf.size, consumed := s.body.pos,
    headerStreamConsumed := if same then 0 else s.hdr.pos, passes := s.passes }

private def checkStream (tp : TileParams) (hs : Option HeaderStream) (t : TileCodeBlocks) :
    Except Error TileCodeBlocks := do
  if let some s := hs then
    if t.headerStreamConsumed != s.bytes.size then
      throw (.malformed (.atOffset .tier2 t.headerStreamConsumed)
        s!"tile {tp.index}: {s.bytes.size - t.headerStreamConsumed} bytes of packed packet headers left over")
  return t

/-- Actual initial packet-fold state on the chosen body buffer and optional packed header. -/
def firstState (precs : Array PrecState) (buf : ByteArray) (hs : Option HeaderStream) : LoopState :=
  let body := Reader.ofByteArray buf .tier2
  let hdr := match hs.map (·.bytes) with
    | some b => Reader.ofByteArray b .tier2
    | none => body
  { precs, hdr, body }

/-- Packet trace of a present tile, from layout and budget checks through the final
packed-header consumption check. -/
def measureStream (L : Limits) (h : Header) (data : ByteArray) (tp : TileParams)
    (hs : Option HeaderStream) (pb : Nat) : PacketLog × Except Error TileCodeBlocks :=
  before (Layout.ofHeader h tp.index) fun (g, coding) =>
  before (L.check JPEG2000.Tier2.Packet.loc .packets (iterationWork g coding.progression coding.poc)) fun _ =>
  before (initPrecincts L g) fun (precs, base, spans) =>
  before (tileData data tp.tile) fun (buf, parts) =>
    let same := (hs.map (·.bytes)).isNone
    afterRun (walk (packetStep L coding base same pb) (schedule g [] (volumes g coding.progression coding.poc))
      (firstState precs buf hs)) fun s => checkStream tp hs (outputTile tp same buf parts spans s)

/-- Erasing packet instrumentation returns the identical tile store or the identical error. -/
theorem measureStream_erase {L : Limits} {h : Header} {data : ByteArray}
    (parsed : Header.parse L data = .ok h) (tp : TileParams) (hs : Option HeaderStream) (pb : Nat) :
    (measureStream L h data tp hs pb).2 = JPEG2000.Tier2.Headers.decodeWithStream L h data tp hs pb := by
  unfold measureStream firstState JPEG2000.Tier2.Headers.decodeWithStream decodeTilePacketsWith
  simp only [before_erase, bind_assoc, pure_bind, afterRun, walk_erase]
  cases layout : Layout.ofHeader h tp.index with
  | error => rfl
  | ok gc =>
    obtain ⟨g, c⟩ := gc
    have wf := Tier2Equiv.ofHeader_wf (Equiv.parse_dxdy parsed) layout
    simp only [bind, Except.bind, forPackets_schedule g wf]
    rfl

/-- Packet bounds include prefixes ending inside a tile and a fully read tile
rejected for leftover packed-header bytes. The final equality counts new passes
and packet callbacks from the actual successful reads. -/
theorem measureStream_bounds {L : Limits} {h : Header} {data : ByteArray}
    (parsed : Header.parse L data = .ok h) (tp : TileParams) (hs : Option HeaderStream)
    (pb : Nat) (budget : pb ≤ L.maxCodingPasses) :
    let r := measureStream L h data tp hs pb
    attempts r.1 ≤ r.1.length ∧ r.1.length ≤ charge (r.1.map Prod.fst) ∧
      charge (r.1.map Prod.fst) ≤ L.maxPackets ∧ pb + passSum r.1 ≤ L.maxCodingPasses ∧
      ∀ t, r.2 = .ok t → t.passes = passSum r.1 ∧ t.packets = attempts r.1 := by
  dsimp only
  refine ⟨List.countP_le_length, ?_, ?_⟩
  · simpa using length_charge ((measureStream L h data tp hs pb).1.map Prod.fst)
  unfold measureStream
  cases layout : Layout.ofHeader h tp.index with
  | error => exact ⟨Nat.zero_le _, by simpa [passSum, before] using budget, by intro _ contra; cases contra⟩
  | ok gc =>
    obtain ⟨g, c⟩ := gc
    simp only [before]
    cases checked : L.check JPEG2000.Tier2.Packet.loc .packets (iterationWork g c.progression c.poc) with
    | error => exact ⟨Nat.zero_le _, by simpa [passSum] using budget, by intro _ contra; cases contra⟩
    | ok u =>
      have quota : iterationWork g c.progression c.poc ≤ L.maxPackets := (Limits.check_eq_ok_iff ..).1 checked
      cases init : initPrecincts L g with
      | error => exact ⟨Nat.zero_le _, by simpa [passSum] using budget, by intro _ contra; cases contra⟩
      | ok b =>
        obtain ⟨precs, base, spans⟩ := b
        cases input : tileData data tp.tile with
        | error => exact ⟨Nat.zero_le _, by simpa [passSum] using budget, by intro _ contra; cases contra⟩
        | ok bufparts =>
          obtain ⟨buf, parts⟩ := bufparts
          dsimp only [afterRun, firstState]
          have wf := Tier2Equiv.ofHeader_wf (Equiv.parse_dxdy parsed) layout
          refine ⟨Nat.le_trans (prefix_charge (walk_prefix ..)) (by rwa [schedule_charge g wf]), ?_⟩
          obtain ⟨bound, eqs⟩ := walk_passes L c base ((hs.map (·.bytes)).isNone) pb
            (schedule g [] (volumes g c.progression c.poc)) (s := { precs, hdr := _, body := _ }) budget
          refine ⟨bound, ?_⟩
          intro t ok
          obtain ⟨z, hz, ht⟩ := bind_ok.1 ok
          obtain ⟨hp, hn⟩ := eqs z hz
          unfold checkStream at ht
          repeat' split at ht
          all_goals cases ht <;> simp only [outputTile] <;> exact ⟨by simpa only [Nat.zero_add] using hp, by simpa only [Nat.zero_add] using hn⟩

/-- Each recorded pass contribution comes from a first-occurrence packet in the
actual layout, after the exact preceding callbacks on the real initial readers
and precincts. Together with `packetStep_passes` and `decodePacket_contributions`
this identifies its value with the pieces consumed by the packet-body reader. -/
theorem measureStream_read {L : Limits} {h : Header} {data : ByteArray} {tp : TileParams}
    {hs : Option HeaderStream} {pb : Nat} {p : Position} {n : Nat}
    (hit : (p, .accepted n) ∈ (measureStream L h data tp hs pb).1) :
    ∃ g c precs base spans buf parts pre tail a b,
      Layout.ofHeader h tp.index = .ok (g, c) ∧
      initPrecincts L g = .ok (precs, base, spans) ∧ tileData data tp.tile = .ok (buf, parts) ∧
      schedule g [] (volumes g c.progression c.poc) = pre ++ p :: tail ∧
      let f := packetStep L c base (hs.map (·.bytes)).isNone pb
      pre.foldlM (dispatch f) (firstState precs buf hs) = .ok a ∧
      p.previous.any (·.contains p.packet) = false ∧ f a p.packet = .ok b ∧ b.passes - a.passes = n := by
  unfold measureStream at hit
  cases layout : Layout.ofHeader h tp.index with
  | error => simp [layout, before] at hit
  | ok gc =>
    obtain ⟨g, c⟩ := gc
    simp only [layout, before] at hit
    cases quota : L.check JPEG2000.Tier2.Packet.loc .packets (iterationWork g c.progression c.poc) with
    | error => simp [quota] at hit
    | ok u =>
      simp only [quota] at hit
      cases init : initPrecincts L g with
      | error => simp [init] at hit
      | ok b =>
        obtain ⟨precs, base, spans⟩ := b
        simp only [init] at hit
        cases input : tileData data tp.tile with
        | error => simp [input] at hit
        | ok bufparts =>
          obtain ⟨buf, parts⟩ := bufparts
          simp only [input, afterRun] at hit
          obtain ⟨pre, tail, a, b, ids, run, fresh, step, count⟩ := walk_read _ _ _ p n hit
          exact ⟨g, c, precs, base, spans, buf, parts, pre, tail, a, b,
            rfl, init, rfl, ids, run, fresh, step, count⟩

end JPEG2000.Spec.Resources.PacketTraversal
