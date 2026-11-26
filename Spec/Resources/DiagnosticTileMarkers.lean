import Spec.Resources.DiagnosticMarker
import Spec.Resources.HeaderPayload

/-!
# Tile-part header diagnostic construction (Plan.md §§3–5, 7, S3)

T.800 A.4 and Table A.4, A.6, A.7.3–A.7.5. The marker loop starts after
SOT and ends at SOD or the first failure. Its cumulative POC count includes
earlier tile-parts and the main header. A short marker read constructs two
messages, first the byte reader's truncation and then the missing-SOD error.
-/

namespace JPEG2000.Spec.Resources.DiagnosticTileMarkers

open JPEG2000.Bytes JPEG2000.Marker JPEG2000.TilePart DiagnosticCost
open Tier2Equiv (bind_ok)

private theorem pos {cap : Nat} {r : Reader} (h : r.data.size ≤ cap) : r.pos ≤ cap :=
  Nat.le_trans r.pos_le_size h

private theorem remaining (r : Reader) : r.remaining ≤ r.data.size :=
  Nat.le_trans (Nat.sub_le ..) r.stop_le

private def markerHex {cap : Nat} (wire : 65535 ≤ cap) (m : UInt16) :
    ExprFor cap (hex m.toNat) 2 3 :=
  catExpr (litExpr _ "0x") (⟨_, rfl, .hex (by have := m.toNat_lt; omega)⟩ : ExprFor cap _ 0 1)

private def bad {α : Type} {cap : Nat} {s : String} (r : Reader) (hr : r.data.size ≤ cap)
    (b : Built cap s) : Trace cap (Except.error (malformedAt r s) : Except Error α) 1 :=
  ⟨[⟨s,b⟩], by simp, by intro e h; cases h; exact ⟨pos hr, ⟨s,b⟩, by simp, rfl⟩⟩

private def noSod {cap : Nat} (r : Reader) (hr : r.data.size ≤ cap) :
    Trace cap (Except.error (r.truncErr "tile-part header: no SOD") : Except Error (TPAcc × Reader)) 1 :=
  let b := oneFixed (cap := cap) "tile-part header: no SOD" (by decide)
  ⟨[⟨_,b⟩], by simp, by intro e h; cases h; exact ⟨pos hr, ⟨_,b⟩, by simp, rfl⟩⟩

private def propagated {α β : Type} {cap k : Nat} {x : Except Error α} {e : Error}
    (t : Trace cap x k) (h : x = .error e) : Trace cap (Except.error e : Except Error β) k :=
  ⟨t.messages, t.countBound, by intro _ he; cases he; exact t.origin _ h⟩

private def mapped {α β : Type} {cap k : Nat} {x : Except Error α}
    (t : Trace cap x k) (f : α → β) : Trace cap (x >>= fun v => pure (f v)) k :=
  widen (bindTrace (j := 0) t (fun _ _ => doneTrace _)) (by omega)

/-- PLT's continuation-byte loop constructs at most one message. Its overflow
diagnostic is fixed even when the attempted packet length exceeds 32 bits. -/
def varintsTrace {cap : Nat} (fuel cur : Nat) (pending : Bool) (a : Array Nat)
    (r : Reader) (hr : r.data.size ≤ cap) :
    Trace cap (readVarints fuel cur pending a r) 1 := by
  induction fuel generalizing cur pending a r with
  | zero =>
    rw [readVarints]
    split
    · exact bad r hr (oneFixed _ (by decide))
    · exact doneTrace _
  | succ n ih =>
    rw [readVarints]
    split
    · exact propagated (u8Trace r (pos hr)) (by assumption)
    · rename_i b t h
      have ht : t.data.size ≤ cap := (Reader.u8_pos h).2.2.1 ▸ hr
      dsimp only
      split
      · exact bad r hr (oneFixed _ (by decide))
      split <;> exact ih _ _ _ t ht

/-- PLT's index read precedes the packet-length loop. -/
def pltTrace {cap : Nat} (r : Reader) (hr : r.data.size ≤ cap) : Trace cap (parsePLT r) 2 := by
  unfold parsePLT
  apply bindTrace (u8Trace r (pos hr))
  rintro ⟨_,t⟩ h
  exact mapped (varintsTrace _ _ _ _ t ((Reader.u8_pos h).2.2.1 ▸ hr)) _

/-- PPT constructs its nonempty-body requirement after a successful index read. -/
def pptTrace {cap : Nat} (r : Reader) (hr : r.data.size ≤ cap) : Trace cap (parsePPT r) 2 := by
  unfold parsePPT
  apply bindTrace (u8Trace r (pos hr))
  rintro ⟨_,_⟩ _
  exact mapped (requireTrace r (pos hr) _ _ (oneFixed _ (by decide))) _

private theorem readCount {α : Type} {f : Reader → Except Error (α × Reader)} {n : Nat}
    {a z : Array α} {r t : Reader} (ok : readArray f a n r = .ok (z,t)) : z.size = a.size+n := by
  induction n generalizing a r with
  | zero => cases ok; rfl
  | succ n ih =>
    rw [readArray] at ok
    split at ok <;> try contradiction
    rw [ih ok, Array.size_push]
    omega

private theorem pocCount {L : Limits} {c : Nat} {r : Reader} {p : POC} (ok : parsePOC L c r = .ok p) :
    p.entries.size ≤ L.maxPocEntries := by
  unfold parsePOC at ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  obtain ⟨_,h,ok⟩ := bind_ok ok
  obtain ⟨⟨_,_⟩,a,ok⟩ := bind_ok ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  cases ok
  have sz := readCount a
  simp at sz
  exact sz ▸ (Limits.check_eq_ok_iff ..).1 h

/-- Per length-bearing tile marker, allowing the coding checks and every admitted POC entry. -/
def segmentBudget (L : Limits) := L.maxPocEntries*10 + 281

/-- Trace the production marker dispatch on its retained duplicate flags and
cumulative POC count. Its first-part check precedes every body and requirement. -/
def addTrace {cap : Nat} (wire : 65535 ≤ cap) (L : Limits) (total : 2*L.maxPocEntries ≤ cap)
    (c : Nat) (hc : c ≤ cap) (first ppm : Bool) (a : TPAcc) (ha : a.pocEntries ≤ L.maxPocEntries)
    (m : UInt16) (r : Reader) (hr : r.data.size ≤ cap) :
    Trace cap (addTileSegment L c first ppm a m r) (segmentBudget L) := by
  unfold addTileSegment segmentBudget
  by_cases hg : (firstPartOnly m && !first) = true
  · simp only [hg, ↓reduceIte]
    exact widen (bad r hr (closeExpr (catExpr (catExpr (litExpr _ "marker ") (markerHex wire m))
      (litExpr _ " in a tile-part other than the first")) (by decide) (by decide))) (by omega)
  simp only [hg, Bool.false_eq_true, ↓reduceIte]
  by_cases hm : m == Code.COD
  · rw [ite_eq_left hm]
    apply widen (bindTrace (j := 280) (requireTrace r (pos hr) _ _ (oneFixed _ (by decide))) ?_) (by omega)
    intro _ _
    exact mapped (DiagnosticMarker.codTrace wire L r hr) _
  rw [ite_eq_right hm]
  split
  · exact widen (mapped (DiagnosticMarker.cocTrace wire L c hc r hr) _) (by omega)
  split
  · apply widen (bindTrace (j := 200) (requireTrace r (pos hr) _ _ (oneFixed _ (by decide))) ?_) (by omega)
    intro _ _
    exact mapped (DiagnosticMarker.qcdTrace wire r hr) _
  split
  · exact widen (mapped (DiagnosticMarker.qccTrace wire c hc r hr) _) (by omega)
  split
  · exact widen (mapped (DiagnosticMarker.rgnTrace wire c hc r hr) _) (by omega)
  split
  · apply widen (bindTrace (j := 0) (DiagnosticMarker.pocTrace wire L c r hr) ?_) (by omega)
    intro p hp
    have width := pocCount hp
    exact mapped (checkedTrace L _ _ (a.pocEntries+p.entries.size) (pos hr) (by omega)) _
  split
  · apply widen (bindTrace (j := 2) (requireTrace r (pos hr) _ _ (oneFixed _ (by decide))) ?_) (by omega)
    intro _ _
    exact mapped (pptTrace r hr) _
  split
  · exact widen (mapped (pltTrace r hr) _) (by omega)
  split
  · exact widen (mapped (DiagnosticMarker.comTrace r hr) _) (by omega)
  exact doneTrace _

private theorem addCount {L : Limits} {c : Nat} {a z : TPAcc} {first ppm : Bool} {m : UInt16} {r : Reader}
    (ha : a.pocEntries ≤ L.maxPocEntries) (ok : addTileSegment L c first ppm a m r = .ok z) :
    z.pocEntries ≤ L.maxPocEntries := by
  unfold addTileSegment at ok
  repeat' first | (split at ok <;> try contradiction) | (obtain ⟨_,_,ok⟩ := bind_ok ok)
  all_goals cases ok
  all_goals first | exact ha | exact (Limits.check_eq_ok_iff ..).1 (by assumption)

/-- The diagnostic event allowance for a tile header with the given loop fuel. -/
def headerBudget (L : Limits) (fuel : Nat) := fuel*(segmentBudget L+4)+1

/-- Ordered constructions through SOD or rejection on the actual loop state.
A failed marker-word read contributes its own message before the replacement. -/
def headerTrace {cap : Nat} (wire : 65535 ≤ cap) (L : Limits) (total : 2*L.maxPocEntries ≤ cap)
    (c : Nat) (hc : c ≤ cap) (first ppm : Bool) (fuel : Nat) (a : TPAcc)
    (ha : a.pocEntries ≤ L.maxPocEntries) (r : Reader) (hr : r.data.size ≤ cap) :
    Trace cap (TilePart.headerLoop L c first ppm fuel a r) (headerBudget L fuel) := by
  unfold headerBudget
  induction fuel generalizing a r with
  | zero => simpa only [Nat.zero_mul, Nat.zero_add, TilePart.headerLoop] using noSod r hr
  | succ f ih =>
    rw [TilePart.headerLoop, Nat.succ_mul]
    let read := u16beTrace r (pos hr)
    split
    · exact widen (includeTrace read (noSod r hr)) (by omega)
    · rename_i m t h
      have ht : t.data.size ≤ cap := (Reader.u16be_pos h).2.2.1 ▸ hr
      split
      · exact doneTrace _
      split
      · exact widen (bad r hr (closeExpr (catExpr (litExpr _ "expected a marker, found ")
          (markerHex wire m)) (by decide) (by decide))) (by omega)
      split
      · exact widen (ih {a with markers := a.markers.push ⟨m,r.pos,2⟩} ha t ht) (by omega)
      split
      · exact widen (bad r hr (closeExpr
          (catExpr (catExpr (litExpr _ "marker ") (markerHex wire m))
            (litExpr _ " not allowed in a tile-part header")) (by decide) (by decide))) (by omega)
      let frame := segmentTrace t ht wire
      split
      · exact widen (propagated frame (by assumption)) (by omega)
      · rename_i body len next hs
        have ext := HeaderWork.readSegment_extent hs
        have hb : body.data.size ≤ cap := ext.1 ▸ ht
        have hn : next.data.size ≤ cap := ext.2.1 ▸ ht
        let indexed : TPAcc := {a with markers := a.markers.push ⟨m,r.pos,len+2⟩}
        let payload := addTrace wire L total c hc first ppm indexed ha m body hb
        dsimp only
        split
        · exact widen (includeTrace frame (propagated payload (by assumption))) (by omega)
        · rename_i z hz
          exact widen (includeTrace frame (includeTrace payload (ih z (addCount (a := indexed) ha hz) next hn)))
            (by omega)

private theorem varintsBounds {f cur : Nat} {pending : Bool} {a z : Array Nat} {r : Reader}
    (fits : ∀ v ∈ a, v < 2^32) (ok : readVarints f cur pending a r = .ok z) :
    z.size ≤ a.size+f ∧ ∀ v ∈ z, v < 2^32 := by
  induction f generalizing cur pending a r with
  | zero =>
    rw [readVarints] at ok
    split at ok <;> cases ok
    exact ⟨Nat.le_refl _,fits⟩
  | succ f ih =>
    rw [readVarints] at ok
    split at ok <;> try contradiction
    dsimp only at ok
    split at ok <;> try contradiction
    split at ok
    · obtain ⟨sz,fields⟩ := ih fits ok
      exact ⟨by omega,fields⟩
    · obtain ⟨sz,fields⟩ := ih (a := a.push _) (by
        intro v hv
        rcases Array.mem_push.mp hv with old | rfl
        · exact fits v old
        · omega) ok
      simp only [Array.size_push] at sz
      exact ⟨by omega,fields⟩

/-- Each PLT result fits the body in bytes and retains only unsigned 32-bit lengths. -/
theorem plt_bounds {r : Reader} {p : PLT} (ok : parsePLT r = .ok p) :
    p.lengths.size < r.remaining ∧ ∀ v ∈ p.lengths, v < 2^32 := by
  unfold parsePLT at ok
  obtain ⟨⟨_,t⟩,ht,ok⟩ := bind_ok ok
  obtain ⟨_,hv,ok⟩ := bind_ok ok
  cases ok
  obtain ⟨sz,fields⟩ := varintsBounds (by simp) hv
  have step := Reader.u8_pos ht
  have := t.pos_le
  simp only [Array.size_empty,Nat.zero_add,Reader.remaining] at sz ⊢
  exact ⟨by omega,fields⟩

/-- The nonempty PPT range begins after Zppt and ends exactly at the body stop. -/
theorem ppt_range {r : Reader} {p : PPT} (ok : parsePPT r = .ok p) :
    p.body.offset = r.pos+1 ∧ 0 < p.body.length ∧ p.body.stop = r.stop := by
  unfold parsePPT at ok
  obtain ⟨⟨_,t⟩,ht,ok⟩ := bind_ok ok
  obtain ⟨_,req,ok⟩ := bind_ok ok
  cases ok
  have step := Reader.u8_pos ht
  have := t.pos_le
  unfold require at req
  split at req <;> try contradiction
  simp_all [ByteRange.stop,Reader.remaining] <;> omega

/-- Bounds needed when later tile-part stages inspect the retained POC, PLT and PPT payloads. -/
def PayloadFits (L : Limits) (bytes : Nat) : TileSegment → Prop
  | .poc p => p.entries.size ≤ L.maxPocEntries
  | .plt p => p.lengths.size ≤ bytes ∧ ∀ v ∈ p.lengths, v < 2^32
  | .ppt p => 0 < p.body.length ∧ p.body.stop ≤ bytes
  | _ => True

private theorem addFits {L : Limits} {c : Nat} {a z : TPAcc} {first ppm : Bool} {m : UInt16} {r : Reader}
    (ha : ∀ s ∈ a.segments, PayloadFits L r.data.size s)
    (ok : addTileSegment L c first ppm a m r = .ok z) :
    ∀ s ∈ z.segments, PayloadFits L r.data.size s := by
  unfold addTileSegment at ok
  repeat' first | (split at ok <;> try contradiction) | (obtain ⟨_,_,ok⟩ := bind_ok ok)
  all_goals cases ok; intro s hs; rcases Array.mem_push.mp hs with old | rfl
  all_goals try first | exact ha _ old | trivial | exact pocCount (by assumption)
  · obtain ⟨_,positive,stop⟩ := ppt_range (by assumption : parsePPT r = .ok _)
    exact ⟨positive,stop ▸ r.stop_le⟩
  · obtain ⟨sz,values⟩ := plt_bounds (by assumption : parsePLT r = .ok _)
    exact ⟨Nat.le_trans (Nat.le_of_lt sz) (remaining r),values⟩

/-- On SOD the reader and both retained arrays share the initial byte budget.
The final POC counter is admitted and every preserved pointer payload fits. -/
theorem header_continuation {L : Limits} {c f : Nat} {a z : TPAcc} {first ppm : Bool} {r t : Reader}
    (hc : a.pocEntries ≤ L.maxPocEntries) (ha : ∀ s ∈ a.segments, PayloadFits L r.data.size s)
    (ok : TilePart.headerLoop L c first ppm f a r = .ok (z,t)) :
    z.pocEntries ≤ L.maxPocEntries ∧ (∀ s ∈ z.segments, PayloadFits L r.data.size s) ∧
    z.markers.size + z.segments.size + t.remaining ≤ a.markers.size + a.segments.size + r.remaining ∧
    t.data = r.data ∧ t.stop = r.stop := by
  suffices h : z.pocEntries ≤ L.maxPocEntries ∧ ∀ s ∈ z.segments, PayloadFits L r.data.size s from
    ⟨h.1,h.2,HeaderWork.tileHeaderLoop_storage ok⟩
  induction f generalizing a r with
    | zero => cases ok
    | succ f ih =>
      rw [TilePart.headerLoop] at ok
      split at ok <;> try contradiction
      rename_i m t1 h1
      have d1 := (Reader.u16be_pos h1).2.2.1
      split at ok
      · cases ok; exact ⟨hc,ha⟩
      split at ok <;> try contradiction
      split at ok
      · let indexed : TPAcc := {a with markers := a.markers.push ⟨m,r.pos,2⟩}
        simpa only [d1] using ih (a := indexed) hc (by simpa only [d1] using ha) ok
      split at ok <;> try contradiction
      split at ok <;> try contradiction
      rename_i body len next hs
      have ext := HeaderWork.readSegment_extent hs
      have db := ext.1.trans d1
      have dn := ext.2.1.trans d1
      dsimp only at ok
      split at ok <;> try contradiction
      rename_i acc hz
      have count := addCount (a := {a with markers := a.markers.push ⟨m,r.pos,len+2⟩}) hc hz
      have fits := addFits (a := {a with markers := a.markers.push ⟨m,r.pos,len+2⟩})
        (by simpa only [db] using ha) hz
      simpa only [dn] using ih count (by simpa only [dn,db] using fits) ok

/-- The SOT fields and two readers at the header call inside a tile-part read. -/
structure HeaderCall where
  /-- Parsed SOT. -/
  sot : SOT
  /-- Length returned by the SOT segment framing. -/
  len : Nat
  /-- Subreader bounded by the tile-part extent. -/
  tile : Reader
  /-- Reader following that extent. -/
  next : Reader

/-- The production accumulator carries the incoming global count and the SOT index entry. -/
def HeaderCall.initial (v : HeaderCall) (st : State) (r : Reader) : TPAcc :=
  { markers := #[⟨Code.SOT,r.pos,v.len+2⟩], pocEntries := st.pocEntries }

/-- Run the header stage with the exact fuel, flags and accumulator of its caller. -/
def HeaderCall.run (v : HeaderCall) (c : Ctx) (st : State) (r : Reader) :=
  TilePart.headerLoop c.limits c.csiz (v.sot.tpsot = 0) c.ppm v.tile.remaining (v.initial st r) v.tile

/-- Observation of the header stage within a production tile-part read. On success
the next state keeps the header's final POC count and resumes on the outer reader. -/
inductive ReadHeader (c : Ctx) (st : State) (r : Reader) : Except Error (State × Reader) → Type where
  /-- An earlier bind rejected before construction of the header subreader. -/
  | earlier (e : Error) : ReadHeader c st r (.error e)
  /-- The header receives the original buffer. Its failure is the caller's failure. -/
  | reached (v : HeaderCall) (source : v.tile.data = r.data) {out : Except Error (State × Reader)}
      (resume : match v.run c st r with
        | .error e => out = .error e
        | .ok (z,_) => ∃ st', out = .ok (st',v.next) ∧ st'.pocEntries = z.pocEntries) :
      ReadHeader c st r out

private def beforeHeader {α : Type} {c : Ctx} {st : State} {r : Reader} {x : Except Error α}
    {f : α → Except Error (State × Reader)}
    (rest : ∀ v, x = .ok v → ReadHeader c st r (f v)) : ReadHeader c st r (x >>= f) := by
  cases x with
  | error e => exact .earlier e
  | ok v => exact rest v rfl

/-- Locate the call by following the binds of `readTilePart`, including failed
prefixes. No assumption about the tile-part result is needed. -/
def readHeader (c : Ctx) (st : State) (r : Reader) : ReadHeader c st r (readTilePart c st r) := by
  unfold readTilePart
  apply beforeHeader; rintro ⟨_,r1⟩ h1
  apply beforeHeader; rintro ⟨_,len,r2⟩ hs
  apply beforeHeader; intro sot _
  iterate 6 (apply beforeHeader; intro _ _)
  dsimp only
  split <;> split
  all_goals try exact .earlier _
  all_goals
    simp only [pure_bind]
    apply beforeHeader
    rintro ⟨tp,next⟩ ht
    let v : HeaderCall := ⟨sot,len,tp,next⟩
    apply ReadHeader.reached v ((Reader.take_spec ht).2.2.1.trans
      ((HeaderWork.readSegment_extent hs).2.1.trans (Reader.u16be_pos h1).2.2.1))
    change match v.run c st r with
      | .error e => (v.run c st r >>= _) = .error e
      | .ok (z,_) => ∃ (st' : State), (v.run c st r >>= _) = .ok (st',v.next) ∧ st'.pocEntries = z.pocEntries
    split <;> rename_i h <;> rw [h]
    · rfl
    · exact ⟨_,rfl,rfl⟩

/-- A successful tile-part passes its admitted POC counter to the next tile-part. -/
theorem read_count {c : Ctx} {st z : State} {r t : Reader} (hc : st.pocEntries ≤ c.limits.maxPocEntries)
    (ok : readTilePart c st r = .ok (z,t)) : z.pocEntries ≤ c.limits.maxPocEntries := by
  have observed := readHeader c st r
  rw [ok] at observed
  cases observed with
  | reached v _ resume =>
    split at resume
    · cases resume
    · rename_i a rd h
      obtain ⟨_,eq,count⟩ := resume
      cases eq
      exact count ▸ (header_continuation (a := v.initial st r) hc (by simp [HeaderCall.initial]) h).1

private def mainCounter (L : Limits) (a : Acc) : Prop :=
  a.poc.foldl (fun n p => n+p.entries.size) 0 = a.pocEntries ∧ a.pocEntries ≤ L.maxPocEntries

private theorem mainStep {L : Limits} {a z : Acc} {c m b} (ha : mainCounter L a)
    (ok : addSegment L c a m b = .ok z) : mainCounter L z := by
  unfold addSegment at ok
  by_cases hm : m == Code.COD
  · rw [ite_eq_left hm] at ok
    iterate 2 obtain ⟨_,_,ok⟩ := bind_ok ok
    cases ok; exact ha
  rw [ite_eq_right hm] at ok
  repeat' first | (split at ok <;> try contradiction) | (obtain ⟨_,_,ok⟩ := bind_ok ok)
  all_goals cases ok
  all_goals first | exact ha | exact ⟨by simp [ha.1],(Limits.check_eq_ok_iff ..).1 (by assumption)⟩

private theorem mainLoop {L : Limits} {a z : Acc} {c f r t} (ha : mainCounter L a)
    (ok : segmentLoop L c f a r = .ok (z,t)) : mainCounter L z := by
  induction f generalizing a r with
  | zero => cases ok
  | succ f ih =>
    simp only [segmentLoop] at ok
    repeat' split at ok <;> try contradiction
    all_goals first | (cases ok; exact ha) | (apply ih _ ok; first | exact ha | (apply mainStep _ (by assumption); exact ha))

/-- The retained main-header POC array supplies the initial count in parseTileParts. -/
theorem main_count {L : Limits} {mh : MainHeader} {r t : Reader} (ok : parseMainHeader L r = .ok (mh,t)) :
    mh.poc.foldl (fun n p => n+p.entries.size) 0 ≤ L.maxPocEntries := by
  unfold parseMainHeader at ok
  iterate 6 obtain ⟨_,_,ok⟩ := bind_ok ok
  obtain ⟨⟨a,_⟩,loop,ok⟩ := bind_ok ok
  cases hc : a.cod <;> simp only [hc] at ok <;> try contradiction
  cases hq : a.qcd <;> simp only [hq] at ok <;> try contradiction
  cases ok
  obtain ⟨eq,limit⟩ := mainLoop (by exact ⟨rfl,Nat.zero_le _⟩) loop
  exact eq ▸ limit

/-- A reader/state pair after a successful prefix of the public tile-part loop.
The initial case includes the real container, main-header and pointer checks. -/
inductive PublicPrefix (L : Limits) (d : ByteArray) (red : Nat) (c : Ctx) : State → Reader → Prop where
  /-- First reader and retained state of the public tile-part parser. -/
  | start {st r} (ok : tileStart L d red = .ok (c,st,r)) : PublicPrefix L d red c st r
  /-- Continue from a successful SOT callback with its actual output state and reader. -/
  | next {st r z t mr} (prev : PublicPrefix L d red c st r) (sot : r.u16be = .ok (Code.SOT,mr))
      (ok : readTilePart c st r = .ok (z,t)) : PublicPrefix L d red c z t

/-- Public tile-part readers preserve the backing bytes, parsed component count
and admitted POC count, including the state at the first failing tile-part. -/
theorem prefix_fields {L : Limits} {d : ByteArray} {red : Nat} {c : Ctx} {st : State} {r : Reader}
    (h : PublicPrefix L d red c st r) :
    r.data = d ∧ c.limits = L ∧ c.csiz ≤ 16384 ∧ c.csiz ≤ L.maxComponents ∧ st.pocEntries ≤ L.maxPocEntries := by
  induction h with
  | start ok =>
    unfold tileStart at ok
    obtain ⟨_,reader,ok⟩ := bind_ok ok
    obtain ⟨⟨_,_⟩,main,ok⟩ := bind_ok ok
    iterate 4 obtain ⟨_,_,ok⟩ := bind_ok ok
    cases ok
    unfold mainReader at reader
    iterate 2 obtain ⟨_,_,reader⟩ := bind_ok reader
    obtain ⟨tail,_,_,_,_,_,_,_,_,_,wire,limit⟩ := DiagnosticMarker.main_source main
    exact ⟨tail.trans (DiagnosticMarker.range_source reader).1,rfl,wire,limit,main_count main⟩
  | next _ _ ok ih =>
    exact ⟨(HeaderWork.readTilePart_step ok).2.2.2.1.trans ih.1,ih.2.1,ih.2.2.1,ih.2.2.2.1,
      ih.2.1 ▸ read_count (ih.2.1 ▸ ih.2.2.2.2) ok⟩

/-- The call selected by the production binds, absent on rejection before the header. -/
def ReadHeader.call? {c st r out} : ReadHeader c st r out → Option HeaderCall
  | .earlier _ => none
  | .reached v _ _ => some v

private theorem reachedCall {c st r out} {v : HeaderCall} (obs : ReadHeader c st r out)
    (hit : obs.call? = some v) :
    v.tile.data = r.data ∧ match v.run c st r with
      | .error e => out = .error e
      | .ok (z,_) => ∃ st', out = .ok (st',v.next) ∧ st'.pocEntries = z.pocEntries := by
  cases obs with
  | earlier => cases hit
  | reached v' source resume => cases hit; exact ⟨source,resume⟩

/-- Tile-header diagnostics at a reached public reader, bounded only by the
byte input and limits. The allowance includes construction of discarded errors. -/
def publicTrace {L : Limits} {d : ByteArray} {red : Nat} {c : Ctx} {st : State} {r : Reader}
    (prev : PublicPrefix L d red c st r) {v : HeaderCall} (hit : (readHeader c st r).call? = some v) :
    Trace (DiagnosticMarker.scalarCap L d.size) (v.run c st r) (headerBudget L d.size) := by
  obtain ⟨src,lim,components,_,count⟩ := prefix_fields prev
  have data := (reachedCall _ hit).1.trans src
  have cap : d.size ≤ DiagnosticMarker.scalarCap L d.size := by unfold DiagnosticMarker.scalarCap; omega
  apply widen (headerTrace (cap := DiagnosticMarker.scalarCap L d.size) (by unfold DiagnosticMarker.scalarCap; omega)
    c.limits (by rw [lim]; unfold DiagnosticMarker.scalarCap; omega) c.csiz
    (by unfold DiagnosticMarker.scalarCap; omega) _ _ _ (v.initial st r) (by exact lim ▸ count)
    v.tile (data ▸ cap))
  have fuel := remaining v.tile
  rw [data] at fuel
  unfold headerBudget
  rw [lim]
  exact Nat.add_le_add_right (Nat.mul_le_mul_right _ fuel) _

/-- Diagnostic and descriptor costs for the same reached header. Its first failure
propagates to readTilePart, and success passes the final global count to its next state. -/
theorem public_header {L : Limits} {d : ByteArray} {red : Nat} {c : Ctx} {st : State} {r : Reader}
    (prev : PublicPrefix L d red c st r) {v : HeaderCall} (hit : (readHeader c st r).call? = some v) :
    let tr := publicTrace prev hit
    let p := HeaderPayload.tileHeaderPayload c.limits c.csiz (v.sot.tpsot = 0) c.ppm
      v.tile.remaining (v.initial st r) v.tile
    tr.messages.length ≤ headerBudget L d.size ∧
    (tr.messages.map (fun m => m.2.tree.work)).sum ≤
      headerBudget L d.size * Text.workBound (DiagnosticMarker.scalarCap L d.size) 128 24 ∧
    p.run.1 = v.run c st r ∧ p.run.2 ≤ d.size*(3+HeaderPayload.markerBudget L L.maxComponents d.size) ∧
    (match v.run c st r with
     | .error e => readTilePart c st r = .error e
     | .ok (z,_) => ∃ st', readTilePart c st r = .ok (st',v.next) ∧ st'.pocEntries = z.pocEntries) := by
  obtain ⟨src,lim,_,components,_⟩ := prefix_fields prev
  obtain ⟨src',resume⟩ := reachedCall _ hit
  let p := HeaderPayload.tileHeaderPayload c.limits c.csiz (v.sot.tpsot = 0) c.ppm
    v.tile.remaining (v.initial st r) v.tile
  refine ⟨(publicTrace prev hit).countBound,(trace_cost (publicTrace prev hit)).1,p.erase,
    Nat.le_trans p.bound ?_,resume⟩
  have fuel := remaining v.tile
  rw [src',src] at fuel ⊢
  rw [lim]
  apply Nat.mul_le_mul fuel
  unfold HeaderPayload.markerBudget
  omega

end JPEG2000.Spec.Resources.DiagnosticTileMarkers
