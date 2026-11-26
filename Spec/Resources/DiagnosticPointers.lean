import Spec.Resources.DiagnosticMarker
import Spec.Resources.HeaderPayload

/-!
# Main-header pointer diagnostics (Plan.md §§3–5, 7, S3; T.800 A.7.1, A.7.3–5)

The segment loop charges the requirements evaluated on admitted TLM and PPM bodies.
After the two index sorts, each Nppm read uses the bytes gathered by the production
split, including length fields crossing segment boundaries. The aggregate TLM guard
can retain a count larger than the limit that admitted either individual table.
-/

namespace JPEG2000.Spec.Resources.DiagnosticPointers

open Bytes Marker TilePart Tier2Equiv DiagnosticCost

private def bad {α : Type} {cap : Nat} {s : String} (loc : Location)
    (hl : loc.offset.getD 0 ≤ cap) (b : Built cap s) :
    Trace cap (Except.error (.malformed loc s) : Except Error α) 1 :=
  ⟨[⟨s,b⟩], by simp, by intro e he; cases he; exact ⟨hl, ⟨s,b⟩, by simp, rfl⟩⟩

private def duplicateTrace {α : Type} {cap : Nat} (wire : 255 ≤ cap)
    (loc : Location) (hl : loc.offset.getD 0 ≤ cap) (name : String)
    (hn : name.utf8ByteSize ≤ 4) (sorted : Array α) (dup : Option UInt8) :
    Trace cap (match dup with
      | some z => throw (.malformed loc s!"duplicate {name} = {z}")
      | none => pure sorted) 1 := by
  cases dup with
  | none => exact doneTrace _
  | some z =>
    have hz := z.toNat_lt
    apply bad loc hl
    apply closeExpr (catExpr (catExpr (catExpr (litExpr _ "duplicate ") (litExpr _ name))
      (litExpr _ " = ")) (decExpr (n := z.toNat) (by omega)))
    · change 10 + name.utf8ByteSize + 3 + 0 ≤ 128; omega
    · decide

/-- A duplicate segment index formats the supplied literal name and the first duplicate
byte in sorted order. All four callers (Ztlm, Zppm, Zplt and Zppt) have four-byte names. -/
def sortTrace {α : Type} {cap : Nat} (wire : 255 ≤ cap) (key : α → UInt8)
    (loc : Location) (hl : loc.offset.getD 0 ≤ cap) (name : String)
    (hn : name.utf8ByteSize ≤ 4) (xs : Array α) : Trace cap (sortUnique key loc name xs) 1 :=
  let sorted := xs.insertionSort (fun a b => key a < key b)
  duplicateTrace wire loc hl name hn sorted (firstDup (sorted.toList.map key))

/-- Exact construction tree produced by each duplicate index site. A successful sort has
no diagnostic events, including when it precedes a later failing sort. -/
theorem sort_events {α : Type} {cap : Nat} (wire : 255 ≤ cap) (key : α → UInt8)
    (loc : Location) (hl : loc.offset.getD 0 ≤ cap) (name : String) (hn : name.utf8ByteSize ≤ 4)
    (xs : Array α) :
    ((sortTrace wire key loc hl name hn xs).messages.map fun m => m.2.tree) =
      match firstDup ((xs.insertionSort (fun a b => key a < key b)).toList.map key) with
      | none => []
      | some z => [.cat (.cat (.cat (.fixed "duplicate ") (.fixed name)) (.fixed " = ")) (.dec z.toNat)] := by
  have events (sorted : Array α) (dup : Option UInt8) :
      ((duplicateTrace wire loc hl name hn sorted dup).messages.map fun m => m.2.tree) =
        match dup with
        | none => []
        | some z => [.cat (.cat (.cat (.fixed "duplicate ") (.fixed name)) (.fixed " = ")) (.dec z.toNat)] := by
    cases dup <;> rfl
  exact events _ _

private def readReturn {α β : Type} {cap : Nat} {x : Except Error α}
    (f : α → β) (t : Trace cap x 1) : Trace cap (x >>= fun a => pure (f a)) 1 :=
  bindTrace (j := 0) t fun _ _ => doneTrace _

private theorem pos {cap : Nat} {r : Reader} (h : r.data.size ≤ cap) : r.pos ≤ cap :=
  Nat.le_trans r.pos_le_size h

private def tileField (st : UInt8) (r : Reader) : Except Error (Option UInt16 × Reader) :=
  match st with
  | 0 => pure (none,r)
  | 1 => do let (b,t) ← r.u8; pure (some b.toUInt16,t)
  | _ => do let (v,t) ← r.u16be; pure (some v,t)

private def tileFieldTrace {cap : Nat} (st : UInt8) (r : Reader) (hr : r.data.size ≤ cap) :
    Trace cap (tileField st r) 1 := by
  unfold tileField
  split
  · exact doneTrace _
  · exact readReturn _ (u8Trace r (pos hr))
  · exact readReturn _ (u16beTrace r (pos hr))

private theorem tileField_data {st : UInt8} {r t : Reader} {a : Option UInt16}
    (h : tileField st r = .ok (a,t)) : t.data = r.data := by
  unfold tileField at h
  split at h
  · cases h; rfl
  all_goals obtain ⟨⟨_,_⟩,read,h⟩ := bind_ok h; cases h
  · exact (Reader.u8_pos read).2.2.1
  · exact (Reader.u16be_pos read).2.2.1

private theorem entry_eq (st : UInt8) (sp : Bool) (r : Reader) :
    readTlmEntry st sp r = (do
      let (tile,t) ← tileField st r
      if sp then
        let (v,u) ← t.u32be
        return ({ tile, length := v },u)
      else
        let (v,u) ← t.u16be
        return ({ tile, length := v.toUInt32 },u)) := by
  unfold readTlmEntry tileField
  dsimp only
  split <;> simp only [bind_assoc, pure_bind] <;> rfl

private def entryTrace {cap : Nat} (st : UInt8) (sp : Bool) (r : Reader) (hr : r.data.size ≤ cap) :
    Trace cap (readTlmEntry st sp r) 2 := by
  rw [entry_eq]
  apply bindTrace (tileFieldTrace st r hr)
  rintro ⟨_,t⟩ read
  have ht := tileField_data read ▸ hr
  dsimp only
  split
  · exact readReturn _ (u32beTrace t (pos ht))
  · exact readReturn _ (u16beTrace t (pos ht))

private theorem entry_data (st : UInt8) (sp : Bool) (r t : Reader) (a : TlmEntry)
    (ok : readTlmEntry st sp r = .ok (a,t)) : t.data = r.data := by
  rw [entry_eq] at ok
  obtain ⟨⟨tile,mid⟩,read,ok⟩ := bind_ok ok
  have hm := tileField_data (st := st) (r := r) (a := tile) (t := mid) read
  dsimp only at ok
  split at ok <;> obtain ⟨⟨_,_⟩,read,ok⟩ := bind_ok ok <;> cases ok
  · exact (Reader.u32be_pos read).2.2.1.trans hm
  · exact (Reader.u16be_pos read).2.2.1.trans hm

private theorem entries_result {st : UInt8} {sp : Bool} {a z : Array TlmEntry} {n : Nat} {r t : Reader}
    (ok : readArray (readTlmEntry st sp) a n r = .ok (z,t)) :
    t.data = r.data ∧ z.size = a.size+n := by
  induction n generalizing a r with
  | zero => cases ok; exact ⟨rfl,rfl⟩
  | succ n ih =>
    rw [readArray] at ok
    split at ok <;> try contradiction
    rename_i x mid read
    obtain ⟨hd,hs⟩ := ih ok
    rw [Array.size_push] at hs
    exact ⟨hd.trans (entry_data _ _ _ _ _ read), by omega⟩

private def tlmTrace {cap : Nat} (wire : 2^32 ≤ cap) (L : Limits) (r : Reader)
    (hr : r.data.size ≤ cap) : Trace cap (parseTLM L r) (L.maxTileParts*2+6) := by
  unfold parseTLM
  apply bindTrace (u8Trace r (pos hr))
  rintro ⟨_,r1⟩ read
  have h1 : r1.data.size ≤ cap := (Reader.u8_pos read).2.2.1 ▸ hr
  apply bindTrace (u8Trace r1 (pos h1))
  rintro ⟨s,t⟩ read
  have ht : t.data.size ≤ cap := (Reader.u8_pos read).2.2.1 ▸ h1
  have hv := s.toNat_lt
  let hx : ExprFor cap (hex s.toNat) 2 3 :=
    catExpr (litExpr _ "0x") (⟨_, rfl, .hex (by omega)⟩ : ExprFor cap _ 0 1)
  apply bindTrace (requireTrace r1 (pos h1) _ _ (closeExpr
    (catExpr (catExpr (litExpr _ "Stlm ") hx) (litExpr _ ": reserved bits set")) (by decide) (by decide)))
  intro _ _
  apply bindTrace (requireTrace r1 (pos h1) _ _ (oneFixed _ (by decide)))
  intro _ _
  let st := (s >>> 4) &&& 3
  let esz := st.toNat + (if s &&& 0x40 != 0 then 4 else 2)
  have sz : esz ≤ cap := by have := st.toNat_lt; dsimp only [esz]; split <;> omega
  have rem : t.remaining ≤ cap := Nat.le_trans (Nat.sub_le ..) (Nat.le_trans t.stop_le ht)
  apply bindTrace (requireTrace t (pos ht) _ _ (closeExpr
    (catExpr (catExpr (catExpr (catExpr (litExpr _ "TLM body of ") (decExpr rem))
      (litExpr _ " bytes (entries of ")) (decExpr sz)) (litExpr _ ")")) (by decide) (by decide)))
  intro _ _
  apply bindTrace (checkedTrace L _ _ _ (pos ht) (Nat.le_trans (Nat.div_le_self _ esz) rem))
  intro _ hc
  have count : t.remaining / esz ≤ L.maxTileParts := (Limits.check_eq_ok_iff ..).1 hc
  apply widen (bindTrace (arrayTrace (entryTrace st _) (entry_data st _) _ (t.remaining / esz) t ht) (j := 1) ?_) (by omega)
  rintro ⟨_,last⟩ arr
  apply bindTrace (endTrace last ((entries_result arr).1 ▸ ht) "TLM" (by decide))
  intro _ _
  exact doneTrace _

private theorem tlm_count {L : Limits} {r : Reader} {t : TLM} (ok : parseTLM L r = .ok t) :
    t.entries.size ≤ L.maxTileParts := by
  unfold parseTLM at ok
  iterate 2 obtain ⟨⟨_,_⟩,_,ok⟩ := bind_ok ok
  iterate 3 obtain ⟨_,_,ok⟩ := bind_ok ok
  obtain ⟨_,checked,ok⟩ := bind_ok ok
  obtain ⟨⟨_,_⟩,arr,ok⟩ := bind_ok ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  cases ok
  have sz := (entries_result arr).2
  change _ = 0 + _ at sz
  rw [Nat.zero_add] at sz
  exact sz ▸ (Limits.check_eq_ok_iff ..).1 checked

private def ppmTrace {cap : Nat} (r : Reader) (hr : r.data.size ≤ cap) : Trace cap (parsePPM r) 2 := by
  unfold parsePPM
  apply bindTrace (u8Trace r (pos hr))
  rintro ⟨_,_⟩ _
  apply bindTrace (requireTrace r (pos hr) _ _ (oneFixed _ (by decide)))
  intro _ _
  exact doneTrace _

private def chunksTrace {cap : Nat} (wire : 2^32 ≤ cap) (L : Limits) (lim : L.maxTileParts+1 ≤ cap)
    (d : ByteArray) (loc : Location) (hl : loc.offset.getD 0 ≤ cap) (fuel : Nat)
    (xs : List ByteRange) (a : Array (Array ByteRange)) (ha : a.size ≤ L.maxTileParts) :
    Trace cap (ppmChunks L d loc fuel xs a) ((L.maxTileParts-a.size+1)*2) := by
  induction fuel generalizing xs a with
  | zero =>
    cases xs
    · exact doneTrace _
    · exact widen (bad loc hl (oneFixed _ (by decide))) (by omega)
  | succ f ih =>
    cases xs with
    | nil => exact doneTrace _
    | cons r rs =>
      rw [ppmChunks]
      apply bindTrace (j := (L.maxTileParts-a.size+1)*2) (checkedTrace L _ _ _ hl (by omega))
      intro _ ok
      have room : a.size+1 ≤ L.maxTileParts := (Limits.check_eq_ok_iff ..).1 ok
      split
      · rename_i nb tail first
        let src := Reader.ofByteArray (gatherBytes d nb)
        have four : src.data.size ≤ 4 := HeaderWork.ppmLength_copy first
        have hs : src.pos ≤ cap := pos (r := src) (Nat.le_trans four (by omega))
        apply widen (bindTrace (u32beTrace src hs) (j := (L.maxTileParts-a.size)*2) ?_) (by rw [Nat.add_one_mul]; omega)
        rintro ⟨n,_⟩ _
        dsimp only
        split
        · rename_i part rest _
          exact widen (ih rest (a.push part) (by simp; omega)) (by simp; omega)
        · have hn := n.toNat_lt
          apply widen (bad loc hl (closeExpr
            (catExpr (catExpr (litExpr _ "PPM: Ippm of ") (decExpr (n := n.toNat) (by omega)))
              (litExpr _ " bytes exceeds the PPM data")) (by decide) (by decide))) (by omega)
      · exact widen (bad loc hl (oneFixed _ (by decide))) (by omega)

private abbrev Fits (n : Nat) (xs : Array RawSegment) :=
  ∀ s ∈ xs, s.offset+s.length ≤ n

private theorem add_fits {L : Limits} {c n : Nat} {r : Reader} {a z : Acc} {m : UInt16}
    (hr : r.data.size ≤ n) (old : Fits n a.pointers) (ok : addSegment L c a m r = .ok z) :
    Fits n z.pointers := by
  unfold addSegment at ok
  by_cases h : m == Code.COD
  · rw [ite_eq_left h] at ok
    iterate 2 obtain ⟨_,_,ok⟩ := bind_ok ok
    cases ok; exact old
  rw [ite_eq_right h] at ok
  repeat' first | (split at ok <;> try contradiction) | obtain ⟨_,_,ok⟩ := bind_ok ok
  all_goals cases ok; try exact old
  intro s hs
  rcases Array.mem_push.mp hs with mem | rfl
  · exact old _ mem
  · change r.pos+(r.stop-r.pos) ≤ n
    have := r.pos_le
    have := r.stop_le
    omega

private theorem loop_fits {L : Limits} {c n : Nat} (fuel : Nat) {r t : Reader} {a z : Acc}
    (hr : r.data.size ≤ n) (old : Fits n a.pointers)
    (ok : segmentLoop L c fuel a r = .ok (z,t)) : Fits n z.pointers := by
  induction fuel generalizing r a with
  | zero => cases ok
  | succ f ih =>
    simp only [segmentLoop] at ok
    split at ok <;> try contradiction
    rename_i m r1 read
    have h1 : r1.data.size ≤ n := (Reader.u16be_pos read).2.2.1 ▸ hr
    split at ok
    · cases ok; exact old
    split at ok <;> try contradiction
    split at ok
    · apply ih h1 _ ok; exact old
    split at ok <;> try contradiction
    split at ok <;> try contradiction
    rename_i body len next seg
    split at ok <;> try contradiction
    rename_i z' step
    obtain ⟨db,dn,_⟩ := HeaderWork.readSegment_extent seg
    exact ih (dn ▸ h1) (add_fits (db ▸ h1) (by exact old) step) ok

/-- On the parser's success branch every raw pointer body lies in the backing input,
the number of pointer descriptors fits the input size, and the sort location fits too. -/
theorem main_ranges {L : Limits} {r t : Reader} {mh : MainHeader}
    (ok : parseMainHeader L r = .ok (mh,t)) :
    (∀ s ∈ mh.pointers, s.offset+s.length ≤ r.data.size) ∧
      mh.pointers.size ≤ r.data.size ∧ mh.endPos ≤ r.data.size := by
  have tail := (DiagnosticMarker.main_source ok).1
  have loc := DiagnosticMarkerOrigin.main_location L r
  rw [ok] at loc
  have ep : mh.endPos ≤ r.data.size := loc.2.2.2 ▸ tail ▸ t.pos_le_size
  unfold parseMainHeader at ok
  obtain ⟨⟨_,r1⟩,h1,ok⟩ := bind_ok ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  obtain ⟨⟨_,r2⟩,h2,ok⟩ := bind_ok ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  obtain ⟨⟨_,_,r3⟩,seg,ok⟩ := bind_ok ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  obtain ⟨⟨a,_⟩,loop,ok⟩ := bind_ok ok
  cases hc : a.cod <;> simp only [hc] at ok
  · cases ok
  cases hq : a.qcd <;> simp only [hq] at ok
  · cases ok
  cases ok
  have extent := HeaderWork.readSegment_extent seg
  have d := extent.2.1.trans ((Reader.u16be_pos h2).2.2.1.trans (Reader.u16be_pos h1).2.2.1)
  refine ⟨loop_fits _ (d ▸ Nat.le_refl _) (by simp [Fits]) loop, ?_, ep⟩
  have slots := (HeaderWork.segmentLoop_storage loop).1
  simp [HeaderWork.mainSlots] at slots
  have p1 := Reader.u16be_pos h1
  have p2 := Reader.u16be_pos h2
  have lim := r3.stop_le
  rw [d] at lim
  simp only [Reader.remaining] at slots
  dsimp only
  have := r3.pos_le
  omega

private abbrev Tables := Array TLM × Array PPM × Nat

private def step (L : Limits) (d : ByteArray) (s : RawSegment) (a : Tables) :
    Except Error (ForInStep Tables) := do
  let r ← rangeReader d ⟨s.offset,s.length⟩
  if s.code == Code.TLM then
    let t ← parseTLM L r
    let total := a.2.2 + t.entries.size
    L.check (.atOffset .marker s.offset) .tileParts total
    return .yield (a.1.push t,a.2.1,total)
  else if s.code == Code.PPM then
    let p ← parsePPM r
    return .yield (a.1,a.2.1.push p,a.2.2)
  else return .yield a

private theorem step_count {L : Limits} {d : ByteArray} {s : RawSegment} {a : Tables} {v}
    (old : a.2.2 ≤ L.maxTileParts) (ok : step L d s a = .ok v) : v.value.2.2 ≤ L.maxTileParts := by
  unfold step at ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  split at ok
  · obtain ⟨_,_,ok⟩ := bind_ok ok
    obtain ⟨_,hc,ok⟩ := bind_ok ok
    cases ok; exact (Limits.check_eq_ok_iff ..).1 hc
  · split at ok
    · obtain ⟨_,_,ok⟩ := bind_ok ok; cases ok; exact old
    · cases ok; exact old

private def stepTrace {cap : Nat} (wire : 2^32 ≤ cap) (L : Limits) (limit : 2*L.maxTileParts ≤ cap)
    (d : ByteArray) (hd : d.size ≤ cap) (s : RawSegment) (hs : s.offset+s.length ≤ d.size)
    (a : Tables) (old : a.2.2 ≤ L.maxTileParts) : Trace cap (step L d s a) (L.maxTileParts*2+8) := by
  unfold step
  have ho : s.offset ≤ cap := by omega
  apply bindTrace (DiagnosticMarker.rangeTrace d hd ⟨s.offset,s.length⟩ ho (by dsimp; omega))
  intro r range
  have hr : r.data.size ≤ cap := (DiagnosticMarker.range_source range).1 ▸ hd
  split
  · rw [← Nat.zero_add (L.maxTileParts*2+6)]
    apply bindTrace (j := 0) (tlmTrace wire L r hr)
    intro t ok
    have hc := tlm_count ok
    apply bindTrace (checkedTrace L _ _ _ ho (by omega))
    intro _ _
    exact doneTrace _
  · split
    · apply widen (bindTrace (ppmTrace r hr) (j := 0) ?_) (by omega)
      intro _ _
      exact doneTrace _
    · exact doneTrace _

private def tablesTrace {cap : Nat} (wire : 2^32 ≤ cap) (L : Limits) (limit : 2*L.maxTileParts ≤ cap)
    (d : ByteArray) (hd : d.size ≤ cap) (xs : List RawSegment)
    (fits : ∀ s ∈ xs, s.offset+s.length ≤ d.size) (a : Tables) (old : a.2.2 ≤ L.maxTileParts) :
    Trace cap (forIn xs a (step L d)) (xs.length*(L.maxTileParts*2+8)) := by
  cases xs with
  | nil => exact doneTrace _
  | cons s xs =>
    rw [List.forIn_cons, List.length_cons, Nat.succ_mul]
    apply bindTrace (stepTrace wire L limit d hd s (fits _ (.head _)) a old)
    intro v ok
    cases v with
    | done => exact doneTrace _
    | yield b => exact tablesTrace wire L limit d hd xs (fun x hx => fits x (.tail _ hx)) b (step_count old ok)
termination_by xs.length

/-- Scalar ceiling for source offsets and lengths, unsigned Nppm, cumulative TLM
entry refusals, and the first excess PPM chunk. -/
def scalarCap (L : Limits) (bytes : Nat) := max (2^32) (max bytes (2*L.maxTileParts+1))

/-- Event allowance for pointer segment reads, the two sorts and the reached chunk prefix. -/
def eventBudget (L : Limits) (bytes : Nat) :=
  (L.maxTileParts+1)*2+2 + bytes*(L.maxTileParts*2+8)

/-- Ordered diagnostic constructions at the real pointer call following a successful
main-header parse. The input range reader and the main parser discharge all location,
range, and count assumptions, including on paths that fail later in the pointer pass. -/
def pointerTrace {L : Limits} {d : ByteArray} {rg : ByteRange} {r t : Reader} {mh : MainHeader}
    (range : rangeReader d rg = .ok r) (main : parseMainHeader L r = .ok (mh,t)) :
    Trace (scalarCap L d.size) (parsePointers L mh d) (eventBudget L d.size) := by
  let cap := scalarCap L d.size
  have wire : 2^32 ≤ cap := Nat.le_max_left ..
  have hd : d.size ≤ cap := Nat.le_trans (Nat.le_max_left ..) (Nat.le_max_right ..)
  have limit : 2*L.maxTileParts+1 ≤ cap := Nat.le_trans (Nat.le_max_right ..) (Nat.le_max_right ..)
  have ⟨fits,count,last⟩ := main_ranges main
  rw [(DiagnosticMarker.range_source range).1] at fits count last
  have loop := tablesTrace wire L (by omega) d hd mh.pointers.toList
    (fun s hs => fits s (by simpa using hs)) (#[],#[],0) (Nat.zero_le _)
  rw [Array.forIn_toList, Array.length_toList] at loop
  unfold parsePointers eventBudget
  apply widen (bindTrace loop (j := (L.maxTileParts+1)*2+2) ?_)
    (Nat.add_le_add_left (Nat.mul_le_mul_right _ count) _)
  intro a _
  have hl : (Location.atOffset .marker mh.endPos).offset.getD 0 ≤ cap := Nat.le_trans last hd
  apply bindTrace (sortTrace (by omega) TLM.ztlm _ hl "Ztlm" (by decide) a.1)
  intro _ _
  apply bindTrace (sortTrace (by omega) PPM.zppm _ hl "Zppm" (by decide) a.2.1)
  intro _ _
  rw [← Nat.zero_add ((L.maxTileParts+1)*2)]
  apply bindTrace (j := 0) (chunksTrace wire L (by omega) d _ hl _ _ #[] (Nat.zero_le _))
  intro _ _
  exact doneTrace _

/-- The public decoder prefix through geometry and default coding, just before
`parsePointers`. The returned range and readers identify the admitted main header. -/
def pointerInput (L : Limits) (d : ByteArray) (red : Nat) :
    Except Error (Box.Container × Reader × MainHeader × Reader) := do
  L.check Decode.loc .decompLevels red
  let c ← Box.parseFile L d
  let r ← rangeReader d ⟨c.codestream.start,c.codestream.len⟩
  let (mh,t) ← parseMainHeader L r
  Header.checkGeometry L mh
  let _ ← Header.mainCoding mh
  return (c,r,mh,t)

private theorem reached {L : Limits} {d : ByteArray} {red : Nat} {c : Box.Container}
    {r t : Reader} {mh : MainHeader} (ok : pointerInput L d red = .ok (c,r,mh,t)) :
    L.check Decode.loc .decompLevels red = .ok () ∧ Box.parseFile L d = .ok c ∧
    rangeReader d ⟨c.codestream.start,c.codestream.len⟩ = .ok r ∧
    parseMainHeader L r = .ok (mh,t) ∧ Header.checkGeometry L mh = .ok () ∧
    ∃ defaults, Header.mainCoding mh = .ok defaults := by
  unfold pointerInput at ok
  obtain ⟨⟨⟩,red,ok⟩ := bind_ok ok
  obtain ⟨_,box,ok⟩ := bind_ok ok
  obtain ⟨_,range,ok⟩ := bind_ok ok
  obtain ⟨⟨_,_⟩,main,ok⟩ := bind_ok ok
  obtain ⟨⟨⟩,geom,ok⟩ := bind_ok ok
  obtain ⟨v,coding,ok⟩ := bind_ok ok
  cases ok
  exact ⟨red,box,range,main,geom,v,coding⟩

private theorem payload_mono (L : Limits) {a b : Nat} (le : a ≤ b) :
    HeaderPayload.pointersBudget L a ≤ HeaderPayload.pointersBudget L b := by
  unfold HeaderPayload.pointersBudget HeaderPayload.sortBudget
  repeat' first | assumption | exact Nat.le_refl _ | apply Nat.add_le_add | apply Nat.mul_le_mul

/-- Charges on arbitrary public bytes. A preceding failure gives zero pointer work.
The first component counts the production payload visits and copies, including
`chunkPayload`'s two range walks and gathered Nppm. The second lists diagnostics. -/
def publicCharge (L : Limits) (d : ByteArray) (red : Nat) :
    Nat × List (Σ s, Built (scalarCap L d.size) s) :=
  match h : pointerInput L d red with
  | .error _ => (0,[])
  | .ok (_,_,mh,_) =>
    let p := reached h
    ((HeaderPayload.pointerPayload L mh d).run.2,(pointerTrace p.2.2.1 p.2.2.2.1).messages)

/-- The combined pointer payload/diagnostic work and the cumulative diagnostic allocation
on any public bytes fit bounds depending only on the limits and byte count. -/
theorem public_cost (L : Limits) (d : ByteArray) (red : Nat) :
    let (payload,events) := publicCharge L d red
    let budget := eventBudget L d.size * Text.workBound (scalarCap L d.size) 128 24
    payload + (events.map (fun m => m.2.tree.work)).sum ≤ HeaderPayload.pointersBudget L d.size + budget ∧
      (events.map (fun m => m.2.tree.storage)).sum ≤ budget := by
  simp only [publicCharge]
  split
  · exact ⟨Nat.zero_le _, Nat.zero_le _⟩
  · rename_i c r mh t ok
    have p := reached ok
    let tr := pointerTrace p.2.2.1 p.2.2.2.1
    have count := (main_ranges p.2.2.2.1).2.1
    rw [(DiagnosticMarker.range_source p.2.2.1).1] at count
    have pay := Nat.le_trans (HeaderPayload.pointerPayload L mh d).bound (payload_mono L count)
    exact ⟨Nat.add_le_add pay (trace_cost tr).1, trace_storage tr⟩

/-- On a reached pointer error the header parser and both public decoders return that
same error. Its stored fields, including the computed value of a refused cumulative
TLM count or chunk count, fit the pointer scalar ceiling and retained-record budget. -/
theorem public_refusal {L : Limits} {d : ByteArray} {opts : DecodeOptions} {c : Box.Container}
    {r t : Reader} {mh : MainHeader} (ok : pointerInput L d opts.reduce = .ok (c,r,mh,t))
    {e : Error} (bad : parsePointers L mh d = .error e) :
    let cap := scalarCap L d.size
    Header.parse L d = .error e ∧ decodeCodestream L d opts.reduce = .error e ∧
      JPEG2000.decode L d opts = .error e ∧
      storedPayload false e ≤ 6 + Text.byteBound cap 128 24 + 2*bits cap ∧
      (∀ loc k v b, e = .limitExceeded loc k v b → v ≤ cap) := by
  obtain ⟨red,box,range,main,geom,_,coding⟩ := reached ok
  have hp : Header.parse L d = .error e := by
    simp only [Header.parse,box,Header.parseCodestreamIn,range,main,geom,coding,bad,bind,Except.bind]
  have raw : decodeCodestream L d opts.reduce = .error e := by
    simp only [decodeCodestream,red,hp,bind,Except.bind]
  let tr := pointerTrace range main
  refine ⟨hp,raw,by simp only [JPEG2000.decode,raw,bind,Except.bind],trace_retained tr bad,?_⟩
  rintro loc k v b rfl
  exact (tr.origin _ bad).2

end JPEG2000.Spec.Resources.DiagnosticPointers
