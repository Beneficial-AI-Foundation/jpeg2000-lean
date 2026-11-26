import Spec.Resources.DiagnosticTileMarkers
import Spec.Resources.DiagnosticPointers

/-!
# Tile-part diagnostic construction (Plan.md §§3–5, 7, S3)

T.800 A.4.2–A.4.4, A.7.3 and A.7.5. Follow the production reader through
EOC and then the per-tile assembly walk. Retained row invariants bound the
previous part count, absolute diagnostic positions and the number of PLT
entries concatenated before the cumulative packet check.
-/

namespace JPEG2000.Spec.Resources.DiagnosticTilePart

open Bytes Marker TilePart DiagnosticCost
open Tier2Equiv (bind_ok)

private def Row (L : Limits) (bytes : Nat) (ps : Array TilePartHeader) : Prop :=
  ps.size ≤ L.maxTilePartsPerTile ∧ ∀ p ∈ ps, p.pos ≤ bytes ∧
    p.segments.size ≤ bytes+1 ∧ ∀ q, TileSegment.plt q ∈ p.segments → q.lengths.size ≤ bytes

private theorem row_empty (L : Limits) (b : Nat) : Row L b #[] := by simp [Row]

private theorem rowAt {L : Limits} {b : Nat} {a : Array (Array TilePartHeader)}
    (ha : ∀ ps ∈ a, Row L b ps) (i : Nat) : Row L b (a[i]?.getD #[]) := by
  cases h : a[i]? with
  | none => exact row_empty L b
  | some ps => exact ha _ (Array.mem_of_getElem? h)

private theorem remaining (r : Reader) : r.remaining ≤ r.data.size :=
  Nat.le_trans (Nat.sub_le ..) r.stop_le

private theorem readRows {c : Ctx} {r t : Reader} {a z : State} {b : Nat}
    (data : r.data.size = b) (count : a.pocEntries ≤ c.limits.maxPocEntries)
    (rows : ∀ ps ∈ a.parts, Row c.limits b ps) (ok : readTilePart c a r = .ok (z,t)) :
    ∀ ps ∈ z.parts, Row c.limits b ps := by
  unfold readTilePart at ok
  obtain ⟨⟨_,r1⟩,h1,ok⟩ := bind_ok ok
  obtain ⟨⟨_,_,r2⟩,h2,ok⟩ := bind_ok ok
  obtain ⟨sot,_,ok⟩ := bind_ok ok
  iterate 2 obtain ⟨_,_,ok⟩ := bind_ok ok
  obtain ⟨_,perTile,ok⟩ := bind_ok ok
  iterate 3 obtain ⟨_,_,ok⟩ := bind_ok ok
  dsimp only at ok
  split at ok <;> split at ok <;> try contradiction
  all_goals
    simp only [pure_bind] at ok
    obtain ⟨⟨tp,_⟩,take,ok⟩ := bind_ok ok
    obtain ⟨⟨acc,rd⟩,header,ok⟩ := bind_ok ok
    cases ok
    have src := (Reader.take_spec take).2.2.1.trans
      ((HeaderWork.readSegment_extent h2).2.1.trans (Reader.u16be_pos h1).2.2.1)
    have ⟨_,fits,slots,_,_⟩ := DiagnosticTileMarkers.header_continuation (a := _) count
      (by intro _ h; simp at h) header
    change acc.markers.size + acc.segments.size + rd.remaining ≤ 1+0+tp.remaining at slots
    have rem := remaining tp
    rw [src,data] at rem fits
    intro ps hp
    obtain ⟨j,hj,rfl⟩ := Array.mem_iff_getElem.1 hp
    have hj' : j < a.parts.size := by simpa using hj
    dsimp only
    rw [Array.getElem_modify]
    split
    · rename_i eq
      subst j
      have lim := (Limits.check_eq_ok_iff ..).1 perTile
      rw [Array.getElem?_eq_getElem hj'] at lim
      refine ⟨by simpa [Limits.bound] using lim,?_⟩
      intro p hp
      rcases Array.mem_push.1 hp with old | rfl
      · exact (rows _ (Array.getElem_mem hj')).2 _ old
      · exact ⟨data ▸ r.pos_le_size,by dsimp only; omega,fun q h => (fits (.plt q) h).1⟩
    · exact rows _ (Array.getElem_mem hj')

private def bad {α : Type} {cap : Nat} {s : String} (loc : Location)
    (hl : loc.offset.getD 0 ≤ cap) (b : Built cap s) :
    Trace cap (Except.error (.malformed loc s) : Except Error α) 1 :=
  ⟨[⟨s,b⟩], by simp, by intro e h; cases h; exact ⟨hl,⟨s,b⟩,by simp,rfl⟩⟩

private def trunc {α : Type} {cap : Nat} {s : String} (r : Reader)
    (hr : r.pos ≤ cap) (b : Built cap s) :
    Trace cap (Except.error (r.truncErr s) : Except Error α) 1 :=
  ⟨[⟨s,b⟩], by simp, by intro e h; cases h; exact ⟨hr,⟨s,b⟩,by simp,rfl⟩⟩

private def propagate {α β : Type} {cap k : Nat} {x : Except Error α} {e : Error}
    (t : Trace cap x k) (h : x = .error e) : Trace cap (Except.error e : Except Error β) k :=
  ⟨t.messages,t.countBound,by intro _ he; cases he; exact t.origin _ h⟩

/-- Ceiling for the wire values, input offsets, admitted indices and first refused
counts. Packet admission sees the previous total plus the entire current tile's PLT array. -/
def scalarCap (L : Limits) (b : Nat) :=
  2^32 + b + 2 + L.maxTiles + L.maxTileParts + L.maxTilePartsPerTile + 2*L.maxPocEntries +
    L.maxPackets + L.maxTilePartsPerTile*((b+1)*b)

/-- Per attempted part, the SOT prefix, index and extent checks, then the SOD loop. -/
def readBudget (L : Limits) (b : Nat) := DiagnosticTileMarkers.headerBudget L b + 19

private def readTrace (c : Ctx) (a : State) (r : Reader) (b : Nat)
    (data : r.data.size = b) (grid : c.numTiles ≤ c.limits.maxTiles) (components : c.csiz ≤ 16384)
    (tot : a.total ≤ c.limits.maxTileParts) (count : a.pocEntries ≤ c.limits.maxPocEntries)
    (rows : ∀ ps ∈ a.parts, Row c.limits b ps) :
    Trace (scalarCap c.limits b) (readTilePart c a r) (readBudget c.limits b) := by
  let cap := scalarCap c.limits b
  have wire : 2^32 ≤ cap := by dsimp [cap,scalarCap]; omega
  have big : b+2 ≤ cap := by dsimp [cap,scalarCap]; omega
  have pos : r.pos ≤ cap := by have := r.pos_le_size; omega
  unfold readTilePart readBudget
  apply bindTrace (u16beTrace r pos)
  rintro ⟨_,r1⟩ h1
  have d1 := (Reader.u16be_pos h1).2.2.1
  apply bindTrace (segmentTrace r1 (by rw [d1,data]; omega) (by omega))
  rintro ⟨body,len,r2⟩ h2
  have ext := HeaderWork.readSegment_extent h2
  have d2 := ext.2.1.trans d1
  apply bindTrace (sotTrace body (by rw [ext.1,d1,data]; exact big) wire)
  intro s _
  have hi : s.isot.toNat ≤ cap := by have := s.isot.toNat_lt; omega
  have hg : c.numTiles ≤ cap := by dsimp [cap,scalarCap]; omega
  have hn : s.tnsot.toNat ≤ cap := by have := s.tnsot.toNat_lt; omega
  have ht : s.tpsot.toNat ≤ cap := by have := s.tpsot.toNat_lt; omega
  let prev := a.parts[s.isot.toNat]?.getD #[]
  have prevlim := (rowAt rows s.isot.toNat).1
  have hp : prev.size+1 ≤ cap := by dsimp [prev,cap,scalarCap]; omega
  apply bindTrace (requireTrace r pos _ _ (closeExpr
    (catExpr (catExpr (catExpr (litExpr _ "Isot = ") (decExpr hi))
      (litExpr _ " ≥ number of tiles ")) (decExpr hg)) (by decide) (by decide)))
  intro _ _
  apply bindTrace (checkedTrace c.limits _ .tileParts _ pos (by dsimp [cap,scalarCap]; omega))
  intro _ _
  apply bindTrace (checkedTrace c.limits _ .tilePartsPerTile _ pos hp)
  intro _ _
  apply bindTrace (checkedTrace c.limits _ .tilePartsPerTile _ pos hn)
  intro _ _
  let tile := catExpr (litExpr _ "tile ") (decExpr hi)
  apply bindTrace (requireTrace r pos _ _ (closeExpr
    (catExpr (catExpr (catExpr (catExpr (catExpr tile (litExpr _ ": TPsot = ")) (decExpr ht))
      (litExpr _ ", expected ")) (decExpr (n := prev.size) (by omega)))
        (litExpr _ " (tile-parts in TPsot order)")) (by decide) (by decide)))
  intro _ _
  apply bindTrace (requireTrace r pos _ _ (closeExpr
    (catExpr (catExpr tile (litExpr _ ": inconsistent TNsot ")) (decExpr hn)) (by decide) (by decide)))
  intro _ _
  dsimp only
  split <;> split
  all_goals try exact widen (trunc r pos
    (oneFixed "Psot = 0 but the codestream does not end with EOC" (by decide))) (by omega)
  all_goals try
    have len : s.psot.toNat ≤ cap := by have := s.psot.toNat_lt; omega
    exact widen (trunc r pos (closeExpr (catExpr (catExpr (litExpr _ "tile-part of Psot = ") (decExpr len))
      (litExpr _ " extends past the end of data")) (by decide) (by decide))) (by omega)
  all_goals
    simp only [pure_bind]
    apply widen (bindTrace (j := DiagnosticTileMarkers.headerBudget c.limits b)
      (takeTrace r2 (by have := r2.pos_le_size; rw [d2,data] at this; omega) _
        (by have := r.stop_le; omega)) ?_) (by omega)
    rintro ⟨tp,next⟩ take
    have src := (Reader.take_spec take).2.2.1.trans d2
    have hb : tp.remaining ≤ b := by simpa only [src,data] using remaining tp
    apply widen (bindTrace (j := 0) (DiagnosticTileMarkers.headerTrace (cap := cap) (by omega)
      c.limits (by dsimp [cap,scalarCap]; omega) c.csiz (by omega) _ _ _ _ count tp
      (by rw [src,data]; omega)) (fun _ _ => doneTrace _)) ?_
    simp only [Nat.zero_add]
    unfold DiagnosticTileMarkers.headerBudget
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hb) _

private theorem loopRows {c : Ctx} {r : Reader} {a z : State} {b f : Nat}
    (data : r.data.size = b) (count : a.pocEntries ≤ c.limits.maxPocEntries)
    (rows : ∀ ps ∈ a.parts, Row c.limits b ps) (ok : tilePartLoop c f a r = .ok z) :
    ∀ ps ∈ z.parts, Row c.limits b ps := by
  induction f generalizing a r with
  | zero => cases ok
  | succ f ih =>
    rw [tilePartLoop] at ok
    split at ok <;> try contradiction
    split at ok
    · cases ok; exact rows
    split at ok <;> try contradiction
    split at ok <;> try contradiction
    rename_i z' t step
    apply ih ((HeaderWork.readTilePart_step step).2.2.2.1 ▸ data)
      (DiagnosticTileMarkers.read_count count step) (readRows data count rows step) ok

private def loopTrace (c : Ctx) (b f : Nat) (a : State) (r : Reader)
    (data : r.data.size = b) (grid : c.numTiles ≤ c.limits.maxTiles) (components : c.csiz ≤ 16384)
    (tot : a.total ≤ c.limits.maxTileParts) (count : a.pocEntries ≤ c.limits.maxPocEntries)
    (rows : ∀ ps ∈ a.parts, Row c.limits b ps) :
    Trace (scalarCap c.limits b) (tilePartLoop c f a r) (f*(readBudget c.limits b+2)+1) := by
  let cap := scalarCap c.limits b
  have pos : r.pos ≤ cap := by have := r.pos_le_size; dsimp [cap,scalarCap]; omega
  induction f generalizing a r with
  | zero =>
    simpa only [tilePartLoop,Nat.zero_mul,Nat.zero_add] using
      (trunc (α := State) r pos (oneFixed "codestream: fuel exhausted before EOC" (by decide)))
  | succ f ih =>
    rw [tilePartLoop,Nat.succ_mul]
    split
    · exact widen (includeTrace (u16beTrace r pos)
        (trunc r pos (oneFixed _ (by decide)))) (by omega)
    · rename_i m t h
      split
      · exact doneTrace _
      split
      · have hm : m.toNat ≤ cap := by have := m.toNat_lt; dsimp [cap,scalarCap]; omega
        let digits : ExprFor cap (String.ofList (Nat.toDigits 16 m.toNat)) 0 1 := ⟨_,rfl,.hex hm⟩
        exact widen (bad _ pos (closeExpr (catExpr (litExpr _ "expected SOT or EOC, found ")
          (catExpr (litExpr _ "0x") digits)) (by decide) (by decide))) (by omega)
      let part := readTrace c a r b data grid components tot count rows
      split
      · exact widen (propagate part (by assumption)) (by omega)
      · rename_i z next step
        have hs := HeaderWork.readTilePart_step step
        have dn : next.data.size = b := hs.2.2.2.1 ▸ data
        apply widen (includeTrace part (ih z next dn hs.2.1 (DiagnosticTileMarkers.read_count count step)
          (readRows data count rows step) (by have := next.pos_le_size; dsimp [cap,scalarCap]; omega))) (by omega)

/-! ## Per-tile PLT accumulation and TNsot validation -/

private def pltSegments (p : TilePartHeader) := p.segments.filterMap fun | .plt x => some x | _ => none

private def appendLengths (a : Array Nat) (p : TilePartHeader) : Except Error (Array Nat) := do
  return a ++ (← partPlt p)

private def lengthTrace {cap : Nat} (wire : 255 ≤ cap) (ps : List TilePartHeader) (a : Array Nat)
    (positions : ∀ p ∈ ps, p.pos ≤ cap) : Trace cap (ps.foldlM appendLengths a) ps.length := by
  cases ps with
  | nil => exact doneTrace _
  | cons p ps =>
    simp only [List.foldlM_cons, appendLengths, partPlt, bind_assoc,pure_bind,List.length_cons]
    apply bindTrace (DiagnosticPointers.sortTrace wire PLT.zplt _ (positions _ (by simp)) "Zplt" (by decide) _)
    intro _ _
    exact lengthTrace wire ps _ (fun q h => positions q (by simp [h]))
termination_by ps.length

private theorem concatWidth (qs : List PLT) (a : Array Nat) (b : Nat)
    (width : ∀ q ∈ qs, q.lengths.size ≤ b) :
    (qs.foldl (fun acc q => acc ++ q.lengths) a).size ≤ a.size + qs.length*b := by
  induction qs generalizing a with
  | nil => simp
  | cons q qs ih =>
    rw [List.foldl_cons,List.length_cons,Nat.succ_mul]
    have h := ih (a++q.lengths) (fun p hp => width p (by simp [hp]))
    rw [Array.size_append] at h
    have := width q (by simp)
    omega

private theorem partWidth {p : TilePartHeader} {b : Nat} {a : Array Nat}
    (slots : p.segments.size ≤ b+1) (width : ∀ q, TileSegment.plt q ∈ p.segments → q.lengths.size ≤ b)
    (ok : partPlt p = .ok a) : a.size ≤ (b+1)*b := by
  unfold partPlt at ok
  obtain ⟨s,sort,ok⟩ := bind_ok ok
  cases ok
  have perm : s.Perm (pltSegments p) := by
    unfold sortUnique at sort
    dsimp only at sort
    split at sort <;> cases sort
    exact HeaderWork.insertionSort_perm ..
  have len : s.size ≤ b+1 := Nat.le_trans (Nat.le_of_eq perm.size_eq)
    (Nat.le_trans Array.size_filterMap_le slots)
  rw [← Array.foldl_toList]
  apply Nat.le_trans (concatWidth s.toList #[] b ?_) (by simpa using Nat.mul_le_mul_right b len)
  intro q hq
  obtain ⟨v,hv,eq⟩ := Array.mem_filterMap.1 (perm.mem_iff.1 (by simpa using hq))
  cases v <;> cases eq
  exact width _ hv

private theorem tileWidth {L : Limits} {b : Nat} {ps : Array TilePartHeader} {corr : Bool}
    {i : Nat} {t : Tile} (row : Row L b ps) (ok : assembleTile corr i ps = .ok t) :
    t.plt.size ≤ L.maxTilePartsPerTile*((b+1)*b) := by
  have fold (xs : List TilePartHeader) (a z : Array Nat) (members : ∀ p ∈ xs, p ∈ ps)
      (done_ : xs.foldlM appendLengths a = .ok z) : z.size ≤ a.size + xs.length*((b+1)*b) := by
    induction xs generalizing a with
    | nil => cases done_; simp
    | cons p xs ih =>
      simp only [List.foldlM_cons,appendLengths,bind_assoc,pure_bind] at done_
      obtain ⟨v,hv,tail⟩ := bind_ok done_
      have h := ih (a++v) (fun q h => members q (by simp [h])) tail
      have fields := (row.2 p (members p (by simp))).2
      have w := partWidth fields.1 fields.2 hv
      rw [Array.size_append] at h
      rw [List.length_cons,Nat.succ_mul]
      omega
  unfold assembleTile at ok
  dsimp only at ok
  split at ok <;> split at ok <;> try (obtain ⟨_,bad,_⟩ := bind_ok ok; cases bad)
  all_goals
    obtain ⟨_,_,ok⟩ := bind_ok ok
    obtain ⟨z,hz,ok⟩ := bind_ok ok
    cases ok
    rw [← Array.foldlM_toList] at hz
    have h := fold ps.toList #[] z (by simp) hz
    exact Nat.le_trans (by simpa using h) (Nat.mul_le_mul_right _ row.1)

private def declared (ps : Array TilePartHeader) :=
  ps.foldl (fun a p => if p.sot.tnsot ≠ 0 then p.sot.tnsot.toNat else a) 0

private theorem declaredBound (ps : Array TilePartHeader) : declared ps ≤ 255 := by
  have aux (xs : List TilePartHeader) (a : Nat) (ha : a ≤ 255) :
      xs.foldl (fun a p => if p.sot.tnsot ≠ 0 then p.sot.tnsot.toNat else a) a ≤ 255 := by
    induction xs generalizing a with
    | nil => exact ha
    | cons p xs ih =>
      apply ih
      dsimp only
      split <;> first | exact ha | (have := p.sot.tnsot.toNat_lt; omega)
  unfold declared
  rw [← Array.foldl_toList]
  exact aux _ _ (by decide)

private theorem locBound {L : Limits} {b : Nat} {ps : Array TilePartHeader} (row : Row L b ps) :
    ((ps[0]?.map (·.pos)).getD 0) ≤ b := by
  cases h : ps[0]? with
  | none => exact Nat.zero_le _
  | some p => exact (row.2 _ (Array.mem_of_getElem? h)).1


private def tileTrace {L : Limits} {b : Nat} (corr : Bool) (i : Nat) (ps : Array TilePartHeader)
    (row : Row L b ps) (idx : i ≤ L.maxTiles) :
    Trace (scalarCap L b) (assembleTile corr i ps) (L.maxTilePartsPerTile+1) := by
  let cap := scalarCap L b
  let tn := if declared ps ≠ 0 ∧ corr then declared ps+1 else declared ps
  have wire : 2^32 ≤ cap := by dsimp [cap,scalarCap]; omega
  have big : b ≤ cap := by dsimp [cap,scalarCap]; omega
  have hl := Nat.le_trans (locBound row) big
  have hi : i ≤ cap := by dsimp [cap,scalarCap]; omega
  have hp : ps.size ≤ cap := by have := row.1; dsimp [cap,scalarCap]; omega
  have hd : declared ps ≤ cap := by have := declaredBound ps; omega
  have ht : tn ≤ cap := by have := declaredBound ps; dsimp [tn]; split <;> omega
  let prefixText := catExpr (catExpr (catExpr (catExpr (catExpr (litExpr _ "tile ") (decExpr hi))
    (litExpr _ ": ")) (decExpr hp)) (litExpr _ " tile-parts, TNsot = ")) (decExpr hd)
  unfold assembleTile
  change Trace _ (if tn ≠ 0 ∧ tn ≠ ps.size then _ else _) _
  split
  · -- The correction note is itself an interpolation. Its appends and decimal
    -- conversion form the right subtree of the outer message.
    cases corr
    · by_cases extra : ps.size = tn+1
      · change Trace _ (Except.error (.malformed _ (_ ++ (if ps.size = tn+1 then _ else ""))) : Except Error Tile) _
        rw [ite_eq_left extra]
        exact widen (bad _ hl (closeExpr (catExpr prefixText
          (litExpr _ " (TPsot = TNsot without the TNsot correction)")) (by decide) (by decide))) (by omega)
      · change Trace _ (Except.error (.malformed _ (_ ++ (if ps.size = tn+1 then _ else ""))) : Except Error Tile) _
        rw [ite_eq_right extra]
        exact widen (bad _ hl (closeExpr (catExpr prefixText (litExpr _ "")) (by decide) (by decide))) (by omega)
    · let note := catExpr (catExpr (litExpr _ " (corrected to ") (decExpr ht)) (litExpr _ ")")
      exact widen (bad _ hl (closeExpr (catExpr prefixText note) (by decide) (by decide))) (by omega)
  · apply bindTrace (DiagnosticPointers.sortTrace (by omega) PPT.zppt _ hl "Zppt" (by decide) _)
    intro _ _
    rw [← Array.foldlM_toList]
    apply widen (bindTrace (j := 0) (lengthTrace (by omega) ps.toList #[]
      (by intro p hm; exact Nat.le_trans (row.2 p (by simpa using hm)).1 big)) (fun _ _ => doneTrace _)) ?_
    simpa using row.1

private def assemblyTrace (L : Limits) (b : Nat) (corr : Bool) (parts : Array (Array TilePartHeader))
    (rows : ∀ ps ∈ parts, Row L b ps) (f i packets : Nat) (a : Array Tile)
    (indices : i+f ≤ L.maxTiles) (admitted : packets ≤ L.maxPackets) :
    Trace (scalarCap L b) (assembleTiles L corr parts f i packets a) (f*(L.maxTilePartsPerTile+1)) := by
  induction f generalizing i packets a with
  | zero => exact doneTrace _
  | succ f ih =>
    rw [assembleTiles,Nat.succ_mul]
    dsimp only
    split
    · exact widen (ih _ _ a (by omega) admitted) (by omega)
    let row := rowAt rows i
    let tile := tileTrace corr i _ row (by omega)
    split
    · exact widen (propagate tile (by assumption)) (by omega)
    · rename_i t step
      have packetBound := tileWidth row step
      let loc := Location.atOffset .marker ((((parts[i]?.getD #[])[0]?).map (·.pos)).getD 0)
      let check := checkedTrace (cap := scalarCap L b) L loc .packets (packets+t.plt.size)
        (Nat.le_trans (locBound row) (show b ≤ scalarCap L b by unfold scalarCap; omega))
        (by unfold scalarCap; omega)
      split
      · exact widen (includeTrace tile (propagate check (by assumption))) (by omega)
      · rename_i ok
        exact widen (includeTrace tile (ih _ _ _ (by omega) ((Limits.check_eq_ok_iff ..).1 ok))) (by omega)

/-- Complete diagnostic event allowance for the byte-fuelled read loop and
the admitted tile rows. Each row attempts one PPT sort and at most one PLT
sort per part after TNsot validation. -/
def eventBudget (L : Limits) (b : Nat) :=
  b*(readBudget L b+2)+1 + L.maxTiles*(L.maxTilePartsPerTile+1)

set_option maxRecDepth 2048 in
/-- Ordered diagnostic events of the exact tile-part stage invoked by
`Header.parseCodestreamIn`. Its hypotheses are the earlier successful
range, main-header and geometry reads. The stage itself can fail. -/
def tilePartsTrace {L : Limits} {d : ByteArray} {rg : ByteRange} {r t : Reader} {mh : MainHeader}
    (range : rangeReader d rg = .ok r) (main : parseMainHeader L r = .ok (mh,t))
    (geom : Header.checkGeometry L mh = .ok ()) :
    Trace (scalarCap L d.size) (parseTileParts L mh t) (eventBudget L d.size) := by
  have components : mh.siz.csiz ≤ 16384 := by
    obtain ⟨_,_,_,_,_,_,_,_,_,_,h,_⟩ := DiagnosticMarker.main_source main
    exact h
  have data := (DiagnosticMarker.main_source main).1.trans (DiagnosticMarker.range_source range).1
  have grid := ((Resources.checkGeometry_ok_iff ..).1 geom).2.2.2.1
  have pc := DiagnosticTileMarkers.main_count main
  let c : Ctx := ⟨L,mh.siz.csiz,numTiles mh.siz,mh.pointers.any (·.code == Code.PPM)⟩
  let a : State := { parts := Array.replicate c.numTiles #[], total := 0,
                     pocEntries := mh.poc.foldl (fun n p => n+p.entries.size) 0 }
  have rows : ∀ ps ∈ a.parts, Row L d.size ps := by
    intro ps h
    obtain ⟨_,rfl⟩ := Array.mem_replicate.1 h
    exact row_empty ..
  unfold parseTileParts
  apply bindTrace (checkedTrace L _ .tiles _ (by
    have pos := t.pos_le_size; rw [data] at pos; change t.pos ≤ _; unfold scalarCap; omega)
    (by unfold scalarCap; omega))
  intro _ _
  apply widen (bindTrace (j := numTiles mh.siz*(L.maxTilePartsPerTile+1))
    (loopTrace c d.size t.remaining a t (data ▸ rfl) grid components (Nat.zero_le _) pc rows) ?_) ?_
  · intro z done_
    exact assemblyTrace L d.size _ _ (loopRows (data ▸ rfl) pc rows done_) _ _ _ _ (by simpa using grid) (Nat.zero_le _)
  · have rem : t.remaining ≤ d.size := data ▸ remaining t
    have left := Nat.mul_le_mul_right (readBudget L d.size+2) rem
    have right := Nat.mul_le_mul_right (L.maxTilePartsPerTile+1) grid
    change numTiles mh.siz * _ + (t.remaining*(readBudget L d.size+2)+1) ≤
      d.size*(readBudget L d.size+2)+1+L.maxTiles*(L.maxTilePartsPerTile+1)
    omega


private theorem mainDescriptors {L : Limits} {r t : Reader} {mh : MainHeader}
    (ok : parseMainHeader L r = .ok (mh,t)) : mh.pointers.size + mh.poc.size ≤ r.data.size+2 := by
  unfold parseMainHeader at ok
  obtain ⟨⟨_,r1⟩,h1,ok⟩ := bind_ok ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  obtain ⟨⟨_,r2⟩,h2,ok⟩ := bind_ok ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  obtain ⟨⟨_,_,r3⟩,h3,ok⟩ := bind_ok ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  obtain ⟨⟨a,_⟩,loop,ok⟩ := bind_ok ok
  cases hc : a.cod <;> simp only [hc] at ok <;> try contradiction
  cases hq : a.qcd <;> simp only [hq] at ok <;> try contradiction
  cases ok
  have slots := (HeaderWork.segmentLoop_storage loop).1
  simp [HeaderWork.mainSlots] at slots
  have bytes := remaining r3
  rw [(HeaderWork.readSegment_extent h3).2.1,(Reader.u16be_pos h2).2.2.1,(Reader.u16be_pos h1).2.2.1] at bytes
  dsimp only
  omega

/-- Payload visits and copies through the same reached prefix, including the
tile whose fully concatenated PLT array first exceeds the packet ceiling. -/
theorem tileParts_payload {L : Limits} {d : ByteArray} {rg : ByteRange} {r t : Reader} {mh : MainHeader}
    (range : rangeReader d rg = .ok r) (main : parseMainHeader L r = .ok (mh,t)) :
    let p := HeaderPayload.tilePartsPayload L mh t
    p.run.1 = parseTileParts L mh t ∧ p.run.2 ≤ HeaderPayload.partsBudget L d.size := by
  let p := HeaderPayload.tilePartsPayload L mh t
  refine ⟨p.erase,Nat.le_trans p.bound ?_⟩
  obtain ⟨src,_,_,_,_,_,_,_,_,_,_,components⟩ := DiagnosticMarker.main_source main
  have fields := mainDescriptors main
  rw [(DiagnosticMarker.range_source range).1] at src fields
  dsimp only [HeaderPayload.partsBudget,HeaderPayload.readPartBudget]
  rw [src]
  apply Nat.add_le_add (by omega)
  apply Nat.add_le_add_right
  apply Nat.mul_le_mul_left
  apply Nat.add_le_add_left
  apply Nat.add_le_add_right
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul_left
  unfold HeaderPayload.markerBudget
  omega

/-- Public decoder prefix immediately before the tile-part parser, including
the preceding main-header pointer pass. -/
def tileInput (L : Limits) (d : ByteArray) (red : Nat) :
    Except Error (Box.Container × Reader × MainHeader × Reader) := do
  let (c,r,mh,t) ← DiagnosticPointers.pointerInput L d red
  let _ ← parsePointers L mh d
  return (c,r,mh,t)

private theorem reached {L : Limits} {d : ByteArray} {red : Nat} {c : Box.Container}
    {r t : Reader} {mh : MainHeader} (ok : tileInput L d red = .ok (c,r,mh,t)) :
    L.check Decode.loc .decompLevels red = .ok () ∧ Box.parseFile L d = .ok c ∧
    rangeReader d ⟨c.codestream.start,c.codestream.len⟩ = .ok r ∧
    parseMainHeader L r = .ok (mh,t) ∧ Header.checkGeometry L mh = .ok () ∧
    (∃ defaults, Header.mainCoding mh = .ok defaults) ∧
    ∃ tlm ppm, parsePointers L mh d = .ok (tlm,ppm) := by
  unfold tileInput at ok
  obtain ⟨⟨_,_,_,_⟩,prefixOK,ok⟩ := bind_ok ok
  obtain ⟨⟨_,_⟩,ptr,ok⟩ := bind_ok ok
  cases ok
  unfold DiagnosticPointers.pointerInput at prefixOK
  obtain ⟨⟨⟩,red,ok⟩ := bind_ok prefixOK
  obtain ⟨_,box,ok⟩ := bind_ok ok
  obtain ⟨_,range,ok⟩ := bind_ok ok
  obtain ⟨⟨_,_⟩,main,ok⟩ := bind_ok ok
  obtain ⟨⟨⟩,geom,ok⟩ := bind_ok ok
  obtain ⟨_,coding,ok⟩ := bind_ok ok
  cases ok
  exact ⟨red,box,range,main,geom,⟨_,coding⟩,_,_,ptr⟩

/-- Descriptor and diagnostic work actually reached by the public decoder.
An earlier failure contributes zero tile-part events and zero tile-part payload. -/
def publicCharge (L : Limits) (d : ByteArray) (red : Nat) :
    Nat × List (Σ s, Built (scalarCap L d.size) s) :=
  match h : tileInput L d red with
  | .error _ => (0,[])
  | .ok (_,_,mh,t) =>
    let p := reached h
    ((HeaderPayload.tilePartsPayload L mh t).run.2,
      (tilePartsTrace p.2.2.1 p.2.2.2.1 p.2.2.2.2.1).messages)

/-- Ordered event count, payload visits plus diagnostic construction work, and
cumulative diagnostic allocation on all public inputs and reductions. -/
theorem public_cost (L : Limits) (d : ByteArray) (red : Nat) :
    let (payload,events) := publicCharge L d red
    let count := eventBudget L d.size
    let budget := count * Text.workBound (scalarCap L d.size) 128 24
    events.length ≤ count ∧
      payload + (events.map (fun m => m.2.tree.work)).sum ≤ HeaderPayload.partsBudget L d.size + budget ∧
      (events.map (fun m => m.2.tree.storage)).sum ≤ budget := by
  simp only [publicCharge]
  split
  · exact ⟨Nat.zero_le _,Nat.zero_le _,Nat.zero_le _⟩
  · rename_i c r mh t h
    have p := reached h
    let tr := tilePartsTrace p.2.2.1 p.2.2.2.1 p.2.2.2.2.1
    exact ⟨tr.countBound,Nat.add_le_add (tileParts_payload p.2.2.1 p.2.2.2.1).2 (trace_cost tr).1,
      trace_storage tr⟩

/-- A reached refusal propagates unchanged to both public decoders. The
stored record, its source offset and the computed value of every refused
limit check fit the input- and limit-dependent bounds before caller rendering. -/
theorem public_refusal {L : Limits} {d : ByteArray} {opts : DecodeOptions} {c : Box.Container}
    {r t : Reader} {mh : MainHeader} (ok : tileInput L d opts.reduce = .ok (c,r,mh,t))
    {e : Error} (bad : parseTileParts L mh t = .error e) :
    let cap := scalarCap L d.size
    Header.parse L d = .error e ∧ decodeCodestream L d opts.reduce = .error e ∧
      JPEG2000.decode L d opts = .error e ∧
      storedPayload false e ≤ 6 + Text.byteBound cap 128 24 + 2*bits cap ∧
      e.offset?.getD 0 ≤ cap ∧ (∀ loc k v bound, e = .limitExceeded loc k v bound → v ≤ cap) := by
  obtain ⟨red,box,range,main,geom,⟨_,coding⟩,_,_,ptr⟩ := reached ok
  have hp : Header.parse L d = .error e := by
    simp only [Header.parse,box,Header.parseCodestreamIn,range,main,geom,coding,ptr,bad,bind,Except.bind]
  have raw : decodeCodestream L d opts.reduce = .error e := by
    simp only [decodeCodestream,red,hp,bind,Except.bind]
  let tr := tilePartsTrace range main geom
  refine ⟨hp,raw,by simp only [JPEG2000.decode,raw,bind,Except.bind],trace_retained tr bad,(tr.origin _ bad).1,?_⟩
  rintro loc k v bound rfl
  exact (tr.origin _ bad).2


end JPEG2000.Spec.Resources.DiagnosticTilePart
