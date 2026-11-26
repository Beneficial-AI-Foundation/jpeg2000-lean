import Spec.Resources.DiagnosticMarker
import Spec.Resources.GeometryInit

/-!
# Geometry admission diagnostics (Plan.md §§3–5, 7, S3)

T.800 A.5.1, A.6.1–2 and B.2–B.9. The SIZ grid and each tile-component
contribution are bounded before the corresponding limit checks. Both stages
construct zero message expressions. Their typed errors use marker offset 2.
-/

namespace JPEG2000.Spec.Resources.DiagnosticGeometry

open JPEG2000.Bytes JPEG2000.Marker JPEG2000.TilePart JPEG2000.Header
open DiagnosticCost
open Tier2Equiv (bind_ok)

private abbrev loc := Location.atOffset .marker 2

private theorem ceil_le (a b : Nat) : cdiv a b ≤ a := by
  cases b with
  | zero => simp [cdiv]
  | succ d =>
    apply Nat.le_of_lt_succ
    apply (Nat.div_lt_iff_lt_mul (Nat.succ_pos d)).2
    rw [Nat.succ_mul, Nat.mul_succ]
    omega

/-- Zero-event trace of the five SIZ guards, including image area, tile count
and the tile-component product, at the return of the main-header reader. -/
def geometryTrace {L : Limits} {r t : Reader} {mh : MainHeader}
    (read : parseMainHeader L r = .ok (mh,t)) : Trace (2^78) (checkGeometry L mh) 0 := by
  have hc : mh.siz.csiz ≤ 16384 := by
    obtain ⟨_,_,_,_,_,_,_,_,_,_,hc,_⟩ := DiagnosticMarker.main_source read
    exact hc
  let s := mh.siz
  have x := s.xsiz.toNat_lt
  have y := s.ysiz.toNat_lt
  have w : (imageRect s).width ≤ 2^32 := by unfold imageRect Rect.width; dsimp; omega
  have h : (imageRect s).height ≤ 2^32 := by unfold imageRect Rect.height; dsimp; omega
  have area := Nat.mul_le_mul w h
  have nx : numTilesX s ≤ 2^32 := Nat.le_trans (ceil_le ..) (by omega)
  have ny : numTilesY s ≤ 2^32 := Nat.le_trans (ceil_le ..) (by omega)
  have nt : numTiles s ≤ 2^64 := (Nat.mul_le_mul nx ny : _ ≤ 2^32 * 2^32)
  have prod : numTiles s * s.csiz ≤ 2^78 := (Nat.mul_le_mul nt hc : _ ≤ 2^64 * 16384)
  have off : loc.offset.getD 0 ≤ 2^78 := by decide
  unfold checkGeometry
  apply bindTrace (checkedTrace L loc _ _ off (Nat.le_trans w (by decide)))
  intro _ _
  apply bindTrace (checkedTrace L loc _ _ off (Nat.le_trans h (by decide)))
  intro _ _
  apply bindTrace (checkedTrace L loc _ _ off (Nat.le_trans area (by decide)))
  intro _ _
  apply bindTrace (checkedTrace L loc _ _ off (Nat.le_trans nt (by decide)))
  intro _ _
  exact checkedTrace L loc _ _ off prod

private theorem signedCeil_le {a b : Int} (hb : 0 ≤ b) (hab : a ≤ b) (k : Nat) :
    cdivPowI a k ≤ b := by
  have pos : 0 < (2:Int)^k := Int.pow_pos (by decide)
  have mul := Int.mul_le_mul_of_nonneg_left (show 1 ≤ (2:Int)^k by omega) hb
  rw [Int.mul_one] at mul
  have := (Int.le_ediv_iff_mul_le (a := -b) (b := -a) pos).2 (by rw [Int.neg_mul]; omega)
  unfold cdivPowI
  omega

private theorem bandAxis (a b n o e : Nat) : bandBlocks1 a b n o e ≤ b := by
  let off : Int := if o = 0 ∨ n = 0 then 0 else (2:Int)^(n-1)
  have pos : 0 < (2:Int)^n := Int.pow_pos (by decide)
  have small : 0 ≤ off ∧ off < (2:Int)^n := by
    unfold off
    split
    · exact ⟨by decide,pos⟩
    · rename_i hn
      cases n with
      | zero => simp at hn
      | succ n =>
        simp only [Nat.add_sub_cancel, Int.pow_succ]
        have h : 0 < (2:Int)^n := Int.pow_pos (by decide)
        omega
  have base : 0 ≤ cdivPowI ((a:Int)-off) n := by
    have := (Int.ediv_lt_iff_lt_mul (a := -((a:Int)-off)) (b := 1) pos).2 (by
      rw [Int.one_mul]; omega)
    unfold cdivPowI
    omega
  have top := signedCeil_le (b := (b:Int)) (Int.natCast_nonneg _) (show (b:Int)-off ≤ b by omega) n
  have ceil := signedCeil_le (Int.natCast_nonneg _) top e
  have floor := Int.ediv_nonneg (b := (2:Int)^e) base (Int.le_of_lt (Int.pow_pos (by decide)))
  change (if cdivPowI ((b:Int)-off) n ≤ cdivPowI ((a:Int)-off) n then 0 else (cdivPowI (cdivPowI ((b:Int)-off) n) e -
    cdivPowI ((a:Int)-off) n / (2:Int)^e).toNat) ≤ b
  split <;> omega

private theorem resolution_counts (tc : Rect) (p : CompParams) (r : Nat) :
    numCodeBlocks tc p r ≤ 3*(tc.x1*tc.y1) ∧
    numPrecincts (resRect tc p.levels r) (p.precincts.getD r Precinct.default) ≤ tc.x1*tc.y1 := by
  have band (n ox oy ex ey : Nat) :=
    Nat.mul_le_mul (bandAxis tc.x0 tc.x1 n ox ex) (bandAxis tc.y0 tc.y1 n oy ey)
  constructor
  · unfold numCodeBlocks
    split
    · dsimp only
      have := band p.levels 0 0 (p.effCbWidthExp r) (p.effCbHeightExp r)
      omega
    · dsimp only
      have b := band (p.levels-r+1) 1 0 (p.effCbWidthExp r) (p.effCbHeightExp r)
      have c := band (p.levels-r+1) 0 1 (p.effCbWidthExp r) (p.effCbHeightExp r)
      have d := band (p.levels-r+1) 1 1 (p.effCbWidthExp r) (p.effCbHeightExp r)
      omega
  · unfold numPrecincts
    split
    · exact Nat.zero_le _
    · apply Nat.mul_le_mul <;> apply Nat.le_trans (Nat.sub_le ..) <;>
        exact Nat.le_trans (ceil_le ..) (ceil_le ..)

/-- The actual component fold, including all bands and resolutions of the
component currently being admitted. The SIZ endpoints bound both coordinates
even for a tile using the main-header defaults. -/
theorem component_counts (s : SIZ) (t i : Nat) (p : CompParams) :
    let tc := compRect (tileRect s t) (s.components.getD i default)
    let counts := tileCompCounts tc p
    counts.1 ≤ (p.levels+1)*(3*2^64) ∧ counts.2 ≤ (p.levels+1)*2^64 := by
  let tc := compRect (tileRect s t) (s.components.getD i default)
  have hx : tc.x1 ≤ 2^32 := Nat.le_trans (ceil_le ..) (Nat.le_trans (Nat.min_le_right ..) (Nat.le_of_lt s.xsiz.toNat_lt))
  have hy : tc.y1 ≤ 2^32 := Nat.le_trans (ceil_le ..) (Nat.le_trans (Nat.min_le_right ..) (Nat.le_of_lt s.ysiz.toNat_lt))
  have area : tc.x1*tc.y1 ≤ 2^64 := (Nat.mul_le_mul hx hy : _ ≤ 2^32 * 2^32)
  let step := fun (cb, pr) r => (cb + numCodeBlocks tc p r,
      pr + numPrecincts (resRect tc p.levels r) (p.precincts.getD r Precinct.default))
  have fold (rs : List Nat) (a : Nat × Nat) :
      (rs.foldl step a).1 ≤ a.1 + rs.length*(3*2^64) ∧
      (rs.foldl step a).2 ≤ a.2 + rs.length*2^64 := by
    induction rs generalizing a with
    | nil => simp
    | cons r rs ih =>
      have ⟨blocks,precincts⟩ := resolution_counts tc p r
      have ⟨bc,pc⟩ := ih (step a r)
      simp only [List.foldl_cons,List.length_cons,Nat.succ_mul]
      dsimp only [step] at bc pc ⊢
      constructor <;> omega
  simpa only [tc,step,tileCompCounts,List.length_range,Nat.zero_add] using fold (List.range (p.levels+1)) (0,0)

/-- Upper bound on the three totals *before* admission. At most 256 wire
resolutions contribute one precinct grid and at most three bands each. A
packet contribution multiplies the precinct count by a 16-bit layer count. -/
def scalarCap (L : Limits) : Nat :=
  max (L.maxCodeBlocks + 256*(3*2^64))
    (max (L.maxPrecincts + 256*2^64) (L.maxPackets + 65535*(256*2^64)))

private def WireCoding (c : Coding) : Prop :=
  c.layers ≤ 65535 ∧ ∀ p ∈ c.comps, p.levels ≤ 255

private theorem mergedLevel {pos roi : Nat} {s : CodingStyle} {q : QCD} {p : CompParams}
    (made : mkComp pos s q roi = .ok p) : p.levels ≤ 255 := by
  unfold mkComp at made
  obtain ⟨_,_,made⟩ := bind_ok made
  cases made
  exact Nat.le_of_lt_succ s.levels.toNat_lt

private theorem defaultWire {mh : MainHeader} {c : Coding} (made : mainCoding mh = .ok c) :
    WireCoding c := by
  unfold mainCoding at made
  obtain ⟨_,_,made⟩ := bind_ok made
  obtain ⟨xs,hm,made⟩ := bind_ok made
  obtain ⟨_,_,made⟩ := bind_ok made
  obtain ⟨_,_,made⟩ := bind_ok made
  cases made
  exact ⟨Nat.le_of_lt_succ mh.cod.layers.toNat_lt,
    HeaderWF.arrayMapM_mem _ _ _ (fun _ _ _ h => mergedLevel h) xs hm⟩

private theorem tileWire {mh : MainHeader} {ov : Overrides} {d c : Coding} {t : Tile}
    (hd : WireCoding d) (made : tileCoding mh ov d t = .ok c) : WireCoding c := by
  unfold tileCoding at made
  dsimp only at made
  obtain ⟨_,_,made⟩ := bind_ok made
  split at made
  · obtain ⟨_,hs,made⟩ := bind_ok made
    obtain ⟨_,_,made⟩ := bind_ok made
    cases made; cases hs
    exact ⟨Nat.le_of_lt_succ (UInt16.toNat_lt _),hd.2⟩
  · obtain ⟨_,_,made⟩ := bind_ok made
    obtain ⟨xs,hm,made⟩ := bind_ok made
    obtain ⟨_,hs,made⟩ := bind_ok made
    obtain ⟨_,_,made⟩ := bind_ok made
    cases made; cases hs
    exact ⟨Nat.le_of_lt_succ (UInt16.toNat_lt _),
      HeaderWF.arrayMapM_mem _ _ _ (fun _ _ _ h => mergedLevel h) xs hm⟩

/-- All three running totals after adding component `i` of tile `t`, before
any of its three production checks. -/
def nextTotals (s : SIZ) (t : Nat) (c : Coding) (i : Nat) (a : Totals) : Totals :=
  let (cb,pr) := tileCompCounts (compRect (tileRect s t) (s.components.getD i default))
    (c.comps.getD i default)
  ⟨a.codeBlocks+cb,a.precincts+pr,a.packets+c.layers*pr⟩

private theorem next_bounds {L : Limits} {a : Totals} (prev : TotalsWithin L a)
    (s : SIZ) (t i : Nat) {c : Coding} (wire : WireCoding c) :
    let z := nextTotals s t c i a
    z.codeBlocks ≤ scalarCap L ∧ z.precincts ≤ scalarCap L ∧ z.packets ≤ scalarCap L := by
  let p := c.comps.getD i default
  have nl : p.levels ≤ 255 := by
    unfold p
    rw [Array.getD_eq_getD_getElem?]
    cases h : c.comps[i]? with
    | none => decide
    | some v => exact wire.2 v (Array.mem_of_getElem? h)
  obtain ⟨cb,pr⟩ := component_counts s t i p
  have n : p.levels+1 ≤ 256 := by omega
  have b := Nat.le_trans cb (Nat.mul_le_mul_right (3*2^64) n)
  have q := Nat.le_trans pr (Nat.mul_le_mul_right (2^64) n)
  have pk := Nat.mul_le_mul wire.1 q
  exact ⟨Nat.le_trans (Nat.add_le_add prev.1 b) (Nat.le_max_left ..),
    Nat.le_trans (Nat.add_le_add prev.2.1 q) (Nat.le_trans (Nat.le_max_left ..) (Nat.le_max_right ..)),
    Nat.le_trans (Nat.add_le_add prev.2.2 pk) (Nat.le_trans (Nat.le_max_right ..) (Nat.le_max_right ..))⟩

/-- Ordered component callback of `addTile`. Its input includes the admitted
totals of all preceding tiles and the preceding components of this tile. -/
def componentStep (L : Limits) (s : SIZ) (t : Nat) (c : Coding) (i : Nat) (a : Totals) :
    Except Error (ForInStep Totals) := do
  let z := nextTotals s t c i a
  L.check loc .codeBlocks z.codeBlocks
  L.check loc .precincts z.precincts
  L.check loc .packets z.packets
  pure (.yield z)

/-- The tile table cursor advances only on an index match. Both a later
entry and an exhausted table select the main-header defaults. -/
def codingHere (tiles : Array TileParams) (t cursor : Nat) : Option Coding :=
  match tiles[cursor]? with
  | some tp => if tp.index = t then some tp.coding else none
  | none => none

/-- Outer callback of `checkWork`, including the default-coding path. -/
def tileStep (L : Limits) (s : SIZ) (d : Coding) (tiles : Array TileParams)
    (t : Nat) (a : Totals × Nat) : Except Error (ForInStep (Totals × Nat)) := do
  let here := codingHere tiles t a.2
  if here.isSome then
    let z ← addTile L s t (here.getD d) a.1
    pure (.yield (z,a.2+1))
  else
    let z ← addTile L s t (here.getD d) a.1
    pure (.yield (z,a.2))

private theorem tile_loop (L : Limits) (s : SIZ) (t : Nat) (c : Coding) (a : Totals) :
    addTile L s t c a = forIn (List.range' 0 s.csiz) a (componentStep L s t c) := by
  unfold addTile
  simp only [bind_pure,Std.Legacy.Range.forIn_eq_forIn_range']
  have hs : [:s.csiz].size = s.csiz := by simp [Std.Legacy.Range.size]
  rw [hs]
  rfl

private theorem grid_loop (L : Limits) (s : SIZ) (d : Coding) (tiles : Array TileParams) :
    checkWork L s d tiles = (do
      let a ← forIn (List.range' 0 (numTiles s)) (({} : Totals),0) (tileStep L s d tiles)
      pure a.1) := by
  unfold checkWork
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  have hs : [:(numTiles s)].size = numTiles s := by simp [Std.Legacy.Range.size]
  rw [hs]
  rfl

private theorem checked {L : Limits} {k n u} (h : L.check loc k n = .ok u) : n ≤ L.bound k :=
  (Limits.check_eq_ok_iff ..).1 h

private theorem component_pres {L s t c i a z} (ok : componentStep L s t c i a = .ok z) :
    TotalsWithin L z.value := by
  unfold componentStep at ok
  obtain ⟨_,b,ok⟩ := bind_ok ok
  obtain ⟨_,p,ok⟩ := bind_ok ok
  obtain ⟨_,k,ok⟩ := bind_ok ok
  cases ok
  exact ⟨checked b,checked p,checked k⟩

private theorem tile_pres {L s d tiles t a z} (prev : TotalsWithin L a.1)
    (ok : tileStep L s d tiles t a = .ok z) : TotalsWithin L z.value.1 := by
  simp only [tileStep] at ok
  split at ok <;> obtain ⟨_,h,ok⟩ := bind_ok ok <;> cases ok <;> exact addTile_within prev h

/-- The failing guard in production order. Earlier guards on this component
have already passed. The diagnostic keeps the exact value and original limit. -/
def Excess (L : Limits) (z : Totals) (e : Error) : Prop :=
  (L.maxCodeBlocks < z.codeBlocks ∧ e = .limitExceeded loc .codeBlocks z.codeBlocks L.maxCodeBlocks) ∨
  (z.codeBlocks ≤ L.maxCodeBlocks ∧ L.maxPrecincts < z.precincts ∧
    e = .limitExceeded loc .precincts z.precincts L.maxPrecincts) ∨
  (z.codeBlocks ≤ L.maxCodeBlocks ∧ z.precincts ≤ L.maxPrecincts ∧ L.maxPackets < z.packets ∧
    e = .limitExceeded loc .packets z.packets L.maxPackets)

private theorem component_failure {L s t c i a e} (bad : componentStep L s t c i a = .error e) :
    Excess L (nextTotals s t c i a) e := by
  let z := nextTotals s t c i a
  simp only [componentStep, ← show z = nextTotals s t c i a from rfl] at bad
  cases hb : L.check loc .codeBlocks z.codeBlocks with
  | error err =>
    rw [hb] at bad
    cases bad
    exact .inl ⟨(Limits.checkLe_eq_error hb).2,(Limits.checkLe_eq_error hb).1⟩
  | ok u =>
    rw [hb] at bad
    dsimp only [bind,Except.bind] at bad
    cases hp : L.check loc .precincts z.precincts with
    | error err =>
      rw [hp] at bad
      cases bad
      exact .inr (.inl ⟨checked hb,(Limits.checkLe_eq_error hp).2,(Limits.checkLe_eq_error hp).1⟩)
    | ok u =>
      rw [hp] at bad
      dsimp only [bind,Except.bind] at bad
      cases hk : L.check loc .packets z.packets <;> rw [hk] at bad <;> cases bad
      exact .inr (.inr ⟨checked hb,checked hp,(Limits.checkLe_eq_error hk).2,(Limits.checkLe_eq_error hk).1⟩)

/-- The prefix preceding a particular loop iteration returned its input state.
The split identifies the occurrence even when elements can repeat. -/
def AtStep {α β : Type} (xs : List α) (start : β) (f : α → β → Except Error (ForInStep β))
    (x : α) (b : β) : Prop :=
  ∃ seen rest, xs = seen ++ x :: rest ∧ forIn seen start f = .ok b

private theorem first_failure {α β : Type} {f : α → β → Except Error (ForInStep β)}
    (P : β → Prop) (pres : ∀ x a z, P a → f x a = .ok z → P z.value)
    {xs : List α} {a : β} {e : Error} (start : P a) (bad : forIn xs a f = .error e) :
    ∃ x b, AtStep xs a f x b ∧ P b ∧ f x b = .error e := by
  induction xs generalizing a with
  | nil => cases bad
  | cons x xs ih =>
    rw [List.forIn_cons] at bad
    cases h : f x a with
    | error err =>
      rw [h] at bad
      cases bad
      exact ⟨x,a,⟨[],xs,rfl,rfl⟩,start,h⟩
    | ok st =>
      rw [h] at bad
      cases st with
      | done => cases bad
      | yield b =>
        obtain ⟨y,c,⟨seen,rest,eq,reached⟩,pc,hy⟩ := ih (pres _ _ _ start h) bad
        exact ⟨y,c,⟨x::seen,rest,by simp [eq],by rw [List.forIn_cons,h]; exact reached⟩,pc,hy⟩

/-- A `checkWork` error identifies both admitted loop prefixes, the selected
coding, and the three counts computed at the failing component. -/
def WorkRefusal (L : Limits) (s : SIZ) (d : Coding) (tiles : Array TileParams) (e : Error) : Prop :=
  ∃ t state i prev,
    AtStep (List.range' 0 (numTiles s)) (({} : Totals),0) (tileStep L s d tiles) t state ∧
    let c := (codingHere tiles t state.2).getD d
    AtStep (List.range' 0 s.csiz) state.1 (componentStep L s t c) i prev ∧
    TotalsWithin L prev ∧
    let z := nextTotals s t c i prev
    z.codeBlocks ≤ scalarCap L ∧ z.precincts ≤ scalarCap L ∧ z.packets ≤ scalarCap L ∧ Excess L z e

private theorem selectedWire {d : Coding} {tiles : Array TileParams}
    (hd : WireCoding d) (ht : ∀ tp ∈ tiles, WireCoding tp.coding) (t cursor : Nat) :
    WireCoding ((codingHere tiles t cursor).getD d) := by
  unfold codingHere
  cases h : tiles[cursor]? with
  | none => exact hd
  | some tp =>
    dsimp only
    split
    · exact ht tp (Array.mem_of_getElem? h)
    · exact hd

private theorem work_failure {L s d tiles e} (hd : WireCoding d)
    (ht : ∀ tp ∈ tiles, WireCoding tp.coding) (bad : checkWork L s d tiles = .error e) :
    WorkRefusal L s d tiles e := by
  rw [grid_loop] at bad
  cases loop : forIn (List.range' 0 (numTiles s)) (({} : Totals),0) (tileStep L s d tiles) with
  | ok => rw [loop] at bad; cases bad
  | error err =>
    rw [loop] at bad
    cases bad
    obtain ⟨t,state,outer,prior,fail⟩ := first_failure (fun a => TotalsWithin L a.1)
      (fun _ _ _ prev ok => tile_pres prev ok) (by simp [TotalsWithin]) loop
    let c := (codingHere tiles t state.2).getD d
    have tile : addTile L s t c state.1 = .error e := by
      simp only [tileStep] at fail
      cases h : addTile L s t c state.1 <;> split at fail <;>
        simp only [c] at h <;> rw [h] at fail <;> cases fail <;> rfl
    rw [tile_loop] at tile
    obtain ⟨i,prev,inner,within,refused⟩ := first_failure (TotalsWithin L)
      (fun _ _ _ _ ok => component_pres ok) prior tile
    have ⟨blocks,precincts,packets⟩ := next_bounds within s t i (selectedWire hd ht t state.2)
    exact ⟨t,state,i,prev,outer,inner,within,blocks,precincts,packets,component_failure refused⟩

/-- Public byte prefix immediately preceding geometry admission, with an absolute
range reader for either a JP2 container or a raw codestream. -/
def geometryInput (L : Limits) (data : ByteArray) : Except Error (MainHeader × Reader) := do
  let c ← Box.parseFile L data
  let r ← rangeReader data ⟨c.codestream.start,c.codestream.len⟩
  parseMainHeader L r

/-- The tile-parameter map used by the header driver just before work admission. -/
def mergeTile (mh : MainHeader) (ov : Overrides) (d : Coding) (t : Tile) : Except Error TileParams := do
  let coding ← tileCoding mh ov d t
  let rect := tileRect mh.siz t.index
  return { index := t.index,rect,coding,tile := t,compRects := mh.siz.components.map (compRect rect) }

/-- Exact public prefix preceding `checkWork`, including pointer admission,
tile-part assembly, overrides, and the completed tile-parameter map. -/
def workInput (L : Limits) (data : ByteArray) : Except Error (MainHeader × Coding × Array TileParams) := do
  let (mh,r) ← geometryInput L data
  checkGeometry L mh
  let d ← mainCoding mh
  let _ ← parsePointers L mh data
  let ts ← parseTileParts L mh r
  let ov ← mkOverrides mh.endPos mh.siz.csiz mh.coc mh.qcc mh.rgn
  let tiles ← ts.mapM (mergeTile mh ov d)
  return (mh,d,tiles)

private theorem prefixWire {L data mh d tiles} (ok : workInput L data = .ok (mh,d,tiles)) :
    checkGeometry L mh = .ok () ∧ WireCoding d ∧ ∀ tp ∈ tiles, WireCoding tp.coding := by
  unfold workInput at ok
  obtain ⟨⟨_,_⟩,_,ok⟩ := bind_ok ok
  obtain ⟨⟨⟩,grid,ok⟩ := bind_ok ok
  obtain ⟨_,made,ok⟩ := bind_ok ok
  obtain ⟨⟨_,_⟩,_,ok⟩ := bind_ok ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  obtain ⟨_,mapped,ok⟩ := bind_ok ok
  cases ok
  refine ⟨grid,defaultWire made,HeaderWF.arrayMapM_mem _ _ _ ?_ _ mapped⟩
  intro _ _ _ hp
  obtain ⟨_,hc,hp⟩ := bind_ok hp
  cases hp
  exact tileWire (defaultWire made) hc

private def scanTrace {α β : Type} {cap : Nat} (P : β → Prop)
    (f : α → β → Except Error (ForInStep β))
    (step : ∀ x a, P a → Trace cap (f x a) 0)
    (pres : ∀ x a z, P a → f x a = .ok z → P z.value) :
    (xs : List α) → (a : β) → P a → Trace cap (forIn xs a f) 0
  | [],a,_ => doneTrace a
  | x::xs,a,h => by
    rw [List.forIn_cons]
    apply bindTrace (step x a h)
    rintro (b|b) got
    · exact doneTrace b
    · exact scanTrace P f step pres xs b (pres x a (.yield b) h got)

private def componentTrace {L s t c i a} (wire : WireCoding c) (prev : TotalsWithin L a) :
    Trace (scalarCap L) (componentStep L s t c i a) 0 := by
  obtain ⟨b,p,k⟩ := next_bounds prev s t i wire
  have off : loc.offset.getD 0 ≤ scalarCap L := by
    change 2 ≤ scalarCap L
    unfold scalarCap
    omega
  unfold componentStep
  apply bindTrace (checkedTrace L loc _ _ off b)
  intro _ _
  apply bindTrace (checkedTrace L loc _ _ off p)
  intro _ _
  apply bindTrace (checkedTrace L loc _ _ off k)
  intro _ _
  exact doneTrace _

/-- The public work prefix suffices on both outcomes. Both loops compose the
ordered zero-event limit checks for each visited component, stopping at the
first refusal. Its pre-admission count and offset 2 remain in the error. -/
def workTrace {L data mh d tiles} (ok : workInput L data = .ok (mh,d,tiles)) :
    Trace (scalarCap L) (checkWork L mh.siz d tiles) 0 := by
  have facts := prefixWire ok
  rw [grid_loop]
  refine bindTrace (scanTrace (fun a => TotalsWithin L a.1) _ ?_
    (fun _ _ _ prev h => tile_pres prev h) _ _ (by simp [TotalsWithin])) (fun _ _ => doneTrace _)
  intro t state prior
  let c := (codingHere tiles t state.2).getD d
  have wire := selectedWire facts.2.1 facts.2.2 t state.2
  have tile : Trace (scalarCap L) (addTile L mh.siz t c state.1) 0 := by
    rw [tile_loop]
    exact scanTrace (TotalsWithin L) _ (fun _ _ prev => componentTrace wire prev)
      (fun _ _ _ _ h => component_pres h) _ _ prior
  simp only [tileStep]
  split <;> exact bindTrace tile (fun _ _ => doneTrace _)

/-- All three candidate totals are already bounded at every reached component,
including when all three guards succeed or the first guard stops the traversal. -/
theorem reached_totals {L data mh d tiles} (ok : workInput L data = .ok (mh,d,tiles))
    {t state i prev}
    (outer : AtStep (List.range' 0 (numTiles mh.siz)) (({} : Totals),0)
      (tileStep L mh.siz d tiles) t state)
    (inner : AtStep (List.range' 0 mh.siz.csiz) state.1
      (componentStep L mh.siz t ((codingHere tiles t state.2).getD d)) i prev) :
    let z := nextTotals mh.siz t ((codingHere tiles t state.2).getD d) i prev
    TotalsWithin L prev ∧ z.codeBlocks ≤ scalarCap L ∧ z.precincts ≤ scalarCap L ∧
      z.packets ≤ scalarCap L := by
  obtain ⟨xs,_,_,first⟩ := outer
  obtain ⟨ys,_,_,second⟩ := inner
  obtain ⟨_,hd,ht⟩ := prefixWire ok
  have prior := Tier2Equiv.forIn_inv (fun a => TotalsWithin L a.1) _
    (fun _ _ _ hp h => tile_pres hp h) xs _ _ (by simp [TotalsWithin]) first
  have within := Tier2Equiv.forIn_inv (TotalsWithin L) _ (fun _ _ _ _ h => component_pres h)
    ys _ _ prior second
  exact ⟨within,next_bounds within mh.siz t i (selectedWire hd ht t state.2)⟩

/-- SIZ checks in production order. The two image sides share a limit kind. -/
def geometryGuards (s : SIZ) : List (LimitKind × Nat) :=
  let r := imageRect s
  [(.imageSide,r.width),(.imageSide,r.height),(.imageArea,r.width*r.height),
    (.tiles,numTiles s),(.codeBlocks,numTiles s*s.csiz)]

private def firstExcess (L : Limits) (xs : List (LimitKind × Nat)) :=
  xs.find? fun (k,v) => decide (L.bound k < v)

private theorem geometry_result (L : Limits) (mh : MainHeader) :
    checkGeometry L mh = match firstExcess L (geometryGuards mh.siz) with
      | none => .ok ()
      | some (k,v) => .error (.limitExceeded loc k v (L.bound k)) := by
  let report := fun xs => match firstExcess L xs with
    | none => Except.ok ()
    | some (k,v) => Except.error (Error.limitExceeded loc k v (L.bound k))
  have cons (k v xs) : report ((k,v)::xs) = (L.check loc k v >>= fun _ => report xs) := by
    by_cases h : v ≤ L.bound k <;>
      simp [report,firstExcess,Limits.check,Limits.checkLe,← Nat.not_le,h,bind,Except.bind]
  change checkGeometry L mh = report (geometryGuards mh.siz)
  simp only [geometryGuards,cons,checkGeometry,
    show (fun _ : Unit => report []) = (pure : Unit → Except Error Unit) from rfl,bind_pure]

private theorem bits_mono {a b : Nat} (h : a ≤ b) : bits a ≤ bits b := by
  cases a with
  | zero => simp [bits,Nat.log2_zero]
  | succ a =>
    exact Nat.succ_le_succ ((Nat.le_log2 (by omega : b ≠ 0)).2
      (Nat.le_trans (Nat.log2_self_le (Nat.succ_ne_zero a)) h))

/-- The first failed SIZ guard returns the same error from the header and both
public decoders. The typed record keeps its computed value without formatting
either that value or the caller's ceiling. -/
theorem geometry_refusal {L data mh r e} (ok : geometryInput L data = .ok (mh,r))
    (bad : checkGeometry L mh = .error e) (opts : DecodeOptions)
    (admitted : L.check Decode.loc .decompLevels opts.reduce = .ok ()) :
    Header.parse L data = .error e ∧ decodeCodestream L data opts.reduce = .error e ∧
    JPEG2000.decode L data opts = .error e ∧
    ∃ k v, (geometryGuards mh.siz).find? (fun (k,v) => decide (L.bound k < v)) = some (k,v) ∧
      e = .limitExceeded (.atOffset .marker 2) k v (L.bound k) ∧ v ≤ 2^78 ∧
      storedPayload false e ≤ 6 + bits 2 + bits (2^78) := by
  unfold geometryInput at ok
  obtain ⟨_,box,ok⟩ := bind_ok ok
  obtain ⟨_,range,read⟩ := bind_ok ok
  have hp : Header.parse L data = .error e := by
    simp only [Header.parse,box,parseCodestreamIn,range,read,bad,bind,Except.bind]
  have raw : decodeCodestream L data opts.reduce = .error e := by
    simp only [decodeCodestream,admitted,hp,bind,Except.bind]
  refine ⟨hp,raw,by simp only [JPEG2000.decode,raw,bind,Except.bind],?_⟩
  have origin := (geometryTrace read).origin e bad
  rw [geometry_result] at bad
  cases he : firstExcess L (geometryGuards mh.siz) with
  | none => rw [he] at bad; cases bad
  | some pair =>
    obtain ⟨k,v⟩ := pair
    rw [he] at bad
    cases bad
    exact ⟨k,v,he,rfl,origin.2,Nat.add_le_add_left (bits_mono origin.2) _⟩

/-- The late refusal propagates through the same byte prefix to both public
decoders. Both admitted prefixes locate the failing tile-component, and the
stored record pays the binary width of the refused count. -/
theorem work_refusal {L data mh d tiles e} (ok : workInput L data = .ok (mh,d,tiles))
    (bad : checkWork L mh.siz d tiles = .error e) (opts : DecodeOptions)
    (admitted : L.check Decode.loc .decompLevels opts.reduce = .ok ()) :
    Header.parse L data = .error e ∧ decodeCodestream L data opts.reduce = .error e ∧
    JPEG2000.decode L data opts = .error e ∧ WorkRefusal L mh.siz d tiles e ∧
      storedPayload false e ≤ 6 + bits 2 + bits (scalarCap L) := by
  obtain ⟨_,hd,ht⟩ := prefixWire ok
  have site := work_failure hd ht bad
  have hp : Header.parse L data = .error e := by
    unfold workInput at ok
    obtain ⟨⟨_,_⟩,geo,ok⟩ := bind_ok ok
    obtain ⟨⟨⟩,grid,ok⟩ := bind_ok ok
    obtain ⟨_,made,ok⟩ := bind_ok ok
    obtain ⟨⟨_,_⟩,ptr,ok⟩ := bind_ok ok
    obtain ⟨_,ts,ok⟩ := bind_ok ok
    obtain ⟨_,ov,ok⟩ := bind_ok ok
    obtain ⟨_,mapped,ok⟩ := bind_ok ok
    cases ok
    unfold geometryInput at geo
    obtain ⟨_,box,geo⟩ := bind_ok geo
    obtain ⟨_,range,main⟩ := bind_ok geo
    simp only [Header.parse,box,parseCodestreamIn,range,main,grid,made,ptr,ts,ov,bind,Except.bind]
    unfold mergeTile at mapped
    simp only [bind,Except.bind] at mapped
    rw [mapped]
    simp only [bad]
  have raw : decodeCodestream L data opts.reduce = .error e := by
    simp only [decodeCodestream,admitted,hp,bind,Except.bind]
  refine ⟨hp,raw,by simp only [JPEG2000.decode,raw,bind,Except.bind],site,?_⟩
  obtain ⟨_,_,_,_,_,_,_,b,p,k,ex⟩ := site
  rcases ex with ⟨_,rfl⟩ | ⟨_,_,rfl⟩ | ⟨_,_,_,rfl⟩
  · exact Nat.add_le_add_left (bits_mono b) _
  · exact Nat.add_le_add_left (bits_mono p) _
  · exact Nat.add_le_add_left (bits_mono k) _

/-- On either outcome the component-visit meter includes the current component
and the public arithmetic meter includes its resolution and band folds. The
diagnostic event list has no entries to charge alongside these meters. -/
theorem work_cost {L data mh d tiles} (ok : workInput L data = .ok (mh,d,tiles)) :
    (workTrace ok).messages = [] ∧
    (HeaderWork.chargedCheckWork L mh.siz d tiles).1 = checkWork L mh.siz d tiles ∧
    (HeaderWork.chargedCheckWork L mh.siz d tiles).2 ≤ L.maxCodeBlocks ∧
    (GeometryInit.parseWork L data).result = Header.parse L data ∧
    (GeometryInit.parseWork L data).work ≤ GeometryInit.headerBudget L := by
  have ⟨eq,bound⟩ := HeaderWork.checkWork_visits d tiles (prefixWire ok).1
  exact ⟨List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero (workTrace ok).countBound),
    eq,bound,GeometryInit.parse_geometry_work L data⟩

end JPEG2000.Spec.Resources.DiagnosticGeometry
