import Spec.Resources.HeaderWork

/-!
# Effective layer and progression-volume counts

Plan.md §§3–5, 7 (S3), T.800 A.6.1 and A.6.6. Carry the parser's POC
counter through tile-part grouping and COD/POC selection. The counter in a
tile-part header starts at the cumulative count on entry.
-/

namespace JPEG2000.Spec.Resources.ProgressionFields

open JPEG2000.Bytes JPEG2000.Marker JPEG2000.TilePart JPEG2000.Header JPEG2000.Progression
open Tier2Equiv (bind_ok)

private def total {α : Type} (f : α → Nat) (xs : Array α) := (xs.toList.map f).sum

private def mainGood (L : Limits) (a : Acc) : Prop :=
  total (fun p => p.entries.size) a.poc = a.pocEntries ∧ a.pocEntries ≤ L.maxPocEntries

private theorem main_step {L : Limits} {a z : Acc} {c m b} (ha : mainGood L a)
    (ok : addSegment L c a m b = .ok z) : mainGood L z := by
  unfold addSegment at ok
  generalize (m == Code.COD) = k0 at ok
  generalize (m == Code.COC) = k1 at ok
  generalize (m == Code.QCD) = k2 at ok
  generalize (m == Code.QCC) = k3 at ok
  generalize (m == Code.RGN) = k4 at ok
  generalize (m == Code.POC) = k5 at ok
  generalize (m == Code.COM) = k6 at ok
  generalize (m == Code.CRG) = k7 at ok
  generalize (m == Code.CAP) = k8 at ok
  generalize (m == Code.TLM || m == Code.PLM || m == Code.PPM) = k9 at ok
  cases k0 <;> simp only [Bool.false_eq_true,↓reduceIte] at ok
  case true =>
    repeat' obtain ⟨_,_,ok⟩ := bind_ok ok
    cases ok
    exact ha
  cases k1 <;> simp only [Bool.false_eq_true,↓reduceIte] at ok
  case true =>
    repeat' obtain ⟨_,_,ok⟩ := bind_ok ok
    cases ok
    exact ha
  cases k2 <;> simp only [Bool.false_eq_true,↓reduceIte] at ok
  case true =>
    repeat' obtain ⟨_,_,ok⟩ := bind_ok ok
    cases ok
    exact ha
  cases k3 <;> simp only [Bool.false_eq_true,↓reduceIte] at ok
  case true =>
    repeat' obtain ⟨_,_,ok⟩ := bind_ok ok
    cases ok
    exact ha
  cases k4 <;> simp only [Bool.false_eq_true,↓reduceIte] at ok
  case true =>
    repeat' obtain ⟨_,_,ok⟩ := bind_ok ok
    cases ok
    exact ha
  cases k5 <;> simp only [Bool.false_eq_true,↓reduceIte] at ok
  case true =>
    repeat' obtain ⟨_,_,ok⟩ := bind_ok ok
    cases ok
    obtain ⟨eq,_⟩ := ha
    exact ⟨by simpa [total] using eq, (Limits.check_eq_ok_iff ..).1 (by assumption)⟩
  cases k6 <;> simp only [Bool.false_eq_true,↓reduceIte] at ok
  case true =>
    repeat' obtain ⟨_,_,ok⟩ := bind_ok ok
    cases ok
    exact ha
  cases k7 <;> simp only [Bool.false_eq_true,↓reduceIte] at ok
  case true =>
    repeat' obtain ⟨_,_,ok⟩ := bind_ok ok
    cases ok
    exact ha
  cases k8 <;> simp only [Bool.false_eq_true,↓reduceIte] at ok
  case true =>
    repeat' obtain ⟨_,_,ok⟩ := bind_ok ok
    cases ok
    exact ha
  cases k9 <;> simp only [Bool.false_eq_true,↓reduceIte] at ok
  case true =>
    repeat' obtain ⟨_,_,ok⟩ := bind_ok ok
    cases ok
    exact ha
  cases ok; exact ha

private theorem main_loop {L : Limits} {a z : Acc} {c f r t} (ha : mainGood L a)
    (ok : segmentLoop L c f a r = .ok (z,t)) : mainGood L z := by
  induction f generalizing a r with
  | zero => cases ok
  | succ f ih =>
    simp only [segmentLoop] at ok
    repeat' split at ok <;> try contradiction
    all_goals first | (cases ok; exact ha) | (apply ih _ ok; first | exact ha | (apply main_step _ (by assumption); exact ha))

private theorem main_count {L : Limits} {r t : Reader} {mh : MainHeader}
    (ok : parseMainHeader L r = .ok (mh,t)) : total (fun p => p.entries.size) mh.poc ≤ L.maxPocEntries := by
  unfold parseMainHeader at ok
  iterate 4 obtain ⟨_,_,ok⟩ := bind_ok ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  obtain ⟨⟨a,t'⟩,loop,ok⟩ := bind_ok ok
  cases hc : a.cod <;> simp only [hc] at ok <;> try contradiction
  cases hq : a.qcd <;> simp only [hq] at ok <;> try contradiction
  cases ok
  obtain ⟨eq,cap⟩ := main_loop (by exact ⟨rfl,Nat.zero_le _⟩) loop
  exact eq ▸ cap

private def entries : TileSegment → Nat
  | .poc p => p.entries.size
  | _ => 0

private def tpGood (L : Limits) (before : Nat) (a : TPAcc) : Prop :=
  before + total entries a.segments = a.pocEntries ∧ a.pocEntries ≤ L.maxPocEntries

private theorem tp_step {L : Limits} {a z : TPAcc} {c first ppm m b start} (ha : tpGood L start a)
    (ok : addTileSegment L c first ppm a m b = .ok z) : tpGood L start z := by
  unfold addTileSegment at ok
  repeat' first | (split at ok <;> try contradiction) | (obtain ⟨_,_,ok⟩ := bind_ok ok)
  all_goals cases ok
  all_goals simp only [tpGood,total,Array.toList_push,List.map_append,List.map_singleton,
    List.sum_append,List.sum_singleton,entries,Nat.add_zero] at ha ⊢
  all_goals first | exact ha | exact ⟨by omega,(Limits.check_eq_ok_iff ..).1 (by assumption)⟩

private theorem tp_loop {L : Limits} {a z : TPAcc} {c first ppm f r t start} (ha : tpGood L start a)
    (ok : headerLoop L c first ppm f a r = .ok (z,t)) : tpGood L start z := by
  induction f generalizing a r with
  | zero => cases ok
  | succ f ih =>
    simp only [headerLoop] at ok
    repeat' split at ok <;> try contradiction
    all_goals first | (cases ok; exact ha) | (apply ih _ ok; first | exact ha | (apply tp_step _ (by assumption); exact ha))

private def partEntries (p : TilePartHeader) := total entries p.segments

private def stateGood (L : Limits) (s : State) : Prop :=
  (∀ ps ∈ s.parts, total partEntries ps ≤ s.pocEntries) ∧ s.pocEntries ≤ L.maxPocEntries

private theorem part_step {c : Ctx} {s z : State} {r t} (hs : stateGood c.limits s)
    (ok : readTilePart c s r = .ok (z,t)) : stateGood c.limits z := by
  unfold readTilePart at ok
  iterate 9 obtain ⟨_,_,ok⟩ := bind_ok ok
  dsimp only at ok
  split at ok <;> split at ok <;> try contradiction
  all_goals
    simp only [pure_bind] at ok
    obtain ⟨_,_,ok⟩ := bind_ok ok
    obtain ⟨⟨a,b⟩,loop,ok⟩ := bind_ok ok
    cases ok
    obtain ⟨eq,hc⟩ := tp_loop (by exact ⟨Nat.add_zero _,hs.2⟩) loop
    change s.pocEntries + total entries a.segments = a.pocEntries at eq
    refine ⟨?_,hc⟩
    intro ps hp
    obtain ⟨j,hj,rfl⟩ := Array.mem_iff_getElem.mp hp
    simp only [Array.getElem_modify]
    split
    · have prev := hs.1 _ (Array.getElem_mem (xs := s.parts) (i := j) (by simpa using hj))
      dsimp only [total,partEntries] at eq prev ⊢
      simp only [Array.toList_push,List.map_append,List.map_singleton,List.sum_append,List.sum_singleton]
      dsimp only [partEntries,total]
      omega
    · have prev := hs.1 _ (Array.getElem_mem (xs := s.parts) (i := j) (by simpa using hj))
      exact Nat.le_trans prev (by omega)

private theorem part_loop {c : Ctx} {s z : State} {r f} (hs : stateGood c.limits s)
    (ok : tilePartLoop c f s r = .ok z) : stateGood c.limits z := by
  induction f generalizing s r with
  | zero => cases ok
  | succ f ih =>
    simp only [tilePartLoop] at ok
    repeat' split at ok <;> try contradiction
    all_goals first | (cases ok; exact hs) | exact ih (part_step hs (by assumption)) ok

private theorem assembled {L : Limits} {n i packets parts} {acc out : Array Tile} {corr}
    (each : ∀ ps ∈ parts, total partEntries ps ≤ L.maxPocEntries)
    (ha : ∀ t ∈ acc, total partEntries t.parts ≤ L.maxPocEntries)
    (ok : assembleTiles L corr parts n i packets acc = .ok out) :
    ∀ t ∈ out, total partEntries t.parts ≤ L.maxPocEntries := by
  induction n generalizing i packets acc with
  | zero => cases ok; exact ha
  | succ n ih =>
    simp only [assembleTiles] at ok
    split at ok
    · exact ih ha ok
    split at ok <;> try contradiction
    rename_i tile ht
    split at ok <;> try contradiction
    apply ih _ ok
    intro t hm
    rcases Array.mem_push.mp hm with h | rfl
    · exact ha _ h
    · have hp : t.parts = parts[i]?.getD #[] := by
        unfold assembleTile at ht
        dsimp only at ht
        split at ht <;> split at ht <;> try contradiction
        all_goals repeat' obtain ⟨_,_,ht⟩ := bind_ok ht
        all_goals cases ht; rfl
      rw [hp]
      cases get : parts[i]? with
      | none => exact Nat.zero_le _
      | some p => exact each _ (Array.mem_of_getElem? get)

private theorem fold_size {α : Type} {β : Type} (xs : List α) (get : α → Array β) (a : Array β) :
    (xs.foldl (fun a x => a ++ get x) a).size = a.size+(xs.map (fun x => (get x).size)).sum := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih => simp [ih,Nat.add_assoc]

private theorem fold_count {α : Type} (xs : List α) (f : α → Nat) (n : Nat) :
    xs.foldl (fun a x => a+f x) n = n+(xs.map f).sum := by
  induction xs generalizing n with
  | nil => simp
  | cons x xs ih => simp [ih,Nat.add_assoc]

private theorem parts_count {L : Limits} {mh : MainHeader} {r ts} (main : total (fun p => p.entries.size) mh.poc ≤ L.maxPocEntries)
    (ok : parseTileParts L mh r = .ok ts) : ∀ t ∈ ts, total partEntries t.parts ≤ L.maxPocEntries := by
  unfold parseTileParts at ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  obtain ⟨s,loop,ok⟩ := bind_ok ok
  have hs := part_loop (by
    constructor
    · intro ps h
      simp only [Array.mem_replicate] at h
      obtain ⟨_,rfl⟩ := h; exact Nat.zero_le _
    · simpa [← Array.foldl_toList,fold_count,total] using main) loop
  exact assembled (fun ps hp => Nat.le_trans (hs.1 ps hp) hs.2) (by simp) ok


private theorem tile_count (t : Tile) : (tileSegs t).poc.size = total partEntries t.parts := by
  let step (acc : TileSegs) (s : TileSegment) : TileSegs :=
    match s with
    | .cod c => { acc with cod := some c }
    | .qcd q => { acc with qcd := some q }
    | .coc c => { acc with coc := acc.coc.push c }
    | .qcc q => { acc with qcc := acc.qcc.push q }
    | .rgn r => { acc with rgn := acc.rgn.push r }
    | .poc p => { acc with poc := acc.poc ++ p.entries }
    | _ => acc
  have inner (xs : List TileSegment) (a : TileSegs) :
      (xs.foldl step a).poc.size = a.poc.size+(xs.map entries).sum := by
    induction xs generalizing a with
    | nil => simp
    | cons s xs ih => rw [List.foldl_cons,ih]; cases s <;> simp [step,entries,Nat.add_assoc]
  have outer (xs : List TilePartHeader) (a : TileSegs) :
      (xs.foldl (fun v p => p.segments.foldl step v) a).poc.size = a.poc.size+(xs.map partEntries).sum := by
    induction xs generalizing a with
    | nil => simp
    | cons p xs ih =>
      rw [List.foldl_cons,ih,← Array.foldl_toList,inner]
      simp [partEntries,total,Nat.add_assoc]
  unfold tileSegs
  rw [← Array.foldl_toList]
  apply Eq.trans (b := (t.parts.toList.foldl (fun v p => p.segments.foldl step v) ({} : TileSegs)).poc.size)
  · congr 3
  · simpa only [total,Array.size_empty,Nat.zero_add] using outer t.parts.toList {}

private theorem cod_layers {L : Limits} {d : COD} (hd : HeaderWF.SegmentRead L (.cod d)) :
    d.layers.toNat ≤ L.maxLayers := by
  obtain ⟨_, h⟩ := hd
  unfold parseCOD at h
  obtain ⟨⟨_,_⟩,_,h⟩ := bind_ok h
  obtain ⟨_,_,h⟩ := bind_ok h
  obtain ⟨⟨_,_⟩,_,h⟩ := bind_ok h
  dsimp only at h
  split at h <;> try contradiction
  simp only [pure_bind] at h
  obtain ⟨⟨_,_⟩,_,h⟩ := bind_ok h
  obtain ⟨_,_,h⟩ := bind_ok h
  obtain ⟨_,check,h⟩ := bind_ok h
  obtain ⟨⟨_,_⟩,_,h⟩ := bind_ok h
  split at h <;> try contradiction
  obtain ⟨⟨_,_⟩,_,h⟩ := bind_ok h
  obtain ⟨_,_,h⟩ := bind_ok h
  cases h; exact (Limits.check_eq_ok_iff ..).1 check

private def Bounded (L : Limits) (c : Coding) := c.layers ≤ L.maxLayers ∧ c.poc.size ≤ L.maxPocEntries

private theorem codings {L : Limits} {data : ByteArray} {h : Header} (ok : Header.parse L data = .ok h) :
    Bounded L h.defaults ∧ ∀ tp ∈ h.tiles, Bounded L tp.coding := by
  unfold Header.parse at ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  unfold parseCodestreamIn at ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  obtain ⟨⟨mh,_⟩,hm,ok⟩ := bind_ok ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  obtain ⟨d,md,ok⟩ := bind_ok ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  obtain ⟨tiles,tileReads,ok⟩ := bind_ok ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  obtain ⟨tps,hmap,ok⟩ := bind_ok ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  cases ok
  have main := main_count hm
  have mainLayers := cod_layers ((HeaderWF.parseMainHeader_fields hm).2.cod _ rfl)
  have hd : Bounded L d := by
    unfold mainCoding at md
    repeat' obtain ⟨_,_,md⟩ := bind_ok md
    cases md
    exact ⟨mainLayers, by simpa [← Array.foldl_toList,fold_size,total] using main⟩
  refine ⟨hd, Tier2WF.arrayMapM_mem _ _ _ ?_ _ hmap⟩
  intro t mem tp ht
  obtain ⟨c,hc,ht⟩ := bind_ok ht
  cases ht
  have tile := parts_count main tileReads t mem
  have pc : (tileSegs t).poc.size ≤ L.maxPocEntries := tile_count t ▸ tile
  have source := HeaderWF.parseTileParts_fields tileReads t mem
  have layers : ((tileSegs t).cod.getD mh.cod).layers.toNat ≤ L.maxLayers := by
    unfold tileSegs
    rw [← Array.foldl_toList]
    let P := fun (s : TileSegs) => (s.cod.getD mh.cod).layers.toNat ≤ L.maxLayers
    refine HeaderWF.list_foldl_inv P _ _ ?_ _ mainLayers
    intro p hp acc ha
    rw [← Array.foldl_toList]
    refine HeaderWF.list_foldl_inv P _ _ ?_ _ ha
    intro s hs acc ha
    have read := source p (Array.mem_def.2 hp) s (Array.mem_def.2 hs)
    cases s <;> first | exact ha | exact cod_layers read
  have selected : (if (tileSegs t).poc.isEmpty then d.poc else (tileSegs t).poc).size ≤ L.maxPocEntries := by
    split <;> first | exact hd.2 | exact pc
  unfold tileCoding at hc
  dsimp only at hc
  obtain ⟨_,_,hc⟩ := bind_ok hc
  split at hc
  · obtain ⟨_,r, hc⟩ := bind_ok hc
    obtain ⟨_,_,hc⟩ := bind_ok hc
    cases hc; cases r; exact ⟨layers,selected⟩
  · obtain ⟨_,_,hc⟩ := bind_ok hc
    obtain ⟨_,_,hc⟩ := bind_ok hc
    obtain ⟨_,r,hc⟩ := bind_ok hc
    obtain ⟨_,_,hc⟩ := bind_ok hc
    cases hc; cases r; exact ⟨layers,selected⟩

/-- Effective layout layers and POC table size at the actual parsed tile, including
the default coding selected for an uncovered tile index. -/
theorem parsed_limits {L : Limits} {data : ByteArray} {h : Header} {t g c}
    (parsed : Header.parse L data = .ok h) (layout : Layout.ofHeader h t = .ok (g,c)) :
    g.layers ≤ L.maxLayers ∧ c.poc.size ≤ L.maxPocEntries := by
  have ⟨defaults,tiles⟩ := codings parsed
  unfold Layout.ofHeader at layout
  dsimp only at layout
  split at layout <;> try contradiction
  obtain ⟨_,_,layout⟩ := bind_ok layout
  cases layout
  split
  · exact tiles _ (Array.mem_of_find?_eq_some (by assumption))
  · exact defaults

end JPEG2000.Spec.Resources.ProgressionFields
