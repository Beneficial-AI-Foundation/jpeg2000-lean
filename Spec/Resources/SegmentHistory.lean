import Spec.Resources.PacketLocalWork
import Spec.Resources.AssemblyCost
import Spec.RoundTrip.PrecinctShape
import Spec.ColorResources.Layout

/-!
# Segment histories at the packet-to-coefficient boundary

Plan.md §§3–5 and 7 (S3), T.800 B.9–B.12. Offsets in a packet body
initially refer to the gathered tile. A single retained range can intersect
multiple source parts. Every translation visits the whole part table.
-/

namespace JPEG2000.Spec.Resources.SegmentHistory

open JPEG2000.Header JPEG2000.Bytes JPEG2000.TilePart JPEG2000.Tier2.Geometry
open JPEG2000.Tier2.Packet JPEG2000.Tier2.Headers JPEG2000.Progression
open PacketLocalWork PacketTraversal AssemblyCost

/-- Tile-buffer start, original input offset and byte count for each source part. -/
abbrev Parts := List (Nat × Nat × Nat)

/-- Translate a tile-buffer range and count the source triples examined. -/
def translateVisits (r : ByteRange) : Parts → Array ByteRange → Array ByteRange × Nat
  | [], acc => (acc, 0)
  | (bs, io, n) :: ps, acc =>
    let lo := max r.offset bs
    let hi := min r.stop (bs+n)
    let next := if lo < hi then pushRange acc ⟨io+(lo-bs), hi-lo⟩ else acc
    let tail := translateVisits r ps next
    (tail.1, 1+tail.2)

/-- Exact charge for translation, including triples with no intersection.
Each intersection introduces at most one additional descriptor. -/
theorem translate_visits (r : ByteRange) (ps : Parts) (acc : Array ByteRange) :
    let run := translateVisits r ps acc
    run.1 = translate r ps acc ∧ run.2 = ps.length ∧ run.1.size ≤ acc.size + run.2 := by
  induction ps generalizing acc with
  | nil => exact ⟨rfl,rfl,by simp [translateVisits]⟩
  | cons x xs ih =>
    obtain ⟨bs,io,n⟩ := x
    simp only [translateVisits,translate,List.length_cons]
    split
    · let lo := max r.offset bs
      let piece : ByteRange := ⟨io+(lo-bs), min r.stop (bs+n)-lo⟩
      obtain ⟨eq,visits,sz⟩ := ih (pushRange acc piece)
      have growth (a : ByteRange) : (pushRange acc a).size ≤ acc.size+1 := by
        unfold pushRange
        (repeat' split) <;> simp [Array.size_pop]
      have bound := Nat.le_trans sz (Nat.add_le_add_right (growth _) _)
      dsimp only [piece,lo] at visits bound
      exact ⟨eq,by omega,by omega⟩
    · obtain ⟨eq,visits,sz⟩ := ih acc
      exact ⟨eq,by omega,by omega⟩

private def outputSeg (ps : Parts) (s : Segment) : Segment :=
  { s with ranges := s.ranges.foldl (fun acc r => translate r ps acc) #[] }

private def outputBlock (ps : Parts) (cb : CodeBlock) : CodeBlock :=
  { cb with segments := cb.segments.map (outputSeg ps) }

private theorem segment_ranges (ps : Parts) (s : Segment) :
    (outputSeg ps s).ranges.size ≤ s.ranges.size * ps.length := by
  have fold (xs : List ByteRange) (a : Array ByteRange) :
      (xs.foldl (fun acc r => translate r ps acc) a).size ≤ a.size + xs.length*ps.length := by
    induction xs generalizing a with
    | nil => simp
    | cons x xs ih =>
      obtain ⟨eq,count,growth⟩ := translate_visits x ps a
      rw [eq,count] at growth
      have rest := ih (translate x ps a)
      simp only [List.foldl_cons,List.length_cons,Nat.succ_mul]
      omega
  simpa only [outputSeg,Array.foldl_toList,Array.length_toList,Array.size_empty,Nat.zero_add]
    using fold s.ranges.toList #[]

private theorem block_ranges (ps : Parts) (cb : CodeBlock) :
    rangeCount (outputBlock ps cb) ≤ rangeCount cb * ps.length := by
  change HeaderWork.blockRanges (cb.segments.map (outputSeg ps)).toList ≤ _
  rw [Array.toList_map]
  unfold rangeCount HeaderWork.blockRanges
  induction cb.segments.toList with
  | nil => simp
  | cons s ss ih =>
    simp only [List.map_cons,List.sum_cons,Nat.add_mul]
    exact Nat.add_le_add (segment_ranges ps s) ih

private theorem member_cost {α : Type} (f : α → Nat) {xs : Array α} {x : α} (member : x ∈ xs) :
    f x ≤ (xs.toList.map f).sum := by
  have mem := Array.mem_toList_iff.mpr member
  generalize xs.toList = ys at mem ⊢
  induction ys with
  | nil => cases mem
  | cons y ys ih =>
    rcases List.mem_cons.mp mem with rfl | tail
    · simp
    · exact Nat.le_add_left_of_le (ih tail)

private theorem state_records (s : LoopState) (j : Nat) :
    retained (s.precs.getD j default).bands ≤ tileRecords s := by
  rw [Array.getD_eq_getD_getElem?]
  cases h : s.precs[j]? with
  | none => exact Nat.zero_le _
  | some st => exact member_cost (fun p => retained p.bands) (Array.mem_of_getElem? h)

private theorem block_records (st : PrecState) {b : BandState} {cb : CodeBlock}
    (band : b ∈ st.bands) (block : cb ∈ b.blocks) :
    segmentSlots cb.segments ≤ retained st.bands := by
  let slots := fun (x : CodeBlock) => segmentSlots x.segments
  exact Nat.le_trans (member_cost slots block)
    (member_cost (fun a : BandState => (a.blocks.toList.map slots).sum) band)

/-- A block selected from the completed production store inherits its tile's
packet count. Translation preserves its segment count and can multiply its
range count by the actual number of source parts. -/
theorem completed_history {L : Limits} {h : Header} {data : ByteArray} {tp : TileParams}
    {hs : Option HeaderStream} {pb : Nat} {out : TileCodeBlocks}
    (parsed : Header.parse L data = .ok h) (ok : decodeWithStream L h data tp hs pb = .ok out) :
    out.packets ≤ L.maxPackets ∧ ∀ i r, ∀ p ∈ (selected (some out) i).getD r #[],
      ∀ b ∈ p.bands, ∀ cb ∈ b.blocks,
        cb.segments.size ≤ out.packets * recordGrowth L ∧
        rangeCount cb ≤ (out.packets * recordGrowth L) * tp.tile.parts.size := by
  obtain ⟨s,parts,spans,len,seq,cap,records,output⟩ := completed_store parsed ok
  rw [seq] at records cap
  refine ⟨cap,?_⟩
  intro i r p hp b hb cb hc
  change p ∈ (out.comps.getD i #[]).getD r #[] at hp
  rw [output] at hp
  obtain ⟨ys,hys,hp⟩ := Tier2WF.mem_getD hp
  obtain ⟨zs,hzs,hys⟩ := Tier2WF.mem_getD hys
  obtain ⟨si,_,rfl⟩ := Array.mem_map.mp hzs
  obtain ⟨⟨start,n⟩,_,rfl⟩ := Array.mem_map.mp hys
  obtain ⟨k,_,rfl⟩ := Array.mem_map.mp hp
  obtain ⟨bs,hbs,rfl⟩ := Array.mem_map.mp hb
  obtain ⟨orig,horig,rfl⟩ := Array.mem_map.mp hc
  have slots := Nat.le_trans (block_records _ hbs horig) (Nat.le_trans (state_records s (start+k)) records)
  change orig.segments.size + rangeCount orig ≤ _ at slots
  change (orig.segments.map _).size ≤ _ ∧ rangeCount (outputBlock parts orig) ≤ _
  rw [Array.size_map,← len]
  exact ⟨by omega,Nat.le_trans (block_ranges parts orig) (Nat.mul_le_mul_right _ (by omega))⟩

private def Geometry (L : Limits) (a : Store) : Prop :=
  ∀ r, (a.getD r #[]).size ≤ L.maxPrecincts ∧ ∀ p ∈ a.getD r #[],
    p.bands.size ≤ 3 ∧ ∀ b ∈ p.bands, b.blocks.size ≤ L.maxCodeBlocks

private theorem initialized_shape {L : Limits} {tc : TileCompGeom} {r k res pg st}
    (hr : resolution L tc r = .ok res) (hp : precinct L res k = .ok pg)
    (hi : PrecState.init L tc.params r pg = .ok st) :
    (Tier2WF.pshape st).size ≤ 3 ∧ ∀ b ∈ Tier2WF.pshape st, b.2.size ≤ L.maxCodeBlocks := by
  obtain ⟨_,nb,blocks⟩ := HeaderWork.precinct_geometry hr hp
  unfold PrecState.init at hi
  obtain ⟨bs,hm,hi⟩ := Tier2Equiv.bind_ok hi
  cases hi
  simp only [Tier2WF.pshape,Array.size_map]
  refine ⟨Nat.le_trans (Nat.le_of_eq (ColorResources.channel_map_size hm)) nb,?_⟩
  intro b hb
  obtain ⟨band,mem,rfl⟩ := Array.mem_map.mp hb
  apply Tier2WF.arrayMapM_mem (fun b : BandState => (Tier2WF.bshape b).2.size ≤ L.maxCodeBlocks)
    _ _ _ _ hm band mem
  intro geom hg b read
  obtain ⟨_,_,read⟩ := Tier2Equiv.bind_ok read
  obtain ⟨_,_,read⟩ := Tier2Equiv.bind_ok read
  cases read
  simpa [Tier2WF.bshape] using blocks geom hg

private theorem raw_geometry {L : Limits} {h : Header} {data : ByteArray} {tp : TileParams}
    {hs : Option ByteArray} {pb : Nat} {out : TileCodeBlocks}
    (ok : decodeTilePacketsWith L h data tp hs pb = .ok out) (i : Nat) :
    Geometry L (selected (some out) i) := by
  unfold decodeTilePacketsWith at ok
  obtain ⟨⟨g,c⟩,_,ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨_,_,ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨⟨precs,base,spans⟩,init,ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨⟨buf,parts⟩,_,ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨s,run,ok⟩ := Tier2Equiv.bind_ok ok
  cases ok
  have shapes := Tier2WF.forPackets_pres
    (fun s : LoopState => s.precs.map Tier2WF.pshape = precs.map Tier2WF.pshape)
    g c.progression c.poc _ (fun _ _ _ before step =>
      (Tier2WF.fastStep_pres (L := L) (sop := c.sop) (eph := c.eph) (same := hs.isNone)
        (base := base) (pb := pb) step).trans before) _ s rfl run
  obtain ⟨_,outer,inner⟩ := RoundTrip.initPrecincts_shape init
  intro r
  dsimp only [selected,Option.map,Option.getD]
  rw [Tier2WF.getD_map_arr _ _ _ #[] (by simp), Tier2WF.getD_map_arr _ _ _ (0,0) (by simp)]
  by_cases ci : i < g.numComps
  · by_cases ri : r ≤ g.levels i
    · obtain ⟨res,hr,_,lookup,states⟩ := RoundTrip.initPrecincts_geometry init ci ri
      rw [Array.getD_eq_getD_getElem?,lookup]
      simp only [Option.getD_some,Array.size_map,Array.size_range,Array.mem_map,Array.mem_range]
      refine ⟨?_,?_⟩
      · by_cases pos : 0 < res.numPrecincts
        · obtain ⟨_,_,hp,_,_⟩ := states 0 pos
          exact (HeaderWork.precinct_geometry hr hp).1
        · omega
      · intro p ⟨k,hk,eq⟩
        subst p
        obtain ⟨pg,st,hp,hi,lookup⟩ := states k hk
        have eq := congrArg (fun a => a[((base.getD i #[]).getD r 0)+k]?) shapes
        simp only [Array.getElem?_map,lookup,Option.map_some] at eq
        generalize ((base.getD i #[]).getD r 0)+k = j at eq ⊢
        cases actual : s.precs[j]? with
        | none => simp [actual] at eq
        | some st' =>
          have same : Tier2WF.pshape st' = Tier2WF.pshape st := by simpa [actual] using eq
          obtain ⟨nb,blocks⟩ := initialized_shape hr hp hi
          rw [← same] at nb blocks
          simp only [Array.getD_eq_getD_getElem?,actual,Option.getD_some,PrecState.out,Array.size_map,
            Array.mem_map]
          refine ⟨by simpa [Tier2WF.pshape] using nb,?_⟩
          rintro b ⟨bs,hbs,rfl⟩
          simpa [Tier2WF.bshape] using blocks _ (Array.mem_map_of_mem hbs)
    · have outside : (spans.getD i #[])[r]? = none := Array.getElem?_eq_none (by
        rw [(inner i ci).2]; omega)
      rw [Array.getD_eq_getD_getElem?,outside]
      simp
  · have outside : spans[i]? = none := Array.getElem?_eq_none (by omega)
    simp [Array.getD_eq_getD_getElem?,outside]

private theorem stream_raw {L : Limits} {h : Header} {data : ByteArray} {tp : TileParams}
    {hs : Option HeaderStream} {pb : Nat} {out : TileCodeBlocks}
    (ok : decodeWithStream L h data tp hs pb = .ok out) :
    decodeTilePacketsWith L h data tp (hs.map (·.bytes)) pb = .ok out := by
  unfold decodeWithStream at ok
  obtain ⟨_,rd,ok⟩ := Tier2Equiv.bind_ok ok
  cases hs with
  | none => cases ok; exact rd
  | some b => dsimp only at ok; split at ok <;> cases ok; exact rd

/-- Number of pre-translation segment and range descriptors admitted per tile. -/
def segmentLimit (L : Limits) := L.maxPackets * recordGrowth L

/-- Range descriptors per output block, counting every possible source-part split. -/
def rangeLimit (L : Limits) := segmentLimit L * L.maxTilePartsPerTile

/-- All five assembly bounds for the component of the actual parsed packet store. -/
theorem store_bounds {L : Limits} {h : Header} {data : ByteArray} {tp : TileParams}
    {hs : Option HeaderStream} {pb : Nat} {out : TileCodeBlocks}
    (parsed : Header.parse L data = .ok h) (member : tp ∈ h.tiles)
    (ok : decodeWithStream L h data tp hs pb = .ok out) (i : Nat) :
    StoreBounds (selected (some out) i) L.maxPrecincts 3 L.maxCodeBlocks (segmentLimit L) (rangeLimit L) := by
  obtain ⟨count,hist⟩ := completed_history parsed ok
  have seq := Nat.mul_le_mul_right (recordGrowth L) count
  have parts := (HeaderWork.parse_tile_storage parsed tp member).1
  intro r
  obtain ⟨prec,bands⟩ := raw_geometry (stream_raw ok) i r
  refine ⟨prec,?_⟩
  intro p hp
  obtain ⟨nb,blocks⟩ := bands p hp
  refine ⟨nb,?_⟩
  intro b hb
  refine ⟨blocks b hb,?_⟩
  intro cb hc
  obtain ⟨ns,nk⟩ := hist i r p hp b hb cb hc
  exact ⟨Nat.le_trans ns seq,Nat.le_trans nk (Nat.mul_le_mul seq parts)⟩

/-- The packet-store selection inside the public tile loop, using its incoming
tile cursor, PPM index and coding-pass count. -/
def packetStore (L : Limits) (h : Header) (data : ByteArray) (idx : Array (Array Nat))
    (t j pb : Nat) : Except Error (Option TileCodeBlocks) :=
  match presentAt h t j with
  | none => pure none
  | some tp => do
    let hs ← headerStreamAt h data tp (idx.getD j #[])
    let out ← decodeWithStream L h data tp hs pb
    pure (some out)

private theorem present_mem {h : Header} {t j : Nat} {tp : TileParams}
    (found : presentAt h t j = some tp) : tp ∈ h.tiles := by
  unfold presentAt at found
  split at found <;> try contradiction
  split at found <;> cases found
  exact Array.mem_of_getElem? (by assumption)

/-- Uniform bounds at reconstruction's actual optional-store lookup. An absent
tile has an empty component array at every index. -/
theorem selected_store_bounds {L : Limits} {h : Header} {data : ByteArray}
    {idx t j pb a} (parsed : Header.parse L data = .ok h)
    (ok : packetStore L h data idx t j pb = .ok a) (i : Nat) :
    StoreBounds (selected a i) L.maxPrecincts 3 L.maxCodeBlocks (segmentLimit L) (rangeLimit L) := by
  unfold packetStore at ok
  split at ok
  · cases ok; intro r; simp [selected]
  · rename_i tp found
    obtain ⟨hs,_,ok⟩ := Tier2Equiv.bind_ok ok
    obtain ⟨out,decoded,ok⟩ := Tier2Equiv.bind_ok ok
    cases ok
    exact store_bounds parsed (present_mem found) decoded i

/-- Cumulative byte writes for gathering the tile's part data, once, before
the packet loop. This count also covers a prefix ending in a gather error. -/
def tileCopies (h : Header) (data : ByteArray) (t j : Nat) : Nat :=
  match presentAt h t j with
  | none => 0
  | some tp => (HeaderWork.chargedTile data tp.tile.parts.toList (ByteArray.empty,#[])).2

/-- Tile-data byte-copy bound through a refusal, independent of whether packet
selection or coefficient assembly subsequently succeeds. -/
theorem tile_copies {L : Limits} {h : Header} {data : ByteArray}
    (parsed : Header.parse L data = .ok h) (t j : Nat) :
    tileCopies h data t j ≤ L.maxTilePartsPerTile * (data.size + L.maxTilePartsPerTile*data.size) := by
  unfold tileCopies
  split
  · exact Nat.zero_le _
  · rename_i tp hit
    have bound := (HeaderWork.parse_tile_storage parsed tp (present_mem hit)).1
    exact Nat.le_trans (HeaderWork.tileData_copy_charge data tp.tile).2.1
      (Nat.mul_le_mul bound (Nat.add_le_add_left (Nat.mul_le_mul_right _ bound) _))

/-- One component's assembly budget for the admitted tile, allowing the checked
compact traversal followed by the wide retry. -/
def componentLimit (L : Limits) (n : Nat) :=
  let m := L.maxDecompLevels
  let block := AssemblyCost.blockBudget n m (segmentLimit L) (rangeLimit L)
  5*L.maxWorkSamples + 2*((m+1)*(1 + L.maxPrecincts*(1 + 3*(1 + L.maxCodeBlocks*(1+block)))))

private theorem component_limit {L : Limits} {h : Header} {data : ByteArray}
    {idx t j pb a g coding} (parsed : Header.parse L data = .ok h)
    (ok : packetStore L h data idx t j pb = .ok a)
    (layout : Layout.ofHeader h t = .ok (g,coding)) (red : Nat) (i : Fin g.numComps)
    (admitted : Resources.tileCells g red ≤ L.maxWorkSamples) :
    (component L h data g coding a i red).1 = JPEG2000.TileDispatch.component L h data g coding a i red ∧
    (component L h data g coding a i red).2 ≤ componentLimit L data.size := by
  obtain ⟨eq,work⟩ := component_budget parsed layout a i red _ _ _ _ _
    (selected_store_bounds parsed ok i) admitted
  have limit := (WideHeaderBounds.parsed_component_bounds parsed layout i red).1.levels
  let nl := (g.comp i).params.levels - red
  have levels : nl ≤ L.maxDecompLevels := Nat.le_trans (Nat.sub_le ..) limit
  have block : blockBudget data.size nl (segmentLimit L) (rangeLimit L) ≤
      blockBudget data.size L.maxDecompLevels (segmentLimit L) (rangeLimit L) := by
    unfold AssemblyCost.blockBudget; omega
  have blocks := Nat.mul_le_mul_left L.maxCodeBlocks (Nat.add_le_add_left block 1)
  have bands := Nat.mul_le_mul_left 3 (Nat.add_le_add_left blocks 1)
  have precs := Nat.mul_le_mul_left L.maxPrecincts (Nat.add_le_add_left bands 1)
  have traversal := Nat.mul_le_mul (Nat.add_le_add_right levels 1) (Nat.add_le_add_left precs 1)
  exact ⟨eq, Nat.le_trans work (Nat.add_le_add_left (Nat.mul_le_mul_left 2 traversal) _)⟩

private theorem sum_cap {α : Type} (xs : List α) (f : α → Nat) (k : Nat)
    (h : ∀ x ∈ xs, f x ≤ k) : (xs.map f).sum ≤ xs.length*k := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have tail := ih (fun y hy => h y (by simp [hy]))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.succ_mul]; omega

/-- One tile gather plus assembly of all selected components at one invocation
of reconstruction. The component meter charges range validation, direct-path
selection, the two fragmented append folds, and compact/wide retries. Summing
the full set of nonnegative component charges covers every visited prefix. -/
theorem tile_assembly_work {L : Limits} {h : Header} {data : ByteArray}
    {idx t j pb a g coding} (parsed : Header.parse L data = .ok h)
    (ok : packetStore L h data idx t j pb = .ok a)
    (layout : Layout.ofHeader h t = .ok (g,coding)) (red : Nat)
    (admitted : Resources.tileCells g red ≤ L.maxWorkSamples) :
    (∀ i, (component L h data g coding a i red).1 = JPEG2000.TileDispatch.component L h data g coding a i red) ∧
    ∀ pre : List (Fin g.numComps), pre <+: List.finRange g.numComps →
      tileCopies h data t j + (pre.map (fun i => (component L h data g coding a i red).2)).sum ≤
      L.maxTilePartsPerTile*(data.size+L.maxTilePartsPerTile*data.size) +
        L.maxComponents*componentLimit L data.size := by
  refine ⟨fun i => (component_limit parsed ok layout red i admitted).1,?_⟩
  intro pre prefixOf
  have len : pre.length ≤ L.maxComponents := Nat.le_trans
    (by simpa using prefixOf.length_le) (HeaderWork.layout_budget parsed layout).1
  exact Nat.add_le_add (tile_copies parsed ..) (Nat.le_trans
    (sum_cap pre _ _ (fun i _ => (component_limit parsed ok layout red i admitted).2))
    (Nat.mul_le_mul_right _ len))

private theorem bind_ok {α β : Type} {x : Except Error α} {f : α → Except Error β} {z} :
    (x >>= f) = .ok z ↔ ∃ y, x = .ok y ∧ f y = .ok z := by
  cases x <;> simp [bind,Except.bind]

private theorem field_runs {lb : Nat} {ps : List Nat} {b : BitReader} {z}
    (ok : readLengths lb ps b = .ok z) : z.1.map Prod.fst = ps := by
  induction ps generalizing b z with
  | nil => cases ok; rfl
  | cons p ps ih =>
    simp only [readLengths,bind_ok] at ok
    obtain ⟨⟨_,_⟩,_,⟨_,_⟩,fields,ok⟩ := ok
    cases ok
    exact congrArg (p :: ·) (ih fields)

private theorem field_count {L : Limits} {cb : CodeBlock} {n b lb style z}
    (checked : L.check (locAt b.pos) .passesPerCodeBlock (cb.numPasses+n) = .ok ())
    (read : readLengths lb (segmentPasses style n cb.numPasses) b = .ok z) :
    z.1.length ≤ L.maxPassesPerCodeBlock := by
  have eq := field_runs read
  rw [Tier2Equiv.segmentPasses_eq] at eq
  have pos := Spec.Tier1.segmentPasses_pos (Spec.Tier1.Mode.ofStyle style) n cb.numPasses
  have len (xs : List Nat) (positive : ∀ a ∈ xs, 0 < a) : xs.length ≤ xs.sum := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
      have hx := positive x (by simp)
      have tail := ih (fun y hy => positive y (by simp [hy]))
      simp only [List.length_cons,List.sum_cons]; omega
  have hl := len _ pos
  rw [Spec.Tier1.segmentPasses_sum,← eq,List.length_map] at hl
  have cap : cb.numPasses+n ≤ L.maxPassesPerCodeBlock := (Limits.check_eq_ok_iff ..).1 checked
  omega

private theorem block_pieces {L : Limits} {style layer bi k bs br out}
    (ok : headerBlock L style layer bi k bs br = .ok out) :
    ∀ c, out.2.1 = some c → c.pieces.length ≤ L.maxPassesPerCodeBlock := by
  unfold headerBlock at ok
  cases hx : bs.blocks[k]? with
  | none => simp [hx] at ok
  | some cb =>
    cases prev : cb.included <;>
      simp only [hx,prev,Bool.false_eq_true,↓reduceIte,bind_ok,pure,Except.pure,Except.ok.injEq] at ok
    all_goals
      obtain ⟨⟨inc,src⟩,_,_,rfl,ok⟩ := ok
      cases inc
      · cases ok; intro c no; cases no
      · simp only [Bool.not_true,Bool.false_eq_true,↓reduceIte,bind_ok,Except.ok.injEq] at ok
        first
        | obtain ⟨⟨_,_,_⟩,_,_,rfl,⟨n,b⟩,_,⟨_,b'⟩,_,_,check,_,fields,ok⟩ := ok
        | obtain ⟨_,rfl,⟨n,b⟩,_,⟨_,b'⟩,_,_,check,_,fields,ok⟩ := ok
        cases ok
        rintro c eq; cases eq
        exact field_count check fields

private def TableBound (L : Limits) (n : Nat) (cs : Array Contribution) : Prop :=
  cs.size ≤ n ∧ ∀ c ∈ cs, c.pieces.length ≤ L.maxPassesPerCodeBlock

private theorem band_table {L : Limits} {style layer bi bs br z}
    (ok : headerBand L style layer bi bs br = .ok z) : TableBound L bs.blocks.size z.2.1 := by
  rw [Tier2Equiv.headerBand_eq] at ok
  obtain ⟨a,loop,ok⟩ := Tier2Equiv.bind_ok ok
  cases ok
  have inv := Tier2WF.forIn_range'_inv (fun i (s : BandState × BitReader × Array Contribution) =>
    TableBound L i s.2.2) _ ?_ _ 0 _ _ (by simp [TableBound]) loop
  · simpa using inv
  intro k s step inv run
  unfold Tier2Equiv.bandBody at run
  obtain ⟨⟨bs',opt,b'⟩,hd,run⟩ := Tier2Equiv.bind_ok run
  cases opt with
  | none => cases run; exact ⟨_,rfl,Nat.le_succ_of_le inv.1,inv.2⟩
  | some c =>
    cases run
    exact ⟨_,rfl,by simpa using Nat.add_le_add_right inv.1 1,
      fun x hx => (Array.mem_push.mp hx).elim (inv.2 x)
        (fun eq => eq ▸ block_pieces hd c rfl)⟩

private theorem header_table {L : Limits} {layer br st pre cs bits} {present : Bool}
    (good : st.bands.size ≤ 3 ∧ ∀ b ∈ st.bands, b.blocks.size ≤ L.maxCodeBlocks)
    (hd : (if present then headerBands L layer st br else pure (st,#[],br)) = .ok (pre,cs,bits)) :
    TableBound L (3*L.maxCodeBlocks) cs := by
  cases present
  · cases hd; simp [TableBound]
  · rw [ite_eq_left rfl,Tier2Equiv.headerBands_eq] at hd
    obtain ⟨a,loop,hd⟩ := Tier2Equiv.bind_ok hd
    cases hd
    let inv := fun i (s : Array BandState × BitReader × Array Contribution) =>
      (∀ b ∈ s.1, b.blocks.size ≤ L.maxCodeBlocks) ∧ TableBound L (i*L.maxCodeBlocks) s.2.2
    have result := Tier2WF.forIn_range'_inv inv _ ?_ _ 0 _ _ ?_ loop
    · obtain ⟨n,each⟩ := result.2
      exact ⟨Nat.le_trans n (Nat.mul_le_mul_right _ (by simpa using good.1)),each⟩
    · intro i s step h run
      unfold Tier2Equiv.bandsBody at run
      split at run <;> try contradiction
      rename_i bs lookup
      obtain ⟨⟨bs',cs,b'⟩,hdr,run⟩ := Tier2Equiv.bind_ok run
      cases run
      obtain ⟨count,each⟩ := band_table hdr
      dsimp only at count
      have blocks := h.1 _ (Array.mem_of_getElem? lookup)
      have same := congrArg (fun x => x.2.size) (Tier2WF.headerBand_shape hdr)
      simp only [Tier2WF.bshape,Array.size_map] at same
      refine ⟨_,rfl,fun b hb => (Array.mem_or_eq_of_mem_setIfInBounds hb).elim (h.1 b)
        (fun e => by cases e; omega),?_,?_⟩
      · have old := h.2.1
        simp only [Array.size_append,Nat.succ_mul]
        omega
      · intro c hc
        exact (Array.mem_append.mp hc).elim (h.2.2 c) (each c)
    · exact ⟨good.2, by simp [TableBound]⟩

/-- The number of successful single-piece skips inside a contribution, even when
a later length refuses. Zero-byte skips still create a range on a successful read. -/
def skippedPieces (r : Reader) : List (Nat × Nat) → Nat
  | [] => 0
  | (_,n)::ps => if r.pos+n > r.stop then 0 else
    match r.skip n with
    | .error _ => 0
    | .ok b => 1 + skippedPieces b ps

private theorem skipped_count (r : Reader) (ps : List (Nat × Nat)) :
    skippedPieces r ps ≤ ps.length ∧
      ∀ z, takePieces r ps = .ok z → skippedPieces r ps = z.1.length := by
  induction ps generalizing r with
  | nil => exact ⟨Nat.le_refl 0,fun _ ok => by cases ok; rfl⟩
  | cons x ps ih =>
    obtain ⟨p,n⟩ := x
    simp only [skippedPieces,takePieces,List.length_cons]
    split
    · exact ⟨Nat.zero_le _,fun _ ok => by cases ok⟩
    · cases skip : r.skip n with
      | error e => exact ⟨Nat.zero_le _,fun _ ok => by cases ok⟩
      | ok b =>
        dsimp only
        refine ⟨by have := (ih b).1; omega,?_⟩
        intro z ok
        obtain ⟨⟨ls,t⟩,read,ok⟩ := Tier2Equiv.bind_ok (show (takePieces b ps >>= _) = .ok z from ok)
        cases ok
        simp [(ih b).2 _ read,Nat.add_comm]

/-- Completed contribution updates and successful single-piece skips in the real
body loop. A failed lookup or truncated length may have consumed pieces without
completing the enclosing update. -/
def bodyCounts : List Contribution → Array BandState × Reader → Nat × Nat
  | [], _ => (0,0)
  | c::cs, s =>
    let reads := skippedPieces s.2 c.pieces
    match Tier2Equiv.bodyBody c s with
    | .error _ => (0,reads)
    | .ok (.done _) => (1,reads)
    | .ok (.yield t) =>
      let rest := bodyCounts cs t
      (1+rest.1,reads+rest.2)

private theorem body_counts (xs : List Contribution) (s : Array BandState × Reader) :
    let m := bodyCounts xs s
    m.1 ≤ xs.length ∧ m.2 ≤ (xs.map (·.pieces.length)).sum ∧
    ∀ z, forIn xs s Tier2Equiv.bodyBody = .ok z →
      m = (xs.length,(xs.map (·.pieces.length)).sum) := by
  induction xs generalizing s with
  | nil => exact ⟨Nat.le_refl 0,Nat.le_refl 0,fun _ _ => rfl⟩
  | cons c cs ih =>
    have head := skipped_count s.2 c.pieces
    simp only [bodyCounts,List.map_cons,List.sum_cons,List.length_cons,List.forIn_cons]
    cases step : Tier2Equiv.bodyBody c s with
    | error => exact ⟨Nat.zero_le _,Nat.le_trans head.1 (Nat.le_add_right ..),fun _ bad => by cases bad⟩
    | ok y =>
      have good : ∃ t, y = .yield t ∧ skippedPieces s.2 c.pieces = c.pieces.length := by
        unfold Tier2Equiv.bodyBody at step
        obtain ⟨⟨rs,b⟩,read,step⟩ := Tier2Equiv.bind_ok step
        dsimp only at step
        split at step <;> try contradiction
        split at step <;> try contradiction
        cases step
        exact ⟨_,rfl,(head.2 _ read).trans (takePieces_extent _ _ read).1⟩
      obtain ⟨t,rfl,hn⟩ := good
      obtain ⟨count,pieces,exactly⟩ := ih t
      dsimp only
      refine ⟨by omega,by omega,?_⟩
      intro z run
      rw [exactly z run,hn]
      simp [Nat.add_comm]

/-- Arguments handed to the packet body reader after header processing. -/
abbrev BodyInput := PrecState × Array Contribution × Reader

/-- The packet prefix ending at the body loop's actual input, after SOP, the
present flag, block headers, byte alignment and EPH. -/
def packetBody (L : Limits) (c : Coding) (same : Bool) (s : LoopState)
    (p : PacketId) (st : PrecState) : Except Error BodyInput :=
  (if c.sop then readSop s.seq s.body else pure (false,s.body)) >>= fun (_,body) =>
  readBit (BitReader.ofReader (if same then body else s.hdr)) >>= fun (present,br) =>
  (if present then headerBands L p.layer st br else pure (st,#[],br)) >>= fun (pre,cs,bits) =>
  bits.align >>= fun aligned =>
  (if c.eph then readEph (aligned.toReader .tier2) else pure (aligned.toReader .tier2)) >>= fun head =>
  pure (pre,cs,if same then head else body)

private theorem branch_bind {α β : Type} (b : Prop) [Decidable b] (x y : Except Error α)
    (f : α → Except Error β) :
    (if b then x >>= f else y >>= f) = (if b then x else y) >>= f := by split <;> rfl

/-- Projecting the production packet result to its updated precinct and body
reader factors through the counted body's input, including the identical error
from a refusing header or a partially consumed body. -/
theorem packet_body_erase (L : Limits) (c : Coding) (same : Bool) (s : LoopState)
    (p : PacketId) (st : PrecState) :
    (decodePacket L c.sop c.eph s.seq p.layer st same s.hdr s.body >>= fun (t,_,_,r) => pure (t,r)) =
      (packetBody L c same s p st >>= fun (pre,cs,r) => readBody pre cs r) := by
  unfold decodePacket packetBody
  simp only [branch_bind,bind_assoc]
  congr 1
  funext ⟨found,body⟩
  congr 1
  funext ⟨present,br⟩
  congr 1
  funext ⟨pre,cs,bits⟩
  congr 1
  funext aligned
  congr 1
  funext head
  simp only [pure_bind]
  cases readBody pre cs (if same then head else body) <;> rfl

private def bodyAt (L : Limits) (c : Coding) (base : Array (Array Nat)) (same : Bool)
    (s : LoopState) (p : PacketId) : Option BodyInput :=
  match s.precs[(base.getD p.comp #[]).getD p.res 0 + p.prec]? with
  | none => none
  | some st => (packetBody L c same s p st).toOption

/-- A physical packet position and its body input, when the callback reaches
the body. The trace is proof instrumentation and also retains the refusing entry. -/
structure BodyEvent where
  /-- The physical position and production outcome. -/
  event : Position × PacketAction
  /-- Precinct, contribution table and body reader at entry to the body loop. -/
  body : Option (PrecState × Array Contribution × Reader)

/-- Counts through this body, including work before an error. -/
def BodyEvent.counts (e : BodyEvent) : Nat × Nat :=
  match e.body with
  | none => (0,0)
  | some (st,cs,r) => bodyCounts cs.toList (st.bands,r)

private def walkBodies (L : Limits) (c : Coding) (base : Array (Array Nat)) (same : Bool)
    (pb : Nat) : List Position → LoopState → List BodyEvent
  | [], _ => []
  | p::ps, s =>
    if p.previous.any (·.contains p.packet) then
      ⟨(p,.skip),none⟩ :: walkBodies L c base same pb ps s
    else
      let body := bodyAt L c base same s p.packet
      match packetStep L c base same pb s p.packet with
      | .error _ => [⟨(p,.rejected),body⟩]
      | .ok t => ⟨(p,.accepted (t.passes-s.passes)),body⟩ :: walkBodies L c base same pb ps t

private def shapeOK (L : Limits) (st : PrecState) : Prop :=
  (Tier2WF.pshape st).size ≤ 3 ∧ ∀ b ∈ Tier2WF.pshape st, b.2.size ≤ L.maxCodeBlocks

private theorem initial_shapes {L : Limits} {g ps base spans}
    (init : initPrecincts L g = .ok (ps,base,spans)) : ∀ st ∈ ps, shapeOK L st := by
  unfold initPrecincts at init
  simp only [Std.Legacy.Range.forIn_eq_forIn_range'] at init
  obtain ⟨s,loop,init⟩ := Tier2Equiv.bind_ok init
  cases init
  refine Tier2Equiv.forIn_inv (fun (a : Array PrecState × Array (Array Nat) × Array (Array (Nat × Nat)) × Nat) =>
    ∀ st ∈ a.1, shapeOK L st) _ ?_ _ _ _ (by simp) loop
  intro i a y inv run
  obtain ⟨z,middle,run⟩ := Tier2Equiv.bind_ok run
  cases run
  refine Tier2Equiv.forIn_inv (fun (a : Array PrecState × Nat × Array Nat × Array (Nat × Nat)) =>
    ∀ st ∈ a.1, shapeOK L st) _ ?_ _ _ _ inv middle
  intro r a y inv run
  obtain ⟨res,hr,run⟩ := Tier2Equiv.bind_ok run
  obtain ⟨_,_,run⟩ := Tier2Equiv.bind_ok run
  obtain ⟨z,inner,run⟩ := Tier2Equiv.bind_ok run
  cases run
  refine Tier2Equiv.forIn_inv (fun (a : Array PrecState × Nat) => ∀ st ∈ a.1, shapeOK L st)
    _ ?_ _ _ _ inv inner
  intro k a y inv run
  obtain ⟨pg,hp,run⟩ := Tier2Equiv.bind_ok run
  obtain ⟨_,_,run⟩ := Tier2Equiv.bind_ok run
  obtain ⟨st,hi,run⟩ := Tier2Equiv.bind_ok run
  cases run
  intro x hx
  exact (Array.mem_push.mp hx).elim (inv x) (fun eq => eq ▸ initialized_shape hr hp hi)

private theorem next_shapes {L : Limits} {c base same pb s p t}
    (all : ∀ st ∈ s.precs, shapeOK L st)
    (step : packetStep L c base same pb s p = .ok t) : ∀ st ∈ t.precs, shapeOK L st := by
  have eq := Tier2WF.fastStep_pres (L := L) (sop := c.sop) (eph := c.eph) (same := same)
    (base := base) (pb := pb) step
  intro st mem
  have image : Tier2WF.pshape st ∈ s.precs.map Tier2WF.pshape := eq ▸ Array.mem_map_of_mem mem
  obtain ⟨old,ho,he⟩ := Array.mem_map.mp image
  unfold shapeOK
  rw [← he]
  exact all old ho

private theorem reached_table {L : Limits} {c base same s p z}
    (all : ∀ st ∈ s.precs, shapeOK L st) (found : bodyAt L c base same s p = some z) :
    TableBound L (3*L.maxCodeBlocks) z.2.1 := by
  unfold bodyAt at found
  cases sel : s.precs[(base.getD p.comp #[]).getD p.res 0+p.prec]? with
  | none => rw [sel] at found; cases found
  | some st =>
    obtain ⟨nb,blocks⟩ := all st (Array.mem_of_getElem? sel)
    have geom : st.bands.size ≤ 3 ∧ ∀ b ∈ st.bands, b.blocks.size ≤ L.maxCodeBlocks :=
      ⟨by simpa [Tier2WF.pshape] using nb,fun b hb => by
        simpa [Tier2WF.bshape] using blocks _ (Array.mem_map_of_mem hb)⟩
    rw [sel] at found
    change (packetBody L c same s p st).toOption = some z at found
    cases rd : packetBody L c same s p st with
    | error => rw [rd] at found; cases found
    | ok input =>
      rw [rd] at found; cases found
      unfold packetBody at rd
      obtain ⟨⟨_,_⟩,_,⟨present,br⟩,_,⟨pre,cs,bits⟩,hd,_,_,_,_,rd⟩ := by
        simpa only [bind_ok] using rd
      cases rd
      exact header_table geom hd

private theorem accepted_body {L : Limits} {c base same pb s p t}
    (step : packetStep L c base same pb s p = .ok t) :
    ∃ st cs r st' r', bodyAt L c base same s p = some (st,cs,r) ∧
      readBody st cs r = .ok (st',r') := by
  obtain ⟨orig,st',info,hdr',r',sel,rd,_⟩ := packetStep_passes step
  obtain ⟨sop,b,present,br,st,cs,bits,al,hd,sopOk,bitOk,tableOk,alignOk,ephOk,bodyOk,_⟩ :=
    decodePacket_contributions rd
  refine ⟨st,cs,_,st',r',?_,bodyOk⟩
  simp only [bodyAt,sel,packetBody,sopOk,bitOk,tableOk,alignOk,ephOk,Tier2Equiv.ok_bind]
  rfl

private def CountedEvent (L : Limits) (e : BodyEvent) : Prop :=
  let b := 3*L.maxCodeBlocks
  e.counts.1 ≤ e.event.2.attempted.toNat*b ∧
  e.counts.2 ≤ e.event.2.attempted.toNat*(b*L.maxPassesPerCodeBlock) ∧
  ∀ n, e.event.2 = .accepted n → ∃ st cs r st' r', e.body = some (st,cs,r) ∧
    readBody st cs r = .ok (st',r') ∧ e.counts = (cs.size,(cs.toList.map (·.pieces.length)).sum)

private theorem counted_event {L : Limits} {e : BodyEvent} (entered : e.event.2.attempted = true)
    (bound : ∀ z, e.body = some z → TableBound L (3*L.maxCodeBlocks) z.2.1)
    (success : ∀ n, e.event.2 = .accepted n → ∃ st cs r st' r', e.body = some (st,cs,r) ∧
      readBody st cs r = .ok (st',r')) : CountedEvent L e := by
  simp only [CountedEvent,entered,Bool.toNat_true,Nat.one_mul]
  cases h : e.body with
  | none =>
    refine ⟨by simp [BodyEvent.counts,h],by simp [BodyEvent.counts,h],?_⟩
    intro n eq
    obtain ⟨_,_,_,_,_,bad,_⟩ := success n eq
    rw [h] at bad; cases bad
  | some z =>
    obtain ⟨st,cs,r⟩ := z
    obtain ⟨count,bound⟩ := bound _ h
    obtain ⟨visits,reads,full⟩ := body_counts cs.toList (st.bands,r)
    have pieceCap := sum_cap cs.toList (fun c => c.pieces.length) L.maxPassesPerCodeBlock
      (fun c hc => bound c (Array.mem_toList_iff.mp hc))
    simp only [Array.length_toList] at visits pieceCap count
    simp only [BodyEvent.counts,h]
    refine ⟨Nat.le_trans visits count,Nat.le_trans reads (Nat.le_trans pieceCap
      (Nat.mul_le_mul_right _ count)),?_⟩
    intro n eq
    obtain ⟨st0,cs0,r0,st',r',found,body⟩ := success n eq
    rw [h] at found; cases found
    refine ⟨st,cs,r,st',r',rfl,body,?_⟩
    rw [Tier2Equiv.readBody_eq] at body
    obtain ⟨_,run,_⟩ := Tier2Equiv.bind_ok body
    simpa using full _ run

private theorem walk_bodies {L : Limits} (c base same pb) (ps : List Position) (s : LoopState)
    (all : ∀ st ∈ s.precs, shapeOK L st) :
    let rows := walkBodies L c base same pb ps s
    rows.map BodyEvent.event = (PacketTraversal.walk (packetStep L c base same pb) ps s).1 ∧
    ∀ e ∈ rows, CountedEvent L e := by
  induction ps generalizing s with
  | nil => exact ⟨rfl,by simp [walkBodies]⟩
  | cons p ps ih =>
    simp only [walkBodies, PacketTraversal.walk]
    split
    · obtain ⟨erase,tail⟩ := ih s all
      exact ⟨congrArg (_ :: ·) erase,fun e he => (List.mem_cons.mp he).elim
        (fun eq => eq ▸ ⟨Nat.zero_le _,Nat.zero_le _,by intro _ bad; cases bad⟩) (tail e)⟩
    · cases step : packetStep L c base same pb s p.packet with
      | error err =>
        refine ⟨rfl,?_⟩
        rintro e he
        obtain rfl := List.mem_singleton.mp he
        exact counted_event rfl (fun _ hz => reached_table all hz) (by intro _ bad; cases bad)
      | ok t =>
        obtain ⟨erase,tail⟩ := ih t (next_shapes all step)
        refine ⟨congrArg (_ :: ·) erase,?_⟩
        intro e he
        rcases List.mem_cons.mp he with rfl | mem
        · exact counted_event rfl (fun _ hz => reached_table all hz) (fun _ _ => accepted_body step)
        · exact tail e mem

/-- Contribution histories on the production tile's physical packet prefix. Setup
errors produce an empty list, and the last entry can be a refusal. -/
def bodyHistory (L : Limits) (h : Header) (data : ByteArray) (tp : TileParams)
    (hs : Option HeaderStream) (pb : Nat) : List BodyEvent :=
  let setup : Except Error (List BodyEvent) := do
    let (g,c) ← Layout.ofHeader h tp.index
    L.check Tier2.Packet.loc .packets (iterationWork g c.progression c.poc)
    let (ps,base,_) ← initPrecincts L g
    let (buf,_) ← tileData data tp.tile
    pure (walkBodies L c base (hs.map (·.bytes)).isNone pb (schedule g [] (volumes g c.progression c.poc))
      (firstState ps buf hs))
  setup.toOption.getD []

private theorem history_events (L : Limits) (h : Header) (data : ByteArray) (tp : TileParams)
    (hs : Option HeaderStream) (pb : Nat) :
    let rows := bodyHistory L h data tp hs pb
    rows.map BodyEvent.event = (measureStream L h data tp hs pb).1 ∧ ∀ e ∈ rows, CountedEvent L e := by
  unfold bodyHistory measureStream
  cases layout : Layout.ofHeader h tp.index with
  | error => simp [before,bind,Except.bind,Except.toOption]
  | ok pair =>
    obtain ⟨g,c⟩ := pair
    cases chk : L.check Tier2.Packet.loc .packets (iterationWork g c.progression c.poc) with
    | error => simp [before,bind,Except.bind,Except.toOption,chk]
    | ok u =>
      cases init : initPrecincts L g with
      | error => simp [before,bind,Except.bind,Except.toOption,chk,init]
      | ok a =>
        obtain ⟨ps,base,spans⟩ := a
        cases input : tileData data tp.tile with
        | error => simp [before,bind,Except.bind,Except.toOption,chk,init]
        | ok z =>
          obtain ⟨buf,parts⟩ := z
          simpa only [before,afterRun,bind,Except.bind,chk,init,input,pure,Except.pure,Except.toOption,
            Option.getD_some] using walk_bodies (L := L) c base (hs.map (·.bytes)).isNone pb
              (schedule g [] (volumes g c.progression c.poc)) (firstState ps buf hs) (initial_shapes init)

private theorem prefix_sum (L : Limits) (xs : List BodyEvent) (good : ∀ e ∈ xs, CountedEvent L e) :
    let calls := attempts (xs.map BodyEvent.event)
    let b := 3*L.maxCodeBlocks
    (xs.map (fun e => e.counts.1)).sum ≤ calls*b ∧
    (xs.map (fun e => e.counts.2)).sum ≤ calls*(b*L.maxPassesPerCodeBlock) := by
  induction xs with
  | nil => simp [attempts]
  | cons e es ih =>
    obtain ⟨n,k,_⟩ := good e (by simp)
    obtain ⟨nt,kt⟩ := ih (fun x hx => good x (by simp [hx]))
    simp only [attempts,List.map_cons,List.countP_cons,List.sum_cons] at *
    cases h : e.event.2.attempted <;> simp [h,Nat.add_mul] at * <;> omega

/-- Exact body inputs for accepted events and counts over any prefix of the real
packet log. A refusing event contributes only the updates it finished and the
piece skips it completed, including inside its last unsuccessful contribution. -/
theorem packet_prefix_counts {L : Limits} {h : Header} {data : ByteArray}
    (parsed : Header.parse L data = .ok h) (tp : TileParams) (hs : Option HeaderStream)
    (pb : Nat) (prior : pb ≤ L.maxCodingPasses) :
    let rows := bodyHistory L h data tp hs pb
    rows.map BodyEvent.event = (measureStream L h data tp hs pb).1 ∧
    (∀ e ∈ rows, ∀ n, e.event.2 = .accepted n → ∃ st cs r st' r',
      e.body = some (st,cs,r) ∧ readBody st cs r = .ok (st',r') ∧
      e.counts = (cs.size,(cs.toList.map (·.pieces.length)).sum)) ∧
    ∀ pre : List BodyEvent, pre <+: rows → let calls := attempts (pre.map BodyEvent.event)
      calls ≤ L.maxPackets ∧
      (pre.map (fun e => e.counts.1)).sum ≤ calls*(3*L.maxCodeBlocks) ∧
      (pre.map (fun e => e.counts.2)).sum ≤ calls*((3*L.maxCodeBlocks)*L.maxPassesPerCodeBlock) := by
  obtain ⟨eq,hist⟩ := history_events L h data tp hs pb
  refine ⟨eq,fun e he => (hist e he).2.2,?_⟩
  intro pre sub
  have counts := prefix_sum L pre (fun e mem => hist e (sub.subset mem))
  obtain ⟨_,positions,charge,_⟩ := measureStream_bounds parsed tp hs pb prior
  have length := sub.length_le
  have total := congrArg List.length eq
  simp only [List.length_map] at total
  have calls := List.countP_le_length (p := fun x : Position × PacketAction => x.2.attempted)
    (l := pre.map BodyEvent.event)
  simp only [List.length_map] at calls
  exact ⟨by unfold attempts; omega,counts⟩

/-- Per selected input, the direct branch borrows the original input and copies
no data bytes. The fragmented branch charges range extraction, every segment
append and every block append, and its resulting byte buffer is bounded as well. -/
theorem selected_block_input {L : Limits} {h : Header} {data : ByteArray}
    {idx t j pb a} (parsed : Header.parse L data = .ok h)
    (ok : packetStore L h data idx t j pb = .ok a) (i r : Nat)
    {p : PrecinctOut} (hp : p ∈ (selected a i).getD r #[]) {b : BandOut} (hb : b ∈ p.bands)
    {cb : CodeBlock} (hc : cb ∈ b.blocks) :
    let input := Assemble.tier1Input data cb
    input.2.size ≤ segmentLimit L ∧
    if cb.segments.all (·.ranges.size ≤ 1) then input = (data,cb.segments.map Assemble.directSeg)
    else let run := HeaderWork.chargedBlock data cb.segments.toList (ByteArray.empty,#[])
         run.1 = input ∧ input.1.size ≤ rangeLimit L*data.size ∧
           run.2 ≤ (2*rangeLimit L+segmentLimit L)*(rangeLimit L*data.size) := by
  obtain ⟨ns,nk⟩ := ((((selected_store_bounds parsed ok i r).2 p hp).2 b hb).2 cb hc)
  obtain ⟨size,storage⟩ := HeaderWork.tier1Input_storage data cb
  refine ⟨Nat.le_trans (Nat.le_of_eq size) ns,?_⟩
  split at storage
  · simpa only [‹_ = true›,↓reduceIte] using storage
  · rename_i no
    have frag : cb.segments.all (·.ranges.size ≤ 1) = false := by simpa using no
    simp only [frag,Bool.false_eq_true,↓reduceIte]
    obtain ⟨eq,writes⟩ := HeaderWork.tier1Input_copy_charge data cb frag
    have cap := Nat.mul_le_mul_right data.size nk
    change HeaderWork.blockRanges cb.segments.toList ≤ _ at nk
    exact ⟨eq,Nat.le_trans storage.2 cap,Nat.le_trans writes (Nat.mul_le_mul (by omega) cap)⟩

private def measuredSegment (ps : Parts) (s : Segment) : Segment × Nat :=
  let rs := s.ranges.foldl (fun (a : Array ByteRange × Nat) r =>
    let next := translateVisits r ps a.1
    (next.1,a.2+next.2)) (#[],0)
  ({s with ranges := rs.1},rs.2)

private theorem measured_segment (ps : Parts) (s : Segment) :
    measuredSegment ps s = (outputSeg ps s,s.ranges.size*ps.length) := by
  let step := fun (a : Array ByteRange × Nat) r =>
    let next := translateVisits r ps a.1
    (next.1,a.2+next.2)
  have fold (xs : List ByteRange) (a : Array ByteRange × Nat) :
      xs.foldl step a =
        (xs.foldl (fun acc r => translate r ps acc) a.1,a.2+xs.length*ps.length) := by
    induction xs generalizing a with
    | nil => simp
    | cons r rs ih =>
      rw [List.foldl_cons,ih]
      obtain ⟨val,cnt,_⟩ := translate_visits r ps a.1
      simp only [step,val,cnt,List.foldl_cons,List.length_cons,Nat.succ_mul,Prod.mk.injEq,true_and]
      omega
  have eq := fold s.ranges.toList (#[],0)
  simp only [Nat.zero_add,Array.length_toList,Array.foldl_toList] at eq
  unfold measuredSegment outputSeg
  change (let rs := s.ranges.foldl step (#[],0); _) = _
  rw [eq]

/-- Translate the segments of one block and count the tile-part probes performed
by the actual accumulator for each range. -/
def translateBlock (ps : Parts) (cb : CodeBlock) : CodeBlock × Nat :=
  let segs := cb.segments.map (measuredSegment ps)
  ({cb with segments := segs.map Prod.fst}, (segs.toList.map Prod.snd).sum)

private theorem sum_mul {α : Type} (xs : List α) (f : α → Nat) (n : Nat) :
    (xs.map (fun x => f x*n)).sum = (xs.map f).sum*n := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons,List.sum_cons,ih,Nat.add_mul]

private theorem translated_block (ps : Parts) (cb : CodeBlock) :
    translateBlock ps cb = (outputBlock ps cb,rangeCount cb*ps.length) := by
  simp only [translateBlock,Array.map_map,Array.toList_map,List.map_map,Function.comp_def,
    measured_segment,outputBlock,rangeCount,HeaderWork.blockRanges,sum_mul]

/-- Rebuild the output precinct using the value projection of each counted block translation. -/
def translatePrecinct (ps : Parts) (k : Nat) (st : PrecState) : PrecinctOut :=
  {index := k, bands := st.bands.map fun b =>
    {band := b.band, rect := b.rect, maxZero := b.maxZero,
     blocks := b.blocks.map fun cb => (translateBlock ps cb).1}}

private theorem measured_prec (ps : Parts) (k : Nat) (st : PrecState) :
    translatePrecinct ps k st = st.out ps k := by
  simp only [translatePrecinct,translated_block,outputBlock,PrecState.out]
  rfl

private theorem sum_mono {α : Type} (xs : List α) (f g : α → Nat) (h : ∀ x ∈ xs, f x ≤ g x) :
    (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons x xs ih => exact Nat.add_le_add (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

/-- Probes of every source triple over all segment ranges of all blocks in the
specified precinct. Empty intersections count as probes. -/
def precinctProbes (ps : Parts) (st : PrecState) : Nat :=
  (st.bands.toList.map fun b => (b.blocks.toList.map fun cb => (translateBlock ps cb).2).sum).sum

private theorem precinct_probes (ps : Parts) (st : PrecState) :
    precinctProbes ps st ≤ retained st.bands * ps.length := by
  simp only [precinctProbes,translated_block,sum_mul]
  apply Nat.mul_le_mul_right
  apply sum_mono
  intro b _
  apply sum_mono
  intro cb _
  exact Nat.le_add_left ..

/-- A completed store uses the counted translations at the actual span offsets.
The probe bound aggregates every block of one output precinct, independently of
whether intersections were merged, retained separately, or empty. -/
theorem translation_history {L : Limits} {h : Header} {data : ByteArray} {tp : TileParams}
    {hs : Option HeaderStream} {pb : Nat} {out : TileCodeBlocks}
    (parsed : Header.parse L data = .ok h) (member : tp ∈ h.tiles)
    (ok : decodeWithStream L h data tp hs pb = .ok out) :
    ∃ (s : LoopState) (ps : Parts) (spans : Array (Array (Nat × Nat))),
      ps.length = tp.tile.parts.size ∧
      out.comps = spans.map (fun si => si.map fun (start,n) =>
        (Array.range n).map fun k => translatePrecinct ps k (s.precs.getD (start+k) default)) ∧
      ∀ j, precinctProbes ps (s.precs.getD j default) ≤
        (out.packets*recordGrowth L)*tp.tile.parts.size ∧
        precinctProbes ps (s.precs.getD j default) ≤ rangeLimit L := by
  obtain ⟨s,ps,spans,len,seq,packets,records,output⟩ := completed_store parsed ok
  refine ⟨s,ps,spans,len,by simpa only [measured_prec] using output,?_⟩
  intro j
  have bound := Nat.le_trans (precinct_probes ps _) (Nat.mul_le_mul_right ps.length
    (Nat.le_trans (state_records s j) records))
  rw [len,seq] at bound
  exact ⟨bound,Nat.le_trans bound (Nat.mul_le_mul (Nat.mul_le_mul_right _ (seq ▸ packets))
    (HeaderWork.parse_tile_storage parsed tp member).1)⟩

private def precinctCount (comps : Array (Array (Array PrecinctOut))) :=
  (comps.toList.map fun row => (row.toList.map Array.size).sum).sum

private def spanCount (spans : Array (Array (Nat × Nat))) :=
  (spans.toList.map fun row => (row.toList.map Prod.snd).sum).sum

private theorem init_span_count {L : Limits} {g ps base spans}
    (init : initPrecincts L g = .ok (ps,base,spans)) : spanCount spans = ps.size := by
  unfold initPrecincts at init
  simp only [Std.Legacy.Range.forIn_eq_forIn_range'] at init
  obtain ⟨s,loop,init⟩ := Tier2Equiv.bind_ok init
  cases init
  refine Tier2Equiv.forIn_inv (fun (a : Array PrecState × Array (Array Nat) × Array (Array (Nat × Nat)) × Nat) =>
    spanCount a.2.2.1 = a.1.size) _ ?_ _ _ _ rfl loop
  intro i a y inv run
  obtain ⟨z,middle,run⟩ := Tier2Equiv.bind_ok run
  cases run
  have mid := Tier2Equiv.forIn_inv (fun (v : Array PrecState × Nat × Array Nat × Array (Nat × Nat)) =>
    a.1.size+(v.2.2.2.toList.map Prod.snd).sum = v.1.size) _ ?_ _ _ _ (by simp) middle
  · simp [spanCount] at inv ⊢
    omega
  intro r v y inv run
  obtain ⟨res,_,run⟩ := Tier2Equiv.bind_ok run
  obtain ⟨_,_,run⟩ := Tier2Equiv.bind_ok run
  obtain ⟨w,inner,run⟩ := Tier2Equiv.bind_ok run
  cases run
  have len := Tier2WF.forIn_range'_inv (fun k (a : Array PrecState × Nat) =>
    a.1.size = v.1.size+k) _ ?_ _ 0 _ _ (by simp) inner
  · simp [Std.Legacy.Range.size] at len
    simp
    omega
  intro k a y inv run
  obtain ⟨pg,_,run⟩ := Tier2Equiv.bind_ok run
  obtain ⟨_,_,run⟩ := Tier2Equiv.bind_ok run
  obtain ⟨st,_,run⟩ := Tier2Equiv.bind_ok run
  cases run
  exact ⟨_,rfl,by simp [inv,Nat.add_assoc]⟩

private theorem rows_count (spans : Array (Array (Nat × Nat)))
    (make : Nat × Nat → Nat → PrecinctOut) :
    precinctCount (spans.map (fun row => row.map (fun sn => (Array.range sn.2).map (make sn)))) =
      spanCount spans := by simp [precinctCount,spanCount,List.map_map,Function.comp_def]

private theorem output_count {L : Limits} {h : Header} {data : ByteArray} {tp : TileParams}
    {hs : Option ByteArray} {pb : Nat} {out : TileCodeBlocks}
    (ok : decodeTilePacketsWith L h data tp hs pb = .ok out) : precinctCount out.comps ≤ L.maxPrecincts := by
  unfold decodeTilePacketsWith at ok
  obtain ⟨⟨g,c⟩,_,ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨_,_,ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨⟨ps,base,spans⟩,init,ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨⟨buf,parts⟩,_,ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨s,_,ok⟩ := Tier2Equiv.bind_ok ok
  cases ok
  exact Nat.le_trans (Nat.le_of_eq ((rows_count spans (fun sn k =>
    (s.precs.getD (sn.1+k) default).out parts k)).trans (init_span_count init)))
    (HeaderWork.initPrecincts_storage init).1

/-- Sum the probe counts of all translated precincts at the actual span indices. -/
def tileProbes (s : LoopState) (ps : Parts) (spans : Array (Array (Nat × Nat))) :=
  (spans.toList.map fun row => (row.toList.map fun sn =>
    ((List.range sn.2).map (fun k => precinctProbes ps (s.precs.getD (sn.1+k) default))).sum).sum).sum

/-- Total part-table probes across every translated segment and range in the
completed tile. The sum of the emitted span lengths equals the number of
initialized precincts, including empty precincts. -/
theorem tile_translation_work {L : Limits} {h : Header} {data : ByteArray} {tp : TileParams}
    {hs : Option HeaderStream} {pb : Nat} {out : TileCodeBlocks}
    (parsed : Header.parse L data = .ok h) (member : tp ∈ h.tiles)
    (ok : decodeWithStream L h data tp hs pb = .ok out) :
    ∃ (s : LoopState) (ps : Parts) (spans : Array (Array (Nat × Nat))),
      ps.length = tp.tile.parts.size ∧
      out.comps = spans.map (fun si => si.map fun (start,n) =>
        (Array.range n).map fun k => translatePrecinct ps k (s.precs.getD (start+k) default)) ∧
      tileProbes s ps spans ≤ L.maxPrecincts*rangeLimit L := by
  obtain ⟨s,ps,spans,parts,eq,each⟩ := translation_history parsed member ok
  refine ⟨s,ps,spans,parts,eq,?_⟩
  have n := output_count (stream_raw ok)
  rw [eq] at n
  change precinctCount (spans.map (fun row => row.map (fun sn =>
    (Array.range sn.2).map (fun k => translatePrecinct ps k (s.precs.getD (sn.1+k) default)))) ) ≤ _ at n
  rw [rows_count] at n
  apply Nat.le_trans _ (Nat.mul_le_mul_right (rangeLimit L) n)
  unfold tileProbes spanCount
  rw [← sum_mul]
  apply sum_mono
  intro row _
  rw [← sum_mul]
  apply sum_mono
  intro sn _
  simpa using sum_cap (List.range sn.2) _ (rangeLimit L) (fun k _ => (each (sn.1+k)).2)

end JPEG2000.Spec.Resources.SegmentHistory
