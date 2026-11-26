import Spec.Resources.HeaderPayload
import Spec.Resources.ReconstructionCost

/-!
# Native decoder resource composition (Plan.md §§3–5, 7, S3)

T.800 A, B.2–B.12, C–G. These observations follow the public reduction,
header, allocation, rank, tile and packet cursors. All input buffers are
borrowed until the explicit gathers. A slot denotes a logical record or
reference. Packed raster, gathered bytes and wide signed-magnitude payload
have byte prices. Stage meters may reserve work at a reached call.
-/

namespace JPEG2000.Spec.Resources.NativeCost

open JPEG2000.Header JPEG2000.Bytes JPEG2000.Progression JPEG2000.Tier2.Packet
open JPEG2000.Tier2.Headers PacketLocalWork PacketTraversal

private theorem sumCap {α : Type} (xs : List α) (f : α → Nat) (n : Nat)
    (bound : ∀ x ∈ xs, f x ≤ n) : (xs.map f).sum ≤ xs.length*n := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have head := bound x (by simp)
    have tail := ih (fun y hy => bound y (by simp [hy]))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.succ_mul]
    omega

/-- Layout entries, both aggregate folds, mapped component descriptors and
the actual four- or eight-byte zero backings. Parsed depths ensure the
allocation map succeeds once both checks pass. Each of the four reduced
coordinates can construct a power of two with a caller-supplied exponent.
The per-coordinate reservation includes its divisor and the addition to a
32-bit SIZ coordinate in ceiling division. -/
def allocation (L : Limits) (s : Marker.SIZ) (red : Nat) :=
  let rs := JPEG2000.NativeOutput.layout s red
  let width := rs.size
  let cells := JPEG2000.NativeOutput.cells rs
  let bytes := JPEG2000.NativeOutput.decodedBytes rs
  1 + match L.check (.at .decode) .decompLevels red with
  | .error _ => 0
  | .ok _ => 2 + 3*width + 4*width*(2*(5+min red L.maxDecompLevels)) + match L.check (.at .decode) .workSamples cells with
    | .error _ => 0
    | .ok _ => 1 + width + match L.check (.at .decode) .decodedBytes bytes with
      | .error _ => 0
      | .ok _ => 1 + 3*width + match JPEG2000.NativeOutput.allocOutput L s red with
        | .error _ => 0
        | .ok ds => (ds.toList.map Spec.NativeOutput.backingBytes).sum

/-- Logical charges before tile entry, including all reduced rectangles and
the full four- or eight-byte native destinations. -/
def allocationBudget (L : Limits) :=
  5 + 7*L.maxComponents + 8*L.maxWorkSamples + 4*L.maxComponents*(2*(5+L.maxDecompLevels))

/-- The allocation prefix and its uniform charge. The final field identifies
the result of the allocation map whenever both aggregate checks admitted it. -/
theorem allocation_work {L : Limits} {data : ByteArray} {h : Header}
    (parsed : Header.parse L data = .ok h) (red : Nat) :
    allocation L h.siz red ≤ allocationBudget L ∧
    ∀ (_ : red ≤ L.maxDecompLevels),
      JPEG2000.NativeOutput.cells (JPEG2000.NativeOutput.layout h.siz red) ≤ L.maxWorkSamples →
      JPEG2000.NativeOutput.decodedBytes (JPEG2000.NativeOutput.layout h.siz red) ≤ L.maxDecodedBytes →
      ∃ ds, JPEG2000.NativeOutput.allocOutput L h.siz red = .ok ds := by
  refine ⟨?_,fun hr hw hb => Spec.NativeOutput.allocOutput_succeeds _ _ _ hr hw hb
    (NativePlacement.parsed_depth parsed)⟩
  have size : (JPEG2000.NativeOutput.layout h.siz red).size ≤ L.maxComponents := by
    simpa only [JPEG2000.NativeOutput.layout,Array.size_map,Marker.SIZ.csiz] using
      (HeaderWork.parse_storage parsed).2.1
  have coord := Nat.mul_le_mul (Nat.mul_le_mul_left 4 size)
    (Nat.mul_le_mul_left 2 (Nat.add_le_add_left (Nat.min_le_right red L.maxDecompLevels) 5))
  unfold allocation allocationBudget
  dsimp only
  repeat' split
  all_goals try simp only [Nat.add_zero, Nat.add_assoc]
  all_goals try lia
  rename_i ds ha
  have physical := (Spec.NativeOutput.allocOutput_bounds ha).2.2
  lia

private def entryAllocation (L : Limits) (data : ByteArray) (red : Nat) :=
  match L.check JPEG2000.Decode.loc .decompLevels red with
  | .error _ => 0
  | .ok _ => match Header.parse L data with
    | .error _ => 0
    | .ok h => allocation L h.siz red

private theorem entry_le (L : Limits) (data : ByteArray) (red : Nat) :
    entryAllocation L data red ≤ allocationBudget L := by
  unfold entryAllocation
  split <;> try exact Nat.zero_le _
  split <;> try exact Nat.zero_le _
  exact (allocation_work (by assumption) red).1

/-- Retained header and destination data at the entry to the tile loop.
The header bounds also hold when allocation is the first failing operation. -/
def EntryStorage (L : Limits) (data : ByteArray) (red : Nat) : Prop :=
  match L.check JPEG2000.Decode.loc .decompLevels red with
  | .error _ => True
  | .ok _ => match Header.parse L data with
    | .error _ => True
    | .ok h =>
      HeaderWithin L data h ∧ h.siz.csiz ≤ L.maxComponents ∧
      h.codestream.start + h.codestream.len ≤ data.size ∧
      h.main.markers.size + h.main.coc.size + h.main.qcc.size + h.main.rgn.size +
        h.main.poc.size + h.main.com.size + h.main.pointers.size + h.main.unknown.size ≤ h.codestream.len ∧
      h.ppm.chunks.size ≤ L.maxTileParts ∧ h.ppm.segments.size ≤ data.size ∧
      (h.ppm.chunks.toList.map Array.size).sum ≤ L.maxTileParts*data.size ∧
      (∀ tp ∈ h.tiles, tp.tile.parts.size ≤ L.maxTilePartsPerTile ∧
        tp.tile.ppt.size ≤ L.maxTilePartsPerTile*(data.size+1) ∧
        ∀ part ∈ tp.tile.parts, part.data.stop ≤ data.size ∧ part.markers.size+part.segments.size ≤ data.size+1) ∧
      match JPEG2000.NativeOutput.allocOutput L h.siz red with
      | .error _ => True
      | .ok ds =>
        ds.size = h.siz.components.size ∧
        JPEG2000.NativeOutput.decodedBytes (ds.map fun d => (d.rect,d.format)) ≤ L.maxDecodedBytes ∧
        (ds.toList.map Spec.NativeOutput.backingBytes).sum ≤ 8*L.maxWorkSamples ∧
        ∀ d ∈ ds, Spec.NativeOutput.backingBytes d =
          (if JPEG2000.NativeOutput.compact d.format then 4 else 8)*(d.rect.width*d.rect.height)

/-- Recover the header and native backing sizes on arbitrary input from the
public admission checks, independently of rank, packet and placement errors. -/
theorem entry_storage (L : Limits) (data : ByteArray) (red : Nat) : EntryStorage L data red := by
  unfold EntryStorage
  split <;> try trivial
  split <;> try trivial
  rename_i h hp
  obtain ⟨within,cs,range,main⟩ := HeaderWork.parse_storage hp
  obtain ⟨chunks,segments,ranges⟩ := HeaderWork.parse_ppm hp
  refine ⟨within,cs,range,main,chunks,segments,ranges,HeaderWork.parse_tile_storage hp,?_⟩
  split <;> try trivial
  rename_i ds alloc
  obtain ⟨shape,bytes,backing⟩ := Spec.NativeOutput.allocOutput_bounds alloc
  refine ⟨?_,bytes,backing,fun d _ => Spec.NativeOutput.backing_size d⟩
  simpa only [JPEG2000.NativeOutput.layout,Array.size_map] using congrArg Array.size shape

/-- Body updates and successful piece skips, including the last, partially
read contribution. Both can be nonzero for a rejected packet. -/
def bodyCharge (rows : List SegmentHistory.BodyEvent) :=
  (rows.map (fun e => e.counts.1)).sum + (rows.map (fun e => e.counts.2)).sum

/-- Maximum completed body updates and piece skips per selected tile. -/
def bodyLimit (L : Limits) := L.maxPackets*(3*L.maxCodeBlocks) +
  L.maxPackets*(3*L.maxCodeBlocks*L.maxPassesPerCodeBlock)

private theorem body_le {L : Limits} {h : Header} {data : ByteArray}
    (hp : Header.parse L data = .ok h) (tp : TileParams) (hs : Option HeaderStream)
    (pb : Nat) (prior : pb ≤ L.maxCodingPasses) :
    bodyCharge (SegmentHistory.bodyHistory L h data tp hs pb) ≤ bodyLimit L := by
  have ⟨calls,updates,pieces⟩ := (SegmentHistory.packet_prefix_counts hp tp hs pb prior).2.2
    (SegmentHistory.bodyHistory L h data tp hs pb) ⟨[],by simp⟩
  exact Nat.add_le_add (Nat.le_trans updates (Nat.mul_le_mul_right _ calls))
    (Nat.le_trans pieces (Nat.mul_le_mul_right _ calls))

private def preflightLimit (L : Limits) := 1+2*L.maxPocEntries+3*L.maxComponents +
  (L.maxPocEntries+1)*(4+L.maxComponents*(3+3*L.maxComponents+2*(L.maxDecompLevels+1)))

private def gatherLimit (L : Limits) (n : Nat) :=
  2 + 4*L.maxTilePartsPerTile + L.maxTilePartsPerTile*(n+L.maxTilePartsPerTile*n)

private def stepCharge {α β : Type} (x : Except Error α) (n : Nat)
    (next : α → Except Error β × Nat) : Except Error β × Nat :=
  match x with
  | .error e => (.error e,n)
  | .ok a => let m := next a; (m.1,n+m.2)

private theorem step_result {α β : Type} (x : Except Error α) (n : Nat)
    (next : α → Except Error β × Nat) :
    (stepCharge x n next).1 = (x >>= fun a => (next a).1) := by cases x <;> rfl

private theorem step_work {α β : Type} (x : Except Error α) (n : Nat)
    (next : α → Except Error β × Nat) :
    (stepCharge x n next).2 = n + (match x with | .error _ => 0 | .ok a => (next a).2) := by
  cases x <;> simp [stepCharge]

/-- Raw packet execution and the charges before, around and after the iterator.
The packet check follows preflight, the gather precedes progression setup,
and translation precedes the packed-header exhaustion check. Gathering
reserves array/list slots and visits per triple plus extract/append copies. -/
def packetMeter (L : Limits) (h : Header) (data : ByteArray) (tp : TileParams)
    (hs : Option HeaderStream) (pb : Nat) : Except Error TileCodeBlocks × Nat :=
  stepCharge (Layout.ofHeader h tp.index) 0 fun (g,c) =>
    let pf := preflight g c.progression c.poc
    stepCharge (L.check JPEG2000.Tier2.Packet.loc .packets pf.1) pf.2 fun _ =>
    stepCharge (initPrecincts L g) 0 fun (precs,base,spans) =>
      let copies := (HeaderWork.chargedTile data tp.tile.parts.toList (ByteArray.empty,#[])).2
      stepCharge (tileData data tp.tile) (2+4*tp.tile.parts.size+copies) fun (buf,parts) =>
        let same := (hs.map (·.bytes)).isNone
        let prog := progressionSetup g c.progression c.poc (packetStep L c base same pb)
          (firstState precs buf hs)
        stepCharge prog.result prog.work fun s =>
          (.ok (outputTile tp same buf parts spans s),SegmentHistory.translationCharge s parts spans)

/-- Erasing setup and translation charges preserves the complete raw tile
result, including a rejection at preflight, initialization, gather or callback. -/
theorem packetMeter_result {L : Limits} {h : Header} {data : ByteArray} {tp : TileParams}
    (hp : Header.parse L data = .ok h) (hs : Option HeaderStream) (pb : Nat) :
    (packetMeter L h data tp hs pb).1 = decodeTilePacketsWith L h data tp (hs.map (·.bytes)) pb := by
  unfold packetMeter decodeTilePacketsWith
  simp only [step_result]
  cases layout : Layout.ofHeader h tp.index with
  | error => rfl
  | ok pair =>
    obtain ⟨g,c⟩ := pair
    simp only [bind,Except.bind,(preflight_work hp layout).1]
    cases L.check JPEG2000.Tier2.Packet.loc .packets (iterationWork g c.progression c.poc) with
    | error => rfl
    | ok =>
      cases initPrecincts L g with
      | error => rfl
      | ok state =>
        obtain ⟨precs,base,spans⟩ := state
        cases tileData data tp.tile with
        | error => rfl
        | ok dataParts =>
          obtain ⟨buf,parts⟩ := dataParts
          simp only [Counted.erase]
          rfl

private def streamLimit (L : Limits) (n : Nat) :=
  preflightLimit L + (gatherLimit L n +
    (setupLimit L L.maxLayers L.maxPocEntries + SegmentHistory.translationBudget L))

private theorem stream_le {L : Limits} {h : Header} {data : ByteArray} {tp : TileParams}
    (hp : Header.parse L data = .ok h) (mem : tp ∈ h.tiles) (hs : Option HeaderStream) (pb : Nat) :
    (packetMeter L h data tp hs pb).2 ≤ streamLimit L data.size := by
  unfold packetMeter streamLimit
  simp only [step_work,Nat.zero_add]
  split
  · exact Nat.zero_le _
  rename_i g c layout
  obtain ⟨same,price⟩ := preflight_work hp layout
  apply Nat.add_le_add price
  rw [same]
  split <;> try exact Nat.zero_le _
  rename_i u quota
  cases u
  split <;> try exact Nat.zero_le _
  rename_i precs base spans init
  have k := (HeaderWork.parse_tile_storage hp tp mem).1
  have copies := (HeaderWork.tileData_copy_charge data tp.tile).2.1
  have cap := Nat.mul_le_mul k (Nat.add_le_add_left (Nat.mul_le_mul_right data.size k) data.size)
  apply Nat.add_le_add (show _ ≤ gatherLimit L data.size by unfold gatherLimit; omega)
  split <;> try exact Nat.zero_le _
  rename_i buf parts input
  apply Nat.add_le_add (parsed_setup hp layout init ..)
  split <;> try exact Nat.zero_le _
  rename_i s run
  exact SegmentHistory.iteration_translation hp mem layout quota init input
    ((progressionSetup ..).erase.symm.trans run)

/-- PPM table selected once by the production grid driver. -/
def ranks (L : Limits) (h : Header) : Except Error (Array (Array Nat)) :=
  if h.ppm.segments.isEmpty then pure #[] else ppmChunkIndex L h

private theorem prepared {L : Limits} {data : ByteArray} {red : Nat} {h dst}
    (ok : PublicPacketWork.prepareTiles L data red = .ok (h,dst)) :
    Header.parse L data = .ok h ∧ JPEG2000.NativeOutput.allocOutput L h.siz red = .ok dst := by
  unfold PublicPacketWork.prepareTiles at ok
  obtain ⟨_,_,ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨_,hp,ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨_,ha,ok⟩ := Tier2Equiv.bind_ok ok
  cases ok
  exact ⟨hp,ha⟩

private theorem publicTrace {L : Limits} {data : ByteArray} {red : Nat} {h dst}
    (entry : PublicPacketWork.prepareTiles L data red = .ok (h,dst)) :
    Trace L h data 0 0 0 (PublicPacketWork.measure L data red).1 := by
  simp only [PublicPacketWork.measure,entry,before,measureTiles_finish,afterRun]
  exact (measureGrid_trace (prepared entry).1 dst (JPEG2000.Decode.centeredTile L h data red)
    (·.saturated) (fun acc tile => JPEG2000.NativeOutput.writeTile L h.siz red
      tile.layout tile.coding acc tile.sources)).1

private theorem visitFacts {L : Limits} {data : ByteArray} {red : Nat} {h dst v}
    (entry : PublicPacketWork.prepareTiles L data red = .ok (h,dst))
    (hit : v ∈ (PublicPacketWork.measure L data red).1) :
    Sourced L h data v ∧ v.passesBefore ≤ L.maxCodingPasses := by
  obtain ⟨pre,tail,eq⟩ := List.mem_iff_append.mp hit
  have tr := publicTrace entry
  rw [eq] at tr
  have hv := trace_visit tr
  have cap := hv.nextPasses
  rw [← hv.start] at cap
  exact ⟨hv.source,by omega⟩

/-- Retained index rows, both tag trees, position-table candidates and the
gathered tile body, including setup that produces zero packet callbacks. -/
def SetupStorage (L : Limits) (h : Header) (data : ByteArray) (tp : TileParams) : Prop :=
  match Layout.ofHeader h tp.index with
  | .error _ => True
  | .ok (g,c) =>
    (preflight g c.progression c.poc).1 = iterationWork g c.progression c.poc ∧
    (preflight g c.progression c.poc).2 ≤ preflightLimit L ∧
    match L.check JPEG2000.Tier2.Packet.loc .packets (iterationWork g c.progression c.poc) with
    | .error _ => True
    | .ok _ =>
      (∃ comps levels, let run := GeometryInit.initWork L g comps levels
        run.result = initPrecincts L g ∧ run.work ≤ GeometryInit.initBudget L) ∧
      match initPrecincts L g with
      | .error _ => True
      | .ok (ps,base,spans) =>
        ps.size ≤ L.maxPrecincts ∧ base.size = g.numComps ∧ spans.size = g.numComps ∧
        g.numComps ≤ L.maxComponents ∧
        (∀ i row, base[i]? = some row → row.size = (g.comp i).numResolutions) ∧
        (∀ i row, spans[i]? = some row → row.size = (g.comp i).numResolutions) ∧
        (∀ i : Fin g.numComps, (g.comp i).numResolutions ≤ L.maxDecompLevels+1) ∧
        (ps.toList.map (fun st => (st.bands.toList.map HeaderWork.bandSlots).sum)).sum ≤
          L.maxPrecincts*(3*(17*L.maxCodeBlocks)) ∧
        match tileData data tp.tile with
        | .error _ => True
        | .ok (buf,parts) => buf.size ≤ L.maxTilePartsPerTile*data.size ∧
          parts.length = tp.tile.parts.size ∧ ∀ v : Volume,
            (precRefs g v).length ≤ L.maxComponents*((L.maxDecompLevels+1)*L.maxPrecincts)

private theorem setup_storage {L : Limits} {h : Header} {data : ByteArray} {tp : TileParams}
    (hp : Header.parse L data = .ok h) (mem : tp ∈ h.tiles) : SetupStorage L h data tp := by
  unfold SetupStorage
  split <;> try trivial
  rename_i g c layout
  have pf := preflight_work hp layout
  refine ⟨pf.1,pf.2,?_⟩
  split <;> try trivial
  have dims := HeaderWork.layout_budget hp layout
  refine ⟨⟨dims.1,dims.2,GeometryInit.parsed_init_work hp layout⟩,?_⟩
  split <;> try trivial
  rename_i ps base spans init
  obtain ⟨prec,b,s,slots⟩ := HeaderWork.initPrecincts_storage init
  obtain ⟨nc,nr⟩ := HeaderWork.layout_budget hp layout
  obtain ⟨baseRows,spanRows⟩ := GeometryInit.init_index_rows init
  refine ⟨prec,b,s,nc,baseRows,spanRows,nr,slots,?_⟩
  split <;> try trivial
  rename_i buf parts got
  obtain ⟨size,len⟩ := (HeaderWork.tileData_copy_charge data tp.tile).2.2 buf parts got
  exact ⟨Nat.le_trans size (Nat.mul_le_mul_right _ (HeaderWork.parse_tile_storage hp tp mem).1),
    len,table_limit hp layout init⟩

/-- Resource facts at a visited tile, including a visit with no packet
positions. The rank table, pass count and cursor come from the same execution.
The packed stream and packet body history can survive only until that tile
returns. A completed packet store can still be followed by a failing transform. -/
def VisitStorage (L : Limits) (h : Header) (data : ByteArray) (v : TileVisit) : Prop :=
  ∃ idx, ranks L h = .ok idx ∧ idx.size ≤ L.maxTiles ∧
    (idx.map Array.size).toList.sum ≤ L.maxTileParts ∧
    match presentAt h v.tile v.cursor with
    | none => v.packets = []
    | some tp => tp ∈ h.tiles ∧ tp.tile.parts.size ≤ L.maxTilePartsPerTile ∧
      match headerStreamAt h data tp (idx.getD v.cursor #[]) with
      | .error _ => v.packets = []
      | .ok hs =>
        let rows := SegmentHistory.bodyHistory L h data tp hs v.passesBefore
        SetupStorage L h data tp ∧ rows.map SegmentHistory.BodyEvent.event = v.packets ∧
        (∀ pre, pre <+: rows → bodyCharge pre ≤ bodyLimit L) ∧
        (∀ stream, hs = some stream →
          let k := if stream.fromPpm then L.maxTilePartsPerTile*(L.maxTileParts*data.size)
                   else L.maxTilePartsPerTile*(data.size+1)
          stream.ranges.size ≤ k ∧ stream.bytes.size ≤ k*data.size) ∧
        (∀ out, decodeTilePacketsWith L h data tp (hs.map (·.bytes)) v.passesBefore = .ok out →
          SegmentHistory.storeSlots out ≤ SegmentHistory.translationBudget L) ∧
        ∀ out, decodeWithStream L h data tp hs v.passesBefore = .ok out →
          (∀ i, AssemblyCost.StoreBounds (AssemblyCost.selected (some out) i) L.maxPrecincts
            3 L.maxCodeBlocks (SegmentHistory.segmentLimit L) (SegmentHistory.rangeLimit L)) ∧
          ∃ s ps spans, ps.length = tp.tile.parts.size ∧
            out.comps = spans.map (fun row => row.map fun (start,n) =>
              (Array.range n).map fun k => SegmentHistory.translatePrecinct ps k
                (s.precs.getD (start+k) default)) ∧
            SegmentHistory.tileProbes s ps spans ≤ L.maxPrecincts*SegmentHistory.rangeLimit L

private theorem storage_of_source {L : Limits} {h : Header} {data : ByteArray} {v : TileVisit}
    (hp : Header.parse L data = .ok h) (src : Sourced L h data v)
    (prior : v.passesBefore ≤ L.maxCodingPasses) : VisitStorage L h data v := by
  obtain ⟨idx,hidx,src⟩ := src
  obtain ⟨rows,entries⟩ := HeaderPayload.rank_storage hp hidx
  refine ⟨idx,hidx,rows,entries,?_⟩
  cases sel : presentAt h v.tile v.cursor with
  | none => simpa [sel] using src
  | some tp =>
    have mem := SegmentHistory.present_mem sel
    refine ⟨mem,(HeaderWork.parse_tile_storage hp tp mem).1,?_⟩
    cases got : headerStreamAt h data tp (idx.getD v.cursor #[]) with
    | error e => simpa only [sel,got] using src
    | ok hs =>
      obtain ⟨eq,_,prefixes⟩ := SegmentHistory.packet_prefix_counts hp tp hs v.passesBefore prior
      refine ⟨setup_storage hp mem,eq.trans (by simpa only [sel,got] using src.symm),?_,?_,?_,?_⟩
      · intro pre sub
        obtain ⟨calls,updates,pieces⟩ := prefixes pre sub
        exact Nat.add_le_add (Nat.le_trans updates (Nat.mul_le_mul_right _ calls))
          (Nat.le_trans pieces (Nat.mul_le_mul_right _ calls))
      · rintro stream rfl
        exact HeaderWork.parsed_headerStream hp mem got
      · exact fun _ raw => SegmentHistory.raw_store_slots (hs := hs) hp mem raw
      · intro out decoded
        exact ⟨SegmentHistory.store_bounds hp mem decoded,SegmentHistory.tile_translation_work hp mem decoded⟩

/-- Public prefix witnesses for every attempted grid tile, independent of the
final image or error. Includes the initially retained native destination bytes. -/
theorem visited_storage (L : Limits) (data : ByteArray) (red : Nat) (v : TileVisit)
    (hit : v ∈ (PublicPacketWork.measure L data red).1) :
    ∃ h dst, PublicPacketWork.prepareTiles L data red = .ok (h,dst) ∧
      Header.parse L data = .ok h ∧
      (dst.toList.map Spec.NativeOutput.backingBytes).sum ≤ 8*L.maxWorkSamples ∧
      v.passesBefore ≤ L.maxCodingPasses ∧ VisitStorage L h data v := by
  cases entry : PublicPacketWork.prepareTiles L data red with
  | error => simp [PublicPacketWork.measure,entry,before] at hit
  | ok pair =>
    obtain ⟨h,dst⟩ := pair
    obtain ⟨hp,ha⟩ := prepared entry
    obtain ⟨src,prior⟩ := visitFacts entry hit
    exact ⟨h,dst,rfl,hp,(Spec.NativeOutput.allocOutput_bounds ha).2.2,prior,
      storage_of_source hp src prior⟩

private theorem write_backing {L : Limits} {s : Marker.SIZ} {red tc coding ds out sources}
    (wrote : JPEG2000.NativeOutput.writeTile L s red tc coding ds sources = .ok out) :
    out.map Spec.NativeOutput.backingBytes = ds.map Spec.NativeOutput.backingBytes := by
  obtain ⟨sz,_,_,_,placed⟩ := Spec.NativeOutput.writeTile_spec wrote
  apply Array.ext
  · simpa using sz.symm
  · intro i _ hi
    have h := Array.size_map .. ▸ hi
    obtain ⟨q,_,found,_,hr,hf,_,_⟩ := placed i h
    simp only [Array.getElem?_eq_getElem (sz ▸ h),Option.some.injEq] at found
    simp [found,Spec.NativeOutput.backing_size,hr,hf]

/-- The live native destination at the start of every visited tile has the
same individual byte lengths as the allocator's result. The checked prefix
recovers the current array even if this tile is the first failing write. -/
theorem destination_storage (L : Limits) (data : ByteArray) (red : Nat) {pre v tail}
    (trace : (PublicPacketWork.measure L data red).1 = pre ++ v::tail) :
    ∃ h initial idx dst sat,
      PublicPacketWork.prepareTiles L data red = .ok (h,initial) ∧ ranks L h = .ok idx ∧
      gridPrefix L h data initial (JPEG2000.Decode.centeredTile L h data red) (·.saturated)
        (fun arr t => JPEG2000.NativeOutput.writeTile L h.siz red t.layout t.coding arr t.sources)
        idx pre.length = .ok (dst,v.passesBefore,sat,v.cursor) ∧ v.tile = pre.length ∧
      dst.map Spec.NativeOutput.backingBytes = initial.map Spec.NativeOutput.backingBytes ∧
      (dst.toList.map Spec.NativeOutput.backingBytes).sum ≤ 8*L.maxWorkSamples := by
  cases entry : PublicPacketWork.prepareTiles L data red with
  | error => simp [PublicPacketWork.measure,entry,before] at trace
  | ok pair =>
    obtain ⟨h,initial⟩ := pair
    simp only [PublicPacketWork.measure,entry,before,measureTiles_finish,afterRun] at trace
    obtain ⟨idx,dst,sat,index,before,number,bytes⟩ := prefix_destination
      (fun ds => ds.map Spec.NativeOutput.backingBytes = initial.map Spec.NativeOutput.backingBytes)
      rfl (fun _ _ _ old wrote => (write_backing wrote).trans old) trace
    refine ⟨h,initial,idx,dst,sat,rfl,index,before,number,bytes,?_⟩
    have lengths := congrArg (fun (a : Array Nat) => a.toList.sum) bytes
    simp only [Array.toList_map] at lengths
    exact lengths ▸ (Spec.NativeOutput.allocOutput_bounds (prepared entry).2).2.2

/-- Contribution descriptors and total tile records retained through the body of an attempted packet. -/
def BodyStorage (L : Limits) (c : Coding) (base : Array (Array Nat)) (same : Bool)
    (s : LoopState) (p : PacketId) : Prop :=
  let j := (base.getD p.comp #[]).getD p.res 0 + p.prec
  ∀ st, s.precs[j]? = some st → ∀ pre cs body,
    SegmentHistory.packetBody L c same s p st = .ok (pre,cs,body) →
    ∀ xs : List Contribution, xs <+: cs.toList → ∀ z,
      forIn xs (pre.bands,body) Tier2Equiv.bodyBody = .ok z →
      weight cs ≤ 3*(L.maxCodeBlocks*(1+L.maxPassesPerCodeBlock)) ∧
      tileRecords {s with precs := s.precs.setIfInBounds j {pre with bands := z.1}} ≤
        SegmentHistory.segmentLimit L

private theorem bodyStorage {L : Limits} {c base same s p}
    (shape : StatesValid L s) (records : tileRecords s ≤ s.seq*recordGrowth L)
    (seq : s.seq < L.maxPackets) : BodyStorage L c base same s p := by
  intro st get pre cs body bodyOk xs sub z read
  unfold SegmentHistory.packetBody at bodyOk
  obtain ⟨⟨_,_⟩,_,tail⟩ := Tier2Equiv.bind_ok bodyOk
  obtain ⟨⟨flag,br⟩,_,tail⟩ := Tier2Equiv.bind_ok tail
  obtain ⟨⟨next,table,bits⟩,header,tail⟩ := Tier2Equiv.bind_ok tail
  obtain ⟨_,_,tail⟩ := Tier2Equiv.bind_ok tail
  obtain ⟨_,_,last⟩ := Tier2Equiv.bind_ok tail
  cases last
  exact partial_body_store shape records seq get header sub read

/-- Every attempted public event identifies its actual state and readers
before the callback. Even on body rejection the contribution table, partially
updated tile and gathered buffer obey the explicit storage bounds. -/
theorem attempted_storage (L : Limits) (data : ByteArray) (red : Nat) {v p a}
    (tile : v ∈ (PublicPacketWork.measure L data red).1)
    (event : (p,a) ∈ v.packets) (entered : a.attempted = true) :
    ∃ h tp hs g c precs base spans buf parts pre tail s,
      Header.parse L data = .ok h ∧ presentAt h v.tile v.cursor = some tp ∧
      Layout.ofHeader h tp.index = .ok (g,c) ∧ initPrecincts L g = .ok (precs,base,spans) ∧
      tileData data tp.tile = .ok (buf,parts) ∧ buf.size ≤ L.maxTilePartsPerTile*data.size ∧
      parts.length ≤ L.maxTilePartsPerTile ∧ schedule g [] (volumes g c.progression c.poc) = pre ++ p::tail ∧
      let same := (hs.map HeaderStream.bytes).isNone
      let f := packetStep L c base same v.passesBefore
      pre.foldlM (dispatch f) (firstState precs buf hs) = .ok s ∧
      s.body.data = buf ∧ s.body.stop = buf.size ∧
      (∀ b, hs = some b → s.hdr.data = b.bytes ∧ b.bytes.size ≤ packedCap L data.size b) ∧
      tileRecords s ≤ SegmentHistory.segmentLimit L ∧
      BodyStorage L c base same s p.packet ∧
      ∃ shape layer, let call := attempt L c base same v.passesBefore s p.packet shape layer
        call.result = f s p.packet ∧ agrees s a call.result ∧ call.work ≤ attemptBudget L := by
  obtain ⟨h,tp,hs,hp,sel,partsCap,packed,obs⟩ :=
    (decode_attempts L data red).2.2 v tile p a event entered
  obtain ⟨g,c,ps,base,spans,buf,parts,pre,tail,s,layout,init,input,size,sched,run,_,
    records,seq,bufEq,stopEq,headers,shape,layer,action,erase,work⟩ := obs
  have sizeCap := Nat.le_trans size (Nat.mul_le_mul_right _ partsCap)
  have len := ((HeaderWork.tileData_copy_charge data tp.tile).2.2 buf parts input).2
  exact ⟨h,tp,hs,g,c,ps,base,spans,buf,parts,pre,tail,s,hp,sel,layout,init,input,sizeCap,
    len ▸ partsCap,sched,run,bufEq,stopEq,(fun b eq => ⟨(headers b eq).1,packed b eq⟩),
    Nat.le_trans records (Nat.mul_le_mul_right _ (Nat.le_of_lt seq)),
    bodyStorage shape records seq,shape,layer,erase,action,work⟩

private def visitWork (L : Limits) (h : Header) (data : ByteArray) (idx : Array (Array Nat))
    (v : TileVisit) :=
  match presentAt h v.tile v.cursor with
  | none => 0
  | some tp => match headerStreamAt h data tp (idx.getD v.cursor #[]) with
    | .error _ => 0
    | .ok hs => (packetMeter L h data tp hs v.passesBefore).2 +
      bodyCharge (SegmentHistory.bodyHistory L h data tp hs v.passesBefore)

open JPEG2000.TileDispatch (Spatial)

/-- Successful predecessor rasters and the outcome of the next callback. On
a failed component the rasters already accumulated by the production map are
still available for accounting. -/
def componentHistory {n : Nat} (f : Fin n → Except Error Spatial) :
    (k j : Nat) → k+j = n → List (Fin n × Spatial) × Except Error Unit
  | 0, _, _ => ([],.ok ())
  | k+1, j, _ =>
    match f ⟨j,by omega⟩ with
    | .error e => ([],.error e)
    | .ok v =>
      let rest := componentHistory f k (j+1) (by omega)
      ((⟨j,by omega⟩,v)::rest.1,rest.2)

private theorem history_spec {α : Type} (xs : Array α) (f : Fin xs.size → Except Error Spatial)
    (k j : Nat) (len : k+j = xs.size) (acc : Array Spatial) :
    let hist := componentHistory f k j len
    (hist.1.map fun e => e.1.val).Sublist (List.range' j k) ∧
    (∀ e ∈ hist.1, f e.1 = .ok e.2) ∧
    Array.mapFinIdxM.map xs (fun i _ hi => f ⟨i,hi⟩) k j len acc =
      (hist.2.map fun _ => acc ++ (hist.1.map Prod.snd).toArray) := by
  induction k generalizing j acc with
  | zero => simp [componentHistory,Array.mapFinIdxM.map,Except.map,pure,Except.pure]
  | succ k ih =>
    simp only [componentHistory,Array.mapFinIdxM.map,List.range'_succ]
    cases call : f ⟨j,by omega⟩ with
    | error e => simp [Except.map,bind,Except.bind]
    | ok v =>
      obtain ⟨order,calls,eq⟩ := ih (j+1) (by omega) (acc.push v)
      refine ⟨List.Sublist.cons_cons j order,?_,?_⟩
      · intro e hit
        rcases List.mem_cons.mp hit with rfl | tail
        · exact call
        · exact calls _ tail
      · simp only [bind,Except.bind,eq]
        cases (componentHistory f k (j+1) (by omega)).2 <;>
          simp [Except.map]

private theorem packet_origin {L : Limits} {h : Header} {data : ByteArray}
    {idx t j pb a} (hp : Header.parse L data = .ok h)
    (store : SegmentHistory.packetStore L h data idx t j pb = .ok a) :
    ∃ b, TileDispatch.Packets L h data t a b := by
  unfold SegmentHistory.packetStore at store
  split at store
  · cases store; exact ⟨none,.absent⟩
  rename_i tp sel
  obtain ⟨hs,_,tail⟩ := Tier2Equiv.bind_ok store
  obtain ⟨out,decoded,ret⟩ := Tier2Equiv.bind_ok tail
  cases ret
  have index : tp.index = t := by
    unfold presentAt at sel
    split at sel <;> try contradiction
    split at sel <;> cases sel
    assumption
  have equiv := Tier2Equiv.decodeWithStream_sim L h data tp hs pb
    (fun _ _ layout => Tier2Equiv.ofHeader_wf (Equiv.parse_dxdy hp) layout)
  rw [decoded] at equiv
  cases ref : Spec.Tier2.decodeWithStream L h data tp hs pb with
  | error => rw [ref] at equiv; contradiction
  | ok b => exact ⟨some b,.present index decoded ref⟩

/-- Gathered bytes, retained segment descriptors, the two bordered compact
arrays and the signed-magnitude payload of a decoded wide block. The preflight
postcondition applies even when decoding the block later fails. -/
def BlockStorage (L : Limits) (data : ByteArray) (g : Layout) (a : Option TileCodeBlocks) : Prop :=
  ∀ i : Fin g.numComps, ∀ r, ∀ pr ∈ (AssemblyCost.selected a i).getD r #[],
    ∀ bo ∈ pr.bands, ∀ cb ∈ bo.blocks,
    let params := (g.comp i).params
    let input := Assemble.tier1Input data cb
    input.2.size ≤ SegmentHistory.segmentLimit L ∧
    (if cb.segments.all (·.ranges.size ≤ 1) then input = (data,cb.segments.map Assemble.directSeg)
     else let k := SegmentHistory.rangeLimit L
          let run := HeaderWork.chargedBlock data cb.segments.toList (ByteArray.empty,#[])
          run.1 = input ∧ input.1.size ≤ k*data.size ∧
            run.2 ≤ (2*k+SegmentHistory.segmentLimit L)*(k*data.size)) ∧
    (∀ wide kept, (Tier1Work.preflight wide input.1 input.2 cb.geom.rect.width cb.geom.rect.height
      (JPEG2000.Tier1.Style.ofByte params.cbStyle) ((bandMb params r bo.band + params.roiShift) -
        (if cb.included then cb.zeroBitPlanes else 0))).1 = .ok kept →
        kept.size ≤ SegmentHistory.segmentLimit L ∧ cb.geom.rect.width*cb.geom.rect.height ≤ 4096 ∧
          2*((cb.geom.rect.width+2)*(cb.geom.rect.height+2)) ≤ 16392) ∧
    (∀ o, JPEG2000.ReversibleDispatch.checkedBlock data params r bo.band cb = .ok o →
      o.plane.data.size ≤ 4*4096 ∧ o.flags.size ≤ 8196) ∧
    ∀ cs, JPEG2000.WideAssembly.decodeBlock data params r bo.band cb = .ok cs →
      cs.size ≤ 4096 ∧ (∀ z ∈ cs, ReconstructionCost.blockCellBytes z ≤ 43) ∧
        (cs.toList.map ReconstructionCost.blockCellBytes).sum ≤ 43*4096

/-- A packed Mallat allocation, either at creation or after a block placement
at the component rectangle. Saturation can send this component to the wide path. -/
inductive PackedBuffer (L : Limits) (rc : Rect) : Plane → Prop where
  | zero {p} (ok : Plane.zeroChecked L Assemble.loc rc.width rc.height = .ok p) : PackedBuffer L rc p
  | write {dst nl r b cb q F block p fits}
      (ok : JPEG2000.Quant.dequantBlock dst rc nl r b cb q F block = .ok (p,fits)) : PackedBuffer L rc p

/-- Every wide assembly prefix begins with the checked zero plane and extends
only after a decoded block has been placed successfully. -/
inductive WideBuffer (L : Limits) (data : ByteArray) (rc : Rect) (params : CompParams)
    (depth red F : Nat) : JPEG2000.WideQuant.Plane → Prop where
  | zero {p} (ok : JPEG2000.WideQuant.zeroChecked L rc = .ok p) : WideBuffer L data rc params depth red F p
  | write {dst r b cb cs p} (old : WideBuffer L data rc params depth red F dst)
      (decoded : JPEG2000.WideAssembly.decodeBlock data params r b cb = .ok cs)
      (placed : JPEG2000.WideQuant.dequantBlock L dst params depth red r b cb.geom.rect F cs = .ok p) :
      WideBuffer L data rc params depth red F p

/-- Simultaneous earlier component rasters, packed and wide Mallat buffers and
all fresh transform payload. The only conditions on buffers are their checked
construction steps. A failed component can retain both assembly attempts. -/
def ComponentStorage (L : Limits) (h : Header) (data : ByteArray) (g : Layout) (c : Coding)
    (a : Option TileCodeBlocks) (red : Nat) (done : List (Fin g.numComps × Spatial)) : Prop :=
  ∀ i : Fin g.numComps, ∀ (packed : Option Plane) (wide : Option JPEG2000.WideQuant.Plane),
    let tc := g.comp i
    let rc := Assemble.reduceRect tc.rect red
    let d := (h.siz.components.getD i default).depth.toNat
    let F := Assemble.fracBitsOf h.siz (c.mctApplies h.siz) i
    let payload : ReconstructionCost.Prices := ⟨0,0,0,1,0⟩
    (∀ p, packed = some p → PackedBuffer L rc p) →
    (∀ p, wide = some p → WideBuffer L data rc tc.params d red F p) →
    ∃ bs : List TileColorPlacement.Backing,
      bs.map (·.source) = (done.take i.val).map (fun e => e.2.source) ∧
      (bs.map (·.logicalBytes)).sum + (packed.map (·.data.size)).getD 0 +
        (wide.map (fun q => (q.samples.toArray.toList.map TileColorPlacement.signedBytes).sum)).getD 0 +
        ReconstructionCost.transforms payload L data tc d F red (AssemblyCost.selected a i) ≤
        (4+TileColorPlacement.componentBytes L+4+47)*L.maxWorkSamples + ReconstructionCost.transformBudget payload L

private theorem component_storage {L : Limits} {h : Header} {data : ByteArray} {g c t red a b}
    (hp : Header.parse L data = .ok h) (layout : Layout.ofHeader h t = .ok (g,c))
    (origin : TileDispatch.Packets L h data t a b) (admitted : tileCells g red ≤ L.maxWorkSamples)
    (done : List (Fin g.numComps × Spatial))
    (ord : (done.map fun e => e.1.val).Sublist (List.range' 0 g.numComps))
    (calls : ∀ e ∈ done, JPEG2000.TileDispatch.component L h data g c a e.1 red = .ok e.2) :
    ComponentStorage L h data g c a red done := by
  intro i packed wide
  dsimp only
  intro hpck hwide
  have below := List.take_sublist i.val done
  apply ReconstructionCost.live_workspace hp layout origin admitted (done.take i.val)
    ((below.map _).trans ord) (fun e he => calls e (below.subset he)) i packed wide
  · intro p hit
    cases hpck p hit with
    | zero ok =>
      unfold Plane.zeroChecked at ok
      obtain ⟨_,_,ok⟩ := Tier2Equiv.bind_ok ok
      cases ok
      rfl
    | write ok =>
      have bytes := (AssemblyCost.packed_storage ok).2.2
      rw [p.size_eq] at bytes
      change p.width*p.height = _
      change 4*(p.width*p.height) = 4*_ at bytes
      unfold AssemblyCost.planeArea
      omega
  · intro p hit
    have bound := ReconstructionCost.mallat_prefix (red := red) hp layout i
    have reached := hwide p hit
    clear hit hwide
    induction reached with
    | zero ok => exact bound.1 _ ok
    | write _ decoded placed ih => exact bound.2 _ _ _ _ _ _ ih decoded placed

/-- Live spatial payload at the exact component prefix, plus the predecessors
captured by a lazy native colour reader when the tile reaches placement. -/
def ReconstructionStorage (L : Limits) (h : Header) (data : ByteArray) (red : Nat)
    (idx : Array (Array Nat)) (v : TileVisit) : Prop :=
  match SegmentHistory.packetStore L h data idx v.tile v.cursor v.passesBefore with
  | .error _ => True
  | .ok a => match Layout.ofHeader h v.tile with
    | .error _ => True
    | .ok (g,c) =>
      if Resources.tileCells g red ≤ L.maxWorkSamples then
        let f := fun i => JPEG2000.TileDispatch.component L h data g c a i red
        let hist := componentHistory f g.numComps 0 rfl
        let ps := (hist.1.map Prod.snd).toArray
        ReconstructionCost.StoreCaps.Holds (ReconstructionCost.storeCaps L) g a ∧
        BlockStorage L data g a ∧
        ComponentStorage L h data g c a red hist.1 ∧
        (g.comps.mapFinIdxM (fun i _ hi => f ⟨i,hi⟩)) = hist.2.map (fun _ => ps) ∧
        (∃ bs : List TileColorPlacement.Backing,
          bs.map (·.source) = hist.1.map (fun e => e.2.source) ∧
          (bs.map (·.logicalBytes)).sum ≤ (4+TileColorPlacement.componentBytes L)*L.maxWorkSamples) ∧
        ∀ out, JPEG2000.Decode.centeredTile L h data red v.tile a = .ok out →
          ∃ (planes : Array Spatial) (backing : List TileColorPlacement.Backing),
            (TileColorPlacement.preColourMeter (TileColorPlacement.componentBytes L)
              L h data out.layout out.coding a red).1 = .ok planes ∧
            backing.map (·.source) = planes.toList.map JPEG2000.TileDispatch.Spatial.source ∧
            (backing.map (·.logicalBytes)).sum ≤ (4+TileColorPlacement.componentBytes L)*L.maxWorkSamples ∧
            ∀ s ∈ out.sources, TileColorPlacement.Reader planes s
      else True

/-- Public byte inputs determine the store, layout, consumed component
prefix, signed-magnitude payload and lazy readers, including a tile that fails
after retaining earlier components. -/
theorem reconstruction_storage (L : Limits) (data : ByteArray) (red : Nat) (v : TileVisit)
    (hit : v ∈ (PublicPacketWork.measure L data red).1) :
    ∃ h dst idx, PublicPacketWork.prepareTiles L data red = .ok (h,dst) ∧
      ranks L h = .ok idx ∧ ReconstructionStorage L h data red idx v := by
  obtain ⟨h,dst,entry,hp,_,_,idx,index,_⟩ := visited_storage L data red v hit
  refine ⟨h,dst,idx,entry,index,?_⟩
  unfold ReconstructionStorage
  split <;> try trivial
  rename_i a store
  split <;> try trivial
  rename_i g c layout
  split <;> try trivial
  rename_i admitted
  obtain ⟨b,origin⟩ := packet_origin hp store
  let f := fun i => JPEG2000.TileDispatch.component L h data g c a i red
  obtain ⟨ord,calls,eq⟩ := history_spec g.comps f g.numComps 0 rfl #[]
  have caps : (ReconstructionCost.storeCaps L).Holds g a :=
    fun i => SegmentHistory.selected_store_bounds hp store i.val
  refine ⟨caps,?_,component_storage hp layout origin admitted _ ord calls,?_,
    ReconstructionCost.prefix_backing hp layout origin admitted _ ord calls,?_⟩
  · intro i r pr hp' bo hb cb hc
    obtain ⟨n,bytes⟩ := SegmentHistory.selected_block_input hp store i.val r hp' hb hc
    have space := ReconstructionCost.block_workspace hp layout i a _ caps r pr hp' bo hb cb hc
    exact ⟨n,bytes,space.2.2,ReconstructionCost.block_payload hp layout i r bo.band cb⟩
  · simpa only [Array.mapFinIdxM,Array.emptyWithCapacity_eq,Array.empty_append,Layout.numComps,f] using eq
  · exact fun _ ok => TileColorPlacement.centeredTile_backing_bytes hp origin ok

/-- Sum packet setup, gathers, body updates and translations over the actual
public grid prefix. Empty and failing tiles retain their reached charges. -/
def packetStages (L : Limits) (data : ByteArray) (red : Nat) :=
  match PublicPacketWork.prepareTiles L data red with
  | .error _ => 0
  | .ok (h,_) => match ranks L h with
    | .error _ => 0
    | .ok idx => ((PublicPacketWork.measure L data red).1.map (visitWork L h data idx)).sum

private theorem stages_le (L : Limits) (data : ByteArray) (red : Nat) :
    packetStages L data red ≤ (PublicPacketWork.measure L data red).1.length *
      (streamLimit L data.size + bodyLimit L) := by
  unfold packetStages
  split <;> try exact Nat.zero_le _
  rename_i h dst entry
  have hp := (prepared entry).1
  split <;> try exact Nat.zero_le _
  apply sumCap
  intro v hit
  have prior := (visitFacts entry hit).2
  unfold visitWork
  split <;> try exact Nat.zero_le _
  rename_i tp sel
  split <;> try exact Nat.zero_le _
  exact Nat.add_le_add (stream_le hp (SegmentHistory.present_mem sel) ..) (body_le hp tp _ _ prior)

/-- Prices all five reconstruction projections, including allocated arrays,
references, logical sample payload and the widths of arithmetic operands. -/
def prices : ReconstructionCost.Prices := ⟨1,1,1,1,1⟩

private def reconstructionLimit (L : Limits) (n : Nat) :=
  ReconstructionCost.prefixBudget prices L n (ReconstructionCost.storeCaps L) +
    ReconstructionCost.nativeBudget prices L

private def finishCharge : Except Error CodestreamImage → Nat
  | .error _ => 0
  | .ok d => 1 + 2*d.comps.size

private theorem finish_le (L : Limits) (data : ByteArray) (red : Nat) :
    finishCharge (decodeCodestream L data red) ≤ 1 + 2*L.maxComponents := by
  cases eq : decodeCodestream L data red with
  | error => exact Nat.zero_le _
  | ok d =>
    have post := NativeResources.decodeCodestream_resources eq
    obtain ⟨h,hp,tail⟩ := Tier2Equiv.bind_ok (Tier2Equiv.bind_ok eq).choose_spec.2
    have head := (CodestreamDispatch.native_geometry hp eq).1
    have cap := (HeaderWork.parse_storage hp).2.1
    have count := post.geometry.1
    simp only [JPEG2000.NativeOutput.layout,Array.size_map,head] at count
    change h.siz.components.size ≤ _ at cap
    change 1+2*d.comps.size ≤ _
    lia

/-- Logical cost on the ordinary byte input. The header observation includes
the zero-price placement projection. Subtract that same projection from the
reconstruction observation before adding them. One additional full native
backing per placement unit allows a fresh destination on a write. The factor
eight on the header charge allows a UInt64 payload in a parser table slot.
The original byte array is counted once as live input. -/
def measure (L : Limits) (data : ByteArray) (red : Nat) : Except Error CodestreamImage × Nat :=
  let packets := PublicPacketWork.measure L data red
  let recon := ReconstructionCost.measure prices L data red
  let shared := (PublicPacketWork.measurePlacement 0 L data red).2
  let header := HeaderPayload.publicHeaderCharge L data red
  let charge := data.size + 1 + entryAllocation L data red + (header+shared) +
    (recon.2-shared) + 7*header + (GeometryInit.decodeWork L data red).work +
    packetStages L data red + packets.1.length +
    (imagePositions packets.1 + imageTests packets.1) + imageAttempts packets.1*attemptBudget L +
    shared*(8*L.maxWorkSamples) + finishCharge packets.2
  (recon.1,charge)

/-- Explicit budget with a tile count parameter so that callers can retain
the tighter rejecting-prefix bound. Callback reservations charge construction
before a cumulative pass refusal. The header bound retains its placement
allowance as conservative slack. -/
def prefixBudget (L : Limits) (n tiles : Nat) :=
  let header := HeaderPayload.headerBudget L n + HeaderPayload.rankBudget L +
    tiles*(HeaderPayload.selectionBudget L n + placementBudget 0 L)
  n + 1 + allocationBudget L + header +
    tiles*reconstructionLimit L n + 7*header + GeometryInit.geometryBudget L +
    tiles*(streamLimit L n+bodyLimit L) + tiles + tiles*L.maxPackets +
    tiles*L.maxPackets*attemptBudget L + (tiles*placementBudget 0 L)*(8*L.maxWorkSamples) +
    (1+2*L.maxComponents)

/-- Native decoder work and cumulative logical allocation bound as a function
only of caller limits and original byte length. -/
def budget (L : Limits) (n : Nat) := prefixBudget L n L.maxTiles

private theorem prefix_mono (L : Limits) (n : Nat) {k t : Nat} (le : k ≤ t) :
    prefixBudget L n k ≤ prefixBudget L n t := by
  unfold prefixBudget
  repeat' first | exact le | exact Nat.le_refl _ | apply Nat.add_le_add | apply Nat.mul_le_mul

private theorem share_le (L : Limits) (data : ByteArray) (red : Nat) :
    (PublicPacketWork.measurePlacement 0 L data red).2 ≤ (ReconstructionCost.measure prices L data red).2 := by
  unfold ReconstructionCost.measure
  dsimp only
  apply Nat.le_add_left_of_le
  apply Nat.le_add_right_of_le
  apply Nat.le_mul_of_pos_right
  change 0 < 1+1+ReconstructionCost.placementBytes L*1
  omega

/-- The public measure recovers the exact image or first error. The prefix cap
uses the number of actual visited tiles and the closed cap uses only limits
and input size. The shared placement charge occurs once in the stage sum. -/
theorem decode_work (L : Limits) (data : ByteArray) (red : Nat) :
    let m := measure L data red
    let visits := (PublicPacketWork.measure L data red).1
    let shared := (PublicPacketWork.measurePlacement 0 L data red).2
    let recon := (ReconstructionCost.measure prices L data red).2
    m.1 = decodeCodestream L data red ∧
      (HeaderPayload.publicHeaderCharge L data red + shared) + (recon-shared) =
        HeaderPayload.publicHeaderCharge L data red + recon ∧
      m.2 ≤ prefixBudget L data.size visits.length ∧ m.2 ≤ budget L data.size ∧
      ∀ img, m.1 = .ok img → NativeResources.Within L data red img := by
  obtain ⟨erase,reconstruction,_⟩ := ReconstructionCost.public_work prices L data red
  obtain ⟨_,header,_⟩ := HeaderPayload.decode_header_work 0 L data red
  obtain ⟨out,nt,calls,positions,_,_⟩ := PublicPacketWork.decode_packet_work L data red
  obtain ⟨_,geom⟩ := GeometryInit.decode_geometry_work L data red
  have placement := (PublicPacketWork.decode_placement_work 0 L data red).2.1
  have packetCap : imageCharge (PublicPacketWork.measure L data red).1 ≤
      (PublicPacketWork.measure L data red).1.length*L.maxPackets := by
    cases entry : PublicPacketWork.prepareTiles L data red with
    | error => simp [PublicPacketWork.measure,entry,before,imageCharge]
    | ok pair =>
      obtain ⟨h,dst⟩ := pair
      obtain ⟨_,present,_,_,_,_,bound⟩ := trace_bounds (publicTrace entry)
      exact Nat.le_trans bound (Nat.mul_le_mul_right _ present)
  have physical := Nat.le_trans positions packetCap
  have attempts := Nat.mul_le_mul_right (attemptBudget L) (Nat.le_trans calls
    (Nat.le_trans (Nat.le_add_right ..) physical))
  have finish := finish_le L data red
  rw [← out] at finish
  have shared := share_le L data red
  have headerOnly := Nat.le_trans (Nat.le_add_right ..) header
  have prefixCap : (measure L data red).2 ≤
      prefixBudget L data.size (PublicPacketWork.measure L data red).1.length := by
    unfold measure prefixBudget
    dsimp only
    repeat' first
      | exact Nat.le_refl _
      | exact entry_le ..
      | exact header
      | exact Nat.le_trans (Nat.sub_le ..) reconstruction
      | exact Nat.mul_le_mul_left 7 headerOnly
      | exact geom
      | exact stages_le ..
      | exact physical
      | exact attempts
      | exact Nat.mul_le_mul_right _ placement
      | exact finish
      | apply Nat.add_le_add
  refine ⟨erase,by omega,prefixCap,Nat.le_trans prefixCap (prefix_mono L _ nt),?_⟩
  intro img eq
  exact NativeResources.decodeCodestream_resources (erase.symm.trans eq)

end JPEG2000.Spec.Resources.NativeCost
