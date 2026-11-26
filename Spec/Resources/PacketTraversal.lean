import Spec.Resources.PacketPrefix
import Spec.Resources

/-!
# Packet and pass work of the public tile traversal

Plan.md §§3–5, 7 (S2/S3), T.800 A.7.4–5 and B.9–12. Each attempted grid
tile keeps its tile-part cursor, incoming pass count and physical packet log.
This includes omitted tiles, a rejecting tile, and tiles whose packet reads
succeed but whose reconstruction or placement fails. Trace storage belongs
only to the proof model. The public API streams the tiles.
-/

namespace JPEG2000.Spec.Resources.PacketTraversal

open JPEG2000.Header JPEG2000.TilePart JPEG2000.Tier2.Headers JPEG2000.Tier2.Packet

/-- One attempted grid tile, before reconstruction. -/
structure TileVisit where
  tile : Nat
  cursor : Nat
  passesBefore : Nat
  present : Bool
  packets : PacketLog

/-- The tile selected by the public loop at this grid coordinate and tile-part cursor. -/
def presentAt (h : Header) (t j : Nat) : Option TileParams :=
  match h.tiles[j]? with
  | none => none
  | some tp => if tp.index = t then some tp else none

private def chunks (L : Limits) (h : Header) : Except Error (Array (Array Nat)) :=
  if h.ppm.segments.isEmpty then pure #[] else ppmChunkIndex L h

private def storeAt (L : Limits) (h : Header) (data : ByteArray) (idx : Array (Array Nat))
    (j pb : Nat) : Option TileParams → PacketLog × Except Error (Option TileCodeBlocks)
  | none => ([], .ok none)
  | some tp =>
    before (headerStreamAt h data tp (idx.getD j #[])) fun hs =>
      afterRun (measureStream L h data tp hs pb) (fun d => pure (some d))

private abbrev State (P : Type) := P × Nat × Nat × Nat

private def visit {P T : Type} (L : Limits) (h : Header) (data : ByteArray)
    (tile : Nat → Option TileCodeBlocks → Except Error T) (saturated : T → Nat)
    (write : P → T → Except Error P) (idx : Array (Array Nat)) (t : Nat) (s : State P) :
    TileVisit × Except Error (State P) :=
  let (dst, pb, sat, j) := s
  let selected := presentAt h t j
  let r := storeAt L h data idx j pb selected
  (⟨t, j, pb, selected.isSome, r.1⟩, do
    let cb ← r.2
    let out ← tile t cb
    let next ← write dst out
    return (next, pb + (cb.map (·.passes)).getD 0, sat + saturated out, j + selected.isSome.toNat))

private def grid {P : Type} (f : Nat → State P → TileVisit × Except Error (State P)) :
    Nat → Nat → State P → Measured TileVisit (State P)
  | 0, _, s => ([], .ok s)
  | n + 1, t, s =>
    let (v, result) := f t s
    match result with
    | .error e => ([v], .error e)
    | .ok s' =>
      let r := grid f n (t + 1) s'
      (v :: r.1, r.2)

/-- Public traversal with a proof-only packet trace. The grid starts with cursor
and pass count zero; errors at any stage keep precisely the attempted prefix. -/
def measureTiles {P T α : Type} (L : Limits) (h : Header) (data : ByteArray)
    (initial : P) (tile : Nat → Option TileCodeBlocks → Except Error T)
    (saturated : T → Nat) (write : P → T → Except Error P) (finish : P → Nat → α) :
    Measured TileVisit α :=
  before (chunks L h) fun idx =>
    afterRun (grid (visit L h data tile saturated write idx) (numTiles h.siz) 0 (initial, 0, 0, 0))
      (fun s => pure (finish s.1 s.2.2.1))

private theorem grid_erase {P : Type} (f : Nat → State P → TileVisit × Except Error (State P))
    (n t : Nat) (s : State P) :
    (grid f n t s).2 = forIn (List.range' t n) s (fun t s => do return .yield (← (f t s).2)) := by
  induction n generalizing t s with
  | zero => rfl
  | succ n ih =>
    simp only [grid, List.range'_succ, List.forIn_cons]
    obtain ⟨v, r⟩ := f t s
    cases r <;> simp [bind, Except.bind, pure, Except.pure, ih]

private theorem ok_bind {α β : Type} (a : α) (k : α → Except Error β) :
    (Except.ok a >>= k) = k a := rfl

private theorem branch_bind {α β : Type} (c : Prop) [Decidable c]
    (x y : Except Error α) (k : α → Except Error β) :
    (if c then x >>= k else y >>= k) = (if c then x else y) >>= k := by split <;> rfl

private theorem lift_before {log α β : Type} (x : Except Error α) (k : α → Measured log β) :
    (before x k).2 = x >>= fun a => (k a).2 := by cases x <;> rfl

/-- Erasure gives the production traversal, including its exact error and the
arguments to tile reconstruction, placement and finish. -/
theorem measureTiles_erase {P T α : Type} {L : Limits} {h : Header} {data : ByteArray}
    (parsed : Header.parse L data = .ok h) (initial : P) (tile : Nat → Option TileCodeBlocks → Except Error T)
    (saturated : T → Nat) (write : P → T → Except Error P) (finish : P → Nat → α) :
    (measureTiles L h data initial tile saturated write finish).2 =
      JPEG2000.Decode.withTiles L h data initial tile saturated write finish := by
  unfold measureTiles JPEG2000.Decode.withTiles
  dsimp only
  rw [lift_before, branch_bind]
  unfold chunks
  congr 1
  funext idx
  simp only [afterRun, grid_erase, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  congr 1
  congr 1
  funext t s
  obtain ⟨dst, pb, sat, j⟩ := s
  simp only [visit, presentAt]
  cases sel : h.tiles[j]? with
  | none =>
    simp [storeAt, ok_bind]
  | some tp =>
    by_cases ix : tp.index = t
    · simp [ix, storeAt, lift_before, afterRun, measureStream_erase parsed, bind_assoc]
    · simp [ix, storeAt, ok_bind]

/-- The precise source of a visit's log. The public PPM table is built once,
and the stream for this header entry uses the ranks at its incoming cursor.
A missing tile or a failed gather has no packet positions. -/
def Sourced (L : Limits) (h : Header) (data : ByteArray) (v : TileVisit) : Prop :=
  ∃ idx, (if h.ppm.segments.isEmpty then pure #[] else ppmChunkIndex L h) = .ok idx ∧
    v.packets = match presentAt h v.tile v.cursor with
      | none => []
      | some tp => match headerStreamAt h data tp (idx.getD v.cursor #[]) with
        | .error _ => []
        | .ok hs => (measureStream L h data tp hs v.passesBefore).1

/-- Pointwise work and selection facts, with the incoming public cursors. -/
structure VisitWithin (L : Limits) (h : Header) (data : ByteArray) (t j pb : Nat) (v : TileVisit) : Prop where
  index : v.tile = t
  cursor : v.cursor = j
  start : v.passesBefore = pb
  selection : v.present = (presentAt h t j).isSome
  calls : attempts v.packets ≤ v.packets.length
  positions : v.packets.length ≤ charge (v.packets.map Prod.fst)
  cost : charge (v.packets.map Prod.fst) ≤ v.present.toNat * L.maxPackets
  nextCursor : j + v.present.toNat ≤ h.tiles.size
  nextPasses : pb + passSum v.packets ≤ L.maxCodingPasses
  source : Sourced L h data v

private theorem visit_within {P T : Type} {L : Limits} {h : Header} {data : ByteArray}
    (parsed : Header.parse L data = .ok h) (tile : Nat → Option TileCodeBlocks → Except Error T)
    (saturated : T → Nat) (write : P → T → Except Error P) (idx : Array (Array Nat))
    (indexed : chunks L h = .ok idx) (t : Nat) (s : State P) (hj : s.2.2.2 ≤ h.tiles.size) (hp : s.2.1 ≤ L.maxCodingPasses) :
    let r := visit L h data tile saturated write idx t s
    VisitWithin L h data t s.2.2.2 s.2.1 r.1 ∧
      ∀ z, r.2 = .ok z → z.2.1 = s.2.1 + passSum r.1.packets ∧
        z.2.2.2 = s.2.2.2 + r.1.present.toNat := by
  obtain ⟨dst, pb, sat, j⟩ := s
  dsimp only at hj hp
  simp only [visit]
  cases sel : presentAt h t j with
  | none =>
    refine ⟨⟨rfl, rfl, rfl, by rw [sel], Nat.le_refl _, Nat.le_refl _, Nat.zero_le _, hj,
      by simpa [storeAt, passSum] using hp, ⟨idx, indexed, by simp [sel, storeAt]⟩⟩, ?_⟩
    intro z ok
    simp only [storeAt, bind, Except.bind] at ok
    split at ok <;> try contradiction
    split at ok <;> cases ok
    exact ⟨rfl, rfl⟩
  | some tp =>
    have lt : j < h.tiles.size := by
      unfold presentAt at sel
      cases e : h.tiles[j]? with
      | none => simp [e] at sel
      | some d => exact (Array.getElem?_eq_some_iff.1 e).1
    simp only [storeAt]
    cases source : headerStreamAt h data tp (idx.getD j #[]) with
    | error =>
      exact ⟨⟨rfl, rfl, rfl, by rw [sel], Nat.le_refl _, Nat.le_refl _, Nat.zero_le _, lt,
        by simpa [before, passSum] using hp, ⟨idx, indexed, by simp only [sel, source, before]⟩⟩,
        by intro z hz; cases hz⟩
    | ok hs =>
      obtain ⟨calls, positions, cost, next, result⟩ := measureStream_bounds parsed tp hs pb hp
      refine ⟨⟨rfl, rfl, rfl, by rw [sel], calls, positions,
        by simpa [before, afterRun] using cost, lt, next,
        ⟨idx, indexed, by simp only [sel, source, before, afterRun]⟩⟩, ?_⟩
      intro z ok
      dsimp only [before, afterRun] at ok ⊢
      cases r : (measureStream L h data tp hs pb).2 with
      | error => simp [r, bind, Except.bind] at ok
      | ok d =>
        obtain ⟨passes, _⟩ := result d r
        simp only [r, bind, Except.bind, pure, Except.pure] at ok
        split at ok <;> try contradiction
        split at ok <;> cases ok
        exact ⟨by simp [passes], rfl⟩

/-- Number of tile-header entries selected, including a selection that rejects. -/
def presentCount (vs : List TileVisit) : Nat := (vs.map (fun v => v.present.toNat)).sum

/-- Admitted coding passes across the whole attempted prefix. -/
def imagePasses (vs : List TileVisit) : Nat := (vs.map (fun v => passSum v.packets)).sum

/-- Physical positions reached across tiles, counting duplicate positions across POC volumes. -/
def imagePositions (vs : List TileVisit) : Nat := (vs.map (fun v => v.packets.length)).sum

/-- Attempted first-occurrence callbacks across tiles. -/
def imageAttempts (vs : List TileVisit) : Nat := (vs.map (fun v => attempts v.packets)).sum

/-- Actual short-circuit membership tests at the physical positions visited. -/
def imageTests (vs : List TileVisit) : Nat :=
  (vs.map (fun v => membershipTests (v.packets.map Prod.fst))).sum

/-- Physical visitation and capacity for the membership tests at each visited position. -/
def imageCharge (vs : List TileVisit) : Nat := (vs.map (fun v => charge (v.packets.map Prod.fst))).sum

private theorem physical_cost (vs : List TileVisit) :
    imagePositions vs + imageTests vs ≤ imageCharge vs := by
  induction vs with
  | nil => exact Nat.le_refl _
  | cons v vs ih =>
    have localCost := visits_tests_le_charge (v.packets.map Prod.fst)
    simp only [imagePositions, imageTests, imageCharge, List.map_cons, List.length_map, List.sum_cons] at *
    omega

/-- Consecutive grid visits with their actual tile indices, pass sums and header cursors. -/
inductive Trace (L : Limits) (h : Header) (data : ByteArray) : Nat → Nat → Nat → List TileVisit → Prop where
  | stop {t j pb} (cursor : j ≤ h.tiles.size) (passes : pb ≤ L.maxCodingPasses) :
      Trace L h data t j pb []
  | next {t j pb v vs} (visit : VisitWithin L h data t j pb v)
      (rest : Trace L h data (t + 1) (j + v.present.toNat) (pb + passSum v.packets) vs) :
      Trace L h data t j pb (v :: vs)

/-- At any attempted tile the public pass input is the sum of the preceding
accepted packet contributions, and the PPM/PPT cursor is the number of preceding
present tiles. The source field identifies this visit's actual packet log. -/
theorem trace_visit {L : Limits} {h : Header} {data : ByteArray} {t j pb pre v vs}
    (tr : Trace L h data t j pb (pre ++ v :: vs)) :
    VisitWithin L h data (t + pre.length) (j + presentCount pre) (pb + imagePasses pre) v := by
  induction pre generalizing t j pb with
  | nil =>
    cases tr with
    | next hv _ => exact hv
  | cons w pre ih =>
    cases tr with
    | next _ tail =>
      simpa [presentCount, imagePasses, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih tail

/-- Sum the per-tile limits without resetting the pass budget. Header indices increase
only for present tiles. The physical POC charge includes the failed callback on rejection. -/
theorem trace_bounds {L : Limits} {h : Header} {data : ByteArray} {t j pb vs} (tr : Trace L h data t j pb vs) :
    vs.map TileVisit.tile = List.range' t vs.length ∧
    presentCount vs ≤ vs.length ∧ j + presentCount vs ≤ h.tiles.size ∧
    pb + imagePasses vs ≤ L.maxCodingPasses ∧
    imageAttempts vs ≤ imagePositions vs ∧ imagePositions vs ≤ imageCharge vs ∧
    imageCharge vs ≤ presentCount vs * L.maxPackets := by
  induction tr with
  | stop hj hp => simpa [presentCount, imagePasses, imageAttempts, imagePositions, imageCharge]
                    using And.intro hj hp
  | @next t j pb v vs hv _ ih =>
    obtain ⟨indices, count, cursor, passes, calls, pos, cost⟩ := ih
    have localCalls := hv.calls
    have localPositions := hv.positions
    have localCost := hv.cost
    have bit : v.present.toNat ≤ 1 := by cases v.present <;> decide
    simp only [presentCount, imagePasses, imageAttempts, imagePositions, imageCharge,
      List.map_cons, List.sum_cons, List.length_cons, List.range'_succ, hv.index, indices,
      Nat.add_mul] at *
    exact ⟨trivial, by omega, by omega, by omega, by omega, by omega, by omega⟩

private theorem grid_trace {P T : Type} {L : Limits} {h : Header} {data : ByteArray}
    (parsed : Header.parse L data = .ok h) (tile : Nat → Option TileCodeBlocks → Except Error T)
    (saturated : T → Nat) (write : P → T → Except Error P) (idx : Array (Array Nat)) (indexed : chunks L h = .ok idx)
    (n t : Nat) (s : State P) (hj : s.2.2.2 ≤ h.tiles.size) (hp : s.2.1 ≤ L.maxCodingPasses) :
    let r := grid (visit L h data tile saturated write idx) n t s
    Trace L h data t s.2.2.2 s.2.1 r.1 ∧ r.1.length ≤ n ∧
      ∀ z, r.2 = .ok z → r.1.length = n ∧
        z.2.1 = s.2.1 + imagePasses r.1 ∧ z.2.2.2 = s.2.2.2 + presentCount r.1 := by
  induction n generalizing t s with
  | zero =>
    exact ⟨.stop hj hp, Nat.le_refl _, fun z e => by cases e; exact ⟨rfl, rfl, rfl⟩⟩
  | succ n ih =>
    obtain ⟨hv, next⟩ := visit_within parsed tile saturated write idx indexed t s hj hp
    generalize eq : visit L h data tile saturated write idx t s = pair at hv next ⊢
    obtain ⟨v, result⟩ := pair
    simp only [grid, eq]
    cases result with
    | error err => exact ⟨.next hv (.stop hv.nextCursor hv.nextPasses), by simp, by intro _ e; cases e⟩
    | ok a =>
      obtain ⟨pa, ja⟩ := next a rfl
      obtain ⟨tr, len, done⟩ := ih (t + 1) a (ja ▸ hv.nextCursor) (pa ▸ hv.nextPasses)
      rw [ja, pa] at tr
      refine ⟨.next hv tr, Nat.succ_le_succ len, ?_⟩
      intro z ok
      obtain ⟨sz, pz, jz⟩ := done z ok
      refine ⟨congrArg Nat.succ sz, ?_, ?_⟩
      · simpa [imagePasses, pa, Nat.add_assoc] using pz
      · simpa [presentCount, ja, Nat.add_assoc] using jz

/-- Measured result before the pure finish callback. On success the tuple contains the
destination, cumulative passes, saturation and final header cursor used by the public loop. -/
def measureGrid {P T : Type} (L : Limits) (h : Header) (data : ByteArray) (initial : P)
    (tile : Nat → Option TileCodeBlocks → Except Error T) (saturated : T → Nat)
    (write : P → T → Except Error P) : Measured TileVisit (P × Nat × Nat × Nat) :=
  before (chunks L h) fun idx =>
    grid (visit L h data tile saturated write idx) (numTiles h.siz) 0 (initial, 0, 0, 0)

/-- The public result consumes the measured final destination and saturation; the counters
and trace can be dropped on both success and failure. -/
theorem measureTiles_finish {P T α : Type} (L : Limits) (h : Header) (data : ByteArray) (initial : P)
    (tile : Nat → Option TileCodeBlocks → Except Error T) (saturated : T → Nat)
    (write : P → T → Except Error P) (finish : P → Nat → α) :
    measureTiles L h data initial tile saturated write finish =
      afterRun (measureGrid L h data initial tile saturated write)
        (fun s => pure (finish s.1 s.2.2.1)) := by
  unfold measureTiles measureGrid
  cases chunks L h <;> rfl

/-- At the initial tile both counters are zero. The end counters on success equal the
actual packet pass sum and number of present tiles. On rejection the trace stops at or
before the final grid tile and includes all admitted packet passes of the rejecting tile. -/
theorem measureGrid_trace {P T : Type} {L : Limits} {h : Header} {data : ByteArray}
    (parsed : Header.parse L data = .ok h) (initial : P) (tile : Nat → Option TileCodeBlocks → Except Error T)
    (saturated : T → Nat) (write : P → T → Except Error P) :
    let r := measureGrid L h data initial tile saturated write
    Trace L h data 0 0 0 r.1 ∧ r.1.length ≤ numTiles h.siz ∧
      ∀ z, r.2 = .ok z → r.1.length = numTiles h.siz ∧ z.2.1 = imagePasses r.1 ∧
        z.2.2.2 = presentCount r.1 := by
  unfold measureGrid
  cases indexed : chunks L h with
  | error => exact ⟨.stop (Nat.zero_le _) (Nat.zero_le _), Nat.zero_le _, by intro _ e; cases e⟩
  | ok idx =>
    simpa only [before, Nat.zero_add] using
      grid_trace parsed tile saturated write idx indexed (numTiles h.siz) 0 (initial, 0, 0, 0)
        (Nat.zero_le _) (Nat.zero_le _)

/-- Whole-image work in tile, packet-position, previous-volume-test and admitted-pass
units for the ordinary public traversal, for every finish result and every early rejection. -/
theorem measureTiles_bounds {P T α : Type} {L : Limits} {h : Header} {data : ByteArray}
    (parsed : Header.parse L data = .ok h) (initial : P) (tile : Nat → Option TileCodeBlocks → Except Error T)
    (saturated : T → Nat) (write : P → T → Except Error P) (finish : P → Nat → α) :
    let vs := (measureTiles L h data initial tile saturated write finish).1
    vs.map TileVisit.tile = List.range vs.length ∧ vs.length ≤ numTiles h.siz ∧
      vs.length ≤ L.maxTiles ∧ presentCount vs ≤ min vs.length h.tiles.size ∧
      imageAttempts vs ≤ imagePositions vs ∧ imagePositions vs + imageTests vs ≤ imageCharge vs ∧
      imageCharge vs ≤ presentCount vs * L.maxPackets ∧ imageCharge vs ≤ L.maxTiles * L.maxPackets ∧
      imagePasses vs ≤ L.maxCodingPasses := by
  rw [measureTiles_finish]
  dsimp only [afterRun]
  obtain ⟨tr, len, _⟩ := measureGrid_trace parsed initial tile saturated write
  obtain ⟨ids, present, cursor, passes, calls, _, cost⟩ := trace_bounds tr
  have tiles : numTiles h.siz ≤ L.maxTiles := (parse_within parsed).2.2.1.2.2.2.1
  have total := Nat.le_trans len tiles
  exact ⟨by simpa [List.range_eq_range'] using ids, len, total, Nat.le_min.mpr ⟨present, by simpa using cursor⟩,
    calls, physical_cost _, cost, Nat.le_trans cost (Nat.mul_le_mul_right _ (Nat.le_trans present total)), by simpa using passes⟩

end JPEG2000.Spec.Resources.PacketTraversal
