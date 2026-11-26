import Spec.Resources.DiagnosticBox
import Spec.Resources.DiagnosticPacket

/-!
# Diagnostics of the native tile traversal (Plan.md §§3–5, 7, S3)

T.800 A.7.4–A.7.5, B.2–B.3, B.9–B.12, F.3 and G.1–G.3. The shared
rank check precedes the grid. Each entered tile consumes its packet store,
reconstructs centred sources and writes them into the preceding destination.
The initial reduction and header stages precede this trace. In particular
`DiagnosticBox.public_admission_excess` handles the caller-owned reduction.
-/

namespace JPEG2000.Spec.Resources.DiagnosticReconstruction

open JPEG2000.Header JPEG2000.TilePart JPEG2000.Progression JPEG2000.Tier2.Headers JPEG2000.Tier2.Packet
open PacketTraversal DiagnosticCost DiagnosticPacket

/-- Native component destinations carried from allocation through successful writes. -/
abbrev Destination := Array JPEG2000.NativeOutput.OutputComponent
private abbrev GridState := Destination × Nat × Nat × Nat

/-- Numeric cap and message allowances for the three independent native callbacks.
Each allowance is a function of public limits and input byte length. -/
structure Allowances where
  scalar : Limits → Nat → Nat
  allocation : Limits → Nat → Nat
  tile : Limits → Nat → Nat
  placement : Limits → Nat → Nat

/-- The exact success prefix required by the reconstruction and placement callbacks. -/
structure Reached (L : Limits) (d : ByteArray) (red : Nat) (h : Header) (initial : Destination)
    (idx : Array (Array Nat)) (v : TileVisit) (cb : Option TileCodeBlocks) (g : Layout) (c : Coding) : Prop where
  hit : v ∈ (PublicPacketWork.measure L d red).1
  prepared : PublicPacketWork.prepareTiles L d red = .ok (h,initial)
  rank : NativeCost.ranks L h = .ok idx
  store : SegmentHistory.packetStore L h d idx v.tile v.cursor v.passesBefore = .ok cb
  layout : Layout.ofHeader h v.tile = .ok (g,c)

/-- Destination and counters immediately before grid entry `n`. -/
def prefixState (L : Limits) (h : Header) (d : ByteArray) (red : Nat) (initial : Destination)
    (idx : Array (Array Nat)) (n : Nat) :=
  gridPrefix L h d initial (JPEG2000.Decode.centeredTile L h d red) (·.saturated)
    (fun dst t => JPEG2000.NativeOutput.writeTile L h.siz red t.layout t.coding dst t.sources) idx n

/-- Each continuation sees the successful arguments of the real caller. Placement
also receives the grid split, incoming state, backing bound and exact successful
source array. Callback traces include eager and discarded constructions on success. -/
structure Callbacks (K : Allowances) (L : Limits) (d : ByteArray) (red : Nat) where
  allocation : ∀ {h}, red ≤ L.maxDecompLevels → Header.parse L d = .ok h →
    DiagnosticCost.Trace (K.scalar L d.size) (JPEG2000.NativeOutput.allocOutput L h.siz red) (K.allocation L d.size)
  tile : ∀ {h initial idx v cb g c}, Reached L d red h initial idx v cb g c →
    DiagnosticCost.Trace (K.scalar L d.size) (JPEG2000.TileDispatch.tile L h d g c cb red) (K.tile L d.size)
  placement : ∀ {h initial idx v cb g c dst sat sources} {pre tail : List TileVisit},
    Reached L d red h initial idx v cb g c →
    (PublicPacketWork.measure L d red).1 = pre ++ v :: tail → v.tile = pre.length →
    prefixState L h d red initial idx pre.length = .ok (dst,v.passesBefore,sat,v.cursor) →
    dst.map Spec.NativeOutput.backingBytes = initial.map Spec.NativeOutput.backingBytes →
    (dst.toList.map Spec.NativeOutput.backingBytes).sum ≤ 8*L.maxWorkSamples →
    JPEG2000.TileDispatch.tile L h d g c cb red = .ok sources →
    DiagnosticCost.Trace (K.scalar L d.size) (JPEG2000.NativeOutput.writeTile L h.siz red g c dst sources)
      (K.placement L d.size)

/-- Under a successful geometry lookup, a centred callback and its source-array
callback return the same refusals. Keep the centred trace's ordered trees when
supplying the post-geometry tile field of `Callbacks`. -/
def tileTraceOfCentered {L : Limits} {h : Header} {d : ByteArray} {red t cb g c cap k}
    (layout : Layout.ofHeader h t = .ok (g,c))
    (tr : DiagnosticCost.Trace cap (JPEG2000.Decode.centeredTile L h d red t cb) k) :
    DiagnosticCost.Trace cap (JPEG2000.TileDispatch.tile L h d g c cb red) k where
  messages := tr.messages
  countBound := tr.countBound
  origin := fun e bad => tr.origin e (by
    simp only [JPEG2000.Decode.centeredTile,layout,bind,Except.bind,bad])

/-- Common cap for the packet records and reconstruction continuations. -/
def scalarCap (K : Allowances) (L : Limits) (n : Nat) := max (tileCap L n) (K.scalar L n)

/-- Textual packet records carry their original interpolation trees. Typed
records have no constructed string and are checked separately by trace origin. -/
private def message {cap : Nat} : (Σ e, Fault cap e) → Option (Σ s, Built cap s)
  | ⟨.limitExceeded .., _⟩ => none
  | ⟨.malformed _ s,f⟩ | ⟨.truncated _ s,f⟩ | ⟨.unsupported _ s,f⟩ => some ⟨s,f.payload⟩

private def fromEvents {α : Type} {cap k : Nat} {r : Except Error α} (xs : List (Σ e, Fault cap e))
    (count : xs.length ≤ k) (origin : ∀ e, r = .error e → ∃ f : Fault cap e, ⟨e,f⟩ ∈ xs) :
    DiagnosticCost.Trace cap r k := by
  refine ⟨xs.filterMap message,Nat.le_trans (List.length_filterMap_le ..) count,?_⟩
  intro e bad
  obtain ⟨f,mem⟩ := origin e bad
  refine ⟨f.offset,?_⟩
  cases e with
  | limitExceeded => exact f.payload.down
  | _ => exact ⟨⟨_,f.payload⟩,List.mem_filterMap.mpr ⟨⟨_,f⟩,mem,rfl⟩,rfl⟩

private def rankTrace {L : Limits} {d : ByteArray} {red h initial}
    (entry : PublicPacketWork.prepareTiles L d red = .ok (h,initial)) :
    DiagnosticCost.Trace (tileCap L d.size) (NativeCost.ranks L h) 1 := by
  match rank : NativeCost.ranks L h with
  | .ok idx => exact doneTrace idx
  | .error e =>
    let xs := (records L d red).events
    have single := (public_rank_refusal (opts := {reduce := red}) entry rank).2.2
    apply fromEvents xs
    · obtain ⟨f,eq⟩ := single
      simp [xs,eq]
    · intro err bad
      cases bad
      obtain ⟨f,eq⟩ := single
      exact ⟨f,by simp [xs,eq]⟩

private def packetAndLayout (L : Limits) (h : Header) (d : ByteArray) (idx : Array (Array Nat))
    (v : TileVisit) : Except Error (Option TileCodeBlocks × Layout × Coding) := do
  let cb ← tileResult L h d idx v
  return (cb, ← Layout.ofHeader h v.tile)

private def packetTrace {L : Limits} {d : ByteArray} {red h initial idx v}
    (entry : PublicPacketWork.prepareTiles L d red = .ok (h,initial)) (rank : NativeCost.ranks L h = .ok idx)
    (hit : v ∈ (PublicPacketWork.measure L d red).1) :
    DiagnosticCost.Trace (tileCap L d.size) (packetAndLayout L h d idx v) (2+2*attempts v.packets) := by
  let a := geometryAudit entry rank hit
  apply fromEvents a.events a.count
  intro e bad
  apply a.origin
  unfold reachedLayout
  unfold packetAndLayout at bad
  cases store : tileResult L h d idx v with
  | error err => rw [store] at bad; cases bad; rfl
  | ok cb =>
    cases layout : Layout.ofHeader h v.tile <;> simp [store,layout,bind,Except.bind,pure,Except.pure] at bad ⊢
    exact bad

private def packetRun (L : Limits) (h : Header) (d : ByteArray) (idx : Array (Array Nat)) (j pb : Nat) :
    Option TileParams → PacketLog × Except Error (Option TileCodeBlocks)
  | none => ([],.ok none)
  | some tp => before (headerStreamAt h d tp (idx.getD j #[])) fun hs =>
      afterRun (measureStream L h d tp hs pb) (fun out => pure (some out))

private def writeCentered (L : Limits) (h : Header) (red : Nat) (dst : Destination) (t : JPEG2000.Decode.CenteredTile) :=
  JPEG2000.NativeOutput.writeTile L h.siz red t.layout t.coding dst t.sources

private def visit (L : Limits) (h : Header) (d : ByteArray) (red : Nat) (idx : Array (Array Nat))
    (t : Nat) (s : GridState) : TileVisit × Except Error GridState :=
  let (dst,pb,sat,j) := s
  let selected := presentAt h t j
  let r := packetRun L h d idx j pb selected
  (⟨t,j,pb,selected.isSome,r.1⟩,do
    let cb ← r.2
    let out ← JPEG2000.Decode.centeredTile L h d red t cb
    let next ← writeCentered L h red dst out
    return (next,pb+(cb.map (·.passes)).getD 0,sat+out.saturated,j+selected.isSome.toNat))

private def walk (f : Nat → GridState → TileVisit × Except Error GridState) :
    Nat → Nat → GridState → Measured TileVisit GridState
  | 0, _, s => ([], .ok s)
  | n+1, t, s =>
    let (v,r) := f t s
    match r with
    | .error e => ([v],.error e)
    | .ok z =>
      let tail := walk f n (t+1) z
      (v::tail.1,tail.2)

private theorem grid_eq (L : Limits) (h : Header) (d : ByteArray) (red : Nat) (initial : Destination) :
    measureGrid L h d initial (JPEG2000.Decode.centeredTile L h d red) (·.saturated) (writeCentered L h red) =
      before (NativeCost.ranks L h) (fun idx => walk (visit L h d red idx) (numTiles h.siz) 0 (initial,0,0,0)) := by
  unfold measureGrid
  congr 1
  funext idx
  generalize numTiles h.siz = n
  generalize (initial,(0:Nat),(0:Nat),(0:Nat)) = s
  generalize (0:Nat) = t
  induction n generalizing t s with
  | zero => rfl
  | succ n ih =>
    rw [walk]
    conv => lhs; whnf
    simp only [ih]
    split <;> rename_i eq <;> change (visit L h d red idx t s).2 = _ at eq <;> rw [eq] <;> rfl

private theorem prefix_eq (L : Limits) (h : Header) (d : ByteArray) (red : Nat) (initial : Destination)
    (idx : Array (Array Nat)) (n : Nat) :
    prefixState L h d red initial idx n = (walk (visit L h d red idx) n 0 (initial,0,0,0)).2 := by
  unfold prefixState gridPrefix
  apply congrArg Prod.snd
  generalize (initial,(0:Nat),(0:Nat),(0:Nat)) = s
  generalize (0:Nat) = t
  induction n generalizing t s with
  | zero => rfl
  | succ n ih =>
    rw [walk]
    conv => lhs; whnf
    simp only [ih]
    split <;> rename_i eq <;> change (visit L h d red idx t s).2 = _ at eq <;> rw [eq] <;> rfl

private theorem walk_succ (f : Nat → GridState → TileVisit × Except Error GridState) (n t : Nat) (s : GridState) :
    (walk f (n+1) t s).2 = (walk f n t s).2 >>= fun z => (f (t+n) z).2 := by
  induction n generalizing t s with
  | zero => cases step : f t s with | mk v r => cases r <;> simp [walk,step,bind,Except.bind]
  | succ n ih =>
    cases step : f t s with
    | mk v r =>
      cases r with
      | error e => simp [walk,step,bind,Except.bind]
      | ok z =>
        simpa only [walk,step,Nat.add_assoc,Nat.add_comm 1] using ih (t+1) z

private def joined (L : Limits) (h : Header) (d : ByteArray) (red : Nat) (idx : Array (Array Nat))
    (dst : Destination) (sat : Nat) (v : TileVisit) : Except Error GridState := do
  let (cb,g,c) ← packetAndLayout L h d idx v
  let sources ← JPEG2000.TileDispatch.tile L h d g c cb red
  let next ← JPEG2000.NativeOutput.writeTile L h.siz red g c dst sources
  return (next,v.passesBefore+(cb.map (·.passes)).getD 0,sat+0,v.cursor+v.present.toNat)

private theorem visit_eq {L : Limits} {h : Header} {d : ByteArray} (parsed : Header.parse L d = .ok h)
    (red : Nat) (idx : Array (Array Nat)) (t : Nat) (s : GridState) :
    (visit L h d red idx t s).2 = joined L h d red idx s.1 s.2.2.1 (visit L h d red idx t s).1 := by
  obtain ⟨dst,pb,sat,j⟩ := s
  let v := (visit L h d red idx t (dst,pb,sat,j)).1
  have store : (packetRun L h d idx j pb (presentAt h t j)).2 = tileResult L h d idx v := by
    change _ = tileResult L h d idx ⟨t,j,pb,_,_⟩
    unfold tileResult
    cases sel : presentAt h t j with
    | none => rfl
    | some tp =>
      dsimp only [packetRun]
      cases hs : headerStreamAt h d tp (idx.getD j #[]) with
      | error => rfl
      | ok x => simp only [before,afterRun,measureStream_erase parsed,bind,Except.bind]
  change (_ >>= fun cb => JPEG2000.Decode.centeredTile L h d red t cb >>= _) = joined L h d red idx dst sat v
  rw [store]
  unfold joined packetAndLayout JPEG2000.Decode.centeredTile
  simp only [bind_assoc,pure_bind]
  rfl

private def visitTrace {K : Allowances} {L : Limits} {d : ByteArray} {red h initial idx}
    (callbacks : Callbacks K L d red) (parsed : Header.parse L d = .ok h)
    (entry : PublicPacketWork.prepareTiles L d red = .ok (h,initial)) (rank : NativeCost.ranks L h = .ok idx)
    (pre tail : List TileVisit) (s : GridState)
    (past : prefixState L h d red initial idx pre.length = .ok s)
    (splitAt : (PublicPacketWork.measure L d red).1 =
      pre ++ (visit L h d red idx pre.length s).1 :: tail) :
    let step := visit L h d red idx pre.length s
    DiagnosticCost.Trace (scalarCap K L d.size) step.2
      (K.placement L d.size + K.tile L d.size + (2+2*attempts step.1.packets)) := by
  let v := (visit L h d red idx pre.length s).1
  have hit : v ∈ (PublicPacketWork.measure L d red).1 := by rw [splitAt]; exact List.mem_append_right _ (.head _)
  have bytes : s.1.map Spec.NativeOutput.backingBytes = initial.map Spec.NativeOutput.backingBytes ∧
      (s.1.toList.map Spec.NativeOutput.backingBytes).sum ≤ 8*L.maxWorkSamples := by
    obtain ⟨hh,ii,ix,dst,sat,prep,index,old,_,same,bound⟩ := NativeCost.destination_storage L d red splitAt
    rw [entry] at prep
    cases prep
    rw [rank] at index
    cases index
    change prefixState _ _ _ _ _ _ _ = _ at old
    rw [past] at old
    have dest := congrArg Prod.fst (Except.ok.inj old)
    exact dest ▸ ⟨same,bound⟩
  dsimp only
  rw [visit_eq parsed]
  change DiagnosticCost.Trace _ (joined L h d red idx s.1 s.2.2.1 v) _
  unfold joined
  apply bindTrace ((packetTrace entry rank hit).raiseCap (Nat.le_max_left ..))
  rintro ⟨cb,g,c⟩ good
  have reached : Reached L d red h initial idx v cb g c := by
    obtain ⟨a,store,tail⟩ := Tier2Equiv.bind_ok good
    obtain ⟨gc,layout,ret⟩ := Tier2Equiv.bind_ok tail
    cases ret
    refine ⟨hit,entry,rank,?_,layout⟩
    unfold tileResult at store
    unfold SegmentHistory.packetStore
    cases sel : presentAt h v.tile v.cursor <;> rw [sel] at store <;> exact store
  apply bindTrace ((callbacks.tile reached).raiseCap (Nat.le_max_right ..))
  intro sources made
  let write := callbacks.placement reached splitAt rfl past bytes.1 bytes.2 made
  simpa only [Nat.zero_add] using bindTrace (j := 0)
    (f := fun next => pure (next,v.passesBefore+(cb.map (·.passes)).getD 0,s.2.2.1+0,v.cursor+v.present.toNat))
    (write.raiseCap (Nat.le_max_right (tileCap L d.size) _)) (fun _ _ => doneTrace _)

/-- The grid charges each entered callback pair once and each attempted packet twice. -/
def gridCount (K : Allowances) (L : Limits) (n : Nat) (vs : List TileVisit) :=
  vs.length * (K.placement L n + K.tile L n + 2) + 2 * imageAttempts vs

private theorem gridCount_cons (K : Allowances) (L : Limits) (n : Nat) (v : TileVisit) (vs : List TileVisit) :
    gridCount K L n (v::vs) = gridCount K L n vs +
      (K.placement L n + K.tile L n + (2+2*attempts v.packets)) := by
  simp only [gridCount,imageAttempts,List.length_cons,Nat.add_one_mul,List.map_cons,List.sum_cons]
  omega

private def gridTrace {K : Allowances} {L : Limits} {d : ByteArray} {red h initial idx}
    (callbacks : Callbacks K L d red) (parsed : Header.parse L d = .ok h)
    (entry : PublicPacketWork.prepareTiles L d red = .ok (h,initial)) (rank : NativeCost.ranks L h = .ok idx)
    (n : Nat) (pre : List TileVisit) (s : GridState)
    (past : prefixState L h d red initial idx pre.length = .ok s)
    (remaining : (PublicPacketWork.measure L d red).1 = pre ++ (walk (visit L h d red idx) n pre.length s).1) :
    let run := walk (visit L h d red idx) n pre.length s
    DiagnosticCost.Trace (scalarCap K L d.size) run.2 (gridCount K L d.size run.1) := by
  match n with
  | 0 => exact doneTrace s
  | n+1 =>
    let f := visit L h d red idx
    let v := (f pre.length s).1
    cases step : (f pre.length s).2 with
    | error e =>
      have stop : walk f (n+1) pre.length s = ([v],.error e) := by simp only [walk,step,v]
      rw [stop] at remaining ⊢
      let tr := visitTrace callbacks parsed entry rank pre [] s past remaining
      change DiagnosticCost.Trace _ (f pre.length s).2 _ at tr
      rw [step] at tr
      change DiagnosticCost.Trace _ (.error e : Except Error GridState) (gridCount K L d.size (v::[]))
      rw [gridCount_cons]
      simpa only [gridCount,imageAttempts,List.length_nil,List.map_nil,List.sum_nil,
        Nat.zero_mul,Nat.mul_zero,Nat.zero_add,Nat.add_zero] using tr
    | ok z =>
      let rest := walk f n (pre.length+1) z
      have cont : walk f (n+1) pre.length s = (v::rest.1,rest.2) := by simp only [walk,step,v,rest]
      rw [cont] at remaining ⊢
      let tr := visitTrace callbacks parsed entry rank pre rest.1 s past remaining
      have next : prefixState L h d red initial idx (pre++[v]).length = .ok z := by
        simp only [List.length_append,List.length_cons,List.length_nil,Nat.zero_add,prefix_eq,walk_succ]
        rw [prefix_eq] at past
        simpa only [past,bind,Except.bind,Nat.zero_add] using step
      have tail : (PublicPacketWork.measure L d red).1 =
          (pre++[v]) ++ (walk f n (pre++[v]).length z).1 := by
        simpa only [List.append_assoc,List.singleton_append,List.length_append,List.length_singleton,rest] using remaining
      let later := gridTrace callbacks parsed entry rank n (pre++[v]) z next tail
      have reindex : (pre++[v]).length = pre.length+1 := by simp
      rw [reindex] at later
      change DiagnosticCost.Trace _ rest.2 (gridCount _ _ _ (v :: rest.1))
      rw [gridCount_cons]
      -- Bind a successful visit to its suffix even when the visit emitted messages.
      change DiagnosticCost.Trace _ (f pre.length s).2 _ at tr
      rw [step] at tr
      exact bindTrace (f := fun _ => rest.2) tr (fun _ _ => later)

private def finish (h : Header) (red : Nat) (ds : Destination) (sat : Nat) : CodestreamImage :=
  ⟨h,red,ds.map .native,sat⟩

private theorem eraseGrid {L : Limits} {h : Header} {d : ByteArray} {red : Nat}
    (parsed : Header.parse L d = .ok h) (initial : Destination) :
    JPEG2000.Decode.withTiles L h d initial (JPEG2000.Decode.centeredTile L h d red) (·.saturated)
      (writeCentered L h red) (finish h red) =
    (NativeCost.ranks L h >>= fun idx => (walk (visit L h d red idx) (numTiles h.siz) 0 (initial,0,0,0)).2 >>=
      fun s => pure (finish h red s.1 s.2.2.1)) := by
  rw [← measureTiles_erase parsed,measureTiles_finish,grid_eq]
  cases rank : NativeCost.ranks L h <;> rfl

/-- Trace the production grid from its shared rank preflight to its pure image finish.
The destination supplied here is exactly the one returned by public allocation. -/
def withTilesTrace {K : Allowances} {L : Limits} {d : ByteArray} {red h initial}
    (callbacks : Callbacks K L d red) (parsed : Header.parse L d = .ok h)
    (entry : PublicPacketWork.prepareTiles L d red = .ok (h,initial)) :
    DiagnosticCost.Trace (scalarCap K L d.size)
      (JPEG2000.Decode.withTiles L h d initial (JPEG2000.Decode.centeredTile L h d red) (·.saturated)
        (fun dst t => JPEG2000.NativeOutput.writeTile L h.siz red t.layout t.coding dst t.sources)
        (fun ds sat => (⟨h,red,ds.map .native,sat⟩ : CodestreamImage)))
      (gridCount K L d.size (PublicPacketWork.measure L d red).1 + 1) := by
  change DiagnosticCost.Trace _ (JPEG2000.Decode.withTiles _ _ _ _ _ _ (writeCentered L h red) (finish h red)) _
  rw [eraseGrid parsed]
  apply bindTrace ((rankTrace entry).raiseCap (Nat.le_max_left ..))
  intro idx rank
  let run := walk (visit L h d red idx) (numTiles h.siz) 0 (initial,0,0,0)
  have actual : (PublicPacketWork.measure L d red).1 = run.1 := by
    simp only [PublicPacketWork.measure,entry,before,measureTiles_finish,afterRun]
    change (measureGrid L h d initial _ _ (writeCentered L h red)).1 = _
    rw [grid_eq,rank]
    rfl
  let tr := gridTrace callbacks parsed entry rank (numTiles h.siz) [] (initial,0,0,0) rfl actual
  rw [actual]
  simpa only [Nat.zero_add,run,List.length_nil,scalarCap] using bindTrace (j := 0) (f := fun s : GridState => pure (finish h red s.1 s.2.2.1))
    tr (fun _ _ => doneTrace _)

/-- Native diagnostic count after successful public header parsing, on the exact
tile and packet prefix. The rank and allocation allowances also cover refusal
before entry to the first tile. -/
def prefixCount (K : Allowances) (L : Limits) (d : ByteArray) (red : Nat) :=
  gridCount K L d.size (PublicPacketWork.measure L d red).1 + 1 + K.allocation L d.size

/-- Ordered production trace from native allocation to the final codestream image.
A refused rank contributes its sole packet record. Successful predecessors
contribute all their messages, even on a later packet, tile or placement refusal. -/
def nativeTrace {K : Allowances} {L : Limits} {d : ByteArray} {red h}
    (callbacks : Callbacks K L d red) (reduce : red ≤ L.maxDecompLevels) (parsed : Header.parse L d = .ok h) :
    DiagnosticCost.Trace (scalarCap K L d.size) (JPEG2000.Decode.nativeFromHeader L h d red)
      (prefixCount K L d red) := by
  unfold JPEG2000.Decode.nativeFromHeader prefixCount
  apply bindTrace ((callbacks.allocation reduce parsed).raiseCap (Nat.le_max_right ..))
  intro initial allocated
  have checked : L.check JPEG2000.Decode.loc .decompLevels red = .ok () := (Limits.check_eq_ok_iff ..).2 reduce
  have entry : PublicPacketWork.prepareTiles L d red = .ok (h,initial) := by
    simp only [PublicPacketWork.prepareTiles,checked,parsed,allocated,bind,Except.bind,pure,Except.pure]
  exact withTilesTrace callbacks parsed entry

/-- Event count bound in limits and input byte length alone. -/
def countBound (K : Allowances) (L : Limits) (n : Nat) :=
  L.maxTiles * (K.placement L n + K.tile L n + 2) + 2*(L.maxTiles*L.maxPackets) + 1 + K.allocation L n

private theorem prefix_le (K : Allowances) (L : Limits) (d : ByteArray) (red : Nat) :
    prefixCount K L d red ≤ countBound K L d.size := by
  obtain ⟨_,tiles,calls,positions,cost,_⟩ := PublicPacketWork.decode_packet_work L d red
  have t := Nat.mul_le_mul_right (K.placement L d.size + K.tile L d.size + 2) tiles
  unfold prefixCount gridCount countBound
  omega

/-- Closed work and cumulative temporary storage bound for diagnostic message
construction on this stage of the public native path. -/
def budget (K : Allowances) (L : Limits) (n : Nat) :=
  countBound K L n * Text.workBound (scalarCap K L n) 128 24

/-- Result-indexed public trace of the native suffix after the actual reduction
and header succeed. It retains the same ordered trees as `nativeTrace`. -/
def publicTrace {K : Allowances} {L : Limits} {d : ByteArray} {red h}
    (callbacks : Callbacks K L d red) (reduce : red ≤ L.maxDecompLevels) (parsed : Header.parse L d = .ok h) :
    DiagnosticCost.Trace (scalarCap K L d.size) (decodeCodestream L d red) (prefixCount K L d red) := by
  have checked : L.check JPEG2000.Decode.loc .decompLevels red = .ok () := (Limits.check_eq_ok_iff ..).2 reduce
  simpa only [decodeCodestream,checked,parsed,bind,Except.bind] using nativeTrace callbacks reduce parsed

/-- The observed native suffix obeys both the prefix count and the uniform
limits-and-length bound. All UTF-8 conversion, append work and cumulative
temporary storage fit the same budget. The final decoder-owned error includes
its offset and computed numeric fields. Rendering remains a caller operation. -/
theorem public_bounds {K : Allowances} {L : Limits} {d : ByteArray} {red h}
    (callbacks : Callbacks K L d red) (reduce : red ≤ L.maxDecompLevels) (parsed : Header.parse L d = .ok h) :
    let tr := publicTrace callbacks reduce parsed
    let cap := scalarCap K L d.size
    tr.messages.length ≤ prefixCount K L d red ∧ prefixCount K L d red ≤ countBound K L d.size ∧
    (tr.messages.map (fun m => m.2.tree.work)).sum ≤ budget K L d.size ∧
    (tr.messages.map (fun m => m.2.tree.storage)).sum ≤ budget K L d.size ∧
    (∀ e, decodeCodestream L d red = .error e → storedPayload false e ≤ 6+Text.byteBound cap 128 24+2*bits cap) := by
  intro tr cap
  have count := prefix_le K L d red
  have upper := Nat.mul_le_mul_right (Text.workBound cap 128 24) count
  exact ⟨tr.countBound,count,Nat.le_trans (trace_cost tr).1 upper,Nat.le_trans (trace_storage tr) upper,
    fun _ bad => trace_retained tr bad⟩

end JPEG2000.Spec.Resources.DiagnosticReconstruction
