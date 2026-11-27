import Spec.Resources.PacketLocalWork

/-!
# Geometry construction on rejecting prefixes (Plan.md §§3–5, 7, S3)

T.800 A.5–A.6, B.5–B.7 and B.10.2. The meter counts loop visits, logical entry reservations and initializers, and
descriptor pushes. Cumulative construction bounds the logical geometry entries
live in each prefix. The original input contributes a separate `data.size`
bytes. Arithmetic, runtime capacity growth and object sizes have separate units.
Range iteration includes empty precinct grids. Lists used to express the
erasure of a loop are proof models.
-/

namespace JPEG2000.Spec.Resources.GeometryInit

open JPEG2000.Header JPEG2000.Marker JPEG2000.TilePart JPEG2000.Progression
open JPEG2000.Tier2.Geometry JPEG2000.Tier2.Packet
open PacketLocalWork (Counted)
open Tier2Equiv (bind_ok)

private def pay {α : Type} (x : Except Error α) (n : Nat) : Counted x n :=
  ⟨x, n, rfl, Nat.le_refl _⟩

private def widen {α : Type} {x : Except Error α} {n m : Nat} (a : Counted x n) (h : n ≤ m) :
    Counted x m := ⟨a.result, a.work, a.erase, Nat.le_trans a.within h⟩

private def charge {α : Type} {x : Except Error α} {n : Nat} (k : Nat) (a : Counted x n) :
    Counted x (k + n) := ⟨a.result, k + a.work, a.erase, Nat.add_le_add_left a.within k⟩

private def chain {α β : Type} {x : Except Error α} {f : α → Except Error β} {n m : Nat}
    (a : Counted x n) (next : ∀ z, x = .ok z → Counted (f z) m) : Counted (x >>= f) (n + m) :=
  match h : a.result with
  | .error e => ⟨.error e, a.work, by rw [← a.erase, h]; rfl, by have := a.within; omega⟩
  | .ok z =>
    let b := next z (a.erase.symm.trans h)
    ⟨b.result, a.work + b.work, by rw [← a.erase, h]; exact b.erase, Nat.add_le_add a.within b.within⟩

private def loop {α β : Type} (f : α → β → Except Error (ForInStep β)) (k : Nat) :
    (xs : List α) → (s : β) → (∀ x ∈ xs, ∀ b, Counted (f x b) k) →
      Counted (forIn xs s f) (xs.length * k)
  | [], _, _ => by simp only [List.length_nil, Nat.zero_mul]; exact pay _ 0
  | x :: xs, s, each => by
    rw [List.forIn_cons, List.length_cons, Nat.succ_mul, Nat.add_comm]
    refine chain (each x (by simp) s) ?_
    rintro (b|b) _
    · exact widen (pay _ 0) (Nat.zero_le _)
    · exact loop f k xs b (fun a ha => each a (by simp [ha]))

private def rangeLoop {β : Type} (n k : Nat) (s : β) (f : Nat → β → Except Error (ForInStep β))
    (each : ∀ i, i < n → ∀ b, Counted (f i b) k) :
    Counted (forIn [:n] s f) (n*k) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have sz : [:n].size = n := by simp [Std.Legacy.Range.size]
  simpa only [sz, List.length_range'] using
    loop f k (List.range' 0 n) s (fun i hi => each i (by simpa using hi))

private def mapList {α β : Type} (f : α → Except Error β) (k : Nat) :
    (xs : List α) → (∀ x ∈ xs, Counted (f x) k) → Counted (xs.mapM f) (xs.length*k)
  | [], _ => by simp only [List.length_nil, Nat.zero_mul]; exact pay _ 0
  | x :: xs, each => by
    rw [List.mapM_cons, List.length_cons, Nat.succ_mul, Nat.add_comm]
    refine chain (each x (by simp)) (fun y _ => ?_)
    exact widen (chain (mapList f k xs (fun a h => each a (by simp [h])))
      (fun _ _ => pay _ 0)) (by omega)

private def mapArray {α β : Type} (xs : Array α) (f : α → Except Error β) (k : Nat)
    (each : ∀ x ∈ xs, Counted (f x) k) : Counted (xs.mapM f) (xs.size + xs.size*k) := by
  rw [Array.mapM_eq_mapM_toList]
  let a := mapList f k xs.toList (fun x hx => each x (by simpa using hx))
  exact ⟨_, xs.size + a.work, rfl, Nat.add_le_add_left (by simpa using a.within) _⟩

private theorem checked {L : Limits} {loc k n} {u : Unit} (h : L.check loc k n = .ok u) :
    n ≤ L.bound k := (Limits.check_eq_ok_iff ..).1 h

private theorem levels_fuel (f w h : Nat) : JPEG2000.TagTree.levelsAux f w h ≤ f+1 := by
  induction f generalizing w h with
  | zero => exact Nat.le_refl _
  | succ f ih =>
    simp only [JPEG2000.TagTree.levelsAux]
    split
    · omega
    · have := ih ((w+1)/2) ((h+1)/2); omega

private theorem axes {w h b : Nat} (empty : w = 0 ↔ h = 0) (cap : w*h ≤ b) : w+h ≤ 2*b := by
  by_cases hw : w = 0
  · simp [hw, empty.mp hw]
  · have hh := mt empty.mpr hw
    have := Nat.mul_le_mul_left w (show 1 ≤ h by omega)
    have := Nat.mul_le_mul_right h (show 1 ≤ w by omega)
    simp only [Nat.mul_one, Nat.one_mul] at *
    omega

private def shapeFrames : Nat → Nat → Nat → Nat
  | 0, _, _ => 1
  | fuel+1, w, h =>
    if w ≤ 1 ∧ h ≤ 1 then 1 else 1 + shapeFrames fuel ((w+1)/2) ((h+1)/2)

private theorem shape_frames (f w h : Nat) : shapeFrames f w h = JPEG2000.TagTree.levelsAux f w h := by
  induction f generalizing w h with
  | zero => rfl
  | succ f ih => simp [shapeFrames, JPEG2000.TagTree.levelsAux, ih, Nat.add_comm]

private def nodeCount : Nat → Nat → Nat → Nat × Nat
  | 0, _, _ => (0,1)
  | n+1, w, h =>
    let next := nodeCount n ((w+1)/2) ((h+1)/2)
    (w*h+next.1, 1+next.2)

private theorem node_count (n w h : Nat) :
    nodeCount n w h = (JPEG2000.TagTree.totalAux n w h, n+1) := by
  induction n generalizing w h with
  | zero => rfl
  | succ n ih => simp [nodeCount, JPEG2000.TagTree.totalAux, ih, Nat.add_comm]

/-- The leaf check precedes shape calculation. `levelsAux` visits exactly
`levels` frames including its terminal frame. `totalAux` visits one frame per
level plus its terminal zero. Only the successful node-count check initializes
the two flat arrays and returns their tree descriptor. Empty precinct bands
normalize both dimensions to zero. -/
def tree (L : Limits) (w h : Nat) (empty : w = 0 ↔ h = 0) :
    Counted (JPEG2000.TagTree.create L w h) (8 + 12*L.maxCodeBlocks) := by
  unfold JPEG2000.TagTree.create
  refine widen (chain (pay _ 1) (m := 7+12*L.maxCodeBlocks) ?_) (by omega)
  intro _ hl
  let n := JPEG2000.TagTree.levels w h
  let cells := JPEG2000.TagTree.totalAux n w h
  have depth : n ≤ 2*L.maxCodeBlocks+1 := by
    have d := levels_fuel (w+h) w h
    have := axes empty (show w*h ≤ L.maxCodeBlocks from checked hl)
    change JPEG2000.TagTree.levelsAux (w+h) w h ≤ _
    omega
  let depthFrames := shapeFrames (w+h) w h
  let tally := nodeCount n w h
  have hDepth : depthFrames = n := shape_frames ..
  have hTally : tally = (cells,n+1) := node_count ..
  refine widen (chain (pay _ (depthFrames+tally.2+1)) (m := 3+8*L.maxCodeBlocks) ?_) (by rw [hTally]; dsimp; omega)
  rintro ⟨⟩ hc
  have hc' := (Limits.checkLe_eq_ok_iff JPEG2000.TagTree.loc .codeBlocks
    (JPEG2000.TagTree.totalAux (JPEG2000.TagTree.levels w h) w h) (4*L.maxCodeBlocks)).1 hc
  change cells ≤ 4*L.maxCodeBlocks at hc'
  exact widen (pay _ (3+2*tally.1)) (by rw [hTally]; dsimp; omega)

private theorem bands_size (r : Nat) : (bandsOf r).size ≤ 3 := by
  simp only [bandsOf]; split <;> decide

private theorem resolution_shape {L : Limits} {tc : TileCompGeom} {r : Nat} {res : ResolutionGeom}
    (ok : resolution L tc r = .ok res) : res.numPrecincts ≤ L.maxPrecincts ∧ res.bands.size ≤ 3 := by
  unfold resolution at ok
  dsimp only at ok
  split at ok <;> try contradiction
  obtain ⟨_,hc,ok⟩ := bind_ok ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  cases ok
  exact ⟨checked hc, by simpa only [Array.size_map] using bands_size r⟩

/-- Resolution visits pay the guards, the temporary orientation and mapped
band arrays, and every attempted band check after the precinct grid check. -/
def resolutionWork (L : Limits) (tc : TileCompGeom) (r : Nat) :
    Counted (resolution L tc r) 13 := by
  unfold resolution
  dsimp only
  split
  · exact widen (pay _ 1) (by decide)
  · refine widen (chain (pay _ 2) (m := 11) ?_) (by decide)
    intro _ _
    have len := bands_size r
    let bs := (bandsOf r).map (bandGeom tc r)
    have size : bs.size ≤ 3 := by simpa [bs] using len
    rw [← Array.forIn_toList]
    refine widen (charge (2*bs.size) (chain (loop _ 1 bs.toList _ (fun _ _ _ => pay _ 1))
      (fun _ _ => pay _ 1))) ?_
    simp only [Array.length_toList, Nat.mul_one]
    omega

private def geomBandBudget (L : Limits) := 3 + 4*L.maxCodeBlocks
private def precinctBudget (L : Limits) := 2 + 3 + 3*geomBandBudget L

private def blockGeometry {α : Type} (L : Limits) (n : Nat) (build : Unit → Except Error α) :
    Counted (L.check JPEG2000.Tier2.Geometry.loc .codeBlocks n >>= build) (geomBandBudget L) := by
  refine widen (chain (pay _ 2) (m := 1+4*L.maxCodeBlocks) ?_) (by unfold geomBandBudget; omega)
  intro _ hc
  have cap : n ≤ L.maxCodeBlocks := checked hc
  exact widen (pay _ (1+4*n)) (by omega)

/-- Before the tile-wide block check, each admitted precinct band already
materializes the range list, the index array, and the mapped block geometry.
The fourth unit per block pays the descriptor construction. A band that fails its
product check pays for its visit and check. -/
def precinctWork (L : Limits) (res : ResolutionGeom) (p : Nat) (size : res.bands.size ≤ 3) :
    Counted (precinct L res p) (precinctBudget L) := by
  unfold precinct
  dsimp only
  split
  · exact widen (pay _ 1) (by unfold precinctBudget; omega)
  · refine widen (charge 1 (chain (mapArray res.bands _ (geomBandBudget L) ?_)
      (fun _ _ => pay _ 1))) ?_
    · intro b _
      split <;> exact blockGeometry L _ _
    · have := Nat.mul_le_mul_right (geomBandBudget L) size
      unfold precinctBudget
      omega

private theorem empty_axes {L : Limits} {res : ResolutionGeom} {p pg}
    (hp : precinct L res p = .ok pg) : ∀ b ∈ pg.bands, b.cw = 0 ↔ b.ch = 0 := by
  unfold precinct at hp
  dsimp only at hp
  split at hp <;> try contradiction
  obtain ⟨bands,hm,hp⟩ := bind_ok hp
  cases hp
  refine Tier2WF.arrayMapM_mem _ _ _ ?_ _ hm
  intro b _ pb ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  cases ok
  dsimp only
  split <;> simp_all

private def stateBandBudget (L : Limits) := 2 + 2*(8+12*L.maxCodeBlocks) + L.maxCodeBlocks
private def stateBudget (L : Limits) := 1 + 3 + 3*stateBandBudget L

private def stateWork {L : Limits} {tc : TileCompGeom} {r p res pg}
    (hr : resolution L tc r = .ok res) (hp : precinct L res p = .ok pg) :
    Counted (PrecState.init L tc.params r pg) (stateBudget L) := by
  obtain ⟨_,size,blocks⟩ := HeaderWork.precinct_geometry hr hp
  unfold PrecState.init
  refine widen (chain (mapArray pg.bands _ (stateBandBudget L) ?_) (fun _ _ => pay _ 1)) ?_
  · intro b hb
    let tr := tree L b.cw b.ch (empty_axes hp b hb)
    refine widen (charge 1 (chain tr (m := 8+12*L.maxCodeBlocks+(1+L.maxCodeBlocks)) ?_)) ?_
    · intro _ _
      apply chain tr
      intro _ _
      exact widen (pay _ (1+b.codeBlocks.size)) (Nat.add_le_add_left (blocks b hb) 1)
    · unfold stateBandBudget
      omega
  · have := Nat.mul_le_mul_right (stateBandBudget L) size
    unfold stateBudget
    omega

private def packetPrecinctBudget (L : Limits) := 2 + precinctBudget L + 3 + stateBudget L + 1
private def packetResolutionBudget (L : Limits) := 17 + L.maxPrecincts*packetPrecinctBudget L
private def packetComponentBudget (L : Limits) := 5 + (L.maxDecompLevels+1)*packetResolutionBudget L

/-- Uniform per-tile charge for component rows, base and span entries,
resolution summaries, precinct geometry (including pre-admission blocks), both
tree shapes and their checked arrays, block states and flat precinct pushes. -/
def initBudget (L : Limits) := L.maxComponents * packetComponentBudget L

/-- Instrumentation of all three production loops. The base index is pushed
before resolution construction and the span after precinct admission. The
block sum visits every constructed band before aggregate block admission. -/
def initWork (L : Limits) (g : Layout) (comps : g.numComps ≤ L.maxComponents)
    (levels : ∀ i : Fin g.numComps, (g.comp i).numResolutions ≤ L.maxDecompLevels+1) :
    Counted (initPrecincts L g) (initBudget L) := by
  unfold initPrecincts
  refine widen (chain (rangeLoop g.numComps (packetComponentBudget L) _ _ ?_) (fun _ _ => pay _ 0)) ?_
  · intro i hi s
    let tc := g.comp i
    have nr := levels ⟨i,hi⟩
    change tc.params.levels+1 ≤ _ at nr
    refine widen (charge 3 (chain
      (rangeLoop (tc.params.levels+1) (packetResolutionBudget L) _ _ ?_) (fun _ _ => pay _ 2))) ?_
    · intro r _ s2
      refine widen (charge 2 (chain (resolutionWork L tc r)
        (m := 2+L.maxPrecincts*packetPrecinctBudget L) ?_)) ?_
      · intro res hr
        obtain ⟨pr,size⟩ := resolution_shape hr
        refine widen (chain (pay _ 1) (m := 1+L.maxPrecincts*packetPrecinctBudget L) ?_) (by omega)
        intro _ _
        refine widen (charge 1 (chain (rangeLoop res.numPrecincts (packetPrecinctBudget L) _ _ ?_)
          (fun _ _ => pay _ 0))) ?_
        · intro p _ s3
          refine widen (charge 1 (chain (precinctWork L res p size)
            (m := 4+stateBudget L+1) ?_)) ?_
          · intro pg hp
            have bands := (HeaderWork.precinct_geometry hr hp).2.1
            refine widen (chain (pay _ (pg.bands.size+1)) (m := stateBudget L+1) ?_) (by omega)
            intro _ _
            exact chain (stateWork hr hp) (fun _ _ => pay _ 1)
          · unfold packetPrecinctBudget
            omega
        · have := Nat.mul_le_mul_right (packetPrecinctBudget L) pr
          omega
      · unfold packetResolutionBudget
        omega
    · have := Nat.mul_le_mul_right (packetResolutionBudget L) nr
      unfold packetComponentBudget
      omega
  · simpa [initBudget] using Nat.mul_le_mul_right (packetComponentBudget L) comps

/-- Per-tile stage at the parsed layout, regardless of the initialization result.
A component with zero precincts still consumes its row and resolution charges. -/
theorem parsed_init_work {L : Limits} {data : ByteArray} {h : Header} {t g c}
    (parsed : Header.parse L data = .ok h) (layout : Layout.ofHeader h t = .ok (g,c)) :
    let d := HeaderWork.layout_budget parsed layout
    let run := initWork L g d.1 d.2
    run.result = initPrecincts L g ∧ run.work ≤ initBudget L :=
  ⟨(initWork ..).erase, (initWork ..).within⟩

private def Rows {α : Type} (g : Layout) (n : Nat) (xs : Array (Array α)) : Prop :=
  xs.size = n ∧ ∀ i row, xs[i]? = some row → row.size = (g.comp i).numResolutions

private theorem next_row {α : Type} {g : Layout} {i : Nat} {xs : Array (Array α)} {row : Array α}
    (old : Rows g i xs) (len : row.size = (g.comp i).numResolutions) : Rows g (i+1) (xs.push row) := by
  refine ⟨by simp [old.1], ?_⟩
  intro j other hit
  rw [Array.getElem?_push,old.1] at hit
  split at hit
  · rename_i eq
    cases hit; exact eq ▸ len
  · exact old.2 j other hit

/-- Each successfully returned component has precisely one base and one span
entry per resolution, including resolutions with a zero precinct dimension. -/
theorem init_index_rows {L : Limits} {g : Layout} {ps base spans}
    (ok : initPrecincts L g = .ok (ps,base,spans)) :
    (∀ i row, base[i]? = some row → row.size = (g.comp i).numResolutions) ∧
    (∀ i row, spans[i]? = some row → row.size = (g.comp i).numResolutions) := by
  unfold initPrecincts at ok
  simp only [Std.Legacy.Range.forIn_eq_forIn_range'] at ok
  obtain ⟨_,loop,ok⟩ := bind_ok ok
  cases ok
  have len (n : Nat) : [:n].size = n := by simp [Std.Legacy.Range.size]
  simp only [len] at loop
  have outer := Tier2WF.forIn_range'_inv
    (fun i (s : Array PrecState × Array (Array Nat) × Array (Array (Nat × Nat)) × Nat) =>
      Rows g i s.2.1 ∧ Rows g i s.2.2.1) _ ?_ _ 0 _ _ (by simp [Rows]) loop
  · exact ⟨outer.1.2,outer.2.2⟩
  intro i b z prev step
  obtain ⟨s,middle,step⟩ := bind_ok step
  cases step
  have rows := Tier2WF.forIn_range'_inv
    (fun r (s : Array PrecState × Nat × Array Nat × Array (Nat × Nat)) =>
      s.2.2.1.size = r ∧ s.2.2.2.size = r) _ ?_ _ 0 _ _ ⟨rfl,rfl⟩ middle
  · exact ⟨_,rfl,next_row prev.1 (by simpa [TileCompGeom.numResolutions] using rows.1),
       next_row prev.2 (by simpa [TileCompGeom.numResolutions] using rows.2)⟩
  intro r state z hr step
  obtain ⟨_,_,step⟩ := bind_ok step
  obtain ⟨_,_,step⟩ := bind_ok step
  obtain ⟨_,_,step⟩ := bind_ok step
  cases step
  exact ⟨_,rfl,by simp [hr.1],by simp [hr.2]⟩

private theorem map_size {α β : Type} {xs : Array α} {ys : Array β} {f : α → Except Error β}
    (ok : xs.mapM f = .ok ys) : ys.size = xs.size := by
  have len (xs : List α) (ys : List β) (ok : xs.mapM f = .ok ys) : ys.length = xs.length := by
    induction xs generalizing ys with
    | nil => cases ok; rfl
    | cons x xs ih =>
      rw [List.mapM_cons] at ok
      obtain ⟨_,_,ok⟩ := bind_ok ok
      obtain ⟨tail,ht,ok⟩ := bind_ok ok
      cases ok
      exact congrArg Nat.succ (ih tail ht)
  rw [Array.mapM_eq_mapM_toList] at ok
  cases he : xs.toList.mapM f with
  | error => rw [he] at ok; cases ok
  | ok l => rw [he] at ok; cases ok; simpa using len _ _ he

private def Shape (L : Limits) (a : Array (Band × Array CodeBlockGeom)) :=
  a.size ≤ 3 ∧ ∀ b ∈ a, b.2.size ≤ L.maxCodeBlocks

private theorem fresh_shape {L : Limits} {tc : TileCompGeom} {r p res pg st}
    (hr : resolution L tc r = .ok res) (hp : precinct L res p = .ok pg)
    (hs : PrecState.init L tc.params r pg = .ok st) : Shape L (Tier2WF.pshape st) := by
  obtain ⟨_,nb,blocks⟩ := HeaderWork.precinct_geometry hr hp
  unfold PrecState.init at hs
  obtain ⟨bands,hm,hs⟩ := bind_ok hs
  cases hs
  refine ⟨by simpa [Tier2WF.pshape, map_size hm] using nb, ?_⟩
  have each : ∀ b ∈ bands, b.blocks.size ≤ L.maxCodeBlocks := by
    refine Tier2WF.arrayMapM_mem _ _ _ ?_ _ hm
    intro pb hb bs h
    obtain ⟨_,_,h⟩ := bind_ok h
    obtain ⟨_,_,h⟩ := bind_ok h
    cases h
    simpa using blocks pb hb
  intro x hx
  obtain ⟨b,hb,rfl⟩ := Array.mem_map.mp hx
  simpa [Tier2WF.bshape] using each b hb

private theorem init_shapes {L : Limits} {g : Layout} {ps base spans}
    (ok : initPrecincts L g = .ok (ps,base,spans)) : ∀ st ∈ ps, Shape L (Tier2WF.pshape st) := by
  unfold initPrecincts at ok
  simp only [Std.Legacy.Range.forIn_eq_forIn_range'] at ok
  obtain ⟨_,loop,ok⟩ := bind_ok ok
  cases ok
  refine Tier2Equiv.forIn_inv (fun (s : Array PrecState × Array (Array Nat) × Array (Array (Nat × Nat)) × Nat) =>
    ∀ st ∈ s.1, Shape L (Tier2WF.pshape st)) _ ?_ _ _ _ (by simp) loop
  intro i b r hb hr
  obtain ⟨_,middle,hr⟩ := bind_ok hr
  cases hr
  refine Tier2Equiv.forIn_inv (fun (s : Array PrecState × Nat × Array Nat × Array (Nat × Nat)) =>
    ∀ st ∈ s.1, Shape L (Tier2WF.pshape st)) _ ?_ _ _ _ hb middle
  intro r b2 z hb2 hz
  obtain ⟨res,hr,hz⟩ := bind_ok hz
  obtain ⟨_,_,hz⟩ := bind_ok hz
  obtain ⟨_,inner,hz⟩ := bind_ok hz
  cases hz
  refine Tier2Equiv.forIn_inv (fun (s : Array PrecState × Nat) => ∀ st ∈ s.1, Shape L (Tier2WF.pshape st))
    _ ?_ _ _ _ hb2 inner
  intro p b3 z hb3 hz
  obtain ⟨pg,hp,hz⟩ := bind_ok hz
  obtain ⟨_,_,hz⟩ := bind_ok hz
  obtain ⟨st,hs,hz⟩ := bind_ok hz
  cases hz
  intro x hx
  rcases Array.mem_push.mp hx with hx | rfl
  · exact hb3 x hx
  · exact fresh_shape hr hp hs

/-- The three geometry conjuncts consumed by reconstruction's
`AssemblyCost.StoreBounds`, including out-of-range component/resolution lookups. -/
def StoreGeometry (L : Limits) (out : TileCodeBlocks) : Prop :=
  ∀ i r, let row := (out.comps.getD i #[]).getD r #[]
    row.size ≤ L.maxPrecincts ∧ ∀ p ∈ row, p.bands.size ≤ 3 ∧ ∀ b ∈ p.bands, b.blocks.size ≤ L.maxCodeBlocks

private theorem raw_store {L : Limits} {h : Header} {data : ByteArray} {tp : TileParams}
    {hs : Option ByteArray} {pb : Nat} {out : TileCodeBlocks}
    (ok : decodeTilePacketsWith L h data tp hs pb = .ok out) : StoreGeometry L out := by
  unfold decodeTilePacketsWith at ok
  obtain ⟨⟨g,coding⟩,_,ok⟩ := bind_ok ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  obtain ⟨⟨ps,base,spans⟩,init,ok⟩ := bind_ok ok
  obtain ⟨⟨buf,parts⟩,_,ok⟩ := bind_ok ok
  obtain ⟨s,run,ok⟩ := bind_ok ok
  cases ok
  have same := Tier2WF.forPackets_pres (fun s : LoopState => s.precs.map Tier2WF.pshape = ps.map Tier2WF.pshape)
    g coding.progression coding.poc _ (fun _ _ _ prev step =>
      (Tier2WF.fastStep_pres (L := L) (sop := coding.sop) (eph := coding.eph) (same := hs.isNone)
        (base := base) (pb := pb) step).trans prev) _ s rfl run
  have states : ∀ k, Shape L (Tier2WF.pshape (s.precs.getD k default)) := by
    intro k
    rw [Array.getD_eq_getD_getElem?]
    cases he : s.precs[k]? with
    | none => exact ⟨by change (#[].map Tier2WF.bshape).size ≤ 3; simp, by change ∀ b ∈ #[].map Tier2WF.bshape, _; simp⟩
    | some st =>
      have hm : Tier2WF.pshape st ∈ s.precs.map Tier2WF.pshape :=
        Array.mem_map_of_mem (Array.mem_of_getElem? he)
      rw [same] at hm
      obtain ⟨old,ho,eq⟩ := Array.mem_map.mp hm
      exact eq ▸ init_shapes init old ho
  intro i r
  dsimp only
  rw [Tier2WF.getD_map_arr _ _ _ #[] (by simp), Tier2WF.getD_map_arr _ _ _ (0,0) (by simp)]
  generalize hpair : (spans.getD i #[]).getD r (0,0) = sn
  obtain ⟨start,n⟩ := sn
  refine ⟨?_,?_⟩
  · simp only [Array.size_map, Array.size_range]
    rcases Nat.eq_zero_or_pos n with rfl | pos
    · exact Nat.zero_le _
    · rw [Array.getD_eq_getD_getElem? (xs := spans.getD i #[]) (i := r)] at hpair
      cases he : (spans.getD i #[])[r]? with
      | none => rw [he] at hpair; cases hpair; omega
      | some pair =>
        rw [he] at hpair
        change pair = _ at hpair
        subst pair
        obtain ⟨_,hit,_⟩ := Tier2WF.initPrecincts_wf init i r start n he (n-1) (by omega)
        have last := (Array.getElem?_eq_some_iff.mp hit).1
        have total := (HeaderWork.initPrecincts_storage init).1
        omega
  · intro p hp
    obtain ⟨k,_,rfl⟩ := Array.mem_map.mp hp
    have ⟨bn,bb⟩ := states (start+k)
    refine ⟨by simpa [PrecState.out,Tier2WF.pshape] using bn, ?_⟩
    intro b hb
    obtain ⟨old,ho,rfl⟩ := Array.mem_map.mp hb
    simpa [Tier2WF.bshape] using bb (Tier2WF.bshape old) (Array.mem_map_of_mem ho)

/-- The actual translated public tile store has bounded resolution rows, band
arrays and block arrays, independently of segment/range fragmentation. -/
theorem decoded_store_geometry {L : Limits} {h : Header} {data : ByteArray} {tp : TileParams}
    {hs : Option JPEG2000.Tier2.Headers.HeaderStream} {pb : Nat} {out : TileCodeBlocks}
    (ok : JPEG2000.Tier2.Headers.decodeWithStream L h data tp hs pb = .ok out) : StoreGeometry L out := by
  unfold JPEG2000.Tier2.Headers.decodeWithStream at ok
  obtain ⟨tile,hd,tail⟩ := bind_ok ok
  cases hs with
  | none => cases tail; exact raw_store hd
  | some stream =>
    simp only at tail
    split at tail <;> first | contradiction | (cases tail; exact raw_store hd)

/-! ## Header geometry before the aggregate checks -/

private def foldCounts (rect : Rect) (p : CompParams) (rs : List Nat) :=
  rs.foldl (fun (a : (Nat × Nat) × Nat) r =>
    ((a.1.1 + Header.numCodeBlocks rect p r,
      a.1.2 + Header.numPrecincts (Header.resRect rect p.levels r) (p.precincts.getD r Precinct.default)),
      a.2 + 1 + (bandsOf r).size))

private theorem fold_counts (rect : Rect) (p : CompParams) (rs : List Nat) (a : (Nat × Nat) × Nat) :
    (foldCounts rect p rs a).1 = rs.foldl (fun (b : Nat × Nat) r =>
      (b.1 + Header.numCodeBlocks rect p r, b.2 + Header.numPrecincts (Header.resRect rect p.levels r)
        (p.precincts.getD r Precinct.default))) a.1 ∧
    (foldCounts rect p rs a).2 ≤ a.2 + 4*rs.length := by
  induction rs generalizing a with
  | nil => exact ⟨rfl, by simp [foldCounts]⟩
  | cons r rs ih =>
    simp only [foldCounts, List.foldl_cons, List.length_cons] at ih ⊢
    obtain ⟨eq,cap⟩ := ih (_,a.2+1+(bandsOf r).size)
    refine ⟨eq,?_⟩
    dsimp only at cap
    have := bands_size r
    omega

private def levelCap (c : Coding) (d : Nat) := ∀ p ∈ c.comps, p.levels ≤ d

private theorem component_levels {c : Coding} {d : Nat} (h : levelCap c d) (i : Nat) :
    (c.comps.getD i default).levels ≤ d := by
  rw [Array.getD_eq_getD_getElem?]
  cases he : c.comps[i]? with
  | none => exact Nat.zero_le _
  | some p => exact h p (Array.mem_of_getElem? he)

private def headerComponentBudget (d : Nat) := 4 + 5*(d+1)

private def tileWork (L : Limits) (s : SIZ) (t : Nat) (c : Coding) (d : Nat) (levels : levelCap c d)
    (tot : Totals) : Counted (addTile L s t c tot) (s.csiz*headerComponentBudget d) := by
  unfold addTile
  rw [bind_pure]
  refine rangeLoop _ _ _ _ ?_
  intro i _ b
  let rect := compRect (tileRect s t) (s.components.getD i default)
  let p := c.comps.getD i default
  let rs := List.range (p.levels+1)
  let work := foldCounts rect p rs ((0,0),0)
  have ⟨erase,cap⟩ := fold_counts rect p rs ((0,0),0)
  change work.1 = tileCompCounts rect p at erase
  have len : rs.length = p.levels+1 := List.length_range
  change work.2 ≤ 0+4*rs.length at cap
  have hl : p.levels ≤ d := component_levels levels i
  dsimp only
  rw [← erase]
  refine widen (charge (1+rs.length+work.2) (chain (pay _ 1) (m := 2) ?_)) ?_
  · intro _ _
    exact chain (pay _ 1) (fun _ _ => chain (pay _ 1) (fun _ _ => pay _ 0))
  · unfold headerComponentBudget
    omega

/- Range-list entries, resolution visits and LL/HL/LH/HH counts inside
`tileCompCounts`, plus tile and component visits and the checks attempted in
order. `checkGeometry` admits the tile count and the full tile-component product
before this stage. -/
private def foldBudget (L : Limits) :=
  L.maxTiles + L.maxCodeBlocks*headerComponentBudget L.maxDecompLevels

private def gridWork {L : Limits} {mh : MainHeader} (defaults : Coding) (tiles : Array TileParams)
    (grid : checkGeometry L mh = .ok ()) (hd : levelCap defaults L.maxDecompLevels)
    (ht : ∀ tp ∈ tiles, levelCap tp.coding L.maxDecompLevels) :
    Counted (checkWork L mh.siz defaults tiles) (foldBudget L) := by
  let k := headerComponentBudget L.maxDecompLevels
  unfold checkWork
  refine widen (chain (rangeLoop (numTiles mh.siz) (1+mh.siz.csiz*k) _ _ ?_)
    (fun _ _ => pay _ 0)) ?_
  · intro t _ b
    let here := match tiles[b.2]? with
      | some tp => if tp.index = t then some tp.coding else none
      | none => none
    have good : levelCap (here.getD defaults) L.maxDecompLevels := by
      unfold here
      cases he : tiles[b.2]? with
      | none => exact hd
      | some tp =>
        dsimp only
        split
        · exact ht tp (Array.mem_of_getElem? he)
        · exact hd
    let a := tileWork L mh.siz t (here.getD defaults) L.maxDecompLevels good b.1
    change Counted (if here.isSome = true then _ else _) _
    by_cases hf : here.isSome = true <;> simp only [hf, ↓reduceIte] <;>
      exact widen (charge 1 (chain a (fun _ _ => pay _ 0))) (by simp [k])
  · obtain ⟨_,_,_,tiles,comps⟩ := (Resources.checkGeometry_ok_iff L mh).1 grid
    have := Nat.mul_le_mul_right k comps
    simp only [Nat.mul_add,Nat.mul_one,← Nat.mul_assoc,Nat.add_zero]
    exact Nat.add_le_add tiles this

/-! The late check can fail before there is a `Header.parse = .ok` witness.
Recover the effective decomposition bound from the already-read coding styles
and their merge at precisely that point. -/

private abbrev StyleOK (L : Limits) (s : CodingStyle) := s.levels.toNat ≤ L.maxDecompLevels

private theorem read_levels {L : Limits} {defined : Bool} {r r' : Bytes.Reader} {s : CodingStyle}
    (h : readCodingStyle L defined r = .ok (s,r')) : StyleOK L s := by
  unfold readCodingStyle at h
  obtain ⟨⟨levels,_⟩,_,h⟩ := bind_ok h
  obtain ⟨_,_,h⟩ := bind_ok h
  obtain ⟨_,hc,h⟩ := bind_ok h
  have bound : levels.toNat ≤ L.maxDecompLevels := checked hc
  obtain ⟨⟨_,_⟩,_,h⟩ := bind_ok h
  obtain ⟨⟨_,_⟩,_,h⟩ := bind_ok h
  obtain ⟨_,_,h⟩ := bind_ok h
  obtain ⟨⟨_,_⟩,_,h⟩ := bind_ok h
  dsimp only at h
  split at h <;> try contradiction
  obtain ⟨_,_,h⟩ := bind_ok h
  obtain ⟨⟨_,_⟩,_,h⟩ := bind_ok h
  dsimp only at h
  split at h <;> try contradiction
  all_goals
    simp only [pure_bind] at h
    cases defined <;> try dsimp only at h
    · cases h; exact bound
    · obtain ⟨⟨_,_⟩,_,h⟩ := bind_ok h
      obtain ⟨_,_,h⟩ := bind_ok h
      cases h; exact bound

private theorem cod_level {L : Limits} {d : COD} (read : HeaderWF.SegmentRead L (.cod d)) :
    StyleOK L d.style := by
  obtain ⟨_,h⟩ := read
  unfold parseCOD at h
  obtain ⟨⟨_,_⟩,_,h⟩ := bind_ok h
  obtain ⟨_,_,h⟩ := bind_ok h
  obtain ⟨⟨_,_⟩,_,h⟩ := bind_ok h
  dsimp only at h
  split at h <;> try contradiction
  simp only [pure_bind] at h
  obtain ⟨⟨_,_⟩,_,h⟩ := bind_ok h
  obtain ⟨_,_,h⟩ := bind_ok h
  obtain ⟨_,_,h⟩ := bind_ok h
  obtain ⟨⟨_,_⟩,_,h⟩ := bind_ok h
  try dsimp only at h
  split at h <;> try contradiction
  obtain ⟨⟨_,_⟩,hs,h⟩ := bind_ok h
  obtain ⟨_,_,h⟩ := bind_ok h
  cases h; exact read_levels hs

private theorem coc_level {L : Limits} {d : COC} (read : HeaderWF.SegmentRead L (.coc d)) :
    StyleOK L d.style := by
  obtain ⟨_,_,h⟩ := read
  unfold parseCOC at h
  obtain ⟨⟨_,_⟩,_,h⟩ := bind_ok h
  obtain ⟨⟨_,_⟩,_,h⟩ := bind_ok h
  obtain ⟨_,_,h⟩ := bind_ok h
  obtain ⟨⟨_,_⟩,hs,h⟩ := bind_ok h
  obtain ⟨_,_,h⟩ := bind_ok h
  cases h; exact read_levels hs

private def Styles (L : Limits) (cod : Option COD) (coc : Array COC) : Prop :=
  (∀ d, cod = some d → StyleOK L d.style) ∧ ∀ d ∈ coc, StyleOK L d.style

private theorem tile_styles {L : Limits} {t : Tile}
    (read : ∀ p ∈ t.parts, ∀ s ∈ p.segments, HeaderWF.SegmentRead L s) :
    Styles L (tileSegs t).cod (tileSegs t).coc := by
  unfold tileSegs
  rw [← Array.foldl_toList]
  let P := fun (x : TileSegs) => Styles L x.cod x.coc
  refine HeaderWF.list_foldl_inv P _ _ ?_ _ (by simp [P, Styles])
  intro p hp acc prev
  rw [← Array.foldl_toList]
  refine HeaderWF.list_foldl_inv P _ _ ?_ _ prev
  intro s hs acc prev
  have seen := read p (Array.mem_def.2 hp) s (Array.mem_def.2 hs)
  cases s with
  | cod d => exact ⟨fun _ eq => by cases eq; exact cod_level seen, prev.2⟩
  | coc d =>
    refine ⟨prev.1, fun x hx => ?_⟩
    rcases Array.mem_push.mp hx with hx | rfl
    · exact prev.2 x hx
    · exact coc_level seen
  | _ => exact prev

private abbrev OverrideOK (L : Limits) (ov : Overrides) :=
  ∀ o ∈ ov.coc, ∀ s, o = some s → StyleOK L s

private theorem override_levels {L : Limits} {pos n ds qs rs ov}
    (good : ∀ d ∈ ds, StyleOK L d.style) (h : mkOverrides pos n ds qs rs = .ok ov) : OverrideOK L ov := by
  unfold mkOverrides at h
  obtain ⟨_,hc,h⟩ := bind_ok h
  obtain ⟨_,_,h⟩ := bind_ok h
  obtain ⟨_,_,h⟩ := bind_ok h
  cases h
  refine HeaderWF.overrides_inv (StyleOK L) ?_ hc
  intro _ hx
  obtain ⟨d,hd,rfl⟩ := Array.mem_map.mp hx
  exact good d hd

private theorem mk_levels {L : Limits} {pos roi q p} {s : CodingStyle} (level : StyleOK L s)
    (h : mkComp pos s q roi = .ok p) : p.levels ≤ L.maxDecompLevels := by
  unfold mkComp at h
  obtain ⟨_,_,h⟩ := bind_ok h
  cases h; exact level

private theorem main_levels {L : Limits} {mh : MainHeader} {c : Coding}
    (style : Styles L (some mh.cod) mh.coc) (h : mainCoding mh = .ok c) : levelCap c L.maxDecompLevels := by
  unfold mainCoding at h
  obtain ⟨_,hov,h⟩ := bind_ok h
  obtain ⟨xs,hx,h⟩ := bind_ok h
  obtain ⟨_,_,h⟩ := bind_ok h
  obtain ⟨_,_,h⟩ := bind_ok h
  cases h
  refine HeaderWF.arrayMapM_mem _ _ _ ?_ xs hx
  intro _ _ _ hp
  exact mk_levels (HeaderWF.getD_getD _ (override_levels style.2 hov) (style.1 _ rfl)) hp

private theorem tile_levels {L : Limits} {mh : MainHeader} {ov : Overrides} {defaults c : Coding} {t : Tile}
    (main : Styles L (some mh.cod) mh.coc) (base : OverrideOK L ov) (hd : levelCap defaults L.maxDecompLevels)
    (tile : Styles L (tileSegs t).cod (tileSegs t).coc) (h : tileCoding mh ov defaults t = .ok c) :
    levelCap c L.maxDecompLevels := by
  unfold tileCoding at h
  dsimp only at h
  obtain ⟨_,_,h⟩ := bind_ok h
  split at h
  · obtain ⟨_,hs,h⟩ := bind_ok h
    obtain ⟨_,_,h⟩ := bind_ok h
    cases h; cases hs; exact hd
  · obtain ⟨_,hov,h⟩ := bind_ok h
    obtain ⟨xs,hx,h⟩ := bind_ok h
    obtain ⟨_,hs,h⟩ := bind_ok h
    obtain ⟨_,_,h⟩ := bind_ok h
    cases h; cases hs
    refine HeaderWF.arrayMapM_mem _ _ _ ?_ xs hx
    intro i _ _ hp
    apply mk_levels _ hp
    split
    · exact HeaderWF.getD_none _ (override_levels tile.2 hov) (by assumption)
    · exact tile.1 _ (by assumption)
    · exact HeaderWF.getD_getD _ base (main.1 _ rfl)

private def before {α β : Type} (x : Except Error α) {f : α → Except Error β} {n : Nat}
    (k : ∀ z, x = .ok z → Counted (f z) n) : Counted (x >>= f) n :=
  widen (chain (pay x 0) k) (by omega)

private theorem assembled_count (L : Limits) (corr : Bool) (parts : Array (Array TilePartHeader))
    (fuel i packets : Nat) (acc out : Array Tile)
    (ok : assembleTiles L corr parts fuel i packets acc = .ok out) : out.size ≤ acc.size+fuel := by
  induction fuel generalizing i packets acc with
  | zero => cases ok; omega
  | succ n ih =>
    simp only [assembleTiles] at ok
    split at ok
    · have := ih _ _ _ ok; omega
    · split at ok <;> try contradiction
      split at ok <;> try contradiction
      have := ih _ _ _ ok
      simp only [Array.size_push] at this
      omega

private theorem tile_count {L : Limits} {mh : MainHeader} {r tiles}
    (ok : parseTileParts L mh r = .ok tiles) : tiles.size ≤ numTiles mh.siz := by
  unfold parseTileParts at ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  simpa using assembled_count _ _ _ _ _ _ _ _ ok

/-- Tile-parameter array reservation, merge visits, tile descriptors and all
component rectangles, followed by the full header resolution fold. -/
def headerBudget (L : Limits) := 3*L.maxTiles + L.maxCodeBlocks + foldBudget L

/-- Public parse projected onto its tile rectangle arrays and `checkWork`. Earlier
parser stages cost zero in this projection. An earlier failure suppresses the whole fold.
A failure of an aggregate guard retains the complete component fold. -/
def parseWork (L : Limits) (data : ByteArray) : Counted (Header.parse L data) (headerBudget L) := by
  unfold Header.parse
  refine before _ (fun container _ => ?_)
  unfold parseCodestreamIn
  refine before _ (fun _ _ => ?_)
  refine before _ (fun ⟨mh,_⟩ read => ?_)
  refine before _ (fun ⟨⟩ grid => ?_)
  refine before _ (fun defaults made => ?_)
  refine before _ (fun ⟨_,_⟩ _ => ?_)
  refine before _ (fun tiles assembled => ?_)
  refine before _ (fun ov overrides => ?_)
  let locCost := 2+mh.siz.csiz
  have nt := tile_count assembled
  obtain ⟨_,_,_,tilesLimit,product⟩ := (Resources.checkGeometry_ok_iff L mh).1 grid
  refine widen (chain (mapArray tiles _ locCost ?_) (m := foldBudget L) ?_) ?_
  · intro t _
    exact widen (chain (pay _ 1) (fun _ _ => pay _ (1+mh.siz.csiz))) (by unfold locCost; omega)
  · intro tps merged
    have fields := (HeaderWF.parseMainHeader_fields read).2
    have styles : Styles L (some mh.cod) mh.coc :=
      ⟨fun d eq => cod_level (fields.cod d eq), fun d mem => coc_level (fields.coc d mem)⟩
    have hd := main_levels styles made
    have ht : ∀ tp ∈ tps, levelCap tp.coding L.maxDecompLevels := by
      refine HeaderWF.arrayMapM_mem _ _ _ ?_ _ merged
      intro t mem tp htp
      obtain ⟨_,hc,htp⟩ := bind_ok htp
      cases htp
      exact tile_levels styles (override_levels styles.2 overrides) hd
        (tile_styles (HeaderWF.parseTileParts_fields assembled t mem)) hc
    exact widen (chain (gridWork defaults tps grid hd ht) (fun _ _ => pay _ 0)) (by omega)
  · have side := Nat.le_trans nt tilesLimit
    have cells := Nat.le_trans (Nat.mul_le_mul_right mh.siz.csiz nt) product
    simp only [locCost, Nat.mul_add, Nat.mul_two, headerBudget]
    omega

/-- Late header geometry folds on every byte string, including rejected
codestreams and incomplete tile grids. -/
theorem parse_geometry_work (L : Limits) (data : ByteArray) :
    (parseWork L data).result = Header.parse L data ∧ (parseWork L data).work ≤ headerBudget L :=
  ⟨(parseWork ..).erase, (parseWork ..).within⟩


private theorem parsed_tiles {L : Limits} {data : ByteArray} {h : Header}
    (ok : Header.parse L data = .ok h) : h.tiles.size ≤ L.maxTiles := by
  unfold Header.parse at ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  unfold parseCodestreamIn at ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  obtain ⟨⟨mh,_⟩,_,ok⟩ := bind_ok ok
  obtain ⟨_,hg,ok⟩ := bind_ok ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  obtain ⟨⟨_,_⟩,_,ok⟩ := bind_ok ok
  obtain ⟨tiles,ht,ok⟩ := bind_ok ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  obtain ⟨tps,hm,ok⟩ := bind_ok ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  cases ok
  exact (map_size hm) ▸ Nat.le_trans (tile_count ht) ((Resources.checkGeometry_ok_iff L mh).1 hg).2.2.2.1

private def lookup (t : Nat) : List TileParams → Option TileParams × Nat
  | [] => (none,0)
  | tp::rest =>
    if tp.index == t then (some tp,1)
    else let q := lookup t rest; (q.1,q.2+1)

private theorem lookup_spec (t : Nat) (xs : List TileParams) :
    (lookup t xs).1 = xs.find? (·.index == t) ∧ (lookup t xs).2 ≤ xs.length := by
  induction xs with
  | nil => exact ⟨rfl,Nat.le_refl _⟩
  | cons x xs ih =>
    simp only [lookup, List.find?_cons, List.length_cons]
    cases he : x.index == t <;> simp [ih.1,ih.2]

private def compLayout (h : Header) (t c lim : Nat) (ht : h.tiles.size ≤ lim) :
    Counted (JPEG2000.Tier2.Geometry.ofHeader h t c) (4+lim) := by
  unfold JPEG2000.Tier2.Geometry.ofHeader
  dsimp only
  split
  · exact widen (pay _ 1) (by omega)
  · split
    · let found := lookup t h.tiles.toList
      have ⟨eq,cap⟩ := lookup_spec t h.tiles.toList
      rw [Array.find?_toList] at eq
      rw [← eq]
      simp only [Array.length_toList] at cap
      exact widen (pay _ (4+found.2)) (Nat.add_le_add_left (Nat.le_trans cap ht) _)
    · exact widen (pay _ 2) (by omega)

/-- One layout builds a component index range, reserves a component array and
searches the tile-parameter table once for the selected coding and again for
each component reached by the map. -/
def layoutBudget (L : Limits) := 2+L.maxTiles + L.maxComponents*(6+L.maxTiles)

private def layoutWork {L : Limits} {data : ByteArray} {h : Header}
    (parsed : Header.parse L data = .ok h) (t : Nat) : Counted (Layout.ofHeader h t) (layoutBudget L) := by
  have hc := (HeaderWork.parse_storage parsed).2.1
  have ht := parsed_tiles parsed
  unfold Layout.ofHeader
  dsimp only
  split
  · exact widen (pay _ 1) (by unfold layoutBudget; omega)
  · have ⟨eq,cap⟩ := lookup_spec t h.tiles.toList
    rw [Array.find?_toList] at eq
    rw [← eq]
    simp only [Array.length_toList] at cap
    refine widen (charge (1+(lookup t h.tiles.toList).2+h.siz.csiz)
      (chain (mapArray (Array.range h.siz.csiz) _ (4+L.maxTiles)
        (fun c _ => compLayout h t c _ ht)) (fun _ _ => pay _ 1))) ?_
    have := Nat.mul_le_mul_right (6+L.maxTiles) hc
    simp only [Array.size_range]
    unfold layoutBudget
    simp only [Nat.mul_add,Nat.mul_succ,Nat.mul_zero,Nat.zero_add] at *
    omega

private def packetGeom {L : Limits} {h : Header} {data : ByteArray} (parsed : Header.parse L data = .ok h)
    (tp : TileParams) (hs : Option JPEG2000.Tier2.Headers.HeaderStream) (pb : Nat) :
    Counted (JPEG2000.Tier2.Headers.decodeWithStream L h data tp hs pb) (layoutBudget L+initBudget L) := by
  unfold JPEG2000.Tier2.Headers.decodeWithStream
  refine widen (chain (n := layoutBudget L+initBudget L) ?_ (fun _ _ => pay _ 0)) (by omega)
  unfold decodeTilePacketsWith
  refine chain (layoutWork parsed tp.index) ?_
  rintro ⟨g,c⟩ layout
  refine before _ (fun _ _ => ?_)
  have bounds := HeaderWork.layout_budget parsed layout
  exact widen (chain (initWork L g bounds.1 bounds.2) (fun _ _ => pay _ 0)) (by omega)

private def centered {L : Limits} {h : Header} {data : ByteArray} (parsed : Header.parse L data = .ok h)
    (red t : Nat) (store : Option TileCodeBlocks) :
    Counted (JPEG2000.Decode.centeredTile L h data red t store) (layoutBudget L) := by
  unfold JPEG2000.Decode.centeredTile
  exact widen (chain (layoutWork parsed t) (fun _ _ => pay _ 0)) (by omega)

private def perTile (L : Limits) := layoutBudget L+initBudget L+layoutBudget L

private def nativeWork {L : Limits} {h : Header} {data : ByteArray} (parsed : Header.parse L data = .ok h)
    (red : Nat) : Counted (JPEG2000.Decode.nativeFromHeader L h data red) (L.maxTiles*perTile L) := by
  have tiles := (Resources.parse_within parsed).2.2.1.2.2.2.1
  unfold JPEG2000.Decode.nativeFromHeader
  refine before _ (fun initial _ => ?_)
  unfold JPEG2000.Decode.withTiles
  dsimp only
  split <;> refine before _ (fun idx _ => ?_) <;>
    refine widen (chain (rangeLoop (numTiles h.siz) (perTile L) _ _ ?_) (fun _ _ => pay _ 0))
      (by simpa using Nat.mul_le_mul_right (perTile L) tiles)
  all_goals
    intro t _ s
    cases h.tiles[s.2.2.2]? with
    | none =>
      simp only [pure_bind, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      exact widen (chain (centered parsed red t none) (fun _ _ => pay _ 0)) (by unfold perTile; omega)
    | some tp =>
      by_cases index : tp.index = t
      · simp only [index,↓reduceIte,pure_bind,Option.isSome_some]
        refine before _ (fun hs _ => ?_)
        refine chain (packetGeom parsed tp hs s.2.1) (fun store _ => ?_)
        exact widen (chain (centered parsed red t (some store)) (fun _ _ => pay _ 0)) (by omega)
      · simp only [index,↓reduceIte,pure_bind,Option.isSome_none,Bool.false_eq_true]
        exact widen (chain (centered parsed red t none) (fun _ _ => pay _ 0)) (by unfold perTile; omega)

/-- The geometry projection at the ordinary codestream API. It measures the
header's component rectangles and quota folds, then each visited tile's packet
layout and initialization, and the layout built for centred reconstruction.
A missing tile skips packet setup. Any earlier rejection stops its continuation. -/
def decodeWork (L : Limits) (data : ByteArray) (red : Nat) :
    Counted (decodeCodestream L data red) (headerBudget L + L.maxTiles*perTile L) := by
  unfold decodeCodestream
  refine before _ (fun _ _ => ?_)
  exact chain (parseWork L data) (fun _ parsed => nativeWork parsed red)

/-- Closed bound on header and packet geometry construction and the two tile
layout selections. `p` bounds one layout and `q` the nested initialization loops. -/
def geometryBudget (L : Limits) : Nat :=
  let t := L.maxTiles
  let c := L.maxComponents
  let b := L.maxCodeBlocks
  let d := L.maxDecompLevels+1
  let p := 2+t+c*(6+t)
  let q := c*(5+d*(17+L.maxPrecincts*(78+87*b)))
  4*t+b*(5+5*d)+t*(p+q+p)

private theorem public_budget (L : Limits) : headerBudget L+L.maxTiles*perTile L ≤ geometryBudget L := by
  have prec : packetPrecinctBudget L = 78+87*L.maxCodeBlocks := by
    unfold packetPrecinctBudget precinctBudget geomBandBudget stateBudget stateBandBudget
    omega
  simp only [geometryBudget, perTile, layoutBudget, initBudget, packetComponentBudget, packetResolutionBudget,
    prec, headerBudget, foldBudget, headerComponentBudget]
  apply Nat.add_le_add_right
  simp only [Nat.mul_add, Nat.mul_succ, Nat.mul_zero, Nat.zero_add]
  omega

/-- Public codestream geometry work, on successful and rejecting byte strings. -/
theorem decode_geometry_work (L : Limits) (data : ByteArray) (red : Nat) :
    (decodeWork L data red).result = decodeCodestream L data red ∧
      (decodeWork L data red).work ≤ geometryBudget L :=
  ⟨(decodeWork ..).erase, Nat.le_trans (decodeWork ..).within (public_budget L)⟩

/-- Project the same geometry charge through the public image API and its colour
continuation, retaining either diagnostic and the work preceding it. -/
def imageWork (L : Limits) (data : ByteArray) (opts : DecodeOptions) :
    Counted (JPEG2000.decode L data opts) (geometryBudget L) := by
  unfold JPEG2000.decode
  exact widen (chain (decodeWork L data opts.reduce) (fun _ _ => pay _ 0)) (by simpa using public_budget L)

/-- The ordinary image API preserves the geometry meter and its limit-only bound. -/
theorem image_geometry_work (L : Limits) (data : ByteArray) (opts : DecodeOptions) :
    (imageWork L data opts).result = JPEG2000.decode L data opts ∧
      (imageWork L data opts).work ≤ geometryBudget L :=
  ⟨(imageWork ..).erase, (imageWork ..).within⟩

end JPEG2000.Spec.Resources.GeometryInit
