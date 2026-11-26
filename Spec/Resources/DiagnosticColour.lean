import Spec.Resources.DiagnosticComponent

/-!
# Diagnostics through centred tile colour (Plan.md §§3–5, 7, S3; T.800 B.2–3, G.2–3)

The layout lookup is charged by the packet trace. After it succeeds, the component
trace supplies the ordered prefix, including discarded compact attempts. Colour
dispatch checks three reconstructed domains before examining their shapes. The
optional compact colour kernels and the lazy RCT readers construct no diagnostics.
-/

namespace JPEG2000.Spec.Resources.DiagnosticColour

open JPEG2000.Header JPEG2000.NativeOutput JPEG2000.Tier2.Geometry
open JPEG2000.TileDispatch (Spatial)
open DiagnosticCost
open DiagnosticComponent (errors errorText beforeColour tileErrors)

noncomputable section

variable {α β : Type} {cap : Nat}

private abbrev Single (cap : Nat) (r : Except Error α) :=
  { t : Trace cap r 1 // t.messages.map Sigma.fst = (errors r).flatMap errorText }

private def silent (a : α) : Single cap (.ok a) := ⟨doneTrace a,rfl⟩

private def refusal {s : String} (b : Built cap s) : Single (α := α) cap (.error (.malformed (.at .mct) s)) :=
  ⟨⟨[⟨s,b⟩],by simp,by intro e eq; cases eq; exact ⟨Nat.zero_le _,⟨s,b⟩,by simp,rfl⟩⟩,rfl⟩

private def finish {x : Except Error α} (f : α → β) (u : Single cap x) :
    Single cap (x >>= fun a => pure (f a)) := by
  cases x with
  | ok a => exact ⟨⟨u.val.messages,u.val.countBound,by intros; contradiction⟩,u.property⟩
  | error e => exact ⟨⟨u.val.messages,u.val.countBound,by intro _ eq; cases eq; exact u.val.origin _ rfl⟩,u.property⟩

private theorem finish_messages {x : Except Error α} (f : α → β) (u : Single cap x) :
    (finish f u).val.messages = u.val.messages := by cases x <;> rfl

private def workspace (L : Limits) (n : Nat) (bound : n ≤ cap) (next : Unit → Except Error α)
    (run : ∀ u, Single cap (next u)) :
    Single cap (L.check (.at .mct) .workSamples n >>= next) := by
  unfold Limits.check Limits.checkLe
  split
  · exact run ()
  · exact ⟨⟨[],by simp,by intro e eq; cases eq; exact ⟨Nat.zero_le _,bound⟩⟩,rfl⟩

private abbrev Sides (s : Source) (cap : Nat) := s.width ≤ cap ∧ s.height ≤ cap

private def shapeText (y cb cr : Source) (hy : Sides y cap) (hb : Sides cb cap) (hr : Sides cr cap) :
    Built cap s!"component transform on planes {y.width}×{y.height}, {cb.width}×{cb.height}, {cr.width}×{cr.height}" :=
  let yText := catExpr (catExpr (catExpr (litExpr cap "component transform on planes ") (decExpr hy.1))
    (litExpr cap "×")) (decExpr hy.2)
  let cbText := catExpr (catExpr (catExpr (catExpr yText (litExpr cap ", ")) (decExpr hb.1))
    (litExpr cap "×")) (decExpr hb.2)
  closeExpr (catExpr (catExpr (catExpr (catExpr cbText (litExpr cap ", ")) (decExpr hr.1))
    (litExpr cap "×")) (decExpr hr.2)) (by decide) (by decide)

private def reversible (L : Limits) (y cb cr : Source)
    (work : y.width*y.height + cb.width*cb.height + cr.width*cr.height ≤ cap)
    (hy : Sides y cap) (hb : Sides cb cap) (hr : Sides cr cap) :
    Single cap (JPEG2000.ReversibleDispatch.colour L y cb cr) := by
  unfold JPEG2000.ReversibleDispatch.colour
  apply workspace L _ work
  intro _
  split
  · rename_i shape
    cases y <;> cases cb <;> cases cr <;> try exact silent _
    rename_i a b c
    dsimp only at ⊢
    split
    · -- The compact kernel repeats the shape check on precisely the admitted planes.
      unfold JPEG2000.MCT.rctInverse JPEG2000.MCT.apply3
      dsimp only [Source.width,Source.height] at shape
      rw [dite_eq_left shape]
      exact silent _
    · exact silent _
  · exact refusal (shapeText y cb cr hy hb hr)

private abbrev IPlane := JPEG2000.IrreversibleDispatch.Spatial

private def irreversible (L : Limits) (y cb cr : IPlane)
    (work : rectArea y.rect + rectArea cb.rect + rectArea cr.rect ≤ cap) :
    Single cap (JPEG2000.IrreversibleDispatch.ict L y cb cr) := by
  unfold JPEG2000.IrreversibleDispatch.ict
  apply workspace L _ work
  intro _
  split
  · cases trial : JPEG2000.IrreversibleDispatch.compactICT y cb cr with
    | some rgb => exact silent rgb
    | none =>
      have rect (p : IPlane) : p.toWide.rect = p.rect := by cases p <;> rfl
      unfold JPEG2000.WideICT.ictInverse
      rw [bind_assoc]
      apply workspace L _ (by simpa only [rect] using work)
      intro _
      split
      · exact silent _
      · exact refusal (oneFixed _ (by decide))
  · exact refusal (oneFixed _ (by decide))

private abbrev cells (s : Spatial) := s.source.width * s.source.height

private theorem irrevArea (p : IPlane) : rectArea p.rect = cells (.irrev p) := by
  cases p with
  | compact r _ p hw hh =>
    change r.width*r.height = p.width*p.height
    rw [hw,hh]
  | wide => rfl

private def sources (L : Limits) (mct : Bool) (ps : Array Spatial)
    (bounds : ∀ (i : Nat) (p : Spatial), ps[i]? = some p → Sides p.source cap)
    (work : ∀ y cb cr, ps[0]? = some y → ps[1]? = some cb → ps[2]? = some cr →
      cells y + cells cb + cells cr ≤ cap) :
    Single cap (JPEG2000.TileDispatch.sources L mct ps) := by
  unfold JPEG2000.TileDispatch.sources
  split
  · exact silent _
  · dsimp only
    split
    · rename_i y cb cr hy hb hr
      apply finish _ (reversible L y cb cr (work _ _ _ hy hb hr)
        (bounds 0 _ hy) (bounds 1 _ hb) (bounds 2 _ hr))
    · rename_i y cb cr hy hb hr
      apply finish _ (irreversible L y cb cr (by simpa only [irrevArea] using work _ _ _ hy hb hr))
    · exact refusal (oneFixed _ (by decide))

private theorem parsedHeader {L : Limits} {data : ByteArray} {red : Nat} {h dst}
    (entry : PublicPacketWork.prepareTiles L data red = .ok (h,dst)) : Header.parse L data = .ok h := by
  obtain ⟨_,_,tail⟩ := Tier2Equiv.bind_ok entry
  obtain ⟨_,parsed,tail⟩ := Tier2Equiv.bind_ok tail
  obtain ⟨_,_,ret⟩ := Tier2Equiv.bind_ok tail
  cases ret
  exact parsed

private theorem packets {L : Limits} {h : Header} {data : ByteArray} {idx t j pb a}
    (parsed : Header.parse L data = .ok h)
    (store : SegmentHistory.packetStore L h data idx t j pb = .ok a) :
    ∃ b, TileDispatch.Packets L h data t a b := by
  unfold SegmentHistory.packetStore at store
  split at store
  · cases store; exact ⟨none,.absent⟩
  rename_i tp selected
  obtain ⟨hs,_,tail⟩ := Tier2Equiv.bind_ok store
  obtain ⟨out,decoded,ret⟩ := Tier2Equiv.bind_ok tail
  cases ret
  have index : tp.index = t := by
    unfold PacketTraversal.presentAt at selected
    split at selected <;> try contradiction
    split at selected <;> cases selected
    assumption
  have rel := Tier2Equiv.decodeWithStream_sim L h data tp hs pb
    (fun _ _ layout => Tier2Equiv.ofHeader_wf (Equiv.parse_dxdy parsed) layout)
  rw [decoded] at rel
  cases spec : Spec.Tier2.decodeWithStream L h data tp hs pb with
  | ok b => exact ⟨_,.present index decoded spec⟩
  | error => rw [spec] at rel; contradiction

private theorem ceil_le (a d : Nat) : cdiv a d ≤ a := by
  cases d with
  | zero => simp [cdiv]
  | succ d =>
    apply Nat.le_of_lt_succ
    apply (Nat.div_lt_iff_lt_mul (Nat.succ_pos _)).2
    rw [Nat.succ_mul,Nat.mul_succ]
    omega

private theorem gridThree (g : Progression.Layout) (red : Nat) (three : 3 ≤ g.numComps) :
    let area := fun i => rectArea (Assemble.reduceRect (g.comp i).rect red)
    area 0 + area 1 + area 2 ≤ tileCells g red := by
  obtain ⟨tile,layers,⟨cs⟩⟩ := g
  change 3 ≤ cs.length at three
  match cs with
  | [] | [_] | [_,_] => simp at three
  | x :: y :: z :: tail =>
    simp [tileCells,Progression.Layout.comp,Array.getD_eq_getD_getElem?,rectArea,Nat.add_assoc]

/-- At the entry to colour dispatch, every source has its parsed reduced width and height,
even when a zero axis makes its area uninformative. The first three areas together fit
the previously admitted workspace. Neither conclusion assumes a successful MCT. -/
theorem source_geometry {L : Limits} {data : ByteArray} {h dst red idx t j pb a g coding ps}
    (entry : PublicPacketWork.prepareTiles L data red = .ok (h,dst))
    (store : SegmentHistory.packetStore L h data idx t j pb = .ok a)
    (layout : Progression.Layout.ofHeader h t = .ok (g,coding))
    (reached : beforeColour L h data g coding a red = .ok ps) :
    (∀ (i : Nat) (p : Spatial), ps[i]? = some p →
      let r := Assemble.reduceRect (g.comp i).rect red
      p.source.width = r.width ∧ p.source.height = r.height ∧
      p.source.width ≤ 2^32 ∧ p.source.height ≤ 2^32) ∧
    (∀ (y cb cr : Spatial), ps[0]? = some y → ps[1]? = some cb → ps[2]? = some cr →
      TileColorPlacement.area y.source + TileColorPlacement.area cb.source + TileColorPlacement.area cr.source ≤
        tileCells g red) ∧ tileCells g red ≤ L.maxWorkSamples := by
  have parsed := parsedHeader entry
  obtain ⟨b,origin⟩ := packets parsed store
  obtain ⟨u,admitted,loop⟩ := Tier2Equiv.bind_ok reached
  cases u
  have sim := TileDispatch.components_equiv parsed layout origin red
  rw [loop] at sim
  have lift {γ δ : Type} {x : γ} {res : Except Error δ} {P : γ → δ → Prop}
      (rel : Tier2Equiv.Res P (.ok x) res) : ∃ y, P x y := by
    cases res with
    | ok y => exact ⟨y,rel⟩
    | error => contradiction
  obtain ⟨out,agree⟩ := lift sim
  obtain ⟨count,grid⟩ := NativePlacement.tile_grid (red := red) parsed layout
  have dims (i : Nat) (p : Spatial) (read : ps[i]? = some p) :
      let r := Assemble.reduceRect (g.comp i).rect red
      p.source.width = r.width ∧ p.source.height = r.height ∧
        p.source.width ≤ 2^32 ∧ p.source.height ≤ 2^32 := by
    obtain ⟨hi,rfl⟩ := Array.getElem?_eq_some_iff.mp read
    obtain ⟨comp,geo⟩ := agree.2.2 i hi
    have w := comp.centered.1.trans geo.2.1
    have hgt := comp.centered.2.1.trans geo.2.2
    obtain ⟨_,_,x,_,_,y⟩ := grid i (agree.1 ▸ hi)
    have xmax : (Assemble.reduceRect (g.comp i).rect red).x1 ≤ 2^32 :=
      Nat.le_trans x (Nat.le_trans (ceil_le ..) (Nat.le_trans (ceil_le ..) (Nat.le_of_lt h.siz.xsiz.toNat_lt)))
    have ymax : (Assemble.reduceRect (g.comp i).rect red).y1 ≤ 2^32 :=
      Nat.le_trans y (Nat.le_trans (ceil_le ..) (Nat.le_trans (ceil_le ..) (Nat.le_of_lt h.siz.ysiz.toNat_lt)))
    exact ⟨w,hgt,Nat.le_trans (Nat.le_of_eq w) (Nat.le_trans (Nat.sub_le ..) xmax),
      Nat.le_trans (Nat.le_of_eq hgt) (Nat.le_trans (Nat.sub_le ..) ymax)⟩
  refine ⟨dims,?_,(Limits.check_eq_ok_iff ..).1 admitted⟩
  intro y cb cr hy hb hr
  obtain ⟨yw,yh,_⟩ := dims 0 y hy
  obtain ⟨bw,bh,_⟩ := dims 1 cb hb
  obtain ⟨rw_,rh,_⟩ := dims 2 cr hr
  simpa only [TileColorPlacement.area,yw,yh,bw,bh,rw_,rh,rectArea] using
    gridThree g red (agree.1 ▸ (Array.getElem?_eq_some_iff.mp hr).choose)

/-- Scalar bound for component diagnostics, typed colour checks and each decimal dimension. -/
def scalarCap (L : Limits) := max (DiagnosticComponent.scalarCap L) (2^32)

/-- Each component can discard one compact error and return one definitive error.
Colour dispatch contributes at most one further message. -/
def eventCap (L : Limits) := 2*L.maxComponents + 1

private theorem work_le (L : Limits) : L.maxWorkSamples ≤ scalarCap L :=
  Nat.le_trans (Nat.le_trans (Nat.le_max_left ..) (Nat.le_max_right ..)) (Nat.le_max_left ..)

/-- Diagnostics of the actual colour call at a successful component prefix. A typed
work refusal carries its scalar, and a textual refusal carries its single construction. -/
def sourcesTrace {L : Limits} {data : ByteArray} {h dst red idx t j pb a g coding ps}
    (entry : PublicPacketWork.prepareTiles L data red = .ok (h,dst))
    (store : SegmentHistory.packetStore L h data idx t j pb = .ok a)
    (layout : Progression.Layout.ofHeader h t = .ok (g,coding))
    (reached : beforeColour L h data g coding a red = .ok ps) :
    let call := JPEG2000.TileDispatch.sources L (coding.mctApplies h.siz) ps
    { z : Trace (scalarCap L) call 1 // z.messages.map Sigma.fst = (errors call).flatMap errorText } := by
  obtain ⟨dims,three,admitted⟩ := source_geometry entry store layout reached
  apply sources
  · intro i p read
    obtain ⟨_,_,hw,hh⟩ := dims i p read
    exact ⟨Nat.le_trans hw (Nat.le_max_right ..),Nat.le_trans hh (Nat.le_max_right ..)⟩
  · intro y cb cr hy hb hr
    exact Nat.le_trans (three y cb cr hy hb hr) (Nat.le_trans admitted (work_le L))

private def afterSuccess {γ : Type} (x : Except Error α) (f : ∀ a, x = .ok a → List γ) : List γ :=
  match x with
  | .error _ => []
  | .ok a => f a rfl

/-- The certified colour expressions following a component prefix. A failed prefix
stops before dispatch. A successful prefix supplies the actual spatial array. -/
def colourMessages {L : Limits} {data : ByteArray} {h dst red idx t j pb a g coding}
    (entry : PublicPacketWork.prepareTiles L data red = .ok (h,dst))
    (store : SegmentHistory.packetStore L h data idx t j pb = .ok a)
    (layout : Progression.Layout.ofHeader h t = .ok (g,coding)) : List (Σ s, Built (scalarCap L) s) :=
  afterSuccess (beforeColour L h data g coding a red) fun _ reached =>
    (sourcesTrace entry store layout reached).val.messages

private def extend {x : Except Error α} {f : α → Except Error β} {es : List Error} {n : Nat}
    (pre : Trace cap x n) (order : pre.messages.map Sigma.fst = (es ++ errors x).flatMap errorText)
    (next : ∀ a, x = .ok a → Single cap (f a)) :
    { z : Trace cap (x >>= f) (n+1) //
        z.messages = pre.messages ++ afterSuccess x (fun a h => (next a h).val.messages) ∧
        z.messages.map Sigma.fst = (es ++ errors (x >>= f)).flatMap errorText } := by
  cases x with
  | error e =>
    exact ⟨⟨pre.messages,Nat.le_succ_of_le pre.countBound,by intro _ eq; cases eq; exact pre.origin _ rfl⟩,
      (List.append_nil _).symm,order⟩
  | ok a =>
    let c := next a rfl
    refine ⟨includeTrace pre c.val,rfl,?_⟩
    simp only [includeTrace,List.map_append,order,c.property,errors,List.append_nil,List.flatMap_append,
      Equiv.ok_bind]

section

variable {L : Limits} {data : ByteArray} {red : Nat} {v : PacketTraversal.TileVisit}
variable (hit : v ∈ (PublicPacketWork.measure L data red).1) {h dst idx a g coding}
variable (entry : PublicPacketWork.prepareTiles L data red = .ok (h,dst))
variable (ranks : NativeCost.ranks L h = .ok idx)
variable (store : SegmentHistory.packetStore L h data idx v.tile v.cursor v.passesBefore = .ok a)
variable (layout : Progression.Layout.ofHeader h v.tile = .ok (g,coding))

private abbrev prefixTrace :=
  (DiagnosticComponent.tileTrace hit entry ranks store layout).trace.raiseCap
    (show DiagnosticComponent.scalarCap L ≤ scalarCap L from Nat.le_max_left ..)

private def complete :
    let call := JPEG2000.Decode.centeredTile L h data red v.tile a
    { z : Trace (scalarCap L) call (eventCap L) //
      z.messages = (prefixTrace hit entry ranks store layout).messages ++ colourMessages entry store layout ∧
      z.messages.map Sigma.fst = (tileErrors L h data g coding a red ++ errors call).flatMap errorText } := by
  dsimp only
  let pre := prefixTrace hit entry ranks store layout
  have order := congrArg (List.map Prod.fst)
    ((DiagnosticComponent.tileTrace hit entry ranks store layout).trace.raiseCap_events
      (show DiagnosticComponent.scalarCap L ≤ scalarCap L from Nat.le_max_left ..))
  simp only [List.map_map,Function.comp_def] at order
  have first := order.trans (DiagnosticComponent.messages hit entry ranks store layout).2
  have run : JPEG2000.Decode.centeredTile L h data red v.tile a =
      (beforeColour L h data g coding a red >>= fun ps => do
        let ss ← JPEG2000.TileDispatch.sources L (coding.mctApplies h.siz) ps
        pure ⟨g,coding,ss,0⟩) := by
    simp only [JPEG2000.Decode.centeredTile,layout,Equiv.ok_bind,DiagnosticComponent.tile_eq,bind_assoc]
  rw [run]
  let pack := fun (ss : Array Source) => (⟨g,coding,ss,0⟩ : JPEG2000.Decode.CenteredTile)
  let z := extend pre first (fun _ reached => finish pack (sourcesTrace entry store layout reached))
  refine ⟨z.val,?_,z.property.2⟩
  simpa only [finish_messages,colourMessages] using z.property.1

/-- The trace from an actual packet store and successful layout through the returned
centred tile, including all earlier component reader visits and ordered compact retries. -/
def centeredTrace : DiagnosticComponent.Report (DiagnosticComponent.ReaderVisit L data) (scalarCap L)
    (JPEG2000.Decode.centeredTile L h data red v.tile a) (eventCap L) :=
  let z := complete hit entry ranks store layout
  ⟨(DiagnosticComponent.tileTrace hit entry ranks store layout).visits,z.val,
    tileErrors L h data g coding a red,z.property.2⟩

/-- The ordered component trees are an exact prefix, including on colour failure.
The full text sequence consists of all reached compact retries and the terminal
text, if present. Packing a successful centred tile emits no additional message. -/
theorem messages :
    let p := (DiagnosticComponent.tileTrace hit entry ranks store layout).trace
    let z := centeredTrace hit entry ranks store layout
    z.trace.messages =
      (p.raiseCap (show DiagnosticComponent.scalarCap L ≤ scalarCap L from Nat.le_max_left ..)).messages ++
        colourMessages entry store layout ∧
    z.trace.messages.map Sigma.fst =
      (tileErrors L h data g coding a red ++ errors (JPEG2000.Decode.centeredTile L h data red v.tile a)).flatMap
        errorText :=
  (complete hit entry ranks store layout).property

/-- Construction work, logical storage and the retained diagnostic for a visited tile
after packet and layout selection. The caller's rendering charge is separate. -/
theorem public_colour :
    let z := centeredTrace hit entry ranks store layout
    let budget := eventCap L * Text.workBound (scalarCap L) 128 24
    (z.trace.messages.map (fun m => m.2.tree.work)).sum ≤ budget ∧
    (z.trace.messages.map (fun m => m.2.tree.storage)).sum ≤ budget ∧
    ∀ e, JPEG2000.Decode.centeredTile L h data red v.tile a = .error e →
      storedPayload false e ≤ 6 + Text.byteBound (scalarCap L) 128 24 + 2*bits (scalarCap L) := by
  let t := (centeredTrace hit entry ranks store layout).trace
  exact ⟨(trace_cost t).1,trace_storage t,fun _ bad => trace_retained t bad⟩

end

end

end JPEG2000.Spec.Resources.DiagnosticColour
