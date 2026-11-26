import JPEG2000.TileDispatch
import Spec.ReversibleDispatch
import Spec.IrreversibleDispatch
import Spec.WideHeaderBounds

/-!
# Checked tile reconstruction (Plan.md §§3–5, 7; T.800 B, D, E, F and G)

Compare the public mixed-transform component dispatch to the independent packet and
wavelet specification, including rejection at the requested reduction.
-/

namespace JPEG2000.Spec.TileDispatch

open Header JPEG2000.Tier2.Geometry JPEG2000.Tier2.Packet JPEG2000.TileDispatch
open Tier2Equiv (Res)

/-- The source selected by the public component loop carries the effective transform.
For 9/7 the reference plane contains the specification's exact rational wavelet cells. -/
def ComponentRel (tc : TileCompGeom) (F red : Nat) (s : Spatial) (p : Decode.CellPlane) : Prop :=
  match s with
  | .rev a => tc.params.transform = .reversible53 ∧ ReversibleDispatch.Exact a p
  | .irrev a =>
    let r := Assemble.reduceRect tc.rect red
    let nl := tc.params.levels - red
    tc.params.transform = .irreversible97 ∧ ∃ es, p = Decode.idwt false es r nl ∧
      IrreversibleDispatch.SpatialAgrees a r F nl (Decode.dec97 es nl)

private theorem entries_admit {L : Limits} {tc : TileCompGeom} {depth F red : Nat}
    {rs : Decode.SpecPrecs} {v : List Decode.Entry × Nat}
    (ok : WideAssembly.entries L tc depth F red rs = .ok v) :
    red ≤ tc.params.levels ∧ rectArea (Assemble.reduceRect tc.rect red) ≤ L.maxWorkSamples := by
  unfold WideAssembly.entries at ok
  dsimp only at ok
  split at ok <;> try contradiction
  obtain ⟨_, init, _⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨u, check, _⟩ := Tier2Equiv.bind_ok init
  cases u
  exact ⟨by omega, (Limits.check_eq_ok_iff ..).1 check⟩

private theorem irrev_complete {L : Limits} {data : ByteArray} {tc : TileCompGeom} {depth F red : Nat}
    {ps : Array (Array PrecinctOut)} {rs : Decode.SpecPrecs} {es : List Decode.Entry × Nat}
    (irr : tc.params.transform = .irreversible97) (levels : tc.params.levels ≤ L.maxDecompLevels)
    (ordered : let r := Assemble.reduceRect tc.rect red; r.x0 ≤ r.x1 ∧ r.y0 ≤ r.y1)
    (collected : WideAssembly.entries L tc depth F red rs = .ok es)
    (bands : ∃ p, JPEG2000.WideAssembly.tileComp L data tc depth F red ps = .ok p ∧
      p.rect = Assemble.reduceRect tc.rect red) :
    ∃ s, JPEG2000.IrreversibleDispatch.component L data tc depth F red ps = .ok s := by
  obtain ⟨reduce, work⟩ := entries_admit collected
  obtain ⟨p, assembled, rect⟩ := bands
  obtain ⟨hx, hy⟩ := ordered
  have lc : L.check Assemble.loc .decompLevels tc.params.levels = .ok () :=
    (Limits.check_eq_ok_iff ..).2 levels
  have lifted : ∃ q, JPEG2000.WideDWT97.idwt97 L p (tc.params.levels - red) = .ok q :=
    ⟨_, (WideDWT97.idwt97_spec ..).2 ⟨Nat.le_trans (Nat.sub_le ..) levels, rect ▸ work,
      rect ▸ hx, rect ▸ hy, rfl⟩⟩
  obtain ⟨q, lifted⟩ := lifted
  unfold JPEG2000.IrreversibleDispatch.component
  simp only [irr, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, Nat.not_lt.mpr reduce,
    lc, Equiv.ok_bind, Nat.not_lt.mpr hx, Nat.not_lt.mpr hy, or_self]
  unfold JPEG2000.IrreversibleDispatch.tryCompact
  cases compact : JPEG2000.IrreversibleDispatch.compactBands L data tc depth F red ps with
  | error => exact ⟨_, by simp only [Equiv.ok_bind, assembled, lifted]; rfl⟩
  | ok b =>
    cases packed : JPEG2000.IrreversibleDispatch.compactSpatial b (Assemble.reduceRect tc.rect red)
        (tc.params.levels - red) F <;> exact ⟨_, by simp only [Equiv.ok_bind, packed, assembled, lifted]; rfl⟩

/-- Both components reject, or both succeed with exact 5/3 cells or C8-bounded 9/7 cells.
The parser provides the level, precision and geometry premises even for omitted tiles. -/
theorem component_equiv {L : Limits} {data : ByteArray} {h : Header} {t : Nat}
    {g : Progression.Layout} {coding : Coding} (parsed : Header.parse L data = .ok h)
    (layout : Progression.Layout.ofHeader h t = .ok (g,coding)) (store : Option TileCodeBlocks)
    (c : Fin g.numComps) (red : Nat)
    (wf : Equiv.PrecsWF (g.comp c) ((store.map (·.comps.getD c #[])).getD #[]))
    (ranges : Equiv.BlocksIn data ((store.map (·.comps.getD c #[])).getD #[])) :
    let tc := g.comp c
    let depth := (h.siz.components.getD c default).depth.toNat
    let F := Assemble.fracBitsOf h.siz (coding.mctApplies h.siz) c
    let ps := (store.map (·.comps.getD c #[])).getD #[]
    Res (fun s v => ComponentRel tc F red s v.1) (component L h data g coding store c red)
      (Decode.tileComp L tc depth F red (Equiv.imagePrecs data ps)) := by
  let tc := g.comp c
  let depth := (h.siz.components.getD c default).depth.toNat
  let F := Assemble.fracBitsOf h.siz (coding.mctApplies h.siz) c
  let ps := (store.map (·.comps.getD c #[])).getD #[]
  dsimp only
  obtain ⟨bounds, ordered⟩ := WideHeaderBounds.parsed_component_bounds parsed layout c red
  have params := (HeaderWF.headerWF _ _ _ parsed _ _ _ layout).1 c
  unfold component
  cases tr : (g.comp c).params.transform with
  | reversible53 =>
    have eq := ReversibleDispatch.tileComp_equiv L data tc depth F red ps tr params wf ranges
      bounds.levels ordered (fun r b _ _ => bounds.block_planes r b)
    have same : JPEG2000.ReversibleDispatch.component L data h.siz g coding store c red =
      JPEG2000.ReversibleDispatch.tileComp L data tc depth F red ps := by cases store <;> rfl
    rw [same]
    change Res _ (Spatial.rev <$> JPEG2000.ReversibleDispatch.tileComp L data tc depth F red ps)
      (Decode.tileComp L tc depth F red (Equiv.imagePrecs data ps))
    cases fast : JPEG2000.ReversibleDispatch.tileComp L data tc depth F red ps <;>
      cases spec : Decode.tileComp L tc depth F red (Equiv.imagePrecs data ps) <;>
      rw [fast, spec] at eq
    · trivial
    · contradiction
    · contradiction
    · exact ⟨tr, eq⟩
  | irreversible97 =>
    change Res _ (Spatial.irrev <$> JPEG2000.IrreversibleDispatch.component L data tc depth F red ps)
      (Decode.tileComp L tc depth F red (Equiv.imagePrecs data ps))
    rw [WideAssembly.tileComp_eq_finish]
    cases fast : JPEG2000.IrreversibleDispatch.component L data tc depth F red ps with
    | ok s =>
      obtain ⟨es, hs, agree⟩ := IrreversibleDispatch.component_c8 params wf ranges fast
      rw [hs, Equiv.ok_bind]
      exact ⟨tr, es, by simp only [tc, tr]; rfl, agree⟩
    | error e =>
      cases spec : WideAssembly.entries L tc depth F red (Equiv.imagePrecs data ps) with
      | error => trivial
      | ok es =>
        have eq := WideAssembly.tileComp_equiv L data tc depth F red ps bounds.levels ordered
          (fun r b _ _ => bounds.block_planes r b) wf ranges
        rw [spec] at eq
        cases bands : JPEG2000.WideAssembly.tileComp L data tc depth F red ps with
        | error => rw [bands] at eq; contradiction
        | ok p =>
          rw [bands] at eq
          obtain ⟨_, ok⟩ := irrev_complete tr bounds.levels ordered spec ⟨p, bands, eq.1.1⟩
          rw [fast] at ok
          contradiction

/-- The samplewise native placement premise on a centred component. -/
def PlaneRel (F : Nat) (rev : Bool) (s : NativeOutput.Source) (p : Decode.CellPlane) : Prop :=
  s.width = p.width ∧ s.height = p.height ∧ p.cells.size = p.width * p.height ∧
    ∀ j (hj : j < p.cells.size), ∃ z, s.get? j = some z ∧ NativeSample.CenteredAgrees F rev z p.cells[j]

/-- A reconstructed component already meets the centred sample claim outside the MCT. -/
theorem ComponentRel.centered {tc : TileCompGeom} {F red : Nat} {s : Spatial} {p : Decode.CellPlane}
    (rel : ComponentRel tc F red s p) :
    PlaneRel F (tc.params.transform == .reversible53) s.source p := by
  cases s with
  | rev a =>
    obtain ⟨tr, hw, hh, sz, read⟩ := rel
    refine ⟨hw, hh, sz, fun j hj => ⟨p.cells[j].ival, ?_, ?_⟩⟩
    · simpa [Spatial.source, Array.getElem?_eq_getElem hj] using read j (sz ▸ hj)
    · simp [NativeSample.CenteredAgrees, tr]
  | irrev a =>
    obtain ⟨tr, es, rfl, rect, bits, all⟩ := rel
    let r := Assemble.reduceRect tc.rect red
    let n := tc.params.levels - red
    have shape : a.source.width = a.rect.width ∧ a.source.height = a.rect.height := by
      cases a with
      | compact r f p hw hh => exact ⟨hw, hh⟩
      | wide => exact ⟨rfl, rfl⟩
    refine ⟨shape.1.trans (congrArg Rect.width rect), shape.2.trans (congrArg Rect.height rect),
      by simp [Decode.idwt], fun j hj => ?_⟩
    have inside : j < rectArea r := by simpa [Decode.idwt, r, rectArea] using hj
    refine ⟨_, IrreversibleDispatch.source_fixed a j (rect ▸ inside), ?_⟩
    have rt : (tc.params.transform == .reversible53) = false := by rw [tr]; rfl
    simpa only [rt, NativeSample.CenteredAgrees, Bool.false_eq_true, ↓reduceIte, Decode.idwt,
      Spec.DWT97.memo_eq, Array.getElem_ofFn, Decode.SpecCell.ofIrrev, bits,
      IrreversibleDispatch.target, Equiv.posU, Equiv.posV] using all j inside

/-- The real tile packet stores and their well-formed precincts, or the empty
stores used at an omitted tile. -/
inductive Packets (L : Limits) (h : Header) (data : ByteArray) (t : Nat) :
    Option TileCodeBlocks → Option Spec.Tier2.TileOut → Prop where
  /-- No tile-part at this grid index. -/
  | absent : Packets L h data t none none
  /-- Both stores were decoded with the same tile header stream and pass count. -/
  | present {tp : TileParams} {hs : Option JPEG2000.Tier2.Headers.HeaderStream} {n : Nat}
      {a : TileCodeBlocks} {b : Spec.Tier2.TileOut} (atTile : tp.index = t)
      (fast : JPEG2000.Tier2.Headers.decodeWithStream L h data tp hs n = .ok a)
      (spec : Spec.Tier2.decodeWithStream L h data tp hs n = .ok b) :
      Packets L h data t (some a) (some b)

/-- The component correspondence on the actual tile-part (or its omitted-tile defaults).
All quantisation, geometry and block-range premises follow from parsing. -/
theorem parsed_component {L : Limits} {h : Header} {data : ByteArray} {t : Nat}
    {g : Progression.Layout} {coding : Coding} {a : Option TileCodeBlocks} {b : Option Spec.Tier2.TileOut}
    (parsed : Header.parse L data = .ok h) (layout : Progression.Layout.ofHeader h t = .ok (g,coding))
    (stores : Packets L h data t a b) (c : Fin g.numComps) (red : Nat) :
    let tc := g.comp c
    let F := Assemble.fracBitsOf h.siz (coding.mctApplies h.siz) c
    Res (fun s v => ComponentRel tc F red s v.1) (component L h data g coding a c red)
      (Decode.tileComp L tc (h.siz.components.getD c default).depth.toNat F red
        ((b.map (·.comps.getD c [])).getD [])) := by
  cases stores with
  | absent =>
    apply component_equiv parsed layout none c red
    · intro i hi
      simp at hi
    · intro i p hp
      simp [Array.getD_eq_getD_getElem?] at hp
  | @present tp hs n a b atTile fast spec =>
    subst t
    have wf := Tier2WF.tier2WF _ _ _ _ _ _ _ fast
    have sim := Tier2Equiv.tier2_equiv_of_siz L h data tp hs n (Equiv.parse_dxdy parsed)
    rw [fast, spec] at sim
    simpa only [Option.map_some, Option.getD_some, sim.1, Equiv.image_getD] using
      component_equiv parsed layout (some a) c red (wf.1 _ _ layout c) (wf.2 c)

private def Geometry (tc : TileCompGeom) (red : Nat) (p : Decode.CellPlane) : Prop :=
  let r := Assemble.reduceRect tc.rect red
  red ≤ tc.params.levels ∧ p.width = r.width ∧ p.height = r.height

private theorem tileComp_geometry {L : Limits} {tc : TileCompGeom} {depth F red : Nat}
    {rs : Decode.SpecPrecs} {v : Decode.CellPlane × Nat} (ok : Decode.tileComp L tc depth F red rs = .ok v) :
    Geometry tc red v.1 := by
  rw [WideAssembly.tileComp_eq_finish] at ok
  obtain ⟨es, entries, fin⟩ := Tier2Equiv.bind_ok ok
  cases fin
  refine ⟨(entries_admit entries).1, ?_⟩
  unfold Decode.idwt
  split <;> exact ⟨rfl,rfl⟩

private theorem parsed_row {L : Limits} {h : Header} {data : ByteArray} {t : Nat}
    {g : Progression.Layout} {coding : Coding} {a : Option TileCodeBlocks} {b : Option Spec.Tier2.TileOut}
    (parsed : Header.parse L data = .ok h) (layout : Progression.Layout.ofHeader h t = .ok (g,coding))
    (stores : Packets L h data t a b) (c : Fin g.numComps) (red : Nat) :
    let tc := g.comp c
    let F := Assemble.fracBitsOf h.siz (coding.mctApplies h.siz) c
    Res (fun s v => ComponentRel tc F red s v.1 ∧ Geometry tc red v.1) (component L h data g coding a c red)
      (Decode.tileComp L tc (h.siz.components.getD c default).depth.toNat F red
        ((b.map (·.comps.getD c [])).getD [])) := by
  have sim := parsed_component parsed layout stores c red
  dsimp only at sim ⊢
  cases fast : component L h data g coding a c red <;> cases spec : Decode.tileComp .. <;>
    rw [fast,spec] at sim
  · trivial
  · contradiction
  · contradiction
  · exact ⟨sim,tileComp_geometry spec⟩

private def specComponent (L : Limits) (h : Header) (g : Progression.Layout)
    (coding : Coding) (b : Option Spec.Tier2.TileOut) (red c : Nat) :=
  Decode.tileComp L (g.comp c) (h.siz.components.getD c default).depth.toNat
    (Assemble.fracBitsOf h.siz (coding.mctApplies h.siz) c) red ((b.map (·.comps.getD c [])).getD [])

private def specStep (f : Nat → Except Error (Decode.CellPlane × Nat)) (i : Nat)
    (s : Array Decode.CellPlane × Nat) : Except Error (ForInStep (Array Decode.CellPlane × Nat)) := do
  let (p, n) ← f i
  return .yield (s.1.push p, s.2 + n)

/-- Component order, dimensions and numerical correspondence before the colour step. -/
def ComponentsRel (h : Header) (g : Progression.Layout) (coding : Coding) (red : Nat)
    (xs : Array Spatial) (ys : Array Decode.CellPlane) : Prop :=
  xs.size = g.numComps ∧ ys.size = xs.size ∧ ∀ i (hi : i < xs.size),
    ComponentRel (g.comp i) (Assemble.fracBitsOf h.siz (coding.mctApplies h.siz) i) red xs[i]
      (ys.getD i Decode.CellPlane.empty) ∧ Geometry (g.comp i) red (ys.getD i Decode.CellPlane.empty)

/-- The actual packed-or-wide component loop and the independent tile decoder's first loop
stop together on rejection. This covers every mixture of transforms and any reduction. -/
theorem components_equiv {L : Limits} {h : Header} {data : ByteArray} {t : Nat}
    {g : Progression.Layout} {coding : Coding} {a : Option TileCodeBlocks} {b : Option Spec.Tier2.TileOut}
    (parsed : Header.parse L data = .ok h) (layout : Progression.Layout.ofHeader h t = .ok (g,coding))
    (stores : Packets L h data t a b) (red : Nat) :
    Res (fun xs s => ComponentsRel h g coding red xs s.1)
      (g.comps.mapFinIdxM (fun i _ hi => component L h data g coding a ⟨i,hi⟩ red))
      (forIn [0:g.numComps] (#[], 0) (specStep (specComponent L h g coding b red))) := by
  let f := fun i (_ : TileCompGeom) (hi : i < g.comps.size) =>
    component L h data g coding a ⟨i,hi⟩ red
  let st := specStep (specComponent L h g coding b red)
  let inv (j : Nat) (xs : Array Spatial) (ys : Array Decode.CellPlane) :=
    xs.size = j ∧ ys.size = xs.size ∧ ∀ i (hi : i < xs.size),
      ComponentRel (g.comp i) (Assemble.fracBitsOf h.siz (coding.mctApplies h.siz) i) red xs[i]
        (ys.getD i Decode.CellPlane.empty) ∧ Geometry (g.comp i) red (ys.getD i Decode.CellPlane.empty)
  have loop (k j : Nat) (len : k+j = g.comps.size) (xs : Array Spatial) (ys : Array Decode.CellPlane)
      (n : Nat) (acc : inv j xs ys) :
      Res (fun xs s => ComponentsRel h g coding red xs s.1)
        (Array.mapFinIdxM.map g.comps f k j len xs) (forIn (List.range' j k) (ys,n) st) := by
    induction k generalizing j xs ys n with
    | zero => exact ⟨acc.1.trans (by simpa [Progression.Layout.numComps] using len), acc.2⟩
    | succ k ih =>
      simp only [Array.mapFinIdxM.map, List.range'_succ, List.forIn_cons]
      change Res _ (_ >>= _) ((specComponent L h g coding b red j >>= _) >>= _)
      rw [bind_assoc]
      apply Res.bind (parsed_row parsed layout stores ⟨j, by change j < g.comps.size; omega⟩ red)
      intro x z rel
      apply ih
      refine ⟨by simp [acc.1], by simp [acc.2.1], fun i hi => ?_⟩
      by_cases lt : i < xs.size
      · simpa [Array.getElem_push_lt lt, Array.getD_eq_getD_getElem?, Array.getElem?_push,
          show i ≠ ys.size by omega] using acc.2.2 i lt
      · have eq : i = j := by simp only [Array.size_push] at hi; omega
        subst i
        simp only [← acc.1, Array.getD_eq_getD_getElem?, Array.getElem?_push,
          ← acc.2.1, ↓reduceIte, Option.getD_some]
        simpa only [acc.2.1, ← acc.1, Array.getElem_push_eq] using rel
  simpa only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_one_sub_one, Nat.div_one, Progression.Layout.numComps, Array.mapFinIdxM, f, st, Array.emptyWithCapacity] using
    loop g.comps.size 0 rfl #[] #[] 0 ⟨rfl,rfl,by simp⟩

/-- Placement facts for one post-colour component, including the scale in the C9 trace. -/
def OutputRel (h : Header) (g : Progression.Layout) (coding : Coding) (red i : Nat)
    (s : NativeOutput.Source) (p : Decode.CellPlane) : Prop :=
  let rev := (g.comp i).params.transform == .reversible53
  let F := Assemble.fracBitsOf h.siz (coding.mctApplies h.siz) i
  PlaneRel F rev s p ∧
    (red ≤ (g.comp i).params.levels ∧ p.width = (Assemble.reduceRect (g.comp i).rect red).width ∧
      p.height = (Assemble.reduceRect (g.comp i).rect red).height) ∧
    ∀ j (hj : j < p.cells.size), rev = true ∨ Assemble.fracBitsOf h.siz p.cells[j].mct i = F

/-- Effective scale, geometry and centred cells of every source passed to G.1. -/
def SourcesRel (h : Header) (g : Progression.Layout) (coding : Coding) (red : Nat)
    (xs : Array NativeOutput.Source) (ps : Array Decode.CellPlane) : Prop :=
  xs.size = g.numComps ∧ ps.size = xs.size ∧ ∀ i (hi : i < xs.size),
    OutputRel h g coding red i xs[i] (ps.getD i Decode.CellPlane.empty)

private theorem single {h : Header} {g : Progression.Layout} {coding : Coding} {red i : Nat}
    {s : Spatial} {p : Decode.CellPlane}
    (row : ComponentRel (g.comp i) (Assemble.fracBitsOf h.siz (coding.mctApplies h.siz) i) red s p ∧
      Geometry (g.comp i) red p) (pass : coding.mctApplies h.siz = false ∨ 3 ≤ i) :
    OutputRel h g coding red i s.source p := by
  refine ⟨row.1.centered,row.2,fun j hj => ?_⟩
  cases s with
  | rev => exact Or.inl (by simp [row.1.1])
  | irrev =>
    obtain ⟨_,es,rfl,_⟩ := row.1
    apply Or.inr
    simp only [Decode.idwt, Bool.false_eq_true, ↓reduceIte, Array.getElem_ofFn, Decode.SpecCell.ofIrrev]
    rcases pass with eq | le
    · rw [eq]
    · simp [Assemble.fracBitsOf, Nat.not_lt.mpr le]

private theorem passThrough {h : Header} {g : Progression.Layout} {coding : Coding} {red : Nat}
    {ps : Array Spatial} {ys : Array Decode.CellPlane} (hs : ComponentsRel h g coding red ps ys)
    (hm : coding.mctApplies h.siz = false) :
    SourcesRel h g coding red (ps.map Spatial.source) ys := by
  refine ⟨by simpa using hs.1, by simpa using hs.2.1, fun i hi => ?_⟩
  simpa only [Array.getElem_map] using single (hs.2.2 i (by simpa using hi)) (.inl hm)

/-- Post-colour centred samples and effective precision for each spec output rectangle.
Native G.1 consumes the very same cell that the independent spec converts to a sample. -/
structure TileRel (h : Header) (t red : Nat) (out : JPEG2000.Decode.CenteredTile)
    (tile : Decode.TileOut) : Prop where
  /-- Effective header used by the tile and the public writer. -/
  layout : Progression.Layout.ofHeader h t = .ok (out.layout,out.coding)
  /-- Grid index of the spec tile. -/
  index : tile.tile = t
  /-- Successful checked reconstruction has retained its full working precision. -/
  saturated : out.saturated = 0
  /-- Individual post-colour cells and their independent G.1 continuation. -/
  cells : ∃ ps, SourcesRel h out.layout out.coding red out.sources ps ∧
    tile.comps.size = out.layout.numComps ∧ ∀ i (hi : i < tile.comps.size),
      let tc := out.layout.comp i
      let fmt := h.siz.components.getD i default
      tile.comps[i] = (Assemble.reduceRect tc.rect red,
        Decode.dcSpec (fmt.signed, fmt.depth.toNat) (tc.params.transform == .reversible53)
          (ps.getD i Decode.CellPlane.empty))

private theorem dc_loop {n : Nat} (ps : Array Decode.CellPlane)
    (make : Nat → Decode.CellPlane → Rect × Decode.SamplePlane) :
    let step := fun i (s : Array Decode.CellPlane × Array (Rect × Decode.SamplePlane)) =>
      (pure (.yield (s.1.setIfInBounds i Decode.CellPlane.empty,
        s.2.push (make i (s.1.getD i Decode.CellPlane.empty)))) :
          Except Error (ForInStep (Array Decode.CellPlane × Array (Rect × Decode.SamplePlane))))
    ∃ v, forIn [0:n] (ps,#[]) step = .ok v ∧ v.2.size = n ∧
      ∀ i (hi : i < v.2.size), v.2[i] = make i (ps.getD i Decode.CellPlane.empty) := by
  intro step
  let P (j : Nat) (s : Array Decode.CellPlane × Array (Rect × Decode.SamplePlane)) :=
    s.2.size = j ∧ (∀ i, j ≤ i → s.1.getD i Decode.CellPlane.empty = ps.getD i Decode.CellPlane.empty) ∧
    ∀ i (hi : i < s.2.size), s.2[i] = make i (ps.getD i Decode.CellPlane.empty)
  have go (k j : Nat) (s : Array Decode.CellPlane × Array (Rect × Decode.SamplePlane))
      (inv : P j s) : ∃ v, forIn (List.range' j k) s step = .ok v ∧ P (j+k) v := by
    induction k generalizing j s with
    | zero => exact ⟨s,rfl,inv⟩
    | succ k ih =>
      let next := (s.1.setIfInBounds j Decode.CellPlane.empty, s.2.push (make j (s.1.getD j Decode.CellPlane.empty)))
      have pn : P (j+1) next := by
        refine ⟨by simp [next, inv.1], fun i hi => ?_, fun i hi => ?_⟩
        · simpa only [next, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_ne (by omega : j ≠ i)]
            using inv.2.1 i (by omega)
        · by_cases lt : i < s.2.size
          · simpa only [next, Array.getElem_push_lt lt] using inv.2.2 i lt
          · have he : i = s.2.size := by simp only [next, Array.size_push] at hi; omega
            subst i
            simp only [next, inv.1, inv.2.1 j (Nat.le_refl _)]
            exact inv.1 ▸ Array.getElem_push_eq
      obtain ⟨v,hv,prop⟩ := ih (j+1) next pn
      rw [List.range'_succ, List.forIn_cons]
      exact ⟨v,hv,by rwa [show j+(k+1) = j+1+k by omega]⟩
  obtain ⟨v,hv,shape,_,vals⟩ := go n 0 (ps,#[]) ⟨rfl,fun _ _ => rfl,by simp⟩
  exact ⟨v,by simpa [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size] using hv,
    by simpa using shape,vals⟩

private def specColour (h : Header) (g : Progression.Layout) (coding : Coding) (ps : Array Decode.CellPlane) :=
  if coding.mctApplies h.siz then Decode.mctSpec ((g.comp 0).params.transform == .reversible53) ps
  else pure ps

private def update {α : Type} (ps : Array α) (q : α × α × α) :=
  ((ps.setIfInBounds 0 q.1).setIfInBounds 1 q.2.1).setIfInBounds 2 q.2.2

private theorem updated {h : Header} {g : Progression.Layout} {coding : Coding} {red : Nat}
    {ps : Array Spatial} {ys : Array Decode.CellPlane} (prev : ComponentsRel h g coding red ps ys)
    (three : 3 ≤ ps.size) (q : NativeOutput.Source × NativeOutput.Source × NativeOutput.Source)
    (v : Decode.CellPlane × Decode.CellPlane × Decode.CellPlane)
    (r0 : OutputRel h g coding red 0 q.1 v.1)
    (r1 : OutputRel h g coding red 1 q.2.1 v.2.1)
    (r2 : OutputRel h g coding red 2 q.2.2 v.2.2) :
    SourcesRel h g coding red (update (ps.map Spatial.source) q) (update ys v) := by
  refine ⟨by simpa [update] using prev.1, by simpa [update] using prev.2.1, fun i hi => ?_⟩
  have hys := prev.2.1
  have bound : i < ps.size := by simpa [update] using hi
  match i with
  | 0 | 1 | 2 =>
    simp (disch := simp only [Array.size_setIfInBounds, Array.size_map] <;> omega) [update, Array.getElem_setIfInBounds,
      Array.getD_eq_getD_getElem?,r0,r1,r2]
  | i+3 =>
    have iy : i+3 < ys.size := hys ▸ bound
    simpa (disch := simp only [Array.size_setIfInBounds, Array.size_map] <;> omega) [update, Array.getElem_setIfInBounds, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds,
      Array.getElem_setIfInBounds_ne (a := v.1) iy (by omega : 0 ≠ i+3), Array.getElem?_eq_getElem iy, iy, show 0 ≠ i+3 by omega, show 1 ≠ i+3 by omega, show 2 ≠ i+3 by omega]
      using single (prev.2.2 (i+3) bound) (.inr (by omega))

private theorem layout_count {h : Header} {t : Nat} {g : Progression.Layout} {coding : Coding}
    (layout : Progression.Layout.ofHeader h t = .ok (g,coding)) : g.numComps = h.siz.csiz := by
  unfold Progression.Layout.ofHeader at layout
  dsimp only at layout
  split at layout <;> try contradiction
  obtain ⟨xs,mapped,layout⟩ := Tier2Equiv.bind_ok layout
  cases layout
  change xs.size = h.siz.csiz
  rw [Array.mapM_eq_mapM_toList] at mapped
  have len {α β : Type} (f : α → Except Error β) (l : List α) (b : List β) :
      l.mapM f = .ok b → b.length = l.length := by
    induction l generalizing b with
    | nil => intro eq; cases eq; rfl
    | cons a l ih =>
      rw [List.mapM_cons]
      intro eq
      obtain ⟨_,_,eq⟩ := Tier2Equiv.bind_ok eq
      obtain ⟨bs,hb,eq⟩ := Tier2Equiv.bind_ok eq
      cases eq
      simp [ih bs hb]
  cases hl : List.mapM (fun c => JPEG2000.Tier2.Geometry.ofHeader h t c) (Array.range h.siz.csiz).toList with
  | error => rw [hl] at mapped; contradiction
  | ok bs =>
    rw [hl] at mapped
    cases mapped
    simpa using len _ _ _ hl

private theorem firstThreeWork (g : Progression.Layout) (red : Nat) (three : 3 ≤ g.numComps) :
    let area := fun c => rectArea (Assemble.reduceRect (g.comp c).rect red)
    area 0 + area 1 + area 2 ≤ g.comps.foldl (fun n tc => n + rectArea (Assemble.reduceRect tc.rect red)) 0 := by
  obtain ⟨tile,layers,⟨cs⟩⟩ := g
  let f := fun (tc : TileCompGeom) => rectArea (Assemble.reduceRect tc.rect red)
  change 3 ≤ cs.length at three
  match cs with
  | [] | [_] | [_,_] => simp at three
  | a :: b :: c :: cs =>
    change f _ + f _ + f _ ≤ _
    have grow (l : List TileCompGeom) (n : Nat) : n ≤ l.foldl (fun v tc => v + f tc) n := by
      induction l generalizing n with
      | nil => exact Nat.le_refl _
      | cons tc l ih => exact Nat.le_trans (Nat.le_add_right n _) (ih _)
    simpa [Progression.Layout.comp, Array.getD_eq_getD_getElem?, f] using grow cs (f a + f b + f c)

private abbrev grid (g : Progression.Layout) (red i : Nat) := Assemble.reduceRect (g.comp i).rect red

private abbrev plane (ys : Array Decode.CellPlane) (i : Nat) := ys.getD i Decode.CellPlane.empty

private theorem rct_step {L : Limits} {h : Header} {g : Progression.Layout} {coding : Coding} {red : Nat}
    {ps : Array Spatial} {ys : Array Decode.CellPlane} (hs : ComponentsRel h g coding red ps ys)
    (three : 3 ≤ ps.size) (hm : coding.mctApplies h.siz = true)
    (budget : rectArea (grid g red 0) + rectArea (grid g red 1) + rectArea (grid g red 2) ≤ L.maxWorkSamples)
    {y cb cr : NativeOutput.Source} (sy : ps[0]? = some (.rev y)) (sb : ps[1]? = some (.rev cb))
    (sr : ps[2]? = some (.rev cr)) :
    Res (SourcesRel h g coding red) (sources L (coding.mctApplies h.siz) ps) (specColour h g coding ys) := by
  have row {i : Nat} {v : NativeOutput.Source} (read : ps[i]? = some (.rev v)) :
      ((g.comp i).params.transform = .reversible53 ∧ ReversibleDispatch.Exact v (plane ys i)) ∧
      Geometry (g.comp i) red (plane ys i) := by
    obtain ⟨hi,eq⟩ := Array.getElem?_eq_some_iff.mp read
    have rel := hs.2.2 i hi
    rw [eq] at rel
    exact rel
  obtain ⟨⟨ty,ey⟩,gy⟩ := row sy
  obtain ⟨⟨tb,eb⟩,gb⟩ := row sb
  obtain ⟨⟨tr,er⟩,gr⟩ := row sr
  have work : y.width*y.height + cb.width*cb.height + cr.width*cr.height ≤ L.maxWorkSamples := by
    simpa only [grid,rectArea,ey.1,ey.2.1,eb.1,eb.2.1,er.1,er.2.1,gy.2.1,gy.2.2,gb.2.1,gb.2.2,gr.2.1,gr.2.2]
      using (show rectArea (grid g red 0) + rectArea (grid g red 1) + rectArea (grid g red 2) ≤ _ from budget)
  simp only [sources, hm, Bool.not_true, Bool.false_eq_true, ↓reduceIte, sy, sb, sr, specColour,ty,BEq.rfl]
  have exactColour := ReversibleDispatch.colour_spec L y cb cr
  cases ok : JPEG2000.ReversibleDispatch.colour L y cb cr with
  | error e =>
    rw [ok] at exactColour
    have bad : ¬ ((plane ys 1).width = (plane ys 0).width ∧ (plane ys 1).height = (plane ys 0).height ∧
        (plane ys 2).width = (plane ys 0).width ∧ (plane ys 2).height = (plane ys 0).height) :=
      fun shape => exactColour ⟨work,by simpa only [ey.1,ey.2.1,eb.1,eb.2.1,er.1,er.2.1] using shape⟩
    unfold Decode.mctSpec
    dsimp only [plane] at bad
    rw [ite_eq_right bad]
    trivial
  | ok q =>
    rw [ok] at exactColour
    obtain ⟨v0,v1,v2,spec,h0,h1,h2⟩ := ReversibleDispatch.colour_mctSpec ys ey eb er ok
    rw [spec]
    apply updated hs three q (v0,v1,v2)
    · exact ⟨ComponentRel.centered (red := red) (s := .rev _) ⟨ty,h0⟩,
        ⟨gy.1,h0.1.symm.trans (exactColour.2.2.1.trans (ey.1.trans gy.2.1)),
          h0.2.1.symm.trans (exactColour.2.2.2.1.trans (ey.2.1.trans gy.2.2))⟩,fun _ _ => Or.inl (by simp [ty])⟩
    · exact ⟨ComponentRel.centered (red := red) (s := .rev _) ⟨tb,h1⟩,
        ⟨gb.1,h1.1.symm.trans (exactColour.2.2.2.2.1.trans (eb.1.trans gb.2.1)),
          h1.2.1.symm.trans (exactColour.2.2.2.2.2.1.trans (eb.2.1.trans gb.2.2))⟩,fun _ _ => Or.inl (by simp [tb])⟩
    · exact ⟨ComponentRel.centered (red := red) (s := .rev _) ⟨tr,h2⟩,
        ⟨gr.1,h2.1.symm.trans (exactColour.2.2.2.2.2.2.1.trans (er.1.trans gr.2.1)),
          h2.2.1.symm.trans (exactColour.2.2.2.2.2.2.2.1.trans (er.2.1.trans gr.2.2))⟩,fun _ _ => Or.inl (by simp [tr])⟩

private abbrev Ref := IrreversibleDispatch.Reference

private def painted (ref : Nat → Ref) (i : Nat) : Decode.CellPlane :=
  let r := (ref i).rect
  ⟨r.width,r.height,Array.ofFn (n := rectArea r) fun j => IrreversibleDispatch.postCell true ref i j⟩

private theorem spec_ict {ys : Array Decode.CellPlane} (ref : Nat → Ref)
    (shape : JPEG2000.WideReversible.SameShape (ref 0).rect (ref 1).rect (ref 2).rect)
    (pre : ∀ i, i < 3 → (plane ys i).width = (ref i).rect.width ∧
      (plane ys i).height = (ref i).rect.height ∧
      ∀ j, j < rectArea (ref i).rect → (plane ys i).cells.getD j default = (ref i).cell j) :
    Decode.mctSpec false ys = .ok (update ys (painted ref 0,painted ref 1,painted ref 2)) := by
  obtain ⟨w0,h0,c0⟩ := pre 0 (by decide)
  obtain ⟨w1,h1,c1⟩ := pre 1 (by decide)
  obtain ⟨w2,h2,c2⟩ := pre 2 (by decide)
  obtain ⟨bw,bh,rw_,rh⟩ := shape
  have sh : (plane ys 1).width = (plane ys 0).width ∧ (plane ys 1).height = (plane ys 0).height ∧
      (plane ys 2).width = (plane ys 0).width ∧ (plane ys 2).height = (plane ys 0).height := by
    rw [w0,w1,w2,h0,h1,h2,bw,bh,rw_,rh]
    exact ⟨rfl,rfl,rfl,rfl⟩
  unfold Decode.mctSpec
  rw [ite_eq_left sh]
  dsimp only [plane] at w0 w1 w2 h0 h1 h2 c0 c1 c2
  simp only [pure, Except.pure, Except.ok.injEq, Bool.false_eq_true, ↓reduceIte, update, painted]
  congr 1
  · congr 1
    · congr 1
      apply Decode.CellPlane.mk.injEq .. |>.mpr
      refine ⟨w0,h0,Array.ext (by simp only [Array.size_map, Array.size_ofFn,w0,h0,rectArea]) ?_⟩
      intro i hi _
      simp only [Array.size_map, Array.size_ofFn] at hi
      have inside : i < rectArea (ref 0).rect := by simpa only [← w0,← h0,rectArea] using hi
      simp only [Array.getElem_map, Array.getElem_ofFn, c0 i inside, c1 i (by simpa [rectArea,bw,bh] using inside),
        c2 i (by simpa [rectArea,rw_,rh] using inside)]
      rfl
    · apply Decode.CellPlane.mk.injEq .. |>.mpr
      refine ⟨w1,h1,Array.ext (by simp only [Array.size_map, Array.size_ofFn,w0,h0,rectArea,bw,bh]) ?_⟩
      intro i hi _
      simp only [Array.size_map, Array.size_ofFn] at hi
      have inside : i < rectArea (ref 0).rect := by simpa only [← w0,← h0,rectArea] using hi
      simp only [Array.getElem_map, Array.getElem_ofFn, c0 i inside, c1 i (by simpa [rectArea,bw,bh] using inside),
        c2 i (by simpa [rectArea,rw_,rh] using inside)]
      rfl
  · apply Decode.CellPlane.mk.injEq .. |>.mpr
    refine ⟨w2,h2,Array.ext (by simp only [Array.size_map, Array.size_ofFn,w0,h0,rectArea,rw_,rh]) ?_⟩
    intro i hi _
    simp only [Array.size_map, Array.size_ofFn] at hi
    have inside : i < rectArea (ref 0).rect := by simpa only [← w0,← h0,rectArea] using hi
    simp only [Array.getElem_map, Array.getElem_ofFn, c0 i inside, c1 i (by simpa [rectArea,bw,bh] using inside),
      c2 i (by simpa [rectArea,rw_,rh] using inside)]
    rfl

private theorem ict_step {L : Limits} {h : Header} {g : Progression.Layout} {coding : Coding} {red : Nat}
    {ps : Array Spatial} {ys : Array Decode.CellPlane} (hs : ComponentsRel h g coding red ps ys)
    (three : 3 ≤ ps.size) (hm : coding.mctApplies h.siz = true)
    (budget : rectArea (grid g red 0) + rectArea (grid g red 1) + rectArea (grid g red 2) ≤ L.maxWorkSamples)
    (ordered : ∀ i, i < 3 → JPEG2000.WideICT.Ordered (grid g red i))
    {y cb cr : JPEG2000.IrreversibleDispatch.Spatial}
    (sy : ps[0]? = some (.irrev y)) (sb : ps[1]? = some (.irrev cb)) (sr : ps[2]? = some (.irrev cr)) :
    Res (SourcesRel h g coding red) (sources L (coding.mctApplies h.siz) ps) (specColour h g coding ys) := by
  let F i := Assemble.fracBitsOf h.siz (coding.mctApplies h.siz) i
  let nl (i : Nat) := (g.comp i).params.levels-red
  let input (i : Nat) := if i = 0 then y else if i = 1 then cb else cr
  have row (i : Nat) (hi : i < 3) :
      (g.comp i).params.transform = .irreversible97 ∧ Geometry (g.comp i) red (plane ys i) ∧
      ∃ es, plane ys i = Decode.idwt false es (grid g red i) (nl i) ∧
        IrreversibleDispatch.SpatialAgrees (input i) (grid g red i) (F i) (nl i) (Decode.dec97 es (nl i)) := by
    have hit : ps[i]? = some (.irrev (input i)) := by
      match i with
      | 0 => exact sy
      | 1 => exact sb
      | 2 => exact sr
      | i+3 => omega
    obtain ⟨bound,eq⟩ := Array.getElem?_eq_some_iff.mp hit
    obtain ⟨rel,geo⟩ := hs.2.2 i bound
    rw [eq] at rel
    exact ⟨rel.1,geo,rel.2⟩
  let es := fun i => if hi : i < 3 then Classical.choose (row i hi).2.2 else []
  let ref (i : Nat) : Ref := ⟨grid g red i, F i, nl i, Decode.dec97 (es i) (nl i)⟩
  have pre (i : Nat) (hi : i < 3) : plane ys i = Decode.idwt false (es i) (grid g red i) (nl i) ∧
      IrreversibleDispatch.SpatialAgrees (input i) (ref i).rect (ref i).bits (ref i).levels (ref i).bands := by
    simpa only [ref,es,dite_eq_left hi] using Classical.choose_spec (row i hi).2.2
  have yA := (pre 0 (by decide)).2
  have bA := (pre 1 (by decide)).2
  have rA := (pre 2 (by decide)).2
  change IrreversibleDispatch.SpatialAgrees y .. at yA
  change IrreversibleDispatch.SpatialAgrees cb .. at bA
  change IrreversibleDispatch.SpatialAgrees cr .. at rA
  have points (i : Nat) (hi : i < 3) :
      (plane ys i).width = (ref i).rect.width ∧ (plane ys i).height = (ref i).rect.height ∧
      ∀ j, j < rectArea (ref i).rect → (plane ys i).cells.getD j default = (ref i).cell j := by
    rw [(pre i hi).1]
    refine ⟨rfl,rfl,fun j hj => ?_⟩
    change j < (grid g red i).width * (grid g red i).height at hj
    simp only [Decode.idwt, Bool.false_eq_true, ↓reduceIte, Spec.DWT97.memo_eq,
      Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hj, ↓reduceDIte, Option.getD_some]
    rfl
  have toOut (i : Nat) (hi : i < 3) (s : NativeOutput.Source)
      (agree : IrreversibleDispatch.SourceAgrees s (ref i) (IrreversibleDispatch.postCell true ref i)) :
      OutputRel h g coding red i s (painted ref i) := by
    have rt : ((g.comp i).params.transform == .reversible53) = false := by rw [(row i hi).1]; rfl
    refine ⟨⟨agree.1, agree.2.1, by simp [painted, rectArea], fun j hj => ?_⟩,
      ⟨(row i hi).2.1.1,rfl,rfl⟩,fun j hj => Or.inr ?_⟩
    · simpa only [painted,Array.getElem_ofFn,rt] using agree.2.2 j (by simpa [painted] using hj)
    · have tag : (IrreversibleDispatch.postCell true ref i j).mct = true := by
        simp only [IrreversibleDispatch.postCell, hi, and_self, ↓reduceIte, Decode.ictCells]
        split <;> first | rfl | split <;> rfl
      simp only [painted, Array.getElem_ofFn, tag, hm]
  have work : rectArea y.rect + rectArea cb.rect + rectArea cr.rect ≤ L.maxWorkSamples := by
    rw [yA.1,bA.1,rA.1]; exact budget
  have scale (i : Nat) (hi : i < 3) : F i = F 0 := by simp [F,hm,Assemble.fracBitsOf,hi]
  have bc : cb.bits = y.bits := bA.2.1.trans ((scale 1 (by decide)).trans yA.2.1.symm)
  have rc : cr.bits = y.bits := rA.2.1.trans ((scale 2 (by decide)).trans yA.2.1.symm)
  simp only [sources, hm, Bool.not_true, Bool.false_eq_true, ↓reduceIte, sy, sb, sr, specColour,
    (row 0 (by decide)).1]
  by_cases shape : JPEG2000.WideReversible.SameShape y.rect cb.rect cr.rect
  · have hshape : JPEG2000.WideReversible.SameShape (ref 0).rect (ref 1).rect (ref 2).rect := by
      rwa [← yA.1,← bA.1,← rA.1]
    have compat : JPEG2000.WideICT.Compatible y.toWide cb.toWide cr.toWide := by
      have metadata (p : JPEG2000.IrreversibleDispatch.Spatial) : p.toWide.rect = p.rect ∧
          p.toWide.fracBits = p.bits := by cases p <;> exact ⟨rfl,rfl⟩
      simp only [JPEG2000.WideICT.Compatible,(metadata y).1,(metadata cb).1,(metadata cr).1,(metadata y).2,
        (metadata cb).2,(metadata cr).2]
      exact ⟨shape,yA.1 ▸ ordered 0 (by decide),bA.1 ▸ ordered 1 (by decide),
        rA.1 ▸ ordered 2 (by decide),bc,rc⟩
    have ok : ∃ result, JPEG2000.IrreversibleDispatch.ict L y cb cr = .ok result := by
      unfold JPEG2000.IrreversibleDispatch.ict
      rw [(Limits.check_eq_ok_iff ..).2 work, Equiv.ok_bind, ite_eq_left ⟨shape,
        yA.1 ▸ ordered 0 (by decide), bA.1 ▸ ordered 1 (by decide), rA.1 ▸ ordered 2 (by decide),bc,rc⟩]
      split
      · exact ⟨_,rfl⟩
      · have wideWork : rectArea y.toWide.rect + rectArea cb.toWide.rect + rectArea cr.toWide.rect ≤
            L.maxWorkSamples := by cases y <;> cases cb <;> cases cr <;> exact work
        rw [(WideICT.ictInverse_ok ..).2 ⟨wideWork,compat,rfl⟩,Equiv.ok_bind]
        exact ⟨_,rfl⟩
    obtain ⟨out,ok⟩ := ok
    obtain ⟨r,b,c⟩ := IrreversibleDispatch.ict_sources (ref := ref) ok yA bA rA
    have spec := spec_ict ref hshape points
    change Res _ _ (Decode.mctSpec false ys)
    rw [spec]
    simp only [ok,Equiv.ok_bind,pure_bind]
    exact updated hs three (out.1.source,out.2.1.source,out.2.2.source)
      (painted ref 0,painted ref 1,painted ref 2) (toOut 0 (by decide) _ r) (toOut 1 (by decide) _ b)
      (toOut 2 (by decide) _ c)
  · have bad : ¬ ((plane ys 1).width = (plane ys 0).width ∧ (plane ys 1).height = (plane ys 0).height ∧
        (plane ys 2).width = (plane ys 0).width ∧ (plane ys 2).height = (plane ys 0).height) := by
      intro eq
      apply shape
      rw [yA.1,bA.1,rA.1]
      simpa only [JPEG2000.WideReversible.SameShape,(points 0 (by decide)).1,(points 0 (by decide)).2.1,
        (points 1 (by decide)).1,(points 1 (by decide)).2.1,
        (points 2 (by decide)).1,(points 2 (by decide)).2.1] using eq
    change Res _ _ (Decode.mctSpec false ys)
    unfold Decode.mctSpec JPEG2000.IrreversibleDispatch.ict
    rw [ite_eq_right bad, (Limits.check_eq_ok_iff ..).2 work, Equiv.ok_bind, ite_eq_right (fun c => shape c.1)]
    trivial

private theorem tile_from_colour {L : Limits} {h : Header} {data : ByteArray} {t red : Nat}
    {a : Option TileCodeBlocks} {b : Option Spec.Tier2.TileOut}
    (parsed : Header.parse L data = .ok h) (stores : Packets L h data t a b)
    (colour : ∀ g coding, Progression.Layout.ofHeader h t = .ok (g,coding) →
      L.check Assemble.loc .workSamples (g.comps.foldl (fun n tc => n+rectArea (Assemble.reduceRect tc.rect red)) 0) = .ok () →
      ∀ xs ps, ComponentsRel h g coding red xs ps →
      Res (SourcesRel h g coding red) (sources L (coding.mctApplies h.siz) xs) (specColour h g coding ps)) :
    Res (TileRel h t red) (JPEG2000.Decode.centeredTile L h data red t a) (Decode.decodeTile L h t red b) := by
  unfold JPEG2000.Decode.centeredTile Decode.decodeTile Decode.tileWith
  cases hl : Progression.Layout.ofHeader h t with
  | error => trivial
  | ok gc =>
    obtain ⟨g,coding⟩ := gc
    simp only [Equiv.ok_bind]
    unfold tile
    rw [bind_assoc]
    cases work : L.check Assemble.loc .workSamples (g.comps.foldl
        (fun n tc => n + rectArea (Assemble.reduceRect tc.rect red)) 0) with
    | error =>
      simp only [rectArea] at work
      simp only [work, bind, Except.bind,Tier2Equiv.Res]
    | ok u =>
      cases u
      have work' := work
      simp only [rectArea] at work'
      simp only [work', Equiv.ok_bind, bind_assoc]
      have planes := components_equiv parsed hl stores red
      cases b <;> apply Res.bind planes <;> intro xs pair rel
      all_goals
        obtain ⟨ps,n⟩ := pair
        have cm := colour g coding hl work xs ps rel
        let make := fun i pl => (Assemble.reduceRect (g.comp i).rect red,
          Decode.dcSpec ((h.siz.components.getD i default).signed, (h.siz.components.getD i default).depth.toNat)
            ((g.comp i).params.transform == .reversible53) pl)
        cases hm : coding.mctApplies h.siz <;> simp only [specColour, hm, ↓reduceIte, Bool.false_eq_true] at cm ⊢
        all_goals
          apply Res.bind cm
          intro ss qs post
          obtain ⟨v,hd,sz,vals⟩ := dc_loop (n := g.numComps) qs make
          dsimp only [make] at hd
          simp only [pure_bind, hd, Equiv.ok_bind]
          exact ⟨hl,rfl,rfl,qs,post,sz,vals⟩

/-- Two-sided correspondence of the public tile reconstruction on the stores decoded by
Tier-2, including an omitted tile. On success every centred source meets the exact 5/3
or C8 sample bound for the independent spec tile at its actual geometry and scale. -/
theorem parsed_tile {L : Limits} {h : Header} {data : ByteArray} {t red : Nat}
    {a : Option TileCodeBlocks} {b : Option Spec.Tier2.TileOut}
    (parsed : Header.parse L data = .ok h) (stores : Packets L h data t a b) :
    Res (TileRel h t red) (JPEG2000.Decode.centeredTile L h data red t a) (Decode.decodeTile L h t red b) := by
  apply tile_from_colour parsed stores
  intro g coding layout work ps ys hs
  cases hm : coding.mctApplies h.siz with
  | false =>
    simpa only [sources, Bool.not_false, ↓reduceIte, specColour, hm, Bool.false_eq_true, Res,
      pure, Except.pure] using passThrough hs hm
  | true =>
    have count := layout_count layout
    have three : 3 ≤ ps.size := by
      rw [hs.1,count]
      simp only [Coding.mctApplies, Bool.and_eq_true, decide_eq_true_eq] at hm
      exact hm.2
    have budget := Nat.le_trans (firstThreeWork g red (hs.1 ▸ three)) ((Limits.check_eq_ok_iff ..).1 work)
    have peers := (HeaderWF.headerWF _ _ _ parsed _ _ _ layout).2 hm
    cases tr : (g.comp 0).params.transform with
    | reversible53 =>
      have tag (i : Nat) (hi : i < 3) : ∃ s, ps[i]? = some (.rev s) := by
        have bound : i < ps.size := by omega
        have rel := (hs.2.2 i bound).1
        have ty := (peers i hi).trans tr
        cases eq : ps[i] with
        | rev s => exact ⟨s,by rw [Array.getElem?_eq_getElem bound,eq]⟩
        | irrev s => rw [eq] at rel; exact False.elim (by have := rel.1; rw [ty] at this; contradiction)
      obtain ⟨y,sy⟩ := tag 0 (by decide)
      obtain ⟨cb,sb⟩ := tag 1 (by decide)
      obtain ⟨cr,sr⟩ := tag 2 (by decide)
      simpa only [hm] using rct_step hs three hm budget sy sb sr
    | irreversible97 =>
      have tag (i : Nat) (hi : i < 3) : ∃ s, ps[i]? = some (.irrev s) := by
        have bound : i < ps.size := by omega
        have rel := (hs.2.2 i bound).1
        have ty := (peers i hi).trans tr
        cases eq : ps[i] with
        | irrev s => exact ⟨s,by rw [Array.getElem?_eq_getElem bound,eq]⟩
        | rev s => rw [eq] at rel; exact False.elim (by have := rel.1; rw [ty] at this; contradiction)
      obtain ⟨y,sy⟩ := tag 0 (by decide)
      obtain ⟨cb,sb⟩ := tag 1 (by decide)
      obtain ⟨cr,sr⟩ := tag 2 (by decide)
      have ordered (i : Nat) (hi : i < 3) : JPEG2000.WideICT.Ordered (grid g red i) :=
        (WideHeaderBounds.parsed_component_bounds parsed layout ⟨i,hs.1 ▸ (by omega : i < ps.size)⟩ red).2
      simpa only [hm] using ict_step hs three hm budget ordered sy sb sr

end JPEG2000.Spec.TileDispatch
