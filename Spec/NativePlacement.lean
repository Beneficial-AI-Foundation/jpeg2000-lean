import Spec.NativePlacement.Allocation
import Spec.NativePlacement.Geometry
import Spec.NativePlacement.Place

/-!
# Native C9 placement and finalization (Plan.md §§4, 5, 7, T.800 B.2, B.3 and G.1)

Allocation initializes the state with blank samples. A post-MCT tile supplies
centred values in its own component raster. Placement transports that relation
through both decoders' writes and preserves all earlier cells outside the tile.
-/

namespace JPEG2000.Spec.NativePlacement

open JPEG2000.NativeOutput JPEG2000.Spec.Decode Header Bytes

/-- The centred source and its G.1 specification tile have matching extents and
a specification cell for every local read. The scale is checked against the MCT
trace of that particular sample, including components outside the MCT triple. -/
structure SourceRel (s : Marker.SIZ) (i F : Nat) (rev : Bool) (fmt : Marker.Component)
    (src : Source) (p : SamplePlane) : Prop where
  /-- Source and specification row strides coincide. -/
  width : p.width = src.width
  /-- Source and specification heights coincide. -/
  height : p.height = src.height
  /-- All rows of the specification tile are present. -/
  size : p.samples.size = p.width * p.height
  /-- The specification stores G.1 applied to the related centred cell. -/
  cell : ∀ x y (hx : x < src.width) (hy : y < src.height), ∃ c : SpecCell,
    let a := c.toSample fmt.signed fmt.depth.toNat rev
    p.samples[y * src.width + x]? = some a ∧
      NativeSample.CenteredAgrees F rev (src.read ⟨y * src.width + x, DWT53.idx_lt hx hy⟩) c ∧
      (rev = true ∨ Assemble.fracBitsOf s a.mct i = F)

/-- Construct the placement contract directly on the successful post-MCT cell
plane and its actual specification G.1 map. -/
theorem source_dcSpec (s : Marker.SIZ) (i F : Nat) (rev : Bool) (fmt : Marker.Component)
    (src : Source) (p : CellPlane) (hw : p.width = src.width) (hh : p.height = src.height)
    (size : p.cells.size = p.width * p.height)
    (centered : ∀ x y (hx : x < src.width) (hy : y < src.height),
      let j := y * src.width + x
      let c := p.cells[j]'(by rw [size, hw, hh]; exact DWT53.idx_lt hx hy)
      NativeSample.CenteredAgrees F rev (src.read ⟨j, DWT53.idx_lt hx hy⟩) c ∧
        (rev = true ∨ Assemble.fracBitsOf s c.mct i = F)) :
    SourceRel s i F rev fmt src (dcSpec (fmt.signed, fmt.depth.toNat) rev p) := by
  refine ⟨hw, hh, by simpa [dcSpec] using size, ?_⟩
  intro x y hx hy
  have hj : y * src.width + x < p.cells.size := by rw [size, hw, hh]; exact DWT53.idx_lt hx hy
  obtain ⟨cell, scale⟩ := centered x y hx hy
  refine ⟨p.cells[y * src.width + x], by simp [dcSpec, hj], cell, ?_⟩
  cases rev
  · simpa [SpecCell.toSample] using scale
  · simp

/-- Input interface to placement for one reconstructed tile. Layout containment and
both per-output budgets follow from parsing and the accumulated state. -/
structure TileRel (s : Marker.SIZ) (red : Nat) (g : Progression.Layout) (coding : Coding)
    (src : Array Source) (tile : TileOut) : Prop where
  /-- Number of native centred sources. -/
  sources : src.size = g.numComps
  /-- Number of specification tile-components. -/
  specs : tile.comps.size = g.numComps
  /-- Each component admits the reduction and has the selected rectangle, transform and scale. -/
  component : ∀ i (hi : i < g.numComps),
    let tc := g.comp i
    let r := Assemble.reduceRect tc.rect red
    let source := src[i]'(sources.symm ▸ hi)
    let spec := tile.comps[i]'(specs.symm ▸ hi)
    red ≤ tc.params.levels ∧ source.width = r.width ∧ source.height = r.height ∧ spec.1 = r ∧
      SourceRel s i (Assemble.fracBitsOf s (coding.mctApplies s) i)
        (tc.params.transform == .reversible53) (s.components.getD i default) source spec.2

private theorem component_place {s : Marker.SIZ} {i F : Nat} {rev : Bool} {d q : OutputComponent}
    {p sp : SamplePlane} {src : Source} {r : Rect}
    (prev : PlaneRel s i d p) (source : SourceRel s i F rev d.format src sp)
    (fit : fitsTile d.rect r src)
    (placed : NativeOutput.Placed d q r (if rev then 0 else F) src) :
    ∃ result, blit p sp (r.x0 - d.rect.x0) (r.y0 - d.rect.y0) = .ok result ∧ PlaneRel s i q result := by
  let ox := r.x0 - d.rect.x0
  let oy := r.y0 - d.rect.y0
  have fx : ox + sp.width ≤ p.width := by
    rw [prev.width, source.width]
    simp only [fitsTile, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at fit
    dsimp [ox]; unfold Rect.width at *; omega
  have fy : oy + sp.height ≤ p.height := by
    rw [prev.height, source.height]
    simp only [fitsTile, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at fit
    dsimp [oy]; unfold Rect.height at *; omega
  obtain ⟨result, hbl, w, h, sz, copy, frame⟩ := blit_reads p sp ox oy source.size prev.size fx fy
  have qr := placed.1
  have nativeFrame := placed.2.2.2
  refine ⟨result, hbl, ⟨w.trans (prev.width.trans (congrArg Rect.width qr.symm)),
    h.trans (prev.height.trans (congrArg Rect.height qr.symm)), by rw [sz, prev.size, w, h], ?_⟩⟩
  intro x y hx hy
  rw [qr] at hx hy ⊢
  rw [prev.width, source.width, source.height] at copy frame
  by_cases inside : WideOutput.Inside src.width src.height ox oy x y
  · unfold WideOutput.Inside at inside
    have lx : x - ox < src.width := by omega
    have ly : y - oy < src.height := by omega
    obtain ⟨c, specCell, agree, scale⟩ := source.cell (x - ox) (y - oy) lx ly
    obtain ⟨v, hv, claim⟩ := NativeSample.placed_sample F rev placed (x - ox) (y - oy) lx ly c agree
    change q.get? ((oy + (y - oy)) * d.rect.width + (ox + (x - ox))) = some v at hv
    have cx := copy (x - ox) (y - oy) lx ly
    rw [show oy + (y - oy) = y by omega, show ox + (x - ox) = x by omega] at hv cx
    refine ⟨v, _, hv, cx.trans specCell, ?_⟩
    rcases scale with rfl | scale
    · exact claim
    · rwa [scale]
  · obtain ⟨v, a, hv, ha, agree⟩ := prev.read x y hx hy
    exact ⟨v, a, (nativeFrame x y hx hy inside).trans hv, (frame x y hx inside).trans ha, agree⟩

/-- With related reconstructed inputs, both actual writers succeed and preserve the
whole state. The origin, stride, shape and budget checks hold for every component. -/
theorem placement {L : Limits} {data : ByteArray} {h : Header} {t red : Nat}
    {g : Progression.Layout} {coding : Coding} {ds : Array OutputComponent}
    {info : Array DecodedComponent} {ps : Array SamplePlane} {src : Array Source} {tile : TileOut}
    (parsed : Header.parse L data = .ok h) (layoutOk : Progression.Layout.ofHeader h t = .ok (g, coding))
    (prev : State L h.siz red ds info ps)
    (input : TileRel h.siz red g coding src tile) :
    ∃ qs ss, writeTile L h.siz red g coding ds src = .ok qs ∧
      place info ps tile = .ok ss ∧ State L h.siz red qs info ss := by
  obtain ⟨count, grid⟩ := tile_grid (red := red) parsed layoutOk
  have ng := prev.count.trans count.symm
  have ns := ng.trans input.sources.symm
  have nt := ng.trans input.specs.symm
  have fit (i : Nat) (hi : i < ds.size) :
      fitsTile ds[i].rect (Assemble.reduceRect (g.comp i).rect red) (src[i]'(ns ▸ hi)) := by
    obtain ⟨hr, _, _, _, _, _⟩ := prev.component i hi
    obtain ⟨_, hw, hh, _, _⟩ := input.component i (ng ▸ hi)
    obtain ⟨a, b, c, d, e, f⟩ := grid i (ng ▸ hi)
    simp [fitsTile, hr, hw, hh, a, b, c, d, e, f]
  obtain ⟨qs, ok⟩ := NativeOutput.writeTile_succeeds L h.siz red g coding ds src prev.reduction
    ⟨prev.count, ng, ns⟩ (by
      intro i hi
      obtain ⟨grid, fmt, _, work, bytes, _⟩ := prev.component i hi
      exact ⟨fmt, grid, (input.component i (ng ▸ hi)).1, fit i hi, work, bytes⟩)
  obtain ⟨nq, _, _, _, written⟩ := NativeOutput.writeTile_spec ok
  have ni := prev.infos.trans nt
  have np := prev.planes.trans nt
  have step (j : Fin tile.comps.size) :
      let i := j.val
      let hi : i < ds.size := nt.symm ▸ j.isLt
      let d := ds[i]
      let q := qs[i]'(nq ▸ hi)
      let dc := info[i]'(ni.symm ▸ j.isLt)
      let r := tile.comps[j.val].1
      let sp := tile.comps[j.val].2
      q.rect = d.rect ∧ q.format = d.format ∧ dc.x0 ≤ r.x0 ∧ dc.y0 ≤ r.y0 ∧
      ∃ result, blit (ps[i]'(np.symm ▸ j.isLt)) sp (r.x0 - dc.x0) (r.y0 - dc.y0) = .ok result ∧
        PlaneRel h.siz i q result := by
    let i := j.val
    have hi : i < ds.size := nt.symm ▸ j.isLt
    have hiq : i < qs.size := nq ▸ hi
    have his : i < src.size := ns ▸ hi
    have hic : i < h.siz.components.size := prev.count ▸ hi
    obtain ⟨dgrid, fmt, metadata, _, _, rel⟩ := prev.component i hi
    obtain ⟨_, _, _, rEq, source⟩ := input.component i (ng ▸ hi)
    obtain ⟨q, st, hq, hs, placed⟩ := written i hi
    simp only [Array.getElem?_eq_getElem hiq, Array.getElem?_eq_getElem his, Option.some.injEq] at hq hs
    subst q; subst st
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hic, Option.getD_some, ← fmt] at source
    obtain ⟨res, bl, good⟩ := component_place rel source (fit i hi) placed
    obtain ⟨x0, _, _, y0, _, _⟩ := grid i (ng ▸ hi)
    dsimp only
    change _ ∧ _ ∧ info[i].x0 ≤ _ ∧ info[i].y0 ≤ _ ∧ _
    rw [metadata, rEq]
    exact ⟨placed.1, placed.2.1, dgrid.symm ▸ x0, dgrid.symm ▸ y0, res, bl, good⟩
  let result := fun j => (step j).2.2.2.2.choose
  have spec := place_components info ps tile ni np result fun j =>
    ⟨(step j).2.2.1, (step j).2.2.2.1, (step j).2.2.2.2.choose_spec.1⟩
  refine ⟨qs, _, ok, spec, ⟨prev.reduction, nq.symm.trans prev.count, prev.infos.trans nq, by simp [← nq, nt], ?_⟩⟩
  intro i hi
  have hid : i < ds.size := nq.symm ▸ hi
  let j : Fin tile.comps.size := ⟨i, nt ▸ hid⟩
  obtain ⟨grid, fmt, metadata, work, bytes, _⟩ := prev.component i hid
  have qr := (step j).1
  have qf := (step j).2.1
  change qs[i].rect = ds[i].rect at qr
  change qs[i].format = ds[i].format at qf
  simp only [Array.getElem_ofFn]
  exact ⟨qr.trans grid, qf.trans fmt, by rw [qr, qf]; exact metadata, qr ▸ work,
    by rw [qr, qf]; exact bytes, (step j).2.2.2.2.choose_spec.2⟩

/-- Two-way placement relation in the form consumed by the traversal's bind rule. -/
theorem placement_sim {L : Limits} {data : ByteArray} {h : Header} {t red : Nat}
    {g : Progression.Layout} {coding : Coding} {ds : Array OutputComponent}
    {info : Array DecodedComponent} {ps : Array SamplePlane} {src : Array Source} {tile : TileOut}
    (parsed : Header.parse L data = .ok h) (layoutOk : Progression.Layout.ofHeader h t = .ok (g, coding))
    (prev : State L h.siz red ds info ps) (input : TileRel h.siz red g coding src tile) :
    Tier2Equiv.Res (fun qs ss => State L h.siz red qs info ss)
      (writeTile L h.siz red g coding ds src) (place info ps tile) := by
  obtain ⟨_, _, native, spec, state⟩ := placement parsed layoutOk prev input
  rw [native, spec]
  exact state

private theorem outside (d : OutputComponent) (j : Nat) (hj : d.rect.width * d.rect.height ≤ j) :
    d.get? j = none := by
  obtain ⟨r, c, hd, b, hb⟩ := d
  cases b with
  | narrow p =>
    simp only [Storage.matches, Bool.and_eq_true, beq_iff_eq] at hb
    simp [OutputComponent.get?, Plane.get?, hb.1.1, hb.1.2, Nat.not_lt.mpr hj]
  | wide p =>
    simp only [Storage.matches, Bool.and_eq_true, beq_iff_eq] at hb
    simp [OutputComponent.get?, WidePlane.get?, hb.1.1.1.1, hb.1.1.1.2, Nat.not_lt.mpr hj]

/-- The two real finalizers turn the accumulated state into C9 at every public
accessor, including every index beyond the exact component raster length. -/
theorem finalize {L : Limits} (h : Header) (red sat : Nat) (ds : Array OutputComponent)
    (info : Array DecodedComponent) (ps : Array SamplePlane) (state : State L h.siz red ds info ps) :
    NativeEquiv.ImageRel red ⟨h, red, ds.map .native, sat⟩
      ⟨h, info.zipWith (fun m p => ⟨m, p.samples⟩) ps⟩ := by
  refine ⟨rfl, rfl, by simp [state.infos, state.planes], ?_⟩
  intro i hi hs
  simp only [Array.size_map] at hi
  simp only [Array.getElem_map, Array.getElem_zipWith]
  obtain ⟨_, _, metadata, _, _, rel⟩ := state.component i hi
  rw [metadata]
  have size := rel.size
  rw [rel.width, rel.height] at size
  refine ⟨by simp [infoFor, CodestreamComponent.x0, CodestreamComponent.y0, CodestreamComponent.width,
    CodestreamComponent.height, CodestreamComponent.depth, CodestreamComponent.signed,
    CodestreamComponent.dx, CodestreamComponent.dy], size, ?_, fun j hj => outside _ j (size ▸ hj)⟩
  intro j hj
  let w := ds[i].rect.width
  have bound : j < w * ds[i].rect.height := size ▸ hj
  have pos : 0 < w := by
    by_cases hz : w = 0
    · simp [hz] at bound
    · omega
  have hy : j / w < ds[i].rect.height := (Nat.div_lt_iff_lt_mul pos).2 ((Nat.mul_comm ..) ▸ bound)
  obtain ⟨v, a, read, cell, agree⟩ := rel.read (j % w) (j / w) (Nat.mod_lt _ pos) hy
  have idx : j / w * w + j % w = j := by rw [Nat.add_comm, Nat.mul_comm]; exact Nat.mod_add_div ..
  change ds[i].get? (j / w * w + j % w) = some v at read
  change (ps[i]'(state.planes.symm ▸ hi)).samples[j / w * w + j % w]? = some a at cell
  rw [idx] at read cell
  rw [Array.getElem?_eq_getElem hj, Option.some.injEq] at cell
  exact ⟨v, read, cell ▸ agree⟩

end JPEG2000.Spec.NativePlacement
