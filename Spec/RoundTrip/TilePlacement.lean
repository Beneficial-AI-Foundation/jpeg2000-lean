import Spec.Decode
import Spec.Resources
import Spec.RoundTrip.DisplayReconstruction

/-!
# Full-tile sample placement

Plan.md §§4 (C10), 5.3 and 7 (M7). T.800 Annex B.2 defines the image and
tile-component grids. At zero reduction the encoder's single tile covers the
entire output. The row, row-loop and component-loop proofs follow the writes
performed by the specification decoder.
-/

namespace JPEG2000.Spec.RoundTrip

open JPEG2000.Spec.Decode
open JPEG2000.Bytes (Plane)

/-- With equal source and destination offsets, copying a run updates exactly its
row-major indices. -/
theorem blitRow_samples (src : SamplePlane) (k start : Nat) (dst : Array SpecSample)
    (hs : dst.size = src.samples.size) (hb : start + k ≤ src.samples.size) :
    (blitRow src k start start dst).size = dst.size ∧
    ∀ j, (blitRow src k start start dst)[j]? =
      if start ≤ j ∧ j < start + k then src.samples[j]? else dst[j]? := by
  induction k generalizing start dst with
  | zero => simp [blitRow]; omega
  | succ k ih =>
    have hi : start < src.samples.size := by omega
    simp only [blitRow, Array.getElem?_eq_getElem hi]
    have h := ih (start + 1) (dst.setIfInBounds start src.samples[start])
      (by simpa using hs) (by omega)
    refine ⟨h.1.trans (by simp), fun j => ?_⟩
    rw [h.2, Array.getElem?_setIfInBounds]
    by_cases he : start = j
    · subst j
      simp [hs, hi]
    · simp only [he, ite_false]
      congr 1
      apply propext
      omega

/-- Copying consecutive full-width rows preserves the exact samples in those rows
and leaves every other index at its original value. -/
theorem blitRows_samples (src : SamplePlane) (k y : Nat) (dst : Array SpecSample)
    (hs : dst.size = src.samples.size) (hb : (y + k) * src.width ≤ src.samples.size) :
    (blitRows src src.width 0 0 k y dst).size = dst.size ∧
    ∀ j, (blitRows src src.width 0 0 k y dst)[j]? =
      if y * src.width ≤ j ∧ j < (y + k) * src.width then src.samples[j]? else dst[j]? := by
  induction k generalizing y dst with
  | zero => simp [blitRows]; omega
  | succ k ih =>
    have hy : (y + 1) * src.width ≤ (y + (k + 1)) * src.width :=
      Nat.mul_le_mul_right _ (by omega)
    have hr := blitRow_samples src src.width (y * src.width) dst hs
      (by simpa only [Nat.succ_mul] using Nat.le_trans hy hb)
    simp only [blitRows, Nat.zero_add, Nat.add_zero]
    have hend : y + 1 + k = y + (k + 1) := by omega
    have ht := ih (y+1) _ (hr.1.trans hs) (by rwa [hend])
    refine ⟨ht.1.trans hr.1, fun j => ?_⟩
    rw [ht.2, hr.2, hend, Nat.succ_mul]
    rw [Nat.succ_mul] at hy
    repeat' split
    all_goals first | rfl | omega

/-- A full-tile blit at zero offset returns the complete source plane,
including every sample's reconstruction trace. -/
theorem blit_fullTile (dst src : SamplePlane)
    (hw : dst.width = src.width) (hh : dst.height = src.height)
    (hs : src.samples.size = src.width * src.height)
    (hd : dst.samples.size = src.samples.size) :
    blit dst src 0 0 = .ok src := by
  have area : (0 + src.height) * src.width = src.samples.size := by
    rw [Nat.zero_add, Nat.mul_comm, hs]
  have h := blitRows_samples src src.height 0 dst.samples hd (Nat.le_of_eq area)
  have he : blitRows src src.width 0 0 src.height 0 dst.samples = src.samples := by
    apply Array.ext_getElem?
    intro j
    rw [h.2, area]
    by_cases hj : j < src.samples.size
    · simp [hj]
    · simp [hj, Array.getElem?_eq_none (show dst.samples.size ≤ j by omega)]
  simp [blit, hw, hh, he]

private theorem range_states {α : Type} {f : Nat → α → Except Error (ForInStep α)}
    (state : Nat → α) (n : Nat) (step : ∀ i < n, f i (state i) = .ok (.yield (state (i+1)))) :
    forIn [0:n] (state 0) f = .ok (state n) := by
  have aux (k : Nat) : ∀ i, i + k ≤ n →
      forIn (List.range' i k) (state i) f = .ok (state (i+k)) := by
    induction k with
    | zero => intro i _; rfl
    | succ k ih =>
      intro i hi
      rw [List.range'_succ, List.forIn_cons, step i (by omega)]
      exact (ih (i+1) (by omega)).trans (by rw [show i+1+k = i+(k+1) by omega])
  simpa [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size] using aux n 0 (by simp)

/-- Placing a tile covering each output component returns its source planes in component
order. Origins and extents are compared per component, for any component count. -/
theorem place_fullTile (info : Array DecodedComponent) (planes : Array SamplePlane) (t : TileOut)
    (hi : info.size = t.comps.size) (hp : planes.size = t.comps.size)
    (geom : ∀ (i : Nat) (h : i < t.comps.size),
      let r := t.comps[i].1
      let src := t.comps[i].2
      let dc := info[i]'(by omega)
      let dst := planes[i]'(by omega)
      r.x0 = dc.x0 ∧ r.y0 = dc.y0 ∧ dst.width = src.width ∧ dst.height = src.height ∧
      src.samples.size = src.width * src.height ∧ dst.samples.size = src.samples.size) :
    place info planes t = .ok (t.comps.map Prod.snd) := by
  let state (i : Nat) := Array.ofFn (n := t.comps.size) fun j =>
    if j.val < i then t.comps[j.val].2 else planes[j.val]'(by have := j.isLt; omega)
  have hzero : planes = state 0 := by
    apply Array.ext (by simp [state, hp])
    intros
    simp [state]
  have hend : state t.comps.size = t.comps.map Prod.snd := by
    apply Array.ext (by simp [state])
    intros
    simp [state]
  unfold place
  dsimp only
  rw [hzero, range_states state t.comps.size]
  · exact congrArg Except.ok hend
  · intro i hit
    have hii : i < info.size := by omega
    have hist : i < (state i).size := by simpa [state] using hit
    obtain ⟨hx, hy, hw, hh, hs, hd⟩ := geom i hit
    rw [Array.getElem?_eq_getElem hit, Array.getElem?_eq_getElem hii]
    dsimp only
    simp only [hx, hy, Nat.lt_irrefl, or_self, ite_false, Nat.sub_self]
    have hdst : (state i).getD i default = planes[i]'(by omega) := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hist]
      simp [state]
    rw [hdst, blit_fullTile _ _ hw hh hs hd]
    suffices (state i).setIfInBounds i t.comps[i].2 = state (i+1) by
      exact congrArg (fun a => Except.ok (ForInStep.yield a)) this
    apply Array.ext (by simp [state])
    intro j _ hj
    have hj' : j < (state i).size := by simpa [state] using hj
    rw [Array.getElem_setIfInBounds hj']
    by_cases hij : i = j
    · subst j; simp [state]
    · have he : j < i + 1 ↔ j < i := by omega
      simp [state, hij, he]

/-- At reduction zero, placing the encoder's full-image tile into the actual allocated
component stores returns all reconstructed planes, with their row-major arrays intact. -/
theorem place_encTile {L : Limits} {img : Encode.Image} {info : Array DecodedComponent}
    {ps : Array Plane} (t : TileOut)
    (hw : img.width < 2^32) (hh : img.height < 2^32)
    (ha : JPEG2000.Decode.allocOutput L (encSIZ img) 0 = .ok (info, ps))
    (hc : t.comps.size = img.comps.size)
    (ht : ∀ (i : Nat) (h : i < t.comps.size),
      t.comps[i].1 = encRect img ∧ t.comps[i].2.width = img.width ∧
      t.comps[i].2.height = img.height ∧ t.comps[i].2.samples.size = img.width * img.height) :
    place info (initPlanes ps) t = .ok (t.comps.map Prod.snd) := by
  unfold JPEG2000.Decode.allocOutput at ha
  simp only [bind, Except.bind, pure, Except.pure] at ha
  split at ha
  · contradiction
  split at ha
  · contradiction
  simp only [Except.ok.injEq, Prod.mk.injEq] at ha
  obtain ⟨rfl, rfl⟩ := ha
  apply place_fullTile _ _ _ (by simp [encSIZ, hc]) (by simp [initPlanes, encSIZ, hc])
  intro i hi
  obtain ⟨hr, hw', hh', hs⟩ := ht i hi
  simp [initPlanes, encSIZ, JPEG2000.Decode.compImageRect, Header.compRect, Header.imageRect,
    Assemble.reduceRect, Header.cdivPow, Header.cdiv, hr, encRect, Header.Rect.width,
    Header.Rect.height, Plane.zero, hw', hh', hs, Nat.mod_eq_of_lt hw, Nat.mod_eq_of_lt hh]

/-- The full-resolution cell budget of an encoder image is its area times its component count. -/
theorem outputCells_encSIZ {img : Encode.Image} (hw : img.width < 2^32) (hh : img.height < 2^32) :
    Resources.outputCells (encSIZ img) 0 = img.comps.size * (img.width * img.height) := by
  simp [Resources.outputCells, encSIZ, JPEG2000.Decode.compImageRect, Header.compRect,
    Header.imageRect, Assemble.reduceRect, Header.cdivPow, Header.cdiv, Header.Rect.width,
    Header.Rect.height, Nat.mod_eq_of_lt hw, Nat.mod_eq_of_lt hh, Function.comp_def, List.map_const',
    List.sum_replicate_nat]

/-- The full-resolution byte budget sums the stored width of each input component across its pixels. -/
theorem outputBytes_encSIZ {img : Encode.Image} (hw : img.width < 2^32) (hh : img.height < 2^32)
    (hd : ∀ c ∈ img.comps, c.depth < 256) :
    Resources.outputBytes (encSIZ img) 0 = (img.comps.toList.map fun c =>
      img.width * img.height * Header.bytesPerSample c.depth).sum := by
  unfold Resources.outputBytes
  congr 1
  simp only [encSIZ, Array.toList_map, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro c hc
  simp [JPEG2000.Decode.compImageRect, Header.compRect, Header.imageRect, Assemble.reduceRect,
    Header.cdivPow, Header.cdiv, Header.Rect.width, Header.Rect.height,
    Nat.mod_eq_of_lt hw, Nat.mod_eq_of_lt hh, Nat.mod_eq_of_lt (hd c (by simpa using hc))]

/-- Allocating and placing the reconstructed encoder tile preserves all of its component planes.
The two output budgets are measured at zero reduction as in the public decoder. -/
theorem place_encTile_of_limits {L : Limits} {p : Encode.Params} {img : Encode.Image} (t : TileOut)
    (checked : Encode.check Limits.default p img = .ok ())
    (hw : img.width < 2^32) (hh : img.height < 2^32)
    (hcells : img.comps.size * (img.width * img.height) ≤ L.maxWorkSamples)
    (hbytes : (img.comps.toList.map fun c => img.width * img.height *
      Header.bytesPerSample c.depth).sum ≤ L.maxDecodedBytes)
    (hc : t.comps.size = img.comps.size)
    (ht : ∀ (i : Nat) (h : i < t.comps.size),
      t.comps[i].1 = encRect img ∧ t.comps[i].2.width = img.width ∧
      t.comps[i].2.height = img.height ∧ t.comps[i].2.samples.size = img.width * img.height) :
    ∃ info ps, JPEG2000.Decode.allocOutput L (encSIZ img) 0 = .ok (info, ps) ∧
      place info (initPlanes ps) t = .ok (t.comps.map Prod.snd) := by
  have hd (c : Encode.Component) (hc : c ∈ img.comps) : c.depth < 256 :=
    Nat.lt_trans (Nat.lt_succ_of_le (check_component_samples checked c hc).1.2) (by decide)
  obtain ⟨⟨info, ps⟩, ha⟩ := (Resources.allocOutput_ok_iff L (encSIZ img) 0).2
    ⟨(outputCells_encSIZ hw hh).symm ▸ hcells, (outputBytes_encSIZ hw hh hd).symm ▸ hbytes⟩
  exact ⟨info, ps, ha, place_encTile t hw hh ha hc ht⟩

end JPEG2000.Spec.RoundTrip
