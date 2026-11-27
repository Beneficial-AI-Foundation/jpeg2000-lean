import Spec.NativeEquiv
import Spec.Resources
import Spec.WideHeaderBounds

/-!
# Initial native and specification planes (Plan.md §§4, 5, 7, T.800 A.5.1 and B.2)

The component state records the original grid, the allocated budgets, and the
sample relation at each raster coordinate. It is shared by allocation, placement
and the final image construction.
-/

namespace JPEG2000.Spec.NativePlacement

open JPEG2000.NativeOutput JPEG2000.Spec.Decode Header Bytes

/-- Specification component metadata before attaching a raster. -/
def infoFor (r : Rect) (c : Marker.Component) : DecodedComponent :=
  { x0 := r.x0, y0 := r.y0, width := r.width, height := r.height,
    depth := c.depth.toNat, signed := c.signed, dx := c.dx.toNat, dy := c.dy.toNat,
    plane := Plane.zero 0 0 }

/-- The two raster representations have the same dimensions and agree at every coordinate. -/
structure PlaneRel (s : Marker.SIZ) (i : Nat) (d : OutputComponent) (p : SamplePlane) : Prop where
  /-- Reduced component width. -/
  width : p.width = d.rect.width
  /-- Reduced component height. -/
  height : p.height = d.rect.height
  /-- Exact length of the specification sample array. -/
  size : p.samples.size = p.width * p.height
  /-- Quantitative C9 at each row-major read, using the stored sample's transform metadata. -/
  read : ∀ x y, x < d.rect.width → y < d.rect.height → ∃ v a,
    d.get? (y*d.rect.width+x) = some v ∧ p.samples[y*d.rect.width+x]? = some a ∧
    NativeSample.Agrees (Assemble.fracBitsOf s a.mct i) v a

/-- Invariant after any number of tile placements, including zero. -/
structure State (L : Limits) (s : Marker.SIZ) (red : Nat) (ds : Array OutputComponent)
    (info : Array DecodedComponent) (ps : Array SamplePlane) : Prop where
  /-- The allocation admitted the requested reduction. -/
  reduction : red ≤ L.maxDecompLevels
  /-- Native count in SIZ order. -/
  count : ds.size = s.components.size
  /-- Metadata count. -/
  infos : info.size = ds.size
  /-- Specification raster count. -/
  planes : ps.size = ds.size
  /-- Each component retains its parsed format, reduced grid, limits and related samples. -/
  component : ∀ i (hi : i < ds.size),
    let d := ds[i]
    let c := s.components[i]'(count ▸ hi)
    d.rect = JPEG2000.Decode.compImageRect s c red ∧ d.format = c ∧
      info[i]'(infos.symm ▸ hi) = infoFor d.rect d.format ∧
      d.rect.width * d.rect.height ≤ L.maxWorkSamples ∧
      d.rect.width * d.rect.height * bytesPerSample d.format.depth.toNat ≤ L.maxDecodedBytes ∧
      PlaneRel s i d (ps[i]'(planes.symm ▸ hi))

open JPEG2000.Spec.Tier2Equiv (bind_ok)

private theorem read_depth {r r' : Reader} {c : Marker.Component}
    (ok : Marker.readSizComponent r = .ok (c, r')) : 1 ≤ c.depth.toNat ∧ c.depth.toNat ≤ 38 := by
  unfold Marker.readSizComponent at ok
  obtain ⟨⟨s, _⟩, _, ok⟩ := bind_ok ok
  obtain ⟨_, checked, ok⟩ := bind_ok ok
  obtain ⟨⟨_, _⟩, _, ok⟩ := bind_ok ok
  obtain ⟨_, _, ok⟩ := bind_ok ok
  obtain ⟨⟨_, _⟩, _, ok⟩ := bind_ok ok
  obtain ⟨_, _, ok⟩ := bind_ok ok
  unfold Marker.require at checked
  split at checked <;> try contradiction
  rename_i bound
  cases ok
  simp only [decide_eq_true_eq, UInt8.lt_iff_toNat_lt] at bound
  change (s &&& 127).toNat < 38 at bound
  simp only [UInt8.toNat_add, UInt8.toNat_one]
  omega

private theorem siz_depth {L : Limits} {r : Reader} {s : Marker.SIZ}
    (ok : Marker.parseSIZ L r = .ok s) :
    ∀ c ∈ s.components, 1 ≤ c.depth.toNat ∧ c.depth.toNat ≤ 38 := by
  unfold Marker.parseSIZ at ok
  iterate 10 obtain ⟨⟨_, _⟩, _, ok⟩ := bind_ok ok
  iterate 7 obtain ⟨_, _, ok⟩ := bind_ok ok
  obtain ⟨⟨_, _⟩, components, ok⟩ := bind_ok ok
  obtain ⟨_, _, ok⟩ := bind_ok ok
  cases ok
  exact HeaderWF.readArray_inv _ _ (fun _ _ _ => read_depth) _ _ _ _ _ (by simp) components

/-- Successful header parsing supplies the exact precision interval required by native allocation. -/
theorem parsed_depth {L : Limits} {data : ByteArray} {h : Header}
    (parsed : Header.parse L data = .ok h) :
    ∀ c ∈ h.siz.components, 1 ≤ c.depth.toNat ∧ c.depth.toNat ≤ 38 := by
  unfold Header.parse at parsed
  obtain ⟨_, _, parsed⟩ := bind_ok parsed
  unfold parseCodestreamIn at parsed
  obtain ⟨_, _, parsed⟩ := bind_ok parsed
  obtain ⟨⟨_, _⟩, main, parsed⟩ := bind_ok parsed
  repeat (obtain ⟨_, _, parsed⟩ := bind_ok parsed)
  cases parsed
  obtain ⟨⟨_, ok⟩, _⟩ := HeaderWF.parseMainHeader_fields main
  exact siz_depth ok

private theorem budgets (s : Marker.SIZ) (red : Nat) :
    cells (layout s red) = Resources.outputCells s red ∧
    decodedBytes (layout s red) = Resources.outputBytes s red := by
  unfold cells decodedBytes
  rw [Resources.array_foldl_sum _ (fun (x : Rect × Marker.Component) => x.1.width * x.1.height)
    (fun _ _ => rfl), Resources.array_foldl_sum _ (fun (x : Rect × Marker.Component) =>
      x.1.width*x.1.height*bytesPerSample x.2.depth.toNat) (fun _ _ => rfl)]
  simp only [layout, Array.toList_map, List.map_map]
  exact ⟨rfl, rfl⟩

private theorem term_le_sum {α : Type} (f : α → Nat) {l : List α} {a : α} (ha : a ∈ l) :
    f a ≤ (l.map f).sum := by
  induction l with
  | nil => cases ha
  | cons b l ih =>
    simp only [List.mem_cons] at ha
    simp only [List.map_cons, List.sum_cons]
    rcases ha with rfl | ha
    · omega
    · have := ih ha; omega

private theorem initial {L : Limits} {s : Marker.SIZ} {red : Nat} {ds : Array OutputComponent}
    {info : Array DecodedComponent} {ps : Array Plane}
    (ha : allocOutput L s red = .ok ds) (hb : JPEG2000.Decode.allocOutput L s red = .ok (info, ps)) :
    State L s red ds info (initPlanes ps) := by
  obtain ⟨work, bytes, sz, idx⟩ := NativeOutput.allocOutput_spec ha
  have count : ds.size = s.components.size := by simpa [layout] using sz.symm
  have ⟨wc, bc⟩ := budgets s red
  rw [wc] at work
  rw [bc] at bytes
  unfold JPEG2000.Decode.allocOutput at hb
  simp only [bind, Except.bind] at hb
  split at hb <;> try contradiction
  split at hb <;> try contradiction
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hb
  obtain ⟨rfl, rfl⟩ := hb
  have reduction : red ≤ L.maxDecompLevels := by
    unfold allocOutput at ha
    obtain ⟨_, checked, _⟩ := Tier2Equiv.bind_ok ha
    unfold Limits.check Limits.checkLe at checked
    split at checked <;> first | assumption | contradiction
  refine ⟨reduction, count, by simp [count], by simp [initPlanes, count], ?_⟩
  intro i hi
  have hc : i < s.components.size := count ▸ hi
  obtain ⟨d, hit, hr, hf, zero⟩ := idx i (sz.symm ▸ hi)
  have eq : ds[i] = d := by simpa [hi] using hit
  simp only [layout, Array.getElem_map] at hr hf
  simp only [Array.getElem_map, initPlanes, eq]
  have mem := Array.getElem_mem_toList hc
  refine ⟨hr, hf, by rw [hr, hf]; rfl, ?_, ?_, ?_⟩
  · rw [hr]
    apply Nat.le_trans _ work
    exact term_le_sum (fun c => let r := JPEG2000.Decode.compImageRect s c red
      r.width * r.height) mem
  · rw [hr, hf]
    apply Nat.le_trans _ bytes
    exact term_le_sum (fun c => let r := JPEG2000.Decode.compImageRect s c red
      r.width * r.height * bytesPerSample c.depth.toNat) mem
  · refine ⟨congrArg Rect.width hr.symm, congrArg Rect.height hr.symm, by simp, ?_⟩
    intro x y hx hy
    refine ⟨0, SpecSample.blank, zero _ (DWT53.idx_lt hx hy), ?_, rfl⟩
    have bound := DWT53.idx_lt hx hy
    rw [hr] at bound ⊢
    simp [Plane.zero, JPEG2000.Decode.compImageRect, bound]

/-- At an admitted reduction the allocators agree on rejection in both directions.
On success all SIZ metadata, aggregate-limit consequences and blank samples agree. -/
theorem allocation {L : Limits} {data : ByteArray} {h : Header} {red : Nat}
    (parsed : Header.parse L data = .ok h) (hr : red ≤ L.maxDecompLevels) :
    Tier2Equiv.Res (fun ds p => State L h.siz red ds p.1 (initPlanes p.2))
      (allocOutput L h.siz red) (JPEG2000.Decode.allocOutput L h.siz red) := by
  obtain ⟨w, b⟩ := budgets h.siz red
  cases ha : allocOutput L h.siz red with
  | error e =>
    cases hb : JPEG2000.Decode.allocOutput L h.siz red with
    | error => trivial
    | ok p =>
      obtain ⟨hw, hb'⟩ := (Resources.allocOutput_ok_iff ..).1 ⟨p, hb⟩
      obtain ⟨q, hq⟩ := NativeOutput.allocOutput_succeeds L h.siz red hr
        (w ▸ hw) (b ▸ hb') (parsed_depth parsed)
      rw [ha] at hq; contradiction
  | ok ds =>
    obtain ⟨hw, hb, _, _⟩ := NativeOutput.allocOutput_spec ha
    obtain ⟨⟨info, ps⟩, ok⟩ := (Resources.allocOutput_ok_iff L h.siz red).2 ⟨w ▸ hw, b ▸ hb⟩
    rw [ok]
    exact initial ha ok

/-- With the entry point's reduction check included on the spec side, the allocation
relation covers every reduction, including an over-limit request. -/
theorem guarded_allocation {L : Limits} {data : ByteArray} {h : Header} (red : Nat)
    (parsed : Header.parse L data = .ok h) :
    Tier2Equiv.Res (fun ds p => State L h.siz red ds p.1 (initPlanes p.2))
      (allocOutput L h.siz red) (do
        L.check JPEG2000.Decode.loc .decompLevels red
        JPEG2000.Decode.allocOutput L h.siz red) := by
  by_cases hr : red ≤ L.maxDecompLevels
  · simpa [Limits.check, Limits.checkLe, Limits.bound, hr, bind, Except.bind] using
      allocation parsed hr
  · simp [allocOutput, Limits.check, Limits.checkLe, Limits.bound, hr, bind, Except.bind, Tier2Equiv.Res]

end JPEG2000.Spec.NativePlacement
