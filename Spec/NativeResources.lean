import Spec.Resources
import Spec.CodestreamDispatch

/-!
# Allocation bounds for the public codestream result

Plan.md §§3, 4 (S3), 7. Declared output bytes follow the SIZ sample precision.
Physical storage uses four bytes for compact cells and eight for wider cells.
The bounds below cover the completed tile writes and the exact component accessor.
-/

namespace JPEG2000.Spec.NativeResources

open JPEG2000 JPEG2000.Header JPEG2000.Bytes JPEG2000.NativeOutput

/-- Byte length of the backing array actually held by a public component. -/
def backingBytes : CodestreamComponent → Nat
  | .compact c => c.plane.data.size
  | .native d => Spec.NativeOutput.backingBytes d

/-- The observable component grid and format agree with the corresponding SIZ entry. -/
def OnGrid (c : CodestreamComponent) (r : Rect) (f : Marker.Component) : Prop :=
  c.x0 = r.x0 ∧ c.y0 = r.y0 ∧ c.width = r.width ∧ c.height = r.height ∧
    c.depth = f.depth.toNat ∧ c.signed = f.signed ∧ c.dx = f.dx.toNat ∧ c.dy = f.dy.toNat

/-- Each SIZ component has one output with its reduced grid and declared format, in order. -/
def LayoutAgrees (cs : Array CodestreamComponent) (rs : Array (Rect × Marker.Component)) : Prop :=
  cs.size = rs.size ∧ ∀ i : Fin rs.size, ∃ c, cs[i.val]? = some c ∧ OnGrid c rs[i].1 rs[i].2

private theorem native_layout (ds : Array OutputComponent) (s : Marker.SIZ) (reduce : Nat)
    (hs : ds.map (fun d => (d.rect, d.format)) = layout s reduce) :
    LayoutAgrees (ds.map .native) (layout s reduce) := by
  rw [← hs]
  simp only [LayoutAgrees, Array.size_map, true_and]
  intro i
  have hi : i.val < ds.size := by simpa using i.isLt
  refine ⟨.native ds[i.val], ?_, ?_⟩
  · simp [Array.getElem?_eq_getElem hi]
  · simp [OnGrid, CodestreamComponent.x0, CodestreamComponent.y0, CodestreamComponent.width,
      CodestreamComponent.height, CodestreamComponent.depth, CodestreamComponent.signed,
      CodestreamComponent.dx, CodestreamComponent.dy]

/-- Public S3 postcondition on a successful full or reduced codestream decode. -/
structure Within (L : Limits) (data : ByteArray) (reduce : Nat) (img : CodestreamImage) : Prop where
  /-- The result uses the requested, admitted reduction. -/
  reduction : img.reduce = reduce ∧ reduce ≤ L.maxDecompLevels
  /-- The retained header satisfies all input and geometry bounds. -/
  header : Resources.HeaderWithin L data img.header
  /-- Component count, order, reduced grids, sampling factors and precision. -/
  geometry : LayoutAgrees img.comps (layout img.header.siz reduce)
  /-- Aggregate reduced output cells. -/
  work : (img.comps.toList.map fun c => c.width * c.height).sum ≤ L.maxWorkSamples
  /-- Aggregate output bytes counted under the declared SIZ precisions. -/
  bytes : (img.comps.toList.map fun c => c.width * c.height * bytesPerSample c.depth).sum ≤ L.maxDecodedBytes
  /-- Byte length of all actual backing arrays. -/
  physical : (img.comps.toList.map backingBytes).sum ≤ 8 * L.maxWorkSamples
  /-- The exact accessor succeeds precisely inside the component raster. -/
  readable : ∀ c ∈ img.comps, ∀ i, (c.get? i).isSome ↔ i < c.width * c.height

private theorem sum_bound {α : Type} (f g : α → Nat) (cs : List α)
    (h : ∀ c ∈ cs, f c ≤ 8 * g c) : (cs.map f).sum ≤ 8 * (cs.map g).sum := by
  induction cs with
  | nil => simp
  | cons a cs ih =>
    have ha := h a (by simp)
    have ht := ih (fun c hc => h c (by simp [hc]))
    simp only [List.map_cons, List.sum_cons, Nat.mul_add]
    omega

private theorem native_readable (d : OutputComponent) (i : Nat) :
    (d.get? i).isSome ↔ i < d.rect.width * d.rect.height := by
  obtain ⟨r, c, hd, s, hs⟩ := d
  cases s with
  | narrow p =>
    simp only [Storage.matches, Bool.and_eq_true, beq_iff_eq] at hs
    simp [OutputComponent.get?, Plane.get?, ← hs.1.1, ← hs.1.2]
  | wide p =>
    simp only [Storage.matches, Bool.and_eq_true, beq_iff_eq] at hs
    simp [OutputComponent.get?, WidePlane.get?, ← hs.1.1.1.1, ← hs.1.1.1.2]

private theorem native_within {L : Limits} {data : ByteArray} {reduce : Nat} {h : Header}
    {img : CodestreamImage} (hr : reduce ≤ L.maxDecompLevels) (hp : Header.parse L data = .ok h)
    (ok : decodeCodestream L data reduce = .ok img) : Within L data reduce img := by
  obtain ⟨hh, hred, ⟨ds, hd, shape⟩, work, bytes⟩ := CodestreamDispatch.native_geometry hp ok
  rw [← shape, cells, Resources.array_foldl_sum _ _ (fun _ _ => rfl)] at work
  rw [← shape, decodedBytes, Resources.array_foldl_sum _ _ (fun _ _ => rfl)] at bytes
  simp only [Array.toList_map, List.map_map, Function.comp_def] at work bytes
  refine ⟨⟨hred, hr⟩, hh ▸ Resources.parse_within hp, by rw [hd, hh]; exact native_layout ds _ _ shape, ?_, ?_, ?_, ?_⟩
  · simpa [hd, CodestreamComponent.width, CodestreamComponent.height, Function.comp_def] using work
  · simpa [hd, CodestreamComponent.width, CodestreamComponent.height, CodestreamComponent.depth,
      Function.comp_def] using bytes
  · have cap := sum_bound Spec.NativeOutput.backingBytes (fun d : OutputComponent => d.rect.width * d.rect.height)
        ds.toList (by intro c _; rw [Spec.NativeOutput.backing_size]; split <;> omega)
    simpa [hd, Function.comp_def, backingBytes] using (Nat.le_trans cap (Nat.mul_le_mul_left 8 work))
  · intro c hc i
    rw [hd] at hc
    obtain ⟨d, _, rfl⟩ := Array.mem_map.mp hc
    exact native_readable d i

/-- S3 for the public codestream decoder across all 1–38-bit component depths. -/
theorem decodeCodestream_resources {L : Limits} {data : ByteArray} {reduce : Nat}
    {img : CodestreamImage} (ok : decodeCodestream L data reduce = .ok img) :
    Within L data reduce img := by
  have check : L.check JPEG2000.Decode.loc .decompLevels reduce = .ok () := by
    cases he : L.check JPEG2000.Decode.loc .decompLevels reduce with
    | ok u => cases u; rfl
    | error e => simp [decodeCodestream, he, bind, Except.bind] at ok
  have hr : reduce ≤ L.maxDecompLevels := (Limits.checkLe_eq_ok_iff ..).mp check
  cases hp : Header.parse L data with
  | error e => simp [decodeCodestream, check, hp, bind, Except.bind] at ok
  | ok h => exact native_within hr hp ok

end JPEG2000.Spec.NativeResources
