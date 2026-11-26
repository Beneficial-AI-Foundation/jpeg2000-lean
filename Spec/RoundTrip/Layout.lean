import Spec.RoundTrip.Header
import Spec.Tier2

/-!
# The packet layout of the reference encoder's tile

Plan.md §§4 (C10, S3), 5.3 and 7 (M7), task 7.3f1. T.800 A.5.1, A.6.1,
B.3, B.6 and B.12.1.1. All components cover the image with unit sampling.
Their LRCP packet count is the sum of the default precinct grid sizes over
resolutions, multiplied by the component count.
-/

namespace JPEG2000.Spec.RoundTrip

open JPEG2000 JPEG2000.Encode JPEG2000.Header JPEG2000.Marker JPEG2000.TilePart
open JPEG2000.Progression JPEG2000.Tier2.Geometry

variable (p : Params) (img : Image) (guard : Nat) (exps : Array Nat)

/-- The geometry shared by every encoder component. -/
def encGeom : TileCompGeom :=
  { tile := encRect img, rect := encRect img, dx := 1, dy := 1, params := encParams p guard exps }

/-- The packet iterator's single-tile layout. -/
def encLayout : Layout :=
  { tile := encRect img, layers := 1, comps := Array.replicate img.comps.size (encGeom p img guard exps) }

/-- The encoder passes this geometry to `encodeComp` at every component index it visits. -/
theorem tileComp_enc (i : Nat) (hi : i < img.comps.size) :
    tileComp (encRect img) ((encSIZ img).components.getD i default) (encParams p guard exps) =
      encGeom p img guard exps := by
  simp [tileComp, encSIZ, Array.getD_eq_getD_getElem?, hi, compRect, encRect, cdiv, encGeom]

/-- The component count, packet progression, layer count and marker flags used by the tile decoder. -/
theorem encLayout_coding :
    (encLayout p img guard exps).numComps = img.comps.size ∧
    (encLayout p img guard exps).layers = 1 ∧
    (encCoding p img guard exps).progression = .lrcp ∧ (encCoding p img guard exps).layers = 1 ∧
    (encCoding p img guard exps).poc = #[] ∧ (encCoding p img guard exps).sop = false ∧
    (encCoding p img guard exps).eph = false := by
  simp [Layout.numComps, encLayout, encCoding]

/-- Looking up a valid component gives the encoder's geometry. -/
theorem encLayout_comp (i : Nat) (hi : i < img.comps.size) :
    (encLayout p img guard exps).comp i = encGeom p img guard exps := by
  simp [Layout.comp, encLayout, Array.getD_eq_getD_getElem?, hi]

/-- Component rectangles satisfy the packet iterator's sampling equations. -/
theorem encLayout_wf : (encLayout p img guard exps).WF := by
  intro i hi
  rw [(encLayout_coding p img guard exps).1] at hi
  rw [encLayout_comp p img guard exps i hi]
  simp [encGeom, encRect, encLayout, cdiv]

private theorem geometry_ofHeader_enc (data : ByteArray) (hc : EncCheckFacts p img)
    (i : Nat) (hi : i < img.comps.size) :
    JPEG2000.Tier2.Geometry.ofHeader (encHeader p img guard exps data) 0 i = .ok (encGeom p img guard exps) := by
  let h := encHeader p img guard exps data
  have hn := (numTiles_enc img hc.width_le hc.height_le hc.width_pos hc.height_pos).2.2
  have ht := tileRect_enc img hc.width_le hc.height_le hc.width_pos hc.height_pos
  change JPEG2000.Tier2.Geometry.ofHeader h 0 i = _
  simp only [JPEG2000.Tier2.Geometry.ofHeader, show h.siz = encSIZ img from rfl, hn, ht]
  simp [h, encHeader, encSIZ, encCoding, hi, tileComp, compRect, encGeom, encRect, cdiv,
    pure, Except.pure]

private theorem mapM_const_on {α β ε : Type} (f : α → Except ε β) (b : β) (xs : List α)
    (hf : ∀ x ∈ xs, f x = .ok b) : xs.mapM f = .ok (List.replicate xs.length b) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [List.mapM_cons, hf x (by simp), ih (fun y hy => hf y (by simp [hy])),
      List.replicate_succ, bind, Except.bind, pure, Except.pure]

/-- The layout lookup at tile zero succeeds on the parsed encoder header. -/
theorem layout_ofHeader_enc (data : ByteArray) (hc : EncCheckFacts p img) :
    Layout.ofHeader (encHeader p img guard exps data) 0 =
      .ok (encLayout p img guard exps, encCoding p img guard exps) := by
  let h := encHeader p img guard exps data
  have hn := (numTiles_enc img hc.width_le hc.height_le hc.width_pos hc.height_pos).2.2
  have ht := tileRect_enc img hc.width_le hc.height_le hc.width_pos hc.height_pos
  have hm : (Array.range img.comps.size).mapM (JPEG2000.Tier2.Geometry.ofHeader h 0) =
      .ok (Array.replicate img.comps.size (encGeom p img guard exps)) := by
    rw [Array.mapM_eq_mapM_toList, mapM_const_on _ (encGeom p img guard exps)]
    · simp [Functor.map, Except.map]
    · intro i hi
      exact geometry_ofHeader_enc p img guard exps data hc i (by simpa using hi)
  change Layout.ofHeader h 0 = _
  simp only [Layout.ofHeader, show h.siz = encSIZ img from rfl, hn, ht,
    show (encSIZ img).csiz = img.comps.size by simp [encSIZ, SIZ.csiz], hm]
  rfl

private theorem foldr_max_replicate (k n : Nat) :
    (List.replicate (n + 1) k).foldr max 0 = k := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, List.foldr_cons, ih, Nat.max_self]

/-- The maximum decomposition depth of the nonempty component array is the encoder depth. -/
theorem encLayout_maxLevels (hn : 0 < img.comps.size) :
    (encLayout p img guard exps).maxLevels = p.levels := by
  simp only [Layout.maxLevels, encLayout, Array.toList_replicate, List.map_replicate]
  obtain ⟨n, he⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [he, foldr_max_replicate]
  rfl

/-- Precincts of resolution `r ≤ NL` of one encoder component, in image coordinates.
A default precinct spans `2^(NL − r + 15)` reference-grid samples along each axis. -/
def encResolutionPrecincts (levels width height r : Nat) : Nat :=
  let e := levels - r + 15
  cdivPow width e * cdivPow height e

private theorem zero_cdivPow (e : Nat) : cdivPow 0 e = 0 := by
  have h : 0 < 2 ^ e := Nat.pow_pos (by decide)
  simp [cdivPow, cdiv, Nat.div_eq_of_lt (show 2 ^ e - 1 < 2 ^ e by omega)]

private theorem gridCount_zero (w e : Nat) : gridCount 0 w e = cdivPow w e := by
  cases w <;> simp [gridCount, zero_cdivPow]

private theorem precinct_exp (r : Nat) :
    (encParams p guard exps).precincts.getD r Precinct.default = Precinct.default := by
  simp only [encParams, Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
  split <;> rfl

private theorem scale_precinct_axis (w d : Nat) :
    cdivPow (cdivPow w d) 15 = cdivPow w (d + 15) := by
  unfold cdivPow
  rw [Spec.Progression.Axis.cdiv_cdiv (Nat.pow_pos (by decide)) (by decide), Nat.pow_add]

/-- Every valid layout lookup counts exactly the default precinct grid at that resolution. -/
theorem encLayout_numPrecincts (i r : Nat) (hi : i < img.comps.size) (hr : r ≤ p.levels) :
    (encLayout p img guard exps).numPrecincts i r =
      encResolutionPrecincts p.levels img.width img.height r := by
  simp only [Layout.numPrecincts, Layout.levels, Layout.pw, Layout.ph, Layout.resRect,
    Layout.ppx, Layout.ppy, encLayout_comp p img guard exps i hi, encGeom, precinct_exp]
  change (if r ≤ p.levels then _ else 0) = _
  rw [ite_eq_left hr]
  simp [Header.resRect, encRect, encParams, zero_cdivPow, gridCount_zero, Precinct.default,
    scale_precinct_axis, encResolutionPrecincts]

private theorem fold_add_on {α : Type} (xs : List α) (f : Nat → α → Nat) (w : α → Nat)
    (hf : ∀ x ∈ xs, ∀ a, f a x = a + w x) (a : Nat) :
    xs.foldl f a = a + (xs.map w).sum := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, ih (fun y hy => hf y (by simp [hy])), hf x (by simp)]
    simp [Nat.add_assoc]

/-- LRCP work is one visit per precinct of each component and resolution. The formula
depends only on the image dimensions, number of components and decomposition depth. -/
theorem iterationWork_enc (hn : 0 < img.comps.size) :
    iterationWork (encLayout p img guard exps) .lrcp #[] =
      img.comps.size * ((List.range (p.levels + 1)).map
        (encResolutionPrecincts p.levels img.width img.height)).sum := by
  let g := encLayout p img guard exps
  let w := encResolutionPrecincts p.levels img.width img.height
  let rs := List.range (p.levels + 1)
  have hc : g.numComps = img.comps.size := (encLayout_coding p img guard exps).1
  have inner (i : Nat) (hi : i < img.comps.size) (a : Nat) :
      rs.foldl (fun a r => a + g.numPrecincts i r) a = a + (rs.map w).sum := by
    apply fold_add_on
    intro r hr b
    rw [encLayout_numPrecincts p img guard exps i r hi (by
      have : r < p.levels + 1 := List.mem_range.mp hr
      omega)]
  change iterationWork g .lrcp #[] = _
  simp only [iterationWork, volumes, Array.isEmpty_empty, ite_true, List.zipIdx_cons,
    List.zipIdx_nil, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
    Volume.le, Volume.ce, Volume.re, Volume.full, Nat.min_self, hc,
    show g.layers = 1 from rfl, show g.maxLevels = p.levels from encLayout_maxLevels p img guard exps hn,
    Nat.sub_zero, ← List.range_eq_range', Nat.zero_add, Nat.one_mul]
  rw [fold_add_on _ _ (fun _ => (rs.map w).sum) (fun i hi a => inner i (List.mem_range.mp hi) a)]
  simp [List.map_const', List.sum_replicate_nat, rs, w]

private theorem numPrecincts_grid (rr : Rect) (pp : Precinct) :
    Header.numPrecincts rr pp =
      gridCount rr.x0 rr.x1 pp.ppx.toNat * gridCount rr.y0 rr.y1 pp.ppy.toNat := by
  by_cases hx : rr.x1 ≤ rr.x0 <;> by_cases hy : rr.y1 ≤ rr.y0 <;>
    simp [Header.numPrecincts, gridCount, hx, hy]

private theorem fold_counts (cb pr : Nat → Nat) (rs : List Nat) (acc : Nat × Nat) :
    (rs.foldl (fun (b, n) r => (b + cb r, n + pr r)) acc).2 = acc.2 + (rs.map pr).sum := by
  induction rs generalizing acc with
  | nil => simp
  | cons r rs ih =>
    cases acc
    simp [ih, Nat.add_assoc]

/-- The header work check counts precisely the same precincts as the LRCP iterator. -/
theorem encCounts_precincts :
    (encCounts p img guard exps).2 =
      ((List.range (p.levels + 1)).map (encResolutionPrecincts p.levels img.width img.height)).sum := by
  unfold encCounts tileCompCounts
  rw [fold_counts]
  simp only [Nat.zero_add]
  congr 1
  apply List.map_congr_left
  intro r _
  rw [precinct_exp, numPrecincts_grid]
  simp [Header.resRect, encRect, encParams, Precinct.default, zero_cdivPow,
    gridCount_zero, scale_precinct_axis, encResolutionPrecincts]

/-- The packet limit already assumed for the header admits the work check in `Spec.Tier2.decodeTile`. -/
theorem iterationWork_check_of_headerFits (L : Limits) (size : Nat) (hc : EncCheckFacts p img)
    (fits : HeaderFits L p img guard exps size) :
    L.check Spec.Tier2.loc .packets
      (iterationWork (encLayout p img guard exps) (encCoding p img guard exps).progression
        (encCoding p img guard exps).poc) = .ok () := by
  apply (Limits.check_eq_ok_iff ..).2
  change iterationWork (encLayout p img guard exps) .lrcp #[] ≤ L.maxPackets
  rw [iterationWork_enc p img guard exps hc.comps_pos, ← encCounts_precincts p img guard exps]
  exact fits.packets

private theorem precinct_axis_le_four (w d : Nat) (hw : w ≤ 2 ^ 17) :
    cdivPow w (d + 15) ≤ 4 := by
  have h : 2 ^ 15 ≤ 2 ^ (d + 15) := Nat.pow_le_pow_right (by decide) (by omega)
  rw [← Nat.lt_succ_iff]
  unfold cdivPow cdiv
  exact (Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide))).2 (by omega)

/-- Under the encoder side-length bounds, at most sixteen precincts per resolution suffice
to bound one component's packet work, including images wider or taller than a precinct. -/
theorem iterationWork_enc_le (hc : EncCheckFacts p img) :
    iterationWork (encLayout p img guard exps) .lrcp #[] ≤ img.comps.size * ((p.levels + 1) * 16) := by
  rw [iterationWork_enc p img guard exps hc.comps_pos]
  apply Nat.mul_le_mul_left
  have bound (rs : List Nat) :
      (rs.map (encResolutionPrecincts p.levels img.width img.height)).sum ≤ rs.length * 16 := by
    induction rs with
    | nil => simp
    | cons r rs ih =>
      have hr : encResolutionPrecincts p.levels img.width img.height r ≤ 4 * 4 :=
        Nat.mul_le_mul (precinct_axis_le_four _ _ hc.width_le) (precinct_axis_le_four _ _ hc.height_le)
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
      omega
  simpa using bound (List.range (p.levels + 1))

/-- Every checked encoder image passes the default packet iteration limit, independently of
the other header resource checks. -/
theorem iterationWork_check_default (hc : EncCheckFacts p img) :
    Limits.default.check Spec.Tier2.loc .packets (iterationWork (encLayout p img guard exps) .lrcp #[]) =
      .ok () := by
  apply (Limits.check_eq_ok_iff ..).2
  have h := Nat.mul_le_mul hc.comps_le (Nat.mul_le_mul_right 16 (Nat.succ_le_succ hc.levels_le))
  exact Nat.le_trans (iterationWork_enc_le p img guard exps hc) (Nat.le_trans h (by decide))

end JPEG2000.Spec.RoundTrip
