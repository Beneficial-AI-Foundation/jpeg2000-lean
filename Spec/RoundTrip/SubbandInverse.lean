import Spec.RoundTrip.DisplayReconstruction
import Spec.QuantBlock
import Spec.DWTPlane.Local
import Spec.DWTPlane.Out

/-!
# Full-resolution reversible subband reconstruction (Plan.md §§4, 5.3, 7; T.800 B.5, F.3–F.4)

The encoder stores each band of the forward 5/3 transform as a row-major array. Agreement
with those arrays on their B-15 rectangles suffices to reconstruct the component supplied
to the forward transform, including the forward RCT when selected.
-/

namespace JPEG2000.Spec.RoundTrip

open JPEG2000.Encode JPEG2000.Tier2.Geometry JPEG2000.Spec.Decode
open JPEG2000.Spec.Equiv (ReadBand InBand BandsEq)

/-- A band from the reversible encoder's actual component, resolution and packet-band arrays. -/
def reversibleBand (p : Params) (img : Image) (c r : Nat) (b : Band) : BandData :=
  (((bands53 p img (encMct p img)).getD c #[]).getD r #[]).getD (b.index - 1) default

/-- Read a stored coefficient using the band's origin and row stride. -/
def bandSample (d : BandData) (u v : Int) : Int :=
  d.vals.getD ((v - d.rect.y0).toNat * d.rect.width + (u - d.rect.x0).toNat) 0

private theorem rowCount (p : Params) (img : Image) :
    (reversibleRows p img).size = img.comps.size := by
  unfold reversibleRows
  split <;> simp [mct3, shifted]

private theorem bandSlot {r : Nat} {b : Band} (hb : b ∈ bandsOf r) :
    (bandsOf r)[b.index - 1]? = some b := by
  by_cases hr : r = 0 <;> cases b <;> simp_all [bandsOf, Band.index]

/-- The forward 5/3 decomposition sampled by the encoder for component `c`. -/
def sampled53 (p : Params) (img : Image) (c : Nat) : DWT53.Dec :=
  DWT53.sdMulti (dwtRect img.width img.height) p.levels
    ⟨at2 ((reversibleRows p img).getD c #[]) img.width⟩

/-- The actual array entry has the B-15 rectangle and raster values produced by `bandData`. -/
theorem reversibleBand_eq {p : Params} {img : Image} {c r : Nat} {b : Band}
    (hc : c < img.comps.size) (hr : r ≤ p.levels) (hb : b ∈ bandsOf r) :
    reversibleBand p img c r b = bandData img.width img.height p.levels r b
      (Encode.band53 (sampled53 p img c) p.levels r b).get := by
  have hrow : c < (reversibleRows p img).size := by rwa [rowCount]
  change ((((reversibleRows p img).map _).getD c #[]).getD r #[]).getD (b.index - 1) default = _
  simp [Array.getD_eq_getD_getElem?, hrow, compBands, show r < p.levels + 1 by omega,
    bandSlot hb, sampled53]

private theorem bandData_sample {w h nl r : Nat} {b : Band} (f : Int → Int → Int)
    {u v : Int} (hin : InBand { x0 := 0, y0 := 0, x1 := w, y1 := h } (bandLevel nl r) b u v) :
    bandSample (bandData w h nl r b f) u v = f u v := by
  let rect := bandRect { x0 := 0, y0 := 0, x1 := w, y1 := h } (bandLevel nl r) b
  obtain ⟨hu0, hu1, hv0, hv1⟩ :
      (rect.x0 : Int) ≤ u ∧ u < rect.x1 ∧ (rect.y0 : Int) ≤ v ∧ v < rect.y1 := hin
  let x := (u - rect.x0).toNat
  let y := (v - rect.y0).toNat
  have hx : x < rect.width := by simp only [x, Header.Rect.width]; omega
  have hy : y < rect.height := by simp only [y, Header.Rect.height]; omega
  have hidx := JPEG2000.DWT53.idx_lt hx hy
  obtain ⟨hdiv, hmod⟩ := DWTPlane.divmod_idx (y := y) hx
  change (Array.ofFn (n := rect.width * rect.height) fun i =>
    f (rect.x0 + i.val % rect.width : Nat) (rect.y0 + i.val / rect.width : Nat)).getD
      (y * rect.width + x) 0 = f u v
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hidx, ↓reduceDIte,
    Option.getD_some, hmod, hdiv, Int.natCast_add]
  congr 1 <;> dsimp only [x, y] <;> omega

/-- At every valid band position the stored row-major coefficient equals the selected
grid of the sampled forward decomposition. -/
theorem reversibleBand_sample {p : Params} {img : Image} {c r : Nat} {b : Band}
    (hc : c < img.comps.size) (hr : r ≤ p.levels) (hb : b ∈ bandsOf r) {u v : Int}
    (hin : InBand (encRect img) (bandLevel p.levels r) b u v) :
    bandSample (reversibleBand p img c r b) u v =
      (Encode.band53 (sampled53 p img c) p.levels r b).get u v := by
  rw [reversibleBand_eq hc hr hb]
  exact bandData_sample _ hin

private theorem readBand_resolution {nl lvl : Nat} {b : Band} (h : ReadBand nl lvl b) :
    ∃ r, r ≤ nl ∧ b ∈ bandsOf r ∧ bandLevel nl r = lvl ∧
      ∀ d, Encode.band53 d nl r b = Equiv.band53 d lvl b := by
  rcases h with ⟨rfl, rfl⟩ | ⟨hb, hlo, hhi⟩
  · exact ⟨0, Nat.zero_le _, by simp [bandsOf], rfl, fun _ => rfl⟩
  · let r := nl - lvl + 1
    have hr : r ≠ 0 := by dsimp [r]; omega
    have he : nl - r = lvl - 1 := by dsimp [r]; omega
    refine ⟨r, by dsimp [r]; omega, ?_, by simp [bandLevel, hr, he]; omega, ?_⟩
    · cases b <;> simp_all [bandsOf]
    · intro d
      cases b <;> cases hd : d.details[lvl - 1]? <;>
        simp_all [Encode.band53, Equiv.band53]

private theorem details_length (rect : DWT53.Rect) (nl : Nat) (g : DWT53.Grid) :
    (DWT53.sdMulti rect nl g).details.length = nl := by
  induction nl generalizing rect g with
  | zero => rfl
  | succ nl ih => simp [DWT53.sdMulti, ih]

/-- At zero reduction, agreement of the collected grids with the stored coefficients inside
each encoded band recovers the encoder's full reversible row for the selected component. -/
theorem idwt_reversibleRow {p : Params} {img : Image} {c : Nat} (hc : c < img.comps.size)
    (es : List Entry)
    (hbands : ∀ r, r ≤ p.levels → ∀ b ∈ bandsOf r, ∀ u v,
      InBand (encRect img) (bandLevel p.levels r) b u v →
      (bandGrid53 es p.levels (bandLevel p.levels r) b).get u v =
        bandSample (reversibleBand p img c r b) u v) :
    ReversibleRow img.width img.height (idwt true es (encRect img) p.levels)
      ((reversibleRows p img).getD c #[]) := by
  have hagree : BandsEq (encRect img) p.levels (dec53 es p.levels) (sampled53 p img c) := by
    intro lvl b u v hread hin
    obtain ⟨r, hr, hb, rfl, hgrid⟩ := readBand_resolution hread
    rw [QuantBlock.band53_dec53 _ _ _ _ hread, ← hgrid]
    exact (hbands r hr b hb u v hin).trans (reversibleBand_sample hc hr hb hin)
  have hget (u v : Int) (hm : (dwtRect img.width img.height).mem u v) :
      (DWT53.srMulti (dwtRect img.width img.height) p.levels (dec53 es p.levels)).get u v =
        at2 ((reversibleRows p img).getD c #[]) img.width u v := by
    refine Eq.trans ?_ (DWT53.srMulti_sdMulti p.levels _
      ⟨at2 ((reversibleRows p img).getD c #[]) img.width⟩ u v hm)
    rw [← DWTPlane.gMulti_sr1d, ← DWTPlane.gMulti_sr1d]
    exact DWTPlane.gMulti_local DWTPlane.kspec53 p.levels _ _ _
      (by simp [dec53]) (details_length _ _ _)
      (DWTPlane.bandsEq_agree _ _ _ _ hagree) u v hm
  refine ⟨rfl, rfl, Array.size_ofFn, ?_⟩
  intro j hj
  have hw : 0 < img.width := Nat.pos_of_ne_zero (by intro hz; simp [hz] at hj)
  have hx := Nat.mod_lt j hw
  have hy : j / img.width < img.height := by
    rwa [Nat.div_lt_iff_lt_mul hw, Nat.mul_comm]
  have hm : (dwtRect img.width img.height).mem (j % img.width : Nat) (j / img.width : Nat) :=
    ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr hx, Int.natCast_nonneg _, Int.ofNat_lt.mpr hy⟩
  simp only [idwt, ↓reduceIte, encRect, Header.Rect.width, Header.Rect.height, Nat.sub_zero,
    Int.natCast_zero, Int.zero_add, DWT53.memo_eq, Array.getD_eq_getD_getElem?,
    Array.getElem?_ofFn, hj, ↓reduceDIte, Option.getD_some, SpecCell.ofRev]
  refine (hget _ _ hm).trans ?_
  simp only [at2, Int.toNat_natCast, Nat.div_add_mod', Array.getD_eq_getD_getElem?]
  rfl

end JPEG2000.Spec.RoundTrip
