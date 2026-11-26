import Spec.RoundTrip.InitAdmission
import Spec.RoundTrip.PrecinctShape
import Spec.DWTPlane.Geometry

/-!
# Coverage of encoder subbands by precincts and code-blocks

Plan.md §§4, 5.3 and 7 (C10, M7). T.800 B.5–B.7. Coordinates are absolute
band coordinates. Both raster grids use half-open rectangles and the final
coefficient stride is the width of the clipped code-block.
-/

namespace JPEG2000.Spec.RoundTrip

open JPEG2000.Header JPEG2000.Tier2.Geometry
open JPEG2000.Encode (Params Image)
open JPEG2000.Spec.Tier2Equiv (bind_ok)

/-- Membership of a sample in a half-open geometric rectangle. -/
def InSampleRect (rect : Rect) (x y : Nat) : Prop :=
  rect.x0 ≤ x ∧ x < rect.x1 ∧ rect.y0 ≤ y ∧ y < rect.y1

private theorem raster {i j w h : Nat} (hi : i < w) (hj : j < h) :
    j * w + i < w * h ∧ (j * w + i) % w = i ∧ (j * w + i) / w = j := by
  have hw : 0 < w := by omega
  have hrow := Nat.mul_le_mul_right w (Nat.succ_le_of_lt hj)
  rw [Nat.succ_mul, Nat.mul_comm h w] at hrow
  refine ⟨by omega, ?_, ?_⟩
  · rw [Nat.mul_comm j w, Nat.mul_add_mod, Nat.mod_eq_of_lt hi]
  · rw [Nat.mul_comm j w, Nat.mul_add_div hw, Nat.div_eq_of_lt hi, Nat.add_zero]

/-- The local raster index, with both inverse-coordinate equations used by
the encoder's coefficient extraction. This also covers clipped edge blocks. -/
theorem sample_raster {rect : Rect} {x y : Nat} (hin : InSampleRect rect x y) :
    let n := (y - rect.y0) * rect.width + (x - rect.x0)
    n < rect.width * rect.height ∧ rect.x0 + n % rect.width = x ∧
      rect.y0 + n / rect.width = y := by
  obtain ⟨hx, hx', hy, hy'⟩ := hin
  have H := raster (show x - rect.x0 < rect.width by unfold Rect.width; omega)
    (show y - rect.y0 < rect.height by unfold Rect.height; omega)
  exact ⟨H.1, by rw [H.2.1]; omega, by rw [H.2.2]; omega⟩

private def cell (rect : Rect) (ex ey gx gy : Nat) : Rect :=
  clip rect (gx * 2^ex) (gy * 2^ey) ((gx+1) * 2^ex) ((gy+1) * 2^ey)

private theorem cell_iff (rect : Rect) (ex ey gx gy x y : Nat) :
    InSampleRect (cell rect ex ey gx gy) x y ↔
      InSampleRect rect x y ∧ x / 2^ex = gx ∧ y / 2^ey = gy := by
  rw [Nat.div_eq_iff (Nat.two_pow_pos ex), Nat.div_eq_iff (Nat.two_pow_pos ey)]
  have := Nat.two_pow_pos ex
  have := Nat.two_pow_pos ey
  simp only [InSampleRect, cell, clip, Nat.succ_mul]
  omega

private theorem precinct_cell (res : ResolutionGeom) (b : BandGeom) (px py : Nat) :
    precinctBandRect res b px py =
      cell b.rect res.bandPpx res.bandPpy (res.k0x + px) (res.k0y + py) := by
  simp only [precinctBandRect, cell, Nat.succ_mul]

private theorem div_lt_ceil {x a e : Nat} (hx : x < a) : x / 2^e < cdivPow a e := by
  have h := Nat.div_mul_le_self x (2^e)
  have hp := Nat.two_pow_pos e
  apply (Nat.le_div_iff_mul_le hp).mpr
  rw [Nat.succ_mul]
  omega

private theorem grid_offset {a z x e : Nat} (hx : a ≤ x) (hz : x < z) :
    a / 2^e + (x / 2^e - a / 2^e) = x / 2^e ∧
    x / 2^e - a / 2^e < gridCount a z e := by
  have h := Nat.div_le_div_right (c := 2^e) hx
  have := div_lt_ceil (e := e) hz
  unfold gridCount
  rw [ite_eq_right (by omega)]
  omega

private def blockCell (pb : Rect) (ex ey cw k : Nat) : CodeBlockGeom :=
  let gx := pb.x0 / 2^ex + k % cw
  let gy := pb.y0 / 2^ey + k / cw
  { index := k, gx, gy, rect := cell pb ex ey gx gy }

private theorem block_at {pb : Rect} {ex ey cw ch k : Nat} (hk : k < cw * ch) :
    (codeBlocksOf pb ex ey cw ch)[k]? = some (blockCell pb ex ey cw k) := by
  simp only [codeBlocksOf, Array.getElem?_map, List.getElem?_toArray,
    List.getElem?_range hk, Option.map_some]
  rfl

private theorem block_cover {pb : Rect} {ex ey x y : Nat} (hp : InSampleRect pb x y) :
    let cw := gridCount pb.x0 pb.x1 ex
    let ch := gridCount pb.y0 pb.y1 ey
    ∃ (k : Nat) (cb : CodeBlockGeom), (codeBlocksOf pb ex ey cw ch)[k]? = some cb ∧ InSampleRect cb.rect x y := by
  intro cw ch
  obtain ⟨hx, hi⟩ := grid_offset (e := ex) hp.1 hp.2.1
  obtain ⟨hy, hj⟩ := grid_offset (e := ey) hp.2.2.1 hp.2.2.2
  obtain ⟨hk, hmod, hdiv⟩ := raster hi hj
  refine ⟨_, _, block_at hk, (cell_iff ..).mpr ⟨hp, ?_, ?_⟩⟩
  · rw [hmod, hx]
  · rw [hdiv, hy]

-- The checked band map is pointwise deterministic on success.
private theorem map_checked {α β : Type} {f : α → Except Error β} (g : α → β)
    (hf : ∀ a v, f a = .ok v → v = g a) {xs : Array α} {ys : Array β}
    (hm : xs.mapM f = .ok ys) : ys = xs.map g := by
  have list_eq : ∀ (l : List α) (vs : List β), l.mapM f = .ok vs → vs = l.map g := by
    intro l
    induction l with
    | nil => intro vs hv; cases hv; rfl
    | cons a l ih =>
      intro vs hv
      rw [List.mapM_cons] at hv
      obtain ⟨v, ha, hv⟩ := bind_ok hv
      obtain ⟨tail, ht, hv⟩ := bind_ok hv
      cases hv
      rw [hf a v ha, ih _ ht, List.map_cons]
  rw [Array.mapM_eq_mapM_toList] at hm
  cases hl : xs.toList.mapM f with
  | error e => rw [hl] at hm; cases hm
  | ok vs =>
    rw [hl] at hm
    cases hm
    rw [list_eq _ _ hl, ← Array.toList_map, Array.toArray_toList]

private def bandAt (res : ResolutionGeom) (k : Nat) (bg : BandGeom) : PrecinctBandGeom :=
  let rect := precinctBandRect res bg (k % res.pw) (k / res.pw)
  let w := gridCount rect.x0 rect.x1 bg.cbWidthExp
  let h := gridCount rect.y0 rect.y1 bg.cbHeightExp
  let wh := if w = 0 ∨ h = 0 then (0, 0) else (w, h)
  { band := bg.band, rect, cw := wh.1, ch := wh.2,
    codeBlocks := codeBlocksOf rect bg.cbWidthExp bg.cbHeightExp wh.1 wh.2 }

private theorem precinct_map {L : Limits} {res : ResolutionGeom} {k : Nat} {pg : PrecinctGeom}
    (h : precinct L res k = .ok pg) :
    k < res.numPrecincts ∧ pg.index = k ∧ pg.bands = res.bands.map (bandAt res k) := by
  unfold precinct at h
  dsimp only at h
  split at h
  · cases h
  next valid =>
    obtain ⟨bs, hbs, h⟩ := bind_ok h
    cases h
    refine ⟨by omega, rfl, map_checked _ ?_ hbs⟩
    intro a v hv
    obtain ⟨_, _, hv⟩ := bind_ok hv
    exact Except.ok.inj hv.symm

private theorem bandAt_cover {res : ResolutionGeom} {k x y : Nat} {bg : BandGeom}
    (hin : InSampleRect (bandAt res k bg).rect x y) :
    ∃ (j : Nat) (cb : CodeBlockGeom), (bandAt res k bg).codeBlocks[j]? = some cb ∧
      InSampleRect cb.rect x y := by
  let pb := (bandAt res k bg).rect
  have hx := (grid_offset (e := bg.cbWidthExp) hin.1 hin.2.1).2
  have hy := (grid_offset (e := bg.cbHeightExp) hin.2.2.1 hin.2.2.2).2
  have hne : ¬ (gridCount pb.x0 pb.x1 bg.cbWidthExp = 0 ∨
      gridCount pb.y0 pb.y1 bg.cbHeightExp = 0) := by
    change _ < gridCount pb.x0 pb.x1 bg.cbWidthExp at hx
    change _ < gridCount pb.y0 pb.y1 bg.cbHeightExp at hy
    omega
  dsimp only [pb, bandAt] at hne
  simpa only [bandAt, ite_eq_right hne] using
    (block_cover (ex := bg.cbWidthExp) (ey := bg.cbHeightExp) hin)

private theorem bandAt_block {res : ResolutionGeom} {k j : Nat} {bg : BandGeom}
    {cb : CodeBlockGeom} (h : (bandAt res k bg).codeBlocks[j]? = some cb) :
    let pb := bandAt res k bg
    cb = blockCell pb.rect bg.cbWidthExp bg.cbHeightExp pb.cw j ∧
      Spec.Tier2WF.RectIn pb.rect cb.rect := by
  let pb := bandAt res k bg
  change (codeBlocksOf pb.rect bg.cbWidthExp bg.cbHeightExp pb.cw pb.ch)[j]? = _ at h
  have hj := (Array.getElem?_eq_some_iff.mp h).1
  simp only [codeBlocksOf, Array.size_map, List.size_toArray, List.length_range] at hj
  refine ⟨Option.some.inj (h.symm.trans (block_at hj)), ?_⟩
  apply Spec.Tier2WF.codeBlocksOf_in (ex := bg.cbWidthExp) (ey := bg.cbHeightExp)
    (cw := pb.cw) (ch := pb.ch) _ _ cb (Array.mem_iff_getElem?.mpr ⟨_, h⟩)
  all_goals dsimp only [pb, bandAt]; split <;> simp

private theorem enc_axis {w nl r o x : Nat} (hx : x < bandCoord w (bandLevel nl r) o) :
    x / 2^(if r = 0 then 15 else 14) < gridCount 0 (cdivPow w (nl-r)) 15 := by
  have upper (n : Nat) : bandCoord w n o ≤ cdivPow w n := by
    unfold bandCoord cdivPow cdiv
    apply Nat.div_le_div_right
    omega
  have hx' := Nat.lt_of_lt_of_le hx (upper _)
  by_cases hr : r = 0
  · subst r
    simp only [bandLevel, ite_true, Nat.sub_zero] at hx' ⊢
    simpa only [Nat.zero_div, Nat.sub_zero] using
      (grid_offset (e := 15) (Nat.zero_le x) hx').2
  · simp only [bandLevel, hr, ite_false, DWTPlane.cdivPow_succ] at hx'
    have h2 : 2*x < cdivPow w (nl-r) := by omega
    have H := (grid_offset (e := 15) (Nat.zero_le (2*x)) h2).2
    simp only [Nat.zero_div, Nat.sub_zero] at H
    rw [ite_eq_right hr]
    exact (show x / 2^14 = 2*x / 2^15 by omega) ▸ H

private theorem encoder_resolution {p : Params} {img : Image} {guard r : Nat} {exps : Array Nat}
    {L : Limits} {res : ResolutionGeom} (h : resolution L (encGeom p img guard exps) r = .ok res) :
    res.bands = (bandsOf r).map (bandGeom (encGeom p img guard exps) r) ∧
      res.k0x = 0 ∧ res.k0y = 0 ∧
      res.bandPpx = (if r = 0 then 15 else 14) ∧ res.bandPpy = (if r = 0 then 15 else 14) ∧
      res.pw = gridCount 0 (cdivPow img.width (p.levels - r)) 15 ∧
      res.ph = gridCount 0 (cdivPow img.height (p.levels - r)) 15 := by
  have hpp : (encParams p guard exps).precincts.getD r Marker.Precinct.default = Marker.Precinct.default := by
    simp only [encParams, Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
    split <;> rfl
  have h0 (d : Nat) : cdivPow 0 d = 0 := by
    have := Nat.two_pow_pos d
    simp [cdivPow, cdiv, Nat.div_eq_of_lt (show 2^d-1 < 2^d by omega)]
  unfold resolution at h
  dsimp only at h
  split at h
  · cases h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  cases h
  simp only [encGeom, encRect, resRect, hpp, h0, Nat.zero_div]
  exact ⟨trivial, trivial, trivial, rfl, rfl, rfl, rfl⟩

private theorem band_index {r i : Nat} {b : Band} (h : (bandsOf r)[i]? = some b) :
    i = b.index - (if r = 0 then 0 else 1) := by
  cases r <;> rcases i with _ | _ | _ | i <;>
    simp [bandsOf] at h <;> subst b <;> rfl

/-- The checked precinct, band and code-block lookups for a sample. The
orientation is the stored band label. No assumption about canonical indices
is needed when using this predicate to rule out another covering block. -/
structure BandBlockAt (L : Limits) (res : ResolutionGeom) (b : Band) (x y k bi j : Nat)
    (pg : PrecinctGeom) (pb : PrecinctBandGeom) (cb : CodeBlockGeom) : Prop where
  /-- Geometry admitted the precinct at its raster index. -/
  precinct_ok : precinct L res k = .ok pg
  /-- The selected precinct-band occupies this packet-order slot. -/
  band_at : pg.bands[bi]? = some pb
  /-- The stored orientation matches the requested band. -/
  label : pb.band = b
  /-- The block occupies this raster slot in the selected precinct-band. -/
  block_at : pb.codeBlocks[j]? = some cb
  /-- The coefficient lies in the clipped block rectangle. -/
  inside : InSampleRect cb.rect x y

private theorem lookup_band {res : ResolutionGeom} {tc : TileCompGeom} {r k bi : Nat}
    {L : Limits} {pg : PrecinctGeom} {pb : PrecinctBandGeom}
    (hres : res.bands = (bandsOf r).map (bandGeom tc r))
    (hpg : precinct L res k = .ok pg) (hpb : pg.bands[bi]? = some pb) :
    (bandsOf r)[bi]? = some pb.band ∧ pb = bandAt res k (bandGeom tc r pb.band) := by
  rw [(precinct_map hpg).2.2, hres, Array.getElem?_map, Array.getElem?_map] at hpb
  cases hb : (bandsOf r)[bi]? with
  | none => simp [hb] at hpb
  | some b =>
    simp only [hb, Option.map_some, Option.some.injEq] at hpb
    subst pb
    exact ⟨rfl, rfl⟩

/-- Every covering block has these indices. The precinct is selected by
the band-coordinate quotients and the block by its grid offsets within the
clipped precinct-band. The block record carries that same raster index. -/
theorem BandBlockAt.indices {p : Params} {img : Image} {guard r : Nat} {exps : Array Nat}
    {L M : Limits} {res : ResolutionGeom} {b : Band} {x y k bi j : Nat}
    {pg : PrecinctGeom} {pb : PrecinctBandGeom} {cb : CodeBlockGeom}
    (hr : resolution L (encGeom p img guard exps) r = .ok res)
    (a : BandBlockAt M res b x y k bi j pg pb cb) :
    let bg := bandGeom (encGeom p img guard exps) r b
    k = (y / 2^res.bandPpy) * res.pw + x / 2^res.bandPpx ∧
      bi = b.index - (if r = 0 then 0 else 1) ∧
      j = (y / 2^bg.cbHeightExp - pb.rect.y0 / 2^bg.cbHeightExp) * pb.cw +
        (x / 2^bg.cbWidthExp - pb.rect.x0 / 2^bg.cbWidthExp) ∧
      cb.index = j ∧ cb.gx = x / 2^bg.cbWidthExp ∧ cb.gy = y / 2^bg.cbHeightExp ∧
      pb.rect = precinctBandRect res bg (k % res.pw) (k / res.pw) ∧
      InSampleRect pb.rect x y ∧ (bandsOf r)[bi]? = some b ∧ res.bands[bi]? = some bg ∧
      pb.codeBlocks = codeBlocksOf pb.rect bg.cbWidthExp bg.cbHeightExp pb.cw pb.ch := by
  intro bg
  obtain ⟨hbs, h0x, h0y, _⟩ := encoder_resolution hr
  obtain ⟨hbi, he⟩ := lookup_band hbs a.precinct_ok a.band_at
  rw [a.label] at hbi he
  change pb = bandAt res k bg at he
  have hb := a.block_at
  rw [he] at hb
  obtain ⟨hcb, hrect⟩ := bandAt_block hb
  rw [← he] at hcb hrect
  have hs := a.inside
  have hp : InSampleRect pb.rect x y := by
    obtain ⟨_, _, _, _⟩ := hs
    obtain ⟨_, _, _, _⟩ := hrect
    unfold InSampleRect
    omega
  have epb : pb.rect = precinctBandRect res bg (k % res.pw) (k / res.pw) := he ▸ rfl
  have hprec := hp
  rw [epb, precinct_cell, cell_iff, h0x, h0y, Nat.zero_add, Nat.zero_add] at hprec
  rw [hcb] at hs
  obtain ⟨_, hcx, hcy⟩ := (cell_iff ..).mp hs
  have hbg : res.bands[bi]? = some bg := by rw [hbs, Array.getElem?_map, hbi]; rfl
  refine ⟨?_, band_index hbi, ?_, hcb ▸ rfl, ?_, ?_, epb, hp, hbi, hbg, he ▸ rfl⟩
  · rw [hprec.2.1, hprec.2.2, Nat.div_add_mod']
  · rw [hcx, hcy, Nat.add_sub_cancel_left, Nat.add_sub_cancel_left, Nat.div_add_mod']
  · rw [hcb]; exact hcx.symm
  · rw [hcb]; exact hcy.symm

/-- Any two geometric blocks of the same resolution and band covering the
sample have the same precinct, band slot and block slot, even when their
precincts were admitted under different limits. -/
theorem BandBlockAt.unique {p : Params} {img : Image} {guard r : Nat} {exps : Array Nat}
    {L M N : Limits} {res : ResolutionGeom} {b : Band} {x y k bi j k' bi' j' : Nat}
    {pg pg' : PrecinctGeom} {pb pb' : PrecinctBandGeom} {cb cb' : CodeBlockGeom}
    (hr : resolution L (encGeom p img guard exps) r = .ok res)
    (a : BandBlockAt M res b x y k bi j pg pb cb)
    (a' : BandBlockAt N res b x y k' bi' j' pg' pb' cb') :
    k = k' ∧ bi = bi' ∧ j = j' := by
  have ha := a.indices hr
  have ha' := a'.indices hr
  have hk := ha.1.trans ha'.1.symm
  have hi := ha.2.1.trans ha'.2.1.symm
  subst k'
  obtain ⟨_, he⟩ := lookup_band (encoder_resolution hr).1 a.precinct_ok a.band_at
  obtain ⟨_, he'⟩ := lookup_band (encoder_resolution hr).1 a'.precinct_ok a'.band_at
  rw [a.label] at he
  rw [a'.label] at he'
  obtain rfl := he.trans he'.symm
  exact ⟨rfl, hi, ha.2.2.1.trans ha'.2.2.1.symm⟩

/-- At an arbitrary in-band sample, the coordinate quotients select a valid
precinct. Looking up that precinct yields a band and code-block containing
the sample. `BandBlockAt.unique` rules out every other set of indices. -/
theorem encBandCoverage {p : Params} {img : Image} {guard r : Nat} {exps : Array Nat}
    {L : Limits} {res : ResolutionGeom} {b : Band} {x y : Nat}
    (hr : resolution L (encGeom p img guard exps) r = .ok res) (hb : b ∈ bandsOf r)
    (hin : InSampleRect (bandRect (encRect img) (bandLevel p.levels r) b) x y) :
    let k := (y / 2^res.bandPpy) * res.pw + x / 2^res.bandPpx
    k < res.numPrecincts ∧ ∀ (M : Limits) (pg : PrecinctGeom), precinct M res k = .ok pg →
      ∃ bi j pb cb, BandBlockAt M res b x y k bi j pg pb cb := by
  intro k
  obtain ⟨hbs, h0x, h0y, hex, hey, hw, hh⟩ := encoder_resolution hr
  have hx : x / 2^res.bandPpx < res.pw := by
    rw [hex, hw]; exact enc_axis hin.2.1
  have hy : y / 2^res.bandPpy < res.ph := by
    rw [hey, hh]; exact enc_axis hin.2.2.2
  obtain ⟨hk, hpx, hpy⟩ := raster hx hy
  change k % res.pw = _ at hpx
  change k / res.pw = _ at hpy
  refine ⟨hk, ?_⟩
  intro M pg hpg
  obtain ⟨bi, hbi⟩ := Array.mem_iff_getElem?.mp hb
  let bg := bandGeom (encGeom p img guard exps) r b
  let pb := bandAt res k bg
  have hpb : pg.bands[bi]? = some pb := by
    rw [(precinct_map hpg).2.2, hbs, Array.getElem?_map, Array.getElem?_map, hbi]
    rfl
  have hp : InSampleRect pb.rect x y := by
    change InSampleRect (precinctBandRect res bg (k % res.pw) (k / res.pw)) x y
    rw [precinct_cell, cell_iff, h0x, h0y, Nat.zero_add, Nat.zero_add, hpx, hpy]
    exact ⟨hin, rfl, rfl⟩
  obtain ⟨j, cb, hcb, hs⟩ := bandAt_cover hp
  exact ⟨bi, j, pb, cb, hpg, hpb, rfl, hcb, hs⟩

/-- An admitted encoder component covers every sample read at a valid band
and resolution. The witnesses use actual successful geometry calls. The
raster index recovers the original signed coordinates of the inverse DWT. -/
theorem encBandCoverage_of_headerFits {p : Params} {img : Image} {guard size c r : Nat}
    {exps : Array Nat} {L : Limits} {b : Band} {u v : Int}
    (fits : HeaderFits L p img guard exps size) (hc : c < img.comps.size) (hr : r ≤ p.levels)
    (hb : b ∈ bandsOf r) (hin : Equiv.InBand (encRect img) (bandLevel p.levels r) b u v) :
    ∃ res k bi j pg pb cb, resolution L (encGeom p img guard exps) r = .ok res ∧
      k < res.numPrecincts ∧ BandBlockAt L res b u.toNat v.toNat k bi j pg pb cb ∧
      ∃ n < cb.rect.width * cb.rect.height, Equiv.posU cb.rect n = u ∧ Equiv.posV cb.rect n = v := by
  let g := encLayout p img guard exps
  have hcomp := encLayout_comp p img guard exps c hc
  have hci : c < g.numComps := (encLayout_coding p img guard exps).1 ▸ hc
  have hri : r ≤ g.levels c := by
    unfold JPEG2000.Progression.Layout.levels
    rw [hcomp]
    exact hr
  obtain ⟨precs, base, spans, init⟩ := initPrecincts_of_headerFits fits
  obtain ⟨res, hres, _, _, precAt⟩ := initPrecincts_geometry init hci hri
  rw [hcomp] at hres
  obtain ⟨hx, hx', hy, hy'⟩ := hin
  have hs : InSampleRect (bandRect (encRect img) (bandLevel p.levels r) b) u.toNat v.toNat := by
    unfold InSampleRect; omega
  obtain ⟨hk, atPrec⟩ := encBandCoverage hres hb hs
  obtain ⟨pg, _, hpg, _⟩ := precAt _ hk
  obtain ⟨bi, j, pb, cb, ha⟩ := atPrec L pg hpg
  obtain ⟨hn, hmod, hdiv⟩ := sample_raster ha.inside
  refine ⟨res, _, bi, j, pg, pb, cb, hres, hk, ha, _, hn, ?_, ?_⟩
  · unfold Equiv.posU; omega
  · unfold Equiv.posV; omega

/-- The encoder reads the band value at the covered sample when it extracts
this block coefficient, including the shortened stride on the right edge. -/
theorem blockCoeffs_sample {cb : Rect} (d : Encode.BandData) {x y : Nat}
    (hin : InSampleRect cb x y) :
    (Encode.blockCoeffs d cb)[(y - cb.y0) * cb.width + (x - cb.x0)]? =
      some (d.vals.getD ((y - d.rect.y0) * d.rect.width + (x - d.rect.x0)) 0) := by
  obtain ⟨hn, hx, hy⟩ := sample_raster hin
  simp only [Encode.blockCoeffs, Array.getElem?_ofFn, hn, dite_true, hx, hy]

end JPEG2000.Spec.RoundTrip
