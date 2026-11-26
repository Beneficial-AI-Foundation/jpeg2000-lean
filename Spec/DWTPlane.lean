import Spec.DWTPlane.Out
import Spec.DWTPlane.Local
import Spec.DWTPlane.Err97

/-!
# The 2-D inverse DWT plane loops = spec (5/3) and within C8 (9/7)

Plan.md §4 (C6, C8, C9), §5.1 (one equivalence theorem per stage), §5.2 "DWT", §5.4 (fixed
width, checked slow path); T.800 Annex F.3 (`IDWT`, `2D_SR`, `2D_INTERLEAVE`, `HOR_SR`,
`VER_SR`, `1D_SR`), Annex B.5 (B-14, B-15). Task 7.1d.

Discharges two stage hypotheses of `Spec.Equiv.c9_of_stages` (task 7.1a):

* `dwt53PlaneEquiv : Spec.Equiv.DWT53PlaneEquiv` — `DWT53.idwt53` keeps the size, and on a
  plane whose bands (read by `toDec`) agree with a decomposition `D` on every band position
  the transform reads (`BandsEq`), every output cell is `clamp32` of `Spec.DWT53.srMulti D`.
  Fast path: `idwt53Fast_spec` (the level loop `levelsG_spec` with the 5/3 kernel `kspec53`
  computes `srMulti` of `toDec` exactly); slow path: `ofGrid_spec` (the spec itself,
  saturated); both: band locality of `srMulti` (`gMulti_local`, `bandsEq_agree`, from the
  B-15 band rectangles of `Spec.DWTPlane.Geometry`).
* `dwt97PlaneErr : Spec.Equiv.DWT97PlaneErr` — see the 9/7 section.

## Band positions read by a multi-level inverse transform

Level `i + 1` of `gMulti` on rectangle `r` interleaves its bands into `R = rhalf r i`: the HL
band is read at `u ∈ Hx R` (`⌊u0/2⌋ ≤ u < ⌊u1/2⌋`, odd columns), `v ∈ Ly R` (`⌈v0/2⌉ ≤ v <
⌈v1/2⌉`, even rows), etc.; the LL band at `rhalf r n`. These are exactly the B-15 rectangles
`bandRect` (`bandsEq_agree`).
-/

namespace JPEG2000.Spec.DWTPlane

open JPEG2000 JPEG2000.Bytes JPEG2000.Tier2.Geometry
open JPEG2000.DWT53 (Buf batch halfN halfN_le cellInt toDec specRect sat32 ofGrid)
open JPEG2000.Spec.DWT53 (Grid Dec interleave)
open JPEG2000.Spec.Equiv (band53 InBand ReadBand BandsEq posU posV)

/-! ## The fast path -/

/-- The level loop of a fast path started on the plane `p` itself: the result keeps the
width, `okP` holds of every pass, and the corner holds `gMulti op` of `toDec p`. -/
theorem fast_core {K : Kern} {op : Int → Int → (Int → Int) → Int → Int}
    {okP : Int → Int → (Int → Int) → Prop} (hK : KSpec K op okP) (p : Plane) (tc : Header.Rect)
    (nl : Nat) (hw : p.width = tc.x1 - tc.x0) {T : Nat} (tmp : Buf T)
    (hN : p.width * p.height = p.width * (p.width * p.height / p.width))
    (hpw : tc.x1 - tc.x0 ≤ p.width) (hph : tc.y1 - tc.y0 ≤ p.width * p.height / p.width)
    (hT : batch * (tc.y1 - tc.y0) ≤ T) (hT2 : tc.x1 - tc.x0 ≤ T)
    (hok : (levelsG K tc p.width hN hpw hph hT hT2 nl ⟨p, rfl⟩ tmp true).2 = true) :
    (levelsG K tc p.width hN hpw hph hT hT2 nl ⟨p, rfl⟩ tmp true).1.1.width = p.width ∧
    gOk op okP (specRect tc) nl (toDec p tc nl) ∧
    ∀ yy xx, xx < tc.x1 - tc.x0 → yy < tc.y1 - tc.y0 →
      rd (levelsG K tc p.width hN hpw hph hT hT2 nl ⟨p, rfl⟩ tmp true).1 (yy * p.width + xx) =
        (gMulti op (specRect tc) nl (toDec p tc nl)).get (tc.x0 + xx) (tc.y0 + yy) := by
  have hwid := levelsG_width K tc p.width hN hpw hph hT hT2 nl ⟨p, rfl⟩ tmp true
  have hle := halfN_le tc nl
  have := levelsG_spec hK tc p.width hN hpw hph hT hT2 p nl ⟨p, rfl⟩ tmp true
    ⟨fun u v => cellInt p (u - ((halfN tc nl).x0 : Int)) (v - ((halfN tc nl).y0 : Int))⟩
    (by
      intro yy xx hxx hyy
      dsimp only
      rw [show ((halfN tc nl).x0 : Int) + xx - (halfN tc nl).x0 = xx by omega,
        show ((halfN tc nl).y0 : Int) + yy - (halfN tc nl).y0 = yy by omega]
      exact (cellInt_rd p xx yy (by omega)).symm)
    (fun yy xx hxx _ => (cellInt_rd p xx yy hxx).symm) hok
  rw [toDec_eq]
  exact ⟨hwid, this⟩

/-- `p.width * p.height = p.width * (p.width * p.height / p.width)` for `p.width > 0`. -/
private theorem area_div (w h : Nat) (hw : 0 < w) : w * h / w = h := by
  rw [Nat.mul_div_cancel_left _ hw]

/-- **Fast 5/3 path = spec**: when `idwt53Fast` succeeds, the result has the plane's size
and every cell is `Spec.DWT53.srMulti` of `toDec`. -/
theorem idwt53Fast_spec (p : Plane) (tc : Header.Rect) (nl : Nat) (q : Plane)
    (h : DWT53.idwt53Fast p tc nl = some q) :
    q.width = p.width ∧ q.height = p.height ∧ ∀ j, j < p.width * p.height →
      (q.get? j).map Int32.toInt = some ((Spec.DWT53.srMulti (specRect tc) nl (toDec p tc nl)).get
        (tc.x0 + (j % p.width : Nat)) (tc.y0 + (j / p.width : Nat))) := by
  unfold DWT53.idwt53Fast at h
  split at h
  · rename_i hw
    split at h
    · rename_i hz
      cases h
      refine ⟨rfl, rfl, fun j hj => ?_⟩
      rcases hz with hz | hz <;> rw [hz] at hj <;> simp at hj
    · rename_i hz
      dsimp only at h
      split at h
      · rename_i hok
        cases h
        rw [levels53_eq] at hok ⊢
        obtain ⟨c1, -, c3⟩ := fast_core kspec53 p tc nl hw.1 _ _ _ _ _ _ hok
        generalize (levelsG _ tc p.width _ _ _ _ _ nl ⟨p, rfl⟩ _ true).1 = P at c1 c3
        have hW : 0 < p.width := by omega
        refine ⟨c1, ?_, fun j hj => ?_⟩
        · have := P.2
          rw [c1] at this
          exact Nat.eq_of_mul_eq_mul_left hW this
        · rw [get?_rd P j hj]
          have hjd := Nat.div_add_mod j p.width
          have hjy : j / p.width < p.height := by
            rw [Nat.div_lt_iff_lt_mul hW, Nat.mul_comm]; exact hj
          have := c3 (j / p.width) (j % p.width) (by rw [← hw.1]; exact Nat.mod_lt _ hW)
            (by rw [← hw.2]; exact hjy)
          rw [show j / p.width * p.width + j % p.width = j by rw [Nat.mul_comm]; exact hjd] at this
          rw [this, gMulti_sr1d]
      · cases h
  · cases h

/-! ## Theorem: the 5/3 plane transform -/

/-- `clamp32` is the identity on `Int32` values. -/
theorem clamp32_int32 (v : Int32) : MCT.clamp32 v.toInt = v.toInt := by
  have h1 := v.le_toInt; have h2 := v.toInt_lt
  unfold MCT.clamp32
  apply Spec.MCT.clamp_of_mem <;> omega

private theorem raster_mem (rect : Header.Rect) (j : Nat) (hj : j < rect.width * rect.height) :
    (specRect rect).mem (posU rect j) (posV rect j) := by
  simp only [Header.Rect.width, Header.Rect.height] at hj
  have hW : 0 < rect.x1 - rect.x0 := Nat.pos_of_ne_zero (by intro h0; rw [h0] at hj; simp at hj)
  have h1 := Nat.mod_lt j hW
  have h2 : j / (rect.x1 - rect.x0) < rect.y1 - rect.y0 := by
    rw [Nat.div_lt_iff_lt_mul hW, Nat.mul_comm]; exact hj
  simp only [specRect, Spec.DWT53.Rect.mem, posU, posV, Header.Rect.width]
  generalize j % (rect.x1 - rect.x0) = a at h1 ⊢
  generalize j / (rect.x1 - rect.x0) = b at h2 ⊢
  omega

private theorem srMulti_bandsEq (p : Plane) (rect : Header.Rect) (nl : Nat) (D : Dec)
    (hD : D.details.length = nl) (hb : BandsEq rect nl (toDec p rect nl) D)
    (u v : Int) (hm : (specRect rect).mem u v) :
    (Spec.DWT53.srMulti (specRect rect) nl (toDec p rect nl)).get u v =
      (Spec.DWT53.srMulti (specRect rect) nl D).get u v := by
  rw [← gMulti_sr1d, ← gMulti_sr1d]
  exact gMulti_local kspec53 nl _ _ _ (by simp [toDec]) hD (bandsEq_agree rect nl _ _ hb) u v hm

/-- Each cell of a successful checked 5/3 reconstruction equals the exact Annex F
sample for any decomposition agreeing on its B-15 bands. These values can feed RCT. -/
theorem idwt53Fast_bandsEq (p : Plane) (rect : Header.Rect) (nl : Nat) (D : Dec) (q : Plane)
    (hw : p.width = rect.width) (hh : p.height = rect.height) (hD : D.details.length = nl)
    (hf : DWT53.idwt53Fast p rect nl = some q) :
    q.width = rect.width ∧ q.height = rect.height ∧
    (BandsEq rect nl (toDec p rect nl) D → ∀ j, j < rect.width * rect.height →
      ∃ v, q.get? j = some v ∧ v.toInt =
        (Spec.DWT53.srMulti (specRect rect) nl D).get (posU rect j) (posV rect j)) := by
  obtain ⟨qw, qh, cells⟩ := idwt53Fast_spec p rect nl q hf
  refine ⟨qw.trans hw, qh.trans hh, fun hb j hj => ?_⟩
  have lookup := cells j (by rw [hw, hh]; exact hj)
  rw [hw] at lookup
  change (q.get? j).map Int32.toInt = some
    ((Spec.DWT53.srMulti (specRect rect) nl (toDec p rect nl)).get (posU rect j) (posV rect j)) at lookup
  rw [srMulti_bandsEq p rect nl D hD hb _ _ (raster_mem rect j hj)] at lookup
  simpa only [Option.map_eq_some_iff] using lookup

/-- **Stage hypothesis `DWT53PlaneEquiv` of C9, proved** (F.3.1, B-15): `DWT53.idwt53` keeps
the rectangle's size, and when the bands it reads agree with a decomposition `D` on the
B-15 band positions, every output cell is `clamp32` of `Spec.DWT53.srMulti D` (fast path:
exact and in range; slow path: the spec saturated). -/
theorem dwt53PlaneEquiv : Spec.Equiv.DWT53PlaneEquiv := by
  intro p rect nl D q hw hh hD hq
  unfold DWT53.idwt53 at hq
  rw [if_t ⟨hw, hh⟩] at hq
  cases hf : DWT53.idwt53Fast p rect nl with
  | some q' =>
    rw [hf] at hq
    cases hq
    obtain ⟨qw, qh, exactCell⟩ := idwt53Fast_bandsEq p rect nl D q hw hh hD hf
    refine ⟨qw, qh, fun hb j hj => ?_⟩
    obtain ⟨v, hv, hval⟩ := exactCell hb j hj
    rw [hv, Option.map_some, ← hval, clamp32_int32]
  | none =>
    rw [hf] at hq
    cases hq
    obtain ⟨c1, c2, c3⟩ := ofGrid_spec (Spec.DWT53.srMulti (specRect rect) nl (toDec p rect nl))
      rect.x0 rect.y0 p.width p.height
    refine ⟨by rw [DWT53.idwt53Spec, c1, hw], by rw [DWT53.idwt53Spec, c2, hh], fun hb j hj => ?_⟩
    have hj' : j < p.width * p.height := by rw [hw, hh]; exact hj
    simp only [DWT53.idwt53Spec]
    rw [c3 j hj', hw]
    simp only [Option.map_some, sat32_clamp]
    congr 2
    exact srMulti_bandsEq p rect nl D hD hb _ _ (raster_mem rect j hj)

/-! ## Theorem: the 9/7 plane transform -/

open JPEG2000.Spec.Equiv (band97 BandsClose clampR)
open JPEG2000.Spec.DWT97 (abs_le_iff abs_add_le)

/-- `BandsClose` (the band positions of B-15, fixed point with `F` fractional bits) gives
`DecCloseR` between the cells read as rationals and `2^F · D`. -/
theorem bandsClose_agree (rect : Header.Rect) (nl F : Nat) (ε : Rat) (d1 : Dec)
    (d2 : Spec.DWT97.Dec) (h : BandsClose ε F rect nl d1 d2) :
    DecCloseR ε (specRect rect) nl (DWT97.castDec d1) (d2.smul ((2 ^ F : Nat) : Rat)) := by
  refine ⟨fun u v hm => ?_, fun i b1 b2 hi h1 h2 => ?_⟩
  · have := h nl .LL u v (.inl ⟨rfl, rfl⟩) (by
      rw [← specRect_halfN] at hm
      obtain ⟨c1, c2, c3, c4⟩ := halfN_coords rect nl
      simp only [specRect, Spec.DWT53.Rect.mem, c1, c2, c3, c4] at hm
      simp only [InBand, bandRect, Band.xob, Band.yob, bandCoord_low]
      omega)
    simpa [band53, band97, DWT97.castDec, DWT97.castG, Spec.DWT97.Dec.smul, Spec.DWT97.Grid.smul]
      using this
  · have hb : ∀ b, b ≠ .LL → ReadBand nl (i + 1) b := fun b hb => .inr ⟨hb, by omega, by omega⟩
    simp only [DWT97.castDec, List.getElem?_map, Option.map_eq_some_iff] at h1
    obtain ⟨t1, ht1, rfl⟩ := h1
    simp only [Spec.DWT97.Dec.smul, List.getElem?_map, Option.map_eq_some_iff] at h2
    obtain ⟨t2, ht2, rfl⟩ := h2
    obtain ⟨c1, c2, c3, c4⟩ := halfN_coords rect i
    have hR : rhalf (specRect rect) i = specRect (halfN rect i) := (specRect_halfN rect i).symm
    rw [hR]
    simp only [Hx, Lx, Hy, Ly, specRect, c1, c2, c3, c4]
    refine ⟨fun u v hu hv => ?_, fun u v hu hv => ?_, fun u v hu hv => ?_⟩
    · have := h (i + 1) .HL u v (hb _ (by decide)) (by
        simp only [InBand, bandRect, Band.xob, Band.yob, bandCoord_high, bandCoord_low,
          cdivPow_succ]
        omega)
      simpa [band53, band97, ht1, ht2, DWT97.castG, Spec.DWT97.Grid.smul] using this
    · have := h (i + 1) .LH u v (hb _ (by decide)) (by
        simp only [InBand, bandRect, Band.xob, Band.yob, bandCoord_high, bandCoord_low,
          cdivPow_succ]
        omega)
      simpa [band53, band97, ht1, ht2, DWT97.castG, Spec.DWT97.Grid.smul] using this
    · have := h (i + 1) .HH u v (hb _ (by decide)) (by
        simp only [InBand, bandRect, Band.xob, Band.yob, bandCoord_high]
        omega)
      simpa [band53, band97, ht1, ht2, DWT97.castG, Spec.DWT97.Grid.smul] using this

/-- **Fast 9/7 path = fixed-point model**: when `idwt97Fast` succeeds, the result has the
plane's size, every cell is the model `qsrMulti` of `toDec`, and no pass of the model overflows
(`OkMulti`, the hypothesis of C8). -/
theorem idwt97Fast_spec (p : Plane) (tc : Header.Rect) (nl : Nat) (q : Plane)
    (h : DWT97.idwt97Fast p tc nl = some q) :
    q.width = p.width ∧ q.height = p.height ∧
    (0 < p.width * p.height → DWT97.OkMulti (specRect tc) nl (toDec p tc nl)) ∧
    ∀ j, j < p.width * p.height →
      (q.get? j).map Int32.toInt = some ((DWT97.qsrMulti (specRect tc) nl (toDec p tc nl)).get
        (tc.x0 + (j % p.width : Nat)) (tc.y0 + (j / p.width : Nat))) := by
  unfold DWT97.idwt97Fast at h
  split at h
  · rename_i hw
    split at h
    · rename_i hz
      cases h
      refine ⟨rfl, rfl, fun hpos => ?_, fun j hj => ?_⟩
      · rcases hz with hz | hz <;> rw [hz] at hpos <;> simp at hpos
      · rcases hz with hz | hz <;> rw [hz] at hj <;> simp at hj
    · rename_i hz
      dsimp only at h
      split at h
      · rename_i hok
        cases h
        rw [levels97_eq] at hok ⊢
        obtain ⟨c1, c2, c3⟩ := fast_core kspec97 p tc nl hw.1 _ _ _ _ _ _ hok
        generalize (levelsG _ tc p.width _ _ _ _ _ nl ⟨p, rfl⟩ _ true).1 = P at c1 c3
        have hW : 0 < p.width := by omega
        refine ⟨c1, ?_, fun _ => gOk_okMulti _ _ _ c2, fun j hj => ?_⟩
        · have := P.2
          rw [c1] at this
          exact Nat.eq_of_mul_eq_mul_left hW this
        · rw [get?_rd P j hj]
          have hjd := Nat.div_add_mod j p.width
          have hjy : j / p.width < p.height := by
            rw [Nat.div_lt_iff_lt_mul hW, Nat.mul_comm]; exact hj
          have := c3 (j / p.width) (j % p.width) (by rw [← hw.1]; exact Nat.mod_lt _ hW)
            (by rw [← hw.2]; exact hjy)
          rw [show j / p.width * p.width + j % p.width = j by rw [Nat.mul_comm]; exact hjd] at this
          rw [this, gMulti_qsr1d]
      · cases h
  · cases h

/-- `clampR` of an integer is its `Int32` clamp. -/
theorem clampR_int (z : Int) : clampR (z : Rat) = ((MCT.clamp32 z : Int) : Rat) := by
  have e1 : ((-2147483648 : Int) : Rat) = -2147483648 := by rfl
  have e2 : ((2147483647 : Int) : Rat) = 2147483647 := by rfl
  unfold clampR MCT.clamp32 Spec.MCT.clamp
  by_cases h1 : z < -2147483648
  · have : (z : Rat) < -2147483648 := by rw [← e1]; exact Rat.intCast_lt_intCast.mpr h1
    rw [if_t this, if_t h1, e1]
  · have : ¬ (z : Rat) < -2147483648 := fun h => h1 (Rat.intCast_lt_intCast.mp (by rw [e1]; exact h))
    rw [if_f this, if_f h1]
    by_cases h2 : 2147483647 < z
    · have : (2147483647 : Rat) < z := by rw [← e2]; exact Rat.intCast_lt_intCast.mpr h2
      rw [if_t this, if_t h2, e2]
    · have : ¬ (2147483647 : Rat) < z := fun h => h2 (Rat.intCast_lt_intCast.mp (by rw [e2]; exact h))
      rw [if_f this, if_f h2]

/-- `clampR` is 1-Lipschitz. -/
theorem clampR_lip (a b : Rat) : (clampR a - clampR b).abs ≤ (a - b).abs := by
  have h := abs_le_iff.mp (Rat.le_refl (a := (a - b).abs))
  apply abs_le_iff.mpr
  unfold clampR
  split <;> split <;> (try split) <;> (try split) <;> constructor <;> grind

/-- An `Int32` value is at least as close to `clampR x` as to `x`. -/
theorem clampR_int32 (v : Int32) (x : Rat) : ((v.toInt : Rat) - clampR x).abs ≤ ((v.toInt : Rat) - x).abs := by
  have e : clampR (v.toInt : Rat) = (v.toInt : Rat) := by
    rw [clampR_int]
    have h1 := v.le_toInt; have h2 := v.toInt_lt
    unfold MCT.clamp32
    rw [Spec.MCT.clamp_of_mem _ _ _ (by omega) (by omega)]
  have := clampR_lip (v.toInt : Rat) x
  rwa [e] at this

/-- `roundRat x` is within `1/2` of `x`. -/
theorem roundRat_err (x : Rat) : ((DWT97.roundRat x : Rat) - x).abs ≤ 1 / 2 := by
  have a := Rat.floor_le (x + 1 / 2)
  have b := Rat.lt_floor_add_one (x + 1 / 2)
  unfold DWT97.roundRat
  apply abs_le_iff.mpr
  push_cast at b
  constructor <;> grind

/-- A successful checked 9/7 pass is within C8's fixed-point error of the exact
Annex F sample, including when that rational sample lies outside the Int32 range.
The band error is measured at the B-15 coordinates of the actual coefficient plane. -/
theorem idwt97Fast_err (p : Plane) (rect : Header.Rect) (nl F : Nat) (D : Spec.DWT97.Dec)
    (ε : Rat) (q : Plane) (hw : p.width = rect.width) (hh : p.height = rect.height)
    (hD : D.details.length = nl) (hf : DWT97.idwt97Fast p rect nl = some q) :
    q.width = rect.width ∧ q.height = rect.height ∧
    (BandsClose ε F rect nl (toDec p rect nl) D → ∀ j, j < rect.width * rect.height →
      ∃ v, q.get? j = some v ∧
        ((v.toInt : Rat) - ((2 ^ F : Nat) : Rat) *
          (Spec.DWT97.srMulti (specRect rect) nl D).get (posU rect j) (posV rect j)).abs ≤
          DWT97.En nl ε) := by
  obtain ⟨qw, qh, noOverflow, cells⟩ := idwt97Fast_spec p rect nl q hf
  refine ⟨qw.trans hw, qh.trans hh, fun hb j hj => ?_⟩
  have hj' : j < p.width * p.height := by rw [hw, hh]; exact hj
  have hok := noOverflow (by omega)
  have lookup := cells j hj'
  rw [hw] at lookup
  obtain ⟨v, hv1, hv2⟩ : ∃ v, q.get? j = some v ∧ v.toInt =
      (DWT97.qsrMulti (specRect rect) nl (toDec p rect nl)).get (posU rect j) (posV rect j) := by
    simpa only [Option.map_eq_some_iff, posU, posV] using lookup
  refine ⟨v, hv1, ?_⟩
  have herr := qsrMulti_err_loc nl (specRect rect) (toDec p rect nl) (D.smul ((2 ^ F : Nat) : Rat)) ε
    (by simp [toDec]) (by simp [Spec.DWT97.Dec.smul, hD]) (bandsClose_agree rect nl F ε _ _ hb) hok _ _ (raster_mem rect j hj)
  rw [Spec.DWT97.srMulti_smul, ← hv2] at herr
  exact herr

/-- **Stage hypothesis `DWT97PlaneErr` of C9, proved** (F.3.1, C8, B-15): `DWT97.idwt97` keeps
the rectangle's size, and when its fixed-point bands are within `ε` ulps of `2^F · D` on the
B-15 band positions, every output cell is within `En nl ε + 1/2` ulps of
`clampR (2^F · Spec.DWT97.srMulti D)` (fast path: the model `qsrMulti`, within `En nl ε` by
`qsrMulti_err_loc`; slow path: the exact transform of the cells, within `En nl ε` by
`srMulti_lip`, rounded (`1/2`) and saturated (`clampR` is 1-Lipschitz)). -/
theorem dwt97PlaneErr : Spec.Equiv.DWT97PlaneErr := by
  intro p rect nl F D ε q hw hh hD hq
  unfold DWT97.idwt97 at hq
  rw [if_t ⟨hw, hh⟩] at hq
  have hlenD : (D.smul ((2 ^ F : Nat) : Rat)).details.length = nl := by
    simp [Spec.DWT97.Dec.smul, hD]
  have hlenT : (toDec p rect nl).details.length = nl := by simp [toDec]
  have hX : ∀ j, (Spec.DWT97.srMulti (specRect rect) nl (D.smul ((2 ^ F : Nat) : Rat))).get
      (posU rect j) (posV rect j) = ((2 ^ F : Nat) : Rat) *
        (Spec.DWT97.srMulti (specRect rect) nl D).get (posU rect j) (posV rect j) := by
    intro j; rw [Spec.DWT97.srMulti_smul]; rfl
  have hEn := le_En' nl ε
  cases hf : DWT97.idwt97Fast p rect nl with
  | some q' =>
    rw [hf] at hq
    cases hq
    obtain ⟨qw, qh, measured⟩ := idwt97Fast_err p rect nl F D ε q hw hh hD hf
    refine ⟨qw, qh, fun hb j hj => ?_⟩
    obtain ⟨v, hv, herr⟩ := measured hb j hj
    refine ⟨v, hv, ?_⟩
    have := clampR_int32 v (((2 ^ F : Nat) : Rat) *
      (Spec.DWT97.srMulti (specRect rect) nl D).get (posU rect j) (posV rect j))
    generalize (Spec.DWT97.srMulti (specRect rect) nl D).get (posU rect j) (posV rect j) = y at *
    generalize ((v.toInt : Int) : Rat) = a at *
    generalize clampR (((2 ^ F : Nat) : Rat) * y) = c at *
    grind
  | none =>
    rw [hf] at hq
    cases hq
    obtain ⟨c1, c2, c3⟩ := ofGrid_spec ⟨fun u v => DWT97.roundRat ((Spec.DWT97.memo (specRect rect)
      (Spec.DWT97.srMulti (specRect rect) nl (DWT97.castDec (toDec p rect nl)))).get u v)⟩
      rect.x0 rect.y0 p.width p.height
    refine ⟨by rw [DWT97.idwt97Spec, c1, hw], by rw [DWT97.idwt97Spec, c2, hh], fun hb j hj => ?_⟩
    have hj' : j < p.width * p.height := by rw [hw, hh]; exact hj
    refine ⟨_, by simp only [DWT97.idwt97Spec]; rw [c3 j hj', hw], ?_⟩
    rw [sat32_clamp, ← clampR_int, Spec.DWT97.memo_eq]
    have hl := srMulti_lip nl (specRect rect) (DWT97.castDec (toDec p rect nl))
      (D.smul ((2 ^ F : Nat) : Rat)) ε (by simp [DWT97.castDec, hlenT]) hlenD
      (bandsClose_agree rect nl F ε _ _ hb) _ _ (raster_mem rect j hj)
    rw [hX] at hl
    have hr := roundRat_err ((Spec.DWT97.srMulti (specRect rect) nl
      (DWT97.castDec (toDec p rect nl))).get (posU rect j) (posV rect j))
    have hc := clampR_lip ((DWT97.roundRat ((Spec.DWT97.srMulti (specRect rect) nl
      (DWT97.castDec (toDec p rect nl))).get (posU rect j) (posV rect j)) : Int) : Rat)
      (((2 ^ F : Nat) : Rat) * (Spec.DWT97.srMulti (specRect rect) nl D).get (posU rect j) (posV rect j))
    simp only [posU, posV] at hl hr hc ⊢
    generalize (Spec.DWT97.srMulti (specRect rect) nl (DWT97.castDec (toDec p rect nl))).get _ _ = Y at *
    generalize ((DWT97.roundRat Y : Int) : Rat) = R at *
    generalize ((2 ^ F : Nat) : Rat) * (Spec.DWT97.srMulti (specRect rect) nl D).get _ _ = X at *
    have t := abs_add_le (R - Y) (Y - X)
    rw [show R - Y + (Y - X) = R - X by grind] at t
    generalize clampR R - clampR X = cc at *
    grind

end JPEG2000.Spec.DWTPlane
