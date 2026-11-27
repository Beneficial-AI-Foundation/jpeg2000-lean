import JPEG2000.WideQuant
import Spec.Tier1Wide.Plain
import Spec.QuantBlock.Step
import Spec.WideOutput

/-!
# Wide Mallat coefficient values and placement

Plan.md §§4, 5.1, 5.4, 7; T.800 B-14, B-15, Annex E.1.1.2 and Annex H.
The reference values use the Annex D coefficient before conversion to the wide raster.
The reference addresses use band coordinates on the requested component grid.
-/

namespace JPEG2000.Spec.WideQuant

open JPEG2000.WideQuant Tier1Wide
open JPEG2000.Tier2.Geometry
open Header (Rect)
open Spec.Quant (BandQuant)
open Spec.Tier1 (Coeff)

/-- Round the magnitude of the signed rational reconstruction, with half units
rounded away from zero in either direction. -/
def roundSigned (negative : Bool) (x : Rat) : Int :=
  if negative then -Decode.roundHalf (-x) else Decode.roundHalf x

/-- On an ordered rectangle the checked allocator succeeds exactly up to the
inclusive work limit, and every coefficient of an absent block starts at zero. -/
theorem zeroChecked_eq (L : Limits) (rect : Rect)
    (hx : rect.x0 ≤ rect.x1) (hy : rect.y0 ≤ rect.y1) :
    zeroChecked L rect = .ok ⟨rect, Vector.replicate (rectArea rect) 0⟩ ↔
      rectArea rect ≤ L.maxWorkSamples := by
  by_cases hw : rectArea rect ≤ L.maxWorkSamples <;>
    simp [zeroChecked, Limits.check, Limits.checkLe, Limits.bound, hw, Nat.not_lt.mpr hx,
      Nat.not_lt.mpr hy, bind, Except.bind, pure, Except.pure]

/-- Annex H agrees on both the quantisation index and the last decoded plane,
including shifts greater than a machine word. -/
theorem unshift_eq (s : Nat) (c : Coeff) :
    unshift s (cellOf c) = ((Quant.roiUnshift s c).mag, (Quant.roiUnshift s c).lsbPlane) := by
  unfold unshift Quant.roiUnshift
  simp only [cellOf, Nat.shiftRight_eq_div_pow]
  split <;> rfl

/-- Neither transform adds a midpoint to an insignificant or zero coefficient. -/
theorem prepare_zero (q : BandQuant) (F : Nat) (c : JPEG2000.Tier1.WidePlain.Cell)
    (h : c.sig = false ∨ c.mag = 0) : prepare q F c = 0 := by
  rcases h with hs | hm
  · simp [prepare, hs]
  · have hpos := Nat.two_pow_pos q.roiShift
    simp [prepare, unshift, hm, Nat.not_le.mpr hpos]

private theorem kernel_form (q : BandQuant) (F : Nat) (c : Coeff)
    (hc : c.sig = false → c.mag = 0) :
    let u := Quant.roiUnshift q.roiShift c
    prepare q F (cellOf c) = if u.mag = 0 then 0 else
      if u.sign then -(magnitude q F u.mag u.lsbPlane) else magnitude q F u.mag u.lsbPlane := by
  dsimp only
  have sign : (Quant.roiUnshift q.roiShift c).sign = c.sign := by
    unfold Quant.roiUnshift; split <;> rfl
  rw [sign]
  cases hs : c.sig with
  | false =>
    have hm := hc hs
    have hb : c.mag < 2 ^ q.roiShift := hm ▸ Nat.two_pow_pos _
    rw [prepare_zero _ _ _ (.inl hs), Quant.roiUnshift_background _ _ hb, ite_eq_left hm]
  | true =>
    simp only [prepare, show (cellOf c).sig = true from hs, Bool.not_true, Bool.false_eq_true,
      ite_false, unshift_eq]
    rfl

/-- Exact reversible reconstruction on the real Annex D fields. The single
significance invariant is the zero-magnitude clause of `Tier1Equiv.Base`. -/
theorem reversible_eq (q : BandQuant) (F : Nat) (c : Coeff) (hr : q.reversible = true)
    (hc : c.sig = false → c.mag = 0) :
    prepare q F (cellOf c) = Quant.dequantRev q.roiShift c := by
  rw [kernel_form q F c hc]
  simp [Quant.dequantRev, Quant.reconstructRev, magnitude, hr]

/-- Plane zero returns the exact signed ROI-unshifted index. A truncated last
plane gives the rational E-6 midpoint with unit step size. -/
theorem reversible_midpoint (q : BandQuant) (F : Nat) (c : Coeff) (hr : q.reversible = true)
    (hc : c.sig = false → c.mag = 0) :
    let u := Quant.roiUnshift q.roiShift c
    (u.lsbPlane = 0 → prepare q F (cellOf c) = u.value) ∧
    (1 ≤ u.lsbPlane → (prepare q F (cellOf c) : Rat) = Quant.reconstructIrrev 1 u) := by
  rw [reversible_eq q F c hr hc]
  exact ⟨Quant.reconstructRev_full _, Quant.reconstructRev_eq_irrev _⟩

private theorem magnitude_irrev (q : BandQuant) (F m l : Nat) (hr : q.reversible = false) :
    magnitude q F m l = Decode.roundHalf
      (((m : Rat) + ((2 ^ l : Nat) : Rat) / 2) * q.delta * ((2 ^ F : Nat) : Rat)) := by
  let n := (2 * m + 2 ^ l) * (2048 + q.mantissa) * 2 ^ (q.range + F)
  have h : magnitude q F m l = MCT.roundFix (q.exponent + 12) (n : Int) := by
    simp [magnitude, hr, MCT.roundFix, n, Nat.mul_assoc]
  rw [h, WideOutput.roundFix_eq_roundHalf, Quant.BandQuant.delta, JPEG2000.Quant.scaled_value]
  have he : (2 : Int) ^ (q.exponent + 12) = ((2 ^ (q.exponent + 12) : Nat) : Int) := by simp
  rw [he]
  rfl

/-- The wide irreversible kernel gives the signed, nearest-integer rounding of
the independent E-3/E-6 rational at the requested binary scale. -/
theorem irreversible_eq (q : BandQuant) (F : Nat) (c : Coeff) (hr : q.reversible = false)
    (hc : c.sig = false → c.mag = 0) :
    prepare q F (cellOf c) =
      roundSigned c.sign (Quant.dequantIrrevScaled q.roiShift q.delta F c) := by
  rw [kernel_form q F c hc]
  have hs : (Quant.roiUnshift q.roiShift c).sign = c.sign := by
    unfold Quant.roiUnshift; split <;> rfl
  unfold Quant.dequantIrrevScaled Quant.dequantIrrev Quant.reconstructIrrev
  generalize Quant.roiUnshift q.roiShift c = u at hs ⊢
  rw [← hs]
  by_cases hm : u.mag = 0
  · have hz := WideOutput.roundFix_eq_roundHalf 0 0
    simp [MCT.roundFix] at hz
    rw [show (0 / 1 : Rat) = 0 by grind] at hz
    cases u.sign <;> simp [hm, roundSigned, ← hz]
  · cases u.sign <;> simp [hm, roundSigned, magnitude_irrev q _ _ _ hr, Rat.neg_mul]

/-- Quantisation contributes at most half a fixed-point unit on every wide
irreversible cell, with no width, range or saturation premise. -/
theorem irreversible_error (q : BandQuant) (F : Nat) (c : Coeff) (hr : q.reversible = false)
    (hc : c.sig = false → c.mag = 0) :
    ((prepare q F (cellOf c) : Rat) - Quant.dequantIrrevScaled q.roiShift q.delta F c).abs ≤
      1 / 2 := by
  rw [irreversible_eq q F c hr hc]
  generalize Quant.dequantIrrevScaled q.roiShift q.delta F c = x
  apply Spec.DWT97.abs_le_iff.mpr
  cases c.sign <;> simp only [roundSigned, Decode.roundHalf, Bool.false_eq_true, ↓reduceIte]
  · have := Rat.floor_le (x + 1/2)
    have := Rat.lt_floor_add_one (x + 1/2)
    grind
  · have := Rat.floor_le (-x + 1/2)
    have := Rat.lt_floor_add_one (-x + 1/2)
    grind

private theorem read_writeCells {n area : Nat} (index : Fin n → Fin area) (value : Fin n → Int)
    (j : Fin area) (z : Int) (k : Nat) (hk : k ≤ n) (dst : Vector Int area)
    (hit : ∀ i : Fin n, i.val < k → (index i).val = j.val → value i = z)
    (miss : (∀ i : Fin n, i.val < k → (index i).val ≠ j.val) → dst[j.val] = z) :
    (writeCells index value k hk dst)[j.val] = z := by
  induction k generalizing dst with
  | zero => exact miss (by intro i hi; omega)
  | succ k ih =>
    unfold writeCells
    apply ih (by omega) _ (fun i hi => hit i (by omega))
    intro skipped
    rw [Vector.getElem_set]
    split
    · exact hit ⟨k, hk⟩ (Nat.lt_succ_self _) ‹_›
    · rename_i last
      apply miss
      intro i hi
      by_cases h : i.val < k
      · exact skipped i h
      · have eq : i = ⟨k, hk⟩ := Fin.ext (by change i.val = k; omega)
        exact eq ▸ last

private theorem dest_coords {dw w ox oy x y i : Nat} (hx : x < dw) (hw : 0 < w)
    (fit : ox + w ≤ dw) (eq : JPEG2000.WideOutput.destIndex dw w ox oy i = y * dw + x) :
    ox + i % w = x ∧ oy + i / w = y := by
  have hcol : ox + i % w < dw := by have := Nat.mod_lt i hw; omega
  have hd : 0 < dw := by omega
  unfold JPEG2000.WideOutput.destIndex at eq
  rw [Nat.mul_comm y dw] at eq
  exact ⟨by simpa [Nat.mul_add_mod, Nat.mod_eq_of_lt hcol, Nat.mod_eq_of_lt hx]
            using congrArg (· % dw) eq,
         by simpa [Nat.mul_add_div hd, Nat.div_eq_of_lt hcol, Nat.div_eq_of_lt hx]
            using congrArg (· / dw) eq⟩

private theorem place_read (dst : Plane) (cb : Rect) (ox oy : Nat)
    (f : JPEG2000.Tier1.WidePlain.Cell → Int) (cs : Array JPEG2000.Tier1.WidePlain.Cell)
    (hs : cs.size = rectArea cb) (fit : ox + cb.width ≤ dst.rect.width ∧ oy + cb.height ≤ dst.rect.height)
    (x y : Nat) (hx : x < dst.rect.width) (hy : y < dst.rect.height) :
    (place dst cb ox oy f cs hs fit).samples.toArray[y * dst.rect.width + x]? =
      if ox ≤ x ∧ x < ox + cb.width ∧ oy ≤ y ∧ y < oy + cb.height then
        (cs[(y - oy) * cb.width + (x - ox)]?).map f
      else dst.samples.toArray[y * dst.rect.width + x]? := by
  let j : Fin (rectArea dst.rect) := ⟨_, JPEG2000.DWT53.idx_lt hx hy⟩
  have hj : j.val = y * dst.rect.width + x := rfl
  rw [← hj]
  unfold place
  have get (a : Vector Int (rectArea dst.rect)) : a.toArray[j.val]? = some a[j.val] := by
    rw [Array.getElem?_eq_getElem (by simp)]
    rfl
  simp only [get]
  split
  · obtain ⟨hx0, hx1, hy0, hy1⟩ := ‹_ ∧ _ ∧ _ ∧ _›
    have hcol : x - ox < cb.width := by omega
    have hrow : y - oy < cb.height := by omega
    let src : Fin (rectArea cb) := ⟨_, JPEG2000.DWT53.idx_lt hcol hrow⟩
    have hs' : src.val < cs.size := by rw [hs]; exact src.isLt
    rw [Array.getElem?_eq_getElem hs', Option.map_some]
    congr 1
    apply read_writeCells _ _ j
    · intro i _ eq
      have hw : 0 < cb.width := by omega
      obtain ⟨ex, ey⟩ := dest_coords (y := y) (oy := oy) (i := i.val) hx hw fit.1 eq
      have ei : i.val = src.val := by
        change i.val = (y - oy) * cb.width + (x - ox)
        rw [← ey, ← ex, Nat.add_sub_cancel_left, Nat.add_sub_cancel_left, Nat.mul_comm,
          Nat.div_add_mod]
      simp only [ei]
    · intro none
      exfalso
      apply none src src.isLt
      have hw : 0 < cb.width := by omega
      simp only [src, j, JPEG2000.WideOutput.destIndex, Nat.mul_comm (y - oy) cb.width,
        Nat.mul_add_mod, Nat.mod_eq_of_lt hcol, Nat.mul_add_div hw, Nat.div_eq_of_lt hcol,
        Nat.add_zero, Nat.add_sub_of_le hx0, Nat.add_sub_of_le hy0, Nat.mul_comm dst.rect.width]
  · rename_i outside
    congr 1
    apply read_writeCells _ _ j
    · intro i hi eq
      have hi' : i.val < cb.width * cb.height := hi
      have hw : 0 < cb.width := by
        by_cases hz : cb.width = 0
        · simp [hz] at hi'
        · omega
      obtain ⟨ex, ey⟩ := dest_coords (y := y) (oy := oy) (i := i.val) hx hw fit.1 eq
      have hmod := Nat.mod_lt i.val hw
      have hdiv := Nat.div_lt_of_lt_mul hi'
      exfalso
      apply outside
      rw [← ex, ← ey]
      simp [hmod, hdiv]
    · exact fun _ => rfl

/-- The packet's band rectangle is also the retained band's rectangle on the
reduced grid. This includes LL when every detail level was discarded. -/
theorem reduced_band (tc : Rect) (nl red r : Nat) (b : Band)
    (hd : red ≤ nl) (hr : r ≤ nl - red) (hb : b ∈ bandsOf r) :
    bandRect (Assemble.reduceRect tc red) (bandLevel (nl - red) r) b =
      bandRect tc (bandLevel nl r) b := by
  rw [DWTPlane.bandRect_reduce]
  · congr 1; unfold bandLevel; split <;> omega
  · by_cases h : r = 0
    · subst r; exact .inr (by simpa [bandsOf] using hb)
    · simp [bandLevel, h]

/-- The translated block coordinates coincide with the inverse transform's
independent Mallat column and row, for each position of a cropped block. Apply
on the reduced rectangle with `reduced_band` for original packet coordinates. -/
theorem blockOffset_eq (rect : Rect) (nl r : Nat) (b : Band) (cb : Rect)
    (hr : r ≤ nl) (hb : b ∈ bandsOf r)
    (bounds : let band := bandRect rect (bandLevel nl r) b
              band.x0 ≤ cb.x0 ∧ band.y0 ≤ cb.y0 ∧ cb.x1 ≤ band.x1 ∧ cb.y1 ≤ band.y1)
    (x y : Nat) (hx : x < cb.width) (hy : y < cb.height) :
    let off := blockOffset rect nl r b cb
    QuantBlock.mx rect (bandLevel nl r) b ((cb.x0 + x : Nat) : Int) = ((off.1 + x : Nat) : Int) ∧
    QuantBlock.my rect (bandLevel nl r) b ((cb.y0 + y : Nat) : Int) = ((off.2 + y : Nat) : Int) :=
  (QuantBlock.block_pos rect nl r b cb hr hb bounds.1 bounds.2.1 bounds.2.2.1
    bounds.2.2.2 x y hx hy).2.2

private theorem offset_fits (rect : Rect) (nl r : Nat) (b : Band) (cb : Rect)
    (hr : r ≤ nl) (hb : b ∈ bandsOf r)
    (bounds : let band := bandRect rect (bandLevel nl r) b
              band.x0 ≤ cb.x0 ∧ band.y0 ≤ cb.y0 ∧ cb.x1 ≤ band.x1 ∧ cb.y1 ≤ band.y1)
    (hw : 0 < cb.width) (hh : 0 < cb.height) :
    let off := blockOffset rect nl r b cb
    off.1 + cb.width ≤ rect.width ∧ off.2 + cb.height ≤ rect.height := by
  let x := cb.width - 1
  let y := cb.height - 1
  obtain ⟨read, inside, ex, ey⟩ := QuantBlock.block_pos rect nl r b cb hr hb bounds.1
    bounds.2.1 bounds.2.2.1 bounds.2.2.2 x y (by change cb.width - 1 < cb.width; omega)
    (by change cb.height - 1 < cb.height; omega)
  obtain ⟨_, _, ll, detail⟩ := QuantBlock.mpos_range _ _ _ _ _ _ read inside
  dsimp only [blockOffset]
  rw [ex, ey] at ll detail
  have axis (k : Nat) : QuantBlock.Wd rect k ≤ rect.width ∧ QuantBlock.Hd rect k ≤ rect.height :=
    QuantBlock.Wd_anti rect (Nat.zero_le k)
  dsimp only [x, y] at ll detail
  by_cases h : b = .LL
  · obtain ⟨_, _⟩ := ll h
    obtain ⟨_, _⟩ := axis nl
    omega
  · obtain ⟨_, _, _, _⟩ := detail h
    obtain ⟨_, _⟩ := axis (bandLevel nl r - 1)
    omega

section Block
variable {L : Limits} {dst out : Plane} {p : Header.CompParams} {depth red r F : Nat}
    {b : Band} {cb : Rect} {cs : Array JPEG2000.Tier1.WidePlain.Cell}

/-- Every nonempty packet block contained in its retained band can be written
when its raster size and the caller's budgets agree. Its destination fit follows
from Mallat geometry. -/
theorem dequantBlock_succeeds
    (hw : rectArea dst.rect ≤ L.maxWorkSamples) (hl : p.levels ≤ L.maxDecompLevels)
    (hd : red ≤ p.levels) (hr : r ≤ p.levels - red) (hb : b ∈ bandsOf r)
    (bounds : let band := bandRect dst.rect (bandLevel (p.levels - red) r) b
              band.x0 ≤ cb.x0 ∧ band.y0 ≤ cb.y0 ∧ cb.x1 ≤ band.x1 ∧ cb.y1 ≤ band.y1)
    (hx : 0 < cb.width) (hy : 0 < cb.height) (hs : cs.size = rectArea cb) :
    ∃ out, dequantBlock L dst p depth red r b cb F cs = .ok out := by
  have fit := offset_fits dst.rect _ _ b cb hr hb bounds hx hy
  have hx' : ¬ cb.x1 < cb.x0 := by unfold Header.Rect.width at hx; omega
  have hy' : ¬ cb.y1 < cb.y0 := by unfold Header.Rect.height at hy; omega
  simp [dequantBlock, Limits.check, Limits.checkLe, Limits.bound, hw, hl, Nat.not_lt.mpr hd,
    Nat.not_lt.mpr hr, hb, hx', hy', Nat.not_lt.mpr bounds.1, Nat.not_lt.mpr bounds.2.1,
    Nat.not_lt.mpr bounds.2.2.1, Nat.not_lt.mpr bounds.2.2.2, hs, fit, bind, Except.bind,
    pure, Except.pure]

private theorem written (ok : dequantBlock L dst p depth red r b cb F cs = .ok out) :
    let off := blockOffset dst.rect (p.levels - red) r b cb
    ∃ (hs : cs.size = rectArea cb)
      (fit : off.1 + cb.width ≤ dst.rect.width ∧ off.2 + cb.height ≤ dst.rect.height),
      out = place dst cb off.1 off.2 (prepare (Quant.bandQuant p depth r b) F) cs hs fit := by
  unfold dequantBlock at ok
  cases hw : L.check JPEG2000.Quant.loc .workSamples (rectArea dst.rect) <;>
    simp only [hw, bind, Except.bind] at ok <;> try contradiction
  cases hl : L.check JPEG2000.Quant.loc .decompLevels p.levels <;>
    simp only [hl] at ok <;> try contradiction
  repeat' split at ok <;> try contradiction
  exact ⟨by assumption, by assumption, (Except.ok.inj ok).symm⟩

/-- A successful checked block write preserves the grid. Read at any destination
coordinate to get the kernel applied to the corresponding raster cell inside
the block, or the previous coefficient everywhere outside it. -/
theorem dequantBlock_read (ok : dequantBlock L dst p depth red r b cb F cs = .ok out) :
    let off := blockOffset dst.rect (p.levels - red) r b cb
    out.rect = dst.rect ∧ ∀ x y, x < dst.rect.width → y < dst.rect.height →
      out.samples.toArray[y * dst.rect.width + x]? =
        if off.1 ≤ x ∧ x < off.1 + cb.width ∧ off.2 ≤ y ∧ y < off.2 + cb.height then
          (cs[(y - off.2) * cb.width + (x - off.1)]?).map (prepare (Quant.bandQuant p depth r b) F)
        else dst.samples.toArray[y * dst.rect.width + x]? := by
  obtain ⟨hs, fit, rfl⟩ := written ok
  exact ⟨rfl, place_read _ _ _ _ _ _ hs fit⟩

/-- At the inverse transform's actual band address, a mapped Annex D raster
produces the exact reversible integer or the signed rounding of the rational
E-6 value. The band parameters use the packet's original resolution and orientation. -/
theorem dequantBlock_sample {coeffs : Array Coeff}
    (ok : dequantBlock L dst p depth red r b cb F (coeffs.map cellOf) = .ok out)
    (hr : r ≤ p.levels - red) (hb : b ∈ bandsOf r)
    (bounds : let band := bandRect dst.rect (bandLevel (p.levels - red) r) b
              band.x0 ≤ cb.x0 ∧ band.y0 ≤ cb.y0 ∧ cb.x1 ≤ band.x1 ∧ cb.y1 ≤ band.y1)
    (x y : Nat) (hx : x < cb.width) (hy : y < cb.height) (c : Coeff)
    (atCell : coeffs[y * cb.width + x]? = some c) (hc : c.sig = false → c.mag = 0) :
    let lvl := bandLevel (p.levels - red) r
    let u := QuantBlock.mx dst.rect lvl b ((cb.x0 + x : Nat) : Int)
    let v := QuantBlock.my dst.rect lvl b ((cb.y0 + y : Nat) : Int)
    let q := Quant.bandQuant p depth r b
    out.samples.toArray[v.toNat * dst.rect.width + u.toNat]? =
      some (if q.reversible then Quant.dequantRev q.roiShift c else
        roundSigned c.sign (Quant.dequantIrrevScaled q.roiShift q.delta F c)) := by
  let off := blockOffset dst.rect (p.levels - red) r b cb
  let q := Quant.bandQuant p depth r b
  obtain ⟨_, fit, _⟩ := written ok
  change off.1 + cb.width ≤ dst.rect.width ∧ off.2 + cb.height ≤ dst.rect.height at fit
  obtain ⟨ex, ey⟩ := blockOffset_eq dst.rect _ r b cb hr hb bounds x y hx hy
  dsimp only
  rw [ex, ey]
  change out.samples.toArray[(off.2 + y) * dst.rect.width + (off.1 + x)]? = _
  have h := (dequantBlock_read ok).2 (off.1 + x) (off.2 + y) (by omega) (by omega)
  have inside : off.1 ≤ off.1 + x ∧ off.1 + x < off.1 + cb.width ∧
      off.2 ≤ off.2 + y ∧ off.2 + y < off.2 + cb.height := by omega
  rw [h, ite_eq_left inside]
  simp only [off, Nat.add_sub_cancel_left, Array.getElem?_map, atCell, Option.map_some]
  cases hq : q.reversible
  · exact congrArg some (irreversible_eq q F c hq hc)
  · exact congrArg some (reversible_eq q F c hq hc)

end Block

private def extrema (rev : Bool) : BandQuant :=
  { reversible := rev, roiShift := 255, guard := 7, range := 31, exponent := 31, mantissa := 0 }

-- The maximum E-2/RGN magnitude, the highest truncated negative plane, the
-- largest background index and the threshold itself exercise both sides of H.2.
set_option exponentiation.threshold 292 in
example :
    let f := prepare (extrema true) 0
    f { sig := true, mag := 2^292 - 1 } = 2^37 - 1 ∧
    f { sig := true, sign := true, mag := 2^291, lsbPlane := 291 } = -(2^36 + 2^35) ∧
    f { sig := true, mag := 2^255 - 1 } = 2^255 - 1 ∧
    f { sig := true, mag := 2^255, lsbPlane := 254 } = 1 := by decide

-- Both signed half-unit ties, including a rounded value beyond the largest
-- post-ROI index. A significant zero with a stale last plane still reads zero.
set_option exponentiation.threshold 292 in
example :
    let f := prepare (extrema false) 0
    f { sig := true, mag := 2^292 - 1 } = 2^37 ∧
    f { sig := true, sign := true, mag := 2^292 - 1 } = -(2^37) ∧
    f { sig := true, sign := true, lsbPlane := 291 } = 0 ∧ f {} = 0 := by decide

private def cropped (cb : Rect) (b : Band) (L : Limits := Limits.default) :
    Option (Array Int) := do
  let p : Header.CompParams := { (default : Header.CompParams) with
    levels := 2, transform := .irreversible97
    steps := #[default, default, default, ⟨31, 1024⟩] }
  let rect := Assemble.reduceRect ⟨3, 5, 16, 17⟩ 1
  let dst ← (zeroChecked L rect).toOption
  let cs : Array JPEG2000.Tier1.WidePlain.Cell := #[
    { sig := true, mag := 3355443188 }, {}, { sig := true, sign := true, mag := 1 },
    { sig := true, mag := 2, lsbPlane := 1 }]
  let out ← (dequantBlock L dst p 38 1 1 b cb 1 cs).toOption
  return out.samples.toArray

-- Cropped HH on an odd-origin tile, one retained level. The HH gain and step
-- yield Δ = 768. The output has six columns and one fractional bit.
set_option maxRecDepth 4096 in
example : cropped ⟨2, 2, 4, 4⟩ .HH = some (#[
    0,0,0,0,0,0, 0,0,0,0,0,0, 0,0,0,0,0,0,
    0,0,0,0,0,0, 0,0,0,0,(2 * 3355443188 + 1) * 768,0, 0,0,0,0,-2304,4608]) := by decide +kernel

-- Reject an out-of-band block, an incorrect raster size, a disallowed orientation
-- and a one-cell budget shortfall before writing.
set_option maxRecDepth 4096 in
example : cropped ⟨3, 2, 5, 4⟩ .HH = none ∧ cropped ⟨2, 2, 3, 4⟩ .HH = none ∧
    cropped ⟨2, 2, 4, 4⟩ .LL = none ∧
    cropped ⟨2, 2, 4, 4⟩ .HH { Limits.default with maxWorkSamples := 35 } = none := by decide +kernel

end JPEG2000.Spec.WideQuant
