import Spec.QuantBlock.Write
import Spec.QuantBlock.Mallat

/-!
# One code-block written into the Mallat layout

Plan.md §4 (C9); T.800 Annex B.5 (B-15), E.1.1.2. Task 7.1d.

`write_hit`: after `Quant.blockRows` writes a code-block of band `b`, resolution `r` at its
band's Mallat origin (`Quant.bandOrigin`), the cell `toDec` reads for a band position of the
inverse transform holds the kernel value of the code-block's coefficient there if the
code-block covers that position (same band, same level, inside its rectangle), and is
unchanged otherwise (`mpos_inj`: no other read position shares the cell).
-/

namespace JPEG2000.Spec.QuantBlock

open JPEG2000 JPEG2000.Bytes JPEG2000.Tier2.Geometry
open JPEG2000.DWT53 (halfN cellInt toDec)
open JPEG2000.Spec.DWTPlane (halfN_coords bandCoord_high bandCoord_low if_t if_f)
open JPEG2000.Spec.Equiv (band53 band97 InBand ReadBand)
open JPEG2000.Quant (blockRows bandOrigin)

/-- A band of resolution `r ≤ NL` is read by the `NL`-level inverse transform at its level. -/
theorem readBand_of (nl r : Nat) (b : Band) (hr : r ≤ nl) (hb : b ∈ bandsOf r) :
    ReadBand nl (bandLevel nl r) b := by
  unfold bandsOf at hb
  unfold bandLevel
  by_cases h0 : r = 0
  · subst h0
    simp at hb
    exact .inl ⟨hb, rfl⟩
  · simp only [h0, ↓reduceIte] at hb ⊢
    refine .inr ⟨?_, by omega, by omega⟩
    intro e; subst e; simp at hb

/-- The Mallat column of band column `u` is the band origin plus the offset in the band. -/
theorem mx_origin (rect : Header.Rect) (nl r : Nat) (b : Band) (hr : r ≤ nl) (hb : b ∈ bandsOf r)
    (hne : (bandRect rect (bandLevel nl r) b).x0 < (bandRect rect (bandLevel nl r) b).x1)
    (u : Int) :
    mx rect (bandLevel nl r) b u =
      ((bandOrigin rect nl r b).1 : Int) + u - (bandRect rect (bandLevel nl r) b).x0 := by
  unfold bandsOf at hb
  by_cases h0 : r = 0
  · subst h0
    simp at hb; subst hb
    obtain ⟨c1, -, -, -⟩ := halfN_coords rect (bandLevel nl 0)
    simp [mx, bandOrigin, bandRect, Band.xob, bandCoord_low, c1]
  · simp only [h0, ↓reduceIte] at hb
    obtain ⟨k, hk⟩ : ∃ k, bandLevel nl r = k + 1 := ⟨nl - r, by unfold bandLevel; simp only [h0, ↓reduceIte]⟩
    rw [hk] at hne ⊢
    obtain ⟨c1, -, c3, -⟩ := halfN_coords rect k
    have e1 : (halfN rect (k + 1)).x0 = ((halfN rect k).x0 + 1) / 2 := rfl
    have e2 : (halfN rect (k + 1)).x1 = ((halfN rect k).x1 + 1) / 2 := rfl
    have hbo : bandOrigin rect nl r b = (if b.xob = 1 then (halfN rect (k + 1)).x1 - (halfN rect (k + 1)).x0 else 0,
        if b.yob = 1 then (halfN rect (k + 1)).y1 - (halfN rect (k + 1)).y0 else 0) := by
      simp only [bandOrigin, h0, ↓reduceIte, hk]
    rw [hbo]
    simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with hb | hb | hb <;> subst hb <;>
      simp (config := { decide := true }) only [mx, bandRect, Band.xob, bandCoord_high,
        bandCoord_low, Nat.add_sub_cancel, ↓reduceIte, e1, e2, DWTPlane.cdivPow_succ] at hne ⊢ <;>
      omega

/-- The Mallat row of band row `v` is the band origin plus the offset in the band. -/
theorem my_origin (rect : Header.Rect) (nl r : Nat) (b : Band) (hr : r ≤ nl) (hb : b ∈ bandsOf r)
    (hne : (bandRect rect (bandLevel nl r) b).y0 < (bandRect rect (bandLevel nl r) b).y1)
    (v : Int) :
    my rect (bandLevel nl r) b v =
      ((bandOrigin rect nl r b).2 : Int) + v - (bandRect rect (bandLevel nl r) b).y0 := by
  unfold bandsOf at hb
  by_cases h0 : r = 0
  · subst h0
    simp at hb; subst hb
    obtain ⟨-, c2, -, -⟩ := halfN_coords rect (bandLevel nl 0)
    simp [my, bandOrigin, bandRect, Band.yob, bandCoord_low, c2]
  · simp only [h0, ↓reduceIte] at hb
    obtain ⟨k, hk⟩ : ∃ k, bandLevel nl r = k + 1 := ⟨nl - r, by unfold bandLevel; simp only [h0, ↓reduceIte]⟩
    rw [hk] at hne ⊢
    obtain ⟨-, c2, -, c4⟩ := halfN_coords rect k
    have e1 : (halfN rect (k + 1)).y0 = ((halfN rect k).y0 + 1) / 2 := rfl
    have e2 : (halfN rect (k + 1)).y1 = ((halfN rect k).y1 + 1) / 2 := rfl
    have hbo : bandOrigin rect nl r b = (if b.xob = 1 then (halfN rect (k + 1)).x1 - (halfN rect (k + 1)).x0 else 0,
        if b.yob = 1 then (halfN rect (k + 1)).y1 - (halfN rect (k + 1)).y0 else 0) := by
      simp only [bandOrigin, h0, ↓reduceIte, hk]
    rw [hbo]
    simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with hb | hb | hb <;> subst hb <;>
      simp (config := { decide := true }) only [my, bandRect, Band.yob, bandCoord_high,
        bandCoord_low, Nat.add_sub_cancel, ↓reduceIte, e1, e2, DWTPlane.cdivPow_succ] at hne ⊢ <;>
      omega

/-- A plane cell as an `Int` by index (0 out of range). -/
def cv (p : Plane) (i : Nat) : Int :=
  match p.get? i with
  | some v => v.toInt
  | none => 0

/-- `cellInt` inside the plane's width is `cv` of the row-major index. -/
theorem cellInt_cv (p : Plane) (X Y : Int) (h0 : 0 ≤ X) (h1 : 0 ≤ Y) (h2 : X < p.width) :
    cellInt p X Y = cv p (Y.toNat * p.width + X.toNat) := by
  unfold cellInt
  rw [if_t ⟨h0, h1, h2⟩]
  rfl

/-- The block cells' band positions are read positions inside the band, at the block's
Mallat cells. -/
theorem block_pos (rect : Header.Rect) (nl r : Nat) (b : Band) (cbr : Header.Rect)
    (hr : r ≤ nl) (hb : b ∈ bandsOf r)
    (hx0 : (bandRect rect (bandLevel nl r) b).x0 ≤ cbr.x0)
    (hy0 : (bandRect rect (bandLevel nl r) b).y0 ≤ cbr.y0)
    (hx1 : cbr.x1 ≤ (bandRect rect (bandLevel nl r) b).x1)
    (hy1 : cbr.y1 ≤ (bandRect rect (bandLevel nl r) b).y1)
    (x y : Nat) (hx : x < cbr.x1 - cbr.x0) (hy : y < cbr.y1 - cbr.y0) :
    ReadBand nl (bandLevel nl r) b ∧
    InBand rect (bandLevel nl r) b ((cbr.x0 + x : Nat) : Int) ((cbr.y0 + y : Nat) : Int) ∧
    mx rect (bandLevel nl r) b ((cbr.x0 + x : Nat) : Int) =
      (((bandOrigin rect nl r b).1 + (cbr.x0 - (bandRect rect (bandLevel nl r) b).x0) + x : Nat) : Int) ∧
    my rect (bandLevel nl r) b ((cbr.y0 + y : Nat) : Int) =
      (((bandOrigin rect nl r b).2 + (cbr.y0 - (bandRect rect (bandLevel nl r) b).y0) + y : Nat) : Int) := by
  refine ⟨readBand_of nl r b hr hb, ?_, ?_, ?_⟩
  · simp only [InBand]; omega
  · rw [mx_origin rect nl r b hr hb (by omega)]; omega
  · rw [my_origin rect nl r b hr hb (by omega)]; omega

/-- **One code-block written** (module doc). -/
theorem write_hit (rect : Header.Rect) (nl r : Nat) (b : Band) (cbr : Header.Rect)
    (o : Tier1.CodeBlockOut) (f : Int32 → Nat → Int32 × Bool) (pl : Plane) (ok0 : Bool)
    (hw : pl.width = rect.width) (hh : pl.height = rect.height) (hr : r ≤ nl) (hb : b ∈ bandsOf r)
    (ow : o.plane.width = cbr.x1 - cbr.x0) (oh : o.plane.height = cbr.y1 - cbr.y0)
    (hx0 : (bandRect rect (bandLevel nl r) b).x0 ≤ cbr.x0)
    (hy0 : (bandRect rect (bandLevel nl r) b).y0 ≤ cbr.y0)
    (hx1 : cbr.x1 ≤ (bandRect rect (bandLevel nl r) b).x1)
    (hy1 : cbr.y1 ≤ (bandRect rect (bandLevel nl r) b).y1)
    (hnx : cbr.x0 < cbr.x1) (hny : cbr.y0 < cbr.y1) :
    let px := (bandOrigin rect nl r b).1 + (cbr.x0 - (bandRect rect (bandLevel nl r) b).x0)
    let py := (bandOrigin rect nl r b).2 + (cbr.y0 - (bandRect rect (bandLevel nl r) b).y0)
    (blockRows f o px py o.plane.height 0 pl ok0).1.width = pl.width ∧
    (blockRows f o px py o.plane.height 0 pl ok0).1.height = pl.height ∧
    ((blockRows f o px py o.plane.height 0 pl ok0).2 = true →
      ∀ x y, x < o.plane.width → y < o.plane.height →
        (f (bval o x y) (o.lsbPlane x y)).2 = true) ∧
    ∀ lvl2 b2 u v, ReadBand nl lvl2 b2 → InBand rect lvl2 b2 u v →
      cellInt (blockRows f o px py o.plane.height 0 pl ok0).1 (mx rect lvl2 b2 u) (my rect lvl2 b2 v) =
        if b = b2 ∧ bandLevel nl r = lvl2 ∧ (cbr.x0 : Int) ≤ u ∧ u < cbr.x1 ∧ (cbr.y0 : Int) ≤ v ∧
            v < cbr.y1 then
          (f (bval o (u - cbr.x0).toNat (v - cbr.y0).toNat)
            (o.lsbPlane (u - cbr.x0).toNat (v - cbr.y0).toNat)).1.toInt
        else cellInt pl (mx rect lvl2 b2 u) (my rect lvl2 b2 v) := by
  intro px py
  -- the block's last cell fits in the plane
  obtain ⟨_, ⟨_, _, _, _⟩, _, _⟩ := block_pos rect nl r b cbr hr hb hx0 hy0 hx1 hy1 0 0 (by omega) (by omega)
  obtain ⟨rl, il, xl, yl⟩ := block_pos rect nl r b cbr hr hb hx0 hy0 hx1 hy1
    (cbr.x1 - cbr.x0 - 1) (cbr.y1 - cbr.y0 - 1) (by omega) (by omega)
  obtain ⟨g1, g2, g3, g4⟩ := mpos_range rect nl _ b _ _ rl il
  have hW0 : Wd rect 0 = rect.width := rfl
  have hH0 : Hd rect 0 = rect.height := rfl
  have hfitW : ∀ X : Int, ∀ l c, ReadBand nl l c → (c = .LL → X < Wd rect nl) →
      (c ≠ .LL → X < Wd rect (l - 1)) → X < rect.width := by
    intro X l c hrb h1 h2
    by_cases hc : c = .LL
    · have := (Wd_anti rect (Nat.zero_le nl)).1; rw [hW0] at this; have := h1 hc; omega
    · have := (Wd_anti rect (Nat.zero_le (l - 1))).1; rw [hW0] at this; have := h2 hc; omega
  have hfitH : ∀ Y : Int, ∀ l c, ReadBand nl l c → (c = .LL → Y < Hd rect nl) →
      (c ≠ .LL → Y < Hd rect (l - 1)) → Y < rect.height := by
    intro Y l c hrb h1 h2
    by_cases hc : c = .LL
    · have := (Wd_anti rect (Nat.zero_le nl)).2; rw [hH0] at this; have := h1 hc; omega
    · have := (Wd_anti rect (Nat.zero_le (l - 1))).2; rw [hH0] at this; have := h2 hc; omega
  have hfit : px + o.plane.width ≤ pl.width := by
    have := hfitW _ _ b rl (fun h => (g3 h).1) (fun h => (g4 h).1)
    rw [xl] at this; rw [hw, ow]; omega
  obtain ⟨w1, w2, w3, w4⟩ := blockRows_spec f o px py o.plane.height 0 pl ok0 hfit
  refine ⟨w1, w2, fun h x y hx hy => (w4 h).2 y x (Nat.zero_le _) (by omega) hx, ?_⟩
  intro lvl2 b2 u v r2 i2
  obtain ⟨a1, a2, a3, a4⟩ := mpos_range rect nl lvl2 b2 u v r2 i2
  have hX := hfitW _ _ b2 r2 (fun h => (a3 h).1) (fun h => (a4 h).1)
  have hY := hfitH _ _ b2 r2 (fun h => (a3 h).2) (fun h => (a4 h).2.1)
  rw [cellInt_cv _ _ _ a1 a2 (by rw [w1, hw]; exact hX), cellInt_cv _ _ _ a1 a2 (by rw [hw]; exact hX)]
  simp only [cv]
  rw [w1, w3 _ _ (by rw [hw]; omega)]
  by_cases hm : b = b2 ∧ bandLevel nl r = lvl2 ∧ (cbr.x0 : Int) ≤ u ∧ u < cbr.x1 ∧
      (cbr.y0 : Int) ≤ v ∧ v < cbr.y1
  · rw [if_t hm]
    obtain ⟨e1, e2, h1, h2, h3, h4⟩ := hm
    subst e1; subst e2
    obtain ⟨-, -, xm, ym⟩ := block_pos rect nl r b cbr hr hb hx0 hy0 hx1 hy1
      (u - cbr.x0).toNat (v - cbr.y0).toNat (by omega) (by omega)
    rw [show ((cbr.x0 + (u - cbr.x0).toNat : Nat) : Int) = u by omega] at xm
    rw [show ((cbr.y0 + (v - cbr.y0).toNat : Nat) : Int) = v by omega] at ym
    rw [xm, ym]
    have hidx := DWT53.idx_lt (x := px + (u - cbr.x0).toNat) (y := py + (v - cbr.y0).toNat)
      (w := pl.width) (h := pl.height) (by rw [hw]; omega) (by rw [hh]; omega)
    rw [if_t ⟨by simp only [Int.toNat_natCast]; omega, by simp only [Int.toNat_natCast]; omega,
      by simp only [Int.toNat_natCast]; omega, by simp only [Int.toNat_natCast]; omega,
      by simp only [Int.toNat_natCast]; omega⟩]
    simp only [Int.toNat_natCast, px, py, Nat.add_sub_cancel_left]
  · rw [if_f hm, if_f]
    intro ⟨c1, c2, c3, c4, _⟩
    apply hm
    obtain ⟨rb, ib, xb, yb⟩ := block_pos rect nl r b cbr hr hb hx0 hy0 hx1 hy1
      ((mx rect lvl2 b2 u).toNat - px) ((my rect lvl2 b2 v).toNat - py) (by omega) (by omega)
    obtain ⟨q1, q2, q3, q4⟩ := mpos_inj rect nl _ _ b b2 _ _ u v rb ib r2 i2
      (by rw [xb]; omega) (by rw [yb]; omega)
    subst q1; subst q2
    refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩ <;> omega

end JPEG2000.Spec.QuantBlock
