import Spec.DWTPlane.Levels

/-!
# Band positions in the Mallat layout

Plan.md §4 (C9), §5.2 "DWT"; T.800 Annex B.5 (B-15), Annex F.3.3. Task 7.1d.

`mx` / `my`: the plane cell of band coordinate `(u, v)` of band `b` at decomposition level
`lvl` in the Mallat layout of `JPEG2000.DWT53` (what `DWT53.toDec` reads, `band53_toDec`; what
`Quant.dequantBlock` writes). `mpos_range`: a band position read by the inverse transform
(`ReadBand`, `InBand`) lands in its band's region (LL: the corner of `halfN rect nl`; a
detail band of level `l`: inside the corner of level `l − 1`, outside that of level `l`, on
the side its orientation says). `mpos_inj`: distinct read positions have distinct cells.
-/

namespace JPEG2000.Spec.QuantBlock

open JPEG2000 JPEG2000.Bytes JPEG2000.Tier2.Geometry
open JPEG2000.DWT53 (halfN cellInt toDec)
open JPEG2000.Spec.DWTPlane (tdBands toDec_eq halfN_coords halfN_mono bandCoord_high bandCoord_low)
open JPEG2000.Spec.Equiv (band53 band97 InBand ReadBand)

/-- Width of the resolution rectangle `halfN rect k`. -/
def Wd (rect : Header.Rect) (k : Nat) : Nat := (halfN rect k).x1 - (halfN rect k).x0
/-- Height of the resolution rectangle `halfN rect k`. -/
def Hd (rect : Header.Rect) (k : Nat) : Nat := (halfN rect k).y1 - (halfN rect k).y0

/-- The Mallat column of band column `u` of band `b` at level `lvl` (as `toDec`). -/
def mx (rect : Header.Rect) (lvl : Nat) (b : Band) (u : Int) : Int :=
  let R := halfN rect (lvl - 1)
  let L := halfN rect lvl
  let sn : Int := L.x1 - L.x0
  let hx0 : Int := R.x0 / 2
  let lx0 : Int := L.x0
  if b.xob = 1 then sn + u - hx0 else u - lx0

/-- The Mallat row of band row `v` of band `b` at level `lvl` (as `toDec`). -/
def my (rect : Header.Rect) (lvl : Nat) (b : Band) (v : Int) : Int :=
  let R := halfN rect (lvl - 1)
  let L := halfN rect lvl
  let sv : Int := L.y1 - L.y0
  let hy0 : Int := R.y0 / 2
  let ly0 : Int := L.y0
  if b.yob = 1 then sv + v - hy0 else v - ly0

/-- `toDec` reads band `b` of level `lvl` at the Mallat cell `(mx, my)`. -/
theorem band53_toDec (p : Plane) (rect : Header.Rect) (nl lvl : Nat) (b : Band)
    (hr : ReadBand nl lvl b) (u v : Int) :
    (band53 (toDec p rect nl) lvl b).get u v = cellInt p (mx rect lvl b u) (my rect lvl b v) := by
  rcases hr with ⟨hb, hl⟩ | ⟨hb, h1, h2⟩
  · subst hb; subst hl
    simp [band53, toDec_eq, mx, my, Band.xob, Band.yob]
  · have hd : (toDec p rect nl).details[lvl - 1]? = some (tdBands p rect lvl) := by
      rw [toDec_eq]
      simp only [List.getElem?_map, List.getElem?_range (show lvl - 1 < nl by omega),
        Option.map_some, show lvl - 1 + 1 = lvl by omega]
    cases b with
    | LL => exact absurd rfl hb
    | HL => simp only [band53, hd, tdBands, mx, my, Band.xob, Band.yob]; rfl
    | LH => simp only [band53, hd, tdBands, mx, my, Band.xob, Band.yob]; rfl
    | HH => simp only [band53, hd, tdBands, mx, my, Band.xob, Band.yob]; rfl

/-- The same for the rational decomposition reader `band97` (only the band choice). -/
theorem band97_eq (d : Spec.DWT97.Dec) (nl lvl : Nat) (b : Band) (hr : ReadBand nl lvl b)
    (hl : d.details.length = nl) :
    ∃ g, band97 d lvl b = g ∧ (b = .LL → g = d.ll) ∧
      (b ≠ .LL → ∃ t, d.details[lvl - 1]? = some t ∧
        g = (match b with | .HL => t.1 | .LH => t.2.1 | _ => t.2.2)) := by
  refine ⟨_, rfl, fun h => by subst h; rfl, fun h => ?_⟩
  rcases hr with ⟨hb, _⟩ | ⟨_, h1, h2⟩
  · exact absurd hb h
  · obtain ⟨t, ht⟩ : ∃ t, d.details[lvl - 1]? = some t :=
      ⟨d.details[lvl - 1]'(by omega), List.getElem?_eq_getElem _⟩
    refine ⟨t, ht, ?_⟩
    cases b <;> simp_all [band97]

/-- Resolution widths shrink with the level. -/
theorem Wd_anti (rect : Header.Rect) {k k' : Nat} (h : k ≤ k') : Wd rect k' ≤ Wd rect k ∧ Hd rect k' ≤ Hd rect k := by
  induction k' with
  | zero => have : k = 0 := by omega
            subst this; exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | succ k' ih =>
    by_cases e : k = k' + 1
    · subst e; exact ⟨Nat.le_refl _, Nat.le_refl _⟩
    · have := ih (by omega)
      have := halfN_mono rect k'
      simp only [Wd, Hd] at *
      omega

/-- **Where a read band position lands** in the Mallat layout. -/
theorem mpos_range (rect : Header.Rect) (nl lvl : Nat) (b : Band) (u v : Int)
    (hr : ReadBand nl lvl b) (hin : InBand rect lvl b u v) :
    0 ≤ mx rect lvl b u ∧ 0 ≤ my rect lvl b v ∧
    (b = .LL → mx rect lvl b u < Wd rect nl ∧ my rect lvl b v < Hd rect nl) ∧
    (b ≠ .LL → mx rect lvl b u < Wd rect (lvl - 1) ∧ my rect lvl b v < Hd rect (lvl - 1) ∧
      (b.xob = 1 ↔ (Wd rect lvl : Int) ≤ mx rect lvl b u) ∧
      (b.yob = 1 ↔ (Hd rect lvl : Int) ≤ my rect lvl b v)) := by
  rcases hr with ⟨hb, hl⟩ | ⟨hb, h1, h2⟩
  · subst hb; subst hl
    obtain ⟨c1, c2, c3, c4⟩ := halfN_coords rect lvl
    simp only [InBand, bandRect, Band.xob, Band.yob, bandCoord_low] at hin
    simp (config := { decide := true }) only [mx, my, Wd, Hd, ↓reduceIte]
    simp only [c1, c2, c3, c4]
    refine ⟨by omega, by omega, fun _ => ⟨by omega, by omega⟩, fun h => h.elim⟩
  · obtain ⟨k, rfl⟩ : ∃ k, lvl = k + 1 := ⟨lvl - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    obtain ⟨c1, c2, c3, c4⟩ := halfN_coords rect k
    have e1 : (halfN rect (k + 1)).x0 = ((halfN rect k).x0 + 1) / 2 := rfl
    have e2 : (halfN rect (k + 1)).x1 = ((halfN rect k).x1 + 1) / 2 := rfl
    have e3 : (halfN rect (k + 1)).y0 = ((halfN rect k).y0 + 1) / 2 := rfl
    have e4 : (halfN rect (k + 1)).y1 = ((halfN rect k).y1 + 1) / 2 := rfl
    simp only [InBand, bandRect] at hin
    refine ⟨?_, ?_, fun h => absurd h hb, fun _ => ?_⟩ <;>
    cases b with
    | LL => exact absurd rfl hb
    | HL =>
      simp only [Band.xob, Band.yob, bandCoord_high, bandCoord_low, DWTPlane.cdivPow_succ] at hin
      simp (config := { decide := true }) only [mx, my, Wd, Hd,
        Nat.add_sub_cancel, e1, e2, e3, e4, ↓reduceIte]
      simp only [c1, c2, c3, c4, true_iff, false_iff, Int.not_le]
      omega
    | LH =>
      simp only [Band.xob, Band.yob, bandCoord_high, bandCoord_low, DWTPlane.cdivPow_succ] at hin
      simp (config := { decide := true }) only [mx, my, Wd, Hd,
        Nat.add_sub_cancel, e1, e2, e3, e4, ↓reduceIte]
      simp only [c1, c2, c3, c4, true_iff, false_iff, Int.not_le]
      omega
    | HH =>
      simp only [Band.xob, Band.yob, bandCoord_high] at hin
      simp (config := { decide := true }) only [mx, my, Wd, Hd,
        Nat.add_sub_cancel, e1, e2, e3, e4, ↓reduceIte]
      simp only [c1, c2, c3, c4, true_iff]
      omega

/-- A non-LL band has a high-pass direction. -/
theorem Band.ob_of_ne (b : Band) (h : b ≠ .LL) : b.xob = 1 ∨ b.yob = 1 := by
  cases b <;> simp_all [Band.xob, Band.yob]

/-- Two non-LL bands with the same orientation bits are equal. -/
theorem Band.eq_of_ob (b1 b2 : Band) (h1 : b1 ≠ .LL) (h2 : b2 ≠ .LL) (hx : b1.xob = b2.xob)
    (hy : b1.yob = b2.yob) : b1 = b2 := by
  cases b1 <;> cases b2 <;> simp_all [Band.xob, Band.yob]

/-- **Distinct read band positions occupy distinct Mallat cells.** -/
theorem mpos_inj (rect : Header.Rect) (nl : Nat) (l1 l2 : Nat) (b1 b2 : Band) (u1 v1 u2 v2 : Int)
    (r1 : ReadBand nl l1 b1) (i1 : InBand rect l1 b1 u1 v1)
    (r2 : ReadBand nl l2 b2) (i2 : InBand rect l2 b2 u2 v2)
    (hx : mx rect l1 b1 u1 = mx rect l2 b2 u2) (hy : my rect l1 b1 v1 = my rect l2 b2 v2) :
    l1 = l2 ∧ b1 = b2 ∧ u1 = u2 ∧ v1 = v2 := by
  obtain ⟨a1, a2, a3, a4⟩ := mpos_range rect nl l1 b1 u1 v1 r1 i1
  obtain ⟨b1', b2', b3, b4⟩ := mpos_range rect nl l2 b2 u2 v2 r2 i2
  -- levels agree
  have hl : l1 = l2 ∧ b1 = b2 := by
    by_cases e1 : b1 = .LL <;> by_cases e2 : b2 = .LL
    · subst e1; subst e2
      exact ⟨by rcases r1 with ⟨_, h⟩ | ⟨h, _⟩ <;> rcases r2 with ⟨_, h'⟩ | ⟨h', _⟩ <;> simp_all, rfl⟩
    · exfalso
      have hl1 : l1 = nl := by rcases r1 with ⟨_, h⟩ | ⟨h, _⟩; exact h; exact absurd e1 h
      have hl2 : l2 ≤ nl := by rcases r2 with ⟨h, _⟩ | ⟨_, _, h⟩; exact absurd h e2; exact h
      obtain ⟨w1, w2⟩ := Wd_anti rect hl2
      obtain ⟨c1, c2⟩ := a3 e1
      obtain ⟨d1, d2, d3, d4⟩ := b4 e2
      rcases Band.ob_of_ne b2 e2 with h | h
      · have := d3.mp h; omega
      · have := d4.mp h; omega
    · exfalso
      have hl2 : l2 = nl := by rcases r2 with ⟨_, h⟩ | ⟨h, _⟩; exact h; exact absurd e2 h
      have hl1 : l1 ≤ nl := by rcases r1 with ⟨h, _⟩ | ⟨_, _, h⟩; exact absurd h e1; exact h
      obtain ⟨w1, w2⟩ := Wd_anti rect hl1
      obtain ⟨c1, c2⟩ := b3 e2
      obtain ⟨d1, d2, d3, d4⟩ := a4 e1
      rcases Band.ob_of_ne b1 e1 with h | h
      · have := d3.mp h; omega
      · have := d4.mp h; omega
    · obtain ⟨c1, c2, c3, c4⟩ := a4 e1
      obtain ⟨d1, d2, d3, d4⟩ := b4 e2
      have g1 : 1 ≤ l1 := by rcases r1 with ⟨h, _⟩ | ⟨_, h, _⟩; exact absurd h e1; exact h
      have g2 : 1 ≤ l2 := by rcases r2 with ⟨h, _⟩ | ⟨_, h, _⟩; exact absurd h e2; exact h
      rcases Nat.lt_trichotomy l1 l2 with hlt | heq | hgt
      · exfalso
        obtain ⟨w1, w2⟩ := Wd_anti rect (show l1 ≤ l2 - 1 by omega)
        rcases Band.ob_of_ne b1 e1 with h | h
        · have := c3.mp h; omega
        · have := c4.mp h; omega
      · subst heq
        refine ⟨rfl, Band.eq_of_ob b1 b2 e1 e2 ?_ ?_⟩
        · have := DWTPlane.Band.xob_le b1; have := DWTPlane.Band.xob_le b2
          by_cases h : b1.xob = 1
          · have := d3.mpr (by rw [← hx]; exact c3.mp h); omega
          · have : ¬ b2.xob = 1 := fun h' => h (c3.mpr (by rw [hx]; exact d3.mp h'))
            omega
        · have := DWTPlane.Band.yob_le b1; have := DWTPlane.Band.yob_le b2
          by_cases h : b1.yob = 1
          · have := d4.mpr (by rw [← hy]; exact c4.mp h); omega
          · have : ¬ b2.yob = 1 := fun h' => h (c4.mpr (by rw [hy]; exact d4.mp h'))
            omega
      · exfalso
        obtain ⟨w1, w2⟩ := Wd_anti rect (show l2 ≤ l1 - 1 by omega)
        rcases Band.ob_of_ne b2 e2 with h | h
        · have := d3.mp h; omega
        · have := d4.mp h; omega
  obtain ⟨hl1, hb1⟩ := hl
  subst hl1; subst hb1
  refine ⟨rfl, rfl, ?_, ?_⟩
  · simp only [mx] at hx; split at hx <;> omega
  · simp only [my] at hy; split at hy <;> omega

end JPEG2000.Spec.QuantBlock
