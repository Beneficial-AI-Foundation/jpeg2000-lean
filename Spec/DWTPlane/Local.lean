import Spec.DWTPlane.Kernels

/-!
# Band locality of the multi-level inverse transform

Plan.md §4 (C6, C9); T.800 Annex F.3.1–F.3.3, Annex B.5 (B-15). Task 7.1d.

Level `i + 1` of `gMulti` on rectangle `r` interleaves its bands into `R = rhalf r i`: the HL
band is read at `u ∈ Hx R` (`⌊u0/2⌋ ≤ u < ⌊u1/2⌋`, the odd columns), `v ∈ Ly R`
(`⌈v0/2⌉ ≤ v < ⌈v1/2⌉`, the even rows), etc.; the LL band at `rhalf r n`. `gMulti_local`: two
decompositions agreeing there (`DecAgree`) give the same output on `r`. `bandsEq_agree`: these
positions are exactly the B-15 rectangles `bandRect` (`Spec.Equiv.BandsEq`).
-/

namespace JPEG2000.Spec.DWTPlane

open JPEG2000 JPEG2000.Bytes JPEG2000.Tier2.Geometry
open JPEG2000.DWT53 (halfN specRect)
open JPEG2000.Spec.DWT53 (Grid Dec interleave)
open JPEG2000.Spec.Equiv (band53 InBand ReadBand BandsEq)

/-! ## Band locality of the multi-level transform -/

/-- High-pass band coordinates of rectangle `R` along `u`: `⌊u0/2⌋ ≤ u < ⌊u1/2⌋`. -/
def Hx (R : Spec.DWT53.Rect) (u : Int) : Prop := R.u0 / 2 ≤ u ∧ u < R.u1 / 2
/-- Low-pass band coordinates along `u`: `⌈u0/2⌉ ≤ u < ⌈u1/2⌉`. -/
def Lx (R : Spec.DWT53.Rect) (u : Int) : Prop := (R.u0 + 1) / 2 ≤ u ∧ u < (R.u1 + 1) / 2
/-- High-pass band coordinates along `v`. -/
def Hy (R : Spec.DWT53.Rect) (v : Int) : Prop := R.v0 / 2 ≤ v ∧ v < R.v1 / 2
/-- Low-pass band coordinates along `v`. -/
def Ly (R : Spec.DWT53.Rect) (v : Int) : Prop := (R.v0 + 1) / 2 ≤ v ∧ v < (R.v1 + 1) / 2

/-- Two decompositions agree on every band position an `n`-level inverse transform to `r`
reads. -/
def DecAgree (r : Spec.DWT53.Rect) (n : Nat) (d1 d2 : Dec) : Prop :=
  (∀ u v, (rhalf r n).mem u v → d1.ll.get u v = d2.ll.get u v) ∧
  ∀ i b1 b2, i < n → d1.details[i]? = some b1 → d2.details[i]? = some b2 →
    (∀ u v, Hx (rhalf r i) u → Ly (rhalf r i) v → b1.1.get u v = b2.1.get u v) ∧
    (∀ u v, Lx (rhalf r i) u → Hy (rhalf r i) v → b1.2.1.get u v = b2.2.1.get u v) ∧
    (∀ u v, Hx (rhalf r i) u → Hy (rhalf r i) v → b1.2.2.get u v = b2.2.2.get u v)

/-- **Band locality**: `gMulti` (any local kernel) reads its decomposition only at the band
positions of `DecAgree`. -/
theorem gMulti_local {K : Kern} {op : Int → Int → (Int → Int) → Int → Int}
    {okP : Int → Int → (Int → Int) → Prop} (hK : KSpec K op okP) (n : Nat) :
    ∀ (r : Spec.DWT53.Rect) (d1 d2 : Dec), d1.details.length = n → d2.details.length = n →
    DecAgree r n d1 d2 → ∀ u v, r.mem u v →
      (gMulti op r n d1).get u v = (gMulti op r n d2).get u v := by
  induction n with
  | zero => intro r d1 d2 _ _ h u v hm; exact h.1 u v hm
  | succ n ih =>
    intro r d1 d2 l1 l2 h u v hm
    obtain ⟨ll1, det1⟩ := d1
    obtain ⟨ll2, det2⟩ := d2
    cases det1 with
    | nil => simp at l1
    | cons e1 t1 =>
    cases det2 with
    | nil => simp at l2
    | cons e2 t2 =>
    obtain ⟨hl1, lh1, hh1⟩ := e1
    obtain ⟨hl2, lh2, hh2⟩ := e2
    obtain ⟨hll, hdet⟩ := h
    simp only [gMulti]
    obtain ⟨a1, a2, a3⟩ := hdet 0 _ _ (by omega) rfl rfl
    have hrec : DecAgree r.half n ⟨ll1, t1⟩ ⟨ll2, t2⟩ :=
      ⟨hll, fun i b1 b2 hi h1 h2 => hdet (i + 1) b1 b2 (by omega) h1 h2⟩
    refine (g2d_local hK r _ _ ?_).1 u v hm
    intro u' v' ⟨h0, h1, h2, h3⟩
    simp only [interleave]
    by_cases hu : u' % 2 = 0 <;> by_cases hv : v' % 2 = 0 <;> simp only [hu, hv, ↓reduceIte]
    · exact ih r.half _ _ (by simpa using l1) (by simpa using l2) hrec _ _
        (by simp only [Spec.DWT53.Rect.half, Spec.DWT53.Rect.mem]; omega)
    · exact a2 _ _ (by simp only [Lx, rhalf]; omega) (by simp only [Hy, rhalf]; omega)
    · exact a1 _ _ (by simp only [Hx, rhalf]; omega) (by simp only [Ly, rhalf]; omega)
    · exact a3 _ _ (by simp only [Hx, rhalf]; omega) (by simp only [Hy, rhalf]; omega)

/-- `BandsEq` (the band positions of B-15) gives `DecAgree`. -/
theorem bandsEq_agree (rect : Header.Rect) (nl : Nat) (d1 d2 : Dec) (h : BandsEq rect nl d1 d2) :
    DecAgree (specRect rect) nl d1 d2 := by
  refine ⟨fun u v hm => ?_, fun i b1 b2 hi h1 h2 => ?_⟩
  · have := h nl .LL u v (.inl ⟨rfl, rfl⟩) (by
      rw [← specRect_halfN] at hm
      obtain ⟨c1, c2, c3, c4⟩ := halfN_coords rect nl
      simp only [specRect, Spec.DWT53.Rect.mem, c1, c2, c3, c4] at hm
      simp only [InBand, bandRect, Band.xob, Band.yob, bandCoord_low]
      omega)
    simpa [band53] using this
  · have hb : ∀ b, b ≠ .LL → ReadBand nl (i + 1) b := fun b hb => .inr ⟨hb, by omega, by omega⟩
    have e1 : (band53 d1 (i + 1) .HL) = b1.1 := by simp [band53, h1]
    have e2 : (band53 d2 (i + 1) .HL) = b2.1 := by simp [band53, h2]
    have e3 : (band53 d1 (i + 1) .LH) = b1.2.1 := by simp [band53, h1]
    have e4 : (band53 d2 (i + 1) .LH) = b2.2.1 := by simp [band53, h2]
    have e5 : (band53 d1 (i + 1) .HH) = b1.2.2 := by simp [band53, h1]
    have e6 : (band53 d2 (i + 1) .HH) = b2.2.2 := by simp [band53, h2]
    obtain ⟨c1, c2, c3, c4⟩ := halfN_coords rect i
    have hR : rhalf (specRect rect) i = specRect (halfN rect i) := (specRect_halfN rect i).symm
    rw [hR]
    simp only [Hx, Lx, Hy, Ly, specRect, c1, c2, c3, c4]
    refine ⟨fun u v hu hv => ?_, fun u v hu hv => ?_, fun u v hu hv => ?_⟩
    · have := h (i + 1) .HL u v (hb _ (by decide)) (by
        simp only [InBand, bandRect, Band.xob, Band.yob, bandCoord_high, bandCoord_low,
          cdivPow_succ]
        omega)
      rwa [e1, e2] at this
    · have := h (i + 1) .LH u v (hb _ (by decide)) (by
        simp only [InBand, bandRect, Band.xob, Band.yob, bandCoord_high, bandCoord_low,
          cdivPow_succ]
        omega)
      rwa [e3, e4] at this
    · have := h (i + 1) .HH u v (hb _ (by decide)) (by
        simp only [InBand, bandRect, Band.xob, Band.yob, bandCoord_high]
        omega)
      rwa [e5, e6] at this

end JPEG2000.Spec.DWTPlane
