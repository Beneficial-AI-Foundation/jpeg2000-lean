import Spec.DWTPlane.Loops

/-!
# One level and the level loop of the inverse DWT, proved

Plan.md §4 (C6, C8, C9), §5.2 "DWT"; T.800 Annex F.3.1–F.3.3 (`IDWT`, `2D_SR`,
`2D_INTERLEAVE`), Annex B.5 (B-14). Task 7.1d.

`level_spec`: a row pass then a column pass over the resolution rectangle `r` turn the
Mallat-layout corner of `r` (read as an interleaved grid, `mallatGrid`) into `g2d` of it.
`levelsG_spec`: the level loop, from the coarsest level down, computes `gMulti` of the
decomposition stored in the plane (LL corner + detail bands, `tdBands`), for every kernel
satisfying `KSpec`.
-/

namespace JPEG2000.Spec.DWTPlane

open JPEG2000 JPEG2000.Bytes
open JPEG2000.DWT53 (Buf srcIdx batch halfN halfN_le specRect)
open JPEG2000.Spec.DWT53 (Grid Dec interleave)

/-- `g2d` reads its grid only on the rectangle; so does `gOk2d`. -/
theorem g2d_local {K : Kern} {op : Int → Int → (Int → Int) → Int → Int}
    {okP : Int → Int → (Int → Int) → Prop} (hK : KSpec K op okP) (r : Spec.DWT53.Rect)
    (g g' : Grid) (h : ∀ u v, r.mem u v → g.get u v = g'.get u v) :
    (∀ u v, r.mem u v → (g2d op r g).get u v = (g2d op r g').get u v) ∧
    (gOk2d op okP r g → gOk2d op okP r g') := by
  have hh : ∀ u v, r.mem u v → (ghor op r g).get u v = (ghor op r g').get u v := by
    intro u v ⟨h0, h1, h2, h3⟩
    exact (hK.loc _ _ _ _ (fun k hk0 hk1 => h k v ⟨hk0, hk1, h2, h3⟩)).1 u h0 h1
  refine ⟨?_, ?_⟩
  · intro u v ⟨h0, h1, h2, h3⟩
    exact (hK.loc _ _ _ _ (fun k hk0 hk1 => hh u k ⟨h0, h1, hk0, hk1⟩)).1 v h2 h3
  · intro ⟨o1, o2⟩
    refine ⟨fun v h2 h3 => (hK.loc _ _ _ _ (fun k hk0 hk1 => h k v ⟨hk0, hk1, h2, h3⟩)).2 (o1 v h2 h3),
      fun u h0 h1 => (hK.loc _ _ _ _ (fun k hk0 hk1 => hh u k ⟨h0, h1, hk0, hk1⟩)).2 (o2 u h0 h1)⟩

/-- The Mallat-layout corner of the resolution rectangle `r` read as an interleaved grid
(absolute `(u, v)` ↦ Mallat cell `(srcIdx (u − x0), srcIdx (v − y0))`). -/
def mallatGrid {N : Nat} (pw : Nat) (r : Header.Rect) (P : Buf N) : Grid :=
  ⟨fun u v => rd P (srcIdx r.y0 ((r.y1 + 1) / 2 - (r.y0 + 1) / 2) (v - r.y0).toNat * pw +
    srcIdx r.x0 ((r.x1 + 1) / 2 - (r.x0 + 1) / 2) (u - r.x0).toNat)⟩

/-- **One level** (`2D_SR` on the Mallat layout): a row pass then a column pass over the
rectangle `r`, when the flag stays set, leave `g2d op` of the interleaved corner in the corner
`[0, W) × [0, H)` and every other cell unchanged; `okP` holds of every pass. -/
theorem level_spec {K : Kern} {op : Int → Int → (Int → Int) → Int → Int}
    {okP : Int → Int → (Int → Int) → Prop} (hK : KSpec K op okP) {N T : Nat} (pw : Nat)
    (hN : N = pw * (N / pw)) (r : Header.Rect) (hW : r.x1 - r.x0 ≤ pw)
    (hH : r.y1 - r.y0 ≤ N / pw) (hT1 : r.x1 - r.x0 ≤ T) (hT : batch * (r.y1 - r.y0) ≤ T)
    (P : Buf N) (tmp : Buf T) (ok : Bool) (P1 : Buf N) (tmp1 : Buf T) (ok1 : Bool) (P2 : Buf N)
    (tmp2 : Buf T) (ok2 : Bool)
    (h1 : rowPassG K pw hN r.x0 r.x1 (r.y1 - r.y0) hW hH hT1 P tmp ok 0 = (P1, tmp1, ok1))
    (h2 : colPassG K pw hN (r.x1 - r.x0) r.y0 r.y1 hW hH hT P1 tmp1 ok1 0 = (P2, tmp2, ok2))
    (hok : ok2 = true) :
    ok = true ∧ gOk2d op okP (specRect r) (mallatGrid pw r P) ∧
    ∀ yy xx, xx < pw → rd P2 (yy * pw + xx) =
      if xx < r.x1 - r.x0 ∧ yy < r.y1 - r.y0 then
        (g2d op (specRect r) (mallatGrid pw r P)).get (r.x0 + xx) (r.y0 + yy)
      else rd P (yy * pw + xx) := by
  obtain ⟨c1, c2, c3⟩ := colPassG_spec hK pw hN (r.x1 - r.x0) r.y0 r.y1 hW hH hT P1 tmp1 ok1 0
    (by rw [h2]; exact hok)
  obtain ⟨r1, r2, r3⟩ := rowPassG_spec hK pw hN r.x0 r.x1 (r.y1 - r.y0) hW hH hT1 P tmp ok 0
    (by rw [h1]; exact c1)
  rw [h1] at r3
  rw [h2] at c3
  -- the column signals after the row pass, on the range
  have hcol : ∀ xx, xx < r.x1 - r.x0 → ∀ k, (r.y0 : Int) ≤ k → k < r.y1 →
      colSig pw r.y0 r.y1 P1 xx k = (ghor op (specRect r) (mallatGrid pw r P)).get (r.x0 + xx) k := by
    intro xx hxx k hk0 hk1
    have hs := DWT53.srcIdx_lt (a0 := r.y0) (a1 := r.y1) (i := (k - r.y0).toNat) (by omega)
    simp only [colSig]
    rw [r3 _ xx (by omega), if_t ⟨Nat.zero_le _, hs, hxx⟩]
    simp only [ghor, specRect]
    rw [show (r.x0 : Int) + ((r.x1 - r.x0 : Nat) : Int) = r.x1 by omega]
    rfl
  refine ⟨r1, ⟨?_, ?_⟩, ?_⟩
  · intro v h0 h1'
    simp only [specRect] at h0 h1' ⊢
    have hs := DWT53.srcIdx_lt (a0 := r.y0) (a1 := r.y1) (i := (v - r.y0).toNat) (by omega)
    have := r2 _ (Nat.zero_le _) hs
    by_cases hx : r.x0 ≤ r.x1
    · rw [show (r.x0 : Int) + ((r.x1 - r.x0 : Nat) : Int) = r.x1 by omega] at this
      exact this
    · exact hK.triv _ _ _ (by omega)
  · intro u h0 h1'
    simp only [specRect] at h0 h1' ⊢
    have := c2 (u - r.x0).toNat (Nat.zero_le _) (by omega)
    by_cases hy : r.y0 ≤ r.y1
    · rw [show (r.y0 : Int) + ((r.y1 - r.y0 : Nat) : Int) = r.y1 by omega] at this
      refine (hK.loc _ _ _ _ (fun k hk0 hk1 => ?_)).2 this
      rw [hcol _ (by omega) k hk0 hk1, show (r.x0 : Int) + ((u - r.x0).toNat : Nat) = u by omega]
      rfl
    · exact hK.triv _ _ _ (by omega)
  · intro yy xx hxx
    rw [c3 yy xx hxx]
    by_cases hc : xx < r.x1 - r.x0 ∧ yy < r.y1 - r.y0
    · rw [if_t ⟨Nat.zero_le _, hc.1, hc.2⟩, if_t hc]
      simp only [g2d, specRect]
      rw [show (r.y0 : Int) + ((r.y1 - r.y0 : Nat) : Int) = r.y1 by omega]
      exact (hK.loc _ _ _ _ (fun k hk0 hk1 => hcol xx hc.1 k hk0 hk1)).1 _ (by omega) (by omega)
    · rw [if_f (by omega), if_f hc, r3 yy xx hxx, if_f (by omega)]

/-! ## The level loop -/

open JPEG2000.DWT53 (cellInt toDec)

/-- The detail bands `(HL, LH, HH)` of level `l` exactly as `DWT53.toDec` reads them. -/
def tdBands (p : Plane) (tc : Header.Rect) (l : Nat) : Grid × Grid × Grid :=
  let R := halfN tc (l - 1)
  let L := halfN tc l
  let sn : Int := L.x1 - L.x0
  let sv : Int := L.y1 - L.y0
  let hx0 : Int := R.x0 / 2
  let hy0 : Int := R.y0 / 2
  let lx0 : Int := L.x0
  let ly0 : Int := L.y0
  ((⟨fun u v => cellInt p (sn + u - hx0) (v - ly0)⟩ : Grid),
   (⟨fun u v => cellInt p (u - lx0) (sv + v - hy0)⟩ : Grid),
   (⟨fun u v => cellInt p (sn + u - hx0) (sv + v - hy0)⟩ : Grid))

/-- `toDec` is the LL corner and `tdBands` per level. -/
theorem toDec_eq (p : Plane) (tc : Header.Rect) (nl : Nat) :
    toDec p tc nl = ⟨⟨fun u v => cellInt p (u - ((halfN tc nl).x0 : Int)) (v - ((halfN tc nl).y0 : Int))⟩,
      (List.range nl).map fun i => tdBands p tc (i + 1)⟩ := rfl

/-- The interleaved Mallat corner of level `k + 1` (rectangle `halfN tc k`) is `2D_INTERLEAVE`
of the LL corner (`G`, at `halfN tc (k+1)`) and the detail bands stored in the plane. -/
theorem mallat_interleave {N : Nat} (pw : Nat) (tc : Header.Rect) (k : Nat) (p0 : Plane)
    (P : Buf N) (G : Grid) (hpw : (halfN tc k).x1 - (halfN tc k).x0 ≤ pw)
    (hG : ∀ yy xx, xx < (halfN tc (k + 1)).x1 - (halfN tc (k + 1)).x0 →
      yy < (halfN tc (k + 1)).y1 - (halfN tc (k + 1)).y0 →
      rd P (yy * pw + xx) = G.get ((halfN tc (k + 1)).x0 + xx) ((halfN tc (k + 1)).y0 + yy))
    (hO : ∀ yy xx, xx < pw → ¬ (xx < (halfN tc (k + 1)).x1 - (halfN tc (k + 1)).x0 ∧
      yy < (halfN tc (k + 1)).y1 - (halfN tc (k + 1)).y0) → rd P (yy * pw + xx) = cellInt p0 xx yy) :
    ∀ u v, (specRect (halfN tc k)).mem u v →
      (mallatGrid pw (halfN tc k) P).get u v =
        (interleave G (tdBands p0 tc (k + 1)).1 (tdBands p0 tc (k + 1)).2.1
          (tdBands p0 tc (k + 1)).2.2).get u v := by
  intro u v hm
  simp only [specRect, Spec.DWT53.Rect.mem] at hm
  simp only [halfN, DWT53.halfRect] at hG hO
  simp only [mallatGrid, interleave, tdBands, Nat.add_sub_cancel, halfN, DWT53.halfRect]
  generalize halfN tc k = r at hm hG hO hpw ⊢
  obtain ⟨x0, y0, x1, y1⟩ := r
  simp only at hm hG hO hpw ⊢
  have hi : (u - x0).toNat < x1 - x0 := by omega
  have hj : (v - y0).toNat < y1 - y0 := by omega
  unfold srcIdx
  generalize hI : (u - (x0 : Int)).toNat = i at hi
  generalize hJ : (v - (y0 : Int)).toNat = j at hj
  by_cases hu : u % 2 = 0 <;> by_cases hv : v % 2 = 0
  · have e1 : (x0 + i) % 2 = 0 := by omega
    have e2 : (y0 + j) % 2 = 0 := by omega
    simp only [e1, e2, hu, hv, ↓reduceIte]
    rw [hG (j / 2) (i / 2) (by omega) (by omega)]
    congr 1 <;> omega
  · have e1 : (x0 + i) % 2 = 0 := by omega
    have e2 : ¬ (y0 + j) % 2 = 0 := by omega
    simp only [e1, e2, hu, hv, ↓reduceIte]
    rw [hO ((y1 + 1) / 2 - (y0 + 1) / 2 + j / 2) (i / 2) (by omega) (by omega)]
    congr 1 <;> omega
  · have e1 : ¬ (x0 + i) % 2 = 0 := by omega
    have e2 : (y0 + j) % 2 = 0 := by omega
    simp only [e1, e2, hu, hv, ↓reduceIte]
    rw [hO (j / 2) ((x1 + 1) / 2 - (x0 + 1) / 2 + i / 2) (by omega) (by omega)]
    congr 1 <;> omega
  · have e1 : ¬ (x0 + i) % 2 = 0 := by omega
    have e2 : ¬ (y0 + j) % 2 = 0 := by omega
    simp only [e1, e2, hu, hv, ↓reduceIte]
    rw [hO ((y1 + 1) / 2 - (y0 + 1) / 2 + j / 2) ((x1 + 1) / 2 - (x0 + 1) / 2 + i / 2)
      (by omega) (by omega)]
    congr 1 <;> omega

/-- The level loop's flag only goes from `true` to `false`. -/
theorem levelsG_ok {K : Kern} {op : Int → Int → (Int → Int) → Int → Int}
    {okP : Int → Int → (Int → Int) → Prop} (hK : KSpec K op okP) {N T : Nat}
    (tc : Header.Rect) (pw : Nat) (hN : N = pw * (N / pw)) (hpw : tc.x1 - tc.x0 ≤ pw)
    (hph : tc.y1 - tc.y0 ≤ N / pw) (hT : batch * (tc.y1 - tc.y0) ≤ T) (hT2 : tc.x1 - tc.x0 ≤ T)
    (k : Nat) : ∀ (P : Buf N) (tmp : Buf T) (ok : Bool),
    (levelsG K tc pw hN hpw hph hT hT2 k P tmp ok).2 = true → ok = true := by
  induction k with
  | zero => intro P tmp ok h; exact h
  | succ k ih =>
    intro P tmp ok hok
    have hr := halfN_le tc k
    simp only [levelsG] at hok
    rcases h1 : rowPassG K pw hN (halfN tc k).x0 (halfN tc k).x1
      ((halfN tc k).y1 - (halfN tc k).y0) (by omega) (by omega) (by omega) P tmp ok 0 with
      ⟨P1, tmp1, ok1⟩
    simp only [h1] at hok
    rcases h2 : colPassG K pw hN ((halfN tc k).x1 - (halfN tc k).x0) (halfN tc k).y0
      (halfN tc k).y1 (by omega) (by omega) (Nat.le_trans (Nat.mul_le_mul_left _ hr.2) hT)
      P1 tmp1 ok1 0 with ⟨P2, tmp2, ok2⟩
    simp only [h2] at hok
    have := (colPassG_spec hK pw hN _ _ _ _ _ _ P1 tmp1 ok1 0 (by rw [h2]; exact ih _ _ _ hok)).1
    exact (rowPassG_spec hK pw hN _ _ _ _ _ _ P tmp ok 0 (by rw [h1]; exact this)).1

/-- **The level loop** (`IDWT`, F.3.1, from the coarsest level down): if the corner of
`halfN tc k` holds the grid `G` (the LL band, absolute coordinates) and every cell outside it
holds the original plane `p0` (the detail bands), and the flag stays set, the corner of `tc`
ends holding `gMulti` of `G` and the detail bands of levels `1 … k` (`tdBands p0`), and `okP`
holds of every 1-D pass. -/
theorem levelsG_spec {K : Kern} {op : Int → Int → (Int → Int) → Int → Int}
    {okP : Int → Int → (Int → Int) → Prop} (hK : KSpec K op okP) {N T : Nat}
    (tc : Header.Rect) (pw : Nat) (hN : N = pw * (N / pw)) (hpw : tc.x1 - tc.x0 ≤ pw)
    (hph : tc.y1 - tc.y0 ≤ N / pw) (hT : batch * (tc.y1 - tc.y0) ≤ T) (hT2 : tc.x1 - tc.x0 ≤ T)
    (p0 : Plane) (k : Nat) :
    ∀ (P : Buf N) (tmp : Buf T) (ok : Bool) (G : Grid),
    (∀ yy xx, xx < (halfN tc k).x1 - (halfN tc k).x0 → yy < (halfN tc k).y1 - (halfN tc k).y0 →
      rd P (yy * pw + xx) = G.get ((halfN tc k).x0 + xx) ((halfN tc k).y0 + yy)) →
    (∀ yy xx, xx < pw → ¬ (xx < (halfN tc k).x1 - (halfN tc k).x0 ∧
      yy < (halfN tc k).y1 - (halfN tc k).y0) → rd P (yy * pw + xx) = cellInt p0 xx yy) →
    (levelsG K tc pw hN hpw hph hT hT2 k P tmp ok).2 = true →
    gOk op okP (specRect tc) k ⟨G, (List.range k).map fun i => tdBands p0 tc (i + 1)⟩ ∧
    ∀ yy xx, xx < tc.x1 - tc.x0 → yy < tc.y1 - tc.y0 →
      rd (levelsG K tc pw hN hpw hph hT hT2 k P tmp ok).1 (yy * pw + xx) =
        (gMulti op (specRect tc) k ⟨G, (List.range k).map fun i => tdBands p0 tc (i + 1)⟩).get
          (tc.x0 + xx) (tc.y0 + yy) := by
  induction k with
  | zero =>
    intro P tmp ok G hG _ _
    exact ⟨trivial, fun yy xx h1 h2 => hG yy xx h1 h2⟩
  | succ k ih =>
    intro P tmp ok G hG hO hok
    have hr := halfN_le tc k
    have hmono := halfN_mono tc k
    simp only [levelsG] at hok ⊢
    rcases h1 : rowPassG K pw hN (halfN tc k).x0 (halfN tc k).x1
      ((halfN tc k).y1 - (halfN tc k).y0) (by omega) (by omega) (by omega) P tmp ok 0 with
      ⟨P1, tmp1, ok1⟩
    simp only [h1] at hok ⊢
    rcases h2 : colPassG K pw hN ((halfN tc k).x1 - (halfN tc k).x0) (halfN tc k).y0
      (halfN tc k).y1 (by omega) (by omega) (Nat.le_trans (Nat.mul_le_mul_left _ hr.2) hT)
      P1 tmp1 ok1 0 with ⟨P2, tmp2, ok2⟩
    simp only [h2] at hok ⊢
    have hok2 : ok2 = true := levelsG_ok hK tc pw hN hpw hph hT hT2 k P2 tmp2 ok2 hok
    obtain ⟨l1, l2, l3⟩ := level_spec hK pw hN (halfN tc k) (by omega) (by omega) (by omega)
      (Nat.le_trans (Nat.mul_le_mul_left _ hr.2) hT) P tmp ok P1 tmp1 ok1 P2 tmp2 ok2 h1 h2 hok2
    have hagree := mallat_interleave pw tc k p0 P G (by omega) hG hO
    have hloc := g2d_local hK _ _ _ hagree
    have hdets : (List.range (k + 1)).map (fun i => tdBands p0 tc (i + 1)) =
        (List.range k).map (fun i => tdBands p0 tc (i + 1)) ++ [tdBands p0 tc (k + 1)] := by
      rw [List.range_succ, List.map_append]; rfl
    have hlen : ((List.range k).map (fun i => tdBands p0 tc (i + 1))).length = k := by simp
    rw [hdets, gMulti_snoc op k _ G _ _ hlen]
    rw [← specRect_halfN]
    obtain ⟨i1, i2⟩ := ih P2 tmp2 ok2 (g2d op (specRect (halfN tc k))
        (interleave G (tdBands p0 tc (k + 1)).1 (tdBands p0 tc (k + 1)).2.1
          (tdBands p0 tc (k + 1)).2.2)) (by
        intro yy xx hxx hyy
        rw [l3 yy xx (by omega), if_t ⟨hxx, hyy⟩]
        exact hloc.1 _ _ (by simp only [specRect, Spec.DWT53.Rect.mem]; omega))
      (by
        intro yy xx hxx hn
        rw [l3 yy xx hxx, if_f hn]
        exact hO yy xx hxx (by omega)) hok
    refine ⟨gOk_snoc op okP k _ G _ _ hlen ⟨?_, ?_⟩, i2⟩
    · rw [specRect_halfN] at i1; exact i1
    · rw [← specRect_halfN]; exact hloc.2 l2

end JPEG2000.Spec.DWTPlane
