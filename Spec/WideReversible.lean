import JPEG2000.WideReversible
import Spec.DWTPlane.Local
import Spec.MCT

/-!
# Exact wide 5/3 and colour reconstruction (Plan.md §§4, 5.1, 5.4, 7; T.800 B.5, F.3, G.2)

Read a Mallat raster as Annex F bands at their absolute sub-band coordinates.
Compare the checked spatial samples with the independent multi-level specification
and the three centred colour components with the Annex G inverse RCT.
-/

namespace JPEG2000.Spec.WideReversible

open JPEG2000.WideReversible
open JPEG2000.DWT53 (halfRect specRect srcIdx passVal lnb rnb sym_left sym_right unupdate_sym)
open Spec.DWT53 (Dec Grid sr1d sr2d srMulti interleave ext unupdate unpredict)

/-- The HL, LH and HH quadrants in absolute sub-band coordinates. A high band
starts at floor(origin/2) after the low band's extent in that direction. -/
def details (p : Array Int) (stride : Nat) (r : Header.Rect) : Grid × Grid × Grid :=
  let low := halfRect r
  let xh := fun (u : Int) => low.width + (u.toNat - r.x0 / 2)
  let yh := fun (v : Int) => low.height + (v.toNat - r.y0 / 2)
  let band := fun (x y : Int → Nat) =>
    (⟨fun u v => p.getD (y v * stride + x u) 0⟩ : Grid)
  let xl := fun (u : Int) => u.toNat - low.x0
  let yl := fun (v : Int) => v.toNat - low.y0
  (band xh yl, band xl yh, band xh yh)

/-- Read a Mallat raster as a decomposition. The coarsest LL begins at the
top-left cell of the original, full-stride buffer. -/
def mallat (p : Array Int) (stride : Nat) (r : Header.Rect) : Nat → Dec
  | 0 => ⟨⟨fun u v => p.getD ((v.toNat - r.y0) * stride + (u.toNat - r.x0)) 0⟩, []⟩
  | n + 1 =>
    let coarse := mallat p stride (halfRect r) n
    ⟨coarse.ll, details p stride r :: coarse.details⟩

private theorem raster_get (w h : Nat) (f : Nat → Nat → Int) (x y : Nat)
    (hx : x < w) (hy : y < h) :
    (raster w h f).getD (y * w + x) 0 = f x y := by
  have hi := JPEG2000.DWT53.idx_lt hx hy
  simp only [raster, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hi, ↓reduceDIte,
    Option.getD_some]
  simp only [Nat.mul_comm y w, Nat.mul_add_mod, Nat.mod_eq_of_lt hx,
    Nat.mul_add_div (show 0 < w by omega), Nat.div_eq_of_lt hx, Nat.add_zero]

private theorem lift_eq (a n : Nat) (f : Nat → Int) (g : Int → Int)
    (hg : ∀ k, k < n → f k = g ((a : Int) + k)) (k : Nat) (hk : k < n) :
    lift a n f k = sr1d a ((a : Int) + n) g ((a : Int) + k) := by
  by_cases hn : n ≤ 1
  · have : n = 1 := by omega
    subst n
    simp only [lift, sr1d, hn, ↓reduceIte, hg k hk, Int.natCast_one,
      show ¬ (a : Int) + 1 ≤ a by omega]
    split <;> split <;> first | rfl | omega
  · have hlen : (a : Int) + 2 ≤ (a : Int) + n := by omega
    let e := ext a ((a : Int) + n) g
    have he := Spec.DWT53.ext_sym hlen g
    have hu := unupdate_sym he
    rw [show (a : Int) + n - a - 1 = (n : Int) - 1 by omega] at he hu
    change Spec.DWT53.Sym (a : Int) ((n : Int) - 1) e at he
    change Spec.DWT53.Sym (a : Int) ((n : Int) - 1) (unupdate e) at hu
    have hread (i : Nat) (hi : i < n) : e ((a : Int) + i) = f i := by
      rw [hg i hi]; exact congrArg g (Spec.DWT53.pse_id (by omega) (by omega))
    have left (i : Nat) (hi : i < n) : lnb i < n := by unfold lnb; split <;> omega
    have right (i : Nat) (hi : i < n) : rnb n i < n := by unfold rnb; split <;> omega
    let ev := fun i => if (a + i) % 2 = 0 then passVal true n f i else f i
    have hup (i : Nat) (hi : i < n) : unupdate e ((a : Int) + i) = ev i := by
      unfold unupdate ev
      by_cases hp : (a + i) % 2 = 0
      · simp only [hp, show ((a : Int) + i) % 2 = 0 by omega, ↓reduceIte, passVal]
        rw [sym_left he i hi, sym_right he (by omega) i hi, hread i hi,
          hread _ (left i hi), hread _ (right i hi)]
      · simp only [hp, show ¬ ((a : Int) + i) % 2 = 0 by omega, ↓reduceIte, hread i hi]
    simp only [lift, hn, sr1d, show ¬ (a : Int) + n ≤ a by omega,
      show ¬ (a : Int) + n = a + 1 by omega, ↓reduceIte]
    change (if (a + k) % 2 = 0 then ev k else passVal false n ev k) =
      unpredict (unupdate e) ((a : Int) + k)
    by_cases hp : (a + k) % 2 = 0
    · simp only [hp, unpredict, show ¬ ((a : Int) + k) % 2 = 1 by omega, ↓reduceIte, hup k hk]
    · simp only [hp, unpredict, show ((a : Int) + k) % 2 = 1 by omega, ↓reduceIte,
        passVal, Bool.false_eq_true]
      rw [sym_left hu k hk, sym_right hu (by omega) k hk, hup k hk,
        hup _ (left k hk), hup _ (right k hk)]

private theorem lift_rect (a b k : Nat) (f : Nat → Int) (g : Int → Int)
    (hg : ∀ i, i < b - a → f i = g ((a : Int) + i)) (hk : k < b - a) :
    lift a (b - a) f k = sr1d a b g ((a : Int) + k) := by
  rw [lift_eq _ _ _ _ hg _ hk, show (a : Int) + (b - a : Nat) = b by omega]

private theorem synthesize_eq (p : Array Int) (stride : Nat) (r : Header.Rect) (nl : Nat)
    (x y : Nat) (hx : x < r.width) (hy : y < r.height) :
    (synthesize p stride r nl).getD (y * r.width + x) 0 =
      (srMulti (specRect r) nl (mallat p stride r nl)).get ((r.x0 : Int) + x) ((r.y0 : Int) + y) := by
  induction nl generalizing r x y with
  | zero =>
    rw [synthesize, raster_get _ _ _ _ _ hx hy]
    simp only [mallat, srMulti, show ((r.y0 : Int) + y).toNat - r.y0 = y by omega,
      show ((r.x0 : Int) + x).toNat - r.x0 = x by omega]
  | succ n ih =>
    let low := halfRect r
    let d := mallat p stride low n
    let ll := srMulti (specRect low) n d
    let b := details p stride r
    let input := interleave ll b.1 b.2.1 b.2.2
    have step : srMulti (specRect r) (n + 1) (mallat p stride r (n + 1)) =
        sr2d (specRect r) input := by
      simp only [mallat, srMulti, input, ll, d, low, b, DWTPlane.specRect_halfRect]
    rw [step, synthesize, raster_get _ _ _ _ _ hx hy]
    simp only [sr2d, Spec.DWT53.memo_eq, Spec.DWT53.verSR, Spec.DWT53.horSR, specRect]
    apply lift_rect _ _ _ _ _ _ hy
    intro j hj
    change j < r.height at hj
    rw [raster_get _ _ _ _ _ hx hj]
    apply lift_rect _ _ _ _ _ _ hx
    intro i hi
    change i < r.width at hi
    change (if (r.x0 + i) % 2 = 0 ∧ (r.y0 + j) % 2 = 0 then _ else _) = input.get _ _
    have lowCoord (a k : Nat) (h : (a + k) % 2 = 0) :
        (((a : Int) + k) / 2).toNat - (a + 1) / 2 = k / 2 := by omega
    have highCoord (a k : Nat) (h : (a + k) % 2 ≠ 0) :
        (((a : Int) + k) / 2).toNat - a / 2 = k / 2 := by omega
    have parity (a k : Nat) : ((a : Int) + k) % 2 = 0 ↔ (a + k) % 2 = 0 := by omega
    by_cases ex : (r.x0 + i) % 2 = 0 <;> by_cases ey : (r.y0 + j) % 2 = 0
    all_goals
      simp only [input, interleave, srcIdx, parity,
        ex, ey, and_self, and_false, false_and, ↓reduceIte]
    · have ix : i / 2 < low.width := by
        simp only [low, halfRect, Header.Rect.width] at hi ⊢; omega
      have jy : j / 2 < low.height := by
        simp only [low, halfRect, Header.Rect.height] at hj ⊢; omega
      rw [ih low _ _ ix jy]
      change ll.get _ _ = ll.get _ _
      congr 1 <;> simp only [low, halfRect] <;> omega
    · simp only [b, details, halfRect, lowCoord _ _ ex, highCoord _ _ ey]
    · simp only [b, details, halfRect, highCoord _ _ ex, lowCoord _ _ ey]
    · simp only [b, details, halfRect, highCoord _ _ ex, highCoord _ _ ey]

/-- All Annex F output samples at their actual coordinates, in row-major order. -/
def spatial (r : Header.Rect) (nl : Nat) (p : Array Int) : Array Int :=
  let g := srMulti (specRect r) nl (mallat p r.width r nl)
  raster r.width r.height fun x y => g.get ((r.x0 : Int) + x) ((r.y0 : Int) + y)

private theorem eq_raster (q : Array Int) (w h : Nat) (f : Nat → Nat → Int)
    (hs : q.size = w * h)
    (hv : ∀ x y, x < w → y < h → q.getD (y * w + x) 0 = f x y) :
    q = raster w h f := by
  apply Array.ext
  · simp [raster, hs]
  · intro i hi _
    have harea : i < w * h := hs ▸ hi
    have hw : 0 < w := by cases w <;> simp_all
    have e := hv _ _ (Nat.mod_lt i hw) (Nat.div_lt_of_lt_mul harea)
    rw [Nat.mul_comm (i / w) w, Nat.div_add_mod] at e
    simpa only [raster, Array.getElem_ofFn, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi,
      Option.getD_some] using e

private theorem synthesis_result (r : Header.Rect) (nl : Nat) (p : Array Int) (fit : Fits r p) :
    (if nl = 0 ∨ p.isEmpty then p else synthesize p r.width r nl) = spatial r nl p := by
  unfold spatial
  apply eq_raster
  · split
    · exact fit.2.2
    · cases nl <;> simp [synthesize, raster]
  · intro x y hx hy
    split
    · rename_i h
      rcases h with h | h
      · subst nl
        simp only [srMulti, mallat, show ((r.y0 : Int) + y).toNat - r.y0 = y by omega,
          show ((r.x0 : Int) + x).toNat - r.x0 = x by omega]
      · have hi := JPEG2000.DWT53.idx_lt hx hy
        have size := fit.2.2
        rw [Array.isEmpty_iff.mp h] at size
        simp only [Array.size_empty] at size
        omega
    · exact synthesize_eq _ _ _ _ _ _ hx hy

/-- Exact success domain and the complete reconstructed plane, for the supplied
remaining levels and rectangle. No sample magnitude bound is required. -/
theorem idwt53_spec (L : Limits) (r : Header.Rect) (nl : Nat) (p q : Array Int) :
    idwt53 L r nl p = .ok q ↔ nl ≤ L.maxDecompLevels ∧
      r.width * r.height ≤ L.maxWorkSamples ∧ Fits r p ∧ q = spatial r nl p := by
  unfold idwt53
  by_cases hl : nl ≤ L.maxDecompLevels <;>
    by_cases hw : r.width * r.height ≤ L.maxWorkSamples <;> by_cases hf : Fits r p <;>
    simp only [Limits.check, Limits.checkLe, Limits.bound, hl, hw, hf,
      bind, Except.bind, pure, Except.pure, throw, ↓reduceIte, true_and, false_and,
      Except.ok.injEq, reduceCtorEq]
  rw [synthesis_result _ _ _ hf, eq_comm]

private theorem mallat_length (p : Array Int) (stride : Nat) (r : Header.Rect) (nl : Nat) :
    (mallat p stride r nl).details.length = nl := by
  induction nl generalizing r with
  | zero => rfl
  | succ n ih => simp [mallat, ih]

/-- The C9 band interface: equality on the B-15 sub-band rectangles is enough
to substitute the dequantiser's independent decomposition at every output pixel. -/
theorem idwt53_of_bandsEq {L : Limits} {r : Header.Rect} {nl : Nat} {p q : Array Int}
    (h : idwt53 L r nl p = .ok q) (d : Dec) (hd : d.details.length = nl)
    (hb : Equiv.BandsEq r nl (mallat p r.width r nl) d)
    (x y : Nat) (hx : x < r.width) (hy : y < r.height) :
    q.getD (y * r.width + x) 0 =
      (srMulti (specRect r) nl d).get ((r.x0 : Int) + x) ((r.y0 : Int) + y) := by
  rw [((idwt53_spec ..).mp h).2.2.2, spatial, raster_get _ _ _ _ _ hx hy,
    ← DWTPlane.gMulti_sr1d, ← DWTPlane.gMulti_sr1d]
  apply DWTPlane.gMulti_local DWTPlane.kspec53 nl _ _ _ (mallat_length ..) hd
    (DWTPlane.bandsEq_agree _ _ _ _ hb)
  simp only [Header.Rect.width, Header.Rect.height] at hx hy
  simp only [specRect, Spec.DWT53.Rect.mem]
  omega

/-- Three row-major centred component rasters obtained by the Annex G.2 transform. -/
def rgb (n : Nat) (y cb cr : Array Int) : Array Int × Array Int × Array Int :=
  let triples := Array.ofFn (n := n) fun i =>
    MCT.rctInv (y.getD i.val 0, cb.getD i.val 0, cr.getD i.val 0)
  (triples.map (·.1), triples.map (·.2.1), triples.map (·.2.2))

private theorem colour_eq (n : Nat) (y cb cr : Array Int)
    (hy : y.size = n) (hb : cb.size = n) (hr : cr.size = n) :
    colour y cb cr = rgb n y cb cr := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  all_goals
    apply Array.ext
    · simp [colour, rgb, hy, hb, hr]
    · intro i hi _
      have hn : i < n := by simpa [colour, hy, hb, hr] using hi
      simp [colour, rgb, MCT.rctInv, Array.getElem_zipWith, Array.getD_eq_getD_getElem?,
        show i < y.size by omega, show i < cb.size by omega, show i < cr.size by omega]

/-- Exact success domain and every pre-DC colour sample. The inclusive work
bound counts the three component rectangles together. -/
theorem rctInverse_spec (L : Limits) (r s t : Header.Rect) (y cb cr : Array Int)
    (q : Array Int × Array Int × Array Int) :
    rctInverse L r s t y cb cr = .ok q ↔
      r.width * r.height + s.width * s.height + t.width * t.height ≤ L.maxWorkSamples ∧
      (SameShape r s t ∧ Fits r y ∧ Fits s cb ∧ Fits t cr) ∧
      q = rgb (r.width * r.height) y cb cr := by
  by_cases hw : r.width * r.height + s.width * s.height + t.width * t.height ≤ L.maxWorkSamples
  · by_cases hf : SameShape r s t ∧ Fits r y ∧ Fits s cb ∧ Fits t cr
    · obtain ⟨sw, sh, tw, th⟩ := hf.1
      obtain ⟨fy, fb, fr⟩ := hf.2
      have e := colour_eq (r.width * r.height) y cb cr fy.2.2
        (by rw [fb.2.2, sw, sh]) (by rw [fr.2.2, tw, th])
      simp [rctInverse, Limits.check, Limits.checkLe, Limits.bound, hw, hf, bind, Except.bind,
        pure, Except.pure, e, eq_comm]
    · simp [rctInverse, Limits.check, Limits.checkLe, Limits.bound, hw, hf, bind, Except.bind, throw]
  · simp [rctInverse, Limits.check, Limits.checkLe, Limits.bound, hw, bind, Except.bind]

private theorem rgb_get (n : Nat) (a b c : Array Int) (j : Nat) (hj : j < n) :
    let q := rgb n a b c
    (q.1.getD j 0, q.2.1.getD j 0, q.2.2.getD j 0) =
      MCT.rctInv (a.getD j 0, b.getD j 0, c.getD j 0) := by
  simp only [rgb, Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_ofFn,
    hj, ↓reduceDIte, Option.map_some, Option.getD_some]

/-- At every colour output coordinate the checked 5/3 and RCT stages together
give Annex G.2 applied to the three Annex F.3 values. Each component uses its
own absolute origin and remaining decomposition level count. -/
theorem reconstruct_rgb {L : Limits} {r s t : Header.Rect} {n₀ n₁ n₂ : Nat}
    {p₀ p₁ p₂ y cb cr : Array Int} {q : Array Int × Array Int × Array Int}
    (h₀ : idwt53 L r n₀ p₀ = .ok y) (h₁ : idwt53 L s n₁ p₁ = .ok cb)
    (h₂ : idwt53 L t n₂ p₂ = .ok cr) (hc : rctInverse L r s t y cb cr = .ok q)
    (x v : Nat) (hx : x < r.width) (hv : v < r.height) :
    let j := v * r.width + x
    (q.1.getD j 0, q.2.1.getD j 0, q.2.2.getD j 0) =
      MCT.rctInv
        ((srMulti (specRect r) n₀ (mallat p₀ r.width r n₀)).get ((r.x0 : Int) + x) ((r.y0 : Int) + v),
         (srMulti (specRect s) n₁ (mallat p₁ s.width s n₁)).get ((s.x0 : Int) + x) ((s.y0 : Int) + v),
         (srMulti (specRect t) n₂ (mallat p₂ t.width t n₂)).get ((t.x0 : Int) + x) ((t.y0 : Int) + v)) := by
  obtain ⟨_, ⟨⟨sw, sh, tw, th⟩, _⟩, rfl⟩ := (rctInverse_spec ..).mp hc
  dsimp only
  rw [rgb_get _ _ _ _ _ (JPEG2000.DWT53.idx_lt hx hv), ((idwt53_spec ..).mp h₀).2.2.2,
    ((idwt53_spec ..).mp h₁).2.2.2, ((idwt53_spec ..).mp h₂).2.2.2]
  simp only [spatial]
  rw [raster_get _ _ _ _ _ hx hv]
  rw [← sw, raster_get _ _ _ _ _ (sw ▸ hx) (sh ▸ hv), sw, ← tw,
    raster_get _ _ _ _ _ (tw ▸ hx) (th ▸ hv)]

-- Odd-origin row (high, low, high), followed by an odd singleton column.
-- F-5 rounds its negative correction down, and the wide LL survives both passes.
example : (idwt53 Limits.default ⟨1, 3, 4, 4⟩ 1 #[68719476736, -6, 2]).toOption =
    some #[34359738365, 34359738368, 34359738369] := by decide

-- Even singletons propagate the LL through every legal decomposition level.
set_option maxRecDepth 8192 in
example : (idwt53 Limits.default ⟨0, 0, 1, 1⟩ 32 #[-137438953472]).toOption =
    some #[-137438953472] := by decide

-- Both chroma differences exceed Int32.max, while all three colours fit.
example : (rctInverse { Limits.default with maxWorkSamples := 3 }
    ⟨0, 0, 1, 1⟩ ⟨1, 3, 2, 4⟩ ⟨2, 6, 3, 7⟩ #[0] #[2147483648] #[2147483649]).toOption =
    some (#[1073741825], #[-1073741824], #[1073741824]) := by
  change some (colour #[0] #[2147483648] #[2147483649]) = _
  rw [colour_eq 1 _ _ _ rfl rfl rfl]
  simp [rgb, Array.ofFn_succ, MCT.rctInv]

-- Each plane alone fits the budget, but the three planes together exceed it.
example : (rctInverse { Limits.default with maxWorkSamples := 2 }
    ⟨0, 0, 1, 1⟩ ⟨0, 0, 1, 1⟩ ⟨0, 0, 1, 1⟩ #[0] #[0] #[0]).toOption = none := by decide

-- Equal area is insufficient for an RCT if the component row strides differ.
example : (rctInverse Limits.default
    ⟨0, 0, 1, 2⟩ ⟨0, 0, 2, 1⟩ ⟨0, 0, 1, 2⟩ #[0, 0] #[0, 0] #[0, 0]).toOption = none := by decide

end JPEG2000.Spec.WideReversible
