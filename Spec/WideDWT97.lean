import JPEG2000.WideDWT97
import Spec.WideReversible
import Spec.DWTPlane

/-!
# C8 for wide Mallat synthesis (Plan.md §§4, 5.1, 5.4, 7; T.800 B-15 and F.3)

The integer filter multiplies by the exact Table F.4 ratios. Its residuals fit
the existing per-parity C8 budgets independently of intermediate magnitudes.
-/

namespace JPEG2000.Spec.WideDWT97

open JPEG2000.WideDWT97 (Step product unit kNum steps passes line lines atLine synthesize idwt97)
open JPEG2000.DWT97 (castS E1 B1 En rmax ηInv)
open Spec.DWT97 (Sig invSteps sr1d chain ext pert add smul pb zero ResBound abs_le_iff)
open Spec.DWT53 (pse Sym)
open JPEG2000.DWT53 (halfRect specRect srcIdx lnb rnb)
open DWTPlane (g2d gMulti DecCloseR)
open JPEG2000.Spec.WideReversible (mallat details)

/-- A single integer product has at most half a unit of rounding error at any
magnitude, for every signed numerator and positive denominator. -/
theorem product_err (num den x : Int) (hd : 0 < den) :
    ((product num den x : Rat) - (num : Rat) / den * x).abs ≤ 1/2 := by
  let z := num * x
  let q := product num den x
  have eqn : den * q + (z + den / 2) % den = z + den / 2 := Int.mul_ediv_add_emod ..
  have lo := Int.emod_nonneg (z + den / 2) (by omega : den ≠ 0)
  have hi := Int.emod_lt_of_pos (z + den / 2) hd
  have bounds : -den ≤ 2 * (den * q - z) ∧ 2 * (den * q - z) ≤ den := by omega
  have h₁ := Rat.intCast_le_intCast.mpr bounds.1
  have h₂ := Rat.intCast_le_intCast.mpr bounds.2
  simp only [z, Rat.intCast_neg, Rat.intCast_mul, Rat.intCast_sub, Rat.intCast_ofNat] at h₁ h₂
  have pos : (0 : Rat) < den := by exact_mod_cast hd
  have cancel := Rat.div_mul_cancel (a := (num : Rat)) (b := (den : Rat)) (by grind)
  change ((q : Rat) - (num : Rat) / den * x).abs ≤ 1/2
  apply abs_le_iff.mpr
  have e : ((q : Rat) - (num : Rat) / den * x) * den =
      (den : Rat) * q - (num : Rat) * x := by
    calc
      _ = (den : Rat) * q - (((num : Rat) / den * den) * x) := by grind only
      _ = _ := by rw [cancel]
  constructor <;> apply Rat.le_of_mul_le_mul_right _ pos <;> rw [e] <;>
    apply Rat.le_of_mul_le_mul_left _ (by decide : (0 : Rat) < 2)
  · rw [← Rat.mul_assoc, show (2 : Rat) * -(1/2) = -1 by decide +kernel]
    simpa only [Rat.neg_mul, Rat.one_mul] using h₁
  · rwa [← Rat.mul_assoc, show (2 : Rat) * (1/2) = 1 by decide +kernel, Rat.one_mul]

private def act (s : Step) (f : Int → Int) (j : Int) : Int :=
  s.cell (j % 2 == 0) (f j) (fun _ => f (j - 1) + f (j + 1))

private def exactStep : Step → Spec.DWT97.Step
  | .scale => .scaling ((kNum : Rat) / unit) ((unit : Rat) / kNum)
  | .lift p num => .lifting (if p then 0 else 1) ((num : Rat) / unit)

private theorem table : steps.map exactStep = invSteps := by
  simp only [steps, invSteps, List.map_cons, List.map_nil, exactStep,
    Bool.false_eq_true, ↓reduceIte, List.cons.injEq, Spec.DWT97.Step.scaling.injEq,
    Spec.DWT97.Step.lifting.injEq, and_true, true_and]
  decide +kernel

private def cap : Step → Rat × Rat
  | .scale => (1/2, 1/2)
  | .lift true _ => (1/2, 0)
  | .lift false _ => (0, 1/2)

private def residual (s : Step) (f : Int → Int) (j : Int) : Rat :=
  (act s f j : Rat) - (exactStep s).apply (castS f) j

private theorem residual_le (s : Step) (f : Int → Int) (j : Int) :
    (residual s f j).abs ≤ pb (cap s).1 (cap s).2 j := by
  have h0 : 0 < unit := by decide
  have hK : 0 < kNum := by decide
  cases s with
  | scale =>
    simp only [residual, act, Step.cell, exactStep, Spec.DWT97.Step.apply, Spec.DWT97.scale,
      castS, cap, pb, beq_iff_eq, ite_self]
    split
    · exact product_err _ _ _ h0
    · exact product_err _ _ _ hK
  | lift p num =>
    have h := product_err num unit (f (j - 1) + f (j + 1)) h0
    rw [Rat.intCast_add] at h
    cases p <;> rcases (by omega : j % 2 = 0 ∨ j % 2 = 1) with hj | hj <;>
      simp [residual, act, Step.cell, exactStep, Spec.DWT97.Step.apply, Spec.DWT97.lift,
        castS, cap, pb, hj, Rat.intCast_add, Rat.sub_self, Rat.abs_zero] <;>
      (rwa [show ∀ a b c : Rat, a + b - (a + c) = b - c by grind])

private def run : List Step → (Int → Int) → Int → Int
  | [], f => f
  | s :: ss, f => run ss (act s f)

private def residuals : List Step → (Int → Int) → List Sig
  | [], _ => []
  | s :: ss, f => residual s f :: residuals ss (act s f)

private theorem trajectory (ss : List Step) (f : Int → Int) :
    castS (run ss f) = pert (ss.map exactStep) (residuals ss f) (castS f) := by
  induction ss generalizing f with
  | nil => rfl
  | cons s ss ih =>
    simp only [run, List.map_cons, residuals, pert]
    rw [ih]
    congr 1
    funext j
    simp only [add, residual, castS]
    grind

private def FitsCap (s : Step) (e : Rat × Rat) : Prop := (cap s).1 ≤ e.1 ∧ (cap s).2 ≤ e.2

private inductive CapsFit : List Step → List (Rat × Rat) → Prop where
  | nil : CapsFit [] []
  | cons {s e ss es} : FitsCap s e → CapsFit ss es → CapsFit (s :: ss) (e :: es)

private theorem caps_fit : CapsFit steps ηInv := by
  repeat' apply CapsFit.cons
  all_goals first | exact CapsFit.nil | (unfold FitsCap; decide +kernel)

private theorem residuals_le {ss : List Step} {es : List (Rat × Rat)}
    (fit : CapsFit ss es) (f : Int → Int) :
    ResBound (residuals ss f) (es.map fun e => pb e.1 e.2) := by
  induction fit generalizing f with
  | nil => trivial
  | cons h _ ih =>
    refine ⟨fun j => Rat.le_trans (residual_le _ _ j) ?_, ih _⟩
    dsimp only
    unfold pb
    split <;> first | exact h.1 | exact h.2

private def model (a b : Int) (f : Int → Int) : Int → Int :=
  if b ≤ a then f
  else if b = a + 1 then (fun j => if a % 2 = 0 then f j else f j / 2)
  else run steps (JPEG2000.DWT97.qext a b f)

open JPEG2000.DWT97 (qext)
open Spec.DWT53 (pse_mem)
open Spec.DWT97 (chain_add chain_smul pert_eq pert_zero_bound chain_bound gb_mod injBound_mod abs_add_le)

private theorem model_err (i0 i1 : Int) (y : Int → Int) (x : Sig) (ε : Rat)
    (hx : ∀ k, i0 ≤ k → k < i1 → (((y k : Int) : Rat) - x k).abs ≤ ε)
    (j : Int) (h0 : i0 ≤ j) (h1 : j < i1) :
    (((model i0 i1 y j : Int) : Rat) - sr1d i0 i1 x j).abs ≤ E1 ε := by
  unfold model sr1d
  by_cases he : i1 ≤ i0
  · omega
  · by_cases h2 : i1 = i0 + 1
    · subst h2
      have hj : j = i0 := by omega
      subst hj
      have hxe := hx j (by omega) (by omega)
      have hε := DWTPlane.le_E1' ε
      have hnn : 0 ≤ ε := Rat.le_trans Rat.abs_nonneg hxe
      simp only [show ¬ j + 1 ≤ j by omega, ↓reduceIte]
      by_cases hp : j % 2 = 0
      · simp only [hp, ↓reduceIte]; grind
      · simp only [hp, ↓reduceIte]
        have ha := abs_le_iff.mp hxe
        have k1 : 2 * (y j / 2) ≤ y j := by omega
        have k2 : y j ≤ 2 * (y j / 2) + 1 := by omega
        have k1' := Rat.intCast_le_intCast.mpr k1
        have k2' := Rat.intCast_le_intCast.mpr k2
        simp only [Rat.intCast_add, Rat.intCast_mul, Rat.intCast_ofNat] at k1' k2'
        apply Rat.le_trans _ hε
        apply abs_le_iff.mpr
        constructor <;> grind
    · have hl : i0 + 2 ≤ i1 := by omega
      simp only [he, h2, ↓reduceIte]
      have hp := congrFun (trajectory steps (qext i0 i1 y)) j
      simp only [castS] at hp
      rw [hp, table, pert_eq]
      have hlin : chain invSteps (castS (qext i0 i1 y)) j - chain invSteps (ext i0 i1 x) j
          = chain invSteps (add (castS (qext i0 i1 y)) (smul (-1) (ext i0 i1 x))) j := by
        rw [chain_add, chain_smul]; simp only [add, smul]; grind
      have hb1 := chain_bound invSteps (add (castS (qext i0 i1 y)) (smul (-1) (ext i0 i1 x))) j
        (pb ε ε) (by
          intro k
          have := hx _ (pse_mem hl k).1 (pse_mem hl k).2
          simp only [add, smul, castS, qext, ext, pb]
          split <;> (have e : ((y (pse i0 i1 k) : Int) : Rat) + -1 * x (pse i0 i1 k)
              = ((y (pse i0 i1 k) : Int) : Rat) - x (pse i0 i1 k) := by grind) <;> rw [e] <;>
            exact this)
      have hb2 := pert_zero_bound invSteps _ _ (residuals_le caps_fit (qext i0 i1 y)) j
      rw [gb_mod] at hb1
      rw [injBound_mod] at hb2
      have hB := DWTPlane.B1_le_E1' j ε
      unfold B1 at hB
      simp only [add]
      have := abs_add_le (chain invSteps (add (castS (qext i0 i1 y)) (smul (-1) (ext i0 i1 x))) j)
        (pert invSteps (residuals steps (qext i0 i1 y)) zero j)
      have e : chain invSteps (castS (qext i0 i1 y)) j + pert invSteps (residuals steps (qext i0 i1 y)) zero j
          - chain invSteps (ext i0 i1 x) j
          = chain invSteps (add (castS (qext i0 i1 y)) (smul (-1) (ext i0 i1 x))) j
            + pert invSteps (residuals steps (qext i0 i1 y)) zero j := by rw [← hlin]; grind
      rw [e]
      grind

open Spec.DWT53 (Rect)
open DWTPlane (rmax_l rmax_r Hx Hy Lx Ly rhalf)

private theorem grid_err (r : Rect) (g : Spec.DWT53.Grid) (gx : Spec.DWT97.Grid) (ε : Rat)
    (h : ∀ u v, r.mem u v → ((g.get u v : Rat) - gx.get u v).abs ≤ ε)
    (u v : Int) (hm : r.mem u v) :
    (((g2d model r g).get u v : Rat) - (Spec.DWT97.sr2d r gx).get u v).abs ≤ E1 (E1 ε) := by
  simp only [g2d, DWTPlane.ghor, Spec.DWT97.sr2d, Spec.DWT97.memo_eq,
    Spec.DWT97.verSR, Spec.DWT97.horSR]
  obtain ⟨h0, h1, h2, h3⟩ := hm
  apply model_err _ _ _ _ _ _ v h2 h3
  intro k hk0 hk1
  apply model_err _ _ _ _ _ _ u h0 h1
  intro m hm0 hm1
  exact h m k ⟨hm0, hm1, hk0, hk1⟩

private theorem multi_err (n : Nat) : ∀ (r : Rect) (dq : Spec.DWT53.Dec) (dx : Spec.DWT97.Dec)
    (ε : Rat), dq.details.length = n → dx.details.length = n →
    DecCloseR ε r n (JPEG2000.DWT97.castDec dq) dx → ∀ u v, r.mem u v →
    ((((gMulti model r n dq).get u v : Int) : Rat) - (Spec.DWT97.srMulti r n dx).get u v).abs
      ≤ En n ε := by
  induction n with
  | zero => intro r dq dx ε _ _ h u v hm; exact h.1 u v hm
  | succ n ih =>
    intro r dq dx ε l1 l2 h u v hm
    obtain ⟨llq, detq⟩ := dq
    obtain ⟨llx, detx⟩ := dx
    cases detq with
    | nil => simp at l1
    | cons e1 t1 =>
    cases detx with
    | nil => simp at l2
    | cons e2 t2 =>
    obtain ⟨hlq, lhq, hhq⟩ := e1
    obtain ⟨hlx, lhx, hhx⟩ := e2
    obtain ⟨hll, hdet⟩ := h
    simp only [gMulti, Spec.DWT97.srMulti, En]
    obtain ⟨a1, a2, a3⟩ := hdet 0 _ _ (by omega) rfl rfl
    have hrec : DecCloseR ε r.half n (JPEG2000.DWT97.castDec ⟨llq, t1⟩) ⟨llx, t2⟩ :=
      ⟨hll, fun i b1 b2 hi h1 h2 => hdet (i + 1) b1 b2 (by omega) (by simpa [JPEG2000.DWT97.castDec] using h1) h2⟩
    apply grid_err _ _ _ _ _ u v hm
    intro u' v' ⟨h0, h1, h2, h3⟩
    have m1 := rmax_l (En n ε) ε
    have m2 := rmax_r (En n ε) ε
    simp only [Spec.DWT53.interleave, Spec.DWT97.interleave]
    by_cases hu : u' % 2 = 0 <;> by_cases hv : v' % 2 = 0 <;> simp only [hu, hv, ↓reduceIte]
    · exact Rat.le_trans (ih r.half _ _ ε (by simpa using l1) (by simpa using l2) hrec _ _
        (by simp only [Spec.DWT53.Rect.half, Spec.DWT53.Rect.mem]; omega)) m1
    · exact Rat.le_trans (a2 _ _ (by simp only [Lx, rhalf]; omega) (by simp only [Hy, rhalf]; omega)) m2
    · exact Rat.le_trans (a1 _ _ (by simp only [Hx, rhalf]; omega) (by simp only [Ly, rhalf]; omega)) m2
    · exact Rat.le_trans (a3 _ _ (by simp only [Hx, rhalf]; omega) (by simp only [Hy, rhalf]; omega)) m2

private theorem act_sym {a L : Int} {f : Int → Int} (s : Step) (hf : Sym a L f) :
    Sym a L (act s f) := by
  constructor
  · intro j
    simp only [act, show (2 * a - j) % 2 = j % 2 by omega,
      show 2 * a - j - 1 = 2 * a - (j + 1) by omega,
      show 2 * a - j + 1 = 2 * a - (j - 1) by omega, hf.1, Int.add_comm (f (j + 1))]
  · intro j
    simp only [act, show (j + 2 * L) % 2 = j % 2 by omega,
      show j + 2 * L - 1 = j - 1 + 2 * L by omega,
      show j + 2 * L + 1 = j + 1 + 2 * L by omega, hf.2]

private theorem ofFn_get {α : Type} (n : Nat) (f : Fin n → α) (k : Nat) (d : α) (hk : k < n) :
    (Array.ofFn f).getD k d = f ⟨k, hk⟩ := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hk, ↓reduceDIte, Option.getD_some]

private theorem passes_eq (a n : Nat) (hn : 2 ≤ n) (ss : List Step) (xs : Array Int)
    (g : Int → Int) (sym : Sym a ((n : Int) - 1) g)
    (read : ∀ i, i < n → xs.getD i 0 = g ((a : Int) + i)) (k : Nat) (hk : k < n) :
    (passes a n ss xs).getD k 0 = run ss g ((a : Int) + k) := by
  induction ss generalizing xs g with
  | nil => exact read k hk
  | cons s ss ih =>
    apply ih _ (act s g) (act_sym s sym)
    intro i hi
    have left : lnb i < n := by unfold lnb; split <;> omega
    have right : rnb n i < n := by unfold rnb; split <;> omega
    rw [ofFn_get _ _ _ _ hi]
    simp only [act, JPEG2000.DWT53.sym_left sym i hi, JPEG2000.DWT53.sym_right sym hn i hi,
      read i hi, read _ left, read _ right]
    congr 1
    by_cases h : (a + i) % 2 = 0
    · simp [h, show ((a : Int) + i) % 2 = 0 by omega]
    · rw [show (a + i) % 2 = 1 by omega, show ((a : Int) + i) % 2 = 1 by omega]
      decide

private theorem line_eq (a b : Nat) (f : Nat → Int) (g : Int → Int)
    (read : ∀ i, i < b - a → f i = g ((a : Int) + i)) (k : Nat) (hk : k < b - a) :
    (line a (b - a) f).getD k 0 = model a b g ((a : Int) + k) := by
  have hn : ¬ (b : Int) ≤ a := by omega
  unfold line model
  by_cases h1 : b - a ≤ 1
  · rw [ite_eq_left h1, ite_eq_right hn, ite_eq_left (show (b : Int) = a + 1 by omega),
      ofFn_get _ _ _ _ hk]
    dsimp only
    rw [read k hk]
    split <;> split <;> first | rfl | omega
  · have hl : (a : Int) + 2 ≤ b := by omega
    simp only [h1, hn, show ¬ (b : Int) = a + 1 by omega, ↓reduceIte]
    apply passes_eq _ _ (by omega) _ _ _ _ _ _ hk
    · have h := Spec.DWT53.ext_sym hl g
      rw [show (b : Int) - a - 1 = ((b - a : Nat) : Int) - 1 by omega] at h
      exact h
    · intro i hi
      rw [ofFn_get _ _ _ _ hi, read i hi, qext, Spec.DWT53.pse_id (by omega) (by omega)]

private theorem lines_get (a n c i k : Nat) (f : Nat → Nat → Int) (hi : i < c) (hk : k < n) :
    atLine (lines a n c f) i k = (line a n (f i)).getD k 0 := by
  simp only [atLine, lines, show n ≠ 0 by omega, ↓reduceIte, ofFn_get _ _ _ _ hi]

open JPEG2000.WideReversible (raster)
open Spec.DWT53 (interleave)

private theorem raster_get (w h : Nat) (f : Nat → Nat → Int) (x y : Nat)
    (hx : x < w) (hy : y < h) :
    (raster w h f).getD (y * w + x) 0 = f x y := by
  have hi := JPEG2000.DWT53.idx_lt hx hy
  simp only [raster, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hi, ↓reduceDIte,
    Option.getD_some]
  simp only [Nat.mul_comm y w, Nat.mul_add_mod, Nat.mod_eq_of_lt hx,
    Nat.mul_add_div (show 0 < w by omega), Nat.div_eq_of_lt hx, Nat.add_zero]

private theorem synthesize_eq (p : Array Int) (stride : Nat) (r : Header.Rect) (nl : Nat)
    (x y : Nat) (hx : x < r.width) (hy : y < r.height) :
    (synthesize p stride r nl).toArray.getD (y * r.width + x) 0 =
      (gMulti model (specRect r) nl (mallat p stride r nl)).get ((r.x0 : Int) + x) ((r.y0 : Int) + y) := by
  induction nl generalizing r x y with
  | zero =>
    rw [synthesize, raster_get _ _ _ _ _ hx hy]
    simp only [mallat, gMulti, show ((r.y0 : Int) + y).toNat - r.y0 = y by omega,
      show ((r.x0 : Int) + x).toNat - r.x0 = x by omega]
  | succ n ih =>
    let low := halfRect r
    let d := mallat p stride low n
    let ll := gMulti model (specRect low) n d
    let b := details p stride r
    let input := interleave ll b.1 b.2.1 b.2.2
    have step : gMulti model (specRect r) (n + 1) (mallat p stride r (n + 1)) =
        g2d model (specRect r) input := by
      simp only [mallat, gMulti, input, ll, d, low, b, DWTPlane.specRect_halfRect]
    rw [step, synthesize, raster_get _ _ _ _ _ hx hy]
    simp only [g2d, DWTPlane.ghor, specRect]
    rw [lines_get _ _ _ _ _ _ hx hy]
    apply line_eq _ _ _ _ _ _ hy
    intro j hj
    change j < r.height at hj
    rw [lines_get _ _ _ _ _ _ hj hx]
    apply line_eq _ _ _ _ _ _ hx
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

open WideQuant (Plane)
open Tier2.Geometry (rectArea)

/-- Exact admission conditions and output plane for the wide inverse. The
`Vector` length in `Plane` enforces the rectangular raster size. -/
theorem idwt97_spec (L : Limits) (p q : Plane) (nl : Nat) :
    idwt97 L p nl = .ok q ↔ nl ≤ L.maxDecompLevels ∧ rectArea p.rect ≤ L.maxWorkSamples ∧
      p.rect.x0 ≤ p.rect.x1 ∧ p.rect.y0 ≤ p.rect.y1 ∧
      q = (if nl = 0 ∨ rectArea p.rect = 0 then p else
        ⟨p.rect, synthesize p.samples.toArray p.rect.width p.rect nl⟩) := by
  unfold idwt97
  by_cases hl : nl ≤ L.maxDecompLevels <;> by_cases hw : rectArea p.rect ≤ L.maxWorkSamples <;>
    by_cases hx : p.rect.x0 ≤ p.rect.x1 <;> by_cases hy : p.rect.y0 ≤ p.rect.y1 <;>
    simp [Limits.check, Limits.checkLe, Limits.bound, hl, hw, hx, hy,
      show (p.rect.x1 < p.rect.x0) ↔ ¬ p.rect.x0 ≤ p.rect.x1 by omega,
      show (p.rect.y1 < p.rect.y0) ↔ ¬ p.rect.y0 ≤ p.rect.y1 by omega,
      bind, Except.bind, pure, Except.pure, throw]
  split <;> simp [eq_comm]

/-- Each resolution's raster, and each dimension of any nonempty raster, fit
the checked work ceiling. Empty lines allocate no line headers. -/
theorem level_work {L : Limits} {p q : Plane} {nl : Nat} (ok : idwt97 L p nl = .ok q) (k : Nat) :
    let r := JPEG2000.DWT53.halfN p.rect k
    rectArea r ≤ L.maxWorkSamples ∧ (0 < rectArea r →
      r.width ≤ L.maxWorkSamples ∧ r.height ≤ L.maxWorkSamples) := by
  obtain ⟨_, hw, _⟩ := (idwt97_spec ..).mp ok
  obtain ⟨hx, hy⟩ := JPEG2000.DWT53.halfN_le p.rect k
  have area := Nat.le_trans (Nat.mul_le_mul hx hy) hw
  refine ⟨area, fun h => ?_⟩
  let r := JPEG2000.DWT53.halfN p.rect k
  change 0 < r.width * r.height at h
  have ha : r.width * r.height ≤ L.maxWorkSamples := area
  exact ⟨Nat.le_trans (Nat.le_mul_of_pos_right _ (Nat.pos_of_mul_pos_left h)) ha,
    Nat.le_trans (Nat.le_mul_of_pos_left _ (Nat.pos_of_mul_pos_right h)) ha⟩

private theorem result_model {L : Limits} {p q : Plane} {nl : Nat} (ok : idwt97 L p nl = .ok q) :
    q.rect = p.rect ∧ ∀ x y, x < p.rect.width → y < p.rect.height →
      q.samples.toArray.getD (y * p.rect.width + x) 0 =
        (gMulti model (specRect p.rect) nl (mallat p.samples.toArray p.rect.width p.rect nl)).get
          ((p.rect.x0 : Int) + x) ((p.rect.y0 : Int) + y) := by
  obtain ⟨_, _, _, _, hq⟩ := (idwt97_spec ..).mp ok
  by_cases h : nl = 0 ∨ rectArea p.rect = 0
  · rw [ite_eq_left h] at hq
    subst q
    refine ⟨rfl, fun x y hx hy => ?_⟩
    rcases h with rfl | empty
    · simp only [gMulti, mallat, show ((p.rect.x0 : Int) + x).toNat - p.rect.x0 = x by omega,
        show ((p.rect.y0 : Int) + y).toNat - p.rect.y0 = y by omega]
    · have := Nat.mul_pos (Nat.zero_lt_of_lt hx) (Nat.zero_lt_of_lt hy)
      change p.rect.width * p.rect.height = 0 at empty
      omega
  · rw [ite_eq_right h] at hq
    subst q
    exact ⟨rfl, fun x y hx hy => synthesize_eq _ _ _ _ x y hx hy⟩

private theorem mallat_length (p : Array Int) (stride : Nat) (r : Header.Rect) (nl : Nat) :
    (mallat p stride r nl).details.length = nl := by
  induction nl generalizing r with
  | zero => rfl
  | succ n ih => simp [mallat, ih]

/-- C8 on the actual output grid. B-15 band errors of at most `ε` fixed-point
units give at most the existing `En nl ε` units at each output. For the wide
irreversible dequantiser, take `ε = 1/2`. The independent Annex F decomposition
and its transform are in physical units, with `F` fractional bits in the plane. -/
theorem idwt97_of_bandsClose {L : Limits} {p q : Plane} {nl F : Nat}
    (ok : idwt97 L p nl = .ok q) (d : Spec.DWT97.Dec) (hd : d.details.length = nl) (ε : Rat)
    (bands : Equiv.BandsClose ε F p.rect nl (mallat p.samples.toArray p.rect.width p.rect nl) d) :
    q.rect = p.rect ∧ ∀ x y, x < p.rect.width → y < p.rect.height →
      ∃ z, q.samples.toArray[y * p.rect.width + x]? = some z ∧
        ((z : Rat) - ((2 ^ F : Nat) : Rat) * (Spec.DWT97.srMulti (specRect p.rect) nl d).get
          ((p.rect.x0 : Int) + x) ((p.rect.y0 : Int) + y)).abs ≤ En nl ε := by
  obtain ⟨shape, sample⟩ := result_model ok
  refine ⟨shape, fun x y hx hy => ?_⟩
  have hi : y * p.rect.width + x < q.samples.toArray.size := by
    rw [q.samples.size_toArray, shape]
    exact JPEG2000.DWT53.idx_lt hx hy
  refine ⟨_, Array.getElem?_eq_getElem hi, ?_⟩
  have eqn := sample x y hx hy
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi, Option.getD_some] at eqn
  rw [eqn]
  have hm : (specRect p.rect).mem ((p.rect.x0 : Int) + x) ((p.rect.y0 : Int) + y) := by
    simp only [Header.Rect.width, Header.Rect.height] at hx hy
    simp only [specRect, Rect.mem]; omega
  have err := multi_err nl (specRect p.rect) _ (d.smul ((2 ^ F : Nat) : Rat)) ε
    (mallat_length ..) (by simp [Spec.DWT97.Dec.smul, hd])
    (DWTPlane.bandsClose_agree _ _ _ _ _ _ bands) _ _ hm
  rw [Spec.DWT97.srMulti_smul] at err
  exact err

private def samples (L : Limits) (p : Plane) (nl : Nat) : Option (Array Int) :=
  (idwt97 L p nl).toOption.map fun q => q.samples.toArray

private def oddTile : Plane :=
  ⟨⟨3, 5, 6, 7⟩, #v[1099511627777, -3, 2, -274877906944, 5, -7]⟩

-- A 3 × 2 odd-origin raster, two levels, and values beyond Int32 both before
-- and after synthesis. The first LL is a 1 × 1 high-vertical singleton.
set_option maxRecDepth 4096 in
example : samples { Limits.default with maxWorkSamples := 6 } oddTile 2 =
    some #[412316860416, 412316860418, 412316860416, 687194767356, 687194767360, 687194767365] := by
  decide +kernel

-- The negative HH singleton is halved twice with floor; an even singleton
-- passes unchanged through the full 32 levels.
set_option maxRecDepth 8192 in
example : samples Limits.default ⟨⟨1, 3, 2, 4⟩, #v[-1099511627777]⟩ 1 = some #[-274877906945] ∧
    samples Limits.default ⟨⟨0, 0, 1, 1⟩, #v[-1099511627777]⟩ 32 = some #[-1099511627777] := by
  decide +kernel

-- A short work ceiling and excess levels produce their specific limit errors.
example : idwt97 { Limits.default with maxWorkSamples := 5 } oddTile 2 =
    .error (.limitExceeded (.at .dwt) .workSamples 6 5) := rfl

example : idwt97 Limits.default oddTile 33 =
    .error (.limitExceeded (.at .dwt) .decompLevels 33 32) := rfl

-- An inverted rectangle remains malformed even at zero levels and zero area.
example : idwt97 Limits.default ⟨⟨4, 3, 3, 5⟩, #v[]⟩ 0 =
    .error (.malformed (.at .dwt) "inverted wide Mallat rectangle") := rfl

-- The other dimension of a valid empty plane requires no allocation.
example : samples { Limits.default with maxWorkSamples := 0 }
    ⟨⟨7, 0, 7, 1000000000⟩, #v[]⟩ 32 = some #[] := by decide +kernel

end JPEG2000.Spec.WideDWT97
