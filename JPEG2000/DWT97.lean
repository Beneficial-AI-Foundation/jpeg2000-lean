import JPEG2000.Bytes
import JPEG2000.Header
import JPEG2000.DWT53
import Spec.DWT97

/-!
# Fixed-point inverse 9/7 wavelet and theorem C8 (DWT part)

Plan.md §4 (C8), §5.2 "DWT", §5.4 (fixed point, fractional bits per bit depth, C8 bound vs
the T.803 thresholds), §6 item 5, §10 (open question "fixed-point precision for 9/7"), §11
(risk "fixed-point 9/7 misses conformance thresholds"); T.800 Annex F.3 (`IDWT`, `2D_SR`,
`1D_SR` F.3.6, `1D_EXTR` F-4, `1D_FILTR_9-7I` F.3.8.2, equations F-7, Table F.4).

## Number format

A cell `z : Int32` stands for `z / 2^F` (`F` fractional bits, `fracBits depth = 26 − depth`;
the transform itself never looks at `F`: lifting is scale-invariant, so everything below is
stated in units of `2^−F`, "ulps"). Constants have `C = 30` fractional bits
(`kQ … mAlphaQ = round(c · 2^30)`). A lifting step is
`x += rnd(cq · (l + r))`, a scaling `x := rnd(q · x)`, with `rnd t = ⌊(t + 2^29) / 2^30⌋`,
computed in `Int64` from `Int32` operands: `|cq| < 2^31` and `|l + r| ≤ 2^32` keep the
product below `2^63` (`liftStep_exact`, `scaleStep_exact`); `C = 30` is the largest value
with this property. Narrowing back to `Int32` is checked (a flag, no branch in the loop);
if any narrowing would overflow, the tile-component is recomputed by the exact `Rat`
specification (`idwt97Spec`), rounded and saturated.

Layout and loops are those of `JPEG2000.DWT53` (Mallat layout, bands at
`Tier2.Geometry.bandRect`; `loadRow`/`storeRow`/`loadCols`/`storeCols` are reused); only the
1-D kernel `lift1d97` differs.

## Theorem C8 (DWT)

* Model: `QStep`/`qchain`/`qsr1d`/`qsr2d`/`qsrMulti` — the kernel's arithmetic on integer
  signals with the F-4 extension, structured exactly like `Spec.DWT97`.
* Kernel = model: `lift1d97_eq` (every length, offset, start parity; when the flag stays
  set it also yields `Ok1d`, the no-overflow hypothesis of C8). The plane loops (Mallat
  layout ↔ interleaved order) and the level composition are tested, not proved
  (`Tests/DWT97.lean`: `idwt97Fast = idwt97Model`), as for the 5/3.
* Error: each fixed-point step = the exact step + a residual bounded by
  `1/2 + |ĉ/2^30 − c| · (operand bound)` (`step_resid`; operands are `Int32`, bound `2^31`).
  The exact chain is linear, local and translation-invariant, so the residuals and the input
  error propagate through the remaining steps with the sharp convolution bound
  `Spec.DWT97.gb`. Result: `qsr1d_err` (1-D, any input error `ε` → `E1 ε`), `qsr2d_err`
  (one level → `E1 (E1 ε)`), `qsrMulti_err` (`n` levels → `En n ε`, by induction),
  `qsrMulti_err_exact` (exact integer inputs → `En n 0` ulps) and `qsrMulti_err_frac`
  (inputs `z / 2^F` → `En n 0 / 2^F` in sample units, via homogeneity of the spec).

## The numbers (the Plan §10 question)

`E1 0 ≈ 12.54` ulps (1-D gain ≈ 2.178), and the per-level growth is `≈ 2.178² ≈ 4.74`:
`En n 0 ≈ 40, 229, 1126, 5380, 25559, 121281` ulps for `n = 1 … 6` (printed by the tests).
With `F = 26 − depth`: 8-bit `F = 18`, bound `0.02 / 0.10 / 0.46` samples at NL = 4/5/6;
12-bit `F = 14`: `0.33 / 1.6 / 7.4`; 16-bit `F = 10`: `5.3 / 25 / 118`. The T.803 class-1
peak thresholds of the 9/7 streams in the corpus (8-bit: 1–6 except three streams with peak
0; 12-bit: ≥ 378) are met on paper for 8 and 12 bits except the peak-0 streams, which no
error bound can guarantee (an exact value near `k + 1/2` can round either way) and are
checked by test. The bound is the product of per-level `ℓ∞` gains and is pessimistic: the
measured errors are far smaller (tests). For 16-bit 9/7 the proved bound is loose; a
tighter multi-level analysis or an `Int64`-cell path would be needed to prove sub-sample
accuracy there.
-/

namespace JPEG2000.DWT97

open JPEG2000.Spec.DWT97
open JPEG2000.Spec.DWT53 (pse pse_mem pse_id)

/-! ## Fixed-point constants (`C = 30` fractional bits) -/

/-- `2^30`, the scale of the fixed-point constants. -/
def cScale : Int := 1073741824

/-- `2^29`, the rounding offset (`½` of `cScale`). -/
def cHalf : Int := 536870912

/-- Round-to-nearest (ties up) of `t / 2^30`: `⌊(t + 2^29) / 2^30⌋`. -/
def rnd (t : Int) : Int := (t + 536870912) / 1073741824

/-- `round(K · 2^30)`. -/
def kQ : Int := 1320889387
/-- `round((1/K) · 2^30)`. -/
def invKQ : Int := 872837284
/-- `round(−δ · 2^30)`. -/
def mDeltaQ : Int := -476211856
/-- `round(−γ · 2^30)`. -/
def mGammaQ : Int := -948018549
/-- `round(−β · 2^30)`. -/
def mBetaQ : Int := 56886969
/-- `round(−α · 2^30)`. -/
def mAlphaQ : Int := 1703098782

/-! ## The fixed-point model on integer signals -/

/-- A fixed-point step together with the exact step it approximates. -/
inductive QStep where
  /-- Lifting on parity `p`: `f j + rnd(cq · (f (j−1) + f (j+1)))`, approximating `lift p c`. -/
  | lifting (p : Int) (c : Rat) (cq : Int)
  /-- Scaling: `rnd(qe · f j)` (even), `rnd(qo · f j)` (odd), approximating `scale ce co`. -/
  | scaling (ce co : Rat) (qe qo : Int)

/-- The action of a fixed-point step on an integer signal. -/
def QStep.apply : QStep → (Int → Int) → (Int → Int)
  | .lifting p _ cq, f => fun j =>
    if j % 2 = p then f j + rnd (cq * (f (j - 1) + f (j + 1))) else f j
  | .scaling _ _ qe qo, f => fun j =>
    if j % 2 = 0 then rnd (qe * f j) else rnd (qo * f j)

/-- The exact step approximated. -/
def QStep.toStep : QStep → Step
  | .lifting p c _ => .lifting p c
  | .scaling ce co _ _ => .scaling ce co

/-- Parity classes are 0 or 1. -/
def QStep.WF : QStep → Prop
  | .lifting p _ _ => p = 0 ∨ p = 1
  | .scaling _ _ _ _ => True

/-- A sequence of fixed-point steps. -/
def qchain : List QStep → (Int → Int) → (Int → Int)
  | [], f => f
  | s :: l, f => qchain l (s.apply f)

/-- The fixed-point inverse 9/7 (F-7 with 30-bit constants). -/
def invQ : List QStep :=
  [.scaling K (1 / K) kQ invKQ, .lifting 0 (-delta) mDeltaQ, .lifting 1 (-gamma) mGammaQ,
   .lifting 0 (-beta) mBetaQ, .lifting 1 (-alpha) mAlphaQ]

/-- `invQ` approximates `invSteps`. -/
theorem invQ_toStep : invQ.map QStep.toStep = invSteps := rfl

/-- The steps of `invQ` are well formed. -/
private theorem invQ_wf : ∀ s ∈ invQ, s.WF := by
  intro s hs
  simp only [invQ, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with h | h | h | h | h <;> subst h <;> simp [QStep.WF]

/-- An integer signal read as a rational one. -/
def castS (q : Int → Int) : Sig := fun k => (q k : Rat)

/-- The residuals of a fixed-point trajectory: after step `i`, the fixed-point value minus
the exact step applied to the previous fixed-point values. -/
def resids : List QStep → (Int → Int) → List Sig
  | [], _ => []
  | s :: l, q => (fun j => (s.apply q j : Rat) - s.toStep.apply (castS q) j) :: resids l (s.apply q)

/-- A fixed-point trajectory is the exact chain perturbed by its residuals. -/
theorem qchain_pert (l : List QStep) : ∀ q,
    castS (qchain l q) = pert (l.map QStep.toStep) (resids l q) (castS q) := by
  induction l with
  | nil => intro q; rfl
  | cons s l ih =>
    intro q
    simp only [qchain, List.map_cons, resids, pert]
    rw [ih]
    congr 1
    funext j
    simp only [castS, add]
    grind

/-! ## Residual bounds -/

/-- `|rnd t − t / 2^30| ≤ 1/2`. -/
theorem rnd_err (t : Int) : ((rnd t : Rat) - (t : Rat) / 1073741824).abs ≤ 1 / 2 := by
  have h1 : 1073741824 * rnd t ≤ t + 536870912 := by unfold rnd; omega
  have h2 : t + 536870912 < 1073741824 * rnd t + 1073741824 := by unfold rnd; omega
  have h1' := Rat.intCast_le_intCast.mpr h1
  have h2' := Rat.intCast_lt_intCast.mpr h2
  simp only [Rat.intCast_add, Rat.intCast_mul, Rat.intCast_ofNat] at h1' h2'
  apply abs_le_iff.mpr
  constructor <;> grind

/-- The per-parity residual bound `(even, odd)` of a step whose input is bounded by `M`:
rounding (`1/2`) plus the constant's error times the largest operand. -/
def qη (s : QStep) (M : Rat) : Rat × Rat :=
  match s with
  | .lifting p c cq =>
    let e := 1 / 2 + ((cq : Rat) / 1073741824 - c).abs * (2 * M)
    if p = 0 then (e, 0) else (0, e)
  | .scaling ce co qe qo =>
    (1 / 2 + ((qe : Rat) / 1073741824 - ce).abs * M,
     1 / 2 + ((qo : Rat) / 1073741824 - co).abs * M)

/-- `|a·b| ≤ |a|·B` when `|b| ≤ B`. -/
private theorem abs_mul_le_bound (a b B : Rat) (hb : b.abs ≤ B) : (a * b).abs ≤ a.abs * B := by
  have h := abs_mul_le b a B hb
  rw [Rat.mul_comm b a, Rat.mul_comm B] at h
  exact h

/-- Residual of one fixed-point lifting at a lifted position. -/
private theorem lift_res (qk a b cq : Int) (c M : Rat) (ha : ((a : Int) : Rat).abs ≤ M)
    (hb : ((b : Int) : Rat).abs ≤ M) :
    (((qk + rnd (cq * (a + b)) : Int) : Rat) - ((qk : Rat) + c * ((a : Rat) + (b : Rat)))).abs
      ≤ 1 / 2 + ((cq : Rat) / 1073741824 - c).abs * (2 * M) := by
  have e : (((qk + rnd (cq * (a + b)) : Int) : Rat) - ((qk : Rat) + c * ((a : Rat) + (b : Rat))))
      = (((rnd (cq * (a + b)) : Int) : Rat) - ((cq * (a + b) : Int) : Rat) / 1073741824)
        + ((cq : Rat) / 1073741824 - c) * ((a : Rat) + (b : Rat)) := by
    push_cast; grind
  rw [e]
  have h1 := rnd_err (cq * (a + b))
  have hab : ((a : Rat) + (b : Rat)).abs ≤ 2 * M := by
    have := abs_add_le (a : Rat) (b : Rat); grind
  have h2 := abs_mul_le_bound ((cq : Rat) / 1073741824 - c) _ _ hab
  have h3 := abs_add_le (((rnd (cq * (a + b)) : Int) : Rat) - ((cq * (a + b) : Int) : Rat) / 1073741824)
    (((cq : Rat) / 1073741824 - c) * ((a : Rat) + (b : Rat)))
  grind

/-- Residual of one fixed-point scaling. -/
private theorem scale_res (x qe : Int) (ce M : Rat) (hx : ((x : Int) : Rat).abs ≤ M) :
    (((rnd (qe * x) : Int) : Rat) - ce * (x : Rat)).abs
      ≤ 1 / 2 + ((qe : Rat) / 1073741824 - ce).abs * M := by
  have e : (((rnd (qe * x) : Int) : Rat) - ce * (x : Rat))
      = (((rnd (qe * x) : Int) : Rat) - ((qe * x : Int) : Rat) / 1073741824)
        + ((qe : Rat) / 1073741824 - ce) * (x : Rat) := by
    push_cast; grind
  rw [e]
  have h1 := rnd_err (qe * x)
  have h2 := abs_mul_le_bound ((qe : Rat) / 1073741824 - ce) _ _ hx
  have h3 := abs_add_le (((rnd (qe * x) : Int) : Rat) - ((qe * x : Int) : Rat) / 1073741824)
    (((qe : Rat) / 1073741824 - ce) * (x : Rat))
  grind

/-- One step's residual is bounded by `qη` when its input is bounded by `M`. -/
theorem step_resid (s : QStep) (hs : s.WF) (M : Rat) (q : Int → Int)
    (hq : ∀ k, ((q k : Int) : Rat).abs ≤ M) (k : Int) :
    (((s.apply q k : Int) : Rat) - s.toStep.apply (castS q) k).abs
      ≤ pb (qη s M).1 (qη s M).2 k := by
  cases s with
  | lifting p c cq =>
    simp only [QStep.WF] at hs
    simp only [QStep.apply, QStep.toStep, Step.apply, lift, castS, qη, pb]
    by_cases hk : k % 2 = p
    · have := lift_res (q k) (q (k - 1)) (q (k + 1)) cq c M (hq _) (hq _)
      rcases hs with hp | hp <;> subst hp <;>
        simp only [hk, ↓reduceIte, show ¬ (1 : Int) = 0 by decide] <;>
        first | exact this | (simp only [show ¬ (1 : Int) = 0 by omega, ↓reduceIte]; exact this)
    · simp only [hk, ↓reduceIte, Rat.sub_self, Rat.abs_zero]
      rcases hs with hp | hp <;> subst hp <;> split <;> simp_all <;> omega
  | scaling ce co qe qo =>
    simp only [QStep.apply, QStep.toStep, Step.apply, scale, castS, qη, pb]
    split
    · exact scale_res _ _ _ _ (hq k)
    · exact scale_res _ _ _ _ (hq k)

/-- Every state before a step of the fixed-point trajectory is bounded by `M` everywhere. -/
def StagesBounded : List QStep → (Int → Int) → Rat → Prop
  | [], _, _ => True
  | s :: l, q, M => (∀ k, ((q k : Int) : Rat).abs ≤ M) ∧ StagesBounded l (s.apply q) M

/-- Bounded stages give bounded residuals. -/
theorem resids_bound (l : List QStep) (hl : ∀ s ∈ l, s.WF) (M : Rat) : ∀ q,
    StagesBounded l q M →
    ResBound (resids l q) ((l.map fun s => qη s M).map fun e => pb e.1 e.2) := by
  induction l with
  | nil => intro q _; trivial
  | cons s l ih =>
    intro q h
    simp only [resids, List.map_cons, ResBound]
    exact ⟨fun k => step_resid s (hl s List.mem_cons_self) M q h.1 k,
      ih (fun t ht => hl t (List.mem_cons_of_mem _ ht)) _ h.2⟩

/-! ## C8, one dimension -/

/-- `2^31`: every value held in an `Int32` cell is at most this in magnitude. -/
def M32 : Rat := 2147483648

/-- The per-step residual bounds of `invQ` with operands bounded by `2^31`. -/
def ηInv : List (Rat × Rat) := invQ.map fun s => qη s M32

/-- The 1-D error bound at output parity `p` for input errors `≤ ε`: the propagated input
error plus the injected rounding/constant errors. -/
def B1 (p : Int) (ε : Rat) : Rat :=
  gb invSteps p (pb ε ε) + injBound invSteps (ηInv.map fun e => pb e.1 e.2) p

/-- Maximum of two rationals. -/
def rmax (a b : Rat) : Rat := if a ≤ b then b else a

private theorem le_rmax_left (a b : Rat) : a ≤ rmax a b := by unfold rmax; split <;> grind
private theorem le_rmax_right (a b : Rat) : b ≤ rmax a b := by unfold rmax; split <;> grind

/-- **The 1-D error bound** (in units of the last fixed-point bit): the inverse 9/7 pass of
`qsr1d` on inputs within `ε` of the exact ones is within `E1 ε` of `sr1d` (both parities;
`ε + 1/2` covers length-1 signals). -/
def E1 (ε : Rat) : Rat := rmax (rmax (B1 0 ε) (B1 1 ε)) (ε + 1 / 2)

private theorem B1_le_E1 (j : Int) (ε : Rat) : B1 (j % 2) ε ≤ E1 ε := by
  unfold E1
  have h1 := le_rmax_left (rmax (B1 0 ε) (B1 1 ε)) (ε + 1 / 2)
  rcases (by omega : j % 2 = 0 ∨ j % 2 = 1) with h | h <;> rw [h]
  · exact Rat.le_trans (le_rmax_left _ _) h1
  · exact Rat.le_trans (le_rmax_right _ _) h1

private theorem le_E1 (ε : Rat) : ε + 1 / 2 ≤ E1 ε := le_rmax_right _ _

/-- The fixed-point signal extended by periodic symmetric extension (F-4). -/
def qext (i0 i1 : Int) (y : Int → Int) : Int → Int := fun j => y (pse i0 i1 j)

/-- The fixed-point `1D_SR` model: length 0 unchanged, length 1 copied (even start) or
`⌊y/2⌋` (odd start), otherwise `invQ` on the extended signal. -/
def qsr1d (i0 i1 : Int) (y : Int → Int) : Int → Int :=
  if i1 ≤ i0 then y
  else if i1 = i0 + 1 then (fun j => if i0 % 2 = 0 then y j else y j / 2)
  else qchain invQ (qext i0 i1 y)

/-- No intermediate value of the fixed-point 1-D pass exceeds `2^31` (what the `Int32`
kernel's overflow flag guarantees). -/
def Ok1d (i0 i1 : Int) (y : Int → Int) : Prop :=
  i0 + 2 ≤ i1 → StagesBounded invQ (qext i0 i1 y) M32

/-- **C8 (1-D)**: if the fixed-point inputs are within `ε` of the exact inputs on
`[i0, i1)` and no intermediate value overflows, then every output of the fixed-point
inverse 9/7 is within `E1 ε` of `1D_SR` (`Spec.DWT97.sr1d`) of the exact inputs. -/
theorem qsr1d_err (i0 i1 : Int) (y : Int → Int) (x : Sig) (ε : Rat)
    (hx : ∀ k, i0 ≤ k → k < i1 → (((y k : Int) : Rat) - x k).abs ≤ ε) (hok : Ok1d i0 i1 y)
    (j : Int) (h0 : i0 ≤ j) (h1 : j < i1) :
    (((qsr1d i0 i1 y j : Int) : Rat) - sr1d i0 i1 x j).abs ≤ E1 ε := by
  unfold qsr1d sr1d
  by_cases he : i1 ≤ i0
  · omega
  · by_cases h2 : i1 = i0 + 1
    · subst h2
      have hj : j = i0 := by omega
      subst hj
      have hxe := hx j (by omega) (by omega)
      have hε := le_E1 ε
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
      have hp := congrFun (qchain_pert invQ (qext i0 i1 y)) j
      simp only [castS] at hp
      rw [hp, invQ_toStep, pert_eq]
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
      have hb2 := pert_zero_bound invSteps _ _ (resids_bound invQ invQ_wf M32 _ (hok hl)) j
      rw [gb_mod] at hb1
      rw [injBound_mod] at hb2
      have hB := B1_le_E1 j ε
      unfold B1 at hB
      simp only [add]
      have := abs_add_le (chain invSteps (add (castS (qext i0 i1 y)) (smul (-1) (ext i0 i1 x))) j)
        (pert invSteps (resids invQ (qext i0 i1 y)) zero j)
      have e : chain invSteps (castS (qext i0 i1 y)) j + pert invSteps (resids invQ (qext i0 i1 y)) zero j
          - chain invSteps (ext i0 i1 x) j
          = chain invSteps (add (castS (qext i0 i1 y)) (smul (-1) (ext i0 i1 x))) j
            + pert invSteps (resids invQ (qext i0 i1 y)) zero j := by rw [← hlin]; grind
      rw [e]
      simp only [ηInv] at hB
      grind

/-! ## C8, two dimensions and multi-level -/

open JPEG2000.Spec.DWT53 (Rect)

/-- An integer grid read as a rational one. -/
def castG (g : Spec.DWT53.Grid) : Grid := ⟨fun u v => (g.get u v : Rat)⟩

/-- Fixed-point `HOR_SR`: `qsr1d` on every row. -/
def qhorSR (r : Rect) (g : Spec.DWT53.Grid) : Spec.DWT53.Grid :=
  ⟨fun u v => qsr1d r.u0 r.u1 (fun u' => g.get u' v) u⟩

/-- Fixed-point `VER_SR`: `qsr1d` on every column. -/
def qverSR (r : Rect) (g : Spec.DWT53.Grid) : Spec.DWT53.Grid :=
  ⟨fun u v => qsr1d r.v0 r.v1 (fun v' => g.get u v') v⟩

/-- Fixed-point `2D_SR` (rows, then columns), materialised per pass. -/
def qsr2d (r : Rect) (g : Spec.DWT53.Grid) : Spec.DWT53.Grid :=
  Spec.DWT53.memo r (qverSR r (Spec.DWT53.memo r (qhorSR r g)))

/-- No 1-D pass of `qsr2d` overflows `Int32`. -/
def Ok2d (r : Rect) (g : Spec.DWT53.Grid) : Prop :=
  (∀ v, r.v0 ≤ v → v < r.v1 → Ok1d r.u0 r.u1 (fun u' => g.get u' v)) ∧
  (∀ u, r.u0 ≤ u → u < r.u1 → Ok1d r.v0 r.v1 (fun v' => (qhorSR r g).get u v'))

/-- **C8 (2-D, one level)**: inputs within `ε` on the rectangle and no overflow give outputs
within `E1 (E1 ε)` of `sr2d` (rows then columns). -/
theorem qsr2d_err (r : Rect) (g : Spec.DWT53.Grid) (x : Grid) (ε : Rat)
    (hx : ∀ u v, r.mem u v → (((g.get u v : Int) : Rat) - x.get u v).abs ≤ ε)
    (hok : Ok2d r g) (u v : Int) (h : r.mem u v) :
    ((((qsr2d r g).get u v : Int) : Rat) - (sr2d r x).get u v).abs ≤ E1 (E1 ε) := by
  simp only [qsr2d, sr2d, Spec.DWT53.memo_eq, memo_eq, qverSR, verSR]
  obtain ⟨h0, h1, h2, h3⟩ := h
  apply qsr1d_err _ _ _ _ _ _ (hok.2 u h0 h1) v h2 h3
  intro k hk0 hk1
  simp only [qhorSR, horSR]
  apply qsr1d_err _ _ _ _ _ _ (hok.1 k hk0 hk1) u h0 h1
  intro m hm0 hm1
  exact hx m k ⟨hm0, hm1, hk0, hk1⟩

/-- Fixed-point `IDWT` over `n` levels (the structure of `Spec.DWT97.srMulti`). -/
def qsrMulti : Rect → Nat → Spec.DWT53.Dec → Spec.DWT53.Grid
  | _, 0, d => d.ll
  | r, n + 1, ⟨ll, (hl, lh, hh) :: rest⟩ =>
    qsr2d r (Spec.DWT53.interleave (qsrMulti r.half n ⟨ll, rest⟩) hl lh hh)
  | _, _ + 1, ⟨ll, []⟩ => ll

/-- No 1-D pass of `qsrMulti` overflows `Int32`. -/
def OkMulti : Rect → Nat → Spec.DWT53.Dec → Prop
  | _, 0, _ => True
  | r, n + 1, ⟨ll, (hl, lh, hh) :: rest⟩ =>
    OkMulti r.half n ⟨ll, rest⟩ ∧
    Ok2d r (Spec.DWT53.interleave (qsrMulti r.half n ⟨ll, rest⟩) hl lh hh)
  | _, _ + 1, ⟨_, []⟩ => True

/-- An integer grid within `ε` of a rational one, everywhere. -/
def GClose (ε : Rat) (gq : Spec.DWT53.Grid) (gx : Grid) : Prop :=
  ∀ u v, (((gq.get u v : Int) : Rat) - gx.get u v).abs ≤ ε

/-- Detail bands within `ε`, level by level (equal numbers of levels). -/
def DetClose (ε : Rat) :
    List (Spec.DWT53.Grid × Spec.DWT53.Grid × Spec.DWT53.Grid) → List (Grid × Grid × Grid) → Prop
  | [], [] => True
  | (a, b, c) :: l, (a', b', c') :: l' =>
    GClose ε a a' ∧ GClose ε b b' ∧ GClose ε c c' ∧ DetClose ε l l'
  | _, _ => False

/-- A fixed-point decomposition within `ε` of a rational one. -/
def DecClose (ε : Rat) (dq : Spec.DWT53.Dec) (dx : Dec) : Prop :=
  GClose ε dq.ll dx.ll ∧ DetClose ε dq.details dx.details

/-- **The multi-level error bound** `E(NL)` (units of the last fixed-point bit) for input
errors `≤ ε`: each level applies `E1` twice (rows, columns) to the larger of the LL error
and `ε`. -/
def En : Nat → Rat → Rat
  | 0, ε => ε
  | n + 1, ε => E1 (E1 (rmax (En n ε) ε))

private theorem le_En (n : Nat) (ε : Rat) : ε ≤ En n ε := by
  cases n with
  | zero => exact Rat.le_refl
  | succ n =>
    simp only [En]
    have a := le_E1 (rmax (En n ε) ε)
    have b := le_E1 (E1 (rmax (En n ε) ε))
    have c := le_rmax_right (En n ε) ε
    grind

/-- **C8 (multi-level)**: for every number of levels `n`, every rectangle and every
fixed-point decomposition within `ε` of a rational one, if no 1-D pass overflows `Int32`,
the fixed-point inverse 9/7 `qsrMulti` is within `En n ε` of `Spec.DWT97.srMulti` at every
sample of the rectangle. -/
theorem qsrMulti_err (n : Nat) : ∀ (r : Rect) (dq : Spec.DWT53.Dec) (dx : Dec) (ε : Rat),
    DecClose ε dq dx → OkMulti r n dq → ∀ u v, r.mem u v →
    ((((qsrMulti r n dq).get u v : Int) : Rat) - (srMulti r n dx).get u v).abs ≤ En n ε := by
  induction n with
  | zero => intro r dq dx ε h _ u v _; exact h.1 u v
  | succ n ih =>
    intro r dq dx ε h hok u v hm
    obtain ⟨llq, detq⟩ := dq
    obtain ⟨llx, detx⟩ := dx
    obtain ⟨hll, hdet⟩ := h
    cases detq with
    | nil =>
      cases detx with
      | nil =>
        simp only [qsrMulti, srMulti]
        exact Rat.le_trans (hll u v) (le_En (n + 1) ε)
      | cons _ _ => exact absurd hdet (by simp [DetClose])
    | cons bq restq =>
      cases detx with
      | nil => exact absurd hdet (by simp [DetClose])
      | cons bx restx =>
        obtain ⟨hlq, lhq, hhq⟩ := bq
        obtain ⟨hlx, lhx, hhx⟩ := bx
        obtain ⟨c1, c2, c3, crest⟩ := hdet
        obtain ⟨hok1, hok2⟩ := hok
        simp only [qsrMulti, srMulti, En]
        apply qsr2d_err _ _ _ _ _ hok2 u v hm
        intro u' v' hm'
        have m1 := le_rmax_left (En n ε) ε
        have m2 := le_rmax_right (En n ε) ε
        simp only [Spec.DWT53.interleave, interleave]
        by_cases hu : u' % 2 = 0 <;> by_cases hv : v' % 2 = 0 <;> simp only [hu, hv, ↓reduceIte]
        · have hr : r.half.mem (u' / 2) (v' / 2) := by
            obtain ⟨a, b, c, d⟩ := hm'
            simp only [Rect.half, Rect.mem]; omega
          exact Rat.le_trans (ih r.half ⟨llq, restq⟩ ⟨llx, restx⟩ ε ⟨hll, crest⟩ hok1 _ _ hr) m1
        · exact Rat.le_trans (c2 _ _) m2
        · exact Rat.le_trans (c1 _ _) m2
        · exact Rat.le_trans (c3 _ _) m2

/-- An integer decomposition read as a rational one (the exact inputs `z`, in units of the
last fixed-point bit). -/
def castDec (d : Spec.DWT53.Dec) : Dec :=
  ⟨castG d.ll, d.details.map fun b => (castG b.1, castG b.2.1, castG b.2.2)⟩

theorem castDec_close (d : Spec.DWT53.Dec) : DecClose 0 d (castDec d) := by
  have hg : ∀ g : Spec.DWT53.Grid, GClose 0 g (castG g) := by
    intro g u v; simp [castG, Rat.sub_self]
  refine ⟨hg _, ?_⟩
  obtain ⟨_, det⟩ := d
  simp only [castDec]
  induction det with
  | nil => trivial
  | cons b rest ih => exact ⟨hg _, hg _, hg _, ih⟩

/-- **C8 (multi-level, exact fixed-point inputs)**: the inputs are the integers `z` of the
decomposition (a value `z` stands for `z / 2^F`); if no pass overflows, every output sample
of `qsrMulti` is within `En n 0` units of `2^−F` of `Spec.DWT97.srMulti` applied to the
exact inputs. -/
theorem qsrMulti_err_exact (n : Nat) (r : Rect) (d : Spec.DWT53.Dec) (hok : OkMulti r n d)
    (u v : Int) (hm : r.mem u v) :
    ((((qsrMulti r n d).get u v : Int) : Rat) - (srMulti r n (castDec d)).get u v).abs
      ≤ En n 0 :=
  qsrMulti_err n r d (castDec d) 0 (castDec_close d) hok u v hm

/-- **C8 for the inverse 9/7 (multi-level, `F` fractional bits)**: a fixed-point
decomposition `d` (each cell `z` standing for `z / 2^F`) is reconstructed by `qsrMulti`
(the arithmetic of the `Int32` kernel) within `En n 0 / 2^F` of the exact `Rat`
specification `Spec.DWT97.srMulti` applied to the exact inputs `z / 2^F`, at every sample of
the rectangle, for every number of levels, provided no 1-D pass overflows `Int32`. -/
theorem qsrMulti_err_frac (F n : Nat) (r : Rect) (d : Spec.DWT53.Dec) (hok : OkMulti r n d)
    (u v : Int) (hm : r.mem u v) :
    ((((qsrMulti r n d).get u v : Int) : Rat) / ((2 ^ F : Nat) : Rat)
      - (srMulti r n ((castDec d).smul (1 / ((2 ^ F : Nat) : Rat)))).get u v).abs
      ≤ En n 0 / ((2 ^ F : Nat) : Rat) := by
  have h := qsrMulti_err_exact n r d hok u v hm
  rw [srMulti_smul]
  have hD : (0 : Rat) < ((2 ^ F : Nat) : Rat) := by
    have : 0 < 2 ^ F := Nat.two_pow_pos F
    exact_mod_cast this
  generalize ((2 ^ F : Nat) : Rat) = D at hD ⊢
  generalize (((qsrMulti r n d).get u v : Int) : Rat) = a at h ⊢
  simp only [Grid.smul]
  generalize (srMulti r n (castDec d)).get u v = b at h ⊢
  have hk : (0 : Rat) ≤ 1 / D := by
    have := Rat.le_of_lt (Rat.inv_pos.mpr hD)
    rw [Rat.div_def, Rat.one_mul]; exact this
  have e : a / D - 1 / D * b = (a - b) * (1 / D) := by grind
  rw [e]
  have := abs_mul_le (a - b) (1 / D) (En n 0) h
  rw [Rat.abs_of_nonneg hk] at this
  have e2 : En n 0 * (1 / D) = En n 0 / D := by grind
  rw [e2] at this
  exact this

end JPEG2000.DWT97

namespace JPEG2000.DWT97

open JPEG2000.Bytes
open JPEG2000.Header (Rect)
open JPEG2000.DWT53 (Buf idx_lt lnb rnb loadRow storeRow loadCols storeCols batch halfN halfN_le
  toDec specRect ofGrid sat32)
open JPEG2000.Spec.DWT97 (srMulti)

/-- The error location of this module. -/
def loc : Location := .at .dwt

/-! ## Fixed-point 1-D kernel on `Int32` cells -/

/-- `round(K·2^30)` as `Int64`. -/ def kQ64 : Int64 := 1320889387
/-- `round((1/K)·2^30)` as `Int64`. -/ def invKQ64 : Int64 := 872837284
/-- `round(−δ·2^30)` as `Int64`. -/ def mDeltaQ64 : Int64 := -476211856
/-- `round(−γ·2^30)` as `Int64`. -/ def mGammaQ64 : Int64 := -948018549
/-- `round(−β·2^30)` as `Int64`. -/ def mBetaQ64 : Int64 := 56886969
/-- `round(−α·2^30)` as `Int64`. -/ def mAlphaQ64 : Int64 := 1703098782

/-- `rnd` in `Int64`: `(t + 2^29) >>> 30`. -/
@[inline] def rnd64 (t : Int64) : Int64 := (t + 536870912) >>> 30

/-- One fixed-point lifting pass over cells `[off, off + n)` (`n ≥ 2`), visiting
`i, i + 2, …`: `x += rnd(cq · (l + r))` with the neighbours mirrored at both ends (F-4), in
`Int64`; `ok` becomes `false` if a result does not fit in `Int32`. -/
def liftPass97 {N : Nat} (cq : Int64) (off n : Nat) (hN : off + n ≤ N) (hn : 2 ≤ n)
    (b : Buf N) (i : Nat) (ok : Bool) : Buf N × Bool :=
  if hi : i < n then
    let l := lnb i
    let r := rnb n i
    have hl : l < n := by simp only [l, lnb]; split <;> omega
    have hr : r < n := by simp only [r, rnb]; split <;> omega
    let xl := (b.get (off + l) (by omega)).toInt64
    let xr := (b.get (off + r) (by omega)).toInt64
    let xi := (b.get (off + i) (by omega)).toInt64
    let v : Int64 := xi + rnd64 (cq * (xl + xr))
    let w := v.toInt32
    liftPass97 cq off n hN hn (b.set (off + i) w (by omega)) (i + 2) (ok && w.toInt64 == v)
  else (b, ok)
termination_by n - i

/-- The fixed-point scaling pass over cells `[off, off + n)`, from `i`: `x := rnd(q · x)`
with `q = qe` at absolute even positions (`(par + i)` even) and `qo` at odd ones. -/
def scalePass97 {N : Nat} (qe qo : Int64) (par off n : Nat) (hN : off + n ≤ N)
    (b : Buf N) (i : Nat) (ok : Bool) : Buf N × Bool :=
  if hi : i < n then
    let q := if (par + i) % 2 = 0 then qe else qo
    let v : Int64 := rnd64 (q * (b.get (off + i) (by omega)).toInt64)
    let w := v.toInt32
    scalePass97 qe qo par off n hN (b.set (off + i) w (by omega)) (i + 1) (ok && w.toInt64 == v)
  else (b, ok)
termination_by n - i

/-- Fixed-point `1D_SR` (F.3.6 with F-7) in place on cells `[off, off + n)` holding
interleaved coefficients whose first has absolute parity `par`: length 1 at an odd position
is halved (`⌊y/2⌋`); length ≥ 2 runs the scaling, then δ (even), γ (odd), β (even),
α (odd). -/
def lift1d97 {N : Nat} (off n par : Nat) (hN : off + n ≤ N) (b : Buf N) (ok : Bool) :
    Buf N × Bool :=
  if hn : 2 ≤ n then
    let s0 := scalePass97 kQ64 invKQ64 par off n hN b 0 ok
    let s1 := liftPass97 mDeltaQ64 off n hN hn s0.1 (par % 2) s0.2
    let s2 := liftPass97 mGammaQ64 off n hN hn s1.1 ((par + 1) % 2) s1.2
    let s3 := liftPass97 mBetaQ64 off n hN hn s2.1 (par % 2) s2.2
    liftPass97 mAlphaQ64 off n hN hn s3.1 ((par + 1) % 2) s3.2
  else if h1 : n = 1 then
    if par % 2 = 1 then
      (b.set off (b.get off (by omega) >>> 1) (by omega), ok)
    else (b, ok)
  else (b, ok)

/-! ## Row and column passes, levels (the 5/3 loops of `JPEG2000.DWT53` with `lift1d97`) -/

/-- `HOR_SR` on rows `y, …, H − 1` of the level `[u0, u1) × [v0, v1)`. -/
def rowPass {N T : Nat} (pw : Nat) (hN : N = pw * (N / pw)) (u0 u1 H : Nat) (hW : u1 - u0 ≤ pw)
    (hH : H ≤ N / pw) (hT : u1 - u0 ≤ T) (P : Buf N) (tmp : Buf T) (ok : Bool) (y : Nat) :
    Buf N × Buf T × Bool :=
  if hy : y < H then
    let tmp := loadRow pw hN u0 u1 y hW (by omega) P hT tmp 0
    let (tmp, ok) := lift1d97 0 (u1 - u0) (u0 % 2) (by omega) tmp ok
    let P := storeRow pw hN (u1 - u0) y hW (by omega) tmp hT P 0
    rowPass pw hN u0 u1 H hW hH hT P tmp ok (y + 1)
  else (P, tmp, ok)
termination_by H - y

/-- Lifts the `bw` columns held in `tmp` (column `c` at `[c·H, c·H + H)`), from `c`. -/
def liftCols {T : Nat} (H par bw : Nat) (hT : bw * H ≤ T) (tmp : Buf T) (ok : Bool)
    (c : Nat) : Buf T × Bool :=
  if hc : c < bw then
    have : c * H + H ≤ bw * H := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hc
    let (tmp, ok) := lift1d97 (c * H) H par (by omega) tmp ok
    liftCols H par bw hT tmp ok (c + 1)
  else (tmp, ok)
termination_by bw - c

/-- `VER_SR` on columns `x, …, W − 1` of the level, in batches of up to `batch` columns. -/
def colPass {N T : Nat} (pw : Nat) (hN : N = pw * (N / pw)) (W v0 v1 : Nat) (hW : W ≤ pw)
    (hH : v1 - v0 ≤ N / pw) (hT : batch * (v1 - v0) ≤ T) (P : Buf N) (tmp : Buf T)
    (ok : Bool) (x : Nat) : Buf N × Buf T × Bool :=
  if hx : x < W then
    let bw := min batch (W - x)
    have hbw : bw * (v1 - v0) ≤ T :=
      Nat.le_trans (Nat.mul_le_mul_right _ (Nat.min_le_left _ _)) hT
    have hxb : x + bw ≤ pw := by omega
    let tmp := loadCols pw hN v0 v1 x bw hxb hH hbw P tmp 0 0
    let (tmp, ok) := liftCols (v1 - v0) (v0 % 2) bw hbw tmp ok 0
    let P := storeCols pw hN (v1 - v0) x bw hxb hH hbw tmp P 0 0
    have : 0 < bw := by simp only [bw, batch]; omega
    colPass pw hN W v0 v1 hW hH hT P tmp ok (x + bw)
  else (P, tmp, ok)
termination_by W - x

/-- Runs levels `k, k − 1, …, 1`. -/
def levels {N T : Nat} (tc : Rect) (pw : Nat) (hN : N = pw * (N / pw))
    (hpw : tc.x1 - tc.x0 ≤ pw) (hph : tc.y1 - tc.y0 ≤ N / pw)
    (hT : batch * (tc.y1 - tc.y0) ≤ T) (hT2 : tc.x1 - tc.x0 ≤ T) :
    Nat → Buf N → Buf T → Bool → Buf N × Bool
  | 0, P, _, ok => (P, ok)
  | k + 1, P, tmp, ok =>
    let r := halfN tc k
    have hr : r.x1 - r.x0 ≤ tc.x1 - tc.x0 ∧ r.y1 - r.y0 ≤ tc.y1 - tc.y0 := halfN_le tc k
    let (P, tmp, ok) := rowPass pw hN r.x0 r.x1 (r.y1 - r.y0) (by omega) (by omega) (by omega)
      P tmp ok 0
    let (P, tmp, ok) := colPass pw hN (r.x1 - r.x0) r.y0 r.y1 (by omega) (by omega)
      (Nat.le_trans (Nat.mul_le_mul_left _ hr.2) hT) P tmp ok 0
    levels tc pw hN hpw hph hT hT2 k P tmp ok

/-! ## Entry points -/

/-- The fractional bits `F` used for a component of bit depth `depth` (≤ 26): `26 − depth`.
With `F` bits the integer part has `31 − F = depth + 5` bits, enough for the worst-case
9/7 intermediate growth (worst-case `ℓ1` gain of every intermediate lifting value over
the image samples ≈ 4.85 per dimension, ≈ 23.5 in 2-D, computed offline from impulse
responses of forward + inverse) with a factor 2 margin for quantisation noise. Dequantisation (task
5.1) must deliver `round(value · 2^F)`. -/
def fracBits (depth : Nat) : Nat := 26 - depth

/-- Fast path: in-place fixed-point lifting; `none` if some intermediate value does not fit
`Int32`. `p` must be `(tc.x1 − tc.x0) × (tc.y1 − tc.y0)`. -/
def idwt97Fast (p : Plane) (tc : Rect) (nl : Nat) : Option Plane :=
  if hw : p.width = tc.x1 - tc.x0 ∧ p.height = tc.y1 - tc.y0 then
    if hz : p.width = 0 ∨ p.height = 0 then some p
    else
      let pw := p.width
      let N := pw * p.height
      have hpw : 0 < pw := by omega
      have hdiv : N / pw = p.height := by simp only [N]; rw [Nat.mul_div_cancel_left _ hpw]
      have hN : N = pw * (N / pw) := by rw [hdiv]
      let T := max pw (batch * p.height)
      let tmp : Buf T := ⟨Plane.zero T 1, Nat.mul_one T⟩
      let (P, ok) := levels tc pw hN (by omega) (by rw [hdiv]; omega)
        (by simp only [T]; rw [← hw.2]; exact Nat.le_max_right _ _)
        (by simp only [T]; omega) nl ⟨p, rfl⟩ tmp true
      if ok then some P.1 else none
  else none

/-- Round to nearest (ties up). -/
def roundRat (x : Rat) : Int := (x + 1 / 2).floor

/-- Slow path: the exact `Rat` specification `Spec.DWT97.srMulti` on the cells (read as
exact rationals, in units of `2^−F`), rounded to the nearest integer and saturated to
`Int32`. -/
def idwt97Spec (p : Plane) (tc : Rect) (nl : Nat) : Plane :=
  let g := srMulti (specRect tc) nl (castDec (toDec p tc nl))
  let g' := Spec.DWT97.memo (specRect tc) g
  ofGrid ⟨fun u v => roundRat (g'.get u v)⟩ tc.x0 tc.y0 p.width p.height

/-- The fixed-point model `qsrMulti` on the cells (what the fast path computes; tests
check `idwt97Fast = idwt97Model`). -/
def idwt97Model (p : Plane) (tc : Rect) (nl : Nat) : Plane :=
  ofGrid (qsrMulti (specRect tc) nl (toDec p tc nl)) tc.x0 tc.y0 p.width p.height

/-- `IDWT` (F.3.1) with the 9/7 irreversible filter on one tile-component: `p` holds the
sub-bands of `nl` levels in the Mallat layout (as `JPEG2000.DWT53.idwt53`), each cell a
fixed-point value with `F` fractional bits (`fracBits`); the result holds the reconstructed
samples with the same `F`. Fast `Int32` lifting with 30-bit constants (error bound `En nl 0`
units of `2^−F`, theorem C8 `qsrMulti_err_exact`), falling back to the exact `Rat`
specification when an intermediate value would overflow. Errors when the plane's size
differs from `tc`'s. -/
def idwt97 (p : Plane) (tc : Rect) (nl : Nat) : Except Error Plane :=
  if p.width = tc.x1 - tc.x0 ∧ p.height = tc.y1 - tc.y0 then
    match idwt97Fast p tc nl with
    | some q => .ok q
    | none => .ok (idwt97Spec p tc nl)
  else .error (.malformed loc
    s!"DWT plane {p.width}×{p.height} differs from tile-component {tc.x1 - tc.x0}×{tc.y1 - tc.y0}")

end JPEG2000.DWT97

namespace JPEG2000.DWT97

open JPEG2000.Bytes
open JPEG2000.DWT53 (Buf lnb rnb narrow_exact sym_left sym_right)
open JPEG2000.Spec.DWT53 (pse pse_mem pse_id)
open JPEG2000.Spec.DWT97 (K delta gamma beta alpha abs_le_iff)

section KernelProof

/-- `>>> 30` on `Int64` is floor division by `2^30`. -/
private theorem shr30 (x : Int64) : (x >>> 30).toInt = x.toInt / 1073741824 := by
  show (Int64.shiftRight x 30).toInt = _
  simp only [Int64.shiftRight, BitVec.sshiftRight']
  rw [← Int64.toInt_toBitVec]
  show (BitVec.sshiftRight _ _).toInt = _
  rw [BitVec.toInt_sshiftRight, Int64.toInt_toBitVec, Int.shiftRight_eq_div_pow]
  rfl

/-- `>>> 1` on `Int32` is floor division by 2. -/
private theorem shr1_32 (x : Int32) : (x >>> 1).toInt = x.toInt / 2 := by
  show (Int32.shiftRight x 1).toInt = _
  simp only [Int32.shiftRight, BitVec.sshiftRight']
  rw [← Int32.toInt_toBitVec]
  show (BitVec.sshiftRight _ _).toInt = _
  rw [BitVec.toInt_sshiftRight, Int32.toInt_toBitVec, Int.shiftRight_eq_div_pow]
  rfl

/-- `bmod 2^64` is the identity on `[−2^63, 2^63)`. -/
private theorem bm64 (z : Int) (h1 : -9223372036854775808 ≤ z) (h2 : z < 9223372036854775808) :
    z.bmod (2^64) = z := by
  apply Int.bmod_eq_of_le <;> omega

/-- `|c| ≤ A`, `0 ≤ s ≤ B` ⇒ `|c·s| ≤ A·B`. -/
private theorem mul_bound_nn (c s A B : Int) (hA : 0 ≤ A) (hc1 : -A ≤ c) (hc2 : c ≤ A)
    (hs : 0 ≤ s) (hs2 : s ≤ B) : -(A * B) ≤ c * s ∧ c * s ≤ A * B := by
  have h1 := Int.mul_le_mul_of_nonneg_right hc2 hs
  have h2 := Int.mul_le_mul_of_nonneg_left hs2 hA
  have h3 := Int.mul_le_mul_of_nonneg_right hc1 hs
  rw [Int.neg_mul] at h3
  omega

/-- `|c| ≤ A`, `|s| ≤ B` ⇒ `|c·s| ≤ A·B`. -/
private theorem mul_bound (c s A B : Int) (hA : 0 ≤ A) (hc1 : -A ≤ c) (hc2 : c ≤ A)
    (hs1 : -B ≤ s) (hs2 : s ≤ B) : -(A * B) ≤ c * s ∧ c * s ≤ A * B := by
  by_cases hs : 0 ≤ s
  · exact mul_bound_nn c s A B hA hc1 hc2 hs hs2
  · have h := mul_bound_nn c (-s) A B hA hc1 hc2 (by omega) (by omega)
    rw [Int.mul_neg] at h
    omega

/-- The `Int64` lifting step on `Int32` operands is exact (no `Int64` overflow) for every
constant `|cq| < 2^31`. -/
theorem liftStep_exact (cq : Int64) (hc1 : -2147483647 ≤ cq.toInt) (hc2 : cq.toInt ≤ 2147483647)
    (a b c : Int32) :
    (c.toInt64 + rnd64 (cq * (a.toInt64 + b.toInt64))).toInt
      = c.toInt + rnd (cq.toInt * (a.toInt + b.toInt)) := by
  have ha1 := a.toInt_lt; have ha2 := a.le_toInt
  have hb1 := b.toInt_lt; have hb2 := b.le_toInt
  have hc1' := c.toInt_lt; have hc2' := c.le_toInt
  unfold rnd64 rnd
  rw [Int64.toInt_add, shr30, Int64.toInt_add, Int64.toInt_mul, Int64.toInt_add,
    Int32.toInt_toInt64, Int32.toInt_toInt64, Int32.toInt_toInt64]
  have h5 : (536870912 : Int64).toInt = 536870912 := rfl
  rw [h5, bm64 (a.toInt + b.toInt) (by omega) (by omega)]
  have hm := mul_bound cq.toInt (a.toInt + b.toInt) 2147483647 4294967296 (by omega) hc1 hc2
    (by omega) (by omega)
  generalize cq.toInt * (a.toInt + b.toInt) = z at hm ⊢
  rw [bm64 z (by omega) (by omega), bm64 (z + 536870912) (by omega) (by omega)]
  rw [bm64 _ (by omega) (by omega)]

/-- The `Int64` scaling step on an `Int32` operand is exact for `|q| < 2^31`. -/
theorem scaleStep_exact (q : Int64) (hq1 : -2147483647 ≤ q.toInt) (hq2 : q.toInt ≤ 2147483647)
    (c : Int32) : (rnd64 (q * c.toInt64)).toInt = rnd (q.toInt * c.toInt) := by
  have hc1 := c.toInt_lt; have hc2 := c.le_toInt
  unfold rnd64 rnd
  rw [shr30, Int64.toInt_add, Int64.toInt_mul, Int32.toInt_toInt64]
  have h5 : (536870912 : Int64).toInt = 536870912 := rfl
  rw [h5]
  have hm := mul_bound q.toInt c.toInt 2147483647 2147483648 (by omega) hq1 hq2
    (by omega) (by omega)
  generalize q.toInt * c.toInt = z at hm ⊢
  rw [bm64 z (by omega) (by omega), bm64 (z + 536870912) (by omega) (by omega)]

/-- The value one fixed-point lifting pass writes at position `k` from the values `g`. -/
def passVal97 (cq : Int) (n : Nat) (g : Nat → Int) (k : Nat) : Int :=
  g k + rnd (cq * (g (lnb k) + g (rnb n k)))

/-- The lifting pass's flag only goes from `true` to `false`. -/
private theorem liftPass97_ok {N : Nat} (cq : Int64) (off n : Nat) (hN : off + n ≤ N) (hn : 2 ≤ n)
    (b : Buf N) (i : Nat) (ok : Bool) (h : (liftPass97 cq off n hN hn b i ok).2 = true) :
    ok = true := by
  rw [liftPass97] at h
  split at h
  · have := liftPass97_ok cq off n hN hn _ _ _ h
    simp only [Bool.and_eq_true] at this
    exact this.1
  · exact h
termination_by n - i

/-- The scaling pass's flag only goes from `true` to `false`. -/
private theorem scalePass97_ok {N : Nat} (qe qo : Int64) (par off n : Nat) (hN : off + n ≤ N)
    (b : Buf N) (i : Nat) (ok : Bool) (h : (scalePass97 qe qo par off n hN b i ok).2 = true) :
    ok = true := by
  rw [scalePass97] at h
  split at h
  · have := scalePass97_ok qe qo par off n hN _ _ _ h
    simp only [Bool.and_eq_true] at this
    exact this.1
  · exact h
termination_by n - i

/-- One lifting pass, when its flag stays `true`, writes `passVal97` (computed from the
values before the pass) at every position of its class and leaves the others. -/
theorem liftPass97_spec {N : Nat} (cq : Int64) (hc1 : -2147483647 ≤ cq.toInt)
    (hc2 : cq.toInt ≤ 2147483647) (off n : Nat) (hN : off + n ≤ N) (hn : 2 ≤ n)
    (g : Nat → Int) (b : Buf N) (i : Nat) (ok : Bool)
    (H : ∀ k (hk : k < n), (b.get (off + k) (by omega)).toInt =
      if k % 2 = i % 2 ∧ k < i then passVal97 cq.toInt n g k else g k)
    (hok : (liftPass97 cq off n hN hn b i ok).2 = true) :
    ∀ k (hk : k < n), ((liftPass97 cq off n hN hn b i ok).1.get (off + k) (by omega)).toInt =
      if k % 2 = i % 2 then passVal97 cq.toInt n g k else g k := by
  rw [liftPass97] at hok ⊢
  split
  · rename_i hi
    simp only [hi, ↓reduceDIte] at hok
    have hok0 := liftPass97_ok cq off n hN hn _ _ _ hok
    simp only [Bool.and_eq_true, beq_iff_eq] at hok0
    have hrec := liftPass97_spec cq hc1 hc2 off n hN hn g _ (i + 2) _ ?_ hok
    · intro k hk
      rw [hrec k hk]
      simp only [Nat.add_mod_right]
    · intro k hk
      rw [JPEG2000.DWT53.Buf.get_set]
      by_cases hki : off + i = off + k
      · have hk' : k = i := by omega
        subst hk'
        simp only [↓reduceIte, Nat.add_mod_right, Nat.lt_add_right_iff_pos, and_self,
          show 0 < 2 by omega]
        rw [narrow_exact _ hok0.2]
        have hl := H (lnb k) (by unfold lnb; split <;> omega)
        have hr := H (rnb n k) (by unfold rnb; split <;> omega)
        have hc := H k hk
        have hpl : ¬ (lnb k % 2 = k % 2 ∧ lnb k < k) := by unfold lnb; split <;> omega
        have hpr : ¬ (rnb n k % 2 = k % 2 ∧ rnb n k < k) := by unfold rnb; split <;> omega
        simp only [hpl, hpr, Nat.lt_irrefl, and_false, ↓reduceIte] at hl hr hc
        simp only [passVal97]
        rw [liftStep_exact cq hc1 hc2, hl, hr, hc]
      · simp only [hki, ↓reduceIte]
        rw [H k hk]
        have hne : k ≠ i := by omega
        by_cases hp : k % 2 = i % 2
        · have : k < i ↔ k < i + 2 := by omega
          simp only [hp, Nat.add_mod_right, true_and, this]
        · simp only [hp, Nat.add_mod_right, false_and]
  · rename_i hi
    intro k hk
    rw [H k hk]
    by_cases hp : k % 2 = i % 2
    · simp only [hp, true_and, show k < i by omega, ↓reduceIte]
    · simp only [hp, false_and, ↓reduceIte]
termination_by n - i

/-- The value the scaling pass writes at position `k`. -/
def scaleVal97 (qe qo : Int) (par : Nat) (g : Nat → Int) (k : Nat) : Int :=
  rnd ((if (par + k) % 2 = 0 then qe else qo) * g k)

/-- The scaling pass, when its flag stays `true`, writes `scaleVal97` at every position. -/
theorem scalePass97_spec {N : Nat} (qe qo : Int64) (he1 : -2147483647 ≤ qe.toInt)
    (he2 : qe.toInt ≤ 2147483647) (ho1 : -2147483647 ≤ qo.toInt) (ho2 : qo.toInt ≤ 2147483647)
    (par off n : Nat) (hN : off + n ≤ N) (g : Nat → Int) (b : Buf N) (i : Nat) (ok : Bool)
    (H : ∀ k (hk : k < n), (b.get (off + k) (by omega)).toInt =
      if k < i then scaleVal97 qe.toInt qo.toInt par g k else g k)
    (hok : (scalePass97 qe qo par off n hN b i ok).2 = true) :
    ∀ k (hk : k < n), ((scalePass97 qe qo par off n hN b i ok).1.get (off + k) (by omega)).toInt =
      scaleVal97 qe.toInt qo.toInt par g k := by
  rw [scalePass97] at hok ⊢
  split
  · rename_i hi
    simp only [hi, ↓reduceDIte] at hok
    have hok0 := scalePass97_ok qe qo par off n hN _ _ _ hok
    simp only [Bool.and_eq_true, beq_iff_eq] at hok0
    apply scalePass97_spec qe qo he1 he2 ho1 ho2 par off n hN g _ (i + 1) _ ?_ hok
    intro k hk
    rw [JPEG2000.DWT53.Buf.get_set]
    by_cases hki : off + i = off + k
    · have hk' : k = i := by omega
      subst hk'
      simp only [↓reduceIte, Nat.lt_add_one]
      rw [narrow_exact _ hok0.2]
      have hc := H k hk
      simp only [Nat.lt_irrefl, ↓reduceIte] at hc
      simp only [scaleVal97]
      split
      · rw [scaleStep_exact qe he1 he2, hc]
      · rw [scaleStep_exact qo ho1 ho2, hc]
    · simp only [hki, ↓reduceIte]
      rw [H k hk]
      have : k < i ↔ k < i + 1 := by omega
      simp only [this]
  · rename_i hi
    intro k hk
    rw [H k hk]
    simp only [show k < i by omega, ↓reduceIte]
termination_by n - i

/-! ### From passes to the fixed-point model -/

open JPEG2000.Spec.DWT53 (Sym)

/-- A fixed-point step preserves the symmetries of an integer signal. -/
private theorem QStep.apply_sym {i0 L : Int} {f : Int → Int} (s : QStep) (h : Sym i0 L f) :
    Sym i0 L (s.apply f) := by
  obtain ⟨hm, hper⟩ := h
  cases s with
  | lifting p c cq =>
    constructor
    · intro j
      simp only [QStep.apply]
      have e1 : 2 * i0 - j - 1 = 2 * i0 - (j + 1) := by omega
      have e2 : 2 * i0 - j + 1 = 2 * i0 - (j - 1) := by omega
      have hpar : (2 * i0 - j) % 2 = p ↔ j % 2 = p := by omega
      rw [e1, e2, hm, hm, hm]
      by_cases hj : j % 2 = p
      · simp only [hj, hpar.mpr hj, ↓reduceIte, Int.add_comm (f (j + 1))]
      · have : ¬ (2 * i0 - j) % 2 = p := fun h => hj (hpar.mp h)
        simp only [hj, this, ↓reduceIte]
    · intro j
      simp only [QStep.apply]
      have e1 : j + 2 * L - 1 = (j - 1) + 2 * L := by omega
      have e2 : j + 2 * L + 1 = (j + 1) + 2 * L := by omega
      have hpar : (j + 2 * L) % 2 = p ↔ j % 2 = p := by omega
      rw [e1, e2, hper, hper, hper]
      by_cases hj : j % 2 = p
      · simp only [hj, hpar.mpr hj, ↓reduceIte]
      · have : ¬ (j + 2 * L) % 2 = p := fun h => hj (hpar.mp h)
        simp only [hj, this, ↓reduceIte]
  | scaling ce co qe qo =>
    constructor
    · intro j
      simp only [QStep.apply]
      have hpar : (2 * i0 - j) % 2 = 0 ↔ j % 2 = 0 := by omega
      rw [hm]
      by_cases hj : j % 2 = 0
      · simp only [hj, hpar.mpr hj, ↓reduceIte]
      · have : ¬ (2 * i0 - j) % 2 = 0 := fun h => hj (hpar.mp h)
        simp only [hj, this, ↓reduceIte]
    · intro j
      simp only [QStep.apply]
      have hpar : (j + 2 * L) % 2 = 0 ↔ j % 2 = 0 := by omega
      rw [hper]
      by_cases hj : j % 2 = 0
      · simp only [hj, hpar.mpr hj, ↓reduceIte]
      · have : ¬ (j + 2 * L) % 2 = 0 := fun h => hj (hpar.mp h)
        simp only [hj, this, ↓reduceIte]

/-- A lifting pass computes the fixed-point lifting step of the model on its range. -/
private theorem liftPass97_model {N : Nat} (cq : Int64) (hc1 : -2147483647 ≤ cq.toInt)
    (hc2 : cq.toInt ≤ 2147483647) (p : Int) (c : Rat) (off n : Nat) (hN : off + n ≤ N)
    (hn : 2 ≤ n) (b : Buf N) (ok : Bool) (i0 : Int) (st : Nat) (hst : st < 2)
    (hpst : (i0 + st) % 2 = p) (f : Int → Int) (hf : Sym i0 ((n : Int) - 1) f)
    (hb : ∀ k (hk : k < n), (b.get (off + k) (by omega)).toInt = f (i0 + k))
    (hok : (liftPass97 cq off n hN hn b st ok).2 = true) :
    ∀ k (hk : k < n), ((liftPass97 cq off n hN hn b st ok).1.get (off + k) (by omega)).toInt =
      (QStep.lifting p c cq.toInt).apply f (i0 + k) := by
  intro k hk
  rw [liftPass97_spec cq hc1 hc2 off n hN hn (fun m => f (i0 + m)) b st ok (by
    intro m hm
    rw [hb m hm]
    have : ¬ (m % 2 = st % 2 ∧ m < st) := by omega
    simp only [this, ↓reduceIte]) hok k hk]
  simp only [QStep.apply]
  by_cases hk2 : k % 2 = st % 2
  · have : (i0 + (k : Int)) % 2 = p := by omega
    simp only [hk2, this, ↓reduceIte, passVal97]
    rw [sym_left hf k hk, sym_right hf hn k hk]
  · have : ¬ (i0 + (k : Int)) % 2 = p := by omega
    simp only [hk2, this, ↓reduceIte]

/-- The scaling pass computes the fixed-point scaling step of the model on its range. -/
private theorem scalePass97_model {N : Nat} (qe qo : Int64) (he1 : -2147483647 ≤ qe.toInt)
    (he2 : qe.toInt ≤ 2147483647) (ho1 : -2147483647 ≤ qo.toInt) (ho2 : qo.toInt ≤ 2147483647)
    (ce co : Rat) (par off n : Nat) (hN : off + n ≤ N) (b : Buf N) (ok : Bool) (i0 : Int)
    (hpar : i0 % 2 = (par % 2 : Nat)) (f : Int → Int)
    (hb : ∀ k (hk : k < n), (b.get (off + k) (by omega)).toInt = f (i0 + k))
    (hok : (scalePass97 qe qo par off n hN b 0 ok).2 = true) :
    ∀ k (hk : k < n), ((scalePass97 qe qo par off n hN b 0 ok).1.get (off + k) (by omega)).toInt =
      (QStep.scaling ce co qe.toInt qo.toInt).apply f (i0 + k) := by
  intro k hk
  rw [scalePass97_spec qe qo he1 he2 ho1 ho2 par off n hN (fun m => f (i0 + m)) b 0 ok (by
    intro m hm
    rw [hb m hm]
    simp only [Nat.not_lt_zero, ↓reduceIte]) hok k hk]
  simp only [QStep.apply, scaleVal97]
  by_cases h : (par + k) % 2 = 0
  · have : (i0 + (k : Int)) % 2 = 0 := by omega
    simp only [h, this, ↓reduceIte]
  · have : ¬ (i0 + (k : Int)) % 2 = 0 := by omega
    simp only [h, this, ↓reduceIte]

/-- A symmetric signal whose values on the range are `Int32` cells is bounded by `2^31`
everywhere. -/
private theorem cells_bound {N : Nat} (off n : Nat) (hN : off + n ≤ N) (hn : 2 ≤ n) (b : Buf N)
    (i0 : Int) (f : Int → Int) (hf : Sym i0 ((n : Int) - 1) f)
    (hb : ∀ k (hk : k < n), (b.get (off + k) (by omega)).toInt = f (i0 + k)) :
    ∀ j, ((f j : Int) : Rat).abs ≤ M32 := by
  intro j
  have hl : i0 + 2 ≤ i0 + (n : Int) := by omega
  have hf' : Sym i0 (i0 + (n : Int) - i0 - 1) f := by
    rw [show i0 + (n : Int) - i0 - 1 = (n : Int) - 1 by omega]; exact hf
  rw [← JPEG2000.Spec.DWT53.sym_pse hl hf' j]
  have hm := pse_mem hl j
  have e : pse i0 (i0 + n) j = i0 + ((pse i0 (i0 + n) j - i0).toNat : Nat) := by omega
  rw [e, ← hb _ (by omega)]
  generalize b.get _ _ = v
  have h1 := v.toInt_lt; have h2 := v.le_toInt
  have h1' := Rat.intCast_lt_intCast.mpr h1
  have h2' := Rat.intCast_le_intCast.mpr h2
  simp only [M32]
  apply abs_le_iff.mpr
  constructor <;> grind

/-- **Fast = model, 1-D kernel.** If `lift1d97` keeps its flag, every cell holds exactly the
fixed-point model `qsr1d` of the input cells (every length, offset and start parity), and
no intermediate value of the model exceeds `2^31` (`Ok1d`), so C8 (`qsr1d_err`) applies. -/
theorem lift1d97_eq {N : Nat} (off n par : Nat) (hN : off + n ≤ N) (b : Buf N) (ok : Bool)
    (i0 : Int) (hpar : i0 % 2 = (par % 2 : Nat)) (y : Int → Int)
    (hy : ∀ k (hk : k < n), (b.get (off + k) (by omega)).toInt = y (i0 + k))
    (hok : (lift1d97 off n par hN b ok).2 = true) :
    (∀ k (hk : k < n), ((lift1d97 off n par hN b ok).1.get (off + k) (by omega)).toInt =
      qsr1d i0 (i0 + n) y (i0 + k)) ∧ Ok1d i0 (i0 + n) y := by
  by_cases hn : 2 ≤ n
  · simp only [lift1d97, hn, ↓reduceDIte] at hok ⊢
    have hl : i0 + 2 ≤ i0 + (n : Int) := by omega
    let f0 := qext i0 (i0 + n) y
    have hS0 : Sym i0 ((n : Int) - 1) f0 := by
      have := JPEG2000.Spec.DWT53.ext_sym hl y
      rw [show i0 + (n : Int) - i0 - 1 = (n : Int) - 1 by omega] at this
      exact this
    have hb0 : ∀ k (hk : k < n), (b.get (off + k) (by omega)).toInt = f0 (i0 + k) := by
      intro k hk
      rw [hy k hk]; simp only [f0, qext]; rw [pse_id (by omega) (by omega)]
    let qS := QStep.scaling K (1 / K) kQ invKQ
    let qD := QStep.lifting 0 (-delta) mDeltaQ
    let qG := QStep.lifting 1 (-gamma) mGammaQ
    let qB := QStep.lifting 0 (-beta) mBetaQ
    let qA := QStep.lifting 1 (-alpha) mAlphaQ
    let f1 := qS.apply f0
    let f2 := qD.apply f1
    let f3 := qG.apply f2
    let f4 := qB.apply f3
    have hS1 : Sym i0 ((n : Int) - 1) f1 := QStep.apply_sym _ hS0
    have hS2 : Sym i0 ((n : Int) - 1) f2 := QStep.apply_sym _ hS1
    have hS3 : Sym i0 ((n : Int) - 1) f3 := QStep.apply_sym _ hS2
    have hS4 : Sym i0 ((n : Int) - 1) f4 := QStep.apply_sym _ hS3
    -- the passes and their flags
    let s0 := scalePass97 kQ64 invKQ64 par off n hN b 0 ok
    let s1 := liftPass97 mDeltaQ64 off n hN hn s0.1 (par % 2) s0.2
    let s2 := liftPass97 mGammaQ64 off n hN hn s1.1 ((par + 1) % 2) s1.2
    let s3 := liftPass97 mBetaQ64 off n hN hn s2.1 (par % 2) s2.2
    have ok3 : s3.2 = true := liftPass97_ok _ _ _ _ _ _ _ _ hok
    have ok2 : s2.2 = true := liftPass97_ok _ _ _ _ _ _ _ _ ok3
    have ok1 : s1.2 = true := liftPass97_ok _ _ _ _ _ _ _ _ ok2
    have ok0 : s0.2 = true := liftPass97_ok _ _ _ _ _ _ _ _ ok1
    have hb1 : ∀ k (hk : k < n), (s0.1.get (off + k) (by omega)).toInt = f1 (i0 + k) :=
      scalePass97_model kQ64 invKQ64 (by decide) (by decide) (by decide) (by decide) K (1 / K)
        par off n hN b ok i0 hpar f0 hb0 ok0
    have hb2 : ∀ k (hk : k < n), (s1.1.get (off + k) (by omega)).toInt = f2 (i0 + k) :=
      liftPass97_model mDeltaQ64 (by decide) (by decide) 0 (-delta) off n hN hn s0.1 s0.2 i0
        (par % 2) (by omega) (by omega) f1 hS1 hb1 ok1
    have hb3 : ∀ k (hk : k < n), (s2.1.get (off + k) (by omega)).toInt = f3 (i0 + k) :=
      liftPass97_model mGammaQ64 (by decide) (by decide) 1 (-gamma) off n hN hn s1.1 s1.2 i0
        ((par + 1) % 2) (by omega) (by omega) f2 hS2 hb2 ok2
    have hb4 : ∀ k (hk : k < n), (s3.1.get (off + k) (by omega)).toInt = f4 (i0 + k) :=
      liftPass97_model mBetaQ64 (by decide) (by decide) 0 (-beta) off n hN hn s2.1 s2.2 i0
        (par % 2) (by omega) (by omega) f3 hS3 hb3 ok3
    have hb5 := liftPass97_model mAlphaQ64 (by decide) (by decide) 1 (-alpha) off n hN hn s3.1
      s3.2 i0 ((par + 1) % 2) (by omega) (by omega) f4 hS4 hb4 hok
    constructor
    · intro k hk
      rw [hb5 k hk]
      simp only [qsr1d, show ¬ i0 + (n : Int) ≤ i0 by omega,
        show ¬ i0 + (n : Int) = i0 + 1 by omega, ↓reduceIte]
      rfl
    · intro _
      exact ⟨cells_bound off n hN hn b i0 f0 hS0 hb0,
        cells_bound off n hN hn s0.1 i0 f1 hS1 hb1,
        cells_bound off n hN hn s1.1 i0 f2 hS2 hb2,
        cells_bound off n hN hn s2.1 i0 f3 hS3 hb3,
        cells_bound off n hN hn s3.1 i0 f4 hS4 hb4, trivial⟩
  · refine ⟨?_, fun h => absurd h (by omega)⟩
    intro k hk
    have hn' : n = 1 := by omega
    subst hn'
    have hk0 : k = 0 := by omega
    subst hk0
    simp only [qsr1d,
      show i0 + ((1 : Nat) : Int) = i0 + 1 by omega, ↓reduceIte]
    simp only [lift1d97, show ¬ 2 ≤ 1 by omega, ↓reduceDIte]
    have hy0 := hy 0 (by omega)
    simp only [Nat.add_zero] at hy0
    simp only [Nat.add_zero]
    by_cases hp : par % 2 = 1
    · have : ¬ i0 % 2 = 0 := by omega
      simp only [hp, ↓reduceIte, this, JPEG2000.DWT53.Buf.get_set]
      rw [shr1_32, hy0]
      simp only [show ¬ i0 + 1 ≤ i0 by omega, ↓reduceIte]
    · have : i0 % 2 = 0 := by omega
      simp only [hp, ↓reduceIte, this]
      rw [hy0]
      simp only [show ¬ i0 + 1 ≤ i0 by omega, ↓reduceIte]

end KernelProof

end JPEG2000.DWT97
