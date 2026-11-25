import Spec.DWT53

/-!
# Irreversible 9/7 wavelet: exact `Rat` specification, round trip, error calculus

Plan.md §4 (C8), §5.2 "DWT", §5.4; T.800 Annex F:

* F.3.1/F.3.2 `IDWT` / `2D_SR`: one level = `2D_INTERLEAVE` (F.3.3), then `HOR_SR` (F.3.4)
  and `VER_SR` (F.3.5) — the same composition as the 5/3 (`Spec.DWT53`).
* F.3.6 `1D_SR`: a length-1 signal is copied (even start) or halved, `Y/2` (odd start);
  otherwise `1D_EXTR` (F.3.7, periodic symmetric extension F-4, `Spec.DWT53.pse`) followed by
  `1D_FILTR_9-7I` (F.3.8.2, equations F-7): STEP1 `X(2n) = K·Y(2n)`, STEP2
  `X(2n+1) = (1/K)·Y(2n+1)`, STEP3 `X(2n) −= δ·(X(2n−1) + X(2n+1))`, STEP4
  `X(2n+1) −= γ·(X(2n) + X(2n+2))`, STEP5 `X(2n) −= β·(…)`, STEP6 `X(2n+1) −= α·(…)`.
* F.4 forward transform (reference encoder, tests): `1D_SD` (F.4.6: length 1 copied at an
  even start, doubled at an odd one), `1D_FILTD_9-7I` (F.4.8.2, equations F-8): `+α` on odd,
  `+β` on even, `+γ` on odd, `+δ` on even, then odd `·K`, even `·(1/K)`.

## The constants

T.800 derives α, β, γ, δ, K from the Daubechies 9/7 factorisation (they are irrational) and
prints them in Table F.4 as decimals: α = −1.586134342059924, β = −0.052980118572961,
γ = 0.882911075530934, δ = 0.443506852043971, K = 1.230174104914001. **This specification
takes these decimal values, read as exact rationals, as the definition of the filter.** The
orientation (low-pass `·K`, high-pass `·(1/K)` on synthesis) was checked against OpenJPEG
`opj_v8dwt_decode`, which uses `K` and `2/K` because its dequantisation uses gain 0 for every
band; T.800's Table E-1 gains (task 5.1, `Spec.Quant`) with `1/K` give the same samples. For
a length-1 high-pass signal OpenJPEG leaves the sample unchanged — again the same as T.800's
`Y/2` under its gain convention.

## Formulation

As in `Spec.DWT53`, signals are total functions `Int → Rat` indexed by absolute coordinate,
the extension is `ext i0 i1 x = x ∘ pse` and every step acts pointwise on the whole line.
The six steps are data (`Step`: a lifting step `lift p c` on parity class `p`, or a
per-parity scaling), and a 1-D filter is a `chain` of steps. Each lifting step is undone by
the step with `−c` and the scaling by the inverse scaling, so `sr1d_sd1d` (inverse ∘ forward
= identity, every range, every parity) holds exactly over `Rat` with the decimal constants;
2-D (`sr2d_sd2d`) and multi-level (`srMulti_sdMulti`) follow as for the 5/3.

## Error calculus (used by C8 in `JPEG2000.DWT97`)

Chains are linear (`chain_add`, `chain_smul`), local (`chain_local`: radius = number of
steps) and invariant under even translations (`chain_shift2`). Hence a chain is a
convolution with its impulse responses (`chain_eq_wsum`) and `chain_bound` gives the sharp
per-sample `ℓ∞` bound `gb l j bnd = Σ_k bnd k · |chain l (δ_k) j|` (cancellations between
the lifting paths are kept, which matters: the 1-D inverse 9/7 has gain ≈ 2.18, while
propagating bounds step by step gives ≈ 11.9). A perturbed chain (`pert`: after step `i` a
residual `r_i` is added) splits as `chain` of the input plus `pert` of zero
(`pert_eq`), bounded by `injBound` (`pert_zero_bound`).
-/

namespace JPEG2000.Spec.DWT97

open JPEG2000.Spec.DWT53 (pse pse_mem pse_id Rect)

/-! ## Constants (T.800 Table F.4, read as exact rationals) -/

/-- α of Table F.4. -/
def alpha : Rat := -1.586134342059924
/-- β of Table F.4. -/
def beta : Rat := -0.052980118572961
/-- γ of Table F.4. -/
def gamma : Rat := 0.882911075530934
/-- δ of Table F.4. -/
def delta : Rat := 0.443506852043971
/-- K of Table F.4. -/
def K : Rat := 1.230174104914001

/-- `K ≠ 0`. -/
theorem K_ne_zero : K ≠ 0 := by unfold K; grind

/-! ## Signals and steps -/

/-- A one-dimensional signal indexed by absolute coordinate. -/
abbrev Sig := Int → Rat

/-- A lifting step on parity class `p` (0 or 1): `f j + c·(f (j−1) + f (j+1))` at the
indices `j ≡ p (mod 2)`, unchanged elsewhere. -/
def lift (p : Int) (c : Rat) (f : Sig) : Sig := fun j =>
  if j % 2 = p then f j + c * (f (j - 1) + f (j + 1)) else f j

/-- Scaling: even indices times `ce`, odd indices times `co`. -/
def scale (ce co : Rat) (f : Sig) : Sig := fun j =>
  if j % 2 = 0 then ce * f j else co * f j

/-- One step of a lifting filter. -/
inductive Step where
  /-- `lift p c`. -/
  | lifting (p : Int) (c : Rat)
  /-- `scale ce co`. -/
  | scaling (ce co : Rat)

/-- The action of a step on a signal. -/
def Step.apply : Step → Sig → Sig
  | .lifting p c, f => lift p c f
  | .scaling ce co, f => scale ce co f

/-- A sequence of steps, applied first to last. -/
def chain : List Step → Sig → Sig
  | [], f => f
  | s :: l, f => chain l (s.apply f)

/-- `1D_FILTR_9-7I` (F-7): STEP1/2 scaling by `K`, `1/K`, then δ (even), γ (odd), β (even),
α (odd), each subtracted. -/
def invSteps : List Step :=
  [.scaling K (1 / K), .lifting 0 (-delta), .lifting 1 (-gamma), .lifting 0 (-beta),
    .lifting 1 (-alpha)]

/-- `1D_FILTD_9-7I` (F-8): α (odd), β (even), γ (odd), δ (even), then odd `·K`, even
`·(1/K)`. -/
def fwdSteps : List Step :=
  [.lifting 1 alpha, .lifting 0 beta, .lifting 1 gamma, .lifting 0 delta, .scaling (1 / K) K]

/-- The lifting step with `−c` undoes the step with `c`. -/
private theorem lift_neg_lift (p : Int) (c : Rat) (f : Sig) :
    lift p (-c) (lift p c f) = f := by
  funext j
  simp only [lift]
  by_cases h : j % 2 = p
  · have h1 : ¬ (j - 1) % 2 = p := by omega
    have h2 : ¬ (j + 1) % 2 = p := by omega
    simp only [h, h1, h2, ↓reduceIte]
    grind
  · simp only [h, ↓reduceIte]

/-- The inverse scaling undoes the forward scaling. -/
private theorem scale_inv_scale (f : Sig) : scale K (1 / K) (scale (1 / K) K f) = f := by
  funext j
  have hK := K_ne_zero
  simp only [scale]
  split <;> grind

/-- The inverse filter undoes the forward filter on the whole line. -/
theorem chain_inv_fwd (f : Sig) : chain invSteps (chain fwdSteps f) = f := by
  simp only [chain, invSteps, fwdSteps, Step.apply]
  rw [scale_inv_scale, lift_neg_lift, lift_neg_lift, lift_neg_lift, lift_neg_lift]

/-! ## Extension and symmetry -/

/-- `1D_EXTR` (F.3.7 / F.4.7): the signal extended by periodic symmetric extension. -/
def ext (i0 i1 : Int) (x : Sig) : Sig := fun j => x (pse i0 i1 j)

/-- Mirror about `i0` and period `2L` (the symmetries of an extended signal). -/
def Sym (i0 L : Int) (f : Sig) : Prop :=
  (∀ j, f (2 * i0 - j) = f j) ∧ (∀ j, f (j + 2 * L) = f j)

/-- A lifting step preserves the symmetries. -/
private theorem lift_sym {i0 L : Int} {f : Sig} (p : Int) (c : Rat)
    (h : Sym i0 L f) : Sym i0 L (lift p c f) := by
  obtain ⟨hm, hper⟩ := h
  constructor
  · intro j
    simp only [lift]
    have e1 : 2 * i0 - j - 1 = 2 * i0 - (j + 1) := by omega
    have e2 : 2 * i0 - j + 1 = 2 * i0 - (j - 1) := by omega
    have hpar : (2 * i0 - j) % 2 = p ↔ j % 2 = p := by omega
    rw [e1, e2, hm, hm, hm]
    by_cases hj : j % 2 = p
    · simp only [hj, hpar.mpr hj, ↓reduceIte]; grind
    · have : ¬ (2 * i0 - j) % 2 = p := fun h => hj (hpar.mp h)
      simp only [hj, this, ↓reduceIte]
  · intro j
    simp only [lift]
    have e1 : j + 2 * L - 1 = (j - 1) + 2 * L := by omega
    have e2 : j + 2 * L + 1 = (j + 1) + 2 * L := by omega
    have hpar : (j + 2 * L) % 2 = p ↔ j % 2 = p := by omega
    rw [e1, e2, hper, hper, hper]
    by_cases hj : j % 2 = p
    · simp only [hj, hpar.mpr hj, ↓reduceIte]
    · have : ¬ (j + 2 * L) % 2 = p := fun h => hj (hpar.mp h)
      simp only [hj, this, ↓reduceIte]

/-- A scaling preserves the symmetries. -/
private theorem scale_sym {i0 L : Int} {f : Sig} (ce co : Rat) (h : Sym i0 L f) :
    Sym i0 L (scale ce co f) := by
  obtain ⟨hm, hper⟩ := h
  constructor
  · intro j
    simp only [scale]
    have hpar : (2 * i0 - j) % 2 = 0 ↔ j % 2 = 0 := by omega
    rw [hm]
    by_cases hj : j % 2 = 0
    · simp only [hj, hpar.mpr hj, ↓reduceIte]
    · have : ¬ (2 * i0 - j) % 2 = 0 := fun h => hj (hpar.mp h)
      simp only [hj, this, ↓reduceIte]
  · intro j
    simp only [scale]
    have hpar : (j + 2 * L) % 2 = 0 ↔ j % 2 = 0 := by omega
    rw [hper]
    by_cases hj : j % 2 = 0
    · simp only [hj, hpar.mpr hj, ↓reduceIte]
    · have : ¬ (j + 2 * L) % 2 = 0 := fun h => hj (hpar.mp h)
      simp only [hj, this, ↓reduceIte]

/-- A step preserves the symmetries. -/
private theorem Step.apply_sym {i0 L : Int} {f : Sig} (s : Step) (h : Sym i0 L f) :
    Sym i0 L (s.apply f) := by
  cases s with
  | lifting p c => exact lift_sym p c h
  | scaling ce co => exact scale_sym ce co h

/-- A chain preserves the symmetries. -/
private theorem chain_sym {i0 L : Int} (l : List Step) :
    ∀ f : Sig, Sym i0 L f → Sym i0 L (chain l f) := by
  induction l with
  | nil => intro f h; exact h
  | cons s l ih => intro f h; exact ih _ (Step.apply_sym s h)

/-- A `2L`-periodic function is invariant under translation by any multiple of `2L`. -/
private theorem sym_shift {i0 L : Int} {f : Sig} (h : Sym i0 L f) (q : Int) (j : Int) :
    f (j + 2 * L * q) = f j := by
  have hn : ∀ n : Nat, ∀ k, f (k + 2 * L * (n : Int)) = f k := by
    intro n
    induction n with
    | zero => intro k; simp
    | succ n ih =>
      intro k
      have : k + 2 * L * ((n + 1 : Nat) : Int) = (k + 2 * L * (n : Int)) + 2 * L := by
        simp only [Int.natCast_add, Int.natCast_one, Int.mul_add, Int.mul_one]; omega
      rw [this, h.2, ih]
  obtain ⟨n, hq | hq⟩ := Int.eq_nat_or_neg q
  · subst hq; exact hn n j
  · subst hq
    have := hn n (j + 2 * L * (-(n : Int)))
    rw [Int.mul_neg] at this
    rw [Int.mul_neg]
    rw [show j + -(2 * L * (n : Int)) + 2 * L * (n : Int) = j by omega] at this
    exact this.symm

/-- Facts about `a mod M`. -/
private theorem emod_facts (a M : Int) (hM : 0 < M) :
    0 ≤ a % M ∧ a % M < M ∧ a = a % M + M * (a / M) := by
  refine ⟨Int.emod_nonneg a (by omega), Int.emod_lt_of_pos a hM, ?_⟩
  have := Int.mul_ediv_add_emod a M
  omega

/-- A symmetric signal is unchanged by symmetric re-extension. -/
private theorem sym_pse {i0 i1 : Int} (h : i0 + 2 ≤ i1) {f : Sig} (hf : Sym i0 (i1 - i0 - 1) f)
    (j : Int) : f (pse i0 i1 j) = f j := by
  have hL : ¬ i1 - i0 - 1 ≤ 0 := by omega
  simp only [pse, hL, ↓reduceIte]
  obtain ⟨h1, h2, h3⟩ := emod_facts (j - i0) (2 * (i1 - i0 - 1)) (by omega)
  generalize (j - i0) % (2 * (i1 - i0 - 1)) = r at h1 h2 h3 ⊢
  generalize hq : (j - i0) / (2 * (i1 - i0 - 1)) = q at h3
  by_cases hm : r ≤ 2 * (i1 - i0 - 1) - r
  · rw [Int.min_eq_left hm]
    have := sym_shift hf q (i0 + r)
    rw [← this]; congr 1; omega
  · rw [Int.min_eq_right (by omega)]
    have e1 := hf.1 (i0 + (2 * (i1 - i0 - 1) - r))
    have e2 := sym_shift hf (-(q + 1)) j
    rw [Int.mul_neg, Int.mul_add, Int.mul_one] at e2
    rw [← e1, ← e2]; congr 1; omega

/-- The extension of any signal (range length ≥ 2) has both symmetries. -/
private theorem ext_sym {i0 i1 : Int} (h : i0 + 2 ≤ i1) (x : Sig) :
    Sym i0 (i1 - i0 - 1) (ext i0 i1 x) := by
  have hL : ¬ i1 - i0 - 1 ≤ 0 := by omega
  have hM : 0 < 2 * (i1 - i0 - 1) := by omega
  constructor
  · intro j
    simp only [ext, pse, hL, ↓reduceIte]
    congr 1
    obtain ⟨h1, h2, h3⟩ := emod_facts (j - i0) (2 * (i1 - i0 - 1)) hM
    generalize hM' : 2 * (i1 - i0 - 1) = M at h1 h2 h3 hM ⊢
    generalize (j - i0) % M = r at h1 h2 h3 ⊢
    generalize (j - i0) / M = q at h3
    have e : 2 * i0 - j - i0 = (M - r) + M * (-q - 1) := by
      rw [Int.mul_sub, Int.mul_neg, Int.mul_one]; omega
    rw [e, Int.add_mul_emod_self_left]
    by_cases hr : r = 0
    · subst hr; simp
    · rw [Int.emod_eq_of_lt (by omega) (by omega)]; omega
  · intro j
    simp only [ext, pse, hL, ↓reduceIte]
    rw [show j + 2 * (i1 - i0 - 1) - i0 = (j - i0) + 2 * (i1 - i0 - 1) * 1 by omega,
      Int.add_mul_emod_self_left]

/-! ## One dimension -/

/-- `1D_SR` (F.3.6, 9/7 irreversible): inverse transform of the interleaved coefficients `y`
on `[i0, i1)`. Length 0: no change; length 1: copied at an even `i0`, halved (`Y/2`) at an
odd one; otherwise extension (F.3.7) then F-7. -/
def sr1d (i0 i1 : Int) (y : Sig) : Sig :=
  if i1 ≤ i0 then y
  else if i1 = i0 + 1 then (fun j => if i0 % 2 = 0 then y j else y j / 2)
  else chain invSteps (ext i0 i1 y)

/-- `1D_SD` (F.4.6, 9/7 irreversible): forward transform of `x` on `[i0, i1)`. Length 0: no
change; length 1: copied at an even `i0`, doubled at an odd one; otherwise extension then
F-8. Low-pass at even, high-pass at odd indices. -/
def sd1d (i0 i1 : Int) (x : Sig) : Sig :=
  if i1 ≤ i0 then x
  else if i1 = i0 + 1 then (fun j => if i0 % 2 = 0 then x j else 2 * x j)
  else chain fwdSteps (ext i0 i1 x)

/-- **Round trip (1-D)**: the inverse 9/7 undoes the forward 9/7 on `[i0, i1)` exactly, for
every range and every rational signal (the Table F.4 decimals as exact constants). -/
theorem sr1d_sd1d (i0 i1 : Int) (x : Sig) (j : Int) (h0 : i0 ≤ j) (h1 : j < i1) :
    sr1d i0 i1 (sd1d i0 i1 x) j = x j := by
  unfold sr1d sd1d
  by_cases he : i1 ≤ i0
  · omega
  · by_cases h2 : i1 = i0 + 1
    · subst h2
      simp only [show ¬ i0 + 1 ≤ i0 by omega, ↓reduceIte]
      by_cases hp : i0 % 2 = 0
      · simp only [hp, ↓reduceIte]
      · simp only [hp, ↓reduceIte]; grind
    · have hl : i0 + 2 ≤ i1 := by omega
      simp only [he, h2, ↓reduceIte]
      have hs := chain_sym fwdSteps _ (ext_sym hl x)
      have hz : ext i0 i1 (chain fwdSteps (ext i0 i1 x)) = chain fwdSteps (ext i0 i1 x) := by
        funext k; exact sym_pse hl hs k
      rw [hz, chain_inv_fwd]
      simp only [ext, pse_id h0 h1]

/-- `sr1d` reads its input only on `[i0, i1)`. -/
private theorem sr1d_local (i0 i1 : Int) (y y' : Sig) (hy : ∀ k, i0 ≤ k → k < i1 → y k = y' k)
    (j : Int) (h0 : i0 ≤ j) (h1 : j < i1) : sr1d i0 i1 y j = sr1d i0 i1 y' j := by
  unfold sr1d
  by_cases he : i1 ≤ i0
  · omega
  · by_cases h2 : i1 = i0 + 1
    · subst h2
      simp only [show ¬ i0 + 1 ≤ i0 by omega, ↓reduceIte, hy j h0 h1]
    · have hl : i0 + 2 ≤ i1 := by omega
      simp only [he, h2, ↓reduceIte]
      have : ext i0 i1 y = ext i0 i1 y' := by
        funext k; simp only [ext]
        exact hy _ (pse_mem hl k).1 (pse_mem hl k).2
      rw [this]

/-! ## Two dimensions -/

/-- A two-dimensional rational signal `g.get u v` (column `u`, row `v`). -/
structure Grid where
  /-- The sample at column `u`, row `v`. -/
  get : Int → Int → Rat

/-- Materialises a grid on its rectangle and reads it back; equal to the grid (`memo_eq`). -/
def memo (r : Rect) (g : Grid) : Grid :=
  let a : Array (Array Rat) :=
    Array.ofFn (n := (r.v1 - r.v0).toNat) fun j =>
      Array.ofFn (n := (r.u1 - r.u0).toNat) fun i => g.get (r.u0 + (i : Nat)) (r.v0 + (j : Nat))
  ⟨fun u v =>
    if r.mem u v then
      ((a[(v - r.v0).toNat]?).bind (·[(u - r.u0).toNat]?)).getD (g.get u v)
    else g.get u v⟩

/-- `memo` does not change a grid. -/
theorem memo_eq (r : Rect) (g : Grid) : memo r g = g := by
  cases g with
  | mk f =>
  simp only [memo, Grid.mk.injEq]
  funext u v
  split
  · rename_i hm
    simp only [Rect.mem] at hm
    have hv : (v - r.v0).toNat < (r.v1 - r.v0).toNat := by omega
    have hu : (u - r.u0).toNat < (r.u1 - r.u0).toNat := by omega
    simp only [Array.getElem?_ofFn, hv, hu, ↓reduceDIte, Option.bind_some, Option.getD_some]
    congr 1 <;> omega
  · rfl

/-- `HOR_SR` (F.3.4): `1D_SR` on every row. -/
def horSR (r : Rect) (g : Grid) : Grid := ⟨fun u v => sr1d r.u0 r.u1 (fun u' => g.get u' v) u⟩

/-- `VER_SR` (F.3.5): `1D_SR` on every column. -/
def verSR (r : Rect) (g : Grid) : Grid := ⟨fun u v => sr1d r.v0 r.v1 (fun v' => g.get u v') v⟩

/-- `HOR_SD` (F.4.4): `1D_SD` on every row. -/
def horSD (r : Rect) (g : Grid) : Grid := ⟨fun u v => sd1d r.u0 r.u1 (fun u' => g.get u' v) u⟩

/-- `VER_SD` (F.4.3): `1D_SD` on every column. -/
def verSD (r : Rect) (g : Grid) : Grid := ⟨fun u v => sd1d r.v0 r.v1 (fun v' => g.get u v') v⟩

/-- `2D_SR` without the interleaving: `HOR_SR` then `VER_SR`. -/
def sr2d (r : Rect) (g : Grid) : Grid := memo r (verSR r (memo r (horSR r g)))

/-- `2D_SD` without the deinterleaving: `VER_SD` then `HOR_SD`. -/
def sd2d (r : Rect) (g : Grid) : Grid := memo r (horSD r (memo r (verSD r g)))

/-- `sr2d` reads its input only on the rectangle. -/
private theorem sr2d_local (r : Rect) (g g' : Grid) (hg : ∀ u v, r.mem u v → g.get u v = g'.get u v)
    (u v : Int) (h : r.mem u v) : (sr2d r g).get u v = (sr2d r g').get u v := by
  simp only [sr2d, memo_eq, verSR, horSR]
  obtain ⟨h0, h1, h2, h3⟩ := h
  apply sr1d_local _ _ _ _ _ _ h2 h3
  intro k hk0 hk1
  apply sr1d_local _ _ _ _ _ _ h0 h1
  intro m hm0 hm1
  exact hg m k ⟨hm0, hm1, hk0, hk1⟩

/-- **Round trip (2-D, one level)**. -/
theorem sr2d_sd2d (r : Rect) (g : Grid) (u v : Int) (h : r.mem u v) :
    (sr2d r (sd2d r g)).get u v = g.get u v := by
  simp only [sr2d, sd2d, memo_eq, verSR]
  obtain ⟨h0, h1, h2, h3⟩ := h
  rw [sr1d_local r.v0 r.v1 _ (sd1d r.v0 r.v1 fun v' => g.get u v') _ v h2 h3]
  · exact sr1d_sd1d _ _ _ _ h2 h3
  · intro k _ _
    simp only [horSR, horSD]
    exact sr1d_sd1d _ _ _ _ h0 h1

/-- `2D_INTERLEAVE` (F.3.3): LL at (even, even), HL at (odd, even), LH at (even, odd), HH
at (odd, odd); band coordinates `⌊u / 2⌋, ⌊v / 2⌋`. -/
def interleave (ll hl lh hh : Grid) : Grid := ⟨fun u v =>
  if u % 2 = 0 then (if v % 2 = 0 then ll.get (u / 2) (v / 2) else lh.get (u / 2) (v / 2))
  else (if v % 2 = 0 then hl.get (u / 2) (v / 2) else hh.get (u / 2) (v / 2))⟩

/-- `2D_DEINTERLEAVE` (F.4.5): `(LL, HL, LH, HH)`. -/
def deinterleave (a : Grid) : Grid × Grid × Grid × Grid :=
  (⟨fun u v => a.get (2 * u) (2 * v)⟩, ⟨fun u v => a.get (2 * u + 1) (2 * v)⟩,
   ⟨fun u v => a.get (2 * u) (2 * v + 1)⟩, ⟨fun u v => a.get (2 * u + 1) (2 * v + 1)⟩)

/-- Interleaving the deinterleaved bands gives back the grid. -/
private theorem interleave_deinterleave (a : Grid) (u v : Int) :
    (interleave (deinterleave a).1 (deinterleave a).2.1 (deinterleave a).2.2.1
      (deinterleave a).2.2.2).get u v = a.get u v := by
  simp only [interleave, deinterleave]
  by_cases hu : u % 2 = 0 <;> by_cases hv : v % 2 = 0 <;>
    simp only [hu, hv, ↓reduceIte] <;> congr 1 <;> omega

/-- A multi-level decomposition: coarsest LL and `(HL, LH, HH)` per level, finest first. -/
structure Dec where
  /-- The LL band of the coarsest level. -/
  ll : Grid
  /-- `(HL, LH, HH)` per level, finest first. -/
  details : List (Grid × Grid × Grid)

/-- `FDWT` (F.4.1) over `n` levels from rectangle `r`. -/
def sdMulti : Rect → Nat → Grid → Dec
  | _, 0, g => ⟨g, []⟩
  | r, n + 1, g =>
    let a := sd2d r g
    let b := deinterleave a
    let d := sdMulti r.half n b.1
    ⟨d.ll, (b.2.1, b.2.2.1, b.2.2.2) :: d.details⟩

/-- `IDWT` (F.3.1) over `n` levels to rectangle `r` (stops at the LL when the decomposition
has fewer detail levels). -/
def srMulti : Rect → Nat → Dec → Grid
  | _, 0, d => d.ll
  | r, n + 1, ⟨ll, (hl, lh, hh) :: rest⟩ =>
    sr2d r (interleave (srMulti r.half n ⟨ll, rest⟩) hl lh hh)
  | _, _ + 1, ⟨ll, []⟩ => ll

/-- **Round trip (multi-level)**: `IDWT ∘ FDWT = id` on the rectangle (9/7, exact `Rat`). -/
theorem srMulti_sdMulti (n : Nat) : ∀ (r : Rect) (g : Grid) (u v : Int), r.mem u v →
    (srMulti r n (sdMulti r n g)).get u v = g.get u v := by
  induction n with
  | zero => intro r g u v _; rfl
  | succ n ih =>
    intro r g u v h
    simp only [sdMulti, srMulti]
    rw [sr2d_local r _ (sd2d r g) _ u v h]
    · exact sr2d_sd2d r g u v h
    · intro u' v' h'
      rw [← interleave_deinterleave (sd2d r g) u' v']
      simp only [interleave]
      by_cases hu : u' % 2 = 0 <;> by_cases hv : v' % 2 = 0 <;> simp only [hu, hv, ↓reduceIte]
      have hm : r.half.mem (u' / 2) (v' / 2) := by
        obtain ⟨a, b, c, d⟩ := h'
        simp only [Rect.half, Rect.mem]; omega
      exact ih r.half _ _ _ hm

/-! ## Error calculus: linearity, locality, convolution bound -/

/-- Pointwise sum. -/
def add (f g : Sig) : Sig := fun j => f j + g j

/-- Pointwise multiple. -/
def smul (c : Rat) (f : Sig) : Sig := fun j => c * f j

/-- The zero signal. -/
def zero : Sig := fun _ => 0

/-- The unit impulse at `a`. -/
def impulse (a : Int) : Sig := fun k => if k = a then 1 else 0

/-- Translation by an even amount `2m`. -/
def shift2 (m : Int) (f : Sig) : Sig := fun k => f (k + 2 * m)

/-- Steps are additive. -/
private theorem Step.apply_add (s : Step) (f g : Sig) :
    s.apply (add f g) = add (s.apply f) (s.apply g) := by
  funext j
  cases s <;> simp only [Step.apply, lift, scale, add] <;> split <;> grind

/-- Steps are homogeneous. -/
private theorem Step.apply_smul (s : Step) (a : Rat) (f : Sig) :
    s.apply (smul a f) = smul a (s.apply f) := by
  funext j
  cases s <;> simp only [Step.apply, lift, scale, smul] <;> split <;> grind

/-- Steps map zero to zero. -/
private theorem Step.apply_zero (s : Step) : s.apply zero = zero := by
  funext j
  cases s <;> simp only [Step.apply, lift, scale, zero] <;> split <;> grind

/-- Steps commute with even translations. -/
private theorem Step.apply_shift2 (s : Step) (m : Int) (f : Sig) :
    s.apply (shift2 m f) = shift2 m (s.apply f) := by
  funext k
  have hp0 : (k + 2 * m) % 2 = k % 2 := by omega
  have e1 : k - 1 + 2 * m = k + 2 * m - 1 := by omega
  have e2 : k + 1 + 2 * m = k + 2 * m + 1 := by omega
  cases s <;> simp only [Step.apply, lift, scale, shift2, hp0, e1, e2]

/-- A step at `j` reads its input only on `[j − 1, j + 1]`. -/
private theorem Step.apply_local (s : Step) (f f' : Sig) (j : Int)
    (h : ∀ k, j - 1 ≤ k → k ≤ j + 1 → f k = f' k) : s.apply f j = s.apply f' j := by
  have h0 := h j (by omega) (by omega)
  have h1 := h (j - 1) (by omega) (by omega)
  have h2 := h (j + 1) (by omega) (by omega)
  cases s <;> simp only [Step.apply, lift, scale, h0, h1, h2]

/-- Chains are additive. -/
theorem chain_add (l : List Step) : ∀ f g, chain l (add f g) = add (chain l f) (chain l g) := by
  induction l with
  | nil => intro f g; rfl
  | cons s l ih => intro f g; simp only [chain, Step.apply_add]; exact ih _ _

/-- Chains are homogeneous. -/
theorem chain_smul (l : List Step) (a : Rat) : ∀ f, chain l (smul a f) = smul a (chain l f) := by
  induction l with
  | nil => intro f; rfl
  | cons s l ih => intro f; simp only [chain, Step.apply_smul]; exact ih _

/-- Chains map zero to zero. -/
private theorem chain_zero (l : List Step) : chain l zero = zero := by
  induction l with
  | nil => rfl
  | cons s l ih => simp only [chain, Step.apply_zero]; exact ih

/-- Chains commute with even translations. -/
private theorem chain_shift2 (l : List Step) (m : Int) :
    ∀ f, chain l (shift2 m f) = shift2 m (chain l f) := by
  induction l with
  | nil => intro f; rfl
  | cons s l ih => intro f; simp only [chain, Step.apply_shift2]; exact ih _

/-- A chain at `j` reads its input only on `[j − |l|, j + |l|]`. -/
private theorem chain_local (l : List Step) : ∀ (f f' : Sig) (j : Int),
    (∀ k, j - l.length ≤ k → k ≤ j + l.length → f k = f' k) → chain l f j = chain l f' j := by
  induction l with
  | nil => intro f f' j h; exact h j (by simp) (by simp)
  | cons s l ih =>
    intro f f' j h
    simp only [chain]
    apply ih
    intro k hk1 hk2
    apply Step.apply_local
    intro m hm1 hm2
    simp only [List.length_cons, Int.natCast_add, Int.natCast_one] at h
    exact h m (by omega) (by omega)

/-- `Σ_{i < n} h (a + i)`. -/
def wsum (h : Int → Rat) (a : Int) : Nat → Rat
  | 0 => 0
  | n + 1 => wsum h a n + h (a + n)

/-- The restriction of `f` to `[a, a + n)`. -/
def restr (f : Sig) (a : Int) (n : Nat) : Sig := fun k => if a ≤ k ∧ k < a + n then f k else 0

private theorem restr_succ (f : Sig) (a : Int) (n : Nat) :
    restr f a (n + 1) = add (restr f a n) (smul (f (a + n)) (impulse (a + n))) := by
  funext k
  simp only [restr, add, smul, impulse]
  by_cases hk : k = a + n
  · subst hk
    have h1 : a ≤ a + (n : Int) ∧ a + (n : Int) < a + ((n + 1 : Nat) : Int) := by omega
    have h2 : ¬ (a ≤ a + (n : Int) ∧ a + (n : Int) < a + (n : Int)) := by omega
    simp only [h1, ↓reduceIte]; grind
  · simp only [hk, ↓reduceIte]
    by_cases hin : a ≤ k ∧ k < a + (n : Int)
    · have : a ≤ k ∧ k < a + ((n + 1 : Nat) : Int) := by omega
      simp only [hin, this]; grind
    · have : ¬ (a ≤ k ∧ k < a + ((n + 1 : Nat) : Int)) := by omega
      simp only [hin, this, ↓reduceIte]; grind

/-- A chain applied to a restriction is a weighted sum of impulse responses. -/
private theorem chain_restr (l : List Step) (f : Sig) (a j : Int) : ∀ n : Nat,
    chain l (restr f a n) j = wsum (fun k => f k * chain l (impulse k) j) a n := by
  intro n
  induction n with
  | zero =>
    have : restr f a 0 = zero := by
      funext k; simp only [restr, zero]; split
      · omega
      · rfl
    rw [this, chain_zero]; rfl
  | succ n ih =>
    rw [restr_succ, chain_add, chain_smul]
    simp only [add, smul, wsum, ih]

/-- **Convolution form**: a chain at `j` is `Σ_k f k · chain l (δ_k) j` over the window
`[j − |l|, j + |l|]`. -/
theorem chain_eq_wsum (l : List Step) (f : Sig) (j : Int) :
    chain l f j = wsum (fun k => f k * chain l (impulse k) j) (j - l.length)
      (2 * l.length + 1) := by
  rw [← chain_restr]
  apply chain_local
  intro k h1 h2
  simp only [restr]
  rw [ite_eq_left_iff.mpr (fun h => absurd (by omega) h)]

/-! ### Absolute values -/

/-- `|x| ≤ e ↔ −e ≤ x ≤ e`. -/
theorem abs_le_iff {x e : Rat} : x.abs ≤ e ↔ -e ≤ x ∧ x ≤ e := by
  unfold Rat.abs
  split <;> constructor <;> intro h <;> grind

/-- `−|x| ≤ x ≤ |x|`. -/
private theorem le_abs (x : Rat) : -x.abs ≤ x ∧ x ≤ x.abs := abs_le_iff.mp Rat.le_refl

/-- Triangle inequality. -/
theorem abs_add_le (a b : Rat) : (a + b).abs ≤ a.abs + b.abs := by
  have := le_abs a; have := le_abs b
  exact abs_le_iff.mpr ⟨by grind, by grind⟩

/-- `|a·b| ≤ e·|b|` when `|a| ≤ e`. -/
theorem abs_mul_le (a b e : Rat) (h : a.abs ≤ e) : (a * b).abs ≤ e * b.abs := by
  have ha := abs_le_iff.mp h
  by_cases hb : 0 ≤ b
  · rw [Rat.abs_of_nonneg hb]
    have h1 := Rat.mul_le_mul_of_nonneg_right ha.2 hb
    have h2 := Rat.mul_le_mul_of_nonneg_right ha.1 hb
    rw [Rat.neg_mul] at h2
    exact abs_le_iff.mpr ⟨h2, h1⟩
  · have hb' : 0 ≤ -b := by grind
    rw [Rat.abs_of_nonpos (x := b) (by grind)]
    have h1 := Rat.mul_le_mul_of_nonneg_right ha.2 hb'
    have h2 := Rat.mul_le_mul_of_nonneg_right ha.1 hb'
    rw [Rat.neg_mul, Rat.mul_neg, Rat.mul_neg] at h2
    rw [Rat.mul_neg] at h1
    exact abs_le_iff.mpr ⟨by grind, by grind⟩

/-- Termwise bound of a window sum. -/
private theorem wsum_abs_le (h h' : Int → Rat) (a : Int) (H : ∀ k, (h k).abs ≤ h' k) :
    ∀ n, (wsum h a n).abs ≤ wsum h' a n := by
  intro n
  induction n with
  | zero => simp [wsum]
  | succ n ih =>
    simp only [wsum]
    have := abs_add_le (wsum h a n) (h (a + n))
    have := H (a + n)
    grind

/-- The sharp per-sample bound of a chain at `j` for inputs bounded by `bnd`:
`Σ_k bnd k · |chain l (δ_k) j|` over the window. -/
def gb (l : List Step) (j : Int) (bnd : Int → Rat) : Rat :=
  wsum (fun k => bnd k * (chain l (impulse k) j).abs) (j - l.length) (2 * l.length + 1)

/-- **Convolution bound**: `|chain l f j| ≤ gb l j bnd` when `|f k| ≤ bnd k` everywhere. -/
theorem chain_bound (l : List Step) (f : Sig) (j : Int) (bnd : Int → Rat)
    (hf : ∀ k, (f k).abs ≤ bnd k) : (chain l f j).abs ≤ gb l j bnd := by
  rw [chain_eq_wsum]
  exact wsum_abs_le _ _ _ (fun k => abs_mul_le _ _ _ (hf k)) _

/-- A parity-dependent bound: `be` on even indices, `bo` on odd ones. -/
def pb (be bo : Rat) : Int → Rat := fun k => if k % 2 = 0 then be else bo

/-- Window sums agree when their terms do. -/
private theorem wsum_congr (h h' : Int → Rat) (a a' : Int) :
    ∀ n, (∀ i : Nat, i < n → h (a + i) = h' (a' + i)) → wsum h a n = wsum h' a' n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro H
    simp only [wsum]
    rw [ih (fun i hi => H i (by omega)), H n (by omega)]

/-- Impulse responses are invariant under even translations. -/
private theorem chain_impulse_shift (l : List Step) (a j m : Int) :
    chain l (impulse (a + 2 * m)) (j + 2 * m) = chain l (impulse a) j := by
  have : impulse a = shift2 m (impulse (a + 2 * m)) := by
    funext k; simp only [impulse, shift2]
    by_cases h : k = a
    · subst h; simp
    · have : ¬ k + 2 * m = a + 2 * m := by omega
      simp only [h, this, ↓reduceIte]
  rw [this, chain_shift2]
  rfl

/-- `gb` with a parity bound depends only on the parity of `j`. -/
private theorem gb_shift (l : List Step) (j m : Int) (be bo : Rat) :
    gb l (j + 2 * m) (pb be bo) = gb l j (pb be bo) := by
  unfold gb
  apply wsum_congr
  intro i _
  have e : j + 2 * m - l.length + i = (j - l.length + i) + 2 * m := by omega
  rw [e, chain_impulse_shift]
  simp only [pb]
  have : (j - l.length + i + 2 * m) % 2 = (j - l.length + i) % 2 := by omega
  rw [this]

/-- `gb` with a parity bound at `j` equals its value at `j % 2`. -/
theorem gb_mod (l : List Step) (j : Int) (be bo : Rat) :
    gb l j (pb be bo) = gb l (j % 2) (pb be bo) := by
  have := gb_shift l (j % 2) (j / 2) be bo
  rw [show j % 2 + 2 * (j / 2) = j by omega] at this
  exact this

/-! ### Perturbed chains -/

/-- A chain with a residual `r_i` added after step `i` (missing residuals are zero). -/
def pert : List Step → List Sig → Sig → Sig
  | [], _, f => f
  | s :: l, [], f => pert l [] (s.apply f)
  | s :: l, r :: rs, f => pert l rs (add (s.apply f) r)

/-- Without residuals a perturbed chain is the chain. -/
private theorem pert_nil (l : List Step) : ∀ f, pert l [] f = chain l f := by
  induction l with
  | nil => intro f; rfl
  | cons s l ih => intro f; simp only [pert, chain]; exact ih _

/-- **Superposition**: a perturbed chain is the chain of its input plus the perturbed chain
of zero. -/
theorem pert_eq (l : List Step) : ∀ rs f, pert l rs f = add (chain l f) (pert l rs zero) := by
  induction l with
  | nil => intro rs f; funext j; simp [pert, chain, add, zero, Rat.add_zero]
  | cons s l ih =>
    intro rs f
    cases rs with
    | nil =>
      simp only [pert, pert_nil, chain, Step.apply_zero, chain_zero]
      funext j; simp [add, zero, Rat.add_zero]
    | cons r rs =>
      simp only [pert, chain]
      rw [ih rs (add (s.apply f) r), ih rs (add (s.apply zero) r), chain_add, chain_add,
        Step.apply_zero, chain_zero]
      funext j; simp only [add, zero]; grind

/-- Residual bounds, step by step (lists of equal length). -/
def ResBound : List Sig → List (Int → Rat) → Prop
  | [], [] => True
  | r :: rs, η :: ηs => (∀ k, (r k).abs ≤ η k) ∧ ResBound rs ηs
  | _, _ => False

/-- The bound on the injected errors: residual `i` (bounded by `η_i`) passes through the
steps after step `i`. -/
def injBound : List Step → List (Int → Rat) → Int → Rat
  | _ :: l, η :: ηs, j => gb l j η + injBound l ηs j
  | _, _, _ => 0

/-- **Injected-error bound** of a perturbed chain of zero. -/
theorem pert_zero_bound (l : List Step) : ∀ (rs : List Sig) (ηs : List (Int → Rat)),
    ResBound rs ηs → ∀ j, (pert l rs zero j).abs ≤ injBound l ηs j := by
  induction l with
  | nil => intro rs ηs _ j; simp [pert, injBound, zero]
  | cons s l ih =>
    intro rs ηs h j
    cases rs with
    | nil =>
      cases ηs with
      | nil => simp [pert, pert_nil, Step.apply_zero, chain_zero, zero, injBound]
      | cons _ _ => exact absurd h (by simp [ResBound])
    | cons r rs =>
      cases ηs with
      | nil => exact absurd h (by simp [ResBound])
      | cons η ηs =>
        obtain ⟨hr, hrs⟩ := h
        simp only [pert, injBound]
        rw [pert_eq, Step.apply_zero]
        have e : add zero r = r := by funext k; simp [add, zero, Rat.zero_add]
        rw [e]
        simp only [add]
        have := abs_add_le (chain l r j) (pert l rs zero j)
        have := chain_bound l r j η hr
        have := ih rs ηs hrs j
        grind

/-- `injBound` with parity bounds depends only on the parity of `j`. -/
theorem injBound_mod (l : List Step) (ηs : List (Rat × Rat)) (j : Int) :
    injBound l (ηs.map fun e => pb e.1 e.2) j = injBound l (ηs.map fun e => pb e.1 e.2) (j % 2) := by
  induction l generalizing ηs with
  | nil => cases ηs <;> rfl
  | cons s l ih =>
    cases ηs with
    | nil => rfl
    | cons e ηs =>
      simp only [List.map_cons, injBound]
      rw [gb_mod l j, ih]

/-! ### Homogeneity (fixed point with `F` fractional bits = scaling by `2^−F`) -/

/-- `1D_SR` is homogeneous. -/
private theorem sr1d_smul (i0 i1 : Int) (c : Rat) (y : Sig) :
    sr1d i0 i1 (smul c y) = smul c (sr1d i0 i1 y) := by
  funext j
  unfold sr1d
  by_cases he : i1 ≤ i0
  · simp only [he, ↓reduceIte]
  · by_cases h2 : i1 = i0 + 1
    · simp only [h2, ↓reduceIte, smul]
      split <;> grind
    · simp only [he, h2, ↓reduceIte]
      have : ext i0 i1 (smul c y) = smul c (ext i0 i1 y) := rfl
      rw [this, chain_smul]

/-- A grid times a constant. -/
def Grid.smul (c : Rat) (g : Grid) : Grid := ⟨fun u v => c * g.get u v⟩

/-- A decomposition times a constant (every band). -/
def Dec.smul (c : Rat) (d : Dec) : Dec :=
  ⟨d.ll.smul c, d.details.map fun b => (b.1.smul c, b.2.1.smul c, b.2.2.smul c)⟩

/-- `2D_SR` is homogeneous. -/
private theorem sr2d_smul (r : Rect) (c : Rat) (g : Grid) : sr2d r (g.smul c) = (sr2d r g).smul c := by
  simp only [sr2d, memo_eq, verSR, horSR, Grid.smul, Grid.mk.injEq]
  funext u v
  have h1 : (fun v' => sr1d r.u0 r.u1 (fun u' => c * g.get u' v') u)
      = smul c (fun v' => sr1d r.u0 r.u1 (fun u' => g.get u' v') u) := by
    funext v'
    exact congrFun (sr1d_smul r.u0 r.u1 c (fun u' => g.get u' v')) u
  rw [h1, sr1d_smul]
  rfl

/-- `2D_INTERLEAVE` commutes with scaling. -/
private theorem interleave_smul (c : Rat) (ll hl lh hh : Grid) :
    interleave (ll.smul c) (hl.smul c) (lh.smul c) (hh.smul c)
      = (interleave ll hl lh hh).smul c := by
  simp only [interleave, Grid.smul, Grid.mk.injEq]
  funext u v
  split <;> split <;> rfl

/-- `IDWT` is homogeneous: `srMulti (c·d) = c · srMulti d`. -/
theorem srMulti_smul (c : Rat) (n : Nat) : ∀ (r : Rect) (d : Dec),
    srMulti r n (d.smul c) = (srMulti r n d).smul c := by
  induction n with
  | zero => intro r d; rfl
  | succ n ih =>
    intro r d
    obtain ⟨ll, det⟩ := d
    cases det with
    | nil => rfl
    | cons b rest =>
      obtain ⟨hl, lh, hh⟩ := b
      have := ih r.half ⟨ll, rest⟩
      simp only [Dec.smul, List.map_cons, srMulti] at this ⊢
      rw [this, interleave_smul, sr2d_smul]

end JPEG2000.Spec.DWT97
