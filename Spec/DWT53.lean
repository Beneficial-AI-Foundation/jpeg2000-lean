/-!
# Reversible 5/3 wavelet: Annex F specification and theorem C6

Plan.md §4 (C6), §5.2 "DWT", §5.4; T.800 Annex F:

* F.3.1/F.3.2 `IDWT` / `2D_SR`: one level = `2D_INTERLEAVE` (F.3.3) of the four sub-bands,
  then `HOR_SR` (F.3.4, every row) and `VER_SR` (F.3.5, every column).
* F.3.6 `1D_SR`: a length-1 signal is copied (even start) or halved (odd start); otherwise
  `1D_EXTR` (F.3.7, periodic symmetric extension, equation F-4) followed by
  `1D_FILTR_5-3R` (F.3.8.1, equations F-5, F-6).
* F.4 forward transform (used by the reference encoder and for C6): `2D_SD` = `VER_SD` then
  `HOR_SD`, then `2D_DEINTERLEAVE`; `1D_SD` (F.4.6): length 1 copied (even start) or doubled
  (odd start); otherwise extension and `1D_FILTD_5-3R` (F.4.8.1, equations F-9, F-10).

## Formulation

Signals are total functions `Int → Int` (index = absolute coordinate, as in Annex F); only
the values on the index range `[i0, i1)` are meaningful. The extension `ext i0 i1 x = x ∘ pse`
is defined everywhere, and each lifting step is applied pointwise at every index: the
standard computes the same formulas on just enough extended samples (Table F.2/F.3), and
every value it computes equals ours at the same index.

* `predict`/`unpredict` act on odd indices (F-10 / F-6), `update`/`unupdate` on even ones
  (F-9 / F-5); `unpredict ∘ predict = id` and `unupdate ∘ update = id` pointwise.
* The periodic symmetric extension `pse` (F-4) has period `2(i1 − i0 − 1)` and is a mirror
  about `i0`; both lifting steps preserve functions with these two symmetries, and a
  symmetric function is unchanged by re-extension. This gives C6 for every length `≥ 2`;
  lengths 0 and 1 are direct.

Images are `Grid`s (wrapped functions `Int → Int → Int`) on a `Rect` (`[u0, u1) × [v0, v1)`); `memo`
materialises a grid on its rectangle (so the executable spec runs in polynomial time) and
is provably the identity. Multi-level decompositions use the rectangle sequence
`rect_r = ⌈rect_{r+1} / 2⌉` (`Rect.half`), which is B-14/B-15's `⌈tc / 2^(NL−r)⌉` because
`⌈⌈x / 2^k⌉ / 2⌉ = ⌈x / 2^(k+1)⌉`.

Theorems (C6): `sr1d_sd1d` (1-D, every range incl. length 0 and 1, every start parity,
every signal), `sr1dList_sd1dList` (list form), `sr2d_sd2d` (one 2-D level),
`srMulti_sdMulti` (any number of levels).
-/

namespace JPEG2000.Spec.DWT53

/-- A one-dimensional signal indexed by absolute coordinate. -/
abbrev Sig := Int → Int

/-- A two-dimensional signal `g.get u v` (column `u`, row `v`), absolute coordinates. It is a
structure rather than a bare function so that compiled code evaluates a materialised level
(`memo`) once: a definition whose type is a function type is eta-expanded by the compiler,
which would recompute the materialisation at every sample. -/
structure Grid where
  /-- The sample at column `u`, row `v`. -/
  get : Int → Int → Int

/-! ## One dimension -/

/-- Periodic symmetric extension, equation F-4:
`PSE(i) = i0 + min(mod(i − i0, 2(i1−i0−1)), 2(i1−i0−1) − mod(i − i0, 2(i1−i0−1)))`.
For ranges of length ≤ 1 (where F-4 is not used) it returns `i0`. -/
def pse (i0 i1 j : Int) : Int :=
  if i1 - i0 - 1 ≤ 0 then i0
  else
    let r := (j - i0) % (2 * (i1 - i0 - 1))
    i0 + min r (2 * (i1 - i0 - 1) - r)

/-- `1D_EXTR` (F.3.7 / F.4.7): the signal extended by periodic symmetric extension. -/
def ext (i0 i1 : Int) (x : Sig) : Sig := fun j => x (pse i0 i1 j)

/-- Forward predict step, F-10: `Y(2n+1) = X(2n+1) − ⌊(X(2n) + X(2n+2)) / 2⌋` at odd
indices; even indices unchanged. -/
def predict (f : Sig) : Sig := fun j =>
  if j % 2 = 1 then f j - (f (j - 1) + f (j + 1)) / 2 else f j

/-- Forward update step, F-9: `Y(2n) = X(2n) + ⌊(Y(2n−1) + Y(2n+1) + 2) / 4⌋` at even
indices; odd indices unchanged. -/
def update (f : Sig) : Sig := fun j =>
  if j % 2 = 0 then f j + (f (j - 1) + f (j + 1) + 2) / 4 else f j

/-- Inverse update step, F-5: `X(2n) = Y(2n) − ⌊(Y(2n−1) + Y(2n+1) + 2) / 4⌋` at even
indices; odd indices unchanged. -/
def unupdate (f : Sig) : Sig := fun j =>
  if j % 2 = 0 then f j - (f (j - 1) + f (j + 1) + 2) / 4 else f j

/-- Inverse predict step, F-6: `X(2n+1) = Y(2n+1) + ⌊(X(2n) + X(2n+2)) / 2⌋` at odd
indices; even indices unchanged. -/
def unpredict (f : Sig) : Sig := fun j =>
  if j % 2 = 1 then f j + (f (j - 1) + f (j + 1)) / 2 else f j

/-- `1D_SD` (F.4.6, 5/3 reversible): forward transform of `x` on `[i0, i1)`. Length 0: no
change; length 1: copied at an even `i0`, doubled at an odd one; otherwise extension
(F.4.7) then F-10 and F-9. The result interleaves low-pass (even indices) and high-pass
(odd indices) coefficients. -/
def sd1d (i0 i1 : Int) (x : Sig) : Sig :=
  if i1 ≤ i0 then x
  else if i1 = i0 + 1 then (fun j => if i0 % 2 = 0 then x j else 2 * x j)
  else update (predict (ext i0 i1 x))

/-- `1D_SR` (F.3.6, 5/3 reversible): inverse transform of the interleaved coefficients `y`
on `[i0, i1)`. Length 0: no change; length 1: copied at an even `i0`, halved (`⌊Y/2⌋`) at an
odd one; otherwise extension (F.3.7) then F-5 and F-6. -/
def sr1d (i0 i1 : Int) (y : Sig) : Sig :=
  if i1 ≤ i0 then y
  else if i1 = i0 + 1 then (fun j => if i0 % 2 = 0 then y j else y j / 2)
  else unpredict (unupdate (ext i0 i1 y))

/-- A list as a signal starting at `i0` (0 outside). -/
def ofList (i0 : Int) (xs : List Int) : Sig := fun j => xs.getD (j - i0).toNat 0

/-- A signal's values on `[i0, i0 + n)` as a list. -/
def toList (i0 : Int) (n : Nat) (f : Sig) : List Int :=
  (List.range n).map fun (k : Nat) => f (i0 + (k : Int))

/-- `1D_SD` on a list whose first sample has absolute index `i0`. -/
def sd1dList (i0 : Int) (xs : List Int) : List Int :=
  toList i0 xs.length (sd1d i0 (i0 + xs.length) (ofList i0 xs))

/-- `1D_SR` on a list of interleaved coefficients whose first has absolute index `i0`. -/
def sr1dList (i0 : Int) (ys : List Int) : List Int :=
  toList i0 ys.length (sr1d i0 (i0 + ys.length) (ofList i0 ys))

/-! ### Lifting steps invert each other -/

/-- The inverse predict step undoes the predict step (pointwise, every function). -/
theorem unpredict_predict (f : Sig) : unpredict (predict f) = f := by
  funext j
  simp only [unpredict, predict]
  by_cases h : j % 2 = 1
  · have h1 : ¬ (j - 1) % 2 = 1 := by omega
    have h2 : ¬ (j + 1) % 2 = 1 := by omega
    simp only [h, h1, h2, ↓reduceIte]; omega
  · simp only [h, ↓reduceIte]

/-- The inverse update step undoes the update step (pointwise, every function). -/
theorem unupdate_update (f : Sig) : unupdate (update f) = f := by
  funext j
  simp only [unupdate, update]
  by_cases h : j % 2 = 0
  · have h1 : ¬ (j - 1) % 2 = 0 := by omega
    have h2 : ¬ (j + 1) % 2 = 0 := by omega
    simp only [h, h1, h2, ↓reduceIte]; omega
  · simp only [h, ↓reduceIte]

/-! ### Symmetric extension -/

/-- The two symmetries of a periodically symmetrically extended signal: mirror about `i0`
and period `2L`. -/
def Sym (i0 L : Int) (f : Sig) : Prop :=
  (∀ j, f (2 * i0 - j) = f j) ∧ (∀ j, f (j + 2 * L) = f j)

/-- `predict` preserves the symmetries. -/
theorem predict_sym {i0 L : Int} {f : Sig} (h : Sym i0 L f) : Sym i0 L (predict f) := by
  obtain ⟨hm, hp⟩ := h
  constructor
  · intro j
    simp only [predict]
    have e1 : 2 * i0 - j - 1 = 2 * i0 - (j + 1) := by omega
    have e2 : 2 * i0 - j + 1 = 2 * i0 - (j - 1) := by omega
    have hpar : (2 * i0 - j) % 2 = 1 ↔ j % 2 = 1 := by omega
    rw [e1, e2, hm, hm, hm]
    by_cases hj : j % 2 = 1
    · simp only [hj, hpar.mpr hj, ↓reduceIte]; omega
    · have : ¬ (2 * i0 - j) % 2 = 1 := fun h => hj (hpar.mp h)
      simp only [hj, this, ↓reduceIte]
  · intro j
    simp only [predict]
    have e1 : j + 2 * L - 1 = (j - 1) + 2 * L := by omega
    have e2 : j + 2 * L + 1 = (j + 1) + 2 * L := by omega
    have hpar : (j + 2 * L) % 2 = 1 ↔ j % 2 = 1 := by omega
    rw [e1, e2, hp, hp, hp]
    by_cases hj : j % 2 = 1
    · simp only [hj, hpar.mpr hj, ↓reduceIte]
    · have : ¬ (j + 2 * L) % 2 = 1 := fun h => hj (hpar.mp h)
      simp only [hj, this, ↓reduceIte]

/-- `update` preserves the symmetries. -/
theorem update_sym {i0 L : Int} {f : Sig} (h : Sym i0 L f) : Sym i0 L (update f) := by
  obtain ⟨hm, hp⟩ := h
  constructor
  · intro j
    simp only [update]
    have e1 : 2 * i0 - j - 1 = 2 * i0 - (j + 1) := by omega
    have e2 : 2 * i0 - j + 1 = 2 * i0 - (j - 1) := by omega
    have hpar : (2 * i0 - j) % 2 = 0 ↔ j % 2 = 0 := by omega
    rw [e1, e2, hm, hm, hm]
    by_cases hj : j % 2 = 0
    · simp only [hj, hpar.mpr hj, ↓reduceIte]; omega
    · have : ¬ (2 * i0 - j) % 2 = 0 := fun h => hj (hpar.mp h)
      simp only [hj, this, ↓reduceIte]
  · intro j
    simp only [update]
    have e1 : j + 2 * L - 1 = (j - 1) + 2 * L := by omega
    have e2 : j + 2 * L + 1 = (j + 1) + 2 * L := by omega
    have hpar : (j + 2 * L) % 2 = 0 ↔ j % 2 = 0 := by omega
    rw [e1, e2, hp, hp, hp]
    by_cases hj : j % 2 = 0
    · simp only [hj, hpar.mpr hj, ↓reduceIte]
    · have : ¬ (j + 2 * L) % 2 = 0 := fun h => hj (hpar.mp h)
      simp only [hj, this, ↓reduceIte]

/-- A `2L`-periodic function is invariant under translation by any multiple of `2L`. -/
theorem sym_shift {i0 L : Int} {f : Sig} (h : Sym i0 L f) (q : Int) (j : Int) :
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

/-- Facts about `(j − i0) mod 2L`. -/
private theorem emod_facts (a M : Int) (hM : 0 < M) :
    0 ≤ a % M ∧ a % M < M ∧ a = a % M + M * (a / M) := by
  refine ⟨Int.emod_nonneg a (by omega), Int.emod_lt_of_pos a hM, ?_⟩
  have := Int.mul_ediv_add_emod a M
  omega

/-- For a range of length ≥ 2, `pse` lands in the range. -/
theorem pse_mem {i0 i1 : Int} (h : i0 + 2 ≤ i1) (j : Int) :
    i0 ≤ pse i0 i1 j ∧ pse i0 i1 j < i1 := by
  have hL : ¬ i1 - i0 - 1 ≤ 0 := by omega
  simp only [pse, hL, ↓reduceIte]
  obtain ⟨h1, h2, -⟩ := emod_facts (j - i0) (2 * (i1 - i0 - 1)) (by omega)
  omega

/-- `pse` is the identity on the range. -/
theorem pse_id {i0 i1 j : Int} (h0 : i0 ≤ j) (h1 : j < i1) : pse i0 i1 j = j := by
  unfold pse
  by_cases hL : i1 - i0 - 1 ≤ 0
  · simp only [hL, ↓reduceIte]; omega
  · simp only [hL, ↓reduceIte]
    rw [Int.emod_eq_of_lt (by omega) (by omega)]
    omega

/-- A symmetric function is unchanged by symmetric re-extension: `f (pse j) = f j`. -/
theorem sym_pse {i0 i1 : Int} (h : i0 + 2 ≤ i1) {f : Sig} (hf : Sym i0 (i1 - i0 - 1) f)
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
theorem ext_sym {i0 i1 : Int} (h : i0 + 2 ≤ i1) (x : Sig) :
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

/-! ### Theorem C6, one dimension -/

/-- **C6 (1-D)**: the inverse 5/3 transform undoes the forward one on the range `[i0, i1)`,
for every range (length 0, 1, odd, even; any start parity) and every integer signal. -/
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
      · simp only [hp, ↓reduceIte]; omega
    · have hl : i0 + 2 ≤ i1 := by omega
      simp only [he, h2, ↓reduceIte]
      have hs := update_sym (predict_sym (ext_sym hl x))
      have hz : ext i0 i1 (update (predict (ext i0 i1 x))) = update (predict (ext i0 i1 x)) := by
        funext k; exact sym_pse hl hs k
      rw [hz, unupdate_update, unpredict_predict]
      simp only [ext, pse_id h0 h1]

/-- `sr1d` reads its input only on the range `[i0, i1)` (outputs on the range agree). -/
theorem sr1d_local (i0 i1 : Int) (y y' : Sig) (hy : ∀ k, i0 ≤ k → k < i1 → y k = y' k)
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

/-- `sd1d` reads its input only on the range `[i0, i1)` (outputs on the range agree). -/
theorem sd1d_local (i0 i1 : Int) (x x' : Sig) (hx : ∀ k, i0 ≤ k → k < i1 → x k = x' k)
    (j : Int) (h0 : i0 ≤ j) (h1 : j < i1) : sd1d i0 i1 x j = sd1d i0 i1 x' j := by
  unfold sd1d
  by_cases he : i1 ≤ i0
  · omega
  · by_cases h2 : i1 = i0 + 1
    · subst h2
      simp only [show ¬ i0 + 1 ≤ i0 by omega, ↓reduceIte, hx j h0 h1]
    · have hl : i0 + 2 ≤ i1 := by omega
      simp only [he, h2, ↓reduceIte]
      have : ext i0 i1 x = ext i0 i1 x' := by
        funext k; simp only [ext]
        exact hx _ (pse_mem hl k).1 (pse_mem hl k).2
      rw [this]

/-- Reading back a list signal inside its range. -/
theorem ofList_get (i0 : Int) (xs : List Int) (k : Nat) (hk : k < xs.length) :
    ofList i0 xs (i0 + k) = xs[k] := by
  simp only [ofList, show i0 + (k : Int) - i0 = k by omega, Int.toNat_natCast]
  simp [List.getD_eq_getElem?_getD, hk]

/-- **C6 (1-D, lists)**: `sr1dList i0 (sd1dList i0 xs) = xs` for every start `i0` and every
list (including the empty list and singletons). -/
theorem sr1dList_sd1dList (i0 : Int) (xs : List Int) : sr1dList i0 (sd1dList i0 xs) = xs := by
  simp only [sr1dList, sd1dList, toList, List.length_map, List.length_range]
  apply List.ext_getElem
  · simp
  · intro k hk _
    simp only [List.getElem_map, List.getElem_range]
    simp only [List.length_map, List.length_range] at hk
    rw [sr1d_local i0 (i0 + xs.length) _ (sd1d i0 (i0 + xs.length) (ofList i0 xs))]
    · rw [sr1d_sd1d _ _ _ _ (by omega) (by omega), ofList_get _ _ _ hk]
    · intro m hm0 hm1
      have hm : (m - i0).toNat < xs.length := by omega
      simp only [ofList]
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hm]
      simp only [Option.map_some, Option.getD_some]
      congr 1; omega
    · omega
    · omega

/-! ## Two dimensions -/

/-- A rectangle `[u0, u1) × [v0, v1)` (column range `u`, row range `v`). -/
structure Rect where
  /-- First column. -/
  u0 : Int
  /-- One past the last column. -/
  u1 : Int
  /-- First row. -/
  v0 : Int
  /-- One past the last row. -/
  v1 : Int
  deriving Repr, DecidableEq, Inhabited

/-- Membership in a rectangle. -/
def Rect.mem (r : Rect) (u v : Int) : Prop := r.u0 ≤ u ∧ u < r.u1 ∧ r.v0 ≤ v ∧ v < r.v1

instance (r : Rect) (u v : Int) : Decidable (r.mem u v) := by
  unfold Rect.mem; exact inferInstance

/-- The next coarser resolution's rectangle: `⌈· / 2⌉` on every coordinate (B-14/B-15). -/
def Rect.half (r : Rect) : Rect :=
  { u0 := (r.u0 + 1) / 2, u1 := (r.u1 + 1) / 2, v0 := (r.v0 + 1) / 2, v1 := (r.v1 + 1) / 2 }

/-- Materialises a grid on its rectangle (row arrays) and reads it back; equal to the grid
(`memo_eq`). Used so the executable spec evaluates each level once. -/
def memo (r : Rect) (g : Grid) : Grid :=
  let a : Array (Array Int) :=
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

/-- `HOR_SR` (F.3.4): `1D_SR` on every row over the column range. -/
def horSR (r : Rect) (g : Grid) : Grid := ⟨fun u v => sr1d r.u0 r.u1 (fun u' => g.get u' v) u⟩

/-- `VER_SR` (F.3.5): `1D_SR` on every column over the row range. -/
def verSR (r : Rect) (g : Grid) : Grid := ⟨fun u v => sr1d r.v0 r.v1 (fun v' => g.get u v') v⟩

/-- `HOR_SD` (F.4.4): `1D_SD` on every row. -/
def horSD (r : Rect) (g : Grid) : Grid := ⟨fun u v => sd1d r.u0 r.u1 (fun u' => g.get u' v) u⟩

/-- `VER_SD` (F.4.3): `1D_SD` on every column. -/
def verSD (r : Rect) (g : Grid) : Grid := ⟨fun u v => sd1d r.v0 r.v1 (fun v' => g.get u v') v⟩

/-- `2D_SR` without the interleaving (F.3.2): `HOR_SR` then `VER_SR` on the interleaved
coefficients of rectangle `r`. -/
def sr2d (r : Rect) (g : Grid) : Grid := memo r (verSR r (memo r (horSR r g)))

/-- `2D_SD` without the deinterleaving (F.4.2): `VER_SD` then `HOR_SD`. -/
def sd2d (r : Rect) (g : Grid) : Grid := memo r (horSD r (memo r (verSD r g)))

/-- `sr2d` reads its input only on the rectangle. -/
theorem sr2d_local (r : Rect) (g g' : Grid) (hg : ∀ u v, r.mem u v → g.get u v = g'.get u v)
    (u v : Int) (h : r.mem u v) : (sr2d r g).get u v = (sr2d r g').get u v := by
  simp only [sr2d, memo_eq, verSR, horSR]
  obtain ⟨h0, h1, h2, h3⟩ := h
  apply sr1d_local _ _ _ _ _ _ h2 h3
  intro k hk0 hk1
  apply sr1d_local _ _ _ _ _ _ h0 h1
  intro m hm0 hm1
  exact hg m k ⟨hm0, hm1, hk0, hk1⟩

/-- **C6 (2-D, one level)**: `HOR_SR`/`VER_SR` undo `VER_SD`/`HOR_SD` on the rectangle. -/
theorem sr2d_sd2d (r : Rect) (g : Grid) (u v : Int) (h : r.mem u v) :
    (sr2d r (sd2d r g)).get u v = g.get u v := by
  simp only [sr2d, sd2d, memo_eq, verSR]
  obtain ⟨h0, h1, h2, h3⟩ := h
  rw [sr1d_local r.v0 r.v1 _ (sd1d r.v0 r.v1 fun v' => g.get u v') _ v h2 h3]
  · exact sr1d_sd1d _ _ _ _ h2 h3
  · intro k _ _
    simp only [horSR, horSD]
    exact sr1d_sd1d _ _ _ _ h0 h1

/-! ## Interleaving and multi-level decomposition -/

/-- `2D_INTERLEAVE` (F.3.3): LL at (even, even), HL at (odd, even), LH at (even, odd), HH
at (odd, odd); band coordinates are `⌊u / 2⌋, ⌊v / 2⌋`. -/
def interleave (ll hl lh hh : Grid) : Grid := ⟨fun u v =>
  if u % 2 = 0 then (if v % 2 = 0 then ll.get (u / 2) (v / 2) else lh.get (u / 2) (v / 2))
  else (if v % 2 = 0 then hl.get (u / 2) (v / 2) else hh.get (u / 2) (v / 2))⟩

/-- `2D_DEINTERLEAVE` (F.4.5): the four sub-bands `(LL, HL, LH, HH)` of an interleaved
grid. -/
def deinterleave (a : Grid) : Grid × Grid × Grid × Grid :=
  (⟨fun u v => a.get (2 * u) (2 * v)⟩, ⟨fun u v => a.get (2 * u + 1) (2 * v)⟩,
   ⟨fun u v => a.get (2 * u) (2 * v + 1)⟩, ⟨fun u v => a.get (2 * u + 1) (2 * v + 1)⟩)

/-- Interleaving the deinterleaved bands gives back the grid (everywhere). -/
theorem interleave_deinterleave (a : Grid) (u v : Int) :
    (interleave (deinterleave a).1 (deinterleave a).2.1 (deinterleave a).2.2.1
      (deinterleave a).2.2.2).get u v = a.get u v := by
  simp only [interleave, deinterleave]
  by_cases hu : u % 2 = 0 <;> by_cases hv : v % 2 = 0 <;>
    simp only [hu, hv, ↓reduceIte] <;> congr 1 <;> omega

/-- A multi-level decomposition: the coarsest LL band and the `(HL, LH, HH)` bands of each
level, finest first. -/
structure Dec where
  /-- The LL band of the coarsest level (band coordinates). -/
  ll : Grid
  /-- `(HL, LH, HH)` per level, finest (level 1) first. -/
  details : List (Grid × Grid × Grid)

/-- `FDWT` (F.4.1) over `n` levels from rectangle `r`: `2D_SD` then deinterleave; recurse on
LL with `r.half`. -/
def sdMulti : Rect → Nat → Grid → Dec
  | _, 0, g => ⟨g, []⟩
  | r, n + 1, g =>
    let a := sd2d r g
    let b := deinterleave a
    let d := sdMulti r.half n b.1
    ⟨d.ll, (b.2.1, b.2.2.1, b.2.2.2) :: d.details⟩

/-- `IDWT` (F.3.1) over `n` levels to rectangle `r`: reconstruct the LL of `r.half`
recursively, interleave with the level's detail bands (F.3.3), then `2D_SR`. A
decomposition with fewer detail levels than `n` stops at its LL. -/
def srMulti : Rect → Nat → Dec → Grid
  | _, 0, d => d.ll
  | r, n + 1, ⟨ll, (hl, lh, hh) :: rest⟩ =>
    sr2d r (interleave (srMulti r.half n ⟨ll, rest⟩) hl lh hh)
  | _, _ + 1, ⟨ll, []⟩ => ll

/-- **C6 (multi-level)**: `IDWT ∘ FDWT = id` on the rectangle, for every number of levels,
every rectangle and every integer image. -/
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

end JPEG2000.Spec.DWT53
