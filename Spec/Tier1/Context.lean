/-!
# Spec: Tier-1 context tables (T.800 Annex D, Tables D.1–D.4, D.7)

Plan.md §4 (C3), §5.1 (spec/implementation pattern), §5.2 "Tier-1 / EBCOT" ("the context
tables D.1–D.3 as data").

A literal transcription of the context-formation rules of ITU-T T.800 Annex D:

* D.3.1, Table D.1 — zero coding (significance propagation and cleanup passes): contexts
  0–8 from the sub-band orientation and the neighbour significance counts `ΣH` (0–2),
  `ΣV` (0–2), `ΣD` (0–4) (`zcContext`);
* D.3.2, Table D.2 — the horizontal / vertical sign contributions (`signContribution`);
* D.3.2, Table D.3 — sign-coding context 9–13 and `XORbit` from the two contributions
  (`scContext`);
* D.3.3, Table D.4 — magnitude-refinement contexts 14–16 (`mrContext`);
* D.3.4 — the run-length context (`ctxRunLength = 17`) and the UNIFORM context
  (`ctxUniform = 18`);
* D.7, Table D.7 — initial states of the 19 contexts (`initialStates`).

## Context numbering

T.800 names the contexts by their role and does not number them; this project numbers them
as OpenJPEG does (`T1_CTXNO_ZC = 0`, `T1_CTXNO_SC = 9`, `T1_CTXNO_MAG = 14`,
`T1_CTXNO_AGG = 17`, `T1_CTXNO_UNI = 18` in `t1.h`) and as the context labels printed in
Tables D.1, D.3, D.4 (0–8, 9–13, 14–16) suggest:

| contexts | role |
|---|---|
| 0–8   | zero coding, Table D.1 (context 0 = all eight neighbours insignificant) |
| 9–13  | sign coding, Table D.3 |
| 14–16 | magnitude refinement, Table D.4 |
| 17    | run-length (cleanup pass, D.3.4) |
| 18    | UNIFORM (cleanup pass run interruption, D.3.4; segmentation symbol, D.5) |

With this numbering Table D.7 ("UNIFORM: state 46; run-length: state 3; all-zero-neighbours
zero-coding context: state 4; all others: state 0") is `initialStates`, the same list as
`JPEG2000.MQ.tier1Inits` and the `tier1Inits` of the MQ test suites (`Spec.MQ` indexes its
context table by these numbers).

## Representation choices

* Orientations are T.800's names: `LH` is horizontally low-pass and vertically high-pass
  (Table D.1 groups it with `LL`), `HL` horizontally high-pass, vertically low-pass.
  OpenJPEG's `band->bandno` is `0 = LL, 1 = HL, 2 = LH, 3 = HH`; its LUT generator stores the
  table for generator orientation `j` at `bandno` `j` with 1 and 2 exchanged, so that at
  look-up `bandno = 1` (HL) gets the H/V-swapped table — the same as here.
* Counts are `Nat`, not `Fin`: the Tier-1 spec computes them as sums of `0/1` terms, and a
  `Nat` signature saves every caller a range proof. Each table row reads "`= k`" for the
  values it names and "`≥ k`" for its last row, exactly as T.800's "≥1", "≥2", "≥3" and
  "x" (don't care) entries, so an out-of-range count is treated as the largest count of
  its row (`zcContext_clamp`): the function is total with no arbitrary default.
* Sign contributions are `Int` in `{-1, 0, 1}`; `scContext` reads its arguments by sign
  (`> 0`, `= 0`, `< 0`), so any `Int` is accepted and in-range values give Table D.3.
* All functions are total over small finite inputs; the sanity lemmas below are proved by
  `decide` over the in-range inputs and by case splits for the unbounded ones.
-/

namespace JPEG2000.Spec.Tier1

/-! ## Sub-band orientation -/

/-- The orientation of a sub-band (T.800 Annex F/B.5 naming: first letter = horizontal
filter, second = vertical filter; `L` low-pass, `H` high-pass). -/
inductive Orientation where
  /-- Low-pass both ways (the lowest resolution). -/
  | LL
  /-- Horizontally high-pass, vertically low-pass (vertical edges). -/
  | HL
  /-- Horizontally low-pass, vertically high-pass (horizontal edges). -/
  | LH
  /-- High-pass both ways (diagonal detail). -/
  | HH
  deriving DecidableEq, Repr, Inhabited

/-- All four orientations (for exhaustive checks). -/
def Orientation.all : List Orientation := [.LL, .HL, .LH, .HH]

/-! ## Table D.1 — zero coding (D.3.1) -/

/-- Table D.1, columns "LL and LH sub-bands (vertically high-pass)", as a function of
`ΣH`, `ΣV`, `ΣD`. Rows of the standard, top to bottom:

| ΣH | ΣV | ΣD | context |
|---|---|---|---|
| 2 | x  | x  | 8 |
| 1 | ≥1 | x  | 7 |
| 1 | 0  | ≥1 | 6 |
| 1 | 0  | 0  | 5 |
| 0 | 2  | x  | 4 |
| 0 | 1  | x  | 3 |
| 0 | 0  | ≥2 | 2 |
| 0 | 0  | 1  | 1 |
| 0 | 0  | 0  | 0 |

(The match lists them bottom to top; its catch-all patterns are the "x" and "≥" entries.) -/
def zcTableLLLH : (h v d : Nat) → Nat
  | 0, 0, 0 => 0
  | 0, 0, 1 => 1
  | 0, 0, _ => 2   -- ΣD ≥ 2
  | 0, 1, _ => 3
  | 0, _, _ => 4   -- ΣV = 2
  | 1, 0, 0 => 5
  | 1, 0, _ => 6   -- ΣD ≥ 1
  | 1, _, _ => 7   -- ΣV ≥ 1
  | _, _, _ => 8   -- ΣH = 2

/-- Table D.1, columns "HH sub-band (diagonally high-pass)", as a function of
`ΣH + ΣV` and `ΣD`. Rows of the standard, top to bottom:

| ΣH+ΣV | ΣD | context |
|---|---|---|
| x  | ≥3 | 8 |
| ≥1 | 2  | 7 |
| 0  | 2  | 6 |
| ≥2 | 1  | 5 |
| 1  | 1  | 4 |
| 0  | 1  | 3 |
| ≥2 | 0  | 2 |
| 1  | 0  | 1 |
| 0  | 0  | 0 |
-/
def zcTableHH : (hv d : Nat) → Nat
  | 0, 0 => 0
  | 1, 0 => 1
  | _, 0 => 2   -- ΣH+ΣV ≥ 2
  | 0, 1 => 3
  | 1, 1 => 4
  | _, 1 => 5   -- ΣH+ΣV ≥ 2
  | 0, 2 => 6
  | _, 2 => 7   -- ΣH+ΣV ≥ 1
  | _, _ => 8   -- ΣD ≥ 3

/-- Zero-coding context (T.800 D.3.1, Table D.1) of a coefficient in a sub-band of
orientation `o` whose horizontal, vertical and diagonal neighbours contain `h`, `v`, `d`
significant coefficients (`h, v ≤ 2`, `d ≤ 4`; larger counts read as the largest row). The
HL column is the LL/LH column with `ΣH` and `ΣV` exchanged. -/
def zcContext : Orientation → (h v d : Nat) → Nat
  | .LL, h, v, d => zcTableLLLH h v d
  | .LH, h, v, d => zcTableLLLH h v d
  | .HL, h, v, d => zcTableLLLH v h d
  | .HH, h, v, d => zcTableHH (h + v) d

/-! ## Tables D.2 and D.3 — sign coding (D.3.2) -/

/-- The state of one horizontal or vertical neighbour as seen by Table D.2. -/
inductive NeighbourSign where
  /-- Not (yet) significant. -/
  | insignificant
  /-- Significant with a positive sign. -/
  | positive
  /-- Significant with a negative sign. -/
  | negative
  deriving DecidableEq, Repr, Inhabited

/-- All three neighbour states (for exhaustive checks). -/
def NeighbourSign.all : List NeighbourSign := [.insignificant, .positive, .negative]

/-- The neighbour state from its significance and sign bits (`neg = true`: negative). -/
def NeighbourSign.ofBits (sig neg : Bool) : NeighbourSign :=
  if sig then (if neg then .negative else .positive) else .insignificant

/-- Table D.2: the horizontal (resp. vertical) contribution from the two horizontal (resp.
vertical) neighbours, one row of the standard per line. -/
def signContribution : NeighbourSign → NeighbourSign → Int
  | .positive,      .positive      => 1
  | .negative,      .positive      => 0
  | .insignificant, .positive      => 1
  | .positive,      .negative      => 0
  | .negative,      .negative      => -1
  | .insignificant, .negative      => -1
  | .positive,      .insignificant => 1
  | .negative,      .insignificant => -1
  | .insignificant, .insignificant => 0

/-- Table D.3: the sign-coding context (9–13) and `XORbit` from the horizontal contribution
`hc` and the vertical contribution `vc` (each `1`, `0` or `-1`; any other `Int` is read by
its sign). The decoded sign bit is the decision XOR `XORbit` (D.3.2). Rows of the standard:

| H | V | context | XORbit |
|---|---|---|---|
| 1  | 1  | 13 | 0 |
| 1  | 0  | 12 | 0 |
| 1  | −1 | 11 | 0 |
| 0  | 1  | 10 | 0 |
| 0  | 0  | 9  | 0 |
| 0  | −1 | 10 | 1 |
| −1 | 1  | 11 | 1 |
| −1 | 0  | 12 | 1 |
| −1 | −1 | 13 | 1 |
-/
def scContext (hc vc : Int) : Nat × Bool :=
  if 0 < hc then
    if 0 < vc then (13, false) else if vc = 0 then (12, false) else (11, false)
  else if hc = 0 then
    if 0 < vc then (10, false) else if vc = 0 then (9, false) else (10, true)
  else
    if 0 < vc then (11, true) else if vc = 0 then (12, true) else (13, true)

/-! ## Table D.4 — magnitude refinement (D.3.3) -/

/-- Table D.4: the magnitude-refinement context. `firstRefinement`: this is the first
refinement of the coefficient (it became significant in an earlier bit-plane and has not been
refined yet); `anySigNeighbour`: `ΣH + ΣV + ΣD ≥ 1`. Rows: not first refinement → 16; first
refinement with `ΣH + ΣV + ΣD ≥ 1` → 15; first refinement with no significant neighbour → 14. -/
def mrContext (firstRefinement anySigNeighbour : Bool) : Nat :=
  if !firstRefinement then 16 else if anySigNeighbour then 15 else 14

/-! ## Run-length and UNIFORM contexts (D.3.4), initial states (D.7) -/

/-- The run-length context (cleanup pass, D.3.4). -/
def ctxRunLength : Nat := 17

/-- The UNIFORM context (cleanup pass run interruption, D.3.4; segmentation symbol, D.5). -/
def ctxUniform : Nat := 18

/-- The number of Tier-1 contexts. -/
def numContexts : Nat := 19

/-- The zero-coding context of a coefficient whose eight neighbours are all insignificant. -/
def ctxAllZero : Nat := 0

/-- Initial MQ state index of context `cx` (T.800 D.7, Table D.7): UNIFORM state 46,
run-length state 3, all-zero-neighbours zero-coding context state 4, all others state 0
(all with `MPS = 0`). -/
def initialState (cx : Nat) : Nat :=
  if cx = ctxUniform then 46
  else if cx = ctxRunLength then 3
  else if cx = ctxAllZero then 4
  else 0

/-- The initial state indices of contexts `0 … 18` (Table D.7), in the form
`Spec.MQ.initContexts` takes. -/
def initialStates : List Nat := (List.range numContexts).map initialState

/-! ## Sanity lemmas -/

/-- `initialStates` written out (the list `JPEG2000.MQ.tier1Inits`). -/
theorem initialStates_eq : initialStates = [4] ++ List.replicate 16 0 ++ [3, 46] := by decide

/-- There are `numContexts = 19` initial states. -/
theorem initialStates_length : initialStates.length = numContexts := by decide

/-- LL and LH use the same column of Table D.1. -/
theorem zcContext_LL_eq_LH : zcContext .LL = zcContext .LH := rfl

/-- The HL column of Table D.1 is the LH column with `ΣH` and `ΣV` exchanged. -/
theorem zcContext_HL_swap (h v d : Nat) : zcContext .HL h v d = zcContext .LH v h d := rfl

/-- The HH column of Table D.1 is symmetric in `ΣH` and `ΣV`. -/
theorem zcContext_HH_symm (h v d : Nat) : zcContext .HH h v d = zcContext .HH v h d := by
  simp only [zcContext, Nat.add_comm]

/-- Counts above their range (`ΣH, ΣV > 2`, `ΣD > 4`) read as the largest row. -/
theorem zcContext_clamp (o : Orientation) (h v d : Nat) :
    zcContext o h v d = zcContext o (min h 2) (min v 2) (min d 4) := by
  rcases h with _ | _ | _ | h <;> rcases v with _ | _ | _ | v <;>
    rcases d with _ | _ | _ | _ | _ | d <;> cases o <;>
    simp [zcContext, zcTableLLLH, zcTableHH, Nat.add_assoc]

/-- Every zero-coding context is in `0 … 8`. -/
theorem zcContext_le (o : Orientation) (h v d : Nat) : zcContext o h v d ≤ 8 := by
  rw [zcContext_clamp]
  have key : ∀ h < 3, ∀ v < 3, ∀ d < 5, zcContext o h v d ≤ 8 := by cases o <;> decide
  exact key _ (by omega) _ (by omega) _ (by omega)

/-- Zero-coding context 0 is exactly "all eight neighbours insignificant" (the context that
Table D.7 starts in state 4). -/
theorem zcContext_eq_zero_iff (o : Orientation) (h v d : Nat) :
    zcContext o h v d = 0 ↔ h = 0 ∧ v = 0 ∧ d = 0 := by
  rw [zcContext_clamp]
  have key : ∀ h < 3, ∀ v < 3, ∀ d < 5, (zcContext o h v d = 0 ↔ h = 0 ∧ v = 0 ∧ d = 0) := by
    cases o <;> decide
  rw [key _ (by omega) _ (by omega) _ (by omega)]
  omega

/-- Zero-coding contexts are monotone in `ΣH` (in-range counts). -/
theorem zcContext_mono_h (o : Orientation) :
    ∀ h < 2, ∀ v < 3, ∀ d < 5, zcContext o h v d ≤ zcContext o (h + 1) v d := by
  cases o <;> decide

/-- Zero-coding contexts are monotone in `ΣV` (in-range counts). -/
theorem zcContext_mono_v (o : Orientation) :
    ∀ h < 3, ∀ v < 2, ∀ d < 5, zcContext o h v d ≤ zcContext o h (v + 1) d := by
  cases o <;> decide

/-- Zero-coding contexts are monotone in `ΣD` (in-range counts). -/
theorem zcContext_mono_d (o : Orientation) :
    ∀ h < 3, ∀ v < 3, ∀ d < 4, zcContext o h v d ≤ zcContext o h v (d + 1) := by
  cases o <;> decide

/-- Table D.2 is symmetric in the two neighbours. -/
theorem signContribution_comm (a b : NeighbourSign) :
    signContribution a b = signContribution b a := by
  cases a <;> cases b <;> rfl

/-- Every contribution is `-1`, `0` or `1`. -/
theorem signContribution_range (a b : NeighbourSign) :
    signContribution a b = -1 ∨ signContribution a b = 0 ∨ signContribution a b = 1 := by
  cases a <;> cases b <;> decide

/-- Table D.2 is the clamped sum of the neighbours' signs: "one positive, one negative"
cancels, "two positive" counts as one. -/
theorem signContribution_eq_clamp (a b : NeighbourSign) :
    let s : NeighbourSign → Int := fun | .positive => 1 | .negative => -1 | _ => 0
    signContribution a b = max (-1) (min 1 (s a + s b)) := by
  cases a <;> cases b <;> decide

/-- Every sign-coding context is in `9 … 13`. -/
theorem scContext_range (hc vc : Int) :
    9 ≤ (scContext hc vc).1 ∧ (scContext hc vc).1 ≤ 13 := by
  simp only [scContext]; repeat' split
  all_goals decide

/-- Negating both contributions keeps the context. -/
theorem scContext_neg_fst (hc vc : Int) : (scContext (-hc) (-vc)).1 = (scContext hc vc).1 := by
  simp only [scContext]; repeat' split
  all_goals first | rfl | omega

/-- Negating both contributions flips `XORbit`, except at `(0, 0)` (context 9, `XORbit` 0):
Table D.3 codes the sign relative to the neighbours' prevailing sign. -/
theorem scContext_neg_snd : ∀ hc ∈ ([-1, 0, 1] : List Int), ∀ vc ∈ ([-1, 0, 1] : List Int),
    (hc, vc) ≠ (0, 0) → (scContext (-hc) (-vc)).2 = !(scContext hc vc).2 := by decide

/-- The `(0, 0)` row of Table D.3: context 9, `XORbit` 0. -/
theorem scContext_zero : scContext 0 0 = (9, false) := by decide

/-- Every magnitude-refinement context is in `14 … 16`. -/
theorem mrContext_range (f s : Bool) : 14 ≤ mrContext f s ∧ mrContext f s ≤ 16 := by
  cases f <;> cases s <;> decide

/-- The 19 contexts are partitioned: zero coding `< 9 ≤` sign coding `< 14 ≤` magnitude
refinement `< 17` = run-length `< 18` = UNIFORM `< 19` = `numContexts`. -/
theorem contexts_partition :
    ctxRunLength = 17 ∧ ctxUniform = 18 ∧ numContexts = 19 ∧ ctxAllZero = 0 := by decide

end JPEG2000.Spec.Tier1
