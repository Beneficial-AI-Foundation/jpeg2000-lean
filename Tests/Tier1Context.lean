import Spec.Tier1.Context
import JPEG2000.MQ

/-!
# Unit tests: Tier-1 context tables (task 3.1)

Plan.md §4 (C3), §5.2 "Tier-1 / EBCOT"; T.800 Annex D (Tables D.1–D.4, D.7).

`Spec.Tier1.Context` is compared entrywise, over every input, with an independent
transcription of OpenJPEG's LUT generator (`src/lib/openjp2/t1_generate_luts.c`:
`t1_init_ctxno_zc`, `t1_init_ctxno_sc`, `t1_init_spb`; `t1.c`: `opj_t1_getctxno_mag`),
written here over OpenJPEG's own flag-word bit layout (`t1.h`). Then a few rows of each
table are checked by hand against the standard.

OpenJPEG conventions used below:

* `T1_SIGMA_0 … T1_SIGMA_8` = significance of NW, N, NE, W, (this), E, SW, S, SE.
* `T1_LUT_SGN_W = 1, T1_LUT_SIG_N = 2, T1_LUT_SGN_E = 4, T1_LUT_SIG_W = 8,
  T1_LUT_SGN_N = 16, T1_LUT_SIG_E = 32, T1_LUT_SGN_S = 64, T1_LUT_SIG_S = 128`
  (a set `SGN` bit means negative).
* `T1_MU_0`: the coefficient has already been refined (so "not first refinement").
* Orientation: OpenJPEG's `band->bandno` is `0 = LL, 1 = HL, 2 = LH, 3 = HH`. The generator
  stores `t1_init_ctxno_zc(f, j)` at table `j` with 1 and 2 exchanged; `t1_init_ctxno_zc`
  swaps H and V for `j = 2`. So the look-up for `bandno` `b` computes
  `t1_init_ctxno_zc(f, swap12 b)`, i.e. HL (`bandno 1`) is the swapped table, as T.800 says.
-/

namespace JPEG2000.Tests.Tier1Context

open JPEG2000.Spec.Tier1

/-- Runs one named check, printing a line on failure; returns 1 on failure, 0 on success. -/
def expect (name : String) (ok : Bool) : IO Nat := do
  if ok then return 0
  IO.eprintln s!"  FAIL tier1ctx: {name}"
  return 1

/-- Bit `i` of `f` as `0/1`. -/
def bit (f i : Nat) : Nat := f / 2 ^ i % 2

/-- Is bit `i` of `f` set? -/
def isSet (f i : Nat) : Bool := bit f i == 1

/-! ## OpenJPEG's generator, transcribed -/

/-- `t1_init_ctxno_zc(f, orient)` (`T1_CTXNO_ZC = 0`), with OpenJPEG's generator
orientation `orient` (0, 1: no swap; 2: swap H and V; 3: diagonal). -/
def opjZc (f orient : Nat) : Nat := Id.run do
  let mut h := bit f 3 + bit f 5
  let mut v := bit f 1 + bit f 7
  let d := bit f 0 + bit f 2 + bit f 8 + bit f 6
  let mut n := 0
  if orient == 2 then
    let t := h
    h := v
    v := t
  if orient != 3 then
    if h == 0 then
      if v == 0 then
        if d == 0 then n := 0 else if d == 1 then n := 1 else n := 2
      else if v == 1 then n := 3
      else n := 4
    else if h == 1 then
      if v == 0 then
        if d == 0 then n := 5 else n := 6
      else n := 7
    else n := 8
  else
    let hv := h + v
    if d == 0 then
      if hv == 0 then n := 0 else if hv == 1 then n := 1 else n := 2
    else if d == 1 then
      if hv == 0 then n := 3 else if hv == 1 then n := 4 else n := 5
    else if d == 2 then
      if hv == 0 then n := 6 else n := 7
    else n := 8
  return n

/-- The generator's table exchange: `lut_ctxno_zc[(swap12 j) << 9 | f] = t1_init_ctxno_zc(f, j)`
(`swap12` is an involution, so table `b` holds `t1_init_ctxno_zc(f, swap12 b)`). -/
def swap12 : Nat → Nat
  | 1 => 2
  | 2 => 1
  | j => j

/-- OpenJPEG's `lut_ctxno_zc[(bandno << 9) | f]`. -/
def opjLutZc (bandno f : Nat) : Nat := opjZc f (swap12 bandno)

/-- OpenJPEG's `band->bandno` of a T.800 orientation. -/
def bandno : Orientation → Nat
  | .LL => 0
  | .HL => 1
  | .LH => 2
  | .HH => 3

/-- `min(a, 1)` as in `opj_int_min(…, 1)`. -/
def min1 (a : Nat) : Int := if a ≥ 1 then 1 else 0

/-- `(f & (sig | sgn)) == sig`: significant, positive. -/
def posAt (f sig sgn : Nat) : Nat := if isSet f sig && !isSet f sgn then 1 else 0

/-- `(f & (sig | sgn)) == (sig | sgn)`: significant, negative. -/
def negAt (f sig sgn : Nat) : Nat := if isSet f sig && isSet f sgn then 1 else 0

/-- OpenJPEG's `hc` (bits: SIG_E = 5, SGN_E = 2, SIG_W = 3, SGN_W = 0). -/
def opjHc (f : Nat) : Int :=
  min1 (posAt f 5 2 + posAt f 3 0) - min1 (negAt f 5 2 + negAt f 3 0)

/-- OpenJPEG's `vc` (bits: SIG_N = 1, SGN_N = 4, SIG_S = 7, SGN_S = 6). -/
def opjVc (f : Nat) : Int :=
  min1 (posAt f 1 4 + posAt f 7 6) - min1 (negAt f 1 4 + negAt f 7 6)

/-- `t1_init_ctxno_sc(f)` (`T1_CTXNO_SC = 9`). -/
def opjSc (f : Nat) : Nat := Id.run do
  let mut hc := opjHc f
  let mut vc := opjVc f
  let mut n := 0
  if hc < 0 then
    hc := -hc
    vc := -vc
  if hc == 0 then
    if vc == -1 then n := 1 else if vc == 0 then n := 0 else n := 1
  else if hc == 1 then
    if vc == -1 then n := 2 else if vc == 0 then n := 3 else n := 4
  return 9 + n

/-- `t1_init_spb(f)`: the sign-prediction (XOR) bit. -/
def opjSpb (f : Nat) : Bool :=
  let hc := opjHc f
  let vc := opjVc f
  if hc == 0 && vc == 0 then false else !(hc > 0 || (hc == 0 && vc > 0))

/-- `opj_t1_getctxno_mag(f)` with `T1_CTXNO_MAG = 14`; `mu` = `f & T1_MU_0`, `nbrs` =
`f & T1_SIGMA_NEIGHBOURS`. -/
def opjMag (mu : Bool) (nbrs : Nat) : Nat :=
  let tmp := if nbrs != 0 then 14 + 1 else 14
  if mu then 14 + 2 else tmp

/-! ## The spec, driven from the same flag words -/

/-- `zcContext` from an OpenJPEG `T1_SIGMA` neighbourhood word. -/
def specZc (o : Orientation) (f : Nat) : Nat :=
  zcContext o (bit f 3 + bit f 5) (bit f 1 + bit f 7) (bit f 0 + bit f 2 + bit f 6 + bit f 8)

/-- Table D.2 neighbour state from `T1_LUT` significance / sign bits. -/
def nb (f sig sgn : Nat) : NeighbourSign := NeighbourSign.ofBits (isSet f sig) (isSet f sgn)

/-- `scContext` from an OpenJPEG `T1_LUT` sign-context word. -/
def specSc (f : Nat) : Nat × Bool :=
  scContext (signContribution (nb f 3 0) (nb f 5 2)) (signContribution (nb f 1 4) (nb f 7 6))

/-- The `T1_SIGMA_NEIGHBOURS` bits of `f`. -/
def neighbourBits (f : Nat) : Nat :=
  [0, 1, 2, 3, 5, 6, 7, 8].foldl (fun acc i => acc + bit f i * 2 ^ i) 0

/-! ## Suite -/

/-- Runs the suite; returns the number of failures. -/
def run : IO Nat := do
  let mut f := 0
  -- Exhaustive zero coding: 4 orientations × all 512 `T1_SIGMA_0..8` words.
  for o in Orientation.all do
    let bad := (List.range 512).filter fun w => specZc o w != opjLutZc (bandno o) w
    f := f + (← expect s!"zcContext {repr o} vs OpenJPEG lut_ctxno_zc ({bad.length} mismatches)"
      bad.isEmpty)
  -- Exhaustive sign coding: all 256 `T1_LUT` words, context and XOR bit.
  let badSc := (List.range 256).filter fun w => (specSc w).1 != opjSc w
  f := f + (← expect s!"scContext vs OpenJPEG lut_ctxno_sc ({badSc.length} mismatches)"
    badSc.isEmpty)
  let badSpb := (List.range 256).filter fun w => (specSc w).2 != opjSpb w
  f := f + (← expect s!"XORbit vs OpenJPEG lut_spb ({badSpb.length} mismatches)"
    badSpb.isEmpty)
  -- Exhaustive magnitude refinement: `T1_MU_0` × all 512 neighbourhood words.
  let badMr := (List.range 1024).filter fun w =>
    let mu := w ≥ 512
    let nbrs := neighbourBits (w % 512)
    mrContext (!mu) (nbrs != 0) != opjMag mu nbrs
  f := f + (← expect s!"mrContext vs opj_t1_getctxno_mag ({badMr.length} mismatches)"
    badMr.isEmpty)
  -- Contribution over all signed neighbour pairs equals OpenJPEG's clamped counts.
  let badHc := (List.range 256).filter fun w =>
    signContribution (nb w 3 0) (nb w 5 2) != opjHc w ||
    signContribution (nb w 1 4) (nb w 7 6) != opjVc w
  f := f + (← expect s!"signContribution vs OpenJPEG hc/vc ({badHc.length} mismatches)"
    badHc.isEmpty)
  -- Hand-picked rows of Table D.1 (LL/LH column).
  f := f + (← expect "D.1 LL ΣH=2" (zcContext .LL 2 0 0 == 8 && zcContext .LL 2 2 4 == 8))
  f := f + (← expect "D.1 LL ΣH=1 ΣV≥1" (zcContext .LL 1 1 0 == 7 && zcContext .LL 1 2 3 == 7))
  f := f + (← expect "D.1 LL ΣH=1 ΣV=0" (zcContext .LL 1 0 1 == 6 && zcContext .LL 1 0 0 == 5))
  f := f + (← expect "D.1 LH ΣH=0" (zcContext .LH 0 2 0 == 4 && zcContext .LH 0 1 4 == 3))
  f := f + (← expect "D.1 LH ΣH=ΣV=0" (zcContext .LH 0 0 3 == 2 && zcContext .LH 0 0 1 == 1 &&
    zcContext .LH 0 0 0 == 0))
  -- HL column: ΣV plays ΣH's role.
  f := f + (← expect "D.1 HL" (zcContext .HL 0 2 0 == 8 && zcContext .HL 2 0 0 == 4 &&
    zcContext .HL 1 1 0 == 7 && zcContext .HL 0 1 2 == 6 && zcContext .HL 1 0 0 == 3))
  -- HH column.
  f := f + (← expect "D.1 HH" (zcContext .HH 0 0 3 == 8 && zcContext .HH 1 0 2 == 7 &&
    zcContext .HH 0 0 2 == 6 && zcContext .HH 1 1 1 == 5 && zcContext .HH 0 1 1 == 4 &&
    zcContext .HH 0 0 1 == 3 && zcContext .HH 2 0 0 == 2 && zcContext .HH 0 1 0 == 1 &&
    zcContext .HH 0 0 0 == 0 && zcContext .HH 2 2 4 == 8))
  -- Table D.2 rows.
  f := f + (← expect "D.2" (signContribution .positive .positive == 1 &&
    signContribution .negative .positive == 0 && signContribution .insignificant .negative == -1 &&
    signContribution .negative .negative == -1 && signContribution .insignificant .insignificant == 0))
  -- Table D.3, all nine rows.
  let d3 : List (Int × Int × Nat × Bool) :=
    [(1, 1, 13, false), (1, 0, 12, false), (1, -1, 11, false), (0, 1, 10, false),
     (0, 0, 9, false), (0, -1, 10, true), (-1, 1, 11, true), (-1, 0, 12, true),
     (-1, -1, 13, true)]
  for (h, v, c, x) in d3 do
    f := f + (← expect s!"D.3 row H={h} V={v}" (scContext h v == (c, x)))
  -- Table D.4.
  f := f + (← expect "D.4" (mrContext false false == 16 && mrContext false true == 16 &&
    mrContext true true == 15 && mrContext true false == 14))
  -- D.3.4 / D.7: numbering and initial states agree with the MQ decoder's.
  f := f + (← expect "run-length 17, UNIFORM 18, 19 contexts"
    (ctxRunLength == 17 && ctxUniform == 18 && numContexts == 19))
  f := f + (← expect "initialStates = JPEG2000.MQ.tier1Inits"
    (initialStates == JPEG2000.MQ.tier1Inits))
  f := f + (← expect "D.7 states" (initialStates.getD ctxUniform 0 == 46 &&
    initialStates.getD ctxRunLength 0 == 3 && initialStates.getD (zcContext .HH 0 0 0) 0 == 4 &&
    initialStates.getD 9 99 == 0 && initialStates.getD 16 99 == 0))
  return f

end JPEG2000.Tests.Tier1Context
