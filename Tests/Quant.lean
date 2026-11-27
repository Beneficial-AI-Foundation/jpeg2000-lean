import JPEG2000.Quant
import JPEG2000.Tier1.Decode
import JPEG2000.DWT53
import Spec.Quant
import Spec.Tier1.Decode
import Spec.DWT53
import Encode.MQ
import Tests.Tier1Spec

/-!
# Tests: dequantisation and ROI max-shift (task 5.1)

Plan.md §4 (C8, C9), §5.4; T.800 Annex E (E-2…E-7), Annex H.

1. **Hand cases** for E-2 (`Mb`), E-3/E-4 (`Δb`, gains of Table E-1, negative `Rb − εb`),
   E-5 (derived quantisation as `Header.bandSteps` expands it, and its error for
   `εo < NL − 1`), E-6 (literal form vs `reconstructIrrev`), reversible reconstruction with
   all bit-planes and truncated (`Nb < Mb`), ROI unshift of ROI and background coefficients.
2. **OpenJPEG transcriptions**: `opj_dwt_encode_stepsize` (the encoder's
   `(expn, mant)` of a step size) composed with our E-3 gives the step back within the
   mantissa precision; the decoder's step formula of `opj_tcd_init_tile` (gain 0 for 9/7,
   `BUG_WEIRD_TWO_INVK`) is ours divided by `2^gain`; the Tier-1 output scaling of
   `opj_t1_clbl_decode_processor` (`2·mag + 2^lsb`, ROI threshold on that doubled value,
   `/2` for 5/3, `·Δ/2` for 9/7) agrees with ours whenever background magnitudes stay below
   `2^(s−1)`, and one case shows the documented difference above it.
3. **Kernels vs spec on random inputs**: `revCoeff` = `sat32 ∘ dequantRev` with the flag
   (also covered by the proof `revCoeff_eq`); `irrevCoeff` within `1/2` of
   `dequantIrrevScaled` when its flag is set, exact when `Rb + F ≥ εb + 12`, and a cleared
   flag only when the exact value is out of the `Int32` range (or `lsb > 33`).
4. **Blocks, fast = spec**: random code-blocks are coded with the test encoder, decoded by
   the fast Tier-1 and the spec, dequantised by `dequantBlock` into a tile-component plane at
   a random position (random tile-component rectangle, levels, resolution, band); the plane
   is read back through `DWT53.toDec` (the absolute band coordinates the 5/3 consumes) and
   every block cell must equal the spec value (reversible) or be within `1/2` of it
   (irreversible); no other cell may change.

Environment: `JPEG2000_QUANT_CASES` (random kernel cases, default 3000),
`JPEG2000_QUANT_BLOCKS` (random blocks, default 120).
-/

namespace JPEG2000.Tests.Quant

open JPEG2000 JPEG2000.Bytes
open JPEG2000.Header (Rect)
open JPEG2000.Tier2.Geometry (Band bandRect bandLevel)
open JPEG2000.Spec.Quant
open JPEG2000.Spec.Tier1 (Coeff)
open JPEG2000.Tests.Tier1Spec (Blk plainTrace below)

/-- Runs one named check, printing a line on failure; 1 on failure, 0 on success. -/
def expect (name : String) (ok : Bool) : IO Nat := do
  if ok then return 0
  IO.eprintln s!"  FAIL quant: {name}"
  return 1

/-- Number from an environment variable, or a default. -/
def envNat (name : String) (dflt : Nat) : IO Nat := do
  match ← IO.getEnv name with
  | some v => return v.trimAscii.toString.toNat?.getD dflt
  | none => return dflt

/-- A coefficient from sign, magnitude and last plane. -/
def co (neg : Bool) (mag lsb : Nat) : Coeff :=
  { sig := mag != 0, sign := neg, mag, lsbPlane := lsb }

/-- `|x| ≤ 1/2` in `Rat`. -/
def withinHalf (x : Rat) : Bool := decide (x ≤ 1 / 2) && decide (-(1 / 2) ≤ x)

/-! ## 1. Hand cases -/

/-- E-2 … E-6 and Annex H by hand. -/
def handChecks : IO Nat := do
  let mut f := 0
  -- E-2
  f := f + (← expect "Mb = G + eps - 1 (G 2, eps 9)" (magBits 2 9 == 10))
  f := f + (← expect "Mb with G 1, eps 0 is 0" (magBits 1 0 == 0))
  -- E-3 / E-4 / Table E-1
  f := f + (← expect "gains LL 0 HL 1 LH 1 HH 2"
    ([Band.LL, .HL, .LH, .HH].map log2Gain == [0, 1, 1, 2]))
  f := f + (← expect "Rb = depth + gain" (nominalRange 8 .HH == 10))
  f := f + (← expect "Delta = 1 (8-bit LL, eps 8, mu 0)" (stepSize 8 0 8 0 == 1))
  f := f + (← expect "Delta = 3 (8-bit HH, eps 9, mu 1024)" (stepSize 8 2 9 1024 == 3))
  f := f + (← expect "Delta = 1/16 (8-bit LL, eps 12, mu 0)" (stepSize 8 0 12 0 == 1 / 16))
  f := f + (← expect "Delta = 2^-2 * (1 + 2047/2048) (depth 1, HL, eps 4, mu 2047)"
    (stepSize 1 1 4 2047 == (1 / 4) * (1 + 2047 / 2048)))
  -- E-5 through Header.bandSteps
  let base : Marker.StepSize := { exponent := 10, mantissa := 100 }
  match Header.bandSteps 0 3 (.derived base) with
  | .error _ => f := f + (← expect "derived bandSteps (NL 3) succeeds" false)
  | .ok st =>
    f := f + (← expect "derived: 10 steps" (st.size == 10))
    f := f + (← expect "derived exponents 10,10,10,10,9,9,9,8,8,8"
      (st.toList.map (·.exponent.toNat) == [10, 10, 10, 10, 9, 9, 9, 8, 8, 8]))
    f := f + (← expect "derived mantissas all 100" (st.toList.all (·.mantissa == 100)))
    let ok := (List.range 4).all fun r =>
      (if r = 0 then [Band.LL] else [Band.HL, .LH, .HH]).all fun b =>
        (st.getD (bandIndex r b) default).exponent.toNat == derivedExponent 10 3 (bandLevel 3 r)
    f := f + (← expect "derived exponents = E-5 eps_o - NL + nb" ok)
  f := f + (← expect "derived with eps_o < NL - 1 is an error"
    ((Header.bandSteps 0 5 (.derived { exponent := 2, mantissa := 0 })).toOption.isNone))
  -- E-6 and the reversible rule
  f := f + (← expect "rev full planes: -5" (reconstructRev (co true 5 0) == -5))
  f := f + (← expect "rev truncated (lsb 2): 12 -> 14" (reconstructRev (co false 12 2) == 14))
  f := f + (← expect "rev truncated (lsb 1): -6 -> -7" (reconstructRev (co true 6 1) == -7))
  f := f + (← expect "rev zero stays zero" (reconstructRev (co true 0 3) == 0))
  f := f + (← expect "irrev full planes: 5 -> 5.5 Delta" (reconstructIrrev 2 (co false 5 0) == 11))
  f := f + (← expect "irrev truncated: -12 (lsb 2) -> -14 Delta"
    (reconstructIrrev (1 / 4) (co true 12 2) == -(14 / 4)))
  f := f + (← expect "irrev = E-6 literal (Mb 10, Nb 8)"
    (reconstructIrrev 3 (co true 12 2) == reconstructE6 (1 / 2) 10 8 (-12) 3))
  -- Annex H
  f := f + (← expect "ROI: 40 (= 5 * 2^3, lsb 3) -> 5, lsb 0"
    (roiUnshift 3 (co false 40 3) == co false 5 0))
  f := f + (← expect "ROI truncated: 48 (lsb 4) -> 6, lsb 1 -> rev 6 + 1"
    (dequantRev 3 (co false 48 4) == 7))
  f := f + (← expect "background 6 < 2^3 kept" (roiUnshift 3 (co true 6 1) == co true 6 1))
  f := f + (← expect "s = 0 is the identity" (roiUnshift 0 (co true 13 2) == co true 13 2))
  return f

/-! ## 2. OpenJPEG transcriptions -/

/-- `opj_int_floorlog2`. -/
def floorLog2 (a : Nat) : Nat := Nat.log2 a

/-- `opj_dwt_encode_stepsize(stepsize, numbps)`: `(expn, mant)` from a step size scaled by
`2^13` (`(OPJ_INT32) floor(stepsize * 8192.0)`) and `numbps = prec + gain`. -/
def opjEncodeStepsize (stepsize numbps : Nat) : Int × Nat :=
  let p : Int := (floorLog2 stepsize : Int) - 13
  let n : Int := 11 - (floorLog2 stepsize : Int)
  let mant := (if n < 0 then stepsize >>> (-n).toNat else stepsize <<< n.toNat) % 2048
  ((numbps : Int) - p, mant)

/-- OpenJPEG decoder step size (`opj_tcd_init_tile`): `(1 + mant/2048) · 2^(Rb − expn)` with
`Rb = prec + log2_gain`, where `log2_gain` is 0 for every band of a 9/7 component. -/
def opjDecodeStep (prec gain expn mant : Nat) (irreversible : Bool) : Rat :=
  let g := if irreversible then 0 else gain
  stepSize prec g expn mant

/-- OpenJPEG's Tier-1 output for a coefficient: `±(2·mag + 2^lsb)` (0 if insignificant). -/
def opjDatap (c : Coeff) : Int :=
  if c.mag = 0 then 0
  else
    let v : Int := 2 * c.mag + 2 ^ c.lsbPlane
    if c.sign then -v else v

/-- OpenJPEG's ROI step on `datap`: `|v| ≥ 2^s` → `|v| >> s`. -/
def opjRoi (s : Nat) (v : Int) : Int :=
  if s = 0 then v
  else
    let m := v.natAbs
    if m ≥ 2 ^ s then (if v < 0 then -((m / 2 ^ s : Nat) : Int) else ((m / 2 ^ s : Nat) : Int))
    else v

/-- OpenJPEG's 5/3 step: C division by 2 (truncation toward zero). -/
def opjRev (v : Int) : Int := v.tdiv 2

/-- OpenJPEG cross-checks. -/
def opjChecks : IO Nat := do
  let mut f := 0
  -- encode_stepsize then our E-3: within 2^-11 relative (the mantissa has 11 bits)
  let mut bad := 0
  for i in [0:400] do
    let prec := 1 + i % 16
    let gain := i % 3
    -- step sizes 2^-6 … 2^10 as integers scaled by 2^13, varied mantissas
    let scaled := (8192 * (i + 1) * 37 / 64) + 1
    let (expn, mant) := opjEncodeStepsize scaled (prec + gain)
    if expn < 0 then continue
    let d := stepSize prec gain expn.toNat mant
    let orig : Rat := (scaled : Rat) / 8192
    -- relative error < 2^-11 (truncation of the mantissa)
    if !(d ≤ orig && orig - d < orig / 2048) then bad := bad + 1
  f := f + (← expect s!"opj_dwt_encode_stepsize ∘ E-3 within 2^-11 ({bad} bad)" (bad == 0))
  -- decoder formula: ours = OpenJPEG's (9/7: gain 0) · 2^gain
  let ok := (List.range 200).all fun i =>
    let prec := 1 + i % 16
    let gain := i % 3
    let e := i % 32
    let m := (i * 97) % 2048
    stepSize prec gain e m == opjDecodeStep prec gain e m true * (2 ^ gain : Nat) &&
      stepSize prec gain e m == opjDecodeStep prec gain e m false
  f := f + (← expect "E-3 = OpenJPEG step (9/7 gain 0, times 2^gain)" ok)
  -- Tier-1 scaling, reversible and irreversible, no ROI
  let mut s := (7 : UInt64)
  let mut badR := 0
  let mut badI := 0
  for _ in [0:2000] do
    let (lsb, s1) := below s 12
    let (q, s2) := below s1 4096
    let (ng, s3) := below s2 2
    s := s3
    let c := co (ng == 1) (q * 2 ^ lsb) lsb
    if (opjRev (opjDatap c) : Int) != dequantRev 0 c then badR := badR + 1
    if ((opjDatap c : Int) : Rat) * (3 / 8) / 2 != dequantIrrev 0 (3 / 8) c then badI := badI + 1
  f := f + (← expect s!"OpenJPEG 5/3 scaling = ours ({badR} bad)" (badR == 0))
  f := f + (← expect s!"OpenJPEG 9/7 scaling = ours ({badI} bad)" (badI == 0))
  -- ROI: agreement when background magnitudes stay below 2^(s-1)
  let mut badRoi := 0
  for _ in [0:2000] do
    let (sh, s1) := below s 6
    let sh := sh + 1
    let (roi, s2) := below s1 2
    let (q, s3) := below s2 64
    let (lsb, s4) := below s3 (sh + 6)
    let (ng, s5) := below s4 2
    s := s5
    -- ROI: magnitude q·2^s + bits below; background: < 2^(s-1), multiple of 2^lsb
    let c :=
      if roi == 1 then co (ng == 1) ((q + 1) * 2 ^ sh) (if lsb ≥ sh then lsb else 0)
      else
        let l := lsb % sh
        let m := (q * 2 ^ l) % 2 ^ (sh - 1)
        co (ng == 1) (m - m % 2 ^ l) l
    -- the doubled-scale OpenJPEG threshold sees 2·mag + 2^lsb < 2^s for such background
    if c.mag != 0 && c.mag < 2 ^ sh && 2 * c.mag + 2 ^ c.lsbPlane ≥ 2 ^ sh then continue
    if opjRev (opjRoi sh (opjDatap c)) != dequantRev sh c then badRoi := badRoi + 1
  f := f + (← expect s!"OpenJPEG ROI = ours below 2^(s-1) ({badRoi} bad)" (badRoi == 0))
  -- the documented difference: background magnitude 2^(s-1)
  let c := co false 4 2
  f := f + (← expect "OpenJPEG ROI differs at background 2^(s-1) (s 3, mag 4)"
    (dequantRev 3 c == 6 && opjRev (opjRoi 3 (opjDatap c)) == 0))
  return f

/-! ## 3. Kernels vs spec -/

/-- A random `Int32`, often small, sometimes extreme. -/
def randI32 (s : UInt64) : Int32 × UInt64 :=
  let (sel, s) := below s 8
  if sel == 0 then
    let (k, s) := below s 4
    ((#[(-2147483648 : Int32), 2147483647, -2147483647, 0].getD k 0), s)
  else
    let (bits, s) := below s 32
    let (m, s) := below s (2 ^ bits)
    let (ng, s) := below s 2
    (Int32.ofInt (if ng == 1 then -(m : Int) else m), s)

/-- Random reversible and irreversible kernel checks. -/
def kernelChecks (n : Nat) : IO Nat := do
  let mut f := 0
  let mut s := (12345 : UInt64)
  let mut badR := 0
  let mut badI := 0
  let mut badSat := 0
  for _ in [0:n] do
    let (v, s1) := randI32 s
    let (lsb, s2) := below s1 36
    let (sh, s3) := below s2 12
    let (bigS, s4) := below s3 16
    let sh := if bigS == 0 then sh * 6 else if sh < 6 then 0 else sh - 5
    let (rng, s5) := below s4 40
    let (ex, s6) := below s5 32
    let (mu, s7) := below s6 2048
    let (F, s8) := below s7 24
    s := s8
    let c := Quant.coeffOf v lsb
    -- reversible
    let spec := dequantRev sh c
    let (z, ok) := Quant.revCoeff sh v lsb
    if z != DWT53.sat32 spec || ok != (decide (-2 ^ 31 ≤ spec) && decide (spec < 2 ^ 31)) then
      badR := badR + 1
    -- irreversible
    let q : BandQuant := {
      reversible := false, roiShift := sh, guard := 2, range := rng + 1,
      exponent := ex, mantissa := mu }
    let k := Quant.irrevConsts q F
    let (zi, oki) := Quant.irrevCoeff k sh v lsb
    let X := dequantIrrevScaled sh q.delta F c
    if oki then
      let d := (zi.toInt : Rat) - X
      if !withinHalf d then badI := badI + 1
      if k.up && d != 0 then badI := badI + 1
    else
      let l := (roiUnshift sh c).lsbPlane
      if !(l > 33 || X ≥ 2147483647 + 1 / 2 || X ≤ -(2147483648 + 1 / 2)) then
        badSat := badSat + 1
  f := f + (← expect s!"revCoeff = sat32 ∘ dequantRev ({badR}/{n} bad)" (badR == 0))
  f := f + (← expect s!"irrevCoeff within 1/2, exact upwards ({badI}/{n} bad)" (badI == 0))
  f := f + (← expect s!"irrevCoeff flag cleared only out of range ({badSat} bad)" (badSat == 0))
  return f

/-! ## 4. Blocks: fast = spec through the Mallat layout -/

/-- The spec orientation of a band. -/
def orientOf : Band → Spec.Tier1.Orientation
  | .LL => .LL
  | .HL => .HL
  | .LH => .LH
  | .HH => .HH

/-- The spec grid of band `b` at resolution `r` of a `toDec` decomposition. -/
def gridOf (d : Spec.DWT53.Dec) (nl r : Nat) (b : Band) : Spec.DWT53.Grid :=
  if r = 0 then d.ll
  else
    let (hl, lh, hh) := d.details.getD (bandLevel nl r - 1) (⟨fun _ _ => 0⟩, ⟨fun _ _ => 0⟩, ⟨fun _ _ => 0⟩)
    match b with
    | .HL => hl
    | .LH => lh
    | _ => hh

/-- Number of non-zero cells of a plane. -/
def nonZero (p : Plane) : Nat :=
  (List.range (p.width * p.height)).foldl (fun a i =>
    if (p.get? i).getD 0 != 0 then a + 1 else a) 0

/-- Random magnitudes (a quarter zero) below `2^K` and signs for `n` coefficients. -/
def genMags (s : UInt64) (n K : Nat) : Array Nat × Array Bool × UInt64 := Id.run do
  let mut st := s
  let mut mags : Array Nat := #[]
  let mut negs : Array Bool := #[]
  for _ in [0:n] do
    let (sel, s1) := below st 4
    let (m, s2) := below s1 (2 ^ K)
    let (ng, s3) := below s2 2
    st := s3
    mags := mags.push (if sel == 0 then 0 else m)
    negs := negs.push (ng == 1)
  return (mags, negs, st)

/-- One random block test; `none` on success, otherwise a message. -/
def oneBlock (seed : UInt64) : Option String := Id.run do
  let s := seed
  let (nl, s) := below s 4
  let (x0, s) := below s 20
  let (y0, s) := below s 20
  let (w0, s) := below s 48
  let (h0, s) := below s 48
  let tc : Rect := { x0, y0, x1 := x0 + w0 + 1, y1 := y0 + h0 + 1 }
  let (r, s) := below s (nl + 1)
  let (bi, s) := below s 3
  let b : Band := if r = 0 then .LL else #[Band.HL, .LH, .HH].getD bi .HH
  let band := bandRect tc (bandLevel nl r) b
  if band.x1 ≤ band.x0 || band.y1 ≤ band.y0 then return none
  -- a random sub-rectangle of the band, at most 32 × 32
  let bw := band.x1 - band.x0
  let bh := band.y1 - band.y0
  let (cx, s) := below s bw
  let (cy, s) := below s bh
  let (cw, s) := below s (min 32 (bw - cx))
  let (ch, s) := below s (min 32 (bh - cy))
  let cb : Rect := {
    x0 := band.x0 + cx, y0 := band.y0 + cy,
    x1 := band.x0 + cx + cw + 1, y1 := band.y0 + cy + ch + 1 }
  let w := cw + 1
  let h := ch + 1
  let (K, s) := below s 14
  let K := K + 1
  let (sh, s) := below s 4
  let sh := if sh == 3 then 0 else sh * 2
  let (mags, negs, s) := genMags s (w * h) K
  let blk : Blk := { w, h, orient := orientOf b, K, zbp := 1, mags, negs }
  let (np, s) := below s (3 * K - 2)
  let n := np + 1
  let code := Encode.MQ.encodeAll Spec.Tier1.initialStates (plainTrace blk n)
  let buf : ByteArray := ⟨code.toArray⟩
  let fast := Tier1.decodeCodeBlock buf 0 code.length w h b (K + 1) 1 n
  let scb : Spec.Tier1.CodeBlock := {
    width := w, height := h, orient := orientOf b, numBitPlanes := K + 1, zeroBitPlanes := 1,
    segments := Spec.Tier1.Segment.single n code }
  let spec := Spec.Tier1.decodeCodeBlock scb
  let (rev, s) := below s 2
  let (F, s) := below s 16
  let (ex, s) := below s 20
  let (mu, _) := below s 2048
  let q : BandQuant := {
    reversible := rev == 1, roiShift := sh, guard := 2, range := 9,
    exponent := ex, mantissa := mu }
  match fast, spec with
  | .error e, _ => return some s!"fast Tier-1 error {repr e}"
  | _, .error e => return some s!"spec Tier-1 error {repr e}"
  | .ok o, .ok cs =>
    let dst := Plane.zero (tc.x1 - tc.x0) (tc.y1 - tc.y0)
    match Quant.dequantBlock dst tc nl r b cb q F o with
    | .error e => return some s!"dequantBlock error {repr e}"
    | .ok (p, ok) =>
      let g := gridOf (DWT53.toDec p tc nl) nl r b
      let mut bad := 0
      let mut nz := 0
      for y in [0:h] do
        for x in [0:w] do
          let c := cs.getD (y * w + x) {}
          let got := g.get ((cb.x0 + x : Nat) : Int) ((cb.y0 + y : Nat) : Int)
          if got != 0 then nz := nz + 1
          if q.reversible then
            if got != (DWT53.sat32 (dequantRev sh c)).toInt then bad := bad + 1
          else
            let X := dequantIrrevScaled sh q.delta F c
            if ok && !withinHalf ((got : Rat) - X) then bad := bad + 1
      if bad != 0 then
        return some s!"{bad} bad cells (tc {repr tc}, nl {nl}, r {r}, {repr b}, cb {repr cb})"
      if nonZero p != nz then
        return some s!"cells outside the block changed ({nonZero p} vs {nz})"
      return none

/-- Random block tests. -/
def blockChecks (n : Nat) : IO Nat := do
  let mut f := 0
  let mut s := (99 : UInt64)
  for i in [0:n] do
    let (seed, s1) := Tests.Tier1Spec.splitmix s
    s := s1
    match oneBlock seed with
    | none => pure ()
    | some msg => f := f + (← expect s!"block {i}: {msg}" false)
  return f

/-- Argument checks of `dequantBlock`. -/
def argChecks : IO Nat := do
  let mut f := 0
  let tc : Rect := { x0 := 0, y0 := 0, x1 := 8, y1 := 8 }
  let o : Tier1.CodeBlockOut := {
    plane := Plane.zero 2 2, flags := #[], codedPlanes := 0, numPasses := 0 }
  let q : BandQuant := default
  let isErr (x : Except Error (Plane × Bool)) : Bool := match x with
    | .error _ => true
    | .ok _ => false
  f := f + (← expect "wrong plane size"
    (isErr (Quant.dequantBlock (Plane.zero 7 8) tc 1 1 .HL ⟨0, 0, 2, 2⟩ q 0 o)))
  f := f + (← expect "r > NL"
    (isErr (Quant.dequantBlock (Plane.zero 8 8) tc 1 2 .HL ⟨0, 0, 2, 2⟩ q 0 o)))
  f := f + (← expect "block outside band"
    (isErr (Quant.dequantBlock (Plane.zero 8 8) tc 1 1 .HL ⟨3, 0, 5, 2⟩ q 0 o)))
  f := f + (← expect "block plane size mismatch"
    (isErr (Quant.dequantBlock (Plane.zero 8 8) tc 1 1 .HL ⟨0, 0, 3, 2⟩ q 0 o)))
  f := f + (← expect "valid call succeeds"
    (!isErr (Quant.dequantBlock (Plane.zero 8 8) tc 1 1 .HL ⟨0, 0, 2, 2⟩ q 0 o)))
  return f

/-- The suite: number of failures. -/
def run : IO Nat := do
  let n ← envNat "JPEG2000_QUANT_CASES" 3000
  let nb ← envNat "JPEG2000_QUANT_BLOCKS" 120
  let mut f := 0
  f := f + (← handChecks)
  f := f + (← opjChecks)
  f := f + (← kernelChecks n)
  f := f + (← argChecks)
  f := f + (← blockChecks nb)
  return f

end JPEG2000.Tests.Quant
