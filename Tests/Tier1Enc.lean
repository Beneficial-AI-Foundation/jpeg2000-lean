import Encode.Tier1
import Spec.Tier1.Decode
import Tests.Tier1Spec

/-!
# Tests: reference Tier-1 encoder, plain mode (task 3.5)

Plan.md §5.3 (reference encoder), §4 (C10); T.800 Annex D.

1. **Round trip.** Random code-blocks (sides 1–64 with area ≤ 4096, plus the 4096-area shapes
   64 × 64, 1024 × 4, 4 × 1024, 256 × 16, 16 × 256; all four orientations; magnitudes up to
   2^15; sparse to dense; `Mb` from `K` to `K + 3`) are encoded with
   `Encode.Tier1.encodeCodeBlock` and decoded with `Spec.Tier1.decodeValues`: the result must
   be the input exactly.
2. **Simulation invariant.** The decoder's final coefficient states (every field) equal the
   encoder's model (`EncState.coeffs` after `encodePasses`) — the invariant a proof of
   `decode ∘ encode = id` would carry.
3. **Agreement with the test-only encoder** of `Tests.Tier1Spec` (OpenJPEG-style, written
   independently): same decision trace, hence the same bytes.
4. **Output fields.** `numPasses = 3K − 2`, `zeroBitPlanes = Mb − K`, `passTraces` has
   `numPasses` entries whose concatenation MQ-encodes to `bytes`, `passEmitted` is monotone
   and bounded by `bytes.length`; argument errors.

`toCodeBlock` is the adapter from the encoder output to the decoder input; it is the only place
that depends on the layout of `Spec.Tier1.CodeBlock`.
-/

namespace JPEG2000.Tests.Tier1Enc

open JPEG2000
open JPEG2000.Spec.Tier1
open JPEG2000.Encode.Tier1
open JPEG2000.Tests.Tier1Spec (expect err? ok? below Blk plainTrace)

/-- Adapter: the decoder's view of an encoded code-block (plain mode, one codeword). -/
def toCodeBlock (w h : Nat) (o : Orientation) (mb : Nat) (out : EncOut) : CodeBlock := {
  width := w, height := h, orient := o, numBitPlanes := mb,
  zeroBitPlanes := out.zeroBitPlanes, segments := Segment.single out.numPasses out.bytes }

/-- A random test block: geometry, `Mb` and the signed coefficients. -/
structure Case where
  /-- Width. -/
  w : Nat
  /-- Height. -/
  h : Nat
  /-- Orientation. -/
  orient : Orientation
  /-- `Mb` passed to the encoder. -/
  mb : Nat
  /-- Coefficients, raster order. -/
  vals : Array Int

/-- A random side length: mostly small, sometimes up to 64. -/
def genSide (s : UInt64) : Nat × UInt64 :=
  let (sel, s) := below s 10
  if sel < 5 then let (v, s) := below s 8; (v + 1, s)
  else if sel < 8 then let (v, s) := below s 24; (v + 1, s)
  else let (v, s) := below s 64; (v + 1, s)

/-- Random coefficients for a `w × h` block. -/
def genVals (s : UInt64) (n : Nat) : Array Int × UInt64 := Id.run do
  let (K, s) := below s 17               -- 0 … 16 bit-planes (magnitudes < 2^16)
  let (density, s) := below s 6          -- 0: very sparse … 5: dense
  let (topBits, s) := below s (K + 1)
  let mut s := s
  let mut vals : Array Int := #[]
  for _ in [0:n] do
    let (r, s1) := below s 8
    let (big, s2) := below s1 16
    let bits := if big == 0 then K else topBits
    let (m, s3) := below s2 (2 ^ bits)
    let (ng, s4) := below s3 2
    s := s4
    let m : Int := if r < density + 1 then m else 0
    vals := vals.push (if ng == 1 then -m else m)
  return (vals, s)

/-- Draw a random case with the given shape (or a random one). -/
def genCase (s : UInt64) (shape : Option (Nat × Nat)) : Case × UInt64 :=
  let (w, h, s) := match shape with
    | some (w, h) => (w, h, s)
    | none =>
      let (w, s) := genSide s
      let (h, s) := genSide s
      (w, if w * h > 4096 then 4096 / w else h, s)
  let (oi, s) := below s 4
  let (vals, s) := genVals s (w * h)
  let (extra, s) := below s 4
  let mb := numBits (maxMag vals) + extra
  ({ w, h, orient := Orientation.all.getD oi .LL, mb, vals }, s)

/-- The test-only encoder's input for the same block (`K` coded planes, magnitudes and
signs). -/
def toBlk (c : Case) (K : Nat) : Blk :=
  { w := c.w, h := c.h, orient := c.orient, K, zbp := c.mb - K,
    mags := c.vals.map Int.natAbs, negs := c.vals.map fun v => decide (v < 0) }

/-- `l` is non-decreasing. -/
def monotone : List Nat → Bool
  | a :: b :: rest => a ≤ b && monotone (b :: rest)
  | _ => true

/-- All checks on one case; `none` if they pass, else a description. -/
def checkCase (c : Case) : Option String :=
  let tag := s!"{c.w}x{c.h} {repr c.orient} Mb={c.mb}"
  match encodeCodeBlock c.w c.h c.orient c.mb c.vals with
  | .error e => some s!"{tag}: encoder error {repr e}"
  | .ok out =>
    let K := out.codedPlanes
    let cb := toCodeBlock c.w c.h c.orient c.mb out
    let g : Geom := { width := c.w, height := c.h, orient := c.orient }
    let model := (encodePasses g c.vals K out.numPasses (EncState.init g)).coeffs
    let fieldsOk :=
      K == numBits (maxMag c.vals) && out.zeroBitPlanes + K == c.mb &&
      out.numPasses == (if K == 0 then 0 else 3 * K - 2) &&
      out.passTraces.length == out.numPasses &&
      (K == 0 || out.bytes == Encode.MQ.encodeAll initialStates out.trace) &&
      out.passEmitted.length == out.numPasses && monotone out.passEmitted &&
      out.passEmitted.all (· ≤ out.bytes.length)
    if !fieldsOk then some s!"{tag}: output fields inconsistent (K={K})"
    else match decodeCodeBlock cb with
    | .error e => some s!"{tag}: decoder error {repr e}"
    | .ok cs =>
      if cs.map Coeff.value != c.vals then some s!"{tag} K={K}: decoded values differ"
      else if cs != model then some s!"{tag} K={K}: decoder state differs from encoder model"
      else if K == 0 then none
      else
        let other := plainTrace (toBlk c K) out.numPasses
        if other != out.trace then
          some s!"{tag} K={K}: trace differs from Tests.Tier1Spec.plainTrace"
        else if Encode.MQ.encodeAll initialStates other != out.bytes then
          some s!"{tag} K={K}: bytes differ from Tests.Tier1Spec.plainTrace"
        else none

/-- Default number of random blocks. -/
def defaultN : Nat := 600

/-- Number of random blocks: `JPEG2000_TIER1ENC_BLOCKS` if set to a number, else
`defaultN`. -/
def numBlocks : IO Nat := do
  match ← IO.getEnv "JPEG2000_TIER1ENC_BLOCKS" with
  | some v => return v.trimAscii.toString.toNat?.getD defaultN
  | none => return defaultN

/-- The 4096-coefficient shapes tested on every run. -/
def bigShapes : List (Nat × Nat) := [(64, 64), (1024, 4), (4, 1024), (256, 16), (16, 256)]

/-- Unit tests: fixed blocks and argument errors. -/
def runUnits : IO Nat := do
  let mut f := 0
  let fixed : List Case := [
    { w := 1, h := 1, orient := .LL, mb := 1, vals := #[-1] },
    { w := 1, h := 1, orient := .HH, mb := 5, vals := #[3] },
    { w := 1, h := 4, orient := .LL, mb := 2, vals := #[2, 1, 0, 0] },
    { w := 1, h := 4, orient := .LL, mb := 1, vals := #[0, 0, -1, 0] },
    { w := 3, h := 5, orient := .HL, mb := 0, vals := Array.replicate 15 0 },
    { w := 2, h := 2, orient := .LH, mb := 16, vals := #[32767, -32768, 0, 1] },
    { w := 0, h := 3, orient := .LL, mb := 2, vals := #[] } ]
  for c in fixed do
    f := f + (← expect s!"fixed block {c.vals}: {checkCase c}" (checkCase c).isNone)
  -- the all-zero block: no passes, no bytes
  f := f + (← expect "all-zero block: 0 passes, no bytes"
    ((ok? (encodeCodeBlock 3 5 .HL 2 (Array.replicate 15 0))).map
      (fun o => (o.numPasses, o.bytes, o.zeroBitPlanes)) == some (0, [], 2)))
  -- the hand-traced trace of Tests.Tier1Spec ("1x4 K=2 [2,1,0,0]")
  f := f + (← expect "1x4 [2,1,0,0] trace equals the hand trace"
    ((ok? (encodeCodeBlock 1 4 .LL 2 #[2, 1, 0, 0])).map EncOut.trace ==
      some [(17, true), (18, false), (18, false), (9, false), (3, false), (0, false),
        (0, false), (3, true), (10, false), (3, false), (15, false), (0, false)]))
  f := f + (← expect "K > Mb rejected"
    ((err? (encodeCodeBlock 1 1 .LL 2 #[4])).isSome))
  f := f + (← expect "K = Mb accepted"
    ((err? (encodeCodeBlock 1 1 .LL 3 #[-4])).isNone))
  f := f + (← expect "wrong coefficient count rejected"
    ((err? (encodeCodeBlock 2 2 .LL 3 #[1, 2, 3])).isSome))
  f := f + (← expect "64 x 65 rejected"
    ((err? (encodeCodeBlock 64 65 .LL 3 (Array.replicate (64 * 65) 0))).isSome))
  f := f + (← expect "2048 x 2 rejected"
    ((err? (encodeCodeBlock 2048 2 .LL 3 (Array.replicate 4096 0))).isSome))
  f := f + (← expect "numBits 0, 1, 2^15, 2^16 - 1"
    ([0, 1, 2 ^ 15, 2 ^ 16 - 1].map numBits == [0, 1, 16, 16]))
  return f

/-- Runs the suite; returns the number of failures. -/
def run : IO Nat := do
  let mut f ← runUnits
  let n ← numBlocks
  let mut s : UInt64 := 0x2026_1125
  let mut fails := 0
  let mut checks := 0
  let mut coeffs := 0
  let t0 ← IO.monoMsNow
  let shapes : List (Option (Nat × Nat)) :=
    bigShapes.map some ++ (List.replicate n none)
  for shape in shapes do
    let (c, s1) := genCase s shape
    s := s1
    checks := checks + 1
    coeffs := coeffs + c.w * c.h
    match checkCase c with
    | none => pure ()
    | some msg =>
      fails := fails + 1
      if fails ≤ 5 then IO.eprintln s!"  mismatch: {msg}"
  let t1 ← IO.monoMsNow
  IO.println s!"  tier1 encoder round trips: {checks - fails}/{checks} ok ({coeffs} coefficients, {t1 - t0} ms)"
  f := f + (← expect s!"random encode/decode round trips ({fails} failures)" (fails == 0))
  return f

end JPEG2000.Tests.Tier1Enc
