import Encode.MQ
import Spec.Tier1.Decode

/-!
# Reference Tier-1 encoder, plain mode (T.800 Annex D, encoder side)

Plan.md §5.3 (reference encoder: tests and proofs only, never in the public API), §4 (C10,
and C3's spec decoder it inverts). Task 3.5. T.800 Annex D: D.1 (scan), D.2 (bit-planes and
passes), D.3.1–D.3.4 (the three passes, sign coding, run-length coding), D.4 (one MQ
codeword per code-block in plain mode, terminated with `FLUSH`, C.2.9), D.7 (context
initialisation, Table D.7).

## Design: a mirror of the spec decoder

The encoder is written as the exact dual of `Spec.Tier1` (`Spec/Tier1/Decode.lean`), so that
the round trip `decode ∘ encode = id` can be proved as a pass-by-pass simulation:

* Its state (`EncState`) carries **the decoder's own coefficient states** (`Spec.Tier1.Coeff`,
  in raster order) — the encoder's model of what the decoder knows — and the decisions coded
  so far. Every step (`sigPropStep`, `magRefStep`, `cleanupStep`, `cleanupColumn`, …) has the
  same name, the same control flow and the same state update as the decoder step, with "decode
  a decision" replaced by "emit the decision taken from the source coefficients". The intended
  simulation invariant is therefore plain equality of the coefficient arrays.
* Contexts are computed with the decoder's own functions (`Geom.zcCtx`, `Geom.signContext`,
  `Geom.mrCtx`, `runLengthColumn`), the scan with `scanOrder`/`stripeColumns`, the pass
  schedule with `passKind`/`passPlane`.
* Tier-1 produces the **decision trace**: the list of `(context, decision)` pairs, per pass.
  The MQ coding is separate: `bytes = Encode.MQ.encodeAll initialStates trace`, exactly the
  form in which the MQ round trip C1 is stated, so C10's Tier-1 step factors as
  "Tier-1 trace correctness" + C1.

## Source values

The coefficients are signed quantisation indices at the `2^p` scale (the same scale as
`Spec.Tier1.decodeValues`, no reconstruction offset). Bit-plane `p` of `(x, y)` is bit `p` of
`|v|`; the sign is `v < 0`. A zero coefficient never becomes significant, so its sign is
irrelevant (the decoder returns `0`).

## Bit-planes and passes (D.2, B.10.5)

`K` = number of bits of the largest magnitude (`0` for an all-zero block). Given the sub-band's
`Mb` (`numBitPlanes`), the block has `zeroBitPlanes = Mb − K` missing most significant
bit-planes; `K > Mb` is an error. All `3K − 2` passes are coded (`0` passes when `K = 0`, in
which case the block is not included and `bytes = []`). Plain mode: one MQ codeword for all
passes, contexts never reset, terminated with `Encode.MQ.flush` (C.2.9).

## Per-pass information for Tier-2

`EncOut.passTraces` holds the decisions of each pass. `EncOut.passEmitted` gives, after each
pass, the number of codeword bytes the MQ encoder has already *fixed* (written before `BP`;
the byte in `B` may still receive a carry). This is a lower bound, not a verified truncation
point: a truncated plain-mode codeword needs the bytes a `FLUSH` at that point would produce
(T.800 D.4), which this reference encoder does not compute. The
reference Tier-2 encoder is meant to put all passes of a block into one layer, which needs
only `bytes` and `numPasses`.

Every loop is a fold over a list (scan order, stripe columns, `List.range` of the pass count):
structural, total, no fuel.
-/

namespace JPEG2000.Encode.Tier1

open JPEG2000
open JPEG2000.Spec.Tier1

/-! ## Source coefficients -/

/-- The coefficient to encode at `(x, y)` (raster order, `0` outside the array). -/
def srcAt (g : Geom) (src : Array Int) (x y : Nat) : Int := src.getD (g.idx x y) 0

/-- Bit `p` of the magnitude of the source coefficient at `(x, y)`. -/
def srcBit (g : Geom) (src : Array Int) (p x y : Nat) : Bool :=
  (srcAt g src x y).natAbs / 2 ^ p % 2 == 1

/-- The sign of the source coefficient at `(x, y)` (`true` = negative). -/
def srcNeg (g : Geom) (src : Array Int) (x y : Nat) : Bool := decide (srcAt g src x y < 0)

/-! ## Encoder state -/

/-- The Tier-1 encoder state: the decoder's coefficient states (the encoder's model of what
the decoder knows, raster order) and the decisions coded so far. -/
structure EncState where
  /-- The decoder-side coefficient states, raster order. -/
  coeffs : Array Coeff
  /-- `(context, decision)` pairs coded so far, in order. -/
  out : Array (Nat × Bool)

/-- The initial state: all coefficients `{}` (`w · h` of them), nothing coded (mirror of
`DecState.init`). -/
def EncState.init (g : Geom) : EncState where
  coeffs := Array.replicate (g.width * g.height) {}
  out := #[]

/-- Code the decision `b` in context `cx` (the dual of `DecState.decodeBit`). -/
def EncState.emit (e : EncState) (cx : Nat) (b : Bool) : EncState :=
  { e with out := e.out.push (cx, b) }

/-! ## D.3.2 — sign coding, zero coding -/

/-- D.3.2: code the sign of `(x, y)`: the decision is `sign XOR XORbit` in the Table D.3
context (the decoder recovers `sign = decision XOR XORbit`). Returns the sign. -/
def encodeSign (g : Geom) (src : Array Int) (e : EncState) (x y : Nat) : Bool × EncState :=
  let (cx, xorBit) := g.signContext e.coeffs x y
  let neg := srcNeg g src x y
  (neg, e.emit cx (neg != xorBit))

/-- The coefficient becomes significant at bit-plane `p`: code its sign, then the same state
update as `Spec.Tier1.becomeSignificant`. -/
def becomeSignificant (g : Geom) (src : Array Int) (p : Nat) (vis : Bool) (e : EncState)
    (x y : Nat) : EncState :=
  let (neg, e) := encodeSign g src e x y
  let c := g.coeffAt e.coeffs x y
  let c' := { c with sig := true, sign := neg, mag := c.mag + 2 ^ p, visited := vis,
                     lsbPlane := p }
  { e with coeffs := g.setCoeff e.coeffs x y c' }

/-- Zero coding of `(x, y)` at bit-plane `p`: code bit `p` in the zero-coding context; on `1`
the coefficient becomes significant. `visited` is set to `vis` either way (mirror of
`Spec.Tier1.zeroCode`). -/
def zeroCode (g : Geom) (src : Array Int) (p : Nat) (vis : Bool) (e : EncState) (x y : Nat) :
    EncState :=
  let b := srcBit g src p x y
  let e := e.emit (g.zcCtx e.coeffs x y) b
  if b then becomeSignificant g src p vis e x y
  else
    let c := g.coeffAt e.coeffs x y
    { e with coeffs := g.setCoeff e.coeffs x y { c with visited := vis } }

/-! ## D.3.1 — significance propagation pass -/

/-- One step of the significance propagation pass at bit-plane `p` (mirror of
`Spec.Tier1.sigPropStep`). -/
def sigPropStep (g : Geom) (src : Array Int) (p : Nat) (e : EncState) (pos : Nat × Nat) :
    EncState :=
  let (x, y) := pos
  let c := g.coeffAt e.coeffs x y
  if !c.sig && g.anySigNeighbour e.coeffs x y then zeroCode g src p true e x y
  else e

/-- The significance propagation pass at bit-plane `p` (D.3.1), in scan order. -/
def sigPropPass (g : Geom) (src : Array Int) (p : Nat) (e : EncState) : EncState :=
  (scanOrder g.width g.height).foldl (sigPropStep g src p) e

/-! ## D.3.3 — magnitude refinement pass -/

/-- One step of the magnitude refinement pass at bit-plane `p`: a coefficient significant
before this bit-plane codes its bit `p` in the Table D.4 context (mirror of
`Spec.Tier1.magRefStep`). -/
def magRefStep (g : Geom) (src : Array Int) (p : Nat) (e : EncState) (pos : Nat × Nat) :
    EncState :=
  let (x, y) := pos
  let c := g.coeffAt e.coeffs x y
  if c.sig && !c.visited then
    let b := srcBit g src p x y
    let e := e.emit (g.mrCtx e.coeffs x y) b
    let c := g.coeffAt e.coeffs x y
    let c' := { c with mag := c.mag + (if b then 2 ^ p else 0), refined := true,
                       lsbPlane := p }
    { e with coeffs := g.setCoeff e.coeffs x y c' }
  else e

/-- The magnitude refinement pass at bit-plane `p` (D.3.3), in scan order. -/
def magRefPass (g : Geom) (src : Array Int) (p : Nat) (e : EncState) : EncState :=
  (scanOrder g.width g.height).foldl (magRefStep g src p) e

/-! ## D.3.4 — cleanup pass -/

/-- Normal cleanup coding of `(x, y)` at bit-plane `p` (mirror of `Spec.Tier1.cleanupStep`). -/
def cleanupStep (g : Geom) (src : Array Int) (p : Nat) (e : EncState) (pos : Nat × Nat) :
    EncState :=
  let (x, y) := pos
  let c := g.coeffAt e.coeffs x y
  if !c.sig && !c.visited then zeroCode g src p false e x y
  else e

/-- The row, inside a stripe column, of the first coefficient whose bit `p` is `1`. -/
def firstOne (g : Geom) (src : Array Int) (p : Nat) (col : List (Nat × Nat)) : Option Nat :=
  col.findIdx? fun (x, y) => srcBit g src p x y

/-- The cleanup pass on one stripe column at bit-plane `p` (D.3.4, mirror of
`Spec.Tier1.cleanupColumn`): in run-length mode, `0` in the run-length context if every bit
`p` of the column is `0`; else `1`, the row `r` of the first `1` as two UNIFORM decisions (most
significant first), that coefficient becomes significant and normal coding resumes at row
`r + 1`. Otherwise coefficient by coefficient. -/
def cleanupColumn (g : Geom) (src : Array Int) (p : Nat) (e : EncState)
    (col : List (Nat × Nat)) : EncState :=
  if runLengthColumn g e.coeffs col then
    match firstOne g src p col with
    | none => e.emit ctxRunLength false
    | some r =>
      let e := e.emit ctxRunLength true
      let e := e.emit ctxUniform (r / 2 % 2 == 1)
      let e := e.emit ctxUniform (r % 2 == 1)
      match col.drop r with
      | [] => e
      | (x, y) :: rest =>
        let e := becomeSignificant g src p false e x y
        rest.foldl (cleanupStep g src p) e
  else col.foldl (cleanupStep g src p) e

/-- The cleanup pass at bit-plane `p` (D.3.4); clears the `visited` marks afterwards. -/
def cleanupPass (g : Geom) (src : Array Int) (p : Nat) (e : EncState) : EncState :=
  let e := (stripeColumns g.width g.height).foldl (cleanupColumn g src p) e
  { e with coeffs := clearVisited e.coeffs }

/-! ## D.2 — the sequence of coding passes -/

/-- Run pass number `i` of a block with `K` coded bit-planes (mirror of
`Spec.Tier1.runPass`). -/
def runPass (g : Geom) (src : Array Int) (K : Nat) (e : EncState) (i : Nat) : EncState :=
  let p := passPlane K i
  match passKind i with
  | .sigProp => sigPropPass g src p e
  | .magRef => magRefPass g src p e
  | .cleanup => cleanupPass g src p e

/-- Run passes `0, …, n − 1` (mirror of `Spec.Tier1.decodePasses`). -/
def encodePasses (g : Geom) (src : Array Int) (K n : Nat) (e : EncState) : EncState :=
  (List.range n).foldl (runPass g src K) e

/-- Run passes `0, …, n − 1`, collecting the decisions of each pass separately. The
concatenation of the per-pass lists is the `out` of `encodePasses` started from an empty
`out`. -/
def encodePassesSplit (g : Geom) (src : Array Int) (K n : Nat) (e : EncState) :
    EncState × List (List (Nat × Bool)) :=
  let (e, acc) := (List.range n).foldl
    (fun (st : EncState × Array (List (Nat × Bool))) i =>
      let e := runPass g src K { st.1 with out := #[] } i
      (e, st.2.push e.out.toList))
    (e, #[])
  (e, acc.toList)

/-! ## The code-block encoder -/

/-- The number of bits of `m` (`0` for `0`): the least `K` with `m < 2^K`. -/
def numBits (m : Nat) : Nat := if m = 0 then 0 else m.log2 + 1

/-- The largest magnitude of the coefficients. -/
def maxMag (src : Array Int) : Nat := src.foldl (fun m v => max m v.natAbs) 0

/-- The encoder's output for one code-block. -/
structure EncOut where
  /-- The MQ codeword of all passes (plain mode: one segment), `FLUSH`-terminated. -/
  bytes : List UInt8
  /-- Number of coding passes (`3K − 2`, or `0` when `K = 0`). -/
  numPasses : Nat
  /-- Missing most significant bit-planes `Mb − K` (B.10.5). -/
  zeroBitPlanes : Nat
  /-- `K`: coded bit-planes. -/
  codedPlanes : Nat
  /-- The `(context, decision)` pairs of each pass, in pass order. -/
  passTraces : List (List (Nat × Bool))
  deriving Repr, Inhabited

/-- The whole decision trace: the concatenation of the per-pass traces. -/
def EncOut.trace (o : EncOut) : List (Nat × Bool) := o.passTraces.flatten

/-- After each pass, the number of codeword bytes the MQ encoder has already written before
its byte pointer (the byte in `B` excluded, the dummy byte at `BPST − 1` excluded). A lower
bound on what a decoder of the first `i + 1` passes needs; not a verified truncation point
(see the module doc). -/
def EncOut.passEmitted (o : EncOut) : List Nat :=
  let step (st : Encode.MQ.EncState × Spec.MQ.Contexts × Array Nat) (tr : List (Nat × Bool)) :=
    let (s, cxs) := Encode.MQ.encodeMany st.1 st.2.1 tr
    (s, cxs, st.2.2.push (s.outRev.length - 1))
  (o.passTraces.foldl step
    (Encode.MQ.initenc, Spec.MQ.initContexts initialStates, #[])).2.2.toList

/-- The location reported by encoder argument errors. -/
def encLoc : Location := Location.at .tier1

/-- Tier-1 encoding of one code-block in plain mode (T.800 Annex D): `w × h` coefficients in
raster order (signed quantisation indices at the `2^p` scale), sub-band orientation `orient`,
`Mb = numBitPlanes` magnitude bit-planes. Errors: block larger than 1024 × 1024 or 4096
coefficients (A.6.1), `coeffs.size ≠ w · h`, or more than `Mb` bit-planes needed. -/
def encodeCodeBlock (w h : Nat) (orient : Orientation) (numBitPlanes : Nat)
    (coeffs : Array Int) : Except Error EncOut := do
  if w > 1024 ∨ h > 1024 ∨ w * h > 4096 then
    throw (.malformed encLoc "code-block larger than 1024 x 1024 or 4096 coefficients")
  if coeffs.size ≠ w * h then
    throw (.malformed encLoc "coefficient count differs from width * height")
  let K := numBits (maxMag coeffs)
  if K > numBitPlanes then
    throw (.malformed encLoc "coefficients need more than Mb bit-planes")
  let g : Geom := { width := w, height := h, orient := orient }
  let n := if K = 0 then 0 else 3 * K - 2
  let (_, passTraces) := encodePassesSplit g coeffs K n (EncState.init g)
  let bytes := if n = 0 then [] else Encode.MQ.encodeAll initialStates passTraces.flatten
  return { bytes, numPasses := n, zeroBitPlanes := numBitPlanes - K, codedPlanes := K,
           passTraces }

/-! ## Sanity lemmas -/

/-- `numBits m` bits suffice: `m < 2 ^ numBits m`. -/
theorem lt_two_pow_numBits (m : Nat) : m < 2 ^ numBits m := by
  unfold numBits
  split
  · subst_vars; decide
  · exact Nat.lt_log2_self

end JPEG2000.Encode.Tier1
