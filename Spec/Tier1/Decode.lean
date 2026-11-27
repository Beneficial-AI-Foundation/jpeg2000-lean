import JPEG2000.Error
import Spec.MQ
import Spec.Tier1.Context

/-!
# Spec: Tier-1 code-block decoder, plain mode (T.800 Annex D)

Plan.md §4 (C3), §5.1 (spec/implementation pattern), §5.2 "Tier-1 / EBCOT". Task 3.2.

The reference decoder of one code-block: a near-literal transcription of ITU-T T.800
Annex D for the *plain* code-block style (all six mode flags of `SPcod`/`SPcoc` clear), on
top of the MQ decoder spec `Spec.MQ` (Annex C) and the context tables `Spec.Tier1.Context`
(Tables D.1–D.4, D.7). It is the reference the fast flag-word decoder is proved equal to (C3,
task 3.6) and the base the mode extensions (task 3.3) slot into.

## What each part transcribes

* **D.1 — code-block scan.** `stripeColumns`, `scanOrder`: stripes of four rows from the
  top; inside a stripe, column by column from the left; inside a column, top to bottom. The
  last stripe may be shorter than four rows when the height is not a multiple of 4.
* **D.2 — bit-planes and coding passes.** The first coded bit-plane is the most significant
  one not skipped by Tier-2: with `Mb` magnitude bit-planes in the sub-band (E.1, Equation
  E-2: `Mb = G + εb − 1`) and `zeroBitPlanes` missing most significant bit-planes (B.10.5),
  the block has `K = Mb − zeroBitPlanes` coded bit-planes `K−1, …, 0`. Pass 0 is the cleanup
  pass of bit-plane `K−1`; then each lower bit-plane has a significance propagation, a
  magnitude refinement and a cleanup pass (`passKind`, `passPlane`): `3K − 2` passes in all.
  Tier-2 says how many passes are included; exactly that many are decoded (`decodePasses`),
  possibly stopping in the middle of a bit-plane.
* **D.3.1 — significance propagation** (`sigPropStep`, `sigPropPass`): a coefficient that is
  not yet significant and has at least one significant neighbour among its eight (current
  state, so including coefficients that became significant earlier in this very pass) is
  coded with the zero-coding context of Table D.1; if the decision is 1 it becomes
  significant and its sign is decoded (D.3.2). Every coefficient coded here is marked
  `visited` ("coded in this bit-plane").
* **D.3.2 — sign coding** (`signContext`, `decodeSign`): contexts and `XORbit` from Tables
  D.2/D.3 over the four horizontal and vertical neighbours; sign bit = decision XOR `XORbit`,
  `1` = negative.
* **D.3.3 — magnitude refinement** (`magRefStep`, `magRefPass`): every coefficient that was
  significant before this bit-plane, i.e. significant and not `visited` (a coefficient that
  became significant in this bit-plane's significance propagation pass is `visited`), gets
  one refinement bit, coded with Table D.4 (`refined = false` means first refinement).
* **D.3.4 — cleanup** (`cleanupColumn`, `cleanupPass`): every coefficient not yet
  significant and not `visited` is coded. A stripe column of four coefficients (only a full
  column of height 4) that are all insignificant, unvisited and without any significant
  neighbour is run-length coded: one decision in the run-length context; `0` → all four stay
  insignificant; `1` → two decisions in the UNIFORM context give the row `r` (most significant
  bit first) of the first significant coefficient, which becomes significant (its sign is
  decoded), and normal cleanup coding resumes at row `r + 1`. Other columns are coded
  coefficient by coefficient (zero coding, then sign). At the end of the cleanup pass the
  `visited` marks are cleared for the next bit-plane.
* **D.7 — context initialisation**: the 19 contexts start in the states of Table D.7
  (`initialStates`); plain mode never resets them.
* **D.4 — termination**: in plain mode all passes form one MQ codeword (one `INITDEC`
  on the whole segment); `Spec.MQ.byteAt` pads with `0xFF` past its end (C.3.4).

## Representation and conventions

* The state of a coefficient (`Coeff`) is the record `{sig, sign, mag, visited, refined,
  lsbPlane}`; the block is an `Array Coeff` in raster order (index `y * width + x`). All reads
  are total: a neighbour outside the code-block reads as `{}` (insignificant), as Annex D
  requires ("coefficients outside the code-block are considered insignificant").
* Coordinates are `(x, y)` = (column, row).
* **Magnitude scale.** `mag` holds the decoded magnitude bits at their place value: the bit
  of bit-plane `p` contributes `2^p` (bit-plane 0 is the least significant bit of the
  quantisation index). A fully decoded block therefore yields the quantisation indices
  `q_b(u, v)` of E.1 (without the ROI shift of Annex H). No reconstruction offset is added
  here: OpenJPEG stores `2·|q| + (midpoint)` (`oneplushalf = one | (one >> 1)` with
  `one = 1 << (p + 1)`, the extra bit being `T1_NMSEDEC_FRACBITS`-style headroom) and halves
  later; the midpoint (`r` of E.1.1.2) belongs to dequantisation (task 5.1).
* **Decoded bits per coefficient.** `lsbPlane` is the bit-plane of the last magnitude bit
  decoded for a significant coefficient (the plane at which it became significant or was last
  refined), so `Nb(u, v) = Mb − lsbPlane` in the notation of E.1.1.2 and `2^lsbPlane` is the
  weight of the reconstruction offset. It is `0` and meaningless while the coefficient is
  insignificant (its value is then `0` whatever the offset).
* **Modes.** `Mode` carries all six code-block style flags (Table A.19) so that task 3.3 can
  add their behaviour; this module implements only `Mode.plain` and `decodeCodeBlock` returns
  `Error.unsupported` for any other mode.
* Every loop is a fold over a list (the scan order, the stripe columns, `List.range` of the
  pass count): structural, total, no fuel.
-/

namespace JPEG2000.Spec.Tier1

open JPEG2000
open JPEG2000.Spec.MQ (Contexts)

/-! ## Code-block style (Table A.19) -/

/-- The code-block style flags of `SPcod`/`SPcoc` (T.800 A.6.1, Table A.19). Only the plain
mode (all flags clear) is decoded by this module; the fields exist so that the mode
extensions (task 3.3) are added as parameters, not as a new interface. -/
structure Mode where
  /-- Bit 0: selective arithmetic coding bypass (D.6). -/
  bypass : Bool := false
  /-- Bit 1: reset context probabilities on coding pass boundaries (D.7). -/
  reset : Bool := false
  /-- Bit 2: termination on each coding pass (D.4). -/
  termAll : Bool := false
  /-- Bit 3: vertically causal context formation (D.7). -/
  vertCausal : Bool := false
  /-- Bit 4: predictable termination (D.4.2). -/
  predTerm : Bool := false
  /-- Bit 5: segmentation symbols (D.5). -/
  segSymbols : Bool := false
  deriving Repr, DecidableEq, Inhabited

/-- The plain mode: every flag clear. -/
def Mode.plain : Mode := {}

/-- The mode from the code-block style byte of `SPcod`/`SPcoc` (Table A.19, bits 0–5). -/
def Mode.ofStyle (b : Nat) : Mode where
  bypass := b % 2 == 1
  reset := b / 2 % 2 == 1
  termAll := b / 4 % 2 == 1
  vertCausal := b / 8 % 2 == 1
  predTerm := b / 16 % 2 == 1
  segSymbols := b / 32 % 2 == 1

/-- Is this the plain mode (all six flags clear)? -/
def Mode.isPlain (m : Mode) : Bool := m == Mode.plain

/-! ## D.1 — scan order -/

/-- The coefficients of one stripe column: column `x` of the stripe starting at row `y0`,
rows `y0, y0+1, …` (at most four), top to bottom, stopping at the block height `h`. -/
def stripeColumn (h x y0 : Nat) : List (Nat × Nat) :=
  ((List.range 4).filter fun r => y0 + r < h).map fun r => (x, y0 + r)

/-- D.1: the stripe columns of a `w × h` code-block in scan order — stripes of four rows from
the top (`⌈h/4⌉` stripes), each scanned column by column from the left. -/
def stripeColumns (w h : Nat) : List (List (Nat × Nat)) :=
  (List.range ((h + 3) / 4)).flatMap fun s =>
    (List.range w).map fun x => stripeColumn h x (4 * s)

/-- D.1: the scan order of a `w × h` code-block, as `(x, y)` positions. -/
def scanOrder (w h : Nat) : List (Nat × Nat) := (stripeColumns w h).flatten

/-! ## Per-coefficient state -/

/-- The decoding state of one coefficient (Annex D). -/
structure Coeff where
  /-- Significance state σ: a 1 bit of the magnitude has been decoded. -/
  sig : Bool := false
  /-- Sign (`true` = negative); meaningful once `sig`. -/
  sign : Bool := false
  /-- Decoded magnitude bits, bit-plane `p` weighing `2^p`. -/
  mag : Nat := 0
  /-- Coded in the significance propagation pass of the current bit-plane. -/
  visited : Bool := false
  /-- Has had at least one magnitude refinement (D.3.3, Table D.4). -/
  refined : Bool := false
  /-- Bit-plane of the last magnitude bit decoded (meaningful once `sig`). -/
  lsbPlane : Nat := 0
  deriving Repr, DecidableEq, BEq, Inhabited

/-- The signed value `±mag` of a coefficient (at the `2^p` scale, no reconstruction
offset). -/
def Coeff.value (c : Coeff) : Int := if c.sign then -(c.mag : Int) else (c.mag : Int)

/-- The geometry of a code-block: width, height (columns, rows) and sub-band orientation. -/
structure Geom where
  /-- Width in coefficients. -/
  width : Nat
  /-- Height in coefficients. -/
  height : Nat
  /-- Orientation of the sub-band the block belongs to (selects Table D.1's column). -/
  orient : Orientation
  deriving Repr, DecidableEq, Inhabited

/-- Raster index of `(x, y)`. -/
def Geom.idx (g : Geom) (x y : Nat) : Nat := y * g.width + x

/-- The state of the coefficient at `(x, y)` (integer coordinates, so that neighbours `x − 1`,
`y − 1` can be named directly); `{}` (insignificant) outside the code-block. -/
def Geom.coeffAt (g : Geom) (cs : Array Coeff) (x y : Int) : Coeff :=
  if 0 ≤ x ∧ x < g.width ∧ 0 ≤ y ∧ y < g.height then
    cs.getD (g.idx x.toNat y.toNat) {}
  else {}

/-- Replace the state of the coefficient at `(x, y)` (a no-op outside the block). -/
def Geom.setCoeff (g : Geom) (cs : Array Coeff) (x y : Nat) (c : Coeff) : Array Coeff :=
  cs.setIfInBounds (g.idx x y) c

/-- `1` if the coefficient at `(x, y)` is significant, else `0`. -/
def Geom.sigAt (g : Geom) (cs : Array Coeff) (x y : Int) : Nat :=
  if (g.coeffAt cs x y).sig then 1 else 0

/-- The neighbour significance counts `(ΣH, ΣV, ΣD)` of `(x, y)` (D.3.1, Figure D.2):
horizontal = W + E, vertical = N + S, diagonal = NW + NE + SW + SE. -/
def Geom.sigCounts (g : Geom) (cs : Array Coeff) (x y : Nat) : Nat × Nat × Nat :=
  let x : Int := x
  let y : Int := y
  (g.sigAt cs (x - 1) y + g.sigAt cs (x + 1) y,
   g.sigAt cs x (y - 1) + g.sigAt cs x (y + 1),
   g.sigAt cs (x - 1) (y - 1) + g.sigAt cs (x + 1) (y - 1)
     + g.sigAt cs (x - 1) (y + 1) + g.sigAt cs (x + 1) (y + 1))

/-- At least one of the eight neighbours of `(x, y)` is significant. -/
def Geom.anySigNeighbour (g : Geom) (cs : Array Coeff) (x y : Nat) : Bool :=
  let (h, v, d) := g.sigCounts cs x y
  h + v + d != 0

/-- The zero-coding context of `(x, y)` (Table D.1). -/
def Geom.zcCtx (g : Geom) (cs : Array Coeff) (x y : Nat) : Nat :=
  let (h, v, d) := g.sigCounts cs x y
  zcContext g.orient h v d

/-- The neighbour state of `(x, y)` as Table D.2 reads it. -/
def Geom.nbSign (g : Geom) (cs : Array Coeff) (x y : Int) : NeighbourSign :=
  let c := g.coeffAt cs x y
  NeighbourSign.ofBits c.sig c.sign

/-- The sign-coding context and `XORbit` of `(x, y)` (Tables D.2, D.3): horizontal
contribution from W and E, vertical from N and S. -/
def Geom.signContext (g : Geom) (cs : Array Coeff) (x y : Nat) : Nat × Bool :=
  let x : Int := x
  let y : Int := y
  scContext (signContribution (g.nbSign cs (x - 1) y) (g.nbSign cs (x + 1) y))
            (signContribution (g.nbSign cs x (y - 1)) (g.nbSign cs x (y + 1)))

/-- The magnitude-refinement context of `(x, y)` (Table D.4). -/
def Geom.mrCtx (g : Geom) (cs : Array Coeff) (x y : Nat) : Nat :=
  mrContext (!(g.coeffAt cs x y).refined) (g.anySigNeighbour cs x y)

/-! ## Decoder state -/

/-- The state of the Tier-1 decoder of one code-block: MQ registers, the 19 context states and
the coefficient states. -/
structure DecState where
  /-- MQ decoder registers (Annex C). -/
  mq : Spec.MQ.State
  /-- The 19 Tier-1 contexts (numbering of `Spec.Tier1.Context`). -/
  cxs : Contexts
  /-- Coefficient states in raster order. -/
  coeffs : Array Coeff

/-- The initial state: `INITDEC` on the segment, contexts in their Table D.7 states, all
coefficients `{}` (`w · h` of them). -/
def DecState.init (g : Geom) (data : List UInt8) : DecState where
  mq := Spec.MQ.initdec data
  cxs := Spec.MQ.initContexts initialStates
  coeffs := Array.replicate (g.width * g.height) {}

/-- Decode one decision in context `cx` (`Spec.MQ.decode`). -/
def DecState.decodeBit (d : DecState) (cx : Nat) : Bool × DecState :=
  let (b, mq, cxs) := Spec.MQ.decode d.mq d.cxs cx
  (b, { d with mq, cxs })

/-- D.3.2: decode the sign of `(x, y)` (`true` = negative) — decision in the sign context,
XOR `XORbit`. -/
def decodeSign (g : Geom) (d : DecState) (x y : Nat) : Bool × DecState :=
  let (cx, xorBit) := g.signContext d.coeffs x y
  let (b, d) := d.decodeBit cx
  (b != xorBit, d)

/-- A coefficient becomes significant at bit-plane `p`: decode its sign (D.3.2), set `σ`, add
`2^p` to the magnitude. `visited` is set to `vis`. -/
def becomeSignificant (g : Geom) (p : Nat) (vis : Bool) (d : DecState) (x y : Nat) :
    DecState :=
  let (neg, d) := decodeSign g d x y
  let c := g.coeffAt d.coeffs x y
  let c' := { c with sig := true, sign := neg, mag := c.mag + 2 ^ p, visited := vis,
                     lsbPlane := p }
  { d with coeffs := g.setCoeff d.coeffs x y c' }

/-- Zero coding of `(x, y)` at bit-plane `p` (D.3.1, also used by cleanup): one decision in the
zero-coding context; on `1` the coefficient becomes significant. `visited` is set to `vis`
either way. -/
def zeroCode (g : Geom) (p : Nat) (vis : Bool) (d : DecState) (x y : Nat) : DecState :=
  let (b, d) := d.decodeBit (g.zcCtx d.coeffs x y)
  if b then becomeSignificant g p vis d x y
  else
    let c := g.coeffAt d.coeffs x y
    { d with coeffs := g.setCoeff d.coeffs x y { c with visited := vis } }

/-! ## D.3.1 — significance propagation pass -/

/-- One step of the significance propagation pass at bit-plane `p`: a coefficient that is not
significant and has a significant neighbour is zero-coded and marked `visited`. -/
def sigPropStep (g : Geom) (p : Nat) (d : DecState) (pos : Nat × Nat) : DecState :=
  let (x, y) := pos
  let c := g.coeffAt d.coeffs x y
  if !c.sig && g.anySigNeighbour d.coeffs x y then zeroCode g p true d x y
  else d

/-- The significance propagation pass at bit-plane `p` (D.3.1), in scan order. -/
def sigPropPass (g : Geom) (p : Nat) (d : DecState) : DecState :=
  (scanOrder g.width g.height).foldl (sigPropStep g p) d

/-! ## D.3.3 — magnitude refinement pass -/

/-- One step of the magnitude refinement pass at bit-plane `p`: a coefficient significant
before this bit-plane (significant and not `visited`) decodes its bit of plane `p` in the
Table D.4 context. -/
def magRefStep (g : Geom) (p : Nat) (d : DecState) (pos : Nat × Nat) : DecState :=
  let (x, y) := pos
  let c := g.coeffAt d.coeffs x y
  if c.sig && !c.visited then
    let (b, d) := d.decodeBit (g.mrCtx d.coeffs x y)
    let c := g.coeffAt d.coeffs x y
    let c' := { c with mag := c.mag + (if b then 2 ^ p else 0), refined := true,
                       lsbPlane := p }
    { d with coeffs := g.setCoeff d.coeffs x y c' }
  else d

/-- The magnitude refinement pass at bit-plane `p` (D.3.3), in scan order. -/
def magRefPass (g : Geom) (p : Nat) (d : DecState) : DecState :=
  (scanOrder g.width g.height).foldl (magRefStep g p) d

/-! ## D.3.4 — cleanup pass -/

/-- Normal (non-run-length) cleanup coding of `(x, y)` at bit-plane `p`: a coefficient neither
significant nor `visited` is zero-coded. -/
def cleanupStep (g : Geom) (p : Nat) (d : DecState) (pos : Nat × Nat) : DecState :=
  let (x, y) := pos
  let c := g.coeffAt d.coeffs x y
  if !c.sig && !c.visited then zeroCode g p false d x y
  else d

/-- The run-length condition of D.3.4 for a stripe column: it has four coefficients, and each
is insignificant, not `visited`, and has no significant neighbour. -/
def runLengthColumn (g : Geom) (cs : Array Coeff) (col : List (Nat × Nat)) : Bool :=
  col.length == 4 && col.all fun (x, y) =>
    let c := g.coeffAt cs x y
    !c.sig && !c.visited && !g.anySigNeighbour cs x y

/-- The cleanup pass on one stripe column at bit-plane `p` (D.3.4): run-length mode when
`runLengthColumn` holds, else coefficient by coefficient. -/
def cleanupColumn (g : Geom) (p : Nat) (d : DecState) (col : List (Nat × Nat)) : DecState :=
  if runLengthColumn g d.coeffs col then
    let (run, d) := d.decodeBit ctxRunLength
    if !run then d
    else
      let (b1, d) := d.decodeBit ctxUniform
      let (b0, d) := d.decodeBit ctxUniform
      let r := (if b1 then 2 else 0) + (if b0 then 1 else 0)
      match col.drop r with
      | [] => d
      | (x, y) :: rest =>
        let d := becomeSignificant g p false d x y
        rest.foldl (cleanupStep g p) d
  else col.foldl (cleanupStep g p) d

/-- Clear every `visited` mark (end of a bit-plane). -/
def clearVisited (cs : Array Coeff) : Array Coeff := cs.map fun c => { c with visited := false }

/-- The cleanup pass at bit-plane `p` (D.3.4), stripe column by stripe column; it ends the
bit-plane, so the `visited` marks are cleared afterwards. -/
def cleanupPass (g : Geom) (p : Nat) (d : DecState) : DecState :=
  let d := (stripeColumns g.width g.height).foldl (cleanupColumn g p) d
  { d with coeffs := clearVisited d.coeffs }

/-! ## D.2 — the sequence of coding passes -/

/-- The three coding pass types (D.3). -/
inductive PassKind where
  /-- Significance propagation (D.3.1). -/
  | sigProp
  /-- Magnitude refinement (D.3.3). -/
  | magRef
  /-- Cleanup (D.3.4). -/
  | cleanup
  deriving Repr, DecidableEq, Inhabited

/-- The type of pass number `i` (from 0): pass 0 is a cleanup pass, then the cycle
significance propagation, magnitude refinement, cleanup (D.2). -/
def passKind (i : Nat) : PassKind :=
  if i = 0 then .cleanup
  else match (i - 1) % 3 with
    | 0 => .sigProp
    | 1 => .magRef
    | _ => .cleanup

/-- The bit-plane of pass number `i` in a block with `K` coded bit-planes: pass 0 codes plane
`K − 1`, passes `1–3` plane `K − 2`, passes `4–6` plane `K − 3`, … -/
def passPlane (K i : Nat) : Nat := K - 1 - (i + 2) / 3

/-- Run pass number `i` of a block with `K` coded bit-planes. -/
def runPass (g : Geom) (K : Nat) (d : DecState) (i : Nat) : DecState :=
  let p := passPlane K i
  match passKind i with
  | .sigProp => sigPropPass g p d
  | .magRef => magRefPass g p d
  | .cleanup => cleanupPass g p d

/-- Run passes `0, …, n − 1`. -/
def decodePasses (g : Geom) (K n : Nat) (d : DecState) : DecState :=
  (List.range n).foldl (runPass g K) d

/-! ## The code-block decoder -/

/-- What Tier-2 and the headers tell the Tier-1 decoder about one code-block. -/
structure CodeBlock where
  /-- Width in coefficients (≤ 1024). -/
  width : Nat
  /-- Height in coefficients (≤ 1024; `width · height ≤ 4096`). -/
  height : Nat
  /-- Sub-band orientation. -/
  orient : Orientation
  /-- Code-block style (Table A.19); only `Mode.plain` is decoded here. -/
  mode : Mode := Mode.plain
  /-- `Mb`: magnitude bit-planes of the sub-band (E.1, Equation E-2). -/
  numBitPlanes : Nat
  /-- Missing most significant bit-planes, from the packet header (B.10.5). -/
  zeroBitPlanes : Nat
  /-- Number of coding passes included (B.10.6); decoded exactly. -/
  numPasses : Nat
  /-- The code-block's compressed data (all included segments; one MQ codeword in plain
  mode). -/
  data : List UInt8
  deriving Repr, Inhabited

/-- `K`: the number of coded bit-planes, `Mb − zeroBitPlanes`. -/
def CodeBlock.codedPlanes (cb : CodeBlock) : Nat := cb.numBitPlanes - cb.zeroBitPlanes

/-- The block geometry. -/
def CodeBlock.geom (cb : CodeBlock) : Geom := ⟨cb.width, cb.height, cb.orient⟩

/-- The location reported by Tier-1 errors. -/
def tier1Loc : Location := Location.at .tier1

/-- Argument checks: the code-block size bounds of A.6.1 (width and height ≤ 1024, area ≤
4096, checked before the coefficient array is allocated), at most `3K − 2` passes (D.2;
none when `K = 0`), and plain mode. -/
def CodeBlock.validate (cb : CodeBlock) : Except Error Unit := do
  if cb.width > 1024 ∨ cb.height > 1024 ∨ cb.width * cb.height > 4096 then
    throw (.malformed tier1Loc "code-block larger than 1024 x 1024 or 4096 coefficients")
  if cb.numPasses > 0 ∧ cb.numPasses > 3 * cb.codedPlanes - 2 then
    throw (.malformed tier1Loc "more coding passes than 3K - 2 for K coded bit-planes")
  if !cb.mode.isPlain then
    throw (.unsupported tier1Loc "code-block style other than plain (task 3.3)")

/-- The final decoder state of a code-block (no checks; `decodeCodeBlock` validates first). -/
def decodeState (cb : CodeBlock) : DecState :=
  decodePasses cb.geom cb.codedPlanes cb.numPasses (DecState.init cb.geom cb.data)

/-- Tier-1 decoding of one code-block (T.800 Annex D, plain mode): the coefficient states in
raster order. -/
def decodeCodeBlock (cb : CodeBlock) : Except Error (Array Coeff) := do
  cb.validate
  return (decodeState cb).coeffs

/-- The signed coefficient values `±mag` in raster order (bit-plane `p` weighing `2^p`, no
reconstruction offset). -/
def decodeValues (cb : CodeBlock) : Except Error (Array Int) :=
  (decodeCodeBlock cb).map (·.map Coeff.value)

/-! ## Sanity lemmas -/

/-- The pass sequence starts with a cleanup pass, then cycles SP, MR, CU. -/
theorem passKind_cycle (j : Nat) :
    passKind (3 * j + 1) = .sigProp ∧ passKind (3 * j + 2) = .magRef ∧
      passKind (3 * j + 3) = .cleanup := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [passKind] <;> omega

/-- The passes `3j+1, 3j+2, 3j+3` all code bit-plane `K − 2 − j`. -/
theorem passPlane_group (K j : Nat) :
    passPlane K (3 * j + 1) = K - 2 - j ∧ passPlane K (3 * j + 2) = K - 2 - j ∧
      passPlane K (3 * j + 3) = K - 2 - j := by
  simp only [passPlane]; omega

/-- A stripe column has at most four coefficients. -/
theorem stripeColumn_length_le (h x y0 : Nat) : (stripeColumn h x y0).length ≤ 4 := by
  simp only [stripeColumn, List.length_map]
  exact Nat.le_trans (List.length_filter_le _ _) (by simp)

/-- Scan-order positions lie inside the block. -/
theorem mem_scanOrder {w h x y : Nat} (hm : (x, y) ∈ scanOrder w h) : x < w ∧ y < h := by
  simp only [scanOrder, stripeColumns, List.mem_flatten, List.mem_flatMap, List.mem_map,
    List.mem_range] at hm
  obtain ⟨col, ⟨s, _, x', hx', hcol⟩, hmem⟩ := hm
  subst hcol
  simp only [stripeColumn, List.mem_map, List.mem_filter, List.mem_range,
    decide_eq_true_eq, Prod.mk.injEq] at hmem
  obtain ⟨r, ⟨_, hr⟩, rfl, rfl⟩ := hmem
  exact ⟨hx', hr⟩

end JPEG2000.Spec.Tier1
