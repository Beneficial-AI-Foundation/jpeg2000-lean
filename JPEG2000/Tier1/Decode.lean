import JPEG2000.Error
import JPEG2000.Bytes
import JPEG2000.MQ
import JPEG2000.Tier1.Tables

/-!
# Fast Tier-1 code-block decoder, plain mode (T.800 Annex D)

Plan.md §4 (C3), §5.2 "Tier-1 / EBCOT", §6 items 1–4. Task 3.4a.

The production decoder of one code-block in the plain code-block style (all six flags of
Table A.19 clear), on top of the fast MQ decoder `JPEG2000.MQ` (Annex C). It computes the same
coefficients as the reference decoder `Spec.Tier1.decodeValues` (task 3.2); the equivalence
theorem C3 (task 3.6) is a simulation between the state here and `Spec.Tier1.DecState`, so
the control structure deliberately follows the spec pass by pass and step by step:

| T.800 | spec (`Spec.Tier1`) | here |
|---|---|---|
| D.1 scan | `scanOrder`, `stripeColumns` | `scanBlock` → `scanCols` → `colRows` (`colRowsU`) |
| D.3.1 + D.3.2 | `sigPropStep`, `zeroCode`, `becomeSignificant`, `decodeSign` | `spStep`, `zeroCode`, `becomeSig` |
| D.3.3 | `magRefStep` | `mrStep` |
| D.3.4 | `cleanupColumn`, `cleanupStep`, `runLengthColumn`, `clearVisited` | `cuCol`, `cuStep`, `clearVis` |
| D.2 | `passKind`, `passPlane`, `runPass`, `decodePasses` | `passKind`, `passPlane`, `runPass`, `runPasses` |
| D.7, D.4 | `DecState.init` (one `INITDEC`, Table D.7 states) | `MQ.Dec.init … MQ.tier1Contexts` |

## Data layout (Plan §6 items 1–4)

* **Flag words.** One `UInt32` per coefficient (`JPEG2000.Tier1.Tables` documents the layout
  bit by bit): own significance, sign, visited, refined bits plus the significance bits of
  all eight neighbours and the sign bits of the four horizontal/vertical ones, so every
  context is one table read (`zcCtx`, `scEntry`, `mrCtxOf`). The neighbour bits are written
  into the eight neighbours whenever a coefficient becomes significant (`becomeSig`), which is
  the only event that changes them.
* **Border.** Flags and magnitudes live in `(w + 2) × (h + 2)` arrays (row stride `w + 2`)
  with a one-coefficient border, as OpenJPEG: interior `(x, y)` is index
  `(y + 1)(w + 2) + x + 1`, so the eight neighbours are always in the array and there are no
  edge branches. Border words are written (neighbour bits) but never coded: they stay
  insignificant, which is the "outside the code-block is insignificant" rule of Annex D.
* **Accesses** are `fget`/`fset`: one `i < size` comparison, then an unchecked array access
  (`Array` reads/writes with a proof). Out-of-range indices (impossible: every index is
  interior or a neighbour of an interior position) read `0` / write nothing.
* **Magnitudes** are `UInt32` at the spec's `2^p` scale (bit-plane `p` adds `2^p`; no
  reconstruction midpoint): `K ≤ 31` coded bit-planes are required (else `unsupported`, as
  OpenJPEG), so magnitudes stay below `2^31` and the output is an `Int32` `Plane`
  (sign · magnitude). No `Nat` power or shift on the hot path (`one = 1 <<< p` in `UInt32`).
* **Zero-column skipping.** In the significance propagation and magnitude refinement
  passes, a full stripe column (four rows) whose four flag words have nothing to code
  (`spSkip`, `mrSkip`) is skipped with one test; in the cleanup pass such columns take the
  run-length path of D.3.4 (one decision per column).
* **In-place updates.** The state `St` (MQ registers, flags, magnitudes) is destructured
  before each update and rebuilt after, so every array stays unique and is updated in place.

## Decoded bits per coefficient (for dequantisation, Annex E)

E.1.1.2 reconstructs a non-zero index as `(q ± r·2^(Mb − Nb(u,v)))·Δ`, so the dequantiser
needs `Nb(u, v)`, i.e. the spec's `lsbPlane`. It is not stored per coefficient: after the
last decoded pass `n − 1` (plane `p = passPlane K (n − 1)`), every significant coefficient
has `lsbPlane = p`, except when that pass is a significance propagation pass, where those not
coded in it (`VIS` clear) still have `lsbPlane = p + 1`. `CodeBlockOut` keeps the final flag
words and the pass count, and `CodeBlockOut.lsbPlane` recomputes it (this is what OpenJPEG
does implicitly with its pass count). The test suite checks it against the spec's field.
-/

namespace JPEG2000.Tier1

open JPEG2000 JPEG2000.Bytes
open JPEG2000.Tier2.Geometry (Band)

/-! ## Checked array access -/

/-- Word `i` of `a`, `0` out of range (one comparison, then an unchecked read). -/
@[inline] def fget (a : Array UInt32) (i : Nat) : UInt32 := if h : i < a.size then a[i] else 0

/-- Overwrite word `i` of `a` (no-op out of range; in place when `a` is unique). -/
@[inline] def fset (a : Array UInt32) (i : Nat) (v : UInt32) : Array UInt32 :=
  if h : i < a.size then a.set i v h else a

/-- OR the mask `m` into word `i` of `a`. -/
@[inline] def fadd (a : Array UInt32) (i : Nat) (m : UInt32) : Array UInt32 :=
  fset a i (fget a i ||| m)

/-! ## State and geometry -/

/-- Per-block constants: width, height, row stride `w + 2` of the bordered arrays, and the
zero-coding table of the block's orientation. -/
structure Geo where
  /-- Width in coefficients. -/
  w : Nat
  /-- Height in coefficients. -/
  h : Nat
  /-- Row stride of the bordered arrays, `w + 2`. -/
  st : Nat
  /-- Zero-coding table (Table D.1 column of the orientation). -/
  zc : ByteArray
  /-- It has 256 entries. -/
  hzc : zc.size = 256

/-- The decoder state: MQ decoder (with its 19 contexts), bordered flag words and bordered
magnitudes (both `(w + 2) · (h + 2)` words). -/
structure St where
  /-- MQ decoder registers and contexts. -/
  mq : MQ.Dec
  /-- Flag words (layout in `JPEG2000.Tier1.Tables`). -/
  flags : Array UInt32
  /-- Magnitudes at the `2^p` scale. -/
  mags : Array UInt32

/-! ## Coding primitives (D.3.1, D.3.2) -/

/-- A coefficient becomes significant at the plane whose bit value is `one`: decode its sign
(D.3.2: sign context and `XORbit` from `scEntry`, sign = decision XOR `XORbit`), set `SIG`,
`NEG`, `VIS := vis`, add `one` to the magnitude, and publish the new significance (and sign)
into the eight neighbours' flag words. Spec: `Spec.Tier1.becomeSignificant`. -/
@[inline] def becomeSig (g : Geo) (one : UInt32) (vis : Bool) (s : St) (i : Nat) : St :=
  let ⟨mq, fl, mags⟩ := s
  let f := fget fl i
  let e := scEntry f
  let (b, mq) := mq.decode (e >>> 1).toNat
  let neg := b != (e &&& 1 != 0)
  let st := g.st
  let own := (f &&& ~~~VIS) ||| SIG ||| (if neg then NEG else 0) ||| (if vis then VIS else 0)
  let fl := fset fl i own
  let fl := fadd fl (i - st - 1) SIG_SE
  let fl := fadd fl (i - st) (if neg then SIG_S ||| NEG_S else SIG_S)
  let fl := fadd fl (i - st + 1) SIG_SW
  let fl := fadd fl (i - 1) (if neg then SIG_E ||| NEG_E else SIG_E)
  let fl := fadd fl (i + 1) (if neg then SIG_W ||| NEG_W else SIG_W)
  let fl := fadd fl (i + st - 1) SIG_NE
  let fl := fadd fl (i + st) (if neg then SIG_N ||| NEG_N else SIG_N)
  let fl := fadd fl (i + st + 1) SIG_NW
  let mags := fset mags i (fget mags i + one)
  ⟨mq, fl, mags⟩

/-- Zero coding of index `i` (D.3.1, also used by cleanup): one decision in the Table D.1
context; on `1` the coefficient becomes significant. `visited` becomes `vis`; when `vis` is
false the `VIS` bit is already clear (both callers code only unvisited coefficients), so
nothing is written. Spec: `Spec.Tier1.zeroCode`. -/
@[inline] def zeroCode (g : Geo) (one : UInt32) (vis : Bool) (s : St) (i : Nat) : St :=
  let ⟨mq, fl, mags⟩ := s
  let f := fget fl i
  let (b, mq) := mq.decode (zcCtx g.zc g.hzc f)
  if b then becomeSig g one vis ⟨mq, fl, mags⟩ i
  else if vis then ⟨mq, fset fl i (f ||| VIS), mags⟩
  else ⟨mq, fl, mags⟩

/-! ## D.1 — scan -/

/-- The rows of one stripe column with the state passed as its three components (so that the
compiled loop carries them in registers and allocates no `St` per coefficient): `k`
coefficients from index `i` downwards (step `st`). -/
@[specialize] def colRowsU (step : St → Nat → St) (st : Nat) :
    Nat → MQ.Dec → Array UInt32 → Array UInt32 → Nat → St
  | 0, mq, fl, mags, _ => ⟨mq, fl, mags⟩
  | k + 1, mq, fl, mags, i =>
    match step ⟨mq, fl, mags⟩ i with
    | ⟨mq, fl, mags⟩ => colRowsU step st k mq fl mags (i + st)

/-- The rows of one stripe column: `step` on `k` coefficients from index `i` downwards (step
`st`), i.e. `step (… (step s i) …) (i + (k − 1)·st)`. -/
@[inline] def colRows (step : St → Nat → St) (st : Nat) (k : Nat) (s : St) (i : Nat) : St :=
  let ⟨mq, fl, mags⟩ := s
  colRowsU step st k mq fl mags i

/-- The columns of one stripe: `k` columns from index `i` rightwards, each with `rows` rows,
handled by `col s i rows`. -/
@[specialize] def scanCols (col : St → Nat → Nat → St) (rows : Nat) : Nat → St → Nat → St
  | 0, s, _ => s
  | k + 1, s, i => scanCols col rows k (col s i rows) (i + 1)

/-- `k` stripes starting at row `y0`: each has `min 4 (h − y0)` rows. -/
@[specialize] def scanStripes (col : St → Nat → Nat → St) (g : Geo) : Nat → St → Nat → St
  | 0, s, _ => s
  | k + 1, s, y0 =>
    let s := scanCols col (min 4 (g.h - y0)) g.w s ((y0 + 1) * g.st + 1)
    scanStripes col g k s (y0 + 4)

/-- D.1: run `col` on every stripe column of the block in scan order (`⌈h/4⌉` stripes from
the top, columns from the left). Spec: `Spec.Tier1.stripeColumns`. -/
@[inline] def scanBlock (col : St → Nat → Nat → St) (g : Geo) (s : St) : St :=
  scanStripes col g ((g.h + 3) / 4) s 0

/-- OR of the four flag words of a full stripe column at `i`. -/
@[inline] def colOr (g : Geo) (fl : Array UInt32) (i : Nat) : UInt32 :=
  fget fl i ||| fget fl (i + g.st) ||| fget fl (i + 2 * g.st) ||| fget fl (i + 3 * g.st)

/-! ## D.3.1 — significance propagation pass -/

/-- One step: a coefficient not significant with a significant neighbour is zero-coded and
marked visited. Spec: `Spec.Tier1.sigPropStep`. -/
@[inline] def spStep (g : Geo) (one : UInt32) (s : St) (i : Nat) : St :=
  let f := fget s.flags i
  if f &&& SIG == 0 && f &&& SIG_NBRS != 0 then zeroCode g one true s i else s

/-- A full column with no significant neighbour anywhere codes nothing in this pass (a
coefficient with no significant neighbour is skipped, and since none is coded no flag word of
the column changes). -/
@[inline] def spSkip (g : Geo) (s : St) (i rows : Nat) : Bool :=
  rows == 4 && colOr g s.flags i &&& SIG_NBRS == 0

/-- One stripe column of the significance propagation pass. -/
@[inline] def spCol (g : Geo) (one : UInt32) (s : St) (i rows : Nat) : St :=
  if spSkip g s i rows then s else colRows (spStep g one) g.st rows s i

/-- The significance propagation pass at the plane of bit value `one` (D.3.1). -/
def sigPropPass (g : Geo) (one : UInt32) (s : St) : St := scanBlock (spCol g one) g s

/-! ## D.3.3 — magnitude refinement pass -/

/-- One step: a coefficient significant and not visited decodes one magnitude bit in the
Table D.4 context and is marked refined. Spec: `Spec.Tier1.magRefStep`. -/
@[inline] def mrStep (one : UInt32) (s : St) (i : Nat) : St :=
  let f := fget s.flags i
  if f &&& SIG != 0 && f &&& VIS == 0 then
    let ⟨mq, fl, mags⟩ := s
    let (b, mq) := mq.decode (mrCtxOf f)
    let mags := if b then fset mags i (fget mags i + one) else mags
    ⟨mq, fset fl i (f ||| REF), mags⟩
  else s

/-- A full column with no significant coefficient refines nothing. -/
@[inline] def mrSkip (g : Geo) (s : St) (i rows : Nat) : Bool :=
  rows == 4 && colOr g s.flags i &&& SIG == 0

/-- One stripe column of the magnitude refinement pass. -/
@[inline] def mrCol (g : Geo) (one : UInt32) (s : St) (i rows : Nat) : St :=
  if mrSkip g s i rows then s else colRows (mrStep one) g.st rows s i

/-- The magnitude refinement pass at the plane of bit value `one` (D.3.3). -/
def magRefPass (g : Geo) (one : UInt32) (s : St) : St := scanBlock (mrCol g one) g s

/-! ## D.3.4 — cleanup pass -/

/-- One normal cleanup step: a coefficient neither significant nor visited is zero-coded.
Spec: `Spec.Tier1.cleanupStep`. -/
@[inline] def cuStep (g : Geo) (one : UInt32) (s : St) (i : Nat) : St :=
  let f := fget s.flags i
  if f &&& (SIG ||| VIS) == 0 then zeroCode g one false s i else s

/-- The run-length condition (`Spec.Tier1.runLengthColumn`): a full column whose four
coefficients are insignificant, unvisited and without significant neighbours. -/
@[inline] def rlCond (g : Geo) (s : St) (i rows : Nat) : Bool :=
  rows == 4 && colOr g s.flags i &&& (SIG ||| VIS ||| SIG_NBRS) == 0

/-- One stripe column of the cleanup pass (D.3.4): run-length mode — one decision in context
17; on `1`, two UNIFORM (18) decisions give the row `r` of the first significant coefficient,
which becomes significant, and normal coding resumes at row `r + 1` — or coefficient by
coefficient. Spec: `Spec.Tier1.cleanupColumn`. -/
@[inline] def cuCol (g : Geo) (one : UInt32) (s : St) (i rows : Nat) : St :=
  if rlCond g s i rows then
    let ⟨mq, fl, mags⟩ := s
    let (run, mq) := mq.decode 17
    if !run then ⟨mq, fl, mags⟩
    else
      let (b1, mq) := mq.decode 18
      let (b0, mq) := mq.decode 18
      let r := (if b1 then 2 else 0) + (if b0 then 1 else 0)
      let s := becomeSig g one false ⟨mq, fl, mags⟩ (i + r * g.st)
      colRows (cuStep g one) g.st (3 - r) s (i + (r + 1) * g.st)
  else colRows (cuStep g one) g.st rows s i

/-- Clear the `VIS` bit of words `i, i + 1, …` (`k` of them). -/
def clearVisFrom (fl : Array UInt32) : Nat → Nat → Array UInt32
  | 0, _ => fl
  | k + 1, i => clearVisFrom (fset fl i (fget fl i &&& ~~~VIS)) k (i + 1)

/-- Clear every `VIS` bit (end of a bit-plane; `Spec.Tier1.clearVisited`). -/
@[inline] def clearVis (s : St) : St :=
  let ⟨mq, fl, mags⟩ := s
  ⟨mq, clearVisFrom fl fl.size 0, mags⟩

/-- The cleanup pass at the plane of bit value `one` (D.3.4), then the `VIS` bits are
cleared. -/
def cleanupPass (g : Geo) (one : UInt32) (s : St) : St := clearVis (scanBlock (cuCol g one) g s)

/-! ## D.2 — the sequence of coding passes -/

/-- Pass type of pass number `i`: `0` significance propagation, `1` magnitude refinement,
`2` cleanup. Pass 0 is a cleanup pass, then the cycle SP, MR, CU (`Spec.Tier1.passKind`). -/
def passKind (i : Nat) : Nat := if i = 0 then 2 else (i - 1) % 3

/-- Bit-plane of pass number `i` with `K` coded planes (`Spec.Tier1.passPlane`). -/
def passPlane (K i : Nat) : Nat := K - 1 - (i + 2) / 3

/-- Run pass number `i`. -/
def runPass (g : Geo) (K : Nat) (s : St) (i : Nat) : St :=
  let one : UInt32 := (1 : UInt32) <<< (passPlane K i).toUInt32
  match passKind i with
  | 0 => sigPropPass g one s
  | 1 => magRefPass g one s
  | _ => cleanupPass g one s

/-- Run `n` passes starting with pass number `i`. -/
def runPasses (g : Geo) (K : Nat) : Nat → St → Nat → St
  | 0, s, _ => s
  | n + 1, s, i => runPasses g K n (runPass g K s i) (i + 1)

/-! ## The code-block decoder -/

/-- The decoded code-block: the signed coefficients as a `w × h` `Int32` plane (raster order,
bit-plane `p` weighing `2^p`, no reconstruction offset), plus what dequantisation needs to
recover `Nb(u, v)` (`lsbPlane`): the final bordered flag words, `K` and the pass count. -/
structure CodeBlockOut where
  /-- Signed coefficients `±mag`, `w × h`. -/
  plane : Plane
  /-- Final flag words, bordered (`(w + 2) · (h + 2)`). -/
  flags : Array UInt32
  /-- Coded bit-planes `K`. -/
  codedPlanes : Nat
  /-- Number of passes decoded. -/
  numPasses : Nat

/-- Is the coefficient at `(x, y)` significant? -/
def CodeBlockOut.sig (o : CodeBlockOut) (x y : Nat) : Bool :=
  fget o.flags ((y + 1) * (o.plane.width + 2) + x + 1) &&& SIG != 0

/-- The bit-plane of the last magnitude bit decoded at `(x, y)` (`Spec.Tier1.Coeff.lsbPlane`;
`0` for an insignificant coefficient), so `Nb(u, v) = Mb − lsbPlane`. See the module doc. -/
def CodeBlockOut.lsbPlane (o : CodeBlockOut) (x y : Nat) : Nat :=
  let f := fget o.flags ((y + 1) * (o.plane.width + 2) + x + 1)
  if f &&& SIG == 0 || o.numPasses == 0 then 0
  else
    let last := o.numPasses - 1
    let p := passPlane o.codedPlanes last
    if passKind last == 0 && f &&& VIS == 0 then p + 1 else p

/-- The location reported by Tier-1 errors. -/
def tier1Loc : Location := Location.at .tier1

/-- Argument checks, in the order of `Spec.Tier1.CodeBlock.validate`: width and height ≤ 1024
and area ≤ 4096 (A.6.1; before any allocation), at most `3K − 2` passes (D.2); then the byte
range lies in the buffer, and `K ≤ 31` when any pass is decoded (magnitudes must fit `Int32`;
OpenJPEG refuses such blocks too). -/
def validate (data : ByteArray) (start stop w h K numPasses : Nat) : Except Error Unit := do
  if w > 1024 ∨ h > 1024 ∨ w * h > 4096 then
    throw (.malformed tier1Loc "code-block larger than 1024 x 1024 or 4096 coefficients")
  if numPasses > 0 ∧ numPasses > 3 * K - 2 then
    throw (.malformed tier1Loc "more coding passes than 3K - 2 for K coded bit-planes")
  if start > stop ∨ stop > data.size then
    throw (.malformed tier1Loc "code-block data range outside the buffer")
  if numPasses > 0 ∧ K > 31 then
    throw (.unsupported tier1Loc "more than 31 coded bit-planes")

/-- Copy the interior of the bordered arrays into the output plane: `k` cells of row `y`
starting at column `x` (raster index `j`, bordered index `i`). -/
def fillRow (fl mags : Array UInt32) : Nat → Plane → Nat → Nat → Plane
  | 0, p, _, _ => p
  | k + 1, p, j, i =>
    let m := (fget mags i).toInt32
    let v := if fget fl i &&& NEG != 0 then -m else m
    let p := if h : j < p.width * p.height then p.set j v h else p
    fillRow fl mags k p (j + 1) (i + 1)

/-- Fill all `k` rows from row `y`. -/
def fillRows (g : Geo) (fl mags : Array UInt32) : Nat → Plane → Nat → Plane
  | 0, p, _ => p
  | k + 1, p, y => fillRows g fl mags k (fillRow fl mags g.w p (y * g.w) ((y + 1) * g.st + 1)) (y + 1)

/-- Tier-1 decoding of one plain-mode code-block (T.800 Annex D) whose single codeword
segment is `data[start, stop)`: `w × h` coefficients of a sub-band of orientation `band`,
`Mb = numBitPlanes`, `zeroBitPlanes` missing planes (so `K = Mb − zeroBitPlanes` coded
planes), `numPasses` passes included. -/
def decodeCodeBlock (data : ByteArray) (start stop : Nat) (w h : Nat) (band : Band)
    (numBitPlanes zeroBitPlanes numPasses : Nat) : Except Error CodeBlockOut := do
  let K := numBitPlanes - zeroBitPlanes
  validate data start stop w h K numPasses
  let g : Geo := { w, h, st := w + 2, zc := zcFor band, hzc := zcFor_size band }
  let n := (w + 2) * (h + 2)
  let s : St := {
    mq := MQ.Dec.init data start stop MQ.tier1Contexts
    flags := Array.replicate n 0
    mags := Array.replicate n 0 }
  let s := runPasses g K numPasses s 0
  let plane := fillRows g s.flags s.mags h (Plane.zero w h) 0
  return { plane, flags := s.flags, codedPlanes := K, numPasses }

end JPEG2000.Tier1
