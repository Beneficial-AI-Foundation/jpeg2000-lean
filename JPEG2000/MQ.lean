/-!
# The fast MQ arithmetic decoder (T.800 Annex C)

Plan.md §4 (C2), §5.2 "MQ decoder", §6 items 1–3.

The decoder side of T.800 Annex C written for speed, with the same control structure as the
flowchart specification `JPEG2000.Spec.MQ` (task 2.1) so that the equivalence theorem C2 is a
step-by-step simulation:

* Table C.2 (`rows`, 47 packed entries) and the derived 256-entry transition table `qeTab`
  indexed by a packed context byte;
* C.3.1 — the registers `C`, `A`, `CT` are `UInt32`, the byte pointer `BP` is `pos` (`Dec`);
* C.3.4 `BYTEIN` (Figure C.19) — `bytein`;
* C.3.5 `INITDEC` (Figure C.20) — `Dec.init`;
* C.3.3 `RENORMD` (Figure C.18) — `renormLoop`/`renormd`, a do-while loop with fuel 16
  (`Spec.MQ.renormFuel`), iteration for iteration the spec's loop;
* C.3.2 `DECODE` (Figure C.15) with `LPS_EXCHANGE` (C.16) and `MPS_EXCHANGE` (C.17) —
  `step` (+ `renormS`, `RENORMD` on unboxed registers) and `decode`.

## Correspondence with `Spec.MQ` (for C2)

* `c.toNat = C`, `a.toNat = A`, `ct.toNat = CT`, `pos - start = BP` and the spec's `data` is
  the segment `data[start, stop)` as a list.
* `UInt32` addition and left shift wrap modulo `2^32`: exactly the spec's `% 0x100000000`.
  The `A` shift is masked with `0xFFFF` (the spec's `% 0x10000`).
* `A − Qe` is computed without a mask: under the invariant `0x8000 ≤ A < 0x10000`
  (`Spec.MQ.decode_A_range`) and `Qe ≤ 0x5601` (`Spec.MQ.qe_bounds`) it neither wraps nor
  exceeds 16 bits, so it equals the spec's `(A − Qe) % 0x10000`.
* `Chigh = C >>> 16`; on the MPS path `C − (Qe <<< 16)` equals the spec's
  `(Chigh − Qe) · 2^16 + Clow` because `Chigh ≥ Qe` there.
* `byteAt` returns `0xFF` at and past `stop`, like `Spec.MQ.byteAt` past the end of the list.
* A context is one byte `index <<< 1 ||| mps` (`index < 47`). `qeTab[s]` holds
  `Qe <<< 16 ||| nmpsByte <<< 8 ||| nlpsByte` where `nmpsByte = NMPS <<< 1 ||| mps` and
  `nlpsByte = NLPS <<< 1 ||| (mps XOR SWITCH)`: the whole context update of Figures C.16/C.17
  is one table read. Bytes with `index ≥ 47` map to row 0 of Table C.2, like
  `Spec.MQ.qeAt`. The agreement with `Spec.MQ.qeTable` is `Spec.MQTable.qeTab_agree`.
* Out-of-range contexts read state `0` and are not written, like `Spec.MQ.Contexts.get/put`.

Bounded reads: every byte read is guarded by `pos < stop ≤ data.size` (the proof is carried in
`Dec`), so the compiled code has no other bounds checks. No `Nat` shift, power or product is
evaluated on the hot path.

## Allocation-free decisions (task 8.2a)

`decode` returns `Bool × Dec` (the interface the Tier-1 proofs use), but it is an `@[inline]`
wrapper around `step`, which stores the decision in the field `bit`: the pair is built and
taken apart at each call site, so the compiler removes it. `step` folds the five paths of
Figure C.15 into scalar selections and hands the registers to `renormS`, which runs
`RENORMD` on local `UInt32`/`Nat` variables (a loop, no record traffic) and ends with the one
record update of the decision; a uniquely owned `Dec` is updated in place on every path, so
a decision allocates nothing. `renormStep`/`renormLoop`/`renormd` stay as the
flowchart-shaped reference: `Spec.MQEquiv.renormS_eq` and `Spec.MQEquiv.step_eq_ref` prove
`step` equal to the path-by-path form `Spec.MQEquiv.stepRef`, on which C2 is proved.
-/

namespace JPEG2000.MQ

/-! ## Table C.2 -/

/-- T.800 Table C.2, row `i` packed as `Qe <<< 16 ||| NMPS <<< 8 ||| NLPS <<< 1 ||| SWITCH`. -/
def rows : Array UInt32 := #[
  0x56010103, 0x3401020c, 0x18010312, 0x0AC10418, 0x0521053a, 0x02212642, 0x5601070d,
  0x5401081c, 0x4801091c, 0x38010a1c, 0x30010b22, 0x24010c24, 0x1C010d28, 0x16011d2a,
  0x56010f1d, 0x5401101c, 0x5101111e, 0x48011220, 0x38011322, 0x34011424, 0x30011526,
  0x28011626, 0x24011728, 0x2201182a, 0x1C01192c, 0x18011a2e, 0x16011b30, 0x14011c32,
  0x12011d34, 0x11011e36, 0x0AC11f38, 0x09C1203a, 0x08A1213c, 0x0521223e, 0x04412340,
  0x02A12442, 0x02212544, 0x01412646, 0x01112748, 0x0085284a, 0x0049294c, 0x00252a4e,
  0x00152b50, 0x00092c52, 0x00052d54, 0x00012d56, 0x56012e5c ]

/-- Row `i` of `rows` (row 0 past the end, as `Spec.MQ.qeAt`). -/
def row (i : Nat) : UInt32 :=
  if h : i < rows.size then rows[i] else 0x56010103

/-- The transition entry for packed context byte `s = index <<< 1 ||| mps`:
`Qe <<< 16 ||| nmpsByte <<< 8 ||| nlpsByte` (see the module doc). -/
def mkEntry (s : Nat) : UInt32 :=
  let r := row (s / 2)
  let mps : UInt32 := if s % 2 = 1 then 1 else 0
  let qe := r >>> 16
  let nmps := (r >>> 8) &&& 0xFF
  let nlps := (r >>> 1) &&& 0x7F
  let sw := r &&& 1
  (qe <<< 16) ||| (((nmps <<< 1) ||| mps) <<< 8) ||| ((nlps <<< 1) ||| (mps ^^^ sw))

/-- The 256-entry transition table indexed by a packed context byte (computed once). -/
def qeTab : Array UInt32 := Array.ofFn (n := 256) fun i => mkEntry i.val

/-- `qeTab` has 256 entries, so every byte indexes it. -/
theorem qeTab_size : qeTab.size = 256 := Array.size_ofFn

/-- Table entry for context byte `s` (no bounds check: `qeTab_size`). -/
@[inline] def entry (s : UInt8) : UInt32 :=
  qeTab[s.toNat]'(by rw [qeTab_size]; exact UInt8.toNat_lt s)

/-! ## Contexts (D.7) -/

/-- Pack a context state: `index <<< 1 ||| mps` (meaningful for `index < 128`). -/
def packCx (index : Nat) (mps : Bool) : UInt8 :=
  (index * 2 + if mps then 1 else 0).toUInt8

/-- Context array with context `k` in state `inits[k]`, `MPS = 0` (as `Spec.MQ.initContexts`). -/
def initContexts (inits : List Nat) : ByteArray :=
  ⟨(inits.map fun i => packCx i false).toArray⟩

/-- The 19 Tier-1 contexts in their T.800 Table D.7 initial states: context 0 in state 4,
contexts 1–16 in state 0, context 17 (run-length) in state 3, context 18 (UNIFORM) in
state 46; all with `MPS = 0`. -/
def tier1Inits : List Nat := [4] ++ List.replicate 16 0 ++ [3, 46]

/-- `initContexts tier1Inits`. -/
def tier1Contexts : ByteArray := initContexts tier1Inits

/-- State byte of context `i` (`0` out of range, as `Spec.MQ.Contexts.get`). -/
@[inline] def ctxGet (cx : ByteArray) (i : Nat) : UInt8 :=
  if h : i < cx.size then cx.get i h else 0

/-- Write the state byte of context `i` (no-op out of range, as `Spec.MQ.Contexts.put`). -/
@[inline] def ctxSet (cx : ByteArray) (i : Nat) (v : UInt8) : ByteArray :=
  if h : i < cx.size then cx.set i v h else cx

/-! ## Decoder state (C.3.1) -/

/-- MQ decoder state: the segment `data[start, stop)` (bytes at or past `stop` read as
`0xFF`), the byte pointer `pos`, registers `C`, `A`, `CT` and the context array `cx` (one
packed byte per context). -/
structure Dec where
  /-- The buffer holding the segment. -/
  data : ByteArray
  /-- End of the segment (exclusive). -/
  stop : Nat
  /-- The segment end lies within the buffer. -/
  stop_le : stop ≤ data.size
  /-- Byte pointer `BP` (absolute index into `data`). -/
  pos : Nat
  /-- Code register `C`. -/
  c : UInt32
  /-- Interval register `A`. -/
  a : UInt32
  /-- Bit counter `CT`. -/
  ct : UInt32
  /-- Context states, `index <<< 1 ||| mps` per context. -/
  cx : ByteArray
  /-- The last decoded decision (written by `step`, so that `decode` returns its decision
  without allocating a pair; not part of the Annex C state). -/
  bit : Bool := false

namespace Dec

/-- Byte `i` of the segment; `0xFF` at or past `stop` (as `Spec.MQ.byteAt`). -/
@[inline] def byteAt (d : Dec) (i : Nat) : UInt32 :=
  if h : i < d.stop then (d.data.get i (Nat.lt_of_lt_of_le h d.stop_le)).toUInt32 else 0xFF

/-! ## BYTEIN (C.3.4, Figure C.19) -/

/-- `BYTEIN` (Figure C.19): a marker (`0xFF` followed by a byte `> 0x8F`) feeds `0xFF00`
without advancing; a `0xFF` otherwise is followed by a 7-bit (stuffed) byte; else 8 bits. -/
@[inline] def bytein (d : Dec) : Dec :=
  if d.byteAt d.pos = 0xFF then
    if d.byteAt (d.pos + 1) > 0x8F then
      { d with c := d.c + 0xFF00, ct := 8 }
    else
      let bp := d.pos + 1
      { d with pos := bp, c := d.c + (d.byteAt bp <<< 9), ct := 7 }
  else
    let bp := d.pos + 1
    { d with pos := bp, c := d.c + (d.byteAt bp <<< 8), ct := 8 }

/-! ## INITDEC (C.3.5, Figure C.20) -/

/-- `INITDEC` (Figure C.20) on the segment `data[start, stop)` (`stop` is clamped to
`data.size`) with context array `cx`. -/
def init (data : ByteArray) (start stop : Nat) (cx : ByteArray) : Dec :=
  let d : Dec := { data, stop := min stop data.size, stop_le := Nat.min_le_right _ _,
                   pos := start, c := 0, a := 0, ct := 0, cx }
  let d := { d with c := d.byteAt start <<< 16 }
  let d := d.bytein
  { d with c := d.c <<< 7, ct := d.ct - 7, a := 0x8000 }

/-! ## RENORMD (C.3.3, Figure C.18) -/

/-- One pass of the `RENORMD` body: `if CT = 0 then BYTEIN`; `A <<= 1`; `C <<= 1`; `CT −= 1`. -/
@[inline] def renormStep (d : Dec) : Dec :=
  let d := if d.ct = 0 then d.bytein else d
  { d with a := (d.a <<< 1) &&& 0xFFFF, c := d.c <<< 1, ct := d.ct - 1 }

/-- The `RENORMD` do-while loop with fuel: run the body, stop once `A AND 0x8000 ≠ 0`. -/
def renormLoop : Nat → Dec → Dec
  | 0, d => d
  | fuel + 1, d =>
    let d := renormStep d
    if d.a &&& 0x8000 != 0 then d else renormLoop fuel d

/-- `RENORMD` (Figure C.18), fuel 16 (`Spec.MQ.renormd_fuel_suffices`). -/
@[inline] def renormd (d : Dec) : Dec := renormLoop 16 d

/-! ## DECODE (C.3.2, Figures C.15–C.17) -/

/-- The end of `DECODE` on unboxed registers: `RENORMD` (`renormLoop`) run on `A = a`,
`C = c`, `CT = ct`, `BP = pos` held in local variables, followed by the one record update of
the decision: the registers, context `i` := `ns`, `bit` := the decision. With fuel `0` it is
just the update. A uniquely owned `d` is updated in place (no allocation), and the loop
never touches the record (`Spec.MQEquiv.renormS_eq` proves it equal to `renormLoop` on the
updated record). -/
def renormS (d : Dec) (i : Nat) (ns : UInt8) (bit : Bool) :
    Nat → UInt32 → UInt32 → UInt32 → Nat → Dec
  | 0, a, c, ct, pos => { d with a, c, ct, pos, cx := ctxSet d.cx i ns, bit }
  | fuel + 1, a, c, ct, pos =>
    let a := (a <<< 1) &&& 0xFFFF
    if ct == 0 then
      -- `BYTEIN` (Figure C.19) on the local registers, then `C <<= 1`, `CT −= 1`
      let b0 := d.byteAt pos
      let b1 := d.byteAt (pos + 1)
      let c := if b0 == 0xFF then (if b1 > 0x8F then c + 0xFF00 else c + (b1 <<< 9))
        else c + (b1 <<< 8)
      let ct : UInt32 := if b0 == 0xFF && !(b1 > 0x8F) then 6 else 7
      let pos := if b0 == 0xFF && b1 > 0x8F then pos else pos + 1
      if a &&& 0x8000 != 0 then { d with a, c := c <<< 1, ct, pos, cx := ctxSet d.cx i ns, bit }
      else renormS d i ns bit fuel a (c <<< 1) ct pos
    else
      -- `A <<= 1`; `C <<= 1`; `CT −= 1`; loop while `A AND 0x8000 = 0`
      if a &&& 0x8000 != 0 then
        { d with a, c := c <<< 1, ct := ct - 1, pos, cx := ctxSet d.cx i ns, bit }
      else renormS d i ns bit fuel a (c <<< 1) (ct - 1) pos

/-- `DECODE` (Figure C.15) in context `i`, the decision stored in `bit`.

`A = A − Qe`; if `Chigh < Qe`: `LPS_EXCHANGE` (C.16) then `RENORMD`; else `Chigh −= Qe` and,
if `A AND 0x8000 = 0`, `MPS_EXCHANGE` (C.17) then `RENORMD`, else `D = MPS(CX)`.

Written for the compiler: the five paths of the flowchart are folded into scalar selections
(`lps` = the `Chigh < Qe` test, `fast` = the MPS path without renormalisation, `swap` = the
conditional exchange takes the LPS transition), and `renormS` runs `RENORMD` (fuel 16, or
0 on the `fast` path) on local registers and performs the single in-place record update. On
the `fast` path the context byte is written back unchanged. `Spec.MQEquiv.step_eq_ref`
proves it equal to the flowchart shape `Spec.MQEquiv.stepRef`. -/
def step (d : Dec) (i : Nat) : Dec :=
  let s := ctxGet d.cx i
  let e := entry s
  let qe := e >>> 16
  let mps := s &&& 1 != 0
  let a := d.a - qe
  let lps := d.c >>> 16 < qe
  let fast := !lps && a &&& 0x8000 != 0
  let swap := lps != (a < qe)
  let ns : UInt8 := if fast then s else if swap then e.toUInt8 else (e >>> 8).toUInt8
  renormS d i ns (if !fast && swap then !mps else mps) (if fast then 0 else 16)
    (if lps then qe else a) (if lps then d.c else d.c - (qe <<< 16)) d.ct d.pos

/-- `DECODE` (Figure C.15): decode one decision in context `i` (`step`, then read `bit`;
inlined, so the pair is never built at run time). -/
@[inline] def decode (d : Dec) (i : Nat) : Bool × Dec :=
  let d := d.step i
  (d.bit, d)

/-- Decode one decision per context in `cxs`, in order. -/
def decodeList (d : Dec) : List Nat → List Bool × Dec
  | [] => ([], d)
  | i :: rest =>
    let (b, d) := d.decode i
    let (bs, d) := decodeList d rest
    (b :: bs, d)

end Dec

/-- Initialise on `data` and decode one decision per context in `cxList` (the analogue of
`Spec.MQ.decodeAll`, contexts initialised from `inits`). -/
def decodeAll (data : ByteArray) (inits : List Nat) (cxList : List Nat) : List Bool :=
  ((Dec.init data 0 data.size (initContexts inits)).decodeList cxList).1

end JPEG2000.MQ
