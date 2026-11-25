import JPEG2000.Tier1.Decode

/-!
# Fast Tier-1 code-block decoder, every code-block style (T.800 D.4–D.7, Table A.19)

Plan.md §4 (C3), §5.2 "Tier-1 / EBCOT" (staged modes), §6 item 4. Task 3.4b.

The production decoder for code-blocks in any of the 64 code-block styles of Table A.19,
computing the same coefficients as the reference `Spec.Tier1.decodeCodeBlock` (task 3.3).
It is built *next to* the plain-mode decoder of `JPEG2000.Tier1.Decode` (task 3.4a), whose
definitions are untouched (they are the target of the C3 proof, task 3.6): the passes that
can make a coefficient significant get mode-aware copies (`…M`, `raw…`), the scan, the
look-up tables, the magnitude refinement pass, `clearVis`, `fillRows` and `CodeBlockOut` are
reused as they are. The entry point `decodeCodeBlockSegs` sends a block whose style decodes
as plain (every flag clear except predictable termination, which has no decoder effect) to
the plain `decodeCodeBlockExact`, so C3 for plain mode carries over to it unchanged. Passes
signalled beyond the `3K − 2`-th (below bit-plane 0) are dropped before decoding (`clampSegs`,
= `Spec.Tier1.CodeBlock.clampPasses`, task 5.8): they code nothing, OpenJPEG ignores them,
and some encoders emit them (`kodak_2layers_lrcp.j2c`, `test_lossless.j2k`).

| T.800 | spec (`Spec.Tier1`) | here |
|---|---|---|
| Table A.19 | `Mode`, `Mode.ofStyle` | `Style`, `Style.ofByte` |
| D.6 raw passes | `isRawPass` | `isRawPass` |
| D.4 / D.6 segments (Table D.9) | `passEndsSegment`, `segmentPasses` | same names |
| D.6 raw bit reader | `RawState`, `rawBit` | `rawInit`, `rawBit` (on `MQ.Dec`) |
| D.6 raw SP / MR | `rawSigPropStep`, `rawMagRefStep` | `rawSpStep`, `rawMrStep` |
| D.5 segmentation symbol | `segSymbol` | `segSymbol` |
| D.7 reset, pass order | `runPassM` | `runPassM` |
| D.7 vertically causal | `Geom.hidden`, `Geom.nbAt` | `setSig` (`causalTop`) |
| codeword segments | `startSegment`, `decodeSegments` | `startSegment`, `runSegs` |

## Mode by mode

* **Codeword segments** (`Seg`): the block's segments are byte ranges `data[start, stop)` of
  one buffer, in order, each with its pass count; the counts must be
  `segmentPasses style numPasses 0` (as the spec's `CodeBlock.validate`). Each segment starts
  with `INITDEC` on its own range (MQ, `MQ.Dec.init`) or a fresh raw reader (`rawInit`); the
  19 context states are carried from segment to segment (`Dec.cx`).
* **Raw reader on `MQ.Dec`.** A raw segment reuses the MQ decoder record: `pos` is the byte
  pointer, `c` the current byte, `ct` its unread bits, `byteAt` the `0xFF` padding at and past
  `stop`; `cx` keeps the contexts across the raw segment. `rawBit` is `Spec.Tier1.rawBit`
  (bit-unstuffing after `0xFF`; `0xFF` followed by a byte `> 0x8F` gives ones without
  consuming). Keeping one record type means every pass runs on the same `St` and reuses the
  3.4a scan loops.
* **Bypass** (bit 0): `isRawPass` passes run `rawSigPropPass` / `rawMagRefPass`: every
  decision is a raw bit, the sign is a raw bit (`1` = negative, no `XORbit`).
* **Reset** (bit 1): the contexts return to Table D.7 (`MQ.tier1Contexts`) after every pass.
* **Termall** (bit 2): only the segment structure (one pass per segment).
* **Vertically causal** (bit 3): a neighbour in the next stripe reads as insignificant. The
  3.4a flag words carry every neighbour's significance pre-merged, so this is done where the
  bits are written (`setSig`): a coefficient in the first row of a stripe (other than the
  first stripe) does not publish its significance and sign into the three words of the row
  above (their S, SW, SE bits and `NEG_S`). Those bits are read by nothing but the context
  formation of those three coefficients (zero coding, sign coding, refinement context,
  significance-propagation and run-length conditions, zero-column skipping), which is
  exactly where `Spec.Tier1.Geom.hidden` hides them; the own bits 12–15 that
  `CodeBlockOut.sig`/`lsbPlane` read are unaffected. (OpenJPEG masks the same bits at read
  time instead, `opj_t1_dec_sigpass_step_mqc` with `vsc`.)
* **Predictable termination** (bit 4): no decoder effect.
* **Segmentation symbols** (bit 5): four UNIFORM decisions after every cleanup pass; a
  symbol other than `1010` is counted (`decodeCodeBlockSegs` tolerates it like
  `Spec.Tier1.decodeCodeBlock`; `decodeCodeBlockSegsStrict` rejects it like
  `decodeCodeBlockStrict`).
* End-of-pass order (`runPassM`): pass, then segmentation symbol, then reset.
-/

namespace JPEG2000.Tier1

open JPEG2000 JPEG2000.Bytes
open JPEG2000.Tier2.Geometry (Band)

/-! ## Code-block style (Table A.19) -/

/-- The six code-block style flags of `SPcod`/`SPcoc` (T.800 Table A.19). -/
structure Style where
  /-- Bit 0: selective arithmetic coding bypass (D.6). -/
  bypass : Bool := false
  /-- Bit 1: context reset at the end of every pass (D.7). -/
  reset : Bool := false
  /-- Bit 2: termination on each coding pass (D.4). -/
  termAll : Bool := false
  /-- Bit 3: vertically causal context formation (D.7). -/
  vertCausal : Bool := false
  /-- Bit 4: predictable termination (D.4.2); no decoder effect. -/
  predTerm : Bool := false
  /-- Bit 5: segmentation symbols (D.5). -/
  segSymbols : Bool := false
  deriving Repr, DecidableEq, Inhabited

/-- The style from the code-block style byte (bits 0–5; the higher bits are not looked at). -/
def Style.ofByte (b : UInt8) : Style where
  bypass := b &&& 0x01 != 0
  reset := b &&& 0x02 != 0
  termAll := b &&& 0x04 != 0
  vertCausal := b &&& 0x08 != 0
  predTerm := b &&& 0x10 != 0
  segSymbols := b &&& 0x20 != 0

/-- The style decodes exactly as plain mode: every flag clear except possibly predictable
termination (encoder-side only). -/
def Style.decodesAsPlain (s : Style) : Bool :=
  !(s.bypass || s.reset || s.termAll || s.vertCausal || s.segSymbols)

/-! ## Raw passes and codeword segments (D.4, D.6, Table D.9) -/

/-- D.6: pass `i` is raw — bypass, a significance propagation or magnitude refinement pass,
pass index ≥ 10 (`Spec.Tier1.isRawPass`). -/
@[inline] def isRawPass (s : Style) (i : Nat) : Bool :=
  s.bypass && 10 ≤ i && passKind i != 2

/-- A codeword segment ends after pass `i` (`Spec.Tier1.passEndsSegment`): termall, or bypass
from pass 9 on after every magnitude refinement and cleanup pass. -/
def passEndsSegment (s : Style) (i : Nat) : Bool :=
  s.termAll || (s.bypass && 9 ≤ i && passKind i != 0)

/-- Split passes `i, …, i + n − 1` into runs ending at segment ends; `cur` passes are already
in the open run (`Spec.Tier1.segmentRuns`). -/
def segmentRuns (s : Style) : (n i cur : Nat) → List Nat
  | 0, _, cur => if cur = 0 then [] else [cur]
  | n + 1, i, cur =>
    if passEndsSegment s i then (cur + 1) :: segmentRuns s n (i + 1) 0
    else segmentRuns s n (i + 1) (cur + 1)

/-- The pass counts of the codeword segments of `numPasses` passes from pass `firstPass`
(`Spec.Tier1.segmentPasses`). -/
def segmentPasses (s : Style) (numPasses firstPass : Nat) : List Nat :=
  segmentRuns s numPasses firstPass 0

/-- One codeword segment of a code-block as Tier-2 delivers it: the byte range
`data[start, stop)` of the buffer and the number of coding passes it holds. -/
structure Seg where
  /-- First byte (absolute index into the buffer). -/
  start : Nat
  /-- End of the segment (exclusive). -/
  stop : Nat
  /-- Number of coding passes in the segment. -/
  passes : Nat
  deriving Repr, DecidableEq, Inhabited

/-! ## D.6 — the raw bit reader (on the MQ decoder record) -/

/-- A fresh raw reader on `data[start, stop)` keeping the context states `cx`: byte pointer
`pos = start`, current byte `c = 0`, no unread bit (`ct = 0`), as `Spec.Tier1.RawState.init`. -/
def rawInit (data : ByteArray) (start stop : Nat) (cx : ByteArray) : MQ.Dec :=
  { data, stop := min stop data.size, stop_le := Nat.min_le_right _ _,
    pos := start, c := 0, a := 0x8000, ct := 0, cx }

/-- One raw bit (`Spec.Tier1.rawBit`): load a byte when none is left — after `0xFF` the next
byte gives 7 bits, or, if it is `> 0x8F`, the byte `0xFF` again without consuming; `0xFF`
past the end — then the most significant unread bit. -/
@[inline] def rawBit (d : MQ.Dec) : Bool × MQ.Dec :=
  let d :=
    if d.ct == 0 then
      if d.c == 0xFF then
        let b := d.byteAt d.pos
        if b > 0x8F then { d with c := 0xFF, ct := 8 }
        else { d with c := b, pos := d.pos + 1, ct := 7 }
      else { d with c := d.byteAt d.pos, pos := d.pos + 1, ct := 8 }
    else d
  let ct := d.ct - 1
  ((d.c >>> ct) &&& 1 != 0, { d with ct })

/-! ## Becoming significant, with vertically causal context formation -/

/-- Bordered index `i` lies in the first row of a stripe other than the first (row
`y = i / st − 1` with `y > 0`, `y ≡ 0 mod 4`): with vertically causal context formation its
significance is hidden from the row above. -/
@[inline] def causalTop (g : Geo) (i : Nat) : Bool :=
  let r := i / g.st
  r > 1 && (r - 1) % 4 == 0

/-- Index `i` becomes significant at the plane of bit value `one` with sign `neg`: set `SIG`,
`NEG`, `VIS := vis`, add `one` to the magnitude and publish significance (and sign) into the
neighbours' words — except, with `vsc` and `causalTop`, into the row above (D.7, vertically
causal). With `vsc = false` this is the publishing part of `becomeSig`. -/
@[inline] def setSig (g : Geo) (vsc : Bool) (one : UInt32) (vis neg : Bool)
    (mq : MQ.Dec) (fl mags : Array UInt32) (i : Nat) : St :=
  let f := fget fl i
  let st := g.st
  let own := (f &&& ~~~VIS) ||| SIG ||| (if neg then NEG else 0) ||| (if vis then VIS else 0)
  let fl := fset fl i own
  let fl :=
    if vsc && causalTop g i then fl
    else
      let fl := fadd fl (i - st - 1) SIG_SE
      let fl := fadd fl (i - st) (if neg then SIG_S ||| NEG_S else SIG_S)
      fadd fl (i - st + 1) SIG_SW
  let fl := fadd fl (i - 1) (if neg then SIG_E ||| NEG_E else SIG_E)
  let fl := fadd fl (i + 1) (if neg then SIG_W ||| NEG_W else SIG_W)
  let fl := fadd fl (i + st - 1) SIG_NE
  let fl := fadd fl (i + st) (if neg then SIG_N ||| NEG_N else SIG_N)
  let fl := fadd fl (i + st + 1) SIG_NW
  let mags := fset mags i (fget mags i + one)
  ⟨mq, fl, mags⟩

/-- `becomeSig` with vertically causal publishing: decode the sign (D.3.2), then `setSig`. -/
@[inline] def becomeSigM (g : Geo) (vsc : Bool) (one : UInt32) (vis : Bool) (s : St) (i : Nat) :
    St :=
  let ⟨mq, fl, mags⟩ := s
  let e := scEntry (fget fl i)
  let (b, mq) := mq.decode (e >>> 1).toNat
  setSig g vsc one vis (b != (e &&& 1 != 0)) mq fl mags i

/-- `zeroCode` with `becomeSigM`. -/
@[inline] def zeroCodeM (g : Geo) (vsc : Bool) (one : UInt32) (vis : Bool) (s : St) (i : Nat) :
    St :=
  let ⟨mq, fl, mags⟩ := s
  let f := fget fl i
  let (b, mq) := mq.decode (zcCtx g.zc g.hzc f)
  if b then becomeSigM g vsc one vis ⟨mq, fl, mags⟩ i
  else if vis then ⟨mq, fset fl i (f ||| VIS), mags⟩
  else ⟨mq, fl, mags⟩

/-! ## MQ passes (D.3.1, D.3.4) with vertically causal publishing -/

/-- `spStep` with `zeroCodeM`. -/
@[inline] def spStepM (g : Geo) (vsc : Bool) (one : UInt32) (s : St) (i : Nat) : St :=
  let f := fget s.flags i
  if f &&& SIG == 0 && f &&& SIG_NBRS != 0 then zeroCodeM g vsc one true s i else s

/-- `spCol` with `spStepM`. -/
@[inline] def spColM (g : Geo) (vsc : Bool) (one : UInt32) (s : St) (i rows : Nat) : St :=
  if spSkip g s i rows then s else colRows (spStepM g vsc one) g.st rows s i

/-- The significance propagation pass (D.3.1), mode-aware. -/
def sigPropPassM (g : Geo) (vsc : Bool) (one : UInt32) (s : St) : St :=
  scanBlock (spColM g vsc one) g s

/-- `cuStep` with `zeroCodeM`. -/
@[inline] def cuStepM (g : Geo) (vsc : Bool) (one : UInt32) (s : St) (i : Nat) : St :=
  let f := fget s.flags i
  if f &&& (SIG ||| VIS) == 0 then zeroCodeM g vsc one false s i else s

/-- `cuCol` with `becomeSigM` / `cuStepM`. -/
@[inline] def cuColM (g : Geo) (vsc : Bool) (one : UInt32) (s : St) (i rows : Nat) : St :=
  if rlCond g s i rows then
    let ⟨mq, fl, mags⟩ := s
    let (run, mq) := mq.decode 17
    if !run then ⟨mq, fl, mags⟩
    else
      let (b1, mq) := mq.decode 18
      let (b0, mq) := mq.decode 18
      let r := (if b1 then 2 else 0) + (if b0 then 1 else 0)
      let s := becomeSigM g vsc one false ⟨mq, fl, mags⟩ (i + r * g.st)
      colRows (cuStepM g vsc one) g.st (3 - r) s (i + (r + 1) * g.st)
  else colRows (cuStepM g vsc one) g.st rows s i

/-- The cleanup pass (D.3.4), mode-aware; the `VIS` bits are cleared afterwards. -/
def cleanupPassM (g : Geo) (vsc : Bool) (one : UInt32) (s : St) : St :=
  clearVis (scanBlock (cuColM g vsc one) g s)

/-! ## D.6 — raw significance propagation and magnitude refinement -/

/-- One raw significance propagation step (`Spec.Tier1.rawSigPropStep`): the coefficients of
`spStep`; significance is a raw bit, and on `1` the sign is the next raw bit. -/
@[inline] def rawSpStep (g : Geo) (vsc : Bool) (one : UInt32) (s : St) (i : Nat) : St :=
  let ⟨mq, fl, mags⟩ := s
  let f := fget fl i
  if f &&& SIG == 0 && f &&& SIG_NBRS != 0 then
    let (b, mq) := rawBit mq
    if b then
      let (neg, mq) := rawBit mq
      setSig g vsc one true neg mq fl mags i
    else ⟨mq, fset fl i (f ||| VIS), mags⟩
  else ⟨mq, fl, mags⟩

/-- One stripe column of a raw significance propagation pass (same skip test as `spCol`). -/
@[inline] def rawSpCol (g : Geo) (vsc : Bool) (one : UInt32) (s : St) (i rows : Nat) : St :=
  if spSkip g s i rows then s else colRows (rawSpStep g vsc one) g.st rows s i

/-- A raw significance propagation pass (D.6). -/
def rawSigPropPass (g : Geo) (vsc : Bool) (one : UInt32) (s : St) : St :=
  scanBlock (rawSpCol g vsc one) g s

/-- One raw magnitude refinement step (`Spec.Tier1.rawMagRefStep`): the coefficients of
`mrStep`; the refinement bit is a raw bit. -/
@[inline] def rawMrStep (one : UInt32) (s : St) (i : Nat) : St :=
  let f := fget s.flags i
  if f &&& SIG != 0 && f &&& VIS == 0 then
    let ⟨mq, fl, mags⟩ := s
    let (b, mq) := rawBit mq
    let mags := if b then fset mags i (fget mags i + one) else mags
    ⟨mq, fset fl i (f ||| REF), mags⟩
  else s

/-- One stripe column of a raw magnitude refinement pass (same skip test as `mrCol`). -/
@[inline] def rawMrCol (g : Geo) (one : UInt32) (s : St) (i rows : Nat) : St :=
  if mrSkip g s i rows then s else colRows (rawMrStep one) g.st rows s i

/-- A raw magnitude refinement pass (D.6). -/
def rawMagRefPass (g : Geo) (one : UInt32) (s : St) : St := scanBlock (rawMrCol g one) g s

/-! ## D.5, D.7 — end of a pass -/

/-- D.5: four UNIFORM decisions after a cleanup pass; `bad` counts symbols other than `1010`
(`Spec.Tier1.segSymbol`). -/
def segSymbol (s : St) (bad : Nat) : St × Nat :=
  let ⟨mq, fl, mags⟩ := s
  let (b3, mq) := mq.decode 18
  let (b2, mq) := mq.decode 18
  let (b1, mq) := mq.decode 18
  let (b0, mq) := mq.decode 18
  (⟨mq, fl, mags⟩, if b3 && !b2 && b1 && !b0 then bad else bad + 1)

/-- Run pass `i` in style `m` (`Spec.Tier1.runPassM`): the raw variant for a raw pass, else
the MQ pass; then the segmentation symbol after a cleanup pass; then, with reset, the
contexts back to Table D.7. `bad` counts bad segmentation symbols. -/
def runPassM (m : Style) (g : Geo) (K : Nat) (s : St) (bad i : Nat) : St × Nat :=
  let one : UInt32 := (1 : UInt32) <<< (passPlane K i).toUInt32
  let vsc := m.vertCausal
  let kind := passKind i
  let s :=
    if isRawPass m i then
      (match kind with
       | 0 => rawSigPropPass g vsc one s
       | 1 => rawMagRefPass g one s
       | _ => cleanupPassM g vsc one s)
    else
      (match kind with
       | 0 => sigPropPassM g vsc one s
       | 1 => magRefPass g one s
       | _ => cleanupPassM g vsc one s)
  let (s, bad) := if m.segSymbols && kind == 2 then segSymbol s bad else (s, bad)
  if m.reset then
    let ⟨mq, fl, mags⟩ := s
    (⟨{ mq with cx := MQ.tier1Contexts }, fl, mags⟩, bad)
  else (s, bad)

/-- Run `n` passes from pass `i`. -/
def runPassesM (m : Style) (g : Geo) (K : Nat) : Nat → St → Nat → Nat → St × Nat
  | 0, s, bad, _ => (s, bad)
  | n + 1, s, bad, i =>
    let (s, bad) := runPassM m g K s bad i
    runPassesM m g K n s bad (i + 1)

/-- Start a codeword segment whose first pass is `i` (`Spec.Tier1.startSegment`): a raw
reader for a raw pass, else `INITDEC`; the context states are kept. -/
def startSegment (m : Style) (data : ByteArray) (s : St) (i : Nat) (sg : Seg) : St :=
  let ⟨mq, fl, mags⟩ := s
  let mq :=
    if isRawPass m i then rawInit data sg.start sg.stop mq.cx
    else MQ.Dec.init data sg.start sg.stop mq.cx
  ⟨mq, fl, mags⟩

/-- Decode the segments `segs[j], segs[j+1], …` (`k` of them); `i` is the next pass
(`Spec.Tier1.decodeSegments`). -/
def runSegs (m : Style) (g : Geo) (K : Nat) (data : ByteArray) (segs : Array Seg) :
    Nat → Nat → St → Nat → Nat → St × Nat
  | 0, _, s, bad, _ => (s, bad)
  | k + 1, j, s, bad, i =>
    let sg := segs.getD j default
    let s := startSegment m data s i sg
    let (s, bad) := runPassesM m g K sg.passes s bad i
    runSegs m g K data segs k (j + 1) s bad (i + sg.passes)

/-! ## The code-block decoder -/

/-- Total number of passes of the segments. -/
def segsPasses (segs : Array Seg) : Nat := segs.foldl (fun n sg => n + sg.passes) 0

/-- Argument checks, in the order of `Spec.Tier1.CodeBlock.validate`: size (A.6.1, before any
allocation), at most `3K − 2` passes, segments structured as the style requires
(`segmentPasses`); then every segment range lies in the buffer, and `K ≤ 31` when a pass is
decoded (`Int32` output, as `validate`). -/
def validateSegs (data : ByteArray) (segs : Array Seg) (w h : Nat) (m : Style) (K : Nat) :
    Except Error Unit := do
  let numPasses := segsPasses segs
  if w > 1024 ∨ h > 1024 ∨ w * h > 4096 then
    throw (.malformed tier1Loc "code-block larger than 1024 x 1024 or 4096 coefficients")
  if numPasses > 0 ∧ numPasses > 3 * K - 2 then
    throw (.malformed tier1Loc "more coding passes than 3K - 2 for K coded bit-planes")
  if segs.toList.map (·.passes) != segmentPasses m numPasses 0 then
    throw (.malformed tier1Loc "codeword segments do not match the code-block style")
  if segs.any fun sg => sg.start > sg.stop || sg.stop > data.size then
    throw (.malformed tier1Loc "code-block data range outside the buffer")
  if numPasses > 0 ∧ K > 31 then
    throw (.unsupported tier1Loc "more than 31 coded bit-planes")

/-- The decoder behind `decodeCodeBlockSegs`: the decoded block and the number of bad
segmentation symbols (always 0 for a style that decodes as plain, which goes to the plain
`decodeCodeBlockExact`). Exactly the passes of `segs` are decoded (more than `3K − 2` is
`malformed`). -/
def decodeSegsCore (data : ByteArray) (segs : Array Seg) (w h : Nat) (band : Band)
    (style : UInt8) (numBitPlanes zeroBitPlanes : Nat) : Except Error (CodeBlockOut × Nat) := do
  let m := Style.ofByte style
  let K := numBitPlanes - zeroBitPlanes
  validateSegs data segs w h m K
  if m.decodesAsPlain then
    match segs.toList with
    | [sg] =>
      let o ← decodeCodeBlockExact data sg.start sg.stop w h band numBitPlanes zeroBitPlanes
        sg.passes
      return (o, 0)
    | _ =>
      -- no segment (no pass included): validation admits nothing else in plain mode
      let o ← decodeCodeBlockExact data 0 0 w h band numBitPlanes zeroBitPlanes 0
      return (o, 0)
  else
    let g : Geo := { w, h, st := w + 2, zc := zcFor band, hzc := zcFor_size band }
    let n := (w + 2) * (h + 2)
    let s : St := {
      mq := MQ.Dec.init data 0 0 MQ.tier1Contexts
      flags := Array.replicate n 0
      mags := Array.replicate n 0 }
    let (s, bad) := runSegs m g K data segs segs.size 0 s 0 0
    let plane := fillRows g s.flags s.mags h (Plane.zero w h) 0
    return ({ plane, flags := s.flags, codedPlanes := K, numPasses := segsPasses segs }, bad)

/-- Tier-1 decoding of one code-block in any code-block style **as signalled**: exactly the
passes of `segs` (more than `3K − 2` is `malformed`). `decodeCodeBlockSegs` is this on
`clampSegs`. -/
def decodeCodeBlockSegsExact (data : ByteArray) (segs : Array Seg) (w h : Nat) (band : Band)
    (style : UInt8) (numBitPlanes zeroBitPlanes : Nat) : Except Error CodeBlockOut :=
  (decodeSegsCore data segs w h band style numBitPlanes zeroBitPlanes).map Prod.fst

/-- As `decodeCodeBlockSegsExact`, but a segmentation symbol other than `1010` is an error
(`Spec.Tier1.decodeCodeBlockStrictExact`). -/
def decodeCodeBlockSegsStrictExact (data : ByteArray) (segs : Array Seg) (w h : Nat)
    (band : Band) (style : UInt8) (numBitPlanes zeroBitPlanes : Nat) :
    Except Error CodeBlockOut := do
  let (o, bad) ← decodeSegsCore data segs w h band style numBitPlanes zeroBitPlanes
  if bad != 0 then throw (.malformed tier1Loc "bad segmentation symbol")
  return o

/-! ## Passes below bit-plane 0 (task 5.8) -/

/-- The first `m` passes of a segment list (`Spec.Tier1.truncSegments`): whole segments while
they fit, then the first segment that reaches `m` cut to the remaining passes (its byte range
kept), nothing after it. -/
def truncSegs : List Seg → Nat → List Seg
  | [], _ => []
  | s :: ss, m =>
    if m = 0 then []
    else if m ≤ s.passes then [{ s with passes := m }]
    else s :: truncSegs ss (m - s.passes)

/-- The segments of a block of `K` coded bit-planes with the passes beyond the `3K − 2`-th
dropped (`Spec.Tier1.CodeBlock.clampPasses`); unchanged when within the bound. -/
def clampSegs (segs : Array Seg) (K : Nat) : Array Seg :=
  if segsPasses segs ≤ 3 * K - 2 then segs else (truncSegs segs.toList (3 * K - 2)).toArray

/-- Some segment range lies outside the buffer (or is reversed). -/
def badRange (data : ByteArray) (segs : Array Seg) : Bool :=
  segs.any fun sg => sg.start > sg.stop || sg.stop > data.size

/-- **Tier-1 decoding of one code-block in any code-block style** (T.800 Annex D, Table
A.19): `w × h` coefficients of a sub-band of orientation `band`, code-block style byte
`style` (`SPcod`/`SPcoc`, bits 0–5), `Mb = numBitPlanes`, `zeroBitPlanes` missing planes;
`segs` are the block's codeword segments in order, each a byte range of `data` with its pass
count (the counts must be `segmentPasses (Style.ofByte style) numPasses 0`: one segment in
plain mode, none when no pass is included). Every range must lie in `data`; passes beyond
the `3K − 2`-th (below bit-plane 0) code nothing and are dropped first (`clampSegs`, as
OpenJPEG; task 5.8). Bad segmentation symbols are tolerated (as
`Spec.Tier1.decodeCodeBlock` and OpenJPEG). A style that decodes as plain is handed to
`decodeCodeBlockExact` (task 3.4a). -/
def decodeCodeBlockSegs (data : ByteArray) (segs : Array Seg) (w h : Nat) (band : Band)
    (style : UInt8) (numBitPlanes zeroBitPlanes : Nat) : Except Error CodeBlockOut :=
  if badRange data segs then .error (.malformed tier1Loc "code-block data range outside the buffer")
  else decodeCodeBlockSegsExact data (clampSegs segs (numBitPlanes - zeroBitPlanes)) w h band
    style numBitPlanes zeroBitPlanes

/-- As `decodeCodeBlockSegs`, but a segmentation symbol other than `1010` is an error
(`Spec.Tier1.decodeCodeBlockStrict`). -/
def decodeCodeBlockSegsStrict (data : ByteArray) (segs : Array Seg) (w h : Nat) (band : Band)
    (style : UInt8) (numBitPlanes zeroBitPlanes : Nat) : Except Error CodeBlockOut :=
  if badRange data segs then .error (.malformed tier1Loc "code-block data range outside the buffer")
  else decodeCodeBlockSegsStrictExact data (clampSegs segs (numBitPlanes - zeroBitPlanes)) w h
    band style numBitPlanes zeroBitPlanes

end JPEG2000.Tier1
