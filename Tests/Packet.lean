import JPEG2000.Tier2.Packet
import Spec.Tier1.Modes
import Spec.TagTree

/-!
# Tests: packet headers, bodies and per-code-block segments (task 4.4)

Plan.md §5.2 "Tier-2", §8; T.800 B.9, B.10.1–B.10.8, A.8.1–A.8.2, D.4, D.6.

1. **`segmentPasses` transcription = spec**: `Tier2.Packet.segmentPasses style n first` equals
   `Spec.Tier1.segmentPasses (Mode.ofStyle style) n first` for every style byte `0…63`, every
   `n ≤ 200` and `first` in `0…32` plus a few larger values (`JPEG2000_PACKET_SEGMENT_FULL=1`:
   every `first ≤ 200`); `passEndsSegment` agrees for passes `< 400`.
2. **Hand-built headers** (bit level): a hand-traced first inclusion (`0xCE 0x28`), zero-length
   packets (plain, with `SOP`, with `EPH`), every pass-count codeword 1–164, `Lblock`
   increments, `0xFF` stuffing inside a header and at its end, `SOP`/`EPH` errors, a body
   running past the data (`truncated`), multi-layer bypass segments split and continued
   across layers (a segment of two non-adjacent ranges); the plain-mode 109-pass segment cap
   (task 4.9: 150 passes → two length fields and segments `[109, 41]`; 100 + 20 passes over
   two layers → `[109, 11]`) and `maxPassesPerCodeBlock` on the running total (task 4.8).
3. **Random round trips**: a reference packet encoder (spec tag-tree encoder
   `Spec.TagTree.queryEnc`/`exactEnc`, pieces from `Spec.Tier1.segmentPasses`, minimal
   `Lblock` growth, B.10.1 stuffing with the trailing `0x00` after a final `0xFF`) writes
   random precincts (1–3 bands of up to 4 × 3 code-blocks, 1–5 layers, every style byte,
   random `SOP`/`EPH`, random piece lengths, empty packets) with headers in the body stream
   and in a separate stream; decoding gives each code-block's zero bit-planes, passes,
   segment pass counts (= `Spec.Tier1.segmentPasses style total 0`) and segment bytes.
   `JPEG2000_PACKET_CASES` (default 300).
4. **Corpus**: every T.803 codestream (`p0_*`, `p1_*`) and the conformance JP2 files: all
   packets of all tiles decode (`decodeAllTiles`; for `PPM`/`PPT` streams — p1_02, p1_05,
   p1_06 — the header stream is assembled here, task 4.5 wires it into the decoder) with:
   tile data exactly consumed, header + body bytes = data consumed, the separate header
   stream exactly consumed, every code-block's passes ≤ `3K − 2` (`K = Mb + roiShift − P`),
   segment pass counts = `Spec.Tier1.segmentPasses`, segment lengths summing to the
   code-block's bytes, every range inside the tile's tile-part data.
-/

namespace JPEG2000.Tests.Packet

open JPEG2000 JPEG2000.Bytes JPEG2000.Header JPEG2000.Marker JPEG2000.TilePart
open JPEG2000.Tier2.Geometry JPEG2000.Tier2.Packet

/-- Prints a failure line and returns 1 when `ok` is false. -/
def expect (name : String) (ok : Bool) : IO Nat := do
  if ok then return 0
  IO.eprintln s!"  FAIL packet: {name}"
  return 1

/-- `some e` for an error. -/
def err? {α : Type} : Except Error α → Option Error
  | .error e => some e
  | .ok _ => none

/-! ## 1. `segmentPasses` transcription -/

/-- Transcription = spec over the style bytes, pass counts and first passes. -/
def segmentCheck : IO Nat := do
  let full := (← IO.getEnv "JPEG2000_PACKET_SEGMENT_FULL") == some "1"
  let firsts := if full then List.range 201 else List.range 33 ++ [50, 99, 100, 101, 150, 199, 200]
  let mut f := 0
  let mut n := 0
  for style in [0:64] do
    let m := Spec.Tier1.Mode.ofStyle style
    for i in [0:400] do
      if passEndsSegment style i != Spec.Tier1.passEndsSegment m i then
        f := f + (← expect s!"passEndsSegment style {style} pass {i}" false)
    for np in [0:201] do
      for first in firsts do
        n := n + 1
        if segmentPasses style np first != Spec.Tier1.segmentPasses m np first then
          f := f + (← expect s!"segmentPasses style {style} n {np} first {first}" false)
  IO.println s!"  packet: segmentPasses = spec on {n} inputs"
  return f

/-! ## Bit writer (B.10.1) -/

/-- Packs header bits MSB first with B.10.1 stuffing (after `0xFF` the next byte carries 7
bits); pads the last byte with zeros and appends `0x00` when the last byte is `0xFF` (the
byte `align` consumes, as OpenJPEG's `opj_bio_flush`). -/
def packBits (bits : List Bool) : List UInt8 := Id.run do
  let mut out : Array UInt8 := #[]
  let mut cur : Nat := 0
  let mut cnt : Nat := 0
  let mut cap : Nat := 8
  for b in bits do
    cur := cur * 2 + (if b then 1 else 0)
    cnt := cnt + 1
    if cnt == cap then
      out := out.push cur.toUInt8
      cap := if cur == 0xFF then 7 else 8
      cur := 0
      cnt := 0
  if cnt > 0 then
    out := out.push (cur * 2 ^ (cap - cnt)).toUInt8
  if out.back? == some 0xFF then out := out.push 0
  return out.toList

/-- `v` in `w` bits, MSB first. -/
def natBits (v w : Nat) : List Bool := (List.range w).reverse.map fun i => v / 2 ^ i % 2 == 1

/-- The Table B.4 codeword of `n ∈ 1…164` passes. -/
def passBits (n : Nat) : List Bool :=
  if n = 1 then [false]
  else if n = 2 then [true, false]
  else if n ≤ 5 then [true, true] ++ natBits (n - 3) 2
  else if n ≤ 36 then [true, true, true, true] ++ natBits (n - 6) 5
  else [true, true, true, true] ++ natBits 31 5 ++ natBits (n - 37) 7

/-- Number of bits of `v` (0 for 0). -/
def bitLen (v : Nat) : Nat := if v = 0 then 0 else Nat.log2 v + 1

/-! ## Synthetic precincts -/

/-- Coding parameters with style `style`, guard bits 2 and every exponent `eps`
(`Mb = 1 + eps`). -/
def mkParams (style eps : Nat) : CompParams :=
  { levels := 1, cbWidthExp := 2, cbHeightExp := 2, cbStyle := style.toUInt8,
    transform := .reversible53, precinctsDefined := false, precincts := #[],
    quantStyle := 0, guardBits := 2,
    steps := (Array.replicate 4 ({ exponent := eps.toUInt8, mantissa := 0 } : StepSize)),
    roiShift := 0 }

/-- A precinct geometry with one band per `(cw, ch)` (bands LL at `r = 0`, HL/LH/HH above). -/
def mkPrecinct (r : Nat) (shapes : List (Nat × Nat)) : PrecinctGeom :=
  let bands := (bandsOf r).toList
  { index := 0, px := 0, py := 0, rect := { x0 := 0, y0 := 0, x1 := 1, y1 := 1 },
    refX := 0, refY := 0,
    bands := (shapes.zip bands).toArray.map fun ((cw, ch), b) =>
      { band := b, rect := { x0 := 0, y0 := 0, x1 := 4 * cw, y1 := 4 * ch }, cw, ch,
        codeBlocks := codeBlocksOf { x0 := 0, y0 := 0, x1 := 4 * cw, y1 := 4 * ch } 2 2 cw ch } }

/-- A fresh precinct state (fails the test run if creation fails). -/
def mkState (style eps r : Nat) (shapes : List (Nat × Nat)) : Except Error PrecState :=
  PrecState.init Limits.default (mkParams style eps) r (mkPrecinct r shapes)

/-- A reader over a byte list. -/
def rd (bs : List UInt8) : Reader := Reader.ofByteArray (ByteArray.mk bs.toArray) .tier2

/-- Decodes packets of layers `0, 1, …` from one stream (headers in the body stream). -/
def decodeSeq (sop eph : Bool) (layers : Nat) (st : PrecState) (r : Reader) :
    Except Error (PrecState × Array PacketInfo × Reader) := do
  let mut st := st
  let mut r := r
  let mut infos := #[]
  for l in [0:layers] do
    let (st', info, _, r') ← decodePacket Limits.default sop eph l l st true r r
    st := st'
    r := r'
    infos := infos.push info
  return (st, infos, r)

/-- The code-block `k` of band `b`. -/
def blockOf (st : PrecState) (b k : Nat) : CodeBlock :=
  match st.bands[b]? with
  | some bs => bs.blocks.getD k default
  | none => default

/-! ## 2. Hand-built headers -/

/-- Hand-traced: one LL code-block, layer 0: non-empty 1, inclusion 1, zero bit-planes 2
(`0 0 1`), 3 passes (`1100`), `Lblock` + 0 (`0`), length 5 in 4 bits (`0101`):
`1100 1110 0001 01(00)` = `0xCE 0x14`, then 5 body bytes. -/
def handFirst : IO Nat := do
  let bytes : List UInt8 := [0xCE, 0x14, 1, 2, 3, 4, 5, 0xAA]
  let mut f := 0
  f := f + (← expect "hand: bit writer" (packBits
    [true, true, false, false, true, true, true, false, false, false, false, true, false, true] ==
    [0xCE, 0x14]))
  match mkState 0 9 0 [(1, 1)] with
  | .error e => f := f + (← expect s!"hand: state {e}" false)
  | .ok st =>
    match decodePacket Limits.default false false 0 0 st true (rd bytes) (rd bytes) with
    | .error e => f := f + (← expect s!"hand: decode {e}" false)
    | .ok (st, info, _, r) =>
      let cb := blockOf st 0 0
      f := f + (← expect "hand: included" (cb.included && cb.firstLayer == 0))
      f := f + (← expect "hand: zero bit-planes 2" (cb.zeroBitPlanes == 2))
      f := f + (← expect "hand: 3 passes" (cb.numPasses == 3))
      f := f + (← expect "hand: Lblock 3" (cb.lblock == 3))
      f := f + (← expect "hand: one segment [2, 5)"
        (cb.segments.toList.map (fun s => (s.ranges.toList, s.passes)) ==
          [([{ offset := 2, length := 5 }], 3)]))
      f := f + (← expect "hand: sizes" (info.headerBytes == 2 && info.bodyBytes == 5 &&
        !info.empty && r.pos == 7))
  return f

/-- Zero-length packets: plain, with `SOP` (and its `Nsop` check), with `EPH`. -/
def handEmpty : IO Nat := do
  let mut f := 0
  match mkState 0 9 1 [(2, 2), (2, 2), (2, 2)] with
  | .error e => f := f + (← expect s!"empty: state {e}" false)
  | .ok st =>
    let run (sop eph : Bool) (seq : Nat) (bs : List UInt8) :=
      decodePacket Limits.default sop eph seq 0 st true (rd bs) (rd bs)
    match run false false 0 [0x00, 0x77] with
    | .ok (_, i, _, r) => f := f + (← expect "empty: plain" (i.empty && i.headerBytes == 1 && r.pos == 1))
    | .error e => f := f + (← expect s!"empty: plain {e}" false)
    match run true false 7 [0xFF, 0x91, 0, 4, 0, 7, 0x00] with
    | .ok (_, i, _, r) => f := f + (← expect "empty: SOP" (i.empty && i.sop && r.pos == 7))
    | .error e => f := f + (← expect s!"empty: SOP {e}" false)
    match run true false 7 [0x00] with
    | .ok (_, i, _, r) => f := f + (← expect "empty: SOP allowed, absent" (i.empty && !i.sop && r.pos == 1))
    | .error e => f := f + (← expect s!"empty: SOP absent {e}" false)
    f := f + (← expect "empty: SOP wrong Nsop" ((err? (run true false 8 [0xFF, 0x91, 0, 4, 0, 7, 0])).isSome))
    f := f + (← expect "empty: SOP wrong Lsop" ((err? (run true false 7 [0xFF, 0x91, 0, 5, 0, 7, 0])).isSome))
    f := f + (← expect "empty: Nsop mod 2^16" ((err? (run true false 65543 [0xFF, 0x91, 0, 4, 0, 7, 0])).isNone))
    match run false true 0 [0x00, 0xFF, 0x92, 0x55] with
    | .ok (_, i, _, r) => f := f + (← expect "empty: EPH" (i.empty && i.headerBytes == 3 && r.pos == 3))
    | .error e => f := f + (← expect s!"empty: EPH {e}" false)
    f := f + (← expect "empty: EPH missing" ((err? (run false true 0 [0x00, 0x55, 0x92])).isSome))
    f := f + (← expect "empty: no data" ((err? (run false false 0 [])).any Error.isTruncated))
  return f

/-- Every pass-count codeword 1–164 and `Lblock` increments 0–20, read back exactly. -/
def handCodewords : IO Nat := do
  let mut f := 0
  for n in [1:165] do
    let bytes := packBits (passBits n ++ [true, false, true])
    let br := BitReader.ofReader (rd bytes)
    match readNumPasses br with
    | .ok (m, br) =>
      let tail := br.bits 3
      f := f + (← expect s!"codeword {n}" (m == n && (match tail with
        | .ok (t, _) => t == 5 | .error _ => false)))
    | .error e => f := f + (← expect s!"codeword {n}: {e}" false)
  for k in [0:21] do
    let bytes := packBits (List.replicate k true ++ [false, true])
    match commaCode 33 0 (BitReader.ofReader (rd bytes)) with
    | .ok (m, br) => f := f + (← expect s!"comma {k}" (m == k && (match br.bits 1 with
        | .ok (t, _) => t == 1 | .error _ => false)))
    | .error e => f := f + (← expect s!"comma {k}: {e}" false)
  f := f + (← expect "comma: 40 ones rejected"
    ((err? (commaCode 33 0 (BitReader.ofReader (rd (packBits (List.replicate 40 true)))))).isSome))
  return f

/-- `0xFF` inside the header (stuffing) and as its last byte (trailing stuffed byte): one LL
code-block with zero bit-planes 0 and 40 passes: bits `1 1 1 | 1111 11111 0000011 | 0 |
length`; the first byte is `0xFF`. Then a header ending in `0xFF`. -/
def handStuffing : IO Nat := do
  let mut f := 0
  -- Lblock 3 + ⌊log₂ 40⌋ = 8 bits of length 200
  let bits := [true, true, true] ++ passBits 40 ++ [false] ++ natBits 200 8
  let hdr := packBits bits
  f := f + (← expect "stuffing: header starts with 0xFF" (hdr.head? == some 0xFF))
  let body := (List.range 200).map (·.toUInt8)
  match mkState 0 30 0 [(1, 1)] with
  | .error e => f := f + (← expect s!"stuffing: state {e}" false)
  | .ok st =>
    let bs := hdr ++ body
    match decodePacket Limits.default false false 0 0 st true (rd bs) (rd bs) with
    | .ok (st, i, _, r) =>
      let cb := blockOf st 0 0
      f := f + (← expect "stuffing: decoded" (cb.numPasses == 40 && cb.zeroBitPlanes == 0 &&
        i.headerBytes == hdr.length && r.pos == bs.length &&
        cb.segments.toList.map (·.length) == [200]))
    | .error e => f := f + (← expect s!"stuffing: {e}" false)
  -- A header whose last byte is 0xFF: non-empty, inclusion, zbp 0 (`111`), 1 pass (`0`),
  -- Lblock + 8 (`11111111 0`), length 2047 in 11 bits: `1110 1111 | 1111 0111 | 1111 1111`.
  let bits2 := [true, true, true] ++ passBits 1 ++ List.replicate 8 true ++ [false] ++
    natBits 2047 11
  let hdr2 := packBits bits2
  f := f + (← expect s!"stuffing: header ends with 0xFF 0x00 ({hdr2})"
    (hdr2 == [0xEF, 0xF7, 0xFF, 0x00]))
  match mkState 0 30 0 [(1, 1)] with
  | .error e => f := f + (← expect s!"stuffing2: state {e}" false)
  | .ok st =>
    let bs := hdr2 ++ List.replicate 2047 0x11
    match decodePacket Limits.default false false 0 0 st true (rd bs) (rd bs) with
    | .ok (st, i, _, r) =>
      let cb := blockOf st 0 0
      f := f + (← expect "stuffing2: decoded" (cb.numPasses == 1 && cb.lblock == 11 &&
        i.headerBytes == hdr2.length && r.pos == bs.length))
    | .error e => f := f + (← expect s!"stuffing2: {e}" false)
  return f

/-- Bypass (style 1), one code-block, three layers: 5 passes (piece `[5]`), 7 passes
(`[5, 2]`: the first piece continues segment 0 across layers), 3 passes (`[1, 2]`, a new
segment since pass 11 ended one). Segments `[10, 2, 1, 2]`; segment 0 has two ranges (the
second packet's header lies between). A body past the data is `truncated`. -/
def handBypass : IO Nat := do
  let mut f := 0
  -- layer 0: incl 1 (tag tree), zbp 0 (`1`), 5 passes `1110`, Lblock+0, length 4 bits (3+2)
  let h0 := packBits ([true, true, true] ++ passBits 5 ++ [false] ++ natBits 3 5)
  -- layer 1: included bit 1, 7 passes, Lblock+0, pieces 5 (3+2 bits), 2 (3+1 bits)
  let h1 := packBits ([true, true] ++ passBits 7 ++ [false] ++ natBits 4 5 ++ natBits 6 4)
  -- layer 2: 3 passes, pieces 1 (3 bits), 2 (4 bits)
  let h2 := packBits ([true, true] ++ passBits 3 ++ [false] ++ natBits 2 3 ++ natBits 1 4)
  let b0 := [0x10, 0x11, 0x12]
  let b1 := [0x20, 0x21, 0x22, 0x23, 0x30, 0x31, 0x32, 0x33, 0x34, 0x35]
  let b2 := [0x40, 0x41, 0x50]
  let bs := h0 ++ b0 ++ h1 ++ b1 ++ h2 ++ b2
  match mkState 1 30 0 [(1, 1)] with
  | .error e => f := f + (← expect s!"bypass: state {e}" false)
  | .ok st =>
    match decodeSeq false false 3 st (rd bs) with
    | .error e => f := f + (← expect s!"bypass: {e}" false)
    | .ok (st, _, r) =>
      let cb := blockOf st 0 0
      let data := ByteArray.mk bs.toArray
      f := f + (← expect "bypass: passes" (cb.numPasses == 15 && r.pos == bs.length))
      f := f + (← expect "bypass: segments [10, 2, 1, 2]"
        (cb.segments.toList.map (·.passes) == [10, 2, 1, 2]))
      f := f + (← expect "bypass: segment 0 = two ranges"
        (cb.segments[0]?.map (·.ranges.size) == some 2 &&
         (cb.segments[0]?.map (·.contiguous?.isNone)) == some true))
      f := f + (← expect "bypass: segment bytes" (cb.segments.toList.map (fun s => (s.bytes data).toList) ==
        [b0 ++ b1.take 4, b1.drop 4, b2.take 2, b2.drop 2]))
    -- truncated body
    let short := h0 ++ b0.take 2
    f := f + (← expect "bypass: body past the data is truncated"
      ((err? (decodePacket Limits.default false false 0 0 st true (rd short) (rd short))).any
        Error.isTruncated))
  -- per-code-block pass limit
  match PrecState.init { Limits.default with maxPassesPerCodeBlock := 4 } (mkParams 0 30) 0
      (mkPrecinct 0 [(1, 1)]) with
  | .error e => f := f + (← expect s!"limit: state {e}" false)
  | .ok st =>
    f := f + (← expect "limit: passes per code-block"
      ((err? (decodePacket { Limits.default with maxPassesPerCodeBlock := 4 } false false 0 0 st
        true (rd (h0 ++ b0)) (rd (h0 ++ b0)))).any Error.isLimit))
  -- zero bit-planes above Mb: Mb = 2 + 0 − 1 = 1, value 3 (`0001`)
  match mkState 0 0 0 [(1, 1)] with
  | .error e => f := f + (← expect s!"zbp: state {e}" false)
  | .ok st =>
    let hz := packBits ([true, true, false, false, false, true] ++ passBits 1 ++ [false] ++ natBits 0 3)
    f := f + (← expect "zbp above Mb rejected"
      ((err? (decodePacket Limits.default false false 0 0 st true (rd hz) (rd hz))).isSome))
  return f

/-- Plain mode (style 0), one LL code-block (`Mb = 31`): the 109-pass segment cap (task 4.9,
OpenJPEG `opj_t2_init_seg`). (a) 150 passes in one packet: two pieces `[109, 41]`, length
fields of `3 + ⌊log₂ 109⌋ = 9` and `3 + ⌊log₂ 41⌋ = 8` bits, two segments. (b) 100 passes,
then 20: the second packet's pieces are `[9, 11]`, the first continuing segment 0 → segments
`[109, 11]`. (c) task 4.8: `maxPassesPerCodeBlock` is checked on the running total (150
accepted with bound 150, `limitExceeded` with 149; in (b) the second packet with 119). -/
def handPlainCap : IO Nat := do
  let mut f := 0
  f := f + (← expect "cap: segmentPasses plain 150 = [109, 41]"
    (segmentPasses 0 150 0 == [109, 41] &&
      Spec.Tier1.segmentPasses Spec.Tier1.Mode.plain 150 0 == [109, 41]))
  f := f + (← expect "cap: segmentPasses plain 20 from 100 = [9, 11]"
    (segmentPasses 0 20 100 == [9, 11]))
  f := f + (← expect "cap: segmentPasses plain 300 = [109, 109, 82]"
    (segmentPasses 16 300 0 == [109, 109, 82]))
  f := f + (← expect "cap: plain 109 = one segment" (segmentPasses 0 109 0 == [109]))
  f := f + (← expect "cap: not with termall / bypass"
    (segmentPasses 4 3 107 == [1, 1, 1] && (segmentPasses 1 120 0).length > 2))
  -- (a) incl 1, zbp 0 (`1`), 150 passes, Lblock+0, lengths 5 (9 bits), 3 (8 bits)
  let ha := packBits ([true, true, true] ++ passBits 150 ++ [false] ++ natBits 5 9 ++ natBits 3 8)
  let ba : List UInt8 := [1, 2, 3, 4, 5, 6, 7, 8]
  let bsa := ha ++ ba
  let lim (n : Nat) : Limits := { Limits.default with maxPassesPerCodeBlock := n }
  match PrecState.init (lim 150) (mkParams 0 30) 0 (mkPrecinct 0 [(1, 1)]) with
  | .error e => f := f + (← expect s!"cap: state {e}" false)
  | .ok st =>
    match decodePacket (lim 150) false false 0 0 st true (rd bsa) (rd bsa) with
    | .error e => f := f + (← expect s!"cap (a): {e}" false)
    | .ok (st, _, _, r) =>
      let cb := blockOf st 0 0
      let data := ByteArray.mk bsa.toArray
      f := f + (← expect "cap (a): 150 passes, segments [109, 41]" (cb.numPasses == 150 &&
        cb.segments.toList.map (·.passes) == [109, 41] && r.pos == bsa.length))
      f := f + (← expect "cap (a): segment bytes" (cb.segments.toList.map (fun s => (s.bytes data).toList) ==
        [[1, 2, 3, 4, 5], [6, 7, 8]]))
    f := f + (← expect "cap (a): 150 passes > maxPassesPerCodeBlock 149 is limitExceeded"
      ((err? (decodePacket (lim 149) false false 0 0 st true (rd bsa) (rd bsa))).any Error.isLimit))
  -- (b) layer 0: 100 passes, length 4 (9 bits); layer 1: included bit, 20 passes, Lblock+0,
  -- pieces 9 (6 bits) and 11 (6 bits), lengths 2 and 3
  let h0 := packBits ([true, true, true] ++ passBits 100 ++ [false] ++ natBits 4 9)
  let h1 := packBits ([true, true] ++ passBits 20 ++ [false] ++ natBits 2 6 ++ natBits 3 6)
  let b0 : List UInt8 := [0x10, 0x11, 0x12, 0x13]
  let b1 : List UInt8 := [0x20, 0x21, 0x30, 0x31, 0x32]
  let bsb := h0 ++ b0 ++ h1 ++ b1
  match mkState 0 30 0 [(1, 1)] with
  | .error e => f := f + (← expect s!"cap (b): state {e}" false)
  | .ok st =>
    match decodeSeq false false 2 st (rd bsb) with
    | .error e => f := f + (← expect s!"cap (b): {e}" false)
    | .ok (st', _, r) =>
      let cb := blockOf st' 0 0
      let data := ByteArray.mk bsb.toArray
      f := f + (← expect "cap (b): segments [109, 11]" (cb.numPasses == 120 &&
        cb.segments.toList.map (·.passes) == [109, 11] && r.pos == bsb.length))
      f := f + (← expect "cap (b): segment bytes" (cb.segments.toList.map (fun s => (s.bytes data).toList) ==
        [b0 ++ [0x20, 0x21], [0x30, 0x31, 0x32]]))
    -- the second packet brings the code-block to 120 passes > 119
    let r2 : Except Error Unit := do
      let (st1, _, _, r1) ← decodePacket (lim 119) false false 0 0 st true (rd bsb) (rd bsb)
      let _ ← decodePacket (lim 119) false false 1 1 st1 true r1 r1
      return ()
    f := f + (← expect "cap (b): running total 120 > 119 is limitExceeded"
      ((err? r2).any Error.isLimit))
  return f

/-! ## 3. Random round trips -/

/-- One splitmix64 step. -/
def splitmix (s : UInt64) : UInt64 × UInt64 :=
  let s := s + 0x9E3779B97F4A7C15
  let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), s)

/-- A pseudo-random value below `m` (`m > 0`). -/
def below (s : UInt64) (m : Nat) : Nat × UInt64 :=
  let (z, s) := splitmix s
  ((z >>> 11).toNat % m, s)

/-- A random precinct plan: per band `(cw, ch)`, per code-block its first layer (`layers` =
never), zero bit-planes and per-layer pass counts and piece lengths. -/
structure Plan where
  /-- Style byte. -/
  style : Nat
  /-- Resolution (0: one band; else three). -/
  r : Nat
  /-- Layers. -/
  layers : Nat
  /-- `(cw, ch)` per band. -/
  shapes : List (Nat × Nat)
  /-- Per band, per code-block: first layer. -/
  first : Array (Array Nat)
  /-- Per band, per code-block: zero bit-planes. -/
  zbp : Array (Array Nat)
  /-- Per band, per code-block, per layer: new passes. -/
  passes : Array (Array (Array Nat))
  /-- `SOP`, `EPH`. -/
  sop : Bool
  /-- `EPH`. -/
  eph : Bool

/-- Draws a random plan (`Mb = 1 + 30 = 31`). -/
def randPlan (s : UInt64) : Plan × UInt64 := Id.run do
  let mut s := s
  let (style, s1) := below s 64; s := s1
  let (r, s1) := below s 2; s := s1
  let (layers, s1) := below s 5; s := s1
  let layers := layers + 1
  let nb := if r = 0 then 1 else 3
  let mut shapes := #[]
  let mut first := #[]
  let mut zbp := #[]
  let mut passes := #[]
  for _ in [0:nb] do
    let (cw, s1) := below s 5; s := s1
    let (ch, s1) := below s 4; s := s1
    let (cw, ch) := if cw = 0 ∨ ch = 0 then (0, 0) else (cw, ch)
    shapes := shapes.push (cw, ch)
    let mut fb := #[]
    let mut zb := #[]
    let mut pb := #[]
    for _ in [0:cw * ch] do
      let (fl, s1) := below s (layers + 1); s := s1
      let (z, s1) := below s 12; s := s1
      let mut pl := #[]
      let mut tot := 0
      for l in [0:layers] do
        let (n, s1) := below s 8; s := s1
        let (big, s1) := below s 10; s := s1
        let n := if l < fl then 0 else if l = fl then n + 1 + (if big = 0 then 30 else 0)
          else if big < 3 then 0 else n + (if big = 9 then 40 else 0)
        let n := min n (200 - tot)
        tot := tot + n
        pl := pl.push n
      fb := fb.push fl
      zb := zb.push z
      pb := pb.push pl
    first := first.push fb
    zbp := zbp.push zb
    passes := passes.push pb
  let (sop, s1) := below s 2; s := s1
  let (eph, s1) := below s 2; s := s1
  return ({ style, r, layers, shapes := shapes.toList, first, zbp, passes,
            sop := sop == 1, eph := eph == 1 }, s)

/-- The encoder state of one band: the two spec tag-tree states. -/
structure EncBand where
  /-- Inclusion tree state. -/
  incl : Spec.TagTree.St := Spec.TagTree.init
  /-- Zero bit-plane tree state. -/
  zbp : Spec.TagTree.St := Spec.TagTree.init

/-- Per code-block encoder state: `Lblock`, passes so far. -/
structure EncBlock where
  /-- `Lblock`. -/
  lblock : Nat := 3
  /-- Passes so far. -/
  passes : Nat := 0

/-- Encodes all packets of a plan. Returns (header bytes per packet, body bytes per packet,
per code-block the list of `(passes, bytes)` pieces in order). -/
def encodePlan (p : Plan) (s : UInt64) :
    Array (List UInt8) × Array (List UInt8) × Array (Array (List (Nat × List UInt8))) × UInt64 :=
  Id.run do
  let mut s := s
  let mut eb : Array EncBand := p.shapes.toArray.map fun _ => {}
  let mut blocks : Array (Array EncBlock) := p.shapes.toArray.map fun (cw, ch) =>
    Array.replicate (cw * ch) {}
  let mut pieces : Array (Array (List (Nat × List UInt8))) := p.shapes.toArray.map fun (cw, ch) =>
    Array.replicate (cw * ch) []
  let mut hdrs := #[]
  let mut bodies := #[]
  let mut ctr : Nat := 0
  for l in [0:p.layers] do
    let any := (List.range p.shapes.length).any fun b =>
      ((p.passes.getD b #[]).toList.any fun pl => pl.getD l 0 > 0)
    let (forceNE, s1) := below s 3; s := s1
    let nonEmpty := any || forceNE == 0
    let mut bits : Array Bool := #[nonEmpty]
    let mut body : Array UInt8 := #[]
    if nonEmpty then
      for b in [0:p.shapes.length] do
        let (cw, ch) := p.shapes.getD b (0, 0)
        let fv := p.first.getD b #[]
        let zv := p.zbp.getD b #[]
        let vf : Nat → Nat → Nat := fun x y => fv.getD (y * cw + x) 0
        let vz : Nat → Nat → Nat := fun x y => zv.getD (y * cw + x) 0
        for k in [0:cw * ch] do
          let x := k % cw
          let y := k / cw
          let fl := fv.getD k 0
          let n := ((p.passes.getD b #[]).getD k #[]).getD l 0
          let e := eb.getD b {}
          if fl ≥ l then
            let (qb, _, st) := Spec.TagTree.queryEnc cw ch vf e.incl x y (l + 1)
            bits := bits ++ qb.toArray
            eb := eb.set! b { e with incl := st }
          else
            bits := bits.push (n > 0)
          if n > 0 then
            if fl == l then
              let e := eb.getD b {}
              let (zb, _, st) := Spec.TagTree.exactEnc cw ch vz x y (31 + 2) 0 e.zbp
              bits := bits ++ zb.toArray
              eb := eb.set! b { e with zbp := st }
            bits := bits ++ (passBits n).toArray
            let blk := (blocks.getD b #[]).getD k {}
            let ps := Spec.Tier1.segmentPasses (Spec.Tier1.Mode.ofStyle p.style) n blk.passes
            let mut lens := #[]
            for _ in ps do
              let (len, s1) := below s 6; s := s1
              let (len2, s1) := below s 300; s := s1
              lens := lens.push (if len = 0 then 0 else if len = 1 then len2 else len)
            let need := (ps.zip lens.toList).foldl (fun a (q, len) =>
              max a (bitLen len - Nat.log2 q)) 0
            let inc := need - blk.lblock
            bits := bits ++ (List.replicate inc true ++ [false]).toArray
            let lb := blk.lblock + inc
            let mut pcs := (pieces.getD b #[]).getD k []
            for (q, len) in ps.zip lens.toList do
              bits := bits ++ (natBits len (lb + Nat.log2 q)).toArray
              let data := (List.range len).map fun i => (ctr + 7 * i).toUInt8
              ctr := ctr + 1
              body := body ++ data.toArray
              pcs := pcs ++ [(q, data)]
            pieces := pieces.set! b ((pieces.getD b #[]).set! k pcs)
            blocks := blocks.set! b ((blocks.getD b #[]).set! k { lblock := lb, passes := blk.passes + n })
    let mut hdr := packBits bits.toList
    if p.eph then hdr := hdr ++ [0xFF, 0x92]
    let sop : List UInt8 := if p.sop then [0xFF, 0x91, 0, 4, 0, l.toUInt8] else []
    hdrs := hdrs.push hdr
    bodies := bodies.push (sop ++ body.toList)
  return (hdrs, bodies, pieces, s)

/-- Groups `(passes, bytes)` pieces into segments of the given pass counts. -/
def groupPieces : List Nat → List (Nat × List UInt8) → List (List UInt8)
  | [], _ => []
  | q :: qs, ps =>
    let rec take (need : Nat) (ps : List (Nat × List UInt8)) (acc : List UInt8) :
        List UInt8 × List (Nat × List UInt8) :=
      match ps with
      | [] => (acc, [])
      | (n, d) :: rest => if need ≤ n then (acc ++ d, rest) else take (need - n) rest (acc ++ d)
    let (seg, rest) := take q ps []
    seg :: groupPieces qs rest

/-- Checks a decoded precinct state against the plan. -/
def checkState (name : String) (p : Plan) (pieces : Array (Array (List (Nat × List UInt8))))
    (data : ByteArray) (st : PrecState) : IO Nat := do
  let mut f := 0
  for b in [0:p.shapes.length] do
    let (cw, ch) := p.shapes.getD b (0, 0)
    for k in [0:cw * ch] do
      let cb := blockOf st b k
      let pl := (p.passes.getD b #[]).getD k #[]
      let tot := pl.foldl (· + ·) 0
      let fl := (p.first.getD b #[]).getD k 0
      let pcs := (pieces.getD b #[]).getD k []
      let segPasses := Spec.Tier1.segmentPasses (Spec.Tier1.Mode.ofStyle p.style) tot 0
      let ok := cb.numPasses == tot && cb.included == (fl < p.layers) &&
        (fl ≥ p.layers || (cb.zeroBitPlanes == (p.zbp.getD b #[]).getD k 0 && cb.firstLayer == fl)) &&
        cb.segments.toList.map (·.passes) == segPasses &&
        cb.segments.toList.map (fun s => (s.bytes data).toList) == groupPieces segPasses pcs
      if !ok then
        f := f + (← expect s!"{name} band {b} block {k}: passes {cb.numPasses}/{tot} segs {cb.segments.toList.map (·.passes)} vs {segPasses} zbp {cb.zeroBitPlanes} incl {cb.included}/{fl}" false)
  return f

/-- Random round trips, headers in the body stream and in a separate stream. -/
def randomTrips : IO Nat := do
  let cases := ((← IO.getEnv "JPEG2000_PACKET_CASES").bind String.toNat?).getD 300
  let mut s : UInt64 := 0x5EED4A4
  let mut f := 0
  let mut empties := 0
  for c in [0:cases] do
    let (p, s1) := randPlan s; s := s1
    let (hdrs, bodies, pieces, s1) := encodePlan p s; s := s1
    -- headers in the body stream
    let stream := (List.range p.layers).foldl (fun acc l =>
      let b := bodies.getD l []
      let (sop, rest) := if p.sop then (b.take 6, b.drop 6) else ([], b)
      acc ++ sop ++ hdrs.getD l [] ++ rest) []
    let data := ByteArray.mk stream.toArray
    match mkState p.style 30 p.r p.shapes with
    | .error e => f := f + (← expect s!"case {c}: state {e}" false)
    | .ok st0 =>
      match decodeSeq p.sop p.eph p.layers st0 (rd stream) with
      | .error e => f := f + (← expect s!"case {c} (style {p.style}): {e}" false)
      | .ok (st, infos, r) =>
        empties := empties + (infos.filter (·.empty)).size
        f := f + (← expect s!"case {c}: consumed" (r.pos == stream.length &&
          (infos.foldl (fun a i => a + i.headerBytes + i.bodyBytes) 0) == stream.length))
        f := f + (← checkState s!"case {c}" p pieces data st)
      -- separate header stream
      let hs := (List.range p.layers).foldl (fun acc l => acc ++ hdrs.getD l []) []
      let bs := (List.range p.layers).foldl (fun acc l => acc ++ bodies.getD l []) []
      let run : Except Error (PrecState × Reader × Reader) := do
        let mut st := st0
        let mut h := rd hs
        let mut b := rd bs
        for l in [0:p.layers] do
          let (st', _, h', b') ← decodePacket Limits.default p.sop p.eph l l st false h b
          st := st'; h := h'; b := b'
        return (st, h, b)
      match run with
      | .error e => f := f + (← expect s!"case {c} split: {e}" false)
      | .ok (st, h, b) =>
        f := f + (← expect s!"case {c} split: consumed" (h.pos == hs.length && b.pos == bs.length))
        f := f + (← checkState s!"case {c} split" p pieces (ByteArray.mk bs.toArray) st)
  IO.println s!"  packet: {cases} random precincts round-trip ({empties} zero-length packets)"
  return f

/-! ## 4. Corpus -/

/-- Directory of the T.803 conformance files. -/
def corpusDir : System.FilePath := "corpus/files/openjpeg-data/input/conformance"

/-- The T.803 codestreams and conformance JP2 files. -/
def corpusFiles : List String :=
  ((List.range 16).map fun i => s!"p0_{if i + 1 < 10 then "0" else ""}{i + 1}.j2k") ++
  ((List.range 7).map fun i => s!"p1_0{i + 1}.j2k") ++
  ((List.range 9).map fun i => s!"file{i + 1}.jp2")

/-- The separate packet-header stream of a tile, if any: its `PPT` data, or its tile-parts'
`PPM` chunks (tile-parts in codestream order). Task 4.5 moves this into the decoder. -/
def headerStream (h : Header) (data : ByteArray) (tp : TileParams) : Option ByteArray :=
  if !tp.tile.ppt.isEmpty then
    some (tp.tile.ppt.foldl (fun acc r => acc ++ r.bytes data) ByteArray.empty)
  else if h.ppm.segments.isEmpty then none
  else
    let all := (h.tiles.toList.flatMap fun t => t.tile.parts.toList.map (·.pos)).mergeSort
    let idx (pos : Nat) : Nat := (all.findIdx? (· == pos)).getD 0
    some (tp.tile.parts.foldl (fun acc part =>
      (h.ppm.chunks.getD (idx part.pos) #[]).foldl (fun acc r => acc ++ r.bytes data) acc)
      ByteArray.empty)

/-- Sanity checks of one tile's result. -/
def checkTile (name : String) (h : Header) (tp : TileParams)
    (hs : Option ByteArray) (t : TileCodeBlocks) : IO Nat := do
  let mut f := 0
  f := f + (← expect s!"{name}: tile data consumed {t.consumed}/{t.dataLength}"
    (t.consumed == t.dataLength))
  match hs with
  | none => f := f + (← expect s!"{name}: header + body = consumed"
      (t.headerBytes + t.bodyBytes == t.consumed))
  | some hs =>
    f := f + (← expect s!"{name}: header stream consumed {t.headerStreamConsumed}/{hs.size}"
      (t.headerStreamConsumed == hs.size && t.headerBytes == hs.size &&
       t.bodyBytes == t.consumed))
  let coding := (h.tiles.find? (·.index == tp.index)).map (·.coding) |>.getD h.defaults
  let inParts (r : ByteRange) : Bool :=
    tp.tile.parts.any fun p => p.data.offset ≤ r.offset && r.stop ≤ p.data.stop
  let mut bad := 0
  let mut passes := 0
  for br in t.blocks do
    let cb := br.block
    let style := (coding.comps.getD br.comp default).cbStyle.toNat
    passes := passes + cb.numPasses
    let k := br.band.maxZero - cb.zeroBitPlanes
    let ok := (cb.numPasses == 0 || (cb.included && cb.zeroBitPlanes ≤ br.band.maxZero &&
        cb.numPasses + 2 ≤ 3 * k)) &&
      cb.segments.toList.map (·.passes) ==
        Spec.Tier1.segmentPasses (Spec.Tier1.Mode.ofStyle style) cb.numPasses 0 &&
      cb.segments.all (fun s => s.ranges.all inParts)
    if !ok then
      bad := bad + 1
      if bad ≤ 3 then
        f := f + (← expect s!"{name}: block c{br.comp} r{br.res} p{br.prec} b{br.bandIdx} #{cb.geom.index}: passes {cb.numPasses} K {k} segs {cb.segments.toList.map (·.passes)}" false)
  if bad > 3 then f := f + (← expect s!"{name}: {bad} bad blocks" false)
  f := f + (← expect s!"{name}: passes {passes} vs {t.passes}" (passes == t.passes))
  return f

/-- Every corpus file: all packets of all tiles. -/
def corpus : IO Nat := do
  let mut f := 0
  let mut seen := 0
  for file in corpusFiles do
    let path := corpusDir / file
    if !(← path.pathExists) then continue
    seen := seen + 1
    let data ← IO.FS.readBinFile path
    match parse Limits.default data with
    | .error e => f := f + (← expect s!"{file}: header {e}" false)
    | .ok h =>
      let mut packets := 0
      let mut empty := 0
      let mut sops := 0
      let mut passes := 0
      let mut blocks := 0
      let mut split := 0
      let mut ok := true
      for tp in h.tiles do
        let hs := headerStream h data tp
        let res := match hs with
          | none => decodeTilePackets Limits.default h data tp passes
          | some _ => decodeTilePacketsWith Limits.default h data tp hs passes
        match res with
        | .error e =>
          ok := false
          f := f + (← expect s!"{file} tile {tp.index}: {e}" false)
        | .ok t =>
          packets := packets + t.packets
          empty := empty + t.emptyPackets
          sops := sops + t.sopPackets
          passes := passes + t.passes
          let bl := t.blocks
          blocks := blocks + bl.length
          split := split + (bl.filter fun b => b.block.segments.any (·.ranges.size > 1)).length
          f := f + (← checkTile s!"{file} tile {tp.index}" h tp hs t)
      if ok && h.ppm.segments.isEmpty && h.tiles.all (·.tile.ppt.isEmpty) then
        f := f + (← expect s!"{file}: decodeAllTiles" ((err? (decodeAllTiles Limits.default h data)).isNone))
      IO.println s!"  packet: {file} tiles={h.tiles.size} packets={packets} empty={empty} sop={sops} blocks={blocks} passes={passes} split-segment-blocks={split}"
  if seen == 0 then IO.println "  packet: corpus absent, skipped"
  return f

/-- Runs the suite; returns the number of failures. -/
def run : IO Nat := do
  let mut f := 0
  f := f + (← segmentCheck)
  f := f + (← handFirst)
  f := f + (← handEmpty)
  f := f + (← handCodewords)
  f := f + (← handStuffing)
  f := f + (← handBypass)
  f := f + (← handPlainCap)
  f := f + (← randomTrips)
  f := f + (← corpus)
  return f

end JPEG2000.Tests.Packet
