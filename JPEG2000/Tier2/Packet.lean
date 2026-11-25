import JPEG2000.Progression
import JPEG2000.TagTree

/-!
# Packets: headers, bodies and per-code-block segments
(Plan.md §3 rules 1–3, §5.2 "Tier-2"; T.800 B.9, B.10.1–B.10.8, A.8.1–A.8.2, D.4, D.6)

Task 4.4. A packet (B.9) of precinct `(i, r, k)` in layer `l` is

1. an optional `SOP` marker segment (A.8.1: `0xFF91`, `Lsop = 4`, `Nsop`) in the **body**
   stream when `Scod` bit 1 is set;
2. the packet header (B.10), read MSB first with the `0xFF` bit stuffing of B.10.1
   (`Bytes.BitReader`): one bit "non-empty" (`0` = zero-length packet, B.10.3); then for every
   sub-band of the precinct (LL at `r = 0`; HL, LH, HH above) and every code-block of the
   precinct-band in raster order:
   * **inclusion** (B.10.4): a code-block never included before is queried in the inclusion
     tag tree with threshold `l + 1`; one already included reads one bit;
   * on first inclusion, the **number of zero bit-planes** `P` (B.10.5) from the second tag
     tree (`TagTree.decodeValue`, at most `Mb + roiShift`);
   * the **number of new coding passes** (B.10.6, Table B.4: `0` → 1, `10` → 2,
     `11xx` → 3–5, `1111 xxxxx` → 6–36, `1111 11111 xxxxxxx` → 37–164);
   * the **`Lblock` increment** (B.10.7.1): `k` ones then a zero add `k` to `Lblock`
     (3 when the code-block is first included);
   * the **codeword-segment lengths** (B.10.7.2): the new passes are split by
     `segmentPasses style n firstPass` (`firstPass` = passes included by earlier layers) into
     pieces ending at codeword-segment ends (D.4 termination on each pass, D.6 bypass); each
     piece has a length field of `Lblock + ⌊log₂ passes⌋` bits;
   then the header is byte-aligned (`BitReader.align`: after a final `0xFF` the stuffed byte
   is consumed as well) and, when `Scod` bit 2 is set, an `EPH` marker (`0xFF92`, A.8.2)
   follows in the **header** stream;
3. the packet body: the bytes of every included code-block's pieces, in header order.

The header and body streams are separate parameters (`decodePacket`): without `PPM`/`PPT` the
header precedes its body in the tile data (`same = true`); with packed packet headers
(A.7.4–A.7.5) the headers come from another buffer (task 4.5 sources it; here
`decodeTilePacketsWith` takes it as an argument).

## Layer accumulation

The precinct state (`PrecState`) lives across the packets of the precinct: two tag trees per
precinct-band and per code-block whether it was included, `Lblock`, the passes and the
**segments** so far. A codeword segment continues across layers until `passEndsSegment` says
it ended: the first piece of a packet's contribution extends the code-block's last segment
unless the pass before it ended a segment; every further piece starts a new segment. A
segment therefore may consist of several byte ranges, from different packets and even
different tile-parts: **segments are lists of ranges** (`Segment.ranges`, absolute in the
input after `decodeTilePacketsWith`, adjacent ranges merged); `Segment.bytes` concatenates
them into a fresh `ByteArray` for a Tier-1 decoder that wants one contiguous buffer, and
`Segment.contiguous?` gives the single range when there is one (the common case).

`segmentPasses` is transcribed from `Spec.Tier1.segmentPasses` (`JPEG2000/` may not import
`Spec/`); `Tests/Packet.lean` checks that the two agree on every style byte `0…63` and every
`(numPasses, firstPass)` up to 200 × 200, and `Spec.Tier2Equiv.segmentPasses_eq` proves it.
It equals OpenJPEG's `opj_t2_init_seg`, including the plain-mode cap of 109 passes per segment
(`3·37 − 2`, task 4.9): without ROI a valid code-block has at most 109 passes, but streams
may signal more (`kodak_2layers_lrcp.j2c`: 172), and then OpenJPEG reads one length field per
109 passes.

## Strictness (Plan.md §3; compared with OpenJPEG 2.5 `opj_t2_read_packet_header/_data`)

* `SOP` (`Scod` bit 1, T.800 Table A.13 "SOP marker segments may be used"): optional before
  each packet, as OpenJPEG (it only warns when missing); when present it must have
  `Lsop = 4` and `Nsop` = the packet's index in the tile mod 2¹⁶ (A.8.1) — stricter than
  OpenJPEG, which ignores `Nsop`.
* `EPH` (`Scod` bit 2, "EPH marker shall be used"): required after every packet header,
  also of zero-length packets — stricter than OpenJPEG, which warns and continues.
* A packet body or header running past the end of its stream is `truncated`. OpenJPEG
  instead truncates the last segment or stops decoding the tile (partial streams).
* Zero bit-planes above `Mb + roiShift` (`Mb = G + εb − 1`, E-2) is `malformed` (`K < 0`
  coded bit-planes); more than `Limits.maxPassesPerCodeBlock` passes in one code-block is
  `limitExceeded`; a length field wider than 32 bits is `malformed`.
* The number of passes against `3·K − 2` is *not* checked here (OpenJPEG's Tier-1 just stops
  at the last bit-plane); the corpus test checks it.

## Limits (Plan.md §3 rules 2–3)

Before iterating, `decodeTilePacketsWith` checks `Progression.iterationWork` (packets
visited × POC volumes checked) against `Limits.maxPackets` and the tile's precinct count
against `Limits.maxPrecincts` (each precinct's code-block count is checked by
`Geometry.precinct`). Coding passes are accumulated and checked against
`maxPassesPerCodeBlock` per code-block and `maxCodingPasses` per tile (`decodeAllTiles`:
over the whole image). Every loop is a `for` over a bounded range, structural recursion
(`commaCode` with fuel 33 — `Lblock` beyond 32 cannot give a valid length field), or
`Progression.forPackets`.
-/

namespace JPEG2000.Tier2.Packet

open JPEG2000 JPEG2000.Bytes JPEG2000.Header JPEG2000.Marker JPEG2000.TilePart
open JPEG2000.Tier2.Geometry JPEG2000.Progression

/-- Errors of this module are reported at stage `tier2`. -/
def loc : Location := .at .tier2

/-- An error location at a byte offset of the stream being read. -/
def locAt (o : Nat) : Location := .atOffset .tier2 o

/-! ## Codeword segments (transcription of `Spec.Tier1.segmentPasses`) -/

/-- D.4, D.6 (Table D.9): with code-block style byte `style` (Table A.19), a codeword
segment is terminated after pass `i`: always with termination on each pass (bit 2); with
the bypass (bit 0), after pass 9 and after every later pass that is not a significance
propagation pass; otherwise after every 109th pass (OpenJPEG's `maxpasses = 109`, task 4.9). -/
def passEndsSegment (style i : Nat) : Bool :=
  style / 4 % 2 == 1 || (style % 2 == 1 && 9 ≤ i && (i == 0 || (i - 1) % 3 != 0)) ||
    (!(style % 2 == 1) && i % 109 == 108)

/-- Split the passes `i, …, i+n−1` into runs ending at segment ends (`cur` passes already
open). -/
def segmentRuns (style : Nat) : (n i cur : Nat) → List Nat
  | 0, _, cur => if cur = 0 then [] else [cur]
  | n + 1, i, cur =>
    if passEndsSegment style i then (cur + 1) :: segmentRuns style n (i + 1) 0
    else segmentRuns style n (i + 1) (cur + 1)

/-- The pieces of `numPasses` new passes starting at pass `firstPass` (B.10.7.2): the number
of passes of each piece, each piece ending at a codeword-segment end or at the last new
pass. -/
def segmentPasses (style numPasses firstPass : Nat) : List Nat :=
  segmentRuns style numPasses firstPass 0

/-! ## Records -/

/-- A codeword segment of a code-block (D.4): its bytes as a list of byte ranges (several
when it spans packets that are not adjacent in the stream) and its number of passes. -/
structure Segment where
  /-- Byte ranges, in order (adjacent ranges merged). -/
  ranges : Array ByteRange := #[]
  /-- Coding passes of the segment so far. -/
  passes : Nat := 0
  deriving Repr, DecidableEq, Inhabited

/-- Total number of bytes of a segment. -/
def Segment.length (s : Segment) : Nat := s.ranges.foldl (fun a r => a + r.length) 0

/-- The segment's bytes, concatenated into a fresh buffer (`data` is the buffer the ranges
refer to: the input after `decodeTilePacketsWith`). -/
def Segment.bytes (s : Segment) (data : ByteArray) : ByteArray :=
  s.ranges.foldl (fun acc r => acc ++ r.bytes data) ByteArray.empty

/-- The single range of a segment held contiguously (an empty segment gives an empty
range at offset 0), or `none` when it is split. -/
def Segment.contiguous? (s : Segment) : Option ByteRange :=
  match s.ranges.toList with
  | [] => some { offset := 0, length := 0 }
  | [r] => some r
  | _ => none

/-- Appends a range, merging it with the last one when adjacent; empty ranges are dropped. -/
def pushRange (rs : Array ByteRange) (r : ByteRange) : Array ByteRange :=
  if r.length = 0 then rs
  else match rs.back? with
    | some l => if l.stop = r.offset then rs.pop.push { l with length := l.length + r.length }
                else rs.push r
    | none => rs.push r

/-- The Tier-2 state and result of one code-block. -/
structure CodeBlock where
  /-- Its geometry (band coordinates, raster index in the precinct-band). -/
  geom : CodeBlockGeom
  /-- Included in some layer so far. -/
  included : Bool := false
  /-- First layer in which it was included (meaningful when `included`). -/
  firstLayer : Nat := 0
  /-- `Lblock` (B.10.7.1). -/
  lblock : Nat := 3
  /-- Number of missing most significant bit-planes `P` (B.10.5). -/
  zeroBitPlanes : Nat := 0
  /-- Coding passes included so far. -/
  numPasses : Nat := 0
  /-- The codeword segments so far (their pass counts sum to `numPasses`). -/
  segments : Array Segment := #[]
  deriving Repr, Inhabited

/-- The empty tag tree (placeholder). -/
def emptyTree : TagTree.Tree := { w := 0, h := 0, numLevels := 0, low := #[], val := #[] }

/-- The state of one precinct-band: its two tag trees (B.10.2) and its code-blocks. -/
structure BandState where
  /-- Orientation. -/
  band : Band
  /-- Precinct-band rectangle (band coordinates). -/
  rect : Rect
  /-- `Mb + roiShift`: the largest valid number of zero bit-planes (E-2, Annex H). -/
  maxZero : Nat
  /-- Inclusion tag tree (B.10.4). -/
  incl : TagTree.Tree
  /-- Zero bit-plane tag tree (B.10.5). -/
  zbp : TagTree.Tree
  /-- Code-blocks in raster order. -/
  blocks : Array CodeBlock

/-- The state of one precinct across its packets. -/
structure PrecState where
  /-- Code-block style byte (Table A.19) of the tile-component. -/
  style : Nat
  /-- One entry per sub-band of the resolution, in packet order. -/
  bands : Array BandState

instance : Inhabited PrecState := ⟨{ style := 0, bands := #[] }⟩

/-- `Mb = G + εb − 1` (E-2) of band `b` of resolution `r`; the step sizes are in band order
(LL, then HL, LH, HH per resolution). -/
def bandMb (p : CompParams) (r : Nat) (b : Band) : Nat :=
  let idx := if r = 0 then 0 else 3 * (r - 1) + b.index
  p.guardBits + (p.steps.getD idx default).exponent.toNat - 1

/-- A fresh precinct state: tag trees of `cw × ch` leaves per precinct-band (sizes are
bounded by `Geometry.precinct`'s code-block check). -/
def PrecState.init (L : Limits) (p : CompParams) (r : Nat) (pg : PrecinctGeom) :
    Except Error PrecState := do
  let bands ← pg.bands.mapM fun pb => do
    let incl ← TagTree.create L pb.cw pb.ch
    let zbp ← TagTree.create L pb.cw pb.ch
    let bs : BandState :=
      { band := pb.band, rect := pb.rect, maxZero := bandMb p r pb.band + p.roiShift, incl, zbp,
        blocks := pb.codeBlocks.map fun g => { geom := g } }
    return bs
  return { style := p.cbStyle.toNat, bands }

/-! ## Header fields -/

/-- One header bit (B.10.1). -/
@[inline] def readBit (br : BitReader) : Except Error (Bool × BitReader) := TagTree.bitNext br

/-- Number of new coding passes (B.10.6, Table B.4; OpenJPEG `opj_t2_getnumpasses`). -/
def readNumPasses (br : BitReader) : Except Error (Nat × BitReader) := do
  let (b, br) ← readBit br
  if !b then return (1, br)
  let (b, br) ← readBit br
  if !b then return (2, br)
  let (n, br) ← br.bits 2
  if n != 3 then return (3 + n.toNat, br)
  let (n, br) ← br.bits 5
  if n != 31 then return (6 + n.toNat, br)
  let (n, br) ← br.bits 7
  return (37 + n.toNat, br)

/-- The `Lblock` increment (B.10.7.1): the number of `1` bits before the first `0`; at most
`fuel − 1` ones are accepted. -/
def commaCode : Nat → Nat → BitReader → Except Error (Nat × BitReader)
  | 0, _, br => .error (.malformed (locAt br.pos) "Lblock increment too large")
  | fuel + 1, acc, br => do
    let (b, br) ← readBit br
    if b then commaCode fuel (acc + 1) br else return (acc, br)

/-- What a packet header says about one code-block: band and code-block index, the pieces
`(passes, length)` and whether the first piece continues the last segment. -/
structure Contribution where
  /-- Band index within the precinct. -/
  band : Nat
  /-- Code-block index within the precinct-band. -/
  block : Nat
  /-- `(passes, bytes)` of each piece. -/
  pieces : List (Nat × Nat)
  /-- The first piece extends the code-block's last segment. -/
  cont : Bool
  deriving Repr, Inhabited

/-- Reads the `k` length fields of the pieces (B.10.7.2). -/
def readLengths (lblock : Nat) : List Nat → BitReader → Except Error (List (Nat × Nat) × BitReader)
  | [], br => .ok ([], br)
  | p :: ps, br => do
    let (len, br) ← br.bits (lblock + Nat.log2 p)
    let (rest, br) ← readLengths lblock ps br
    return ((p, len.toNat) :: rest, br)

/-- The header part of one code-block in layer `layer` (B.10.4–B.10.7). Returns the updated
band state and, when the code-block is included, its contribution. -/
def headerBlock (L : Limits) (style layer bi k : Nat) (bs : BandState) (br : BitReader) :
    Except Error (BandState × Option Contribution × BitReader) := do
  let some cb := bs.blocks[k]? | throw (.malformed loc "code-block index out of range")
  let (inc, bs, br) ← if cb.included then do
      let (b, br) ← readBit br
      pure (b, bs, br)
    else do
      let (b, t, br) ← TagTree.decode bs.incl br k (layer + 1)
      pure (b, { bs with incl := t }, br)
  if !inc then return (bs, none, br)
  let (cb, bs, br) ← if cb.included then pure (cb, bs, br) else do
      let (z, t, br) ← TagTree.decodeValue bs.zbp br k bs.maxZero
      pure ({ cb with included := true, firstLayer := layer, zeroBitPlanes := z },
            { bs with zbp := t }, br)
  let (n, br) ← readNumPasses br
  let (inc, br) ← commaCode 33 0 br
  let lblock := cb.lblock + inc
  let total := cb.numPasses + n
  L.check (locAt br.pos) .passesPerCodeBlock total
  let pieces := segmentPasses style n cb.numPasses
  let (pieces, br) ← readLengths lblock pieces br
  let cont := cb.numPasses > 0 && !passEndsSegment style (cb.numPasses - 1)
  let cb := { cb with lblock, numPasses := total }
  return ({ bs with blocks := bs.blocks.setIfInBounds k cb },
          some { band := bi, block := k, pieces, cont }, br)

/-- The header part of one precinct-band. -/
def headerBand (L : Limits) (style layer bi : Nat) (bs : BandState) (br : BitReader) :
    Except Error (BandState × Array Contribution × BitReader) := do
  let mut bs := bs
  let mut br := br
  let mut cs : Array Contribution := #[]
  for k in [0:bs.blocks.size] do
    let (bs', c, br') ← headerBlock L style layer bi k bs br
    bs := bs'
    br := br'
    if let some c := c then cs := cs.push c
  return (bs, cs, br)

/-- The packet header after the "non-empty" bit (B.10.3–B.10.7): every band in turn. -/
def headerBands (L : Limits) (layer : Nat) (st : PrecState) (br : BitReader) :
    Except Error (PrecState × Array Contribution × BitReader) := do
  let mut bands := st.bands
  let mut br := br
  let mut cs : Array Contribution := #[]
  for bi in [0:st.bands.size] do
    let some bs := bands[bi]? | throw (.malformed loc "band index out of range")
    let (bs, c, br') ← headerBand L st.style layer bi bs br
    bands := bands.setIfInBounds bi bs
    br := br'
    cs := cs ++ c
  return ({ st with bands }, cs, br)

/-! ## Body -/

/-- Appends the pieces of one contribution read from the body (`ranges` gives each piece's
byte range in the body stream) to the code-block's segments. -/
def addPieces (cb : CodeBlock) (cont : Bool) : List (Nat × ByteRange) → CodeBlock
  | [] => cb
  | (p, rg) :: rest =>
    let segs :=
      match cont, cb.segments.back? with
      | true, some s =>
        cb.segments.pop.push { s with ranges := pushRange s.ranges rg, passes := s.passes + p }
      | _, _ => cb.segments.push { ranges := pushRange #[] rg, passes := p }
    addPieces { cb with segments := segs } false rest

/-- Takes the bytes of the pieces from the body reader (B.10.8): one range per piece. -/
def takePieces (body : Reader) : List (Nat × Nat) →
    Except Error (List (Nat × ByteRange) × Reader)
  | [] => .ok ([], body)
  | (p, len) :: rest => do
    if body.pos + len > body.stop then
      throw (.truncated (locAt body.pos) s!"packet body: segment of {len} bytes")
    let rg : ByteRange := { offset := body.pos, length := len }
    let body ← body.skip len
    let (rs, body) ← takePieces body rest
    return ((p, rg) :: rs, body)

/-- Reads a packet body: the contributions' bytes in order, appended to the segments. -/
def readBody (st : PrecState) (cs : Array Contribution) (body : Reader) :
    Except Error (PrecState × Reader) := do
  let mut bands := st.bands
  let mut body := body
  for c in cs do
    let (rs, body') ← takePieces body c.pieces
    body := body'
    let some bs := bands[c.band]? | throw (.malformed loc "band index out of range")
    let some cb := bs.blocks[c.block]? | throw (.malformed loc "code-block index out of range")
    let cb := addPieces cb c.cont rs
    bands := bands.setIfInBounds c.band { bs with blocks := bs.blocks.setIfInBounds c.block cb }
  return ({ st with bands }, body)

/-! ## One packet -/

/-- Facts about one decoded packet (for statistics and tests). -/
structure PacketInfo where
  /-- The "non-empty" bit was 0 (zero-length packet, B.10.3). -/
  empty : Bool
  /-- An `SOP` marker segment preceded it. -/
  sop : Bool
  /-- Bytes of the packet header (with `EPH`). -/
  headerBytes : Nat
  /-- Bytes of the body (with `SOP`). -/
  bodyBytes : Nat
  /-- Coding passes the packet added (over all its code-blocks). -/
  newPasses : Nat
  deriving Repr, Inhabited

/-- Reads an optional `SOP` marker segment (A.8.1) at the body reader: `Lsop = 4`, `Nsop` =
`seq mod 2¹⁶`. Returns whether one was present. -/
def readSop (seq : Nat) (body : Reader) : Except Error (Bool × Reader) :=
  match body.u16be with
  | .ok (m, r) =>
    if m == 0xFF91 then do
      let (lsop, r) ← r.u16be
      if lsop != 4 then throw (.malformed (locAt body.pos) s!"SOP: Lsop = {lsop}, expected 4")
      let (nsop, r) ← r.u16be
      if nsop.toNat != seq % 65536 then
        throw (.malformed (locAt body.pos) s!"SOP: Nsop = {nsop}, expected {seq % 65536}")
      return (true, r)
    else .ok (false, body)
  | .error _ => .ok (false, body)

/-- Reads the `EPH` marker (A.8.2) that must end the packet header. -/
def readEph (hdr : Reader) : Except Error Reader := do
  let (m, r) ← hdr.u16be
  if m != 0xFF92 then throw (.malformed (locAt hdr.pos) "EPH marker expected after packet header")
  return r

/-- **Decodes one packet** of precinct state `st` in layer `layer` (B.9, B.10): optional
`SOP` (if `sop`, from the body stream; `seq` is the packet's index in the tile), header from
`hdr` — or, when `same`, from the body stream right after the `SOP` — byte-aligned, `EPH` if
`eph`, then the body from the body stream (after the header when `same`). Returns the
updated precinct state (segments hold ranges of the body stream's buffer), facts about the
packet, and the header and body readers after it (equal when `same`). -/
def decodePacket (L : Limits) (sop eph : Bool) (seq layer : Nat) (st : PrecState)
    (same : Bool) (hdr body : Reader) :
    Except Error (PrecState × PacketInfo × Reader × Reader) := do
  let body0 := body.pos
  let (hasSop, body) ← if sop then readSop seq body else pure (false, body)
  let hdr := if same then body else hdr
  let hdr0 := hdr.pos
  let (nonEmpty, br) ← readBit (BitReader.ofReader hdr)
  let (st, cs, br) ← if nonEmpty then headerBands L layer st br else pure (st, #[], br)
  let br ← br.align
  let hdr := br.toReader .tier2
  let hdr ← if eph then readEph hdr else pure hdr
  let headerBytes := hdr.pos - hdr0
  let body := if same then hdr else body
  let bodyStart := body.pos
  let (st, body) ← readBody st cs body
  let newPasses := cs.foldl (fun a c => c.pieces.foldl (fun a p => a + p.1) a) 0
  let info : PacketInfo :=
    { empty := !nonEmpty, sop := hasSop, headerBytes,
      bodyBytes := body.pos - bodyStart + (if same then 0 else bodyStart - body0)
        + (if same && hasSop then 6 else 0),
      newPasses }
  return (st, info, if same then body else hdr, body)

/-! ## Tiles -/

/-- The result for one precinct-band: its code-blocks with their zero bit-planes, passes and
segments. -/
structure BandOut where
  /-- Orientation. -/
  band : Band
  /-- Precinct-band rectangle (band coordinates). -/
  rect : Rect
  /-- `Mb + roiShift` (E-2, Annex H): the coded bit-planes of a code-block are
  `maxZero − zeroBitPlanes`. -/
  maxZero : Nat
  /-- Code-blocks in raster order. -/
  blocks : Array CodeBlock
  deriving Repr, Inhabited

/-- The result for one precinct: its bands in packet order. -/
structure PrecinctOut where
  /-- Precinct index within the resolution. -/
  index : Nat
  /-- One entry per sub-band of the resolution. -/
  bands : Array BandOut
  deriving Repr, Inhabited

/-- The per-code-block result of Tier-2 for one tile: `comps[i][r][k]` is precinct `k` of
resolution `r` of component `i`; every segment range is absolute in the input buffer. -/
structure TileCodeBlocks where
  /-- Tile index. -/
  tile : Nat
  /-- Per component, per resolution, per precinct. -/
  comps : Array (Array (Array PrecinctOut))
  /-- Packets decoded. -/
  packets : Nat
  /-- Zero-length packets among them. -/
  emptyPackets : Nat
  /-- Packets preceded by an `SOP` marker segment. -/
  sopPackets : Nat
  /-- Bytes of packet headers (with `EPH`). -/
  headerBytes : Nat
  /-- Bytes of packet bodies (with `SOP`). -/
  bodyBytes : Nat
  /-- Bytes of the tile's data (all tile-parts after `SOD`). -/
  dataLength : Nat
  /-- Bytes of the tile data consumed by the packets. -/
  consumed : Nat
  /-- Bytes of the separate header stream consumed (0 without one). -/
  headerStreamConsumed : Nat
  /-- Coding passes over all code-blocks of the tile. -/
  passes : Nat
  deriving Repr, Inhabited

/-- One code-block of a tile result with its position. -/
structure BlockRef where
  /-- Component. -/
  comp : Nat
  /-- Resolution. -/
  res : Nat
  /-- Precinct index. -/
  prec : Nat
  /-- Band index within the resolution (0 = LL at `r = 0`; 0–2 = HL, LH, HH above). -/
  bandIdx : Nat
  /-- The band's data. -/
  band : BandOut
  /-- The code-block. -/
  block : CodeBlock

/-- Every code-block of a tile, component by component, resolution, precinct, band,
code-block. -/
def TileCodeBlocks.blocks (t : TileCodeBlocks) : List BlockRef :=
  t.comps.toList.zipIdx.flatMap fun (rs, i) =>
    rs.toList.zipIdx.flatMap fun (ps, r) =>
      ps.toList.flatMap fun p =>
        p.bands.toList.zipIdx.flatMap fun (b, bi) =>
          b.blocks.toList.map fun cb =>
            { comp := i, res := r, prec := p.index, bandIdx := bi, band := b, block := cb }

/-- The tile's data: its tile-parts' bit-stream ranges (after `SOD`) concatenated, with the
map `(start in the buffer, offset in the input, length)` of each part. -/
def tileData (data : ByteArray) (t : Tile) : Except Error (ByteArray × List (Nat × Nat × Nat)) := do
  let mut buf := ByteArray.empty
  let mut parts : Array (Nat × Nat × Nat) := #[]
  for p in t.parts do
    if p.data.stop > data.size then
      throw (.truncated (locAt p.data.offset) "tile-part data past the end of the input")
    parts := parts.push (buf.size, p.data.offset, p.data.length)
    buf := buf ++ p.data.bytes data
  return (buf, parts.toList)

/-- A range of the tile buffer as ranges of the input (split at tile-part boundaries). -/
def translate (rg : ByteRange) : List (Nat × Nat × Nat) → Array ByteRange → Array ByteRange
  | [], acc => acc
  | (bs, io, len) :: ps, acc =>
    let lo := max rg.offset bs
    let hi := min rg.stop (bs + len)
    translate rg ps (if lo < hi then pushRange acc { offset := io + (lo - bs), length := hi - lo }
                     else acc)

/-- A precinct state as a result, its ranges translated to the input. -/
def PrecState.out (parts : List (Nat × Nat × Nat)) (k : Nat) (st : PrecState) : PrecinctOut :=
  { index := k,
    bands := st.bands.map fun bs =>
      { band := bs.band, rect := bs.rect, maxZero := bs.maxZero,
        blocks := bs.blocks.map fun cb =>
          { cb with segments := cb.segments.map fun s =>
              { s with ranges := s.ranges.foldl (fun acc r => translate r parts acc) #[] } } } }

/-- The fold state of the packet loop. -/
structure LoopState where
  /-- Precinct states, indexed through `base`. -/
  precs : Array PrecState
  /-- Header stream reader. -/
  hdr : Reader
  /-- Body stream reader. -/
  body : Reader
  /-- Packets so far (`Nsop` of the next one). -/
  seq : Nat := 0
  /-- Zero-length packets so far. -/
  empty : Nat := 0
  /-- `SOP`s so far. -/
  sops : Nat := 0
  /-- Header bytes so far. -/
  hdrBytes : Nat := 0
  /-- Body bytes so far. -/
  bodyBytes : Nat := 0
  /-- Coding passes so far (tile). -/
  passes : Nat := 0

/-- All precinct states of a tile, and `base[i][r]` = index of precinct 0 of resolution `r`
of component `i`. Checks the tile's precinct and code-block totals against `Limits`. -/
def initPrecincts (L : Limits) (g : Layout) :
    Except Error (Array PrecState × Array (Array Nat) × Array (Array (Nat × Nat))) := do
  let mut precs : Array PrecState := #[]
  let mut base : Array (Array Nat) := #[]
  let mut spans : Array (Array (Nat × Nat)) := #[]
  let mut blocks := 0
  for i in [0:g.numComps] do
    let tc := g.comp i
    let mut bi : Array Nat := #[]
    let mut si : Array (Nat × Nat) := #[]
    for r in [0:tc.params.levels + 1] do
      bi := bi.push precs.size
      let res ← resolution L tc r
      L.check loc .precincts (precs.size + res.numPrecincts)
      si := si.push (precs.size, res.numPrecincts)
      for p in [0:res.numPrecincts] do
        let pg ← precinct L res p
        blocks := blocks + pg.bands.foldl (fun a b => a + b.codeBlocks.size) 0
        L.check loc .codeBlocks blocks
        precs := precs.push (← PrecState.init L tc.params r pg)
    base := base.push bi
    spans := spans.push si
  return (precs, base, spans)

/-- **Decodes every packet of a tile** (B.9–B.12) and returns its per-code-block segments.
`hdrStream` is the separate packet-header stream (`PPM`/`PPT`, A.7.4–A.7.5; sourced by the
caller) or `none` when the headers are in the tile data. `passesBefore` counts the coding
passes of earlier tiles (checked with this tile's against `Limits.maxCodingPasses`).
Errors in the body stream report offsets in the concatenated tile data. -/
def decodeTilePacketsWith (L : Limits) (h : Header) (data : ByteArray) (tp : TileParams)
    (hdrStream : Option ByteArray) (passesBefore : Nat := 0) : Except Error TileCodeBlocks := do
  let (g, coding) ← Layout.ofHeader h tp.index
  L.check loc .packets (iterationWork g coding.progression coding.poc)
  let (precs, base, spans) ← initPrecincts L g
  let (buf, parts) ← tileData data tp.tile
  let body := Reader.ofByteArray buf .tier2
  let same := hdrStream.isNone
  let hdr := match hdrStream with
    | some hs => Reader.ofByteArray hs .tier2
    | none => body
  let step (s : LoopState) (p : PacketId) : Except Error LoopState := do
    let idx := ((base.getD p.comp #[]).getD p.res 0) + p.prec
    let some st := s.precs[idx]? | throw (.malformed loc "precinct index out of range")
    let precs := s.precs.setIfInBounds idx default
    let (st, info, hdr, body) ←
      decodePacket L coding.sop coding.eph s.seq p.layer st same s.hdr s.body
    let passes := s.passes + info.newPasses
    L.check loc .codingPasses (passesBefore + passes)
    return { precs := precs.setIfInBounds idx st, hdr, body, seq := s.seq + 1,
             empty := s.empty + (if info.empty then 1 else 0),
             sops := s.sops + (if info.sop then 1 else 0),
             hdrBytes := s.hdrBytes + info.headerBytes,
             bodyBytes := s.bodyBytes + info.bodyBytes, passes }
  let s ← forPackets (m := Except Error) g coding.progression coding.poc step
    { precs, hdr, body }
  let comps := spans.map fun si => si.map fun (start, n) =>
    (Array.range n).map fun k => (s.precs.getD (start + k) default).out parts k
  return { tile := tp.index, comps, packets := s.seq, emptyPackets := s.empty,
           sopPackets := s.sops, headerBytes := s.hdrBytes, bodyBytes := s.bodyBytes,
           dataLength := buf.size, consumed := s.body.pos,
           headerStreamConsumed := if same then 0 else s.hdr.pos, passes := s.passes }

/-- `decodeTilePacketsWith` with the headers in the tile data. Tiles with packed packet
headers (`PPM` in the main header or `PPT` in the tile) are `unsupported` here: task 4.5
sources their header stream. -/
def decodeTilePackets (L : Limits) (h : Header) (data : ByteArray) (tp : TileParams)
    (passesBefore : Nat := 0) : Except Error TileCodeBlocks := do
  if !h.ppm.segments.isEmpty || !tp.tile.ppt.isEmpty then
    throw (.unsupported loc "packed packet headers (PPM/PPT) are sourced by task 4.5")
  decodeTilePacketsWith L h data tp none passesBefore

/-- Every tile with tile-parts in turn (`decodeTilePackets`), the coding passes checked over
the whole image against `Limits.maxCodingPasses`. -/
def decodeAllTiles (L : Limits) (h : Header) (data : ByteArray) :
    Except Error (Array TileCodeBlocks) := do
  let mut out := #[]
  let mut passes := 0
  for tp in h.tiles do
    let t ← decodeTilePackets L h data tp passes
    passes := passes + t.passes
    out := out.push t
  return out

end JPEG2000.Tier2.Packet
