import JPEG2000.Tier2.Headers
import Spec.TagTree
import Spec.Progression
import Spec.Tier1.Decode

/-!
# Tier-2 specification: packet headers over bit lists, bodies over byte lists
(Plan.md §4 C9, §5.1, §5.2 "Tier-2"; T.800 B.9, B.10.1–B.10.8, B.12, A.8.1–A.8.2, D.4, D.6)

Task 7.1b. A near-literal transcription of Annex B.10 as a decoder over **lists**:

* **B.10.1 bit stuffing** is a function on bytes: `unstuff : List UInt8 → List Bool` gives
  the header bits MSB first, a byte following `0xFF` contributing only its 7 low bits. The
  header ends on a byte boundary; `alignedLength` gives the number of header bytes holding
  its first `n` bits: up to the end of the byte holding bit `n`, plus the following byte when
  that byte is `0xFF` (its stuffed bit belongs to the header, B.10.1).
* **The packet header** (B.10.3–B.10.7) is a function over the header bit list: the
  "non-empty" bit; per sub-band and per code-block in raster order, inclusion (B.10.4: the
  inclusion tag tree `Spec.TagTree.query` with threshold `layer + 1` for a code-block never
  included, one bit otherwise), the zero bit-planes on first inclusion (B.10.5:
  `Spec.TagTree.exact`, at most `Mb + roiShift`), the number of new passes (B.10.6, Table B.4,
  `numPasses`), the `Lblock` increment (B.10.7.1, `commaCode`) and one length field of
  `Lblock + ⌊log₂ passes⌋` bits per codeword-segment piece (B.10.7.2), the pieces given by
  `Spec.Tier1.segmentPasses` of the code-block style (D.4, D.6; with OpenJPEG's plain-mode
  cap of 109 passes per codeword segment, task 4.9).
* **The body** (B.10.8) is a byte list: each included code-block's pieces in header order,
  appended to its codeword segments (a piece continues the code-block's open segment unless
  the pass before it ended one).
* **Per-code-block state** (`BlockSt`: included, `Lblock`, zero bit-planes, passes,
  segments) and per precinct-band tag-tree states (`Spec.TagTree.St`) are plain records in
  lists. A code-block's segments are `Spec.Tier1.Segment`s (byte list + pass count): exactly
  what `Spec.Tier1.decodeCodeBlock` consumes.
* **Packet iteration** follows the spec sequence `Spec.Progression.packets` (B.12, with POC).

## Shared with the fast decoder (not Tier-2 decoding)

The tile layout, the precinct and code-block geometry and their `Limits` checks
(`Packet.initPrecincts`, B.5–B.7, Plan.md §3 rule 3), the tile's data as the concatenation of
its tile-parts (`Packet.tileData`, A.4) and the packed packet-header stream
(`Tier2.Headers.HeaderStream`, A.7.4–A.7.5, task 4.5) are the fast decoder's: they are
geometry and stream assembly, specified elsewhere. The spec starts from fresh states built
from that geometry (`PrecSt.ofFast`: every tag tree `Spec.TagTree.init`).

## Strictness (as the fast decoder, `JPEG2000.Tier2.Packet`)

`SOP` optional, with `Lsop = 4` and `Nsop` = packet index mod 2¹⁶ when present; `EPH`
required when `Scod` says so; running out of header bits or body bytes is an error; zero
bit-planes above `Mb + roiShift` is an error (`exact` with that bound); more than
`Limits.maxPassesPerCodeBlock` passes in a code-block, or the tile's passes plus earlier
tiles' beyond `Limits.maxCodingPasses`, is an error; an `Lblock` increment of 33 or more and a
length field wider than 32 bits are errors; leftover bytes of a separate header stream are an
error. The spec reports one generic error per kind; only success/failure is compared.
-/

namespace JPEG2000.Spec.Tier2

open JPEG2000 JPEG2000.Bytes JPEG2000.Header JPEG2000.TilePart
open JPEG2000.Tier2.Geometry JPEG2000.Tier2.Packet JPEG2000.Progression

/-- Errors of the spec are reported at stage `tier2`. -/
def loc : Location := .at .tier2

/-- The spec's error (the kind is irrelevant: only failure is compared with the fast
decoder). -/
def eSpec (what : String) : Error := .malformed loc what

/-! ## B.10.1 — bit stuffing -/

/-- The `n` low bits of `v`, most significant first. -/
def bitsOf (v : Nat) : Nat → List Bool
  | 0 => []
  | n + 1 => v.testBit n :: bitsOf v n

/-- Un-stuffing with a flag "the previous byte was `0xFF`": such a byte contributes its 7 low
bits (its MSB is the stuffed 0), every other byte its 8 bits. -/
def unstuffAux : Bool → List UInt8 → List Bool
  | _, [] => []
  | ff, b :: bs => bitsOf b.toNat (if ff then 7 else 8) ++ unstuffAux (b == 0xFF) bs

/-- **B.10.1**: the packet-header bits held by a byte sequence (MSB first, a byte after
`0xFF` contributing 7 bits). -/
def unstuff (bs : List UInt8) : List Bool := unstuffAux false bs

/-- The number of bytes of a packet header whose first `n` bits were read from
`unstuffAux ff bs` (B.10.1): up to the byte holding bit `n` (the rest of it is padding), plus
the next byte when that byte is `0xFF` (the header never ends in `0xFF`: the stuffed bit
follows). `none` when the bytes run out. -/
def alignedLength : Bool → List UInt8 → Nat → Option Nat
  | _, _, 0 => some 0
  | _, [], _ + 1 => none
  | ff, b :: bs, n + 1 =>
    if n + 1 ≤ (if ff then 7 else 8) then
      if b == 0xFF then (if bs.isEmpty then none else some 2) else some 1
    else (alignedLength (b == 0xFF) bs (n + 1 - (if ff then 7 else 8))).map (· + 1)

/-! ## B.10.3–B.10.7 — header fields over a bit list -/

/-- One header bit (`none` → error when the bits run out). -/
def bit (bs : List Bool) : Except Error (Bool × List Bool) := Spec.TagTree.listNext bs

/-- `k` bits as an unsigned value, first bit most significant, appended to `acc`. -/
def bitsVal (acc : Nat) : Nat → List Bool → Except Error (Nat × List Bool)
  | 0, bs => .ok (acc, bs)
  | k + 1, bs => do
    let (x, bs) ← bit bs
    bitsVal (2 * acc + if x then 1 else 0) k bs

/-- A field of `n` bits; fields wider than 32 bits are refused (as the fast decoder). -/
def field (n : Nat) (bs : List Bool) : Except Error (Nat × List Bool) :=
  if n ≤ 32 then bitsVal 0 n bs else .error (eSpec "field wider than 32 bits")

/-- **B.10.6, Table B.4**: the number of new coding passes (`0` → 1, `10` → 2,
`11xx` → 3–5, `1111 xxxxx` → 6–36, `1111 11111 xxxxxxx` → 37–164). -/
def numPasses (bs : List Bool) : Except Error (Nat × List Bool) := do
  let (b, bs) ← bit bs
  if !b then return (1, bs)
  let (b, bs) ← bit bs
  if !b then return (2, bs)
  let (n, bs) ← field 2 bs
  if n != 3 then return (3 + n, bs)
  let (n, bs) ← field 5 bs
  if n != 31 then return (6 + n, bs)
  let (n, bs) ← field 7 bs
  return (37 + n, bs)

/-- **B.10.7.1**: the `Lblock` increment, the number of `1`s before the first `0` (at most
`fuel − 1` accepted). -/
def commaCode : Nat → Nat → List Bool → Except Error (Nat × List Bool)
  | 0, _, _ => .error (eSpec "Lblock increment too large")
  | fuel + 1, acc, bs => do
    let (b, bs) ← bit bs
    if b then commaCode fuel (acc + 1) bs else return (acc, bs)

/-- **B.10.7.2**: one length field of `Lblock + ⌊log₂ p⌋` bits per piece of `p` passes. -/
def lengths (lblock : Nat) : List Nat → List Bool → Except Error (List (Nat × Nat) × List Bool)
  | [], bs => .ok ([], bs)
  | p :: ps, bs => do
    let (len, bs) ← field (lblock + Nat.log2 p) bs
    let (rest, bs) ← lengths lblock ps bs
    return ((p, len) :: rest, bs)

/-! ## States -/

/-- The Tier-2 state and result of one code-block. -/
structure BlockSt where
  /-- Its geometry (from `Tier2.Geometry`). -/
  geom : CodeBlockGeom
  /-- Included in some layer so far. -/
  included : Bool := false
  /-- `Lblock` (B.10.7.1). -/
  lblock : Nat := 3
  /-- Number of missing most significant bit-planes `P` (B.10.5). -/
  zbp : Nat := 0
  /-- Coding passes included so far. -/
  passes : Nat := 0
  /-- Codeword segments so far: bytes and passes (the input of `Spec.Tier1.decodeCodeBlock`). -/
  segs : List Spec.Tier1.Segment := []
  deriving Repr, Inhabited

/-- The state of one precinct-band. -/
structure BandSt where
  /-- Orientation. -/
  band : Band
  /-- Precinct-band rectangle (band coordinates). -/
  rect : Rect
  /-- Code-blocks per row (tag-tree leaves per row). -/
  w : Nat
  /-- Code-block rows. -/
  h : Nat
  /-- `Mb + roiShift`: the largest valid number of zero bit-planes. -/
  maxZero : Nat
  /-- Inclusion tag tree (B.10.4). -/
  incl : Spec.TagTree.St
  /-- Zero bit-plane tag tree (B.10.5). -/
  zbp : Spec.TagTree.St
  /-- Code-blocks in raster order. -/
  blocks : List BlockSt

/-- The state of one precinct. -/
structure PrecSt where
  /-- Code-block style byte (Table A.19). -/
  style : Nat
  /-- One entry per sub-band of the resolution, in packet order. -/
  bands : List BandSt

instance : Inhabited PrecSt := ⟨{ style := 0, bands := [] }⟩

/-- A fresh spec precinct state with the geometry of a fresh fast one (tag trees
`Spec.TagTree.init`, code-blocks never included). -/
def PrecSt.ofFast (st : PrecState) : PrecSt :=
  { style := st.style,
    bands := st.bands.toList.map fun bs =>
      { band := bs.band, rect := bs.rect, w := bs.incl.w, h := bs.incl.h, maxZero := bs.maxZero,
        incl := Spec.TagTree.init, zbp := Spec.TagTree.init,
        blocks := bs.blocks.toList.map fun cb => { geom := cb.geom } } }

/-! ## The packet header -/

/-- **B.10.4–B.10.7 for code-block `k` of precinct-band `bi`** in layer `layer`. -/
def blockHeader (L : Limits) (style layer bi k : Nat) (bs : BandSt) (bits : List Bool) :
    Except Error (BandSt × Option Contribution × List Bool) := do
  let some cb := bs.blocks[k]? | throw (eSpec "code-block index")
  let (inc, bs, bits) ← if cb.included then do
      let (b, bits) ← bit bits
      pure (b, bs, bits)
    else do
      let some (b, s, bits) :=
          Spec.TagTree.query bs.w bs.h bs.incl (k % bs.w) (k / bs.w) (layer + 1) bits
        | throw (eSpec "inclusion tag tree")
      pure (b, { bs with incl := s }, bits)
  if !inc then return (bs, none, bits)
  let (cb, bs, bits) ← if cb.included then pure (cb, bs, bits) else do
      let some (z, s, bits) :=
          Spec.TagTree.exact bs.w bs.h bs.zbp (k % bs.w) (k / bs.w) bs.maxZero bits
        | throw (eSpec "zero bit-plane tag tree")
      pure ({ cb with included := true, zbp := z }, { bs with zbp := s }, bits)
  let (n, bits) ← numPasses bits
  let (inc, bits) ← commaCode 33 0 bits
  let lblock := cb.lblock + inc
  let total := cb.passes + n
  L.check loc .passesPerCodeBlock total
  let m := Spec.Tier1.Mode.ofStyle style
  let (pieces, bits) ← lengths lblock (Spec.Tier1.segmentPasses m n cb.passes) bits
  let cont := cb.passes > 0 && !Spec.Tier1.passEndsSegment m (cb.passes - 1)
  return ({ bs with blocks := bs.blocks.set k { cb with lblock, passes := total } },
          some { band := bi, block := k, pieces, cont }, bits)

/-- The code-blocks `ks` of a precinct-band in turn. -/
def blocksHeader (L : Limits) (style layer bi : Nat) :
    List Nat → BandSt → List Bool → Except Error (BandSt × List Contribution × List Bool)
  | [], bs, bits => .ok (bs, [], bits)
  | k :: ks, bs, bits => do
    let (bs, c, bits) ← blockHeader L style layer bi k bs bits
    let (bs, cs, bits) ← blocksHeader L style layer bi ks bs bits
    return (bs, c.toList ++ cs, bits)

/-- The sub-bands `bi, bi + 1, …` of a precinct in turn, each over all its code-blocks in
raster order. -/
def bandsHeader (L : Limits) (style layer : Nat) :
    Nat → List BandSt → List Bool → Except Error (List BandSt × List Contribution × List Bool)
  | _, [], bits => .ok ([], [], bits)
  | bi, bs :: rest, bits => do
    let (bs, c, bits) ← blocksHeader L style layer bi (List.range bs.blocks.length) bs bits
    let (rest, cs, bits) ← bandsHeader L style layer (bi + 1) rest bits
    return (bs :: rest, c ++ cs, bits)

/-! ## B.10.8 — the body -/

/-- The bytes of the pieces, in order (`len` bytes each). -/
def takePieces : List (Nat × Nat) → List UInt8 → Except Error (List (Nat × List UInt8) × List UInt8)
  | [], body => .ok ([], body)
  | (p, len) :: rest, body => do
    if len > body.length then throw (eSpec "packet body truncated")
    let (rs, body') ← takePieces rest (body.drop len)
    return ((p, body.take len) :: rs, body')

/-- Appends the pieces of one contribution to the code-block's segments: the first continues
the last segment when `cont`, every other starts a new segment (D.4). -/
def addPieces (cb : BlockSt) (cont : Bool) : List (Nat × List UInt8) → BlockSt
  | [] => cb
  | (p, d) :: rest =>
    let segs :=
      match cont, cb.segs.getLast? with
      | true, some s => cb.segs.dropLast ++ [{ data := s.data ++ d, passes := s.passes + p }]
      | _, _ => cb.segs ++ [{ data := d, passes := p }]
    addPieces { cb with segs } false rest

/-- The body of a packet: each contribution's bytes appended to its code-block. -/
def readBody (st : PrecSt) : List Contribution → List UInt8 → Except Error (PrecSt × List UInt8)
  | [], body => .ok (st, body)
  | c :: cs, body => do
    let (rs, body) ← takePieces c.pieces body
    let some bs := st.bands[c.band]? | throw (eSpec "band index")
    let some cb := bs.blocks[c.block]? | throw (eSpec "code-block index")
    let cb := addPieces cb c.cont rs
    readBody { st with bands := st.bands.set c.band { bs with blocks := bs.blocks.set c.block cb } }
      cs body

/-! ## One packet (B.9, A.8) -/

/-- An optional `SOP` marker segment (A.8.1): `0xFF91`, `Lsop = 4`, `Nsop = seq mod 2¹⁶`. -/
def readSop (seq : Nat) (body : List UInt8) : Except Error (List UInt8) :=
  match body with
  | m0 :: m1 :: rest =>
    if m0 = 0xFF ∧ m1 = 0x91 then
      match rest with
      | a :: b :: c :: d :: rest =>
        if a.toNat * 256 + b.toNat != 4 then .error (eSpec "SOP: Lsop")
        else if c.toNat * 256 + d.toNat != seq % 65536 then .error (eSpec "SOP: Nsop")
        else .ok rest
      | _ => .error (eSpec "SOP truncated")
    else .ok body
  | _ => .ok body

/-- The `EPH` marker (A.8.2) ending a packet header. -/
def readEph : List UInt8 → Except Error (List UInt8)
  | m0 :: m1 :: rest => if m0 = 0xFF ∧ m1 = 0x92 then .ok rest else .error (eSpec "EPH expected")
  | _ => .error (eSpec "EPH expected")

/-- The coding passes a packet adds. -/
def newPasses (cs : List Contribution) : Nat :=
  cs.foldl (fun a c => c.pieces.foldl (fun a p => a + p.1) a) 0

/-- **One packet** of precinct state `st` in layer `layer` (B.9, B.10): optional `SOP` (body
stream), the header bits `unstuff hdr` (`hdr` = the body stream when `same`), the header's
bytes (`alignedLength`), `EPH`, then the body. Returns the new state, the passes added, and
the remaining header and body streams (equal when `same`). -/
def packet (L : Limits) (sop eph : Bool) (seq layer : Nat) (st : PrecSt) (same : Bool)
    (hdr body : List UInt8) : Except Error (PrecSt × Nat × List UInt8 × List UInt8) := do
  let body ← if sop then readSop seq body else pure body
  let hdr := if same then body else hdr
  let bits := unstuff hdr
  let (nonEmpty, rest) ← bit bits
  let (bands, cs, rest) ← if nonEmpty then bandsHeader L st.style layer 0 st.bands rest
    else pure (st.bands, [], rest)
  let some n := alignedLength false hdr (bits.length - rest.length)
    | throw (eSpec "packet header stuffing byte")
  let hdr := hdr.drop n
  let hdr ← if eph then readEph hdr else pure hdr
  let body := if same then hdr else body
  let (st, body) ← readBody { st with bands } cs body
  return (st, newPasses cs, if same then body else hdr, body)

/-! ## A tile (B.12) -/

/-- The fold state of the packet sequence. -/
structure Loop where
  /-- Precinct states (indexed through `base`). -/
  precs : List PrecSt
  /-- Header stream. -/
  hdr : List UInt8
  /-- Body stream. -/
  body : List UInt8
  /-- Packets so far. -/
  seq : Nat := 0
  /-- Coding passes so far. -/
  passes : Nat := 0

/-- One packet of the sequence. -/
def step (L : Limits) (sop eph same : Bool) (base : Array (Array Nat)) (passesBefore : Nat)
    (s : Loop) (p : PacketId) : Except Error Loop := do
  let idx := ((base.getD p.comp #[]).getD p.res 0) + p.prec
  let some st := s.precs[idx]? | throw (eSpec "precinct index")
  let (st, n, hdr, body) ← packet L sop eph s.seq p.layer st same s.hdr s.body
  let passes := s.passes + n
  L.check loc .codingPasses (passesBefore + passes)
  return { precs := s.precs.set idx st, hdr, body, seq := s.seq + 1, passes }

/-- The result for one precinct-band. -/
structure BandOut where
  /-- Orientation. -/
  band : Band
  /-- Precinct-band rectangle. -/
  rect : Rect
  /-- `Mb + roiShift`. -/
  maxZero : Nat
  /-- Code-blocks in raster order. -/
  blocks : List BlockSt
  deriving Repr, Inhabited

/-- A precinct state as a result. -/
def PrecSt.out (st : PrecSt) : List BandOut :=
  st.bands.map fun bs => { band := bs.band, rect := bs.rect, maxZero := bs.maxZero, blocks := bs.blocks }

/-- The spec result of one tile: per component, resolution, precinct, its bands. -/
structure TileOut where
  /-- `comps[i][r][k]` = the bands of precinct `k` of resolution `r` of component `i`. -/
  comps : List (List (List (List BandOut)))
  /-- Coding passes over the tile. -/
  passes : Nat
  /-- Bytes of the separate header stream left over (0 without one). -/
  hdrLeft : Nat
  deriving Repr, Inhabited

/-- **The packets of a tile** (B.9–B.12): the packet sequence `Spec.Progression.packets`
folded with `step`, header bytes from `hs` (packed headers) or the tile data. -/
def decodeTile (L : Limits) (h : Header) (data : ByteArray) (tp : TileParams)
    (hs : Option (List UInt8)) (passesBefore : Nat) : Except Error TileOut := do
  let (g, coding) ← Layout.ofHeader h tp.index
  L.check loc .packets (iterationWork g coding.progression coding.poc)
  let (precs, base, spans) ← initPrecincts L g
  let (buf, _) ← tileData data tp.tile
  let body := buf.data.toList
  let same := hs.isNone
  let hdr := hs.getD body
  let s ← (Spec.Progression.packets g coding.progression coding.poc).foldlM
    (step L coding.sop coding.eph same base passesBefore)
    { precs := precs.toList.map PrecSt.ofFast, hdr, body }
  let comps := spans.toList.map fun si => si.toList.map fun (start, n) =>
    (List.range n).map fun k => (s.precs.getD (start + k) default).out
  return { comps, passes := s.passes, hdrLeft := if same then 0 else s.hdr.length }

/-- The packets of a tile with the given header stream (`decodeTile`), the header stream
required to be consumed exactly (as `Tier2.Headers.decodeWithStream`). -/
def decodeWithStream (L : Limits) (h : Header) (data : ByteArray) (tp : TileParams)
    (hs : Option Tier2.Headers.HeaderStream) (passesBefore : Nat) : Except Error TileOut := do
  let t ← decodeTile L h data tp (hs.map (·.bytes.data.toList)) passesBefore
  if t.hdrLeft != 0 then throw (eSpec "packed packet headers left over")
  return t

end JPEG2000.Spec.Tier2
