import JPEG2000.Error
import JPEG2000.Limits
import JPEG2000.Bytes
import JPEG2000.Marker

/-!
# Tile-parts and pointer marker segments (Plan.md §3 rules 1–3, §4 S2/S3; T.800 A.4, A.7)

Task 1.4: the codestream after the main header — tile-parts (`SOT` … `SOD` + bit-stream
data) up to `EOC` — grouped into tiles, and the pointer marker segments `TLM`, `PLT`,
`PPM`, `PPT`.

* **Segment parsers** (`parseSOT`, `parseTLM`, `parsePLT`, `parsePPM`, `parsePPT`) take a
  `Reader` over exactly the segment body, as in `JPEG2000.Marker`, and fail on leftover
  bytes. T.800 A.4.2 (SOT), A.7.1 (TLM), A.7.3 (PLT), A.7.4 (PPM), A.7.5 (PPT). `PPM`/`PPT`
  keep their `Ippm`/`Ippt` bytes as absolute byte ranges of the input (no copy).
* **Tile-part headers** (T.800 A.4, Table A.4): after `SOT`, the segments `COD`, `COC`,
  `QCD`, `QCC`, `RGN`, `POC`, `PPT`, `PLT`, `COM` (parsed with the main-header parsers of
  `JPEG2000.Marker`) until `SOD` (A.4.3); the rest of the tile-part (up to `Psot` bytes
  from the `SOT` marker) is the bit-stream data, kept as an absolute byte range.
* **Driver** `parseTileParts`: reads every tile-part until `EOC` (A.4.4), groups them by
  `Isot`. Fuel = remaining bytes (each tile-part consumes ≥ 12 bytes). The number of tiles
  (B.3: `⌈(Xsiz−XTOsiz)/XTsiz⌉·⌈(Ysiz−YTOsiz)/YTsiz⌉`) is checked against
  `Limits.maxTiles` before the per-tile array is allocated; tile-part counts against
  `maxTileParts` and `maxTilePartsPerTile`; POC entries (main + tile headers) against
  `maxPocEntries`; PLT packet lengths against `maxPackets`.
* `parsePointers`: the main header's raw `TLM` and `PPM` segments (task 1.3 keeps them as
  `RawSegment`s). `TLM`s are returned sorted by `Ztlm`; `PPM`s sorted by `Zppm`, and their
  concatenated data split into the `Nppm`/`Ippm` chunks, one per tile-part in codestream
  order (a chunk, and even its 4-byte `Nppm`, may span segments, as in OpenJPEG's
  `opj_j2k_merge_ppm`). **`PLM` is kept raw** (not parsed): no decoder stage needs it.

Strictness choices (Part 1; OpenJPEG 2.5.3 `opj_j2k_read_sot`/`read_ppt`/`read_ppm`/
`read_tlm`/`read_plt` as tolerance reference; recorded for the ledger):

* Strict like OpenJPEG: `Isot` < number of tiles; `TPsot` of a tile = the number of its
  tile-parts seen so far (A.4.2: tile-parts of a tile appear in `TPsot` order; this also
  rules out duplicates); `TPsot < TNsot` when `TNsot ≠ 0`; `Psot` is 0 or ≥ 14; `Zppm`
  unique (main header), `Zppt` unique per tile (across its tile-parts, as OpenJPEG);
  `PPT` forbidden when the main header has `PPM` (A.7.4); a PLT ending inside a packet
  length is malformed.
* Stricter than OpenJPEG: all nonzero `TNsot` of a tile agree and the tile then has exactly
  that many tile-parts (OpenJPEG tolerates missing ones); `COD`/`COC`/`QCD`/`QCC`/`RGN` only
  in the first tile-part of a tile (Table A.4; OpenJPEG accepts them anywhere); a second
  `COD`/`QCD` in one tile-part header is malformed; `Psot = 12` (OpenJPEG warns) is
  malformed; a tile-part extending past the end of the data is `truncated` (OpenJPEG
  truncates it); a missing `EOC` is `truncated` (OpenJPEG accepts); `Psot = 0` (A.4.2:
  the last tile-part, extending to `EOC`) requires the data to end with `EOC`; `TLM`
  reserved `Stlm` bits, `ST = 3` and a body that is not a whole number of entries are
  malformed (OpenJPEG ignores the TLM); `Ztlm`, `Zplt` (per tile-part header) unique;
  a PLT packet length ≥ 2³² is malformed.
* Lenient: bytes after `EOC` are ignored (as OpenJPEG); unknown marker segments in a
  tile-part header are kept raw; parameterless 0xFF30–0xFF3F are skipped (as task 1.3).
  Not every tile needs a tile-part (only tiles present are returned); TLM entries are not
  cross-checked against the tile-parts, nor the number of PPM chunks against the number of
  tile-parts (task 4.5).
-/

namespace JPEG2000.TilePart

open JPEG2000 JPEG2000.Bytes JPEG2000.Marker

/-! ## Records -/

/-- An absolute byte range `[offset, offset + length)` of the input buffer. -/
structure ByteRange where
  /-- Absolute offset of the first byte. -/
  offset : Nat
  /-- Number of bytes. -/
  length : Nat
  deriving Repr, DecidableEq, Inhabited

/-- One past the last byte of a range. -/
def ByteRange.stop (r : ByteRange) : Nat := r.offset + r.length

/-- The bytes of a range, copied out of the input buffer. -/
def ByteRange.bytes (r : ByteRange) (data : ByteArray) : ByteArray :=
  data.extract r.offset r.stop

/-- Start of tile-part (T.800 A.4.2, Table A.5); `Lsot` is always 10. -/
structure SOT where
  /-- `Isot`: tile index (0…65534). -/
  isot : UInt16
  /-- `Psot`: tile-part length in bytes from the first byte of the `SOT` marker to the end
  of the tile-part's data; 0 = extends to `EOC` (only the last tile-part). -/
  psot : UInt32
  /-- `TPsot`: tile-part index within its tile (0…254). -/
  tpsot : UInt8
  /-- `TNsot`: number of tile-parts of the tile; 0 = not given here. -/
  tnsot : UInt8
  deriving Repr, DecidableEq, Inhabited

/-- One `TLM` entry (T.800 A.7.1, Table A.34). -/
structure TlmEntry where
  /-- `Ttlm`: tile index of the tile-part; `none` when `ST = 0` (tile-parts in tile order,
  one per tile). -/
  tile : Option UInt16
  /-- `Ptlm`: the tile-part's length (its `Psot`). -/
  length : UInt32
  deriving Repr, DecidableEq, Inhabited

/-- Tile-part lengths, main header (T.800 A.7.1). -/
structure TLM where
  /-- `Ztlm`: index of this segment among the `TLM`s. -/
  ztlm : UInt8
  /-- `ST`: size of `Ttlm` in bytes (0, 1 or 2). -/
  st : UInt8
  /-- `SP`: `Ptlm` is 32-bit (else 16-bit). -/
  sp : Bool
  /-- The entries, in stream order. -/
  entries : Array TlmEntry
  deriving Repr, DecidableEq, Inhabited

/-- The `Stlm` byte: `ST` in bits 4–5, `SP` in bit 6. -/
def TLM.stlm (t : TLM) : UInt8 := t.st * 16 + (if t.sp then 64 else 0)

/-- Packet lengths, tile-part header (T.800 A.7.3). -/
structure PLT where
  /-- `Zplt`: index of this segment among the `PLT`s of the tile-part header. -/
  zplt : UInt8
  /-- `Iplt`: the packet lengths, decoded from the 7-bit continuation code. -/
  lengths : Array Nat
  deriving Repr, DecidableEq, Inhabited

/-- Packed packet headers, main header (T.800 A.7.4): `Zppm` and the absolute range of the
rest of the body (`Nppm`/`Ippm` data, split by `parsePointers`). -/
structure PPM where
  /-- `Zppm`: index of this segment among the `PPM`s. -/
  zppm : UInt8
  /-- The body after `Zppm`. -/
  body : ByteRange
  deriving Repr, DecidableEq, Inhabited

/-- Packed packet headers, tile-part header (T.800 A.7.5): `Zppt` and the absolute range of
`Ippt`. -/
structure PPT where
  /-- `Zppt`: index of this segment among the tile's `PPT`s. -/
  zppt : UInt8
  /-- The body after `Zppt` (`Ippt`). -/
  body : ByteRange
  deriving Repr, DecidableEq, Inhabited

/-- The main header's packed packet headers (T.800 A.7.4). -/
structure PPMData where
  /-- The `PPM` segments sorted by `Zppm`. -/
  segments : Array PPM := #[]
  /-- The `Ippm` bytes of each tile-part, in codestream order of the tile-parts, as byte
  ranges (a chunk may span `PPM` segments). -/
  chunks : Array (Array ByteRange) := #[]
  deriving Repr, DecidableEq, Inhabited

/-- One marker segment of a tile-part header (T.800 Table A.4), in stream order. -/
inductive TileSegment where
  /-- Coding style default (first tile-part only). -/
  | cod (c : COD)
  /-- Coding style component (first tile-part only). -/
  | coc (c : COC)
  /-- Quantisation default (first tile-part only). -/
  | qcd (q : QCD)
  /-- Quantisation component (first tile-part only). -/
  | qcc (q : QCC)
  /-- Region of interest (first tile-part only). -/
  | rgn (g : RGN)
  /-- Progression order change. -/
  | poc (p : POC)
  /-- Packed packet headers. -/
  | ppt (p : PPT)
  /-- Packet lengths. -/
  | plt (p : PLT)
  /-- Comment. -/
  | com (c : COM)
  /-- An unknown marker segment, kept raw. -/
  | unknown (s : RawSegment)
  deriving DecidableEq, Inhabited

/-- A parsed tile-part: its `SOT`, header segments and the range of its bit-stream data. -/
structure TilePartHeader where
  /-- The `SOT` fields. -/
  sot : SOT
  /-- Absolute offset of the `SOT` marker. -/
  pos : Nat
  /-- The header segments between `SOT` and `SOD`, in stream order. -/
  segments : Array TileSegment
  /-- Marker index of the header from `SOT` to `SOD` inclusive (as `MainHeader.markers`). -/
  markers : Array MarkerPos
  /-- The bit-stream data after `SOD`, up to the end of the tile-part. -/
  data : ByteRange
  deriving DecidableEq, Inhabited

/-- A tile: its tile-parts and the pointer data gathered from them. -/
structure Tile where
  /-- Tile index (`Isot`). -/
  index : Nat
  /-- The tile-parts, sorted by `TPsot` (= their stream order). -/
  parts : Array TilePartHeader
  /-- `TNsot` as declared by some tile-part (all nonzero values agree), or 0 if none. -/
  tnsot : Nat
  /-- The `Ippt` ranges of all the tile's `PPT`s, sorted by `Zppt`. -/
  ppt : Array ByteRange
  /-- The packet lengths of all the tile's `PLT`s: tile-parts in order, each in `Zplt`
  order. -/
  plt : Array Nat
  deriving DecidableEq, Inhabited

/-! ## Helpers -/

/-- The first value occurring twice in a sorted list, if any. -/
def firstDup : List UInt8 → Option UInt8
  | [] => none
  | a :: rest =>
    match rest with
    | [] => none
    | b :: _ => if a == b then some a else firstDup rest

/-- A reader over an absolute range of `data`; `truncated` if the range is not inside. -/
def rangeReader (data : ByteArray) (rg : ByteRange) : Except Error Reader := do
  let r ← (Reader.ofByteArray data).skip rg.offset
  let (sub, _) ← r.take rg.length
  return sub

/-- `⌈a / b⌉` (0 when `b = 0`). -/
def ceilDiv (a b : Nat) : Nat := (a + b - 1) / b

/-- Number of tile columns (T.800 B.3, equation B-5). -/
def numTilesX (s : SIZ) : Nat := ceilDiv (s.xsiz.toNat - s.xtosiz.toNat) s.xtsiz.toNat

/-- Number of tile rows (T.800 B.3, equation B-5). -/
def numTilesY (s : SIZ) : Nat := ceilDiv (s.ysiz.toNat - s.ytosiz.toNat) s.ytsiz.toNat

/-- Number of tiles (T.800 B.3). -/
def numTiles (s : SIZ) : Nat := numTilesX s * numTilesY s

/-! ## Segment parsers -/

/-- Parses a SOT body (T.800 A.4.2): exactly 8 bytes (`Lsot = 10`); checks
`Isot ≤ 65534`, `Psot = 0 ∨ Psot ≥ 14`, `TPsot ≤ 254`, `TPsot < TNsot` when `TNsot ≠ 0`. -/
def parseSOT (r : Reader) : Except Error SOT := do
  require r (r.remaining = 8) s!"Lsot = {r.remaining + 2}, expected 10"
  let (isot, r1) ← r.u16be
  let (psot, r1) ← r1.u32be
  let (tpsot, r1) ← r1.u8
  let (tnsot, r1) ← r1.u8
  expectEnd r1 "SOT"
  require r (isot ≠ 0xFFFF) "Isot = 65535"
  require r (psot = 0 ∨ psot ≥ 14) s!"Psot = {psot} (0 or ≥ 14)"
  require r (tpsot ≠ 255) "TPsot = 255"
  require r (tnsot = 0 ∨ tpsot < tnsot) s!"TPsot = {tpsot} ≥ TNsot = {tnsot}"
  return { isot, psot, tpsot, tnsot }

/-- Reads one TLM entry with `st` tile-index bytes and a 2- or 4-byte length. -/
def readTlmEntry (st : UInt8) (sp : Bool) (r : Reader) : Except Error (TlmEntry × Reader) := do
  let (tile, r) ← match st with
    | 0 => pure (none, r)
    | 1 => do let (b, r) ← r.u8; pure (some b.toUInt16, r)
    | _ => do let (v, r) ← r.u16be; pure (some v, r)
  if sp then
    let (v, r) ← r.u32be
    return ({ tile, length := v }, r)
  else
    let (v, r) ← r.u16be
    return ({ tile, length := v.toUInt32 }, r)

/-- Parses a TLM body (T.800 A.7.1): `Ztlm`, `Stlm` (reserved bits zero, `ST ≤ 2`), then a
whole number of entries, at most `maxTileParts` (checked before reading). -/
def parseTLM (L : Limits) (r : Reader) : Except Error TLM := do
  let (ztlm, r) ← r.u8
  let r1 := r
  let (stlm, r) ← r.u8
  require r1 (stlm &&& 0x8F = 0) s!"Stlm {hex stlm.toNat}: reserved bits set"
  let st := (stlm >>> 4) &&& 3
  let sp := stlm &&& 0x40 != 0
  require r1 (st ≤ 2) "TLM ST = 3"
  let esz := st.toNat + (if sp then 4 else 2)
  require r (r.remaining % esz = 0) s!"TLM body of {r.remaining} bytes (entries of {esz})"
  let n := r.remaining / esz
  L.check (.atOffset r.stage r.pos) .tileParts n
  let (entries, r) ← readArray (readTlmEntry st sp) (Array.mkEmpty n) n r
  expectEnd r "TLM"
  return { ztlm, st, sp, entries }

/-- Decodes `Iplt` packet lengths (T.800 A.7.3, Table A.37): 7 bits per byte, most
significant first, bit 7 set on every byte but the last of a length. `fuel` is the
remaining byte count; `cur`/`pending` hold a length in progress. -/
def readVarints : Nat → Nat → Bool → Array Nat → Reader → Except Error (Array Nat)
  | 0, _, pending, acc, r =>
    if pending then .error (malformedAt r "PLT ends inside a packet length") else .ok acc
  | fuel + 1, cur, _, acc, r =>
    match r.u8 with
    | .error e => .error e
    | .ok (b, r') =>
      let v := cur * 128 + (b &&& 0x7F).toNat
      if v ≥ 4294967296 then .error (malformedAt r "PLT packet length ≥ 2^32")
      else if b &&& 0x80 != 0 then readVarints fuel v true acc r'
      else readVarints fuel 0 false (acc.push v) r'

/-- Parses a PLT body (T.800 A.7.3): `Zplt`, then packet lengths filling the body. -/
def parsePLT (r : Reader) : Except Error PLT := do
  let (zplt, r) ← r.u8
  let lengths ← readVarints r.remaining 0 false #[] r
  return { zplt, lengths }

/-- Parses a PPM body (T.800 A.7.4): `Zppm` and at least one byte of data. -/
def parsePPM (r : Reader) : Except Error PPM := do
  let (zppm, r1) ← r.u8
  require r (r1.remaining ≥ 1) "PPM without data"
  return { zppm, body := { offset := r1.pos, length := r1.remaining } }

/-- Parses a PPT body (T.800 A.7.5): `Zppt` and at least one byte of `Ippt`. -/
def parsePPT (r : Reader) : Except Error PPT := do
  let (zppt, r1) ← r.u8
  require r (r1.remaining ≥ 1) "PPT without data"
  return { zppt, body := { offset := r1.pos, length := r1.remaining } }

/-! ## Main-header pointer segments -/

/-- Takes the first `n` bytes off a list of non-empty ranges: the taken ranges and the rest
(`none` if fewer than `n` bytes remain). -/
def takeRanges : List ByteRange → Nat → Array ByteRange →
    Option (Array ByteRange × List ByteRange)
  | rs, 0, acc => some (acc, rs)
  | [], _ + 1, _ => none
  | r :: rs, n + 1, acc =>
    if n + 1 < r.length then
      some (acc.push { offset := r.offset, length := n + 1 },
        { offset := r.offset + (n + 1), length := r.length - (n + 1) } :: rs)
    else takeRanges rs (n + 1 - r.length) (acc.push r)

/-- Concatenates the bytes of a few ranges. -/
def gatherBytes (data : ByteArray) (rs : Array ByteRange) : ByteArray :=
  rs.foldl (fun acc rg => acc ++ rg.bytes data) ByteArray.empty

/-- Splits the concatenated PPM data (as ranges) into `Nppm`/`Ippm` chunks, one per
tile-part. `fuel` ≥ the remaining byte count; each chunk consumes ≥ 4 bytes. -/
def ppmChunks (L : Limits) (data : ByteArray) (loc : Location) :
    Nat → List ByteRange → Array (Array ByteRange) → Except Error (Array (Array ByteRange))
  | _, [], acc => .ok acc
  | 0, _ :: _, _ => .error (.malformed loc "PPM: fuel exhausted")
  | fuel + 1, rs@(_ :: _), acc => do
    L.check loc .tileParts (acc.size + 1)
    let some (nb, rs) := takeRanges rs 4 #[] | throw (.malformed loc "PPM: truncated Nppm")
    let (n, _) ← (Reader.ofByteArray (gatherBytes data nb)).u32be
    let some (chunk, rs) := takeRanges rs n.toNat #[]
      | throw (.malformed loc s!"PPM: Ippm of {n} bytes exceeds the PPM data")
    ppmChunks L data loc fuel rs (acc.push chunk)

/-- Sorts by a byte key and fails on a duplicate key. -/
def sortUnique {α : Type} (key : α → UInt8) (loc : Location) (what : String) (xs : Array α) :
    Except Error (Array α) := do
  let s := xs.insertionSort (fun a b => key a < key b)
  match firstDup (s.toList.map key) with
  | some z => throw (.malformed loc s!"duplicate {what} = {z}")
  | none => return s

/-- Parses the main header's `TLM` and `PPM` segments (kept raw by `parseMainHeader`):
`TLM`s sorted by `Ztlm` (unique), and the `PPM` data (segments sorted by `Zppm`, unique;
chunks split as in `opj_j2k_merge_ppm`). `data` is the buffer the main header was parsed
from. `PLM` segments stay raw (`MainHeader.pointers`). -/
def parsePointers (L : Limits) (mh : MainHeader) (data : ByteArray) :
    Except Error (Array TLM × PPMData) := do
  let mut tlms : Array TLM := #[]
  let mut ppms : Array PPM := #[]
  let mut tlmEntries := 0
  for s in mh.pointers do
    let body ← rangeReader data { offset := s.offset, length := s.length }
    if s.code == Code.TLM then
      let t ← parseTLM L body
      tlmEntries := tlmEntries + t.entries.size
      L.check (.atOffset .marker s.offset) .tileParts tlmEntries
      tlms := tlms.push t
    else if s.code == Code.PPM then
      ppms := ppms.push (← parsePPM body)
  let loc : Location := .atOffset .marker mh.endPos
  let tlmSorted ← sortUnique TLM.ztlm loc "Ztlm" tlms
  let ppmSorted ← sortUnique PPM.zppm loc "Zppm" ppms
  let ranges := ppmSorted.toList.map PPM.body
  let total := ranges.foldl (fun a rg => a + rg.length) 0
  let chunks ← ppmChunks L data loc total ranges #[]
  return (tlmSorted, { segments := ppmSorted, chunks })

/-! ## Tile-part headers (T.800 A.4) -/

/-- Tile-part header segments collected so far. -/
structure TPAcc where
  /-- Segments in stream order. -/
  segments : Array TileSegment := #[]
  /-- Marker index. -/
  markers : Array MarkerPos := #[]
  /-- A COD was seen in this header. -/
  cod : Bool := false
  /-- A QCD was seen in this header. -/
  qcd : Bool := false
  /-- POC entries so far over the main header and all tile-part headers. -/
  pocEntries : Nat := 0

/-- Markers that may not appear in a tile-part header (T.800 Table A.4). -/
def forbiddenInTile (m : UInt16) : Bool :=
  m == Code.SOC || m == Code.SIZ || m == Code.SOT || m == Code.EOC || m == Code.SOP ||
    m == Code.EPH || m == Code.TLM || m == Code.PLM || m == Code.PPM || m == Code.CRG ||
    m == Code.CAP

/-- Markers allowed only in the first tile-part of a tile (T.800 Table A.4). -/
def firstPartOnly (m : UInt16) : Bool :=
  m == Code.COD || m == Code.COC || m == Code.QCD || m == Code.QCC || m == Code.RGN

/-- Adds one tile-part header segment. `first`: this is the tile's first tile-part;
`ppm`: the main header has `PPM` (then `PPT` is forbidden, T.800 A.7.4). -/
def addTileSegment (L : Limits) (csiz : Nat) (first ppm : Bool) (acc : TPAcc) (m : UInt16)
    (body : Reader) : Except Error TPAcc := do
  if firstPartOnly m && !first then
    throw (malformedAt body s!"marker {hex m.toNat} in a tile-part other than the first")
  let push (s : TileSegment) : TPAcc := { acc with segments := acc.segments.push s }
  if m == Code.COD then
    require body (!acc.cod) "second COD in a tile-part header"
    let c ← parseCOD L body
    return { push (.cod c) with cod := true }
  else if m == Code.COC then
    return push (.coc (← parseCOC L csiz body))
  else if m == Code.QCD then
    require body (!acc.qcd) "second QCD in a tile-part header"
    let q ← parseQCD body
    return { push (.qcd q) with qcd := true }
  else if m == Code.QCC then
    return push (.qcc (← parseQCC csiz body))
  else if m == Code.RGN then
    return push (.rgn (← parseRGN csiz body))
  else if m == Code.POC then
    let p ← parsePOC L csiz body
    let total := acc.pocEntries + p.entries.size
    L.check (.atOffset body.stage body.pos) .pocEntries total
    return { push (.poc p) with pocEntries := total }
  else if m == Code.PPT then
    require body (!ppm) "PPT in a tile-part header while the main header has PPM"
    return push (.ppt (← parsePPT body))
  else if m == Code.PLT then
    return push (.plt (← parsePLT body))
  else if m == Code.COM then
    return push (.com (← parseCOM body))
  else
    return push (.unknown { code := m, offset := body.pos, length := body.remaining })

/-- The tile-part header loop after `SOT`: reads segments until `SOD` and returns the
reader after `SOD`. `fuel` starts at the remaining byte count; every iteration consumes
≥ 2 bytes. -/
def headerLoop (L : Limits) (csiz : Nat) (first ppm : Bool) :
    Nat → TPAcc → Reader → Except Error (TPAcc × Reader)
  | 0, _, r => .error (r.truncErr "tile-part header: no SOD")
  | fuel + 1, acc, r =>
    match r.u16be with
    | .error _ => .error (r.truncErr "tile-part header: no SOD")
    | .ok (m, r1) =>
      if m == Code.SOD then
        .ok ({ acc with markers := acc.markers.push { code := m, pos := r.pos, len := 2 } }, r1)
      else if m < 0xFF01 then .error (malformedAt r s!"expected a marker, found {hex m.toNat}")
      else if 0xFF30 ≤ m ∧ m ≤ 0xFF3F then
        headerLoop L csiz first ppm fuel
          { acc with markers := acc.markers.push { code := m, pos := r.pos, len := 2 } } r1
      else if forbiddenInTile m then
        .error (malformedAt r s!"marker {hex m.toNat} not allowed in a tile-part header")
      else
        match readSegment r1 with
        | .error e => .error e
        | .ok (body, len, r2) =>
          let acc := { acc with markers := acc.markers.push { code := m, pos := r.pos,
                                                               len := len + 2 } }
          match addTileSegment L csiz first ppm acc m body with
          | .error e => .error e
          | .ok acc => headerLoop L csiz first ppm fuel acc r2

/-! ## Driver -/

/-- Codestream-wide context of the tile-part loop. -/
structure Ctx where
  /-- The limits. -/
  limits : Limits
  /-- `Csiz`. -/
  csiz : Nat
  /-- Number of tiles. -/
  numTiles : Nat
  /-- The main header has `PPM`. -/
  ppm : Bool

/-- Loop state: tile-parts per tile index (size `numTiles`), total tile-parts, POC entries
so far. -/
structure State where
  /-- Tile-parts of each tile, in stream order. -/
  parts : Array (Array TilePartHeader)
  /-- Number of tile-parts read. -/
  total : Nat
  /-- POC entries over the main header and the tile-part headers read so far. -/
  pocEntries : Nat

/-- Whether the reader's data ends with `EOC` (`0xFF 0xD9` as the last two bytes before
`stop`). -/
def endsWithEOC (r : Reader) : Bool :=
  r.stop ≥ 2 && r.data[r.stop - 2]? == some 0xFF && r.data[r.stop - 1]? == some 0xD9

/-- Reads one tile-part whose `SOT` marker is at `r` (already checked), and records it.
Returns the new state and the reader after the tile-part. -/
def readTilePart (c : Ctx) (st : State) (r : Reader) : Except Error (State × Reader) := do
  let start := r.pos
  let (_, r1) ← r.u16be
  let (body, len, r2) ← readSegment r1
  let sot ← parseSOT body
  let i := sot.isot.toNat
  let loc : Location := .atOffset r.stage start
  require r (i < c.numTiles) s!"Isot = {i} ≥ number of tiles {c.numTiles}"
  c.limits.check loc .tileParts (st.total + 1)
  let prev := st.parts[i]?.getD #[]
  c.limits.check loc .tilePartsPerTile (prev.size + 1)
  c.limits.check loc .tilePartsPerTile sot.tnsot.toNat
  require r (sot.tpsot.toNat = prev.size)
    s!"tile {i}: TPsot = {sot.tpsot}, expected {prev.size} (tile-parts in TPsot order)"
  require r (prev.all fun p => p.sot.tnsot = 0 ∨ sot.tnsot = 0 ∨ p.sot.tnsot = sot.tnsot)
    s!"tile {i}: inconsistent TNsot {sot.tnsot}"
  -- The tile-part's extent.
  let stop ← if sot.psot = 0 then
      if endsWithEOC r then pure (r.stop - 2)
      else throw (r.truncErr "Psot = 0 but the codestream does not end with EOC")
    else
      let e := start + sot.psot.toNat
      if e ≤ r.stop then pure e
      else throw (r.truncErr s!"tile-part of Psot = {sot.psot} extends past the end of data")
  let (tp, rNext) ← r2.take (stop - r2.pos)
  let acc : TPAcc := { markers := #[{ code := Code.SOT, pos := start, len := len + 2 }],
                       pocEntries := st.pocEntries }
  let (acc, rData) ← headerLoop c.limits c.csiz (sot.tpsot = 0) c.ppm tp.remaining acc tp
  let part : TilePartHeader :=
    { sot, pos := start, segments := acc.segments, markers := acc.markers,
      data := { offset := rData.pos, length := rData.remaining } }
  return ({ parts := st.parts.modify i (·.push part), total := st.total + 1,
            pocEntries := acc.pocEntries }, rNext)

/-- The tile-part loop: tile-parts until `EOC` (bytes after `EOC` are ignored). `fuel`
starts at the remaining byte count; every tile-part consumes ≥ 12 bytes. -/
def tilePartLoop (c : Ctx) : Nat → State → Reader → Except Error State
  | 0, _, r => .error (r.truncErr "codestream: fuel exhausted before EOC")
  | fuel + 1, st, r =>
    match r.u16be with
    | .error _ => .error (r.truncErr "codestream ends without EOC")
    | .ok (m, _) =>
      if m == Code.EOC then .ok st
      else if m != Code.SOT then
        .error (malformedAt r s!"expected SOT or EOC, found {hex m.toNat}")
      else
        match readTilePart c st r with
        | .error e => .error e
        | .ok (st', r') => tilePartLoop c fuel st' r'

/-- The `PLT` lengths of one tile-part: its `PLT`s sorted by `Zplt` (unique), concatenated. -/
def partPlt (p : TilePartHeader) : Except Error (Array Nat) := do
  let plts := p.segments.filterMap fun | .plt x => some x | _ => none
  let plts ← sortUnique PLT.zplt (.atOffset .marker p.pos) "Zplt" plts
  return plts.foldl (fun acc x => acc ++ x.lengths) #[]

/-- Assembles a tile from its tile-parts: checks the tile-part count against `TNsot`,
merges `PPT` (sorted by `Zppt`, unique) and `PLT` data. -/
def assembleTile (i : Nat) (parts : Array TilePartHeader) : Except Error Tile := do
  let loc : Location := .atOffset .marker ((parts[0]?.map (·.pos)).getD 0)
  let tn := parts.foldl (fun a p => if p.sot.tnsot ≠ 0 then p.sot.tnsot.toNat else a) 0
  if tn ≠ 0 ∧ tn ≠ parts.size then
    throw (.malformed loc s!"tile {i}: {parts.size} tile-parts, TNsot = {tn}")
  let ppts := parts.foldl (fun acc p =>
    acc ++ p.segments.filterMap fun | .ppt x => some x | _ => none) #[]
  let ppts ← sortUnique PPT.zppt loc "Zppt" ppts
  let plt ← parts.foldlM (fun acc p => do return acc ++ (← partPlt p)) #[]
  return { index := i, parts, tnsot := tn, ppt := ppts.map PPT.body, plt }

/-- Assembles the tiles `i, i+1, …` that have tile-parts (structural on the count). -/
def assembleTiles (L : Limits) (parts : Array (Array TilePartHeader)) :
    Nat → Nat → Nat → Array Tile → Except Error (Array Tile)
  | 0, _, _, acc => .ok acc
  | n + 1, i, packets, acc =>
    let ps := parts[i]?.getD #[]
    if ps.isEmpty then assembleTiles L parts n (i + 1) packets acc
    else
      match assembleTile i ps with
      | .error e => .error e
      | .ok t =>
        let packets := packets + t.plt.size
        match L.check (.atOffset .marker ((ps[0]?.map (·.pos)).getD 0)) .packets packets with
        | .error e => .error e
        | .ok () => assembleTiles L parts n (i + 1) packets (acc.push t)

/-- Reads every tile-part from the reader (positioned at the first `SOT`, as returned by
`parseMainHeader`) up to `EOC`, and groups them into tiles sorted by index (only tiles with
at least one tile-part). See the module doc for the checks. -/
def parseTileParts (L : Limits) (mh : MainHeader) (r : Reader) : Except Error (Array Tile) := do
  let n := numTiles mh.siz
  L.check (.atOffset r.stage r.pos) .tiles n
  let c : Ctx := { limits := L, csiz := mh.siz.csiz, numTiles := n,
                   ppm := mh.pointers.any (·.code == Code.PPM) }
  let st0 : State := { parts := Array.replicate n #[], total := 0,
                       pocEntries := mh.poc.foldl (fun a p => a + p.entries.size) 0 }
  let st ← tilePartLoop c r.remaining st0 r
  assembleTiles L st.parts n 0 0 #[]

end JPEG2000.TilePart
