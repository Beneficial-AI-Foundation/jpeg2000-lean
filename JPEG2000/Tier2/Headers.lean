import JPEG2000.Tier2.Packet

/-!
# Packed packet headers: sourcing the header stream of a tile
(Plan.md §3 rules 1–3, §5.2 "Tier-2"; T.800 A.7.4, A.7.5, A.4.2, B.9, B.10)

Task 4.5. Without packed packet headers each packet header precedes its body in the tile
data (B.9). With them, the headers of a tile come from a separate **header stream** and the
tile data (after `SOD`) holds only the bodies (with their optional `SOP` markers; an `EPH`
belongs to the header and so lives in the header stream, A.8.2):

* **`PPM`** (A.7.4, main header): the `Ippm` data of all `PPM` segments in `Zppm` order is a
  sequence of chunks `Nppm` (4 bytes) + `Nppm` bytes, **one per tile-part, in the order the
  tile-parts appear in the codestream** (not by tile index: with interleaved tile-parts, as
  in T.803 `p0_10`, chunk `i` belongs to the `i`-th `SOT` of the stream). `Nppm` and a
  chunk may span `PPM` segment boundaries. The split into chunks is task 1.4's
  (`TilePart.parsePointers` → `PPMData.chunks`); here the chunks are assigned to tile-parts
  (`ppmChunkIndex`, by `SOT` position) and a tile's header stream is the concatenation of
  the chunks of its tile-parts in `TPsot` order (= their stream order, A.4.2).
* **`PPT`** (A.7.5, tile-part headers): the tile's header stream is the concatenation of
  its `Ippt` data in `Zppt` order (`TilePart.Tile.ppt`). `Zppt` is unique per tile across its
  tile-parts (task 1.4, as OpenJPEG `opj_j2k_read_ppt`/`opj_j2k_merge_ppt`, which index the
  `PPT`s of a tile by `Zppt` and concatenate them in that order); when the `Zppt` values
  increase with `TPsot` — every encoder we know — this is the concatenation over the
  tile-parts in `TPsot` order.

The header stream is gathered into a fresh `ByteArray` (`HeaderStream.bytes`, the
`Bytes.BitReader` needs contiguous bytes; its size is bounded by the input) together with
the absolute input ranges it came from (`HeaderStream.ranges`). Packet bodies keep their
absolute input ranges (`Packet.decodeTilePacketsWith`). Error offsets inside a packet header
read from a header stream are offsets in `HeaderStream.bytes`.

## Strictness (compared with OpenJPEG 2.5)

OpenJPEG strips the `Nppm` fields, concatenates all `Ippm` data into one buffer and reads
the packet headers of successive tiles from it sequentially (`opj_t2_decode_packets` with
`cp->ppm_data`), so it never matches chunks to tile-parts. We are stricter:

* with `PPM`, the number of chunks must equal the number of tile-parts in the codestream
  (`malformed` otherwise);
* a tile's header stream must be consumed **exactly** by its packets: leftover header bytes
  are `malformed` (OpenJPEG's sequential reading would hand them to the next tile; for
  `PPT` it ignores them). A header stream that runs out is `truncated` (task 4.4).

`PPT` together with `PPM` is already rejected by task 1.4.

## Limits (Plan.md §3)

No new allocation is driven by a declared size: the chunk ranges were checked against the
input by task 1.4 (and are checked again here before copying), the number of tile-parts
against `Limits.maxTileParts`; the per-tile and per-image work limits are 4.4's
(`decodeTilePacketsWith`). All loops are `for` over arrays or `List.mergeSort`.
-/

namespace JPEG2000.Tier2.Headers

open JPEG2000 JPEG2000.Bytes JPEG2000.Header JPEG2000.TilePart JPEG2000.Tier2.Packet

/-- Errors of this module are reported at stage `tier2`. -/
def loc : Location := .at .tier2

/-- A tile's separate packet-header stream (A.7.4–A.7.5). -/
structure HeaderStream where
  /-- Where it came from: `true` for `PPM` (main header), `false` for `PPT`. -/
  fromPpm : Bool
  /-- The absolute input ranges of the header bytes, in stream order (adjacent ranges
  merged). -/
  ranges : Array ByteRange
  /-- The header bytes, concatenated. -/
  bytes : ByteArray

/-- Total number of tile-parts of the codestream. -/
def numTileParts (h : Header) : Nat :=
  h.tiles.foldl (fun a tp => a + tp.tile.parts.size) 0

/-- `idx[j][p]` = stream rank (0-based position among all `SOT`s of the codestream) of
tile-part `p` (`TPsot` order) of `h.tiles[j]`: the index of its `PPM` chunk (A.7.4). Ranks
are computed from the `SOT` positions. -/
def streamRanks (h : Header) : Array (Array Nat) :=
  let all := (h.tiles.toList.zipIdx.flatMap fun (tp, j) =>
      tp.tile.parts.toList.zipIdx.map fun (p, k) => (p.pos, j, k)).mergeSort
    (fun a b => a.1 ≤ b.1)
  let init := h.tiles.map fun tp => Array.replicate tp.tile.parts.size 0
  all.zipIdx.foldl (fun acc ((_, j, k), rank) => acc.modify j (·.setIfInBounds k rank)) init

/-- The `PPM` chunk index of every tile-part (`streamRanks`), after checking that there is
exactly one chunk per tile-part of the codestream (A.7.4). Only meaningful with `PPM`. -/
def ppmChunkIndex (L : Limits) (h : Header) : Except Error (Array (Array Nat)) := do
  let n := numTileParts h
  L.check loc .tileParts n
  if h.ppm.chunks.size != n then
    throw (.malformed loc
      s!"PPM: {h.ppm.chunks.size} Nppm/Ippm chunks for {n} tile-parts")
  return streamRanks h

/-- Gathers byte ranges of the input into a header stream (`truncated` if a range is not
inside the input). -/
def gather (fromPpm : Bool) (data : ByteArray) (rs : Array ByteRange) :
    Except Error HeaderStream := do
  let mut merged : Array ByteRange := #[]
  for r in rs do
    if r.stop > data.size then
      throw (.truncated (.atOffset .tier2 r.offset) "packed packet headers past the end of the input")
    merged := pushRange merged r
  return { fromPpm, ranges := merged, bytes := gatherBytes data merged }

/-- The header stream of tile `tp` given the `PPM` chunk indices of its tile-parts
(`ranks`, from `ppmChunkIndex`; ignored without `PPM`): `none` when the tile has neither
`PPM` nor `PPT` data. -/
def headerStreamAt (h : Header) (data : ByteArray) (tp : TileParams) (ranks : Array Nat) :
    Except Error (Option HeaderStream) := do
  if !h.ppm.segments.isEmpty then
    if !tp.tile.ppt.isEmpty then
      throw (.malformed loc "PPT in a codestream with PPM (A.7.4)")
    let mut rs : Array ByteRange := #[]
    for k in [0:tp.tile.parts.size] do
      let some c := ranks[k]? | throw (.malformed loc "PPM: tile-part without a chunk index")
      let some chunk := h.ppm.chunks[c]? | throw (.malformed loc "PPM: missing Nppm/Ippm chunk")
      rs := rs ++ chunk
    return some (← gather true data rs)
  else if !tp.tile.ppt.isEmpty then
    return some (← gather false data tp.tile.ppt)
  else return none

/-- **The packet-header stream of a tile** (A.7.4–A.7.5): its `PPM` chunks (tile-parts in
`TPsot` order, chunks assigned by stream order) or its `PPT` data (`Zppt` order); `none`
when the headers are in the tile data. With `PPM` the chunk count is checked against the
tile-part count; `tp` must be one of `h.tiles`. -/
def headerStreamOf (L : Limits) (h : Header) (data : ByteArray) (tp : TileParams) :
    Except Error (Option HeaderStream) := do
  if h.ppm.segments.isEmpty then headerStreamAt h data tp #[]
  else
    let idx ← ppmChunkIndex L h
    let some j := h.tiles.findIdx? (·.index == tp.index)
      | throw (.malformed loc s!"tile {tp.index} is not a tile of the codestream")
    headerStreamAt h data tp (idx.getD j #[])

/-- Decodes the packets of a tile with the given header stream (`Packet.decodeTilePacketsWith`)
and checks that the header stream is consumed exactly. -/
def decodeWithStream (L : Limits) (h : Header) (data : ByteArray) (tp : TileParams)
    (hs : Option HeaderStream) (passesBefore : Nat) : Except Error TileCodeBlocks := do
  let t ← decodeTilePacketsWith L h data tp (hs.map (·.bytes)) passesBefore
  if let some s := hs then
    if t.headerStreamConsumed != s.bytes.size then
      throw (.malformed (.atOffset .tier2 t.headerStreamConsumed)
        s!"tile {tp.index}: {s.bytes.size - t.headerStreamConsumed} bytes of packed packet headers left over")
  return t

/-- **Decodes every packet of a tile** (B.9–B.12, A.7.4–A.7.5), its packet headers taken
from the tile data, its `PPM` chunks or its `PPT` data, and returns its per-code-block
segments (ranges absolute in the input). `passesBefore` as in
`Packet.decodeTilePacketsWith`. -/
def decodeTileCodeBlocks (L : Limits) (h : Header) (data : ByteArray) (tp : TileParams)
    (passesBefore : Nat := 0) : Except Error TileCodeBlocks := do
  let hs ← headerStreamOf L h data tp
  decodeWithStream L h data tp hs passesBefore

/-- **Every tile with tile-parts in turn** (`decodeTileCodeBlocks`; the `PPM` chunk
assignment computed once), the coding passes checked over the whole image against
`Limits.maxCodingPasses`. -/
def decodeAllTileCodeBlocks (L : Limits) (h : Header) (data : ByteArray) :
    Except Error (Array TileCodeBlocks) := do
  let idx ← if h.ppm.segments.isEmpty then pure #[] else ppmChunkIndex L h
  let mut out := #[]
  let mut passes := 0
  for j in [0:h.tiles.size] do
    let some tp := h.tiles[j]? | throw (.malformed loc "tile index out of range")
    let hs ← headerStreamAt h data tp (idx.getD j #[])
    let t ← decodeWithStream L h data tp hs passes
    passes := passes + t.passes
    out := out.push t
  return out

end JPEG2000.Tier2.Headers
