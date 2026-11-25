import JPEG2000.Tier2.Headers
import Tests.Packet

/-!
# Tests: packed packet headers (task 4.5)

Plan.md §5.2 "Tier-2", §8; T.800 A.7.4 (`PPM`), A.7.5 (`PPT`), A.4.2, B.9.

1. **Hand-built codestreams**: two 8 × 8 tiles of one component (no decomposition, 2 layers,
   one code-block each), every tile in two tile-parts, **interleaved** in the stream
   (`T0P0, T1P0, T0P1, T1P1`); one packet body per tile-part. Packet headers (hand-traced:
   layer 0 `1 1 1 0 0 len₃`, layer 1 `1 1 0 0 len₃ 0`):
   * `PPM`: four `Nppm`/`Ippm` chunks in stream order, split over three `PPM` segments
     written out of `Zppm` order, with an `Nppm` and an `Ippm` spanning segment boundaries;
     assigning chunks by tile index instead of stream order would swap tile 1's first header
     with tile 0's second;
   * `PPT`: tile 0 one `PPT` per tile-part, tile 1 both headers in its first tile-part as two
     `PPT`s written out of `Zppt` order;
   * expected: each code-block one segment of 2 passes over two non-adjacent ranges (the two
     tile-parts' data) of 2 + 3 resp. 1 + 4 bytes; the header stream's ranges and bytes;
   * errors: one chunk too many (`malformed`), a leftover header byte (`malformed`), a
     chunk one byte short (`truncated`).
2. **Corpus**: all 23 T.803 codestreams and the 9 conformance JP2 files decode through
   `decodeAllTileCodeBlocks` (p1_02/p1_06 `PPT`, p1_05 `PPM` included) with 4.4's
   consistency checks (`Tests.Packet.checkTile`: data and header streams consumed exactly,
   pass counts vs `segmentPasses`, ranges inside the tile-part data); for `PPM`/`PPT`
   streams the result equals 4.4's test-scaffolded decoding (`Tests.Packet.headerStream`)
   and the header stream equals the scaffold's bytes.
-/

namespace JPEG2000.Tests.Tier2Headers

open JPEG2000 JPEG2000.Bytes JPEG2000.Header JPEG2000.TilePart
open JPEG2000.Tier2.Packet JPEG2000.Tier2.Headers

/-- Prints a failure line and returns 1 when `ok` is false. -/
def expect (name : String) (ok : Bool) : IO Nat := do
  if ok then return 0
  IO.eprintln s!"  FAIL tier2headers: {name}"
  return 1

/-- `some e` for an error. -/
def err? {α : Type} : Except Error α → Option Error
  | .error e => some e
  | .ok _ => none

/-! ## 1. Hand-built codestreams -/

/-- Big-endian 16-bit value. -/
def u16 (v : Nat) : List UInt8 := [UInt8.ofNat (v / 256), UInt8.ofNat v]

/-- Big-endian 32-bit value. -/
def u32 (v : Nat) : List UInt8 := u16 (v / 65536) ++ u16 (v % 65536)

/-- A marker segment: marker, `L = 2 + body`, body. -/
def seg (m : Nat) (body : List UInt8) : List UInt8 := u16 m ++ u16 (body.length + 2) ++ body

/-- Main header: `SOC`, `SIZ` (16 × 8 image, 8 × 8 tiles, one 8-bit component), `COD`
(LRCP, 2 layers, no decomposition, 64 × 64 code-blocks, 5/3), `QCD` (no quantisation,
guard bits 2, ε = 8), then `extra` (e.g. `PPM`s). -/
def mainHeader (extra : List UInt8) : List UInt8 :=
  u16 0xFF4F ++
  seg 0xFF51 (u16 0 ++ u32 16 ++ u32 8 ++ u32 0 ++ u32 0 ++ u32 8 ++ u32 8 ++ u32 0 ++ u32 0 ++
    u16 1 ++ [7, 1, 1]) ++
  seg 0xFF52 ([0, 0] ++ u16 2 ++ [0, 0, 4, 4, 0, 1]) ++
  seg 0xFF5C [0x40, 0x40] ++ extra

/-- A tile-part: `SOT` (tile `i`, part `tp` of 2), header segments `hdr`, `SOD`, `body`. -/
def tilePart (i tp : Nat) (hdr body : List UInt8) : List UInt8 :=
  let psot := 12 + hdr.length + 2 + body.length
  u16 0xFF90 ++ u16 10 ++ u16 i ++ u32 psot ++ [UInt8.ofNat tp, 2] ++ hdr ++ u16 0xFF93 ++ body

/-- Packet bodies: tile 0 layers 0/1 (2 and 3 bytes), tile 1 layers 0/1 (1 and 4 bytes). -/
def b00 : List UInt8 := [0x11, 0x12]
/-- See `b00`. -/
def b01 : List UInt8 := [0x13, 0x14, 0x15]
/-- See `b00`. -/
def b10 : List UInt8 := [0x21]
/-- See `b00`. -/
def b11 : List UInt8 := [0x22, 0x23, 0x24, 0x25]

/-- Packet headers (one code-block, `Lblock = 3`): layer 0 `1` non-empty, `1` included
(inclusion tree, threshold 1), `1` zero bit-planes = 0, `0` one pass, `0` no `Lblock`
increment, 3-bit length; layer 1 `1`, `1` included, `0`, `0`, 3-bit length, padding `0`. -/
def h00 : UInt8 := 0xE2  -- 1110 0 010: length 2
/-- See `h00`: `1100 011 0`, length 3. -/
def h01 : UInt8 := 0xC6
/-- See `h00`: `1110 0 001`, length 1. -/
def h10 : UInt8 := 0xE1
/-- See `h00`: `1100 100 0`, length 4. -/
def h11 : UInt8 := 0xC8

/-- The tile-parts in stream order `T0P0, T1P0, T0P1, T1P1` with per-part headers. -/
def parts (p00 p10 p01 p11 : List UInt8) : List UInt8 :=
  tilePart 0 0 p00 b00 ++ tilePart 1 0 p10 b10 ++ tilePart 0 1 p01 b01 ++ tilePart 1 1 p11 b11

/-- A `PPM` codestream: `chunks` (stream order) concatenated, split at `cuts`, written as
`PPM` segments in the order `zorder` (a permutation of the segment indices). -/
def ppmStream (chunks : List (List UInt8)) (cuts : List Nat) (zorder : List Nat) : ByteArray :=
  let all := chunks.flatMap fun c => u32 c.length ++ c
  let bounds := (0 :: cuts) ++ [all.length]
  let pieces := (List.range (bounds.length - 1)).map fun k =>
    (all.drop (bounds.getD k 0)).take (bounds.getD (k + 1) 0 - bounds.getD k 0)
  let ppms := zorder.flatMap fun z => seg 0xFF60 (UInt8.ofNat z :: pieces.getD z [])
  ByteArray.mk (mainHeader ppms ++ parts [] [] [] [] ++ u16 0xFFD9).toArray

/-- The `PPT` codestream (module doc). -/
def pptStream : ByteArray :=
  ByteArray.mk (mainHeader [] ++
    parts (seg 0xFF61 [0, h00]) (seg 0xFF61 [1, h11] ++ seg 0xFF61 [0, h10])
      (seg 0xFF61 [1, h01]) [] ++ u16 0xFFD9).toArray

/-- The good `PPM` chunks in stream order. -/
def goodChunks : List (List UInt8) := [[h00], [h10], [h01], [h11]]

/-- Checks the decoded tiles: tile `i`'s code-block has one segment of 2 passes made of the
two tile-parts' data ranges with the expected lengths and bytes. -/
def checkTiles (name : String) (data : ByteArray) (h : Header) (ts : Array TileCodeBlocks) :
    IO Nat := do
  let mut f := 0
  f := f + (← expect s!"{name}: 2 tiles" (ts.size == 2 && h.tiles.size == 2))
  for (t, i) in ts.toList.zipIdx do
    let some tp := h.tiles[i]? | f := f + (← expect s!"{name}: tile {i}" false)
    let (lens, body) := if i == 0 then ([2, 3], b00 ++ b01) else ([1, 4], b10 ++ b11)
    let blocks := t.blocks
    f := f + (← expect s!"{name} tile {i}: one block" (blocks.length == 1))
    for br in blocks do
      let cb := br.block
      let ranges := cb.segments.toList.flatMap (·.ranges.toList)
      let partRanges := tp.tile.parts.toList.map (·.data)
      f := f + (← expect s!"{name} tile {i}: passes/zbp" (cb.numPasses == 2 && cb.zeroBitPlanes == 0))
      f := f + (← expect s!"{name} tile {i}: one 2-pass segment"
        (cb.segments.toList.map (·.passes) == [2]))
      f := f + (← expect s!"{name} tile {i}: ranges {repr ranges}"
        (ranges.map (·.length) == lens && ranges == partRanges))
      f := f + (← expect s!"{name} tile {i}: bytes"
        ((cb.segments.toList.map (·.bytes data)) == [ByteArray.mk body.toArray]))
    f := f + (← expect s!"{name} tile {i}: streams consumed"
      (t.consumed == t.dataLength && t.headerStreamConsumed == 2 && t.packets == 2))
  return f

/-- The hand-built `PPM` and `PPT` cases. -/
def hand : IO Nat := do
  let mut f := 0
  let L := Limits.default
  -- PPM: 20 bytes of chunk data; cuts at 2 (inside the first Nppm) and 9 (inside the second
  -- chunk's Nppm… `00 00 00 01 E2 | 00 00 00 01 E1`: byte 9 is E1, so the cut puts the second
  -- Ippm alone in the last segment); segments written as Zppm 1, 0, 2.
  let cases : List (String × List Nat × List Nat) :=
    [("ppm one segment", [], [0]), ("ppm spanning", [2, 9], [1, 0, 2]),
     ("ppm many", [1, 3, 4, 5, 8, 13, 19], [7, 6, 5, 4, 3, 2, 1, 0])]
  for (name, cuts, zorder) in cases do
    let data := ppmStream goodChunks cuts zorder
    match parse L data with
    | .error e => f := f + (← expect s!"{name}: parse {e}" false)
    | .ok h =>
      f := f + (← expect s!"{name}: PPM segments" (h.ppm.segments.size == zorder.length))
      match decodeAllTileCodeBlocks L h data with
      | .error e => f := f + (← expect s!"{name}: decode {e}" false)
      | .ok ts => f := f + (← checkTiles name data h ts)
      -- header streams: tile 0 = h00 h01, tile 1 = h10 h11
      for (tp, i) in h.tiles.toList.zipIdx do
        match headerStreamOf L h data tp with
        | .ok (some hs) =>
          let want := if i == 0 then [h00, h01] else [h10, h11]
          f := f + (← expect s!"{name}: stream {i}"
            (hs.fromPpm && hs.bytes == ByteArray.mk want.toArray &&
             gatherBytes data hs.ranges == hs.bytes))
        | _ => f := f + (← expect s!"{name}: stream {i} missing" false)
        f := f + (← expect s!"{name}: decodeTileCodeBlocks {i}"
          ((err? (decodeTileCodeBlocks L h data tp)).isNone))
  -- PPT
  let data := pptStream
  match parse L data with
  | .error e => f := f + (← expect s!"ppt: parse {e}" false)
  | .ok h =>
    match decodeAllTileCodeBlocks L h data with
    | .error e => f := f + (← expect s!"ppt: decode {e}" false)
    | .ok ts => f := f + (← checkTiles "ppt" data h ts)
    for (tp, i) in h.tiles.toList.zipIdx do
      match headerStreamOf L h data tp with
      | .ok (some hs) =>
        let want := if i == 0 then [h00, h01] else [h10, h11]
        f := f + (← expect s!"ppt: stream {i}"
          (!hs.fromPpm && hs.bytes == ByteArray.mk want.toArray))
      | _ => f := f + (← expect s!"ppt: stream {i} missing" false)
  -- errors
  let errCase (name : String) (data : ByteArray) (ok : Error → Bool) : IO Nat := do
    match parse L data with
    | .error e => expect s!"{name}: parse {e}" false
    | .ok h =>
      match decodeAllTileCodeBlocks L h data with
      | .ok _ => expect s!"{name}: accepted" false
      | .error e => expect s!"{name}: wrong error {e}" (ok e)
  let isMal (e : Error) := match e with | .malformed .. => true | _ => false
  let isTrunc (e : Error) := match e with | .truncated .. => true | _ => false
  f := f + (← errCase "ppm extra chunk" (ppmStream (goodChunks ++ [[0]]) [] [0]) isMal)
  f := f + (← errCase "ppm missing chunk" (ppmStream (goodChunks.take 3) [] [0]) isMal)
  f := f + (← errCase "ppm leftover byte" (ppmStream [[h00], [h10], [h01], [h11, 0]] [] [0]) isMal)
  f := f + (← errCase "ppm short chunk" (ppmStream [[h00], [h10], [], [h11]] [] [0]) isTrunc)
  -- interleaving matters: chunks in tile order instead of stream order misdecode
  f := f + (← match parse L (ppmStream [[h00], [h01], [h10], [h11]] [] [0]) with
    | .ok h => do
      let data := ppmStream [[h00], [h01], [h10], [h11]] [] [0]
      match decodeAllTileCodeBlocks L h data with
      | .ok ts => do
        let lens := ts.toList.map fun t => t.blocks.map (·.block.segments.toList.map (·.length))
        expect "tile-ordered chunks differ" (lens != [[[5]], [[5]]])
      | .error _ => pure 0
    | .error e => expect s!"tile-ordered: parse {e}" false)
  IO.println "  tier2headers: hand-built PPM (3 segmentations) / PPT codestreams and 5 error cases"
  return f

/-! ## 2. Corpus -/

/-- What must agree between two decodings of a tile. -/
def summary (t : TileCodeBlocks) :
    List (Nat × Nat × Nat × Nat) × List (Bool × Nat × Nat × Nat × Nat × Array Segment) :=
  ([(t.packets, t.emptyPackets, t.sopPackets, t.headerBytes),
    (t.bodyBytes, t.dataLength, t.consumed, t.headerStreamConsumed), (t.passes, t.tile, 0, 0)],
   t.blocks.map fun b => let cb := b.block
     (cb.included, cb.firstLayer, cb.lblock, cb.zeroBitPlanes, cb.numPasses, cb.segments))

/-- Every corpus file through `decodeAllTileCodeBlocks`. -/
def corpus : IO Nat := do
  let mut f := 0
  let mut seen := 0
  let mut packed := 0
  for file in Tests.Packet.corpusFiles do
    let path := Tests.Packet.corpusDir / file
    if !(← path.pathExists) then continue
    seen := seen + 1
    let data ← IO.FS.readBinFile path
    match parse Limits.default data with
    | .error e => f := f + (← expect s!"{file}: header {e}" false)
    | .ok h =>
      match decodeAllTileCodeBlocks Limits.default h data with
      | .error e => f := f + (← expect s!"{file}: {e}" false)
      | .ok ts =>
        f := f + (← expect s!"{file}: tile count" (ts.size == h.tiles.size))
        let isPacked := !h.ppm.segments.isEmpty || h.tiles.any (!·.tile.ppt.isEmpty)
        if isPacked then packed := packed + 1
        let mut passes := 0
        for (t, tp) in ts.toList.zip h.tiles.toList do
          let hs ← match headerStreamOf Limits.default h data tp with
            | .ok hs => pure (hs.map (·.bytes))
            | .error e => do f := f + (← expect s!"{file} tile {tp.index}: stream {e}" false); pure none
          let scaffold := Tests.Packet.headerStream h data tp
          f := f + (← expect s!"{file} tile {tp.index}: stream = scaffold" (hs == scaffold))
          f := f + (← Tests.Packet.checkTile s!"{file} tile {tp.index}" h tp hs t)
          if isPacked then
            match decodeTilePacketsWith Limits.default h data tp scaffold passes with
            | .error e => f := f + (← expect s!"{file} tile {tp.index}: scaffold {e}" false)
            | .ok s => f := f + (← expect s!"{file} tile {tp.index}: = scaffold"
                (summary s == summary t))
          else
            match decodeTilePackets Limits.default h data tp passes with
            | .error e => f := f + (← expect s!"{file} tile {tp.index}: 4.4 {e}" false)
            | .ok s => f := f + (← expect s!"{file} tile {tp.index}: = 4.4"
                (summary s == summary t))
          passes := passes + t.passes
  if seen == 0 then IO.println "  tier2headers: corpus absent, skipped"
  else IO.println s!"  tier2headers: {seen} corpus files through decodeAllTileCodeBlocks ({packed} with PPM/PPT)"
  return f

/-- Runs the suite; returns the number of failures. -/
def run : IO Nat := do
  let mut f := 0
  f := f + (← hand)
  f := f + (← corpus)
  return f

end JPEG2000.Tests.Tier2Headers
