import Spec.Tier2
import Tests.Packet

/-!
# Tests: the Tier-2 specification against the fast packet decoder (task 7.1b)

Plan.md §5.1, §5.2 "Tier-2", §8; T.800 B.9–B.12.

1. **Un-stuffing** (`Spec.Tier2.unstuff`, `alignedLength`) on hand-computed byte strings.
2. **Corpus**: every tile of the 23 T.803 codestreams and the 9 conformance JP2 files: the
   spec `Spec.Tier2.decodeWithStream` and the fast `Tier2.Headers.decodeWithStream` both
   succeed and agree (`agree`: per code-block geometry, inclusion, `Lblock`, zero
   bit-planes, passes and every segment's bytes = the bytes of the fast ranges; equal pass
   totals).
3. **Mutated corpus**: the same with one byte of a tile's data (or header stream) replaced
   by a pseudo-random value at a pseudo-random position: both fail, or both succeed and
   agree.
-/

namespace JPEG2000.Tests.Tier2Spec

open JPEG2000 JPEG2000.Bytes JPEG2000.Header JPEG2000.TilePart
open JPEG2000.Tier2.Packet JPEG2000.Tier2.Headers

/-- Prints a failure line and returns 1 when `ok` is false. -/
def expect (name : String) (ok : Bool) : IO Nat := do
  if ok then return 0
  IO.eprintln s!"  FAIL tier2spec: {name}"
  return 1

/-- A fast code-block and a spec code-block agree. -/
def blockAgree (data : ByteArray) (cb : CodeBlock) (sb : Spec.Tier2.BlockSt) : Bool :=
  cb.geom == sb.geom && cb.included == sb.included && cb.lblock == sb.lblock &&
    cb.zeroBitPlanes == sb.zbp && cb.numPasses == sb.passes &&
    cb.segments.toList.map (fun s => ((s.bytes data).data.toList, s.passes)) ==
      sb.segs.map (fun s => (s.data, s.passes))

/-- Lists of equal length agreeing pointwise. -/
def allAgree {α β : Type} (f : α → β → Bool) : List α → List β → Bool
  | [], [] => true
  | a :: as, b :: bs => f a b && allAgree f as bs
  | _, _ => false

/-- A fast tile result and a spec tile result agree. -/
def agree (data : ByteArray) (t : TileCodeBlocks) (s : Spec.Tier2.TileOut) : Bool :=
  t.passes == s.passes &&
  allAgree (allAgree (allAgree (fun (p : PrecinctOut) (q : List Spec.Tier2.BandOut) =>
      allAgree (fun (b : BandOut) (c : Spec.Tier2.BandOut) =>
        b.band == c.band && b.rect == c.rect && b.maxZero == c.maxZero &&
          allAgree (blockAgree data) b.blocks.toList c.blocks) p.bands.toList q)))
    (t.comps.toList.map fun rs => rs.toList.map (·.toList)) s.comps

/-! ## 1. Un-stuffing -/

/-- Hand-computed cases. -/
def unstuffCases : IO Nat := do
  let mut f := 0
  -- 0xA5 = 10100101; 0xFF then 0x7F: 7 bits 1111111
  f := f + (← expect "unstuff A5" (Spec.Tier2.unstuff [0xA5] ==
    [true, false, true, false, false, true, false, true]))
  f := f + (← expect "unstuff FF 7F" (Spec.Tier2.unstuff [0xFF, 0x7F] ==
    List.replicate 8 true ++ List.replicate 7 true))
  f := f + (← expect "unstuff FF FF 01" ((Spec.Tier2.unstuff [0xFF, 0xFF, 0x01]).length == 8 + 7 + 7))
  -- 3 bits of [0x12, ..] → 1 byte; 8 bits of [0xFF, 0x00] → 2 bytes; 9 bits of [0xFF, 0x00] → 2
  f := f + (← expect "align 3" (Spec.Tier2.alignedLength false [0x12, 0x34] 3 == some 1))
  f := f + (← expect "align 8 FF" (Spec.Tier2.alignedLength false [0xFF, 0x00] 8 == some 2))
  f := f + (← expect "align 8 FF end" (Spec.Tier2.alignedLength false [0xFF] 8 == none))
  f := f + (← expect "align 9 FF" (Spec.Tier2.alignedLength false [0xFF, 0x00, 0x11] 9 == some 2))
  f := f + (← expect "align 16" (Spec.Tier2.alignedLength false [0x01, 0x02, 0x03] 16 == some 2))
  f := f + (← expect "align 17" (Spec.Tier2.alignedLength false [0x01, 0x02, 0x03] 17 == some 3))
  -- fast bit reader on the same bytes
  let bytes : List UInt8 := [0xFF, 0x7F, 0x80, 0xFF, 0x00, 0x13]
  let ba := ByteArray.mk bytes.toArray
  let rec readN : Nat → BitReader → List Bool → Option (List Bool)
    | 0, _, acc => some acc.reverse
    | n + 1, br, acc => match JPEG2000.TagTree.bitNext br with
      | .ok (b, br) => readN n br (b :: acc)
      | .error _ => if acc.length == (Spec.Tier2.unstuff bytes).length then some acc.reverse else none
  f := f + (← expect "bit reader = unstuff"
    (readN 100 (BitReader.ofReader (Reader.ofByteArray ba)) [] == some (Spec.Tier2.unstuff bytes)))
  return f

/-! ## 2–3. Corpus, mutated corpus -/

/-- Compares fast and spec on one tile; `expectOk` requires success. -/
def compareTile (name : String) (h : Header) (data : ByteArray) (tp : TileParams)
    (hs : Option HeaderStream) (passes : Nat) (expectOk : Bool) : IO (Nat × Bool) := do
  let fast := decodeWithStream Limits.default h data tp hs passes
  let spec := Spec.Tier2.decodeWithStream Limits.default h data tp hs passes
  match fast, spec with
  | .ok t, .ok s => return (← expect s!"{name}: agree" (agree data t s), true)
  | .error _, .error _ => return (← expect s!"{name}: fails" (!expectOk), false)
  | .ok _, .error e => return (← expect s!"{name}: spec fails {e}" false, false)
  | .error e, .ok _ => return (← expect s!"{name}: fast fails {e}" false, false)

/-- A small linear congruential generator. -/
def lcg (s : Nat) : Nat := (s * 1103515245 + 12345) % 2147483648

/-- One byte of `data` replaced. -/
def mutate (data : ByteArray) (pos : Nat) (v : UInt8) : ByteArray :=
  if pos < data.size then data.set! pos v else data

/-- The spec re-un-stuffs the remaining tile data for every packet header (it is literal, not
fast): tiles with more data than this are skipped. -/
def maxTileBytes : Nat := 16384

/-- Bytes of a tile's data (all tile-parts). -/
def tileBytes (tp : TileParams) : Nat := tp.tile.parts.foldl (fun a p => a + p.data.length) 0

/-- The given corpus files (tiles of at most `maxTileBytes`), unmutated and mutated. -/
def corpusOn (files : List String) : IO Nat := do
  let mut f := 0
  let mut seen := 0
  let mut tiles := 0
  let mut mutOk := 0
  let mut mutAll := 0
  let mut seed := 7
  let mut skipped := 0
  for file in files do
    let path := Tests.Packet.corpusDir / file
    if !(← path.pathExists) then continue
    seen := seen + 1
    let data ← IO.FS.readBinFile path
    match parse Limits.default data with
    | .error e => f := f + (← expect s!"{file}: header {e}" false)
    | .ok h =>
      let mut passes := 0
      let mut k := 0
      for tp in h.tiles do
        let hs := match headerStreamOf Limits.default h data tp with
          | .ok hs => hs
          | .error _ => none
        if tileBytes tp > maxTileBytes then
          skipped := skipped + 1
          if let .ok t := decodeWithStream Limits.default h data tp hs passes then
            passes := passes + t.passes
          continue
        let (g, _) ← compareTile s!"{file} tile {tp.index}" h data tp hs passes true
        f := f + g
        tiles := tiles + 1
        if let .ok t := decodeWithStream Limits.default h data tp hs passes then
          passes := passes + t.passes
        -- mutations: only the first tiles of each file (speed)
        if k < 2 then
          for _ in [0:6] do
            seed := lcg seed
            let part := tp.tile.parts.getD (seed % max 1 tp.tile.parts.size) default
            seed := lcg seed
            -- a position in the first 64 bytes of the tile-part data (packet headers live there)
            let pos := part.data.offset + seed % (max 1 (min 64 part.data.length))
            seed := lcg seed
            let v := UInt8.ofNat (if seed % 4 == 0 then 0xFF else seed / 7 % 256)
            let data' := mutate data pos v
            let (g, ok) ← compareTile s!"{file} tile {tp.index} mut@{pos}={v}" h data' tp hs 0 false
            f := f + g
            mutAll := mutAll + 1
            if ok then mutOk := mutOk + 1
          if let some s := hs then
            seed := lcg seed
            let pos := seed % (max 1 s.bytes.size)
            seed := lcg seed
            let v := UInt8.ofNat (seed / 7 % 256)
            let s' := { s with bytes := mutate s.bytes pos v }
            let (g, ok) ← compareTile s!"{file} tile {tp.index} hdr mut@{pos}" h data tp (some s') 0 false
            f := f + g
            mutAll := mutAll + 1
            if ok then mutOk := mutOk + 1
        k := k + 1
  if seen == 0 then IO.println "  tier2spec: corpus absent, skipped"
  else IO.println s!"  tier2spec: {seen} corpus files, {tiles} tiles spec = fast ({skipped} tiles > {maxTileBytes} bytes skipped); {mutAll} mutated tiles agree ({mutOk} decode)"
  return f

/-- Every corpus file. -/
def corpus : IO Nat := corpusOn Tests.Packet.corpusFiles

/-- Runs the suite; returns the number of failures. -/
def run : IO Nat := do
  let mut f := 0
  f := f + (← unstuffCases)
  f := f + (← corpus)
  return f

end JPEG2000.Tests.Tier2Spec
