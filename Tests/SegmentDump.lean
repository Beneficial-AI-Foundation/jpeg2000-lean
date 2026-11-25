import JPEG2000.Tier2.Headers
import JPEG2000.Tier1.Modes

/-!
# `segment-dump`: per-code-block segments and coefficients in the OpenJPEG dump format (4.6b)

Plan.md §8 (differential testing against OpenJPEG), milestones M3 and M4; T.800 B.6–B.10
(precincts, code-blocks, packet headers: zero bit-planes, passes, codeword segments), D.4
(codeword segments), Annex D (Tier-1 coefficient values), E-2 (`Mb`).

`lake exe segment-dump <file>` parses a raw codestream or a JP2 file
(`JPEG2000.Header.parse Limits.default`), decodes every tile's packets
(`Tier2.Headers.decodeAllTileCodeBlocks`: per-code-block zero bit-planes, passes and
codeword segments), decodes each code-block with the fast Tier-1
(`Tier1.decodeCodeBlockSegs`) and prints the result in exactly the format of the instrumented
OpenJPEG dump of task 4.6a (`docs/differential.md`, version 1): an `opjdump 1` line, then per
code-block with non-zero area a `cb` line (Tier-2 result) followed by its `coef` line (Tier-1
result). `scripts/diff-segments.py` compares the two dumps record by record, keyed by
`(tile, comp, res, band, prec, cblk)`.

Field mapping (ours → dump):

* `band` = `Band.index` (0 LL, 1 HL, 2 LH, 3 HH); `prec` = `PrecinctOut.index` (raster over
  the resolution's precinct grid); `cblk` = `CodeBlockGeom.index` (raster over the
  precinct-band's code-block grid, empty cells keep their number); `x0 … y1` = the code-block
  rectangle in band coordinates;
* `sty` = the tile-component's `cbStyle`; `Mb` = `Packet.bandMb` (E-2) of the tile-component;
  `zbp` = the tag-tree value `P` (B.10.5); `numbps = Mb − P` modulo 2³² (OpenJPEG prints
  its `OPJ_UINT32`; with ROI `P` may exceed `Mb`, e.g. p0_06 prints `4294967288` for −8);
* `passes`, `segs`, `seglens`, `segpasses`, `seghash`, `hash` from `CodeBlock.segments`
  (each segment's ranges concatenated: `Segment.bytes`); `corrupt` is always 0 (a stream our
  Tier-2 rejects fails the whole dump instead);
* `coef`: the fast Tier-1 run with `numBitPlanes = Mb + roiShift` and `P` zero bit-planes,
  i.e. at the ROI-scaled level before any ROI step, which is what OpenJPEG dumps; `hash` is
  FNV-1a 64 of the plane's cells (row-major little-endian `Int32`, = `Plane.data`).

A Tier-1 error on one code-block prints `coef … nz=- hash=-` and a message on stderr (so the
diff reports it); a parse or Tier-2 error prints `segment-dump: <file>: <error>` on stderr and
exits with 1.
-/

namespace JPEG2000.Tests.SegmentDump

open JPEG2000 JPEG2000.Bytes JPEG2000.Header JPEG2000.Tier2.Geometry JPEG2000.Tier2.Packet

/-- FNV-1a 64 of a byte array, continuing from `h` (docs/differential.md). -/
def fnvFrom (h : UInt64) (bs : ByteArray) : UInt64 :=
  bs.foldl (fun h b => (h ^^^ b.toUInt64) * 0x100000001b3) h

/-- FNV-1a 64 offset basis (the hash of no bytes). -/
def fnvBasis : UInt64 := 0xcbf29ce484222325

/-- FNV-1a 64 of a byte array. -/
def fnv (bs : ByteArray) : UInt64 := fnvFrom fnvBasis bs

/-- 16 lowercase hex digits. -/
def hex16 (v : UInt64) : String :=
  let s := String.ofList (Nat.toDigits 16 v.toNat)
  String.ofList (List.replicate (16 - s.length) '0') ++ s

/-- A comma-separated list, `-` when empty. -/
def commaList (xs : List String) : String :=
  if xs.isEmpty then "-" else ",".intercalate xs

/-- Number of non-zero 4-byte cells of a plane. -/
def nonZero (p : Plane) : Nat := Id.run do
  let mut n := 0
  for i in [0:p.width * p.height] do
    if (p.get? i).getD 0 != 0 then
      n := n + 1
  return n

/-- The `cb` and `coef` lines of one code-block (`none` for a zero-area block). Also
returns a Tier-1 error message, if any. -/
def blockLines (data : ByteArray) (tile : Nat) (p : CompParams) (r : BlockRef) :
    Option (String × String × Option String) :=
  let g := r.block.geom
  let rc := g.rect
  let w := rc.x1 - rc.x0
  let hh := rc.y1 - rc.y0
  if w = 0 ∨ hh = 0 then none else
  let cb := r.block
  let key := s!"tile={tile} comp={r.comp} res={r.res} band={r.band.band.index} " ++
    s!"prec={r.prec} cblk={g.index}"
  let mb := bandMb p r.res r.band.band
  let segBytes := cb.segments.map (·.bytes data)
  let all := segBytes.foldl (· ++ ·) ByteArray.empty
  let (nb, zb) := if cb.included then
      -- OpenJPEG's `cblk->numbps` is an `OPJ_UINT32` printed with `%u`: with ROI the zero
      -- bit-planes may exceed `Mb` (p0_06: `P = Mb + 8`) and the value wraps mod 2^32.
      (toString (((mb : Int) - (cb.zeroBitPlanes : Int)) % 4294967296), toString cb.zeroBitPlanes)
    else ("-", "-")
  let cbLine := s!"cb {key} x0={rc.x0} y0={rc.y0} x1={rc.x1} y1={rc.y1} " ++
    s!"sty={p.cbStyle.toNat} Mb={mb} numbps={nb} zbp={zb} passes={cb.numPasses} " ++
    s!"segs={cb.segments.size} len={all.size} corrupt=0 " ++
    s!"seglens={commaList (segBytes.toList.map (toString ·.size))} " ++
    s!"segpasses={commaList (cb.segments.toList.map (toString ·.passes))} " ++
    s!"seghash={commaList (segBytes.toList.map (hex16 ∘ fnv))} hash={hex16 (fnv all)}"
  -- Tier-1 on the concatenated segment bytes.
  let (segs, _) := segBytes.foldl (fun (acc : Array Tier1.Seg × Nat) (bs : ByteArray) =>
      let (a, off) := acc
      (a.push { start := off, stop := off + bs.size, passes := 0 }, off + bs.size)) (#[], 0)
  let segs := (segs.zip cb.segments).map fun (s, sg) => { s with passes := sg.passes }
  let zbp := if cb.included then cb.zeroBitPlanes else 0
  let coefHead := s!"coef {key} w={w} h={hh} roi={p.roiShift}"
  match Tier1.decodeCodeBlockSegs all segs w hh r.band.band p.cbStyle (mb + p.roiShift) zbp with
  | .ok o =>
    some (cbLine, s!"{coefHead} nz={nonZero o.plane} hash={hex16 (fnv o.plane.data)}", none)
  | .error e => some (cbLine, s!"{coefHead} nz=- hash=-", some s!"{key}: {e}")

/-- `segment-dump <file>`: prints the dump; exit 1 on a parse/Tier-2 error (or any Tier-1
error), 2 on bad usage. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
    let data ← IO.FS.readBinFile path
    let res := do
      let h ← JPEG2000.Header.parse Limits.default data
      let ts ← Tier2.Headers.decodeAllTileCodeBlocks Limits.default h data
      return (h, ts)
    match res with
    | .error e =>
      IO.eprintln s!"segment-dump: {path}: {e}"
      return 1
    | .ok (h, ts) =>
      let out ← IO.getStdout
      out.putStrLn "opjdump 1"
      let mut failed := false
      for t in ts do
        match Progression.Layout.ofHeader h t.tile with
        | .error e =>
          IO.eprintln s!"segment-dump: {path}: tile {t.tile}: {e}"
          return 1
        | .ok (g, _) =>
          for r in t.blocks do
            match blockLines data t.tile (g.comp r.comp).params r with
            | none => pure ()
            | some (a, b, err) =>
              out.putStrLn a
              out.putStrLn b
              if let some m := err then
                IO.eprintln s!"segment-dump: {path}: Tier-1 error at {m}"
                failed := true
      return (if failed then 1 else 0)
  | _ =>
    IO.eprintln "usage: segment-dump <file.j2k|file.jp2>"
    return 2

end JPEG2000.Tests.SegmentDump

/-- Entry point of `lake exe segment-dump`. -/
def main (args : List String) : IO UInt32 := JPEG2000.Tests.SegmentDump.main args
