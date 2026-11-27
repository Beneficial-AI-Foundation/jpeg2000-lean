import JPEG2000.Header
import Std.Data.HashMap

/-!
# `header-dump`: the merged header in `opj_dump -i` form (task 1.7)

Plan.md §8 (differential testing against OpenJPEG), §4 S2; T.800 A.5.1 (SIZ), A.6.1–A.6.5
(COD/COC/QCD/QCC/RGN, as merged by `JPEG2000.Header`), A.7.1 (TLM), Annex I (JP2: the
codestream offset).

`lake exe header-dump <file>` parses a raw codestream or a JP2 file with
`JPEG2000.Header.parse Limits.default` and prints the fields that OpenJPEG 2.5.3's
`opj_dump -i` prints and that our header models, in the same text format and order, so that
`scripts/diff-headers.py` can compare the two with a plain normalised text diff:

* the two `[INFO]` lines (`Start to read j2k main header (N)`: the codestream offset);
* `Image info` (SIZ: `x0, y0, x1, y1`, `numcomps`, per component `dx, dy, prec, sgnd`);
* `Codestream info from main header` (`tx0, ty0, tdx, tdy, tw, th`) and its `default tile`
  — our `Header.defaults` (main COD/QCD with the main COC/QCC/RGN applied, which is what
  OpenJPEG's default tile holds). Hex fields (`csty`, `prg`, `cblksty`) use C's `%#x`
  (`0` for zero, `0x…` otherwise). Step sizes: one `(m,e)` pair for derived quantisation
  (`qntsty=1`, the signalled base value), `3·numresolutions − 2` pairs otherwise;
* `Codestream index from main header`: start (codestream offset) and end (first `SOT`) of the
  main header, and the marker list with `len = Lxxx + 2`. OpenJPEG does not index the
  parameterless markers `0xFF30–0xFF3F`, so they are left out here too;
* `Tile index`: the `TLM` segments declare the tile-part counts and lengths. Offsets start
  at the end of the main header. A matching physical tile-part supplies its `SOD` data
  offset for `end_header`. OpenJPEG 2.5.3 prints zero there and the differential masks it.

On a parse error it prints `header-dump: <file>: <error>` to stderr and exits with 1.
-/

namespace JPEG2000.Tests.HeaderDump

open JPEG2000 JPEG2000.Marker JPEG2000.TilePart JPEG2000.Header

/-- C's `%#x`: `0` for zero, otherwise `0x` and lowercase hex digits. -/
def hexC (n : Nat) : String :=
  if n = 0 then "0" else "0x" ++ String.ofList (Nat.toDigits 16 n)

/-- The lines of one component of the default tile (OpenJPEG `opj_j2k_dump_tile_info`). -/
def compLines (i : Nat) (p : CompParams) : List String :=
  let numres := p.levels + 1
  let prec := String.join ((List.range numres).map fun r =>
    let pp := p.precincts.getD r Precinct.default
    s!"({pp.ppx},{pp.ppy}) ")
  let nSteps := if p.quantStyle = 1 then 1 else 3 * numres - 2
  let steps := String.join ((p.steps.toList.take nSteps).map fun s =>
    s!"({s.mantissa},{s.exponent}) ")
  [ s!"\t\t comp {i} \{",
    s!"\t\t\t csty={hexC (if p.precinctsDefined then 1 else 0)}",
    s!"\t\t\t numresolutions={numres}",
    s!"\t\t\t cblkw=2^{p.cbWidthExp}",
    s!"\t\t\t cblkh=2^{p.cbHeightExp}",
    s!"\t\t\t cblksty={hexC p.cbStyle.toNat}",
    s!"\t\t\t qmfbid={p.transform.toUInt8}",
    s!"\t\t\t preccintsize (w,h)={prec}",
    s!"\t\t\t qntsty={p.quantStyle}",
    s!"\t\t\t numgbits={p.guardBits}",
    s!"\t\t\t stepsizes (m,e)={steps}",
    s!"\t\t\t roishift={p.roiShift}",
    "\t\t }" ]

/-- Whether OpenJPEG lists a marker in its index (not the parameterless `0xFF30–0xFF3F`). -/
def indexed (m : MarkerPos) : Bool := !(0xFF30 ≤ m.code && m.code ≤ 0xFF3F)

/-- The tile index declared by TLM (A.7.1). A table must cover every tile. -/
def tileIndexLines (h : Header) : List String := Id.run do
  if h.tlm.isEmpty then return []
  let mut parts : Array (Array (Nat × Nat)) := Array.replicate (numTiles h.siz) #[]
  let mut start := h.main.endPos
  let mut ordinal := 0
  for segment in h.tlm do
    for entry in segment.entries do
      let tile := (entry.tile.map UInt16.toNat).getD ordinal
      if tile ≥ parts.size then return []
      let stop := start + entry.length.toNat
      parts := parts.modify tile (·.push (start, stop))
      start := stop
      ordinal := ordinal + 1
  if parts.any Array.isEmpty then return []
  let mut sod : Std.HashMap (Nat × Nat) Nat := ∅
  for tile in h.tiles do
    for part in tile.tile.parts do
      sod := sod.insert (tile.index, part.pos) part.data.offset
  let tiles := parts.toList.zipIdx.flatMap fun (ranges, tile) =>
    s!"\t\t nb of tile-part in tile [{tile}]={ranges.size}" ::
      (ranges.toList.zipIdx.map fun ((start, stop), i) =>
        let headerEnd := sod.getD (tile, start) 0
        s!"\t\t\t tile-part[{i}]: star_pos={start}, end_header={headerEnd}, end_pos={stop}.")
  return ["\t Tile index: {"] ++ tiles ++ ["\t }"]

/-- The whole dump, line by line. -/
def dumpLines (h : Header) : List String :=
  let s := h.siz
  let d := h.defaults
  let start := h.codestream.start
  let comps := (s.components.toList.zipIdx).flatMap fun (c, i) =>
    [ s!"\t\t component {i} \{",
      s!"\t\t dx={c.dx}, dy={c.dy}",
      s!"\t\t prec={c.depth}",
      s!"\t\t sgnd={if c.signed then 1 else 0}",
      "\t}" ]
  let csty := (if h.main.cod.style.precincts.isSome then 1 else 0) +
    (if d.sop then 2 else 0) + (if d.eph then 4 else 0)
  [ s!"[INFO] Start to read j2k main header ({start}).",
    "[INFO] Main header has been correctly decoded.",
    "Image info {",
    s!"\t x0={s.xosiz}, y0={s.yosiz}",
    s!"\t x1={s.xsiz}, y1={s.ysiz}",
    s!"\t numcomps={s.csiz}" ] ++ comps ++
  [ "}",
    "Codestream info from main header: {",
    s!"\t tx0={s.xtosiz}, ty0={s.ytosiz}",
    s!"\t tdx={s.xtsiz}, tdy={s.ytsiz}",
    s!"\t tw={h.numTilesX}, th={h.numTilesY}",
    "\t default tile {",
    s!"\t\t csty={hexC csty}",
    s!"\t\t prg={hexC d.progression.toUInt8.toNat}",
    s!"\t\t numlayers={d.layers}",
    s!"\t\t mct={if d.mct then 1 else 0}" ] ++
  ((d.comps.toList.zipIdx).flatMap fun (p, i) => compLines i p) ++
  [ "\t }",
    "}",
    "Codestream index from main header: {",
    s!"\t Main header start position={start}",
    s!"\t Main header end position={h.main.endPos}",
    "\t Marker list: {" ] ++
  ((h.main.markers.toList.filter indexed).map fun m =>
    s!"\t\t type={hexC m.code.toNat}, pos={m.pos}, len={m.len}") ++
  [ "\t }" ] ++ tileIndexLines h ++ [ "}" ]

/-- `header-dump <file>`: prints the dump; exit 1 on a parse error, 2 on bad usage. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
    let data ← IO.FS.readBinFile path
    match JPEG2000.Header.parse Limits.default data with
    | .ok h =>
      for l in dumpLines h do IO.println l
      return 0
    | .error e =>
      IO.eprintln s!"header-dump: {path}: {e}"
      return 1
  | _ =>
    IO.eprintln "usage: header-dump <file.j2k|file.jp2>"
    return 2

end JPEG2000.Tests.HeaderDump

/-- Entry point of `lake exe header-dump`. -/
def main (args : List String) : IO UInt32 := JPEG2000.Tests.HeaderDump.main args
