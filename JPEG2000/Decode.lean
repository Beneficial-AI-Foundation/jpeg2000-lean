import JPEG2000.Assemble

/-!
# `JPEG2000.decodeCodestream`: bytes → component planes
(Plan.md §3 (pipeline), §6 item 7 (reduced resolution); T.800 B.2, B.3, B-12, B-14, Annex I
(container only))

Task 5.5. `decodeCodestream L data reduce` parses a raw codestream or a JP2 file
(`Header.parse`), then for every tile of the tile grid in index order decodes its packets
(Tier-2, with the `PPM` chunk assignment computed once and the coding passes counted over the
whole image against `Limits.maxCodingPasses`, as `Tier2.Headers.decodeAllTileCodeBlocks`),
reconstructs it (`Assemble.decodeTile`; tiles without tile-parts decode as zero
coefficients, i.e. the DC offset) and copies each tile-component into its component plane.

## Output

One `DecodedComponent` per codestream component, **on the component's own sample grid**
(no up-sampling: display composition, palette, channel definitions and colour are task
6.2's): the component image covers `[⌈XOsiz/XRsiz⌉, ⌈Xsiz/XRsiz⌉) ×
[⌈YOsiz/YRsiz⌉, ⌈Ysiz/YRsiz⌉)` (B-12 applied to the image area), and with `reduce = k` every
coordinate further `⌈· / 2^k⌉` (B-14), as OpenJPEG's `-r k`. Samples are `Int32` cells,
already DC-shifted and clamped to the component's range (G.1).

## Limits

The output planes are checked together against `maxWorkSamples` and (at the output sample
width of `Header.bytesPerSample`) `maxDecodedBytes` before they are allocated; `reduce` is
bounded by `maxDecompLevels` before any `2^reduce` is formed. Per-tile limits are
`Assemble`'s.
-/

namespace JPEG2000

open JPEG2000.Bytes JPEG2000.Marker JPEG2000.Header JPEG2000.TilePart

/-- One decoded component, on its own sample grid. -/
structure DecodedComponent where
  /-- Left edge of the component image on the component grid (`⌈XOsiz / XRsiz⌉`, reduced). -/
  x0 : Nat
  /-- Top edge of the component image on the component grid (`⌈YOsiz / YRsiz⌉`, reduced). -/
  y0 : Nat
  /-- Width in samples. -/
  width : Nat
  /-- Height in samples. -/
  height : Nat
  /-- Bit depth (1…38; > 31 unsigned / > 32 signed is `unsupported` by the decoder). -/
  depth : Nat
  /-- Samples are signed. -/
  signed : Bool
  /-- Horizontal sub-sampling `XRsiz`. -/
  dx : Nat
  /-- Vertical sub-sampling `YRsiz`. -/
  dy : Nat
  /-- The samples, `width × height`, row-major. -/
  plane : Plane

instance : Inhabited DecodedComponent :=
  ⟨{ x0 := 0, y0 := 0, width := 0, height := 0, depth := 0, signed := false, dx := 1, dy := 1,
     plane := Plane.zero 0 0 }⟩

/-- A decoded codestream: its header (with the JP2 container, for task 6.2's colour
handling), the resolution reduction used, and one plane per component. -/
structure DecodedImage where
  /-- The parsed header. -/
  header : Header
  /-- Number of discarded finest resolution levels. -/
  reduce : Nat
  /-- One entry per codestream component. -/
  comps : Array DecodedComponent
  /-- Code-blocks whose dequantised values saturated to `Int32` (0 for valid streams). -/
  saturatedBlocks : Nat

namespace Decode

/-- The error location of the entry point. -/
def loc : Location := .at .decode

/-- The rectangle of component `c` on its own grid at reduction `reduce`. -/
def compImageRect (s : SIZ) (c : Component) (reduce : Nat) : Rect :=
  Assemble.reduceRect (compRect (imageRect s) c) reduce

/-- The output components with empty planes, and their zero planes allocated separately
(kept apart so that they stay uniquely referenced while tiles are copied in), after checking
them against `Limits`. -/
def allocOutput (L : Limits) (s : SIZ) (reduce : Nat) :
    Except Error (Array DecodedComponent × Array Plane) := do
  let rects := s.components.map fun c => (c, compImageRect s c reduce)
  let cells := rects.foldl (fun a (_, r) => a + r.width * r.height) 0
  L.check loc .workSamples cells
  let bytes := rects.foldl (fun a (c, r) => a + r.width * r.height * bytesPerSample c.depth.toNat) 0
  L.check loc .decodedBytes bytes
  let info := rects.map fun (c, r) =>
    { x0 := r.x0, y0 := r.y0, width := r.width, height := r.height, depth := c.depth.toNat,
      signed := c.signed, dx := c.dx.toNat, dy := c.dy.toNat, plane := Plane.zero 0 0 }
  return (info, rects.map fun (_, r) => Plane.zero r.width r.height)

/-- Copies a reconstructed tile into the component planes (in place; `info` gives each
component's origin). -/
def place (info : Array DecodedComponent) (planes : Array Plane) (t : Assemble.TileOut) :
    Except Error (Array Plane) := do
  let mut planes := planes
  for c in [0:t.comps.size] do
    let some (r, pl) := t.comps[c]? | throw (.malformed loc "tile component out of range")
    let some dc := info[c]? | throw (.malformed loc "component out of range")
    if r.x0 < dc.x0 ∨ r.y0 < dc.y0 then
      throw (.malformed loc s!"tile {t.tile} component {c} starts before the image")
    let dst := planes.getD c (Plane.zero 0 0)
    planes := planes.setIfInBounds c (Plane.zero 0 0)
    let dst ← Assemble.blit dst pl (r.x0 - dc.x0) (r.y0 - dc.y0)
    planes := planes.setIfInBounds c dst
  return planes

end Decode

open Decode in
/-- **Decodes a JPEG 2000 codestream** (raw `.j2k`/`.j2c` or a JP2 file) into one plane per
component on the component's own grid, discarding the `reduce` finest resolution levels
(Plan.md §6 item 7; `reduce` must not exceed any tile-component's `NL`). Every stage's
error propagates. -/
def decodeCodestream (L : Limits) (data : ByteArray) (reduce : Nat := 0) :
    Except Error DecodedImage := do
  L.check loc .decompLevels reduce
  let h ← Header.parse L data
  let s := h.siz
  let (info, planes0) ← allocOutput L s reduce
  let mut planes := planes0
  let idx ← if h.ppm.segments.isEmpty then pure #[] else Tier2.Headers.ppmChunkIndex L h
  let mut passes := 0
  let mut sat := 0
  let mut j := 0
  for t in [0:numTiles s] do
    let present := match h.tiles[j]? with
      | some tp => if tp.index = t then some tp else none
      | none => none
    let tcb ← match present with
      | some tp => do
        let hs ← Tier2.Headers.headerStreamAt h data tp (idx.getD j #[])
        let x ← Tier2.Headers.decodeWithStream L h data tp hs passes
        pure (some x)
      | none => pure none
    if present.isSome then j := j + 1
    if let some x := tcb then passes := passes + x.passes
    let out ← Assemble.decodeTile L h data t reduce tcb
    sat := sat + out.saturated
    planes ← place info planes out
  let comps := info.zipWith (fun m p => { m with plane := p }) planes
  return { header := h, reduce, comps, saturatedBlocks := sat }

end JPEG2000
