import JPEG2000.CodestreamTraversal

/-!
# `JPEG2000.decodeCodestream`: bytes → component planes
(Plan.md §3 (pipeline), §6 item 7 (reduced resolution); T.800 B.2, B.3, B-12, B-14, Annex I
(container only))

The public decoder uses checked wavelet and colour reconstruction on every SIZ interval.
Each component retains a compact or wide spatial raster until native G.1 placement chooses
its output storage from the declared precision.

`CodestreamImage.comps` follows SIZ order. Each component covers its own sample grid
with endpoints from B-12 then B-14, including the image origin and the requested
reduction. `CodestreamComponent.get?` reads the final DC-shifted, clamped integer.

Both allocators check the combined reduced area against `maxWorkSamples` and the sum
of the component byte counts at their declared precisions against `maxDecodedBytes`.
The tile reconstruction separately bounds the combined reduced tile area. Reconstruction
before G.1 can restart from the original packet ranges on a compact precision miss.
-/

namespace JPEG2000

open JPEG2000.Bytes JPEG2000.Marker JPEG2000.Header JPEG2000.TilePart

/-- A component returned by the original Int32 decoder, on its own sample grid. -/
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

/-- Compact decoder result used by the Int32 plane API and its numerical theorems. -/
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

/-- Decode a parsed header using the original compact output kernels. -/
def narrowFromHeader (L : Limits) (h : Header) (data : ByteArray) (reduce : Nat) :
    Except Error DecodedImage := do
  let (info, planes) ← allocOutput L h.siz reduce
  withTiles L h data planes (fun t => Assemble.decodeTile L h data t reduce) (·.saturated)
    (place info) fun ps sat =>
      { header := h, reduce, comps := info.zipWith (fun m p => { m with plane := p }) ps,
        saturatedBlocks := sat }

end Decode

/-- Decode into Int32 planes, preserving the compact decoder's original domain and errors. -/
def decodeCodestreamNarrow (L : Limits) (data : ByteArray) (reduce : Nat := 0) :
    Except Error DecodedImage := do
  L.check Decode.loc .decompLevels reduce
  let h ← Header.parse L data
  Decode.narrowFromHeader L h data reduce

/-- A component on its reduced sample grid. Public decoding retains the format-selected
native storage. A converted legacy result borrows its original compact plane. -/
inductive CodestreamComponent where
  /-- Original compact decoder result. -/
  | compact (component : DecodedComponent)
  /-- Checked output of the native tile writer. -/
  | native (component : NativeOutput.OutputComponent)
  deriving Inhabited

namespace CodestreamComponent

/-- Read an exact integer sample by row-major index, including the full unsigned 38-bit range. -/
def get? : CodestreamComponent → Nat → Option Int
  | .compact c, i => (c.plane.get? i).map Int32.toInt
  | .native c, i => c.get? i

/-- Left edge on the reduced component grid. -/
def x0 : CodestreamComponent → Nat
  | .compact c => c.x0
  | .native c => c.rect.x0

/-- Top edge on the reduced component grid. -/
def y0 : CodestreamComponent → Nat
  | .compact c => c.y0
  | .native c => c.rect.y0

/-- Width on the reduced component grid. -/
def width : CodestreamComponent → Nat
  | .compact c => c.width
  | .native c => c.rect.width

/-- Height on the reduced component grid. -/
def height : CodestreamComponent → Nat
  | .compact c => c.height
  | .native c => c.rect.height

/-- Declared sample precision. -/
def depth : CodestreamComponent → Nat
  | .compact c => c.depth
  | .native c => c.format.depth.toNat

/-- Declared sample signedness. -/
def signed : CodestreamComponent → Bool
  | .compact c => c.signed
  | .native c => c.format.signed

/-- Horizontal component separation. -/
def dx : CodestreamComponent → Nat
  | .compact c => c.dx
  | .native c => c.format.dx.toNat

/-- Vertical component separation. -/
def dy : CodestreamComponent → Nat
  | .compact c => c.dy
  | .native c => c.format.dy.toNat

end CodestreamComponent

/-- Codestream result with exact native samples on each component's own grid. -/
structure CodestreamImage where
  /-- Parsed codestream and container metadata. -/
  header : Header
  /-- Number of discarded finest levels. -/
  reduce : Nat
  /-- Components in SIZ order. -/
  comps : Array CodestreamComponent
  /-- Number of blocks saturated by the pre-DC coefficient reconstruction. -/
  saturatedBlocks : Nat

/-- Expose compact samples through the exact accessor without copying any plane. -/
def DecodedImage.toCodestream (img : DecodedImage) : CodestreamImage :=
  ⟨img.header, img.reduce, img.comps.map .compact, img.saturatedBlocks⟩

namespace Decode

/-- Allocate reduced native grids and place every tile's centred reconstruction with G.1. -/
def nativeFromHeader (L : Limits) (h : Header) (data : ByteArray) (reduce : Nat) :
    Except Error CodestreamImage := do
  let initial ← NativeOutput.allocOutput L h.siz reduce
  withTiles L h data initial (centeredTile L h data reduce) (·.saturated)
    (fun dst t => NativeOutput.writeTile L h.siz reduce t.layout t.coding dst t.sources)
    fun ds sat => ⟨h, reduce, ds.map .native, sat⟩

end Decode

/-- Decode a raw or JP2-wrapped codestream with checked component and colour reconstruction.
Read the DC-shifted, clamped samples with `CodestreamComponent.get?`. -/
def decodeCodestream (L : Limits) (data : ByteArray) (reduce : Nat := 0) :
    Except Error CodestreamImage := do
  L.check Decode.loc .decompLevels reduce
  let h ← Header.parse L data
  Decode.nativeFromHeader L h data reduce

end JPEG2000
