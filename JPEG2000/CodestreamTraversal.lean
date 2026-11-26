import JPEG2000.TileDispatch

/-!
# Tile traversal and centred reconstruction
(Plan.md §§3, 5.1, 6, 7; T.800 B.2, B-12, B-14, B.9–B.12, G.1–G.3)

Keep the Tier-2 pass counter and tile-part cursor across the whole grid. Each output
stage consumes one reconstructed tile before the next tile's packets are decoded.
-/

namespace JPEG2000.Decode

open Header TilePart

/-- Traverse the tile grid in codestream order, carrying the packet-pass budget, tile-part
cursor and output storage. Both output paths use this same Tier-2 traversal. -/
@[inline] def withTiles {P T α : Type} (L : Limits) (h : Header) (data : ByteArray)
    (initial : P) (tile : Nat → Option Tier2.Packet.TileCodeBlocks → Except Error T)
    (saturated : T → Nat) (write : P → T → Except Error P) (finish : P → Nat → α) :
    Except Error α := do
  let mut planes := initial
  let idx ← if h.ppm.segments.isEmpty then pure #[] else Tier2.Headers.ppmChunkIndex L h
  let mut passes := 0
  let mut sat := 0
  let mut j := 0
  for t in [0:numTiles h.siz] do
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
    let out ← tile t tcb
    sat := sat + saturated out
    planes ← write planes out
  return finish planes sat

/-- Centred tile planes after the inverse DWT and optional inverse MCT. -/
structure CenteredTile where
  /-- Component geometry and effective parameters for this tile. -/
  layout : Progression.Layout
  /-- Effective tile coding, including the MCT flag. -/
  coding : Coding
  /-- Sources before DC level shift, in component order. -/
  sources : Array NativeOutput.Source
  /-- Blocks saturated in dequantisation. -/
  saturated : Nat

/-- Use the effective tile header for component reconstruction and native placement.
Successful checked reconstruction preserves all coefficients at the selected precision. -/
def centeredTile (L : Limits) (h : Header) (data : ByteArray) (reduce t : Nat)
    (tcb : Option Tier2.Packet.TileCodeBlocks) : Except Error CenteredTile := do
  let (g, coding) ← Progression.Layout.ofHeader h t
  let sources ← TileDispatch.tile L h data g coding tcb reduce
  return ⟨g, coding, sources, 0⟩

end JPEG2000.Decode
