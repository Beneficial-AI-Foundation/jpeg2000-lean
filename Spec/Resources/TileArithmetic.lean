import Spec.Resources.Tier1Work
import Spec.Resources.WideArithmetic

/-!
# Signed integer widths in native tile reconstruction

Plan.md §§3–5 and 7, T.800 Annexes D–G. The parsed Tier-1 coefficients establish
the inputs of the wide-arithmetic bounds. The conclusion applies at the pre-G.1
source read used by the ordinary codestream tile writer.
-/

namespace JPEG2000.Spec.Resources

/-- Every post-MCT source of a parsed tile has a bounded signed width before placement. -/
theorem parsed_tile_signed_width {L : Limits} {data : ByteArray} {h : Header.Header} {t : Nat}
    {g : Progression.Layout} {coding : Header.Coding} (parsed : Header.parse L data = .ok h)
    (layout : Progression.Layout.ofHeader h t = .ok (g,coding))
    (store : Option JPEG2000.Tier2.Packet.TileCodeBlocks) (red : Nat)
    {out : Array JPEG2000.NativeOutput.Source}
    (ok : JPEG2000.TileDispatch.tile L h data g coding store red = .ok out) :
    ∀ s ∈ out, ∀ i, (s.read i).natAbs.log2 + 2 ≤ 395 + 540 * L.maxDecompLevels := by
  have blocks (i : Fin g.numComps) : WideArithmetic.BlockBounds data (g.comp i).params (2^292-1) 291 := by
    intro r b cb cs accepted cell mem
    have params := (WideHeaderBounds.parsed_component_bounds parsed layout i red).1
    obtain ⟨mag, plane, _⟩ := (Tier1Work.parsed_cells params data r b cb cs accepted).2 cell mem
    exact ⟨by omega, plane⟩
  intro s hs i
  have bits := WideArithmetic.magnitude_bits (WideArithmetic.parsed_tile parsed layout store red blocks ok s hs i)
  omega

/-- Bound each centred sample returned by the public traversal, including a missing
tile whose coefficient store is empty. The native reader supplies its index bound. -/
theorem centeredTile_signed_width {L : Limits} {data : ByteArray} {h : Header.Header} {t red : Nat}
    {store : Option JPEG2000.Tier2.Packet.TileCodeBlocks} {out : JPEG2000.Decode.CenteredTile}
    (parsed : Header.parse L data = .ok h)
    (ok : JPEG2000.Decode.centeredTile L h data red t store = .ok out) :
    ∀ s ∈ out.sources, ∀ i, (s.read i).natAbs.log2 + 2 ≤ 395 + 540 * L.maxDecompLevels := by
  obtain ⟨⟨g, coding⟩, layout, tail⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨sources, hs, last⟩ := Tier2Equiv.bind_ok tail
  cases last
  exact parsed_tile_signed_width parsed layout store red hs


end JPEG2000.Spec.Resources
