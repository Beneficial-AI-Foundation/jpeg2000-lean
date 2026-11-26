import Spec.NativePlacement
import Spec.NativeTraversal

/-!
# Whole-image correspondence from checked centred tile reconstruction
Plan.md §4 C9. T.800 Annexes B, F and G.
-/

namespace JPEG2000.Spec.NativeComposition

open JPEG2000.Header JPEG2000.TilePart JPEG2000.Decode JPEG2000.Spec.NativeTraversal
open JPEG2000.Spec.Tier2Equiv (Res)

/-- A reconstructed tile carries the actual parsed layout and the source-to-G.1
correspondence used by the native writer. -/
def TileAgrees (h : Header) (red t : Nat) (out : CenteredTile) (s : Decode.TileOut) : Prop :=
  Progression.Layout.ofHeader h t = .ok (out.layout, out.coding) ∧
    NativePlacement.TileRel h.siz red out.layout out.coding out.sources s

/-- Composing the packet traversal and placement leaves one obligation on the
actual centred reconstruction for a present or omitted tile. -/
theorem of_tiles (L : Limits) (data : ByteArray) (red : Nat)
    (tiles : ∀ h, Header.parse L data = .ok h →
      ∀ t, t < numTiles h.siz → ∀ j n d s, PacketOrigin L h data t j n d s →
      Res (TileAgrees h red t) (centeredTile L h data red t d) (Decode.decodeTile L h t red s)) :
    Res (NativeEquiv.ImageRel red) (do
      L.check JPEG2000.Decode.loc .decompLevels red
      let h ← Header.parse L data
      nativeFromHeader L h data red) (Decode.decode L data red) := by
  apply NativeTraversal.decode_of_stages L data red
    (fun h => NativeOutput.allocOutput L h.siz red)
    (fun h => centeredTile L h data red) (·.saturated)
    (fun h dst t => NativeOutput.writeTile L h.siz red t.layout t.coding dst t.sources)
    (fun h ds sat => ⟨h,red,ds.map .native,sat⟩)
    (fun h info _ _ ds ps => NativePlacement.State L h.siz red ds info ps)
    (fun h => TileAgrees h red) (NativeEquiv.ImageRel red)
  intro allowed h parsed
  constructor
  · exact NativePlacement.allocation parsed ((Limits.checkLe_eq_ok_iff ..).mp allowed)
  · exact tiles h parsed
  · intro info planes allocated t ht sat ds ps out sout state rel
    exact NativePlacement.placement_sim parsed rel.1 state rel.2
  · intro info planes allocated sat ds ps state
    apply NativePlacement.finalize
    exact state

end JPEG2000.Spec.NativeComposition
