import Spec.RoundTrip.CodewordBudget
import Spec.RoundTrip.ImageBudget
import Spec.RoundTrip.InitAdmission
import Spec.RoundTrip.PrecinctIndex
import Spec.RoundTrip.TileDecode

/-!
# Reversible encoder to Tier-2 decoder (Plan.md §§4, 5.3, task 7.3f5e3)

For the single-tile, one-layer LRCP encoder, the three numeric limits in
`ImageBudget` suffice to parse the header (T.800 Annex A) and recover the
packet data at every code-block address (Annex B). The proof uses the actual
encoder calls and the default decoder limits.
-/

namespace JPEG2000.Spec.RoundTrip

open JPEG2000 JPEG2000.Encode JPEG2000.Encode.Tier2

/-- Decoding the packets of a successful reversible encoding recovers its
block geometry, pass counts, inclusion, zero bit-planes and codeword bytes.
The bounds are on the stream size, aggregate code-block count and coding-pass
total, with `passesBefore` available to callers accounting for earlier work. -/
theorem reversible_tile_roundtrip {p : Params} {img : Image} {e : Encoded}
    (he : encodeDetailed p img = .ok e) (hrev : p.reversible = true)
    {passesBefore : Nat} (budget : ImageBudget p img e passesBefore) :
    ∃ prec infos, ReversibleTilePackets p img e prec infos ∧
      let hdr := encHeader p img e.guardBits e.exponents (encodeTileLRCP prec)
      Header.parse Limits.default e.codestream = .ok hdr ∧ ∃ out,
        Spec.Tier2.decodeTile Limits.default hdr e.codestream
          (hdr.tiles[0]'(by simp [hdr, encHeader])) none passesBefore = .ok out ∧
        DecodedEncoderTile Limits.default (encLayout p img e.guardBits e.exponents) prec out := by
  have fits := budget.headerFits he
  obtain ⟨_, _, _, hinit⟩ := initPrecincts_of_headerFits fits
  exact decodeTile_encodeDetailed Limits.default he hrev fits hinit
    (initPrecincts_precIdx_injective hinit rfl)
    (fun hp q hq => encodeDetailed_packetBlockOK he hrev (by decide) hp q hq) passesBefore
    (fun hp => budget.packetPasses hp)

end JPEG2000.Spec.RoundTrip
