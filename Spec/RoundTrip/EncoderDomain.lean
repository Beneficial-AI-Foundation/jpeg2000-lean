import Spec.RoundTrip.Link
import Spec.RoundTrip.TilePlacement

/-!
# Resource limits sufficient for a reference encoding (Plan.md §§3–4, C10 and S3)

The encoder checks the default image geometry. Its successful output also determines the
physical packet work and the size of the full-resolution output. These quantities give
explicit sufficient limits for the single-tile decode, even if they exceed the defaults.
-/

namespace JPEG2000.Spec.RoundTrip

open JPEG2000 JPEG2000.Encode JPEG2000.Encode.Tier2

/-- Decoder limits for this encoding at zero reduction. Each adjustable field covers
both the process default and the demand computed from the input image or encoded blocks. -/
def encoderLimits (p : Params) (img : Encode.Image) (e : Encoded) : Limits :=
  { Limits.default with
    maxInputBytes := max Limits.default.maxInputBytes e.codestream.size
    maxCodeBlocks := max Limits.default.maxCodeBlocks (imageCodeBlocks p img)
    maxCodingPasses := max Limits.default.maxCodingPasses (e.blocks.toList.map BlockInfo.numPasses).sum
    maxWorkSamples := max Limits.default.maxWorkSamples (img.comps.size * (img.width * img.height))
    maxDecodedBytes := max Limits.default.maxDecodedBytes ((img.comps.toList.map fun c =>
      img.width * img.height * Header.bytesPerSample c.depth).sum) }

/-- The computed limits equal the defaults exactly when all five measured demands fit. -/
theorem encoderLimits_eq_default_iff {p : Params} {img : Encode.Image} {e : Encoded} :
    encoderLimits p img e = Limits.default ↔ ImageBudget p img e 0 ∧
      img.comps.size * (img.width * img.height) ≤ Limits.default.maxWorkSamples ∧
      (img.comps.toList.map (fun c => img.width * img.height * Header.bytesPerSample c.depth)).sum ≤
        Limits.default.maxDecodedBytes := by
  constructor
  · intro h
    have bound (proj : Limits → Nat) {n : Nat} (hn : n ≤ proj (encoderLimits p img e)) :
        n ≤ proj Limits.default := h ▸ hn
    exact ⟨⟨bound Limits.maxInputBytes (Nat.le_max_right ..),
      bound Limits.maxCodeBlocks (Nat.le_max_right ..),
      Nat.zero_add _ ▸ bound Limits.maxCodingPasses (Nat.le_max_right ..)⟩,
      bound Limits.maxWorkSamples (Nat.le_max_right ..),
      bound Limits.maxDecodedBytes (Nat.le_max_right ..)⟩
  · rintro ⟨budget, work, bytes⟩
    have passes := budget.passes
    rw [Nat.zero_add] at passes
    simp [encoderLimits, Nat.max_eq_left budget.bytes, Nat.max_eq_left budget.blocks,
      Nat.max_eq_left passes, Nat.max_eq_left work, Nat.max_eq_left bytes]

/-- A successful encoding satisfies all header admission checks at its computed limits. -/
theorem headerFits_encoderLimits {p : Params} {img : Encode.Image} {e : Encoded}
    (he : encodeDetailed p img = .ok e) :
    HeaderFits (encoderLimits p img e) p img e.guardBits e.exponents e.codestream.size := by
  have checked := (encodeDetailed_shape he).check
  have hc := checkFacts_of_ok checked
  have prec := precincts_le_default_of_check checked e.guardBits e.exponents
  refine ⟨Nat.le_max_right .., hc.comps_le, hc.levels_le,
    (by decide : 1 ≤ Limits.default.maxLayers), hc.width_le,
    hc.height_le, imageArea_of_check checked, (by decide : 1 ≤ Limits.default.maxTiles),
    (by decide : 1 ≤ Limits.default.maxTileParts), (by decide : 1 ≤ Limits.default.maxTilePartsPerTile),
    Nat.le_trans hc.comps_le (Nat.le_trans (by decide : 16384 ≤ Limits.default.maxCodeBlocks)
      (Nat.le_max_left ..)), ?_, prec, Nat.le_trans prec (by decide : Limits.default.maxPrecincts ≤ Limits.default.maxPackets)⟩
  rw [← imageCodeBlocks_eq_encCounts hc e.guardBits e.exponents]
  exact Nat.le_max_right ..

/-- The complete single-tile packet round trip for any successful reversible encoding,
with the decoder limits computed from that encoding. -/
theorem reversible_tile_roundtrip_encoderLimits {p : Params} {img : Encode.Image} {e : Encoded}
    (he : encodeDetailed p img = .ok e) (hrev : p.reversible = true) :
    let L := encoderLimits p img e
    ∃ prec infos, ReversibleTilePackets p img e prec infos ∧
      let hdr := encHeader p img e.guardBits e.exponents (encodeTileLRCP prec)
      Header.parse L e.codestream = .ok hdr ∧ ∃ out,
        Spec.Tier2.decodeTile L hdr e.codestream
          (hdr.tiles[0]'(by simp [hdr, encHeader])) none 0 = .ok out ∧
        DecodedEncoderTile L (encLayout p img e.guardBits e.exponents) prec out := by
  exact reversible_tile_roundtrip_with_limits he hrev (headerFits_encoderLimits he)
    (by decide : 109 ≤ Limits.default.maxPassesPerCodeBlock)
    (by rw [Nat.zero_add]; exact Nat.le_max_right ..)

/-- These same limits admit allocation of the full-resolution output component planes
and cover the combined work-sample check of the single tile. -/
theorem output_admitted_encoderLimits {p : Params} {img : Encode.Image} {e : Encoded}
    (he : encodeDetailed p img = .ok e) :
    let L := encoderLimits p img e
    img.comps.size * (img.width * img.height) ≤ L.maxWorkSamples ∧
      ∃ out, JPEG2000.Decode.allocOutput L (encSIZ img) 0 = .ok out := by
  have checked := (encodeDetailed_shape he).check
  have hc := checkFacts_of_ok checked
  have hw : img.width < 2^32 := Nat.lt_of_le_of_lt hc.width_le (by decide)
  have hh : img.height < 2^32 := Nat.lt_of_le_of_lt hc.height_le (by decide)
  refine ⟨Nat.le_max_right .., (Resources.allocOutput_ok_iff ..).2 ?_⟩
  rw [outputCells_encSIZ hw hh, outputBytes_encSIZ hw hh (fun c hc =>
    Nat.lt_trans (Nat.lt_succ_of_le (check_component_samples checked c hc).1.2) (by decide))]
  exact ⟨Nat.le_max_right .., Nat.le_max_right ..⟩

end JPEG2000.Spec.RoundTrip
