import Spec.RoundTrip.EncoderDomain
import Spec.RoundTrip.ReconstructedTile
import Spec.RoundTrip.WaveletReconstruction

/-!
# Specification-level lossless image round trip (Plan.md §4 C10)

At full resolution, the reversible reference codestream recovers every original
sample of every component. The caller can supply admissible limits or use the
explicit limits computed from the encoding. T.800 Annexes A–G.
-/

namespace JPEG2000.Spec.RoundTrip

open JPEG2000 JPEG2000.Encode

/-- Equality of the complete input image for the public spec decoder under admissible packet
and output limits. Every decoded sample carries the reversible flag used by the public C9 sample relation. -/
theorem spec_roundtrip_lossless_with_limits {L : Limits} {p : Params} {img : Encode.Image} {e : Encoded}
    (he : encodeDetailed p img = .ok e) (hrev : p.reversible = true)
    (fits : HeaderFits L p img e.guardBits e.exponents e.codestream.size)
    (perBlock : 109 ≤ L.maxPassesPerCodeBlock)
    (passes : (e.blocks.toList.map BlockInfo.numPasses).sum ≤ L.maxCodingPasses)
    (work : img.comps.size * (img.width * img.height) ≤ L.maxWorkSamples)
    (bytes : (img.comps.toList.map fun c => img.width * img.height *
      Header.bytesPerSample c.depth).sum ≤ L.maxDecodedBytes) :
    ∃ si, Spec.Decode.decode L e.codestream 0 = .ok si ∧
      encoderImageOfSpec si = img ∧
      ∀ i (hi : i < si.comps.size) sample, sample ∈ si.comps[i].samples → sample.reversible = true := by
  obtain ⟨prec, infos, packets, hparse, out, ht, hd⟩ :=
    reversible_tile_roundtrip_with_limits he hrev fits perBlock (passesBefore := 0)
      (by simpa only [Nat.zero_add] using passes)
  have checked := (encodeDetailed_shape he).check
  have hc := checkFacts_of_ok checked
  have area : img.width * img.height ≤ L.maxWorkSamples := by
    apply Nat.le_trans _ work
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (img.width * img.height) hc.comps_pos
  obtain ⟨t, hr, shape, reversible⟩ := decodeTile_reconstructedEncoderTile_lossless
    (data := Encode.Tier2.encodeTileLRCP prec) checked hrev work (out := out) (guard := e.guardBits)
    (exps := e.exponents) (by
    intro c hic
    have hi : c < out.comps.length := by
      rwa [hd.count, (encLayout_coding p img e.guardBits e.exponents).1]
    have hrs : out.comps[c]? = some (out.comps.getD c []) := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    exact hd.tileComp_reversibleRow_of_encodeDetailed packets fits hrs he hrev area _ _)
  obtain ⟨info, ps, ha, placed⟩ := place_encTile_of_limits t checked
    (Nat.lt_of_le_of_lt hc.width_le (by decide)) (Nat.lt_of_le_of_lt hc.height_le (by decide))
    work bytes shape.count shape.shape
  refine ⟨_, decode_encTile hc hparse ha ht hd.hdrLeft hr placed, assembled_image hc shape ha, ?_⟩
  intro i hi sample hs
  simp only [Array.size_zipWith, Array.size_map] at hi
  have hit : i < t.comps.size := Nat.lt_of_lt_of_le hi (Nat.min_le_right ..)
  exact reversible i hit sample (by simpa only [Array.getElem_zipWith, Array.getElem_map] using hs)

/-- Equality of the complete input image for the public spec decoder under admissible packet
and output limits. All intermediate tile, wavelet and display stages are discharged. -/
theorem spec_roundtrip_with_limits {L : Limits} {p : Params} {img : Encode.Image} {e : Encoded}
    (he : encodeDetailed p img = .ok e) (hrev : p.reversible = true)
    (fits : HeaderFits L p img e.guardBits e.exponents e.codestream.size)
    (perBlock : 109 ≤ L.maxPassesPerCodeBlock)
    (passes : (e.blocks.toList.map BlockInfo.numPasses).sum ≤ L.maxCodingPasses)
    (work : img.comps.size * (img.width * img.height) ≤ L.maxWorkSamples)
    (bytes : (img.comps.toList.map fun c => img.width * img.height *
      Header.bytesPerSample c.depth).sum ≤ L.maxDecodedBytes) :
    ∃ si, Spec.Decode.decode L e.codestream 0 = .ok si ∧
      encoderImageOfSpec si = img := by
  obtain ⟨si, ok, image, _⟩ := spec_roundtrip_lossless_with_limits he hrev fits perBlock passes work bytes
  exact ⟨si, ok, image⟩

/-- The spec decodes every successful reversible encoding exactly at its computed resource limits. -/
theorem spec_roundtrip {p : Params} {img : Encode.Image} {e : Encoded}
    (he : encodeDetailed p img = .ok e) (hrev : p.reversible = true) :
    ∃ si, Spec.Decode.decode (encoderLimits p img e) e.codestream 0 = .ok si ∧
      encoderImageOfSpec si = img := by
  exact spec_roundtrip_with_limits he hrev (headerFits_encoderLimits he)
    (by decide : 109 ≤ Limits.default.maxPassesPerCodeBlock)
    (Nat.le_max_right ..) (Nat.le_max_right ..) (Nat.le_max_right ..)

/-- With the default decoder policy, only the five numerical image budgets remain. -/
theorem spec_roundtrip_default {p : Params} {img : Encode.Image} {e : Encoded}
    (he : encodeDetailed p img = .ok e) (hrev : p.reversible = true) (budget : ImageBudget p img e 0)
    (work : img.comps.size * (img.width * img.height) ≤ Limits.default.maxWorkSamples)
    (bytes : (img.comps.toList.map fun c => img.width * img.height *
      Header.bytesPerSample c.depth).sum ≤ Limits.default.maxDecodedBytes) :
    ∃ si, Spec.Decode.decode Limits.default e.codestream 0 = .ok si ∧
      encoderImageOfSpec si = img := by
  simpa only [encoderLimits_eq_default_iff.mpr ⟨budget, work, bytes⟩] using spec_roundtrip he hrev

/-- The ordinary byte-returning reference encoder and public spec decoder round-trip
all components for every successful reversible encoding with sufficient resources. -/
theorem encode_spec_roundtrip {p : Params} {img : Encode.Image} {data : ByteArray}
    (he : encode p img = .ok data) (hrev : p.reversible = true) :
    ∃ L si, Spec.Decode.decode L data 0 = .ok si ∧
      encoderImageOfSpec si = img := by
  cases h : encodeDetailed p img with
  | error err => simp [encode, h, Functor.map, Except.map] at he
  | ok e =>
    have same : e.codestream = data := by simpa [encode, h, Functor.map, Except.map] using he
    subst data
    exact ⟨_, spec_roundtrip h hrev⟩

end JPEG2000.Spec.RoundTrip
