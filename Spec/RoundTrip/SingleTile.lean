import Spec.RoundTrip.Link
import Spec.RoundTrip.TilePlacement

/-!
# Full-image decoding of a single encoder tile (Plan.md §4 C10)

The reference encoder carries packet headers inline. At zero reduction the
public specification parses those packets once, places the reconstructed
tile once and returns its planes in header component order.
-/

namespace JPEG2000.Spec.RoundTrip

open JPEG2000 JPEG2000.Bytes JPEG2000.Encode JPEG2000.Spec.Decode

/-- The spec codestream loop for an encoder header runs exactly its one tile
and returns the placed sample arrays paired with their allocation metadata. -/
theorem decode_encTile {p : Params} {img : Encode.Image} {guard : Nat} {exps : Array Nat}
    {packets data : ByteArray} {L : Limits} {info : Array DecodedComponent}
    {planes : Array Plane} {packetOut : Spec.Tier2.TileOut} {tile : Spec.Decode.TileOut}
    {placed : Array SamplePlane} (hc : EncCheckFacts p img) :
    let h := encHeader p img guard exps packets
    Header.parse L data = .ok h →
    JPEG2000.Decode.allocOutput L (encSIZ img) 0 = .ok (info, planes) →
    Spec.Tier2.decodeTile L h data (h.tiles[0]'(by simp [h, encHeader])) none 0 = .ok packetOut →
    packetOut.hdrLeft = 0 →
    Spec.Decode.decodeTile L h 0 0 (some packetOut) = .ok tile →
    place info (initPlanes planes) tile = .ok placed →
    Spec.Decode.decode L data 0 =
      .ok ⟨h, info.zipWith (fun m pl => { info := m, samples := pl.samples }) placed⟩ := by
  intro h hparse ha ht hn hr hp
  have hlev := (Limits.check_eq_ok_iff L JPEG2000.Decode.loc .decompLevels 0).2 (Nat.zero_le _)
  have htiles := (numTiles_enc img hc.width_le hc.height_le hc.width_pos hc.height_pos).2.2
  have hs : h.siz = encSIZ img := rfl
  have hempty : h.ppm.segments.isEmpty = true := rfl
  have hstream : JPEG2000.Tier2.Headers.headerStreamAt h data
      (h.tiles[0]'(by simp [h, encHeader])) #[] = .ok none := rfl
  have ht2 : Spec.Tier2.decodeWithStream L h data (h.tiles[0]'(by simp [h, encHeader]))
      none 0 = .ok packetOut := by
    simp [Spec.Tier2.decodeWithStream, ht, hn, bind, Except.bind, pure, Except.pure]
  have hfirst : h.tiles[0]? = some (h.tiles[0]'(by simp [h, encHeader])) := rfl
  have hindex : (h.tiles[0]'(by simp [h, encHeader])).index = 0 := rfl
  have hemptyRank : (#[] : Array (Array Nat)).getD 0 #[] = #[] := rfl
  simp only [Spec.Decode.decode, codestreamWith, hlev, hparse, hs, ha, hempty, htiles,
    bind, Except.bind, pure, Except.pure, ↓reduceIte, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, List.range'_succ, List.range'_zero, List.forIn_cons, List.forIn_nil]
  simp only [hfirst, hindex, ↓reduceIte, hemptyRank, hstream, Tier2Spec.decode, ht2, hr, hp,
    Option.isSome_some]

/-- Shape and values of a full reconstructed encoder tile before placement. -/
structure ReconstructedEncoderTile (img : Encode.Image) (t : Spec.Decode.TileOut) : Prop where
  /-- Each input component has a plane. -/
  count : t.comps.size = img.comps.size
  /-- Each plane occupies the full tile and contains one sample per pixel. -/
  shape : ∀ i (hi : i < t.comps.size), t.comps[i].1 = encRect img ∧
    t.comps[i].2.width = img.width ∧ t.comps[i].2.height = img.height ∧
    t.comps[i].2.samples.size = img.width * img.height
  /-- The spec sample values recover each input component in raster order. -/
  values : ∀ i (hi : i < t.comps.size), t.comps[i].2.samples.map SpecSample.value =
    (img.comps[i]'(count ▸ hi)).samples

/-- Read the reference-grid dimensions, signedness, depths and row-major component
values of a spec decode in the reference encoder's image type. -/
def encoderImageOfSpec (si : SpecImage) : Encode.Image :=
  { width := si.header.siz.xsiz.toNat - si.header.siz.xosiz.toNat
    height := si.header.siz.ysiz.toNat - si.header.siz.yosiz.toNat
    comps := si.comps.map fun c =>
      { depth := c.info.depth, signed := c.info.signed, samples := c.samples.map SpecSample.value } }

theorem assembled_image {p : Params} {img : Encode.Image} {guard : Nat} {exps : Array Nat}
    {packets : ByteArray} {L : Limits} {info : Array DecodedComponent} {ps : Array Plane}
    {t : Spec.Decode.TileOut} (hc : EncCheckFacts p img) (rt : ReconstructedEncoderTile img t)
    (ha : JPEG2000.Decode.allocOutput L (encSIZ img) 0 = .ok (info, ps)) :
    encoderImageOfSpec ⟨encHeader p img guard exps packets,
      info.zipWith (fun m pl => { info := m, samples := pl.samples }) (t.comps.map Prod.snd)⟩ = img := by
  have hw : img.width < 2 ^ 32 := Nat.lt_of_le_of_lt hc.width_le (by decide)
  have hh : img.height < 2 ^ 32 := Nat.lt_of_le_of_lt hc.height_le (by decide)
  unfold JPEG2000.Decode.allocOutput at ha
  simp only [bind, Except.bind, pure, Except.pure] at ha
  split at ha
  · contradiction
  split at ha
  · contradiction
  simp only [Except.ok.injEq, Prod.mk.injEq] at ha
  obtain ⟨rfl, rfl⟩ := ha
  simp only [encoderImageOfSpec, encHeader, encSIZ, UInt32.toNat_ofNat',
    Nat.mod_eq_of_lt hw, Nat.mod_eq_of_lt hh]
  congr 1
  apply Array.ext (by simp [rt.count])
  intro i hi hj
  have hit : i < t.comps.size := rt.count ▸ hj
  have hd : img.comps[i].depth < 256 :=
    Nat.lt_trans (Nat.lt_succ_of_le (hc.depth _ (by simp)).2) (by decide)
  simp [Array.getElem_zipWith, rt.values i hit, Nat.mod_eq_of_lt hd]

/-- The single-tile image composition at caller-supplied packet and output limits. -/
theorem spec_roundtrip_with_limits_of_tile {L : Limits} {p : Params} {img : Encode.Image} {e : Encoded}
    (he : encodeDetailed p img = .ok e) (hrev : p.reversible = true)
    (fits : HeaderFits L p img e.guardBits e.exponents e.codestream.size)
    (perBlock : 109 ≤ L.maxPassesPerCodeBlock)
    (passes : (e.blocks.toList.map BlockInfo.numPasses).sum ≤ L.maxCodingPasses)
    (hcells : img.comps.size * (img.width * img.height) ≤ L.maxWorkSamples)
    (hbytes : (img.comps.toList.map fun c => img.width * img.height *
      Header.bytesPerSample c.depth).sum ≤ L.maxDecodedBytes)
    (recon : ∀ prec infos out, ReversibleTilePackets p img e prec infos →
      DecodedEncoderTile L (encLayout p img e.guardBits e.exponents) prec out →
      let h := encHeader p img e.guardBits e.exponents (Encode.Tier2.encodeTileLRCP prec)
      ∃ t, Spec.Decode.decodeTile L h 0 0 (some out) = .ok t ∧
        ReconstructedEncoderTile img t) :
    ∃ si, Spec.Decode.decode L e.codestream 0 = .ok si ∧
      encoderImageOfSpec si = img := by
  obtain ⟨prec, infos, packets, hparse, out, ht, hd⟩ :=
    reversible_tile_roundtrip_with_limits he hrev fits perBlock
      (passesBefore := 0) (by simpa only [Nat.zero_add] using passes)
  obtain ⟨t, hr, hshape⟩ := recon prec infos out packets hd
  have checked := (encodeDetailed_shape he).check
  have hc := checkFacts_of_ok checked
  obtain ⟨info, ps, ha, hp⟩ := place_encTile_of_limits t checked
    (Nat.lt_of_le_of_lt hc.width_le (by decide)) (Nat.lt_of_le_of_lt hc.height_le (by decide))
    hcells hbytes hshape.count hshape.shape
  exact ⟨_, decode_encTile hc hparse ha ht hd.hdrLeft hr hp, assembled_image hc hshape ha⟩

/-- Specialisation of the single-tile image composition to the default decoder limits. -/
theorem spec_roundtrip_of_tile {p : Params} {img : Encode.Image} {e : Encoded}
    (he : encodeDetailed p img = .ok e) (hrev : p.reversible = true)
    (budget : ImageBudget p img e 0)
    (hcells : img.comps.size * (img.width * img.height) ≤ Limits.default.maxWorkSamples)
    (hbytes : (img.comps.toList.map fun c => img.width * img.height *
      Header.bytesPerSample c.depth).sum ≤ Limits.default.maxDecodedBytes)
    (recon : ∀ prec infos out, ReversibleTilePackets p img e prec infos →
      DecodedEncoderTile Limits.default (encLayout p img e.guardBits e.exponents) prec out →
      let h := encHeader p img e.guardBits e.exponents (Encode.Tier2.encodeTileLRCP prec)
      ∃ t, Spec.Decode.decodeTile Limits.default h 0 0 (some out) = .ok t ∧
        ReconstructedEncoderTile img t) :
    ∃ si, Spec.Decode.decode Limits.default e.codestream 0 = .ok si ∧
      si.comps.map (fun c => c.samples.map SpecSample.value) = img.comps.map (·.samples) := by
  obtain ⟨si, hsi, eq⟩ := spec_roundtrip_with_limits_of_tile he hrev (budget.headerFits he)
    (by decide) (by simpa only [Nat.zero_add] using budget.passes) hcells hbytes recon
  refine ⟨si, hsi, ?_⟩
  simpa [encoderImageOfSpec, Function.comp_def] using
    congrArg (fun x : Encode.Image => x.comps.map (·.samples)) eq

end JPEG2000.Spec.RoundTrip
