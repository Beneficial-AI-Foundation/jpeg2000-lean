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

private theorem alloc_count {L : Limits} {img : Encode.Image}
    {info : Array DecodedComponent} {ps : Array Plane}
    (ha : JPEG2000.Decode.allocOutput L (encSIZ img) 0 = .ok (info, ps)) :
    info.size = img.comps.size := by
  unfold JPEG2000.Decode.allocOutput at ha
  simp only [bind, Except.bind, pure, Except.pure] at ha
  split at ha
  · contradiction
  split at ha
  · contradiction
  simp only [Except.ok.injEq, Prod.mk.injEq] at ha
  simp [← ha.1, encSIZ]

/-- Once a single encoder tile is reconstructed, the public specification returns the
original values in every component. Input and output admission follow their numeric
budgets; the only remaining stage is the reconstruction of that tile. -/
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
  obtain ⟨prec, infos, packets, hparse, out, ht, hd⟩ := reversible_tile_roundtrip he hrev budget
  obtain ⟨t, hr, hshape⟩ := recon prec infos out packets hd
  have checked := (encodeDetailed_shape he).check
  have hc := checkFacts_of_ok checked
  obtain ⟨info, ps, ha, hp⟩ := place_encTile_of_limits t checked
    (Nat.lt_of_le_of_lt hc.width_le (by decide)) (Nat.lt_of_le_of_lt hc.height_le (by decide))
    hcells hbytes hshape.count hshape.shape
  refine ⟨_, decode_encTile hc hparse ha ht hd.hdrLeft hr hp, ?_⟩
  have hi := alloc_count ha
  have hcount := hshape.count
  apply Array.ext (by simp [hcount, hi])
  intro i hl _
  have hit : i < t.comps.size := by simpa [hcount, hi] using hl
  simpa using hshape.values i hit

end JPEG2000.Spec.RoundTrip
