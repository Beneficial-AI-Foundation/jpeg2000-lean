import Spec.RoundTrip.BandCoverage
import Spec.RoundTrip.CollectedBlocks
import Spec.RoundTrip.Link
import Spec.RoundTrip.SubbandInverse

/-!
# Reversible tile-component reconstruction (Plan.md §§4, 5.1, 5.3–5.4, 7)

At full resolution, the spec's collected code-blocks cover every coefficient read by
the inverse 5/3 transform (T.800 B.5–B.7 and Annex F). The plane returned by the tile
decoder recovers the row supplied to the forward transform, including the forward RCT
when the encoder selected it.
-/

namespace JPEG2000.Spec.RoundTrip

open JPEG2000.Encode JPEG2000.Tier2.Geometry JPEG2000.Spec.Decode

section Component

variable {L : Limits} {p : Params} {img : Image} {e : Encoded} {prec infos tile}
  (hp : ReversibleTilePackets p img e prec infos)
  (ht : DecodedEncoderTile L (encLayout p img e.guardBits e.exponents) prec tile)
  (fits : HeaderFits L p img e.guardBits e.exponents e.codestream.size)
  {c : Nat} {rs : SpecPrecs} (hrs : tile.comps[c]? = some rs)
  (hK : ComponentPlanes31 (encGeom p img e.guardBits e.exponents)
    ((bands53 p img (encMct p img)).getD c #[]))

include hp ht fits hrs hK in
private theorem collected_bandSample (hc : c < img.comps.size) (depth : Nat)
    {r : Nat} (hr : r ≤ p.levels) {b : Band} (hb : b ∈ bandsOf r) {u v : Int}
    (hin : Equiv.InBand (encRect img) (bandLevel p.levels r) b u v) :
    (bandGrid53 (collectedEntries (encParams p e.guardBits e.exponents) depth rs)
      p.levels (bandLevel p.levels r) b).get u v = bandSample (reversibleBand p img c r b) u v := by
  obtain ⟨res, j, bi, k, pg, pb, cb, hres, hj, cover, _⟩ :=
    encBandCoverage_of_headerFits fits hc hr hb hin
  obtain ⟨sb, ha, hgeom⟩ := ht.blockAtGeometry hp hrs hr hres hj cover.precinct_ok
    cover.band_at cover.block_at
  rw [cover.label] at ha
  have hxy : BlockContains sb.geom.rect u.toNat v.toNat := hgeom ▸ cover.inside
  have hgrid := ht.bandGrid53_collected hp hrs hK depth hr ha hxy (by
    intro j' bi' k' pb' cb' o' call' label' inside'
    obtain ⟨pb₀, o₀, call₀, label₀⟩ := ht.packetBlockAt hp hrs ha
    obtain ⟨res₀, pg₀, hres₀, hpg₀, hpb₀, hcb₀⟩ := call₀.geometry
    obtain ⟨_, pg', hres', hpg', hpb', hcb'⟩ := call'.geometry
    obtain rfl := Except.ok.inj (hres'.symm.trans hres₀)
    exact BandBlockAt.unique hres₀
      ⟨hpg', hpb', label', hcb', inside'⟩ ⟨hpg₀, hpb₀, label₀, hcb₀, hxy⟩)
  have slot : bi = b.index - 1 := by
    have hi := (cover.indices hres).2.1
    by_cases hz : r = 0
    · have hll : b = .LL := by simpa [bandsOf, hz] using hb
      simpa [hz, hll, Band.index] using hi
    · simpa [hz] using hi
  let d := reversibleBand p img c r b
  have rect : d.rect = bandRect (encRect img) (bandLevel p.levels r) b := by
    dsimp only [d]
    rw [reversibleBand_eq hc hr hb]
    rfl
  obtain ⟨hx, _, hy, _⟩ := hin
  rw [← rect] at hx hy
  rw [slot] at hgrid
  change (bandGrid53 _ _ _ _).get (u.toNat : Int) (v.toNat : Int) =
    d.vals.getD ((v.toNat - d.rect.y0) * d.rect.width + (u.toNat - d.rect.x0)) 0 at hgrid
  rw [show (u.toNat : Int) = u by omega, show (v.toNat : Int) = v by omega] at hgrid
  change _ = d.vals.getD ((v - d.rect.y0).toNat * d.rect.width + (u - d.rect.x0).toNat) 0
  rwa [show (v - d.rect.y0).toNat = v.toNat - d.rect.y0 by omega,
    show (u - d.rect.x0).toNat = u.toNat - d.rect.x0 by omega]

include hp ht fits hrs hK in
/-- At zero reduction, the real tile-component decoder returns the encoder's reversible
row and a zero saturation count. The plane limit is charged once for this component. -/
theorem DecodedEncoderTile.tileComp_reversibleRow (hrev : p.reversible = true)
    (hw : img.width * img.height ≤ L.maxWorkSamples) (depth F : Nat) :
    ∃ pl, Decode.tileComp L (encGeom p img e.guardBits e.exponents) depth F 0 rs =
      .ok (pl, 0) ∧ ReversibleRow img.width img.height pl ((reversibleRows p img).getD c #[]) := by
  have hc : c < img.comps.size := (encLayout_coding p img e.guardBits e.exponents).1 ▸
    ht.count ▸ (List.getElem?_eq_some_iff.mp hrs).1
  refine ⟨_, ht.tileComp_collected hp hrs hK hrev hw depth F, idwt_reversibleRow hc _ ?_⟩
  intro r hr b hb u v hin
  exact collected_bandSample hp ht fits hrs hK hc depth hr hb hin

end Component

/-- A successful reversible encoding decodes to a tile whose full-resolution component
planes recover the encoder's pre-wavelet rows. The same parsed header and Tier-2 result
serve every component. The default image budgets admit the stream and its packets. -/
theorem encodeDetailed_waveletReconstruction {p : Params} {img : Image} {e : Encoded}
    (he : encodeDetailed p img = .ok e) (hrev : p.reversible = true)
    {passesBefore : Nat} (budget : ImageBudget p img e passesBefore) :
    ∃ prec infos, ReversibleTilePackets p img e prec infos ∧
      let hdr := encHeader p img e.guardBits e.exponents (Encode.Tier2.encodeTileLRCP prec)
      Header.parse Limits.default e.codestream = .ok hdr ∧ ∃ tile,
        Spec.Tier2.decodeTile Limits.default hdr e.codestream
          (hdr.tiles[0]'(by simp [hdr, encHeader])) none passesBefore = .ok tile ∧
        DecodedEncoderTile Limits.default (encLayout p img e.guardBits e.exponents) prec tile ∧
        ∀ c < img.comps.size, ComponentPlanes31 (encGeom p img e.guardBits e.exponents)
          ((bands53 p img (encMct p img)).getD c #[]) → ∀ depth F, ∃ pl,
          Decode.tileComp Limits.default (encGeom p img e.guardBits e.exponents)
            depth F 0 (tile.comps.getD c []) = .ok (pl, 0) ∧
          ReversibleRow img.width img.height pl ((reversibleRows p img).getD c #[]) := by
  obtain ⟨prec, infos, hp, hhdr, tile, htile, ht⟩ := reversible_tile_roundtrip he hrev budget
  refine ⟨prec, infos, hp, hhdr, tile, htile, ht, ?_⟩
  intro c hc hK depth F
  have fits := budget.headerFits he
  have hci : c < tile.comps.length := by
    rwa [ht.count, (encLayout_coding p img e.guardBits e.exponents).1]
  have hrs : tile.comps[c]? = some (tile.comps.getD c []) := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hci, Option.getD_some]
  exact ht.tileComp_reversibleRow hp fits hrs hK hrev fits.area depth F

end JPEG2000.Spec.RoundTrip
