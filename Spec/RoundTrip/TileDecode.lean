import Spec.RoundTrip.PrecinctShape

/-!
# Decoding the reversible encoder's tile packets

Plan.md §§4, 5.3 and 7 (C10, M7), T.800 A.4 and B.9–B.12. On the parsed
single-tile stream, the actual Tier-2 wrapper groups the packet fold's states
by the initializer's spans. Each band's raster block index therefore selects
the corresponding codeword from the encoder, including the zero-pass case.
-/

namespace JPEG2000.Spec.RoundTrip

open JPEG2000.Encode (Params Image Encoded encodeDetailed)
open JPEG2000.Encode.Tier2 (BandIn BlockIn encodeTileLRCP lblockInc)
open JPEG2000.Progression (Layout PacketId)
open JPEG2000.Spec.Progression (packets)
open JPEG2000.Spec.Tier2 (PrecSt BandSt BlockSt BandOut TileOut)
open JPEG2000.Tier2.Geometry (resolution precinct)
open JPEG2000.Tier2.Packet (initPrecincts PrecState)

/-- The bands of a returned precinct, in encoder order. The initial geometry
identifies each band and raster block. An included block has exactly one
segment, while an omitted block has the fresh state for its geometry. -/
structure DecodedEncoderBands (st : PrecSt) (bands : Array BandIn) (out : List BandOut) : Prop where
  count : out.length = bands.size
  band : ∀ (i : Nat) (b : BandIn), bands[i]? = some b → ∃ (bs : BandSt) (bo : BandOut),
    st.bands[i]? = some bs ∧ out[i]? = some bo ∧ bo = outAfter bs b ∧
    bo.blocks.length = b.blocks.size ∧ ∀ (k : Nat) (blk : BlockIn), b.blocks[k]? = some blk →
      ∃ geom, bs.blocks[k]? = some ({ geom } : BlockSt) ∧
        (bo.blocks[k]? : Option BlockSt) = some (if blk.numPasses = 0 then { geom }
          else { geom, included := true, zbp := blk.zeroBitPlanes, passes := blk.numPasses,
                 lblock := 3 + lblockInc blk.numPasses blk.data.size,
                 segs := [{ data := blk.data.data.toList, passes := blk.numPasses }] })

private theorem decodedBands_of_ready {L : Limits} {st : PrecSt} {bands : Array BandIn}
    (hr : PrecReady L st bands) :
    DecodedEncoderBands st bands (List.zipWith outAfter st.bands bands.toList) := by
  obtain ⟨_, hlen, hready⟩ := hr
  refine ⟨by simp [hlen], ?_⟩
  intro i b hb
  have hi : i < st.bands.length := hlen ▸ (Array.getElem?_eq_some_iff.mp hb).1
  have hbs := List.getElem?_eq_getElem hi
  have hb' : bands.toList[i]? = some b := by simpa only [Array.getElem?_toList] using hb
  have hpair : (st.bands[i], b) ∈ st.bands.zip bands.toList :=
    List.mem_of_getElem? (List.getElem?_zip_eq_some.mpr ⟨hbs, hb'⟩)
  obtain ⟨_, _, _, _, _, _, hsize, hfresh, _⟩ := hready _ hpair
  change st.bands[i].blocks.length = b.blocks.size at hsize
  refine ⟨_, _, hbs, ?_, rfl, ?_, ?_⟩
  · simp only [List.getElem?_zipWith', hbs, hb', Option.bind_some, Option.map_some]
  · simpa only [outAfter, List.length_mapIdx] using hsize
  · intro k blk hk
    have hki : k < st.bands[i].blocks.length := hsize ▸ (Array.getElem?_eq_some_iff.mp hk).1
    have hf := hfresh _ (List.getElem_mem hki)
    have hg : b.blocks.getD k default = blk := by
      simp only [Array.getD_eq_getD_getElem?, hk, Option.getD_some]
    refine ⟨_, (List.getElem?_eq_getElem hki).trans (congrArg some hf), ?_⟩
    simp only [outAfter, List.getElem?_mapIdx, List.getElem?_eq_getElem hki, Option.map_some, hg]
    rw [hf, blockAfter_fresh]

/-- The nested result of the real wrapper. Every component and resolution has
its layout dimension, including a resolution with no precincts. The indexed
bands use the geometry initialized for this particular resolution and precinct. -/
structure DecodedEncoderTile (L : Limits) (g : Layout) (prec : Array (Array (Array (Array BandIn))))
    (out : TileOut) : Prop where
  passes : out.passes = ((packets g .lrcp #[]).map fun q => passesOf (encBands prec q)).sum
  hdrLeft : out.hdrLeft = 0
  count : out.comps.length = g.numComps
  component : ∀ c < g.numComps, ∃ rs, out.comps[c]? = some rs ∧ rs.length = g.levels c + 1 ∧
    ∀ r ≤ g.levels c, ∃ res ps, resolution L (g.comp c) r = .ok res ∧ rs[r]? = some ps ∧
      ps.length = g.pw c r * g.ph c r ∧ ∀ k < ps.length, ∃ pg st bands,
        precinct L res k = .ok pg ∧ PrecState.init L (g.comp c).params r pg = .ok st ∧
        ps[k]? = some bands ∧
          DecodedEncoderBands (PrecSt.ofFast st) (encBands prec ⟨0, r, c, k⟩) bands

/-- Parsing and decoding a successful reversible encoding recovers its packet
arrays' coding passes and individual code-blocks. The intermediate hypotheses
expose header and initialization admission, distinct flat indices, the four
per-block bounds in `BlockOK`, and the cumulative pass budget. -/
theorem decodeTile_encodeDetailed (L : Limits) {p : Params} {img : Image} {e : Encoded}
    (he : encodeDetailed p img = .ok e) (hrev : p.reversible = true)
    (hfits : HeaderFits L p img e.guardBits e.exponents e.codestream.size)
    {precs base spans}
    (hinit : initPrecincts L (encLayout p img e.guardBits e.exponents) = .ok (precs, base, spans))
    (hinj : ∀ q q', (encLayout p img e.guardBits e.exponents).InPacketSet q →
      (encLayout p img e.guardBits e.exponents).InPacketSet q' →
      precIdx base q = precIdx base q' → q = q')
    (hblock : ∀ {prec infos}, ReversibleTilePackets p img e prec infos → ∀ q,
      (encLayout p img e.guardBits e.exponents).InPacketSet q → ∀ b ∈ encBands prec q,
        ∀ k < b.blocks.size, BlockOK L b.maxZero (b.blocks.getD k default))
    (passesBefore : Nat)
    (hpasses : ∀ {prec infos}, ReversibleTilePackets p img e prec infos →
      passesBefore + ((packets (encLayout p img e.guardBits e.exponents) .lrcp #[]).map
        fun q => passesOf (encBands prec q)).sum ≤ L.maxCodingPasses) :
    ∃ prec infos, ReversibleTilePackets p img e prec infos ∧
      let hdr := encHeader p img e.guardBits e.exponents (encodeTileLRCP prec)
      Header.parse L e.codestream = .ok hdr ∧ ∃ out,
        Spec.Tier2.decodeTile L hdr e.codestream (hdr.tiles[0]'(by simp [hdr, encHeader])) none
          passesBefore = .ok out ∧
        DecodedEncoderTile L (encLayout p img e.guardBits e.exponents) prec out := by
  obtain ⟨prec, infos, hp, hparse, hdata⟩ := parse_encodeDetailed_tileData L he hrev hfits
  let g := encLayout p img e.guardBits e.exponents
  let data := encodeTileLRCP prec
  let hdr := encHeader p img e.guardBits e.exponents data
  have hc := checkFacts_of_ok (encodeDetailed_shape he).check
  have hready (q : PacketId) (hq : g.InPacketSet q) := hp.precReady hinit hq (hblock hp q hq)
  obtain ⟨s, hfold, _, htotal, hstates⟩ := tile_enc L g (encLayout_wf p img e.guardBits e.exponents)
    rfl prec hp.tileShape base (precs.toList.map PrecSt.ofFast) passesBefore data.data.toList []
    hinj hready (hpasses hp)
  simp only [List.append_nil] at hfold
  let forSpan (span : Nat × Nat) := (List.range span.2).map fun k =>
    (s.precs.getD (span.1 + k) default).out
  let forComp (rows : Array (Nat × Nat)) := rows.toList.map forSpan
  let out : TileOut := ⟨spans.toList.map forComp, s.passes, 0⟩
  refine ⟨prec, infos, hp, hparse, out, ?_, htotal, rfl, ?_, ?_⟩
  · have hLayout := layout_ofHeader_enc p img e.guardBits e.exponents data hc
    have hwork := iterationWork_check_of_headerFits p img e.guardBits e.exponents L _ hc hfits
    have hidx : (hdr.tiles[0]'(by simp [hdr, encHeader])).index = 0 := rfl
    dsimp only [hdr, data] at hidx hLayout
    simp only [Spec.Tier2.decodeTile, hidx, hLayout, bind, Except.bind, hwork, hinit, hdata]
    change ((packets g .lrcp #[]).foldlM (Spec.Tier2.step L false false true base passesBefore)
      { precs := precs.toList.map PrecSt.ofFast, hdr := data.data.toList, body := data.data.toList }
      >>= _) = _
    rw [hfold]
    rfl
  · simpa only [out, List.length_map, Array.length_toList] using (initPrecincts_shape hinit).2.1
  · intro c hc'
    obtain ⟨_, hcomps, hrows⟩ := initPrecincts_shape hinit
    have hci : c < spans.size := hcomps ▸ hc'
    let rows := spans.getD c #[]
    have hrow : spans.toList[c]? = some rows := by
      simp only [rows, Array.getElem?_toList, Array.getD_eq_getD_getElem?,
        Array.getElem?_eq_getElem hci, Option.getD_some]
    refine ⟨forComp rows, ?_, ?_, ?_⟩
    · simp only [out, List.getElem?_map, hrow, Option.map_some]
    · simpa only [forComp, List.length_map, Array.length_toList] using (hrows c hc').2
    · intro r hr
      obtain ⟨res, hres, hn, hspan, hgeom⟩ := initPrecincts_geometry hinit hc' hr
      let start := (base.getD c #[]).getD r 0
      have hspan' : rows.toList[r]? = some (start, res.numPrecincts) := by
        simpa only [Array.getElem?_toList] using hspan
      refine ⟨res, forSpan (start, res.numPrecincts), hres, ?_, ?_, ?_⟩
      · simp only [forComp, List.getElem?_map, hspan', Option.map_some]
      · simpa only [forSpan, List.length_map, List.length_range] using hn
      · intro k hk
        have hk' : k < res.numPrecincts := by
          simpa only [forSpan, List.length_map, List.length_range] using hk
        let q : PacketId := ⟨0, r, c, k⟩
        have hq : g.InPacketSet q := ⟨Nat.zero_lt_succ 0, hc', hr, hn ▸ hk'⟩
        obtain ⟨pg, st, hpg, hst, hidx⟩ := hgeom k hk'
        have hfast : (precs.toList.map PrecSt.ofFast)[precIdx base q]? = some (PrecSt.ofFast st) := by
          simp only [q, precIdx, List.getElem?_map, Array.getElem?_toList, hidx, Option.map_some]
        obtain ⟨fresh, final, hf, hfinal, hbands⟩ := hstates q hq
        obtain rfl := Option.some.inj (hf.symm.trans hfast)
        obtain ⟨st', hst', hrdy⟩ := hready q hq
        obtain rfl := Option.some.inj (hst'.symm.trans hf)
        refine ⟨pg, st, final.out, hpg, hst, ?_, ?_⟩
        · change s.precs[start + k]? = some final at hfinal
          simp only [forSpan, List.getElem?_map, List.getElem?_range hk', Option.map_some,
            List.getD_eq_getElem?_getD, hfinal, Option.getD_some]
        · rw [hbands]
          exact decodedBands_of_ready hrdy

end JPEG2000.Spec.RoundTrip
