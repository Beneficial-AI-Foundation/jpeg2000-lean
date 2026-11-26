import Spec.Decode
import Spec.RoundTrip.CodewordBudget
import Spec.RoundTrip.Tier1
import Spec.RoundTrip.TileDecode

/-!
# Reconstructing the reversible encoder's packet blocks

Plan.md §§4, 5.3 and 7 (C10, M7), T.800 B.10, Annex D and E.1.1.2.
The encoder ends a nonempty codeword with cleanup at plane zero. The decoder's
per-pass invariant therefore removes the reversible midpoint offset. An omitted
block has no segments and its initial coefficient array reconstructs as zeros.
-/

namespace JPEG2000.Spec.RoundTrip

open JPEG2000.Encode.Tier1 (EncOut encodeCodeBlock numBits maxMag)
open JPEG2000.Tier2.Geometry
open JPEG2000.Tier2.Packet (bandMb PrecState)
open JPEG2000.Spec.Tier1
open JPEG2000.Spec.Tier1Equiv (sgeom orientOf decodePasses_inv)
open JPEG2000.Spec.Tier2 (BlockSt BandSt PrecSt)
open JPEG2000.Spec.Tier2Equiv (bind_ok)

private theorem fullPasses_plane {w h K n : Nat} (b : Band) (data : List UInt8)
    (hn : n = 3 * K - 2) (hnpos : 0 < n) :
    ∀ c ∈ (decodePasses (sgeom w h b) K n (DecState.init (sgeom w h b) data)).coeffs,
      c.lsbPlane = 0 := by
  let cs := (decodePasses (sgeom w h b) K n (DecState.init (sgeom w h b) data)).coeffs
  have H := decodePasses_inv (w := w) (h := h) (b := b) K
    (DecState.init (sgeom w h b) data) rfl n hnpos (Nat.le_of_eq hn)
  have hlast : n - 1 = 3 * (K - 1) := by omega
  have hkind : passKind (n - 1) = .cleanup := hlast ▸ Spec.Tier1Equiv.passKind_mul3 (K - 1)
  have hplane : passPlane K (n - 1) = 0 := by unfold passPlane; omega
  intro c hc
  obtain ⟨i, hi⟩ := Array.mem_iff_getElem?.mp hc
  change cs[i]? = some c at hi
  have hil : i < w * h := H.1 ▸ (Array.getElem?_eq_some_iff.mp hi).1
  have hw : 0 < w := by cases w <;> simp_all
  have hx := Nat.mod_lt i hw
  have hy : i / w < h := (Nat.div_lt_iff_lt_mul hw).mpr (Nat.mul_comm w h ▸ hil)
  have hc' := H.2 (i % w) (i / w) hx hy
  rw [Spec.Tier1Equiv.coeffAt_nat _ _ _ _ hx hy] at hc'
  change Spec.Tier1Equiv.Post K (n - 1) (cs.getD (i / w * w + i % w) {}) at hc'
  rw [Nat.div_add_mod', Array.getD_eq_getD_getElem?, hi] at hc'
  simp only [Option.getD_some, Spec.Tier1Equiv.Post, hkind, hplane] at hc'
  cases hs : c.sig
  · exact (hc'.1.1.1 hs).2
  · exact hc'.1.2 hs

/-- The observations needed by the reversible reconstruction loop on a returned
block. The skipped zero-pass case also gives the source array explicitly. -/
def ReconstructsBlock (params : Header.CompParams) (r : Nat) (b : Band)
    (sb : BlockSt) (src : Array Int) : Prop :=
  ∃ cs, Spec.Decode.decodeBlockSt params r b sb = .ok cs ∧ cs.map Coeff.value = src ∧
    (∀ c ∈ cs, c.lsbPlane = 0) ∧ Spec.Quant.dequantBlockRev params.roiShift cs = src ∧
    (sb.passes = 0 → src = Array.replicate (sb.geom.rect.width * sb.geom.rect.height) 0)

private theorem reconstruct_packetBlock {params : Header.CompParams}
    (hstyle : params.cbStyle.toNat = 0) (hroi : params.roiShift = 0)
    {r : Nat} {b : Band} {g : CodeBlockGeom} {o : EncOut} {src : Array Int}
    (he : encodeCodeBlock g.rect.width g.rect.height (Encode.orient b)
      (bandMb params r b) src = .ok o) (hK : numBits (maxMag src) ≤ 37) :
    ReconstructsBlock params r b (blockAfter { geom := g } (packetBlockOf o)) src := by
  let w := g.rect.width
  let h := g.rect.height
  let Mb := bandMb params r b
  let cb := CodeBlock.ofData w h (orientOf b) Mb o.zeroBitPlanes o.numPasses o.bytes
  obtain ⟨_, hz, hn⟩ := encodeCodeBlock_counts he
  have hk : cb.codedPlanes = o.codedPlanes := by
    change Mb - o.zeroBitPlanes = o.codedPlanes
    change o.zeroBitPlanes + o.codedPlanes = Mb at hz
    omega
  have hnp : cb.numPasses = o.numPasses := by
    simp only [cb, CodeBlock.numPasses, CodeBlock.ofData, Segment.single]
    split <;> simp_all
  have hclamp : cb.clampPasses = cb := by
    simp [CodeBlock.clampPasses, hnp, hk, hn]
  have hval : decodeValues cb = .ok src := decodeValues_encodeCodeBlock he hK
  unfold decodeValues at hval
  cases hd : decodeCodeBlock cb with
  | error e => rw [hd] at hval; cases hval
  | ok cs =>
    rw [hd] at hval
    have hvalues : cs.map Coeff.value = src := Except.ok.inj hval
    have hstate := hd
    unfold decodeCodeBlock at hstate
    rw [hclamp] at hstate
    obtain ⟨_, _, heq⟩ := bind_ok (show (cb.validate >>= fun _ =>
      pure (decodeState cb).coeffs) = .ok cs from hstate)
    have hcs : (decodeState cb).coeffs = cs := Except.ok.inj heq
    have hempty (h0 : o.numPasses = 0) : cs = Array.replicate (w * h) {} := by
      rw [← hcs]; simp only [cb, h0]; rfl
    have hplanes : ∀ c ∈ cs, c.lsbPlane = 0 := by
      by_cases h0 : o.numPasses = 0
      · rw [hempty h0]
        intro c hc
        obtain rfl := (Array.mem_replicate.mp hc).2
        rfl
      · rw [← hcs, decodeState_plain cb rfl o.bytes o.numPasses
          (by simp [cb, CodeBlock.ofData, Segment.single, h0]), hk]
        exact fullPasses_plane b o.bytes hn (by omega)
    have hdeq : Spec.Quant.dequantBlockRev params.roiShift cs = src := by
      rw [← hvalues, hroi]
      apply Array.map_congr_left
      intro c hc
      rw [Spec.Quant.dequantRev, Spec.Quant.roiUnshift_zero,
        Spec.Quant.reconstructRev_full c (hplanes c hc)]
    rw [blockAfter_fresh]
    by_cases h0 : o.numPasses = 0
    · simp only [packetBlockOf, h0, ↓reduceIte]
      refine ⟨cs, ?_, hvalues, hplanes, hdeq, fun _ => ?_⟩
      · -- An omitted block reports zero missing planes. With no passes, validation
        -- and the returned initial coefficients are independent of that field.
        unfold Spec.Decode.decodeBlockSt Spec.Decode.blockStCodeBlock
        simp only [hstyle, hroi, Nat.add_zero, Bool.false_eq_true, ↓reduceIte]
        rw [← hd]
        simp only [cb, h0, decodeCodeBlock, CodeBlock.clampPasses, CodeBlock.ofData,
          Segment.single, ↓reduceIte, CodeBlock.numPasses, List.map_nil, List.sum_nil,
          Nat.zero_le, decodeCodeBlockExact, CodeBlock.validate, Nat.lt_irrefl,
          false_and]
        rfl
      · rw [← hvalues, hempty h0, Array.map_replicate]
        rfl
    · simp only [packetBlockOf, h0, ↓reduceIte]
      refine ⟨cs, ?_, hvalues, hplanes, hdeq, fun h => absurd h h0⟩
      unfold Spec.Decode.decodeBlockSt Spec.Decode.blockStCodeBlock
      simpa only [cb, CodeBlock.ofData, Segment.single, h0, ↓reduceIte, hstyle, hroi,
        Nat.add_zero, List.toList_toArray, show Mode.ofStyle 0 = Mode.plain from rfl] using hd

-- Invert the checked band maps at a common raster index, even when encoder
-- and decoder used different limits for their geometry checks.
private theorem listMapM_at {α β : Type} {f : α → Except Error β} :
    ∀ {xs : List α} {ys : List β} {i : Nat} {y : β}, xs.mapM f = .ok ys → ys[i]? = some y →
      ∃ x, xs[i]? = some x ∧ f x = .ok y
  | [], _, _, _, he, hy => by cases he; simp at hy
  | x :: xs, _, i, y, he, hy => by
    rw [List.mapM_cons] at he
    obtain ⟨v, hv, he⟩ := bind_ok he
    obtain ⟨vs, hvs, he⟩ := bind_ok he
    cases he
    cases i with
    | zero => cases hy; exact ⟨x, rfl, hv⟩
    | succ j => exact listMapM_at (xs := xs) (i := j) hvs hy

private theorem arrayMapM_at {α β : Type} {f : α → Except Error β} {xs : Array α} {ys : Array β}
    {i : Nat} {y : β} (he : xs.mapM f = .ok ys) (hy : ys[i]? = some y) :
    ∃ x, xs[i]? = some x ∧ f x = .ok y := by
  rw [Array.mapM_eq_mapM_toList] at he
  cases hm : xs.toList.mapM f with
  | error e => rw [hm] at he; cases he
  | ok vs =>
    rw [hm] at he; cases he
    simpa only [Array.getElem?_toList] using
      listMapM_at hm (by simpa only [List.getElem?_toArray] using hy)

private theorem sameResolution {L M : Limits} {tc : TileCompGeom} {r : Nat}
    {a b : ResolutionGeom} (ha : resolution L tc r = .ok a) (hb : resolution M tc r = .ok b) :
    a = b := by
  unfold resolution at ha hb
  dsimp only at ha hb
  split at ha
  · cases ha
  next h =>
    rw [ite_eq_right h] at hb
    obtain ⟨_, _, ha⟩ := bind_ok ha
    obtain ⟨_, _, ha⟩ := bind_ok ha
    obtain ⟨_, _, hb⟩ := bind_ok hb
    obtain ⟨_, _, hb⟩ := bind_ok hb
    cases ha; cases hb; rfl

private theorem sameBand {L M : Limits} {res : ResolutionGeom} {p i : Nat}
    {a b : PrecinctGeom} {pa pb : PrecinctBandGeom}
    (ha : precinct L res p = .ok a) (hb : precinct M res p = .ok b)
    (hpa : a.bands[i]? = some pa) (hpb : b.bands[i]? = some pb) : pa = pb := by
  unfold precinct at ha hb
  dsimp only at ha hb
  split at ha
  · cases ha
  next h =>
    rw [ite_eq_right h] at hb
    obtain ⟨as, has, ha⟩ := bind_ok ha
    obtain ⟨bs, hbs, hb⟩ := bind_ok hb
    cases ha; cases hb
    obtain ⟨x, hx, hxa⟩ := arrayMapM_at has hpa
    obtain ⟨y, hy, hyb⟩ := arrayMapM_at hbs hpb
    obtain rfl := Option.some.inj (hx.symm.trans hy)
    obtain ⟨_, _, hxa⟩ := bind_ok hxa
    obtain ⟨_, _, hyb⟩ := bind_ok hyb
    cases hxa; cases hyb; rfl

private theorem initBlock_at {L : Limits} {params : Header.CompParams} {r bi k : Nat}
    {pg : PrecinctGeom} {st : PrecState} {bs : BandSt} {g : CodeBlockGeom}
    (hst : PrecState.init L params r pg = .ok st)
    (hbs : (PrecSt.ofFast st).bands[bi]? = some bs)
    (hg : bs.blocks[k]? = some ({ geom := g } : BlockSt)) :
    ∃ pb, pg.bands[bi]? = some pb ∧ bs.band = pb.band ∧ pb.codeBlocks[k]? = some g := by
  unfold PrecState.init at hst
  obtain ⟨bands, hmap, hst⟩ := bind_ok hst
  cases hst
  simp only [PrecSt.ofFast, List.getElem?_map, Array.getElem?_toList,
    Option.map_eq_some_iff] at hbs
  obtain ⟨fb, hfb, rfl⟩ := hbs
  obtain ⟨pb, hpb, h⟩ := arrayMapM_at hmap hfb
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  cases h
  refine ⟨pb, hpb, rfl, ?_⟩
  simp only [Array.toList_map, List.getElem?_map, Array.getElem?_toList,
    Option.map_eq_some_iff] at hg
  obtain ⟨_, ⟨a, ha, rfl⟩, hg⟩ := hg
  cases hg; exact ha

/-- At the encoder's band and block indices, the returned Tier-2 state decodes
to the coefficients from that exact Tier-1 call. Band labels and rectangles
are recovered from the two geometry traversals, including across distinct
admission limits. The 37-plane segment bound includes the full C10 domain. -/
theorem DecodedEncoderBands.reconstructBlock {L M : Limits} {tc : TileCompGeom}
    {source : Array (Array Encode.BandData)} {r p bi k : Nat}
    {res : ResolutionGeom} {pg : PrecinctGeom} {st : PrecState}
    {pb : PrecinctBandGeom} {cb : CodeBlockGeom} {o : EncOut} {bands b out}
    (hres : resolution M tc r = .ok res) (hpg : precinct M res p = .ok pg)
    (hst : PrecState.init M tc.params r pg = .ok st)
    (hd : DecodedEncoderBands (PrecSt.ofFast st) bands out)
    (hb : bands[bi]? = some b) (hx : b.blocks[k]? = some (packetBlockOf o))
    (hc : PacketBlockCall L tc source r p bi k pb cb o)
    (hstyle : tc.params.cbStyle.toNat = 0) (hroi : tc.params.roiShift = 0) :
    ∃ bo sb, out[bi]? = some bo ∧ bo.blocks[k]? = some sb ∧ bo.band = pb.band ∧
      sb.geom = cb ∧ sb.passes = o.numPasses ∧
      (numBits (maxMag (packetBlockCoeffs source r bi cb)) ≤ 37 →
        ReconstructsBlock tc.params r bo.band sb (packetBlockCoeffs source r bi cb)) := by
  obtain ⟨bs, bo, hbs, hbo, hout, _, block⟩ := hd.band bi b hb
  obtain ⟨g, hg, hsb⟩ := block k _ hx
  obtain ⟨pbd, hpbd, hband, hcb⟩ := initBlock_at hst hbs hg
  obtain ⟨re, pe, hre, hpe, hpb, hgeom⟩ := hc.geometry
  obtain rfl := sameResolution hres hre
  obtain rfl := sameBand hpg hpe hpbd hpb
  obtain rfl := Option.some.inj (hcb.symm.trans hgeom)
  let sb := blockAfter { geom := g } (packetBlockOf o)
  have hafter : bo.blocks[k]? = some sb := by simpa only [sb, blockAfter_fresh] using hsb
  have hlabel : bo.band = pbd.band := hout ▸ hband
  refine ⟨bo, sb, hbo, hafter, hlabel, ?_, ?_, ?_⟩
  · rw [show sb = _ from blockAfter_fresh g (packetBlockOf o)]
    split <;> rfl
  · rw [show sb = _ from blockAfter_fresh g (packetBlockOf o)]
    split <;> simp_all [packetBlockOf]
  · rw [hlabel]
    exact reconstruct_packetBlock hstyle hroi hc.encoded

/-- A physical block at its four nested indices in a decoded component. -/
def ComponentBlockAt (rs : Spec.Decode.SpecPrecs) (r j bi k : Nat) (b : Band)
    (sb : BlockSt) : Prop :=
  ∃ ps bs bo, rs[r]? = some ps ∧ ps[j]? = some bs ∧ bs[bi]? = some bo ∧
    bo.blocks[k]? = some sb ∧ bo.band = b

/-- Every physical block of a decoded component reconstructs its encoder subband slice,
including the all-zero slice for a skipped block. -/
def ReconstructsComponentBlocks (params : Header.CompParams)
    (source : Array (Array Encode.BandData)) (rs : Spec.Decode.SpecPrecs) : Prop :=
  ∀ ⦃r j bi k b sb⦄, ComponentBlockAt rs r j bi k b sb →
    ReconstructsBlock params r b sb (packetBlockCoeffs source r bi sb.geom)

/-- A 31-plane bound on the actual Tier-1 calls of one component. -/
def ComponentPlanes31 (tc : TileCompGeom) (source : Array (Array Encode.BandData)) : Prop :=
  ∀ r j bi k pb cb o, PacketBlockCall Limits.default tc source r j bi k pb cb o →
    numBits (maxMag (packetBlockCoeffs source r bi cb)) ≤ 31

section Component

variable {L : Limits} {p : Encode.Params} {img : Encode.Image} {e : Encode.Encoded}
  {prec infos tile} (hp : ReversibleTilePackets p img e prec infos)
  (ht : DecodedEncoderTile L (encLayout p img e.guardBits e.exponents) prec tile)
  {c : Nat} {rs : Spec.Decode.SpecPrecs} (hrs : tile.comps[c]? = some rs)

include hp ht hrs

private theorem packetBlock_reconstruction {r j bi k : Nat} {b sb}
    (ha : ComponentBlockAt rs r j bi k b sb) :
    let source := (Encode.bands53 p img (encMct p img)).getD c #[]
    ∃ pb o, PacketBlockCall Limits.default (encGeom p img e.guardBits e.exponents)
      source r j bi k pb sb.geom o ∧ pb.band = b ∧
      (numBits (maxMag (packetBlockCoeffs source r bi sb.geom)) ≤ 37 →
        ReconstructsBlock (encParams p e.guardBits e.exponents) r b sb
          (packetBlockCoeffs source r bi sb.geom)) := by
  obtain ⟨ps, out, bo, hps, hout, hbo, hsb, rfl⟩ := ha
  let g := encLayout p img e.guardBits e.exponents
  let q : Progression.PacketId := ⟨0, r, c, j⟩
  have hci : c < g.numComps := ht.count ▸ (List.getElem?_eq_some_iff.mp hrs).1
  obtain ⟨_, hrs', nrs, resAt⟩ := ht.component c hci
  obtain rfl := Option.some.inj (hrs'.symm.trans hrs)
  have hrlen := (List.getElem?_eq_some_iff.mp hps).1
  rw [nrs] at hrlen
  have hri : r ≤ g.levels c := Nat.le_of_lt_succ hrlen
  obtain ⟨res, _, hres, hps', nps, precAt⟩ := resAt r hri
  obtain rfl := Option.some.inj (hps'.symm.trans hps)
  have hj := (List.getElem?_eq_some_iff.mp hout).1
  obtain ⟨pg, st, _, hpg, hst, hout', hd⟩ := precAt j hj
  obtain rfl := Option.some.inj (hout'.symm.trans hout)
  have hq : g.InPacketSet q := ⟨Nat.zero_lt_succ 0, hci, hri, nps ▸ hj⟩
  have hbi : bi < (encBands prec q).size := hd.count ▸ (List.getElem?_eq_some_iff.mp hbo).1
  have hb := Array.getElem?_eq_getElem hbi
  obtain ⟨_, _, _, hbo', _, nbs, _⟩ := hd.band bi _ hb
  obtain rfl := Option.some.inj (hbo'.symm.trans hbo)
  have hki := nbs ▸ (List.getElem?_eq_some_iff.mp hsb).1
  have hx := Array.getElem?_eq_getElem hki
  obtain ⟨pb, cb, o, call, _, hx'⟩ := hp.packetBlock hq hb hx
  rw [hx'] at hx
  have hcomp := encLayout_comp p img e.guardBits e.exponents c
    ((encLayout_coding p img e.guardBits e.exponents).1 ▸ hci)
  rw [hcomp] at hres hst
  obtain ⟨_, _, hbo'', hsb', hband, hgeom, _, rec⟩ :=
    hd.reconstructBlock hres hpg hst hb hx call rfl rfl
  obtain rfl := Option.some.inj (hbo''.symm.trans hbo')
  obtain rfl := Option.some.inj (hsb'.symm.trans hsb)
  subst cb
  exact ⟨pb, o, call, hband.symm, rec⟩

/-- **C10 block reconstruction.** For a successful reversible encoding, the packet
call at each physical address supplies the 37-plane bound for its own coefficients. -/
theorem DecodedEncoderTile.reconstructsComponentBlocks (he : Encode.encodeDetailed p img = .ok e)
    (hrev : p.reversible = true) :
    ReconstructsComponentBlocks (encParams p e.guardBits e.exponents)
      ((Encode.bands53 p img (encMct p img)).getD c #[]) rs := by
  intro r j bi k b sb ha
  obtain ⟨_, _, call, _, rec⟩ := packetBlock_reconstruction hp ht hrs ha
  exact rec (call.planes_le_37 he hrev)

/-- A component-wise 31-plane bound also suffices to reconstruct every physical block. -/
theorem ComponentPlanes31.reconstructsComponentBlocks
    (hK : ComponentPlanes31 (encGeom p img e.guardBits e.exponents)
      ((Encode.bands53 p img (encMct p img)).getD c #[])) :
    ReconstructsComponentBlocks (encParams p e.guardBits e.exponents)
      ((Encode.bands53 p img (encMct p img)).getD c #[]) rs := by
  intro r j bi k b sb ha
  obtain ⟨pb, o, call, _, rec⟩ := packetBlock_reconstruction hp ht hrs ha
  exact rec (Nat.le_trans (hK r j bi k pb sb.geom o call) (by decide))

end Component

/-- The decoded block has the geometry of the encoder call at the same address,
including when its codeword has zero passes. -/
theorem DecodedEncoderTile.packetBlockAt {L : Limits} {p : Encode.Params} {img : Encode.Image}
    {e : Encode.Encoded} {prec infos tile} (hp : ReversibleTilePackets p img e prec infos)
    (ht : DecodedEncoderTile L (encLayout p img e.guardBits e.exponents) prec tile)
    {c r j bi k : Nat} {rs b sb} (hrs : tile.comps[c]? = some rs)
    (ha : ComponentBlockAt rs r j bi k b sb) :
    ∃ pb o, PacketBlockCall Limits.default (encGeom p img e.guardBits e.exponents)
      ((Encode.bands53 p img (encMct p img)).getD c #[]) r j bi k pb sb.geom o ∧ pb.band = b := by
  obtain ⟨pb, o, call, label, _⟩ := packetBlock_reconstruction hp ht hrs ha
  exact ⟨pb, o, call, label⟩

/-- Tile-block reconstruction specialized to a source slice of at most 31 coded planes. -/
theorem DecodedEncoderTile.reconstructBlock {L : Limits} {p : Encode.Params} {img : Encode.Image}
    {e : Encode.Encoded} {prec infos tile} (hp : ReversibleTilePackets p img e prec infos)
    (ht : DecodedEncoderTile L (encLayout p img e.guardBits e.exponents) prec tile)
    {c r j bi k : Nat} {rs ps out bo sb}
    (hrs : tile.comps[c]? = some rs) (hps : rs[r]? = some ps) (hout : ps[j]? = some out)
    (hbo : out[bi]? = some bo) (hsb : bo.blocks[k]? = some sb) :
    let src := packetBlockCoeffs ((Encode.bands53 p img (encMct p img)).getD c #[]) r bi sb.geom
    numBits (maxMag src) ≤ 31 →
      ReconstructsBlock (encParams p e.guardBits e.exponents) r bo.band sb src := by
  intro src hK
  obtain ⟨_, _, _, _, rec⟩ := packetBlock_reconstruction hp ht hrs
    (show ComponentBlockAt _ r j bi k bo.band sb from ⟨_, _, _, hps, hout, hbo, hsb, rfl⟩)
  exact rec (Nat.le_trans hK (by decide))

end JPEG2000.Spec.RoundTrip
