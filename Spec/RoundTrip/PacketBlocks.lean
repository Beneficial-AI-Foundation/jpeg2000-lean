import Spec.RoundTrip.BlockBounds
import Spec.RoundTrip.PrecinctShape

/-!
# Tier-1 provenance of packet blocks

Plan.md §§4, 5.3 and 7 (C10, M7). T.800 Annex D and B.7, B.10, B.12.1.1.
The component traversal writes the same Tier-1 result into the packet and the
encoder's block record. Its record order is component, resolution, precinct,
band, then raster block. LRCP changes the traversal order across components.
-/

namespace JPEG2000.Spec.RoundTrip

open JPEG2000.Encode (encodeComp BlockInfo BandData blockCoeffs orient)
open JPEG2000.Encode.Tier1 (EncOut encodeCodeBlock numBits maxMag)
open JPEG2000.Encode.Tier2 (BandIn BlockIn)
open JPEG2000.Tier2.Geometry
open JPEG2000.Tier2.Packet (bandMb)
open JPEG2000.Spec.Tier2Equiv (bind_ok)
open JPEG2000.Progression (PacketId Layout Volume)
open JPEG2000.Spec.Progression (packets precinctsOf)

private abbrev Bands := Array (Array BandData)
private abbrev CompPackets := Array (Array (Array BandIn))

/-- The exact source coefficients passed to Tier-1 for one geometric block. -/
def packetBlockCoeffs (bands : Array (Array BandData)) (r bi : Nat) (cb : CodeBlockGeom) :=
  blockCoeffs ((bands.getD r #[]).getD bi default) cb.rect

/-- A successful Tier-1 call at the given indices of the encoder geometry. -/
structure PacketBlockCall (L : Limits) (tc : TileCompGeom) (bands : Array (Array BandData))
    (r p bi k : Nat) (pb : PrecinctBandGeom) (cb : CodeBlockGeom) (o : EncOut) : Prop where
  /-- Both checked geometry lookups select this band and raster block. -/
  geometry : ∃ res pg, resolution L tc r = .ok res ∧ precinct L res p = .ok pg ∧
    pg.bands[bi]? = some pb ∧ pb.codeBlocks[k]? = some cb
  /-- The call uses the encoder's orientation, band bit depth and source rectangle. -/
  encoded : encodeCodeBlock cb.rect.width cb.rect.height (orient pb.band)
    (bandMb tc.params r pb.band) (packetBlockCoeffs bands r bi cb) = .ok o

/-- The packet entry written for a successful Tier-1 result, including an all-zero block. -/
def packetBlockOf (o : EncOut) : BlockIn :=
  { numPasses := o.numPasses, zeroBitPlanes := o.zeroBitPlanes, data := ⟨o.bytes.toArray⟩ }

private def recordsOf {α : Type} (f : Nat → α → List BlockInfo) (xs : Array α) :=
  (xs.toList.mapIdx f).flatten

private def blockRecord (c r p bi k : Nat) (b : BlockIn) : BlockInfo :=
  ⟨c, r, p, bi, k, b.numPasses, b.zeroBitPlanes, b.data⟩

/-- Recover every component record from the packet entries with its full encoder address. -/
def componentBlockRecords (c : Nat) (out : Array (Array (Array BandIn))) : List BlockInfo :=
  recordsOf (fun r => recordsOf (fun p => recordsOf (fun bi b =>
    recordsOf (fun k x => [blockRecord c r p bi k x]) b.blocks))) out

private def AllAt {α : Type} (xs : Array α) (P : Nat → α → Prop) :=
  ∀ i x, xs[i]? = some x → P i x

private structure Writes {α : Type} (P : Nat → α → Prop) (f : Nat → α → List BlockInfo)
    (start : Array BlockInfo) (n : Nat) (xs : Array α) (out : Array BlockInfo) : Prop where
  size : xs.size = n
  atIndex : AllAt xs P
  records : out.toList = start.toList ++ recordsOf f xs

private theorem rangeAux {σ : Type} (P : Nat → σ → Prop) {f : Nat → σ → Except Error (ForInStep σ)}
    (s n : Nat) (st out : σ) (h0 : P s st)
    (step : ∀ i < s+n, ∀ b t, P i b → f i b = .ok t → ∃ u, t = .yield u ∧ P (i+1) u)
    (h : forIn (List.range' s n) st f = .ok out) : P (s+n) out := by
  induction n generalizing s st with
  | zero => simp only [List.range'_zero, List.forIn_nil] at h; cases h; exact h0
  | succ n ih =>
    rw [List.range'_succ, List.forIn_cons] at h
    obtain ⟨t, ht, h⟩ := bind_ok h
    obtain ⟨u, rfl, hu⟩ := step s (by omega) st t h0 ht
    exact (show s+1+n = s+(n+1) by omega) ▸
      ih (s+1) u hu (fun i hi => step i (by omega)) h

private theorem collect {α σ : Type} (P : Nat → α → Prop) (recs : Nat → α → List BlockInfo)
    (xs : σ → Array α) (infos : σ → Array BlockInfo) {n : Nat} {st out : σ}
    {f : Nat → σ → Except Error (ForInStep σ)} (h0 : xs st = #[])
    (h : forIn [0:n] st f = .ok out)
    (step : ∀ i < n, ∀ b t, f i b = .ok t → ∃ u x, t = .yield u ∧
      xs u = (xs b).push x ∧ P i x ∧ (infos u).toList = (infos b).toList ++ recs i x) :
    Writes P recs (infos st) n (xs out) (infos out) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at h
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_one_sub_one, Nat.div_one] at h
  let Inv i s := Writes P recs (infos st) i (xs s) (infos s)
  suffices Inv (0 + n) out by simpa [Inv] using this
  apply rangeAux Inv 0 n st out _ _ h
  · exact ⟨by simp [h0], by simp [AllAt, h0], by simp [h0, recordsOf]⟩
  · intro i hi s t hs ht
    obtain ⟨u, x, rfl, hu, hx, hinfo⟩ := step i (by simpa using hi) s t ht
    refine ⟨u, rfl, ⟨by simp [hu, hs.size], ?_, ?_⟩⟩
    · intro k y hy
      rw [hu, Array.getElem?_push, hs.size] at hy
      split at hy
      · rename_i he; subst k; cases hy; exact hx
      · exact hs.atIndex k y hy
    · rw [hinfo, hs.records, hu]
      simp [recordsOf, hs.size, List.append_assoc]

private theorem rasterIndex {L : Limits} {res : ResolutionGeom} {p : Nat} {pg : PrecinctGeom}
    (h : precinct L res p = .ok pg) :
    ∀ pb ∈ pg.bands, ∀ k (hk : k < pb.codeBlocks.size), pb.codeBlocks[k].index = k := by
  unfold precinct at h
  dsimp only at h
  split at h
  · cases h
  obtain ⟨bs, hbs, h⟩ := bind_ok h
  cases h
  refine Spec.Tier2WF.arrayMapM_mem (fun pb : PrecinctBandGeom =>
    ∀ k (hk : k < pb.codeBlocks.size), pb.codeBlocks[k].index = k) _ _ ?_ _ hbs
  intro b _ pb hb
  obtain ⟨_, _, hb⟩ := bind_ok hb
  cases hb
  intro k hk
  simp [codeBlocksOf]

private def TracedBand (L : Limits) (tc : TileCompGeom) (bands : Bands)
    (r p bi : Nat) (b : BandIn) :=
  AllAt b.blocks fun k x => ∃ pb cb o, PacketBlockCall L tc bands r p bi k pb cb o ∧
    b.maxZero = bandMb tc.params r pb.band + tc.params.roiShift ∧ x = packetBlockOf o

private theorem componentTrace {L : Limits} {tc : TileCompGeom} {c : Nat} {bands : Bands}
    {out : CompPackets} {infos : Array BlockInfo} (h : encodeComp L tc c bands = .ok (out, infos)) :
    AllAt out (fun r ps => AllAt ps (fun p bs => AllAt bs (TracedBand L tc bands r p))) ∧
      infos.toList = componentBlockRecords c out := by
  unfold encodeComp at h
  dsimp only at h
  obtain ⟨s, hs, h⟩ := bind_ok h
  cases h
  let blockRecs r p bi k x := [blockRecord c r p bi k x]
  let bandRecs r p bi (b : BandIn) := recordsOf (blockRecs r p bi) b.blocks
  let precRecs r p := recordsOf (bandRecs r p)
  let resRecs r := recordsOf (precRecs r)
  have outer := collect (fun r ps => AllAt ps (fun p bs => AllAt bs (TracedBand L tc bands r p)))
    resRecs Prod.fst Prod.snd rfl hs ?_
  · exact ⟨outer.atIndex, outer.records⟩
  intro r _ st t ht
  obtain ⟨res, hr, ht⟩ := bind_ok ht
  obtain ⟨ps, hps, ht⟩ := bind_ok ht
  cases ht
  have rp := collect (fun p bs => AllAt bs (TracedBand L tc bands r p)) (precRecs r)
    Prod.snd Prod.fst rfl hps ?_
  · exact ⟨_, _, rfl, rfl, rp.atIndex, rp.records⟩
  intro p _ st t ht
  obtain ⟨pg, hp, ht⟩ := bind_ok ht
  obtain ⟨bs, hbs, ht⟩ := bind_ok ht
  cases ht
  have bp := collect (TracedBand L tc bands r p) (bandRecs r p) Prod.snd Prod.fst rfl hbs ?_
  · exact ⟨_, _, rfl, rfl, bp.atIndex, bp.records⟩
  intro bi _ st t ht
  split at ht
  next pb hpb =>
    obtain ⟨blocks, hblocks, ht⟩ := bind_ok ht
    cases ht
    rw [← Array.forIn_toList, ← range_map_array_getD pb.codeBlocks, List.forIn_map] at hblocks
    have hfor (s : Array BlockInfo × Array BlockIn) (f : Nat → _ → Except Error (ForInStep _)) :
        forIn (List.range pb.codeBlocks.size) s f = forIn [0:pb.codeBlocks.size] s f := by
      rw [Std.Legacy.Range.forIn_eq_forIn_range', List.range_eq_range']
      simp [Std.Legacy.Range.size]
    rw [hfor] at hblocks
    let P k x := ∃ cb o, PacketBlockCall L tc bands r p bi k pb cb o ∧ x = packetBlockOf o
    have bk := collect P (blockRecs r p bi) Prod.snd Prod.fst rfl hblocks ?_
    · refine ⟨_, _, rfl, rfl, ?_, bk.records⟩
      intro k x hx
      obtain ⟨cb, o, hc, he⟩ := bk.atIndex k x hx
      exact ⟨pb, cb, o, hc, rfl, he⟩
    intro k hk st t ht
    obtain ⟨o, ho, ht⟩ := bind_ok ht
    split at ht
    · cases ht
    · cases ht
      have hcb : pb.codeBlocks[k]? = some (pb.codeBlocks.getD k default) := by
        simp [Array.getD, hk]
      have hidx := rasterIndex hp pb (Array.mem_iff_getElem?.2 ⟨bi, hpb⟩) k hk
      refine ⟨_, _, rfl, rfl, ⟨_, o, ⟨⟨res, pg, hr, hp, hpb, hcb⟩, ho⟩, rfl⟩, ?_⟩
      rw [Array.toList_push]
      exact congrArg (fun j => st.1.toList ++ [blockRecord c r p bi j (packetBlockOf o)]) hidx
  next => cases ht

/-- Each entry of a successful component has a Tier-1 witness at the same four indices. -/
theorem encodeComp_packetBlock {L : Limits} {tc : TileCompGeom} {c : Nat} {bands : Bands}
    {out : CompPackets} {infos : Array BlockInfo} (h : encodeComp L tc c bands = .ok (out, infos))
    {r p bi k : Nat} {ps bs b x}
    (hr : out[r]? = some ps) (hp : ps[p]? = some bs)
    (hb : bs[bi]? = some b) (hx : b.blocks[k]? = some x) :
    ∃ pb cb o, PacketBlockCall L tc bands r p bi k pb cb o ∧
      b.maxZero = bandMb tc.params r pb.band + tc.params.roiShift ∧ x = packetBlockOf o :=
  (componentTrace h).1 r ps hr p bs hp bi b hb k x hx

/-- The successful component's record array is exactly the packet traversal with addresses. -/
theorem encodeComp_blockRecords {L : Limits} {tc : TileCompGeom} {c : Nat} {bands : Bands}
    {out : CompPackets} {infos : Array BlockInfo} (h : encodeComp L tc c bands = .ok (out, infos)) :
    infos.toList = componentBlockRecords c out :=
  (componentTrace h).2

/-- Bounds on the transformed coefficients and the MQ codewords of the actual source blocks. -/
def ComponentBlockBounds (L : Limits) (tc : TileCompGeom) (bands : Array (Array BandData)) : Prop :=
  ∀ r p bi k pb cb o, PacketBlockCall L tc bands r p bi k pb cb o →
    numBits (maxMag (packetBlockCoeffs bands r bi cb)) ≤ 37 ∧
      (o.numPasses ≠ 0 → o.bytes.length < 2 ^ 32)

private theorem call_blockOK {L M : Limits} {tc : TileCompGeom} {bands : Bands}
    {r p bi k pb cb o} (hc : PacketBlockCall L tc bands r p bi k pb cb o)
    (hs : ComponentBlockBounds L tc bands) (hlim : 109 ≤ M.maxPassesPerCodeBlock) :
    BlockOK M (bandMb tc.params r pb.band + tc.params.roiShift) (packetBlockOf o) := by
  obtain ⟨hmag, hlen⟩ := hs r p bi k pb cb o hc
  exact blockOK_encodeCodeBlock hc.encoded hmag hlim hlen

/-- Each successful component packet entry meets the decoder bounds when its source blocks
meet the magnitude and included-codeword bounds. -/
theorem encodeComp_blockOK {L M : Limits} {tc : TileCompGeom} {c : Nat} {bands : Bands}
    {out : CompPackets} {infos : Array BlockInfo} (h : encodeComp L tc c bands = .ok (out, infos))
    (hs : ComponentBlockBounds L tc bands) (hlim : 109 ≤ M.maxPassesPerCodeBlock)
    {r p bi k : Nat} {ps bs b x}
    (hr : out[r]? = some ps) (hp : ps[p]? = some bs)
    (hb : bs[bi]? = some b) (hx : b.blocks[k]? = some x) : BlockOK M b.maxZero x := by
  obtain ⟨pb, cb, o, call, hz, rfl⟩ := encodeComp_packetBlock h hr hp hb hx
  exact hz ▸ call_blockOK call hs hlim

private theorem lookup_getD {α : Type} {a : Array α} {i : Nat} (hi : i < a.size) (d : α) :
    a[i]? = some (a.getD i d) := by simp [Array.getD, hi]

/-- A tile packet entry determines a Tier-1 call on its component's 5/3 coefficients. -/
theorem ReversibleTilePackets.packetBlock {p : Encode.Params} {img : Encode.Image}
    {e : Encode.Encoded} {prec infos} (he : ReversibleTilePackets p img e prec infos)
    {q : PacketId} (hq : (encLayout p img e.guardBits e.exponents).InPacketSet q)
    {bi k b x} (hb : (encBands prec q)[bi]? = some b) (hx : b.blocks[k]? = some x) :
    let tc := encGeom p img e.guardBits e.exponents
    ∃ pb cb o, PacketBlockCall Limits.default tc ((Encode.bands53 p img (encMct p img)).getD q.comp #[])
        q.res q.prec bi k pb cb o ∧
      b.maxZero = bandMb tc.params q.res pb.band + tc.params.roiShift ∧ x = packetBlockOf o := by
  obtain ⟨_, hc, hr, hk⟩ := hq
  obtain ⟨hrs, hps⟩ := he.tileShape.2 q.comp hc
  rw [(encLayout_coding p img e.guardBits e.exponents).1] at hc
  have hcomp := he.component q.comp hc
  rw [tileComp_enc _ _ _ _ _ hc] at hcomp
  exact encodeComp_packetBlock hcomp (lookup_getD (hrs ▸ Nat.lt_succ_of_le hr) #[])
    (lookup_getD (hps _ hr ▸ hk) #[]) hb hx

/-- Every packet of the reversible tile has the per-entry bounds needed by `precReady`.
The hypotheses concern the component's Tier-1 sources and codewords. -/
theorem ReversibleTilePackets.blockOK {p : Encode.Params} {img : Encode.Image} {e : Encode.Encoded}
    {prec infos} (he : ReversibleTilePackets p img e prec infos) {M : Limits}
    (hlim : 109 ≤ M.maxPassesPerCodeBlock)
    (hsrc : ∀ c < img.comps.size, ComponentBlockBounds Limits.default
      (encGeom p img e.guardBits e.exponents) ((Encode.bands53 p img (encMct p img)).getD c #[]))
    {q : PacketId} (hq : (encLayout p img e.guardBits e.exponents).InPacketSet q) :
    ∀ b ∈ encBands prec q, ∀ k < b.blocks.size, BlockOK M b.maxZero (b.blocks.getD k default) := by
  intro b hb k hk
  obtain ⟨bi, hbi⟩ := Array.mem_iff_getElem?.1 hb
  obtain ⟨pb, cb, o, call, hz, hx⟩ := he.packetBlock hq hbi (lookup_getD hk default)
  rw [hz, hx]
  exact call_blockOK call (hsrc _ ((encLayout_coding p img e.guardBits e.exponents).1 ▸ hq.2.1)) hlim

/-- Each real component record array in a successful tile is recovered from that component's
packet input, including the addresses and codewords. -/
theorem ReversibleTilePackets.componentRecords {p : Encode.Params} {img : Encode.Image}
    {e : Encode.Encoded} {prec infos} (he : ReversibleTilePackets p img e prec infos)
    {c : Nat} (hc : c < img.comps.size) :
    (infos.getD c #[]).toList = componentBlockRecords c (prec.getD c #[]) :=
  encodeComp_blockRecords (he.component c hc)

private theorem recordsOf_passes {α : Type} (xs : Array α) (recs : Nat → α → List BlockInfo)
    (g : α → Nat) (hg : ∀ i x, ((recs i x).map BlockInfo.numPasses).sum = g x) :
    ((recordsOf recs xs).map BlockInfo.numPasses).sum = (xs.toList.map g).sum := by
  unfold recordsOf
  generalize xs.toList = l
  induction l generalizing recs with
  | nil => rfl
  | cons x l ih =>
    simp only [List.mapIdx_cons, List.flatten_cons, List.map_append, List.sum_append,
      hg, List.map_cons, List.sum_cons]
    rw [ih (fun i => recs (i+1)) (fun i => hg (i+1))]

/-- Summing the passes of a real encoder component's records gives the sum of its precinct
pass counts, including zero passes at every omitted block. -/
theorem encodeComp_passes {L : Limits} {tc : TileCompGeom} {c : Nat} {bands : Bands}
    {out : CompPackets} {infos : Array BlockInfo} (h : encodeComp L tc c bands = .ok (out, infos)) :
    (infos.toList.map BlockInfo.numPasses).sum =
      (out.toList.map fun ps => (ps.toList.map passesOf).sum).sum := by
  rw [encodeComp_blockRecords h]
  unfold componentBlockRecords
  apply recordsOf_passes
  intro r ps
  apply recordsOf_passes
  intro p bs
  unfold passesOf
  apply recordsOf_passes
  intro bi b
  apply recordsOf_passes
  intro k x
  simp [blockRecord]

private theorem sum_flatMap {α β : Type} (xs : List α) (f : α → List β) (g : β → Nat) :
    ((xs.flatMap f).map g).sum = (xs.map fun x => ((f x).map g).sum).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

private theorem sum_swap {α β : Type} (xs : List α) (ys : List β) (f : α → β → Nat) :
    (xs.map fun x => (ys.map (f x)).sum).sum =
      (ys.map fun y => (xs.map fun x => f x y).sum).sum := by
  have add (g h : β → Nat) : (ys.map (fun y => g y + h y)).sum =
      (ys.map g).sum + (ys.map h).sum := by
    induction ys with
    | nil => rfl
    | cons y ys ih => simp only [List.map_cons, List.sum_cons, ih]; omega
  induction xs with
  | nil => simp [List.map_const', List.sum_replicate_nat]
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, add, ih]

/-- The LRCP pass charge of the spec decoder is exactly the pass sum of the encoder's
flattened block records. This includes the case of components with empty precinct grids. -/
theorem ReversibleTilePackets.packetPasses {p : Encode.Params} {img : Encode.Image}
    {e : Encode.Encoded} {prec infos} (he : ReversibleTilePackets p img e prec infos) :
    ((packets (encLayout p img e.guardBits e.exponents) .lrcp #[]).map
        (fun q => passesOf (encBands prec q))).sum = (e.blocks.toList.map BlockInfo.numPasses).sum := by
  let g := encLayout p img e.guardBits e.exponents
  let F c r := (((prec.getD c #[]).getD r #[]).toList.map passesOf).sum
  have hn : g.numComps = img.comps.size := (encLayout_coding _ _ _ _).1
  have level (c : Nat) (hc : c < g.numComps) : g.levels c = p.levels := by
    unfold Layout.levels
    rw [show g.comp c = _ from encLayout_comp _ _ _ _ c (hn ▸ hc)]
    rfl
  have packet (r c : Nat) (hc : c < g.numComps) :
      ((precinctsOf g 0 r c).map fun q => passesOf (encBands prec q)).sum = F c r := by
    obtain ⟨hrs, hps⟩ := he.tileShape.2 c hc
    unfold precinctsOf
    split
    · rename_i hr
      unfold F
      rw [← hps r hr, ← range_map_array_getD ((prec.getD c #[]).getD r #[])]
      simp only [List.map_map]
      rfl
    · rename_i hr
      have hge : (prec.getD c #[]).size ≤ r := hrs ▸ Nat.lt_of_not_ge hr
      have hout : (prec.getD c #[]).getD r #[] = #[] := by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hge, Option.getD_none]
      unfold F
      rw [hout]
      rfl
  have component (c : Nat) (hc : c < g.numComps) :
      ((infos.getD c #[]).toList.map BlockInfo.numPasses).sum =
        ((List.range (g.maxLevels + 1)).map (F c)).sum := by
    have hci := hn ▸ hc
    have hsize := (he.tileShape.2 c hc).1
    have hs : (prec.getD c #[]).size = g.maxLevels + 1 :=
      hsize.trans (by rw [level c hc, show g.maxLevels = p.levels from
        encLayout_maxLevels _ _ _ _ (by omega)])
    rw [encodeComp_passes (he.component c hci), ← hs, ← range_map_array_getD (prec.getD c #[])]
    rw [List.map_map]
    rfl
  change ((packets g .lrcp #[]).map _).sum = _
  rw [Spec.Progression.packets_noPoc (show g.WF from encLayout_wf _ _ _ _)]
  simp only [Spec.Progression.order, Spec.Progression.volume, Spec.Progression.lrcp,
    Spec.Progression.layerRange, Spec.Progression.resRange, Spec.Progression.compRange,
    Volume.full, Volume.le, Volume.re, Volume.ce, show g.layers = 1 from rfl,
    Nat.min_self, Nat.sub_zero, List.range_one, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, ← List.range_eq_range', sum_flatMap]
  have inner (r : Nat) :
      ((List.range g.numComps).map (fun c =>
        ((precinctsOf g 0 r c).map fun q => passesOf (encBands prec q)).sum)).sum =
      ((List.range g.numComps).map (fun c => F c r)).sum :=
    congrArg List.sum (List.map_congr_left (fun c hc => packet r c (List.mem_range.1 hc)))
  simp only [inner]
  rw [sum_swap, he.blocks, Array.toList_flatten]
  change _ = ((infos.toList.flatMap Array.toList).map BlockInfo.numPasses).sum
  rw [sum_flatMap, ← range_map_array_getD infos, List.map_map, he.infos_size, ← hn]
  exact congrArg List.sum (List.map_congr_left (fun c hc => (component c (List.mem_range.1 hc)).symm))

end JPEG2000.Spec.RoundTrip
