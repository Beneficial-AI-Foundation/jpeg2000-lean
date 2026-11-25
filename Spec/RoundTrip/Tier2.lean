import Spec.RoundTrip.Tier2Bits

/-!
# C10, layer 2b: packets and tiles — the reference Tier-2 writer against the spec reader

Plan.md §4 (C10, headline theorem `decode (encode img) = img` for the lossless encoder),
§5.3 (reference encoder). Task 7.3b. T.800 B.9 (packets), B.10.1–B.10.8 (packet header and
body), B.12.1.1 (LRCP), B.10.2 via C4 (tag trees).

The encoder side is `Encode.Tier2` (one layer, plain code-block style, one codeword segment
per code-block, no `SOP`/`EPH`, headers in the tile data); the reader is `Spec.Tier2`.

* **Code-block** (`blockHeader_enc`): inclusion (`query_enc`, threshold 1) and zero
  bit-planes (`exact_enc`) are C4 (`Spec.TagTree.decode_encode`); then Table B.4
  (`numPasses_passBits`), the `Lblock` comma code (`commaCode_replicate`) and one length
  field (`field_natBits`; `segmentPasses_plain` gives one piece for `≤ 109` passes).
  Side conditions (`BlockOK`, only for blocks with passes): `zbp ≤ maxZero`,
  `numPasses ≤ min 109 maxPassesPerCodeBlock`, codeword `< 2^32` bytes (the length field is
  then `≤ 32` bits wide, `width_le`).
* **Band / packet header** (`blocksHeader_enc`, `band_enc`, `bands_enc`): the C4 invariant
  `Spec.TagTree.Inv` is carried per band (`blockBits_inv`, via `encodeAll_spec`).
* **Body** (`bandBody_enc`, `bandsBody_enc`): each included block gets its codeword as a
  new segment.
* **One packet** (`packet_enc`, `packet_roundtrip`): `Spec.Tier2.packet … (encodePacket
  bands ++ T)` returns each included block with `segs = [⟨data, numPasses⟩]`,
  `zbp = zeroBitPlanes`, `passes = numPasses` (`blockAfter_fresh`), the other blocks fresh,
  and `T` unconsumed; the finished-header lemma is 7.3a's `finish_spec`.
* **One tile** (`tile_enc`): `Spec.Tier2.step` folded over `Spec.Progression.packets g .lrcp
  #[]` (one layer, `Layout.WF`) on `encodeTileLRCP prec ++ T` — the encoder's loops produce
  the packets in exactly the spec's LRCP order (`encodeTileLRCP_eq`), and every precinct of
  the packet set comes back as `outAfter` of the encoder's bands (`fold_enc`).

Not here: instantiating `tile_enc` at `Spec.Tier2.decodeTile` on the encoder's codestream —
that needs the header round trip (`Layout.ofHeader` of the parsed main header) and the link
between `initPrecincts` and `Encode.encodeComp`'s bands (same `resolution`/`precinct`
geometry, `PrecSt.ofFast` fresh states satisfying `PrecReady`, the side conditions from the
Tier-1 encoder).
-/

namespace JPEG2000.Spec.RoundTrip

open JPEG2000 JPEG2000.Spec.Tier2
open JPEG2000.Spec.TagTree (St Query encodeAll Inv inv_init decode_encode decodeAll trueAnswer)
open JPEG2000.Tier2.Packet (Contribution)
open JPEG2000.Encode.Tier2 (BlockIn BandIn blockBits bandBits lblockInc bitLen natBits passBits
  encodePacket packetHeader packetBody nonEmpty encodeTileLRCP BitWriter)

/-- C4 for one inclusion query. -/
theorem query_enc {w h : Nat} {v : Nat → Nat → Nat} {s : St} {x y t : Nat} (rest : List Bool)
    (hx : x < w) (hy : y < h) (hs : Inv w h v s) :
    Spec.TagTree.query w h s x y t ((encodeAll w h v [.lt x y t] s).1 ++ rest) =
      some (decide (v x y < t), (encodeAll w h v [.lt x y t] s).2.2, rest) := by
  have := decode_encode w h v [.lt x y t] s rest (by simp [Query.Valid, hx, hy]) hs
  revert this
  simp only [decodeAll]
  cases Spec.TagTree.query w h s x y t ((encodeAll w h v [.lt x y t] s).1 ++ rest) with
  | none => simp
  | some r =>
    obtain ⟨b, s', bs⟩ := r
    simp [trueAnswer]

/-- C4 for one exact-value query. -/
theorem exact_enc {w h : Nat} {v : Nat → Nat → Nat} {s : St} {x y m : Nat} (rest : List Bool)
    (hx : x < w) (hy : y < h) (hm : v x y ≤ m) (hs : Inv w h v s) :
    Spec.TagTree.exact w h s x y m ((encodeAll w h v [.exact x y m] s).1 ++ rest) =
      some (v x y, (encodeAll w h v [.exact x y m] s).2.2, rest) := by
  have := decode_encode w h v [.exact x y m] s rest (by simp [Query.Valid, hx, hy, hm]) hs
  revert this
  simp only [decodeAll]
  cases Spec.TagTree.exact w h s x y m ((encodeAll w h v [.exact x y m] s).1 ++ rest) with
  | none => simp
  | some r =>
    obtain ⟨b, s', bs⟩ := r
    simp [trueAnswer]

/-- The length field of a block fits its `Lblock + ⌊log₂ n⌋` bits. -/
theorem lt_width (n len : Nat) : len < 2 ^ (3 + lblockInc n len + Nat.log2 n) := by
  have h1 : len < 2 ^ bitLen len := by
    unfold bitLen; split
    · subst_vars; decide
    · exact Nat.lt_log2_self
  have h2 : bitLen len ≤ 3 + lblockInc n len + Nat.log2 n := by unfold lblockInc; omega
  exact Nat.lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by decide) h2)

/-- The length field is at most 32 bits wide when the codeword has fewer than `2^32` bytes
and the block at most 109 passes. -/
theorem width_le {n len : Nat} (hn : n ≤ 109) (hl : len < 2 ^ 32) :
    3 + lblockInc n len + Nat.log2 n ≤ 32 := by
  have h1 : Nat.log2 n ≤ 6 := by
    by_cases h0 : n = 0
    · subst h0; simp [Nat.log2_zero]
    · have := (Nat.log2_lt h0 (k := 7)).2 (Nat.lt_of_le_of_lt hn (by decide)); omega
  have h2 : bitLen len ≤ 32 := by
    unfold bitLen; split
    · omega
    · have := (Nat.log2_lt (by assumption) (k := 32)).2 hl; omega
  unfold lblockInc; omega

/-- Side conditions on one code-block (vacuous for a block without coding passes): the zero
bit-planes within the decoder's bound `maxZero`, at most `min 109 maxPassesPerCodeBlock`
passes, and a codeword shorter than `2^32` bytes (equivalently: a length field of at most 32
bits, `width_le`). -/
def BlockOK (L : Limits) (maxZero : Nat) (blk : BlockIn) : Prop :=
  blk.numPasses ≠ 0 → blk.zeroBitPlanes ≤ maxZero ∧ blk.numPasses ≤ 109 ∧
    blk.numPasses ≤ L.maxPassesPerCodeBlock ∧ blk.data.size < 2 ^ 32

/-- The decoder state of a code-block after the header of its first packet, when that packet
carries the code-block `blk` written by the encoder. -/
def hdrAfter (cb : BlockSt) (blk : BlockIn) : BlockSt :=
  if blk.numPasses = 0 then cb else
  { cb with included := true, zbp := blk.zeroBitPlanes,
            lblock := 3 + lblockInc blk.numPasses blk.data.size, passes := blk.numPasses }

/-- The contribution the decoder records for code-block `k` of precinct-band `bi`. -/
def contribOf (bi : Nat) (b : BandIn) (k : Nat) : Option Contribution :=
  let blk := b.blocks.getD k default
  if blk.numPasses = 0 then none
  else some { band := bi, block := k, pieces := [(blk.numPasses, blk.data.size)], cont := false }

/-- `blockBits` with its tuple patterns as projections. -/
theorem blockBits_eq (b : BandIn) (k : Nat) (i z : St) :
    blockBits b k i z =
      if (b.blocks.getD k default).numPasses = 0 then
        ((encodeAll b.cw b.ch b.inclLeaf [Query.lt (k % b.cw) (k / b.cw) 1] i).1,
         (encodeAll b.cw b.ch b.inclLeaf [Query.lt (k % b.cw) (k / b.cw) 1] i).2.2, z)
      else
        ((encodeAll b.cw b.ch b.inclLeaf [Query.lt (k % b.cw) (k / b.cw) 1] i).1 ++
          (encodeAll b.cw b.ch b.zbpLeaf [Query.exact (k % b.cw) (k / b.cw) b.maxZero] z).1 ++
          passBits (b.blocks.getD k default).numPasses ++
          List.replicate (lblockInc (b.blocks.getD k default).numPasses
            (b.blocks.getD k default).data.size) true ++ [false] ++
          natBits (b.blocks.getD k default).data.size
            (3 + lblockInc (b.blocks.getD k default).numPasses (b.blocks.getD k default).data.size
              + Nat.log2 (b.blocks.getD k default).numPasses),
         (encodeAll b.cw b.ch b.inclLeaf [Query.lt (k % b.cw) (k / b.cw) 1] i).2.2,
         (encodeAll b.cw b.ch b.zbpLeaf [Query.exact (k % b.cw) (k / b.cw) b.maxZero] z).2.2) := by
  unfold blockBits
  dsimp only

/-- **One code-block of a packet header** (B.10.4–B.10.7, layer 0, style 0, never included
before): the spec's `blockHeader` reads the encoder's `blockBits` back — inclusion and zero
bit-planes by C4, then Table B.4, the comma code and the single length field — leaving exactly
the following bits, with the encoder's tag-tree states. -/
theorem blockHeader_enc (L : Limits) (bi k : Nat) (b : BandIn) (bs : BandSt)
    (g : JPEG2000.Tier2.Geometry.CodeBlockGeom)
    (rest : List Bool) (hk : k < b.cw * b.ch) (hw : bs.w = b.cw) (hh : bs.h = b.ch)
    (hm : bs.maxZero = b.maxZero) (hcb : bs.blocks[k]? = some { geom := g })
    (hI : Inv b.cw b.ch b.inclLeaf bs.incl) (hZ : Inv b.cw b.ch b.zbpLeaf bs.zbp)
    (hok : BlockOK L b.maxZero (b.blocks.getD k default)) :
    blockHeader L 0 0 bi k bs ((blockBits b k bs.incl bs.zbp).1 ++ rest) =
      .ok ({ bs with incl := (blockBits b k bs.incl bs.zbp).2.1,
                     zbp := (blockBits b k bs.incl bs.zbp).2.2,
                     blocks := bs.blocks.set k (hdrAfter { geom := g } (b.blocks.getD k default)) },
           contribOf bi b k, rest) := by
  obtain ⟨band, rect, w, h, mz, incl, zbp, blocks⟩ := bs
  dsimp only at hw hh hm hcb hI hZ ⊢
  subst hw hh hm
  have hcw : 0 < b.cw := Nat.pos_of_ne_zero (by rintro h0; simp [h0] at hk)
  have hx : k % b.cw < b.cw := Nat.mod_lt _ hcw
  have hy : k / b.cw < b.ch := (Nat.div_lt_iff_lt_mul hcw).2 (by rw [Nat.mul_comm]; exact hk)
  have hkk : k / b.cw * b.cw + k % b.cw = k := Nat.div_add_mod' k b.cw
  have hleafI : b.inclLeaf (k % b.cw) (k / b.cw) =
      if (b.blocks.getD k default).numPasses > 0 then 0 else 1 := by
    simp only [BandIn.inclLeaf, hkk]
  have hleafZ : b.zbpLeaf (k % b.cw) (k / b.cw) = (b.blocks.getD k default).zeroBitPlanes := by
    simp only [BandIn.zbpLeaf, hkk]
  rw [blockBits_eq]
  unfold hdrAfter contribOf
  generalize b.blocks.getD k default = blk at hok hleafI hleafZ ⊢
  have hset : blocks.set k { geom := g } = blocks := by
    obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.1 hcb
    rw [← heq]; exact List.set_getElem_self hlt
  by_cases h0 : blk.numPasses = 0
  · simp only [h0, ↓reduceIte]
    unfold blockHeader
    simp only [hcb, bind, Except.bind, pure, Except.pure, Nat.zero_add, query_enc _ hx hy hI, hleafI,
      Bool.false_eq_true, ↓reduceIte, h0, Nat.lt_irrefl, hset, decide_false, Bool.not_false]
  · obtain ⟨hz, h109, hmax, hsz⟩ := hok h0
    have hw32 := width_le h109 hsz
    have hpos : blk.numPasses > 0 := by omega
    have hseg : Tier1.segmentPasses (Tier1.Mode.ofStyle 0) blk.numPasses 0 = [blk.numPasses] := by
      rw [Tier1.segmentPasses_plain _ (by decide) (by decide) _ _ (by omega)]; simp [h0]
    simp only [h0, ↓reduceIte, List.append_assoc]
    unfold blockHeader
    simp only [hcb, bind, Except.bind, pure, Except.pure, Nat.zero_add, query_enc _ hx hy hI, hleafI,
      Bool.false_eq_true, ↓reduceIte, Nat.lt_irrefl, Nat.zero_lt_one, decide_true, Bool.not_true, decide_false, Bool.false_and,
      exact_enc _ hx hy (by rw [hleafZ]; exact hz) hZ, hleafZ,
      numPasses_passBits blk.numPasses _ (by omega) (by omega), hpos, List.singleton_append,
      commaCode_replicate _ (lblockInc blk.numPasses blk.data.size) 33 0 (by omega), Limits.check, Limits.checkLe, Limits.bound, hmax, hseg,
      lengths, field_natBits _ _ _ hw32 (lt_width _ _)]

/-- The tag-tree invariants (C4) survive one code-block of the encoder. -/
theorem blockBits_inv {L : Limits} {b : BandIn} {k : Nat} {i z : St} (hk : k < b.cw * b.ch)
    (hI : Inv b.cw b.ch b.inclLeaf i) (hZ : Inv b.cw b.ch b.zbpLeaf z)
    (hok : BlockOK L b.maxZero (b.blocks.getD k default)) :
    Inv b.cw b.ch b.inclLeaf (blockBits b k i z).2.1 ∧ Inv b.cw b.ch b.zbpLeaf (blockBits b k i z).2.2 := by
  have hcw : 0 < b.cw := Nat.pos_of_ne_zero (by rintro h0; simp [h0] at hk)
  have hx : k % b.cw < b.cw := Nat.mod_lt _ hcw
  have hy : k / b.cw < b.ch := (Nat.div_lt_iff_lt_mul hcw).2 (by rw [Nat.mul_comm]; exact hk)
  have hkk : k / b.cw * b.cw + k % b.cw = k := Nat.div_add_mod' k b.cw
  have hleafZ : b.zbpLeaf (k % b.cw) (k / b.cw) = (b.blocks.getD k default).zeroBitPlanes := by
    simp only [BandIn.zbpLeaf, hkk]
  have h1 := (Spec.TagTree.encodeAll_spec [Query.lt (k % b.cw) (k / b.cw) 1] i
    (by simp [Query.Valid, hx, hy]) hI).2
  rw [blockBits_eq]
  split
  · exact ⟨h1, hZ⟩
  · rename_i h0
    have hz := (hok h0).1
    exact ⟨h1, (Spec.TagTree.encodeAll_spec _ z
      (by simp only [List.mem_singleton, forall_eq, Query.Valid, hleafZ]; exact ⟨hx, hy, hz⟩) hZ).2⟩

/-- The encoder's header bits of the code-blocks `ks` of a precinct-band (in turn), with the
final inclusion and zero bit-plane tag-tree states. -/
def blocksBits (b : BandIn) : List Nat → St → St → List Bool × St × St
  | [], i, z => ([], i, z)
  | k :: ks, i, z =>
    let r := blockBits b k i z
    let r2 := blocksBits b ks r.2.1 r.2.2
    (r.1 ++ r2.1, r2.2)

/-- Writing a concatenation writes its parts in turn. -/
theorem BitWriter.bits_append (w : BitWriter) (a c : List Bool) :
    w.bits (a ++ c) = (w.bits a).bits c := by
  simp [BitWriter.bits, List.foldl_append]

/-- The encoder's band loop writes `blocksBits`. -/
theorem foldl_blockBits (b : BandIn) : ∀ (ks : List Nat) (w : BitWriter) (i z : St),
    List.foldl (fun (acc : BitWriter × St × St) k =>
      let (bits, incl, zbp) := blockBits b k acc.2.1 acc.2.2
      (acc.1.bits bits, incl, zbp)) (w, i, z) ks =
      (w.bits (blocksBits b ks i z).1, (blocksBits b ks i z).2)
  | [], w, i, z => rfl
  | k :: ks, w, i, z => by
    simp only [List.foldl_cons]
    rw [foldl_blockBits b ks]
    simp only [blocksBits, BitWriter.bits_append]

/-- `bandBits` writes the bits of every code-block of the band from fresh tag trees. -/
theorem bandBits_eq (w : BitWriter) (b : BandIn) :
    bandBits w b = w.bits (blocksBits b (List.range b.blocks.size) Spec.TagTree.init
      Spec.TagTree.init).1 := by
  unfold bandBits
  dsimp only
  rw [foldl_blockBits]

/-- **The code-blocks `ks` of a precinct-band** (B.10.4–B.10.7): the spec reader on the
encoder's bits gives, for each included code-block, its contribution, and leaves exactly the
following bits; each block `j ∈ ks` becomes `hdrAfter`, the others are untouched; the
tag-tree states are the encoder's. -/
theorem blocksHeader_enc (L : Limits) (bi : Nat) (b : BandIn)
    (hsz : b.blocks.size = b.cw * b.ch)
    (hok : ∀ k < b.blocks.size, BlockOK L b.maxZero (b.blocks.getD k default)) :
    ∀ (ks : List Nat) (bs : BandSt) (rest : List Bool), ks.Nodup → (∀ k ∈ ks, k < b.blocks.size) →
      bs.w = b.cw → bs.h = b.ch → bs.maxZero = b.maxZero →
      Inv b.cw b.ch b.inclLeaf bs.incl → Inv b.cw b.ch b.zbpLeaf bs.zbp →
      (∀ k ∈ ks, ∃ g, bs.blocks[k]? = some { geom := g }) →
      ∃ blocks', blocksHeader L 0 0 bi ks bs ((blocksBits b ks bs.incl bs.zbp).1 ++ rest) =
        .ok ({ bs with incl := (blocksBits b ks bs.incl bs.zbp).2.1,
                       zbp := (blocksBits b ks bs.incl bs.zbp).2.2, blocks := blocks' },
             ks.filterMap (contribOf bi b), rest) ∧
        blocks'.length = bs.blocks.length ∧
        ∀ j, blocks'[j]? = if j ∈ ks then (bs.blocks[j]?).map (hdrAfter · (b.blocks.getD j default))
          else bs.blocks[j]?
  | [], bs, rest, _, _, _, _, _, _, _, _ =>
    ⟨bs.blocks, by simp [blocksHeader, blocksBits], rfl, by simp⟩
  | k :: ks, bs, rest, hnd, hks, hw, hh, hm, hI, hZ, hfr => by
    obtain ⟨g, hg⟩ := hfr k List.mem_cons_self
    have hk : k < b.blocks.size := hks k List.mem_cons_self
    have hkn : k ∉ ks := (List.nodup_cons.1 hnd).1
    have hB := blockHeader_enc L bi k b bs g ((blocksBits b ks (blockBits b k bs.incl bs.zbp).2.1
      (blockBits b k bs.incl bs.zbp).2.2).1 ++ rest) (by omega) hw hh hm hg hI hZ (hok k hk)
    have hInv := blockBits_inv (L := L) (by omega) hI hZ (hok k hk)
    obtain ⟨blocks', h1, h2, h3⟩ := blocksHeader_enc L bi b hsz hok ks
      { bs with incl := (blockBits b k bs.incl bs.zbp).2.1,
                zbp := (blockBits b k bs.incl bs.zbp).2.2,
                blocks := bs.blocks.set k (hdrAfter { geom := g } (b.blocks.getD k default)) }
      rest (List.nodup_cons.1 hnd).2 (fun j hj => hks j (List.mem_cons_of_mem _ hj)) hw hh hm
      hInv.1 hInv.2 (by
        intro j hj
        have hne : k ≠ j := fun he => hkn (he ▸ hj)
        simp only [List.getElem?_set_ne hne]
        exact hfr j (List.mem_cons_of_mem _ hj))
    refine ⟨blocks', ?_, ?_, ?_⟩
    · simp only [blocksBits, List.append_assoc, blocksHeader, bind, Except.bind, hB, pure,
        Except.pure]
      simp only at h1
      rw [h1]
      simp only [List.filterMap_cons]
      cases contribOf bi b k <;> rfl
    · rw [h2]; simp
    · intro j
      rw [h3 j]
      by_cases hj : j = k
      · subst hj
        simp only [hkn, ↓reduceIte, List.mem_cons_self, hg, Option.map_some]
        rw [List.getElem?_set_self (List.getElem?_eq_some_iff.1 hg).1]
      · have hne : k ≠ j := fun he => hj he.symm
        simp only [List.getElem?_set_ne hne, List.mem_cons, hj, false_or]

/-- The decoder's precinct-band after the header of its first packet carrying the encoder's
band `b`: the encoder's final tag-tree states and every code-block `hdrAfter`. -/
def hdrBand (bs : BandSt) (b : BandIn) : BandSt :=
  { bs with incl := (blocksBits b (List.range b.blocks.size) bs.incl bs.zbp).2.1,
            zbp := (blocksBits b (List.range b.blocks.size) bs.incl bs.zbp).2.2,
            blocks := bs.blocks.mapIdx fun j cb => hdrAfter cb (b.blocks.getD j default) }

/-- A fresh decoder precinct-band `bs` (fresh tag trees, every code-block never included)
with the geometry of the encoder's band `b` (grid `cw × ch`, `maxZero`, one code-block per
leaf), every code-block of `b` meeting `BlockOK`. -/
def BandReady (L : Limits) (bs : BandSt) (b : BandIn) : Prop :=
  bs.w = b.cw ∧ bs.h = b.ch ∧ bs.maxZero = b.maxZero ∧ bs.incl = Spec.TagTree.init ∧
    bs.zbp = Spec.TagTree.init ∧ b.blocks.size = b.cw * b.ch ∧ bs.blocks.length = b.blocks.size ∧
    (∀ cb ∈ bs.blocks, cb = { geom := cb.geom }) ∧
    ∀ k < b.blocks.size, BlockOK L b.maxZero (b.blocks.getD k default)

/-- The header bits of one band, as written by `bandBits`. -/
def bandBitsL (b : BandIn) : List Bool :=
  (blocksBits b (List.range b.blocks.size) Spec.TagTree.init Spec.TagTree.init).1

/-- **One precinct-band** of the packet header: the spec reads the encoder's bits back. -/
theorem band_enc (L : Limits) (bi : Nat) (bs : BandSt) (b : BandIn) (hr : BandReady L bs b)
    (rest : List Bool) :
    blocksHeader L 0 0 bi (List.range bs.blocks.length) bs (bandBitsL b ++ rest) =
      .ok (hdrBand bs b, (List.range b.blocks.size).filterMap (contribOf bi b), rest) := by
  obtain ⟨hw, hh, hm, hi, hz, hsz, hlen, hfr, hok⟩ := hr
  obtain ⟨blocks', h1, h2, h3⟩ := blocksHeader_enc L bi b hsz hok (List.range b.blocks.size) bs rest
    List.nodup_range (fun k hk => List.mem_range.1 hk) hw hh hm (by rw [hi]; exact inv_init _ _ _)
    (by rw [hz]; exact inv_init _ _ _) (by
      intro k hk
      have hk' : k < bs.blocks.length := by rw [hlen]; exact List.mem_range.1 hk
      exact ⟨bs.blocks[k].geom, by rw [List.getElem?_eq_getElem hk', hfr _ (List.getElem_mem hk')]⟩)
  have hb : bandBitsL b = (blocksBits b (List.range b.blocks.size) bs.incl bs.zbp).1 := by
    rw [hi, hz]; rfl
  rw [hlen, hb, h1]
  have : blocks' = bs.blocks.mapIdx fun j cb => hdrAfter cb (b.blocks.getD j default) := by
    apply List.ext_getElem?
    intro j
    rw [h3 j, List.getElem?_mapIdx]
    split
    · rfl
    · rename_i hj
      rw [List.mem_range] at hj
      rw [List.getElem?_eq_none (by omega)]; rfl
  rw [this]; rfl

/-- The contributions of the bands `bi, bi + 1, …` of a packet. -/
def contribs (bi : Nat) : List BandIn → List Contribution
  | [] => []
  | b :: bins => (List.range b.blocks.size).filterMap (contribOf bi b) ++ contribs (bi + 1) bins

/-- **The bands of a packet header** (B.10.3 after the first bit). -/
theorem bands_enc (L : Limits) : ∀ (bss : List BandSt) (bins : List BandIn) (bi : Nat)
    (rest : List Bool), bss.length = bins.length → (∀ p ∈ bss.zip bins, BandReady L p.1 p.2) →
    bandsHeader L 0 0 bi bss ((bins.flatMap bandBitsL) ++ rest) =
      .ok (List.zipWith hdrBand bss bins, contribs bi bins, rest)
  | [], [], bi, rest, _, _ => rfl
  | bs :: bss, b :: bins, bi, rest, hl, hr => by
    simp only [List.zip_cons_cons, List.mem_cons, forall_eq_or_imp] at hr
    simp only [List.flatMap_cons, List.append_assoc, bandsHeader, bind, Except.bind,
      band_enc L bi bs b hr.1, bands_enc L bss bins (bi + 1) rest (by simpa using hl) hr.2, pure,
      Except.pure, contribs, List.zipWith_cons_cons]
  | [], _ :: _, _, _, hl, _ => by simp at hl
  | _ :: _, [], _, _, hl, _ => by simp at hl

/-- The decoder state of a code-block after the body of the packet carrying the encoder's
code-block `blk`: its codeword appended as a new codeword segment. -/
def fillSeg (cb : BlockSt) (blk : BlockIn) : BlockSt :=
  if blk.numPasses = 0 then cb
  else { cb with segs := cb.segs ++ [{ data := blk.data.data.toList, passes := blk.numPasses }] }

/-- The body bytes of code-block `k` of a band (B.10.8): its codeword if included. -/
def blockBody (b : BandIn) (k : Nat) : List UInt8 :=
  if (b.blocks.getD k default).numPasses = 0 then [] else (b.blocks.getD k default).data.data.toList

/-- `readBody` over a concatenation of contribution lists. -/
theorem readBody_append (a c : List Contribution) : ∀ (st st' : PrecSt) (body body' : List UInt8),
    readBody st a body = .ok (st', body') → readBody st (a ++ c) body = readBody st' c body' := by
  induction a with
  | nil => intro st st' body body' h; simp only [readBody, Except.ok.injEq, Prod.mk.injEq] at h; rw [h.1, h.2]; rfl
  | cons x a ih =>
    intro st st' body body' h
    simp only [readBody, bind, Except.bind, List.cons_append] at h ⊢
    revert h
    cases takePieces x.pieces body with
    | error e => intro h; cases h
    | ok r =>
      simp only
      cases st.bands[x.band]? with
      | none => intro h; cases h
      | some bs =>
        simp only
        cases bs.blocks[x.block]? with
        | none => intro h; cases h
        | some cb => simp only; exact ih _ _ _ _

/-- Setting an entry to its own value. -/
theorem list_set_self_of_some {α : Type} {l : List α} {i : Nat} {a : α} (h : l[i]? = some a) : l.set i a = l := by
  obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.1 h
  rw [← heq]; exact List.set_getElem_self hlt

/-- **The body of one precinct-band** (B.10.8): reading the encoder's codewords of the
code-blocks `ks` appends each to its code-block (`fillSeg`) and leaves exactly the rest. -/
theorem bandBody_enc (bi : Nat) (b : BandIn) : ∀ (ks : List Nat) (st : PrecSt) (bs : BandSt)
    (rest : List UInt8), ks.Nodup → st.bands[bi]? = some bs → (∀ k ∈ ks, k < bs.blocks.length) →
    ∃ blocks', readBody st (ks.filterMap (contribOf bi b)) ((ks.flatMap (blockBody b)) ++ rest) =
        .ok ({ st with bands := st.bands.set bi { bs with blocks := blocks' } }, rest) ∧
      ∀ j, blocks'[j]? = if j ∈ ks then (bs.blocks[j]?).map (fillSeg · (b.blocks.getD j default))
        else bs.blocks[j]?
  | [], st, bs, rest, _, hbs, _ => by
    refine ⟨bs.blocks, ?_, by simp⟩
    have : ({ bs with blocks := bs.blocks } : BandSt) = bs := rfl
    simp only [List.filterMap_nil, List.flatMap_nil, List.nil_append, readBody, list_set_self_of_some hbs]
  | k :: ks, st, bs, rest, hnd, hbs, hks => by
    have hk : k < bs.blocks.length := hks k List.mem_cons_self
    have hkn : k ∉ ks := (List.nodup_cons.1 hnd).1
    by_cases h0 : (b.blocks.getD k default).numPasses = 0
    · obtain ⟨blocks', h1, h2⟩ := bandBody_enc bi b ks st bs rest (List.nodup_cons.1 hnd).2 hbs
        (fun j hj => hks j (List.mem_cons_of_mem _ hj))
      refine ⟨blocks', ?_, ?_⟩
      · simp only [List.filterMap_cons, contribOf, h0, ↓reduceIte, List.flatMap_cons, blockBody,
          List.nil_append]
        exact h1
      · intro j
        rw [h2 j]
        by_cases hj : j = k
        · subst hj
          simp only [hkn, ↓reduceIte, List.mem_cons_self]
          cases bs.blocks[j]? <;> simp only [fillSeg, h0, ↓reduceIte, Option.map_none, Option.map_some]
        · simp only [List.mem_cons, hj, false_or]
    · obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.1 hbs
      have hcb : bs.blocks[k]? = some bs.blocks[k] := List.getElem?_eq_getElem hk
      let bs1 : BandSt := { bs with blocks := bs.blocks.set k (fillSeg bs.blocks[k] (b.blocks.getD k default)) }
      let st1 : PrecSt := { st with bands := st.bands.set bi bs1 }
      have hbs1 : st1.bands[bi]? = some bs1 := by simp only [st1]; rw [List.getElem?_set_self hlt]
      obtain ⟨blocks', h1, h2⟩ := bandBody_enc bi b ks st1 bs1 rest (List.nodup_cons.1 hnd).2 hbs1
        (fun j hj => by simp only [bs1, List.length_set]; exact hks j (List.mem_cons_of_mem _ hj))
      refine ⟨blocks', ?_, ?_⟩
      · have hsz : (b.blocks.getD k default).data.size =
            (b.blocks.getD k default).data.data.toList.length := by
          rw [Array.length_toList]; rfl
        simp only [List.filterMap_cons, contribOf, h0, ↓reduceIte, List.flatMap_cons, blockBody,
          List.append_assoc, readBody, takePieces, bind, Except.bind, hsz, hbs, hcb]
        simp only [List.length_append, gt_iff_lt, Nat.not_lt.2 (Nat.le_add_right _ _),
          ↓reduceIte, List.drop_left', List.take_left', pure, Except.pure]
        have hadd : addPieces bs.blocks[k] false
            [((b.blocks.getD k default).numPasses, (b.blocks.getD k default).data.data.toList)] =
            fillSeg bs.blocks[k] (b.blocks.getD k default) := by
          simp only [addPieces, fillSeg, h0, ↓reduceIte]
        rw [hadd]
        refine h1.trans ?_
        simp only [st1, bs1, List.set_set]
      · intro j
        rw [h2 j]
        by_cases hj : j = k
        · subst hj
          simp only [hkn, ↓reduceIte, List.mem_cons_self, bs1, hcb, Option.map_some]
          rw [List.getElem?_set_self hk]
        · have hne : k ≠ j := fun he => hj he.symm
          simp only [bs1, List.getElem?_set_ne hne, List.mem_cons, hj, false_or]

/-- The body bytes of the bands of a packet (B.10.8). -/
def bodyAll (bins : List BandIn) : List UInt8 :=
  bins.flatMap fun b => (List.range b.blocks.size).flatMap (blockBody b)

/-- The decoder's precinct-band `j` after the body of a packet whose bands `bi, bi + 1, …` are
the encoder's `bins`. -/
def fillBands (bi : Nat) (bins : List BandIn) (bands : List BandSt) : List BandSt :=
  bands.mapIdx fun j bs =>
    if bi ≤ j ∧ j - bi < bins.length then
      { bs with blocks := bs.blocks.mapIdx fun k cb => fillSeg cb ((bins.getD (j - bi) default).blocks.getD k default) }
    else bs

/-- **The body of a packet** (B.10.8): every included code-block of every band gets its
codeword as a new segment; exactly the following bytes are left. -/
theorem bandsBody_enc : ∀ (bins : List BandIn) (bi : Nat) (st : PrecSt) (rest : List UInt8),
    (∀ i (h : i < bins.length), ∃ bs, st.bands[bi + i]? = some bs ∧
      bs.blocks.length = bins[i].blocks.size) →
    readBody st (contribs bi bins) (bodyAll bins ++ rest) =
      .ok ({ st with bands := fillBands bi bins st.bands }, rest)
  | [], bi, st, rest, _ => by
    have : fillBands bi [] st.bands = st.bands := by
      apply List.ext_getElem?; intro j
      simp [fillBands, List.getElem?_mapIdx]
    simp only [contribs, bodyAll, List.flatMap_nil, List.nil_append, readBody, this]
  | b :: bins, bi, st, rest, h => by
    obtain ⟨bs, hbs, hlen⟩ := h 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at hbs hlen
    have hlt : bi < st.bands.length := (List.getElem?_eq_some_iff.1 hbs).1
    obtain ⟨blocks', h1, h2⟩ := bandBody_enc bi b (List.range b.blocks.size) st bs
      (bodyAll bins ++ rest) List.nodup_range hbs (fun k hk => by rw [hlen]; exact List.mem_range.1 hk)
    have hb' : blocks' = bs.blocks.mapIdx fun k cb => fillSeg cb (b.blocks.getD k default) := by
      apply List.ext_getElem?; intro j
      rw [h2 j, List.getElem?_mapIdx]
      split
      · rfl
      · rename_i hj
        rw [List.mem_range] at hj
        rw [List.getElem?_eq_none (by omega)]; rfl
    let st1 : PrecSt := { st with bands := st.bands.set bi { bs with blocks := blocks' } }
    have ih := bandsBody_enc bins (bi + 1) st1 rest (by
      intro i hi
      obtain ⟨bs', h3, h4⟩ := h (i + 1) (by simp; omega)
      refine ⟨bs', ?_, by simpa using h4⟩
      simp only [st1]
      rw [List.getElem?_set_ne (by omega), show bi + 1 + i = bi + (i + 1) by omega, h3])
    have hbody : bodyAll (b :: bins) =
        (List.range b.blocks.size).flatMap (blockBody b) ++ bodyAll bins := by
      simp [bodyAll]
    rw [contribs, hbody, List.append_assoc, readBody_append _ _ _ _ _ _ h1, ih]
    congr 3
    apply List.ext_getElem?; intro j
    simp only [fillBands, List.getElem?_mapIdx, st1]
    by_cases hj : j = bi
    · subst hj
      rw [List.getElem?_set_self hlt, hbs]
      simp only [Option.map_some, show ¬ (j + 1 ≤ j) from by omega, false_and, ↓reduceIte,
        Nat.le_refl, Nat.sub_self, true_and, List.length_cons, Nat.zero_lt_succ, List.getD_cons_zero, hb']
    · rw [List.getElem?_set_ne (fun he => hj he.symm)]
      cases st.bands[j]? with
      | none => rfl
      | some x =>
        simp only [Option.map_some, List.length_cons]
        by_cases hlo : bi < j
        · have e1 : bi + 1 ≤ j := hlo
          have e2 : j - bi = (j - (bi + 1)) + 1 := by omega
          simp only [e1, true_and, Nat.le_of_lt hlo, e2, List.getD_cons_succ, Nat.add_lt_add_iff_right]
        · have e1 : ¬ bi + 1 ≤ j := by omega
          have e2 : ¬ bi ≤ j := by omega
          simp [e1, e2]

/-- The decoder state of a code-block after the packet carrying the encoder's `blk` (header,
then body). -/
def blockAfter (cb : BlockSt) (blk : BlockIn) : BlockSt := fillSeg (hdrAfter cb blk) blk

/-- From a fresh code-block, an included `blk` comes back with its codeword as the single
segment of `numPasses` passes and its zero bit-planes; a block without passes stays fresh. -/
theorem blockAfter_fresh (g : JPEG2000.Tier2.Geometry.CodeBlockGeom) (blk : BlockIn) :
    blockAfter { geom := g } blk =
      if blk.numPasses = 0 then { geom := g }
      else { geom := g, included := true, zbp := blk.zeroBitPlanes,
             lblock := 3 + lblockInc blk.numPasses blk.data.size, passes := blk.numPasses,
             segs := [{ data := blk.data.data.toList, passes := blk.numPasses }] } := by
  unfold blockAfter fillSeg hdrAfter
  split <;> simp_all

/-- The spec's result for a precinct-band after the packet carrying the encoder's band `b`. -/
def outAfter (bs : BandSt) (b : BandIn) : BandOut :=
  { band := bs.band, rect := bs.rect, maxZero := bs.maxZero,
    blocks := bs.blocks.mapIdx fun k cb => blockAfter cb (b.blocks.getD k default) }

/-- The coding passes of the code-blocks of a packet. -/
def passesOf (bands : Array BandIn) : Nat :=
  (bands.toList.map fun b => (b.blocks.toList.map (·.numPasses)).sum).sum

/-- A fresh decoder precinct state with style 0 (plain) and the geometry of the encoder's
bands (`BandReady` for each, same number of bands). -/
def PrecReady (L : Limits) (st : PrecSt) (bands : Array BandIn) : Prop :=
  st.style = 0 ∧ st.bands.length = bands.size ∧ ∀ p ∈ st.bands.zip bands.toList, BandReady L p.1 p.2

/-- Index-wise reading of an array. -/
theorem range_map_array_getD {α : Type} [Inhabited α] (a : Array α) :
    (List.range a.size).map (fun k => a.getD k default) = a.toList := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.length_map, List.length_range] at h1
  simp [Array.getD, h1]

/-- The packet header bytes of the encoder, as a writer state. -/
theorem foldl_bandBits : ∀ (bins : List BandIn) (w : BitWriter),
    bins.foldl bandBits w = w.bits (bins.flatMap bandBitsL)
  | [], w => by simp [BitWriter.bits]
  | b :: bins, w => by
    rw [List.foldl_cons, foldl_bandBits bins, bandBits_eq, List.flatMap_cons, BitWriter.bits_append]
    rfl

/-- The packet body bytes of the encoder. -/
theorem packetBody_toList (bands : Array BandIn) :
    (packetBody bands).data.toList = bodyAll bands.toList := by
  have inner : ∀ (bl : List BlockIn) (acc : ByteArray),
      (bl.foldl (fun acc blk => if blk.numPasses > 0 then acc ++ blk.data else acc) acc).data.toList =
        acc.data.toList ++ bl.flatMap (fun blk => if blk.numPasses = 0 then [] else blk.data.data.toList) := by
    intro bl
    induction bl with
    | nil => intro acc; simp
    | cons x bl ih =>
      intro acc
      rw [List.foldl_cons, ih, List.flatMap_cons]
      by_cases h : x.numPasses = 0
      · simp [h]
      · simp [h, Nat.pos_of_ne_zero h]
  have outer : ∀ (bins : List BandIn) (acc : ByteArray),
      (bins.foldl (fun acc b =>
        b.blocks.foldl (fun acc blk => if blk.numPasses > 0 then acc ++ blk.data else acc) acc) acc).data.toList =
        acc.data.toList ++ bodyAll bins := by
    intro bins
    induction bins with
    | nil => intro acc; simp [bodyAll]
    | cons b bins ih =>
      intro acc
      rw [List.foldl_cons, ih, ← Array.foldl_toList, inner]
      have : (List.range b.blocks.size).flatMap (blockBody b) =
          b.blocks.toList.flatMap (fun blk => if blk.numPasses = 0 then [] else blk.data.data.toList) := by
        rw [← range_map_array_getD b.blocks, List.flatMap_map]; rfl
      simp only [bodyAll, List.flatMap_cons, List.append_assoc, this]
  unfold packetBody
  rw [← Array.foldl_toList, outer]
  rfl

/-- `newPasses` sums the passes of the pieces. -/
theorem newPasses_eq (cs : List Contribution) :
    newPasses cs = (cs.map fun c => (c.pieces.map (·.1)).sum).sum := by
  have hp : ∀ (ps : List (Nat × Nat)) (a : Nat), ps.foldl (fun a p => a + p.1) a = a + (ps.map (·.1)).sum := by
    intro ps; induction ps with
    | nil => simp
    | cons p ps ih => intro a; rw [List.foldl_cons, ih]; simp; omega
  have hc : ∀ (cs : List Contribution) (a : Nat),
      cs.foldl (fun a c => c.pieces.foldl (fun a p => a + p.1) a) a =
        a + (cs.map fun c => (c.pieces.map (·.1)).sum).sum := by
    intro cs; induction cs with
    | nil => simp
    | cons c cs ih => intro a; rw [List.foldl_cons, ih, hp]; simp; omega
  simp [newPasses, hc]

/-- The passes of the contributions of a packet. -/
theorem contribs_passes : ∀ (bins : List BandIn) (bi : Nat),
    ((contribs bi bins).map fun c => (c.pieces.map (·.1)).sum).sum =
      (bins.map fun b => (b.blocks.toList.map (·.numPasses)).sum).sum
  | [], _ => rfl
  | b :: bins, bi => by
    have hb : ∀ ks : List Nat, ((ks.filterMap (contribOf bi b)).map fun c => (c.pieces.map (·.1)).sum).sum =
        (ks.map fun k => (b.blocks.getD k default).numPasses).sum := by
      intro ks; induction ks with
      | nil => rfl
      | cons k ks ih =>
        by_cases h : (b.blocks.getD k default).numPasses = 0
        · simp only [List.filterMap_cons, contribOf, h, ↓reduceIte, ih, List.map_cons, List.sum_cons,
            Nat.zero_add]
        · simp only [List.filterMap_cons, contribOf, h, ↓reduceIte, ih, List.map_cons, List.sum_cons,
            List.map_nil, List.sum_nil, Nat.add_zero]
    simp only [contribs, List.map_append, List.sum_append, hb, contribs_passes bins (bi + 1),
      List.map_cons, List.sum_cons]
    rw [← range_map_array_getD b.blocks, List.map_map]; rfl

/-- A sum of zeros. -/
theorem sum_map_eq_zero_of {α : Type} (f : α → Nat) : ∀ l : List α, (∀ x ∈ l, f x = 0) → (l.map f).sum = 0
  | [], _ => rfl
  | x :: l, h => by
    simp only [List.map_cons, List.sum_cons, h x List.mem_cons_self,
      sum_map_eq_zero_of f l (fun y hy => h y (List.mem_cons_of_mem _ hy))]

/-- The spec's result for the bands after a packet. -/
theorem out_fill (bnds : List BandSt) (bins : List BandIn) :
    (fillBands 0 bins (List.zipWith hdrBand bnds bins)).map
      (fun bs => ({ band := bs.band, rect := bs.rect, maxZero := bs.maxZero, blocks := bs.blocks } : BandOut)) =
      List.zipWith outAfter bnds bins := by
  apply List.ext_getElem?; intro j
  simp only [List.getElem?_map, fillBands, List.getElem?_mapIdx, List.getElem?_zipWith']
  cases h1 : bnds[j]? with
  | none => rfl
  | some a =>
    cases h2 : bins[j]? with
    | none => rfl
    | some b =>
      have hj : j < bins.length := (List.getElem?_eq_some_iff.1 h2).1
      have hg : bins.getD j default = b := by simp [List.getD_eq_getElem?_getD, h2]
      simp only [Option.map_some, Option.bind_some, Nat.zero_le, Nat.sub_zero, hj, and_self,
        ↓reduceIte, hg]
      simp only [hdrBand, outAfter, List.mapIdx_mapIdx, blockAfter]
      rfl

/-- **One packet** (B.9, B.10; layer 0, style 0, no `SOP`/`EPH`, header in the body
stream): from a fresh precinct state the spec's `packet` reads the encoder's packet followed by
any `T`, adds `passesOf bands` passes, leaves exactly `T`, and every precinct-band comes back
as `outAfter`. -/
theorem packet_enc (L : Limits) (seq : Nat) (st : PrecSt) (bands : Array BandIn)
    (hr : PrecReady L st bands) (hdr T : List UInt8) :
    ∃ st', packet L false false seq 0 st true hdr ((encodePacket bands).data.toList ++ T) =
        .ok (st', passesOf bands, T, T) ∧ st'.style = st.style ∧
      st'.out = List.zipWith outAfter st.bands bands.toList := by
  obtain ⟨hs, hl, hb⟩ := hr
  obtain ⟨sty, bnds⟩ := st
  dsimp only at hs hl hb ⊢
  subst hs
  simp only [encodePacket, ByteArray.toList_data_append, packetHeader, List.append_assoc,
    packetBody_toList]
  split
  · rename_i hne
    have hw := winv_bits (winv_bit winv_init true) (bands.toList.flatMap bandBitsL)
    rw [← foldl_bandBits, Array.foldl_toList] at hw
    obtain ⟨pad, h1, h2⟩ := finish_spec hw (by simp) (bodyAll bands.toList ++ T)
    have hlen : ∀ a c : List Bool, (true :: (a ++ c)).length - c.length = a.length + 1 := by
      intros; simp; omega
    simp only [List.nil_append, List.cons_append, List.append_assoc,
      List.length_cons] at h1 h2
    have hbe := bands_enc L bnds bands.toList 0
      (pad ++ unstuff (bodyAll bands.toList ++ T)) (by simpa using hl) hb
    have hbody := bandsBody_enc bands.toList 0
      { style := 0, bands := List.zipWith hdrBand bnds bands.toList } T (by
        intro i hi
        have hi' : i < bnds.length := by rw [hl]; simpa using hi
        have hm : (bnds[i], bands.toList[i]) ∈ bnds.zip bands.toList := by
          rw [← List.getElem_zip (h := by simp; omega)]; exact List.getElem_mem _
        refine ⟨hdrBand bnds[i] bands.toList[i], ?_, ?_⟩
        · simp only [Nat.zero_add]
          rw [List.getElem?_zipWith' , List.getElem?_eq_getElem hi', List.getElem?_eq_getElem hi]
          rfl
        · simp only [hdrBand, List.length_mapIdx]
          exact (hb _ hm).2.2.2.2.2.2.1)
    simp only [packet, pure, Except.pure, bind, Except.bind, h1, Bool.false_eq_true, ↓reduceIte,
      bit, Spec.TagTree.listNext, hbe, hlen, h2, List.drop_left, hbody]
    refine ⟨{ style := 0, bands := fillBands 0 bands.toList (List.zipWith hdrBand bnds bands.toList) },
      ?_, rfl, ?_⟩
    · rw [newPasses_eq, contribs_passes]; rfl
    · simp only [PrecSt.out]
      exact out_fill bnds bands.toList
  · rename_i hne
    have hz : ∀ b ∈ bands.toList, ∀ k, (b.blocks.getD k default).numPasses = 0 := by
      intro b hb k
      simp only [nonEmpty, Array.any_eq_true'] at hne
      unfold Array.getD
      split
      · rename_i hk
        have h' : ¬ decide (b.blocks[k].numPasses > 0) = true :=
          fun h => hne ⟨b, Array.mem_toList_iff.1 hb, _, Array.getElem_mem hk, h⟩
        simp at h'; exact h'
      · rfl
    have hbody0 : bodyAll bands.toList = [] := by
      simp only [bodyAll, List.flatMap_eq_nil_iff]
      intro b hb k _
      simp only [blockBody, hz b hb k, ↓reduceIte]
    have hp0 : passesOf bands = 0 := by
      apply sum_map_eq_zero_of
      intro b hb
      rw [← range_map_array_getD b.blocks, List.map_map]
      apply sum_map_eq_zero_of
      intro k _
      exact hz b hb k
    have hw := winv_bit winv_init false
    obtain ⟨pad, h1, h2⟩ := finish_spec hw (by simp) (bodyAll bands.toList ++ T)
    rw [hbody0] at h1 h2
    simp only [List.nil_append, List.cons_append, List.length_cons, List.length_nil] at h1 h2
    have hlen : ∀ c : List Bool, (false :: c).length - c.length = 0 + 1 := by intros; simp
    simp only [packet, pure, Except.pure, bind, Except.bind, h1, Bool.false_eq_true, ↓reduceIte,
      bit, Spec.TagTree.listNext, hlen, h2, List.drop_left, readBody, hbody0, List.nil_append]
    refine ⟨{ style := 0, bands := bnds }, ?_, rfl, ?_⟩
    · rw [hp0]; rfl
    · apply List.ext_getElem?; intro j
      simp only [PrecSt.out, List.getElem?_map, List.getElem?_zipWith']
      cases h1 : bnds[j]? with
      | none => rfl
      | some a =>
        have hj : j < bands.toList.length := by
          have := (List.getElem?_eq_some_iff.1 h1).1; simp; omega
        rw [List.getElem?_eq_getElem hj]
        simp only [Option.map_some, Option.bind_some, outAfter, Option.some.injEq]
        have hb' : bands.toList[j] ∈ bands.toList := List.getElem_mem hj
        have : a.blocks.mapIdx (fun k cb => blockAfter cb (bands.toList[j].blocks.getD k default)) =
            a.blocks := by
          apply List.ext_getElem?; intro k
          rw [List.getElem?_mapIdx]
          cases a.blocks[k]? with
          | none => rfl
          | some cb =>
            simp only [Option.map_some, blockAfter, fillSeg, hdrAfter, hz _ hb' k, ↓reduceIte]
        rw [this]

/-- **C10 layer 2b, one packet, per code-block** (B.9–B.10, one layer, style 0, fresh
precinct state): the spec's `packet` on the encoder's packet bytes followed by any `T`
succeeds, consumes exactly the packet, adds `passesOf bands` coding passes, and returns every
included code-block `blk` (`1 ≤ numPasses`) with the single segment `⟨data, numPasses⟩`, its
zero bit-planes and pass count; every other code-block stays fresh. -/
theorem packet_roundtrip (L : Limits) (seq : Nat) (st : PrecSt) (bands : Array BandIn)
    (hr : PrecReady L st bands) (hdr T : List UInt8) :
    ∃ st' : PrecSt, packet L false false seq 0 st true hdr ((encodePacket bands).data.toList ++ T) =
        .ok (st', passesOf bands, T, T) ∧
      ∀ (bi k : Nat) (blk : BlockIn), (bands[bi]?).bind (fun b : BandIn => (b.blocks[k]? : Option BlockIn)) = some blk →
        ∃ cb : BlockSt, (st'.out[bi]?).bind (fun bo : BandOut => bo.blocks[k]?) = some cb ∧
          if blk.numPasses = 0 then cb = { geom := cb.geom }
          else cb.included = true ∧ cb.zbp = blk.zeroBitPlanes ∧ cb.passes = blk.numPasses ∧
            cb.segs = [{ data := blk.data.data.toList, passes := blk.numPasses }] := by
  obtain ⟨st', h1, -, h3⟩ := packet_enc L seq st bands hr hdr T
  refine ⟨st', h1, ?_⟩
  intro bi k blk hblk
  obtain ⟨_, hl, hb⟩ := hr
  cases hbi : bands[bi]? with
  | none => rw [hbi] at hblk; cases hblk
  | some b =>
    rw [hbi] at hblk
    simp only [Option.bind_some] at hblk
    have hbiL : bi < bands.size := (Array.getElem?_eq_some_iff.1 hbi).1
    have hbi' : bands.toList[bi]? = some b := by rw [Array.getElem?_toList]; exact hbi
    have hsl : bi < st.bands.length := by omega
    have hm : (st.bands[bi], b) ∈ st.bands.zip bands.toList := by
      have : (st.bands.zip bands.toList)[bi]? = some (st.bands[bi], b) := by
        rw [List.getElem?_zip_eq_some]; exact ⟨List.getElem?_eq_getElem hsl, hbi'⟩
      exact List.mem_of_getElem? this
    obtain ⟨-, -, -, -, -, -, hlen, hfr, -⟩ := hb _ hm
    have hk : k < b.blocks.size := (Array.getElem?_eq_some_iff.1 hblk).1
    have hk' : k < st.bands[bi].blocks.length := by simp only at hlen; omega
    have hg : b.blocks.getD k default = blk := by
      simp [Array.getD, hk]; exact (Array.getElem?_eq_some_iff.1 hblk).2
    refine ⟨blockAfter st.bands[bi].blocks[k] blk, ?_, ?_⟩
    · rw [h3, List.getElem?_zipWith' , List.getElem?_eq_getElem hsl, hbi']
      simp only [Option.map_some, Option.bind_some, outAfter, List.getElem?_mapIdx,
        List.getElem?_eq_getElem hk', hg]
    · rw [hfr _ (List.getElem_mem hk'), blockAfter_fresh]
      by_cases h0 : blk.numPasses = 0
      · simp only [h0, ↓reduceIte]
      · simp only [h0, ↓reduceIte, and_self]

/-! ## The packets of a tile -/

open JPEG2000.Progression (PacketId)

/-- The precinct index the spec's `step` uses for packet `p` (`base[c][r] + k`). -/
def precIdx (base : Array (Array Nat)) (p : PacketId) : Nat :=
  ((base.getD p.comp #[]).getD p.res 0) + p.prec

/-- **A sequence of layer-0 packets** on distinct fresh precincts, each the encoder's packet
of the bands `E p`, folded with the spec's `step` (B.9–B.12; no `SOP`/`EPH`, headers in the
body stream): every precinct visited comes back as `outAfter`, the others are untouched, the
coding passes add up, and exactly the bytes after the packets are left. -/
theorem fold_enc (L : Limits) (base : Array (Array Nat)) (pb : Nat) (E : PacketId → Array BandIn)
    (T : List UInt8) : ∀ (ps : List PacketId) (s : Loop),
    (ps.map (precIdx base)).Nodup → (∀ p ∈ ps, p.layer = 0) →
    (∀ p ∈ ps, ∃ st, s.precs[precIdx base p]? = some st ∧ PrecReady L st (E p)) →
    pb + s.passes + (ps.map fun p => passesOf (E p)).sum ≤ L.maxCodingPasses →
    s.body = ps.flatMap (fun p => (encodePacket (E p)).data.toList) ++ T →
    ∃ s', ps.foldlM (step L false false true base pb) s = .ok s' ∧
      s'.body = T ∧ s'.passes = s.passes + (ps.map fun p => passesOf (E p)).sum ∧
      (∀ j, j ∉ ps.map (precIdx base) → s'.precs[j]? = s.precs[j]?) ∧
      ∀ p ∈ ps, ∃ st st', s.precs[precIdx base p]? = some st ∧ s'.precs[precIdx base p]? = some st' ∧
        st'.out = List.zipWith outAfter st.bands (E p).toList
  | [], s, _, _, _, _, hb => ⟨s, rfl, by simpa using hb, by simp, fun _ _ => rfl, by simp⟩
  | p :: ps, s, hnd, hl, hr, hpass, hb => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨st, hst, hready⟩ := hr p List.mem_cons_self
    have hl0 := hl p List.mem_cons_self
    obtain ⟨st', hpk, -, hout⟩ := packet_enc L s.seq st (E p) hready s.hdr
      (ps.flatMap (fun p => (encodePacket (E p)).data.toList) ++ T)
    simp only [List.map_cons, List.sum_cons] at hpass
    let rest := ps.flatMap (fun p => (encodePacket (E p)).data.toList) ++ T
    let s1 : Loop := { precs := s.precs.set (precIdx base p) st', hdr := rest, body := rest,
                       seq := s.seq + 1, passes := s.passes + passesOf (E p) }
    have hstep : step L false false true base pb s p = .ok s1 := by
      have hb' : s.body = (encodePacket (E p)).data.toList ++
          (ps.flatMap (fun p => (encodePacket (E p)).data.toList) ++ T) := by
        rw [hb, List.flatMap_cons, List.append_assoc]
      have hst' : s.precs[(base.getD p.comp #[]).getD p.res 0 + p.prec]? = some st := hst
      simp only [step, hst', hb', hl0, hpk, bind, Except.bind, Limits.check, Limits.checkLe,
        Limits.bound, show pb + (s.passes + passesOf (E p)) ≤ L.maxCodingPasses by omega, ↓reduceIte,
        pure, Except.pure]
      rfl
    have hne : ∀ q ∈ ps, precIdx base q ≠ precIdx base p := fun q hq he =>
      hnd.1 (he ▸ List.mem_map_of_mem hq)
    obtain ⟨s', h1, h2, h3, h4, h5⟩ := fold_enc L base pb E T ps s1 hnd.2
      (fun q hq => hl q (List.mem_cons_of_mem _ hq))
      (fun q hq => by
        obtain ⟨stq, h, hq'⟩ := hr q (List.mem_cons_of_mem _ hq)
        exact ⟨stq, by
          show (s.precs.set (precIdx base p) st')[precIdx base q]? = _
          rw [List.getElem?_set_ne (hne q hq).symm]; exact h, hq'⟩)
      (by show pb + (s.passes + passesOf (E p)) + _ ≤ _; omega) rfl
    refine ⟨s', ?_, h2, ?_, ?_, ?_⟩
    · rw [List.foldlM_cons, hstep]; exact h1
    · rw [h3, List.map_cons, List.sum_cons]; show s.passes + passesOf (E p) + _ = _; omega
    · intro j hj
      simp only [List.map_cons, List.mem_cons, not_or] at hj
      rw [h4 j hj.2]; show (s.precs.set (precIdx base p) st')[j]? = _
      rw [List.getElem?_set_ne (Ne.symm hj.1)]
    · intro q hq
      rcases List.mem_cons.1 hq with he | hq
      · rw [he]
        refine ⟨st, st', hst, ?_, hout⟩
        rw [h4 _ hnd.1]; show (s.precs.set (precIdx base p) st')[precIdx base p]? = _
        rw [List.getElem?_set_self (List.getElem?_eq_some_iff.1 hst).1]
      · obtain ⟨a, b, ha, hb, hab⟩ := h5 q hq
        refine ⟨a, b, ?_, hb, hab⟩
        have ha' : (s.precs.set (precIdx base p) st')[precIdx base q]? = some a := ha
        rw [List.getElem?_set_ne (hne q hq).symm] at ha'; exact ha'

open JPEG2000.Progression (Layout Volume)
open JPEG2000.Spec.Progression (packets precinctsOf)

/-- The encoder's bands of packet `p` (`prec[c][r][k]`). -/
def encBands (prec : Array (Array (Array (Array BandIn)))) (p : PacketId) : Array BandIn :=
  ((prec.getD p.comp #[]).getD p.res #[]).getD p.prec #[]

/-- The shape of the encoder's precinct arrays matches the layout: one entry per component,
`NL_c + 1` resolutions, `pw · ph` precincts per resolution (default precincts, B.6). -/
def TileShape (g : Layout) (prec : Array (Array (Array (Array BandIn)))) : Prop :=
  prec.size = g.numComps ∧ ∀ c < g.numComps, (prec.getD c #[]).size = g.levels c + 1 ∧
    ∀ r ≤ g.levels c, ((prec.getD c #[]).getD r #[]).size = g.pw c r * g.ph c r

/-- `foldr max` bounds every member. -/
private theorem le_foldr_max' {x : Nat} : ∀ {l : List Nat}, x ∈ l → x ≤ l.foldr max 0
  | [], h => by simp at h
  | a :: l, h => by
    rcases List.mem_cons.1 h with h | h
    · subst h; simp only [List.foldr_cons]; omega
    · have := le_foldr_max' h; simp only [List.foldr_cons]; omega

/-- `NL_i ≤ Nmax`. -/
private theorem levels_le_max' {g : Layout} {i : Nat} (hi : i < g.numComps) :
    g.levels i ≤ g.maxLevels := by
  unfold Layout.levels Layout.comp Layout.maxLevels
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi, Option.getD_some]
  apply le_foldr_max'
  exact List.mem_map.2 ⟨_, Array.getElem_mem_toList hi, rfl⟩

/-- `foldl max` bounds its start and every member. -/
private theorem le_foldl_max {α : Type} (f : α → Nat) : ∀ (l : List α) (m : Nat),
    m ≤ l.foldl (fun m x => max m (f x)) m ∧ ∀ x ∈ l, f x ≤ l.foldl (fun m x => max m (f x)) m
  | [], m => ⟨Nat.le_refl _, by simp⟩
  | a :: l, m => by
    obtain ⟨h1, h2⟩ := le_foldl_max f l (max m (f a))
    refine ⟨by simp only [List.foldl_cons]; omega, ?_⟩
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · simp only [List.foldl_cons]; omega
    · exact h2 x hx

/-- A `flatMap` over `range n` whose terms vanish from `A` on is its `flatMap` over `range A`. -/
private theorem flatMap_range_stable {β : Type} (G : Nat → List β) (A : Nat)
    (hG : ∀ r, A ≤ r → G r = []) : ∀ n, A ≤ n → (List.range n).flatMap G = (List.range A).flatMap G
  | 0, h => by rw [show A = 0 by omega]
  | n + 1, h => by
    by_cases hn : A = n + 1
    · rw [hn]
    · rw [List.range_succ, List.flatMap_append, flatMap_range_stable G A hG n (by omega),
        List.flatMap_singleton, hG n (by omega), List.append_nil]

/-- `flatMap` congruence on members. -/
private theorem flatMap_congr_mem {α β : Type} {f h : α → List β} :
    ∀ {l : List α}, (∀ x ∈ l, f x = h x) → l.flatMap f = l.flatMap h
  | [], _ => rfl
  | x :: l, hx => by
    rw [List.flatMap_cons, List.flatMap_cons, hx x List.mem_cons_self,
      flatMap_congr_mem (fun y hy => hx y (List.mem_cons_of_mem _ hy))]

/-- A byte-appending fold as a `flatMap`. -/
private theorem foldl_bytes {α : Type} (h : ByteArray → α → ByteArray) (L : α → List UInt8)
    (hh : ∀ acc x, (h acc x).data.toList = acc.data.toList ++ L x) :
    ∀ (l : List α) (acc : ByteArray), (l.foldl h acc).data.toList = acc.data.toList ++ l.flatMap L
  | [], acc => by simp
  | x :: l, acc => by
    rw [List.foldl_cons, foldl_bytes h L hh l, hh, List.flatMap_cons, List.append_assoc]

/-- **The encoder's tile bytes in the spec's LRCP packet order** (B.12.1.1, one layer, no POC). -/
theorem encodeTileLRCP_eq (g : Layout) (hwf : g.WF) (hlay : g.layers = 1)
    (prec : Array (Array (Array (Array BandIn)))) (hs : TileShape g prec) :
    (encodeTileLRCP prec).data.toList =
      (packets g .lrcp #[]).flatMap fun p => (encodePacket (encBands prec p)).data.toList := by
  obtain ⟨hsz, hc⟩ := hs
  -- the encoder side as list comprehensions
  let F : Nat → List UInt8 := fun r => (List.range g.numComps).flatMap fun c =>
    ((prec.getD c #[]).getD r #[]).toList.flatMap fun bands => (encodePacket bands).data.toList
  have henc : (encodeTileLRCP prec).data.toList =
      (List.range (prec.foldl (fun m rs => max m rs.size) 0)).flatMap F := by
    unfold encodeTileLRCP
    dsimp only
    rw [foldl_bytes _ F]
    · simp
    · intro acc r
      rw [← Array.foldl_toList, foldl_bytes _ (fun rs => (rs.getD r #[]).toList.flatMap
        fun bands => (encodePacket bands).data.toList)]
      · simp only [F]
        rw [← hsz, ← range_map_array_getD prec, List.flatMap_map]; rfl
      · intro acc rs
        rw [← Array.foldl_toList, foldl_bytes _ (fun bands => (encodePacket bands).data.toList)]
        intro acc bands; simp
  -- the spec side
  let G : Nat → List UInt8 := fun r => (List.range g.numComps).flatMap fun i =>
    (precinctsOf g 0 r i).flatMap fun p => (encodePacket (encBands prec p)).data.toList
  have hspec : ((packets g .lrcp #[]).flatMap fun p => (encodePacket (encBands prec p)).data.toList) =
      (List.range (g.maxLevels + 1)).flatMap G := by
    rw [Spec.Progression.packets_noPoc hwf]
    simp only [Spec.Progression.order, Spec.Progression.volume, Spec.Progression.lrcp,
      Spec.Progression.layerRange, Spec.Progression.resRange, Spec.Progression.compRange,
      Volume.full, Volume.le, Volume.re, Volume.ce, hlay, Nat.min_self, Nat.sub_zero,
      List.range_one, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.flatMap_assoc]
    rw [← List.range_eq_range', ← List.range_eq_range']
  have hFG : ∀ r, F r = G r := by
    intro r
    simp only [F, G]
    apply flatMap_congr_mem
    intro c hcm
    have hc' : c < g.numComps := List.mem_range.1 hcm
    obtain ⟨hs1, hs2⟩ := hc c hc'
    unfold precinctsOf
    split
    · rename_i hr
      rw [List.flatMap_map, ← hs2 r hr, ← range_map_array_getD ((prec.getD c #[]).getD r #[]),
        List.flatMap_map]
      rfl
    · rename_i hr
      have : (prec.getD c #[]).getD r #[] = #[] := by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega), Option.getD_none]
      rw [this]; rfl
  have hF : F = G := funext hFG
  rw [henc, hspec, hF]
  have hA : ∀ r, prec.foldl (fun m rs => max m rs.size) 0 ≤ r → G r = [] := by
    intro r hr
    rw [← hFG]
    simp only [F]
    apply List.flatMap_eq_nil_iff.2
    intro c hc
    have hc' : c < prec.size := by rw [hsz]; exact List.mem_range.1 hc
    have hle : (prec.getD c #[]).size ≤ prec.foldl (fun m rs => max m rs.size) 0 := by
      rw [← Array.foldl_toList]
      apply (le_foldl_max (fun rs : Array (Array (Array BandIn)) => rs.size) prec.toList 0).2
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hc', Option.getD_some]
      exact Array.getElem_mem_toList hc'
    have : (prec.getD c #[]).getD r #[] = #[] := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega), Option.getD_none]
    rw [this]; rfl
  have hB : ∀ r, g.maxLevels + 1 ≤ r → G r = [] := by
    intro r hr
    simp only [G]
    apply List.flatMap_eq_nil_iff.2
    intro i hi
    have := levels_le_max' (List.mem_range.1 hi)
    unfold precinctsOf
    simp only [show ¬ r ≤ g.levels i by omega, ↓reduceIte, List.flatMap_nil]
  rw [← flatMap_range_stable G _ hA (max (prec.foldl (fun m rs => max m rs.size) 0) (g.maxLevels + 1))
    (Nat.le_max_left _ _), flatMap_range_stable G _ hB _ (Nat.le_max_right _ _)]

/-- An injective-on-members map keeps `Nodup`. -/
private theorem nodup_map_of_inj {α β : Type} (f : α → β) : ∀ {l : List α}, l.Nodup →
    (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) → (l.map f).Nodup
  | [], _, _ => List.nodup_nil
  | x :: l, hnd, hinj => by
    rw [List.nodup_cons] at hnd
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, nodup_map_of_inj f hnd.2
      (fun a ha b hb => hinj a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))⟩
    obtain ⟨y, hy, he⟩ := List.mem_map.1 hm
    exact hnd.1 (hinj y (List.mem_cons_of_mem _ hy) x List.mem_cons_self he ▸ hy)

/-- **C10 layer 2b, one tile** (B.9–B.12): the spec's packet loop (`step` folded over
`Spec.Progression.packets g .lrcp #[]`, headers in the body stream, no `SOP`/`EPH`) on the
encoder's tile bytes `encodeTileLRCP prec` followed by any `T`, for one layer and no POC,
from fresh precinct states (`PrecReady`) at distinct indices `base[c][r] + k`: it succeeds,
consumes exactly the tile's packets, counts the encoder's coding passes, and every precinct
of the packet set comes back as `outAfter` of the encoder's bands — each included code-block
with its single segment, zero bit-planes and passes (`blockAfter_fresh`). -/
theorem tile_enc (L : Limits) (g : Layout) (hwf : g.WF) (hlay : g.layers = 1)
    (prec : Array (Array (Array (Array BandIn)))) (hs : TileShape g prec)
    (base : Array (Array Nat)) (precs : List PrecSt) (pb : Nat) (H T : List UInt8)
    (hinj : ∀ p q, g.InPacketSet p → g.InPacketSet q → precIdx base p = precIdx base q → p = q)
    (hready : ∀ p, g.InPacketSet p →
      ∃ st, precs[precIdx base p]? = some st ∧ PrecReady L st (encBands prec p))
    (hpass : pb + ((packets g .lrcp #[]).map fun p => passesOf (encBands prec p)).sum ≤
      L.maxCodingPasses) :
    ∃ s', (packets g .lrcp #[]).foldlM (step L false false true base pb)
        { precs, hdr := H, body := (encodeTileLRCP prec).data.toList ++ T } = .ok s' ∧
      s'.body = T ∧ s'.passes = ((packets g .lrcp #[]).map fun p => passesOf (encBands prec p)).sum ∧
      ∀ p, g.InPacketSet p → ∃ st st', precs[precIdx base p]? = some st ∧
        s'.precs[precIdx base p]? = some st' ∧
        st'.out = List.zipWith outAfter st.bands (encBands prec p).toList := by
  have hmem : ∀ p, p ∈ packets g .lrcp #[] ↔ g.InPacketSet p := by
    intro p; rw [Spec.Progression.packets_noPoc hwf]; exact (Spec.Progression.c5 hwf _).2 p
  have hnd : (packets g .lrcp #[]).Nodup := by
    rw [Spec.Progression.packets_noPoc hwf]; exact (Spec.Progression.c5 hwf _).1
  obtain ⟨s', h1, h2, h3, -, h5⟩ := fold_enc L base pb (encBands prec) T (packets g .lrcp #[])
    { precs, hdr := H, body := (encodeTileLRCP prec).data.toList ++ T }
    (nodup_map_of_inj _ hnd (fun x hx y hy he => hinj x y ((hmem x).1 hx) ((hmem y).1 hy) he))
    (fun p hp => by have := ((hmem p).1 hp).1; omega)
    (fun p hp => hready p ((hmem p).1 hp))
    (by simpa using hpass)
    (by rw [encodeTileLRCP_eq g hwf hlay prec hs])
  exact ⟨s', h1, h2, by simpa using h3, fun p hp => h5 p ((hmem p).2 hp)⟩

end JPEG2000.Spec.RoundTrip
