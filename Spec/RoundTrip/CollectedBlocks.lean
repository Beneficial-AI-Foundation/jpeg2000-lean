import Spec.RoundTrip.BlockReconstruction

/-!
# Collecting the reversible encoder's code-blocks

Plan.md §§4, 5.3 and 7 (C10, M7), T.800 B.7, Annex D and E.1.1.2.
The spec visits resolutions, precincts, bands and blocks in list order, consing each
included block. Its reversible grid reads the original encoder band in raster order
at a coordinate covered by a unique physical block, including a block with no passes.
-/

namespace JPEG2000.Spec.RoundTrip

open JPEG2000.Header (CompParams Rect)
open JPEG2000.Tier2.Geometry
open JPEG2000.Spec.Decode
open JPEG2000.Spec.Tier2 (BandOut BlockSt)
open JPEG2000.Encode.Tier1 (maxMag numBits)

/-- A physical block at its four nested indices in a decoded component. -/
def ComponentBlockAt (rs : SpecPrecs) (r j bi k : Nat) (b : Band) (sb : BlockSt) : Prop :=
  ∃ ps bs bo, rs[r]? = some ps ∧ ps[j]? = some bs ∧ bs[bi]? = some bo ∧
    bo.blocks[k]? = some sb ∧ bo.band = b

private def blockEntries (p : CompParams) (depth r : Nat) (b : Band) (cb : BlockSt) : List Entry :=
  if cb.passes != 0 && !rectEmpty cb.geom.rect then
    match decodeBlockSt p r b cb with
    | .ok cs => [⟨r, b, cb.geom.rect, Spec.Quant.bandQuant p depth r b, cs⟩]
    | .error _ => []
  else []

/-- The spec's entries in newest-first order, at full resolution. The outer bound is
the same minimum as the real collection loop. -/
def collectedEntries (p : CompParams) (depth : Nat) (rs : SpecPrecs) : List Entry :=
  ((List.range (min (p.levels + 1) rs.length)).flatMap fun r =>
    (rs.getD r []).flatMap fun bs => bs.flatMap fun bo =>
      bo.blocks.flatMap (blockEntries p depth r bo.band)).reverse

private abbrev State := List Entry × Nat

private theorem for_entries {α : Type} (xs : List α) (es : α → List Entry)
    (f : α → State → Except Error (ForInStep State))
    (step : ∀ x ∈ xs, ∀ s : State, f x s = .ok (.yield ((es x).reverse ++ s.1, s.2)))
    (s : State) : forIn xs s f = .ok ((xs.flatMap es).reverse ++ s.1, s.2) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    rw [List.forIn_cons, step x List.mem_cons_self]
    change forIn xs _ f = _
    rw [ih (fun y hy => step y (List.mem_cons_of_mem _ hy))]
    simp only [List.flatMap_cons, List.reverse_append, List.append_assoc]

private theorem nest_entries {α : Type} (xs : List α) (es : α → List Entry)
    (f : α → State → Except Error (ForInStep State)) (s : State)
    (step : ∀ x ∈ xs, ∀ t : State, f x t = .ok (.yield ((es x).reverse ++ t.1, t.2))) :
    (forIn xs s f >>= fun t => pure (.yield (t.1, t.2))) =
      (.ok (.yield ((xs.flatMap es).reverse ++ s.1, s.2)) : Except Error (ForInStep State)) := by
  rw [for_entries xs es f step]; rfl

private theorem reduce_zero (rect : Rect) : Assemble.reduceRect rect 0 = rect := by
  cases rect
  simp [Assemble.reduceRect, Header.cdivPow, Header.cdiv]

private theorem collect_component (L : Limits) (tc : TileCompGeom) (depth F : Nat)
    (rs : SpecPrecs) (hw : tc.rect.width * tc.rect.height ≤ L.maxWorkSamples)
    (hd : ∀ r j bi k b cb, ComponentBlockAt rs r j bi k b cb →
      ∃ cs, decodeBlockSt tc.params r b cb = .ok cs) :
    Decode.tileComp L tc depth F 0 rs =
      finSpec (tc.params.transform == .reversible53) (collectedEntries tc.params depth rs)
        tc.rect tc.params.levels 0 := by
  unfold Decode.tileComp
  simp only [Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero, reduce_zero, initSpec,
    (Limits.check_eq_ok_iff L Assemble.loc .workSamples _).2 hw, bind, Except.bind, pure, Except.pure]
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_one_sub_one, Nat.div_one,
    ← List.range_eq_range']
  let resEntries := fun r => (rs.getD r []).flatMap fun bs => bs.flatMap fun bo =>
    bo.blocks.flatMap (blockEntries tc.params depth r bo.band)
  rw [for_entries _ resEntries _ ?_]
  · simp [collectedEntries, resEntries]
  intro r hr s
  apply nest_entries
  intro bs hbs t
  apply nest_entries
  intro bo hbo z
  apply nest_entries
  intro cb hcb a
  have hr' := Nat.lt_of_lt_of_le (List.mem_range.mp hr) (Nat.min_le_right _ _)
  have hps : rs[r]? = some (rs.getD r []) := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr', Option.getD_some]
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hbs
  obtain ⟨bi, hbi⟩ := List.getElem?_of_mem hbo
  obtain ⟨k, hk⟩ := List.getElem?_of_mem hcb
  obtain ⟨cs, hcs⟩ := hd r j bi k bo.band cb ⟨_, _, _, hps, hj, hbi, hk, rfl⟩
  dsimp only [blockEntries]
  split <;> simp_all [collect, pure, Except.pure]

private theorem mem_collected {p : CompParams} {depth : Nat} {rs : SpecPrecs} {e : Entry} :
    e ∈ collectedEntries p depth rs ↔ ∃ r j bi k b cb, r ≤ p.levels ∧
      ComponentBlockAt rs r j bi k b cb ∧ e ∈ blockEntries p depth r b cb := by
  simp only [collectedEntries, List.mem_reverse, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨r, hr, bs, hbs, bo, hbo, cb, hcb, he⟩
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hbs
    obtain ⟨bi, hbi⟩ := List.getElem?_of_mem hbo
    obtain ⟨k, hk⟩ := List.getElem?_of_mem hcb
    have hi : r < rs.length := by omega
    refine ⟨r, j, bi, k, bo.band, cb, by omega, ⟨_, bs, bo, ?_, hj, hbi, hk, rfl⟩, he⟩
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  · rintro ⟨r, j, bi, k, b, cb, hr, ⟨ps, bs, bo, hp, hj, hbi, hk, rfl⟩, he⟩
    have hi := (List.getElem?_eq_some_iff.mp hp).1
    refine ⟨r, by omega, bs, ?_, bo, List.mem_of_getElem? hbi, cb, List.mem_of_getElem? hk, he⟩
    simpa only [List.getD_eq_getElem?_getD, hp, Option.getD_some] using List.mem_of_getElem? hj

/-- A coordinate of a band in the half-open rectangle of a physical code-block. -/
def BlockContains (rect : Rect) (u v : Nat) : Prop :=
  rect.x0 ≤ u ∧ u < rect.x1 ∧ rect.y0 ≤ v ∧ v < rect.y1

private theorem grid_at_block {p : CompParams} {depth : Nat} {rs : SpecPrecs}
    {r j bi k : Nat} {b : Band} {cb : BlockSt} {src : Array Int} {u v : Nat}
    (hr : r ≤ p.levels) (ha : ComponentBlockAt rs r j bi k b cb)
    (hxy : BlockContains cb.geom.rect u v)
    (hu : ∀ r' j' bi' k' b' cb', r' ≤ p.levels → ComponentBlockAt rs r' j' bi' k' b' cb' →
      b' = b → bandLevel p.levels r' = bandLevel p.levels r →
      BlockContains cb'.geom.rect u v → r' = r ∧ cb' = cb)
    (hc : ReconstructsBlock p r b cb src) :
    (bandGrid53 (collectedEntries p depth rs) p.levels (bandLevel p.levels r) b).get u v =
      src.getD ((v - cb.geom.rect.y0) * cb.geom.rect.width + (u - cb.geom.rect.x0)) 0 := by
  obtain ⟨cs, hd, _, _, hdeq, hz⟩ := hc
  let target : Entry := ⟨r, b, cb.geom.rect, Spec.Quant.bandQuant p depth r b, cs⟩
  let test (e : Entry) := e.band == b && bandLevel p.levels e.r == bandLevel p.levels r &&
    e.covers u v
  let es := collectedEntries p depth rs
  have inside : test target = true := by
    simpa [test, target, Entry.covers, BlockContains] using hxy
  have hne : rectEmpty cb.geom.rect = false := by
    obtain ⟨_, _, _, _⟩ := hxy
    simp [rectEmpty]; omega
  have unique (e : Entry) (he : e ∈ es) (htest : test e = true) :
      e = target := by
    obtain ⟨r', j', bi', k', b', cb', hr', ha', he'⟩ := mem_collected.mp he
    unfold blockEntries at he'
    split at he'
    · split at he'
      · rename_i cs' hd'
        obtain rfl := List.mem_singleton.mp he'
        simp only [test, Entry.covers, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
          Int.ofNat_le, Int.ofNat_lt] at htest
        obtain ⟨⟨rfl, hl⟩, hc'⟩ := htest
        obtain ⟨rfl, rfl⟩ := hu _ _ _ _ _ _ hr' ha' rfl hl hc'
        rw [hd] at hd'
        cases hd'
        rfl
      · cases he'
    · cases he'
  change (match es.find? test with
    | some e => Spec.Quant.dequantRev e.q.roiShift (e.coeff u v)
    | none => 0) = _
  cases hf : es.find? test with
  | none =>
    have hzero : cb.passes = 0 := by
      apply Classical.byContradiction
      intro hn
      have hm : target ∈ es := mem_collected.mpr ⟨r, j, bi, k, b, cb, hr, ha, by
        simp [blockEntries, hn, hne, hd, target]⟩
      exact (List.find?_eq_none.mp hf target hm) inside
    change 0 = _
    rw [hz hzero, Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
    split <;> rfl
  | some e =>
    have he := unique e (List.mem_of_find?_eq_some hf) (List.find?_some hf)
    rw [he]
    change Spec.Quant.dequantRev p.roiShift (cs.getD _ {}) = _
    rw [← hdeq]
    simp only [target, ← Int.ofNat_sub (show cb.geom.rect.y0 ≤ v from hxy.2.2.1),
      ← Int.ofNat_sub hxy.1, Int.toNat_natCast, Spec.Quant.dequantBlockRev,
      Array.getD_eq_getD_getElem?, Array.getElem?_map]
    cases cs[(v - cb.geom.rect.y0) * cb.geom.rect.width + (u - cb.geom.rect.x0)]? with
    | some c => rfl
    | none =>
      simp [Spec.Quant.dequantRev, Spec.Quant.roiUnshift, Spec.Quant.reconstructRev,
        show ¬2 ^ p.roiShift ≤ 0 by exact Nat.not_le_of_lt (Nat.two_pow_pos _)]

/-- On a coordinate inside the block, its raster slice projects to the corresponding
row and column of the encoder band. -/
theorem blockCoeffs_at {d : Encode.BandData} {rect : Rect} {u v : Nat}
    (h : BlockContains rect u v) :
    (Encode.blockCoeffs d rect).getD ((v - rect.y0) * rect.width + (u - rect.x0)) 0 =
      d.vals.getD ((v - d.rect.y0) * d.rect.width + (u - d.rect.x0)) 0 := by
  obtain ⟨hx, hx', hy, hy'⟩ := h
  let x := u - rect.x0
  let y := v - rect.y0
  let w := rect.width
  have hxl : x < w := by dsimp [x, w, Header.Rect.width]; omega
  have hyl : y < rect.height := by dsimp [y, Header.Rect.height]; omega
  have hw : 0 < w := by omega
  have hidx : y * w + x < w * rect.height := by
    have h1 := Nat.add_lt_add_left hxl (y*w)
    have h2 := Nat.mul_le_mul_right w hyl
    rw [Nat.succ_mul, Nat.mul_comm rect.height w] at h2
    exact Nat.lt_of_lt_of_le h1 h2
  change (Encode.blockCoeffs d rect).getD (y*w+x) 0 = _
  simp only [Encode.blockCoeffs, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn,
    show y*w+x < rect.width * rect.height from hidx, ↓reduceDIte, Option.getD_some]
  have hm : (y*w+x) % w = x := by rw [Nat.mul_comm y w, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hxl]
  have hd : (y*w+x) / w = y := by rw [Nat.mul_comm y w, Nat.mul_add_div hw, Nat.div_eq_of_lt hxl, Nat.add_zero]
  change d.vals[(rect.y0 + (y*w+x) / w - d.rect.y0) * d.rect.width +
    (rect.x0 + (y*w+x) % w - d.rect.x0)]?.getD 0 = _
  rw [hm, hd, show rect.y0+y = v by dsimp [y]; omega,
    show rect.x0+x = u by dsimp [x]; omega]

/-- The decoder's returned block at an address has the physical geometry of the
encoder call at that address, even for a zero-pass codeword. -/
theorem DecodedEncoderTile.packetBlockAt {L : Limits} {p : Encode.Params} {img : Encode.Image}
    {e : Encode.Encoded} {prec infos tile} (hp : ReversibleTilePackets p img e prec infos)
    (ht : DecodedEncoderTile L (encLayout p img e.guardBits e.exponents) prec tile)
    {c r j bi k : Nat} {rs b sb} (hrs : tile.comps[c]? = some rs)
    (ha : ComponentBlockAt rs r j bi k b sb) :
    ∃ pb o, PacketBlockCall Limits.default (encGeom p img e.guardBits e.exponents)
      ((Encode.bands53 p img (encMct p img)).getD c #[]) r j bi k pb sb.geom o ∧ pb.band = b := by
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
  have hx := Array.getElem?_eq_getElem (nbs ▸ (List.getElem?_eq_some_iff.mp hsb).1)
  obtain ⟨pb, cb, o, call, _, hx'⟩ := hp.packetBlock hq hb hx
  rw [hx'] at hx
  have hcomp := encLayout_comp p img e.guardBits e.exponents c
    ((encLayout_coding p img e.guardBits e.exponents).1 ▸ hci)
  rw [hcomp] at hres hst
  obtain ⟨_, _, hbo'', hsb', hband, hgeom, _, _⟩ :=
    hd.reconstructBlock hres hpg hst hb hx call rfl rfl
  obtain rfl := Option.some.inj (hbo''.symm.trans hbo')
  obtain rfl := Option.some.inj (hsb'.symm.trans hsb)
  exact ⟨pb, o, hgeom.symm ▸ call, hband.symm⟩

/-- The 31-plane C10 bound, quantified only over actual Tier-1 calls of this component. -/
def ComponentPlanes31 (tc : TileCompGeom) (source : Array (Array Encode.BandData)) : Prop :=
  ∀ r j bi k pb cb o, PacketBlockCall Limits.default tc source r j bi k pb cb o →
    numBits (maxMag (packetBlockCoeffs source r bi cb)) ≤ 31

open JPEG2000.Spec.Tier2Equiv (bind_ok)
open JPEG2000.Tier2.Packet (PrecState)
open JPEG2000.Spec.Tier2 (PrecSt)

private theorem mapM_at_source {α β : Type} {f : α → Except Error β} :
    ∀ {xs : List α} {ys : List β} {i : Nat} {x : α}, xs.mapM f = .ok ys → xs[i]? = some x →
      ∃ y, ys[i]? = some y ∧ f x = .ok y
  | [], _, _, _, _, hx => by simp at hx
  | x :: xs, _, i, _, h, hx => by
    rw [List.mapM_cons] at h
    obtain ⟨y, hy, h⟩ := bind_ok h
    obtain ⟨ys, hys, h⟩ := bind_ok h
    cases h
    cases i with
    | zero => cases hx; exact ⟨y, rfl, hy⟩
    | succ i => exact mapM_at_source (xs := xs) (i := i) hys hx

private theorem arrayMapM_at_source {α β : Type} {f : α → Except Error β}
    {xs : Array α} {ys : Array β} {i : Nat} {x : α} (h : xs.mapM f = .ok ys)
    (hx : xs[i]? = some x) : ∃ y, ys[i]? = some y ∧ f x = .ok y := by
  rw [Array.mapM_eq_mapM_toList] at h
  cases hm : xs.toList.mapM f with
  | error e => rw [hm] at h; cases h
  | ok bs =>
    rw [hm] at h; cases h
    simpa only [List.getElem?_toArray] using
      mapM_at_source hm (by simpa only [Array.getElem?_toList] using hx)

private theorem initialized_at {L : Limits} {params : CompParams} {r bi k : Nat}
    {pg : PrecinctGeom} {pb : PrecinctBandGeom} {cb : CodeBlockGeom} {st : PrecState}
    (hst : PrecState.init L params r pg = .ok st)
    (hpb : pg.bands[bi]? = some pb) (hcb : pb.codeBlocks[k]? = some cb) :
    ∃ bs, (PrecSt.ofFast st).bands[bi]? = some bs ∧ bs.band = pb.band ∧
      bs.blocks[k]? = some ({ geom := cb } : BlockSt) := by
  unfold PrecState.init at hst
  obtain ⟨bands, hmap, hst⟩ := bind_ok hst
  cases hst
  obtain ⟨b, hb, he⟩ := arrayMapM_at_source hmap hpb
  obtain ⟨_, _, he⟩ := bind_ok he
  obtain ⟨_, _, he⟩ := bind_ok he
  cases he
  simp only [PrecSt.ofFast, List.getElem?_map, Array.getElem?_toList, hb, Option.map_some,
    Option.some.injEq, exists_eq_left', true_and, Array.toList_map, hcb]

private theorem resolution_count {L : Limits} {g : Progression.Layout} {c r : Nat}
    {res : ResolutionGeom} (h : resolution L (g.comp c) r = .ok res) :
    res.numPrecincts = g.pw c r * g.ph c r := by
  unfold resolution at h
  dsimp only at h
  split at h
  · cases h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  cases h
  rfl

private theorem call_band_mem {L : Limits} {tc source r j bi k pb cb o}
    (call : PacketBlockCall L tc source r j bi k pb cb o) : pb.band ∈ bandsOf r := by
  obtain ⟨res, pg, hr, hj, hbi, _⟩ := call.geometry
  obtain ⟨b, hb, heq, _⟩ := Spec.Tier2WF.precinct_bands hj pb
    (Array.mem_iff_getElem?.mpr ⟨bi, hbi⟩)
  rw [heq]
  exact (Spec.Tier2WF.resolution_bands hr b hb).1

private theorem same_band_resolution {nl r s : Nat} {b : Band} (hr : r ≤ nl) (hs : s ≤ nl)
    (hb : b ∈ bandsOf r) (hb' : b ∈ bandsOf s) (hl : bandLevel nl r = bandLevel nl s) : r = s := by
  cases r <;> cases s <;> simp_all [bandsOf, bandLevel] <;> omega

private theorem at_functional {rs : SpecPrecs} {r j bi k : Nat} {b b' sb sb'}
    (h : ComponentBlockAt rs r j bi k b sb) (h' : ComponentBlockAt rs r j bi k b' sb') :
    sb = sb' := by
  obtain ⟨ps, bs, bo, hr, hj, hbi, hk, _⟩ := h
  obtain ⟨_, _, _, hr', hj', hbi', hk', _⟩ := h'
  obtain rfl := Option.some.inj (hr.symm.trans hr')
  obtain rfl := Option.some.inj (hj.symm.trans hj')
  obtain rfl := Option.some.inj (hbi.symm.trans hbi')
  exact Option.some.inj (hk.symm.trans hk')

section Component

variable {L : Limits} {p : Encode.Params} {img : Encode.Image} {e : Encode.Encoded}
  {prec infos tile} (hp : ReversibleTilePackets p img e prec infos)
  (ht : DecodedEncoderTile L (encLayout p img e.guardBits e.exponents) prec tile)
  {c : Nat} {rs : SpecPrecs} (hrs : tile.comps[c]? = some rs)
  (hK : ComponentPlanes31 (encGeom p img e.guardBits e.exponents)
    ((Encode.bands53 p img (encMct p img)).getD c #[]))

include hp ht hrs in
/-- A geometric block selected by precinct and raster index occurs at those same
indices in the decoded component, with its band label and rectangle intact. -/
theorem DecodedEncoderTile.blockAtGeometry {r j bi k : Nat} {res pg pb cb}
    (hr : r ≤ p.levels) (hres : resolution L (encGeom p img e.guardBits e.exponents) r = .ok res)
    (hj : j < res.numPrecincts) (hpg : precinct L res j = .ok pg)
    (hpb : pg.bands[bi]? = some pb) (hcb : pb.codeBlocks[k]? = some cb) :
    ∃ sb, ComponentBlockAt rs r j bi k pb.band sb ∧ sb.geom = cb := by
  let g := encLayout p img e.guardBits e.exponents
  have hci : c < g.numComps := ht.count ▸ (List.getElem?_eq_some_iff.mp hrs).1
  have hc := (encLayout_coding p img e.guardBits e.exponents).1 ▸ hci
  have hcomp := encLayout_comp p img e.guardBits e.exponents c hc
  have hri : r ≤ g.levels c := by
    unfold Progression.Layout.levels
    rw [show g.comp c = _ from hcomp]
    exact hr
  have hr' : resolution L (g.comp c) r = .ok res := hcomp ▸ hres
  obtain ⟨_, hrs', _, resAt⟩ := ht.component c hci
  obtain rfl := Option.some.inj (hrs'.symm.trans hrs)
  obtain ⟨_, ps, hres', hps, nps, precAt⟩ := resAt r hri
  obtain rfl := Except.ok.inj (hres'.symm.trans hr')
  obtain ⟨_, st, out, hpg', hst, hout, hd⟩ := precAt j
    (by rw [nps, ← resolution_count hr']; exact hj)
  obtain rfl := Except.ok.inj (hpg'.symm.trans hpg)
  rw [hcomp] at hst
  obtain ⟨bs, hbs, hb, hk⟩ := initialized_at hst hpb hcb
  have henc := hp.component c hc
  rw [tileComp_enc _ _ _ _ _ hc] at henc
  have hn := (encodeComp_precinctGeometry henc hr hj hres hpg hst).2.1
  let q : Progression.PacketId := ⟨0, r, c, j⟩
  have hbi : bi < (encBands prec q).size := hn ▸ (List.getElem?_eq_some_iff.mp hbs).1
  obtain ⟨_, bo, hbs', hbo, rfl, _, _⟩ := hd.band bi _ (Array.getElem?_eq_getElem hbi)
  obtain rfl := Option.some.inj (hbs'.symm.trans hbs)
  refine ⟨blockAfter { geom := cb } ((encBands prec q)[bi].blocks.getD k default),
    ⟨_, _, _, hps, hout, hbo, ?_, hb⟩, ?_⟩
  · simp only [outAfter, List.getElem?_mapIdx, hk, Option.map_some]
  · rw [blockAfter_fresh]
    split <;> rfl

include hp ht hrs hK
private theorem reconstruct_at {r j bi k : Nat} {b sb} (ha : ComponentBlockAt rs r j bi k b sb) :
    ReconstructsBlock (encParams p e.guardBits e.exponents) r b sb
      (packetBlockCoeffs ((Encode.bands53 p img (encMct p img)).getD c #[]) r bi sb.geom) := by
  obtain ⟨pb, o, call, _⟩ := ht.packetBlockAt hp hrs ha
  obtain ⟨ps, bs, bo, hps, hbs, hbo, hsb, rfl⟩ := ha
  exact ht.reconstructBlock hp hrs hps hbs hbo hsb (hK _ _ _ _ pb _ o call)

/-- **C10 collection.** The real spec loop at zero reduction reaches the inverse DWT
with exactly the newest-first entries of this component and saturation count zero.
The only work check is the area of the full-resolution component. -/
theorem DecodedEncoderTile.tileComp_collected (hrev : p.reversible = true)
    (hw : img.width * img.height ≤ L.maxWorkSamples) (depth F : Nat) :
    Decode.tileComp L (encGeom p img e.guardBits e.exponents) depth F 0 rs =
      finSpec true (collectedEntries (encParams p e.guardBits e.exponents) depth rs)
        (encRect img) p.levels 0 := by
  apply Eq.trans (collect_component L _ _ _ _ ?_ ?_)
  · simp [encGeom, encParams, hrev]
  · simpa [encGeom, encRect, Header.Rect.width, Header.Rect.height] using hw
  · intro r j bi k b sb ha
    obtain ⟨cs, hd, _⟩ := reconstruct_at hp ht hrs hK ha
    exact ⟨cs, hd⟩

/-- **C10 band sample.** At a uniquely covered band coordinate the actual collection's
5/3 grid equals the encoder band's row-major sample. Uniqueness concerns only physical
geometry (including blocks with no passes). -/
theorem DecodedEncoderTile.bandGrid53_collected (depth : Nat) {r j bi k u v : Nat}
    {b : Band} {sb : BlockSt} (hr : r ≤ p.levels) (ha : ComponentBlockAt rs r j bi k b sb)
    (hxy : BlockContains sb.geom.rect u v)
    (hu : ∀ j' bi' k' pb cb o,
      PacketBlockCall Limits.default (encGeom p img e.guardBits e.exponents)
        ((Encode.bands53 p img (encMct p img)).getD c #[]) r j' bi' k' pb cb o →
      pb.band = b → BlockContains cb.rect u v → j' = j ∧ bi' = bi ∧ k' = k) :
    let source := (Encode.bands53 p img (encMct p img)).getD c #[]
    let d := (source.getD r #[]).getD bi default
    (bandGrid53 (collectedEntries (encParams p e.guardBits e.exponents) depth rs)
      p.levels (bandLevel p.levels r) b).get u v =
      d.vals.getD ((v - d.rect.y0) * d.rect.width + (u - d.rect.x0)) 0 := by
  apply Eq.trans (grid_at_block hr ha hxy ?_ (reconstruct_at hp ht hrs hK ha)) (blockCoeffs_at hxy)
  intro r' j' bi' k' b' sb' hr' ha' hb hl hxy'
  subst b'
  obtain ⟨pb, o, call, label⟩ := ht.packetBlockAt hp hrs ha
  obtain ⟨pb', o', call', label'⟩ := ht.packetBlockAt hp hrs ha'
  obtain rfl : r' = r := same_band_resolution hr' hr (label' ▸ call_band_mem call')
    (label ▸ call_band_mem call) hl
  obtain ⟨rfl, rfl, rfl⟩ := hu _ _ _ _ _ _ call' label' hxy'
  exact ⟨rfl, at_functional ha' ha⟩

end Component

end JPEG2000.Spec.RoundTrip
