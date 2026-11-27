import Spec.RoundTrip.Layout
import Spec.RoundTrip.TileBytes
import Spec.RoundTrip.Tier2

/-!
# Encoded precincts and fresh decoder bands

Plan.md §§4 (C10), 5.3 and 7 (M7), task 7.3f4. T.800 B.5–B.7 and B.10.
The resolution, precinct and band loops in `encodeComp` retain the order and
dimensions of the geometry used by the decoder to initialize the tile.
-/

namespace JPEG2000.Spec.RoundTrip

open JPEG2000.Encode (encodeComp BlockInfo BandData)
open JPEG2000.Encode.Tier2 (BandIn BlockIn)
open JPEG2000.Tier2.Geometry
open JPEG2000.Tier2.Packet (PrecState BandState bandMb initPrecincts)
open JPEG2000.Spec.Tier2 (BandSt PrecSt)
open JPEG2000.Spec.Tier2Equiv (bind_ok)
open JPEG2000.Progression (Layout)
open JPEG2000.Header (CompParams)

private abbrev EncPrec := Array BandIn
private abbrev EncRes := Array EncPrec
private abbrev EncComp := Array EncRes

/-- The grid, bit-plane bound and number of blocks written for a precinct-band. -/
def EncBandGeometry (params : CompParams) (r : Nat) (pb : PrecinctBandGeom) (b : BandIn) : Prop :=
  b.cw = pb.cw ∧ b.ch = pb.ch ∧ b.maxZero = bandMb params r pb.band + params.roiShift ∧
    b.blocks.size = pb.codeBlocks.size

private def Entries {α : Type} (P : Nat → α → Prop) (n : Nat) (xs : Array α) : Prop :=
  xs.size = n ∧ ∀ i < n, ∃ x, xs[i]? = some x ∧ P i x

private theorem entries_empty {α : Type} (P : Nat → α → Prop) : Entries P 0 #[] :=
  ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩

private theorem Entries.push {α : Type} {P : Nat → α → Prop} {n : Nat} {xs : Array α} {x : α}
    (h : Entries P n xs) (hx : P n x) : Entries P (n + 1) (xs.push x) := by
  refine ⟨by simp [h.1], fun i hi => ?_⟩
  by_cases he : i = n
  · subst i
    exact ⟨_, by rw [Array.getElem?_push, h.1, ite_eq_left rfl], hx⟩
  · obtain ⟨y, hy, hP⟩ := h.2 i (by omega)
    exact ⟨_, Spec.Tier2WF.getElem?_push_of_some hy, hP⟩

private theorem range_inv {β : Type} (P : Nat → β → Prop) {n : Nat} {init out : β}
    {f : Nat → β → Except Error (ForInStep β)} (h0 : P 0 init)
    (h : forIn [0:n] init f = .ok out)
    (step : ∀ i b t, P i b → f i b = .ok t → ∃ b', t = .yield b' ∧ P (i+1) b') :
    P n out := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at h
  simpa [Std.Legacy.Range.size] using
    Spec.Tier2WF.forIn_range'_inv P f step [0:n].size 0 init out h0 h

private theorem blocks_size {α β : Type} (size : β → Nat) (f : α → β → Except Error (ForInStep β))
    (step : ∀ a b t, f a b = .ok t → ∃ b', t = .yield b' ∧ size b' = size b + 1) :
    ∀ (xs : List α) (b out : β), forIn xs b f = .ok out → size out = size b + xs.length
  | [], b, out, h => by simp only [List.forIn_nil] at h; cases h; simp
  | x :: xs, b, out, h => by
    rw [List.forIn_cons] at h
    obtain ⟨t, ht, h⟩ := bind_ok h
    obtain ⟨b', rfl, hb'⟩ := step x b t ht
    rw [blocks_size size f step xs b' out h, hb', List.length_cons]; omega

private def EncPrecGeometry (params : CompParams) (r : Nat) (pg : PrecinctGeom) (bs : EncPrec) :=
  Entries (fun bi b => ∃ pb, pg.bands[bi]? = some pb ∧ EncBandGeometry params r pb b)
    pg.bands.size bs

private def EncResGeometry (L : Limits) (tc : TileCompGeom) (r : Nat) (ps : EncRes) :=
  ∃ res, resolution L tc r = .ok res ∧
    Entries (fun p bs => ∃ pg, precinct L res p = .ok pg ∧ EncPrecGeometry tc.params r pg bs)
      res.numPrecincts ps

private theorem component_entries {L : Limits} {tc : TileCompGeom} {c : Nat}
    {bands : Array (Array BandData)} {out : EncComp} {infos : Array BlockInfo}
    (h : encodeComp L tc c bands = .ok (out, infos)) :
    Entries (EncResGeometry L tc) (tc.params.levels + 1) out := by
  unfold encodeComp at h
  dsimp only at h
  obtain ⟨s, hs, h⟩ := bind_ok h
  cases h
  refine range_inv (fun i (st : EncComp × Array BlockInfo) =>
    Entries (EncResGeometry L tc) i st.1) (entries_empty _) hs ?_
  intro r st t hst ht
  obtain ⟨res, hr, ht⟩ := bind_ok ht
  obtain ⟨ps, hps, ht⟩ := bind_ok ht
  cases ht
  refine ⟨_, rfl, hst.push ⟨res, hr, ?_⟩⟩
  refine range_inv (fun p (s : Array BlockInfo × EncRes) =>
    Entries (fun k bs => ∃ pg, precinct L res k = .ok pg ∧ EncPrecGeometry tc.params r pg bs) p s.2) (entries_empty _) hps ?_
  intro p st t hst ht
  obtain ⟨pg, hp, ht⟩ := bind_ok ht
  obtain ⟨bs, hbs, ht⟩ := bind_ok ht
  cases ht
  refine ⟨_, rfl, hst.push ⟨pg, hp, ?_⟩⟩
  refine range_inv (fun bi (s : Array BlockInfo × EncPrec) =>
    Entries (fun k b => ∃ pb, pg.bands[k]? = some pb ∧ EncBandGeometry tc.params r pb b) bi s.2) (entries_empty _) hbs ?_
  intro bi st t hst ht
  split at ht
  next pb hpb =>
    obtain ⟨blocks, hblocks, ht⟩ := bind_ok ht
    cases ht
    refine ⟨_, rfl, hst.push ⟨pb, hpb, rfl, rfl, rfl, ?_⟩⟩
    rw [← Array.forIn_toList] at hblocks
    have hn := blocks_size (fun (s : Array BlockInfo × Array BlockIn) => s.2.size) _ ?_
      _ _ _ hblocks
    · simpa using hn
    intro cb b t ht
    obtain ⟨o, ho, ht⟩ := bind_ok ht
    split at ht
    · cases ht
    · cases ht; exact ⟨_, rfl, Array.size_push _⟩
  next => cases ht

private theorem Entries.lookup {α : Type} {P : Nat → α → Prop} {n : Nat} {xs : Array α}
    (h : Entries P n xs) {i : Nat} (hi : i < n) (d : α) : P i (xs.getD i d) := by
  obtain ⟨x, hx, hP⟩ := h.2 i hi
  rwa [Array.getD_eq_getD_getElem?, hx]

private theorem resolution_grid {L : Limits} {g : Layout} {c r : Nat} {res : ResolutionGeom}
    (h : resolution L (g.comp c) r = .ok res) : res.numPrecincts = g.pw c r * g.ph c r := by
  unfold resolution at h
  dsimp only at h
  split at h
  · cases h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  cases h
  rfl

/-- A successful component call emits every resolution and one entry per precinct in
the layout's grid, including resolutions with an empty precinct grid. -/
theorem encodeComp_shape {L : Limits} {g : Layout} {c : Nat} {bands : Array (Array BandData)}
    {out : Array (Array (Array BandIn))} {infos : Array BlockInfo}
    (h : encodeComp L (g.comp c) c bands = .ok (out, infos)) :
    out.size = g.levels c + 1 ∧ ∀ r ≤ g.levels c,
      (out.getD r #[]).size = g.pw c r * g.ph c r := by
  have he := component_entries h
  refine ⟨he.1, fun r hr => ?_⟩
  obtain ⟨res, hres, hp⟩ := he.lookup (Nat.lt_succ_of_le hr) #[]
  exact hp.1.trans (resolution_grid hres)

/-- The actual LRCP input arrays identified by the reversible encoder satisfy `TileShape`. -/
theorem ReversibleTilePackets.tileShape {p : Encode.Params} {img : Encode.Image} {e : Encode.Encoded}
    {prec infos} (hp : ReversibleTilePackets p img e prec infos) :
    TileShape (encLayout p img e.guardBits e.exponents) prec := by
  have hn := (encLayout_coding p img e.guardBits e.exponents).1
  refine ⟨hp.prec_size.trans hn.symm, fun c hc => ?_⟩
  rw [hn] at hc
  have h := hp.component c hc
  rw [tileComp_enc _ _ _ _ c hc, ← encLayout_comp _ _ _ _ c hc] at h
  exact encodeComp_shape h

private theorem list_mapM_project {α β γ : Type} (f : α → Except Error β) (g : α → γ)
    (v : β → γ) (step : ∀ a b, f a = .ok b → v b = g a) :
    ∀ {xs ys}, xs.mapM f = .ok ys → ys.map v = List.map g xs
  | [], ys, h => by cases h; rfl
  | a :: xs, ys, h => by
    rw [List.mapM_cons] at h
    obtain ⟨b, hb, h⟩ := bind_ok h
    obtain ⟨bs, hbs, h⟩ := bind_ok h
    cases h
    simp only [List.map_cons, step a b hb, list_mapM_project f g v step hbs]

private theorem mapM_project {α β γ : Type} {xs : Array α} {ys : Array β}
    {f : α → Except Error β} (g : α → γ) (v : β → γ) (h : xs.mapM f = .ok ys)
    (step : ∀ a b, f a = .ok b → v b = g a) :
    ys.toList.map v = xs.toList.map g := by
  rw [Array.mapM_eq_mapM_toList] at h
  cases hm : xs.toList.mapM f with
  | error e => rw [hm] at h; cases h
  | ok l =>
    rw [hm] at h; cases h
    exact list_mapM_project f g v step hm

/-- The fresh spec band on the decoder's precinct rectangle, with code-blocks in raster order. -/
def freshBand (params : CompParams) (r : Nat) (pb : PrecinctBandGeom) : BandSt :=
  { band := pb.band, rect := pb.rect, w := pb.cw, h := pb.ch,
    incl := Spec.TagTree.init, zbp := Spec.TagTree.init,
    maxZero := bandMb params r pb.band + params.roiShift,
    blocks := pb.codeBlocks.toList.map fun cb => { geom := cb } }

private theorem init_bands {L : Limits} {params : CompParams} {r : Nat} {pg : PrecinctGeom}
    {st : PrecState} (h : PrecState.init L params r pg = .ok st) :
    (PrecSt.ofFast st).style = params.cbStyle.toNat ∧
    (PrecSt.ofFast st).bands = pg.bands.toList.map (freshBand params r) := by
  unfold PrecState.init at h
  obtain ⟨bs, hbs, h⟩ := bind_ok h
  cases h
  refine ⟨rfl, mapM_project _ _ hbs ?_⟩
  intro pb b hb
  obtain ⟨incl, hi, hb⟩ := bind_ok hb
  obtain ⟨zbp, _, hb⟩ := bind_ok hb
  cases hb
  obtain ⟨_, hw, hh⟩ := Spec.TagTree.create_rel hi
  simp [freshBand, hw, hh, List.map_map, Function.comp_def]

private theorem precinct_block_count {L : Limits} {res : ResolutionGeom} {p : Nat} {pg : PrecinctGeom}
    (h : precinct L res p = .ok pg) : ∀ pb ∈ pg.bands, pb.codeBlocks.size = pb.cw * pb.ch := by
  unfold precinct at h
  dsimp only at h
  split at h
  · cases h
  obtain ⟨bs, hbs, h⟩ := bind_ok h
  cases h
  refine Spec.Tier2WF.arrayMapM_mem (fun pb : PrecinctBandGeom => pb.codeBlocks.size = pb.cw * pb.ch)
    _ _ ?_ _ hbs
  intro b _ pb hb
  obtain ⟨_, _, hb⟩ := bind_ok hb
  cases hb
  simp [codeBlocksOf]

/-- The fresh decoder band satisfies all of `BandReady` once the encoded blocks meet
their Tier-1 admissibility bounds. The two premises refer to the same precinct-band. -/
private theorem fresh_ready {L : Limits} {params : CompParams} {r : Nat} {pb : PrecinctBandGeom}
    {b : BandIn} (he : EncBandGeometry params r pb b) (hc : pb.codeBlocks.size = pb.cw * pb.ch)
    (hok : ∀ k < b.blocks.size, BlockOK L b.maxZero (b.blocks.getD k default)) :
    BandReady L (freshBand params r pb) b := by
  obtain ⟨hw, hh, hm, hn⟩ := he
  refine ⟨hw.symm, hh.symm, hm.symm, rfl, rfl, by rw [hw, hh, hn, hc], ?_, ?_, hok⟩
  · simpa [freshBand] using hn.symm
  · intro cb hcb
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hcb
    rfl

-- Changing the resource limits can change success, but a successful check only returns Unit.
private theorem resolution_unique {L M : Limits} {tc : TileCompGeom} {r : Nat} {a b : ResolutionGeom}
    (ha : resolution L tc r = .ok a) (hb : resolution M tc r = .ok b) : a = b := by
  unfold resolution at ha hb
  dsimp only at ha hb
  split at ha
  · cases ha
  next hn =>
    rw [ite_eq_right hn] at hb
    obtain ⟨_, _, ha⟩ := bind_ok ha
    obtain ⟨_, _, ha⟩ := bind_ok ha
    obtain ⟨_, _, hb⟩ := bind_ok hb
    obtain ⟨_, _, hb⟩ := bind_ok hb
    cases ha; cases hb; rfl

private theorem list_mapM_unique {α β : Type} {f g : α → Except Error β}
    (step : ∀ a x y, f a = .ok x → g a = .ok y → x = y) :
    ∀ {xs : List α} {ys zs}, xs.mapM f = .ok ys → xs.mapM g = .ok zs → ys = zs
  | [], _, _, ha, hb => by cases ha; cases hb; rfl
  | a :: xs, _, _, ha, hb => by
    rw [List.mapM_cons] at ha hb
    obtain ⟨x, hx, ha⟩ := bind_ok ha
    obtain ⟨ys, hys, ha⟩ := bind_ok ha
    obtain ⟨y, hy, hb⟩ := bind_ok hb
    obtain ⟨zs, hzs, hb⟩ := bind_ok hb
    cases ha; cases hb
    rw [step a x y hx hy, list_mapM_unique step hys hzs]

private theorem mapM_unique {α β : Type} {f g : α → Except Error β} {xs : Array α} {ys zs}
    (ha : xs.mapM f = .ok ys) (hb : xs.mapM g = .ok zs)
    (step : ∀ a x y, f a = .ok x → g a = .ok y → x = y) : ys = zs := by
  rw [Array.mapM_eq_mapM_toList] at ha hb
  cases hf : xs.toList.mapM f with
  | error _ => rw [hf] at ha; cases ha
  | ok fs =>
    rw [hf] at ha; cases ha
    cases hg : xs.toList.mapM g with
    | error _ => rw [hg] at hb; cases hb
    | ok gs =>
      rw [hg] at hb; cases hb
      rw [list_mapM_unique step hf hg]

private theorem precinct_unique {L M : Limits} {res : ResolutionGeom} {p : Nat} {a b : PrecinctGeom}
    (ha : precinct L res p = .ok a) (hb : precinct M res p = .ok b) : a = b := by
  unfold precinct at ha hb
  dsimp only at ha hb
  split at ha
  · cases ha
  next hn =>
    rw [ite_eq_right hn] at hb
    obtain ⟨bs, hbs, ha⟩ := bind_ok ha
    obtain ⟨cs, hcs, hb⟩ := bind_ok hb
    cases ha; cases hb
    have he : bs = cs := by
      refine mapM_unique hbs hcs ?_
      intro band x y hx hy
      obtain ⟨_, _, hx⟩ := bind_ok hx
      obtain ⟨_, _, hy⟩ := bind_ok hy
      cases hx; cases hy; rfl
    rw [he]

/-- The successful component call and decoder initializer agree on band order, rectangles,
leaf grids, bit-plane bounds and raster block counts. This holds independently of packet
admissibility and with distinct encoder and decoder limits. -/
theorem encodeComp_precinctGeometry {L M : Limits} {tc : TileCompGeom} {c r p : Nat}
    {bands : Array (Array BandData)} {out : Array (Array (Array BandIn))} {infos : Array BlockInfo}
    {res : ResolutionGeom} {pg : PrecinctGeom} {st : PrecState}
    (he : encodeComp L tc c bands = .ok (out, infos))
    (hr : r ≤ tc.params.levels) (hp : p < res.numPrecincts)
    (hres : resolution M tc r = .ok res) (hpg : precinct M res p = .ok pg)
    (hi : PrecState.init M tc.params r pg = .ok st) :
    let bs := (out.getD r #[]).getD p #[]
    (PrecSt.ofFast st).style = tc.params.cbStyle.toNat ∧
      (PrecSt.ofFast st).bands.length = bs.size ∧
      ∀ pair ∈ (PrecSt.ofFast st).bands.zip bs.toList, ∃ pb ∈ pg.bands,
        pair.1 = freshBand tc.params r pb ∧ EncBandGeometry tc.params r pb pair.2 ∧
        pb.codeBlocks.size = pb.cw * pb.ch := by
  obtain ⟨res', hres', hs⟩ := (component_entries he).lookup (Nat.lt_succ_of_le hr) #[]
  obtain rfl := resolution_unique hres hres'
  obtain ⟨pg', hpg', hb⟩ := hs.lookup hp #[]
  obtain rfl := precinct_unique hpg hpg'
  obtain ⟨hst, hbs⟩ := init_bands hi
  let bs := (out.getD r #[]).getD p #[]
  change EncPrecGeometry tc.params r pg bs at hb
  refine ⟨hst, by simp only [hbs, List.length_map, Array.length_toList]; exact hb.1.symm,
    fun pair hpair => ?_⟩
  rw [hbs] at hpair
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hpair
  have hbi : i < pg.bands.size := by
    simp only [List.length_zip, List.length_map, Array.length_toList] at hi
    omega
  obtain ⟨b, hbi', pb, hpb, hg⟩ := hb.2 i hbi
  obtain ⟨hib, heb⟩ := Array.getElem?_eq_some_iff.mp hbi'
  obtain ⟨hipb, hepb⟩ := Array.getElem?_eq_some_iff.mp hpb
  simp only [List.getElem_zip, List.getElem_map, Array.getElem_toList]
  subst b; subst pb
  exact ⟨_, Array.getElem_mem hipb, rfl, hg, precinct_block_count hpg _ (Array.getElem_mem hipb)⟩

/-- For the same resolution and precinct, the fresh decoder bands match the encoded bands
in packet order. Plain code-block style and individual block admissibility suffice for
`PrecReady`. Encoder and decoder may use different resource limits. -/
theorem encodeComp_precReady {L M : Limits} {tc : TileCompGeom} {c r p : Nat}
    {bands : Array (Array BandData)} {out : Array (Array (Array BandIn))} {infos : Array BlockInfo}
    {res : ResolutionGeom} {pg : PrecinctGeom} {st : PrecState}
    (he : encodeComp L tc c bands = .ok (out, infos))
    (hr : r ≤ tc.params.levels) (hp : p < res.numPrecincts)
    (hres : resolution M tc r = .ok res) (hpg : precinct M res p = .ok pg)
    (hi : PrecState.init M tc.params r pg = .ok st) (hstyle : tc.params.cbStyle.toNat = 0)
    (hok : ∀ b ∈ (out.getD r #[]).getD p #[], ∀ k < b.blocks.size,
      BlockOK M b.maxZero (b.blocks.getD k default)) :
    PrecReady M (PrecSt.ofFast st) ((out.getD r #[]).getD p #[]) := by
  obtain ⟨hsty, hlen, hgeom⟩ := encodeComp_precinctGeometry he hr hp hres hpg hi
  refine ⟨hsty.trans hstyle, hlen, fun pair hpair => ?_⟩
  obtain ⟨pb, _, hbs, hb, hn⟩ := hgeom pair hpair
  rw [hbs]
  exact fresh_ready hb hn (hok _ (Array.mem_def.mpr (List.of_mem_zip hpair).2))

-- The decoder appends every resolution to a single flat array. Earlier lookups survive
-- each append, including across resolutions with no precincts and component boundaries.
private def Preserves (xs ys : Array PrecState) : Prop :=
  ∀ (i : Nat) (st : PrecState), xs[i]? = some st → ys[i]? = some st

private def Paired {α β : Type} (da : α) (db : β) (P : Nat → α → β → Prop)
    (n : Nat) (xs : Array α) (ys : Array β) : Prop :=
  xs.size = n ∧ ys.size = n ∧ ∀ i < n, P i (xs.getD i da) (ys.getD i db)

private theorem paired_empty {α β : Type} (da : α) (db : β) (P : Nat → α → β → Prop) :
    Paired da db P 0 #[] #[] := ⟨rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩

private theorem Paired.push {α β : Type} {da : α} {db : β} {P Q : Nat → α → β → Prop}
    {n : Nat} {xs : Array α} {ys : Array β} {x : α} {y : β}
    (h : Paired da db P n xs ys) (hprev : ∀ i a b, P i a b → Q i a b) (hnew : Q n x y) :
    Paired da db Q (n+1) (xs.push x) (ys.push y) := by
  obtain ⟨hx, hy, h⟩ := h
  refine ⟨by simp [hx], by simp [hy], fun i hi => ?_⟩
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push, hx, hy]
  by_cases he : i = n
  · subst i
    simpa only [ite_true, Option.getD_some] using hnew
  · simp only [ite_eq_right he, ← Array.getD_eq_getD_getElem?]
    exact hprev _ _ _ (h i (by omega))

private def InitAt (L : Limits) (tc : TileCompGeom) (r : Nat) (res : ResolutionGeom)
    (precs : Array PrecState) (start n : Nat) : Prop :=
  ∀ k < n, ∃ pg st, precinct L res k = .ok pg ∧ PrecState.init L tc.params r pg = .ok st ∧
    precs[start + k]? = some st

private theorem InitAt.preserve {L tc r res xs start n ys} (h : InitAt L tc r res xs start n)
    (he : Preserves xs ys) : InitAt L tc r res ys start n := by
  intro k hk
  obtain ⟨pg, st, hp, hs, hi⟩ := h k hk
  exact ⟨pg, st, hp, hs, he _ _ hi⟩

private def InitRow (L : Limits) (tc : TileCompGeom) (precs : Array PrecState)
    (r start : Nat) (span : Nat × Nat) : Prop :=
  ∃ res, resolution L tc r = .ok res ∧ span = (start, res.numPrecincts) ∧
    InitAt L tc r res precs start res.numPrecincts

private theorem InitRow.preserve {L tc xs r start span ys} (h : InitRow L tc xs r start span)
    (he : Preserves xs ys) : InitRow L tc ys r start span := by
  obtain ⟨res, hr, hspan, hk⟩ := h
  exact ⟨res, hr, hspan, hk.preserve he⟩

private abbrev Rows (L : Limits) (tc : TileCompGeom) (precs : Array PrecState) :=
  Paired 0 (0, 0) (InitRow L tc precs)

private theorem rows_preserve {L tc xs n bi si ys} (h : Rows L tc xs n bi si)
    (he : Preserves xs ys) : Rows L tc ys n bi si :=
  ⟨h.1, h.2.1, fun i hi => (h.2.2 i hi).preserve he⟩

private abbrev Components (L : Limits) (g : Layout) (precs : Array PrecState) :=
  Paired #[] #[] (fun c bi si => Rows L (g.comp c) precs (g.levels c + 1) bi si)

private theorem init_components {L : Limits} {g : Layout} {precs base spans}
    (h : initPrecincts L g = .ok (precs, base, spans)) :
    Components L g precs g.numComps base spans := by
  unfold initPrecincts at h
  dsimp only at h
  obtain ⟨s, hs, h⟩ := bind_ok h
  cases h
  refine range_inv (fun c (s : Array PrecState × Array (Array Nat) × Array (Array (Nat × Nat)) × Nat) =>
    Components L g s.1 c s.2.1 s.2.2.1) (paired_empty ..) hs ?_
  intro c b t hb ht
  obtain ⟨s, hs, ht⟩ := bind_ok ht
  cases ht
  have hm : Preserves b.1 s.1 ∧ Rows L (g.comp c) s.1 (g.levels c + 1) s.2.2.1 s.2.2.2 := by
    refine range_inv (fun r (s : Array PrecState × Nat × Array Nat × Array (Nat × Nat)) =>
      Preserves b.1 s.1 ∧ Rows L (g.comp c) s.1 r s.2.2.1 s.2.2.2)
      ⟨fun _ _ h => h, paired_empty ..⟩ hs ?_
    intro r b' t' hb' ht'
    obtain ⟨res, hr, ht'⟩ := bind_ok ht'
    obtain ⟨_, _, ht'⟩ := bind_ok ht'
    obtain ⟨s', hs', ht'⟩ := bind_ok ht'
    cases ht'
    have hp := range_inv (fun k (s : Array PrecState × Nat) =>
      Preserves b'.1 s.1 ∧ s.1.size = b'.1.size + k ∧ InitAt L (g.comp c) r res s.1 b'.1.size k)
      ⟨fun _ _ h => h, rfl, fun _ hk => absurd hk (Nat.not_lt_zero _)⟩ hs' ?_
    · refine ⟨_, rfl, fun i st hi => hp.1 _ _ (hb'.1 i st hi), ?_⟩
      exact hb'.2.push (fun _ _ _ hrow => hrow.preserve hp.1) ⟨res, hr, rfl, hp.2.2⟩
    intro k b'' t'' hb'' ht''
    obtain ⟨pg, hpg, ht''⟩ := bind_ok ht''
    obtain ⟨_, _, ht''⟩ := bind_ok ht''
    obtain ⟨st, hst, ht''⟩ := bind_ok ht''
    cases ht''
    obtain ⟨hpre, hsize, hat⟩ := hb''
    refine ⟨_, rfl, fun i st hi => Spec.Tier2WF.getElem?_push_of_some (hpre i st hi),
      by simp [hsize, Nat.add_assoc], fun j hj => ?_⟩
    by_cases he : j = k
    · subst j
      exact ⟨pg, st, hpg, hst, by rw [Array.getElem?_push, hsize, ite_eq_left rfl]⟩
    · exact hat.preserve (fun _ _ h => Spec.Tier2WF.getElem?_push_of_some h) j (by omega)
  exact ⟨_, rfl, hb.push (fun _ _ _ hrow => rows_preserve hrow hm.1) hm.2⟩

/-- Both decoder lookup tables have one row per component and one entry per resolution. -/
theorem initPrecincts_shape {L : Limits} {g : Layout} {precs base spans}
    (h : initPrecincts L g = .ok (precs, base, spans)) :
    base.size = g.numComps ∧ spans.size = g.numComps ∧ ∀ c < g.numComps,
      (base.getD c #[]).size = g.levels c + 1 ∧ (spans.getD c #[]).size = g.levels c + 1 := by
  have hc := init_components h
  exact ⟨hc.1, hc.2.1, fun c hi => ⟨(hc.2.2 c hi).1, (hc.2.2 c hi).2.1⟩⟩

/-- The decoder records the same start in both lookup tables. Its span has the layout's
precinct count, and each indexed state comes from the indicated geometry and initializer. -/
theorem initPrecincts_geometry {L : Limits} {g : Layout} {precs base spans} {c r : Nat}
    (h : initPrecincts L g = .ok (precs, base, spans)) (hc : c < g.numComps) (hr : r ≤ g.levels c) :
    let start := (base.getD c #[]).getD r 0
    ∃ res, resolution L (g.comp c) r = .ok res ∧ res.numPrecincts = g.pw c r * g.ph c r ∧
      (spans.getD c #[])[r]? = some (start, res.numPrecincts) ∧
      ∀ k < res.numPrecincts, ∃ pg st, precinct L res k = .ok pg ∧
        PrecState.init L (g.comp c).params r pg = .ok st ∧ precs[start + k]? = some st := by
  have hrows := (init_components h).2.2 c hc
  obtain ⟨res, hres, hspan, hat⟩ := hrows.2.2 r (Nat.lt_succ_of_le hr)
  refine ⟨res, hres, resolution_grid hres, ?_, hat⟩
  have hir : r < (spans.getD c #[]).size := hrows.2.1 ▸ Nat.lt_succ_of_le hr
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hir] at hspan
  rw [Array.getElem?_eq_getElem hir, ← hspan]
  rfl

/-- For every packet visited in the encoded layout, the decoder's flat precinct lookup
returns a fresh state ready to read that packet, given the per-block admissibility bounds. -/
theorem ReversibleTilePackets.precReady {p : Encode.Params} {img : Encode.Image} {e : Encode.Encoded}
    {prec infos} (he : ReversibleTilePackets p img e prec infos) {L : Limits} {precs base spans}
    (hi : initPrecincts L (encLayout p img e.guardBits e.exponents) = .ok (precs, base, spans))
    {q : JPEG2000.Progression.PacketId} (hq : (encLayout p img e.guardBits e.exponents).InPacketSet q)
    (hok : ∀ b ∈ encBands prec q, ∀ k < b.blocks.size, BlockOK L b.maxZero (b.blocks.getD k default)) :
    ∃ st, (precs.toList.map PrecSt.ofFast)[precIdx base q]? = some st ∧
      PrecReady L st (encBands prec q) := by
  obtain ⟨_, hc, hr, hk⟩ := hq
  obtain ⟨res, hres, hn, _, hat⟩ := initPrecincts_geometry hi hc hr
  obtain ⟨pg, st, hpg, hst, hidx⟩ := hat q.prec (hn ▸ hk)
  rw [(encLayout_coding p img e.guardBits e.exponents).1] at hc
  have hcomp := he.component q.comp hc
  have htc := encLayout_comp p img e.guardBits e.exponents q.comp hc
  rw [tileComp_enc _ _ _ _ _ hc, ← htc] at hcomp
  refine ⟨_, ?_, encodeComp_precReady hcomp hr (hn ▸ hk) hres hpg hst (by rw [htc]; rfl) hok⟩
  simp only [List.getElem?_map, Array.getElem?_toList, precIdx, hidx, Option.map_some]

end JPEG2000.Spec.RoundTrip
