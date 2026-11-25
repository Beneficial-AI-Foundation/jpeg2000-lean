import Spec.Tier1Wire

/-!
# Tier-2 output well-formedness (`Spec.Equiv.Tier2WF`)
(Plan.md §4 C9, §5.1, §5.2 "Tier-2"; T.800 B.6, B.7, B.9–B.10, A.4.2)

Task 7.1g. `tier2WF` proves the stage hypothesis `Spec.Equiv.Tier2WF` of C9: for every tile
the fast Tier-2 decoder (`Tier2.Headers.decodeWithStream`) returns,

* **`PrecsWF`**: every precinct-band of resolution `r` of component `c` is one of `bandsOf r`
  and its code-blocks lie inside `bandRect` of that band. `precinct_bands` (from
  `Geometry.precinct`: precinct-band = clipped band rectangle, code-block cells clipped to the
  non-empty precinct-band) and `initPrecincts_wf` (the invariant per (component, resolution):
  the span `(start, n)` recorded for `(c, r)` indexes `n` well-formed states) give it for the
  initial states; `decodePacket_shape` shows decoding never changes band labels or code-block
  geometries, so the packet loop (`forPackets_pres`, `fastStep_pres`) keeps the shapes;
* **`BlocksIn`**: `tileData` rejects tile-parts past the end of the input, so its parts lie
  inside `data` (`partsOK_in`) and every translated segment range does too (`out_segsIn`).

`c9_of_hdr` is C9 from `HeaderWF` alone (`Spec.Tier1Wire.c9_of_header tier2WF`).
-/

namespace JPEG2000.Spec.Tier2WF

open JPEG2000 JPEG2000.Bytes JPEG2000.Header JPEG2000.TilePart JPEG2000.Tier2.Geometry
open JPEG2000.Tier2.Packet JPEG2000.Progression
open JPEG2000.Spec.Tier2Equiv (bind_ok forIn_inv arrayMapM_inv headerBand_eq headerBands_eq
  readBody_eq bandBody bandsBody bodyBody)

/-! ## Loop invariants of the packet iteration -/

section Iter
variable {α β : Type}

/-- A step function `f` keeps `P`. -/
def Pres (P : β → Prop) (f : β → α → Except Error β) : Prop :=
  ∀ b a r, P b → f b a = .ok r → P r

/-- A loop invariant of `List.foldlM` in `Except`. -/
theorem foldlM_inv (P : β → Prop) (f : β → α → Except Error β) (hf : Pres P f) :
    ∀ (l : List α) (b r : β), P b → l.foldlM f b = .ok r → P r
  | [], b, r, hb, h => by simp only [List.foldlM_nil] at h; cases h; exact hb
  | a :: l, b, r, hb, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨b', h1, h2⟩ := bind_ok h
    exact foldlM_inv P f hf l b' r (hf b a b' hb h1) h2

/-- `forRange` keeps an invariant of its step. -/
theorem forRange_pres (P : β → Prop) (s n : Nat) : ∀ (f : β → Nat → Except Error β), Pres P f →
    ∀ b r, P b → forRange s n f b = .ok r → P r := by
  intro f hf b r hb h
  rw [Spec.Progression.forRange_eq] at h
  exact foldlM_inv P f hf _ b r hb h

/-- `forVolume` keeps an invariant of its step. -/
theorem forVolume_pres (P : β → Prop) (g : Layout) (v : Volume) (f : β → PacketId → Except Error β)
    (hf : Pres P f) : ∀ b r, P b → forVolume g v f b = .ok r → P r := by
  intro b r hb h
  unfold forVolume at h
  split at h
  · unfold forLRCP at h
    refine forRange_pres P _ _ _ ?_ b r hb h
    intro b l r hb h
    refine forRange_pres P _ _ _ ?_ b r hb h
    intro b rr r hb h
    refine forRange_pres P _ _ _ ?_ b r hb h
    intro b i r hb h
    refine forRange_pres P _ _ _ ?_ b r hb h
    intro b k r hb h
    exact hf _ _ _ hb h
  · unfold forRLCP at h
    refine forRange_pres P _ _ _ ?_ b r hb h
    intro b rr r hb h
    refine forRange_pres P _ _ _ ?_ b r hb h
    intro b l r hb h
    refine forRange_pres P _ _ _ ?_ b r hb h
    intro b i r hb h
    refine forRange_pres P _ _ _ ?_ b r hb h
    intro b k r hb h
    exact hf _ _ _ hb h
  · unfold forPosition at h
    refine foldlM_inv P _ ?_ _ b r hb h
    intro b e r hb h
    refine forRange_pres P _ _ _ ?_ b r hb h
    intro b l r hb h
    exact hf _ _ _ hb h

/-- `forVolumes` keeps an invariant of its step. -/
theorem forVolumes_pres (P : β → Prop) (g : Layout) (f : β → PacketId → Except Error β)
    (hf : Pres P f) : ∀ (prev vs : List Volume) (b r : β), P b → forVolumes g prev vs f b = .ok r → P r
  | _, [], b, r, hb, h => by simp only [forVolumes] at h; cases h; exact hb
  | prev, v :: vs, b, r, hb, h => by
    simp only [forVolumes] at h
    obtain ⟨b', h1, h2⟩ := bind_ok h
    refine forVolumes_pres P g f hf _ vs b' r (forVolume_pres P g v _ ?_ b b' hb h1) h2
    intro b p r hb h
    dsimp only at h
    split at h
    · cases h; exact hb
    · exact hf _ _ _ hb h

/-- **`forPackets` keeps an invariant of its step** (any progression, any POC). -/
theorem forPackets_pres (P : β → Prop) (g : Layout) (o : Marker.Progression) (poc : Array Marker.PocEntry)
    (f : β → PacketId → Except Error β) (hf : Pres P f) (b r : β) (hb : P b)
    (h : forPackets g o poc f b = .ok r) : P r :=
  forVolumes_pres P g f hf [] _ b r hb h

end Iter

/-! ## Segment ranges inside the input (`BlocksIn`) -/

section Ranges

/-- A member of `xs.pop` is a member of `xs`. -/
theorem mem_of_mem_pop {γ : Type} {xs : Array γ} {x : γ} (h : x ∈ xs.pop) : x ∈ xs := by
  rw [Array.mem_def, Array.toList_pop] at h
  rw [Array.mem_def]
  exact List.dropLast_subset _ h

/-- Every range of `rs` ends at most at `N`. -/
def RangesIn (N : Nat) (rs : Array ByteRange) : Prop := ∀ r ∈ rs, r.offset + r.length ≤ N

/-- Appending (or merging) a range inside `N` keeps `RangesIn N`. -/
theorem pushRange_in {N : Nat} {rs : Array ByteRange} {r : ByteRange} (h : RangesIn N rs)
    (hr : r.offset + r.length ≤ N) : RangesIn N (pushRange rs r) := by
  unfold pushRange
  split
  · exact h
  · split
    · rename_i l hl
      split
      · rename_i hst
        intro x hx
        rw [Array.mem_push] at hx
        rcases hx with hx | rfl
        · exact h x (mem_of_mem_pop hx)
        · simp only [ByteRange.stop] at hst; dsimp only; omega
      · intro x hx
        rw [Array.mem_push] at hx
        rcases hx with hx | rfl
        · exact h x hx
        · exact hr
    · intro x hx
      rw [Array.mem_push] at hx
      rcases hx with hx | rfl
      · exact h x hx
      · exact hr

/-- The tile-part ranges `(start in the buffer, offset in the input, length)` end inside `N`. -/
def PartsIn (N : Nat) (ps : List (Nat × Nat × Nat)) : Prop := ∀ x ∈ ps, x.2.1 + x.2.2 ≤ N

/-- `PartsOK` parts lie inside the input. -/
theorem partsOK_in (data : ByteArray) : ∀ (ps : List (Nat × Nat × Nat)) (b0 : Nat) (B : List UInt8),
    Spec.Tier2Equiv.PartsOK data b0 ps B → PartsIn data.size ps
  | [], _, _, _ => by intro x hx; cases hx
  | (bs, io, len) :: ps, b0, B, ⟨_, h2, B', _, h4⟩ => by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h2
    · exact partsOK_in data ps _ B' h4 x hx

/-- Translating a range through parts inside `N` gives ranges inside `N`. -/
theorem translate_in {N : Nat} (rg : ByteRange) : ∀ (ps : List (Nat × Nat × Nat)) (acc : Array ByteRange),
    PartsIn N ps → RangesIn N acc → RangesIn N (translate rg ps acc)
  | [], acc, _, ha => ha
  | (bs, io, len) :: ps, acc, hp, ha => by
    simp only [translate]
    refine translate_in rg ps _ (fun x hx => hp x (List.mem_cons_of_mem _ hx)) ?_
    split
    · refine pushRange_in ha ?_
      have := hp (bs, io, len) (List.mem_cons_self ..)
      simp only [ByteRange.stop] at this ⊢
      omega
    · exact ha

/-- The translated ranges of a segment lie inside `N`. -/
theorem foldl_translate_in {N : Nat} (ps : List (Nat × Nat × Nat)) (hp : PartsIn N ps)
    (rs : Array ByteRange) : RangesIn N (rs.foldl (fun acc r => translate r ps acc) #[]) := by
  rw [← Array.foldl_toList]
  suffices ∀ (l : List ByteRange) (acc : Array ByteRange), RangesIn N acc →
      RangesIn N (l.foldl (fun acc r => translate r ps acc) acc) from
    this _ _ (fun x hx => by simp at hx)
  intro l
  induction l with
  | nil => intro acc h; exact h
  | cons r l ih => intro acc h; exact ih _ (translate_in r ps acc hp h)

/-- Every code-block of a precinct result has its segment ranges inside the input. -/
theorem out_segsIn (data : ByteArray) (ps : List (Nat × Nat × Nat)) (hp : PartsIn data.size ps)
    (st : PrecState) (k : Nat) :
    ∀ bo ∈ (st.out ps k).bands, ∀ cb ∈ bo.blocks, Spec.Equiv.segsIn data cb = true := by
  intro bo hbo cb hcb
  simp only [PrecState.out, Array.mem_map] at hbo
  obtain ⟨bs, -, rfl⟩ := hbo
  simp only [Array.mem_map] at hcb
  obtain ⟨cb0, -, rfl⟩ := hcb
  simp only [Spec.Equiv.segsIn, Array.all_eq_true', decide_eq_true_eq]
  intro s hs
  simp only [Array.mem_map] at hs
  obtain ⟨s0, -, rfl⟩ := hs
  intro rg hrg
  exact foldl_translate_in ps hp s0.ranges rg hrg

/-- Membership in an element of an array of arrays looked up with default `#[]`. -/
theorem mem_getD {γ : Type} {xs : Array (Array γ)} {i : Nat} {x : γ} (h : x ∈ xs.getD i #[]) :
    ∃ ys ∈ xs, x ∈ ys := by
  rw [Array.getD_eq_getD_getElem?] at h
  cases he : xs[i]? with
  | none => rw [he] at h; simp at h
  | some ys => rw [he] at h; exact ⟨ys, Array.mem_of_getElem? he, h⟩

end Ranges

/-! ## Shapes

Decoding a packet (`decodePacket`) only updates tag trees, inclusion state, `Lblock`, passes and
segments: per band the orientation and the code-blocks' geometries (`bshape`) never change. -/

/-- Overwriting an entry by one with the same image keeps the mapped array. -/
theorem map_set_eq {α β : Type} (f : α → β) (a : Array α) (i : Nat) (x : α)
    (hx : ∀ y, a[i]? = some y → f x = f y) : (a.setIfInBounds i x).map f = a.map f := by
  apply Array.ext_getElem?
  intro j
  simp only [Array.getElem?_map, Array.getElem?_setIfInBounds]
  split
  · rename_i hij; subst hij
    by_cases hj : i < a.size
    · simp [hj, hx _ (Array.getElem?_eq_getElem hj)]
    · simp [hj]
  · rfl

/-- The shape of a precinct-band state: its orientation and its code-blocks' geometries. -/
def bshape (bs : BandState) : Band × Array CodeBlockGeom := (bs.band, bs.blocks.map (·.geom))

/-- The header part of one code-block keeps the precinct-band's shape. -/
theorem headerBlock_shape {L : Limits} {style layer bi k : Nat} {bs : BandState} {br : BitReader}
    {r : BandState × Option Contribution × BitReader} (h : headerBlock L style layer bi k bs br = .ok r) :
    bshape r.1 = bshape bs := by
  unfold headerBlock at h
  cases hk : bs.blocks[k]? with
  | none => simp [hk] at h
  | some cb =>
    simp only [hk] at h
    split at h <;>
    repeat' (first
      | (simp only [pure_bind] at h)
      | (obtain ⟨_, h1, h⟩ := bind_ok h; try (cases h1; dsimp only at h))
      | split at h)
    all_goals try (cases h; first | rfl | (simp only [bshape, Prod.mk.injEq, true_and]; apply map_set_eq; intro y hy; rw [hk] at hy; cases hy; rfl))

/-- The header part of one precinct-band keeps its shape. -/
theorem headerBand_shape {L : Limits} {style layer bi : Nat} {bs : BandState} {br : BitReader}
    {r : BandState × Array Contribution × BitReader} (h : headerBand L style layer bi bs br = .ok r) :
    bshape r.1 = bshape bs := by
  rw [headerBand_eq] at h
  obtain ⟨s, hs, h⟩ := bind_ok h
  cases h
  refine forIn_inv (fun s : BandState × BitReader × Array Contribution => bshape s.1 = bshape bs)
    _ ?_ _ _ _ rfl hs
  intro k b r hb hr
  unfold bandBody at hr
  obtain ⟨⟨bs', c, br'⟩, h1, hr⟩ := bind_ok hr
  have e := headerBlock_shape h1
  dsimp only at e
  cases c <;> (cases hr; exact e.trans hb)

/-- A packet header keeps the shapes of the precinct's bands. -/
theorem headerBands_shape {L : Limits} {layer : Nat} {st : PrecState} {br : BitReader}
    {r : PrecState × Array Contribution × BitReader} (h : headerBands L layer st br = .ok r) :
    r.1.bands.map bshape = st.bands.map bshape := by
  rw [headerBands_eq] at h
  obtain ⟨s, hs, h⟩ := bind_ok h
  cases h
  refine forIn_inv (fun s : Array BandState × BitReader × Array Contribution =>
    s.1.map bshape = st.bands.map bshape) _ ?_ _ _ _ rfl hs
  intro bi b r hb hr
  unfold bandsBody at hr
  split at hr
  · rename_i bs hbs
    obtain ⟨⟨bs', c, br'⟩, h1, hr⟩ := bind_ok hr
    cases hr
    have e := headerBand_shape h1
    dsimp only at e
    show Array.map bshape (b.1.setIfInBounds bi bs') = _
    rw [map_set_eq _ _ _ _ (fun y hy => by rw [hbs] at hy; cases hy; exact e)]
    exact hb
  · obtain ⟨_, h1, _⟩ := bind_ok hr; cases h1

/-- Appending pieces keeps a code-block's geometry. -/
theorem addPieces_geom : ∀ (rs : List (Nat × ByteRange)) (cb : CodeBlock) (cont : Bool),
    (addPieces cb cont rs).geom = cb.geom
  | [], _, _ => rfl
  | _ :: rs, cb, _ => by simp only [addPieces]; exact addPieces_geom rs _ false

/-- A packet body keeps the shapes of the precinct's bands. -/
theorem readBody_shape {st : PrecState} {cs : Array Contribution} {body : Reader}
    {r : PrecState × Reader} (h : readBody st cs body = .ok r) :
    r.1.bands.map bshape = st.bands.map bshape := by
  rw [readBody_eq] at h
  obtain ⟨s, hs, h⟩ := bind_ok h
  cases h
  refine forIn_inv (fun s : Array BandState × Reader => s.1.map bshape = st.bands.map bshape)
    _ ?_ _ _ _ rfl hs
  intro c b r hb hr
  unfold bodyBody at hr
  obtain ⟨⟨rs, body'⟩, h1, hr⟩ := bind_ok hr
  dsimp only at hr
  split at hr
  · rename_i bs hbs
    split at hr
    · rename_i cb hcb
      cases hr
      show Array.map bshape (b.1.setIfInBounds c.band _) = _
      rw [map_set_eq _ _ _ _ (fun y hy => by
        rw [hbs] at hy; cases hy
        simp only [bshape, Prod.mk.injEq, true_and]
        exact map_set_eq _ _ _ _ (fun z hz => by
          rw [hcb] at hz; cases hz; exact addPieces_geom _ _ _))]
      exact hb
    · obtain ⟨_, h1, _⟩ := bind_ok hr; cases h1
  · obtain ⟨_, h1, _⟩ := bind_ok hr; cases h1

/-- **Decoding a packet never changes a band label or a code-block geometry.** -/
theorem decodePacket_shape {L : Limits} {sop eph : Bool} {seq layer : Nat} {st : PrecState}
    {same : Bool} {hdr body : Reader} {r : PrecState × PacketInfo × Reader × Reader}
    (h : decodePacket L sop eph seq layer st same hdr body = .ok r) :
    r.1.bands.map bshape = st.bands.map bshape := by
  unfold decodePacket at h
  repeat' (first
    | (simp only [pure_bind] at h)
    | (obtain ⟨_, h1, h⟩ := bind_ok h; try (cases h1; dsimp only at h))
    | split at h)
  all_goals
    cases h
    first
    | rfl
    | (refine (readBody_shape (by assumption)).trans ?_
       first
       | rfl
       | exact headerBands_shape (by assumption))


/-! ## Geometry (B.6, B.7)

`Geometry.precinct`: each precinct-band is one of the resolution's bands (whose labels are
`bandsOf r` and rectangles `bandRect`, `resolution_bands`) and its code-blocks lie inside it
(`precinct_bands`). -/

/-- `r` lies inside `o`. -/
def RectIn (o r : Rect) : Prop := o.x0 ≤ r.x0 ∧ o.y0 ≤ r.y0 ∧ r.x1 ≤ o.x1 ∧ r.y1 ≤ o.y1

/-- `q < ⌈t / 2^e⌉ → q · 2^e < t`. -/
theorem lt_cdivPow {q t e : Nat} (h : q < cdivPow t e) : q * 2 ^ e < t := by
  have hm : 0 < 2 ^ e := Nat.two_pow_pos e
  unfold cdivPow cdiv at h
  have h1 : q + 1 ≤ (t + 2 ^ e - 1) / 2 ^ e := h
  have h2 := (Nat.le_div_iff_mul_le hm).1 h1
  rw [Nat.succ_mul] at h2; omega

/-- A code-block cell of a non-empty precinct-band lies inside it. -/
theorem codeBlocksOf_in {pb : Rect} {ex ey cw ch : Nat} (hw : cw ≤ gridCount pb.x0 pb.x1 ex)
    (hh : ch ≤ gridCount pb.y0 pb.y1 ey) :
    ∀ cb ∈ codeBlocksOf pb ex ey cw ch, RectIn pb cb.rect := by
  intro cb hcb
  simp only [codeBlocksOf, List.map_toArray, List.mem_toArray, List.mem_map, List.mem_range] at hcb
  obtain ⟨k, hk, rfl⟩ := hcb
  have hcw : 0 < cw := Nat.pos_of_ne_zero (fun e => by subst e; simp at hk)
  have hch : 0 < ch := Nat.pos_of_ne_zero (fun e => by subst e; simp at hk)
  have hi : k % cw < cw := Nat.mod_lt _ hcw
  have hj : k / cw < ch := by
    rw [Nat.div_lt_iff_lt_mul hcw]; rw [Nat.mul_comm] at hk; exact hk
  unfold gridCount at hw hh
  split at hw
  · omega
  split at hh
  · omega
  have gx := lt_cdivPow (show pb.x0 / 2 ^ ex + k % cw < cdivPow pb.x1 ex by omega)
  have gy := lt_cdivPow (show pb.y0 / 2 ^ ey + k / cw < cdivPow pb.y1 ey by omega)
  simp only [RectIn, clip]
  refine ⟨Nat.le_max_left _ _, Nat.le_max_left _ _, ?_, ?_⟩
  · apply Nat.max_le.2; constructor
    · apply Nat.max_le.2; constructor <;> omega
    · exact Nat.min_le_left _ _
  · apply Nat.max_le.2; constructor
    · apply Nat.max_le.2; constructor <;> omega
    · exact Nat.min_le_left _ _

/-- A clipped rectangle with positive width/height lies inside the original. -/
theorem clip_in {r : Rect} {a b c d : Nat} (hx : (clip r a b c d).x0 < (clip r a b c d).x1)
    (hy : (clip r a b c d).y0 < (clip r a b c d).y1) : RectIn r (clip r a b c d) := by
  dsimp only [clip, RectIn] at hx hy ⊢
  omega

/-- `RectIn` is transitive. -/
theorem RectIn.trans {a b c : Rect} (h1 : RectIn a b) (h2 : RectIn b c) : RectIn a c := by
  obtain ⟨a1, a2, a3, a4⟩ := h1; obtain ⟨b1, b2, b3, b4⟩ := h2
  exact ⟨Nat.le_trans a1 b1, Nat.le_trans a2 b2, Nat.le_trans b3 a3, Nat.le_trans b4 a4⟩

/-- Every result of a successful `List.mapM` satisfies what each call on a member guarantees. -/
theorem listMapM_mem {α β : Type} (P : β → Prop) (f : α → Except Error β) :
    ∀ (l : List α), (∀ a ∈ l, ∀ b, f a = .ok b → P b) → ∀ (out : List β), l.mapM f = .ok out → ∀ y ∈ out, P y
  | [], _, out, h, y, hy => by simp [List.mapM_nil] at h; cases h; simp at hy
  | a :: l, hf, out, h, y, hy => by
    rw [List.mapM_cons] at h
    obtain ⟨b, hb, h⟩ := bind_ok h
    obtain ⟨bs, hbs, h⟩ := bind_ok h
    cases h
    simp only [List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact hf a (List.mem_cons_self ..) y hb
    · exact listMapM_mem P f l (fun a ha => hf a (List.mem_cons_of_mem _ ha)) bs hbs y hy

/-- `Array.mapM` version of `listMapM_mem`. -/
theorem arrayMapM_mem {α β : Type} (P : β → Prop) (f : α → Except Error β) (xs : Array α)
    (hf : ∀ a ∈ xs, ∀ b, f a = .ok b → P b) (out : Array β) (h : xs.mapM f = .ok out) :
    ∀ y ∈ out, P y := by
  rw [Array.mapM_eq_mapM_toList] at h
  cases hm : List.mapM f xs.toList with
  | error e => rw [hm] at h; cases h
  | ok l =>
    rw [hm] at h; cases h
    intro y hy
    exact listMapM_mem P f xs.toList (fun a ha => hf a (Array.mem_def.2 ha)) l hm y (by simpa using hy)

/-- A non-zero grid count comes from a non-empty interval. -/
theorem gridCount_pos {a0 a1 e : Nat} (h : ¬ gridCount a0 a1 e = 0) : a0 < a1 := by
  unfold gridCount at h; split at h <;> omega

/-- A non-empty precinct-band lies inside its band (B.6). -/
theorem pbr_in {res : ResolutionGeom} {b : BandGeom} {px py : Nat}
    (hx : (precinctBandRect res b px py).x0 < (precinctBandRect res b px py).x1)
    (hy : (precinctBandRect res b px py).y0 < (precinctBandRect res b px py).y1) :
    RectIn b.rect (precinctBandRect res b px py) := clip_in hx hy

/-- What a resolution says about its bands. -/
theorem resolution_bands {L : Limits} {tc : TileCompGeom} {r : Nat} {res : ResolutionGeom}
    (h : resolution L tc r = .ok res) :
    ∀ b ∈ res.bands, b.band ∈ bandsOf r ∧ b.rect = bandRect tc.rect (bandLevel tc.params.levels r) b.band := by
  unfold resolution at h
  dsimp only at h
  split at h
  · cases h
  obtain ⟨_, -, h⟩ := bind_ok h
  obtain ⟨_, -, h⟩ := bind_ok h
  cases h
  intro b hb
  simp only [Array.mem_map] at hb
  obtain ⟨bd, hbd, rfl⟩ := hb
  exact ⟨hbd, rfl⟩

/-- **`Geometry.precinct`** (B.6, B.7): every precinct-band is one of the resolution's bands and
its code-blocks lie inside that band's rectangle. -/
theorem precinct_bands {L : Limits} {res : ResolutionGeom} {p : Nat} {pg : PrecinctGeom}
    (h : precinct L res p = .ok pg) :
    ∀ pb ∈ pg.bands, ∃ b ∈ res.bands, pb.band = b.band ∧ ∀ cb ∈ pb.codeBlocks, RectIn b.rect cb.rect := by
  unfold precinct at h
  dsimp only at h
  split at h
  · cases h
  obtain ⟨bands, hb, h⟩ := bind_ok h
  cases h
  refine arrayMapM_mem _ _ res.bands ?_ bands hb
  intro b hbm pbg hp
  obtain ⟨_, -, hp⟩ := bind_ok hp
  cases hp
  refine ⟨b, hbm, rfl, ?_⟩
  intro cb hcb
  dsimp only at hcb
  split at hcb
  · simp [codeBlocksOf] at hcb
  · rename_i hne
    have hin := codeBlocksOf_in (Nat.le_refl _) (Nat.le_refl _) cb hcb
    have hne' := not_or.1 hne
    exact RectIn.trans (pbr_in (gridCount_pos hne'.1) (gridCount_pos hne'.2)) hin

/-! ## `initPrecincts` -/

/-- A precinct state of resolution `r` of tile-component `tc`: its bands are bands of `r`, its
code-blocks inside their band's rectangle. -/
def WFPrec (tc : TileCompGeom) (r : Nat) (st : PrecState) : Prop :=
  ∀ bs ∈ st.bands, bs.band ∈ bandsOf r ∧
    ∀ cb ∈ bs.blocks, RectIn (bandRect tc.rect (bandLevel tc.params.levels r) bs.band) cb.geom.rect

/-- `PrecState.init` of a precinct of resolution `r` is well formed (`WFPrec`). -/
theorem init_wf {L : Limits} {tc : TileCompGeom} {r p : Nat} {res : ResolutionGeom}
    {pg : PrecinctGeom} {st : PrecState} (hr : resolution L tc r = .ok res)
    (hp : precinct L res p = .ok pg) (h : PrecState.init L tc.params r pg = .ok st) :
    WFPrec tc r st := by
  unfold PrecState.init at h
  obtain ⟨bands, hb, h⟩ := bind_ok h
  cases h
  refine arrayMapM_mem _ _ pg.bands ?_ bands hb
  intro pb hpb bs hbs
  obtain ⟨_, -, hbs⟩ := bind_ok hbs
  obtain ⟨_, -, hbs⟩ := bind_ok hbs
  cases hbs
  obtain ⟨b, hbm, e, hcb⟩ := precinct_bands hp pb hpb
  obtain ⟨h1, h2⟩ := resolution_bands hr b hbm
  refine ⟨by rw [e]; exact h1, ?_⟩
  intro cb hcb'
  simp only [Array.mem_map] at hcb'
  obtain ⟨cg, hcg, rfl⟩ := hcb'
  dsimp only
  rw [e, ← h2]
  exact hcb cg hcg

/-- An indexed loop invariant of `forIn` over `List.range'` whose body always yields. -/
theorem forIn_range'_inv {β : Type} (P : Nat → β → Prop) (f : Nat → β → Except Error (ForInStep β))
    (hf : ∀ i b r, P i b → f i b = .ok r → ∃ b', r = .yield b' ∧ P (i + 1) b') :
    ∀ (n s : Nat) (b r : β), P s b → forIn (List.range' s n) b f = .ok r → P (s + n) r
  | 0, s, b, r, hb, h => by simp only [List.range'_zero, List.forIn_nil] at h; cases h; exact hb
  | n + 1, s, b, r, hb, h => by
    rw [List.range'_succ, List.forIn_cons] at h
    obtain ⟨st, hst, h⟩ := bind_ok h
    obtain ⟨b', rfl, hb'⟩ := hf s b st hb hst
    have := forIn_range'_inv P f hf n (s + 1) b' r hb' h
    rwa [Nat.add_right_comm, Nat.add_assoc] at this

/-- The precinct states indexed by the spans `si` of tile-component `c` are well formed. -/
def SpanOK (g : Layout) (c : Nat) (precs : Array PrecState) (si : Array (Nat × Nat)) : Prop :=
  ∀ rr start n, si[rr]? = some (start, n) → ∀ k < n, ∃ st, precs[start + k]? = some st ∧
    WFPrec (g.comp c) rr st

/-- Pushing keeps the existing entries. -/
theorem getElem?_push_of_some {γ : Type} {xs : Array γ} {j : Nat} {y x : γ} (h : xs[j]? = some y) :
    (xs.push x)[j]? = some y := by
  have hj : j < xs.size := by
    rcases Nat.lt_or_ge j xs.size with hj | hj
    · exact hj
    · rw [Array.getElem?_eq_none hj] at h; cases h
  simp [Array.getElem?_push, Nat.ne_of_lt hj, h]

/-- Pushing a precinct state keeps `SpanOK`. -/
theorem SpanOK.push {g : Layout} {c : Nat} {precs : Array PrecState} {si : Array (Nat × Nat)}
    (h : SpanOK g c precs si) (x : PrecState) : SpanOK g c (precs.push x) si := by
  intro rr start n hs k hk
  obtain ⟨st, h1, h2⟩ := h rr start n hs k hk
  exact ⟨st, getElem?_push_of_some h1, h2⟩

/-- **`initPrecincts`**: the spans of every (component, resolution) index well-formed precinct
states of that component and resolution. -/
theorem initPrecincts_wf {L : Limits} {g : Layout} {precs : Array PrecState}
    {base : Array (Array Nat)} {spans : Array (Array (Nat × Nat))}
    (h : initPrecincts L g = .ok (precs, base, spans)) : ∀ c, SpanOK g c precs (spans.getD c #[]) := by
  unfold initPrecincts at h
  simp only [Std.Legacy.Range.forIn_eq_forIn_range'] at h
  obtain ⟨s, hs, h⟩ := bind_ok h
  cases h
  have hsz : ∀ n : Nat, [:n].size = n := by intro n; simp [Std.Legacy.Range.size]
  simp only [hsz] at hs
  have := forIn_range'_inv
    (fun i (s : Array PrecState × Array (Array Nat) × Array (Array (Nat × Nat)) × Nat) =>
      s.2.2.1.size = i ∧ ∀ c, SpanOK g c s.1 (s.2.2.1.getD c #[])) _ ?_ _ 0 _ _
    ⟨rfl, fun c rr start n hs => by simp at hs⟩ hs
  · exact this.2
  intro i b r hb hr
  obtain ⟨s2, hs2, hr⟩ := bind_ok hr
  cases hr
  refine ⟨_, rfl, ?_⟩
  have hm := forIn_range'_inv
    (fun rr (s : Array PrecState × Nat × Array Nat × Array (Nat × Nat)) =>
      s.2.2.2.size = rr ∧ SpanOK g i s.1 s.2.2.2 ∧ ∀ c, SpanOK g c s.1 (b.2.2.1.getD c #[])) _ ?_ _ 0 _ _
    ⟨rfl, fun rr start n hs => by simp at hs, hb.2⟩ hs2
  · obtain ⟨hb1, hb2⟩ := hb
    obtain ⟨_, hm2, hm3⟩ := hm
    refine ⟨by simp [hb1], fun c => ?_⟩
    dsimp only
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_push]
    split
    · rename_i hc; rw [hc, hb1]; exact hm2
    · rw [← Array.getD_eq_getD_getElem?]; exact hm3 c
  intro rr b2 r2 hb2 hr2
  obtain ⟨res, hres, hr2⟩ := bind_ok hr2
  obtain ⟨_, -, hr2⟩ := bind_ok hr2
  obtain ⟨s3, hs3, hr2⟩ := bind_ok hr2
  cases hr2
  refine ⟨_, rfl, ?_⟩
  have hi := forIn_range'_inv
    (fun p (s : Array PrecState × Nat) =>
      s.1.size = b2.1.size + p ∧ SpanOK g i s.1 b2.2.2.2 ∧ (∀ c, SpanOK g c s.1 (b.2.2.1.getD c #[])) ∧
        ∀ k < p, ∃ st, s.1[b2.1.size + k]? = some st ∧ WFPrec (g.comp i) rr st) _ ?_ _ 0 _ _
    ⟨rfl, hb2.2.1, hb2.2.2, fun k hk => absurd hk (Nat.not_lt_zero _)⟩ hs3
  · obtain ⟨hb21, -, -⟩ := hb2
    obtain ⟨-, hi2, hi3, hi4⟩ := hi
    refine ⟨by simp [hb21], ?_, hi3⟩
    intro rr' start n hs k hk
    rw [Array.getElem?_push] at hs
    split at hs
    · rename_i he; cases hs; subst he
      rw [hb21]; exact hi4 k (by simpa using hk)
    · exact hi2 rr' start n hs k hk
  intro p b3 r3 hb3 hr3
  obtain ⟨pg, hpg, hr3⟩ := bind_ok hr3
  obtain ⟨_, -, hr3⟩ := bind_ok hr3
  obtain ⟨st, hst, hr3⟩ := bind_ok hr3
  cases hr3
  refine ⟨_, rfl, ?_⟩
  obtain ⟨hb31, hb32, hb33, hb34⟩ := hb3
  refine ⟨by simp [hb31]; omega, hb32.push _, fun c => (hb33 c).push _, fun k hk => ?_⟩
  rcases Nat.lt_or_ge k p with hk' | hk'
  · obtain ⟨st', h1, h2⟩ := hb34 k hk'
    exact ⟨st', getElem?_push_of_some h1, h2⟩
  · have : k = p := by omega
    subst this
    refine ⟨st, ?_, init_wf hres hpg hst⟩
    dsimp only
    rw [Array.getElem?_push]; simp [hb31]

/-! ## The packet loop keeps the shapes -/

/-- The shape of a precinct state: per band, its orientation and code-block geometries. -/
def pshape (st : PrecState) : Array (Band × Array CodeBlockGeom) := st.bands.map bshape

/-- Clearing then overwriting an entry by one with the same image keeps the mapped array. -/
theorem map_set2 {α β : Type} (f : α → β) (a : Array α) (i : Nat) (d x : α)
    (hx : ∀ y, a[i]? = some y → f x = f y) :
    ((a.setIfInBounds i d).setIfInBounds i x).map f = a.map f := by
  apply Array.ext_getElem?
  intro j
  simp only [Array.getElem?_map, Array.getElem?_setIfInBounds, Array.size_setIfInBounds]
  split
  · rename_i hij; subst hij
    by_cases hj : i < a.size
    · simp [hj, hx _ (Array.getElem?_eq_getElem hj)]
    · simp [hj]
  · rfl

/-- One packet step keeps the precinct shapes. -/
theorem fastStep_pres {L : Limits} {sop eph same : Bool} {base : Array (Array Nat)} {pb : Nat}
    {s : LoopState} {p : PacketId} {r : LoopState}
    (h : Spec.Tier2Equiv.fastStep L sop eph same base pb s p = .ok r) :
    r.precs.map pshape = s.precs.map pshape := by
  unfold Spec.Tier2Equiv.fastStep at h
  dsimp only at h
  split at h
  · rename_i st hst
    obtain ⟨⟨st', info, hdr, body⟩, h1, h⟩ := bind_ok h
    obtain ⟨_, -, h⟩ := bind_ok h
    cases h
    exact map_set2 _ _ _ _ _ (fun y hy => by
      rw [hst] at hy; cases hy; exact decodePacket_shape h1)
  · cases h

/-- Same shape keeps `WFPrec`. -/
theorem WFPrec.of_shape {tc : TileCompGeom} {r : Nat} {st st' : PrecState} (hw : WFPrec tc r st)
    (he : pshape st' = pshape st) : WFPrec tc r st' := by
  intro bs' hbs'
  have hm : bshape bs' ∈ st.bands.map bshape := by
    rw [← show st'.bands.map bshape = st.bands.map bshape from he]
    exact Array.mem_map_of_mem hbs'
  obtain ⟨bs, hbs, e⟩ := Array.mem_map.1 hm
  simp only [bshape, Prod.mk.injEq] at e
  obtain ⟨e1, e2⟩ := e
  obtain ⟨w1, w2⟩ := hw bs hbs
  refine ⟨e1 ▸ w1, fun cb hcb => ?_⟩
  have hg : cb.geom ∈ bs.blocks.map (·.geom) := by rw [e2]; exact Array.mem_map_of_mem hcb
  obtain ⟨cb0, hcb0, e3⟩ := Array.mem_map.1 hg
  rw [← e1, ← e3]
  exact w2 cb0 hcb0

/-- `getD` with default `#[]` on a mapped array of arrays. -/
theorem getD_map_arr {α β : Type} (f : α → Array β) (xs : Array α) (i : Nat) (d : α)
    (hd : f d = #[]) : (xs.map f).getD i #[] = f (xs.getD i d) := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases xs[i]? <;> simp [hd]

/-- **Tier-2 of a tile is well formed**: the fast packet decoder's result satisfies `PrecsWF`
for its layout and `BlocksIn` for the input. -/
theorem decodeTile_wf {L : Limits} {h : Header} {data : ByteArray} {tp : TileParams}
    {hs : Option ByteArray} {pb : Nat} {x : TileCodeBlocks}
    (hd : decodeTilePacketsWith L h data tp hs pb = .ok x) :
    (∀ g coding, Progression.Layout.ofHeader h tp.index = .ok (g, coding) →
      ∀ c, Spec.Equiv.PrecsWF (g.comp c) (x.comps.getD c #[])) ∧
    ∀ c, Spec.Equiv.BlocksIn data (x.comps.getD c #[]) := by
  unfold decodeTilePacketsWith at hd
  obtain ⟨⟨g, coding⟩, hg, hd⟩ := bind_ok hd
  obtain ⟨_, -, hd⟩ := bind_ok hd
  obtain ⟨⟨precs, base, spans⟩, hip, hd⟩ := bind_ok hd
  obtain ⟨⟨buf, parts⟩, htd, hd⟩ := bind_ok hd
  obtain ⟨s, hs', hd⟩ := bind_ok hd
  cases hd
  have hI := forPackets_pres (fun s : LoopState => s.precs.map pshape = precs.map pshape) g
    coding.progression coding.poc _ (fun b p r _ hr => by
      have := fastStep_pres (L := L) (sop := coding.sop) (eph := coding.eph) (same := hs.isNone)
        (base := base) (pb := pb) hr
      rename_i hb
      exact this.trans hb) _ s rfl hs'
  have hwf := initPrecincts_wf hip
  have hparts : PartsIn data.size parts := partsOK_in data parts 0 _ (Spec.Tier2Equiv.tileData_ok htd)
  constructor
  · intro g' coding' hg' c
    rw [hg] at hg'; cases hg'
    intro r hr prec hprec bo hbo
    rw [getD_map_arr _ _ _ #[] (by simp)] at hr hprec
    have hr' : r < (spans.getD c #[]).size := by simpa using hr
    rw [getD_map_arr _ _ _ (0, 0) (by simp)] at hprec
    have hsi : (spans.getD c #[])[r]? = some ((spans.getD c #[]).getD r (0, 0)) := by
      have key : ∀ (xs : Array (Nat × Nat)) (i : Nat), i < xs.size → xs[i]? = some (xs.getD i (0, 0)) := by
        intro xs i hi; rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]; rfl
      exact key _ _ hr'
    generalize (spans.getD c #[]).getD r (0, 0) = sn at hsi hprec
    obtain ⟨start, n⟩ := sn
    simp only [Array.mem_map, Array.mem_range] at hprec
    obtain ⟨k, hk, rfl⟩ := hprec
    obtain ⟨st0, h0, hw0⟩ := hwf c r start n hsi k hk
    have hm : (s.precs.map pshape)[start + k]? = some (pshape st0) := by
      rw [hI, Array.getElem?_map, h0]; rfl
    rw [Array.getElem?_map] at hm
    cases hst : s.precs[start + k]? with
    | none => rw [hst] at hm; cases hm
    | some st' =>
      rw [hst] at hm
      have he : pshape st' = pshape st0 := by simpa using hm
      have hw' := hw0.of_shape he
      have hgd : s.precs.getD (start + k) default = st' := by
        rw [Array.getD_eq_getD_getElem?, hst]; rfl
      rw [hgd] at hbo
      simp only [PrecState.out, Array.mem_map] at hbo
      obtain ⟨bs, hbs, rfl⟩ := hbo
      obtain ⟨w1, w2⟩ := hw' bs hbs
      refine ⟨w1, fun cb hcb => ?_⟩
      simp only [Array.mem_map] at hcb
      obtain ⟨cb0, hcb0, rfl⟩ := hcb
      exact w2 cb0 hcb0
  · intro c r prec hprec bo hbo cb hcb
    obtain ⟨ys, hys, hp1⟩ := mem_getD hprec
    obtain ⟨zs, hzs, hp2⟩ := mem_getD hys
    simp only [Array.mem_map] at hzs
    obtain ⟨si, -, rfl⟩ := hzs
    simp only [Array.mem_map] at hp2
    obtain ⟨⟨start, n⟩, -, rfl⟩ := hp2
    simp only [Array.mem_map] at hp1
    obtain ⟨k, -, rfl⟩ := hp1
    exact out_segsIn data parts hparts _ k bo hbo cb hcb

/-! ## `Tier2WF` and C9 -/

/-- **`Spec.Equiv.Tier2WF`** (task 7.1g): every tile the fast Tier-2 decodes
(`Tier2.Headers.decodeWithStream`) has band labels and code-block rectangles consistent with its
layout (`PrecsWF`) and every segment range inside the input (`BlocksIn`). -/
theorem tier2WF : Spec.Equiv.Tier2WF := by
  intro L h data tp hs n x hx
  unfold Tier2.Headers.decodeWithStream at hx
  obtain ⟨t, ht, hx⟩ := bind_ok hx
  have hxt : x = t := by
    cases hs with
    | none => cases hx; rfl
    | some st =>
      dsimp only at hx
      split at hx
      · obtain ⟨_, h1, _⟩ := bind_ok hx; cases h1
      · cases hx; rfl
  subst hxt
  exact decodeTile_wf ht

/-- **C9 from the header hypothesis alone**: `Spec.Tier1Wire.c9_of_header` with `Tier2WF`
discharged (`tier2WF`). -/
theorem c9_of_hdr (hHd : Spec.Equiv.HeaderWF) :
    ∀ (L : Limits) (data : ByteArray) (reduce : Nat),
      Spec.Equiv.ERel Spec.Equiv.C9Rel (decodeCodestream L data reduce) (Spec.Decode.decode L data reduce) :=
  Spec.Tier1Wire.c9_of_header tier2WF hHd

end JPEG2000.Spec.Tier2WF
