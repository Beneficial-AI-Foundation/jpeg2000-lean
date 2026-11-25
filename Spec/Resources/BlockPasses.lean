import Spec.Resources

/-!
# S3: coding passes per code-block within `Limits.maxPassesPerCodeBlock`
(Plan.md §3 rule 3, §4 S3; task 4.8; T.800 B.10.6 (number of coding passes), B.10.7)

Tier-2 checks every code-block's running pass count against `Limits.maxPassesPerCodeBlock`
when a packet header adds passes to it (`Tier2.Packet.headerBlock`: `L.check …
.passesPerCodeBlock (cb.numPasses + n)`, mirrored by the spec `Spec.Tier2` and covered by
the Tier-2 equivalence). This file proves what the check buys on a **successful** run: every
code-block of every tile Tier-2 returns holds at most `maxPassesPerCodeBlock` passes.

* `decodePacket_within`: one packet keeps the invariant `PrecWithin` (every code-block of the
  precinct within the bound) — header (`headerBlock` → `headerBand` → `headerBands`) and body
  (`readBody`, which only appends byte ranges: `addPieces_numPasses`);
* `decodeTilePacketsWith_blockPasses`: fresh precincts start at 0 passes
  (`initPrecincts_within`), the packet loop keeps the invariant (`forPackets_inv`), and the
  output (`PrecState.out`) keeps the pass counts;
* `decodeWithStream_blockPasses`, `decodeAllTileCodeBlocks_blockPasses`: the same for the
  PPM/PPT wrapper and for all tiles (the Tier-2 driver of `decodeCodestream`).
-/
namespace JPEG2000.Spec.Resources.BlockPasses
open JPEG2000 JPEG2000.Tier2.Packet

/-- A bind in `Except` succeeds exactly when both parts do. -/
private theorem bind_ok' {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β} :
    (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp [bind, Except.bind]

/-- Every code-block of a precinct-band holds at most `M` passes. -/
def BlocksWithin (M : Nat) (bs : BandState) : Prop := ∀ cb ∈ bs.blocks, cb.numPasses ≤ M

/-- Setting a code-block within the bound keeps every code-block within it. -/
private theorem setIfInBounds_within {M k : Nat} {xs : Array CodeBlock} {cb : CodeBlock}
    (hx : ∀ c ∈ xs, c.numPasses ≤ M) (hc : cb.numPasses ≤ M) :
    ∀ c ∈ xs.setIfInBounds k cb, c.numPasses ≤ M := by
  intro c h
  rcases Array.mem_or_eq_of_mem_setIfInBounds h with h | h
  · exact hx c h
  · exact h ▸ hc

/-- The header part of one code-block keeps its band within the bound (the check). -/
private theorem headerBlock_within {L : Limits} {style layer bi k : Nat} {bs : BandState}
    {br : Bytes.BitReader} {r : BandState × Option Contribution × Bytes.BitReader}
    (hb : BlocksWithin L.maxPassesPerCodeBlock bs) (h : headerBlock L style layer bi k bs br = .ok r) :
    BlocksWithin L.maxPassesPerCodeBlock r.1 := by
  unfold headerBlock at h
  cases hk : bs.blocks[k]? with
  | none => simp [hk, throw, throwThe, MonadExceptOf.throw] at h
  | some cb =>
  have hcb : cb ∈ bs.blocks := Array.mem_of_getElem? hk
  cases hi : cb.included <;>
    simp only [hk, hi, bind_ok', Bool.false_eq_true, ↓reduceIte, pure, Except.pure] at h
  all_goals
    obtain ⟨a, -, a1, ha1, h⟩ := h
    simp only [Except.ok.injEq] at ha1
    subst ha1
    split at h
    · simp only [Except.ok.injEq] at h; subst h; exact hb
    · simp only [bind_ok', Except.ok.injEq] at h
      first
      | obtain ⟨_, -, a2, rfl, _, -, _, -, _, hc, _, -, rfl⟩ := h
      | obtain ⟨a2, rfl, _, -, _, -, _, hc, _, -, rfl⟩ := h
      exact setIfInBounds_within hb ((Limits.check_eq_ok_iff _ _ _ _).1 hc)

/-- A loop invariant of `forIn` over a list in `Except`. -/
private theorem forIn_inv' {ε α β : Type} (P : β → Prop) (f : α → β → Except ε (ForInStep β))
    (hf : ∀ a b r, P b → f a b = .ok r → P r.value) :
    ∀ (l : List α) (b r : β), P b → forIn l b f = .ok r → P r
  | [], b, r, hb, h => by simp only [List.forIn_nil] at h; cases h; exact hb
  | a :: l, b, r, hb, h => by
    rw [List.forIn_cons] at h
    obtain ⟨st, hst, h⟩ := bind_ok'.1 h
    have := hf a b st hb hst
    cases st with
    | done b' => cases h; exact this
    | yield b' => exact forIn_inv' P f hf l b' r this h

/-- The header part of one precinct-band keeps the bound. -/
private theorem headerBand_within {L : Limits} {style layer bi : Nat} {bs : BandState}
    {br : Bytes.BitReader} {r : BandState × Array Contribution × Bytes.BitReader}
    (hb : BlocksWithin L.maxPassesPerCodeBlock bs) (h : headerBand L style layer bi bs br = .ok r) :
    BlocksWithin L.maxPassesPerCodeBlock r.1 := by
  unfold headerBand at h
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', bind_ok'] at h
  obtain ⟨a, ha, h⟩ := h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  refine forIn_inv' (fun s : BandState × Bytes.BitReader × Array Contribution =>
    BlocksWithin L.maxPassesPerCodeBlock s.1) _ ?_ _ _ _ hb ha
  intro k s s' hs hk
  simp only [bind_ok'] at hk
  obtain ⟨x, hx, hk⟩ := hk
  have := headerBlock_within hs hx
  split at hk <;> (simp only [pure, Except.pure, Except.ok.injEq] at hk; subst hk; exact this)

/-- Every code-block of a precinct holds at most `M` passes. -/
def PrecWithin (M : Nat) (st : PrecState) : Prop := ∀ bs ∈ st.bands, BlocksWithin M bs

/-- Setting a band within the bound keeps every band within it. -/
private theorem bandsSet_within {M k : Nat} {xs : Array BandState} {b : BandState}
    (hx : ∀ c ∈ xs, BlocksWithin M c) (hc : BlocksWithin M b) :
    ∀ c ∈ xs.setIfInBounds k b, BlocksWithin M c := by
  intro c h
  rcases Array.mem_or_eq_of_mem_setIfInBounds h with h | h
  · exact hx c h
  · exact h ▸ hc

/-- The packet header keeps the precinct within the bound. -/
private theorem headerBands_within {L : Limits} {layer : Nat} {st : PrecState}
    {br : Bytes.BitReader} {r : PrecState × Array Contribution × Bytes.BitReader}
    (hs : PrecWithin L.maxPassesPerCodeBlock st) (h : headerBands L layer st br = .ok r) :
    PrecWithin L.maxPassesPerCodeBlock r.1 := by
  unfold headerBands at h
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', bind_ok'] at h
  obtain ⟨a, ha, h⟩ := h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  refine forIn_inv' (fun s : Array BandState × Bytes.BitReader × Array Contribution =>
    ∀ bs ∈ s.1, BlocksWithin L.maxPassesPerCodeBlock bs) _ ?_ _ _ _ ?_ ha
  rotate_left
  · exact hs
  intro k s s' hs' hk
  split at hk
  · rename_i bs hbs
    simp only [bind_ok'] at hk
    obtain ⟨x, hx, hk⟩ := hk
    simp only [pure, Except.pure, Except.ok.injEq] at hk
    subst hk
    exact bandsSet_within hs' (headerBand_within (hs' bs (Array.mem_of_getElem? hbs)) hx)
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hk

/-- Appending a contribution's byte ranges leaves the pass count unchanged. -/
private theorem addPieces_numPasses (cb : CodeBlock) (cont : Bool) (l : List (Nat × TilePart.ByteRange)) :
    (addPieces cb cont l).numPasses = cb.numPasses := by
  induction l generalizing cb cont with
  | nil => rfl
  | cons x l ih => obtain ⟨p, rg⟩ := x; simp only [addPieces, ih]

/-- The packet body keeps the precinct within the bound. -/
private theorem readBody_within {M : Nat} {st : PrecState} {cs : Array Contribution} {body : Bytes.Reader}
    {r : PrecState × Bytes.Reader}
    (hs : PrecWithin M st) (h : readBody st cs body = .ok r) : PrecWithin M r.1 := by
  unfold readBody at h
  simp only [← Array.forIn_toList, bind_ok'] at h
  obtain ⟨a, ha, h⟩ := h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  refine forIn_inv' (fun s : Array BandState × Bytes.Reader =>
    ∀ bs ∈ s.1, BlocksWithin M bs) _ ?_ _ _ _ ?_ ha
  rotate_left
  · exact hs
  intro c s s' hs' hk
  simp only [bind_ok'] at hk
  obtain ⟨x, -, hk⟩ := hk
  split at hk
  · rename_i bs hbs
    split at hk
    · rename_i cb hcb
      simp only [pure, Except.pure, Except.ok.injEq] at hk
      subst hk
      have hb := hs' bs (Array.mem_of_getElem? hbs)
      refine bandsSet_within hs' (setIfInBounds_within hb ?_)
      rw [addPieces_numPasses]; exact hb cb (Array.mem_of_getElem? hcb)
    · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hk
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hk

/-- **One packet keeps every code-block of its precinct within `maxPassesPerCodeBlock`.** -/
theorem decodePacket_within {L : Limits} {sop eph : Bool} {seq layer : Nat} {st : PrecState}
    {same : Bool} {hdr body : Bytes.Reader} {r : PrecState × PacketInfo × Bytes.Reader × Bytes.Reader}
    (hs : PrecWithin L.maxPassesPerCodeBlock st) (h : decodePacket L sop eph seq layer st same hdr body = .ok r) :
    PrecWithin L.maxPassesPerCodeBlock r.1 := by
  unfold decodePacket at h
  cases sop <;> cases eph <;>
    simp only [Bool.false_eq_true, ↓reduceIte, bind_ok', pure, Except.pure, Except.ok.injEq] at h
  all_goals
    obtain ⟨a, -, a1, -, h⟩ := h
    split at h
    all_goals
      simp only [bind_ok', Except.ok.injEq] at h
      obtain ⟨x, hx, _, -, _, -, x4, hx4, rfl⟩ := h
      first
      | exact readBody_within (headerBands_within hs hx) hx4
      | (subst hx; exact readBody_within hs hx4)

/-- `List.mapM` in `Except`: a property of every successful output holds for all outputs. -/
private theorem list_mapM_all {ε α β : Type} (f : α → Except ε β) (Q : β → Prop)
    (hf : ∀ a b, f a = .ok b → Q b) :
    ∀ (xs : List α) (ys : List β), xs.mapM f = .ok ys → ∀ y ∈ ys, Q y
  | [], ys, h => by
    simp [List.mapM_nil, pure, Except.pure] at h; subst h; simp
  | x :: xs, ys, h => by
    simp only [List.mapM_cons, bind_ok', pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨y, hy, ys', hys, rfl⟩ := h
    intro z hz
    simp only [List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact hf x z hy
    · exact list_mapM_all f Q hf xs ys' hys z hz

/-- `Array.mapM` in `Except`: a property of every successful output holds for all outputs. -/
private theorem array_mapM_all {ε α β : Type} (f : α → Except ε β) (Q : β → Prop)
    (hf : ∀ a b, f a = .ok b → Q b) (xs : Array α) (ys : Array β)
    (h : xs.mapM f = .ok ys) : ∀ y ∈ ys, Q y := by
  rw [Array.mapM_eq_mapM_toList] at h
  cases hm : List.mapM f xs.toList with
  | error e => rw [hm] at h; cases h
  | ok l =>
    rw [hm] at h
    simp only [Functor.map, Except.map, Except.ok.injEq] at h
    subst h
    intro y hy
    exact list_mapM_all f Q hf _ _ hm y (by simpa using hy)

/-- A fresh precinct has no passes. -/
private theorem init_within (M : Nat) {L : Limits} {p : Header.CompParams} {r : Nat}
    {pg : Tier2.Geometry.PrecinctGeom}
    {st : PrecState} (h : PrecState.init L p r pg = .ok st) : PrecWithin M st := by
  unfold PrecState.init at h
  simp only [bind_ok', pure, Except.pure, Except.ok.injEq] at h
  obtain ⟨a, ha, rfl⟩ := h
  refine array_mapM_all _ (BlocksWithin M) ?_ _ _ ha
  intro pb bs hb
  simp only [bind_ok', Except.ok.injEq] at hb
  obtain ⟨_, -, _, -, rfl⟩ := hb
  intro cb hcb
  simp only [Array.mem_map] at hcb
  obtain ⟨_, -, rfl⟩ := hcb
  exact Nat.zero_le _

/-- All fresh precincts of a tile have no passes. -/
private theorem initPrecincts_within (M : Nat) {L : Limits} {g : Progression.Layout} {x}
    (h : initPrecincts L g = .ok x) : ∀ st ∈ x.1, PrecWithin M st := by
  unfold initPrecincts at h
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', bind_ok'] at h
  obtain ⟨a, ha, h⟩ := h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  show ∀ st ∈ a.1, PrecWithin M st
  refine forIn_inv' (fun s : Array PrecState × _ => ∀ st ∈ s.1, PrecWithin M st) _ ?_ _ _ _
    ?_ ha
  rotate_left
  · intro st hst; simp at hst
  intro i s s' hs hi
  simp only [bind_ok', pure, Except.pure, Except.ok.injEq] at hi
  obtain ⟨s1, hs1, rfl⟩ := hi
  show ∀ st ∈ s1.1, PrecWithin M st
  refine forIn_inv' (fun s : Array PrecState × _ => ∀ st ∈ s.1, PrecWithin M st) _ ?_ _ _ _
    ?_ hs1
  rotate_left
  · exact hs
  intro r s s' hs hr
  simp only [bind_ok', Except.ok.injEq] at hr
  obtain ⟨_, -, _, -, s2, hs2, rfl⟩ := hr
  show ∀ st ∈ s2.1, PrecWithin M st
  refine forIn_inv' (fun s : Array PrecState × _ => ∀ st ∈ s.1, PrecWithin M st) _ ?_ _ _ _
    ?_ hs2
  rotate_left
  · exact hs
  intro p s s' hs hp
  simp only [bind_ok', Except.ok.injEq] at hp
  obtain ⟨_, -, _, -, st, hst, rfl⟩ := hp
  intro st' hst'
  simp only [ForInStep.value, Array.mem_push] at hst'
  rcases hst' with h | rfl
  · exact hs st' h
  · exact init_within M hst

/-- An element of `zipIdx` is an element of the list. -/
private theorem zi_mem {α : Type} {l : List α} {x : α} {i : Nat} (h : (x, i) ∈ l.zipIdx) : x ∈ l :=
  List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.1 h)

/-- `getD` with the empty default precinct keeps the bound. -/
private theorem getD_within {M : Nat} {xs : Array PrecState} (hx : ∀ st ∈ xs, PrecWithin M st) (j : Nat) :
    PrecWithin M (xs.getD j default) := by
  unfold Array.getD
  split
  · exact hx _ (Array.getElem_mem _)
  · intro bs hbs; simp [default] at hbs

/-- The output form of a precinct keeps the pass counts. -/
private theorem out_within {M : Nat} {st : PrecState} (hs : PrecWithin M st) (parts) (k : Nat) :
    ∀ b ∈ (st.out parts k).bands, ∀ cb ∈ b.blocks, cb.numPasses ≤ M := by
  intro b hb cb hcb
  simp only [PrecState.out, Array.mem_map] at hb
  obtain ⟨bs, hbs, rfl⟩ := hb
  simp only [Array.mem_map] at hcb
  obtain ⟨c, hc, rfl⟩ := hcb
  exact hs bs hbs c hc

/-- **S3, passes per code-block (task 4.8)**: every code-block of a tile Tier-2 returns holds
at most `Limits.maxPassesPerCodeBlock` coding passes. -/
theorem decodeTilePacketsWith_blockPasses {L : Limits} {h : Header.Header} {data : ByteArray}
    {tp : Header.TileParams} {hs : Option ByteArray} {pb : Nat} {t : TileCodeBlocks}
    (ht : decodeTilePacketsWith L h data tp hs pb = .ok t) :
    ∀ b ∈ t.blocks, b.block.numPasses ≤ L.maxPassesPerCodeBlock := by
  unfold decodeTilePacketsWith at ht
  simp only [bind_ok'] at ht
  obtain ⟨⟨g, c⟩, -, _, -, ⟨precs, base, spans⟩, hinit, ⟨buf, parts⟩, -, s, hst, ht⟩ := ht
  simp only [pure, Except.pure, Except.ok.injEq] at ht
  subst ht
  have hinv := Resources.forPackets_inv (P := fun s : LoopState =>
    ∀ st ∈ s.precs, PrecWithin L.maxPassesPerCodeBlock st) ?_ _ _ _ _ _
    (initPrecincts_within _ hinit) hst
  · intro b hb
    simp only [TileCodeBlocks.blocks, List.mem_flatMap, List.mem_map, Array.mem_toList_iff] at hb
    obtain ⟨⟨rs, i⟩, hi, ⟨ps, r⟩, hr, p, hp, ⟨bo, bi⟩, hbo, cb, hcb, rfl⟩ := hb
    have hi := zi_mem hi
    have hr := zi_mem hr
    have hbo := zi_mem hbo
    simp only [Array.mem_toList_iff, Array.mem_map] at hi hr hbo hp hcb
    obtain ⟨si, -, rfl⟩ := hi
    simp only [Array.mem_map] at hr
    obtain ⟨⟨start, n⟩, -, rfl⟩ := hr
    simp only [Array.mem_map] at hp
    obtain ⟨k, -, rfl⟩ := hp
    exact out_within (getD_within hinv _) parts k bo hbo cb hcb
  · intro b p b' hb hp
    simp only at hp
    split at hp
    · rename_i stp hstp
      simp only [bind_ok'] at hp
      obtain ⟨⟨st', info, hdr, body⟩, hdp, _, -, hp⟩ := hp
      simp only [pure, Except.pure, Except.ok.injEq] at hp
      subst hp
      have := decodePacket_within (hb _ (Array.mem_of_getElem? hstp)) hdp
      intro x hx
      rcases Array.mem_or_eq_of_mem_setIfInBounds hx with hx | rfl
      · rcases Array.mem_or_eq_of_mem_setIfInBounds hx with hx | rfl
        · exact hb x hx
        · intro bs hbs; simp [default] at hbs
      · exact this
    · cases hp

/-- `decodeTilePacketsWith_blockPasses` for `Tier2.Headers.decodeWithStream` (PPM/PPT). -/
theorem decodeWithStream_blockPasses {L : Limits} {h : Header.Header} {data : ByteArray}
    {tp : Header.TileParams} {hs : Option Tier2.Headers.HeaderStream} {pb : Nat}
    {t : TileCodeBlocks} (ht : Tier2.Headers.decodeWithStream L h data tp hs pb = .ok t) :
    ∀ b ∈ t.blocks, b.block.numPasses ≤ L.maxPassesPerCodeBlock := by
  unfold Tier2.Headers.decodeWithStream at ht
  simp only [bind_ok'] at ht
  obtain ⟨t', h1, ht⟩ := ht
  have := decodeTilePacketsWith_blockPasses h1
  repeat' split at ht
  all_goals (try cases ht) <;> exact this

/-- **S3, passes per code-block, all tiles**: every code-block of every tile of
`Tier2.Headers.decodeAllTileCodeBlocks` holds at most `maxPassesPerCodeBlock` passes. -/
theorem decodeAllTileCodeBlocks_blockPasses {L : Limits} {h : Header.Header} {data : ByteArray}
    {ts : Array TileCodeBlocks}
    (ht : Tier2.Headers.decodeAllTileCodeBlocks L h data = .ok ts) :
    ∀ t ∈ ts, ∀ b ∈ t.blocks, b.block.numPasses ≤ L.maxPassesPerCodeBlock := by
  unfold Tier2.Headers.decodeAllTileCodeBlocks at ht
  simp only [Std.Legacy.Range.forIn_eq_forIn_range'] at ht
  split at ht
  all_goals
    simp only [bind_ok'] at ht
    obtain ⟨idx, -, st, hst, ht⟩ := ht
    simp only [pure, Except.pure, Except.ok.injEq] at ht
    subst ht
    refine forIn_inv' (fun s : Array TileCodeBlocks × Nat =>
      ∀ t ∈ s.1, ∀ b ∈ t.blocks, b.block.numPasses ≤ L.maxPassesPerCodeBlock) _ ?_ _ _ _
      (by intro t ht; simp at ht) hst
    intro j b r hb hr
    split at hr
    · simp only [bind_ok'] at hr
      obtain ⟨hs, -, t, htd, hr⟩ := hr
      simp only [pure, Except.pure, Except.ok.injEq] at hr
      subst hr
      intro t' ht'
      simp only [ForInStep.value, Array.mem_push] at ht'
      rcases ht' with ht' | rfl
      · exact hb t' ht'
      · exact decodeWithStream_blockPasses htd
    · cases hr

end JPEG2000.Spec.Resources.BlockPasses
