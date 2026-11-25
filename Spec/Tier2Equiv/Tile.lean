import Spec.Tier2Equiv.Packet
import Spec.Progression

/-!
# Tier-2 equivalence, layer (d): the packets of a tile
(Plan.md §4 C9, §5.1, §5.2 "Tier-2"; T.800 B.9–B.12, A.4, A.7.4–A.7.5)

Task 7.1b. The fast packet loop (`decodeTilePacketsWith`, iterating `Progression.forPackets`)
is the spec loop (`Spec.Tier2.decodeTile`, folding `Spec.Progression.packets`):

* the iteration: `Spec.Progression.forPackets_eq_spec` (task 4.3), under `Layout.WF`;
* one packet step and the fold (`step_sim`, `loop_sim`, over `LRel`: precinct states related
  by `PrecRel`, the streams by their byte lists);
* the start: `initPrecincts` builds fresh precinct states (`initPrecincts_fresh`: tag trees
  `Spec.TagTree.init` by `Spec.TagTree.create_rel`, code-blocks never included), which
  represent the spec's fresh states (`fresh_rel`);
* the tile buffer: `tileData` concatenates the tile-parts' input ranges (`tileData_ok`,
  `PartsOK`), so translating a buffer range to input ranges keeps its bytes
  (`translate_bytes`), and each output code-block's segments have the bytes the spec reads
  (`outBlock_eq`, `out_eq`).

`ofHeader_wf` discharges `Layout.WF` for headers whose components have non-zero
sub-sampling (as `SIZ` parsing requires). `decodeTile_sim` and `decodeWithStream_sim` state the result: both fail, or the spec result is
the image of the fast one (`image`: per code-block `blockOf data`) with equal pass counts.
-/

namespace JPEG2000.Spec.Tier2Equiv

open JPEG2000 JPEG2000.Bytes JPEG2000.TilePart JPEG2000.Header JPEG2000.Progression
open JPEG2000.Spec.Tier2 JPEG2000.Tier2.Packet

/-- The packet step of `decodeTilePacketsWith` (as elaborated). -/
def fastStep (L : Limits) (sop eph same : Bool) (base : Array (Array Nat)) (passesBefore : Nat)
    (s : LoopState) (p : PacketId) : Except Error LoopState :=
  let idx := (base.getD p.comp #[]).getD p.res 0 + p.prec
  match s.precs[idx]? with
  | some st =>
    let precs := s.precs.setIfInBounds idx default
    do
    let (st, info, hdr, body) ← decodePacket L sop eph s.seq p.layer st same s.hdr s.body
    let passes := s.passes + info.newPasses
    L.check JPEG2000.Tier2.Packet.loc LimitKind.codingPasses (passesBefore + passes)
    pure { precs := precs.setIfInBounds idx st, hdr, body, seq := s.seq + 1,
           empty := s.empty + if info.empty = true then 1 else 0,
           sops := s.sops + if info.sop = true then 1 else 0,
           hdrBytes := s.hdrBytes + info.headerBytes, bodyBytes := s.bodyBytes + info.bodyBytes,
           passes }
  | _ => throw (Error.malformed JPEG2000.Tier2.Packet.loc "precinct index out of range")

/-- The fast and spec packet-loop states correspond (`hsb`: the separate header stream). -/
def LRel (buf : ByteArray) (hsb : Option ByteArray) (s : LoopState) (l : Spec.Tier2.Loop) : Prop :=
  (∀ j : Nat, ORel (PrecRel buf) s.precs[j]? l.precs[j]?) ∧ l.hdr = rbytes s.hdr ∧
  l.body = rbytes s.body ∧ s.body.data = buf ∧ s.body.stop = buf.size ∧ s.seq = l.seq ∧
  s.passes = l.passes ∧ (∀ hb, hsb = some hb → s.hdr.data = hb ∧ s.hdr.stop = hb.size)

set_option linter.unusedSimpArgs false in
/-- **One packet of the tile loop.** -/
theorem step_sim (buf : ByteArray) (hsb : Option ByteArray) (L : Limits) (sop eph : Bool)
    (base : Array (Array Nat)) (pb : Nat) (s : LoopState) (l : Spec.Tier2.Loop) (hR : LRel buf hsb s l)
    (p : PacketId) :
    Res (LRel buf hsb) (fastStep L sop eph hsb.isNone base pb s p)
      (Spec.Tier2.step L sop eph hsb.isNone base pb l p) := by
  obtain ⟨hP, hh, hb, hbd, hbs, hseq, hpass, hhs⟩ := hR
  unfold fastStep Spec.Tier2.step
  dsimp only
  have hj := hP ((base.getD p.comp #[]).getD p.res 0 + p.prec)
  revert hj
  cases hfs : s.precs[(base.getD p.comp #[]).getD p.res 0 + p.prec]? with
  | none =>
    cases l.precs[(base.getD p.comp #[]).getD p.res 0 + p.prec]? with
    | none => intro _; exact Res.error _ _
    | some _ => intro h; exact absurd h id
  | some st =>
    cases hss : l.precs[(base.getD p.comp #[]).getD p.res 0 + p.prec]? with
    | none => intro h; exact absurd h id
    | some sst =>
      intro hst
      dsimp only
      rw [hh, hb, ← hseq]
      refine Res.bind (decodePacket_sim buf L sop eph s.seq p.layer st sst hst hsb.isNone s.hdr s.body hbd)
        fun ⟨st', info, hdr', body'⟩ ⟨sst', n, lh, lb⟩ ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ => ?_
      dsimp only at h1 h2 h3 h4 h5 h6 h7 h8 ⊢
      rw [h2, ← hpass]
      refine Res.check L _ _ _ _ ?_
      refine ⟨fun j => ?_, h3, h4, h5, h6.trans hbs, by rw [hseq], rfl, fun hb' e => ?_⟩
      · have hlt : (base.getD p.comp #[]).getD p.res 0 + p.prec < s.precs.size := by
          rcases Nat.lt_or_ge ((base.getD p.comp #[]).getD p.res 0 + p.prec) s.precs.size with h | h
          · exact h
          · rw [Array.getElem?_eq_none h] at hfs; cases hfs
        have hlt' : (base.getD p.comp #[]).getD p.res 0 + p.prec < l.precs.length := by
          rcases Nat.lt_or_ge ((base.getD p.comp #[]).getD p.res 0 + p.prec) l.precs.length with h | h
          · exact h
          · rw [List.getElem?_eq_none h] at hss; cases hss
        rw [Array.getElem?_setIfInBounds, List.getElem?_set, Array.getElem?_setIfInBounds]
        split
        · simp only [Array.size_setIfInBounds, hlt, hlt', ↓reduceIte]; exact h1
        · exact hP j
      · have hns : hsb.isNone = false := by rw [e]; rfl
        obtain ⟨g1, g2⟩ := h7 hns
        obtain ⟨g3, g4⟩ := hhs hb' e
        exact ⟨g1.trans g3, g2.trans g4⟩

/-- **The packet loop**: the fast fold over a packet sequence follows the spec fold. -/
theorem loop_sim (buf : ByteArray) (hsb : Option ByteArray) (L : Limits) (sop eph : Bool)
    (base : Array (Array Nat)) (pb : Nat) : ∀ (ps : List PacketId) (s : LoopState) (l : Spec.Tier2.Loop),
    LRel buf hsb s l →
    Res (LRel buf hsb) (ps.foldlM (fastStep L sop eph hsb.isNone base pb) s)
      (ps.foldlM (Spec.Tier2.step L sop eph hsb.isNone base pb) l)
  | [], s, l, hR => hR
  | p :: ps, s, l, hR => by
    simp only [List.foldlM_cons]
    exact Res.bind (step_sim buf hsb L sop eph base pb s l hR p)
      fun s' l' h => loop_sim buf hsb L sop eph base pb ps s' l' h

/-- A successful bind decomposes. -/
theorem bind_ok {α β : Type} {x : Except Error α} {f : α → Except Error β} {r : β}
    (h : (x >>= f) = .ok r) : ∃ a, x = .ok a ∧ f a = .ok r := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- Every result of a successful `List.mapM` satisfies what each call guarantees. -/
theorem listMapM_inv {α β : Type} (P : β → Prop) (f : α → Except Error β)
    (hf : ∀ a b, f a = .ok b → P b) : ∀ (l : List α) (out : List β), l.mapM f = .ok out → ∀ y ∈ out, P y
  | [], out, h, y, hy => by simp [List.mapM_nil] at h; cases h; simp at hy
  | a :: l, out, h, y, hy => by
    rw [List.mapM_cons] at h
    obtain ⟨b, hb, h⟩ := bind_ok h
    obtain ⟨bs, hbs, h⟩ := bind_ok h
    cases h
    simp only [List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact hf a y hb
    · exact listMapM_inv P f hf l bs hbs y hy

/-- Every result of a successful `Array.mapM` satisfies what each call guarantees. -/
theorem arrayMapM_inv {α β : Type} (P : β → Prop) (f : α → Except Error β)
    (hf : ∀ a b, f a = .ok b → P b) (xs : Array α) (out : Array β) (h : xs.mapM f = .ok out) :
    ∀ y ∈ out.toList, P y := by
  rw [Array.mapM_eq_mapM_toList] at h
  cases hm : List.mapM f xs.toList with
  | error e => rw [hm] at h; cases h
  | ok l =>
    rw [hm] at h; cases h
    exact listMapM_inv P f hf xs.toList l hm

/-- A loop invariant of `forIn` over a list in `Except`. -/
theorem forIn_inv {α β : Type} (P : β → Prop) (f : α → β → Except Error (ForInStep β))
    (hf : ∀ a b r, P b → f a b = .ok r → P r.value) :
    ∀ (l : List α) (b r : β), P b → forIn l b f = .ok r → P r
  | [], b, r, hb, h => by simp only [List.forIn_nil] at h; cases h; exact hb
  | a :: l, b, r, hb, h => by
    rw [List.forIn_cons] at h
    obtain ⟨st, hst, h⟩ := bind_ok h
    have := hf a b st hb hst
    cases st with
    | done b' => cases h; exact this
    | yield b' => exact forIn_inv P f hf l b' r this h

/-- A precinct-band state as `PrecState.init` builds it: both tag trees fresh, code-blocks never
included. -/
def FreshBand (bs : BandState) : Prop :=
  Spec.TagTree.Rel bs.incl Spec.TagTree.init ∧ Spec.TagTree.Rel bs.zbp Spec.TagTree.init ∧
  bs.zbp.w = bs.incl.w ∧ bs.zbp.h = bs.incl.h ∧ ∀ cb ∈ bs.blocks.toList, cb = { geom := cb.geom }

/-- A fresh precinct state. -/
def Fresh (p : PrecState) : Prop := ∀ bs ∈ p.bands.toList, FreshBand bs

/-- `PrecState.init` builds a fresh precinct state. -/
theorem init_fresh {L : Limits} {p : CompParams} {r : Nat} {pg : Tier2.Geometry.PrecinctGeom}
    {st : PrecState} (h : PrecState.init L p r pg = .ok st) : Fresh st := by
  unfold PrecState.init at h
  obtain ⟨bands, hb, h⟩ := bind_ok h
  cases h
  apply arrayMapM_inv FreshBand _ _ pg.bands bands hb
  intro pb bs hbs
  obtain ⟨incl, hi, hbs⟩ := bind_ok hbs
  obtain ⟨zbp, hz, hbs⟩ := bind_ok hbs
  cases hbs
  obtain ⟨r1, w1, h1⟩ := Spec.TagTree.create_rel hi
  obtain ⟨r2, w2, h2⟩ := Spec.TagTree.create_rel hz
  refine ⟨r1, r2, w2.trans w1.symm, h2.trans h1.symm, fun cb hcb => ?_⟩
  simp only [Array.toList_map, List.mem_map] at hcb
  obtain ⟨g, -, rfl⟩ := hcb
  rfl

/-- Every precinct state built by `initPrecincts` is fresh. -/
theorem initPrecincts_fresh {L : Limits} {g : Layout} {precs : Array PrecState}
    {base : Array (Array Nat)} {spans : Array (Array (Nat × Nat))}
    (h : initPrecincts L g = .ok (precs, base, spans)) : ∀ p ∈ precs.toList, Fresh p := by
  unfold initPrecincts at h
  simp only [Std.Legacy.Range.forIn_eq_forIn_range'] at h
  obtain ⟨s, hs, h⟩ := bind_ok h
  cases h
  refine forIn_inv (fun s : Array PrecState × Array (Array Nat) × Array (Array (Nat × Nat)) × Nat =>
    ∀ p ∈ s.1.toList, Fresh p) _ ?_ _ _ _ (by simp) hs
  intro i b r hb hr
  obtain ⟨s2, hs2, hr⟩ := bind_ok hr
  cases hr
  refine forIn_inv (fun s : Array PrecState × Nat × Array Nat × Array (Nat × Nat) =>
    ∀ p ∈ s.1.toList, Fresh p) _ ?_ _ _ _ hb hs2
  intro rr b2 r2 hb2 hr2
  obtain ⟨res, -, hr2⟩ := bind_ok hr2
  obtain ⟨_, -, hr2⟩ := bind_ok hr2
  obtain ⟨s3, hs3, hr2⟩ := bind_ok hr2
  cases hr2
  refine forIn_inv (fun s : Array PrecState × Nat => ∀ p ∈ s.1.toList, Fresh p) _ ?_ _ _ _ hb2 hs3
  intro pp b3 r3 hb3 hr3
  obtain ⟨pg, -, hr3⟩ := bind_ok hr3
  obtain ⟨_, -, hr3⟩ := bind_ok hr3
  obtain ⟨st, hst, hr3⟩ := bind_ok hr3
  cases hr3
  intro q hq
  have hq' : q ∈ (b3.1.push st).toList := hq
  simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hq'
  rcases hq' with hq' | rfl
  · exact hb3 q hq'
  · exact init_fresh hst

/-- A fresh fast precinct state represents the spec's fresh state `PrecSt.ofFast`. -/
theorem fresh_rel (buf : ByteArray) (p : PrecState) (hf : Fresh p) : PrecRel buf p (PrecSt.ofFast p) := by
  refine ⟨rfl, fun j => ?_⟩
  simp only [PrecSt.ofFast, List.getElem?_map, Array.getElem?_toList]
  cases hb : p.bands[j]? with
  | none => trivial
  | some bs =>
    have hm : bs ∈ p.bands.toList := by
      rw [← Array.getElem?_toList] at hb; exact List.mem_of_getElem? hb
    obtain ⟨r1, r2, hw, hh, hcb⟩ := hf bs hm
    refine ⟨rfl, rfl, rfl, rfl, rfl, hw, hh, r1, r2, ?_⟩
    apply List.map_congr_left
    intro cb hcb'
    rw [hcb cb hcb']
    rfl

/-- The tile-part ranges `(start in the buffer, offset in the input, length)` of a tile buffer
`B`, starting at buffer offset `b0`: consecutive, inside the input, `B` their bytes. -/
def PartsOK (data : ByteArray) : Nat → List (Nat × Nat × Nat) → List UInt8 → Prop
  | _, [], B => B = []
  | b0, (bs, io, len) :: ps, B => bs = b0 ∧ io + len ≤ data.size ∧
      ∃ B', B = bytesFrom data io (io + len) ++ B' ∧ PartsOK data (b0 + len) ps B'

/-- Appending a tile-part keeps `PartsOK`. -/
theorem partsOK_snoc (data : ByteArray) (io len : Nat) (hio : io + len ≤ data.size) :
    ∀ (ps : List (Nat × Nat × Nat)) (b0 : Nat) (B : List UInt8), PartsOK data b0 ps B →
      PartsOK data b0 (ps ++ [(b0 + B.length, io, len)]) (B ++ bytesFrom data io (io + len))
  | [], b0, B, h => by
    simp only [PartsOK] at h; subst h
    exact ⟨by simp, hio, [], by simp, rfl⟩
  | (bs, io', len') :: ps, b0, B, ⟨h1, h2, B', h3, h4⟩ => by
    refine ⟨h1, h2, B' ++ bytesFrom data io (io + len), by rw [h3, List.append_assoc], ?_⟩
    have hl : (bytesFrom data io' (io' + len')).length = len' := by
      rw [length_bytesFrom _ _ h2]; omega
    have := partsOK_snoc data io len hio ps (b0 + len') B' h4
    rw [h3, List.length_append, hl, show b0 + (len' + B'.length) = b0 + len' + B'.length by omega]
    exact this

/-- `tileData` returns the concatenated tile-part bytes with their consecutive ranges. -/
theorem tileData_ok {data : ByteArray} {t : Tile} {buf : ByteArray} {parts : List (Nat × Nat × Nat)}
    (h : tileData data t = .ok (buf, parts)) : PartsOK data 0 parts buf.data.toList := by
  unfold tileData at h
  dsimp only at h
  rw [← Array.forIn_toList] at h
  obtain ⟨s, hs, h⟩ := bind_ok h
  cases h
  refine forIn_inv (fun s : ByteArray × Array (Nat × Nat × Nat) => PartsOK data 0 s.2.toList s.1.data.toList)
    _ ?_ _ _ _ (by simp [PartsOK, ByteArray.empty, ByteArray.emptyWithCapacity]; rfl) hs
  intro p b r hb hr
  split at hr
  · obtain ⟨_, hh, _⟩ := bind_ok hr; cases hh
  · rename_i hc
    cases hr
    show PartsOK data 0 (b.2.push (b.1.size, p.data.offset, p.data.length)).toList
      (b.1 ++ p.data.bytes data).data.toList
    rw [Array.toList_push, ByteArray.data_append, Array.toList_append]
    have hsz : b.1.size = b.1.data.toList.length := by rw [Array.length_toList]; rfl
    rw [hsz, show (p.data.bytes data).data.toList = bytesFrom data p.data.offset (p.data.offset + p.data.length)
      from extract_toList _ _ _]
    have := partsOK_snoc data p.data.offset p.data.length
      (by simp only [ByteRange.stop, gt_iff_lt, Nat.not_lt] at hc; omega) _ 0 _ hb
    rwa [Nat.zero_add] at this

/-- A window of a byte range list. -/
theorem window (d : ByteArray) (p s n m : Nat) :
    ((bytesFrom d p s).take n).drop m = bytesFrom d (p + m) (min (p + n) s) := by
  simp only [bytesFrom, List.take_drop, List.take_take, List.drop_drop]

/-- **Translating a tile-buffer range to input ranges keeps its bytes** (the parts tile the
buffer). -/
theorem translate_bytes (data : ByteArray) : ∀ (ps : List (Nat × Nat × Nat)) (b0 : Nat) (B : List UInt8)
    (acc : Array ByteRange) (rg : ByteRange), PartsOK data b0 ps B →
    (translate rg ps acc).toList.flatMap (rb data) =
      acc.toList.flatMap (rb data) ++ (B.take (rg.stop - b0)).drop (rg.offset - b0)
  | [], b0, B, acc, rg, h => by
    simp only [PartsOK] at h; subst h; simp [translate]
  | (bs, io, len) :: ps, b0, B, acc, rg, ⟨h1, h2, B', h3, h4⟩ => by
    subst h1 h3
    simp only [translate]
    rw [translate_bytes data ps (bs + len) B' _ rg h4]
    have hX : (bytesFrom data io (io + len)).length = len := by
      rw [length_bytesFrom _ _ h2]; omega
    rw [List.take_append, List.drop_append, List.length_take, hX, window]
    have htail : List.drop (rg.offset - (bs + len)) (List.take (rg.stop - (bs + len)) B') =
        List.drop (rg.offset - bs - min (rg.stop - bs) len) (List.take (rg.stop - bs - len) B') := by
      by_cases hc : len ≤ rg.stop - bs
      · rw [Nat.min_eq_right hc, show rg.stop - (bs + len) = rg.stop - bs - len by omega,
          show rg.offset - (bs + len) = rg.offset - bs - len by omega]
      · rw [show rg.stop - bs - len = 0 by omega, show rg.stop - (bs + len) = 0 by omega]
        simp
    split
    · rename_i hlh
      rw [pushRange_bytes, List.append_assoc, rb_eq, htail]
      simp only [ByteRange.stop] at hlh ⊢
      congr 2
      · congr 1 <;> omega
    · rename_i hlh
      simp only [ByteRange.stop] at hlh htail ⊢
      rw [bytesFrom_of_le (by omega), List.nil_append, htail]

/-- Translating all ranges of a segment keeps its bytes. -/
theorem foldl_translate (data buf : ByteArray) (parts : List (Nat × Nat × Nat))
    (hp : PartsOK data 0 parts buf.data.toList) : ∀ (rs : List ByteRange) (acc : Array ByteRange),
    (rs.foldl (fun acc r => translate r parts acc) acc).toList.flatMap (rb data) =
      acc.toList.flatMap (rb data) ++ rs.flatMap (rb buf)
  | [], acc => by simp
  | r :: rs, acc => by
    simp only [List.foldl_cons, foldl_translate data buf parts hp rs, translate_bytes data parts 0 _ _ r hp,
      Nat.sub_zero, List.flatMap_cons, List.append_assoc, rb_eq, bytesFrom]

/-- A code-block of `PrecState.out`: its segments' ranges translated to the input. -/
def outBlock (parts : List (Nat × Nat × Nat)) (cb : CodeBlock) : CodeBlock :=
  { cb with segments := cb.segments.map fun s =>
      { s with ranges := s.ranges.foldl (fun acc r => translate r parts acc) #[] } }

/-- An output code-block (ranges in the input) has the spec image of the decoded one (ranges
in the tile buffer). -/
theorem outBlock_eq (data buf : ByteArray) (parts : List (Nat × Nat × Nat))
    (hp : PartsOK data 0 parts buf.data.toList) (cb : CodeBlock) :
    blockOf data (outBlock parts cb) = blockOf buf cb := by
  simp only [blockOf, outBlock, Array.toList_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro s _
  simp only [Function.comp, segOf, segment_bytes]
  congr 1
  rw [← Array.foldl_toList, foldl_translate data buf parts hp]
  simp

/-- The spec image of a fast precinct-band result (segments as their input bytes). -/
def imageBand (data : ByteArray) (b : JPEG2000.Tier2.Packet.BandOut) : Spec.Tier2.BandOut :=
  { band := b.band, rect := b.rect, maxZero := b.maxZero, blocks := b.blocks.toList.map (blockOf data) }

/-- The spec image of a fast tile result: per component, resolution, precinct, band. -/
def image (data : ByteArray) (t : TileCodeBlocks) : List (List (List (List Spec.Tier2.BandOut))) :=
  t.comps.toList.map fun rs => rs.toList.map fun ps => ps.toList.map fun p => p.bands.toList.map (imageBand data)

/-- A spec precinct result is the image of the fast one. -/
theorem out_eq (data buf : ByteArray) (parts : List (Nat × Nat × Nat))
    (hp : PartsOK data 0 parts buf.data.toList) (fp : PrecState) (sp : PrecSt) (hR : PrecRel buf fp sp)
    (k : Nat) : sp.out = (fp.out parts k).bands.toList.map (imageBand data) := by
  apply List.ext_getElem?
  intro j
  have h := hR.2 j
  simp only [PrecSt.out, PrecState.out, List.getElem?_map, Array.toList_map, List.map_map,
    Array.getElem?_toList]
  revert h
  cases fp.bands[j]? with
  | none => cases sp.bands[j]? with
    | none => intro _; rfl
    | some _ => intro h; exact absurd h id
  | some fb => cases sp.bands[j]? with
    | none => intro h; exact absurd h id
    | some sb =>
      intro ⟨e1, e2, e3, _, _, _, _, _, _, e10⟩
      simp only [Option.map_some, Function.comp, imageBand, Option.some.injEq, Spec.Tier2.BandOut.mk.injEq]
      refine ⟨e1, e2, e3, ?_⟩
      rw [e10, Array.toList_map, List.map_map]
      apply List.map_congr_left
      intro cb _
      exact (outBlock_eq data buf parts hp cb).symm

/-- The precinct results looked up by index (with defaults) correspond. -/
theorem outD_eq (data buf : ByteArray) (parts : List (Nat × Nat × Nat))
    (hp : PartsOK data 0 parts buf.data.toList) (fs : Array PrecState) (ss : List PrecSt)
    (hR : ∀ j : Nat, ORel (PrecRel buf) fs[j]? ss[j]?) (j k : Nat) :
    (ss.getD j default).out = ((fs.getD j default).out parts k).bands.toList.map (imageBand data) := by
  have h := hR j
  rw [List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?]
  revert h
  cases fs[j]? with
  | none => cases ss[j]? with
    | none =>
      intro _
      simp only [Option.getD, PrecSt.out, PrecState.out]
      show List.map _ ([] : List BandSt) = List.map _ (Array.map _ (#[] : Array BandState)).toList
      simp
    | some _ => intro h; exact absurd h id
  | some fp => cases ss[j]? with
    | none => intro h; exact absurd h id
    | some sp => intro h; exact out_eq data buf parts hp fp sp h k

/-- A computation corresponds to itself, remembering its value. -/
theorem Res.self {X : Type} (x : Except Error X) : Res (fun a b => a = b ∧ x = .ok a) x x := by
  cases x with
  | error e => trivial
  | ok a => exact ⟨rfl, rfl⟩

/-- **A tile (B.9–B.12)**: for a tile whose layout is well formed (`Layout.WF`, needed by
`Spec.Progression.forPackets_eq_spec`), the fast `decodeTilePacketsWith` and the spec
`decodeTile` both fail or both succeed; the spec result is the image of the fast one (each
code-block's geometry, inclusion, `Lblock`, zero bit-planes, passes and segments, the
segments' bytes read from the input at the fast ranges), with the same pass count and the
separate header stream's leftover = its size − the bytes the fast decoder consumed. -/
theorem decodeTile_sim (L : Limits) (h : Header) (data : ByteArray) (tp : TileParams)
    (hs : Option ByteArray) (pb : Nat)
    (hwf : ∀ g c, Layout.ofHeader h tp.index = .ok (g, c) → g.WF) :
    Res (fun (t : TileCodeBlocks) (s : TileOut) => s.comps = image data t ∧ s.passes = t.passes ∧
        (∀ hb, hs = some hb → t.headerStreamConsumed ≤ hb.size ∧
          s.hdrLeft = hb.size - t.headerStreamConsumed) ∧ (hs = none → s.hdrLeft = 0))
      (decodeTilePacketsWith L h data tp hs pb)
      (Spec.Tier2.decodeTile L h data tp (hs.map (·.data.toList)) pb) := by
  unfold decodeTilePacketsWith Spec.Tier2.decodeTile
  refine Res.bind (Res.self _) fun ⟨g, coding⟩ _ ⟨he, hg⟩ => ?_
  subst he
  dsimp only
  refine Res.check L _ _ _ _ ?_
  refine Res.bind (Res.self _) fun ⟨precs, base, spans⟩ _ ⟨he, hip⟩ => ?_
  subst he
  dsimp only
  refine Res.bind (Res.self _) fun ⟨buf, parts⟩ _ ⟨he, htd⟩ => ?_
  subst he
  dsimp only
  have hp := tileData_ok htd
  have hfr := initPrecincts_fresh hip
  rw [Spec.Progression.forPackets_eq_spec (hwf g coding hg)]
  have h0 : LRel buf hs
      { precs, hdr := match hs with
          | some hs => Reader.ofByteArray hs .tier2
          | none => Reader.ofByteArray buf .tier2,
        body := Reader.ofByteArray buf .tier2 }
      { precs := precs.toList.map PrecSt.ofFast, hdr := (hs.map (·.data.toList)).getD buf.data.toList,
        body := buf.data.toList } := by
    refine ⟨fun j => ?_, ?_, ?_, rfl, rfl, rfl, rfl, fun hb e => ?_⟩
    · rw [List.getElem?_map, Array.getElem?_toList]
      cases hj : precs[j]? with
      | none => trivial
      | some p =>
        have hm : p ∈ precs.toList := by
          rw [← Array.getElem?_toList] at hj; exact List.mem_of_getElem? hj
        exact fresh_rel buf p (hfr p hm)
    · cases hs <;> simp [rbytes, Reader.ofByteArray, bytesFrom_all]
    · simp [rbytes, Reader.ofByteArray, bytesFrom_all]
    · subst e; exact ⟨rfl, rfl⟩
  have hisn : (hs.map (·.data.toList)).isNone = hs.isNone := by cases hs <;> rfl
  rw [hisn]
  refine Res.bind (loop_sim buf hs L coding.sop coding.eph base pb _ _ _ h0)
    fun s l ⟨hP, hh, hb, hbd, hbs, hseq, hpass, hhs⟩ => ?_
  refine ⟨?_, hpass.symm, fun hb' e => ?_, fun e => ?_⟩
  · simp only [image, Array.toList_map, List.map_map]
    apply List.map_congr_left
    intro si _
    simp only [Function.comp, Array.toList_map, List.map_map]
    apply List.map_congr_left
    intro ⟨start, n⟩ _
    simp only [Function.comp, Array.toList_map, Array.toList_range, List.map_map]
    apply List.map_congr_left
    intro k _
    exact outD_eq data buf parts hp s.precs l.precs hP (start + k) k
  · subst e
    obtain ⟨hd', hs'⟩ := hhs hb' rfl
    have hle := s.hdr.pos_le
    simp only [Option.isNone_some, Bool.false_eq_true, ↓reduceIte, hh, length_rbytes, hs']
    exact ⟨by omega, trivial⟩
  · subst e
    simp only [Option.isNone_none, ↓reduceIte]

/-- **Tier-2 of a tile with its header stream** (`Tier2.Headers.decodeWithStream`, A.7.4–A.7.5,
B.9–B.12) **= the spec** (`Spec.Tier2.decodeWithStream`): both fail, or both succeed with the
spec result the image of the fast one and equal pass counts. -/
theorem decodeWithStream_sim (L : Limits) (h : Header) (data : ByteArray) (tp : TileParams)
    (hs : Option Tier2.Headers.HeaderStream) (pb : Nat)
    (hwf : ∀ g c, Layout.ofHeader h tp.index = .ok (g, c) → g.WF) :
    Res (fun (t : TileCodeBlocks) (s : TileOut) => s.comps = image data t ∧ s.passes = t.passes)
      (Tier2.Headers.decodeWithStream L h data tp hs pb)
      (Spec.Tier2.decodeWithStream L h data tp hs pb) := by
  unfold Tier2.Headers.decodeWithStream Spec.Tier2.decodeWithStream
  cases hs with
  | none =>
    have hT := decodeTile_sim L h data tp none pb hwf
    refine Res.bind hT fun t s ⟨h1, h2, _, h4⟩ => ?_
    have := h4 rfl
    simp only [this, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    exact ⟨h1, h2⟩
  | some st =>
    have hT := decodeTile_sim L h data tp (some st.bytes) pb hwf
    refine Res.bind hT fun t s ⟨h1, h2, h3, _⟩ => ?_
    obtain ⟨hle, hl⟩ := h3 st.bytes rfl
    by_cases hc : t.headerStreamConsumed = st.bytes.size
    · have e1 : (t.headerStreamConsumed != st.bytes.size) = false := by simp [hc]
      have e2 : (s.hdrLeft != 0) = false := by simp [hl, hc]
      simp only [e1, e2, Bool.false_eq_true, ↓reduceIte]
      exact ⟨h1, h2⟩
    · have e1 : (t.headerStreamConsumed != st.bytes.size) = true := by simp [hc]
      have e2 : (s.hdrLeft != 0) = true := by simp [hl]; omega
      simp only [e1, e2, ↓reduceIte]
      exact Res.error _ _

/-- `Tier2.Geometry.ofHeader` builds the B-12 rectangle of a component of the `SIZ`. -/
theorem geomOfHeader_rect {h : Header} {t c : Nat} {y : Tier2.Geometry.TileCompGeom}
    (he : Tier2.Geometry.ofHeader h t c = .ok y) :
    ∃ comp ∈ h.siz.components.toList, y.dx = comp.dx.toNat ∧ y.dy = comp.dy.toNat ∧
      y.rect = compRect (tileRect h.siz t) comp := by
  unfold Tier2.Geometry.ofHeader at he
  by_cases ht : t ≥ numTiles h.siz
  · simp only [ht, ↓reduceIte] at he; cases he
  · simp only [ht, ↓reduceIte] at he
    cases hcomp : h.siz.components[c]? with
    | none => simp only [hcomp] at he; cases he
    | some comp =>
      simp only [hcomp] at he
      split at he
      · cases he
        refine ⟨comp, ?_, rfl, rfl, rfl⟩
        rw [← Array.getElem?_toList] at hcomp; exact List.mem_of_getElem? hcomp
      · cases he

/-- **The layout of a tile is well formed** (`Layout.WF`) when every component of the `SIZ`
has non-zero sub-sampling (which `SIZ` parsing requires, A.5.1). -/
theorem ofHeader_wf {h : Header} {t : Nat} {g : Layout} {coding : Coding}
    (hd : ∀ comp ∈ h.siz.components.toList, comp.dx ≠ 0 ∧ comp.dy ≠ 0)
    (he : Layout.ofHeader h t = .ok (g, coding)) : g.WF := by
  unfold Layout.ofHeader at he
  by_cases ht : t ≥ numTiles h.siz
  · simp only [ht, ↓reduceIte] at he
    split at he <;> cases he
  · simp only [ht, ↓reduceIte] at he
    have he' : ∃ cd : Coding, (do
        let comps ← Array.mapM (fun c => Tier2.Geometry.ofHeader h t c) (Array.range h.siz.csiz)
        pure (({ tile := tileRect h.siz t, layers := cd.layers, comps := comps } : Layout), cd)) =
          (Except.ok (g, coding) : Except Error (Layout × Coding)) := by
      split at he
      · exact ⟨_, he⟩
      · exact ⟨_, he⟩
    obtain ⟨cd, he⟩ := he'
    obtain ⟨comps, hc, he⟩ := bind_ok he
    cases he
    have hall := arrayMapM_inv (fun y : Tier2.Geometry.TileCompGeom => ∃ comp ∈ h.siz.components.toList,
        y.dx = comp.dx.toNat ∧ y.dy = comp.dy.toNat ∧ y.rect = compRect (tileRect h.siz t) comp)
      _ (fun _ _ e => geomOfHeader_rect e) _ _ hc
    intro i hi
    have hmem : (Layout.comp { tile := tileRect h.siz t, layers := coding.layers, comps := comps } i) ∈ comps.toList := by
      simp only [Layout.comp, Array.getD_eq_getD_getElem?]
      simp only [Layout.numComps] at hi
      rw [Array.getElem?_eq_getElem hi]
      exact Array.getElem_mem_toList hi
    obtain ⟨comp, hcm, h1, h2, h3⟩ := hall _ hmem
    obtain ⟨d1, d2⟩ := hd comp hcm
    refine ⟨?_, ?_, ?_⟩
    · rw [h1]; have : comp.dx.toNat ≠ 0 := fun e => d1 (UInt8.toNat_inj.mp (by simp [e])); omega
    · rw [h2]; have : comp.dy.toNat ≠ 0 := fun e => d2 (UInt8.toNat_inj.mp (by simp [e])); omega
    · rw [h3, h1, h2]; rfl

end JPEG2000.Spec.Tier2Equiv
