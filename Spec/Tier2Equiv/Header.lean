import Spec.Tier2Equiv.TagTree

/-!
# Tier-2 equivalence, layer (c): one packet header
(Plan.md §4 C9, §5.1, §5.2 "Tier-2"; T.800 B.10.3–B.10.7, Table B.4, D.4, D.6)

Task 7.1b. `Res P x y` says two computations both fail or both succeed with `P`-related
values; `Res.bind` composes it through `do` blocks. Over any bit-reader invariant that
simulates `rem` (`BitSim`, layer (a)) the fast header fields follow the spec fields
(`readNumPasses_sim`, `commaCode_sim`, `readLengths_sim`), the fast `segmentPasses`
transcription is the spec's (`segmentPasses_eq`, previously only tested), and the header of one
code-block (`headerBlock_sim`), one precinct-band (`headerBand_sim`) and a whole precinct
(`headerBands_sim`) follow the spec, for fast states representing the spec states
(`BandRel`, `PrecRel`: tag trees by `Spec.TagTree.Rel`, code-blocks by `blockOf`).
-/

namespace JPEG2000.Spec.Tier2Equiv

open JPEG2000 JPEG2000.Bytes JPEG2000.Spec.Tier2 JPEG2000.Tier2.Packet

section
variable {I : BitReader → Prop}

/-- `Fol` through a bind. -/
theorem Fol.bind {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop}
    {x : Except Error (α × BitReader)} {y : Except Error (β × List Bool)}
    {f : α × BitReader → Except Error (γ × BitReader)} {g : β × List Bool → Except Error (δ × List Bool)}
    (h : Fol rem I R x y) (k : ∀ a b s, R a b → I s → Fol rem I S (f (a, s)) (g (b, rem s))) :
    Fol rem I S (x >>= f) (y >>= g) := by
  match x, y, h with
  | .error _, .error _, _ => trivial
  | .ok (a, s), .ok (b, l), ⟨hr, hl, hs⟩ => subst hl; exact k a b s hr hs

/-- `Fol` of two `pure`s. -/
theorem Fol.pure {α β : Type} {R : α → β → Prop} {a : α} {b : β} {s : BitReader} (hr : R a b)
    (hs : I s) : Fol rem I R (Pure.pure (a, s) : Except Error (α × BitReader))
      (Pure.pure (b, rem s) : Except Error (β × List Bool)) := ⟨hr, rfl, hs⟩

/-- **B.10.6** (Table B.4): `readNumPasses` follows `numPasses`. -/
theorem readNumPasses_sim (hI : BitSim I) (b : BitReader) (hb : I b) :
    Fol rem I (· = ·) (JPEG2000.Tier2.Packet.readNumPasses b) (numPasses (rem b)) := by
  unfold JPEG2000.Tier2.Packet.readNumPasses numPasses
  refine Fol.bind (readBit_sim hI b hb) fun x1 _ b1 h1 hb1 => ?_
  subst h1
  cases x1
  · exact Fol.pure rfl hb1
  refine Fol.bind (readBit_sim hI b1 hb1) fun x2 _ b2 h2 hb2 => ?_
  subst h2
  cases x2
  · exact Fol.pure rfl hb2
  refine Fol.bind (bits_sim hI b2 2 hb2) fun n3 m3 b3 h3 hb3 => ?_
  dsimp only
  by_cases e3 : m3 = 3
  · have : n3 = 3 := UInt32.toNat_inj.mp (by rw [h3, e3]; rfl)
    simp only [this, e3, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    refine Fol.bind (bits_sim hI b3 5 hb3) fun n4 m4 b4 h4 hb4 => ?_
    dsimp only
    by_cases e4 : m4 = 31
    · have : n4 = 31 := UInt32.toNat_inj.mp (by rw [h4, e4]; rfl)
      simp only [this, e4, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      refine Fol.bind (bits_sim hI b4 7 hb4) fun n5 m5 b5 h5 hb5 => ?_
      exact Fol.pure (by simp [h5]) hb5
    · have : n4 ≠ 31 := fun e => e4 (by rw [← h4, e]; rfl)
      simp only [bne_iff_ne, ne_eq, this, e4, not_false_eq_true, ↓reduceIte]
      exact Fol.pure (by simp [h4]) hb4
  · have : n3 ≠ 3 := fun e => e3 (by rw [← h3, e]; rfl)
    simp only [bne_iff_ne, ne_eq, this, e3, not_false_eq_true, ↓reduceIte]
    exact Fol.pure (by simp [h3]) hb3

end

/-- Two computations correspond: both fail, or both succeed with related values. -/
def Res {X Y : Type} (P : X → Y → Prop) : Except Error X → Except Error Y → Prop
  | .error _, .error _ => True
  | .ok x, .ok y => P x y
  | _, _ => False

/-- `Res` through a bind. -/
theorem Res.bind {X Y Z W : Type} {P : X → Y → Prop} {Q : Z → W → Prop}
    {x : Except Error X} {y : Except Error Y} {f : X → Except Error Z} {g : Y → Except Error W}
    (h : Res P x y) (k : ∀ a b, P a b → Res Q (f a) (g b)) : Res Q (x >>= f) (y >>= g) := by
  match x, y, h with
  | .error _, .error _, _ => trivial
  | .ok a, .ok b, hab => exact k a b hab

/-- `Res` through a bind on the right only. -/
theorem Res.bindR {X Y W : Type} {P : X → Y → Prop} {Q : X → W → Prop}
    {x : Except Error X} {y : Except Error Y} {g : Y → Except Error W}
    (h : Res P x y) (k : ∀ a b, P a b → Res Q (Pure.pure a) (g b)) : Res Q x (y >>= g) := by
  rw [← bind_pure x]; exact Res.bind h k

/-- `Res` through a bind on the left only. -/
theorem Res.bindL {X Y Z : Type} {P : X → Y → Prop} {Q : Z → Y → Prop}
    {x : Except Error X} {y : Except Error Y} {f : X → Except Error Z}
    (h : Res P x y) (k : ∀ a b, P a b → Res Q (f a) (Pure.pure b)) : Res Q (x >>= f) y := by
  rw [← bind_pure y]; exact Res.bind h k

/-- Weakening the relation of `Res`. -/
theorem Res.mono {X Y : Type} {P Q : X → Y → Prop} {x : Except Error X} {y : Except Error Y}
    (h : Res P x y) (k : ∀ a b, P a b → Q a b) : Res Q x y := by
  match x, y, h with
  | .error _, .error _, _ => trivial
  | .ok a, .ok b, hab => exact k a b hab

/-- `Res` of two `pure`s. -/
theorem Res.pure {X Y : Type} {P : X → Y → Prop} {a : X} {b : Y} (h : P a b) :
    Res P (Pure.pure a : Except Error X) (Pure.pure b : Except Error Y) := h

/-- `Res` of two failures. -/
theorem Res.error {X Y : Type} {P : X → Y → Prop} (e1 e2 : Error) :
    Res P (Except.error e1 : Except Error X) (Except.error e2 : Except Error Y) := trivial

/-- `ok` then bind. -/
theorem ok_bind {α β : Type} (a : α) (f : α → Except Error β) : (Except.ok a >>= f) = f a := rfl

/-- `pure` then bind. -/
theorem pure_bind' {α β : Type} (a : α) (f : α → Except Error β) :
    (Pure.pure a >>= f : Except Error β) = f a := rfl

/-- `Fol` as `Res`. -/
theorem Res.ofFol {α β : Type} {I : BitReader → Prop} {R : α → β → Prop}
    {x : Except Error (α × BitReader)} {y : Except Error (β × List Bool)} (h : Fol rem I R x y) :
    Res (fun a b => R a.1 b.1 ∧ b.2 = rem a.2 ∧ I a.2) x y := by
  match x, y, h with
  | .error _, .error _, _ => trivial
  | .ok (a, s), .ok (b, l), hab => exact hab

/-- Limit checks at different locations agree. -/
theorem Res.check {Z W : Type} {Q : Z → W → Prop} (L : Limits) (l1 l2 : Location) (kind : LimitKind)
    (v : Nat) {f : Unit → Except Error Z} {g : Unit → Except Error W} (k : Res Q (f ()) (g ())) :
    Res Q (L.check l1 kind v >>= f) (L.check l2 kind v >>= g) := by
  unfold Limits.check Limits.checkLe
  split
  · exact k
  · trivial

section Fields
variable {I : BitReader → Prop}

/-- **B.10.7.1**: `commaCode` follows the spec. -/
theorem commaCode_sim (hI : BitSim I) : ∀ (fuel acc : Nat) (b : BitReader), I b →
    Fol rem I (· = ·) (JPEG2000.Tier2.Packet.commaCode fuel acc b) (Spec.Tier2.commaCode fuel acc (rem b))
  | 0, _, _, _ => trivial
  | fuel + 1, acc, b, hb => by
    unfold JPEG2000.Tier2.Packet.commaCode Spec.Tier2.commaCode
    refine Fol.bind (readBit_sim hI b hb) fun x _ b1 h1 hb1 => ?_
    subst h1
    cases x
    · exact Fol.pure rfl hb1
    · exact commaCode_sim hI fuel (acc + 1) b1 hb1

/-- **B.10.7.2**: `readLengths` follows `lengths`. -/
theorem readLengths_sim (hI : BitSim I) (lblock : Nat) : ∀ (ps : List Nat) (b : BitReader), I b →
    Fol rem I (· = ·) (JPEG2000.Tier2.Packet.readLengths lblock ps b) (Spec.Tier2.lengths lblock ps (rem b))
  | [], b, hb => ⟨rfl, rfl, hb⟩
  | p :: ps, b, hb => by
    unfold JPEG2000.Tier2.Packet.readLengths Spec.Tier2.lengths
    refine Fol.bind (bits_sim hI b _ hb) fun n m b1 h1 hb1 => ?_
    refine Fol.bind (readLengths_sim hI lblock ps b1 hb1) fun r r' b2 h2 hb2 => ?_
    subst h1 h2
    exact Fol.pure rfl hb2

end Fields

/-- The fast `passEndsSegment` is the spec's for the mode of the style byte (D.4, D.6). -/
theorem passEndsSegment_eq (style i : Nat) :
    JPEG2000.Tier2.Packet.passEndsSegment style i =
      Spec.Tier1.passEndsSegment (Spec.Tier1.Mode.ofStyle style) i := by
  unfold JPEG2000.Tier2.Packet.passEndsSegment Spec.Tier1.passEndsSegment Spec.Tier1.Mode.ofStyle
    Spec.Tier1.passKind
  dsimp only
  by_cases h0 : i = 0
  · subst h0; simp
  · simp only [h0, ↓reduceIte]
    have : (i == 0) = false := by simp [h0]
    rw [this]
    rcases Nat.lt_or_ge ((i - 1) % 3) 3 with h | h
    · rcases (show (i - 1) % 3 = 0 ∨ (i - 1) % 3 = 1 ∨ (i - 1) % 3 = 2 by omega) with e | e | e <;>
        simp [e, show (Spec.Tier1.PassKind.magRef != Spec.Tier1.PassKind.sigProp) = true by decide,
          show (Spec.Tier1.PassKind.cleanup != Spec.Tier1.PassKind.sigProp) = true by decide]
    · omega

/-- The fast `segmentRuns` is the spec's. -/
theorem segmentRuns_eq (style : Nat) : ∀ n i cur,
    JPEG2000.Tier2.Packet.segmentRuns style n i cur =
      Spec.Tier1.segmentRuns (Spec.Tier1.Mode.ofStyle style) n i cur
  | 0, _, _ => rfl
  | n + 1, i, cur => by
    simp only [JPEG2000.Tier2.Packet.segmentRuns, Spec.Tier1.segmentRuns, passEndsSegment_eq,
      segmentRuns_eq style n]

/-- **The fast `segmentPasses` transcription is the spec's** (task 4.4 tested it on all styles;
this proves it). -/
theorem segmentPasses_eq (style n first : Nat) :
    JPEG2000.Tier2.Packet.segmentPasses style n first =
      Spec.Tier1.segmentPasses (Spec.Tier1.Mode.ofStyle style) n first :=
  segmentRuns_eq style n first 0

/-- A fast segment as a spec segment: its bytes in the body buffer `buf`, its passes. -/
def segOf (buf : ByteArray) (s : Segment) : Spec.Tier1.Segment :=
  { data := (s.bytes buf).data.toList, passes := s.passes }

/-- A fast code-block as a spec code-block (segments read from `buf`). -/
def blockOf (buf : ByteArray) (cb : CodeBlock) : BlockSt :=
  { geom := cb.geom, included := cb.included, lblock := cb.lblock, zbp := cb.zeroBitPlanes,
    passes := cb.numPasses, segs := cb.segments.toList.map (segOf buf) }

/-- A fast precinct-band state represents a spec one: same labels, tag trees representing the
spec tag-tree states, code-blocks mapped by `blockOf`. -/
def BandRel (buf : ByteArray) (fb : BandState) (sb : BandSt) : Prop :=
  sb.band = fb.band ∧ sb.rect = fb.rect ∧ sb.maxZero = fb.maxZero ∧ sb.w = fb.incl.w ∧
  sb.h = fb.incl.h ∧ fb.zbp.w = fb.incl.w ∧ fb.zbp.h = fb.incl.h ∧
  Spec.TagTree.Rel fb.incl sb.incl ∧ Spec.TagTree.Rel fb.zbp sb.zbp ∧
  sb.blocks = fb.blocks.toList.map (blockOf buf)

section Header
variable {I : BitReader → Prop}

/-- The result relation of one code-block's header. -/
def HBRel (I : BitReader → Prop) (buf : ByteArray) (x : BandState × Option Contribution × BitReader)
    (y : BandSt × Option Contribution × List Bool) : Prop :=
  BandRel buf x.1 y.1 ∧ x.2.1 = y.2.1 ∧ y.2.2 = rem x.2.2 ∧ I x.2.2

/-- The end of a code-block's header (B.10.6–B.10.7) once inclusion and zero bit-planes are
known. -/
theorem tail_sim (hI : BitSim I) (buf : ByteArray) (L : Limits) (style bi k : Nat) (c : CodeBlock)
    (fb : BandState) (sb : BandSt) (hR : BandRel buf fb sb) (br : BitReader) (hb : I br) :
    Res (HBRel I buf)
      (do
        let x1 ← readNumPasses br
        let x2 ← JPEG2000.Tier2.Packet.commaCode 33 0 x1.2
        L.check (locAt x2.2.pos) LimitKind.passesPerCodeBlock (c.numPasses + x1.1)
        let x3 ← readLengths (c.lblock + x2.1) (segmentPasses style x1.1 c.numPasses) x2.2
        pure ({ band := fb.band, rect := fb.rect, maxZero := fb.maxZero, incl := fb.incl, zbp := fb.zbp,
                blocks := fb.blocks.setIfInBounds k
                  { geom := c.geom, included := c.included, firstLayer := c.firstLayer,
                    lblock := c.lblock + x2.1, zeroBitPlanes := c.zeroBitPlanes,
                    numPasses := c.numPasses + x1.1, segments := c.segments } },
              some { band := bi, block := k, pieces := x3.1,
                     cont := decide (c.numPasses > 0) && !passEndsSegment style (c.numPasses - 1) },
              x3.2))
      (do
        let x1 ← numPasses (rem br)
        let x2 ← Spec.Tier2.commaCode 33 0 x1.2
        L.check Spec.Tier2.loc LimitKind.passesPerCodeBlock ((blockOf buf c).passes + x1.1)
        let x3 ← lengths ((blockOf buf c).lblock + x2.1)
          (Spec.Tier1.segmentPasses (Spec.Tier1.Mode.ofStyle style) x1.1 (blockOf buf c).passes) x2.2
        pure ({ band := sb.band, rect := sb.rect, w := sb.w, h := sb.h, maxZero := sb.maxZero,
                incl := sb.incl, zbp := sb.zbp,
                blocks := sb.blocks.set k
                  { geom := (blockOf buf c).geom, included := (blockOf buf c).included,
                    lblock := (blockOf buf c).lblock + x2.1, zbp := (blockOf buf c).zbp,
                    passes := (blockOf buf c).passes + x1.1, segs := (blockOf buf c).segs } },
              some { band := bi, block := k, pieces := x3.1,
                     cont := decide ((blockOf buf c).passes > 0) &&
                       !Spec.Tier1.passEndsSegment (Spec.Tier1.Mode.ofStyle style) ((blockOf buf c).passes - 1) },
              x3.2)) := by
  obtain ⟨hband, hrect, hmz, hw, hh, hzw, hzh, hRi, hRz, hbl⟩ := hR
  refine Res.bind (Res.ofFol (readNumPasses_sim hI br hb)) fun ⟨n, b1⟩ ⟨n', l1⟩ ⟨hn, hl1, hb1⟩ => ?_
  dsimp only at hn hl1 ⊢
  subst hn hl1
  refine Res.bind (Res.ofFol (commaCode_sim hI 33 0 b1 hb1)) fun ⟨m, b2⟩ ⟨m', l2⟩ ⟨hm, hl2, hb2⟩ => ?_
  dsimp only at hm hl2 ⊢
  subst hm hl2
  refine Res.check L _ _ _ _ ?_
  rw [segmentPasses_eq]
  refine Res.bind (Res.ofFol (readLengths_sim hI _ _ b2 hb2)) fun ⟨ps, b3⟩ ⟨ps', l3⟩ ⟨hp, hl3, hb3⟩ => ?_
  dsimp only at hp hl3 ⊢
  subst hp hl3
  refine ⟨⟨hband, hrect, hmz, hw, hh, hzw, hzh, hRi, hRz, ?_⟩, ?_, rfl, hb3⟩
  · rw [hbl, Array.toList_setIfInBounds, List.map_set]; rfl
  · rw [passEndsSegment_eq]; rfl

/-- **B.10.4–B.10.7, one code-block**: the fast `headerBlock` over the bit reader follows the
spec `blockHeader` over its bits. -/
theorem headerBlock_sim (hI : BitSim I) (buf : ByteArray) (L : Limits) (style layer bi k : Nat)
    (fb : BandState) (sb : BandSt) (hR : BandRel buf fb sb) (br : BitReader) (hb : I br) :
    Res (HBRel I buf) (headerBlock L style layer bi k fb br) (blockHeader L style layer bi k sb (rem br)) := by
  have hR0 := hR
  obtain ⟨hband, hrect, hmz, hw, hh, hzw, hzh, hRi, hRz, hbl⟩ := hR
  have hget : sb.blocks[k]? = (fb.blocks[k]?).map (blockOf buf) := by
    rw [hbl, List.getElem?_map, Array.getElem?_toList]
  unfold headerBlock blockHeader
  rw [hget]
  cases hcb : fb.blocks[k]? with
  | none => exact Res.error _ _
  | some cb =>
    dsimp only [Option.map]
    by_cases hinc : cb.included = true
    · have hinc' : (blockOf buf cb).included = true := hinc
      simp only [hinc, hinc', ↓reduceIte]
      refine Res.bind (Res.ofFol (readBit_sim hI br hb)) fun ⟨x, b1⟩ ⟨x', l1⟩ ⟨hx, hl1, hb1⟩ => ?_
      dsimp only at hx hl1 hb1 ⊢
      subst hx hl1
      cases x
      · exact ⟨hR0, rfl, rfl, hb1⟩
      · exact tail_sim hI buf L style bi k cb fb sb hR0 b1 hb1
    · have hinc' : (blockOf buf cb).included = false := by simpa [blockOf] using hinc
      simp only [hinc, hinc', Bool.false_eq_true, ↓reduceIte]
      have hd := decode_spec hI fb.incl sb.incl hRi br hb k (layer + 1)
      rw [← hw, ← hh] at hd
      revert hd
      cases Spec.TagTree.query sb.w sb.h sb.incl (k % sb.w) (k / sb.w) (layer + 1)
          (rem br) with
      | none =>
        intro ⟨e, he⟩
        rw [he]; exact Res.error _ _
      | some r =>
        obtain ⟨x, s1, l1⟩ := r
        intro ⟨t1, b1, he, hl1, hb1, hRt, htw, hth⟩
        rw [he]
        subst hl1
        have hR1 : BandRel buf { fb with incl := t1 } { sb with incl := s1 } :=
          ⟨hband, hrect, hmz, htw.symm, hth.symm, show fb.zbp.w = t1.w by rw [htw, hzw, hw],
            show fb.zbp.h = t1.h by rw [hth, hzh, hh], hRt, hRz, hbl⟩
        cases x
        · exact ⟨hR1, rfl, rfl, hb1⟩
        · have hv := decodeValue_spec hI fb.zbp sb.zbp hRz b1 hb1 k fb.maxZero
          rw [hzw, ← hw, hzh, ← hh] at hv
          simp only [ok_bind, pure_bind', Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          obtain ⟨E, hE⟩ : ∃ E, Spec.TagTree.exact sb.w sb.h sb.zbp (k % sb.w) (k / sb.w) sb.maxZero
              (rem b1) = E := ⟨_, rfl⟩
          have hE' := hE
          rw [hmz] at hE'
          rw [hE'] at hv
          rw [hE]
          revert hv
          cases E with
          | none =>
            intro ⟨e, he⟩
            rw [he]; exact Res.error _ _
          | some r =>
            obtain ⟨z, s2, l2⟩ := r
            intro ⟨t2, b2, he2, hl2, hb2, hRt2, htw2, hth2⟩
            rw [he2]
            subst hl2
            have hR2 : BandRel buf { fb with incl := t1, zbp := t2 } { sb with incl := s1, zbp := s2 } :=
              ⟨hband, hrect, hmz, htw.symm, hth.symm, show t2.w = t1.w by rw [htw2, htw],
                show t2.h = t1.h by rw [hth2, hth], hRt, hRt2, hbl⟩
            exact tail_sim hI buf L style bi k
              { cb with included := true, firstLayer := layer, zeroBitPlanes := z }
              { fb with incl := t1, zbp := t2 } { sb with incl := s1, zbp := s2 } hR2 b2 hb2

end Header

/-- The loop body of `headerBand` (as elaborated). -/
def bandBody (L : Limits) (style layer bi : Nat) (k : Nat)
    (s : BandState × BitReader × Array Contribution) :
    Except Error (ForInStep (BandState × BitReader × Array Contribution)) := do
  let bs := s.1
  let br := s.2.1
  let cs := s.2.2
  let (bs', c, br') ← headerBlock L style layer bi k bs br
  match c with
  | some c => pure (ForInStep.yield (bs', br', cs.push c))
  | _ => pure (ForInStep.yield (bs', br', cs))

/-- `headerBand` as a fold of `bandBody` over the code-block indices. -/
theorem headerBand_eq (L : Limits) (style layer bi : Nat) (bs : BandState) (br : BitReader) :
    headerBand L style layer bi bs br =
      (do
        let s ← forIn (List.range' 0 bs.blocks.size) (bs, br, (#[] : Array Contribution))
          (bandBody L style layer bi)
        pure (s.1, s.2.2, s.2.1)) := by
  unfold headerBand
  dsimp only
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have hs : [:bs.blocks.size].size = bs.blocks.size := by simp [Std.Legacy.Range.size]
  rw [hs]
  rfl

section
variable {I : BitReader → Prop}

/-- The code-block loop of a precinct-band. -/
theorem bandLoop_sim (hI : BitSim I) (buf : ByteArray) (L : Limits) (style layer bi : Nat) :
    ∀ (ks : List Nat) (fbs : BandState) (br : BitReader) (cs : Array Contribution) (sbs : BandSt),
      BandRel buf fbs sbs → I br →
      Res (fun (x : BandState × BitReader × Array Contribution) (y : BandSt × List Contribution × List Bool) =>
          BandRel buf x.1 y.1 ∧ x.2.2.toList = cs.toList ++ y.2.1 ∧ y.2.2 = rem x.2.1 ∧ I x.2.1)
        (forIn ks (fbs, br, cs) (bandBody L style layer bi))
        (blocksHeader L style layer bi ks sbs (rem br))
  | [], fbs, br, cs, sbs, hR, hb => by
    simp only [List.forIn_nil, blocksHeader]
    exact ⟨hR, by simp, rfl, hb⟩
  | k :: ks, fbs, br, cs, sbs, hR, hb => by
    simp only [List.forIn_cons, blocksHeader, bandBody, bind_assoc]
    refine Res.bind (headerBlock_sim hI buf L style layer bi k fbs sbs hR br hb)
      fun ⟨fbs', c, br'⟩ ⟨sbs', c', l'⟩ ⟨hR', hc, hl, hb'⟩ => ?_
    dsimp only at hR' hc hl hb' ⊢
    subst hc hl
    cases c with
    | none =>
      simp only [pure_bind']
      refine Res.bindR (bandLoop_sim hI buf L style layer bi ks fbs' br' cs sbs' hR' hb')
        fun x y ⟨h1, h2, h3, h4⟩ => ?_
      exact ⟨h1, by simpa using h2, h3, h4⟩
    | some c =>
      simp only [pure_bind']
      refine Res.bindR (bandLoop_sim hI buf L style layer bi ks fbs' br' (cs.push c) sbs' hR' hb')
        fun x y ⟨h1, h2, h3, h4⟩ => ?_
      exact ⟨h1, by simpa using h2, h3, h4⟩

/-- **One precinct-band of a packet header**: `headerBand` follows `blocksHeader` over all
code-blocks in raster order. -/
theorem headerBand_sim (hI : BitSim I) (buf : ByteArray) (L : Limits) (style layer bi : Nat)
    (fb : BandState) (sb : BandSt) (hR : BandRel buf fb sb) (br : BitReader) (hb : I br) :
    Res (fun (x : BandState × Array Contribution × BitReader) (y : BandSt × List Contribution × List Bool) =>
        BandRel buf x.1 y.1 ∧ x.2.1.toList = y.2.1 ∧ y.2.2 = rem x.2.2 ∧ I x.2.2)
      (headerBand L style layer bi fb br)
      (blocksHeader L style layer bi (List.range sb.blocks.length) sb (rem br)) := by
  have hlen : sb.blocks.length = fb.blocks.size := by rw [hR.2.2.2.2.2.2.2.2.2]; simp
  rw [headerBand_eq, hlen, List.range_eq_range', ← bind_pure (blocksHeader L style layer bi _ sb _)]
  refine Res.bind (bandLoop_sim hI buf L style layer bi _ fb br #[] sb hR hb)
    fun x y ⟨h1, h2, h3, h4⟩ => ?_
  exact ⟨h1, by simpa using h2, h3, h4⟩

end

/-- Two options related by `R` (both `none`, or both `some` related). -/
def ORel {α β : Type} (R : α → β → Prop) : Option α → Option β → Prop
  | none, none => True
  | some a, some b => R a b
  | _, _ => False

/-- A fast precinct state represents a spec one (band by band). -/
def PrecRel (buf : ByteArray) (fp : PrecState) (sp : PrecSt) : Prop :=
  sp.style = fp.style ∧ ∀ j : Nat, ORel (BandRel buf) fp.bands[j]? sp.bands[j]?

/-- The loop body of `headerBands` (as elaborated). -/
def bandsBody (L : Limits) (style layer : Nat) (bi : Nat)
    (s : Array BandState × BitReader × Array Contribution) :
    Except Error (ForInStep (Array BandState × BitReader × Array Contribution)) :=
  match s.1[bi]? with
  | some bs => do
    let (bs, c, br') ← headerBand L style layer bi bs s.2.1
    pure (ForInStep.yield (s.1.setIfInBounds bi bs, br', s.2.2 ++ c))
  | _ => do
    throw (Error.malformed JPEG2000.Tier2.Packet.loc "band index out of range")
    pure (ForInStep.yield s)

/-- `headerBands` as a fold of `bandsBody` over the band indices. -/
theorem headerBands_eq (L : Limits) (layer : Nat) (st : PrecState) (br : BitReader) :
    headerBands L layer st br =
      (do
        let s ← forIn (List.range' 0 st.bands.size) (st.bands, br, (#[] : Array Contribution))
          (bandsBody L st.style layer)
        pure ({ style := st.style, bands := s.1 }, s.2.2, s.2.1)) := by
  unfold headerBands
  dsimp only
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have hs : [:st.bands.size].size = st.bands.size := by simp [Std.Legacy.Range.size]
  rw [hs]
  rfl

section
variable {I : BitReader → Prop}

/-- The relation of the band loop's results. -/
def BandsRel (I : BitReader → Prop) (buf : ByteArray) (A : Array BandState) (bi : Nat)
    (cs : Array Contribution) (x : Array BandState × BitReader × Array Contribution)
    (y : List BandSt × List Contribution × List Bool) : Prop :=
  x.1.size = A.size ∧ (∀ j, j < bi → x.1[j]? = A[j]?) ∧
  (∀ j, ORel (BandRel buf) x.1[bi + j]? y.1[j]?) ∧
  x.2.2.toList = cs.toList ++ y.2.1 ∧ y.2.2 = rem x.2.1 ∧ I x.2.1

/-- The band loop of a packet header. -/
theorem bandsLoop_sim (hI : BitSim I) (buf : ByteArray) (L : Limits) (style layer : Nat) :
    ∀ (sbs : List BandSt) (bi : Nat) (A : Array BandState) (br : BitReader) (cs : Array Contribution),
      A.size = bi + sbs.length → (∀ j, ORel (BandRel buf) A[bi + j]? sbs[j]?) → I br →
      Res (BandsRel I buf A bi cs)
        (forIn (List.range' bi sbs.length) (A, br, cs) (bandsBody L style layer))
        (bandsHeader L style layer bi sbs (rem br))
  | [], bi, A, br, cs, hsz, hA, hb => by
    simp only [List.length_nil, List.range'_zero, List.forIn_nil, bandsHeader]
    refine ⟨rfl, fun _ _ => rfl, fun j => ?_, by simp, rfl, hb⟩
    have : A[bi + j]? = none := Array.getElem?_eq_none (by simp at hsz; omega)
    simp only [this, List.getElem?_nil, ORel]
  | sb :: sbs, bi, A, br, cs, hsz, hA, hb => by
    simp only [List.length_cons, List.range'_succ, List.forIn_cons, bandsHeader]
    have h0 := hA 0
    simp only [Nat.add_zero, List.getElem?_cons_zero] at h0
    cases hfb : A[bi]? with
    | none => rw [hfb] at h0; exact absurd h0 id
    | some fb =>
      rw [hfb] at h0
      simp only [ORel] at h0
      simp only [bandsBody, hfb, bind_assoc]
      refine Res.bind (headerBand_sim hI buf L style layer bi fb sb h0 br hb)
        fun ⟨fb', c, br'⟩ ⟨sb', c', l'⟩ ⟨hR', hc, hl, hb'⟩ => ?_
      dsimp only at hR' hc hl hb' ⊢
      subst hl
      simp only [pure_bind']
      have hsz' : (A.setIfInBounds bi fb').size = (bi + 1) + sbs.length := by
        simp at hsz ⊢; omega
      have hA' : ∀ j, ORel (BandRel buf) (A.setIfInBounds bi fb')[bi + 1 + j]? sbs[j]? := by
        intro j
        have := hA (j + 1)
        rw [Array.getElem?_setIfInBounds_ne (by omega), show bi + 1 + j = bi + (j + 1) by omega]
        simpa using this
      refine Res.bindR (bandsLoop_sim hI buf L style layer sbs (bi + 1) _ br' (cs ++ c) hsz' hA' hb')
        fun x y ⟨h1, h2, h3, h4, h5, h6⟩ => ?_
      refine ⟨by rw [h1]; simp, fun j hj => ?_, fun j => ?_, ?_, h5, h6⟩
      · rw [h2 j (by omega), Array.getElem?_setIfInBounds_ne (by omega)]
      · rcases j with _ | j
        · rw [Nat.add_zero, h2 bi (by omega),
            Array.getElem?_setIfInBounds_self_of_lt (by simp at hsz; omega)]
          exact hR'
        · have := h3 j
          rw [show bi + 1 + j = bi + (j + 1) by omega] at this
          simpa using this
      · rw [h4]; simp [hc]

/-- **The packet header after the "non-empty" bit** (B.10.3–B.10.7): `headerBands` follows
`bandsHeader` over all bands of the precinct. -/
theorem headerBands_sim (hI : BitSim I) (buf : ByteArray) (L : Limits) (layer : Nat)
    (fp : PrecState) (sp : PrecSt) (hR : PrecRel buf fp sp) (br : BitReader) (hb : I br) :
    Res (fun (x : PrecState × Array Contribution × BitReader) (y : List BandSt × List Contribution × List Bool) =>
        PrecRel buf x.1 { sp with bands := y.1 } ∧ x.2.1.toList = y.2.1 ∧ y.2.2 = rem x.2.2 ∧ I x.2.2)
      (headerBands L layer fp br) (bandsHeader L sp.style layer 0 sp.bands (rem br)) := by
  obtain ⟨hst, hbs⟩ := hR
  have hlen : fp.bands.size = sp.bands.length := by
    rcases Nat.lt_trichotomy fp.bands.size sp.bands.length with h | h | h
    · have := hbs fp.bands.size
      rw [Array.getElem?_eq_none (Nat.le_refl _), List.getElem?_eq_getElem h] at this
      exact absurd this id
    · exact h
    · have := hbs sp.bands.length
      rw [List.getElem?_eq_none (Nat.le_refl _), Array.getElem?_eq_getElem h] at this
      exact absurd this id
  rw [headerBands_eq, hlen, hst]
  refine Res.bindL (bandsLoop_sim hI buf L fp.style layer sp.bands 0 fp.bands br #[]
    (by omega) (fun j => by simpa using hbs j) hb) fun x y ⟨h1, _, h3, h4, h5, h6⟩ => ?_
  exact ⟨⟨rfl, fun j => by simpa using h3 j⟩, by simpa using h4, h5, h6⟩

end

end JPEG2000.Spec.Tier2Equiv
