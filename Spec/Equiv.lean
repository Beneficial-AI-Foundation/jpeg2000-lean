import Spec.Decode
import Spec.Tier2Equiv.Tile

/-!
# C9 composed from per-stage equivalences

Plan.md §4 (C9: "implementation = spec: end to end, `decode = Spec.decode` (exact for
reversible paths; within C8's bound for irreversible ones)"; C3, C7, C8), §5.1 (one
equivalence theorem per stage, composed into C9); T.800 Annexes B, D, E, F, G, H. Tasks 7.1a, 7.1f (real Tier-2 spec wired in).

## The statement

`c9_of_stages : Tier2Equiv → Tier2WF → Tier1Equiv → DequantLoopEquiv → DWT53PlaneEquiv →
DWT97PlaneErr → HeaderWF → ∀ L data reduce, ERel C9Rel (decodeCodestreamNarrow L data reduce)
(Spec.Decode.decode L data reduce)`, proved (no `sorry`). The relation `ERel C9Rel` is the
`≈` of C9:

* **failures**: both decoders fail (any errors), or the fast one fails with `unsupported`
  (an implementation limit: more than 31 coded bit-planes, components wider than `Int32`)
  where the spec succeeds; a fast success where the spec fails is excluded;
* **successes**: same header, same number of components, same geometry/depth/signedness
  per component; and when the decoder reports no saturated code-block
  (`saturatedBlocks = 0`), every sample satisfies `SampleRel` under C8's no-overflow
  precondition `InRangeT` (the exact inverse-DWT values the sample depends on fit the
  decoder's `Int32` fixed point; never needed for a reversible sample without MCT):
  * reversible sample: **equal** to the spec sample;
  * irreversible sample: within `cellErr F mct levels + 1` of the spec sample, where
    `cellErr` is C8's bound — dequantisation `1/2` ulp propagated through the 9/7 levels
    (`DWT97.En`), the fallback rounding `1/2` ulp, divided by `2^F`, and with the ICT
    `ictGain · (…) + ictRnd / 2^F` (`MCT.ict_c8`) — and `+ 1` for the two final roundings
    (fixed point `roundFix` vs exact `roundHalf`).

The `saturatedBlocks = 0` and `InRangeT` conditions are the overflow side conditions of C8
(`DWT97.qsrMulti_err` assumes no `Int32` overflow); for valid streams of at most 26 bits
both hold. They are part of the statement, not weakenings of it: on adversarial streams the
fast decoder saturates to `Int32` by design (Decisions 5.1, 5.5), and the exact spec does not.

## How the composition works

`Spec.Decode` writes the three levels of the fast decoder (`decodeCodestreamNarrow`,
`Assemble.decodeTile`, `Assemble.reconstructTileComp`) as skeletons with the stages as
parameters; the fast decoder is the skeleton instantiated with the fast stages **by `rfl`**
(`decodeCodestream_eq_with`, `decodeTile_eq_with`, `reconstructTileComp_eq_with`). The spec's
tile-component loop runs over the spec Tier-2 result (`Spec.Tier2.TileOut`); under `Tier2Equiv`
it is the image of the fast one, and `tileComp_image` turns the spec loop over the image into
`tileCompWith` over the fast result. Both
decoders therefore run the same loops and the same geometry/limit checks, and C9 is proved
by relational reasoning through the shared control flow (`ERel.bind`, `ERel.forIn_range`,
`ERel.forIn_range_idx`) with one relation per pipeline point:
`BlockAgree` (Tier-1) → `LoopRel` (dequantised bands) → `TCRel`/`PreRel` (inverse DWT) →
`PostArr`/`PostRel` (inverse MCT) → `OutRel`/`SampleRel` (DC shift) → `PlaneArr` (placement)
→ `C9Rel`.

## Inventory of the stage obligations

| obligation | status |
|---|---|
| `Tier2Equiv` (fast Tier-2 = the B.10 spec `Spec.Tier2.decodeWithStream`, spec result = `Spec.Tier2Equiv.image` of the fast one, for non-zero sub-sampling) | **proved**: `Spec.Tier2Wire.tier2Equiv` (from `Spec.Tier2Equiv.tier2_equiv_of_siz`, 7.1b/7.1f); the sub-sampling premise comes from `SIZ` parsing (`parse_dxdy`) |
| spec Tier-2 result in the tile-component loop | **proved**: `tileComp_image` (the spec loop over the image is `tileCompWith` with `decodeBlockSt ∘ blockOf`), `decodeBlock_eq_st` (Tier-1 on a fast code-block = on its image, for in-range segments), `tileCompWith_congr` |
| `Tier2WF` (band labels / code-block rectangles of Tier-2 output; segment ranges inside the input) | OPEN: 7.1g |
| `Tier1Equiv` (all code-block styles) | plain mode: C3 = `Spec.Tier1Equiv.c3_plain`, but the glue from `Assemble.decodeBlock` (`tier1Input`, `decodeCodeBlockSegs`, segment-structure validation) to `c3_plain` is not done; OPEN: 7.1c (modes) + glue |
| `DequantLoopEquiv` (Mallat placement of dequantised code-blocks) | **proved**: `Spec.QuantBlock.dequantLoopEquiv` (7.1d) |
| `DWT53PlaneEquiv` | **proved**: `Spec.DWTPlane.dwt53PlaneEquiv` (7.1d) |
| `DWT97PlaneErr` | **proved**: `Spec.DWTPlane.dwt97PlaneErr` (7.1d) |
| `HeaderWF` (mantissas `< 2^11`; equal transforms on components 0–2 under MCT) | OPEN: 7.1e (header validation of tasks 1.3/1.5) |
| inverse MCT (RCT/ICT, plane loops) | **proved**: `mct_step` (from `MCT.rctSample_eq`, `MCT.ictSample_eq`, `MCT.ict_c8`, `MCT.map3_get`) |
| DC shift, clamp, rounding | **proved**: `dc_step` (from `MCT.DcShift.rev_eq`/`irrev_eq`, `MCT.reconIrrev_sat`, `MCT.map1_get`, `Spec.MCT.roundFix_err`) |
| placement of tiles (`Decode.place`, `Assemble.blit`) | **proved**: `placeEquiv` |
| header parsing, output geometry, limits, tile iteration, `PPM` chunks, header streams | shared code (definitionally equal on both sides) |

`Spec.Tier2Wire.c9_of_open` is `c9_of_stages` with the proved hypotheses supplied. Task 7.1e
states C9 unconditionally by discharging the OPEN hypotheses.
-/

namespace JPEG2000.Spec.Equiv

open JPEG2000 JPEG2000.Bytes JPEG2000.Header JPEG2000.Tier2.Geometry JPEG2000.Tier2.Packet
open JPEG2000.Spec.Decode
open JPEG2000.Spec.Tier1 (Coeff)
open JPEG2000.Spec.Tier2Equiv (blockOf segOf bytesFrom image imageBand bind_ok)

/-- The error is `unsupported`: a valid feature or size the fast decoder deliberately refuses (an
implementation limit, e.g. more than 31 coded bit-planes, components wider than `Int32`). -/
def Unsupported : Error → Prop
  | .unsupported _ _ => True
  | _ => False

/-- **The relation of a fast and a spec computation that may fail** (the `≈` of C9): both succeed
with results related by `R`; or both fail (with any errors); or the fast one fails with an
`unsupported` error (an implementation limit) where the spec succeeds. A fast success where the spec
fails is excluded. -/
def ERel {α β : Type} (R : α → β → Prop) : Except Error α → Except Error β → Prop
  | .ok a, .ok b => R a b
  | .error _, .error _ => True
  | .error e, .ok _ => Unsupported e
  | .ok _, .error _ => False

/-- `ERel` is preserved by `bind` when the continuations preserve it. -/
theorem ERel.bind {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop}
    {x : Except Error α} {y : Except Error β} {f : α → Except Error γ} {g : β → Except Error δ}
    (h : ERel R x y) (k : ∀ a b, R a b → ERel S (f a) (g b)) : ERel S (x >>= f) (y >>= g) := by
  match x, y, h with
  | .error e, .error _, _ => trivial
  | .error e, .ok b, h =>
    show ERel S (.error e) (g b)
    cases g b <;> simp only [ERel] <;> exact h
  | .ok a, .ok b, h => exact k a b h

/-- A stage shared by both computations (same value on both sides). -/
theorem ERel.bind_same {α γ δ : Type} {S : γ → δ → Prop} (x : Except Error α)
    {f : α → Except Error γ} {g : α → Except Error δ}
    (k : ∀ a, ERel S (f a) (g a)) : ERel S (x >>= f) (x >>= g) := by
  cases x with
  | error e => trivial
  | ok a => exact k a

/-- `Except.ok a >>= f = f a`. -/
theorem ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) : (Except.ok a >>= f) = f a := rfl

/-- Related values are related as successful computations. -/
theorem ERel.pure {α β : Type} {R : α → β → Prop} {a : α} {b : β} (h : R a b) :
    ERel R (Pure.pure a : Except Error α) (Pure.pure b) := h

/-- Strengthen an `ERel` with a property of every fast success. -/
theorem ERel.and_left {α β : Type} {R : α → β → Prop} {P : α → Prop} {x : Except Error α}
    {y : Except Error β} (h : ERel R x y) (hp : ∀ a, x = .ok a → P a) :
    ERel (fun a b => R a b ∧ P a) x y := by
  cases x <;> cases y <;> simp only [ERel] at h ⊢ <;> first | exact h | exact ⟨h, hp _ rfl⟩

/-- Weaken the relation of an `ERel`. -/
theorem ERel.mono {α β : Type} {R S : α → β → Prop} {x : Except Error α} {y : Except Error β}
    (h : ERel R x y) (k : ∀ a b, R a b → S a b) : ERel S x y := by
  cases x <;> cases y <;> simp only [ERel] at h ⊢ <;> first | exact h | exact k _ _ h

/-- The relation lifted to `ForInStep` (same constructor). -/
def StepRel {α β : Type} (R : α → β → Prop) : ForInStep α → ForInStep β → Prop
  | .yield a, .yield b => R a b
  | .done a, .done b => R a b
  | _, _ => False

/-- Two `for` loops over the same list with bodies preserving a state relation. -/
theorem ERel.forIn_list {γ α β : Type} {R : α → β → Prop} (xs : List γ)
    (f : γ → α → Except Error (ForInStep α)) (g : γ → β → Except Error (ForInStep β))
    (hf : ∀ x a b, R a b → ERel (StepRel R) (f x a) (g x b)) :
    ∀ a b, R a b → ERel R (forIn xs a f) (forIn xs b g) := by
  induction xs with
  | nil => intro a b h; exact h
  | cons x xs ih =>
    intro a b h
    simp only [List.forIn_cons]
    apply ERel.bind (hf x a b h)
    intro s t hst
    cases s <;> cases t <;> simp only [StepRel] at hst
    · exact hst
    · exact ih _ _ hst

/-- Two `for` loops over `[0:n]` with bodies preserving a state relation. -/
theorem ERel.forIn_range {α β : Type} {R : α → β → Prop} (n : Nat)
    (f : Nat → α → Except Error (ForInStep α)) (g : Nat → β → Except Error (ForInStep β))
    (hf : ∀ x a b, R a b → ERel (StepRel R) (f x a) (g x b)) (a : α) (b : β) (h : R a b) :
    ERel R (forIn [0:n] a f) (forIn [0:n] b g) := by
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  exact ERel.forIn_list _ f g hf a b h



/-- Only `yield` steps, related by `R`. -/
def YieldRel {α β : Type} (R : α → β → Prop) : ForInStep α → ForInStep β → Prop
  | .yield a, .yield b => R a b
  | _, _ => False

/-- Index-aware loop rule over `List.range' i k`: the invariant may depend on the iteration count.
-/
theorem ERel.forIn_range'_idx {α β : Type} (I : Nat → α → β → Prop)
    (f : Nat → α → Except Error (ForInStep α)) (g : Nat → β → Except Error (ForInStep β))
    (hf : ∀ x a b, I x a b → ERel (YieldRel (I (x + 1))) (f x a) (g x b)) :
    ∀ k i a b, I i a b → ERel (I (i + k)) (forIn (List.range' i k) a f) (forIn (List.range' i k) b g) := by
  intro k
  induction k with
  | zero => intro i a b h; exact h
  | succ k ih =>
    intro i a b h
    simp only [List.range'_succ, List.forIn_cons]
    apply ERel.bind (hf i a b h)
    intro s t hst
    cases s <;> cases t <;> simp only [YieldRel] at hst
    have := ih (i + 1) _ _ hst
    rw [show i + 1 + k = i + (k + 1) by omega] at this
    exact this

/-- Index-aware loop rule over `[0:n]` (bodies that always `yield`). -/
theorem ERel.forIn_range_idx {α β : Type} (I : Nat → α → β → Prop) (n : Nat)
    (f : Nat → α → Except Error (ForInStep α)) (g : Nat → β → Except Error (ForInStep β))
    (hf : ∀ x a b, I x a b → ERel (YieldRel (I (x + 1))) (f x a) (g x b)) (a : α) (b : β)
    (h : I 0 a b) : ERel (I n) (forIn [0:n] a f) (forIn [0:n] b g) := by
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  have := ERel.forIn_range'_idx I f g hf (Std.Legacy.Range.size [0:n]) 0 a b h
  simp only [Nat.zero_add] at this
  have e : Std.Legacy.Range.size [0:n] = n := by simp [Std.Legacy.Range.size]
  rw [e] at this ⊢
  exact this

/-- reconstructTileComp is tileCompWith. -/
theorem reconstructTileComp_eq_with (L : Limits) (data : ByteArray) (tc : TileCompGeom) (depth F reduce : Nat)
    (precs : Array (Array PrecinctOut)) :
    Assemble.reconstructTileComp L data tc depth F reduce precs =
      tileCompWith (Plane.zeroChecked L Assemble.loc) (Assemble.decodeBlock data) Quant.dequantBlock
        (fun rev plane rect nl' sat => do
          let out ← if rev then DWT53.idwt53 plane rect nl' else DWT97.idwt97 plane rect nl'
          return (out, sat)) tc depth F reduce precs := rfl

/-- The fast `Assemble.decodeTile` *is* the skeleton `tileWith` with the fast stages (definitional).
-/
theorem decodeTile_eq_with (L : Limits) (h : Header) (data : ByteArray) (t reduce : Nat)
    (tcb : Option TileCodeBlocks) :
    Assemble.decodeTile L h data t reduce tcb =
      tileWith (fun t comps sat => ({ tile := t, comps, saturated := sat } : Assemble.TileOut))
        (fun tc d F r p => Assemble.reconstructTileComp L data tc d F r p)
        (fun (x : TileCodeBlocks) c => x.comps.getD c #[]) #[]
        (Plane.zero 0 0) Assemble.inverseMct (fun comp _ F => MCT.DcShift.make comp.signed comp.depth.toNat F)
        (fun dc rev pl => if rev then MCT.dcShiftClampRev dc pl else MCT.dcShiftClampIrrev dc pl)
        L h t reduce tcb := by
  cases tcb <;> rfl

/-- The fast `decodeCodestreamNarrow` *is* the skeleton `codestreamWith` with the fast stages
(definitional). -/
theorem decodeCodestream_eq_with (L : Limits) (data : ByteArray) (reduce : Nat) :
    decodeCodestreamNarrow L data reduce =
      codestreamWith Tier2.Headers.decodeWithStream (·.passes)
        (fun h t tcb => Assemble.decodeTile L h data t reduce tcb) (·.saturated) id JPEG2000.Decode.place
        (fun h info planes sat =>
          { header := h, reduce := reduce, comps := info.zipWith (fun m p => { m with plane := p }) planes,
            saturatedBlocks := sat })
        L data reduce := rfl

/-! ## The spec Tier-2 result in the tile-component loop (task 7.1f)

`Spec.decode` reads the spec Tier-2 result (`Spec.Tier2.TileOut`: code-blocks as
`Spec.Tier2.BlockSt`, segments as byte lists); the fast decoder reads `TileCodeBlocks` (segments
as byte ranges in the input). Under the Tier-2 equivalence the spec result is the image of the
fast one (`Spec.Tier2Equiv.image`: per code-block `blockOf`, each segment the bytes of its
ranges). Here: the spec tile-component loop over the image is `tileCompWith` with
`decodeBlockSt ∘ blockOf` (`tileComp_image`), and on a code-block whose ranges lie in the input,
Tier-1 on the fast code-block (`Decode.decodeBlock`, the form of `Tier1Equiv`) is Tier-1 on its
image (`decodeBlock_eq_st`). -/

/-- Every segment range of a fast code-block lies in `data`. -/
def segsIn (data : ByteArray) (cb : CodeBlock) : Bool :=
  cb.segments.all fun s => s.ranges.all fun rg => rg.offset + rg.length ≤ data.size

/-- Bytes of a range inside `a` are unchanged by appending to `a`. -/
theorem segment_append (a b : ByteArray) (st sp : Nat) (h : sp ≤ a.size) :
    Spec.MQEquiv.segment (a ++ b) st sp = Spec.MQEquiv.segment a st sp := by
  have ha : a.size = a.data.toList.length := by rw [Array.length_toList]; rfl
  simp only [Spec.MQEquiv.segment, ByteArray.data_append, Array.toList_append]
  by_cases hs : st ≤ a.size
  · rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length]
    simp only [List.length_drop]; omega
  · simp [show sp - st = 0 by omega]

/-- The bytes appended last, read back at their offset. -/
theorem segment_new (a b : ByteArray) :
    Spec.MQEquiv.segment (a ++ b) a.size (a.size + b.size) = b.data.toList := by
  have ha : a.size = a.data.toList.length := by rw [Array.length_toList]; rfl
  have hb : b.size = b.data.toList.length := by rw [Array.length_toList]; rfl
  simp only [Spec.MQEquiv.segment, ByteArray.data_append, Array.toList_append]
  rw [ha, List.drop_left, Nat.add_sub_cancel_left, hb, List.take_length]

/-- A Tier-1 range segment's bytes in `buf`, as a spec segment. -/
def segAt (buf : ByteArray) (sg : Tier1.Seg) : Spec.Tier1.Segment :=
  { data := Spec.MQEquiv.segment buf sg.start sg.stop, passes := sg.passes }

/-- One step of the concatenating fold of `tier1Input`. -/
def concatStep (data : ByteArray) (acc : ByteArray × Array Tier1.Seg) (s : Segment) :
    ByteArray × Array Tier1.Seg :=
  let bs := s.bytes data
  let off := acc.1.size
  (acc.1 ++ bs, acc.2.push { start := off, stop := off + bs.size, passes := s.passes })

/-- The invariant of the concatenating fold of `tier1Input`. -/
theorem foldl_concat (data : ByteArray) : ∀ (l : List Segment) (acc : ByteArray × Array Tier1.Seg),
    (∀ sg ∈ acc.2.toList, sg.start ≤ sg.stop ∧ sg.stop ≤ acc.1.size) →
    let res := l.foldl (concatStep data) acc;
    (∀ sg ∈ res.2.toList, sg.start ≤ sg.stop ∧ sg.stop ≤ res.1.size) ∧
    res.2.toList.map (segAt res.1) = acc.2.toList.map (segAt acc.1) ++ l.map (segOf data)
  | [], acc, h => by simpa using h
  | s :: l, acc, h => by
    simp only [List.foldl_cons, concatStep]
    have ih := foldl_concat data l (acc.1 ++ s.bytes data, acc.2.push
      { start := acc.1.size, stop := acc.1.size + (s.bytes data).size, passes := s.passes }) (by
        intro sg hsg
        simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hsg
        simp only [ByteArray.size_append]
        rcases hsg with hsg | hsg
        · have := h sg hsg; omega
        · subst hsg; simp)
    refine ⟨ih.1, ?_⟩
    rw [ih.2]
    simp only [Array.toList_push, List.map_append, List.map_cons, List.map_nil, List.append_assoc,
      List.singleton_append, segAt, segment_new]
    congr 1
    · apply List.map_congr_left
      intro sg hsg
      simp only [segAt]
      rw [segment_append _ _ _ _ (h sg hsg).2]

/-- A segment held in at most one in-range range: its direct Tier-1 range is valid and holds the
segment's bytes. -/
theorem directSeg_ok (data : ByteArray) (s : Segment) (h1 : s.ranges.size ≤ 1)
    (h2 : ∀ rg ∈ s.ranges, rg.offset + rg.length ≤ data.size) :
    (Assemble.directSeg s).start ≤ (Assemble.directSeg s).stop ∧
      (Assemble.directSeg s).stop ≤ data.size ∧ segAt data (Assemble.directSeg s) = segOf data s := by
  have hb := Spec.Tier2Equiv.segment_bytes data s
  unfold Assemble.directSeg segAt segOf
  rw [hb]
  rcases hr : s.ranges with ⟨l⟩
  rw [hr] at h1 h2
  simp only [List.size_toArray] at h1
  match l, h1, h2 with
  | [], _, _ => simp [Spec.MQEquiv.segment]
  | [rg], _, h2 =>
    have := h2 rg (by simp)
    simp only [List.getElem?_toArray, List.getElem?_cons_zero, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, Spec.Tier2Equiv.rb_eq]
    refine ⟨by omega, this, ?_⟩
    simp only [Spec.MQEquiv.segment, bytesFrom, TilePart.ByteRange.stop, List.drop_take, Nat.add_sub_cancel_left]

/-- `Assemble.tier1Input` of a code-block with in-range segments: every range valid in its
buffer, holding the segments' bytes (`segOf`). -/
theorem tier1Input_ok (data : ByteArray) (cb : CodeBlock) (hin : segsIn data cb = true) :
    (∀ sg ∈ (Assemble.tier1Input data cb).2.toList,
      sg.start ≤ sg.stop ∧ sg.stop ≤ (Assemble.tier1Input data cb).1.size) ∧
    (Assemble.tier1Input data cb).2.toList.map (segAt (Assemble.tier1Input data cb).1) =
      cb.segments.toList.map (segOf data) := by
  unfold Assemble.tier1Input
  split
  · rename_i hall
    simp only [segsIn, Array.all_eq_true', decide_eq_true_eq] at hin hall
    simp only [Array.toList_map, List.mem_map, List.map_map]
    refine ⟨?_, ?_⟩
    · rintro sg ⟨s, hs, rfl⟩
      have hs : s ∈ cb.segments := by simpa using hs
      have := directSeg_ok data s (hall s hs) (hin s hs)
      exact ⟨this.1, this.2.1⟩
    · apply List.map_congr_left
      intro s hs
      have hs : s ∈ cb.segments := by simpa using hs
      exact (directSeg_ok data s (hall s hs) (hin s hs)).2.2
  · have := foldl_concat data cb.segments.toList (ByteArray.empty, #[]) (by simp)
    rw [Array.foldl_toList] at this
    have h2 := this.2
    simp only [List.map_nil, List.nil_append] at h2
    exact ⟨this.1, h2⟩

/-- The spec code-block of a fast code-block with in-range segments is that of its spec image. -/
theorem specCodeBlock_eq (data : ByteArray) (p : CompParams) (r : Nat) (b : Band) (cb : CodeBlock)
    (hin : segsIn data cb = true) :
    specCodeBlock data p r b cb = .ok (blockStCodeBlock p r b (blockOf data cb)) := by
  obtain ⟨h1, h2⟩ := tier1Input_ok data cb hin
  unfold specCodeBlock Tier2Spec.segments
  generalize Assemble.tier1Input data cb = x at h1 h2
  obtain ⟨buf, segs⟩ := x
  have hany : (segs.any fun sg => decide (sg.start > sg.stop) || decide (sg.stop > buf.size)) = false := by
    rw [Bool.eq_false_iff]
    intro hc
    rw [Array.any_eq_true'] at hc
    obtain ⟨sg, hs, hc⟩ := hc
    have := h1 sg (by simpa using hs)
    dsimp only at this
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hc
    omega
  simp only [hany, Bool.false_eq_true, ↓reduceIte]
  show Except.ok _ = _
  simp only [blockStCodeBlock, blockOf, ← h2]
  rfl

/-- **Tier-1 on a fast code-block = Tier-1 on its spec image** when its ranges lie in the input. -/
theorem decodeBlock_eq_st (data : ByteArray) (p : CompParams) (r : Nat) (b : Band) (cb : CodeBlock)
    (hin : segsIn data cb = true) :
    Decode.decodeBlock data p r b cb = decodeBlockSt p r b (blockOf data cb) := by
  unfold Decode.decodeBlock
  rw [specCodeBlock_eq data p r b cb hin]
  rfl

/-- The spec image of a fast tile-component's Tier-2 result. -/
def imagePrecs (data : ByteArray) (precs : Array (Array PrecinctOut)) : SpecPrecs :=
  precs.toList.map fun ps => ps.toList.map fun p => p.bands.toList.map (imageBand data)

/-- Resolution `r` of the image. -/
theorem imagePrecs_getD (data : ByteArray) (precs : Array (Array PrecinctOut)) (r : Nat) :
    (imagePrecs data precs).getD r [] =
      (precs.getD r #[]).toList.map fun p => p.bands.toList.map (imageBand data) := by
  simp only [imagePrecs, List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?, List.getElem?_map,
    Array.getElem?_toList]
  cases precs[r]? <;> rfl

/-- **The spec tile-component loop over the spec image** of a fast Tier-2 result is
`tileCompWith` over the fast result with Tier-1 `decodeBlockSt ∘ blockOf`. -/
theorem tileComp_image (L : Limits) (data : ByteArray) (tc : TileCompGeom) (depth F reduce : Nat)
    (precs : Array (Array PrecinctOut)) :
    Decode.tileComp L tc depth F reduce (imagePrecs data precs) =
      tileCompWith (initSpec L) (fun p r b cb => decodeBlockSt p r b (blockOf data cb)) collect finSpec
        tc depth F reduce precs := by
  unfold Decode.tileComp tileCompWith
  simp only [imagePrecs_getD, List.forIn_map, Array.forIn_toList]
  simp only [imagePrecs, List.length_map, Array.length_toList, imageBand,
    List.forIn_map, Array.forIn_toList]
  rfl

/-- `forIn` over a list depends only on the body at the list's elements. -/
theorem list_forIn_congr {m : Type → Type} [Monad m] {α β : Type} (l : List α)
    (f g : α → β → m (ForInStep β)) (h : ∀ x ∈ l, ∀ b, f x b = g x b) (b : β) :
    forIn l b f = forIn l b g := by
  induction l generalizing b with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.forIn_cons, h x List.mem_cons_self]
    congr 1
    funext r
    cases r with
    | done => rfl
    | yield c => exact ih (fun y hy => h y (List.mem_cons_of_mem _ hy)) c

/-- `forIn` over an array depends only on the body at the array's elements. -/
theorem array_forIn_congr {m : Type → Type} [Monad m] {α β : Type} (xs : Array α)
    (f g : α → β → m (ForInStep β)) (h : ∀ x ∈ xs, ∀ b, f x b = g x b) (b : β) :
    forIn xs b f = forIn xs b g := by
  rw [← Array.forIn_toList, ← Array.forIn_toList]
  exact list_forIn_congr _ f g (fun x hx => h x (by simpa using hx)) b

/-- `tileCompWith` depends on the Tier-1 stage only at the code-blocks it visits. -/
theorem tileCompWith_congr {σ β O : Type} (init : Nat → Nat → Except Error σ)
    (dec dec' : CompParams → Nat → Band → CodeBlock → Except Error β)
    (write : σ → Rect → Nat → Nat → Band → Rect → Quant.BandQuant → Nat → β → Except Error (σ × Bool))
    (fin : Bool → σ → Rect → Nat → Nat → Except Error (O × Nat))
    (tc : TileCompGeom) (depth F reduce : Nat) (precs : Array (Array PrecinctOut))
    (h : ∀ r, ∀ prec ∈ precs.getD r #[], ∀ bo ∈ prec.bands, ∀ cb ∈ bo.blocks, ∀ p b,
      dec p r b cb = dec' p r b cb) :
    tileCompWith init dec write fin tc depth F reduce precs =
      tileCompWith init dec' write fin tc depth F reduce precs := by
  unfold tileCompWith
  dsimp only
  split
  · rfl
  · congr 1; funext plane
    congr 1
    · congr 1; funext r s
      congr 1
      apply array_forIn_congr; intro prec hprec s
      congr 1
      apply array_forIn_congr; intro bo hbo s
      congr 1
      apply array_forIn_congr; intro cb hcb s
      rw [h r prec hprec bo hbo cb hcb]

/-- The image of a tile, component `c`, is `imagePrecs` of the fast component. -/
theorem image_getD (data : ByteArray) (x : TileCodeBlocks) (c : Nat) :
    (image data x).getD c [] = imagePrecs data (x.comps.getD c #[]) := by
  simp only [image, List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?, List.getElem?_map,
    Array.getElem?_toList]
  cases x.comps[c]? <;> rfl

/-! ## Header facts used by the composition -/

/-- Non-zero sub-sampling of a `SIZ` component. -/
def DxDy (c : Marker.Component) : Prop := c.dx ≠ 0 ∧ c.dy ≠ 0

/-- A `SIZ` component read successfully has non-zero sub-sampling. -/
theorem readSizComponent_dxdy {r : Reader} {c : Marker.Component} {r' : Reader}
    (h : Marker.readSizComponent r = .ok (c, r')) : DxDy c := by
  unfold Marker.readSizComponent at h
  obtain ⟨⟨s, r1⟩, -, h⟩ := bind_ok h
  obtain ⟨_, -, h⟩ := bind_ok h
  obtain ⟨⟨dx, r2⟩, -, h⟩ := bind_ok h
  obtain ⟨_, h1, h⟩ := bind_ok h
  obtain ⟨⟨dy, r3⟩, -, h⟩ := bind_ok h
  obtain ⟨_, h2, h⟩ := bind_ok h
  unfold Marker.require at h1 h2
  split at h1 <;> rename_i e1 <;> try cases h1
  split at h2 <;> rename_i e2 <;> try cases h2
  cases h
  simp only [decide_eq_true_eq] at e1 e2
  exact ⟨e1, e2⟩

/-- `Marker.readArray Marker.readSizComponent` keeps non-zero sub-sampling. -/
theorem readArray_dxdy : ∀ (n : Nat) (acc : Array Marker.Component) (r : Reader) (out : Array Marker.Component) (r' : Reader),
    (∀ c ∈ acc.toList, DxDy c) → Marker.readArray Marker.readSizComponent acc n r = .ok (out, r') →
    ∀ c ∈ out.toList, DxDy c
  | 0, acc, r, out, r', ha, h => by
    simp only [Marker.readArray, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h; exact ha
  | n + 1, acc, r, out, r', ha, h => by
    simp only [Marker.readArray] at h
    split at h
    · cases h
    · rename_i a r'' hf
      refine readArray_dxdy n _ _ out r' ?_ h
      intro c hc
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hc
      rcases hc with hc | rfl
      · exact ha c hc
      · exact readSizComponent_dxdy hf

/-- A parsed `SIZ` has non-zero sub-sampling in every component. -/
theorem parseSIZ_dxdy {L : Limits} {r : Reader} {s : Marker.SIZ} (h : Marker.parseSIZ L r = .ok s) :
    ∀ c ∈ s.components.toList, DxDy c := by
  unfold Marker.parseSIZ at h
  repeat (obtain ⟨_, _, h⟩ := bind_ok h)
  cases h
  refine readArray_dxdy _ _ _ _ _ ?_ (by assumption)
  simp

/-- See `parseSIZ_dxdy`: the main header's `SIZ`. -/
theorem parseMainHeader_dxdy {L : Limits} {r : Reader} {mh : Marker.MainHeader} {r' : Reader}
    (h : Marker.parseMainHeader L r = .ok (mh, r')) : ∀ c ∈ mh.siz.components.toList, DxDy c := by
  unfold Marker.parseMainHeader at h
  repeat (obtain ⟨_, _, h⟩ := bind_ok h)
  split at h
  split at h
  · split at h
    · cases h; exact parseSIZ_dxdy (by assumption)
    · cases h
  · cases h

/-- See `parseSIZ_dxdy`: a parsed codestream's `SIZ`. -/
theorem parseCodestreamIn_dxdy {L : Limits} {data : ByteArray} {rg : Box.ByteRange}
    {ct : Option Box.Container} {h : Header} (hp : parseCodestreamIn L data rg ct = .ok h) :
    ∀ c ∈ h.siz.components.toList, DxDy c := by
  unfold parseCodestreamIn at hp
  obtain ⟨_, -, hp⟩ := bind_ok hp
  obtain ⟨⟨mh, r⟩, hm, hp⟩ := bind_ok hp
  repeat (obtain ⟨_, _, hp⟩ := bind_ok hp)
  cases hp
  exact parseMainHeader_dxdy hm

/-- **`SIZ` parsing rejects zero sub-sampling** (T.800 A.5.1, `XRsiz`, `YRsiz` ≥ 1): every
component of a parsed header has `dx ≠ 0` and `dy ≠ 0`. -/
theorem parse_dxdy {L : Limits} {data : ByteArray} {h : Header} (hp : Header.parse L data = .ok h) :
    ∀ comp ∈ h.siz.components.toList, comp.dx ≠ 0 ∧ comp.dy ≠ 0 := by
  unfold Header.parse at hp
  obtain ⟨_, -, hp⟩ := bind_ok hp
  exact parseCodestreamIn_dxdy hp

/-! ## Relations used by the stage hypotheses -/

/-- Band `b` of level `lvl` of an integer decomposition (`LL`: the coarsest LL). -/
def band53 (d : Spec.DWT53.Dec) (lvl : Nat) (b : Band) : Spec.DWT53.Grid :=
  match b, d.details[lvl - 1]? with
  | .LL, _ => d.ll
  | .HL, some t => t.1
  | .LH, some t => t.2.1
  | .HH, some t => t.2.2
  | _, none => ⟨fun _ _ => 0⟩

/-- Band `b` of level `lvl` of a rational decomposition. -/
def band97 (d : Spec.DWT97.Dec) (lvl : Nat) (b : Band) : Spec.DWT97.Grid :=
  match b, d.details[lvl - 1]? with
  | .LL, _ => d.ll
  | .HL, some t => t.1
  | .LH, some t => t.2.1
  | .HH, some t => t.2.2
  | _, none => ⟨fun _ _ => 0⟩

/-- `(u, v)` lies in band `b` of level `lvl` of the tile-component rectangle `rect` (B-15,
`bandRect`). -/
def InBand (rect : Rect) (lvl : Nat) (b : Band) (u v : Int) : Prop :=
  let r := bandRect rect lvl b
  (r.x0 : Int) ≤ u ∧ u < r.x1 ∧ (r.y0 : Int) ≤ v ∧ v < r.y1

/-- The sub-bands an `nl`-level inverse DWT of `rect` reads: LL of level `nl`, and
HL, LH, HH of every level `1 … nl`. -/
def ReadBand (nl lvl : Nat) (b : Band) : Prop :=
  (b = .LL ∧ lvl = nl) ∨ (b ≠ .LL ∧ 1 ≤ lvl ∧ lvl ≤ nl)

/-- Two integer decompositions agree on every band position the inverse DWT reads. -/
def BandsEq (rect : Rect) (nl : Nat) (d1 d2 : Spec.DWT53.Dec) : Prop :=
  ∀ lvl b u v, ReadBand nl lvl b → InBand rect lvl b u v →
    (band53 d1 lvl b).get u v = (band53 d2 lvl b).get u v

/-- A fixed-point decomposition (`F` fractional bits) within `ε` of a rational one (sample
units) on every band position the inverse DWT reads. -/
def BandsClose (ε : Rat) (F : Nat) (rect : Rect) (nl : Nat) (d1 : Spec.DWT53.Dec)
    (d2 : Spec.DWT97.Dec) : Prop :=
  ∀ lvl b u v, ReadBand nl lvl b → InBand rect lvl b u v →
    (((band53 d1 lvl b).get u v : Rat) - ((2 ^ F : Nat) : Rat) * (band97 d2 lvl b).get u v).abs ≤ ε

/-- Clamp a rational to the `Int32` range. -/
def clampR (y : Rat) : Rat :=
  if y < -2147483648 then -2147483648 else if 2147483647 < y then 2147483647 else y

/-- Raster position `j` of rectangle `rect`, as absolute coordinates. -/
def posU (rect : Rect) (j : Nat) : Int := rect.x0 + (j % rect.width : Nat)
/-- See `posU`. -/
def posV (rect : Rect) (j : Nat) : Int := rect.y0 + (j / rect.width : Nat)

/-- What the fast Tier-1 decoder and the spec agree on for a code-block: sizes, every
coefficient value and last decoded bit-plane (the C3 conclusion). -/
def BlockAgree (cb : CodeBlock) (o : Tier1.CodeBlockOut) (cs : Array Coeff) : Prop :=
  o.plane.width = cb.geom.rect.width ∧ o.plane.height = cb.geom.rect.height ∧
  cs.size = cb.geom.rect.width * cb.geom.rect.height ∧
  ∀ x y, x < cb.geom.rect.width → y < cb.geom.rect.height →
    (o.plane.get? (y * cb.geom.rect.width + x)).map Int32.toInt =
      some (cs.getD (y * cb.geom.rect.width + x) {}).value ∧
    o.lsbPlane x y = (cs.getD (y * cb.geom.rect.width + x) {}).lsbPlane

/-- Tier-2 output well-formedness for one tile-component: every precinct-band at resolution
`r` is one of the bands of `r` and its code-blocks lie inside that band (B.6/B.7). -/
def PrecsWF (tc : TileCompGeom) (precs : Array (Array PrecinctOut)) : Prop :=
  ∀ r, r < precs.size → ∀ prec ∈ precs.getD r #[], ∀ bo ∈ prec.bands,
    bo.band ∈ bandsOf r ∧ ∀ cb ∈ bo.blocks,
      let br := bandRect tc.rect (bandLevel tc.params.levels r) bo.band
      br.x0 ≤ cb.geom.rect.x0 ∧ br.y0 ≤ cb.geom.rect.y0 ∧ cb.geom.rect.x1 ≤ br.x1 ∧
        cb.geom.rect.y1 ≤ br.y1

/-- Header well-formedness of one tile-component's parameters: step-size mantissas `< 2^11`
(T.800 A.6.4). -/
def ParamsWF (tc : TileCompGeom) : Prop :=
  ∀ st ∈ tc.params.steps, st.mantissa.toNat < 2048

/-- Every code-block of a tile-component's Tier-2 result has its segment ranges inside the input
(`segsIn`). -/
def BlocksIn (data : ByteArray) (precs : Array (Array PrecinctOut)) : Prop :=
  ∀ r, ∀ prec ∈ precs.getD r #[], ∀ bo ∈ prec.bands, ∀ cb ∈ bo.blocks, segsIn data cb = true

/-- Tier-2 output well-formedness for a tile: `PrecsWF` per component of the tile's layout, and
every code-block's segment ranges inside the input `data` (`BlocksIn`; the fast Tier-1 refuses a
range outside its buffer, the spec's byte lists have no ranges). -/
def T2WF (h : Header) (data : ByteArray) (tp : TileParams) (x : TileCodeBlocks) : Prop :=
  (∀ g coding, Progression.Layout.ofHeader h tp.index = .ok (g, coding) →
    ∀ c, PrecsWF (g.comp c) (x.comps.getD c #[])) ∧
  ∀ c, BlocksIn data (x.comps.getD c #[])

/-- The state of the coefficient loop of a tile-component, fast (plane, saturated count) vs
spec (collected code-blocks): the plane has the rectangle's size, and when nothing
saturated its bands are the spec's (reversible) or within `1/2` ulp of them (irreversible,
`F` fractional bits). -/
def LoopRel (F : Nat) (rev : Bool) (pl : Plane) (rect : Rect) (nl n : Nat) (es : List Entry) : Prop :=
  pl.width = rect.width ∧ pl.height = rect.height ∧
  (n = 0 → if rev then BandsEq rect nl (DWT53.toDec pl rect nl) (dec53 es nl)
           else BandsClose (1 / 2) F rect nl (DWT53.toDec pl rect nl) (dec97 es nl))

/-! ## The stage hypotheses -/

/-- **Stage hypothesis: Tier-2** (B.9–B.12). For a header whose components have non-zero
sub-sampling (`SIZ` parsing guarantees it, `parse_dxdy`), the fast packet decoder and the Tier-2
spec `Spec.Tier2.decodeWithStream` both fail, or both succeed with the spec result the image of
the fast one (`Spec.Tier2Equiv.image`: same geometry, inclusion, zero bit-planes and passes per
code-block, each segment the bytes of the fast segment's ranges) and the same pass count.
Discharged: `Spec.Tier2Wire.tier2Equiv` (from `Spec.Tier2Equiv.tier2_equiv_of_siz`). -/
def Tier2Equiv : Prop :=
  ∀ (L : Limits) (h : Header) (data : ByteArray) (tp : TileParams)
    (hs : Option Tier2.Headers.HeaderStream) (n : Nat),
    (∀ comp ∈ h.siz.components.toList, comp.dx ≠ 0 ∧ comp.dy ≠ 0) →
    ERel (fun (t : TileCodeBlocks) (s : Spec.Tier2.TileOut) => s.comps = image data t ∧ s.passes = t.passes)
      (Tier2.Headers.decodeWithStream L h data tp hs n) (Tier2Spec.decode L h data tp hs n)

/-- **Stage hypothesis: Tier-2 output well-formedness.** Every tile the fast Tier-2 decodes has band
labels and code-block rectangles consistent with the layout, and segment ranges inside the input
(`T2WF`). OPEN: task 7.1g (from `Tier2.Geometry` and `Tier2.Packet`). -/
def Tier2WF : Prop :=
  ∀ (L : Limits) (h : Header) (data : ByteArray) (tp : TileParams)
    (hs : Option Tier2.Headers.HeaderStream) (n : Nat) (x : TileCodeBlocks),
    Tier2.Headers.decodeWithStream L h data tp hs n = .ok x → T2WF h data tp x

/-- **Stage hypothesis: Tier-1, every code-block style** (Annex D). The fast code-block decoder as
the pipeline calls it (`Assemble.decodeBlock`) and the spec (`Spec.Decode.decodeBlock`,
`Spec.Tier1.decodeCodeBlock`) agree (`BlockAgree`) or both fail, or the fast one refuses with
`unsupported` (K > 31). Plain mode is C3 (`Spec.Tier1Equiv.c3_plain`) up to the segment plumbing;
OPEN: task 7.1c (all modes) and the glue of `Assemble.tier1Input` / `decodeCodeBlockSegs` to
`c3_plain`. `Spec.decode` runs Tier-1 on the spec Tier-2 code-blocks (`decodeBlockSt`); on a
code-block with in-range segments the two spec forms agree (`decodeBlock_eq_st`). -/
def Tier1Equiv : Prop :=
  ∀ (data : ByteArray) (p : CompParams) (r : Nat) (b : Band) (cb : CodeBlock),
    ERel (BlockAgree cb) (Assemble.decodeBlock data p r b cb) (Decode.decodeBlock data p r b cb)

/-- **Stage hypothesis: the dequantisation block loop** (E.1.1.2, H; Mallat placement). For any
Tier-1 decoders related by `BlockAgree`, the fast coefficient loop of `tileCompWith` (dequantising
into the `Int32` plane) and the spec loop (collecting code-blocks) end in `LoopRel`, whatever
continuation `fin` follows. Per-coefficient kernels are proved (`Quant.revCoeff_eq`,
`Quant.irrevCoeff_bound`); OPEN: task 7.1d (placement in the Mallat layout, `toDec`, the
reduced-resolution band identity). -/
def DequantLoopEquiv : Prop :=
  ∀ (L : Limits) (O1 O2 : Type)
    (dec : CompParams → Nat → Band → CodeBlock → Except Error Tier1.CodeBlockOut)
    (decS : CompParams → Nat → Band → CodeBlock → Except Error (Array Coeff)),
    (∀ p r b cb, ERel (BlockAgree cb) (dec p r b cb) (decS p r b cb)) →
    ∀ (finF : Bool → Plane → Rect → Nat → Nat → Except Error (O1 × Nat))
      (finS : Bool → List Entry → Rect → Nat → Nat → Except Error (O2 × Nat))
      (RO : O1 × Nat → O2 × Nat → Prop) (tc : TileCompGeom) (depth F reduce : Nat)
      (precs : Array (Array PrecinctOut)),
    ParamsWF tc → PrecsWF tc precs →
    (∀ pl es rect nl n m, LoopRel F (tc.params.transform == .reversible53) pl rect nl n es →
      ERel RO (finF (tc.params.transform == .reversible53) pl rect nl n)
        (finS (tc.params.transform == .reversible53) es rect nl m)) →
    ERel RO (tileCompWith (Plane.zeroChecked L Assemble.loc) dec Quant.dequantBlock finF
        tc depth F reduce precs)
      (tileCompWith (initSpec L) decS collect finS tc depth F reduce precs)

/-- **Stage hypothesis: the 5/3 plane transform** (F.3.1). `DWT53.idwt53` keeps the rectangle's size
and, when its input bands are those of a spec decomposition `D`, outputs `clamp32` of
`Spec.DWT53.srMulti D` at every sample. The 1-D kernel is proved (`DWT53.lift1d_eq_sr1d`); OPEN:
task 7.1d (row/column passes, Mallat load/store, level composition, band locality of `srMulti`). -/
def DWT53PlaneEquiv : Prop :=
  ∀ (p : Plane) (rect : Rect) (nl : Nat) (D : Spec.DWT53.Dec) (q : Plane),
    p.width = rect.width → p.height = rect.height → D.details.length = nl →
    DWT53.idwt53 p rect nl = .ok q →
    q.width = rect.width ∧ q.height = rect.height ∧
    (BandsEq rect nl (DWT53.toDec p rect nl) D → ∀ j, j < rect.width * rect.height →
      (q.get? j).map Int32.toInt =
        some (MCT.clamp32 ((Spec.DWT53.srMulti (DWT53.specRect rect) nl D).get (posU rect j) (posV rect j))))

/-- **Stage hypothesis: the 9/7 plane transform error** (F.3.1, C8). `DWT97.idwt97` keeps the
rectangle's size and, when its fixed-point input bands are within `ε` ulps of a rational
decomposition `D`, every output is within `En nl ε + 1/2` ulps of `clampR (2^F · Spec.DWT97.srMulti
D)`. The fixed-point model bound is proved (`DWT97.qsrMulti_err`); OPEN: task 7.1d (fast plane loops
= `qsrMulti` model, the rounded exact fallback, band locality). -/
def DWT97PlaneErr : Prop :=
  ∀ (p : Plane) (rect : Rect) (nl F : Nat) (D : Spec.DWT97.Dec) (ε : Rat) (q : Plane),
    p.width = rect.width → p.height = rect.height → D.details.length = nl →
    DWT97.idwt97 p rect nl = .ok q →
    q.width = rect.width ∧ q.height = rect.height ∧
    (BandsClose ε F rect nl (DWT53.toDec p rect nl) D → ∀ j, j < rect.width * rect.height →
      ∃ v, q.get? j = some v ∧
        ((v.toInt : Rat) - clampR (((2 ^ F : Nat) : Rat) *
          (Spec.DWT97.srMulti (DWT53.specRect rect) nl D).get (posU rect j) (posV rect j))).abs
          ≤ DWT97.En nl ε + 1 / 2)

/-- **Stage hypothesis: header well-formedness used by the composition.** For a parsed header: step
mantissas `< 2^11`, and in a tile with the MCT, components 0–2 use the same wavelet transform (the
header validation of task 1.5 checks it). OPEN: task 7.1e. -/
def HeaderWF : Prop :=
  ∀ (L : Limits) (data : ByteArray) (h : Header), Header.parse L data = .ok h →
    ∀ (t : Nat) (g : Progression.Layout) (coding : Coding),
      Progression.Layout.ofHeader h t = .ok (g, coding) →
      (∀ c, ParamsWF (g.comp c)) ∧
      (coding.mctApplies h.siz → ∀ c, c < 3 →
        (g.comp c).params.transform = (g.comp 0).params.transform)

/-- `2^F` as a rational. -/
abbrev pw (F : Nat) : Rat := ((2 ^ F : Nat) : Rat)

/-- A fast tile-component cell vs a spec cell after the inverse DWT: reversible: the cell is
`clamp32` of the exact integer; irreversible: when `2^F·x` is in the `Int32` range, the cell is
within `En l (1/2) + 1/2` ulps of it. -/
def PreRel (F : Nat) (rev : Bool) (v : Int32) (cell : SpecCell) : Prop :=
  if rev then ∃ x l, cell = SpecCell.ofRev x l ∧ v.toInt = MCT.clamp32 x
  else ∃ x l, cell = SpecCell.ofIrrev x l ∧
    ((-2147483648 ≤ pw F * x ∧ pw F * x ≤ 2147483647) →
      ((v.toInt : Rat) - pw F * x).abs ≤ DWT97.En l (1 / 2) + 1 / 2)

/-- A fast plane and spec cells: same `w × h` size, and when `b` holds every cell related by `Rc`.
-/
def CellsRel {C : Type} [Inhabited C] (Rc : Int32 → C → Prop) (b : Prop) (p : Plane) (w h : Nat)
    (cells : Array C) : Prop :=
  p.width = w ∧ p.height = h ∧ cells.size = w * h ∧
  (b → ∀ j, j < w * h → ∃ v, p.get? j = some v ∧ Rc v (cells.getD j default))

/-- Fast vs spec result of one tile-component (plane and saturated count vs cell plane). -/
def TCRel (F : Nat) (rev : Bool) (a : Plane × Nat) (b : CellPlane × Nat) : Prop :=
  CellsRel (PreRel F rev) (a.2 = 0) a.1 b.1.width b.1.height b.1.cells

/-- `idwt53` succeeds on a plane of the rectangle's size. -/
private theorem idwt53_ok (p : Plane) (rect : Rect) (nl : Nat) (hw : p.width = rect.width)
    (hh : p.height = rect.height) : ∃ q, DWT53.idwt53 p rect nl = .ok q := by
  unfold DWT53.idwt53
  split
  · split <;> exact ⟨_, rfl⟩
  · rename_i hn; exact absurd ⟨hw, hh⟩ hn

/-- `idwt97` succeeds on a plane of the rectangle's size. -/
private theorem idwt97_ok (p : Plane) (rect : Rect) (nl : Nat) (hw : p.width = rect.width)
    (hh : p.height = rect.height) : ∃ q, DWT97.idwt97 p rect nl = .ok q := by
  unfold DWT97.idwt97
  split
  · split <;> exact ⟨_, rfl⟩
  · rename_i hn; exact absurd ⟨hw, hh⟩ hn

/-- `clampR` is the identity on the `Int32` range. -/
private theorem clampR_of (y : Rat) (h1 : -2147483648 ≤ y) (h2 : y ≤ 2147483647) : clampR y = y := by
  unfold clampR
  simp only [Rat.not_lt.mpr h1, Rat.not_lt.mpr h2, ↓reduceIte]

/-- `dec53` has `nl` detail levels. -/
private theorem dec53_length (es : List Entry) (nl : Nat) : (dec53 es nl).details.length = nl := by
  simp [dec53]

/-- `dec97` has `nl` detail levels. -/
private theorem dec97_length (es : List Entry) (nl : Nat) : (dec97 es nl).details.length = nl := by
  simp [dec97]

/-- `getD` of `Array.ofFn` in range. -/
private theorem ofFn_getD {α : Type} [Inhabited α] (n : Nat) (f : Fin n → α) (j : Nat) (hj : j < n) :
    (Array.ofFn f).getD j default = f ⟨j, hj⟩ := by
  simp [Array.getD_eq_getD_getElem?, hj]

/-- The continuation of the coefficient loop: the inverse DWT, fast vs spec. -/
theorem fin_rel (h53 : DWT53PlaneEquiv) (h97 : DWT97PlaneErr) (F : Nat) (rev : Bool)
    (pl : Plane) (es : List Entry) (rect : Rect) (nl n m : Nat)
    (hl : LoopRel F rev pl rect nl n es) :
    ERel (TCRel F rev)
      ((fun rev plane rect nl' sat => do
          let out ← if rev then DWT53.idwt53 plane rect nl' else DWT97.idwt97 plane rect nl'
          return (out, sat)) rev pl rect nl n : Except Error (Plane × Nat))
      (finSpec rev es rect nl m) := by
  obtain ⟨hw, hh, hv⟩ := hl
  cases rev with
  | true =>
    obtain ⟨q, hq⟩ := idwt53_ok pl rect nl hw hh
    simp only [↓reduceIte, hq]
    obtain ⟨qw, qh, qv⟩ := h53 pl rect nl (dec53 es nl) q hw hh (dec53_length es nl) hq
    refine ⟨qw, qh, by simp [idwt], ?_⟩
    intro h0 j hj
    have hj' : j < rect.width * rect.height := by simpa [idwt] using hj
    have hb := hv h0
    simp only [↓reduceIte] at hb
    have := qv hb j hj'
    cases hgj : q.get? j with
    | none => rw [hgj] at this; simp at this
    | some v =>
      rw [hgj] at this
      refine ⟨v, rfl, ?_⟩
      simp only [PreRel, ↓reduceIte]
      refine ⟨_, nl, ?_, (Option.some.inj this)⟩
      simp [idwt, Array.getD_eq_getD_getElem?, hj', Spec.DWT53.memo_eq, posU, posV]
  | false =>
    obtain ⟨q, hq⟩ := idwt97_ok pl rect nl hw hh
    simp only [Bool.false_eq_true, ↓reduceIte, hq]
    obtain ⟨qw, qh, qv⟩ := h97 pl rect nl F (dec97 es nl) (1 / 2) q hw hh (dec97_length es nl) hq
    refine ⟨qw, qh, by simp [idwt], ?_⟩
    intro h0 j hj
    have hj' : j < rect.width * rect.height := by simpa [idwt] using hj
    have hb := hv h0
    simp only [Bool.false_eq_true, ↓reduceIte] at hb
    obtain ⟨v, hgv, hvb⟩ := qv hb j hj'
    refine ⟨v, hgv, ?_⟩
    simp only [PreRel, Bool.false_eq_true, ↓reduceIte]
    refine ⟨(Spec.DWT97.srMulti (DWT53.specRect rect) nl (dec97 es nl)).get (posU rect j) (posV rect j),
      nl, ?_, fun hr => ?_⟩
    · simp [idwt, Array.getD_eq_getD_getElem?, hj', Spec.DWT97.memo_eq, posU, posV]
    · rw [clampR_of _ hr.1 hr.2] at hvb
      exact hvb

/-- **Tile-component level**: Tier-1, dequantisation and inverse DWT composed. -/
theorem tileComp_rel (hT1 : Tier1Equiv) (hQ : DequantLoopEquiv) (h53 : DWT53PlaneEquiv)
    (h97 : DWT97PlaneErr) (L : Limits) (data : ByteArray) (tc : TileCompGeom)
    (depth F reduce : Nat) (precs : Array (Array PrecinctOut)) (hP : ParamsWF tc)
    (hW : PrecsWF tc precs) (hB : BlocksIn data precs) :
    ERel (TCRel F (tc.params.transform == .reversible53))
      (Assemble.reconstructTileComp L data tc depth F reduce precs)
      (Decode.tileComp L tc depth F reduce (imagePrecs data precs)) := by
  rw [reconstructTileComp_eq_with, tileComp_image,
    tileCompWith_congr _ _ (Decode.decodeBlock data) _ _ _ _ _ _ _
      (fun r prec hp bo hbo cb hcb p b => (decodeBlock_eq_st data p r b cb (hB r prec hp bo hbo cb hcb)).symm)]
  exact hQ L _ _ _ _ (hT1 data) _ _ _ tc depth F reduce precs hP hW
    (fun pl es rect nl n m hl => fin_rel h53 h97 F _ pl es rect nl n m hl)

/-! ## Arrays related index by index (with defaults) -/

/-- Two arrays related index by index (with defaults beyond their common size). -/
def ArrRel {α β : Type} (P : Nat → α → β → Prop) (z : α) (w : β) (xs : Array α) (ys : Array β) : Prop :=
  xs.size = ys.size ∧ ∀ c, P c (xs.getD c z) (ys.getD c w)

/-- `ArrRel` is preserved by pushing related values. -/
theorem ArrRel.push {α β : Type} {P : Nat → α → β → Prop} {z : α} {w : β} {xs : Array α}
    {ys : Array β} {x : α} {y : β} (h : ArrRel P z w xs ys) (hx : P xs.size x y) :
    ArrRel P z w (xs.push x) (ys.push y) := by
  obtain ⟨hs, hc⟩ := h
  refine ⟨by simp [hs], fun c => ?_⟩
  have := hc c
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push] at this ⊢
  by_cases e : c = xs.size
  · subst e; simp only [↓reduceIte, hs, Option.getD_some]; rw [← hs]; exact hx
  · have e' : ¬ c = ys.size := by rw [← hs]; exact e
    simp only [e, e', ↓reduceIte]; exact this

/-- `ArrRel` is preserved by resetting an index to the defaults. -/
theorem ArrRel.set {α β : Type} {P : Nat → α → β → Prop} {z : α} {w : β} {xs : Array α}
    {ys : Array β} (h : ArrRel P z w xs ys) (hz : ∀ c, P c z w) (i : Nat) :
    ArrRel P z w (xs.setIfInBounds i z) (ys.setIfInBounds i w) := by
  obtain ⟨hs, hc⟩ := h
  refine ⟨by simp [hs], fun c => ?_⟩
  have := hc c
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds] at this ⊢
  by_cases e : i = c
  · subst e
    have hz' := hz i
    by_cases hi : i < xs.size
    · have hi' : i < ys.size := hs ▸ hi
      simpa [hi, hi'] using hz'
    · have hi' : ¬ i < ys.size := by rw [← hs]; exact hi
      simpa [hi, hi'] using hz'
  · simp [e]; exact this

/-- Weaken the relation of an `ArrRel`. -/
theorem ArrRel.mono {α β : Type} {P Q : Nat → α → β → Prop} {z : α} {w : β} {xs : Array α}
    {ys : Array β} (h : ArrRel P z w xs ys) (k : ∀ c a b, P c a b → Q c a b) :
    ArrRel Q z w xs ys := ⟨h.1, fun c => k c _ _ (h.2 c)⟩

/-- Weaken the relation and the condition of a `CellsRel`. -/
theorem CellsRel.mono {C : Type} [Inhabited C] {R1 R2 : Int32 → C → Prop} {b1 b2 : Prop}
    {p : Plane} {w h : Nat} {cells : Array C} (hr : CellsRel R1 b1 p w h cells) (hb : b2 → b1)
    (k : ∀ v c, R1 v c → R2 v c) : CellsRel R2 b2 p w h cells := by
  obtain ⟨a, b, c, d⟩ := hr
  refine ⟨a, b, c, fun h2 j hj => ?_⟩
  obtain ⟨v, hv, hr⟩ := d (hb h2) j hj
  exact ⟨v, hv, k _ _ hr⟩

/-- The empty plane is related to no cells. -/
theorem CellsRel.zero {C : Type} [Inhabited C] (R : Int32 → C → Prop) (b : Prop) :
    CellsRel R b (Plane.zero 0 0) 0 0 #[] :=
  ⟨rfl, rfl, rfl, fun _ j hj => absurd hj (by simp)⟩

/-! ## Error bounds and the sample relation -/

/-- Maximum of two rationals. -/
def rmax (a b : Rat) : Rat := if a ≤ b then b else a

/-- C8 error of the irreversible path of one component in sample units: dequantisation (`1/2` ulp)
through `nl` 9/7 levels (`En nl (1/2)`), plus the `1/2` ulp of the rounded fallback, divided by
`2^F`. -/
def errOf (F l : Nat) : Rat := (DWT97.En l (1 / 2) + 1 / 2) / pw F

/-- Largest `errOf` over a list of decomposition levels. -/
def maxErr (F : Nat) : List Nat → Rat
  | [] => 0
  | l :: ls => rmax (errOf F l) (maxErr F ls)

/-- C8 error of an exact irreversible value before rounding: `errOf` without MCT; with the ICT
`ictGain · maxErr + ictRnd / 2^F` (`MCT.ict_c8`). -/
def cellErr (F : Nat) (mct : Bool) (levels : List Nat) : Rat :=
  if mct then MCT.ictGain * maxErr F levels + MCT.ictRnd / pw F else errOf F (levels.headD 0)

/-- The numeric-range precondition of C9 for one sample (C8's "no overflow"): the exact inverse-DWT
outputs the sample depends on, times `2^F` (irreversible) or as integers (reversible), lie in the
`Int32` range. Not needed for a reversible sample without MCT. -/
def InRangeT (rev mct : Bool) (F : Nat) (peers : List Rat) : Prop :=
  (rev = true ∧ mct = false) ∨
    ∀ y ∈ peers, -2147483648 ≤ pw (if rev then 0 else F) * y ∧ pw (if rev then 0 else F) * y ≤ 2147483647

/-- A fast cell vs a spec cell after the inverse MCT: when in range, the cell is `clamp32 w` for an
integer `w` equal to the exact value (reversible) or within `cellErr` of it in sample units
(irreversible). -/
def PostRel (s : Marker.SIZ) (mct : Bool) (c : Nat) (rev : Bool) (v : Int32) (cell : SpecCell) : Prop :=
  cell.rev = rev ∧ Assemble.fracBitsOf s mct c = Assemble.fracBitsOf s cell.mct c ∧
  (InRangeT cell.rev cell.mct (Assemble.fracBitsOf s cell.mct c) cell.peers →
    ∃ w : Int, v.toInt = MCT.clamp32 w ∧
      (if cell.rev then w = cell.ival
       else ((w : Rat) / pw (Assemble.fracBitsOf s cell.mct c) - cell.rval).abs ≤
         cellErr (Assemble.fracBitsOf s cell.mct c) cell.mct cell.levels))

/-- **The per-sample C9 relation**: when the sample is in range (`InRangeT`), a reversible sample
equals the spec sample, an irreversible one is within `cellErr + 1` of it (C8's bound plus the two
roundings). -/
def SampleRel (h : Header) (c : Nat) (v : Int32) (x : SpecSample) : Prop :=
  InRangeT x.reversible x.mct (Assemble.fracBitsOf h.siz x.mct c) x.peers →
    if x.reversible then v.toInt = x.value
    else ((v.toInt : Rat) - x.value).abs ≤ cellErr (Assemble.fracBitsOf h.siz x.mct c) x.mct x.levels + 1

/-- Component `c` of a tile layout uses the reversible 5/3 transform. -/
def revOf (g : Progression.Layout) (c : Nat) : Bool := (g.comp c).params.transform == .reversible53

/-- Fast planes vs spec cell planes of a tile after the inverse DWT (`PreRel` per component). -/
def PreArr (s : Marker.SIZ) (g : Progression.Layout) (mct : Bool) (b : Prop) : Array Plane → Array CellPlane → Prop :=
  ArrRel (fun c a cp => CellsRel (PreRel (Assemble.fracBitsOf s mct c) (revOf g c)) b a cp.width cp.height cp.cells)
    (Plane.zero 0 0) CellPlane.empty

/-- Fast planes vs spec cell planes of a tile after the inverse MCT (`PostRel` per component). -/
def PostArr (s : Marker.SIZ) (g : Progression.Layout) (mct : Bool) (b : Prop) : Array Plane → Array CellPlane → Prop :=
  ArrRel (fun c a cp => CellsRel (PostRel s mct c (revOf g c)) b a cp.width cp.height cp.cells)
    (Plane.zero 0 0) CellPlane.empty

/-- Fast vs spec reconstructed tile-components (rectangle and `SampleRel` per component). -/
def OutRel (h : Header) (b : Prop) : Array (Rect × Plane) → Array (Rect × SamplePlane) → Prop :=
  ArrRel (fun c a sp => a.1 = sp.1 ∧ CellsRel (SampleRel h c) b a.2 sp.2.width sp.2.height sp.2.samples)
    (default, Plane.zero 0 0) default

/-- Fast vs spec reconstructed tile (same index; `OutRel` when nothing saturated). -/
def TileRel (h : Header) (o : Assemble.TileOut) (s : Decode.TileOut) : Prop :=
  o.tile = s.tile ∧ OutRel h (o.saturated = 0) o.comps s.comps

/-- `clamp32` is the identity on `Int32` values. -/
private theorem clamp32_int32 (v : Int32) : MCT.clamp32 v.toInt = v.toInt := by
  have h1 := v.le_toInt; have h2 := v.toInt_lt
  unfold MCT.clamp32
  apply Spec.MCT.clamp_of_mem <;> omega

/-- `2^F > 0`. -/
private theorem pw_pos (F : Nat) : (0 : Rat) < pw F := by
  have : 0 < 2 ^ F := Nat.two_pow_pos F
  unfold pw; exact_mod_cast this

/-- `|a − D·x| ≤ E` ⇒ `|a/D − x| ≤ E/D` for `D > 0`. -/
private theorem div_close (a x E D : Rat) (hD : 0 < D) (h : (a - D * x).abs ≤ E) :
    (a / D - x).abs ≤ E / D := by
  have hD' : D ≠ 0 := by grind
  have e : a / D - x = (a - D * x) * (1 / D) := by grind
  rw [e]
  have := Spec.DWT97.abs_mul_le _ (1 / D) E h
  have hk : (0 : Rat) ≤ 1 / D := by
    have := Rat.le_of_lt (Rat.inv_pos.mpr hD)
    rw [Rat.div_def, Rat.one_mul]; exact this
  rw [Rat.abs_of_nonneg hk] at this
  have e2 : E * (1 / D) = E / D := by grind
  rw [e2] at this
  exact this

/-- Without MCT a cell after the inverse DWT satisfies the post-MCT relation. -/
private theorem pre_post_cell (s : Marker.SIZ) (c : Nat) (rev : Bool) (v : Int32) (cell : SpecCell)
    (h : PreRel (Assemble.fracBitsOf s false c) rev v cell) : PostRel s false c rev v cell := by
  cases rev with
  | true =>
    obtain ⟨x, l, rfl, hv⟩ := h
    exact ⟨rfl, rfl, fun _ => ⟨x, hv, rfl⟩⟩
  | false =>
    obtain ⟨x, l, rfl, hv⟩ := h
    refine ⟨rfl, rfl, fun hr => ⟨v.toInt, (clamp32_int32 v).symm, ?_⟩⟩
    rcases hr with ⟨h1, _⟩ | hr
    · simp [SpecCell.ofIrrev] at h1
    have hx := hr x (by simp [SpecCell.ofIrrev])
    simp only [SpecCell.ofIrrev, Bool.false_eq_true, ↓reduceIte] at hx ⊢
    have := hv hx
    exact div_close _ _ _ _ (pw_pos _) this

/-- Without MCT, `PreArr` gives `PostArr`. -/
theorem pre_post (s : Marker.SIZ) (g : Progression.Layout) (mct : Bool) (b : Prop) (ps : Array Plane)
    (cs : Array CellPlane) (h : PreArr s g mct b ps cs) (hm : mct = false) : PostArr s g mct b ps cs := by
  subst hm
  exact ArrRel.mono h fun c _ _ k => CellsRel.mono k id fun v cell r => pre_post_cell s c _ v cell r

/-- `MCT.map3` keeps the planes' dimensions. -/
private theorem map3_dims {N : Nat} (f : Int32 → Int32 → Int32 → Int32 × Int32 × Int32)
    (b0 b1 b2 : DWT53.Buf N) (i : Nat) :
    (MCT.map3 f b0 b1 b2 i).1.1.width = b0.1.width ∧ (MCT.map3 f b0 b1 b2 i).1.1.height = b0.1.height ∧
    (MCT.map3 f b0 b1 b2 i).2.1.1.width = b1.1.width ∧ (MCT.map3 f b0 b1 b2 i).2.1.1.height = b1.1.height ∧
    (MCT.map3 f b0 b1 b2 i).2.2.1.width = b2.1.width ∧ (MCT.map3 f b0 b1 b2 i).2.2.1.height = b2.1.height := by
  unfold MCT.map3
  split
  · rename_i hi
    have := map3_dims f
      (b0.set i (f (b0.get i hi) (b1.get i hi) (b2.get i hi)).1 hi)
      (b1.set i (f (b0.get i hi) (b1.get i hi) (b2.get i hi)).2.1 hi)
      (b2.set i (f (b0.get i hi) (b1.get i hi) (b2.get i hi)).2.2 hi) (i + 1)
    exact this
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
termination_by N - i

/-- `get?` in range. -/
private theorem plane_get?_of (p : Plane) (j : Nat) (hj : j < p.width * p.height) :
    p.get? j = some (p.get j hj) := by
  simp [Plane.get?, hj]

/-- `MCT.apply3` on planes of equal dimensions succeeds, keeps them and applies the kernel cell by
cell. -/
private theorem apply3_ok (f : Int32 → Int32 → Int32 → Int32 × Int32 × Int32) (p0 p1 p2 : Plane)
    (hd : p1.width = p0.width ∧ p1.height = p0.height ∧ p2.width = p0.width ∧ p2.height = p0.height) :
    ∃ q0 q1 q2, MCT.apply3 f p0 p1 p2 = .ok (q0, q1, q2) ∧
      q0.width = p0.width ∧ q0.height = p0.height ∧ q1.width = p1.width ∧ q1.height = p1.height ∧
      q2.width = p2.width ∧ q2.height = p2.height ∧
      ∀ j, j < p0.width * p0.height → ∃ a b c, p0.get? j = some a ∧ p1.get? j = some b ∧
        p2.get? j = some c ∧ q0.get? j = some (f a b c).1 ∧ q1.get? j = some (f a b c).2.1 ∧
        q2.get? j = some (f a b c).2.2 := by
  unfold MCT.apply3
  simp only [hd, and_self, ↓reduceDIte]
  refine ⟨_, _, _, rfl, ?_⟩
  have hdm := map3_dims f (N := p0.width * p0.height) ⟨p0, rfl⟩ ⟨p1, by rw [hd.1, hd.2.1]⟩
    ⟨p2, by rw [hd.2.2.1, hd.2.2.2]⟩ 0
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := hdm
  refine ⟨d1, d2, d3.trans hd.1, d4.trans hd.2.1, d5.trans hd.2.2.1, d6.trans hd.2.2.2, fun j hj => ?_⟩
  have hg := MCT.map3_get f (N := p0.width * p0.height) ⟨p0, rfl⟩ ⟨p1, by rw [hd.1, hd.2.1]⟩
    ⟨p2, by rw [hd.2.2.1, hd.2.2.2]⟩ 0 j hj
  simp only [Nat.not_lt_zero, ↓reduceIte] at hg
  obtain ⟨g0, g1, g2⟩ := hg
  have hj1 : j < p1.width * p1.height := by rw [hd.1, hd.2.1]; exact hj
  have hj2 : j < p2.width * p2.height := by rw [hd.2.2.1, hd.2.2.2]; exact hj
  refine ⟨_, _, _, plane_get?_of p0 j hj, plane_get?_of p1 j hj1, plane_get?_of p2 j hj2, ?_, ?_, ?_⟩
  · rw [plane_get?_of _ j (by rw [d1, d2]; exact hj)]; exact congrArg some g0
  · rw [plane_get?_of _ j (by rw [d3, d4]; exact hj1)]; exact congrArg some g1
  · rw [plane_get?_of _ j (by rw [d5, d6]; exact hj2)]; exact congrArg some g2

/-- Reading back the zero-then-set sequence of `Assemble.inverseMct`. -/
private theorem set6_getD {α : Type} (A : Array α) (z x0 x1 x2 : α) (c : Nat) :
    ((((((A.setIfInBounds 0 z).setIfInBounds 1 z).setIfInBounds 2 z).setIfInBounds 0 x0).setIfInBounds 1 x1).setIfInBounds 2 x2).getD c z =
      if c < A.size then (if c = 0 then x0 else if c = 1 then x1 else if c = 2 then x2 else A.getD c z)
      else z := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, Array.size_setIfInBounds]
  by_cases h0 : c = 0
  · subst h0; by_cases hs : 0 < A.size <;> simp [hs]
  by_cases h1 : c = 1
  · subst h1; by_cases hs : 1 < A.size <;> simp [hs]
  by_cases h2 : c = 2
  · subst h2; by_cases hs : 2 < A.size <;> simp [hs]
  have a0 : (0 = c) = False := by simp; omega
  have a1 : (1 = c) = False := by simp; omega
  have a2 : (2 = c) = False := by simp; omega
  by_cases hs : c < A.size
  · simp [a0, a1, a2, h0, h1, h2, hs]
  · simp [a0, a1, a2, hs]

/-- Components `≥ 3` have the same fractional bits with or without MCT. -/
private theorem fb_ge3 (s : Marker.SIZ) (c : Nat) (hc : 3 ≤ c) :
    Assemble.fracBitsOf s true c = Assemble.fracBitsOf s false c := by
  unfold Assemble.fracBitsOf; simp; omega

/-- Components 0–2 share their fractional bits under the MCT. -/
private theorem fb_lt3 (s : Marker.SIZ) (c : Nat) (hc : c < 3) :
    Assemble.fracBitsOf s true c = Assemble.fracBitsOf s true 0 := by
  unfold Assemble.fracBitsOf; simp [hc]

/-- `a ≤ rmax a b`. -/
private theorem le_rmax_l (a b : Rat) : a ≤ rmax a b := by unfold rmax; split <;> grind
/-- `b ≤ rmax a b`. -/
private theorem le_rmax_r (a b : Rat) : b ≤ rmax a b := by unfold rmax; split <;> grind

/-- `|v| ≤ 2^31` for an `Int32`. -/
private theorem int32_abs (v : Int32) : ((v.toInt : Int) : Rat).abs ≤ 2147483648 := by
  have h1 := v.le_toInt; have h2 := v.toInt_lt
  apply Spec.DWT97.abs_le_iff.mpr
  have a1 : ((-2147483648 : Int) : Rat) ≤ (v.toInt : Rat) := Rat.intCast_le_intCast.mpr (by omega)
  have a2 : (v.toInt : Rat) ≤ ((2147483648 : Int) : Rat) := Rat.intCast_le_intCast.mpr (by omega)
  push_cast at a1 a2
  exact ⟨a1, a2⟩

/-- An integer in the `Int32` range (as a rational) is fixed by `clamp32`. -/
private theorem int_range_of_rat (x : Int) (h : -2147483648 ≤ pw 0 * (x : Rat) ∧ pw 0 * (x : Rat) ≤ 2147483647) :
    MCT.clamp32 x = x := by
  have e : pw 0 * (x : Rat) = ((x : Int) : Rat) := by simp [pw]
  rw [e] at h
  have a1 : ((-2147483648 : Int) : Rat) ≤ (x : Rat) := by push_cast; exact h.1
  have a2 : (x : Rat) ≤ ((2147483647 : Int) : Rat) := by push_cast; exact h.2
  have b1 := Rat.intCast_le_intCast.mp a1
  have b2 := Rat.intCast_le_intCast.mp a2
  unfold MCT.clamp32
  exact Spec.MCT.clamp_of_mem _ _ _ b1 b2

/-- **C7 kernel in context**: the fast inverse RCT on three related cells gives cells related to the
spec RCT (`MCT.rctSample_eq`). -/
theorem rct_cell (s : Marker.SIZ) (v0 v1 v2 : Int32) (a0 a1 a2 : SpecCell)
    (h0 : PreRel (Assemble.fracBitsOf s true 0) true v0 a0)
    (h1 : PreRel (Assemble.fracBitsOf s true 1) true v1 a1)
    (h2 : PreRel (Assemble.fracBitsOf s true 2) true v2 a2) :
    PostRel s true 0 true (MCT.rctSample v0 v1 v2).1 (rctCells a0 a1 a2).1 ∧
    PostRel s true 1 true (MCT.rctSample v0 v1 v2).2.1 (rctCells a0 a1 a2).2.1 ∧
    PostRel s true 2 true (MCT.rctSample v0 v1 v2).2.2 (rctCells a0 a1 a2).2.2 := by
  obtain ⟨x0, l0, rfl, e0⟩ := h0
  obtain ⟨x1, l1, rfl, e1⟩ := h1
  obtain ⟨x2, l2, rfl, e2⟩ := h2
  obtain ⟨o0, o1, o2⟩ := MCT.rctSample_eq v0 v1 v2
  have key : InRangeT true true 0 ([(x0 : Rat)] ++ [(x1 : Rat)] ++ [(x2 : Rat)]) →
      v0.toInt = x0 ∧ v1.toInt = x1 ∧ v2.toInt = x2 := by
    intro hin
    rcases hin with ⟨_, hf⟩ | hin
    · exact absurd hf (by decide)
    simp only [↓reduceIte] at hin
    refine ⟨?_, ?_, ?_⟩
    · rw [e0]; exact int_range_of_rat x0 (hin _ (by simp))
    · rw [e1]; exact int_range_of_rat x1 (hin _ (by simp))
    · rw [e2]; exact int_range_of_rat x2 (hin _ (by simp))
  simp only [rctCells, SpecCell.ofRev]
  refine ⟨⟨rfl, rfl, fun hin => ?_⟩, ⟨rfl, rfl, fun hin => ?_⟩, ⟨rfl, rfl, fun hin => ?_⟩⟩ <;>
    obtain ⟨k0, k1, k2⟩ := key hin <;> simp only [k0, k1, k2] at o0 o1 o2 <;>
    exact ⟨_, by assumption, by simp⟩

/-- **C8 for the ICT in context**: the fast inverse ICT on three related cells gives cells within
`cellErr` of the exact ICT (`MCT.ict_c8`). -/
theorem ict_cell (s : Marker.SIZ) (v0 v1 v2 : Int32) (a0 a1 a2 : SpecCell)
    (h0 : PreRel (Assemble.fracBitsOf s true 0) false v0 a0)
    (h1 : PreRel (Assemble.fracBitsOf s true 1) false v1 a1)
    (h2 : PreRel (Assemble.fracBitsOf s true 2) false v2 a2) :
    PostRel s true 0 false (MCT.ictSample v0 v1 v2).1 (ictCells a0 a1 a2).1 ∧
    PostRel s true 1 false (MCT.ictSample v0 v1 v2).2.1 (ictCells a0 a1 a2).2.1 ∧
    PostRel s true 2 false (MCT.ictSample v0 v1 v2).2.2 (ictCells a0 a1 a2).2.2 := by
  have f1 := fb_lt3 s 1 (by decide)
  have f2 := fb_lt3 s 2 (by decide)
  rw [f1] at h1; rw [f2] at h2
  generalize hF : Assemble.fracBitsOf s true 0 = F at h0 h1 h2
  obtain ⟨x0, l0, rfl, e0⟩ := h0
  obtain ⟨x1, l1, rfl, e1⟩ := h1
  obtain ⟨x2, l2, rfl, e2⟩ := h2
  obtain ⟨o0, o1, o2⟩ := MCT.ictSample_eq v0 v1 v2
  have key : InRangeT false true F ([x0] ++ [x1] ++ [x2]) →
      let e := maxErr F ([l0] ++ [l1] ++ [l2])
      (((v0.toInt : Int) : Rat) / pw F - x0).abs ≤ e ∧ (((v1.toInt : Int) : Rat) / pw F - x1).abs ≤ e ∧
        (((v2.toInt : Int) : Rat) / pw F - x2).abs ≤ e := by
    intro hin
    rcases hin with ⟨hf, _⟩ | hin
    · exact absurd hf (by decide)
    simp only [Bool.false_eq_true, ↓reduceIte] at hin
    have b0 := div_close _ _ _ _ (pw_pos F) (e0 (hin x0 (by simp)))
    have b1 := div_close _ _ _ _ (pw_pos F) (e1 (hin x1 (by simp)))
    have b2 := div_close _ _ _ _ (pw_pos F) (e2 (hin x2 (by simp)))
    simp only [List.cons_append, List.nil_append, maxErr]
    have m0 := le_rmax_l (errOf F l0) (rmax (errOf F l1) (rmax (errOf F l2) 0))
    have m1 := le_rmax_l (errOf F l1) (rmax (errOf F l2) 0)
    have m1' := le_rmax_r (errOf F l0) (rmax (errOf F l1) (rmax (errOf F l2) 0))
    have m2 := le_rmax_l (errOf F l2) 0
    have m2' := le_rmax_r (errOf F l1) (rmax (errOf F l2) 0)
    unfold errOf at *
    refine ⟨Rat.le_trans b0 m0, Rat.le_trans b1 (Rat.le_trans m1 m1'),
      Rat.le_trans b2 (Rat.le_trans m2 (Rat.le_trans m2' m1'))⟩
  have hF0 : Assemble.fracBitsOf s true 0 = F := hF
  have hF1 : Assemble.fracBitsOf s true 1 = F := f1.trans hF
  have hF2 : Assemble.fracBitsOf s true 2 = F := f2.trans hF
  simp only [ictCells, SpecCell.ofIrrev]
  refine ⟨⟨rfl, rfl, fun hin => ?_⟩, ⟨rfl, rfl, fun hin => ?_⟩, ⟨rfl, rfl, fun hin => ?_⟩⟩
  · simp only [hF0] at hin ⊢
    obtain ⟨k0, k1, k2⟩ := key hin
    have c := MCT.ict_c8 (pw F) (pw_pos F) v0.toInt v1.toInt v2.toInt x0 x1 x2 _
      (int32_abs v1) (int32_abs v2) k0 k1 k2
    exact ⟨_, o0, by simpa [cellErr] using c.1⟩
  · simp only [hF1] at hin ⊢
    obtain ⟨k0, k1, k2⟩ := key hin
    have c := MCT.ict_c8 (pw F) (pw_pos F) v0.toInt v1.toInt v2.toInt x0 x1 x2 _
      (int32_abs v1) (int32_abs v2) k0 k1 k2
    exact ⟨_, o1, by simpa [cellErr] using c.2.1⟩
  · simp only [hF2] at hin ⊢
    obtain ⟨k0, k1, k2⟩ := key hin
    have c := MCT.ict_c8 (pw F) (pw_pos F) v0.toInt v1.toInt v2.toInt x0 x1 x2 _
      (int32_abs v1) (int32_abs v2) k0 k1 k2
    exact ⟨_, o2, by simpa [cellErr] using c.2.2⟩

/-- A component `≥ 3` of an MCT tile passes the MCT unchanged. -/
private theorem pre_post_cell3 (s : Marker.SIZ) (c : Nat) (hc : 3 ≤ c) (rev : Bool) (v : Int32) (cell : SpecCell)
    (h : PreRel (Assemble.fracBitsOf s true c) rev v cell) : PostRel s true c rev v cell := by
  rw [fb_ge3 s c hc] at h
  obtain ⟨a, b, k⟩ := pre_post_cell s c rev v cell h
  exact ⟨a, by rw [fb_ge3 s c hc]; exact b, k⟩

/-- The three transformed components of the MCT, cell by cell. -/
private theorem mct_out (s : Marker.SIZ) (b : Prop) (rev : Bool)
    (f : Int32 → Int32 → Int32 → Int32 × Int32 × Int32)
    (fc : SpecCell → SpecCell → SpecCell → SpecCell × SpecCell × SpecCell)
    (hcell : ∀ v0 v1 v2 a0 a1 a2, PreRel (Assemble.fracBitsOf s true 0) rev v0 a0 →
      PreRel (Assemble.fracBitsOf s true 1) rev v1 a1 → PreRel (Assemble.fracBitsOf s true 2) rev v2 a2 →
      PostRel s true 0 rev (f v0 v1 v2).1 (fc a0 a1 a2).1 ∧
      PostRel s true 1 rev (f v0 v1 v2).2.1 (fc a0 a1 a2).2.1 ∧
      PostRel s true 2 rev (f v0 v1 v2).2.2 (fc a0 a1 a2).2.2)
    (p0 p1 p2 q0 q1 q2 : Plane) (c0 c1 c2 : CellPlane)
    (w0 : p0.width = c0.width) (h0 : p0.height = c0.height)
    (hd' : c1.width = c0.width ∧ c1.height = c0.height ∧ c2.width = c0.width ∧ c2.height = c0.height)
    (qw0 : q0.width = p0.width) (qh0 : q0.height = p0.height) (qw1 : q1.width = p1.width)
    (qh1 : q1.height = p1.height) (qw2 : q2.width = p2.width) (qh2 : q2.height = p2.height)
    (w1 : p1.width = c1.width) (h1 : p1.height = c1.height) (w2 : p2.width = c2.width) (h2 : p2.height = c2.height)
    (qv : ∀ j, j < p0.width * p0.height → ∃ a b c, p0.get? j = some a ∧ p1.get? j = some b ∧
        p2.get? j = some c ∧ q0.get? j = some (f a b c).1 ∧ q1.get? j = some (f a b c).2.1 ∧
        q2.get? j = some (f a b c).2.2)
    (cellk : ∀ j, j < p0.width * p0.height → b → ∃ a0 a1 a2 : Int32,
        p0.get? j = some a0 ∧ p1.get? j = some a1 ∧ p2.get? j = some a2 ∧
        PreRel (Assemble.fracBitsOf s true 0) rev a0 (c0.cells.getD j default) ∧
        PreRel (Assemble.fracBitsOf s true 1) rev a1 (c1.cells.getD j default) ∧
        PreRel (Assemble.fracBitsOf s true 2) rev a2 (c2.cells.getD j default)) :
    let t := Array.ofFn (n := c0.width * c0.height) fun j =>
      fc (c0.cells.getD j default) (c1.cells.getD j default) (c2.cells.getD j default)
    CellsRel (PostRel s true 0 rev) b q0 c0.width c0.height (t.map (·.1)) ∧
    CellsRel (PostRel s true 1 rev) b q1 c1.width c1.height (t.map (·.2.1)) ∧
    CellsRel (PostRel s true 2 rev) b q2 c2.width c2.height (t.map (·.2.2)) := by
  intro t
  have hN1 : c1.width * c1.height = c0.width * c0.height := by rw [hd'.1, hd'.2.1]
  have hN2 : c2.width * c2.height = c0.width * c0.height := by rw [hd'.2.2.1, hd'.2.2.2]
  have pt : ∀ j, j < c0.width * c0.height → t.getD j default =
      fc (c0.cells.getD j default) (c1.cells.getD j default) (c2.cells.getD j default) := by
    intro j hj; simp [t, Array.getD_eq_getD_getElem?, hj]
  have key : ∀ j, j < c0.width * c0.height → b → ∃ a0 a1 a2 : Int32,
      q0.get? j = some (f a0 a1 a2).1 ∧ q1.get? j = some (f a0 a1 a2).2.1 ∧
      q2.get? j = some (f a0 a1 a2).2.2 ∧
      PostRel s true 0 rev (f a0 a1 a2).1 (t.getD j default).1 ∧
      PostRel s true 1 rev (f a0 a1 a2).2.1 (t.getD j default).2.1 ∧
      PostRel s true 2 rev (f a0 a1 a2).2.2 (t.getD j default).2.2 := by
    intro j hj hb
    have hj0 : j < p0.width * p0.height := by rw [w0, h0]; exact hj
    obtain ⟨a0, a1, a2, g0, g1, g2, r0, r1, r2⟩ := cellk j hj0 hb
    obtain ⟨a, b', c, g0', g1', g2', o0, o1, o2⟩ := qv j hj0
    rw [g0] at g0'; rw [g1] at g1'; rw [g2] at g2'
    cases g0'; cases g1'; cases g2'
    rw [pt j hj]
    exact ⟨_, _, _, o0, o1, o2, hcell _ _ _ _ _ _ r0 r1 r2⟩
  have gm : ∀ (k : SpecCell × SpecCell × SpecCell → SpecCell) j, j < c0.width * c0.height →
      (t.map k).getD j default = k (t.getD j default) := by
    intro k j hj; simp [t, Array.getD_eq_getD_getElem?, hj]
  refine ⟨⟨by rw [qw0, w0], by rw [qh0, h0], by simp [t], fun hb j hj => ?_⟩,
    ⟨by rw [qw1, w1], by rw [qh1, h1], by simp [t, hN1], fun hb j hj => ?_⟩,
    ⟨by rw [qw2, w2], by rw [qh2, h2], by simp [t, hN2], fun hb j hj => ?_⟩⟩
  · obtain ⟨a0, a1, a2, o0, -, -, k0, -, -⟩ := key j hj hb
    exact ⟨_, o0, by rw [gm _ j hj]; exact k0⟩
  · rw [hN1] at hj
    obtain ⟨a0, a1, a2, -, o1, -, -, k1, -⟩ := key j hj hb
    exact ⟨_, o1, by rw [gm _ j hj]; exact k1⟩
  · rw [hN2] at hj
    obtain ⟨a0, a1, a2, -, -, o2, -, -, k2⟩ := key j hj hb
    exact ⟨_, o2, by rw [gm _ j hj]; exact k2⟩

/-- Reading back the set sequence of `mctSpec`. -/
private theorem set3_getD {α : Type} (A : Array α) (z x0 x1 x2 : α) (c : Nat) :
    (((A.setIfInBounds 0 x0).setIfInBounds 1 x1).setIfInBounds 2 x2).getD c z =
      if c < A.size then (if c = 0 then x0 else if c = 1 then x1 else if c = 2 then x2 else A.getD c z)
      else z := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, Array.size_setIfInBounds]
  by_cases h0 : c = 0
  · subst h0; by_cases hs : 0 < A.size <;> simp [hs]
  by_cases h1 : c = 1
  · subst h1; by_cases hs : 1 < A.size <;> simp [hs]
  by_cases h2 : c = 2
  · subst h2; by_cases hs : 2 < A.size <;> simp [hs]
  have a0 : (0 = c) = False := by simp; omega
  have a1 : (1 = c) = False := by simp; omega
  have a2 : (2 = c) = False := by simp; omega
  by_cases hs : c < A.size
  · simp [a0, a1, a2, h0, h1, h2, hs]
  · simp [a0, a1, a2, hs]

/-- **MCT stage of C9 (discharged)**: the fast inverse MCT (`Assemble.inverseMct`, plane loop
`MCT.map3`) and `mctSpec`, given equal transforms on components 0–2. -/
theorem mct_step (s : Marker.SIZ) (g : Progression.Layout) (b : Prop) (ps : Array Plane)
    (cs : Array CellPlane) (h : PreArr s g true b ps cs)
    (ht : ∀ c, c < 3 → revOf g c = revOf g 0) :
    ERel (PostArr s g true b) (Assemble.inverseMct (revOf g 0) ps) (mctSpec (revOf g 0) cs) := by
  obtain ⟨hsz, hr⟩ := h
  obtain ⟨w0, h0, s0, v0⟩ := hr 0
  obtain ⟨w1, h1, s1, v1⟩ := hr 1
  obtain ⟨w2, h2, s2, v2⟩ := hr 2
  unfold Assemble.inverseMct mctSpec
  dsimp only
  generalize ps.getD 0 (Plane.zero 0 0) = p0 at w0 h0 v0 ⊢
  generalize ps.getD 1 (Plane.zero 0 0) = p1 at w1 h1 v1 ⊢
  generalize ps.getD 2 (Plane.zero 0 0) = p2 at w2 h2 v2 ⊢
  generalize cs.getD 0 CellPlane.empty = c0 at w0 h0 s0 v0 ⊢
  generalize cs.getD 1 CellPlane.empty = c1 at w1 h1 s1 v1 ⊢
  generalize cs.getD 2 CellPlane.empty = c2 at w2 h2 s2 v2 ⊢
  by_cases hd : p1.width = p0.width ∧ p1.height = p0.height ∧ p2.width = p0.width ∧ p2.height = p0.height
  · have hd' : c1.width = c0.width ∧ c1.height = c0.height ∧ c2.width = c0.width ∧ c2.height = c0.height := by
      rw [← w0, ← w1, ← w2, ← h0, ← h1, ← h2]; exact hd
    simp only [hd', and_self, ↓reduceIte]
    have r1 := ht 1 (by decide)
    have r2 := ht 2 (by decide)
    -- the cell relation of the three transformed components
    have cellk : ∀ j, j < p0.width * p0.height → b → ∃ a0 a1 a2 : Int32,
        p0.get? j = some a0 ∧ p1.get? j = some a1 ∧ p2.get? j = some a2 ∧
        PreRel (Assemble.fracBitsOf s true 0) (revOf g 0) a0 (c0.cells.getD j default) ∧
        PreRel (Assemble.fracBitsOf s true 1) (revOf g 0) a1 (c1.cells.getD j default) ∧
        PreRel (Assemble.fracBitsOf s true 2) (revOf g 0) a2 (c2.cells.getD j default) := by
      intro j hj hb
      obtain ⟨a0, g0, q0⟩ := v0 hb j (by rw [← w0, ← h0]; exact hj)
      obtain ⟨a1, g1, q1⟩ := v1 hb j (by rw [← w1, ← h1, hd.1, hd.2.1]; exact hj)
      obtain ⟨a2, g2, q2⟩ := v2 hb j (by rw [← w2, ← h2, hd.2.2.1, hd.2.2.2]; exact hj)
      rw [r1] at q1; rw [r2] at q2
      exact ⟨a0, a1, a2, g0, g1, g2, q0, q1, q2⟩
    have post : ∀ (f : Int32 → Int32 → Int32 → Int32 × Int32 × Int32)
        (fc : SpecCell → SpecCell → SpecCell → SpecCell × SpecCell × SpecCell) (q0 q1 q2 : Plane),
        (∀ v0 v1 v2 a0 a1 a2, PreRel (Assemble.fracBitsOf s true 0) (revOf g 0) v0 a0 →
          PreRel (Assemble.fracBitsOf s true 1) (revOf g 0) v1 a1 →
          PreRel (Assemble.fracBitsOf s true 2) (revOf g 0) v2 a2 →
          PostRel s true 0 (revOf g 0) (f v0 v1 v2).1 (fc a0 a1 a2).1 ∧
          PostRel s true 1 (revOf g 0) (f v0 v1 v2).2.1 (fc a0 a1 a2).2.1 ∧
          PostRel s true 2 (revOf g 0) (f v0 v1 v2).2.2 (fc a0 a1 a2).2.2) →
        q0.width = p0.width → q0.height = p0.height → q1.width = p1.width → q1.height = p1.height →
        q2.width = p2.width → q2.height = p2.height →
        (∀ j, j < p0.width * p0.height → ∃ a b c, p0.get? j = some a ∧ p1.get? j = some b ∧
          p2.get? j = some c ∧ q0.get? j = some (f a b c).1 ∧ q1.get? j = some (f a b c).2.1 ∧
          q2.get? j = some (f a b c).2.2) →
        PostArr s g true b
          ((((((ps.setIfInBounds 0 (Plane.zero 0 0)).setIfInBounds 1 (Plane.zero 0 0)).setIfInBounds 2
            (Plane.zero 0 0)).setIfInBounds 0 q0).setIfInBounds 1 q1).setIfInBounds 2 q2)
          (((cs.setIfInBounds 0
            { width := c0.width, height := c0.height, cells := (Array.ofFn (n := c0.width * c0.height) fun j =>
                fc (c0.cells.getD j default) (c1.cells.getD j default) (c2.cells.getD j default)).map (·.1) }).setIfInBounds 1
            { width := c0.width, height := c0.height, cells := (Array.ofFn (n := c0.width * c0.height) fun j =>
                fc (c0.cells.getD j default) (c1.cells.getD j default) (c2.cells.getD j default)).map (·.2.1) }).setIfInBounds 2
            { width := c0.width, height := c0.height, cells := (Array.ofFn (n := c0.width * c0.height) fun j =>
                fc (c0.cells.getD j default) (c1.cells.getD j default) (c2.cells.getD j default)).map (·.2.2) }) := by
      intro f fc q0 q1 q2 hc qw0 qh0 qw1 qh1 qw2 qh2 qv
      obtain ⟨o0, o1, o2⟩ := mct_out s b (revOf g 0) f fc hc p0 p1 p2 q0 q1 q2 c0 c1 c2 w0 h0 hd'
        qw0 qh0 qw1 qh1 qw2 qh2 w1 h1 w2 h2 qv cellk
      refine ⟨by simp [hsz], fun c => ?_⟩
      show CellsRel _ _ _ _ _ _
      rw [set6_getD, set3_getD]
      by_cases hc' : c < ps.size
      · simp only [hc', hsz ▸ hc', ↓reduceIte]
        by_cases e0 : c = 0
        · subst e0; simp only [↓reduceIte]; exact o0
        by_cases e1 : c = 1
        · subst e1; simp only [↓reduceIte]; rw [r1]; rw [hd'.1, hd'.2.1] at o1; exact o1
        by_cases e2 : c = 2
        · subst e2; simp only [↓reduceIte]; rw [r2]; rw [hd'.2.2.1, hd'.2.2.2] at o2; exact o2
        simp only [e0, e1, e2, ↓reduceIte]
        exact CellsRel.mono (hr c) id fun v cell k => pre_post_cell3 s c (by omega) _ v cell k
      · have hc'' : ¬ c < cs.size := hsz ▸ hc'
        simp only [hc', hc'', ↓reduceIte]
        exact CellsRel.zero _ _
    cases hrv : revOf g 0
    · simp only [Bool.false_eq_true, ↓reduceIte]
      obtain ⟨q0, q1, q2, hq, qw0, qh0, qw1, qh1, qw2, qh2, qv⟩ := apply3_ok MCT.ictSample p0 p1 p2 hd
      rw [show MCT.ictInverse p0 p1 p2 = .ok (q0, q1, q2) from hq, ok_bind]
      apply ERel.pure
      have := post MCT.ictSample ictCells q0 q1 q2 (by rw [hrv]; exact ict_cell s) qw0 qh0 qw1 qh1 qw2 qh2 qv
      exact this
    · simp only [↓reduceIte]
      obtain ⟨q0, q1, q2, hq, qw0, qh0, qw1, qh1, qw2, qh2, qv⟩ := apply3_ok MCT.rctSample p0 p1 p2 hd
      rw [show MCT.rctInverse p0 p1 p2 = .ok (q0, q1, q2) from hq, ok_bind]
      apply ERel.pure
      have := post MCT.rctSample rctCells q0 q1 q2 (by rw [hrv]; exact rct_cell s) qw0 qh0 qw1 qh1 qw2 qh2 qv
      exact this
  · have hd' : ¬ (c1.width = c0.width ∧ c1.height = c0.height ∧ c2.width = c0.width ∧ c2.height = c0.height) := by
      rw [← w0, ← w1, ← w2, ← h0, ← h1, ← h2]; exact hd
    have e1 : MCT.rctInverse p0 p1 p2 = .error (.malformed MCT.loc
        s!"component transform on planes {p0.width}×{p0.height}, {p1.width}×{p1.height}, {p2.width}×{p2.height}") := by
      unfold MCT.rctInverse MCT.apply3; simp only [hd, ↓reduceDIte]
    have e2 : MCT.ictInverse p0 p1 p2 = .error (.malformed MCT.loc
        s!"component transform on planes {p0.width}×{p0.height}, {p1.width}×{p1.height}, {p2.width}×{p2.height}") := by
      unfold MCT.ictInverse MCT.apply3; simp only [hd, ↓reduceDIte]
    simp only [hd', ↓reduceIte]
    cases revOf g 0 <;> simp only [Bool.false_eq_true, ↓reduceIte, e1, e2] <;> trivial

/-- `DcShift.make` fails only with `unsupported`. -/
private theorem make_unsupported (signed : Bool) (depth F : Nat) (e : Error)
    (h : MCT.DcShift.make signed depth F = .error e) : Unsupported e := by
  unfold MCT.DcShift.make at h
  dsimp only at h
  split at h
  · simp at h
  · simp only [Except.error.injEq] at h; subst h; trivial

/-- `DcShift.make` records its arguments. -/
private theorem make_fields (signed : Bool) (depth F : Nat) (p : MCT.DcShift)
    (h : MCT.DcShift.make signed depth F = .ok p) : p.signed = signed ∧ p.depth = depth ∧ p.F = F := by
  unfold MCT.DcShift.make at h
  dsimp only at h
  split at h
  · simp only [Except.ok.injEq] at h; subst h; exact ⟨rfl, rfl, rfl⟩
  · simp at h

/-- A component range that fits `Int32` has at most 32 bits. -/
private theorem depth_le (signed : Bool) (depth : Nat) (_h1 : 1 ≤ depth)
    (h : Spec.MCT.sampleMax signed depth ≤ 2147483647) : depth ≤ 32 := by
  apply Nat.le_of_not_lt
  intro hc
  have a1 : (2 : Nat) ^ 32 ≤ 2 ^ (depth - 1) := Nat.pow_le_pow_right (by decide) (by omega)
  have a2 : (2 : Nat) ^ (depth - 1) ≤ 2 ^ depth := Nat.pow_le_pow_right (by decide) (by omega)
  have b1 : ((2 : Int) ^ (depth - 1)) = ((2 ^ (depth - 1) : Nat) : Int) := by push_cast; rfl
  have b2 : ((2 : Int) ^ depth) = ((2 ^ depth : Nat) : Int) := by push_cast; rfl
  unfold Spec.MCT.sampleMax at h
  cases signed <;> simp only [Bool.false_eq_true, ↓reduceIte] at h <;> omega

/-- Saturating an integer to `Int32` before the reversible DC shift and clamp changes nothing. -/
private theorem reconRev_clamp32 (signed : Bool) (depth : Nat) (h1 : 1 ≤ depth) (h2 : depth ≤ 32) (w : Int) :
    Spec.MCT.reconRev signed depth (MCT.clamp32 w) = Spec.MCT.reconRev signed depth w := by
  have := MCT.reconIrrev_sat signed depth 0 h1 (by omega) w
  simpa [Spec.MCT.reconIrrev, Spec.MCT.roundFix] using this

/-- `roundHalf x` is within `1/2` of `x`. -/
private theorem roundHalf_err (x : Rat) : ((roundHalf x : Rat) - x).abs ≤ 1 / 2 := by
  have a := Rat.floor_le (x + 1 / 2)
  have b := Rat.lt_floor_add_one (x + 1 / 2)
  unfold roundHalf
  apply Spec.DWT97.abs_le_iff.mpr
  push_cast at b
  constructor <;> grind

/-- A clamp moves two values by amounts between 0 and their difference. -/
private theorem clamp_between (lo hi a b : Int) (h : lo ≤ hi) :
    (0 ≤ Spec.MCT.clamp lo hi a - Spec.MCT.clamp lo hi b ∧
      Spec.MCT.clamp lo hi a - Spec.MCT.clamp lo hi b ≤ a - b) ∨
    (a - b ≤ Spec.MCT.clamp lo hi a - Spec.MCT.clamp lo hi b ∧
      Spec.MCT.clamp lo hi a - Spec.MCT.clamp lo hi b ≤ 0) := by
  unfold Spec.MCT.clamp
  repeat' split
  all_goals omega

/-- The DC shift and clamp do not increase distances. -/
private theorem recon_close (signed : Bool) (depth : Nat) (h1 : 1 ≤ depth) (a b : Int) (r : Rat)
    (h : ((a : Rat) - b).abs ≤ r) :
    ((Spec.MCT.reconRev signed depth a : Rat) - Spec.MCT.reconRev signed depth b).abs ≤ r := by
  have hlh := Spec.MCT.sampleMin_le_max signed depth h1
  have hc := clamp_between (Spec.MCT.sampleMin signed depth) (Spec.MCT.sampleMax signed depth)
    (a + Spec.MCT.dcOffset signed depth) (b + Spec.MCT.dcOffset signed depth) hlh
  unfold Spec.MCT.reconRev
  generalize Spec.MCT.clamp (Spec.MCT.sampleMin signed depth) (Spec.MCT.sampleMax signed depth)
    (a + Spec.MCT.dcOffset signed depth) = p at hc ⊢
  generalize Spec.MCT.clamp (Spec.MCT.sampleMin signed depth) (Spec.MCT.sampleMax signed depth)
    (b + Spec.MCT.dcOffset signed depth) = q at hc ⊢
  have hab := Spec.DWT97.abs_le_iff.mp h
  apply Spec.DWT97.abs_le_iff.mpr
  have e : (p : Rat) - q = ((p - q : Int) : Rat) := by push_cast; rfl
  have e2 : (a : Rat) - b = ((a - b : Int) : Rat) := by push_cast; rfl
  rw [e]; rw [e2] at hab
  rcases hc with ⟨c1, c2⟩ | ⟨c1, c2⟩
  · have d1 : ((0 : Int) : Rat) ≤ ((p - q : Int) : Rat) := Rat.intCast_le_intCast.mpr c1
    have d2 : ((p - q : Int) : Rat) ≤ ((a - b : Int) : Rat) := Rat.intCast_le_intCast.mpr (by omega)
    constructor <;> grind
  · have d1 : ((a - b : Int) : Rat) ≤ ((p - q : Int) : Rat) := Rat.intCast_le_intCast.mpr (by omega)
    have d2 : ((p - q : Int) : Rat) ≤ ((0 : Int) : Rat) := Rat.intCast_le_intCast.mpr (by omega)
    constructor <;> grind

/-- The irreversible output sample is within `e + 1` of the spec sample when the fixed-point
value `w / 2^F` is within `e` of the exact value `x`. -/
theorem irrev_sample (signed : Bool) (depth F : Nat) (h1 : 1 ≤ depth) (w : Int) (x e : Rat)
    (h : ((w : Rat) / pw F - x).abs ≤ e) :
    ((Spec.MCT.reconIrrev signed depth F w : Rat) - Spec.MCT.reconRev signed depth (roundHalf x)).abs
      ≤ e + 1 := by
  unfold Spec.MCT.reconIrrev
  apply recon_close signed depth h1
  have r1 := Spec.MCT.roundFix_err F w
  have r2 := roundHalf_err x
  have t1 := Spec.DWT97.abs_add_le ((Spec.MCT.roundFix F w : Rat) - (w : Rat) / pw F) ((w : Rat) / pw F - x)
  have t2 := Spec.DWT97.abs_add_le (((Spec.MCT.roundFix F w : Rat) - (w : Rat) / pw F) + ((w : Rat) / pw F - x))
    (x - roundHalf x)
  have e1 : (x - (roundHalf x : Rat)).abs = ((roundHalf x : Rat) - x).abs := Rat.abs_sub_comm
  have e2 : ((Spec.MCT.roundFix F w : Rat) - (w : Rat) / pw F) + ((w : Rat) / pw F - x) + (x - roundHalf x)
      = (Spec.MCT.roundFix F w : Rat) - roundHalf x := by grind
  rw [e2] at t2
  unfold pw at h t1 t2 e2
  grind

/-- `MCT.map1` keeps the plane's dimensions. -/
private theorem map1_dims {N : Nat} (f : Int32 → Int32) (b : DWT53.Buf N) (i : Nat) :
    (MCT.map1 f b i).1.width = b.1.width ∧ (MCT.map1 f b i).1.height = b.1.height := by
  unfold MCT.map1
  split
  · have := map1_dims f (b.set i (f (b.get i (by assumption))) (by assumption)) (i + 1)
    exact ⟨this.1.trans rfl, this.2.trans rfl⟩
  · exact ⟨rfl, rfl⟩
termination_by N - i

/-- `MCT.map1` applies the kernel cell by cell. -/
private theorem map1_get? (f : Int32 → Int32) (pl : Plane) (j : Nat) (hj : j < pl.width * pl.height) :
    (MCT.map1 f (N := pl.width * pl.height) ⟨pl, rfl⟩ 0).1.get? j = (pl.get? j).map f := by
  have hd := map1_dims f (N := pl.width * pl.height) ⟨pl, rfl⟩ 0
  have hg := MCT.map1_get f (N := pl.width * pl.height) ⟨pl, rfl⟩ 0 j hj
  simp only [Nat.not_lt_zero, ↓reduceIte] at hg
  have hj' : j < (MCT.map1 f (N := pl.width * pl.height) ⟨pl, rfl⟩ 0).1.width *
      (MCT.map1 f (N := pl.width * pl.height) ⟨pl, rfl⟩ 0).1.height := by rw [hd.1, hd.2]; exact hj
  simp only [Plane.get?, hj, hj', ↓reduceDIte, Option.map_some]
  exact congrArg some hg

/-- `F + depth ≤ 32` for the fractional bits of every component of at most 32 bits. -/
private theorem fracBits_depth (s : Marker.SIZ) (m : Bool) (c : Nat)
    (hd : (s.components.getD c default).depth.toNat ≤ 32) :
    Assemble.fracBitsOf s m c + (s.components.getD c default).depth.toNat ≤ 32 := by
  unfold Assemble.fracBitsOf DWT97.fracBits
  dsimp only
  split
  · rename_i hc
    have : c = 0 ∨ c = 1 ∨ c = 2 := by omega
    rcases this with rfl | rfl | rfl <;> omega
  · omega

/-- **DC shift and clamp stage of C9 (discharged)** (G.1): `MCT.dcShiftClampRev` /
`dcShiftClampIrrev` (`DcShift.rev_eq`, `irrev_eq`) vs `SpecCell.toSample`. -/
theorem dc_step (h : Header) (g : Progression.Layout) (mct : Bool) (b : Prop) (c : Nat) (pl : Plane)
    (cp : CellPlane) (hr : CellsRel (PostRel h.siz mct c (revOf g c)) b pl cp.width cp.height cp.cells) :
    ERel (fun dc sd => CellsRel (SampleRel h c) b
        (if revOf g c = true then MCT.dcShiftClampRev dc pl else MCT.dcShiftClampIrrev dc pl)
        (dcSpec sd (revOf g c) cp).width (dcSpec sd (revOf g c) cp).height (dcSpec sd (revOf g c) cp).samples)
      (MCT.DcShift.make (h.siz.components.getD c default).signed (h.siz.components.getD c default).depth.toNat
        (if revOf g c = true then 0 else Assemble.fracBitsOf h.siz mct c))
      (pure ((h.siz.components.getD c default).signed, (h.siz.components.getD c default).depth.toNat)) := by
  cases hmk : MCT.DcShift.make (h.siz.components.getD c default).signed
      (h.siz.components.getD c default).depth.toNat
      (if revOf g c = true then 0 else Assemble.fracBitsOf h.siz mct c) with
  | error e => exact make_unsupported _ _ _ e hmk
  | ok dc =>
  have hwf := MCT.DcShift.make_wf _ _ _ dc hmk
  obtain ⟨hs, hd, hF⟩ := make_fields _ _ _ dc hmk
  obtain ⟨_, _, hhi, _, _, _, hd1, _, hhb, _⟩ := hwf
  have hd32 : dc.depth ≤ 32 := depth_le dc.signed dc.depth hd1 (by rw [← hhi]; exact hhb)
  show CellsRel _ _ _ _ _ _
  obtain ⟨hw, hh, hsz, hv⟩ := hr
  generalize hsg : (h.siz.components.getD c default).signed = sg at hs hmk ⊢
  generalize hdp : (h.siz.components.getD c default).depth.toNat = dp at hd hmk ⊢
  subst hs hd
  cases hrev : revOf g c
  · -- irreversible
    simp only [hrev, Bool.false_eq_true, ↓reduceIte] at hF hv ⊢
    refine ⟨by simp only [MCT.dcShiftClampIrrev, dcSpec]; rw [(map1_dims _ _ _).1]; exact hw,
      by simp only [MCT.dcShiftClampIrrev, dcSpec]; rw [(map1_dims _ _ _).2]; exact hh,
      by simp [dcSpec, hsz], fun hb j hj => ?_⟩
    have hj' : j < pl.width * pl.height := by rw [hw, hh]; exact hj
    obtain ⟨v, hgv, hpr⟩ := hv hb j hj
    refine ⟨dc.irrev v, ?_, ?_⟩
    · simp only [MCT.dcShiftClampIrrev]; rw [map1_get? _ _ _ hj', hgv]; rfl
    · have hcell : (dcSpec (dc.signed, dc.depth) false cp).samples.getD j default =
          (cp.cells.getD j default).toSample dc.signed dc.depth false := by
        simp [dcSpec, Array.getD_eq_getD_getElem?, hsz ▸ hj]
      rw [hcell]
      obtain ⟨hcr, hFe, himp⟩ := hpr
      generalize cp.cells.getD j default = cell at hcr hFe himp ⊢
      intro hin
      simp only [SpecCell.toSample, Bool.false_eq_true, ↓reduceIte] at hin ⊢
      rw [hcr] at himp
      obtain ⟨w, hvw, hwx⟩ := himp hin
      simp only [Bool.false_eq_true, ↓reduceIte] at hwx
      rw [MCT.DcShift.irrev_eq dc (MCT.DcShift.make_wf _ _ _ dc hmk), hvw, hF, hFe]
      have hFd : Assemble.fracBitsOf h.siz cell.mct c + dc.depth ≤ 32 := by
        rw [← hdp]; exact fracBits_depth _ _ _ (hdp ▸ hd32)
      rw [MCT.reconIrrev_sat _ _ _ hd1 hFd]
      exact irrev_sample _ _ _ hd1 w cell.rval _ hwx
  · -- reversible
    simp only [hrev, ↓reduceIte] at hF hv ⊢
    refine ⟨by simp only [MCT.dcShiftClampRev, dcSpec]; rw [(map1_dims _ _ _).1]; exact hw,
      by simp only [MCT.dcShiftClampRev, dcSpec]; rw [(map1_dims _ _ _).2]; exact hh,
      by simp [dcSpec, hsz], fun hb j hj => ?_⟩
    have hj' : j < pl.width * pl.height := by rw [hw, hh]; exact hj
    obtain ⟨v, hgv, hpr⟩ := hv hb j hj
    refine ⟨dc.rev v, ?_, ?_⟩
    · simp only [MCT.dcShiftClampRev]; rw [map1_get? _ _ _ hj', hgv]; rfl
    · have hcell : (dcSpec (dc.signed, dc.depth) true cp).samples.getD j default =
          (cp.cells.getD j default).toSample dc.signed dc.depth true := by
        simp [dcSpec, Array.getD_eq_getD_getElem?, hsz ▸ hj]
      rw [hcell]
      obtain ⟨hcr, -, himp⟩ := hpr
      generalize cp.cells.getD j default = cell at hcr himp ⊢
      intro hin
      simp only [SpecCell.toSample, ↓reduceIte] at hin ⊢
      rw [hcr] at himp
      obtain ⟨w, hvw, hwx⟩ := himp hin
      simp only [↓reduceIte] at hwx
      rw [MCT.DcShift.rev_eq dc (MCT.DcShift.make_wf _ _ _ dc hmk), hvw, reconRev_clamp32 _ _ hd1 hd32, hwx]

/-- The Tier-2 results of a tile, fast and spec: both absent, or the spec one's components the
image of the fast one (`Spec.Tier2Equiv.image`). -/
def T2Img (data : ByteArray) : Option TileCodeBlocks → Option Spec.Tier2.TileOut → Prop
  | none, none => True
  | some x, some s => s.comps = image data x
  | _, _ => False

/-- **Tile level of C9**: per tile-component reconstruction, MCT and DC shift composed (`TileRel`).
-/
theorem tile_rel (hT1 : Tier1Equiv) (hQ : DequantLoopEquiv) (h53 : DWT53PlaneEquiv)
    (h97 : DWT97PlaneErr) (L : Limits) (h : Header) (data : ByteArray) (t reduce : Nat)
    (tcb : Option TileCodeBlocks) (stcb : Option Spec.Tier2.TileOut) (hT : T2Img data tcb stcb)
    (hH : ∀ g coding, Progression.Layout.ofHeader h t = .ok (g, coding) →
      (∀ c, ParamsWF (g.comp c)) ∧
      (coding.mctApplies h.siz → ∀ c, c < 3 → (g.comp c).params.transform = (g.comp 0).params.transform))
    (hW : ∀ x, tcb = some x → (∀ g coding, Progression.Layout.ofHeader h t = .ok (g, coding) →
      ∀ c, PrecsWF (g.comp c) (x.comps.getD c #[])) ∧ ∀ c, BlocksIn data (x.comps.getD c #[])) :
    ERel (TileRel h) (Assemble.decodeTile L h data t reduce tcb) (Decode.decodeTile L h t reduce stcb) := by
  rw [decodeTile_eq_with]
  unfold Decode.decodeTile tileWith
  cases hl : Progression.Layout.ofHeader h t with
  | error e => trivial
  | ok gc =>
  obtain ⟨g, coding⟩ := gc
  obtain ⟨hP, hM⟩ := hH g coding hl
  rw [ok_bind, ok_bind]
  apply ERel.bind_same
  intro u
  -- first loop: tile-components
  refine ERel.bind (R := fun (a : Array Plane × Nat) (b : Array CellPlane × Nat) =>
    a.1.size = g.numComps ∧ PreArr h.siz g (Coding.mctApplies h.siz coding) (a.2 = 0) a.1 b.1) ?_ ?_
  · apply ERel.forIn_range_idx (fun i (a : Array Plane × Nat) (b : Array CellPlane × Nat) =>
      a.1.size = i ∧ PreArr h.siz g (Coding.mctApplies h.siz coding) (a.2 = 0) a.1 b.1)
    · intro c a b ⟨hsz, hab⟩
      refine ERel.bind (R := TCRel (Assemble.fracBitsOf h.siz (Coding.mctApplies h.siz coding) c)
        ((g.comp c).params.transform == .reversible53)) ?_ ?_
      · rcases tcb with _ | x <;> rcases stcb with _ | sx <;> simp only [T2Img] at hT
        · exact tileComp_rel hT1 hQ h53 h97 L data (g.comp c) _ _ reduce #[] (hP c)
            (fun r hr => by simp at hr) (fun r prec hp => by simp at hp)
        · obtain ⟨hW1, hW2⟩ := hW x rfl
          dsimp only
          rw [hT, image_getD]
          exact tileComp_rel hT1 hQ h53 h97 L data (g.comp c) _ _ reduce _ (hP c) (hW1 g coding hl c) (hW2 c)
      · intro x y hxy
        apply ERel.pure
        refine ⟨by simp [hsz], ?_⟩
        rw [← hsz] at hxy
        refine ArrRel.push ?_ ?_
        · exact ArrRel.mono hab fun c' a' b' hr => CellsRel.mono hr (fun e => by omega) fun _ _ k => k
        · exact CellsRel.mono hxy (fun e => by omega) fun _ _ k => k
    · exact ⟨rfl, rfl, fun c => CellsRel.zero _ _⟩
  · intro a b ⟨hsz, hab⟩
    -- second loop: DC shift (both branches of the MCT)
    have loop2 : ∀ (p0 : Array Plane) (c0 : Array CellPlane),
        PostArr h.siz g (Coding.mctApplies h.siz coding) (a.2 = 0) p0 c0 →
        ERel (TileRel h)
          (do
            let r ← forIn [0:g.numComps] (p0, (#[] : Array (Rect × Plane))) fun c (s : Array Plane × Array (Rect × Plane)) => do
              let dc ← MCT.DcShift.make (h.siz.components.getD c default).signed
                (h.siz.components.getD c default).depth.toNat
                (if ((g.comp c).params.transform == Marker.Transform.reversible53) = true then 0
                  else Assemble.fracBitsOf h.siz (Coding.mctApplies h.siz coding) c)
              pure (ForInStep.yield (s.1.setIfInBounds c (Plane.zero 0 0),
                s.2.push (Assemble.reduceRect (g.comp c).rect reduce,
                  if ((g.comp c).params.transform == Marker.Transform.reversible53) = true then
                    MCT.dcShiftClampRev dc (s.1.getD c (Plane.zero 0 0))
                  else MCT.dcShiftClampIrrev dc (s.1.getD c (Plane.zero 0 0)))))
            pure ({ tile := t, comps := r.2, saturated := a.2 } : Assemble.TileOut))
          (do
            let r ← forIn [0:g.numComps] (c0, (#[] : Array (Rect × SamplePlane))) fun c (s : Array CellPlane × Array (Rect × SamplePlane)) => do
              let dc ← pure ((h.siz.components.getD c default).signed,
                (h.siz.components.getD c default).depth.toNat)
              pure (ForInStep.yield (s.1.setIfInBounds c CellPlane.empty,
                s.2.push (Assemble.reduceRect (g.comp c).rect reduce,
                  dcSpec dc ((g.comp c).params.transform == Marker.Transform.reversible53)
                    (s.1.getD c CellPlane.empty))))
            pure ({ tile := t, comps := r.2 } : Decode.TileOut)) := by
      intro p0 c0 h0
      refine ERel.bind (R := fun (a' : Array Plane × Array (Rect × Plane))
          (b' : Array CellPlane × Array (Rect × SamplePlane)) => OutRel h (a.2 = 0) a'.2 b'.2) ?_ ?_
      · refine (ERel.forIn_range_idx (fun i (a' : Array Plane × Array (Rect × Plane))
            (b' : Array CellPlane × Array (Rect × SamplePlane)) =>
            a'.2.size = i ∧ PostArr h.siz g (Coding.mctApplies h.siz coding) (a.2 = 0) a'.1 b'.1 ∧
              OutRel h (a.2 = 0) a'.2 b'.2) _ _ _ ?_ _ _ ?_).mono (fun _ _ k => k.2.2)
        · intro c a' b' ⟨hsz', hpa, hout⟩
          apply ERel.bind (dc_step h g _ _ c _ _ (hpa.2 c))
          intro dc sd hds
          apply ERel.pure
          refine ⟨by simp [hsz'], ?_, ?_⟩
          · exact ArrRel.set hpa (fun c => CellsRel.zero _ _) c
          · rw [← hsz'] at hds ⊢
            exact ArrRel.push hout ⟨rfl, hds⟩
        · exact ⟨rfl, h0, ⟨rfl, fun c => ⟨rfl, CellsRel.zero _ _⟩⟩⟩
      · intro a' b' hab'
        exact ⟨rfl, hab'⟩
    by_cases hm : Coding.mctApplies h.siz coding = true
    · simp only [hm, ↓reduceIte]
      have ht : ∀ c, c < 3 → revOf g c = revOf g 0 := by
        intro c hc; simp only [revOf, hM hm c hc]
      rw [hm] at hab
      refine ERel.bind (mct_step h.siz g _ a.1 b.1 hab ht) ?_
      intro x y hxy
      rw [← hm] at hxy
      have := loop2 x y hxy
      simp only [hm] at this
      exact this
    · have hm' : Coding.mctApplies h.siz coding = false := by simpa using hm
      have := loop2 a.1 b.1 (pre_post _ _ _ _ _ _ hab hm')
      simp only [hm'] at this ⊢
      exact this

/-- Fast component planes vs spec sample planes (`CellsRel` per component). -/
def PlaneArr (R : Nat → Int32 → SpecSample → Prop) (b : Prop) : Array Plane → Array SamplePlane → Prop :=
  ArrRel (fun c p sp => CellsRel (R c) b p sp.width sp.height sp.samples) (Plane.zero 0 0) default

/-- Two arrays of sample planes of the same sizes. -/
def SameDims (ss ss' : Array SamplePlane) : Prop :=
  ss'.size = ss.size ∧ ∀ c, (ss'.getD c default).width = (ss.getD c default).width ∧
    (ss'.getD c default).height = (ss.getD c default).height

/-- **Stage: placement of tiles into the component planes** (`Decode.place` / `Assemble.blit` vs
`Spec.Decode.place`), for any sample relation. Discharged: `placeEquiv`. -/
def PlaceEquiv : Prop :=
  ∀ (R : Nat → Int32 → SpecSample → Prop) (b : Prop) (info : Array DecodedComponent)
    (ps : Array Plane) (ss : Array SamplePlane) (o : Assemble.TileOut) (s : Decode.TileOut),
    PlaneArr R b ps ss → o.tile = s.tile →
    ArrRel (fun c a sp => a.1 = sp.1 ∧ CellsRel (R c) b a.2 sp.2.width sp.2.height sp.2.samples)
      (default, Plane.zero 0 0) default o.comps s.comps →
    ERel (fun ps' ss' => PlaneArr R b ps' ss' ∧ SameDims ss ss')
      (JPEG2000.Decode.place info ps o) (Decode.place info ss s)

/-- **The C9 relation between `decodeCodestreamNarrow` and `Spec.decode` results**: same header and
component count; per component the same geometry, depth and signedness; the fast plane has the
component's size; and when the decoder reports no saturated code-block, every sample satisfies
`SampleRel` (reversible: equal; irreversible: within C8's bound), under the numeric-range
precondition `InRangeT`. -/
def C9Rel (img : DecodedImage) (si : SpecImage) : Prop :=
  img.header = si.header ∧ img.comps.size = si.comps.size ∧
  ∀ c, c < img.comps.size →
    (si.comps.getD c default).info.x0 = (img.comps.getD c default).x0 ∧
    (si.comps.getD c default).info.y0 = (img.comps.getD c default).y0 ∧
    (si.comps.getD c default).info.width = (img.comps.getD c default).width ∧
    (si.comps.getD c default).info.height = (img.comps.getD c default).height ∧
    (si.comps.getD c default).info.depth = (img.comps.getD c default).depth ∧
    (si.comps.getD c default).info.signed = (img.comps.getD c default).signed ∧
    (si.comps.getD c default).info.dx = (img.comps.getD c default).dx ∧
    (si.comps.getD c default).info.dy = (img.comps.getD c default).dy ∧
    CellsRel (SampleRel img.header c) (img.saturatedBlocks = 0) (img.comps.getD c default).plane
      (img.comps.getD c default).width (img.comps.getD c default).height
      (si.comps.getD c default).samples

/-- Weaken the condition of a `PlaneArr`. -/
theorem PlaneArr.weaken {R : Nat → Int32 → SpecSample → Prop} {b b' : Prop} {ps : Array Plane}
    {ss : Array SamplePlane} (h : PlaneArr R b ps ss) (hb : b' → b) : PlaneArr R b' ps ss :=
  ArrRel.mono h fun _ _ _ k => CellsRel.mono k hb fun _ _ x => x

/-- `SameDims` is transitive. -/
theorem SameDims.trans {a b c : Array SamplePlane} (h1 : SameDims a b) (h2 : SameDims b c) :
    SameDims a c :=
  ⟨h2.1.trans h1.1, fun i => ⟨(h2.2 i).1.trans (h1.2 i).1, (h2.2 i).2.trans (h1.2 i).2⟩⟩

/-- `SameDims` is reflexive. -/
theorem SameDims.refl (a : Array SamplePlane) : SameDims a a := ⟨rfl, fun _ => ⟨rfl, rfl⟩⟩

/-- `Decode.allocOutput` returns zero planes of the components' sizes. -/
private theorem alloc_facts (L : Limits) (s : Marker.SIZ) (reduce : Nat) (info : Array DecodedComponent)
    (ps : Array Plane) (h : JPEG2000.Decode.allocOutput L s reduce = .ok (info, ps)) :
    info.size = ps.size ∧ ∀ c, c < ps.size →
      (ps.getD c (Plane.zero 0 0)).width = (info.getD c default).width ∧
      (ps.getD c (Plane.zero 0 0)).height = (info.getD c default).height ∧
      ∀ j, j < (ps.getD c (Plane.zero 0 0)).width * (ps.getD c (Plane.zero 0 0)).height →
        (ps.getD c (Plane.zero 0 0)).get? j = some 0 := by
  unfold JPEG2000.Decode.allocOutput at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · contradiction
  split at h
  · contradiction
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨by simp, fun c hc => ?_⟩
  simp only [Array.size_map] at hc
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_eq_getElem hc,
    Option.map_some, Option.getD_some]
  refine ⟨rfl, rfl, fun j hj => ?_⟩
  simp only [Plane.get?, hj, ↓reduceDIte, Plane.get_zero]

/-- The initial planes are related (zero vs `SpecSample.blank`). -/
private theorem initPlanes_rel (h : Header) (b : Prop) (ps : Array Plane)
    (hz : ∀ c, c < ps.size → ∀ j, j < (ps.getD c (Plane.zero 0 0)).width * (ps.getD c (Plane.zero 0 0)).height →
        (ps.getD c (Plane.zero 0 0)).get? j = some 0) :
    PlaneArr (SampleRel h) b ps (initPlanes ps) := by
  refine ⟨by simp [initPlanes], fun c => ?_⟩
  by_cases hc : c < ps.size
  · have e : (initPlanes ps).getD c default =
        { width := (ps.getD c (Plane.zero 0 0)).width, height := (ps.getD c (Plane.zero 0 0)).height,
          samples := Array.replicate ((ps.getD c (Plane.zero 0 0)).width * (ps.getD c (Plane.zero 0 0)).height)
            SpecSample.blank } := by
      simp [initPlanes, Array.getD_eq_getD_getElem?, hc]
    rw [e]
    have hz' := hz c hc
    generalize ps.getD c (Plane.zero 0 0) = P at hz' ⊢
    refine ⟨rfl, rfl, by simp, fun _ j hj => ⟨0, hz' j hj, ?_⟩⟩
    have hb : (Array.replicate (P.width * P.height) SpecSample.blank).getD j default = SpecSample.blank := by
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
      simp only at hj
      simp [hj]
    rw [hb]
    intro _
    simp [SpecSample.blank]
  · have e1 : ps.getD c (Plane.zero 0 0) = Plane.zero 0 0 := by
      simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (Nat.le_of_not_lt hc)]
    have e2 : (initPlanes ps).getD c default = default := by
      simp [Array.getD_eq_getD_getElem?, initPlanes, Array.getElem?_eq_none (Nat.le_of_not_lt hc)]
    rw [e1, e2]
    exact ⟨rfl, rfl, rfl, fun _ j hj => absurd (show j < 0 from hj) (Nat.not_lt_zero _)⟩

/-- Writing related values at one index keeps `CellsRel`. -/
private theorem cells_set (R : Int32 → SpecSample → Prop) (b : Prop) (p : Plane) (w h : Nat)
    (a : Array SpecSample) (hr : CellsRel R b p w h a) (i : Nat) (hi : i < p.width * p.height)
    (v : Int32) (x : SpecSample) (hvx : b → R v x) :
    CellsRel R b (p.set i v hi) w h (a.setIfInBounds i x) := by
  obtain ⟨hw, hh, hs, hv⟩ := hr
  refine ⟨hw, hh, by simp [hs], fun hb j hj => ?_⟩
  have hj' : j < (p.set i v hi).width * (p.set i v hi).height := by
    show j < p.width * p.height; rw [hw, hh]; exact hj
  rw [plane_get?_of _ j hj']
  by_cases e : i = j
  · subst e
    refine ⟨v, by rw [Plane.get_set_self], ?_⟩
    have : (a.setIfInBounds i x).getD i default = x := by
      simp [Array.getD_eq_getD_getElem?, hs ▸ hj]
    rw [this]; exact hvx hb
  · obtain ⟨u, hu, hru⟩ := hv hb j hj
    refine ⟨u, ?_, ?_⟩
    · rw [Plane.get_set_ne _ _ _ _ _ _ e]
      rw [plane_get?_of _ j (by rw [hw, hh]; exact hj)] at hu; exact hu
    · have : (a.setIfInBounds i x).getD j default = a.getD j default := by
        simp [Array.getD_eq_getD_getElem?, e]
      rw [this]; exact hru

/-- `Assemble.blitRow` and `Spec.Decode.blitRow` keep `CellsRel`. -/
private theorem blitRow_rel (R : Int32 → SpecSample → Prop) (b : Prop) (src : Plane) (ssp : SamplePlane)
    (hs : CellsRel R b src ssp.width ssp.height ssp.samples) :
    ∀ k si di (dst : Plane) (w h : Nat) (ds : Array SpecSample), CellsRel R b dst w h ds →
      CellsRel R b (Assemble.blitRow src k si di dst) w h (Decode.blitRow ssp k si di ds) := by
  intro k
  induction k with
  | zero => intro si di dst w h ds hd; exact hd
  | succ k ih =>
    intro si di dst w h ds hd
    simp only [Assemble.blitRow, Decode.blitRow]
    apply ih
    obtain ⟨sw, sh, ss, sv⟩ := hs
    by_cases h1 : si < src.width * src.height
    · have h1' : si < ssp.samples.size := by rw [ss, ← sw, ← sh]; exact h1
      rw [Array.getElem?_eq_getElem h1']
      simp only [h1, ↓reduceDIte]
      by_cases h2 : di < dst.width * dst.height
      · simp only [h2, ↓reduceDIte]
        apply cells_set R b dst w h ds hd di h2
        intro hb
        obtain ⟨u, hu, hru⟩ := sv hb si (by rw [← sw, ← sh]; exact h1)
        rw [plane_get?_of _ si h1] at hu
        cases hu
        have : ssp.samples.getD si default = ssp.samples[si] := by
          simp [Array.getD_eq_getD_getElem?, h1']
        rw [this] at hru; exact hru
      · simp only [h2, ↓reduceDIte]
        have h2' : ¬ di < ds.size := by rw [hd.2.2.1, ← hd.1, ← hd.2.1]; exact h2
        obtain ⟨a1, a2, a3, a4⟩ := hd
        refine ⟨a1, a2, by simp [a3], fun hb j hj => ?_⟩
        obtain ⟨u, hu, hru⟩ := a4 hb j hj
        refine ⟨u, hu, ?_⟩
        have e : di ≠ j := by intro e; subst e; exact h2' (by rw [a3]; exact hj)
        simpa [Array.getD_eq_getD_getElem?, e] using hru
    · have h1' : ¬ si < ssp.samples.size := by rw [ss, ← sw, ← sh]; exact h1
      rw [Array.getElem?_eq_none (Nat.le_of_not_lt h1')]
      simp only [h1, ↓reduceDIte]
      exact hd

/-- `Assemble.blitRows` and `Spec.Decode.blitRows` keep `CellsRel`. -/
private theorem blitRows_rel (R : Int32 → SpecSample → Prop) (b : Prop) (src : Plane) (ssp : SamplePlane)
    (hs : CellsRel R b src ssp.width ssp.height ssp.samples) (ox oy : Nat) :
    ∀ k y (dst : Plane) (w h : Nat) (ds : Array SpecSample), CellsRel R b dst w h ds →
      CellsRel R b (Assemble.blitRows src ox oy k y dst) w h (Decode.blitRows ssp w ox oy k y ds) := by
  intro k
  induction k with
  | zero => intro y dst w h ds hd; exact hd
  | succ k ih =>
    intro y dst w h ds hd
    simp only [Assemble.blitRows, Decode.blitRows]
    apply ih
    have e1 : ssp.width = src.width := hs.1.symm
    have e2 : w = dst.width := hd.1.symm
    rw [e1]
    subst e2
    exact blitRow_rel R b src ssp hs src.width (y * src.width) ((oy + y) * dst.width + ox) dst _ h ds hd

/-- `Assemble.blit` and `Spec.Decode.blit` keep `CellsRel` and the destination size. -/
private theorem blit_rel (R : Int32 → SpecSample → Prop) (b : Prop) (dst src : Plane) (dsp ssp : SamplePlane)
    (hd : CellsRel R b dst dsp.width dsp.height dsp.samples)
    (hs : CellsRel R b src ssp.width ssp.height ssp.samples) (ox oy : Nat) :
    ERel (fun d d' => CellsRel R b d d'.width d'.height d'.samples ∧ d'.width = dsp.width ∧
        d'.height = dsp.height)
      (Assemble.blit dst src ox oy) (Decode.blit dsp ssp ox oy) := by
  unfold Assemble.blit Decode.blit
  rw [hd.1, hd.2.1, hs.1, hs.2.1]
  split
  · refine ⟨?_, rfl, rfl⟩
    have := blitRows_rel R b src ssp hs ox oy src.height 0 dst dsp.width dsp.height dsp.samples hd
    rw [hs.2.1] at this
    exact this
  · trivial

/-- `ArrRel` is preserved by writing related values. -/
theorem ArrRel.setv {α β : Type} {P : Nat → α → β → Prop} {z : α} {w : β} {xs : Array α}
    {ys : Array β} (h : ArrRel P z w xs ys) (i : Nat) (x : α) (y : β) (hxy : P i x y) :
    ArrRel P z w (xs.setIfInBounds i x) (ys.setIfInBounds i y) := by
  obtain ⟨hs, hc⟩ := h
  refine ⟨by simp [hs], fun c => ?_⟩
  have := hc c
  by_cases e : i = c
  · subst e
    by_cases hi : i < xs.size
    · have hi' : i < ys.size := hs ▸ hi
      simpa [Array.getD_eq_getD_getElem?, hi, hi'] using hxy
    · have hi' : ¬ i < ys.size := by rw [← hs]; exact hi
      simpa [Array.getD_eq_getD_getElem?, hi, hi'] using this
  · simpa [Array.getD_eq_getD_getElem?, e] using this

/-- A second write at the same index overrides the first. -/
private theorem set_set {α : Type} (xs : Array α) (i : Nat) (a b : α) :
    (xs.setIfInBounds i a).setIfInBounds i b = xs.setIfInBounds i b := by
  apply Array.ext_getElem?
  intro j
  simp only [Array.getElem?_setIfInBounds, Array.size_setIfInBounds]
  by_cases e : i = j <;> simp [e]

/-- Two failing computations are related. -/
theorem ERel.throw_bind {α β γ δ : Type} {S : γ → δ → Prop} (e e' : Error)
    (f : α → Except Error γ) (g : β → Except Error δ) :
    ERel S (throw e >>= f) (throw e' >>= g) := trivial

/-- **`PlaceEquiv` holds**: placing related tiles keeps the component planes related. -/
theorem placeEquiv : PlaceEquiv := by
  intro R b info ps ss o s hps ht hout
  unfold JPEG2000.Decode.place Decode.place
  dsimp only
  rw [show s.comps.size = o.comps.size from hout.1.symm]
  refine ERel.bind (R := fun a b' => PlaneArr R b a b' ∧ SameDims ss b') ?_ (fun a b' h => ERel.pure h)
  apply ERel.forIn_range
  · intro c a a' ⟨hpa, hsd⟩
    by_cases hc : c < o.comps.size
    · have hc' : c < s.comps.size := hout.1 ▸ hc
      have hrel := hout.2 c
      have e1 : o.comps.getD c (default, Plane.zero 0 0) = o.comps[c] := by
        simp [Array.getD_eq_getD_getElem?, hc]
      have e2 : s.comps.getD c default = s.comps[c] := by
        simp [Array.getD_eq_getD_getElem?, hc']
      rw [e1, e2] at hrel
      rw [Array.getElem?_eq_getElem hc, Array.getElem?_eq_getElem hc']
      generalize o.comps[c] = oc at hrel ⊢
      generalize s.comps[c] = sc at hrel ⊢
      obtain ⟨r, pl⟩ := oc
      obtain ⟨r', spl⟩ := sc
      obtain ⟨hr, hcr⟩ := hrel
      simp only at hr hcr
      subst hr
      dsimp only
      cases info[c]? with
      | none => exact ERel.throw_bind _ _ _ _
      | some dc =>
        dsimp only
        split
        · exact ERel.throw_bind _ _ _ _
        · apply ERel.bind (blit_rel (R c) b _ pl _ spl (hpa.2 c) hcr _ _)
          intro d d' ⟨hdd, hw, hh⟩
          apply ERel.pure
          rw [set_set]
          refine ⟨ArrRel.setv hpa c d d' hdd, ?_⟩
          refine ⟨by simp [hsd.1], fun c' => ?_⟩
          by_cases e : c = c'
          · subst e
            by_cases hi : c < a'.size
            · have g1 : (a'.setIfInBounds c d').getD c default = d' := by
                simp [Array.getD_eq_getD_getElem?, hi]
              rw [g1, hw, hh]; exact hsd.2 c
            · have g1 : (a'.setIfInBounds c d').getD c default = a'.getD c default := by
                simp [Array.getD_eq_getD_getElem?, hi]
              rw [g1]; exact hsd.2 c
          · have g1 : (a'.setIfInBounds c d').getD c' default = a'.getD c' default := by
              simp [Array.getD_eq_getD_getElem?, e]
            rw [g1]; exact hsd.2 c'
    · have hc' : ¬ c < s.comps.size := by rw [← hout.1]; exact hc
      rw [Array.getElem?_eq_none (Nat.le_of_not_lt hc), Array.getElem?_eq_none (Nat.le_of_not_lt hc')]
      exact ERel.throw_bind _ _ _ _
  · exact ⟨hps, SameDims.refl _⟩

/-- The invariant of the tile loop of `codestreamWith`: same passes and tile-part position; related
planes (when nothing saturated so far); spec planes of the initial sizes. -/
def LoopInv (h : Header) (p0 : Array Plane) (a : Array Plane × Nat × Nat × Nat)
    (b : Array SamplePlane × Nat × Nat × Nat) : Prop :=
  a.2.1 = b.2.1 ∧ a.2.2.2 = b.2.2.2 ∧ PlaneArr (SampleRel h) (a.2.2.1 = 0) a.1 b.1 ∧
    SameDims (initPlanes p0) b.1

/-- One iteration of the tile loop after Tier-2: reconstruction and placement. -/
theorem tail_rel (hT1 : Tier1Equiv) (hQ : DequantLoopEquiv) (h53 : DWT53PlaneEquiv)
    (h97 : DWT97PlaneErr) (hPl : PlaceEquiv) (L : Limits) (h : Header) (data : ByteArray)
    (t reduce : Nat) (tcb : Option TileCodeBlocks) (stcb : Option Spec.Tier2.TileOut)
    (hT : T2Img data tcb stcb)
    (hH : ∀ g coding, Progression.Layout.ofHeader h t = .ok (g, coding) →
      (∀ c, ParamsWF (g.comp c)) ∧
      (coding.mctApplies h.siz → ∀ c, c < 3 → (g.comp c).params.transform = (g.comp 0).params.transform))
    (hW : ∀ x, tcb = some x → (∀ g coding, Progression.Layout.ofHeader h t = .ok (g, coding) →
      ∀ c, PrecsWF (g.comp c) (x.comps.getD c #[])) ∧ ∀ c, BlocksIn data (x.comps.getD c #[]))
    (info : Array DecodedComponent) (p0 pl : Array Plane) (spl : Array SamplePlane) (n sat s2 j : Nat)
    (hpl : PlaneArr (SampleRel h) (sat = 0) pl spl) (hsd : SameDims (initPlanes p0) spl) :
    ERel (StepRel (LoopInv h p0))
      (do
        let out ← Assemble.decodeTile L h data t reduce tcb
        let p ← JPEG2000.Decode.place info pl out
        pure (ForInStep.yield (p, n, sat + out.saturated, j)))
      (do
        let out ← Decode.decodeTile L h t reduce stcb
        let p ← Decode.place info spl out
        pure (ForInStep.yield (p, n, s2, j))) := by
  apply ERel.bind (tile_rel hT1 hQ h53 h97 L h data t reduce tcb stcb hT hH hW)
  intro o so ⟨ht, hout⟩
  have hpl' := hpl.weaken (b' := sat + o.saturated = 0) (fun e => by omega)
  have hout' : OutRel h (sat + o.saturated = 0) o.comps so.comps :=
    ArrRel.mono hout fun _ _ _ ⟨e, k⟩ => ⟨e, CellsRel.mono k (fun e => by omega) fun _ _ x => x⟩
  apply ERel.bind (hPl (SampleRel h) _ info pl spl o so hpl' ht hout')
  intro ps ss ⟨hps, hsd'⟩
  exact ⟨rfl, rfl, hps, hsd.trans hsd'⟩

/-- `getD` of `Array.zipWith` in range. -/
private theorem zipWith_getD {α β γ : Type} [Inhabited γ] (f : α → β → γ) (xs : Array α) (ys : Array β)
    (c : Nat) (hx : c < xs.size) (hy : c < ys.size) (dx : α) (dy : β) :
    (Array.zipWith f xs ys).getD c default = f (xs.getD c dx) (ys.getD c dy) := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_zipWith, hx, hy]

/-- Sizes of the initial spec planes. -/
private theorem initPlanes_getD (p0 : Array Plane) (c : Nat) (hc : c < p0.size) :
    ((initPlanes p0).getD c default).width = (p0.getD c (Plane.zero 0 0)).width ∧
    ((initPlanes p0).getD c default).height = (p0.getD c (Plane.zero 0 0)).height := by
  simp [initPlanes, Array.getD_eq_getD_getElem?, hc]

/-- The final records are related by `C9Rel`. -/
theorem final_rel (h : Header) (reduce : Nat) (info : Array DecodedComponent) (p0 : Array Plane)
    (hsz0 : info.size = p0.size)
    (hdims0 : ∀ c, c < p0.size →
      (p0.getD c (Plane.zero 0 0)).width = (info.getD c default).width ∧
      (p0.getD c (Plane.zero 0 0)).height = (info.getD c default).height)
    (a : Array Plane × Nat × Nat × Nat) (b : Array SamplePlane × Nat × Nat × Nat)
    (hi : LoopInv h p0 a b) :
    C9Rel { header := h, reduce := reduce,
            comps := info.zipWith (fun m p => { m with plane := p }) a.1, saturatedBlocks := a.2.2.1 }
          { header := h, comps := info.zipWith (fun m p => { info := m, samples := p.samples }) b.1 } := by
  obtain ⟨-, -, hpl, hsd⟩ := hi
  have hab : a.1.size = b.1.size := hpl.1
  have hb : b.1.size = p0.size := by rw [hsd.1]; simp [initPlanes]
  refine ⟨rfl, by simp [hab], fun c hc => ?_⟩
  simp only [Array.size_zipWith] at hc
  have hci : c < info.size := by omega
  have hca : c < a.1.size := by omega
  have hcb : c < b.1.size := by omega
  have hcp : c < p0.size := by omega
  simp only
  rw [zipWith_getD _ _ _ c hci hca default (Plane.zero 0 0),
    zipWith_getD _ _ _ c hci hcb default default]
  have hr := hpl.2 c
  obtain ⟨w1, w2⟩ := hsd.2 c
  obtain ⟨i1, i2⟩ := initPlanes_getD p0 c hcp
  obtain ⟨d1, d2⟩ := hdims0 c hcp
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  simp only
  have ew : (b.1.getD c default).width = (info.getD c default).width := by rw [w1, i1, d1]
  have eh : (b.1.getD c default).height = (info.getD c default).height := by rw [w2, i2, d2]
  rw [← ew, ← eh]
  exact hr

/-- **C9 from the stage hypotheses** (Plan.md §4 C9, §5.1). For every limits, input and resolution
reduction, `decodeCodestreamNarrow` and `Spec.decode` are related by `ERel C9Rel`: both fail, or the fast
decoder refuses with `unsupported`, or both succeed with the same header and geometry and — when no
code-block saturated — every in-range sample equal (reversible paths) or within C8's per-sample
bound `cellErr + 1` (irreversible paths). Assumes the stage obligations `Tier2Equiv`,
`Tier2WF`, `Tier1Equiv`, `DequantLoopEquiv`, `DWT53PlaneEquiv`, `DWT97PlaneErr`, `HeaderWF`; MCT, DC
shift, placement and the sub-sampling premise of `Tier2Equiv` (`parse_dxdy`) are proved here. This
is the composition only: `Spec.Tier2Wire.c9_of_open` supplies the proved hypotheses, C9 itself
(task 7.1e) discharges the rest. -/
theorem c9_of_stages (hT2 : Tier2Equiv) (hT2w : Tier2WF) (hT1 : Tier1Equiv) (hQ : DequantLoopEquiv)
    (h53 : DWT53PlaneEquiv) (h97 : DWT97PlaneErr) (hHd : HeaderWF) :
    ∀ (L : Limits) (data : ByteArray) (reduce : Nat),
      ERel C9Rel (decodeCodestreamNarrow L data reduce) (Spec.Decode.decode L data reduce) := by
  intro L data reduce
  rw [decodeCodestream_eq_with]
  unfold Decode.decode codestreamWith
  apply ERel.bind_same; intro u
  cases hp : Header.parse L data with
  | error e => trivial
  | ok h =>
  rw [ok_bind, ok_bind]
  dsimp only
  cases ha : Decode.allocOutput L h.siz reduce with
  | error e => trivial
  | ok ip =>
  obtain ⟨info, planes0⟩ := ip
  rw [ok_bind, ok_bind]
  dsimp only
  obtain ⟨hsz0, hdims0⟩ := alloc_facts L h.siz reduce info planes0 ha
  have hinit : PlaneArr (SampleRel h) True planes0 (initPlanes planes0) :=
    initPlanes_rel h True planes0 fun c hc => (hdims0 c hc).2.2
  have hH := hHd L data h hp
  split <;> (try simp only [pure_bind]) <;> (try (apply ERel.bind_same; intro idx))
  all_goals
    refine ERel.bind (R := LoopInv h planes0) ?_ ?_
    · apply ERel.forIn_range
      · intro t a b ⟨hpass, hj, hpl, hsd⟩
        obtain ⟨pl, n, sat, j⟩ := a
        obtain ⟨spl, sn, ssat, sj⟩ := b
        simp only at hpass hj hpl hsd ⊢
        subst hpass hj
        cases htj : h.tiles[j]? with
        | none =>
          simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
          try simp only [pure_bind]
          exact tail_rel hT1 hQ h53 h97 placeEquiv L h data t reduce none none trivial (hH t)
            (fun x hx => by simp at hx) info planes0 pl spl n sat _ j hpl hsd
        | some tp =>
          by_cases hti : tp.index = t
          · simp only [hti, ↓reduceIte, Option.isSome_some]
            try simp only [pure_bind]
            apply ERel.bind_same; intro hs
            apply ERel.bind ((hT2 L h data tp hs n (parse_dxdy hp)).and_left (hT2w L h data tp hs n))
            intro x y ⟨⟨hxy, hpass⟩, hwf⟩
            try simp only [pure_bind]
            rw [hpass]
            refine tail_rel hT1 hQ h53 h97 placeEquiv L h data t reduce (some x) (some y) hxy (hH t) ?_ info
              planes0 pl spl _ sat _ _ hpl hsd
            intro x' hx'
            cases hx'
            exact ⟨fun g coding hl c => hwf.1 g coding (hti ▸ hl) c, hwf.2⟩
          · simp only [hti, ↓reduceIte, Option.isSome_none, Bool.false_eq_true]
            try simp only [pure_bind]
            exact tail_rel hT1 hQ h53 h97 placeEquiv L h data t reduce none none trivial (hH t)
              (fun x hx => by simp at hx) info planes0 pl spl n sat _ j hpl hsd
      · exact ⟨rfl, rfl, hinit.weaken (fun _ => trivial), SameDims.refl _⟩
    · intro a b hi
      exact final_rel h reduce info planes0 hsz0 (fun c hc => ⟨(hdims0 c hc).1, (hdims0 c hc).2.1⟩) a b hi

end JPEG2000.Spec.Equiv
