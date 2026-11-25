import Spec.QuantBlock.Step

/-!
# The dequantisation block loop = spec (Mallat placement)

Plan.md §4 (C9), §5.1 (one equivalence theorem per stage), §5.4; T.800 Annex E.1.1.2
(dequantisation, E-6), Annex H (ROI max-shift), Annex B.5 (B-15 band rectangles, reduced
resolutions B-14), Annex F.3.3 (Mallat layout of the sub-bands). Task 7.1d.

Discharges the stage hypothesis `Spec.Equiv.DequantLoopEquiv` of `Spec.Equiv.c9_of_stages`:
`dequantLoopEquiv`. The fast coefficient loop of `tileCompWith` (Tier-1 output dequantised by
`Quant.dequantBlock` straight into the `Int32` tile-component plane, Mallat layout) and the
spec loop (code-blocks collected into a list, read back per band position by
`Spec.Decode.bandGrid53` / `bandGrid97`) end in `LoopRel`: when no code-block saturated, every
band position the inverse DWT reads holds the spec's dequantised value (reversible:
`Quant.revCoeff_eq`) or is within `1/2` ulp of it (irreversible: `Quant.irrevCoeff_bound`).

* `dequantBlock_ok`: under the geometry the loop guarantees (`PrecsWF`, the reduced-resolution
  band identity `bandRect_reduce`, `BlockAgree` sizes) `dequantBlock` never fails;
* `step_rel`: one code-block preserves `LoopRel` (`write_hit` + the kernels);
* `dequantLoopEquiv`: the loops, by relational reasoning over the shared control flow.
-/

namespace JPEG2000.Spec.QuantBlock

open JPEG2000 JPEG2000.Bytes JPEG2000.Header JPEG2000.Tier2.Geometry JPEG2000.Tier2.Packet
open JPEG2000.DWT53 (halfN cellInt toDec)
open JPEG2000.Spec.DWTPlane (if_t if_f)
open JPEG2000.Spec.Equiv (band53 band97 InBand ReadBand BandsEq BandsClose LoopRel BlockAgree
  ERel StepRel PrecsWF ParamsWF)
open JPEG2000.Spec.Decode (Entry entryAt bandGrid53 bandGrid97 dec53 dec97 collect initSpec)
open JPEG2000.Quant (blockRows bandOrigin revCoeff irrevCoeff irrevConsts)
open JPEG2000.Spec.Tier1 (Coeff)

/-! ## `dequantBlock` does not fail -/

/-- `dequantBlock` on a well-formed code-block is `blockRows` at its Mallat origin. -/
theorem dequantBlock_ok (dst : Plane) (rect : Rect) (nl r : Nat) (b : Band) (cb : Rect)
    (q : Spec.Quant.BandQuant) (F : Nat) (o : Tier1.CodeBlockOut)
    (h1 : dst.width = rect.x1 - rect.x0) (h2 : dst.height = rect.y1 - rect.y0) (hr : r ≤ nl)
    (h3 : o.plane.width = cb.x1 - cb.x0) (h4 : o.plane.height = cb.y1 - cb.y0)
    (hx0 : (bandRect rect (bandLevel nl r) b).x0 ≤ cb.x0)
    (hy0 : (bandRect rect (bandLevel nl r) b).y0 ≤ cb.y0)
    (hx1 : cb.x1 ≤ (bandRect rect (bandLevel nl r) b).x1)
    (hy1 : cb.y1 ≤ (bandRect rect (bandLevel nl r) b).y1) :
    Quant.dequantBlock dst rect nl r b cb q F o =
      .ok (blockRows (if q.reversible then revCoeff q.roiShift
          else irrevCoeff (irrevConsts q F) q.roiShift) o
        ((bandOrigin rect nl r b).1 + (cb.x0 - (bandRect rect (bandLevel nl r) b).x0))
        ((bandOrigin rect nl r b).2 + (cb.y0 - (bandRect rect (bandLevel nl r) b).y0))
        o.plane.height 0 dst true) := by
  unfold Quant.dequantBlock
  simp only [show ¬ (dst.width ≠ rect.x1 - rect.x0 ∨ dst.height ≠ rect.y1 - rect.y0) by omega,
    show ¬ (r > nl) by omega,
    show ¬ (o.plane.width ≠ cb.x1 - cb.x0 ∨ o.plane.height ≠ cb.y1 - cb.y0) by omega,
    show ¬ (cb.x0 < (bandRect rect (bandLevel nl r) b).x0 ∨ cb.y0 < (bandRect rect (bandLevel nl r) b).y0 ∨
      (bandRect rect (bandLevel nl r) b).x1 < cb.x1 ∨ (bandRect rect (bandLevel nl r) b).y1 < cb.y1) by omega,
    ↓reduceIte]
  cases q.reversible <;> rfl

/-! ## The spec side: band grids -/

/-- The spec decomposition's band at a read position is `bandGrid53`. -/
theorem band53_dec53 (es : List Entry) (nl lvl : Nat) (b : Band) (hr : ReadBand nl lvl b) :
    band53 (dec53 es nl) lvl b = bandGrid53 es nl lvl b := by
  rcases hr with ⟨hb, hl⟩ | ⟨hb, h1, h2⟩
  · subst hb; subst hl; rfl
  · have hd : (dec53 es nl).details[lvl - 1]? = some (bandGrid53 es nl lvl .HL,
        bandGrid53 es nl lvl .LH, bandGrid53 es nl lvl .HH) := by
      simp only [dec53, List.getElem?_map, List.getElem?_range (show lvl - 1 < nl by omega),
        Option.map_some, show lvl - 1 + 1 = lvl by omega]
    cases b with
    | LL => exact absurd rfl hb
    | HL => simp only [band53, hd]
    | LH => simp only [band53, hd]
    | HH => simp only [band53, hd]

/-- The rational spec decomposition's band at a read position is `bandGrid97`. -/
theorem band97_dec97 (es : List Entry) (nl lvl : Nat) (b : Band) (hr : ReadBand nl lvl b) :
    band97 (dec97 es nl) lvl b = bandGrid97 es nl lvl b := by
  rcases hr with ⟨hb, hl⟩ | ⟨hb, h1, h2⟩
  · subst hb; subst hl; rfl
  · have hd : (dec97 es nl).details[lvl - 1]? = some (bandGrid97 es nl lvl .HL,
        bandGrid97 es nl lvl .LH, bandGrid97 es nl lvl .HH) := by
      simp only [dec97, List.getElem?_map, List.getElem?_range (show lvl - 1 < nl by omega),
        Option.map_some, show lvl - 1 + 1 = lvl by omega]
    cases b with
    | LL => exact absurd rfl hb
    | HL => simp only [band97, hd]
    | LH => simp only [band97, hd]
    | HH => simp only [band97, hd]

/-- Looking up a band position in a list with a new code-block in front. -/
theorem entryAt_cons (e : Entry) (es : List Entry) (nl lvl : Nat) (b : Band) (u v : Int) :
    entryAt (e :: es) nl lvl b u v =
      if e.band = b ∧ bandLevel nl e.r = lvl ∧ (e.rect.x0 : Int) ≤ u ∧ u < e.rect.x1 ∧
          (e.rect.y0 : Int) ≤ v ∧ v < e.rect.y1 then some e
      else entryAt es nl lvl b u v := by
  simp only [entryAt, List.find?_cons, Entry.covers]
  by_cases h : e.band = b ∧ bandLevel nl e.r = lvl ∧ (e.rect.x0 : Int) ≤ u ∧ u < e.rect.x1 ∧
      (e.rect.y0 : Int) ≤ v ∧ v < e.rect.y1
  · rw [if_t h]
    have : (e.band == b && bandLevel nl e.r == lvl &&
        decide ((e.rect.x0 : Int) ≤ u ∧ u < e.rect.x1 ∧ (e.rect.y0 : Int) ≤ v ∧ v < e.rect.y1)) = true := by
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]; exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩
    rw [this]
  · rw [if_f h]
    have : (e.band == b && bandLevel nl e.r == lvl &&
        decide ((e.rect.x0 : Int) ≤ u ∧ u < e.rect.x1 ∧ (e.rect.y0 : Int) ≤ v ∧ v < e.rect.y1)) = false := by
      simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq, decide_eq_false_iff_not]
      by_cases h1 : e.band = b
      · by_cases h2 : bandLevel nl e.r = lvl
        · exact .inr (fun h3 => h ⟨h1, h2, h3⟩)
        · exact .inl (.inr h2)
      · exact .inl (.inl h1)
    rw [this]

/-! ## One code-block preserves `LoopRel` -/

/-- The block value is the spec coefficient's value (`BlockAgree`). -/
theorem bval_agree (cb : CodeBlock) (o : Tier1.CodeBlockOut) (cs : Array Coeff)
    (hag : BlockAgree cb o cs) (x y : Nat) (hx : x < cb.geom.rect.width) (hy : y < cb.geom.rect.height) :
    (cs.getD (y * cb.geom.rect.width + x) {}).value = (QuantBlock.bval o x y).toInt ∧
    o.lsbPlane x y = (cs.getD (y * cb.geom.rect.width + x) {}).lsbPlane := by
  obtain ⟨hw, -, -, hv⟩ := hag
  obtain ⟨h1, h2⟩ := hv x y hx hy
  refine ⟨?_, h2⟩
  simp only [bval, hw]
  cases hg : o.plane.get? (y * cb.geom.rect.width + x) with
  | none => rw [hg] at h1; simp at h1
  | some w => rw [hg] at h1; simp only [Option.map_some, Option.some.injEq] at h1; simp [h1]

/-- **One code-block preserves `LoopRel`** (reversible: exact band values; irreversible:
within `1/2` ulp), with the saturation count incremented when the block saturated. -/
theorem step_rel (F : Nat) (rev : Bool) (pl : Plane) (rect : Rect) (nl n : Nat) (es : List Entry)
    (h : LoopRel F rev pl rect nl n es) (r : Nat) (b : Band) (cb : CodeBlock)
    (o : Tier1.CodeBlockOut) (cs : Array Coeff) (q : Spec.Quant.BandQuant)
    (hq : q.reversible = rev) (hmu : q.mantissa < 2048) (hr : r ≤ nl) (hb : b ∈ bandsOf r)
    (hag : BlockAgree cb o cs)
    (hx0 : (bandRect rect (bandLevel nl r) b).x0 ≤ cb.geom.rect.x0)
    (hy0 : (bandRect rect (bandLevel nl r) b).y0 ≤ cb.geom.rect.y0)
    (hx1 : cb.geom.rect.x1 ≤ (bandRect rect (bandLevel nl r) b).x1)
    (hy1 : cb.geom.rect.y1 ≤ (bandRect rect (bandLevel nl r) b).y1)
    (hnx : cb.geom.rect.x0 < cb.geom.rect.x1) (hny : cb.geom.rect.y0 < cb.geom.rect.y1) :
    LoopRel F rev
      (blockRows (if q.reversible then revCoeff q.roiShift else irrevCoeff (irrevConsts q F) q.roiShift) o
        ((bandOrigin rect nl r b).1 + (cb.geom.rect.x0 - (bandRect rect (bandLevel nl r) b).x0))
        ((bandOrigin rect nl r b).2 + (cb.geom.rect.y0 - (bandRect rect (bandLevel nl r) b).y0))
        o.plane.height 0 pl true).1 rect nl
      (if (!(blockRows (if q.reversible then revCoeff q.roiShift else irrevCoeff (irrevConsts q F) q.roiShift) o
        ((bandOrigin rect nl r b).1 + (cb.geom.rect.x0 - (bandRect rect (bandLevel nl r) b).x0))
        ((bandOrigin rect nl r b).2 + (cb.geom.rect.y0 - (bandRect rect (bandLevel nl r) b).y0))
        o.plane.height 0 pl true).2) = true then n + 1 else n)
      ({ r, band := b, rect := cb.geom.rect, q, coeffs := cs } :: es) := by
  obtain ⟨hw, hh, hv⟩ := h
  have ow := hag.1
  have oh := hag.2.1
  obtain ⟨w1, w2, w3, w4⟩ := write_hit rect nl r b cb.geom.rect o
    (if q.reversible then revCoeff q.roiShift else irrevCoeff (irrevConsts q F) q.roiShift) pl true
    hw hh hr hb ow oh hx0 hy0 hx1 hy1 hnx hny
  generalize blockRows (if q.reversible then revCoeff q.roiShift else irrevCoeff (irrevConsts q F) q.roiShift) o
        ((bandOrigin rect nl r b).1 + (cb.geom.rect.x0 - (bandRect rect (bandLevel nl r) b).x0))
        ((bandOrigin rect nl r b).2 + (cb.geom.rect.y0 - (bandRect rect (bandLevel nl r) b).y0))
        o.plane.height 0 pl true = res at w1 w2 w3 w4
  refine ⟨by rw [w1, hw], by rw [w2, hh], fun h0 => ?_⟩
  have hok : res.2 = true := by cases hr2 : res.2 <;> simp_all
  have hn0 : n = 0 := by cases hr2 : res.2 <;> simp_all
  have hold := hv hn0
  have hall := w3 hok
  -- the coefficient read back at a covered position
  have hcoef : ∀ u v, (cb.geom.rect.x0 : Int) ≤ u → u < cb.geom.rect.x1 → (cb.geom.rect.y0 : Int) ≤ v →
      v < cb.geom.rect.y1 →
      ({ r, band := b, rect := cb.geom.rect, q, coeffs := cs } : Entry).coeff u v =
        cs.getD ((v - cb.geom.rect.y0).toNat * cb.geom.rect.width + (u - cb.geom.rect.x0).toNat) {} ∧
      (u - cb.geom.rect.x0).toNat < o.plane.width ∧ (v - cb.geom.rect.y0).toNat < o.plane.height := by
    intro u v h1 h2 h3 h4
    refine ⟨rfl, ?_, ?_⟩
    · rw [ow]; simp only [Header.Rect.width]; omega
    · rw [oh]; simp only [Header.Rect.height]; omega
  cases rev with
  | true =>
    simp only [↓reduceIte] at hold ⊢
    intro lvl2 b2 u v hrb hin
    have ho := hold lvl2 b2 u v hrb hin
    rw [band53_toDec _ _ _ _ _ hrb, band53_dec53 _ _ _ _ hrb] at ho ⊢
    rw [w4 lvl2 b2 u v hrb hin, ho]
    simp only [bandGrid53, entryAt_cons]
    by_cases hm : b = b2 ∧ bandLevel nl r = lvl2 ∧ (cb.geom.rect.x0 : Int) ≤ u ∧ u < cb.geom.rect.x1 ∧
        (cb.geom.rect.y0 : Int) ≤ v ∧ v < cb.geom.rect.y1
    · rw [if_t hm, if_t hm]
      obtain ⟨-, -, h1, h2, h3, h4⟩ := hm
      obtain ⟨ec, hx, hy⟩ := hcoef u v h1 h2 h3 h4
      dsimp only
      rw [ec]
      obtain ⟨bv, bl⟩ := bval_agree cb o cs hag _ _ (by rw [← ow]; exact hx) (by rw [← oh]; exact hy)
      have hf := hall _ _ hx hy
      rw [if_t hq, bl] at hf ⊢
      obtain ⟨e1, e2⟩ := Quant.revCoeff_eq q.roiShift _ _ bv
      have := e2.mp hf
      rw [e1, Quant.sat32_toInt _ this.1 this.2]
    · rw [if_f hm, if_f hm]
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hold ⊢
    intro lvl2 b2 u v hrb hin
    have ho := hold lvl2 b2 u v hrb hin
    rw [band53_toDec _ _ _ _ _ hrb, band97_dec97 _ _ _ _ hrb] at ho ⊢
    rw [w4 lvl2 b2 u v hrb hin]
    simp only [bandGrid97] at ho ⊢
    rw [entryAt_cons]
    by_cases hm : b = b2 ∧ bandLevel nl r = lvl2 ∧ (cb.geom.rect.x0 : Int) ≤ u ∧ u < cb.geom.rect.x1 ∧
        (cb.geom.rect.y0 : Int) ≤ v ∧ v < cb.geom.rect.y1
    · rw [if_t hm, if_t hm]
      obtain ⟨-, -, h1, h2, h3, h4⟩ := hm
      obtain ⟨ec, hx, hy⟩ := hcoef u v h1 h2 h3 h4
      dsimp only
      rw [ec]
      obtain ⟨bv, bl⟩ := bval_agree cb o cs hag _ _ (by rw [← ow]; exact hx) (by rw [← oh]; exact hy)
      have hf := hall _ _ hx hy
      have hq' : ¬ q.reversible = true := by rw [hq]; decide
      rw [if_f hq', bl] at hf ⊢
      obtain ⟨e1, e2⟩ := Quant.irrevCoeff_bound q F q.roiShift _ _ bv hmu hf
      unfold Spec.Quant.dequantIrrevScaled at e1 e2
      generalize (((irrevCoeff (irrevConsts q F) q.roiShift (bval o (u - ↑cb.geom.rect.x0).toNat
        (v - ↑cb.geom.rect.y0).toNat) (cs.getD ((v - ↑cb.geom.rect.y0).toNat * cb.geom.rect.width +
          (u - ↑cb.geom.rect.x0).toNat) {}).lsbPlane).1.toInt : Int) : Rat) = a at e1 e2 ⊢
      generalize Spec.Quant.dequantIrrev q.roiShift q.delta (cs.getD ((v - ↑cb.geom.rect.y0).toNat *
        cb.geom.rect.width + (u - ↑cb.geom.rect.x0).toNat) {}) = d at e1 e2 ⊢
      generalize ((2 ^ F : Nat) : Rat) = P at e1 e2 ⊢
      apply Spec.DWT97.abs_le_iff.mpr
      constructor <;> grind
    · rw [if_f hm, if_f hm]
      exact ho

/-- The empty store: zero plane vs no code-blocks. -/
theorem init_rel (F : Nat) (rev : Bool) (rect : Rect) (nl : Nat) :
    LoopRel F rev (Plane.zero rect.width rect.height) rect nl 0 [] := by
  refine ⟨rfl, rfl, fun _ => ?_⟩
  have hz : ∀ X Y, cellInt (Plane.zero rect.width rect.height) X Y = 0 := by
    intro X Y
    unfold cellInt
    split
    · split
      · rename_i v hv
        simp only [Plane.get?] at hv
        split at hv
        · cases hv; rw [Plane.get_zero]; rfl
        · cases hv
      · rfl
    · rfl
  cases rev with
  | true =>
    intro lvl b u v hrb _
    rw [band53_toDec _ _ _ _ _ hrb, band53_dec53 _ _ _ _ hrb, hz]
    rfl
  | false =>
    intro lvl b u v hrb _
    rw [band53_toDec _ _ _ _ _ hrb, band97_dec97 _ _ _ _ hrb, hz]
    simp only [bandGrid97, entryAt, List.find?_nil]
    apply Spec.DWT97.abs_le_iff.mpr
    constructor <;> grind

/-! ## Loops related index by index -/

/-- Two `for` loops over the same list, with bodies preserving a relation for every element of
the list. -/
theorem ERel.forIn_list_mem {γ α β : Type} {R : α → β → Prop} (xs : List γ)
    (f : γ → α → Except Error (ForInStep α)) (g : γ → β → Except Error (ForInStep β))
    (hf : ∀ x, x ∈ xs → ∀ a b, R a b → ERel (StepRel R) (f x a) (g x b)) :
    ∀ a b, R a b → ERel R (forIn xs a f) (forIn xs b g) := by
  induction xs with
  | nil => intro a b h; exact h
  | cons x xs ih =>
    intro a b h
    simp only [List.forIn_cons]
    apply Spec.Equiv.ERel.bind (hf x List.mem_cons_self a b h)
    intro s t hst
    cases s <;> cases t <;> simp only [StepRel] at hst
    · exact hst
    · exact ih (fun y hy => hf y (List.mem_cons_of_mem _ hy)) _ _ hst

/-- Two `for` loops over the same array (membership-aware). -/
theorem ERel.forIn_arr_mem {γ α β : Type} {R : α → β → Prop} (xs : Array γ)
    (f : γ → α → Except Error (ForInStep α)) (g : γ → β → Except Error (ForInStep β))
    (hf : ∀ x, x ∈ xs → ∀ a b, R a b → ERel (StepRel R) (f x a) (g x b)) (a : α) (b : β)
    (h : R a b) : ERel R (forIn xs a f) (forIn xs b g) := by
  rw [← Array.forIn_toList, ← Array.forIn_toList]
  exact ERel.forIn_list_mem _ f g (fun x hx => hf x (Array.mem_toList_iff.mp hx)) a b h

/-- Two `for` loops over `[0:n]` (index `< n` available). -/
theorem ERel.forIn_range_mem {α β : Type} {R : α → β → Prop} (n : Nat)
    (f : Nat → α → Except Error (ForInStep α)) (g : Nat → β → Except Error (ForInStep β))
    (hf : ∀ x, x < n → ∀ a b, R a b → ERel (StepRel R) (f x a) (g x b)) (a : α) (b : β)
    (h : R a b) : ERel R (forIn [0:n] a f) (forIn [0:n] b g) := by
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  refine ERel.forIn_list_mem _ f g (fun x hx => hf x ?_) a b h
  rw [List.mem_range'] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  simp [Std.Legacy.Range.size] at hi ⊢
  omega

/-! ## The theorem -/

/-- **Stage hypothesis `DequantLoopEquiv` of C9, proved** (E.1.1.2, H, B-15, Mallat placement):
the fast coefficient loop (Tier-1 output dequantised into the `Int32` plane) and the spec loop
(code-blocks collected, read back per band position) end in `LoopRel`, for any Tier-1 decoders
related by `BlockAgree`, whatever continuation follows. -/
theorem dequantLoopEquiv : Spec.Equiv.DequantLoopEquiv := by
  intro L O1 O2 dec decS hdec finF finS RO tc depth F reduce precs hP hW hfin
  unfold Spec.Decode.tileCompWith
  dsimp only
  split
  · trivial
  · rename_i hred
    have hnl : reduce ≤ tc.params.levels := by omega
    refine Spec.Equiv.ERel.bind (R := fun (pl : Plane) (es : List Entry) =>
      LoopRel F (tc.params.transform == .reversible53) pl (Assemble.reduceRect tc.rect reduce)
        (tc.params.levels - reduce) 0 es) ?_ ?_
    · unfold Plane.zeroChecked initSpec
      apply Spec.Equiv.ERel.bind_same
      intro _
      exact init_rel _ _ _ _
    · intro pl es hrel
      refine Spec.Equiv.ERel.bind (R := fun (a : Plane × Nat) (b : List Entry × Nat) =>
        LoopRel F (tc.params.transform == .reversible53) a.1 (Assemble.reduceRect tc.rect reduce)
          (tc.params.levels - reduce) a.2 b.1) ?_ (fun a b hab => hfin _ _ _ _ _ _ hab)
      refine ERel.forIn_range_mem _ _ _ ?_ _ _ hrel
      intro r hr a b hab
      have hr' : r ≤ tc.params.levels - reduce := by omega
      have hrs : r < precs.size := by omega
      refine Spec.Equiv.ERel.bind (R := fun (a : Plane × Nat) (b : List Entry × Nat) =>
        LoopRel F (tc.params.transform == .reversible53) a.1 (Assemble.reduceRect tc.rect reduce)
          (tc.params.levels - reduce) a.2 b.1) ?_ (fun a b hab => ?_)
      rotate_left
      · exact hab
      refine ERel.forIn_arr_mem _ _ _ ?_ _ _ hab
      intro prec hprec a b hab
      refine Spec.Equiv.ERel.bind (R := fun (a : Plane × Nat) (b : List Entry × Nat) =>
        LoopRel F (tc.params.transform == .reversible53) a.1 (Assemble.reduceRect tc.rect reduce)
          (tc.params.levels - reduce) a.2 b.1) ?_ (fun a b hab => ?_)
      rotate_left
      · exact hab
      refine ERel.forIn_arr_mem _ _ _ ?_ _ _ hab
      intro bo hbo a b hab
      obtain ⟨hband, hblocks⟩ := hW r hrs prec hprec bo hbo
      refine Spec.Equiv.ERel.bind (R := fun (a : Plane × Nat) (b : List Entry × Nat) =>
        LoopRel F (tc.params.transform == .reversible53) a.1 (Assemble.reduceRect tc.rect reduce)
          (tc.params.levels - reduce) a.2 b.1) ?_ (fun a b hab => ?_)
      rotate_left
      · exact hab
      refine ERel.forIn_arr_mem _ _ _ ?_ _ _ hab
      intro cb hcb a b hab
      by_cases hc : (cb.numPasses != 0 && !rectEmpty cb.geom.rect) = true
      · rw [if_t hc, if_t hc]
        have hne : cb.geom.rect.x0 < cb.geom.rect.x1 ∧ cb.geom.rect.y0 < cb.geom.rect.y1 := by
          simp only [rectEmpty, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_eq_eq_not,
            Bool.not_true, Bool.or_eq_false_iff, decide_eq_false_iff_not, Nat.not_le] at hc
          exact hc.2
        apply Spec.Equiv.ERel.bind (hdec tc.params r bo.band cb)
        intro o cs hag
        obtain ⟨bx0, by0, bx1, by1⟩ := hblocks cb hcb
        have hid : bandRect (Assemble.reduceRect tc.rect reduce) (bandLevel (tc.params.levels - reduce) r)
            bo.band = bandRect tc.rect (bandLevel tc.params.levels r) bo.band := by
          rw [DWTPlane.bandRect_reduce]
          · congr 1; unfold bandLevel; split <;> omega
          · unfold bandLevel; unfold bandsOf at hband
            by_cases h0 : r = 0
            · subst h0; simp at hband; exact .inr hband
            · simp only [h0, ↓reduceIte]; exact .inl (by omega)
        have hmu : (Spec.Quant.bandQuant tc.params depth r bo.band).mantissa < 2048 := by
          simp only [Spec.Quant.bandQuant, Array.getD_eq_getD_getElem?]
          cases h : tc.params.steps[Spec.Quant.bandIndex r bo.band]? with
          | none => decide
          | some st => exact hP st (Array.mem_of_getElem? h)
        rw [dequantBlock_ok _ _ _ _ _ _ _ _ _ hab.1 hab.2.1 hr' hag.1 hag.2.1
          (by rw [hid]; exact bx0) (by rw [hid]; exact by0) (by rw [hid]; exact bx1)
          (by rw [hid]; exact by1)]
        have hst := step_rel F (tc.params.transform == .reversible53) a.1
          (Assemble.reduceRect tc.rect reduce) (tc.params.levels - reduce) a.2 b.1 hab r bo.band cb
          o cs (Spec.Quant.bandQuant tc.params depth r bo.band) rfl hmu hr' hband hag
          (by rw [hid]; exact bx0) (by rw [hid]; exact by0) (by rw [hid]; exact bx1)
          (by rw [hid]; exact by1) hne.1 hne.2
        simp only [Spec.Equiv.ok_bind, collect]
        generalize (blockRows _ o _ _ o.plane.height 0 a.fst true) = res at hst ⊢
        by_cases hx : (!res.2) = true
        · rw [if_t hx] at hst ⊢
          exact hst
        · rw [if_f hx] at hst ⊢
          exact hst
      · rw [if_f hc, if_f hc]
        exact hab

end JPEG2000.Spec.QuantBlock
