import JPEG2000.WideAssembly
import Spec.WideQuant
import Spec.Tier1Wide.Segments
import Spec.Tier2WF

/-!
# Wide coefficient assembly and the spec band grids
Plan.md §§4, 5.1, 5.4, 7; T.800 B.6–B.10, D, E.1.1.2, H.

The reference block is decoded from the independent packet image. Its pass invariant
provides both the raster length and the insignificant-cell property used by dequantisation.
-/

namespace JPEG2000.Spec.WideAssembly

open JPEG2000.Header JPEG2000.Tier2.Geometry JPEG2000.Tier2.Packet
open JPEG2000.Spec.Decode (Entry entryAt bandGrid53 bandGrid97 decodeBlockSt blockStCodeBlock)

private theorem pre_base {K n : Nat} {c : Tier1.Coeff} (h : Tier1EquivM.Pre K n c) :
    Tier1Equiv.Base K c := by
  unfold Tier1EquivM.Pre at h
  split at h
  · exact h.1
  · unfold Tier1Equiv.Post at h
    split at h
    · exact h.1
    · exact h.1
    · exact h.1.1

private theorem exact_raster (cb : Tier1.CodeBlock) (b : Band)
    (orient : cb.orient = Tier1Equiv.orientOf b) (cs : Array Tier1.Coeff)
    (decoded : Tier1.decodeCodeBlockExact cb = .ok cs) :
    cs.size = cb.width * cb.height ∧ ∀ x y, x < cb.width → y < cb.height →
      let c := cs.getD (y * cb.width + x) {}
      c.sig = false → c.mag = 0 := by
  let g := Tier1EquivM.gV cb.width cb.height b cb.mode.vertCausal
  have geom : cb.geom = g := by unfold Tier1.CodeBlock.geom; rw [orient]; rfl
  unfold Tier1.decodeCodeBlockExact at decoded
  cases valid : cb.validate with
  | error e => simp [valid, bind, Except.bind] at decoded
  | ok u =>
    simp only [valid, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at decoded
    subst cs
    have count := (Tier1EquivM.validate_ok_facts cb u valid).1
    have limit : 0 + (cb.segments.map (·.passes)).sum ≤ 3 * cb.codedPlanes - 2 := by
      change 0 + cb.numPasses ≤ _
      omega
    have init : Tier1EquivM.AllPV cb.width cb.height b cb.mode.vertCausal
        (Tier1EquivM.Pre cb.codedPlanes 0) (Tier1.DecState.init g []).coeffs := by
      refine ⟨by simp [Tier1.DecState.init, g, Tier1EquivM.gV], fun x y _ _ => ?_⟩
      change Tier1EquivM.Pre _ 0 (g.coeffAt (Array.replicate (g.width * g.height) {}) x y)
      rw [Tier1Equiv.coeffAt_replicate]
      exact ⟨⟨fun _ => ⟨rfl, rfl⟩, fun h => by cases h⟩, fun h => by cases h⟩
    have inv := Tier1EquivM.decodeSegments_inv cb.mode cb.codedPlanes cb.segments 0 _ limit init
    unfold Tier1.decodeState
    rw [geom]
    refine ⟨inv.1, fun x y hx hy => ?_⟩
    have base := pre_base (inv.2 x y hx hy)
    rw [Tier1Equiv.coeffAt_nat _ _ _ _ hx hy] at base
    exact fun h => (base.1 h).1

/-- A successful reference block has its declared raster size and every insignificant
cell has magnitude zero, including after pass clamping and MQ/raw restarts. -/
theorem blockSt_raster (p : CompParams) (r : Nat) (b : Band) (cb : Spec.Tier2.BlockSt)
    (cs : Array Tier1.Coeff) (decoded : decodeBlockSt p r b cb = .ok cs) :
    cs.size = rectArea cb.geom.rect ∧ ∀ x y, x < cb.geom.rect.width → y < cb.geom.rect.height →
      let c := cs.getD (y * cb.geom.rect.width + x) {}
      c.sig = false → c.mag = 0 := by
  unfold Decode.decodeBlockSt Tier1.decodeCodeBlock Tier1.CodeBlock.clampPasses at decoded
  split at decoded <;> exact exact_raster _ b rfl cs decoded

private theorem block_alternatives (data : ByteArray) (p : CompParams) (r : Nat) (b : Band)
    (cb : CodeBlock) (ranges : Equiv.segsIn data cb = true) :
    JPEG2000.WideAssembly.decodeBlock data p r b cb =
      (decodeBlockSt p r b (Tier2Equiv.blockOf data cb)).map (·.map Tier1Wide.cellOf) ∨
    (∃ e, JPEG2000.WideAssembly.decodeBlock data p r b cb = .error e ∧
      JPEG2000.Tier1.WidePlain.maxCodedPlanes < bandMb p r b + p.roiShift -
        (if cb.included then cb.zeroBitPlanes else 0)) := by
  obtain ⟨inside, bytes⟩ := Equiv.tier1Input_ok data cb ranges
  unfold JPEG2000.WideAssembly.decodeBlock
  simp only [show (cb.segments.all fun s => s.ranges.all fun rg =>
    decide (rg.offset + rg.length ≤ data.size)) = true from ranges, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte]
  generalize eq : Assemble.tier1Input data cb = pair at inside bytes ⊢
  obtain ⟨buf, segs⟩ := pair
  dsimp only at inside bytes ⊢
  rw [Tier1Wide.Segments.decodeRanges_equiv]
  unfold Tier1Wide.Segments.decodeRanges
  have good : (segs.toList.all fun sg => sg.start ≤ sg.stop && sg.stop ≤ buf.size) = true := by
    simpa only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] using inside
  rw [good]
  simp only [↓reduceIte, Bool.false_eq_true]
  have same : Tier1EquivM.specBlockM buf segs cb.geom.rect.width cb.geom.rect.height b p.cbStyle
      (bandMb p r b + p.roiShift) (if cb.included then cb.zeroBitPlanes else 0) =
      blockStCodeBlock p r b (Tier2Equiv.blockOf data cb) := by
    unfold Tier1EquivM.specBlockM Decode.blockStCodeBlock Tier2Equiv.blockOf
    rw [← bytes]
    rfl
  rw [same]
  generalize sb : blockStCodeBlock p r b (Tier2Equiv.blockOf data cb) = block
  by_cases over : 0 < block.numPasses ∧ 7 + 31 - 1 + 255 < block.codedPlanes
  · rw [ite_eq_left over]
    right
    have big := over.2
    rw [← sb] at big
    split <;> exact ⟨_, rfl, big⟩
  · rw [ite_eq_right over]
    left
    unfold Decode.decodeBlockSt
    rw [sb]

/-- Decoding the parsed block agrees on all coefficient fields and on the complete
Tier-1 error with decoding the spec packet body's segment lists. -/
theorem decodeBlock_eq (data : ByteArray) (p : CompParams) (r : Nat) (b : Band) (cb : CodeBlock)
    (ranges : Equiv.segsIn data cb = true)
    (budget : bandMb p r b + p.roiShift - (if cb.included then cb.zeroBitPlanes else 0) ≤
      JPEG2000.Tier1.WidePlain.maxCodedPlanes) :
    JPEG2000.WideAssembly.decodeBlock data p r b cb =
      (decodeBlockSt p r b (Tier2Equiv.blockOf data cb)).map (·.map Tier1Wide.cellOf) := by
  rcases block_alternatives data p r b cb ranges with eq | ⟨_, _, big⟩
  · exact eq
  · omega

/-- Numerical reconstruction at a covered band cell, including signed midpoint rounding
at irreversible working precision. -/
def entryValue (rev : Bool) (F : Nat) (u v : Int) (e : Entry) : Int :=
  let c := e.coeff u v
  if rev then Quant.dequantRev e.q.roiShift c else
    WideQuant.roundSigned c.sign (Quant.dequantIrrevScaled e.q.roiShift e.q.delta F c)

/-- The loop invariant after any prefix of the packet traversal. Every readable band
cell contains the value of the newest covering spec entry or exactly zero. -/
def LoopRel (rect : Rect) (nl : Nat) (rev : Bool) (F : Nat)
    (pl : JPEG2000.WideQuant.Plane) (es : List Entry) : Prop :=
  pl.rect = rect ∧ ∀ lvl b u v, Equiv.ReadBand nl lvl b → Equiv.InBand rect lvl b u v →
    let x := (QuantBlock.mx rect lvl b u).toNat
    let y := (QuantBlock.my rect lvl b v).toNat
    pl.samples.toArray[y * rect.width + x]? =
      some (((entryAt es nl lvl b u v).map (entryValue rev F u v)).getD 0)

private theorem mallat_bounds (rect : Rect) (nl lvl : Nat) (b : Band) (u v : Int)
    (read : Equiv.ReadBand nl lvl b) (inside : Equiv.InBand rect lvl b u v) :
    let X := QuantBlock.mx rect lvl b u
    let Y := QuantBlock.my rect lvl b v
    0 ≤ X ∧ 0 ≤ Y ∧ X.toNat < rect.width ∧ Y.toNat < rect.height := by
  obtain ⟨hx, hy, ll, detail⟩ := QuantBlock.mpos_range rect nl lvl b u v read inside
  have axis (k : Nat) : QuantBlock.Wd rect k ≤ rect.width ∧ QuantBlock.Hd rect k ≤ rect.height :=
    QuantBlock.Wd_anti rect (Nat.zero_le k)
  by_cases h : b = .LL
  · obtain ⟨_, _⟩ := ll h
    obtain ⟨_, _⟩ := axis nl
    exact ⟨hx, hy, by omega, by omega⟩
  · obtain ⟨_, _, _, _⟩ := detail h
    obtain ⟨_, _⟩ := axis (lvl - 1)
    exact ⟨hx, hy, by omega, by omega⟩

private theorem init_rel (rect : Rect) (nl : Nat) (rev : Bool) (F : Nat) :
    LoopRel rect nl rev F ⟨rect, Vector.replicate _ 0⟩ [] := by
  refine ⟨rfl, fun lvl b u v read inside => ?_⟩
  obtain ⟨_, _, hx, hy⟩ := mallat_bounds rect nl lvl b u v read inside
  have hi := JPEG2000.DWT53.idx_lt hx hy
  simp [entryAt, Vector.toArray_replicate, rectArea, hi]

private theorem step_rel {L : Limits} {rect : Rect} {p : CompParams} {depth red r F : Nat} {b : Band}
    {cb : Rect} {cs : Array Tier1.Coeff} {dst out : JPEG2000.WideQuant.Plane} {es : List Entry}
    (old : LoopRel rect (p.levels - red) (p.transform == .reversible53) F dst es)
    (ok : JPEG2000.WideQuant.dequantBlock L dst p depth red r b cb F (cs.map Tier1Wide.cellOf) =
      .ok out)
    (hr : r ≤ p.levels - red) (hb : b ∈ bandsOf r)
    (bounds : let br := bandRect rect (bandLevel (p.levels - red) r) b
              br.x0 ≤ cb.x0 ∧ br.y0 ≤ cb.y0 ∧ cb.x1 ≤ br.x1 ∧ cb.y1 ≤ br.y1)
    (hs : cs.size = rectArea cb)
    (base : ∀ x y, x < cb.width → y < cb.height →
      let c := cs.getD (y * cb.width + x) {}
      c.sig = false → c.mag = 0) :
    LoopRel rect (p.levels - red) (p.transform == .reversible53) F out
      (⟨r, b, cb, Quant.bandQuant p depth r b, cs⟩ :: es) := by
  obtain ⟨rfl, prev⟩ := old
  obtain ⟨eq, written⟩ := WideQuant.dequantBlock_read ok
  refine ⟨eq, fun lvl band u v read inside => ?_⟩
  let nl := p.levels - red
  let X := QuantBlock.mx dst.rect lvl band u
  let Y := QuantBlock.my dst.rect lvl band v
  let off := JPEG2000.WideQuant.blockOffset dst.rect nl r b cb
  obtain ⟨xn, yn, xlt, ylt⟩ := mallat_bounds dst.rect nl lvl band u v read inside
  change 0 ≤ X at xn
  change 0 ≤ Y at yn
  rw [QuantBlock.entryAt_cons]
  dsimp only
  by_cases hit : b = band ∧ bandLevel nl r = lvl ∧ (cb.x0 : Int) ≤ u ∧ u < cb.x1 ∧
      (cb.y0 : Int) ≤ v ∧ v < cb.y1
  · rw [ite_eq_left hit]
    obtain ⟨rfl, rfl, ux, ux', vy, vy'⟩ := hit
    let x := (u - cb.x0).toNat
    let y := (v - cb.y0).toNat
    have hx : x < cb.width := by simp only [x, Rect.width]; omega
    have hy : y < cb.height := by simp only [y, Rect.height]; omega
    let i := y * cb.width + x
    have hi : i < cs.size := by rw [hs]; exact JPEG2000.DWT53.idx_lt hx hy
    let c := cs.getD i {}
    have atCell : cs[i]? = some c := by
      simp [c, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]
    have h := WideQuant.dequantBlock_sample ok hr hb bounds x y hx hy c atCell (base x y hx hy)
    have ex : ((cb.x0 + x : Nat) : Int) = u := by dsimp [x]; omega
    have ey : ((cb.y0 + y : Nat) : Int) = v := by dsimp [y]; omega
    dsimp only at h
    rw [ex, ey] at h
    exact h
  · rw [ite_eq_right hit]
    have h := written X.toNat Y.toNat xlt ylt
    have miss : ¬(off.1 ≤ X.toNat ∧ X.toNat < off.1 + cb.width ∧
        off.2 ≤ Y.toNat ∧ Y.toNat < off.2 + cb.height) := by
      rintro ⟨h1, h2, h3, h4⟩
      let x := X.toNat - off.1
      let y := Y.toNat - off.2
      have hx : x < cb.width := by dsimp [x]; omega
      have hy : y < cb.height := by dsimp [y]; omega
      obtain ⟨rr, ri, xx, yy⟩ := QuantBlock.block_pos dst.rect nl r b cb hr hb
        bounds.1 bounds.2.1 bounds.2.2.1 bounds.2.2.2 x y hx hy
      change _ = ((off.1 + x : Nat) : Int) at xx
      change _ = ((off.2 + y : Nat) : Int) at yy
      have xe : ((off.1 + x : Nat) : Int) = X := by dsimp [x]; omega
      have ye : ((off.2 + y : Nat) : Int) = Y := by dsimp [y]; omega
      obtain ⟨el, eb, eu, ev⟩ := QuantBlock.mpos_inj dst.rect nl _ _ _ _ _ _ _ _
        rr ri read inside (xx.trans xe) (yy.trans ye)
      apply hit
      unfold Rect.width at hx
      unfold Rect.height at hy
      exact ⟨eb, el, by omega, by omega, by omega, by omega⟩
    rw [ite_eq_right miss] at h
    exact h.trans (prev lvl band u v read inside)

/-- The accumulation prefix of the independent specification. The spec lists carry the
packet body bytes. The result retains the counter used by the specification continuation. -/
def entries (L : Limits) (tc : TileCompGeom) (depth F reduce : Nat) (precs : Decode.SpecPrecs) :
    Except Error (List Entry × Nat) := do
  let p := tc.params
  let nl := p.levels
  if reduce > nl then
    throw (.unsupported Assemble.loc
      s!"resolution reduction {reduce} exceeds the {nl} decomposition levels of a tile-component")
  let nl' := nl - reduce
  let rect := Assemble.reduceRect tc.rect reduce
  let mut plane ← Decode.initSpec L rect.width rect.height
  let mut sat := 0
  for r in [0:min (nl' + 1) precs.length] do
    let ps := precs.getD r []
    for prec in ps do
      for bo in prec do
        for cb in bo.blocks do
          if cb.passes != 0 && !rectEmpty cb.geom.rect then
            let o ← decodeBlockSt p r bo.band cb
            let q := Spec.Quant.bandQuant p depth r bo.band
            let (pl, ok) ← Decode.collect plane rect nl' r bo.band cb.geom.rect q F o
            plane := pl
            if !ok then sat := sat + 1
  return (plane, sat)

/-- Feeding the collected entries to the spec continuation gives the actual spec
tile-component decoder on the same packets, including reduction and allocation errors. -/
theorem tileComp_eq_finish (L : Limits) (tc : TileCompGeom) (depth F red : Nat)
    (rs : Decode.SpecPrecs) :
    Decode.tileComp L tc depth F red rs =
      (entries L tc depth F red rs >>= fun s =>
        Decode.finSpec (tc.params.transform == .reversible53) s.1 (Assemble.reduceRect tc.rect red)
          (tc.params.levels - red) s.2) := by
  unfold Decode.tileComp entries
  dsimp only
  split
  · rfl
  · simp only [bind_assoc, pure_bind]

/-- Both computations issue the same error, or succeed with related accumulators. -/
def ResultRel {α β : Type} (R : α → β → Prop) : Except Error α → Except Error β → Prop
  | .ok a, .ok b => R a b
  | .error e, .error f => e = f
  | _, _ => False

-- A successful wide result always agrees. Only the converse needs the header bound.
private def Checked {α β : Type} (A : Prop) (R : α → β → Prop) :
    Except Error α → Except Error β → Prop
  | .error e, y => A → y = .error e
  | .ok a, .ok b => R a b
  | .ok _, .error _ => False

private theorem bind_rel {A : Prop} {α β γ δ : Type} {P : α → β → Prop} {Q : γ → δ → Prop}
    {x : Except Error α} {y : Except Error β} {f : α → Except Error γ} {g : β → Except Error δ}
    (h : Checked A P x y) (step : ∀ a b, P a b → Checked A Q (f a) (g b)) :
    Checked A Q (x >>= f) (y >>= g) := by
  match x, y with
  | .error e, .error f => intro admitted; cases h admitted; rfl
  | .error e, .ok b => intro admitted; cases h admitted
  | .ok a, .error f => exact False.elim h
  | .ok a, .ok b => exact step a b h

private theorem for_list {A : Prop} {α β γ : Type} {R : α → β → Prop} (xs : List γ)
    (f : γ → α → Except Error (ForInStep α)) (g : γ → β → Except Error (ForInStep β))
    (step : ∀ x ∈ xs, ∀ a b, R a b → Checked A (Equiv.StepRel R) (f x a) (g x b))
    (a : α) (b : β) (h : R a b) : Checked A R (forIn xs a f) (forIn xs b g) := by
  induction xs generalizing a b with
  | nil => exact h
  | cons x xs ih =>
    simp only [List.forIn_cons]
    apply bind_rel (step x List.mem_cons_self a b h)
    intro s t hs
    cases s <;> cases t <;> simp only [Equiv.StepRel] at hs
    · exact hs
    · exact ih (fun y hy => step y (List.mem_cons_of_mem _ hy)) _ _ hs

private theorem for_array {A : Prop} {α β γ : Type} {R : α → β → Prop} (xs : Array γ)
    (f : γ → α → Except Error (ForInStep α)) (g : γ → β → Except Error (ForInStep β))
    (step : ∀ x ∈ xs, ∀ a b, R a b → Checked A (Equiv.StepRel R) (f x a) (g x b))
    (a : α) (b : β) (h : R a b) : Checked A R (forIn xs a f) (forIn xs b g) := by
  rw [← Array.forIn_toList, ← Array.forIn_toList]
  exact for_list _ _ _ (fun x hx => step x (by simpa using hx)) a b h

private theorem for_range {A : Prop} {α β : Type} {R : α → β → Prop} (n : Nat)
    (f : Nat → α → Except Error (ForInStep α)) (g : Nat → β → Except Error (ForInStep β))
    (step : ∀ r, r < n → ∀ a b, R a b → Checked A (Equiv.StepRel R) (f r a) (g r b))
    (a : α) (b : β) (h : R a b) : Checked A R (forIn [0:n] a f) (forIn [0:n] b g) := by
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  apply for_list _ _ _ _ _ _ h
  intro i hi
  apply step
  simpa [Std.Legacy.Range.size, ← List.range_eq_range'] using hi

private theorem tileComp_compare {A : Prop} (L : Limits) (data : ByteArray) (tc : TileCompGeom) (depth F red : Nat)
    (precs : Array (Array PrecinctOut))
    (levels : tc.params.levels ≤ L.maxDecompLevels)
    (ordered : let z := Assemble.reduceRect tc.rect red
               z.x0 ≤ z.x1 ∧ z.y0 ≤ z.y1)
    (planes : A → ∀ r b, r ≤ tc.params.levels - red → b ∈ bandsOf r →
      bandMb tc.params r b + tc.params.roiShift ≤ JPEG2000.Tier1.WidePlain.maxCodedPlanes)
    (wf : Equiv.PrecsWF tc precs) (ranges : Equiv.BlocksIn data precs) :
    Checked A (fun pl s => LoopRel (Assemble.reduceRect tc.rect red) (tc.params.levels - red)
      (tc.params.transform == .reversible53) F pl s.1 ∧ s.2 = 0)
      (JPEG2000.WideAssembly.tileComp L data tc depth F red precs)
      (entries L tc depth F red (Equiv.imagePrecs data precs)) := by
  unfold JPEG2000.WideAssembly.tileComp entries
  dsimp only
  split
  · intro _; rfl
  · rename_i hred
    let rect := Assemble.reduceRect tc.rect red
    let nl := tc.params.levels - red
    let R := fun (pl : JPEG2000.WideQuant.Plane) (s : List Entry × Nat) =>
      LoopRel rect nl (tc.params.transform == .reversible53) F pl s.1 ∧ s.2 = 0
    simp only [(Limits.check_eq_ok_iff L Assemble.loc .decompLevels _).2 levels, pure_bind,
      Decode.initSpec, bind_assoc]
    cases budget : L.check Assemble.loc .workSamples (rectArea rect) with
    | error e =>
      have budget' : L.check Assemble.loc .workSamples (rect.width * rect.height) = .error e := budget
      rw [budget']
      intro _; rfl
    | ok z =>
      cases z
      have area := (Limits.check_eq_ok_iff ..).1 budget
      have alloc := (WideQuant.zeroChecked_eq L rect ordered.1 ordered.2).2 area
      have budget' : L.check Assemble.loc .workSamples (rect.width * rect.height) = .ok () := budget
      rw [budget']
      simp only [Equiv.ok_bind]
      rw [alloc]
      simp only [Equiv.ok_bind, JPEG2000.WideAssembly.visitBlocks,
        Equiv.imagePrecs_getD, List.forIn_map, Array.forIn_toList]
      simp only [Equiv.imagePrecs, List.length_map, Array.length_toList, Tier2Equiv.imageBand,
        List.forIn_map, Array.forIn_toList]
      refine bind_rel (P := R) ?_ (by intro a s h; exact h)
      apply for_range _ _ _ _ _ _ (show R _ ([], 0) from ⟨init_rel .., rfl⟩)
      intro r hr a s inv
      have hr' : r ≤ nl := by dsimp [nl]; omega
      have hrs : r < precs.size := by omega
      refine bind_rel (P := R) ?_ (by intro a s h; exact h)
      apply for_array _ _ _ _ _ _ inv
      intro prec hprec a s inv
      refine bind_rel (P := R) ?_ (by intro a s h; exact h)
      apply for_array _ _ _ _ _ _ inv
      intro bo hbo a s inv
      obtain ⟨hb, bound⟩ := wf r hrs prec hprec bo hbo
      refine bind_rel (P := R) ?_ (by intro a s h; exact h)
      apply for_array _ _ _ _ _ _ inv
      intro cb hcb a s inv
      simp only [show (Tier2Equiv.blockOf data cb).passes = cb.numPasses from rfl,
        show (Tier2Equiv.blockOf data cb).geom = cb.geom from rfl]
      by_cases active : (cb.numPasses != 0 && !rectEmpty cb.geom.rect) = true
      · simp only [active, ↓reduceIte]
        have splitBytes := ranges r prec hprec bo hbo cb hcb
        rcases block_alternatives data tc.params r bo.band cb splitBytes with eq | ⟨e, failed, big⟩
        case inr =>
          rw [failed]
          intro admitted
          exact False.elim ((Nat.not_lt.mpr (Nat.le_trans (Nat.sub_le ..)
            (planes admitted r bo.band hr' hb))) big)
        rw [eq]
        cases decoded : decodeBlockSt tc.params r bo.band (Tier2Equiv.blockOf data cb) with
        | error e => intro _; rfl
        | ok cs =>
          obtain ⟨hs, base⟩ := blockSt_raster _ _ _ _ _ decoded
          obtain ⟨old, sat⟩ := inv
          have br := WideQuant.reduced_band tc.rect tc.params.levels red r bo.band
            (Nat.le_of_not_lt hred) hr' hb
          have bounds := bound cb hcb
          rw [← br] at bounds
          have ne : 0 < cb.geom.rect.width ∧ 0 < cb.geom.rect.height := by
            simp only [Bool.and_eq_true, Bool.not_eq_true'] at active
            have limits : cb.geom.rect.x0 < cb.geom.rect.x1 ∧ cb.geom.rect.y0 < cb.geom.rect.y1 := by
              simpa [rectEmpty] using active.2
            simp only [Rect.width, Rect.height]
            omega
          obtain ⟨out, ok⟩ := WideQuant.dequantBlock_succeeds (L := L) (dst := a)
            (p := tc.params) (red := red) (depth := depth) (F := F) (r := r) (b := bo.band)
            (cb := cb.geom.rect) (cs := cs.map Tier1Wide.cellOf) (by rw [old.1]; exact area)
            levels (Nat.le_of_not_lt hred) hr' hb (by rw [old.1]; exact bounds) ne.1 ne.2
            (by rw [Array.size_map]; exact hs)
          simp only [Except.map, Equiv.ok_bind, Decode.collect, pure_bind, Bool.not_true,
            Bool.false_eq_true, ↓reduceIte, ok]
          exact ⟨step_rel old ok hr' hb bounds hs base, sat⟩
      · simp only [active]
        exact inv

/-- The checked coefficient stage and the spec's entry collector agree on errors and
on every retained band position. The header hypotheses concern the signalled fields,
and the packet hypotheses concern the real byte ranges and rectangles. -/
theorem tileComp_equiv (L : Limits) (data : ByteArray) (tc : TileCompGeom) (depth F red : Nat)
    (precs : Array (Array PrecinctOut))
    (levels : tc.params.levels ≤ L.maxDecompLevels)
    (ordered : let z := Assemble.reduceRect tc.rect red
               z.x0 ≤ z.x1 ∧ z.y0 ≤ z.y1)
    (planes : ∀ r b, r ≤ tc.params.levels - red → b ∈ bandsOf r →
      bandMb tc.params r b + tc.params.roiShift ≤ JPEG2000.Tier1.WidePlain.maxCodedPlanes)
    (wf : Equiv.PrecsWF tc precs) (ranges : Equiv.BlocksIn data precs) :
    ResultRel (fun pl s => LoopRel (Assemble.reduceRect tc.rect red) (tc.params.levels - red)
      (tc.params.transform == .reversible53) F pl s.1 ∧ s.2 = 0)
      (JPEG2000.WideAssembly.tileComp L data tc depth F red precs)
      (entries L tc depth F red (Equiv.imagePrecs data precs)) := by
  have rel := tileComp_compare (A := True) L data tc depth F red precs levels ordered
    (fun _ => planes) wf ranges
  revert rel
  cases JPEG2000.WideAssembly.tileComp L data tc depth F red precs <;>
    cases entries L tc depth F red (Equiv.imagePrecs data precs) <;>
    simp [Checked, ResultRel, eq_comm]

private theorem successful_limits {L : Limits} {data : ByteArray} {tc : TileCompGeom}
    {depth F red : Nat} {ps : Array (Array PrecinctOut)} {pl : JPEG2000.WideQuant.Plane}
    (ok : JPEG2000.WideAssembly.tileComp L data tc depth F red ps = .ok pl) :
    tc.params.levels ≤ L.maxDecompLevels ∧
      let z := Assemble.reduceRect tc.rect red
      z.x0 ≤ z.x1 ∧ z.y0 ≤ z.y1 := by
  unfold JPEG2000.WideAssembly.tileComp at ok
  dsimp only at ok
  split at ok
  · contradiction
  · cases hl : L.check Assemble.loc .decompLevels tc.params.levels with
    | error e => simp [hl, bind, Except.bind] at ok
    | ok u =>
      cases u
      refine ⟨(Limits.check_eq_ok_iff ..).1 hl, ?_⟩
      cases hw : L.check Assemble.loc .workSamples (rectArea (Assemble.reduceRect tc.rect red)) with
      | error e => simp [hl, hw, bind, Except.bind] at ok
      | ok u =>
        cases u
        have hw' : L.check JPEG2000.Quant.loc .workSamples (rectArea (Assemble.reduceRect tc.rect red)) = .ok () :=
          (Limits.check_eq_ok_iff ..).2 ((Limits.check_eq_ok_iff ..).1 hw)
        simp only [hl, hw, Equiv.ok_bind, JPEG2000.WideQuant.zeroChecked, hw'] at ok
        split at ok <;> first | contradiction | omega

/-- Every returned plane agrees with the independent spec entries, with no premise
on the coded-plane count, component precision or budgets. Only the packet geometry
and in-stream byte ranges of the Tier-2 store are needed. -/
theorem tileComp_sound {L : Limits} {data : ByteArray} {tc : TileCompGeom} {depth F red : Nat}
    {ps : Array (Array PrecinctOut)} {pl : JPEG2000.WideQuant.Plane}
    (wf : Equiv.PrecsWF tc ps) (ranges : Equiv.BlocksIn data ps)
    (ok : JPEG2000.WideAssembly.tileComp L data tc depth F red ps = .ok pl) :
    ∃ es, entries L tc depth F red (Equiv.imagePrecs data ps) = .ok (es, 0) ∧
      LoopRel (Assemble.reduceRect tc.rect red) (tc.params.levels - red)
        (tc.params.transform == .reversible53) F pl es := by
  obtain ⟨levels, ordered⟩ := successful_limits ok
  have rel := tileComp_compare (A := False) L data tc depth F red ps levels ordered
    False.elim wf ranges
  rw [ok] at rel
  cases collected : entries L tc depth F red (Equiv.imagePrecs data ps) with
  | error e => rw [collected] at rel; exact False.elim rel
  | ok s =>
    rw [collected] at rel
    obtain ⟨es, sat⟩ := s
    obtain ⟨h, rfl⟩ := rel
    exact ⟨es, rfl, h⟩

/-- Read the exact reversible spec band at its Mallat array address. -/
theorem bandGrid53_eq {rect : Rect} {nl F : Nat} {pl : JPEG2000.WideQuant.Plane} {es : List Entry}
    (h : LoopRel rect nl true F pl es) (lvl : Nat) (b : Band) (u v : Int)
    (read : Equiv.ReadBand nl lvl b) (inside : Equiv.InBand rect lvl b u v) :
    pl.samples.toArray[(QuantBlock.my rect lvl b v).toNat * rect.width +
        (QuantBlock.mx rect lvl b u).toNat]? = some ((bandGrid53 es nl lvl b).get u v) := by
  rw [h.2 lvl b u v read inside]
  dsimp only [Decode.bandGrid53]
  cases entryAt es nl lvl b u v <;> rfl

/-- At an irreversible spec band position the stored integer differs from the exact
scaled rational by at most half a working unit. Uncovered positions have value zero. -/
theorem bandGrid97_close {rect : Rect} {nl F : Nat} {pl : JPEG2000.WideQuant.Plane}
    {es : List Entry} (h : LoopRel rect nl false F pl es) (lvl : Nat) (b : Band) (u v : Int)
    (read : Equiv.ReadBand nl lvl b) (inside : Equiv.InBand rect lvl b u v) :
    ∃ z : Int, pl.samples.toArray[(QuantBlock.my rect lvl b v).toNat * rect.width +
      (QuantBlock.mx rect lvl b u).toNat]? = some z ∧
      ((z : Rat) - (bandGrid97 es nl lvl b).get u v * ((2 ^ F : Nat) : Rat)).abs ≤ 1/2 := by
  refine ⟨_, h.2 lvl b u v read inside, ?_⟩
  dsimp only [Decode.bandGrid97]
  cases entryAt es nl lvl b u v with
  | none =>
    simp
    apply Spec.DWT97.abs_le_iff.mpr
    constructor <;> grind
  | some e =>
    dsimp only [Option.map_some, Option.getD_some, entryValue, Bool.false_eq_true, ↓reduceIte,
      Quant.dequantIrrevScaled]
    generalize Quant.dequantIrrev _ _ _ * _ = t
    apply Spec.DWT97.abs_le_iff.mpr
    cases (e.coeff u v).sign <;>
      simp only [WideQuant.roundSigned, Decode.roundHalf, Bool.false_eq_true, ↓reduceIte]
    · have := Rat.floor_le (t + 1/2)
      have := Rat.lt_floor_add_one (t + 1/2)
      grind
    · have := Rat.floor_le (-t + 1/2)
      have := Rat.lt_floor_add_one (-t + 1/2)
      grind

private theorem packet_component {L : Limits} {data : ByteArray} {h : Header} {tp : TileParams}
    {hs : Option JPEG2000.Tier2.Headers.HeaderStream} {n : Nat} {store : TileCodeBlocks}
    (parsed : Header.parse L data = .ok h)
    (packets : JPEG2000.Tier2.Headers.decodeWithStream L h data tp hs n = .ok store) (c : Nat) :
    ∃ st, Spec.Tier2.decodeWithStream L h data tp hs n = .ok st ∧
      st.comps.getD c [] = Equiv.imagePrecs data (store.comps.getD c #[]) := by
  have sim := Tier2Equiv.tier2_equiv_of_siz L h data tp hs n (Equiv.parse_dxdy parsed)
  rw [packets] at sim
  cases result : Spec.Tier2.decodeWithStream L h data tp hs n with
  | error e => rw [result] at sim; exact False.elim sim
  | ok st =>
    rw [result] at sim
    exact ⟨st, rfl, by rw [sim.1, Equiv.image_getD]⟩

/-- Correspondence for a real tile and component. Parsing supplies nonzero subsampling,
the layout and the Tier-2 simulation supply the actual spec packet store, and the
packet decoder establishes every byte-range and code-block containment premise. -/
theorem parsed_component {L : Limits} {data : ByteArray} {h : Header} {tp : TileParams}
    {hs : Option JPEG2000.Tier2.Headers.HeaderStream} {n : Nat} {store : TileCodeBlocks}
    {layout : Progression.Layout} {coding : Coding}
    (parsed : Header.parse L data = .ok h)
    (layoutOk : Progression.Layout.ofHeader h tp.index = .ok (layout, coding))
    (packets : JPEG2000.Tier2.Headers.decodeWithStream L h data tp hs n = .ok store)
    (c : Fin layout.numComps) (red : Nat)
    (levels : (layout.comp c).params.levels ≤ L.maxDecompLevels)
    (ordered : let z := Assemble.reduceRect (layout.comp c).rect red
               z.x0 ≤ z.x1 ∧ z.y0 ≤ z.y1)
    (guard : (layout.comp c).params.guardBits ≤ 7) (roi : (layout.comp c).params.roiShift ≤ 255)
    (exponents : ∀ step ∈ (layout.comp c).params.steps, step.exponent.toNat ≤ 31) :
    let tc := layout.comp c
    let depth := (h.siz.components.getD c default).depth.toNat
    let F := Assemble.fracBitsOf h.siz (coding.mctApplies h.siz) c
    ∃ specStore, Spec.Tier2.decodeWithStream L h data tp hs n = .ok specStore ∧
      ResultRel (fun pl s => LoopRel (Assemble.reduceRect tc.rect red) (tc.params.levels - red)
        (tc.params.transform == .reversible53) F pl s.1 ∧ s.2 = 0)
        (JPEG2000.WideAssembly.component L data h.siz layout coding (some store) c red)
        (entries L tc depth F red (specStore.comps.getD c [])) := by
  have wf := Tier2WF.tier2WF L h data tp hs n store packets
  obtain ⟨st, result, image⟩ := packet_component parsed packets c
  refine ⟨st, result, ?_⟩
  rw [image]
  apply tileComp_equiv _ _ _ _ _ _ _ levels ordered _ (wf.1 _ _ layoutOk c) (wf.2 c)
  intro r b _ _
  unfold bandMb
  let idx := if r = 0 then 0 else 3 * (r - 1) + b.index
  have exp : ((layout.comp c).params.steps.getD idx default).exponent.toNat ≤ 31 := by
    simp only [Array.getD_eq_getD_getElem?]
    cases step : (layout.comp c).params.steps[idx]? with
    | none => decide
    | some s => exact exponents s (Array.mem_of_getElem? step)
  exact Tier1Wide.codedPlanes_le_of_header _ _ _ 0 guard exp roi

/-- A successful real packet and component decode supplies the spec store, its actual
collected entries and the band-grid relation without any separate header, geometry,
budget, style, or insignificant-coefficient hypothesis. -/
theorem parsed_component_ok {L : Limits} {data : ByteArray} {h : Header} {tp : TileParams}
    {hs : Option JPEG2000.Tier2.Headers.HeaderStream} {n : Nat} {store : TileCodeBlocks}
    {layout : Progression.Layout} {coding : Coding} {pl : JPEG2000.WideQuant.Plane}
    (parsed : Header.parse L data = .ok h)
    (layoutOk : Progression.Layout.ofHeader h tp.index = .ok (layout, coding))
    (packets : JPEG2000.Tier2.Headers.decodeWithStream L h data tp hs n = .ok store)
    (c : Fin layout.numComps) (red : Nat)
    (ok : JPEG2000.WideAssembly.component L data h.siz layout coding (some store) c red = .ok pl) :
    let tc := layout.comp c
    let depth := (h.siz.components.getD c default).depth.toNat
    let F := Assemble.fracBitsOf h.siz (coding.mctApplies h.siz) c
    ∃ specStore es, Spec.Tier2.decodeWithStream L h data tp hs n = .ok specStore ∧
      entries L tc depth F red (specStore.comps.getD c []) = .ok (es, 0) ∧
      LoopRel (Assemble.reduceRect tc.rect red) (tc.params.levels - red)
        (tc.params.transform == .reversible53) F pl es := by
  have wf := Tier2WF.tier2WF L h data tp hs n store packets
  obtain ⟨st, result, image⟩ := packet_component parsed packets c
  obtain ⟨es, collected, rel⟩ := tileComp_sound (wf.1 _ _ layoutOk c) (wf.2 c) ok
  exact ⟨st, es, result, by rw [image]; exact collected, rel⟩

-- A fragmented segment would lose its invalid final piece during ByteArray.extract.
-- The original range check sees it even though the zero-plane block would drop its passes.
private def fragmented : CodeBlock :=
  { geom := ⟨0, 0, 0, ⟨0, 0, 1, 1⟩⟩, numPasses := 1,
    segments := #[{ passes := 1, ranges := #[⟨0, 1⟩, ⟨8, 1⟩] }] }

private def failure {α : Type} : Except Error α → Option Error
  | .error e => some e
  | .ok _ => none

example : failure (JPEG2000.WideAssembly.decodeBlock ⟨#[0]⟩ default 0 .LL fragmented) =
    some (.malformed JPEG2000.Tier1.tier1Loc "code-block data range outside the buffer") := by
  decide +kernel

private def skipped (L : Limits) : Except Error (Array Int) :=
  let tc : TileCompGeom := { (default : TileCompGeom) with rect := ⟨1, 1, 3, 2⟩ }
  let empty := { fragmented with geom.rect := ⟨1, 1, 1, 2⟩ }
  let absent := { fragmented with numPasses := 0 }
  let prec : PrecinctOut := ⟨0, #[⟨.LL, tc.rect, 0, #[empty, absent]⟩]⟩
  (JPEG2000.WideAssembly.tileComp L ⟨#[0]⟩ tc 8 0 0 #[#[prec]]).map (·.samples.toArray)

-- Neither skipped block reads its invalid ranges. Budget admission still covers both cells.
example : (skipped Limits.default).toOption = some #[0, 0] ∧
    failure (skipped { Limits.default with maxWorkSamples := 1 }) =
      some (.limitExceeded Assemble.loc .workSamples 2 1) := by decide +kernel

end JPEG2000.Spec.WideAssembly
