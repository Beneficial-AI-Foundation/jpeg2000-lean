import Spec.Tier1Equiv.Modes

/-!
# C3 for every code-block style, strict segmentation symbols

Plan.md §4 (C3), §5.2 "Tier-1 / EBCOT"; T.800 D.5 (segmentation symbols). Task 7.1c.

`c3_all_strict_exact` (`c3_all_strict` in `Spec.Tier1Equiv.Clamp` after task 5.8): the strict pair `JPEG2000.Tier1.decodeCodeBlockSegsStrictExact` /
`Spec.Tier1.decodeCodeBlockStrictExact` (a segmentation symbol other than `1010` is an error) agrees
exactly as the lenient pair of `c3_all`. On top of `c3_all` it needs that the fast count of bad
symbols is the spec's `badSegSymbols`:

* the spec passes, segment starts and resets never change `badSegSymbols` (`…_bad` lemmas);
* the fast and spec segmentation symbols decode the same four bits (`segSymbol_both`);
* hence the count is carried through `runPassM`, `runPassesM`, `runSegs` (`runSegs_both`);
* a plain-like style never counts (`decodeSegments_bad_noSeg`), and the fast plain path
  returns 0.
-/

namespace JPEG2000.Spec.Tier1EquivM

open JPEG2000
open JPEG2000.Bytes (Plane)
open JPEG2000.Tier2.Geometry (Band)
open JPEG2000.Spec.Tier1 (Coeff Geom DecState RawState Mode CodeBlock)
open JPEG2000.Spec.Tier1Equiv

/-! ## The spec passes keep the count -/

section spec
variable (g : Geom)

/-- A decision keeps the count. -/
theorem decodeBit_bad (d : DecState) (cx : Nat) :
    (d.decodeBit cx).2.badSegSymbols = d.badSegSymbols := by rw [decodeBit_eq]

/-- `becomeSignificant` keeps the count. -/
theorem becomeSignificant_bad (p : Nat) (vis : Bool) (d : DecState) (x y : Nat) :
    (Spec.Tier1.becomeSignificant g p vis d x y).badSegSymbols = d.badSegSymbols := by
  simp only [Spec.Tier1.becomeSignificant, Spec.Tier1.decodeSign]
  generalize g.signContext d.coeffs x y = sc
  obtain ⟨cx, xb⟩ := sc
  simp only [decodeBit_eq]

/-- `zeroCode` keeps the count. -/
theorem zeroCode_bad (p : Nat) (vis : Bool) (d : DecState) (x y : Nat) :
    (Spec.Tier1.zeroCode g p vis d x y).badSegSymbols = d.badSegSymbols := by
  simp only [Spec.Tier1.zeroCode, decodeBit_eq]
  split
  · rw [becomeSignificant_bad]
  · rfl

/-- A fold of count-keeping steps keeps the count. -/
theorem foldl_bad {α : Type} (step : DecState → α → DecState)
    (h : ∀ d a, (step d a).badSegSymbols = d.badSegSymbols) :
    ∀ (l : List α) (d : DecState), (l.foldl step d).badSegSymbols = d.badSegSymbols := by
  intro l
  induction l with
  | nil => intro d; rfl
  | cons a l ih => intro d; simp only [List.foldl_cons]; rw [ih, h]

/-- The significance propagation pass keeps the count. -/
theorem sigPropPass_bad (p : Nat) (d : DecState) :
    (Spec.Tier1.sigPropPass g p d).badSegSymbols = d.badSegSymbols := by
  unfold Spec.Tier1.sigPropPass
  refine foldl_bad _ (fun d pos => ?_) _ d
  obtain ⟨x, y⟩ := pos
  simp only [Spec.Tier1.sigPropStep]
  split
  · exact zeroCode_bad g p true d x y
  · rfl

/-- The magnitude refinement pass keeps the count. -/
theorem magRefPass_bad (p : Nat) (d : DecState) :
    (Spec.Tier1.magRefPass g p d).badSegSymbols = d.badSegSymbols := by
  unfold Spec.Tier1.magRefPass
  refine foldl_bad _ (fun d pos => ?_) _ d
  obtain ⟨x, y⟩ := pos
  simp only [Spec.Tier1.magRefStep, decodeBit_eq]
  split <;> rfl

/-- The raw significance propagation pass keeps the count. -/
theorem rawSigPropPass_bad (p : Nat) (d : DecState) :
    (Spec.Tier1.rawSigPropPass g p d).badSegSymbols = d.badSegSymbols := by
  unfold Spec.Tier1.rawSigPropPass
  refine foldl_bad _ (fun d pos => ?_) _ d
  obtain ⟨x, y⟩ := pos
  simp only [Spec.Tier1.rawSigPropStep, rawBit_eq]
  split
  · split <;> rfl
  · rfl

/-- The raw magnitude refinement pass keeps the count. -/
theorem rawMagRefPass_bad (p : Nat) (d : DecState) :
    (Spec.Tier1.rawMagRefPass g p d).badSegSymbols = d.badSegSymbols := by
  unfold Spec.Tier1.rawMagRefPass
  refine foldl_bad _ (fun d pos => ?_) _ d
  obtain ⟨x, y⟩ := pos
  simp only [Spec.Tier1.rawMagRefStep, rawBit_eq]
  split <;> rfl

/-- The cleanup pass keeps the count. -/
theorem cleanupPass_bad (p : Nat) (d : DecState) :
    (Spec.Tier1.cleanupPass g p d).badSegSymbols = d.badSegSymbols := by
  unfold Spec.Tier1.cleanupPass
  have hstep : ∀ d pos, (Spec.Tier1.cleanupStep g p d pos).badSegSymbols = d.badSegSymbols := by
    intro d pos
    obtain ⟨x, y⟩ := pos
    simp only [Spec.Tier1.cleanupStep]
    split
    · exact zeroCode_bad g p false d x y
    · rfl
  show ((Spec.Tier1.stripeColumns g.width g.height).foldl (Spec.Tier1.cleanupColumn g p) d).badSegSymbols = _
  refine foldl_bad _ (fun d col => ?_) _ d
  unfold Spec.Tier1.cleanupColumn
  split
  · simp only [decodeBit_eq]
    split
    · rfl
    · split
      · rfl
      · rw [foldl_bad _ hstep, becomeSignificant_bad]
  · exact foldl_bad _ hstep _ _

/-- One plain or raw pass keeps the count. -/
theorem pass_bad (md : Mode) (K : Nat) (d : DecState) (i : Nat) :
    (if Spec.Tier1.isRawPass md i then Spec.Tier1.runRawPass g K d i
     else Spec.Tier1.runPass g K d i).badSegSymbols = d.badSegSymbols := by
  split
  · unfold Spec.Tier1.runRawPass
    split
    · exact rawSigPropPass_bad g _ d
    · exact rawMagRefPass_bad g _ d
    · exact cleanupPass_bad g _ d
  · unfold Spec.Tier1.runPass
    split
    · exact sigPropPass_bad g _ d
    · exact magRefPass_bad g _ d
    · exact cleanupPass_bad g _ d

/-- Without segmentation symbols, a decode never counts. -/
theorem decodeSegments_bad_noSeg (md : Mode) (hs : md.segSymbols = false) (K : Nat) :
    ∀ (L : List Spec.Tier1.Segment) i (d : DecState),
      (Spec.Tier1.decodeSegments md g K L i d).badSegSymbols = d.badSegSymbols := by
  have hp : ∀ d i, (Spec.Tier1.runPassM md g K d i).badSegSymbols = d.badSegSymbols := by
    intro d i
    unfold Spec.Tier1.runPassM
    simp only [hs, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    split
    · exact pass_bad g md K d i
    · exact pass_bad g md K d i
  intro L
  induction L with
  | nil => intro i d; rfl
  | cons sg rest ih =>
    intro i d
    simp only [Spec.Tier1.decodeSegments]
    rw [ih, foldl_bad _ hp]
    unfold Spec.Tier1.startSegment; split <;> rfl

end spec

/-! ## The fast count -/

/-- The count after a fast `runPassM`. -/
theorem runPassM_snd (m : JPEG2000.Tier1.Style) (g : JPEG2000.Tier1.Geo) (K : Nat)
    (s : JPEG2000.Tier1.St) (bad i : Nat) :
    (JPEG2000.Tier1.runPassM m g K s bad i).2 =
      (if (m.segSymbols && JPEG2000.Tier1.passKind i == 2) = true then
        (JPEG2000.Tier1.segSymbol (passF m g K s i) bad).2 else bad) := by
  unfold JPEG2000.Tier1.runPassM passF
  dsimp only
  by_cases c2 : (m.segSymbols && JPEG2000.Tier1.passKind i == 2) = true <;>
    simp only [c2, ↓reduceIte, Bool.false_eq_true] <;>
    by_cases c1 : JPEG2000.Tier1.isRawPass m i = true <;>
    simp only [c1, ↓reduceIte, Bool.false_eq_true] <;>
    by_cases c3 : m.reset = true <;> simp only [c3, ↓reduceIte, Bool.false_eq_true] <;> rfl

section fast
variable {w h : Nat} {b : Band} {vc : Bool} {start : Nat}

/-- **The segmentation symbol, count included**: both sides decode the same four bits. -/
theorem segSymbol_bad {s : JPEG2000.Tier1.St} {d : DecState}
    (R : RelM w h b vc start false s d) (bad : Nat) (hb : bad = d.badSegSymbols) :
    (JPEG2000.Tier1.segSymbol s bad).2 = (Spec.Tier1.segSymbol d).badSegSymbols := by
  obtain ⟨mq, fl, mags⟩ := s
  have hc18 : Spec.Tier1.ctxUniform = 18 := rfl
  unfold JPEG2000.Tier1.segSymbol Spec.Tier1.segSymbol
  simp only [hc18]
  obtain ⟨e1, R1⟩ := decode_relM R 18
  have b1 := decodeBit_bad d 18
  generalize mq.decode 18 = rf at e1 R1 ⊢
  generalize d.decodeBit 18 = rs at e1 R1 b1 ⊢
  obtain ⟨b3, mq1⟩ := rf
  obtain ⟨bs3, d1⟩ := rs
  simp only at e1 R1 b1 ⊢
  subst e1
  obtain ⟨e2, R2⟩ := decode_relM R1 18
  have b2 := decodeBit_bad d1 18
  generalize mq1.decode 18 = rf at e2 R2 ⊢
  generalize d1.decodeBit 18 = rs at e2 R2 b2 ⊢
  obtain ⟨b2', mq2⟩ := rf
  obtain ⟨bs2, d2⟩ := rs
  simp only at e2 R2 b2 ⊢
  subst e2
  obtain ⟨e3, R3⟩ := decode_relM R2 18
  have b3' := decodeBit_bad d2 18
  generalize mq2.decode 18 = rf at e3 R3 ⊢
  generalize d2.decodeBit 18 = rs at e3 R3 b3' ⊢
  obtain ⟨b1', mq3⟩ := rf
  obtain ⟨bs1, d3⟩ := rs
  simp only at e3 R3 b3' ⊢
  subst e3
  obtain ⟨e4, R4⟩ := decode_relM R3 18
  have b4 := decodeBit_bad d3 18
  generalize mq3.decode 18 = rf at e4 R4 ⊢
  generalize d3.decodeBit 18 = rs at e4 R4 b4 ⊢
  obtain ⟨b0, mq4⟩ := rf
  obtain ⟨bs0, d4⟩ := rs
  simp only at e4 R4 b4 ⊢
  subst e4
  have hd4 : d4.badSegSymbols = d.badSegSymbols := by rw [b4, b3', b2, b1]
  split <;> simp [hd4, hb]

variable {m : JPEG2000.Tier1.Style} {md : Mode}

/-- **One pass, count included.** -/
theorem runPassM_bad (hm : StyleRel m md) (hvc : m.vertCausal = vc) (K : Nat) (hK : K ≤ 32)
    (s : JPEG2000.Tier1.St) (d : DecState) (bad i : Nat)
    (R : RelM w h b vc start (Spec.Tier1.isRawPass md i) s d) (hb : bad = d.badSegSymbols) :
    (JPEG2000.Tier1.runPassM m (fgeo w h b) K s bad i).2 =
      (Spec.Tier1.runPassM md (gV w h b vc) K d i).badSegSymbols := by
  rw [runPassM_snd]
  unfold Spec.Tier1.runPassM
  dsimp only
  have P := passF_rel hm hvc K hK s d i R
  have hD := pass_bad (gV w h b vc) md K d i
  generalize passF m (fgeo w h b) K s i = S at P ⊢
  generalize (if Spec.Tier1.isRawPass md i = true then Spec.Tier1.runRawPass (gV w h b vc) K d i
    else Spec.Tier1.runPass (gV w h b vc) K d i) = D at P hD ⊢
  have hcond : (m.segSymbols && JPEG2000.Tier1.passKind i == 2) =
      (md.segSymbols && Spec.Tier1.passKind i == .cleanup) := by
    rw [hm.segSymbols]
    rcases passKind_cases i with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> simp [e1, e2]
  rw [hcond]
  have S2 : (if (md.segSymbols && Spec.Tier1.passKind i == .cleanup) = true then
        (JPEG2000.Tier1.segSymbol S bad).2 else bad) =
      (if (md.segSymbols && Spec.Tier1.passKind i == .cleanup) = true then
        Spec.Tier1.segSymbol D else D).badSegSymbols := by
    split
    · rename_i hc
      have hk : Spec.Tier1.passKind i = .cleanup := by
        simp only [Bool.and_eq_true, beq_iff_eq] at hc; exact hc.2
      have hr : Spec.Tier1.isRawPass md i = false := by
        unfold Spec.Tier1.isRawPass; simp [hk]
      rw [hr] at P
      exact segSymbol_bad P bad (by rw [hb, hD])
    · rw [hb, hD]
  rw [S2]
  by_cases hr : md.reset = true <;> simp only [hr, ↓reduceIte, Bool.false_eq_true]

/-- **A run of passes, count included.** -/
theorem runPassesM_both (hm : StyleRel m md) (hvc : m.vertCausal = vc) (K : Nat) (hK : K ≤ 32)
    (raw : Bool) :
    ∀ n s bad d i, (∀ q < n, Spec.Tier1.isRawPass md (i + q) = raw) →
      RelM w h b vc start raw s d → bad = d.badSegSymbols →
      RelM w h b vc start raw (JPEG2000.Tier1.runPassesM m (fgeo w h b) K n s bad i).1
        ((List.range' i n).foldl (Spec.Tier1.runPassM md (gV w h b vc) K) d) ∧
      (JPEG2000.Tier1.runPassesM m (fgeo w h b) K n s bad i).2 =
        ((List.range' i n).foldl (Spec.Tier1.runPassM md (gV w h b vc) K) d).badSegSymbols := by
  intro n
  induction n with
  | zero => intro s bad d i _ R hb; exact ⟨R, hb⟩
  | succ n ih =>
    intro s bad d i hr R hb
    have e : JPEG2000.Tier1.runPassesM m (fgeo w h b) K (n + 1) s bad i =
        JPEG2000.Tier1.runPassesM m (fgeo w h b) K n
          (JPEG2000.Tier1.runPassM m (fgeo w h b) K s bad i).1
          (JPEG2000.Tier1.runPassM m (fgeo w h b) K s bad i).2 (i + 1) := rfl
    rw [e, List.range'_succ, List.foldl_cons]
    have h0 := hr 0 (by omega)
    simp only [Nat.add_zero] at h0
    rw [← h0] at R
    have R1 := runPassM_rel hm hvc K hK s d bad i R
    have B1 := runPassM_bad hm hvc K hK s d bad i R hb
    rw [h0] at R1
    exact ih _ _ _ (i + 1) (fun q hq => by rw [Nat.add_assoc]; exact hr (1 + q) (by omega)) R1 B1

/-- **The segment loop, count included.** -/
theorem runSegs_both (hm : StyleRel m md) (hvc : m.vertCausal = vc) (K : Nat) (hK : K ≤ 32)
    (data : ByteArray) (segs : Array JPEG2000.Tier1.Seg) :
    ∀ (L : List JPEG2000.Tier1.Seg) (k j : Nat) (s : JPEG2000.Tier1.St) (bad : Nat) (d : DecState)
      (i start : Nat) (raw : Bool), segs.toList.drop j = L → k = L.length →
      Homog md (L.map (·.passes)) i → RelM w h b vc start raw s d → bad = d.badSegSymbols →
      (JPEG2000.Tier1.runSegs m (fgeo w h b) K data segs k j s bad i).2 =
        (Spec.Tier1.decodeSegments md (gV w h b vc) K (L.map (specSeg data)) i d).badSegSymbols := by
  intro L
  induction L with
  | nil =>
    intro k j s bad d i start raw _ hk _ _ hb
    subst hk
    exact hb
  | cons sg rest ih =>
    intro k j s bad d i start raw hd hk hh R hb
    subst hk
    obtain ⟨hg, hd'⟩ := getD_of_drop segs j sg rest hd
    obtain ⟨hh1, hh2⟩ := hh
    have e : JPEG2000.Tier1.runSegs m (fgeo w h b) K data segs (rest.length + 1) j s bad i =
        JPEG2000.Tier1.runSegs m (fgeo w h b) K data segs rest.length (j + 1)
          (JPEG2000.Tier1.runPassesM m (fgeo w h b) K (segs.getD j default).passes
            (JPEG2000.Tier1.startSegment m data s i (segs.getD j default)) bad i).1
          (JPEG2000.Tier1.runPassesM m (fgeo w h b) K (segs.getD j default).passes
            (JPEG2000.Tier1.startSegment m data s i (segs.getD j default)) bad i).2
          (i + (segs.getD j default).passes) := rfl
    rw [List.length_cons, e, hg]
    simp only [List.map_cons, Spec.Tier1.decodeSegments, specSeg]
    have R1 := startSegment_rel hm data s d i sg R
    have hb1 : bad = (Spec.Tier1.startSegment md d i
        (MQEquiv.segment data sg.start sg.stop)).badSegSymbols := by
      rw [hb]; unfold Spec.Tier1.startSegment; split <;> rfl
    obtain ⟨R2, B2⟩ := runPassesM_both (start := sg.start) hm hvc K hK
      (Spec.Tier1.isRawPass md i) sg.passes _ bad _ i hh1 R1 hb1
    exact ih _ (j + 1) _ _ _ _ _ _ hd' rfl hh2 R2 B2

end fast

/-! ## The strict theorem -/

/-- **The fast count is the spec count**: whenever the fast core decoder succeeds on a block
whose spec checks pass, its bad-symbol count is the spec's `badSegSymbols`. -/
theorem core_bad (data : ByteArray) (segs : Array JPEG2000.Tier1.Seg) (w h : Nat) (band : Band)
    (style : UInt8) (Mb zbp : Nat)
    (hK : 0 < (segs.toList.map (·.passes)).sum → Mb - zbp ≤ 31)
    (u : Unit) (hval : (specBlockM data segs w h band style Mb zbp).validate = .ok u)
    (o : JPEG2000.Tier1.CodeBlockOut) (bad : Nat)
    (hcore : JPEG2000.Tier1.decodeSegsCore data segs w h band style Mb zbp = .ok (o, bad))
    (hv : JPEG2000.Tier1.validateSegs data segs w h (JPEG2000.Tier1.Style.ofByte style)
      (Mb - zbp) = (specBlockM data segs w h band style Mb zbp).validate) :
    bad = (Spec.Tier1.decodeState (specBlockM data segs w h band style Mb zbp)).badSegSymbols := by
  have hm := styleRel_ofByte style
  obtain ⟨hnK, hsegP⟩ := validate_ok_facts _ u hval
  rw [specBlockM_numPasses] at hnK hsegP
  have hmap : (specBlockM data segs w h band style Mb zbp).segments.map (·.passes) =
      segs.toList.map (·.passes) := by
    simp [specBlockM, List.map_map, Function.comp_def]
  rw [hmap] at hsegP
  have hmd : (specBlockM data segs w h band style Mb zbp).mode = Mode.ofStyle style.toNat := rfl
  rw [hmd] at hsegP
  have hgeom : (specBlockM data segs w h band style Mb zbp).geom =
      gV w h band (Mode.ofStyle style.toNat).vertCausal := rfl
  have hst : Spec.Tier1.decodeState (specBlockM data segs w h band style Mb zbp) =
      Spec.Tier1.decodeSegments (Mode.ofStyle style.toNat)
        (gV w h band (Mode.ofStyle style.toNat).vertCausal) (Mb - zbp)
        (segs.toList.map (specSeg data)) 0
        (DecState.init (gV w h band (Mode.ofStyle style.toNat).vertCausal) []) := rfl
  unfold JPEG2000.Tier1.decodeSegsCore at hcore
  dsimp only at hcore
  rw [hv, hval] at hcore
  simp only [bind, Except.bind, pure, Except.pure] at hcore
  rw [hst]
  generalize hN : (segs.toList.map (·.passes)).sum = N at hK hnK hsegP
  generalize hmd' : Mode.ofStyle style.toNat = md at hm hsegP ⊢
  generalize hfm : JPEG2000.Tier1.Style.ofByte style = m at hm hcore
  by_cases hp : m.decodesAsPlain = true
  · -- the fast plain path returns 0; a plain-like style never counts
    simp only [hp, ↓reduceIte] at hcore
    simp only [JPEG2000.Tier1.Style.decodesAsPlain, Bool.not_eq_true', Bool.or_eq_false_iff] at hp
    have hs : md.segSymbols = false := by rw [← hm.segSymbols]; exact hp.2
    rw [decodeSegments_bad_noSeg _ md hs]
    revert hcore
    split
    · generalize JPEG2000.Tier1.decodeCodeBlockExact _ _ _ _ _ _ _ _ _ = r
      intro hc; cases r <;> simp at hc; exact hc.2.symm
    · generalize JPEG2000.Tier1.decodeCodeBlockExact _ _ _ _ _ _ _ _ _ = r
      intro hc; cases r <;> simp at hc; exact hc.2.symm
  · simp only [hp, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at hcore
    rw [← hcore.2]
    have R0 := init_relM data w h band md.vertCausal
    by_cases N0 : N = 0
    · have hnil : segs.toList = [] := by
        rw [N0, Spec.Tier1.segmentPasses, Spec.Tier1.segmentRuns] at hsegP
        simpa using hsegP
      have hsz : segs.size = 0 := by rw [← Array.length_toList, hnil]; rfl
      rw [hsz, hnil]
      rfl
    · have hhom : Homog md (segs.toList.map (·.passes)) 0 := by
        rw [hsegP]; exact segmentPasses_homog md N
      exact runSegs_both hm hm.vertCausal (Mb - zbp) (by have := hK (by omega); omega) data segs
        segs.toList segs.size 0 _ 0 _ 0 0 false (by simp) (by simp) hhom R0 rfl

/-- **C3 for every code-block style, strict segmentation symbols**: as `c3_all` for
`decodeCodeBlockSegsStrictExact` and `Spec.Tier1.decodeCodeBlockStrictExact` (a segmentation symbol other
than `1010` is the same `malformed` error on both sides). -/
theorem c3_all_strict_exact (data : ByteArray) (segs : Array JPEG2000.Tier1.Seg) (w h : Nat)
    (band : Band) (style : UInt8) (Mb zbp : Nat)
    (hrange : ∀ sg ∈ segs.toList, sg.start ≤ sg.stop ∧ sg.stop ≤ data.size)
    (hK : 0 < (segs.toList.map (·.passes)).sum → Mb - zbp ≤ 31) :
    match JPEG2000.Tier1.decodeCodeBlockSegsStrictExact data segs w h band style Mb zbp,
      Spec.Tier1.decodeCodeBlockStrictExact (specBlockM data segs w h band style Mb zbp) with
    | .error e1, .error e2 => e1 = e2
    | .ok o, .ok cs => Agree w h o cs
    | _, _ => False := by
  have L := c3_all_exact data segs w h band style Mb zbp hrange hK
  have hv := validate_eqM data segs w h band style Mb zbp hrange hK
  unfold JPEG2000.Tier1.decodeCodeBlockSegsExact at L
  unfold JPEG2000.Tier1.decodeCodeBlockSegsStrictExact Spec.Tier1.decodeCodeBlockStrictExact
  unfold Spec.Tier1.decodeCodeBlockExact at L
  have hB := core_bad data segs w h band style Mb zbp hK
  revert L hB
  generalize JPEG2000.Tier1.decodeSegsCore data segs w h band style Mb zbp = core
  cases hval : (specBlockM data segs w h band style Mb zbp).validate with
  | error e =>
    intro L _
    cases core with
    | error e' => simpa [bind, Except.bind, Except.map] using L
    | ok ob => simp [bind, Except.bind, Except.map] at L
  | ok u =>
    intro L hB
    cases core with
    | error e' => simp [bind, Except.bind, Except.map, pure, Except.pure] at L
    | ok ob =>
      obtain ⟨o, bad⟩ := ob
      have hb := hB u rfl o bad rfl (hv.trans hval)
      simp only [bind, Except.bind, Except.map, pure, Except.pure] at L ⊢
      rw [← hb]
      by_cases h0 : (bad != 0) = true
      · simp [h0, throw, throwThe, MonadExceptOf.throw, JPEG2000.Tier1.tier1Loc,
          Spec.Tier1.tier1Loc]
      · simp only [h0, Bool.false_eq_true, ↓reduceIte]
        exact L

end JPEG2000.Spec.Tier1EquivM
