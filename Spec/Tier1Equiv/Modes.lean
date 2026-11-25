import Spec.Tier1Equiv.Modes.Inv

/-!
# C3 for every code-block style: the fast Tier-1 decoder equals the spec decoder

Plan.md §4 (C3: "the fast EBCOT decoder equals the spec decoder (Annex D, coefficient by
coefficient, pass by pass)"), §5.1, §5.2 "Tier-1 / EBCOT" (staged modes); T.800 Annex D
(D.2–D.7), Table A.19, E.1.1.2. Task 7.1c (extends `Spec.Tier1Equiv.c3_plain`, task 3.6).

`c3_all_exact` (task 5.8 renamed it, with `c3_all_unsup_exact`; `c3_all` and `c3_all_unsup` in
`Spec.Tier1Equiv.Clamp` are the same statements for the decoders that first drop passes beyond
`3K − 2`): for every buffer `data`, codeword segments `segs` (byte ranges of `data` with their
pass counts), block size, band, code-block style byte, `Mb` and zero bit-planes, with every
segment range inside the buffer and `K = Mb − zbp ≤ 31` whenever a pass is decoded, the fast
`JPEG2000.Tier1.decodeCodeBlockSegsExact` and the spec `Spec.Tier1.decodeCodeBlockExact` of the block
`specBlockM` (mode `Mode.ofStyle style`, segments `segment data start stop` with their pass
counts) either both fail with the same error, or both succeed and agree on every coefficient:
the `Int32` value is the spec `Coeff.value`, `sig` is the spec `sig`, and the recomputed
`lsbPlane` is the spec `lsbPlane` (`Agree`). The side conditions are exactly the fast
decoder's two extra checks (`validateSegs`).

Both decoders tolerate bad segmentation symbols (the lenient pair); the strict pair
(`decodeCodeBlockSegsStrictExact` / `decodeCodeBlockStrictExact`) is not covered here.

Proof:
* argument checks: `validate_eqM` (the checks coincide under the side conditions);
* styles that decode as plain (`Style.decodesAsPlain`): the fast decoder calls the plain
  `decodeCodeBlockExact`, so `c3_plain` applies, once the spec block of the style is shown to decode
  as the plain block (`decodeCodeBlock_plainLike`);
* the other styles: the initial states are related (`init_relM`), the segment loop simulates
  `decodeSegments` (`runSegs_rel`, part 5), the spec invariant holds (`decodeSegments_inv`,
  part 6), and the output is read as in the plain proof (`out_okM`).
-/

namespace JPEG2000.Spec.Tier1EquivM

open JPEG2000
open JPEG2000.Bytes (Plane)
open JPEG2000.Tier2.Geometry (Band)
open JPEG2000.Spec.Tier1 (Coeff Geom DecState RawState Mode CodeBlock)
open JPEG2000.Spec.Tier1Equiv

/-! ## The spec block and the conclusion -/

/-- The spec code-block of `c3_all`: the style's mode, and the fast segments as spec segments
(their bytes `segment data start stop` and pass counts). -/
def specBlockM (data : ByteArray) (segs : Array JPEG2000.Tier1.Seg) (w h : Nat) (band : Band)
    (style : UInt8) (Mb zbp : Nat) : CodeBlock :=
  { width := w, height := h, orient := orientOf band, mode := Mode.ofStyle style.toNat,
    numBitPlanes := Mb, zeroBitPlanes := zbp,
    segments := segs.toList.map fun sg => ⟨MQEquiv.segment data sg.start sg.stop, sg.passes⟩ }

/-- The per-coefficient agreement of a fast output and spec coefficients (the conclusion of
`c3_plain`): sizes, and for every in-block `(x, y)` the value, the significance and the
`lsbPlane`. -/
def Agree (w h : Nat) (o : JPEG2000.Tier1.CodeBlockOut) (cs : Array Coeff) : Prop :=
  cs.size = w * h ∧ o.plane.width = w ∧ o.plane.height = h ∧
    ∀ x y, x < w → y < h →
      (o.plane.get? (y * w + x)).map Int32.toInt = some (cs.getD (y * w + x) {}).value ∧
      o.sig x y = (cs.getD (y * w + x) {}).sig ∧
      o.lsbPlane x y = (cs.getD (y * w + x) {}).lsbPlane

/-! ## Argument checks -/

/-- `segsPasses` is the sum of the pass counts. -/
theorem segsPasses_eq (segs : Array JPEG2000.Tier1.Seg) :
    JPEG2000.Tier1.segsPasses segs = (segs.toList.map (·.passes)).sum := by
  unfold JPEG2000.Tier1.segsPasses
  rw [← Array.foldl_toList]
  have : ∀ (l : List JPEG2000.Tier1.Seg) (a : Nat),
      l.foldl (fun n sg => n + sg.passes) a = a + (l.map (·.passes)).sum := by
    intro l
    induction l with
    | nil => intro a; simp
    | cons x l ih => intro a; simp only [List.foldl_cons, ih, List.map_cons, List.sum_cons]; omega
  rw [this]; simp

/-- The pass count of the spec block. -/
theorem specBlockM_numPasses (data : ByteArray) (segs : Array JPEG2000.Tier1.Seg) (w h : Nat)
    (band : Band) (style : UInt8) (Mb zbp : Nat) :
    (specBlockM data segs w h band style Mb zbp).numPasses = (segs.toList.map (·.passes)).sum := by
  simp [specBlockM, CodeBlock.numPasses, List.map_map, Function.comp_def]

/-- **The argument checks agree** when every segment lies in the buffer and `K ≤ 31` for a
non-empty block. -/
theorem validate_eqM (data : ByteArray) (segs : Array JPEG2000.Tier1.Seg) (w h : Nat)
    (band : Band) (style : UInt8) (Mb zbp : Nat)
    (hrange : ∀ sg ∈ segs.toList, sg.start ≤ sg.stop ∧ sg.stop ≤ data.size)
    (hK : 0 < (segs.toList.map (·.passes)).sum → Mb - zbp ≤ 31) :
    JPEG2000.Tier1.validateSegs data segs w h (JPEG2000.Tier1.Style.ofByte style) (Mb - zbp) =
      (specBlockM data segs w h band style Mb zbp).validate := by
  have hn := specBlockM_numPasses data segs w h band style Mb zbp
  have hm := styleRel_ofByte style
  have hany : (segs.any fun sg => sg.start > sg.stop || sg.stop > data.size) = false := by
    rw [← Array.any_toList]
    apply Bool.eq_false_iff.mpr
    intro hc
    rw [List.any_eq_true] at hc
    obtain ⟨sg, hsg, hc⟩ := hc
    have := hrange sg hsg
    simp at hc; omega
  have hmap : (specBlockM data segs w h band style Mb zbp).segments.map (·.passes) =
      segs.toList.map (·.passes) := by
    simp [specBlockM, List.map_map, Function.comp_def]
  unfold JPEG2000.Tier1.validateSegs Spec.Tier1.CodeBlock.validate
  rw [hn, hmap, segsPasses_eq]
  dsimp only
  simp only [segmentPasses_eq hm]
  generalize hN : (segs.toList.map (·.passes)).sum = N at hK
  have h5 : ¬ (N > 0 ∧ Mb - zbp > 31) := fun ⟨a, c⟩ => by have := hK a; omega
  simp only [hany, h5, Bool.false_eq_true, ↓reduceIte]
  by_cases c1 : w > 1024 ∨ h > 1024 ∨ w * h > 4096 <;>
    by_cases c2 : N > 0 ∧ N > 3 * (Mb - zbp) - 2 <;>
    by_cases c3 : (segs.toList.map (·.passes) != Spec.Tier1.segmentPasses
      (Mode.ofStyle style.toNat) N 0) = true <;>
    simp [c1, c2, c3, specBlockM, CodeBlock.codedPlanes, JPEG2000.Tier1.tier1Loc,
      Spec.Tier1.tier1Loc]

/-- What a successful spec validation says: at most `3K − 2` passes, and the segment pass
counts are the style's `segmentPasses`. -/
theorem validate_ok_facts (cb : CodeBlock) (u : Unit) (h : cb.validate = .ok u) :
    (0 < cb.numPasses → cb.numPasses ≤ 3 * cb.codedPlanes - 2) ∧
    cb.segments.map (·.passes) = Spec.Tier1.segmentPasses cb.mode cb.numPasses 0 := by
  unfold CodeBlock.validate at h
  by_cases c1 : cb.width > 1024 ∨ cb.height > 1024 ∨ cb.width * cb.height > 4096
  · simp [c1, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  · by_cases c2 : cb.numPasses > 0 ∧ cb.numPasses > 3 * cb.codedPlanes - 2
    · simp [c1, c2, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
    · by_cases c3 : (cb.segments.map (·.passes) != Spec.Tier1.segmentPasses cb.mode
          cb.numPasses 0) = true
      · simp [c1, c2, c3, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
      · refine ⟨fun hp => by omega, ?_⟩
        simpa using c3

/-! ## Styles that decode as plain -/

/-- A mode with the bypass, reset, termall, vertically causal and segmentation-symbol flags clear
runs every pass as the plain mode. -/
theorem runPassM_plainLike (md : Mode) (hb : md.bypass = false) (hr : md.reset = false)
    (hs : md.segSymbols = false) : Spec.Tier1.runPassM md = Spec.Tier1.runPassM Mode.plain := by
  funext g K d i
  simp [Spec.Tier1.runPassM, Spec.Tier1.isRawPass, hb, hr, hs, Mode.plain]

/-- Such a mode starts segments as the plain mode. -/
theorem startSegment_plainLike (md : Mode) (hb : md.bypass = false) :
    Spec.Tier1.startSegment md = Spec.Tier1.startSegment Mode.plain := by
  funext d i data
  simp [Spec.Tier1.startSegment, Spec.Tier1.isRawPass, hb, Mode.plain]

/-- **A plain-like block decodes as the plain block** with the same fields. -/
theorem decodeCodeBlock_plainLike (cb : CodeBlock) (hb : cb.mode.bypass = false)
    (hr : cb.mode.reset = false) (ht : cb.mode.termAll = false)
    (hv : cb.mode.vertCausal = false) (hs : cb.mode.segSymbols = false) :
    Spec.Tier1.decodeCodeBlockExact cb = Spec.Tier1.decodeCodeBlockExact { cb with mode := Mode.plain } := by
  have hval : cb.validate = ({ cb with mode := Mode.plain } : CodeBlock).validate := by
    unfold CodeBlock.validate
    rw [Spec.Tier1.segmentPasses_plain _ ht hb, Spec.Tier1.segmentPasses_plain _ rfl rfl]
    rfl
  have hgeom : cb.geom = ({ cb with mode := Mode.plain } : CodeBlock).geom := by
    simp [CodeBlock.geom, hv, Mode.plain]
  have hst : Spec.Tier1.decodeState cb =
      Spec.Tier1.decodeState { cb with mode := Mode.plain } := by
    unfold Spec.Tier1.decodeState
    rw [hgeom]
    have e1 := runPassM_plainLike cb.mode hb hr hs
    have e2 := startSegment_plainLike cb.mode hb
    have : ∀ (L : List Spec.Tier1.Segment) i d,
        Spec.Tier1.decodeSegments cb.mode ({ cb with mode := Mode.plain } : CodeBlock).geom
          cb.codedPlanes L i d =
        Spec.Tier1.decodeSegments Mode.plain ({ cb with mode := Mode.plain } : CodeBlock).geom
          cb.codedPlanes L i d := by
      intro L
      induction L with
      | nil => intro i d; rfl
      | cons sg rest ih => intro i d; simp only [Spec.Tier1.decodeSegments, e1, e2, ih]
    exact this _ _ _
  unfold Spec.Tier1.decodeCodeBlockExact
  rw [hval, hst]

/-! ## Initial states -/

/-- The initial fast state of `decodeSegsCore` is related to the spec's initial state. -/
theorem init_relM (data : ByteArray) (w h : Nat) (b : Band) (vc : Bool) :
    RelM w h b vc 0 false
      { mq := MQ.Dec.init data 0 0 MQ.tier1Contexts,
        flags := Array.replicate ((w + 2) * (h + 2)) 0,
        mags := Array.replicate ((w + 2) * (h + 2)) 0 }
      (DecState.init (gV w h b vc) []) := by
  have hc : ∀ X Y : Int, (gV w h b vc).coeffAt
      (DecState.init (gV w h b vc) []).coeffs X Y = {} :=
    fun X Y => coeffAt_replicate _ X Y
  have hseg : MQEquiv.segment data 0 0 = [] := by simp [MQEquiv.segment]
  have hco := MQEquiv.init_sim data 0 0 _ _ tier1Contexts_rel
  rw [hseg] at hco
  refine ⟨hco, by simp, by simp, by simp [DecState.init, gV], ?_, ?_⟩
  · intro x y j _ _ _
    simp only [fget_replicate, bt_zero, specBitV, Geom.nbAt, hc]
    split
    · split <;> split <;> rfl
    · simp [ownBit]; repeat' split
      all_goals rfl
  · intro x y _ _
    simp only [fget_replicate, hc]
    rfl

/-! ## Output -/

/-- **The output value** under `RelM` (as `val_toInt`). -/
theorem val_toIntM {w h : Nat} {b : Band} {vc : Bool} {start : Nat} {raw : Bool}
    {s : JPEG2000.Tier1.St} {d : DecState}
    (R : RelM w h b vc start raw s d) {x y : Nat} (hx : x < w) (hy : y < h) (K : Nat)
    (hb : Base K ((gV w h b vc).coeffAt d.coeffs x y))
    (hK : ((gV w h b vc).coeffAt d.coeffs x y).sig = true → K ≤ 31) :
    (val s.flags s.mags (bidx w x y)).toInt = ((gV w h b vc).coeffAt d.coeffs x y).value := by
  have hm := R.mag x y hx hy
  have hneg := negTest_relM R hx hy
  generalize (gV w h b vc).coeffAt d.coeffs x y = c at hm hneg hb hK
  have hlt : c.mag < 2 ^ 31 := by
    cases hs : c.sig
    · rw [(hb.1 hs).1]; decide
    · have := (hb.2 hs).1
      have := Nat.pow_le_pow_right (show 0 < 2 by decide) (hK hs)
      omega
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  have hu : (JPEG2000.Tier1.fget s.mags (bidx w x y)).toNat < 2 ^ 31 := by omega
  unfold val Spec.Tier1.Coeff.value
  rw [hneg]
  cases hs : c.sig <;> cases hn : c.sign <;>
    simp [toInt_toInt32 _ hu, toInt_neg_toInt32 _ hu, hm, (hb.1 _).1, hs]
  all_goals first | rfl | (have := (hb.1 hs).1; omega)

/-- **The output agrees**: from a final fast state related to the final spec state, with the
spec invariant after `n` passes, the `CodeBlockOut` built as `decodeSegsCore` builds it agrees
with the spec coefficients. -/
theorem out_okM {w h : Nat} {b : Band} {vc : Bool} {start : Nat} {raw : Bool}
    (sF : JPEG2000.Tier1.St) (dF : DecState) (RF : RelM w h b vc start raw sF dF) (K n : Nat)
    (hK : 0 < n → K ≤ 31)
    (hinv : ∀ x y, x < w → y < h →
      (n = 0 → (gV w h b vc).coeffAt dF.coeffs x y = {}) ∧
      (0 < n → Post K (n - 1) ((gV w h b vc).coeffAt dF.coeffs x y))) :
    Agree w h
      { plane := JPEG2000.Tier1.fillRows (fgeo w h b) sF.flags sF.mags h (Plane.zero w h) 0,
        flags := sF.flags, codedPlanes := K, numPasses := n } dF.coeffs := by
  have hdims := fillRows_dims w h b sF.flags sF.mags h (Plane.zero w h) 0
  have hbase : ∀ x y, x < w → y < h →
      Base K ((gV w h b vc).coeffAt dF.coeffs x y) ∧
      (((gV w h b vc).coeffAt dF.coeffs x y).sig = true → 0 < n) := by
    intro x y hx hy
    by_cases n0 : n = 0
    · rw [(hinv x y hx hy).1 n0]
      exact ⟨⟨fun _ => ⟨rfl, rfl⟩, fun h0 => by cases h0⟩, fun h0 => by cases h0⟩
    · have hp := (hinv x y hx hy).2 (by omega)
      refine ⟨?_, fun _ => by omega⟩
      unfold Post at hp
      split at hp
      · exact hp.1
      · exact hp.1
      · exact hp.1.1
  have hw : (JPEG2000.Tier1.fillRows (fgeo w h b) sF.flags sF.mags h (Plane.zero w h) 0).width = w :=
    hdims.1
  refine ⟨RF.csize, hdims.1, hdims.2, fun x y hx hy => ?_⟩
  generalize hc : (gV w h b vc).coeffAt dF.coeffs x y = c
  have hcg : dF.coeffs.getD (y * w + x) {} = c := by
    rw [← hc, coeffAt_nat _ _ _ _ hx hy]; rfl
  rw [hcg]
  obtain ⟨hb, hsn⟩ := hbase x y hx hy
  rw [hc] at hb hsn
  have hsig := sigTest_relM RF hx hy
  have hvis := visTest_relM RF hx hy
  rw [hc] at hsig hvis
  refine ⟨?_, ?_, ?_⟩
  · have hg := fillRows_get w h b sF.flags sF.mags x hx h (Plane.zero w h) 0 y
    have hlt : y * w + x < (Plane.zero w h).width * (Plane.zero w h).height := by
      have := idx_lt (sgeom w h b) hx hy
      simpa [Geom.idx, sgeom, Plane.zero] using this
    rw [ite_pos' ⟨Nat.zero_le _, by omega, hlt⟩] at hg
    show Option.map Int32.toInt
      ((JPEG2000.Tier1.fillRows (fgeo w h b) sF.flags sF.mags h (Plane.zero w h) 0).get?
        (y * w + x)) = _
    rw [hg]
    simp only [Option.map_some]
    have := val_toIntM RF hx hy K (by rw [hc]; exact hb)
      (fun hs => by rw [hc] at hs; have := hsn hs; exact hK this)
    rw [this, hc]
  · show (JPEG2000.Tier1.fget sF.flags ((y + 1) *
      ((JPEG2000.Tier1.fillRows (fgeo w h b) sF.flags sF.mags h (Plane.zero w h) 0).width + 2)
        + x + 1) &&& JPEG2000.Tier1.SIG != 0) = c.sig
    rw [hw]
    have e : (JPEG2000.Tier1.fget sF.flags ((y + 1) * (w + 2) + x + 1) &&& JPEG2000.Tier1.SIG != 0) =
        !(JPEG2000.Tier1.fget sF.flags (bidx w x y) &&& JPEG2000.Tier1.SIG == 0) := rfl
    rw [e, hsig, Bool.not_not]
  · show (let f := JPEG2000.Tier1.fget sF.flags ((y + 1) *
      ((JPEG2000.Tier1.fillRows (fgeo w h b) sF.flags sF.mags h (Plane.zero w h) 0).width + 2)
        + x + 1)
      if (f &&& JPEG2000.Tier1.SIG == 0 || n == 0) = true then 0
      else
        if (JPEG2000.Tier1.passKind (n - 1) == 0 && f &&& JPEG2000.Tier1.VIS == 0) = true then
          JPEG2000.Tier1.passPlane K (n - 1) + 1
        else JPEG2000.Tier1.passPlane K (n - 1)) = c.lsbPlane
    rw [hw]
    have e : JPEG2000.Tier1.fget sF.flags ((y + 1) * (w + 2) + x + 1) =
        JPEG2000.Tier1.fget sF.flags (bidx w x y) := rfl
    simp only [e, hsig, hvis]
    cases hs : c.sig
    · simp [(hb.1 hs).2]
    · have hn := hsn hs
      have hn' : (n == 0) = false := by simp; omega
      simp only [hn', Bool.not_true, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
      have hp := (hinv x y hx hy).2 hn
      rw [hc] at hp
      have epp : JPEG2000.Tier1.passPlane K (n - 1) = Spec.Tier1.passPlane K (n - 1) := rfl
      rw [epp]
      unfold Post at hp
      rcases passKind_cases (n - 1) with ⟨k1, k2⟩ | ⟨k1, k2⟩ | ⟨k1, k2⟩ <;>
        simp only [k2] at hp <;> simp only [k1]
      · cases hv : c.visited
        · simp [hp.2.2 hs hv]
        · simp [hp.2.1 hs hv]
      · simp [hp.2 hs]
      · simp [hp.1.2 hs]


/-! ## The theorem -/

/-- The spec decoder of a validated block returns its decoded coefficients. -/
theorem decodeCodeBlock_ok (cb : CodeBlock) (u : Unit) (h : cb.validate = .ok u) :
    Spec.Tier1.decodeCodeBlockExact cb = .ok (Spec.Tier1.decodeState cb).coeffs := by
  unfold Spec.Tier1.decodeCodeBlockExact
  rw [h]; rfl

/-- **C3 for every code-block style** (Plan.md §4): the fast Tier-1 decoder
`decodeCodeBlockSegsExact` equals the Annex D reference decoder `Spec.Tier1.decodeCodeBlockExact` on
every code-block of every style (Table A.19: bypass, reset, termall, vertically causal,
predictable termination, segmentation symbols, in any combination) given as codeword segments
of one buffer — both fail with the same error, or both succeed and agree coefficient by
coefficient on the value, the significance and `lsbPlane` (`Agree`). Side conditions: every
segment lies in the buffer, and at most 31 bit-planes are coded when a pass is decoded (the
fast decoder's two extra checks). -/
theorem c3_all_exact (data : ByteArray) (segs : Array JPEG2000.Tier1.Seg) (w h : Nat) (band : Band)
    (style : UInt8) (Mb zbp : Nat)
    (hrange : ∀ sg ∈ segs.toList, sg.start ≤ sg.stop ∧ sg.stop ≤ data.size)
    (hK : 0 < (segs.toList.map (·.passes)).sum → Mb - zbp ≤ 31) :
    match JPEG2000.Tier1.decodeCodeBlockSegsExact data segs w h band style Mb zbp,
      Spec.Tier1.decodeCodeBlockExact (specBlockM data segs w h band style Mb zbp) with
    | .error e1, .error e2 => e1 = e2
    | .ok o, .ok cs => Agree w h o cs
    | _, _ => False := by
  have hv := validate_eqM data segs w h band style Mb zbp hrange hK
  have hm := styleRel_ofByte style
  unfold JPEG2000.Tier1.decodeCodeBlockSegsExact JPEG2000.Tier1.decodeSegsCore
  dsimp only
  rw [hv]
  cases hval : (specBlockM data segs w h band style Mb zbp).validate with
  | error e =>
    unfold Spec.Tier1.decodeCodeBlockExact
    simp [hval, bind, Except.bind, Except.map]
  | ok u =>
    rw [decodeCodeBlock_ok _ u hval]
    simp only [bind, Except.bind, pure, Except.pure]
    obtain ⟨hnK, hsegP⟩ := validate_ok_facts _ u hval
    rw [specBlockM_numPasses] at hnK hsegP
    have hmap : (specBlockM data segs w h band style Mb zbp).segments.map (·.passes) =
        segs.toList.map (·.passes) := by
      simp [specBlockM, List.map_map, Function.comp_def]
    rw [hmap] at hsegP
    generalize hN : (segs.toList.map (·.passes)).sum = N at hK hnK hsegP
    have hmd : (specBlockM data segs w h band style Mb zbp).mode = Mode.ofStyle style.toNat := rfl
    rw [hmd] at hsegP
    generalize hmd' : Mode.ofStyle style.toNat = md at hm hsegP
    generalize hfm : JPEG2000.Tier1.Style.ofByte style = m at hm
    by_cases hp : m.decodesAsPlain = true
    · -- the plain-like styles: `c3_plain`
      simp only [hp, ↓reduceIte]
      simp only [JPEG2000.Tier1.Style.decodesAsPlain, Bool.not_eq_true', Bool.or_eq_false_iff] at hp
      obtain ⟨⟨⟨⟨hb, hr⟩, ht⟩, hvc⟩, hs⟩ := hp
      rw [hm.bypass] at hb; rw [hm.reset] at hr; rw [hm.termAll] at ht
      rw [hm.vertCausal] at hvc; rw [hm.segSymbols] at hs
      rw [Spec.Tier1.segmentPasses_plain _ ht hb] at hsegP
      have hpl := decodeCodeBlock_plainLike (specBlockM data segs w h band style Mb zbp)
        (by rw [hmd, hmd']; exact hb) (by rw [hmd, hmd']; exact hr) (by rw [hmd, hmd']; exact ht)
        (by rw [hmd, hmd']; exact hvc) (by rw [hmd, hmd']; exact hs)
      rw [decodeCodeBlock_ok _ u hval] at hpl
      cases hl : segs.toList with
      | nil =>
        simp only
        have heq : specBlock data 0 0 w h band Mb zbp 0 =
            { specBlockM data segs w h band style Mb zbp with mode := Mode.plain } := by
          simp [specBlock, CodeBlock.ofData, Spec.Tier1.Segment.single, specBlockM, hl]
        have C := c3_plain_exact data 0 0 w h band Mb zbp 0 ⟨Nat.le_refl _, Nat.zero_le _⟩
          (fun h0 => absurd h0 (Nat.lt_irrefl 0))
        rw [heq, ← hpl] at C
        revert C
        generalize JPEG2000.Tier1.decodeCodeBlockExact data 0 0 w h band Mb zbp 0 = r
        intro C
        cases r with
        | error e => exact C
        | ok o => exact C
      | cons sg rest =>
        cases rest with
        | nil =>
          simp only
          have hNs : N = sg.passes := by rw [← hN, hl]; simp
          have hn0 : sg.passes ≠ 0 := by
            intro h0; rw [hl, hNs, h0] at hsegP; simp at hsegP
          have heq : specBlock data sg.start sg.stop w h band Mb zbp sg.passes =
              { specBlockM data segs w h band style Mb zbp with mode := Mode.plain } := by
            simp [specBlock, CodeBlock.ofData, Spec.Tier1.Segment.single, specBlockM, hl, hn0]
          have C := c3_plain_exact data sg.start sg.stop w h band Mb zbp sg.passes
            (hrange sg (by rw [hl]; simp)) (fun hp => hK (by omega))
          rw [heq, ← hpl] at C
          revert C
          generalize JPEG2000.Tier1.decodeCodeBlockExact data sg.start sg.stop w h band Mb zbp sg.passes = r
          intro C
          cases r with
          | error e => exact C
          | ok o => exact C
        | cons sg2 rest =>
          exfalso
          rw [hl] at hsegP
          split at hsegP <;> simp at hsegP
    · -- every other style: the simulation
      simp only [hp, Bool.false_eq_true, ↓reduceIte]
      simp only [Except.map]
      have hvc : m.vertCausal = md.vertCausal := hm.vertCausal
      have hgeom : (specBlockM data segs w h band style Mb zbp).geom =
          gV w h band md.vertCausal := by rw [← hmd']; rfl
      have hst : Spec.Tier1.decodeState (specBlockM data segs w h band style Mb zbp) =
          Spec.Tier1.decodeSegments md (gV w h band md.vertCausal) (Mb - zbp)
            (segs.toList.map (specSeg data)) 0 (DecState.init (gV w h band md.vertCausal) []) := by
        unfold Spec.Tier1.decodeState
        rw [hgeom, hmd]
        rw [hmd']
        rfl
      rw [hst, segsPasses_eq, hN]
      have R0 := init_relM data w h band md.vertCausal
      -- the final states are related
      have RF : ∃ st raw, RelM w h band md.vertCausal st raw
          (JPEG2000.Tier1.runSegs m (fgeo w h band) (Mb - zbp) data segs segs.size 0
            { mq := MQ.Dec.init data 0 0 MQ.tier1Contexts,
              flags := Array.replicate ((w + 2) * (h + 2)) 0,
              mags := Array.replicate ((w + 2) * (h + 2)) 0 } 0 0).1
          (Spec.Tier1.decodeSegments md (gV w h band md.vertCausal) (Mb - zbp)
            (segs.toList.map (specSeg data)) 0 (DecState.init (gV w h band md.vertCausal) [])) := by
        by_cases N0 : N = 0
        · have hnil : segs.toList = [] := by
            rw [N0, Spec.Tier1.segmentPasses, Spec.Tier1.segmentRuns] at hsegP
            simpa using hsegP
          have hsz : segs.size = 0 := by rw [← Array.length_toList, hnil]; rfl
          rw [hsz, hnil]
          exact ⟨0, false, R0⟩
        · have hhom : Homog md (segs.toList.map (·.passes)) 0 := by
            rw [hsegP]; exact segmentPasses_homog md N
          exact runSegs_rel hm hvc (Mb - zbp) (by have := hK (by omega); omega) data segs
            segs.toList segs.size 0 _ 0 _ 0 0 false (by simp) (by simp) hhom R0
      obtain ⟨st, raw, RF⟩ := RF
      refine out_okM _ _ RF (Mb - zbp) N (fun hn => hK hn) (fun x y hx hy => ⟨fun N0 => ?_, fun hn => ?_⟩)
      · have hnil : segs.toList = [] := by
          rw [N0, Spec.Tier1.segmentPasses, Spec.Tier1.segmentRuns] at hsegP
          simpa using hsegP
        rw [hnil]
        exact coeffAt_replicate _ _ _
      · have hsum : ((segs.toList.map (specSeg data)).map (·.passes)).sum = N := by
          rw [← hN]; simp [specSeg, List.map_map, Function.comp_def]
        have H0 : AllPV w h band md.vertCausal (Pre (Mb - zbp) 0)
            (DecState.init (gV w h band md.vertCausal) []).coeffs := by
          refine ⟨by simp [DecState.init, gV], fun x y _ _ => ?_⟩
          rw [show (DecState.init (gV w h band md.vertCausal) []).coeffs = Array.replicate
            ((gV w h band md.vertCausal).width * (gV w h band md.vertCausal).height) {} from rfl,
            coeffAt_replicate]
          simp only [Pre, ↓reduceIte]
          exact ⟨⟨fun _ => ⟨rfl, rfl⟩, fun h0 => by cases h0⟩, fun h0 => by cases h0⟩
        have := decodeSegments_inv md (Mb - zbp) (segs.toList.map (specSeg data)) 0 _
          (by
            rw [hsum]
            have hcp : (specBlockM data segs w h band style Mb zbp).codedPlanes = Mb - zbp := rfl
            have := hnK hn; omega) H0
        rw [hsum, Nat.zero_add] at this
        have e : Pre (Mb - zbp) N = Post (Mb - zbp) (N - 1) := by
          simp [Pre, show N ≠ 0 by omega]
        rw [e] at this
        exact this.2 x y hx hy

/-! ## More than 31 coded bit-planes -/

/-- With a decoded pass and `K > 31`, the fast checks are the spec checks followed by the
`unsupported` refusal. -/
theorem validate_eq_unsup (data : ByteArray) (segs : Array JPEG2000.Tier1.Seg) (w h : Nat)
    (band : Band) (style : UInt8) (Mb zbp : Nat)
    (hrange : ∀ sg ∈ segs.toList, sg.start ≤ sg.stop ∧ sg.stop ≤ data.size)
    (hK : 0 < (segs.toList.map (·.passes)).sum ∧ Mb - zbp > 31) :
    JPEG2000.Tier1.validateSegs data segs w h (JPEG2000.Tier1.Style.ofByte style) (Mb - zbp) =
      ((specBlockM data segs w h band style Mb zbp).validate >>= fun _ =>
        throw (.unsupported JPEG2000.Tier1.tier1Loc "more than 31 coded bit-planes")) := by
  have hn := specBlockM_numPasses data segs w h band style Mb zbp
  have hm := styleRel_ofByte style
  have hany : (segs.any fun sg => sg.start > sg.stop || sg.stop > data.size) = false := by
    rw [← Array.any_toList]
    apply Bool.eq_false_iff.mpr
    intro hc
    rw [List.any_eq_true] at hc
    obtain ⟨sg, hsg, hc⟩ := hc
    have := hrange sg hsg
    simp at hc; omega
  have hmap : (specBlockM data segs w h band style Mb zbp).segments.map (·.passes) =
      segs.toList.map (·.passes) := by
    simp [specBlockM, List.map_map, Function.comp_def]
  unfold JPEG2000.Tier1.validateSegs Spec.Tier1.CodeBlock.validate
  rw [hn, hmap, segsPasses_eq]
  dsimp only
  simp only [segmentPasses_eq hm]
  generalize hN : (segs.toList.map (·.passes)).sum = N at hK
  have h5 : N > 0 ∧ Mb - zbp > 31 := hK
  have c2b : (N > 0 ∧ N > 3 * (Mb - zbp) - 2) ↔ 3 * (Mb - zbp) - 2 < N := by omega
  simp only [hany, h5, Bool.false_eq_true, ↓reduceIte, c2b]
  by_cases c1 : w > 1024 ∨ h > 1024 ∨ w * h > 4096 <;>
    by_cases c2 : 3 * (Mb - zbp) - 2 < N <;>
    by_cases c3 : (segs.toList.map (·.passes) != Spec.Tier1.segmentPasses
      (Mode.ofStyle style.toNat) N 0) = true <;>
    simp [c1, c2, c2b, c3, specBlockM, CodeBlock.codedPlanes, JPEG2000.Tier1.tier1Loc,
      Spec.Tier1.tier1Loc, bind, Except.bind, throw, throwThe, MonadExceptOf.throw, pure,
      Except.pure]

/-- **C3 for every code-block style, without the bit-plane bound**: as `c3_all`, but when more
than 31 bit-planes are coded and a pass is decoded, the fast decoder may (and then does) refuse
with `unsupported` where the spec succeeds; every other outcome is as in `c3_all`. Only the
segment ranges are assumed to lie in the buffer. This is the form a relation that tolerates
`unsupported` fast errors (`Spec.Equiv.ERel`) consumes. -/
theorem c3_all_unsup_exact (data : ByteArray) (segs : Array JPEG2000.Tier1.Seg) (w h : Nat)
    (band : Band) (style : UInt8) (Mb zbp : Nat)
    (hrange : ∀ sg ∈ segs.toList, sg.start ≤ sg.stop ∧ sg.stop ≤ data.size) :
    match JPEG2000.Tier1.decodeCodeBlockSegsExact data segs w h band style Mb zbp,
      Spec.Tier1.decodeCodeBlockExact (specBlockM data segs w h band style Mb zbp) with
    | .error e1, .error e2 => e1 = e2
    | .ok o, .ok cs => Agree w h o cs
    | .error e, .ok _ => e = .unsupported JPEG2000.Tier1.tier1Loc "more than 31 coded bit-planes"
    | _, _ => False := by
  by_cases hK : 0 < (segs.toList.map (·.passes)).sum → Mb - zbp ≤ 31
  · have C := c3_all_exact data segs w h band style Mb zbp hrange hK
    revert C
    generalize JPEG2000.Tier1.decodeCodeBlockSegsExact data segs w h band style Mb zbp = r1
    generalize Spec.Tier1.decodeCodeBlockExact (specBlockM data segs w h band style Mb zbp) = r2
    intro C
    cases r1 <;> cases r2
    · exact C
    · exact C.elim
    · exact C.elim
    · exact C
  · have hK' : 0 < (segs.toList.map (·.passes)).sum ∧ Mb - zbp > 31 :=
      ⟨Classical.byContradiction fun h0 => hK fun h1 => absurd h1 h0,
        Classical.byContradiction fun h0 => hK fun _ => by omega⟩
    have hv := validate_eq_unsup data segs w h band style Mb zbp hrange hK'
    unfold JPEG2000.Tier1.decodeCodeBlockSegsExact JPEG2000.Tier1.decodeSegsCore
      Spec.Tier1.decodeCodeBlockExact
    dsimp only
    rw [hv]
    cases (specBlockM data segs w h band style Mb zbp).validate with
    | error e => simp [bind, Except.bind, Except.map]
    | ok u => simp [bind, Except.bind, Except.map, throw, throwThe, MonadExceptOf.throw, pure,
        Except.pure]

end JPEG2000.Spec.Tier1EquivM
