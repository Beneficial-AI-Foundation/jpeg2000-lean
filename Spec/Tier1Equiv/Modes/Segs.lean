import Spec.Tier1Equiv.Modes.Pass

/-!
# C3 (all code-block styles), part 5: the pass sequence and the codeword segments

Plan.md §4 (C3), §5.2 "Tier-1 / EBCOT" (staged modes); T.800 D.2 (pass sequence), D.4 / D.6 /
Table D.9 (codeword segments), D.5 (segmentation symbols), D.7 (context reset), A.6.1
Table A.19 (code-block style). Task 7.1c.

* `StyleRel` — the fast `Style` and the spec `Mode` agree on the five flags that matter to
  the decoder (`styleRel_ofByte`: `Style.ofByte b` and `Mode.ofStyle b.toNat`, all 256 bytes);
  then `isRawPass`, `passEndsSegment`, `segmentRuns`, `segmentPasses` agree.
* `runPassM_rel` — one pass of any style: raw or MQ pass, then the segmentation symbol (D.5,
  four UNIFORM decisions; the count of bad symbols is not part of the relation), then the
  reset of the 19 contexts (D.7).
* `startSegment_rel` — a new codeword segment re-initialises the coder on its own bytes:
  `INITDEC` (C2's `init_sim`) or a fresh raw reader (`rawInit_sim`); contexts persist.
* `segmentRuns_homog` — in the segment structure the style prescribes (`segmentPasses`),
  every segment is all-raw or all-MQ (`Homog`): a pass that does not end a segment has the
  rawness of the next one (`isRawPass_succ`).
* `runSegs_rel` — the whole segment loop `runSegs` simulates `Spec.Tier1.decodeSegments`.
-/

namespace JPEG2000.Spec.Tier1EquivM

open JPEG2000
open JPEG2000.Tier2.Geometry (Band)
open JPEG2000.Spec.Tier1 (Coeff Geom DecState RawState Mode)
open JPEG2000.Spec.Tier1Equiv

/-! ## Style flags -/

/-- The fast style and the spec mode agree on the flags with a decoder effect. -/
structure StyleRel (m : JPEG2000.Tier1.Style) (md : Mode) : Prop where
  /-- Bypass. -/
  bypass : m.bypass = md.bypass
  /-- Reset. -/
  reset : m.reset = md.reset
  /-- Termall. -/
  termAll : m.termAll = md.termAll
  /-- Vertically causal. -/
  vertCausal : m.vertCausal = md.vertCausal
  /-- Segmentation symbols. -/
  segSymbols : m.segSymbols = md.segSymbols

/-- The fast style byte decoder and the spec's `Mode.ofStyle` agree (all 256 bytes). -/
theorem styleRel_ofByte (st : UInt8) :
    StyleRel (JPEG2000.Tier1.Style.ofByte st) (Mode.ofStyle st.toNat) := by
  have : ∀ st : UInt8,
      (JPEG2000.Tier1.Style.ofByte st).bypass = (Mode.ofStyle st.toNat).bypass ∧
      (JPEG2000.Tier1.Style.ofByte st).reset = (Mode.ofStyle st.toNat).reset ∧
      (JPEG2000.Tier1.Style.ofByte st).termAll = (Mode.ofStyle st.toNat).termAll ∧
      (JPEG2000.Tier1.Style.ofByte st).vertCausal = (Mode.ofStyle st.toNat).vertCausal ∧
      (JPEG2000.Tier1.Style.ofByte st).segSymbols = (Mode.ofStyle st.toNat).segSymbols := by
    decide
  obtain ⟨a, b, c, d, e⟩ := this st
  exact ⟨a, b, c, d, e⟩

/-- `!=` on pass kinds. -/
theorem pk_bne (a c : Spec.Tier1.PassKind) : (a != c) = !decide (a = c) := by
  cases a <;> cases c <;> decide

section style
variable {m : JPEG2000.Tier1.Style} {md : Mode} (hm : StyleRel m md)
include hm

/-- Raw passes agree. -/
theorem isRawPass_eq (i : Nat) : JPEG2000.Tier1.isRawPass m i = Spec.Tier1.isRawPass md i := by
  unfold JPEG2000.Tier1.isRawPass Spec.Tier1.isRawPass
  rw [hm.bypass]
  rcases passKind_cases i with ⟨k1, k2⟩ | ⟨k1, k2⟩ | ⟨k1, k2⟩ <;> simp [k1, k2]

/-- Segment ends agree. -/
theorem passEndsSegment_eq (i : Nat) :
    JPEG2000.Tier1.passEndsSegment m i = Spec.Tier1.passEndsSegment md i := by
  unfold JPEG2000.Tier1.passEndsSegment Spec.Tier1.passEndsSegment
  rw [hm.bypass, hm.termAll]
  rcases passKind_cases i with ⟨k1, k2⟩ | ⟨k1, k2⟩ | ⟨k1, k2⟩ <;> simp [k1, k2, pk_bne]

/-- The segment splits agree. -/
theorem segmentRuns_eq (n i cur : Nat) :
    JPEG2000.Tier1.segmentRuns m n i cur = Spec.Tier1.segmentRuns md n i cur := by
  induction n generalizing i cur with
  | zero => rfl
  | succ n ih =>
    simp only [JPEG2000.Tier1.segmentRuns, Spec.Tier1.segmentRuns, passEndsSegment_eq hm, ih]

/-- `segmentPasses` agree. -/
theorem segmentPasses_eq (n i : Nat) :
    JPEG2000.Tier1.segmentPasses m n i = Spec.Tier1.segmentPasses md n i :=
  segmentRuns_eq hm n i 0

end style

/-! ## Coder bookkeeping -/

/-- The context relation inside either coder. -/
theorem coder_cx {start : Nat} {raw : Bool} {mq : MQ.Dec} {q : Spec.MQ.State}
    {cxs : Spec.MQ.Contexts} {r : RawState} (h : Coder start raw mq q cxs r) :
    MQEquiv.CxRel mq.cx cxs := by
  cases raw
  · exact (show MQEquiv.Rel start mq q cxs from h).cx
  · exact h.2

/-- Replacing the contexts on both sides keeps the coder relation. -/
theorem coder_setcx {start : Nat} {raw : Bool} {mq : MQ.Dec} {q : Spec.MQ.State}
    {cxs : Spec.MQ.Contexts} {r : RawState} (h : Coder start raw mq q cxs r) (cx : ByteArray)
    (cxs' : Spec.MQ.Contexts) (hc : MQEquiv.CxRel cx cxs') :
    Coder start raw { mq with cx } q cxs' r := by
  cases raw
  · have h' : MQEquiv.Rel start mq q cxs := h
    exact ⟨⟨h'.sim.c, h'.sim.a, h'.sim.ct, h'.sim.pos,
      fun j => by simpa [MQ.Dec.byteAt] using h'.sim.data j⟩, hc, h'.aLo, h'.aHi⟩
  · exact ⟨⟨h.1.c, h.1.ct, h.1.ctle, h.1.blt, h.1.pos,
      fun j => by simpa [MQ.Dec.byteAt] using h.1.data j⟩, hc⟩

/-- The Table D.7 contexts are related. -/
theorem tier1Contexts_rel :
    MQEquiv.CxRel MQ.tier1Contexts (Spec.MQ.initContexts Spec.Tier1.initialStates) := by
  rw [Spec.Tier1.initialStates_eq]
  exact MQEquiv.initContexts_rel _ (by decide)

/-! ## One pass of any style -/

/-- The pass part of the fast `runPassM` (before the segmentation symbol and the reset). -/
def passF (m : JPEG2000.Tier1.Style) (g : JPEG2000.Tier1.Geo) (K : Nat) (s : JPEG2000.Tier1.St)
    (i : Nat) : JPEG2000.Tier1.St :=
  let one : UInt32 := (1 : UInt32) <<< (JPEG2000.Tier1.passPlane K i).toUInt32
  if JPEG2000.Tier1.isRawPass m i then
    (match JPEG2000.Tier1.passKind i with
     | 0 => JPEG2000.Tier1.rawSigPropPass g m.vertCausal one s
     | 1 => JPEG2000.Tier1.rawMagRefPass g one s
     | _ => JPEG2000.Tier1.cleanupPassM g m.vertCausal one s)
  else
    (match JPEG2000.Tier1.passKind i with
     | 0 => JPEG2000.Tier1.sigPropPassM g m.vertCausal one s
     | 1 => JPEG2000.Tier1.magRefPass g one s
     | _ => JPEG2000.Tier1.cleanupPassM g m.vertCausal one s)

/-- The reset part of the fast `runPassM`. -/
def resetF (m : JPEG2000.Tier1.Style) (s : JPEG2000.Tier1.St) : JPEG2000.Tier1.St :=
  if m.reset then ⟨{ s.mq with cx := MQ.tier1Contexts }, s.flags, s.mags⟩ else s

/-- The state after a fast `runPassM`, in three parts. -/
theorem runPassM_fst (m : JPEG2000.Tier1.Style) (g : JPEG2000.Tier1.Geo) (K : Nat)
    (s : JPEG2000.Tier1.St) (bad i : Nat) :
    (JPEG2000.Tier1.runPassM m g K s bad i).1 =
      resetF m (if (m.segSymbols && JPEG2000.Tier1.passKind i == 2) = true then
        (JPEG2000.Tier1.segSymbol (passF m g K s i) bad).1 else passF m g K s i) := by
  unfold JPEG2000.Tier1.runPassM resetF passF
  dsimp only
  by_cases c2 : (m.segSymbols && JPEG2000.Tier1.passKind i == 2) = true <;>
    simp only [c2, ↓reduceIte, Bool.false_eq_true] <;>
    by_cases c1 : JPEG2000.Tier1.isRawPass m i = true <;>
    simp only [c1, ↓reduceIte, Bool.false_eq_true] <;>
    by_cases c3 : m.reset = true <;> simp only [c3, ↓reduceIte, Bool.false_eq_true] <;> rfl

section pass
variable {w h : Nat} {b : Band} {vc : Bool} {start : Nat}

/-- **Segmentation symbol** (D.5): four UNIFORM decisions on both sides. -/
theorem segSymbol_rel {s : JPEG2000.Tier1.St} {d : DecState}
    (R : RelM w h b vc start false s d) (bad : Nat) :
    RelM w h b vc start false (JPEG2000.Tier1.segSymbol s bad).1 (Spec.Tier1.segSymbol d) := by
  obtain ⟨mq, fl, mags⟩ := s
  have hc18 : Spec.Tier1.ctxUniform = 18 := rfl
  unfold JPEG2000.Tier1.segSymbol Spec.Tier1.segSymbol
  simp only [hc18]
  obtain ⟨e1, R1⟩ := decode_relM R 18
  generalize mq.decode 18 = rf at e1 R1 ⊢
  generalize d.decodeBit 18 = rs at e1 R1 ⊢
  obtain ⟨b3, mq1⟩ := rf
  obtain ⟨bs3, d1⟩ := rs
  simp only at e1 R1 ⊢
  subst e1
  obtain ⟨e2, R2⟩ := decode_relM R1 18
  generalize mq1.decode 18 = rf at e2 R2 ⊢
  generalize d1.decodeBit 18 = rs at e2 R2 ⊢
  obtain ⟨b2, mq2⟩ := rf
  obtain ⟨bs2, d2⟩ := rs
  simp only at e2 R2 ⊢
  subst e2
  obtain ⟨e3, R3⟩ := decode_relM R2 18
  generalize mq2.decode 18 = rf at e3 R3 ⊢
  generalize d2.decodeBit 18 = rs at e3 R3 ⊢
  obtain ⟨b1, mq3⟩ := rf
  obtain ⟨bs1, d3⟩ := rs
  simp only at e3 R3 ⊢
  subst e3
  obtain ⟨e4, R4⟩ := decode_relM R3 18
  generalize mq3.decode 18 = rf at e4 R4 ⊢
  generalize d3.decodeBit 18 = rs at e4 R4 ⊢
  obtain ⟨b0, mq4⟩ := rf
  obtain ⟨bs0, d4⟩ := rs
  simp only at e4 R4 ⊢
  subst e4
  split
  · exact R4
  · exact ⟨R4.coder, R4.fsize, R4.msize, R4.csize, R4.flag, R4.mag⟩

/-- **Context reset** (D.7) on both sides. -/
theorem reset_rel {raw : Bool} {s : JPEG2000.Tier1.St} {d : DecState}
    (R : RelM w h b vc start raw s d) :
    RelM w h b vc start raw ⟨{ s.mq with cx := MQ.tier1Contexts }, s.flags, s.mags⟩
      { d with cxs := Spec.MQ.initContexts Spec.Tier1.initialStates } :=
  ⟨coder_setcx R.coder _ _ tier1Contexts_rel, R.fsize, R.msize, R.csize, R.flag, R.mag⟩

variable {m : JPEG2000.Tier1.Style} {md : Mode}

/-- The pass part: raw or MQ pass of the right kind. -/
theorem passF_rel (hm : StyleRel m md) (hvc : m.vertCausal = vc) (K : Nat) (hK : K ≤ 32)
    (s : JPEG2000.Tier1.St) (d : DecState) (i : Nat)
    (R : RelM w h b vc start (Spec.Tier1.isRawPass md i) s d) :
    RelM w h b vc start (Spec.Tier1.isRawPass md i) (passF m (fgeo w h b) K s i)
      (if Spec.Tier1.isRawPass md i then Spec.Tier1.runRawPass (gV w h b vc) K d i
       else Spec.Tier1.runPass (gV w h b vc) K d i) := by
  have hp : Spec.Tier1.passPlane K i < 32 := by unfold Spec.Tier1.passPlane; omega
  have hone := hone_of _ hp
  unfold passF Spec.Tier1.runRawPass Spec.Tier1.runPass
  rw [isRawPass_eq hm, hvc]
  generalize hr : Spec.Tier1.isRawPass md i = raw at R ⊢
  cases raw
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rcases passKind_cases i with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> simp only [e1, e2]
    · exact sigPropPassM_rel _ _ hone s d R
    · exact magRefPass_relM _ _ hone s d R
    · exact cleanupPassM_rel _ _ hone s d R
  · simp only [↓reduceIte]
    rcases passKind_cases i with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> simp only [e1, e2]
    · exact rawSigPropPass_rel _ _ hone s d R
    · exact rawMagRefPass_rel _ _ hone s d R
    · exfalso
      unfold Spec.Tier1.isRawPass at hr
      simp [e2] at hr

/-- **One pass of any style** (`runPassM`): the pass, the segmentation symbol, the reset. The
coder stays in the mode of the pass (`isRawPass`). -/
theorem runPassM_rel (hm : StyleRel m md) (hvc : m.vertCausal = vc) (K : Nat) (hK : K ≤ 32)
    (s : JPEG2000.Tier1.St) (d : DecState) (bad i : Nat)
    (R : RelM w h b vc start (Spec.Tier1.isRawPass md i) s d) :
    RelM w h b vc start (Spec.Tier1.isRawPass md i)
      (JPEG2000.Tier1.runPassM m (fgeo w h b) K s bad i).1
      (Spec.Tier1.runPassM md (gV w h b vc) K d i) := by
  rw [runPassM_fst]
  unfold Spec.Tier1.runPassM resetF
  dsimp only
  have P := passF_rel hm hvc K hK s d i R
  generalize passF m (fgeo w h b) K s i = S at P ⊢
  generalize (if Spec.Tier1.isRawPass md i = true then Spec.Tier1.runRawPass (gV w h b vc) K d i
    else Spec.Tier1.runPass (gV w h b vc) K d i) = D at P ⊢
  have hcond : (m.segSymbols && JPEG2000.Tier1.passKind i == 2) =
      (md.segSymbols && Spec.Tier1.passKind i == .cleanup) := by
    rw [hm.segSymbols]
    rcases passKind_cases i with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> simp [e1, e2]
  rw [hcond]
  have S2 : RelM w h b vc start (Spec.Tier1.isRawPass md i)
      (if (md.segSymbols && Spec.Tier1.passKind i == .cleanup) = true then
        (JPEG2000.Tier1.segSymbol S bad).1 else S)
      (if (md.segSymbols && Spec.Tier1.passKind i == .cleanup) = true then
        Spec.Tier1.segSymbol D else D) := by
    split
    · rename_i hc
      have hk : Spec.Tier1.passKind i = .cleanup := by
        simp only [Bool.and_eq_true, beq_iff_eq] at hc; exact hc.2
      have hr : Spec.Tier1.isRawPass md i = false := by
        unfold Spec.Tier1.isRawPass; simp [hk]
      rw [hr] at P ⊢
      exact segSymbol_rel P bad
    · exact P
  rw [hm.reset]
  split
  · exact reset_rel S2
  · exact S2

/-- **A run of passes** `i, …, i + n − 1` of one rawness. -/
theorem runPassesM_rel (hm : StyleRel m md) (hvc : m.vertCausal = vc) (K : Nat) (hK : K ≤ 32)
    (raw : Bool) :
    ∀ n s bad d i, (∀ q < n, Spec.Tier1.isRawPass md (i + q) = raw) →
      RelM w h b vc start raw s d →
      RelM w h b vc start raw (JPEG2000.Tier1.runPassesM m (fgeo w h b) K n s bad i).1
        ((List.range' i n).foldl (Spec.Tier1.runPassM md (gV w h b vc) K) d) := by
  intro n
  induction n with
  | zero => intro s bad d i _ R; exact R
  | succ n ih =>
    intro s bad d i hr R
    have e : JPEG2000.Tier1.runPassesM m (fgeo w h b) K (n + 1) s bad i =
        JPEG2000.Tier1.runPassesM m (fgeo w h b) K n
          (JPEG2000.Tier1.runPassM m (fgeo w h b) K s bad i).1
          (JPEG2000.Tier1.runPassM m (fgeo w h b) K s bad i).2 (i + 1) := rfl
    rw [e, List.range'_succ, List.foldl_cons]
    have h0 := hr 0 (by omega)
    simp only [Nat.add_zero] at h0
    rw [← h0] at R
    have R1 := runPassM_rel hm hvc K hK s d bad i R
    rw [h0] at R1
    exact ih _ _ _ (i + 1) (fun q hq => by rw [Nat.add_assoc]; exact hr (1 + q) (by omega)) R1

end pass

/-! ## Starting a codeword segment -/

/-- A fresh raw reader on `data[start, stop)` simulates `RawState.init` on the segment. -/
theorem rawInit_sim (data : ByteArray) (start stop : Nat) (cx : ByteArray) :
    RawSim start (JPEG2000.Tier1.rawInit data start stop cx)
      (RawState.init (MQEquiv.segment data start stop)) := by
  unfold JPEG2000.Tier1.rawInit
  refine ⟨rfl, rfl, Nat.zero_le 8, by show 0 < 256; decide, rfl, ?_⟩
  intro j
  show _ = Spec.MQ.byteAt (MQEquiv.segment data start stop) j
  rw [MQEquiv.segment_byteAt]
  simp only [MQ.Dec.byteAt]
  split <;> simp

/-- **Starting a segment** whose first pass is `i`: `INITDEC` or a fresh raw reader on its own
bytes; the coder is then in the rawness of pass `i`, at the segment's start offset. -/
theorem startSegment_rel {w h : Nat} {b : Band} {vc : Bool} {start : Nat} {raw : Bool}
    {m : JPEG2000.Tier1.Style} {md : Mode} (hm : StyleRel m md) (data : ByteArray)
    (s : JPEG2000.Tier1.St) (d : DecState) (i : Nat) (sg : JPEG2000.Tier1.Seg)
    (R : RelM w h b vc start raw s d) :
    RelM w h b vc sg.start (Spec.Tier1.isRawPass md i)
      (JPEG2000.Tier1.startSegment m data s i sg)
      (Spec.Tier1.startSegment md d i (MQEquiv.segment data sg.start sg.stop)) := by
  obtain ⟨mq, fl, mags⟩ := s
  have hcx := coder_cx R.coder
  unfold JPEG2000.Tier1.startSegment Spec.Tier1.startSegment
  dsimp only
  rw [isRawPass_eq hm]
  cases hr : Spec.Tier1.isRawPass md i
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact ⟨MQEquiv.init_sim data sg.start sg.stop _ _ hcx, R.fsize, R.msize, R.csize, R.flag, R.mag⟩
  · simp only [↓reduceIte]
    exact ⟨⟨rawInit_sim data sg.start sg.stop mq.cx, hcx⟩, R.fsize, R.msize, R.csize, R.flag, R.mag⟩

/-! ## Segments are all-raw or all-MQ -/

/-- Every segment of a pass-count list starting at pass `i` is all-raw or all-MQ. -/
def Homog (md : Mode) : List Nat → Nat → Prop
  | [], _ => True
  | n :: rest, i => (∀ q < n, Spec.Tier1.isRawPass md (i + q) = Spec.Tier1.isRawPass md i) ∧
      Homog md rest (i + n)

/-- A pass that does not end a segment has the rawness of the next pass. -/
theorem isRawPass_succ (md : Mode) (j : Nat) (hne : Spec.Tier1.passEndsSegment md j = false) :
    Spec.Tier1.isRawPass md (j + 1) = Spec.Tier1.isRawPass md j := by
  unfold Spec.Tier1.passEndsSegment at hne
  unfold Spec.Tier1.isRawPass
  have k : ∀ i, Spec.Tier1.passKind i =
      if i = 0 then .cleanup else if (i - 1) % 3 = 0 then .sigProp
      else if (i - 1) % 3 = 1 then .magRef else .cleanup := by
    intro i; unfold Spec.Tier1.passKind
    split
    · rfl
    · split <;> simp_all <;> omega
  rw [k, k] at *
  cases hb : md.bypass <;> cases ht : md.termAll <;> simp only [hb, ht] at hne ⊢ <;>
    simp [pk_bne] at hne ⊢
  · by_cases j0 : j = 0
    · subst j0; simp
    · rcases (by omega : (j - 1) % 3 = 0 ∨ (j - 1) % 3 = 1 ∨ (j - 1) % 3 = 2) with e | e | e
      · have e' : j % 3 = 1 := by omega
        simp_all <;> omega
      · have e' : j % 3 = 2 := by omega
        simp_all <;> omega
      · have e' : j % 3 = 0 := by omega
        simp_all <;> omega

/-- `segmentRuns` produces homogeneous runs (the open run of `cur` passes before `i`
included). -/
theorem segmentRuns_homog (md : Mode) :
    ∀ n i cur, cur ≤ i →
      (∀ q < cur, Spec.Tier1.isRawPass md (i - cur + q) = Spec.Tier1.isRawPass md (i - cur)) →
      (0 < cur → Spec.Tier1.passEndsSegment md (i - 1) = false) →
      Homog md (Spec.Tier1.segmentRuns md n i cur) (i - cur) := by
  intro n
  induction n with
  | zero =>
    intro i cur _ hq _
    simp only [Spec.Tier1.segmentRuns]
    split
    · trivial
    · exact ⟨hq, trivial⟩
  | succ n ih =>
    intro i cur hci hq hend
    have hq' : ∀ q < cur + 1,
        Spec.Tier1.isRawPass md (i - cur + q) = Spec.Tier1.isRawPass md (i - cur) := by
      intro q hq1
      by_cases hqc : q < cur
      · exact hq q hqc
      · have : q = cur := by omega
        subst this
        by_cases c0 : q = 0
        · subst c0; rfl
        · have h1 := isRawPass_succ md (i - 1) (hend (by omega))
          have h2 := hq (q - 1) (by omega)
          rw [show i - 1 + 1 = i by omega] at h1
          rw [show i - q + (q - 1) = i - 1 by omega] at h2
          rw [show i - q + q = i by omega, h1, h2]
    simp only [Spec.Tier1.segmentRuns]
    split
    · refine ⟨hq', ?_⟩
      have := ih (i + 1) 0 (by omega) (fun q hq => by omega) (fun h => by omega)
      rw [show i + 1 - 0 = i + 1 by omega] at this
      rw [show i - cur + (cur + 1) = i + 1 by omega]
      exact this
    · rename_i hne
      have := ih (i + 1) (cur + 1) (by omega)
        (fun q hq => by rw [show i + 1 - (cur + 1) = i - cur by omega]; exact hq' q hq)
        (fun _ => by simpa using hne)
      rw [show i + 1 - (cur + 1) = i - cur by omega] at this
      exact this

/-- **The prescribed segment structure is homogeneous.** -/
theorem segmentPasses_homog (md : Mode) (n : Nat) : Homog md (Spec.Tier1.segmentPasses md n 0) 0 :=
  segmentRuns_homog md n 0 0 (Nat.le_refl _) (fun q hq => by omega) (fun h => by omega)

/-! ## The segment loop -/

/-- The spec segment of a fast segment: its bytes and pass count. -/
def specSeg (data : ByteArray) (sg : JPEG2000.Tier1.Seg) : Spec.Tier1.Segment :=
  ⟨MQEquiv.segment data sg.start sg.stop, sg.passes⟩

/-- Reading the head of a drop. -/
theorem getD_of_drop (segs : Array JPEG2000.Tier1.Seg) (j : Nat) (sg : JPEG2000.Tier1.Seg)
    (rest : List JPEG2000.Tier1.Seg) (h : segs.toList.drop j = sg :: rest) :
    segs.getD j default = sg ∧ segs.toList.drop (j + 1) = rest := by
  have h1 : segs.toList[j]? = some sg := by
    rw [← List.head?_drop, h]; rfl
  refine ⟨?_, ?_⟩
  · rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, h1]; rfl
  · rw [← List.drop_drop, h]; rfl

/-- **The segment loop**: `runSegs` over the segments `segs[j], …` (the list `L`) simulates
`Spec.Tier1.decodeSegments` over their spec segments, for a homogeneous segment structure;
the coder ends in some state. -/
theorem runSegs_rel {w h : Nat} {b : Band} {vc : Bool} {m : JPEG2000.Tier1.Style} {md : Mode}
    (hm : StyleRel m md) (hvc : m.vertCausal = vc) (K : Nat) (hK : K ≤ 32) (data : ByteArray)
    (segs : Array JPEG2000.Tier1.Seg) :
    ∀ (L : List JPEG2000.Tier1.Seg) (k j : Nat) (s : JPEG2000.Tier1.St) (bad : Nat) (d : DecState)
      (i start : Nat) (raw : Bool), segs.toList.drop j = L → k = L.length →
      Homog md (L.map (·.passes)) i → RelM w h b vc start raw s d →
      ∃ st' raw', RelM w h b vc st' raw'
        (JPEG2000.Tier1.runSegs m (fgeo w h b) K data segs k j s bad i).1
        (Spec.Tier1.decodeSegments md (gV w h b vc) K (L.map (specSeg data)) i d) := by
  intro L
  induction L with
  | nil =>
    intro k j s bad d i start raw _ hk _ R
    subst hk
    exact ⟨start, raw, R⟩
  | cons sg rest ih =>
    intro k j s bad d i start raw hd hk hh R
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
    have R2 := runPassesM_rel (start := sg.start) hm hvc K hK (Spec.Tier1.isRawPass md i) sg.passes
      _ bad _ i hh1 R1
    exact ih _ (j + 1) _ _ _ _ _ _ hd' rfl hh2 R2

end JPEG2000.Spec.Tier1EquivM
