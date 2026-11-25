import Spec.MQ

/-!
# Spec: Tier-1 code-block styles — pass sequence, codeword segments, raw bits (T.800 D.2, D.4–D.6)

Plan.md §4 (C3), §5.2 "Tier-1 / EBCOT" (staged modes). Task 3.3.

The mode-driven, data-independent part of the Tier-1 spec, shared by the decoder
(`Spec.Tier1.Decode`) and Tier-2 (task 4.4, which needs to know where codeword segments end):

* **Table A.19 — code-block style** (`Mode`, `Mode.ofStyle`): the six flags of
  `SPcod`/`SPcoc`.
* **D.2 — pass sequence** (`passKind`, `passPlane`): pass 0 is the cleanup pass of the most
  significant coded bit-plane, then significance propagation, magnitude refinement, cleanup
  for every lower bit-plane.
* **D.6 — selective arithmetic coding bypass** (`isRawPass`): with the bypass flag, the
  significance propagation and magnitude refinement passes of every bit-plane after the
  first four coded bit-planes (pass index ≥ 10: passes 0–9 are the cleanup of the first
  bit-plane and the three passes of each of the next three) are coded *raw*, without the MQ
  coder; cleanup passes always use the MQ coder.
* **D.4 / D.6, Table D.9 — codeword segments** (`passEndsSegment`, `segmentPasses`): a
  codeword segment is terminated
  - after every pass with the termination-on-each-pass flag (`termAll`);
  - otherwise, with bypass: after pass 9 (end of the MQ-coded first four bit-planes) and,
    from pass 10 on, at every switch between raw and MQ coding, i.e. after every magnitude
    refinement pass (end of a raw SP+MR pair) and after every cleanup pass (an MQ segment of
    one pass);
  - otherwise after every 109th pass (passes 108, 217, …) and after the last pass of the
    code-block: plain mode has one segment unless more than 109 passes are signalled.
  This is exactly OpenJPEG's `opj_t2_init_seg` (`maxpasses` 1 with TERMALL; 10, then
  alternately 2 and 1 with LAZY; 109 otherwise, task 4.9). T.800 bounds a code-block's
  passes by `3·Mb − 2`, which is at most `3·37 − 2 = 109` without ROI (B.10.6), so the 109-pass
  cap never splits a valid non-ROI stream; for ROI shifts or over-long pass counts we follow
  OpenJPEG for compatibility (it reads one length field per 109 passes).
* **D.6 — raw bit reader** (`RawState`, `rawBit`): bits are read most significant first; a
  byte following an `0xFF` byte carries only 7 bits (its most significant bit is a stuffed
  `0` and is skipped). As for the MQ decoder (C.3.4, `Spec.MQ.byteAt`), the segment is
  padded with `0xFF` bytes past its end, and an `0xFF` followed by a byte `> 0x8F` (a marker)
  makes every further bit a `1` without consuming anything — OpenJPEG's
  `opj_mqc_raw_decode`. For a conforming segment (a byte after `0xFF` always has a clear
  most significant bit) this only matters past the end of the data, where it yields ones.

**Predictable termination (bit 4, D.4.2)** changes only how the *encoder* flushes the MQ
coder (`ERTERM`); the decoding procedure is unchanged, so it appears nowhere in the
decoder. Its optional error-detection use (checking that the decoder consumed exactly the
segment's bytes) is not part of this spec — OpenJPEG does not check it either.
-/

namespace JPEG2000.Spec.Tier1

/-! ## Code-block style (Table A.19) -/

/-- The code-block style flags of `SPcod`/`SPcoc` (T.800 A.6.1, Table A.19). -/
structure Mode where
  /-- Bit 0: selective arithmetic coding bypass (D.6). -/
  bypass : Bool := false
  /-- Bit 1: reset context probabilities on coding pass boundaries (D.7). -/
  reset : Bool := false
  /-- Bit 2: termination on each coding pass (D.4). -/
  termAll : Bool := false
  /-- Bit 3: vertically causal context formation (D.7). -/
  vertCausal : Bool := false
  /-- Bit 4: predictable termination (D.4.2); no effect on decoding. -/
  predTerm : Bool := false
  /-- Bit 5: segmentation symbols (D.5). -/
  segSymbols : Bool := false
  deriving Repr, DecidableEq, Inhabited

/-- The plain mode: every flag clear. -/
def Mode.plain : Mode := {}

/-- The mode from the code-block style byte of `SPcod`/`SPcoc` (Table A.19, bits 0–5). -/
def Mode.ofStyle (b : Nat) : Mode where
  bypass := b % 2 == 1
  reset := b / 2 % 2 == 1
  termAll := b / 4 % 2 == 1
  vertCausal := b / 8 % 2 == 1
  predTerm := b / 16 % 2 == 1
  segSymbols := b / 32 % 2 == 1

/-- Is this the plain mode (all six flags clear)? -/
def Mode.isPlain (m : Mode) : Bool := m == Mode.plain

/-! ## D.2 — the sequence of coding passes -/

/-- The three coding pass types (D.3). -/
inductive PassKind where
  /-- Significance propagation (D.3.1). -/
  | sigProp
  /-- Magnitude refinement (D.3.3). -/
  | magRef
  /-- Cleanup (D.3.4). -/
  | cleanup
  deriving Repr, DecidableEq, Inhabited

/-- The type of pass number `i` (from 0): pass 0 is a cleanup pass, then the cycle
significance propagation, magnitude refinement, cleanup (D.2). -/
def passKind (i : Nat) : PassKind :=
  if i = 0 then .cleanup
  else match (i - 1) % 3 with
    | 0 => .sigProp
    | 1 => .magRef
    | _ => .cleanup

/-- The bit-plane of pass number `i` in a block with `K` coded bit-planes: pass 0 codes plane
`K − 1`, passes `1–3` plane `K − 2`, passes `4–6` plane `K − 3`, … -/
def passPlane (K i : Nat) : Nat := K - 1 - (i + 2) / 3

/-! ## D.6 — raw passes; D.4 / Table D.9 — codeword segments -/

/-- D.6: pass `i` is coded raw (no MQ coder): bypass mode, a significance propagation or
magnitude refinement pass, after the first four coded bit-planes (pass index ≥ 10). -/
def isRawPass (m : Mode) (i : Nat) : Bool :=
  m.bypass && 10 ≤ i && passKind i != .cleanup

/-- D.4, D.6 (Table D.9): a codeword segment is terminated after pass `i` (independently of
the number of passes actually included; the last included pass always ends the data).
Without termall and bypass, a segment holds at most 109 passes (`i % 109 = 108`, task 4.9):
OpenJPEG's `opj_t2_init_seg` cap `maxpasses = 109`; no valid non-ROI block has more passes
(`3·37 − 2`), so the cap only matters for ROI or over-long streams. -/
def passEndsSegment (m : Mode) (i : Nat) : Bool :=
  m.termAll || (m.bypass && 9 ≤ i && passKind i != .sigProp) || (!m.bypass && i % 109 == 108)

/-- Split the passes `i, i+1, …, i+n−1` into maximal runs ending at segment ends; `cur`
passes before `i` are already in the open run. -/
def segmentRuns (m : Mode) : (n i cur : Nat) → List Nat
  | 0, _, cur => if cur = 0 then [] else [cur]
  | n + 1, i, cur =>
    if passEndsSegment m i then (cur + 1) :: segmentRuns m n (i + 1) 0
    else segmentRuns m n (i + 1) (cur + 1)

/-- **The codeword-segment structure of `numPasses` consecutive passes starting at pass
`firstPass`** (pass 0 = the first cleanup pass of the code-block): the number of passes in
each piece, in order, where pieces are cut after every pass that terminates a codeword
segment (`passEndsSegment`). Every entry is positive and they sum to `numPasses`
(`segmentPasses_sum`, `segmentPasses_pos`).

* With `firstPass = 0` and all of a code-block's included passes, these are the passes of
  its codeword segments (the last one possibly incomplete): the `Segment.passes` list
  `Spec.Tier1.Decode` requires.
* With `firstPass` = the passes included by earlier layers, it splits the passes a packet
  contributes as B.10.7.2 does: the first piece continues the code-block's open segment
  unless `firstPass` starts a new one, every later piece starts a new codeword segment, and
  each piece has its own length field in the packet header. -/
def segmentPasses (m : Mode) (numPasses firstPass : Nat) : List Nat :=
  segmentRuns m numPasses firstPass 0

/-! ## D.6 — the raw bit reader -/

/-- The raw (bypass) bit reader state: the segment, the position of the next byte, the
current byte and the number of its bits still unread (as OpenJPEG's `c`, `ct`). -/
structure RawState where
  /-- The segment's bytes. -/
  data : List UInt8 := []
  /-- Index of the next byte to load. -/
  pos : Nat := 0
  /-- The byte being read. -/
  byte : Nat := 0
  /-- Bits of `byte` not yet read (the low `ct` bits). -/
  ct : Nat := 0
  deriving Repr, DecidableEq, Inhabited

/-- Start reading raw bits from a segment. -/
def RawState.init (data : List UInt8) : RawState := { data }

/-- Read one raw bit (D.6), most significant bit first, with bit-unstuffing after `0xFF`;
`0xFF` padding past the end; after `0xFF`, a byte `> 0x8F` is not consumed and reads as
`0xFF` (all ones). -/
def rawBit (s : RawState) : Bool × RawState :=
  let s :=
    if s.ct = 0 then
      if s.byte = 0xFF then
        let b := Spec.MQ.byteAt s.data s.pos
        if b > 0x8F then { s with byte := 0xFF, ct := 8 }
        else { s with byte := b, pos := s.pos + 1, ct := 7 }
      else { s with byte := Spec.MQ.byteAt s.data s.pos, pos := s.pos + 1, ct := 8 }
    else s
  let ct := s.ct - 1
  (s.byte / 2 ^ ct % 2 == 1, { s with ct })

/-- Read `n` raw bits. -/
def rawBits (s : RawState) : Nat → List Bool × RawState
  | 0 => ([], s)
  | n + 1 =>
    let (b, s) := rawBit s
    let (bs, s) := rawBits s n
    (b :: bs, s)

/-! ## Lemmas -/

/-- The pass sequence starts with a cleanup pass, then cycles SP, MR, CU. -/
theorem passKind_cycle (j : Nat) :
    passKind (3 * j + 1) = .sigProp ∧ passKind (3 * j + 2) = .magRef ∧
      passKind (3 * j + 3) = .cleanup := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [passKind] <;> omega

/-- The passes `3j+1, 3j+2, 3j+3` all code bit-plane `K − 2 − j`. -/
theorem passPlane_group (K j : Nat) :
    passPlane K (3 * j + 1) = K - 2 - j ∧ passPlane K (3 * j + 2) = K - 2 - j ∧
      passPlane K (3 * j + 3) = K - 2 - j := by
  simp only [passPlane]; omega

/-- `segmentRuns` covers the open run and the `n` new passes. -/
theorem segmentRuns_sum (m : Mode) (n i cur : Nat) : (segmentRuns m n i cur).sum = n + cur := by
  induction n generalizing i cur with
  | zero => by_cases h : cur = 0 <;> simp [segmentRuns, h]
  | succ n ih =>
    simp only [segmentRuns]
    split
    · simp [ih]; omega
    · rw [ih]; omega

/-- `segmentPasses` partitions the passes: its entries sum to `numPasses`. -/
theorem segmentPasses_sum (m : Mode) (numPasses firstPass : Nat) :
    (segmentPasses m numPasses firstPass).sum = numPasses := by
  simp [segmentPasses, segmentRuns_sum]

/-- Every run of `segmentRuns` is non-empty. -/
theorem segmentRuns_pos (m : Mode) (n i cur : Nat) : ∀ k ∈ segmentRuns m n i cur, 0 < k := by
  induction n generalizing i cur with
  | zero => by_cases h : cur = 0 <;> simp [segmentRuns, h] <;> omega
  | succ n ih =>
    simp only [segmentRuns]
    split
    · intro k hk
      simp only [List.mem_cons] at hk
      rcases hk with rfl | hk
      · omega
      · exact ih _ _ k hk
    · exact ih _ _

/-- Every piece of `segmentPasses` holds at least one pass. -/
theorem segmentPasses_pos (m : Mode) (numPasses firstPass : Nat) :
    ∀ k ∈ segmentPasses m numPasses firstPass, 0 < k :=
  segmentRuns_pos m numPasses firstPass 0

/-- Without termall and bypass no pass before pass 108 ends a segment (the 109-pass cap,
task 4.9, ends one after pass 108, 217, …). -/
theorem segmentRuns_noTerm (m : Mode) (h1 : m.termAll = false) (h2 : m.bypass = false)
    (n i cur : Nat) (hc : i + n ≤ 109) :
    segmentRuns m n i cur = if n + cur = 0 then [] else [n + cur] := by
  induction n generalizing i cur with
  | zero => simp [segmentRuns]
  | succ n ih =>
    simp only [segmentRuns, passEndsSegment, h1, h2, Bool.false_and, Bool.or_false,
      Bool.false_or, Bool.not_false, Bool.true_and]
    by_cases hi : i = 108
    · subst hi
      have hn : n = 0 := by omega
      subst hn
      simp [segmentRuns, Nat.add_comm]
    · have : (i % 109 == 108) = false := by
        rw [Nat.mod_eq_of_lt (by omega)]; simpa using hi
      rw [this, ih (i + 1) (cur + 1) (by omega)]
      simp only [Bool.false_eq_true, ↓reduceIte]
      split <;> split <;> first | rfl | omega | simp_all <;> omega

/-- Plain mode (and any mode without termall and bypass): one codeword segment holding all
the passes, as long as they end by pass 108 (`firstPass + numPasses ≤ 109`; beyond, the
109-pass cap of task 4.9 starts a new segment). -/
theorem segmentPasses_plain (m : Mode) (h1 : m.termAll = false) (h2 : m.bypass = false)
    (numPasses firstPass : Nat) (hc : firstPass + numPasses ≤ 109) :
    segmentPasses m numPasses firstPass = if numPasses = 0 then [] else [numPasses] := by
  simp [segmentPasses, segmentRuns_noTerm m h1 h2 _ _ _ hc]

/-- The segment structure depends only on the termall and bypass flags. -/
theorem segmentPasses_congr {m m' : Mode} (h1 : m.termAll = m'.termAll)
    (h2 : m.bypass = m'.bypass) (numPasses firstPass : Nat) :
    segmentPasses m numPasses firstPass = segmentPasses m' numPasses firstPass := by
  have he : passEndsSegment m = passEndsSegment m' := by
    funext i; simp only [passEndsSegment, h1, h2]
  have : ∀ n i cur, segmentRuns m n i cur = segmentRuns m' n i cur := by
    intro n
    induction n with
    | zero => intro i cur; rfl
    | succ n ih => intro i cur; simp only [segmentRuns, he, ih]
  exact this _ _ _

/-- Termall: one pass per segment. -/
theorem segmentRuns_termAll (m : Mode) (h : m.termAll = true) (n i : Nat) :
    segmentRuns m n i 0 = List.replicate n 1 := by
  induction n generalizing i with
  | zero => simp [segmentRuns]
  | succ n ih => simp [segmentRuns, passEndsSegment, h, ih, List.replicate_succ]

/-- Termall: `segmentPasses` gives one pass per segment. -/
theorem segmentPasses_termAll (m : Mode) (h : m.termAll = true) (numPasses firstPass : Nat) :
    segmentPasses m numPasses firstPass = List.replicate numPasses 1 :=
  segmentRuns_termAll m h numPasses firstPass

/-- No raw pass in plain mode (nor in any mode without bypass). -/
theorem isRawPass_noBypass (m : Mode) (h : m.bypass = false) (i : Nat) : isRawPass m i = false := by
  simp [isRawPass, h]

end JPEG2000.Spec.Tier1
