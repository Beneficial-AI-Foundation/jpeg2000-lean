import JPEG2000.MQ
import Spec.MQ
import Spec.MQTable

/-!
# C2: the fast MQ decoder equals the Annex C flowchart decoder

Plan.md §4 (C2 "MQ conformance"), §5.1 (spec/implementation pattern), §5.2 "MQ decoder";
T.800 Annex C: C.3.1 (registers), C.3.2 `DECODE` (Figures C.15–C.17), C.3.3 `RENORMD`
(Figure C.18), C.3.4 `BYTEIN` (Figure C.19), C.3.5 `INITDEC` (Figure C.20), Table C.2.

The fast decoder `JPEG2000.MQ` (UInt32 registers, packed context bytes, a 256-entry transition
table) is related step by step to the specification `JPEG2000.Spec.MQ` (Nat registers, a
`List UInt8` segment, `List CxState` contexts):

* `Sim start d s` — the register simulation: `C`, `A`, `CT` agree through `toNat`, the byte
  pointer is offset by `start` (`d.pos = start + s.pos`) and every byte the fast decoder can
  read at `start + j` equals the spec's `byteAt s.data j` (`0xFF` past the segment end).
* `CxRel cx cxs` — the context byte array has the length of the spec context list and every
  packed byte decodes (`Spec.MQTable.stateOf`) to the spec context, out-of-range included.
* `Rel start d s cxs` — both, plus the `DECODE` invariant `0x8000 ≤ A < 0x10000`.

Main results: `bytein_sim`, `renormd_sim`, `step_eq_ref` (the allocation-free `Dec.step`,
whose `RENORMD` runs on unboxed registers (`renormS_eq`), equals the path-by-path flowchart form
`stepRef`), `decode_sim` (one decision: same bit, relation preserved), `init_sim` (for any `data start stop`, with spec data `segment data start stop`),
`decodeList_sim`, the general `decode_init_eq` (the form Tier-1 uses: a segment inside a larger
buffer) and the headline `decodeAll_eq`:
`JPEG2000.MQ.decodeAll data inits cxList = Spec.MQ.decodeAll data.toList inits cxList` for all
`data`, `cxList` and every `inits` whose entries are `< 128` (a packed context byte holds a
7-bit index; Table C.2 indices are `< 47`).

## Termination of `RENORMD`

Both decoders write `RENORMD` (a do-while loop) with fuel 16. "Termination" means that 16
iterations always suffice, i.e. the loop exits through its test `A AND 0x8000 ≠ 0` and not
through fuel exhaustion. For the spec this is `Spec.MQ.renormd_fuel_suffices`; for the fast
decoder it is `renormd_fuel_suffices_fast` below (proved directly: `A` evolves independently
of the other registers), and `DECODE` only enters `RENORMD` with `0 < A < 0x8000`
(`Spec.MQ.decode_A_range` + `Rel`). Since the simulation is exact, the fuel bound never
changes a result on either side.
-/

namespace JPEG2000.Spec.MQEquiv

open JPEG2000 JPEG2000.MQ JPEG2000.Spec.MQTable

/-- Register simulation between the fast decoder `d` (segment starting at buffer offset
`start`) and the spec state `s` (T.800 C.3.1). -/

structure Sim (start : Nat) (d : Dec) (s : Spec.MQ.State) : Prop where
  /-- `C` agrees. -/
  c : d.c.toNat = s.C
  /-- `A` agrees. -/
  a : d.a.toNat = s.A
  /-- `CT` agrees. -/
  ct : d.ct.toNat = s.CT
  /-- `BP` agrees, offset by the segment start. -/
  pos : d.pos = start + s.pos
  /-- Every byte read agrees (`0xFF` past the end on both sides). -/
  data : ∀ j, (d.byteAt (start + j)).toNat = Spec.MQ.byteAt s.data j

/-- A byte read by the fast decoder is below 256. -/

theorem byteAt_lt (d : Dec) (i : Nat) : (d.byteAt i).toNat < 256 := by
  unfold Dec.byteAt; split
  · simp; exact UInt8.toNat_lt _
  · decide

/-- `BYTEIN` (C.3.4, Figure C.19) preserves the register simulation. -/

theorem bytein_sim {start : Nat} {d : Dec} {s : Spec.MQ.State} (h : Sim start d s) :
    Sim start d.bytein (Spec.MQ.bytein s) := by
  have h0 : (d.byteAt d.pos).toNat = Spec.MQ.byteAt s.data s.pos := by rw [h.pos]; exact h.data _
  have h1 : (d.byteAt (d.pos + 1)).toNat = Spec.MQ.byteAt s.data (s.pos + 1) := by
    rw [h.pos, Nat.add_assoc]; exact h.data _
  have l1 := byteAt_lt d (d.pos + 1)
  have c0 : d.byteAt d.pos = 0xFF ↔ Spec.MQ.byteAt s.data s.pos = 0xFF := by
    rw [← h0, ← UInt32.toNat_inj]; rfl
  have c1 : d.byteAt (d.pos + 1) > 0x8F ↔ Spec.MQ.byteAt s.data (s.pos + 1) > 0x8F := by
    rw [← h1, GT.gt, UInt32.lt_iff_toNat_lt]; rfl
  have hc := h.c
  unfold Dec.bytein Spec.MQ.bytein
  simp only [c0, c1]
  by_cases p0 : Spec.MQ.byteAt s.data s.pos = 0xFF
  · by_cases p1 : Spec.MQ.byteAt s.data (s.pos + 1) > 0x8F
    · simp only [p0, p1, ↓reduceIte]
      exact ⟨by simp [UInt32.toNat_add, hc], h.a, by simp, h.pos,
        fun j => by simpa [Dec.byteAt] using h.data j⟩
    · simp only [p0, p1, ↓reduceIte]
      exact ⟨by simp [UInt32.toNat_add, UInt32.toNat_shiftLeft, Nat.shiftLeft_eq, hc, h1],
        h.a, by simp, by simp [h.pos]; omega, fun j => by simpa [Dec.byteAt] using h.data j⟩
  · simp only [p0, ↓reduceIte]
    exact ⟨by simp [UInt32.toNat_add, UInt32.toNat_shiftLeft, Nat.shiftLeft_eq, hc, h1],
        h.a, by simp, by simp [h.pos]; omega, fun j => by simpa [Dec.byteAt] using h.data j⟩

private theorem nat_and_8000_ne (x : Nat) : x &&& 0x8000 ≠ 0 ↔ x / 0x8000 % 2 = 1 := by
  have key : x.testBit 15 = decide (x / 0x8000 % 2 = 1) := Nat.testBit_eq_decide_div_mod_eq
  constructor
  · intro h
    by_cases hc : x / 0x8000 % 2 = 1
    · exact hc
    exfalso
    apply h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.zero_testBit]
    show (x.testBit i && (2^15).testBit i) = false
    rw [Nat.testBit_two_pow]
    by_cases hi : 15 = i
    · subst hi; simp [key, hc]
    · simp [hi]
  · intro h hz
    have := congrArg (Nat.testBit · 15) hz
    simp only [Nat.testBit_and, Nat.zero_testBit] at this
    have h2 : (0x8000 : Nat).testBit 15 = true := by decide
    rw [h2, key] at this
    simp [h] at this

private theorem u32_bne (x : UInt32) : (x != 0) = !decide (x.toNat = 0) := by
  by_cases h : x = 0
  · subst h; rfl
  · have : x.toNat ≠ 0 := fun h' => h (UInt32.toNat_inj.mp (by simpa using h'))
    simp [h, this]

/-- The fast bit test `A AND 0x8000 ≠ 0` is `Spec.MQ.bit15`. -/

theorem bit_fast (a : UInt32) : (a &&& 0x8000 != 0) = Spec.MQ.bit15 a.toNat := by
  have h := nat_and_8000_ne a.toNat
  simp only [Spec.MQ.bit15, u32_bne, UInt32.toNat_and]
  by_cases hc : a.toNat / 0x8000 % 2 = 1 <;> simp_all

/-- `BYTEIN` does not touch the contexts. -/

theorem bytein_cx (d : Dec) : d.bytein.cx = d.cx := by
  unfold Dec.bytein; split <;> (try split) <;> rfl

/-- `CT ≥ 7` after the spec `BYTEIN`. -/

theorem spec_bytein_CT (s : Spec.MQ.State) : 7 ≤ (Spec.MQ.bytein s).CT := by
  unfold Spec.MQ.bytein; split <;> (try split) <;> simp

/-- One `RENORMD` body (C.3.3) preserves the simulation and the contexts. -/

theorem renormStep_sim {start : Nat} {d : Dec} {s : Spec.MQ.State} (h : Sim start d s) :
    Sim start (Dec.renormStep d) (Spec.MQ.renormStep s) ∧ (Dec.renormStep d).cx = d.cx := by
  have c0 : d.ct = 0 ↔ s.CT = 0 := by rw [← h.ct, ← UInt32.toNat_inj]; rfl
  have pre : Sim start (if d.ct = 0 then d.bytein else d) (if s.CT = 0 then Spec.MQ.bytein s else s)
      ∧ (if s.CT = 0 then Spec.MQ.bytein s else s).CT ≠ 0
      ∧ (if d.ct = 0 then d.bytein else d).cx = d.cx := by
    simp only [c0]
    by_cases p : s.CT = 0
    · simp only [p, ↓reduceIte]
      exact ⟨bytein_sim h, by have := spec_bytein_CT s; omega, bytein_cx d⟩
    · simp only [p, ↓reduceIte]; exact ⟨h, p, by trivial⟩
  obtain ⟨h', hct, hcx⟩ := pre
  unfold Dec.renormStep Spec.MQ.renormStep
  dsimp only
  generalize (if d.ct = 0 then d.bytein else d) = d' at h' hcx ⊢
  generalize (if s.CT = 0 then Spec.MQ.bytein s else s) = s' at h' hct ⊢
  have hct' := h'.ct
  have ha := h'.a
  have hc := h'.c
  refine ⟨⟨?_, ?_, ?_, h'.pos, fun j => by simpa [Dec.byteAt] using h'.data j⟩, hcx⟩
  · simp [UInt32.toNat_shiftLeft, Nat.shiftLeft_eq, hc]
  · have e : (65535 : UInt32).toNat = 2 ^ 16 - 1 := rfl
    simp only [UInt32.toNat_and, UInt32.toNat_shiftLeft, Nat.shiftLeft_eq, e,
      Nat.and_two_pow_sub_one_eq_mod, ha]
    simp
  · have : (1 : UInt32) ≤ d'.ct := by rw [UInt32.le_iff_toNat_le]; simp; omega
    rw [UInt32.toNat_sub_of_le _ _ this]; simp [hct']

/-- The fuelled `RENORMD` loop preserves the simulation and the contexts, for any fuel. -/

theorem renormLoop_sim (n : Nat) {start : Nat} {d : Dec} {s : Spec.MQ.State} (h : Sim start d s) :
    Sim start (Dec.renormLoop n d) (Spec.MQ.renormLoop n s) ∧ (Dec.renormLoop n d).cx = d.cx := by
  induction n generalizing d s with
  | zero => exact ⟨h, rfl⟩
  | succ n ih =>
    obtain ⟨h1, hcx1⟩ := renormStep_sim h
    have hb : (d.renormStep.a &&& 0x8000 != 0) = Spec.MQ.bit15 (Spec.MQ.renormStep s).A := by
      rw [bit_fast, h1.a]
    simp only [Dec.renormLoop, Spec.MQ.renormLoop, hb]
    split
    · exact ⟨h1, hcx1⟩
    · obtain ⟨h2, hcx2⟩ := ih h1
      exact ⟨h2, hcx2.trans hcx1⟩

/-- `RENORMD` (C.3.3, Figure C.18) preserves the simulation and the contexts. -/

theorem renormd_sim {start : Nat} {d : Dec} {s : Spec.MQ.State} (h : Sim start d s) :
    Sim start (Dec.renormd d) (Spec.MQ.renormd s) ∧ (Dec.renormd d).cx = d.cx :=
  renormLoop_sim 16 h

/-- `RENORMD` does not touch the stored decision. -/
theorem renormLoop_bit (n : Nat) (d : Dec) : (Dec.renormLoop n d).bit = d.bit := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
    have h1 : (Dec.renormStep d).bit = d.bit := by
      unfold Dec.renormStep Dec.bytein; split <;> (try split) <;> (try split) <;> rfl
    simp only [Dec.renormLoop]
    split
    · exact h1
    · rw [ih, h1]

/-- `RENORMD` does not touch the stored decision. -/
theorem renormd_bit (d : Dec) : (Dec.renormd d).bit = d.bit := renormLoop_bit 16 d

/-- The packed context array `cx` stands for the spec context list `cxs`: same length, and
every index (in range or not) reads the same state. -/

def CxRel (cx : ByteArray) (cxs : Spec.MQ.Contexts) : Prop :=
  cx.size = cxs.length ∧ ∀ k, stateOf (ctxGet cx k) = cxs.get k

/-- `ctxSet` keeps the size of the context array. -/

theorem ctxSet_size (cx : ByteArray) (i : Nat) (v : UInt8) : (ctxSet cx i v).size = cx.size := by
  unfold ctxSet; split
  · cases cx; simp [ByteArray.set, ByteArray.size]
  · rfl

/-- Reading a context after `ctxSet`. -/

theorem ctxGet_ctxSet (cx : ByteArray) (i k : Nat) (v : UInt8) :
    ctxGet (ctxSet cx i v) k = if i = k ∧ i < cx.size then v else ctxGet cx k := by
  by_cases hi : i < cx.size
  · have hs := ctxSet_size cx i v
    unfold ctxGet
    by_cases hk : k < cx.size
    · simp only [hs, hk, ↓reduceDIte, hi]
      unfold ctxSet
      simp only [hi, ↓reduceDIte]
      cases cx
      simp [ByteArray.set, ByteArray.get, Array.getElem_set]
    · have hn : ¬(i = k ∧ i < cx.size) := by omega
      simp only [hs, hk, ↓reduceDIte, hn, ↓reduceIte]
  · have : ctxSet cx i v = cx := by unfold ctxSet; simp [hi]
    rw [this]; simp [hi]

/-- Reading a spec context after `Contexts.put`. -/

theorem contexts_get_put (cxs : Spec.MQ.Contexts) (i k : Nat) (st : Spec.MQ.CxState) :
    (cxs.put i st).get k = if i = k ∧ i < cxs.length then st else cxs.get k := by
  simp only [Spec.MQ.Contexts.put, Spec.MQ.Contexts.get, List.getD_eq_getElem?_getD,
    List.getElem?_set]
  by_cases h1 : i = k
  · subst h1; by_cases h2 : i < cxs.length <;> simp [h2]
  · simp [h1]

/-- Writing related states at the same index preserves `CxRel` (out of range: both no-ops). -/

theorem cxRel_set {cx : ByteArray} {cxs : Spec.MQ.Contexts} (h : CxRel cx cxs) (i : Nat) (v : UInt8)
    (st : Spec.MQ.CxState) (hv : stateOf v = st) : CxRel (ctxSet cx i v) (cxs.put i st) := by
  refine ⟨by rw [ctxSet_size, h.1]; simp [Spec.MQ.Contexts.put], fun k => ?_⟩
  rw [ctxGet_ctxSet, contexts_get_put, ← h.1]
  split
  · exact hv
  · exact h.2 k

private theorem u8_bne (x : UInt8) : (x != 0) = !decide (x.toNat = 0) := by
  by_cases h : x = 0
  · subst h; rfl
  · have : x.toNat ≠ 0 := fun h' => h (UInt8.toNat_inj.mp (by simpa using h'))
    simp [h, this]

/-- The fast `MPS(CX)` bit test is the `mps` of `stateOf`. -/

theorem mps_fast (s : UInt8) : (s &&& 1 != 0) = (stateOf s).mps := by
  have h : (s &&& 1).toNat = s.toNat % 2 := by
    rw [UInt8.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod _ 1
  simp only [stateOf, u8_bne, h]
  by_cases hc : s.toNat % 2 = 1
  · simp [hc]
  · have : s.toNat % 2 = 0 := by omega
    simp [this]

/-- The full simulation relation used for `DECODE`: registers, contexts and the invariant
`0x8000 ≤ A < 0x10000` (`Spec.MQ.decode_A_range`). -/

structure Rel (start : Nat) (d : Dec) (s : Spec.MQ.State) (cxs : Spec.MQ.Contexts) : Prop where
  /-- Registers, pointer and data. -/
  sim : Sim start d s
  /-- Contexts. -/
  cx : CxRel d.cx cxs
  /-- `A ≥ 0x8000`. -/
  aLo : 0x8000 ≤ s.A
  /-- `A < 0x10000`. -/
  aHi : s.A < 0x10000

private theorem sim_upd {start : Nat} {d : Dec} {s : Spec.MQ.State} (h : Sim start d s)
    (a c : UInt32)
    (A C : Nat) (ha : a.toNat = A) (hc : c.toNat = C) (cx : ByteArray) (bit : Bool) :
    Sim start { d with a, c, cx, bit } { s with A, C } :=
  ⟨hc, ha, h.ct, h.pos, fun j => by simpa [Dec.byteAt] using h.data j⟩

/-! ## The flowchart shape of `Dec.step` -/

/-- `DECODE` (Figure C.15) written path by path, as the flowchart (and as the fast decoder
was written before task 8.2a): `LPS_EXCHANGE` + `RENORMD`; the MPS path without
renormalisation; `MPS_EXCHANGE` (both branches) + `RENORMD`. The decision is stored in
`bit`. `step_eq_ref` proves the scalar-selection form `Dec.step` equal to it. -/
def stepRef (d : Dec) (i : Nat) : Dec :=
  let s := ctxGet d.cx i
  let e := entry s
  let qe := e >>> 16
  let mps := s &&& 1 != 0
  let a := d.a - qe
  if d.c >>> 16 < qe then
    -- LPS_EXCHANGE
    if a < qe then
      Dec.renormd { d with a := qe, cx := ctxSet d.cx i (e >>> 8).toUInt8, bit := mps }
    else
      Dec.renormd { d with a := qe, cx := ctxSet d.cx i e.toUInt8, bit := !mps }
  else
    let c := d.c - (qe <<< 16)
    if a &&& 0x8000 != 0 then
      { d with a, c, bit := mps }
    else if a < qe then
      -- MPS_EXCHANGE, LPS branch
      Dec.renormd { d with a, c, cx := ctxSet d.cx i e.toUInt8, bit := !mps }
    else
      -- MPS_EXCHANGE, MPS branch
      Dec.renormd { d with a, c, cx := ctxSet d.cx i (e >>> 8).toUInt8, bit := mps }

/-- The scalar `RENORMD` loop `Dec.renormS` is `renormLoop` on the updated record. -/
theorem renormS_eq (d : Dec) (i : Nat) (ns : UInt8) (bit : Bool) (n : Nat)
    (a c ct : UInt32) (pos : Nat) :
    Dec.renormS d i ns bit n a c ct pos =
      Dec.renormLoop n { d with a, c, ct, pos, cx := ctxSet d.cx i ns, bit } := by
  induction n generalizing a c ct pos with
  | zero => rfl
  | succ n ih =>
    have hb : ∀ (a c ct : UInt32) (pos j : Nat) (cx : ByteArray) (bit : Bool),
        Dec.byteAt { d with a, c, ct, pos, cx, bit } j = d.byteAt j := fun _ _ _ _ _ _ _ => rfl
    simp only [Dec.renormS, Dec.renormLoop, Dec.renormStep, Dec.bytein, ih, hb]
    by_cases h0 : ct = 0
    · subst h0
      by_cases h1 : d.byteAt pos = 0xFF
      · by_cases h2 : d.byteAt (pos + 1) > 0x8F <;> simp [h1, h2]
      · simp [h1]
    · simp [h0]

/-- `ctxSet` of the byte just read leaves the context array unchanged. -/
theorem ctxSet_ctxGet (cx : ByteArray) (i : Nat) : ctxSet cx i (ctxGet cx i) = cx := by
  unfold ctxSet ctxGet
  split
  · cases cx
    simp [ByteArray.set, ByteArray.get]
  · rfl

/-- `Dec.step` is the flowchart `stepRef`. -/
theorem step_eq_ref (d : Dec) (i : Nat) : d.step i = stepRef d i := by
  simp only [Dec.step, stepRef, renormS_eq, Dec.renormd]
  generalize hs : ctxGet d.cx i = s
  by_cases p1 : d.c >>> 16 < entry s >>> 16
  · by_cases p2 : d.a - entry s >>> 16 < entry s >>> 16
    · simp only [p1, p2, decide_true, Bool.not_true, Bool.false_and, Bool.true_bne,
        Bool.not_false, Bool.true_and, ↓reduceIte, Bool.false_eq_true]
    · simp only [p1, p2, decide_true, decide_false, Bool.not_true, Bool.false_and,
        Bool.bne_false, Bool.not_false, Bool.true_and, ↓reduceIte, Bool.false_eq_true]
  · by_cases p3 : (d.a - entry s >>> 16 &&& 32768 != 0) = true
    · simp only [p1, p3, decide_false, Bool.not_false, Bool.true_and, Bool.not_true,
        Bool.false_and, ↓reduceIte, Bool.false_eq_true, Dec.renormLoop]
      rw [← hs, ctxSet_ctxGet]
    · by_cases p2 : d.a - entry s >>> 16 < entry s >>> 16
      · simp only [p1, p2, p3, decide_true, decide_false, Bool.not_false, Bool.true_and,
          Bool.and_true, Bool.false_bne, ↓reduceIte, Bool.false_eq_true]
      · simp only [p1, p2, p3, decide_false, Bool.not_false, Bool.true_and,
          Bool.false_bne, ↓reduceIte, Bool.false_eq_true]

/-- `DECODE` (C.3.2, Figures C.15–C.17): from related states, the fast and the spec decoder
return the same decision `D` and related states. -/

theorem decode_sim {start : Nat} {d : Dec} {s : Spec.MQ.State} {cxs : Spec.MQ.Contexts}
    (h : Rel start d s cxs) (i : Nat) :
    (d.decode i).1 = (Spec.MQ.decode s cxs i).1 ∧
    Rel start (d.decode i).2 (Spec.MQ.decode s cxs i).2.1 (Spec.MQ.decode s cxs i).2.2 := by
  have hA := Spec.MQ.decode_A_range s cxs i h.aLo h.aHi
  suffices H : (d.decode i).1 = (Spec.MQ.decode s cxs i).1 ∧
      Sim start (d.decode i).2 (Spec.MQ.decode s cxs i).2.1 ∧
      CxRel (d.decode i).2.cx (Spec.MQ.decode s cxs i).2.2 from
    ⟨H.1, H.2.1, H.2.2, hA.1, hA.2⟩
  have hst : stateOf (ctxGet d.cx i) = cxs.get i := h.cx.2 i
  have hagree := qeTab_agree (ctxGet d.cx i)
  have hmps := mps_fast (ctxGet d.cx i)
  rw [hst] at hagree hmps
  obtain ⟨hq, hn, hl⟩ := hagree
  have hqb := Spec.MQ.qeAt_qe_bounds (cxs.get i).index
  have hcx := h.cx
  simp only [Dec.decode, step_eq_ref, stepRef, Spec.MQ.decode, Spec.MQ.lpsExchange,
    Spec.MQ.mpsExchange]
  generalize entry (ctxGet d.cx i) = e at hq hn hl ⊢
  generalize cxs.get i = st at hq hn hl hmps hqb ⊢
  generalize (Spec.MQ.qeAt st.index).qe = Q at hq hqb ⊢
  have hsa := h.sim.a
  have hsc := h.sim.c
  have hAlo := h.aLo
  have hAhi := h.aHi
  have hClt : s.C < 2 ^ 32 := hsc ▸ d.c.toNat_lt
  have hle : e >>> 16 ≤ d.a := by rw [UInt32.le_iff_toNat_le]; omega
  have ha : (d.a - e >>> 16).toNat = (s.A - Q) % 65536 := by
    rw [UInt32.toNat_sub_of_le _ _ hle]; omega
  have c1 : d.c >>> 16 < e >>> 16 ↔ s.chigh < Q := by
    rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_shiftRight, hq, hsc, Spec.MQ.State.chigh]
    simp [Nat.shiftRight_eq_div_pow]; omega
  have c2 : d.a - e >>> 16 < e >>> 16 ↔ (s.A - Q) % 65536 < Q := by
    rw [UInt32.lt_iff_toNat_lt, ha, hq]
  have c3 : (d.a - e >>> 16 &&& 32768 != 0) = Spec.MQ.bit15 ((s.A - Q) % 65536) := by
    rw [bit_fast, ha]
  simp only [c1, c2, c3, hmps]
  by_cases p1 : s.chigh < Q
  · have hsim : ∀ cx' bit, Sim start { d with a := e >>> 16, cx := cx', bit } { s with A := Q } :=
      fun cx' bit => sim_upd h.sim _ d.c _ s.C hq hsc cx' bit
    by_cases p2 : (s.A - Q) % 65536 < Q
    · simp only [p1, p2, ↓reduceIte]
      obtain ⟨r1, r2⟩ := renormd_sim (hsim (ctxSet d.cx i (e >>> 8).toUInt8) st.mps)
      exact ⟨renormd_bit _, r1, r2 ▸ cxRel_set hcx i _ _ hn⟩
    · simp only [p1, p2, ↓reduceIte]
      obtain ⟨r1, r2⟩ := renormd_sim (hsim (ctxSet d.cx i e.toUInt8) !st.mps)
      exact ⟨renormd_bit _, r1, r2 ▸ cxRel_set hcx i _ _ hl⟩
  · have p1' : ¬ s.C / 65536 % 65536 < Q := p1
    have hcc : (d.c - e >>> 16 <<< 16).toNat = (s.chigh - Q) * 65536 + s.C % 65536 := by
      have h16 : (e >>> 16 <<< 16).toNat = Q * 65536 := by
        rw [UInt32.toNat_shiftLeft, hq]; simp [Nat.shiftLeft_eq]; omega
      have hle2 : e >>> 16 <<< 16 ≤ d.c := by
        rw [UInt32.le_iff_toNat_le, h16, hsc]; omega
      rw [UInt32.toNat_sub_of_le _ _ hle2, h16, hsc]; simp only [Spec.MQ.State.chigh]; omega
    have hsim : ∀ cx' bit,
        Sim start { d with a := d.a - e >>> 16, c := d.c - e >>> 16 <<< 16, cx := cx', bit }
        { s with A := (s.A - Q) % 65536, C := (s.chigh - Q) * 65536 + s.C % 65536 } :=
      fun cx' bit => sim_upd h.sim _ _ _ _ ha hcc cx' bit
    by_cases p3 : Spec.MQ.bit15 ((s.A - Q) % 65536) = true
    · simp only [p1, p3, ↓reduceIte]
      exact ⟨trivial, hsim d.cx st.mps, hcx⟩
    · by_cases p2 : (s.A - Q) % 65536 < Q
      · simp only [p1, p2, p3, Bool.false_eq_true, ↓reduceIte]
        obtain ⟨r1, r2⟩ := renormd_sim (hsim (ctxSet d.cx i e.toUInt8) !st.mps)
        exact ⟨renormd_bit _, r1, r2 ▸ cxRel_set hcx i _ _ hl⟩
      · simp only [p1, p2, p3, Bool.false_eq_true, ↓reduceIte]
        obtain ⟨r1, r2⟩ := renormd_sim (hsim (ctxSet d.cx i (e >>> 8).toUInt8) st.mps)
        exact ⟨renormd_bit _, r1, r2 ▸ cxRel_set hcx i _ _ hn⟩

/-- Decoding a context sequence: same decisions, related final states. -/

theorem decodeList_sim {start : Nat} {d : Dec} {s : Spec.MQ.State} {cxs : Spec.MQ.Contexts}
    (h : Rel start d s cxs) (l : List Nat) :
    (d.decodeList l).1 = (Spec.MQ.decodeMany s cxs l).1 ∧
    Rel start (d.decodeList l).2 (Spec.MQ.decodeMany s cxs l).2.1
      (Spec.MQ.decodeMany s cxs l).2.2 := by
  induction l generalizing d s cxs with
  | nil => exact ⟨rfl, h⟩
  | cons i rest ih =>
    obtain ⟨e1, h1⟩ := decode_sim h i
    obtain ⟨e2, h2⟩ := ih h1
    simp only [Dec.decodeList, Spec.MQ.decodeMany]
    exact ⟨by rw [e1, e2], h2⟩

/-- The segment `data[start, stop)` as a list (clamped to `data.size`; empty if
`stop ≤ start`). -/

def segment (data : ByteArray) (start stop : Nat) : List UInt8 :=
  (data.data.toList.drop start).take (stop - start)

/-- Spec byte `j` of the segment is the fast decoder's byte `start + j` (`0xFF` past the end). -/

theorem segment_byteAt (data : ByteArray) (start stop j : Nat) :
    Spec.MQ.byteAt (segment data start stop) j =
      if h : start + j < min stop data.size then (data.get (start + j) (by omega)).toNat
      else 0xFF := by
  simp only [Spec.MQ.byteAt, segment, List.getD_eq_getElem?_getD, List.getElem?_take,
    List.getElem?_drop]
  by_cases hf : start + j < min stop data.size
  · have hj' : j < stop - start := by omega
    have hs : start + j < data.data.size := Nat.lt_of_lt_of_le hf (Nat.min_le_right _ _)
    simp only [hf, hj', ↓reduceIte, ↓reduceDIte, Array.getElem?_toList]
    rw [Array.getElem?_eq_getElem hs]
    rfl
  · simp only [hf, ↓reduceDIte]
    by_cases hj' : j < stop - start
    · have : data.data.size ≤ start + j := by
        have : ¬ start + j < data.size := by omega
        exact Nat.le_of_not_lt this
      simp [hj', Array.getElem?_eq_none this]
    · simp [hj']

/-- `ByteArray.toList` is the list of the underlying array. -/

theorem toList_eq_data_toList (bs : ByteArray) : bs.toList = bs.data.toList := by
  have : ∀ i r, i ≤ bs.size →
      ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i := by
    intro i r hi
    fun_induction ByteArray.toList.loop bs i r with
    | case1 i r h ih =>
      rw [ih (by omega)]
      have hl : i < bs.data.toList.length := by rw [Array.length_toList]; exact h
      rw [List.drop_eq_getElem_cons hl, List.reverse_cons, List.append_assoc]
      congr 2
      show [bs.data.getD i default] ++ _ = _
      simp [Array.getD, h]
    | case2 i r h =>
      rw [List.drop_eq_nil_of_le (by rw [Array.length_toList]; exact Nat.le_of_not_lt h),
        List.append_nil]
  exact this 0 [] (Nat.zero_le _)

/-- The whole buffer as a segment is `data.toList`. -/

theorem segment_full (data : ByteArray) : segment data 0 data.size = data.toList := by
  rw [toList_eq_data_toList]
  simp only [segment, List.drop_zero, Nat.sub_zero]
  exact List.take_of_length_le (Nat.le_of_eq Array.length_toList)

private theorem init_finish {start : Nat} {d : Dec} {s : Spec.MQ.State} (h : Sim start d s)
    (hct : 7 ≤ s.CT) :
    Sim start { d with c := d.c <<< 7, ct := d.ct - 7, a := 0x8000 }
      { s with C := s.C * 0x80 % 0x100000000, CT := s.CT - 7, A := 0x8000 } := by
  have hc := h.c
  have hct' := h.ct
  refine ⟨?_, rfl, ?_, h.pos, fun j => by simpa [Dec.byteAt] using h.data j⟩
  · simp [UInt32.toNat_shiftLeft, Nat.shiftLeft_eq, hc]
  · have : (7 : UInt32) ≤ d.ct := by rw [UInt32.le_iff_toNat_le]; simp; omega
    rw [UInt32.toNat_sub_of_le _ _ this]; simp [hct']

/-- `INITDEC` (C.3.5, Figure C.20): the fast `Dec.init data start stop cx` is related to the
spec `initdec` on `segment data start stop`, for any `start`, `stop` and related contexts. -/

theorem init_sim (data : ByteArray) (start stop : Nat) (cx : ByteArray) (cxs : Spec.MQ.Contexts)
    (hcx : CxRel cx cxs) :
    Rel start (Dec.init data start stop cx) (Spec.MQ.initdec (segment data start stop)) cxs := by
  unfold Dec.init Spec.MQ.initdec
  dsimp only
  refine ⟨init_finish (bytein_sim ⟨?_, rfl, rfl, by simp, ?_⟩) (spec_bytein_CT _), ?_,
    Nat.le_refl _, by show 0x8000 < 0x10000; decide⟩
  · have h0 := segment_byteAt data start stop 0
    simp only [Nat.add_zero] at h0
    rw [h0]
    simp only [UInt32.toNat_shiftLeft, Dec.byteAt, Nat.shiftLeft_eq]
    split <;> simp
    have := UInt8.toNat_lt (data.get start (by omega)); omega
  · intro j
    rw [segment_byteAt]
    simp only [Dec.byteAt]
    split <;> simp
  · rw [bytein_cx]; exact hcx

/-- Size of the packed initial context array. -/

theorem initContexts_size (inits : List Nat) : (initContexts inits).size = inits.length := by
  simp [initContexts, ByteArray.size]

/-- The packed initial contexts stand for the spec initial contexts (indices `< 128`). -/

theorem initContexts_rel (inits : List Nat) (h : ∀ i ∈ inits, i < 128) :
    CxRel (initContexts inits) (Spec.MQ.initContexts inits) := by
  refine ⟨by rw [initContexts_size]; simp [Spec.MQ.initContexts], fun k => ?_⟩
  have hsz := initContexts_size inits
  simp only [Spec.MQ.Contexts.get, Spec.MQ.initContexts, List.getD_eq_getElem?_getD,
    List.getElem?_map]
  unfold ctxGet
  by_cases hk : k < inits.length
  · have hs : k < (initContexts inits).size := by omega
    simp only [hs, ↓reduceDIte, List.getElem?_eq_getElem hk]
    simp [initContexts, ByteArray.get]
    exact stateOf_packCx _ (h _ (List.getElem_mem hk))
  · have hs : ¬ k < (initContexts inits).size := by omega
    simp only [hs, ↓reduceDIte, List.getElem?_eq_none (Nat.le_of_not_lt hk)]
    rfl

/-- C2, general form (a segment inside a larger buffer, as Tier-1 uses it): the fast decoder
on `data[start, stop)` returns the spec decisions on `segment data start stop`. -/

theorem decode_init_eq (data : ByteArray) (start stop : Nat) (inits cxList : List Nat)
    (h : ∀ i ∈ inits, i < 128) :
    ((Dec.init data start stop (initContexts inits)).decodeList cxList).1 =
      (Spec.MQ.decodeMany (Spec.MQ.initdec (segment data start stop))
        (Spec.MQ.initContexts inits) cxList).1 :=
  (decodeList_sim (init_sim data start stop _ _ (initContexts_rel inits h)) cxList).1

/-- C2 (Plan.md §4): the fast MQ decoder equals the Annex C flowchart decoder on every input
(all `data`, all context sequences, out-of-range contexts included), for initial states
`< 128` (Table C.2 states are `< 47`). -/

theorem decodeAll_eq (data : ByteArray) (inits cxList : List Nat) (h : ∀ i ∈ inits, i < 128) :
    JPEG2000.MQ.decodeAll data inits cxList = Spec.MQ.decodeAll data.toList inits cxList := by
  unfold JPEG2000.MQ.decodeAll Spec.MQ.decodeAll
  rw [decode_init_eq data 0 data.size inits cxList h, segment_full]

/-- `A` after one fast `RENORMD` body (independent of the other registers). -/

theorem renormStep_a (d : Dec) : (Dec.renormStep d).a.toNat = d.a.toNat * 2 % 0x10000 := by
  have ha : (if d.ct = 0 then d.bytein else d).a = d.a := by
    split
    · unfold Dec.bytein; split <;> (try split) <;> rfl
    · rfl
  unfold Dec.renormStep
  dsimp only
  rw [← ha]
  generalize (if d.ct = 0 then d.bytein else d) = d'
  have e : (65535 : UInt32).toNat = 2 ^ 16 - 1 := rfl
  simp only [UInt32.toNat_and, UInt32.toNat_shiftLeft, Nat.shiftLeft_eq, e,
    Nat.and_two_pow_sub_one_eq_mod]
  simp

/-- Generalised fuel lemma for the fast `renormLoop`. -/

theorem renormLoop_a_range (n : Nat) (d : Dec) (h0 : 0 < d.a.toNat) (h1 : d.a.toNat < 0x8000)
    (hn : 0x8000 ≤ d.a.toNat * 2 ^ n) :
    0x8000 ≤ (Dec.renormLoop n d).a.toNat ∧ (Dec.renormLoop n d).a.toNat < 0x10000 := by
  induction n generalizing d with
  | zero => simp at hn; omega
  | succ n ih =>
    have hA : (Dec.renormStep d).a.toNat = d.a.toNat * 2 := by rw [renormStep_a]; omega
    simp only [Dec.renormLoop, bit_fast]
    split
    · rename_i hb
      rw [Spec.MQ.bit15_iff _ (by omega)] at hb
      omega
    · rename_i hb
      rw [Spec.MQ.bit15_iff _ (by omega)] at hb
      apply ih _ (by omega) (by omega)
      rw [hA, Nat.mul_assoc, ← Nat.pow_succ']
      exact hn

/-- Termination of `RENORMD` for the fast decoder: entered with `0 < A < 0x8000`, the
16-iteration loop exits through its test `A AND 0x8000 ≠ 0` with a 16-bit `A ≥ 0x8000`. -/

theorem renormd_fuel_suffices_fast (d : Dec) (h0 : 0 < d.a.toNat) (h1 : d.a.toNat < 0x8000) :
    0x8000 ≤ (Dec.renormd d).a.toNat ∧ (Dec.renormd d).a.toNat < 0x10000 ∧
      ((Dec.renormd d).a &&& 0x8000 != 0) = true := by
  have h : 0x8000 ≤ (Dec.renormd d).a.toNat ∧ (Dec.renormd d).a.toNat < 0x10000 :=
    renormLoop_a_range 16 d h0 h1 (by omega)
  refine ⟨h.1, h.2, ?_⟩
  rw [bit_fast, Spec.MQ.bit15_iff _ h.2]
  exact h.1

/-- On every state reachable from a related one, the fast decoder keeps `A` in
`[0x8000, 0x10000)` after each decision (the fast form of `Spec.MQ.decode_A_range`). -/

theorem decode_a_range {start : Nat} {d : Dec} {s : Spec.MQ.State} {cxs : Spec.MQ.Contexts}
    (h : Rel start d s cxs) (i : Nat) :
    0x8000 ≤ (d.decode i).2.a.toNat ∧ (d.decode i).2.a.toNat < 0x10000 := by
  have r := (decode_sim h i).2
  rw [r.sim.a]
  exact ⟨r.aLo, r.aHi⟩

end JPEG2000.Spec.MQEquiv
