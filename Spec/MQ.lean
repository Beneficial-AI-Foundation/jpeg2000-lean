/-!
# Spec: the MQ arithmetic decoder (T.800 Annex C)

Plan.md §4 (C1, C2), §5.1 (spec/implementation pattern), §5.2 "MQ decoder".

A near-literal transcription of ITU-T T.800 Annex C, decoder side:

* Table C.2 — the 47-state probability estimation table (`qeTable`);
* C.3.1 — the decoder registers: `C` (32 bits, `Chigh` = bits 31..16, `Clow` = bits 15..0),
  `A` (16 bits), the counter `CT` and the byte pointer `BP` (`State`);
* C.3.2 — `DECODE` (Figure C.15) with `LPS_EXCHANGE` (Figure C.16) and `MPS_EXCHANGE`
  (Figure C.17) (`decode`);
* C.3.3 — `RENORMD` (Figure C.18) (`renormd`);
* C.3.4 — `BYTEIN` (Figure C.19) (`bytein`);
* C.3.5 — `INITDEC` (Figure C.20) (`initdec`).

Representation choices (this is a spec: readability and proofs, not speed):

* Registers are `Nat`; every write is masked explicitly (`% 2^32` for `C`, `% 2^16` for `A`),
  which is exactly what a fixed-width hardware register does.
* The compressed data is a `List UInt8` and `B` is `byteAt data BP`. Reading past the end of
  the segment yields `0xFF` (`byteAt`), as OpenJPEG does by appending `0xFF 0xFF`: a pointer
  at or past the end therefore always sees `B = 0xFF`, `B1 = 0xFF > 0x8F` (a "marker"), so
  `BYTEIN` feeds `1` bits forever without advancing (T.800 C.3.4: "the decoder … fills with
  1-bits"). The decoder is total on every byte string.
* `RENORMD` is a do-while loop; it is written with a fuel of 16 (`renormFuel`), and
  `renormd_fuel_suffices` proves that 16 iterations always reach `A ≥ 0x8000` whenever the
  loop is entered with `0 < A < 0x8000` (which `DECODE` guarantees: `decode_A_range`).
* Contexts (Tier-1 uses 19, T.800 D.7 / Table D.7) are `Nat` indices into a `List CxState`;
  out-of-range reads return the default `{ index := 0, mps := false }` and out-of-range writes
  are no-ops (`List.set`).
* The decision `D` is a `Bool` (`true` = 1); `MPS(CX)` is a `Bool` too.
-/

namespace JPEG2000.Spec.MQ

/-! ## Table C.2 -/

/-- One row of T.800 Table C.2: the LPS probability estimate `Qe` and the next-state indices
after an MPS (`NMPS`) or LPS (`NLPS`) renormalisation; `switch` says whether the sense of the
MPS is inverted after an LPS. -/
structure QeEntry where
  /-- `Qe_Value` (hexadecimal column of Table C.2). -/
  qe : Nat
  /-- `NMPS`: next index after an MPS. -/
  nmps : Nat
  /-- `NLPS`: next index after an LPS. -/
  nlps : Nat
  /-- `SWITCH`: exchange the MPS sense on an LPS. -/
  switch : Bool
  deriving Repr, BEq, DecidableEq, Inhabited

/-- T.800 Table C.2 "Qe values and probability estimation", rows `Index = 0 … 46`, as
`⟨Qe_Value, NMPS, NLPS, SWITCH⟩`. -/
def qeTable : List QeEntry :=
  [ ⟨0x5601,  1,  1, true ⟩,   -- 0
    ⟨0x3401,  2,  6, false⟩,   -- 1
    ⟨0x1801,  3,  9, false⟩,   -- 2
    ⟨0x0AC1,  4, 12, false⟩,   -- 3
    ⟨0x0521,  5, 29, false⟩,   -- 4
    ⟨0x0221, 38, 33, false⟩,   -- 5
    ⟨0x5601,  7,  6, true ⟩,   -- 6
    ⟨0x5401,  8, 14, false⟩,   -- 7
    ⟨0x4801,  9, 14, false⟩,   -- 8
    ⟨0x3801, 10, 14, false⟩,   -- 9
    ⟨0x3001, 11, 17, false⟩,   -- 10
    ⟨0x2401, 12, 18, false⟩,   -- 11
    ⟨0x1C01, 13, 20, false⟩,   -- 12
    ⟨0x1601, 29, 21, false⟩,   -- 13
    ⟨0x5601, 15, 14, true ⟩,   -- 14
    ⟨0x5401, 16, 14, false⟩,   -- 15
    ⟨0x5101, 17, 15, false⟩,   -- 16
    ⟨0x4801, 18, 16, false⟩,   -- 17
    ⟨0x3801, 19, 17, false⟩,   -- 18
    ⟨0x3401, 20, 18, false⟩,   -- 19
    ⟨0x3001, 21, 19, false⟩,   -- 20
    ⟨0x2801, 22, 19, false⟩,   -- 21
    ⟨0x2401, 23, 20, false⟩,   -- 22
    ⟨0x2201, 24, 21, false⟩,   -- 23
    ⟨0x1C01, 25, 22, false⟩,   -- 24
    ⟨0x1801, 26, 23, false⟩,   -- 25
    ⟨0x1601, 27, 24, false⟩,   -- 26
    ⟨0x1401, 28, 25, false⟩,   -- 27
    ⟨0x1201, 29, 26, false⟩,   -- 28
    ⟨0x1101, 30, 27, false⟩,   -- 29
    ⟨0x0AC1, 31, 28, false⟩,   -- 30
    ⟨0x09C1, 32, 29, false⟩,   -- 31
    ⟨0x08A1, 33, 30, false⟩,   -- 32
    ⟨0x0521, 34, 31, false⟩,   -- 33
    ⟨0x0441, 35, 32, false⟩,   -- 34
    ⟨0x02A1, 36, 33, false⟩,   -- 35
    ⟨0x0221, 37, 34, false⟩,   -- 36
    ⟨0x0141, 38, 35, false⟩,   -- 37
    ⟨0x0111, 39, 36, false⟩,   -- 38
    ⟨0x0085, 40, 37, false⟩,   -- 39
    ⟨0x0049, 41, 38, false⟩,   -- 40
    ⟨0x0025, 42, 39, false⟩,   -- 41
    ⟨0x0015, 43, 40, false⟩,   -- 42
    ⟨0x0009, 44, 41, false⟩,   -- 43
    ⟨0x0005, 45, 42, false⟩,   -- 44
    ⟨0x0001, 45, 43, false⟩,   -- 45
    ⟨0x5601, 46, 46, false⟩ ]  -- 46 (non-adaptive state, used by the UNIFORM context)

/-- Number of probability states (rows of Table C.2). -/
def numStates : Nat := 47

#guard qeTable.length = numStates
#guard qeTable.all fun e => e.nmps < numStates && e.nlps < numStates
#guard qeTable.all fun e => 0 < e.qe && e.qe ≤ 0x5601
#guard (qeTable.filter (·.switch)).length = 3

/-- Default row returned for an out-of-range index (never reached from a valid context:
`qeAt_lt`); row 0 of Table C.2. -/
def defaultEntry : QeEntry := ⟨0x5601, 1, 1, true⟩

/-- Row `i` of Table C.2 (total: `defaultEntry` past row 46). -/
def qeAt (i : Nat) : QeEntry := qeTable.getD i defaultEntry

#guard qeAt 0 = ⟨0x5601, 1, 1, true⟩
#guard qeAt 3 = ⟨0x0AC1, 4, 12, false⟩
#guard qeAt 5 = ⟨0x0221, 38, 33, false⟩
#guard qeAt 13 = ⟨0x1601, 29, 21, false⟩
#guard qeAt 16 = ⟨0x5101, 17, 15, false⟩
#guard qeAt 32 = ⟨0x08A1, 33, 30, false⟩
#guard qeAt 39 = ⟨0x0085, 40, 37, false⟩
#guard qeAt 45 = ⟨0x0001, 45, 43, false⟩
#guard qeAt 46 = ⟨0x5601, 46, 46, false⟩

/-! ## Contexts (C.3, D.7) -/

/-- The adaptive state of one context `CX`: the index `I(CX)` into Table C.2 (`< 47`) and
the sense `MPS(CX)` of the more probable symbol (`true` = 1). -/
structure CxState where
  /-- `I(CX)`: row of Table C.2. -/
  index : Nat
  /-- `MPS(CX)`. -/
  mps : Bool
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The table of context states, indexed by the context number `CX`. -/
abbrev Contexts := List CxState

/-- Context table with context `k` starting in state `I = inits[k]`, `MPS = 0`
(T.800 D.7 / Table D.7 gives the initial states used by Tier-1). -/
def initContexts (inits : List Nat) : Contexts :=
  inits.map fun i => { index := i, mps := false }

/-- State of context `cx` (total: `{ index := 0, mps := false }` out of range). -/
def Contexts.get (cxs : Contexts) (cx : Nat) : CxState :=
  cxs.getD cx { index := 0, mps := false }

/-- Replace the state of context `cx` (a no-op out of range). -/
def Contexts.put (cxs : Contexts) (cx : Nat) (st : CxState) : Contexts :=
  cxs.set cx st

/-! ## Decoder registers (C.3.1) -/

/-- The MQ decoder state: registers `C` (32 bits), `A` (16 bits), `CT`, the byte pointer
`BP` and the compressed data it points into. -/
structure State where
  /-- Code register `C`; `Chigh = C / 2^16`, `Clow = C % 2^16`. -/
  C : Nat
  /-- Interval register `A`. -/
  A : Nat
  /-- Bit counter `CT`. -/
  CT : Nat
  /-- Byte pointer `BP` (index into `data`). -/
  pos : Nat
  /-- The compressed data of the segment. -/
  data : List UInt8
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Byte `i` of the segment; `0xFF` past the end (synthetic padding). -/
def byteAt (data : List UInt8) (i : Nat) : Nat := (data.getD i 0xFF).toNat

/-- `Chigh`: the upper 16 bits of `C`. -/
def State.chigh (s : State) : Nat := s.C / 0x10000 % 0x10000

/-- `A AND 0x8000 ≠ 0`, i.e. bit 15 of `A` is set. -/
def bit15 (a : Nat) : Bool := a / 0x8000 % 2 == 1

/-! ## BYTEIN (C.3.4, Figure C.19) -/

/-- `BYTEIN` (Figure C.19). `B = byteAt data BP`, `B1 = byteAt data (BP + 1)`.

* `B = 0xFF` and `B1 > 0x8F` (a marker): `C = C + 0xFF00`, `CT = 8`, `BP` unchanged;
* `B = 0xFF` otherwise: `BP = BP + 1`, `C = C + (B << 9)`, `CT = 7` (bit stuffing);
* else: `BP = BP + 1`, `C = C + (B << 8)`, `CT = 8`. -/
def bytein (s : State) : State :=
  if byteAt s.data s.pos = 0xFF then
    if byteAt s.data (s.pos + 1) > 0x8F then
      { s with C := (s.C + 0xFF00) % 0x100000000, CT := 8 }
    else
      let bp := s.pos + 1
      { s with pos := bp, C := (s.C + byteAt s.data bp * 0x200) % 0x100000000, CT := 7 }
  else
    let bp := s.pos + 1
    { s with pos := bp, C := (s.C + byteAt s.data bp * 0x100) % 0x100000000, CT := 8 }

/-! ## INITDEC (C.3.5, Figure C.20) -/

/-- `INITDEC` (Figure C.20): `BP = BPST`, `C = B << 16`, `BYTEIN`, `C = C << 7`,
`CT = CT − 7`, `A = 0x8000`. -/
def initdec (data : List UInt8) : State :=
  let s : State := { C := byteAt data 0 * 0x10000, A := 0, CT := 0, pos := 0, data }
  let s := bytein s
  { s with C := s.C * 0x80 % 0x100000000, CT := s.CT - 7, A := 0x8000 }

/-! ## RENORMD (C.3.3, Figure C.18) -/

/-- One pass of the `RENORMD` loop body: `if CT = 0 then BYTEIN`; `A = A << 1`;
`C = C << 1`; `CT = CT − 1`. -/
def renormStep (s : State) : State :=
  let s := if s.CT = 0 then bytein s else s
  { s with A := s.A * 2 % 0x10000, C := s.C * 2 % 0x100000000, CT := s.CT - 1 }

/-- The `RENORMD` do-while loop with explicit fuel: run the body, stop once
`A AND 0x8000 ≠ 0` (or the fuel is spent). -/
def renormLoop : Nat → State → State
  | 0, s => s
  | fuel + 1, s =>
    let s := renormStep s
    if bit15 s.A then s else renormLoop fuel s

/-- Fuel for `RENORMD`: 16 iterations always suffice (`renormd_fuel_suffices`). -/
def renormFuel : Nat := 16

/-- `RENORMD` (Figure C.18). -/
def renormd (s : State) : State := renormLoop renormFuel s

/-! ## DECODE (C.3.2, Figures C.15–C.17) -/

/-- `LPS_EXCHANGE` (Figure C.16), run with `A` already reduced by `Qe`. Returns `D`, the
new `A` and the new context state. -/
def lpsExchange (A : Nat) (st : CxState) : Bool × Nat × CxState :=
  let e := qeAt st.index
  if A < e.qe then
    (st.mps, e.qe, { st with index := e.nmps })
  else
    (!st.mps, e.qe,
      { index := e.nlps, mps := if e.switch then !st.mps else st.mps })

/-- `MPS_EXCHANGE` (Figure C.17), run with `A` already reduced by `Qe`. Returns `D` and the
new context state (`A` is unchanged). -/
def mpsExchange (A : Nat) (st : CxState) : Bool × CxState :=
  let e := qeAt st.index
  if A < e.qe then
    (!st.mps, { index := e.nlps, mps := if e.switch then !st.mps else st.mps })
  else
    (st.mps, { st with index := e.nmps })

/-- `DECODE` (Figure C.15): decode one decision `D` in context `cx`.

`A = A − Qe(I(CX))`; if `Chigh < Qe` then `LPS_EXCHANGE`, `RENORMD`; else
`Chigh = Chigh − Qe` and, if `A AND 0x8000 = 0`, `MPS_EXCHANGE`, `RENORMD`, else `D = MPS(CX)`. -/
def decode (s : State) (cxs : Contexts) (cx : Nat) : Bool × State × Contexts :=
  let st := cxs.get cx
  let qe := (qeAt st.index).qe
  let A := (s.A - qe) % 0x10000
  if s.chigh < qe then
    let (d, A, st) := lpsExchange A st
    (d, renormd { s with A }, cxs.put cx st)
  else
    let C := (s.chigh - qe) * 0x10000 + s.C % 0x10000
    let s := { s with A, C }
    if bit15 A then
      (st.mps, s, cxs)
    else
      let (d, st) := mpsExchange A st
      (d, renormd s, cxs.put cx st)

/-- Decode one decision per context in `cxList`, in order. -/
def decodeMany (s : State) (cxs : Contexts) : List Nat → List Bool × State × Contexts
  | [] => ([], s, cxs)
  | cx :: rest =>
    let (d, s, cxs) := decode s cxs cx
    let (ds, s, cxs) := decodeMany s cxs rest
    (d :: ds, s, cxs)

/-- Initialise on `data` and decode one decision per context in `cxList`. -/
def decodeAll (data : List UInt8) (inits : List Nat) (cxList : List Nat) : List Bool :=
  (decodeMany (initdec data) (initContexts inits) cxList).1

/-! ## Range invariants -/

/-- Every row of Table C.2 has `0 < Qe ≤ 0x5601`. -/
theorem qe_bounds : ∀ e ∈ qeTable, 0 < e.qe ∧ e.qe ≤ 0x5601 := by decide

/-- Every `Qe` value (including the default row) lies in `(0, 0x5601]`. -/
theorem qeAt_qe_bounds (i : Nat) : 0 < (qeAt i).qe ∧ (qeAt i).qe ≤ 0x5601 := by
  unfold qeAt
  rw [List.getD_eq_getElem?_getD]
  cases h : qeTable[i]? with
  | none => decide
  | some e => exact qe_bounds e (List.mem_of_getElem? h)

/-- `bit15 a` is `0x8000 ≤ a` for a 16-bit `a`. -/
theorem bit15_iff (a : Nat) (h : a < 0x10000) : bit15 a = true ↔ 0x8000 ≤ a := by
  simp only [bit15, beq_iff_eq]; omega

/-- `BYTEIN` does not touch `A`. -/
@[simp] theorem bytein_A (s : State) : (bytein s).A = s.A := by
  unfold bytein; split <;> (try split) <;> rfl

/-- `C` stays a 32-bit value after `BYTEIN`. -/
theorem bytein_C_lt (s : State) : (bytein s).C < 0x100000000 := by
  unfold bytein; split <;> (try split) <;> exact Nat.mod_lt _ (by decide)

/-- `CT ≤ 8` after `BYTEIN`. -/
theorem bytein_CT_le (s : State) : (bytein s).CT ≤ 8 := by
  unfold bytein; split <;> (try split) <;> simp

/-- `BYTEIN` advances the byte pointer by at most one. -/
theorem bytein_pos_le (s : State) : (bytein s).pos ≤ s.pos + 1 := by
  unfold bytein; split <;> (try split) <;> simp

/-- `BYTEIN` keeps the data. -/
@[simp] theorem bytein_data (s : State) : (bytein s).data = s.data := by
  unfold bytein; split <;> (try split) <;> rfl

/-- The `A` register after one `RENORMD` body. -/
theorem renormStep_A (s : State) : (renormStep s).A = s.A * 2 % 0x10000 := by
  unfold renormStep; split <;> simp

/-- Generalised fuel lemma for `renormLoop`. -/
theorem renormLoop_bit15 (n : Nat) (s : State) (h0 : 0 < s.A) (h1 : s.A < 0x8000)
    (hn : 0x8000 ≤ s.A * 2 ^ n) : 0x8000 ≤ (renormLoop n s).A ∧ (renormLoop n s).A < 0x10000 := by
  induction n generalizing s with
  | zero => simp at hn; omega
  | succ n ih =>
    have hA : (renormStep s).A = s.A * 2 := by rw [renormStep_A]; omega
    simp only [renormLoop]
    split
    · rename_i hb
      rw [bit15_iff _ (by omega)] at hb
      omega
    · rename_i hb
      rw [bit15_iff _ (by omega)] at hb
      apply ih _ (by omega) (by omega)
      rw [hA, Nat.mul_assoc, ← Nat.pow_succ']
      exact hn

/-- `renormd_fuel_suffices`: entered with `0 < A < 0x8000`, the 16-iteration `RENORMD`
exits through its loop test (`A AND 0x8000 ≠ 0`) and leaves a 16-bit `A ≥ 0x8000`. -/
theorem renormd_fuel_suffices (s : State) (h0 : 0 < s.A) (h1 : s.A < 0x8000) :
    0x8000 ≤ (renormd s).A ∧ (renormd s).A < 0x10000 := by
  apply renormLoop_bit15 _ _ h0 h1
  show 0x8000 ≤ s.A * 2 ^ 16
  omega

/-- `LPS_EXCHANGE` always sets `A = Qe(I(CX))`. -/
@[simp] theorem lpsExchange_A (A : Nat) (st : CxState) :
    (lpsExchange A st).2.1 = (qeAt st.index).qe := by
  simp only [lpsExchange]; split <;> rfl

/-- `DECODE` keeps `A` in `[0x8000, 0x10000)`. -/
theorem decode_A_range (s : State) (cxs : Contexts) (cx : Nat)
    (h0 : 0x8000 ≤ s.A) (h1 : s.A < 0x10000) :
    0x8000 ≤ (decode s cxs cx).2.1.A ∧ (decode s cxs cx).2.1.A < 0x10000 := by
  have hq := qeAt_qe_bounds (cxs.get cx).index
  unfold decode
  simp only
  split
  · -- LPS path: A = Qe
    apply renormd_fuel_suffices <;> simp <;> omega
  · split
    · rename_i hb
      simp only
      rw [bit15_iff _ (by omega)] at hb
      omega
    · rename_i hb
      rw [bit15_iff _ (by omega)] at hb
      apply renormd_fuel_suffices <;> simp <;> omega

/-! ## Test vector (ITU-T T.88 Annex H.2; same MQ coder) -/

/-- Encoded bytes of the T.88 H.2 test sequence. -/
def t88Encoded : List UInt8 :=
  [0x84, 0xC7, 0x3B, 0xFC, 0xE1, 0xA1, 0x43, 0x04, 0x02, 0x20, 0x00, 0x00, 0x41, 0x0D, 0xBB,
   0x86, 0xF4, 0x31, 0x7F, 0xFF, 0x88, 0xFF, 0x37, 0x47, 0x1A, 0xDB, 0x6A, 0xDF, 0xFF, 0xAC]

/-- The 256-bit source data of the T.88 H.2 test sequence (bytes, MSB first). -/
def t88Data : List UInt8 :=
  [0x00, 0x02, 0x00, 0x51, 0x00, 0x00, 0x00, 0xC0, 0x03, 0x52, 0x87, 0x2A, 0xAA, 0xAA, 0xAA,
   0xAA, 0x82, 0xC0, 0x20, 0x00, 0xFC, 0xD7, 0x9E, 0xF6, 0xBF, 0x7F, 0xED, 0x90, 0x4F, 0x46,
   0xA3, 0xBF]

/-- Bits of a byte list, MSB first. -/
def bitsOf (bs : List UInt8) : List Bool :=
  bs.flatMap fun b => (List.range 8).reverse.map fun i => (b.toNat / 2 ^ i) % 2 == 1

#guard decodeAll t88Encoded [0] (List.replicate 256 0) = bitsOf t88Data

end JPEG2000.Spec.MQ
