import Spec.MQ

/-!
# Reference MQ arithmetic encoder (T.800 Annex C, encoder side)

Plan.md §4 (C1), §5.2 "MQ decoder", §5.3 (reference encoder: tests and proofs only).

A near-literal transcription of the ITU-T T.800 Annex C encoder flowcharts, written in the
same style as the decoder specification `Spec/MQ.lean` (whose probability table `qeTable`,
context types `CxState`/`Contexts` and context initialisation `initContexts` it reuses), so
that the round-trip theorem C1 (`decodeAll (encodeAll inits pairs) inits (pairs.map (·.1)) =
pairs.map (·.2)`) can be stated directly against `Spec.MQ.decodeAll`:

* C.2.1 — the encoder registers: `C` (32-bit register of which 28 bits are used:
  `0000cbbb bbbbbsss xxxxxxxx xxxxxxxx`, carry bit `c` = bit 27), `A` (16 bits), the counter
  `CT`, the byte buffer `B` and the byte pointer `BP` (`EncState`);
* C.2.2 — `ENCODE` (Figure C.3) dispatching to `CODE1` / `CODE0` (Figures C.4, C.5)
  (`encode`);
* C.2.3, C.2.4 — `CODELPS` (Figure C.6) and `CODEMPS` (Figure C.7), each with its
  conditional exchange (`codeLps`, `codeMps`);
* C.2.6 — `RENORME` (Figure C.8) (`renorme`);
* C.2.7 — `BYTEOUT` (Figure C.9), with bit stuffing after `0xFF` and carry propagation into
  `B` (`byteout`);
* C.2.8 — `INITENC` (Figure C.10) (`initenc`);
* C.2.9 — `FLUSH` (Figure C.11) with `SETBITS` (Figure C.12) (`setbits`, `flush`).

Representation choices (mirroring `Spec.MQ`):

* Registers are `Nat`; every write to `C` is masked to 32 bits (`% 2^32`), every write to
  `A` to 16 bits (`% 2^16`) and every load of `B` to 8 bits (`% 2^8`), as a fixed-width
  register would be. The `B` mask matters: after a carry into `B`, the 8-bit path loads
  `C >> 19`, which still holds the carry bit 27 (OpenJPEG truncates through its
  `unsigned char` buffer). `C OR 0xFFFF` is written
  arithmetically (`C / 2^16 * 2^16 + 0xFFFF`) so that proofs stay in `omega`.
* The output is accumulated in reverse (`outRev`): `BP = BP + 1` followed by a store into
  `B` is modelled as "push the finished byte `B` onto `outRev`, then load the new `B`".
* `INITENC` sets `BP = BPST − 1` and treats the byte "before the start" as `B = 0` (not
  `0xFF`, which would wrongly trigger bit stuffing). That byte is pushed as the first
  element of `outRev` by the first `BYTEOUT` and dropped by `flush`. No carry can reach it:
  the first `BYTEOUT` happens after 12 shifts of an interval contained in `[0, 0x8000)`, so
  `C < 0x8000000` there.
* `RENORME` is a do-while loop written with a fuel of 16 (`Spec.MQ.renormFuel`);
  `renorme_fuel_suffices` proves that 16 iterations always reach `A ≥ 0x8000` when the loop
  is entered with `0 < A < 0x8000` (which `CODEMPS`/`CODELPS` guarantee).
* `FLUSH` is the plain termination of C.2.9: `SETBITS`, `C << CT`, `BYTEOUT`, `C << CT`,
  `BYTEOUT`, and a final `B = 0xFF` is not written (T.800 C.2.9 / D.4.1: a terminating `0xFF`
  is discarded; the decoder's `0xFF` padding re-creates it). The "predictable termination"
  (ERTERM, T.800 D.4.2) is not implemented.
-/

namespace JPEG2000.Encode.MQ

open JPEG2000.Spec.MQ

/-! ## Encoder registers (C.2.1) -/

/-- The MQ encoder state: registers `C`, `A`, `CT`, the byte buffer `B` and the bytes
already written (most recent first; the first element pushed is the dummy byte at
`BPST − 1`). -/
structure EncState where
  /-- Code register `C` (28 bits used; carry at bit 27). -/
  C : Nat
  /-- Interval register `A` (16 bits). -/
  A : Nat
  /-- Bit counter `CT`: shifts left before the next `BYTEOUT`. -/
  CT : Nat
  /-- Byte buffer `B` (the byte at `BP`, still subject to a carry). -/
  B : Nat
  /-- The finished bytes before `BP`, most recent first (includes the dummy byte at
  `BPST − 1` once the first `BYTEOUT` has run). -/
  outRev : List Nat
  deriving Repr, BEq, DecidableEq, Inhabited

/-! ## INITENC (C.2.8, Figure C.10) -/

/-- `INITENC` (Figure C.10): `A = 0x8000`, `C = 0`, `BP = BPST − 1`, `CT = 12`; the byte
before the start is taken as `B = 0`. -/
def initenc : EncState := { C := 0, A := 0x8000, CT := 12, B := 0, outRev := [] }

/-! ## BYTEOUT (C.2.7, Figure C.9) -/

/-- The 7-bit output case of `BYTEOUT` (after a `0xFF`): `BP = BP + 1`, `B = C >> 20`,
`C = C AND 0xFFFFF`, `CT = 7` (`B` is an 8-bit register: the write is masked). -/
def byteout7 (s : EncState) : EncState :=
  { s with outRev := s.B :: s.outRev, B := s.C / 0x100000 % 0x100, C := s.C % 0x100000, CT := 7 }

/-- The 8-bit output case of `BYTEOUT`: `BP = BP + 1`, `B = C >> 19`, `C = C AND 0x7FFFF`,
`CT = 8` (`B` is an 8-bit register: the write is masked, which drops the carry bit 27 of
`C` after it has been propagated into the previous `B`). -/
def byteout8 (s : EncState) : EncState :=
  { s with outRev := s.B :: s.outRev, B := s.C / 0x80000 % 0x100, C := s.C % 0x80000, CT := 8 }

/-- `BYTEOUT` (Figure C.9).

* `B = 0xFF`: bit stuffing, the 7-bit case;
* else `C < 0x8000000` (no carry): the 8-bit case;
* else carry: `B = B + 1`; if now `B = 0xFF` then `C = C AND 0x7FFFFFF` and the 7-bit case,
  else the 8-bit case. -/
def byteout (s : EncState) : EncState :=
  if s.B = 0xFF then
    byteout7 s
  else if s.C < 0x8000000 then
    byteout8 s
  else
    let s := { s with B := s.B + 1 }
    if s.B = 0xFF then
      byteout7 { s with C := s.C % 0x8000000 }
    else
      byteout8 s

/-! ## RENORME (C.2.6, Figure C.8) -/

/-- One pass of the `RENORME` loop body: `A = A << 1`; `C = C << 1`; `CT = CT − 1`;
`if CT = 0 then BYTEOUT`. -/
def renormeStep (s : EncState) : EncState :=
  let s := { s with A := s.A * 2 % 0x10000, C := s.C * 2 % 0x100000000, CT := s.CT - 1 }
  if s.CT = 0 then byteout s else s

/-- The `RENORME` do-while loop with explicit fuel: run the body, stop once
`A AND 0x8000 ≠ 0` (or the fuel is spent). -/
def renormeLoop : Nat → EncState → EncState
  | 0, s => s
  | fuel + 1, s =>
    let s := renormeStep s
    if bit15 s.A then s else renormeLoop fuel s

/-- `RENORME` (Figure C.8), with the fuel `Spec.MQ.renormFuel = 16`
(`renorme_fuel_suffices`). -/
def renorme (s : EncState) : EncState := renormeLoop renormFuel s

/-! ## CODEMPS / CODELPS (C.2.3, C.2.4, Figures C.6, C.7) -/

/-- `CODELPS` (Figure C.6): `A = A − Qe`; if `A < Qe` then `C = C + Qe` else `A = Qe`
(conditional exchange); `MPS(CX)` is inverted when `SWITCH`; `I(CX) = NLPS`; `RENORME`.
Returns the new encoder state and the new context state. -/
def codeLps (s : EncState) (st : CxState) : EncState × CxState :=
  let e := qeAt st.index
  let A := (s.A - e.qe) % 0x10000
  let s :=
    if A < e.qe then { s with A, C := (s.C + e.qe) % 0x100000000 }
    else { s with A := e.qe }
  let st : CxState := { index := e.nlps, mps := if e.switch then !st.mps else st.mps }
  (renorme s, st)

/-- `CODEMPS` (Figure C.7): `A = A − Qe`; if `A AND 0x8000 = 0` then (if `A < Qe` then
`A = Qe` else `C = C + Qe`; `I(CX) = NMPS`; `RENORME`) else `C = C + Qe`.
Returns the new encoder state and the new context state. -/
def codeMps (s : EncState) (st : CxState) : EncState × CxState :=
  let e := qeAt st.index
  let A := (s.A - e.qe) % 0x10000
  if bit15 A then
    ({ s with A, C := (s.C + e.qe) % 0x100000000 }, st)
  else
    let s :=
      if A < e.qe then { s with A := e.qe }
      else { s with A, C := (s.C + e.qe) % 0x100000000 }
    (renorme s, { st with index := e.nmps })

/-! ## ENCODE (C.2.2, Figures C.3–C.5) -/

/-- `ENCODE` (Figure C.3) with `CODE1` / `CODE0` (Figures C.4, C.5): code the decision `d`
in context `cx` — `CODEMPS` when `d = MPS(CX)`, `CODELPS` otherwise. -/
def encode (s : EncState) (cxs : Contexts) (cx : Nat) (d : Bool) : EncState × Contexts :=
  let st := cxs.get cx
  let (s, st) := if d == st.mps then codeMps s st else codeLps s st
  (s, cxs.put cx st)

/-- Encode the `(context, decision)` pairs in order. -/
def encodeMany (s : EncState) (cxs : Contexts) : List (Nat × Bool) → EncState × Contexts
  | [] => (s, cxs)
  | (cx, d) :: rest =>
    let (s, cxs) := encode s cxs cx d
    encodeMany s cxs rest

/-! ## FLUSH (C.2.9, Figures C.11, C.12) -/

/-- `SETBITS` (Figure C.12): `TEMPC = C + A`; `C = C OR 0xFFFF`; if `C ≥ TEMPC` then
`C = C − 0x8000`. -/
def setbits (s : EncState) : EncState :=
  let tempc := s.C + s.A
  let c := s.C / 0x10000 * 0x10000 + 0xFFFF
  { s with C := (if c ≥ tempc then c - 0x8000 else c) % 0x100000000 }

/-- `FLUSH` (Figure C.11): `SETBITS`; `C = C << CT`; `BYTEOUT`; `C = C << CT`; `BYTEOUT`;
the final `B` is written unless it is `0xFF` (C.2.9: a terminating `0xFF` is discarded).
Returns the code-word, without the dummy byte at `BPST − 1`. -/
def flush (s : EncState) : List UInt8 :=
  let s := setbits s
  let s := byteout { s with C := s.C * 2 ^ s.CT % 0x100000000 }
  let s := byteout { s with C := s.C * 2 ^ s.CT % 0x100000000 }
  let out := if s.B = 0xFF then s.outRev else s.B :: s.outRev
  (out.reverse.drop 1).map UInt8.ofNat

/-- Encode the `(context, decision)` pairs with the contexts initialised from `inits`
(context `k` in state `inits[k]`, `MPS = 0`) and terminate with `FLUSH`. -/
def encodeAll (inits : List Nat) (pairs : List (Nat × Bool)) : List UInt8 :=
  flush (encodeMany initenc (initContexts inits) pairs).1

/-! ## Termination of RENORME -/

/-- The `A` register after one `RENORME` body. -/
theorem renormeStep_A (s : EncState) : (renormeStep s).A = s.A * 2 % 0x10000 := by
  simp only [renormeStep]
  split
  · simp only [byteout, byteout7, byteout8]
    split
    · rfl
    · split
      · rfl
      · split <;> rfl
  · rfl

/-- Generalised fuel lemma for `renormeLoop`. -/
theorem renormeLoop_bit15 (n : Nat) (s : EncState) (h0 : 0 < s.A) (h1 : s.A < 0x8000)
    (hn : 0x8000 ≤ s.A * 2 ^ n) :
    0x8000 ≤ (renormeLoop n s).A ∧ (renormeLoop n s).A < 0x10000 := by
  induction n generalizing s with
  | zero => simp at hn; omega
  | succ n ih =>
    have hA : (renormeStep s).A = s.A * 2 := by rw [renormeStep_A]; omega
    simp only [renormeLoop]
    split
    · rename_i hb
      rw [bit15_iff _ (by omega)] at hb
      omega
    · rename_i hb
      rw [bit15_iff _ (by omega)] at hb
      apply ih _ (by omega) (by omega)
      rw [hA, Nat.mul_assoc, ← Nat.pow_succ']
      exact hn

/-- `renorme_fuel_suffices`: entered with `0 < A < 0x8000`, the 16-iteration `RENORME`
exits through its loop test (`A AND 0x8000 ≠ 0`) and leaves a 16-bit `A ≥ 0x8000`. -/
theorem renorme_fuel_suffices (s : EncState) (h0 : 0 < s.A) (h1 : s.A < 0x8000) :
    0x8000 ≤ (renorme s).A ∧ (renorme s).A < 0x10000 := by
  apply renormeLoop_bit15 _ _ h0 h1
  show 0x8000 ≤ s.A * 2 ^ 16
  omega

/-- `ENCODE` keeps `A` in `[0x8000, 0x10000)`; in particular every `RENORME` it runs is
entered with `0 < A < 0x8000` and so terminates through its loop test. -/
theorem encode_A_range (s : EncState) (cxs : Contexts) (cx : Nat) (d : Bool)
    (h0 : 0x8000 ≤ s.A) (h1 : s.A < 0x10000) :
    0x8000 ≤ (encode s cxs cx d).1.A ∧ (encode s cxs cx d).1.A < 0x10000 := by
  have hq := qeAt_qe_bounds (cxs.get cx).index
  simp only [encode]
  split
  · simp only [codeMps]
    split
    · rename_i hb
      simp only
      rw [bit15_iff _ (by omega)] at hb
      omega
    · rename_i hb
      rw [bit15_iff _ (by omega)] at hb
      apply renorme_fuel_suffices <;> split <;> simp <;> omega
  · simp only [codeLps]
    apply renorme_fuel_suffices <;> split <;> simp <;> omega

end JPEG2000.Encode.MQ
