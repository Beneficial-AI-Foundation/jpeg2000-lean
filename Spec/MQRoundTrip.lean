import Spec.MQ
import Encode.MQ

/-!
# C1: the MQ round trip `decodeAll (encodeAll inits pairs) inits cxs = ds`

Plan.md §4 (theorem C1), §5.2 "MQ decoder", §5.3 (reference encoder); ITU-T T.800 Annex C
(the encoder C.2.1–C.2.9 of `Encode.MQ`, the decoder C.3.1–C.3.5 of `Spec.MQ`).

`roundTrip`: for all initial context states `inits` and all `(context, decision)` sequences
`pairs`, decoding the reference encoder's code-word returns the decisions. There is no side
condition (out-of-range contexts and states are total and identical on both sides).

## Proof structure

* **Exact interval.** `Lx s` is the encoder's lower interval end with unbounded precision:
  the bytes written so far and the buffer `B`, read with stuffing (`dvR`: a byte after `0xFF`
  is shifted by 7 bits, so a carry into a `0xFF` lands in the next byte's top bit), then the
  register `C`. `BYTEOUT` keeps `Lx` (`byteout_Lx`), a renormalisation shift doubles it, a
  decision adds `0` or `Qe`. `piE s` is the current frame as an absolute bit position.
* **The decoder's view of the output.** `vb`/`vw`/`vpos`/`vval` describe the virtual byte
  stream `0 :: data ++ 0xFF 0xFF …` the decoder reads (`bytein_spec`), with its widths; `Syntax`
  (a `0xFF` is followed by a byte `≤ 0x8F`, no trailing `0xFF`) guarantees the decoder never
  sees a marker inside the data. `bridge` identifies the encoder's own bytes with the
  decoder's.
* **Encoder side** (`run_Q`): at every encoder state of a run, the final output satisfies `Q`:
  `Ext` (written bytes are final, `B` gets at most a carry), `PUB` (what the decoder has read
  at this frame is below the interval's upper end) and `PLB` (what it has read is above the
  lower end). `PUB` comes from nested intervals and the `SETBITS` ones at the end; `PLB`
  needs the *creation-time* argument: the decoder reads about 27 bits ahead of the encoder,
  so the lower bound at a frame is established at the moment the encoder creates the last
  byte the decoder has read (`Q_byteout`), when `C` is below one unit of that byte. Both are
  proved backwards from the end of `FLUSH` (`Q_base`, `flush_Q`) through every
  `RENORME`/`BYTEOUT` step. The byte syntax is a forward invariant (`InvS`, using that the
  interval's upper end never exceeds `0xFF·2^19 + 2^19 + 2^16` after a `0xFF` was buffered).
* **Decoder side** (`dec_many`): `Corr` relates decoder and encoder states (`C ≡ read − Lx`
  modulo `2^32`, same `A`, the decoder positioned at the encoder's frame); `window` turns `Q`
  into the exact value of `C` and so the decoder's `Chigh < Qe` test into the encoder's choice
  of sub-interval (`dec_step`), and `corr_loop` runs `RENORMD` against `RENORME`.
-/

namespace JPEG2000.Spec.MQRoundTrip

open JPEG2000.Spec.MQ JPEG2000.Encode.MQ

/-! ## The encoder's exact interval -/

/-- Width in bits of the byte that follows the most recent byte of `l` (most recent first):
7 after a `0xFF` (bit stuffing), 8 otherwise. -/
def wOf (l : List Nat) : Nat := if l.head? = some 0xFF then 7 else 8

/-- Value of a byte list (most recent first) read with stuffing: each byte is appended
below the previous one with `wOf` bits of shift (a byte after `0xFF` overlaps it by one
bit, which is how a carry into a `0xFF` is represented). -/
def dvR : List Nat → Nat
  | [] => 0
  | d :: l => dvR l * 2 ^ wOf l + d

/-- Bit position of the least significant bit of the most recent byte of a list (most
recent first): the sum of the widths. -/
def pR : List Nat → Nat
  | [] => 0
  | _ :: l => pR l + wOf l

/-- The encoder's exact (unbounded) lower interval end in the current frame (the unit is
the least significant bit of `A`): the bytes already written and the byte buffer `B`, then
the register `C`. Carries are already included, so `Lx` only grows. -/
def Lx (s : EncState) : Nat := dvR (s.B :: s.outRev) * 2 ^ (27 - s.CT) + s.C

/-- The current frame as an absolute bit position: `pR (B :: outRev)` is the position of
`B`'s least significant bit, which sits `27 − CT` bits above the frame unit. -/
def piE (s : EncState) : Nat := pR (s.B :: s.outRev) + 27 - s.CT

/-- One doubling of the frame with `A` replaced by `a` (the `RENORME` body without its
`BYTEOUT`). -/
def shift1 (s : EncState) (a : Nat) : EncState :=
  { s with C := s.C * 2, A := a, CT := s.CT - 1 }

private theorem wOf_cons (b : Nat) (l : List Nat) : wOf (b :: l) = if b = 0xFF then 7 else 8 := by
  simp [wOf]

private theorem wOf_ge (l : List Nat) : 7 ≤ wOf l ∧ wOf l ≤ 8 := by
  unfold wOf; split <;> omega

private theorem Lx_shift1 (s : EncState) (a : Nat) (h1 : 1 ≤ s.CT) (h2 : s.CT ≤ 27) :
    Lx (shift1 s a) = 2 * Lx s := by
  simp only [Lx, shift1]
  have : 27 - (s.CT - 1) = (27 - s.CT) + 1 := by omega
  rw [this, Nat.pow_succ]
  generalize dvR (s.B :: s.outRev) = d
  generalize 2 ^ (27 - s.CT) = p
  rw [← Nat.mul_assoc, Nat.mul_add]
  simp only [Nat.mul_comm]

private theorem piE_shift1 (s : EncState) (a : Nat) (h1 : 1 ≤ s.CT) (h2 : s.CT ≤ 27) :
    piE (shift1 s a) = piE s + 1 := by
  simp only [piE, shift1]; omega

/-- The effect of `BYTEOUT` (entered with `CT = 0`): it pushes the old `B`, possibly
incremented by a carry, and splits `C` into the new `B` and the new `C`. -/
private theorem byteout_cases (s : EncState) (_h0 : s.CT = 0) (hC : s.C < 2 ^ 28) (hB : s.B < 256) :
    ∃ bf, (byteout s).outRev = bf :: s.outRev ∧
      (bf = s.B ∨ (s.B ≠ 0xFF ∧ bf = s.B + 1)) ∧ bf < 256 ∧
      (byteout s).CT = (if bf = 0xFF then 7 else 8) ∧ (byteout s).A = s.A ∧
      (byteout s).B < 256 ∧ (byteout s).C < 2 ^ (27 - (byteout s).CT) ∧
      bf * 2 ^ 27 + (byteout s).B * 2 ^ (27 - (byteout s).CT) + (byteout s).C =
        s.B * 2 ^ 27 + s.C ∧
      (s.C < 2 ^ 27 → bf = s.B) ∧
      (bf = 0xFF → (byteout s).B * 2 ^ 20 + (byteout s).C = s.C % 2 ^ 27 ∨
        (byteout s).B * 2 ^ 20 + (byteout s).C = s.C) ∧
      (bf ≠ 0xFF → (byteout s).B * 2 ^ 19 + (byteout s).C = s.C % 2 ^ 27) := by
  simp only [byteout, byteout7, byteout8]
  split
  · rename_i h
    refine ⟨s.B, rfl, .inl rfl, hB, by simp [h], rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [h] <;> omega
  · split
    · rename_i h h'
      refine ⟨s.B, rfl, .inl rfl, hB, by simp [h], rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [h] <;> omega
    · rename_i h h'
      split
      · rename_i h''
        refine ⟨s.B + 1, rfl, .inr ⟨h, rfl⟩, by omega, by simp [h''], rfl,
          ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
          simp [h''] <;> omega
      · rename_i h''
        refine ⟨s.B + 1, rfl, .inr ⟨h, rfl⟩, by omega, by simp [h''], rfl,
          ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
          simp [h''] <;> omega

private theorem aux_val (X bf b c B C w : Nat) (hw : w ≤ 27)
    (hv : bf * 2 ^ 27 + b * 2 ^ (27 - w) + c = B * 2 ^ 27 + C) :
    ((X + bf) * 2 ^ w + b) * 2 ^ (27 - w) + c = (X + B) * 2 ^ (27 - 0) + C := by
  have h : 2 ^ 27 = 2 ^ w * 2 ^ (27 - w) := by rw [← Nat.pow_add]; congr 1; omega
  rw [Nat.sub_zero]
  rw [h] at hv ⊢
  generalize 2 ^ w = p at *
  generalize 2 ^ (27 - w) = q at *
  grind

private theorem byteout_Lx (s : EncState) (h0 : s.CT = 0) (hC : s.C < 2 ^ 28) (hB : s.B < 256) :
    Lx (byteout s) = Lx s ∧ piE (byteout s) = piE s := by
  obtain ⟨bf, hO, -, -, hCT, -, -, -, hv, -⟩ := byteout_cases s h0 hC hB
  simp only [Lx, piE, hO, dvR, pR, h0, wOf_cons]
  rw [hCT] at hv ⊢
  have hw : (if bf = 0xFF then 7 else 8) ≤ 27 := by split <;> omega
  refine ⟨aux_val _ _ _ _ _ _ _ hw hv, ?_⟩
  split <;> omega

/-! ## The byte string as seen by the decoder -/

section Data

variable (data : List UInt8)

/-- Byte `j` of the virtual stream `0 :: data ++ 0xFF 0xFF …` (index 0 is the encoder's
dummy byte at `BPST − 1`; past the end the decoder sees `0xFF`). -/
def vb (j : Nat) : Nat := if j = 0 then 0 else byteAt data (j - 1)

/-- Width of virtual byte `j`: 7 for a real byte following a real `0xFF` (bit stuffing),
8 otherwise (in particular for the `0xFF` padding, which the decoder reads 8 bits at a
time). -/
def vw (j : Nat) : Nat :=
  if 2 ≤ j ∧ j ≤ data.length ∧ byteAt data (j - 2) = 0xFF then 7 else 8

/-- Absolute bit position of the least significant bit of virtual byte `k`. -/
def vpos : Nat → Nat
  | 0 => vw data 0
  | k + 1 => vpos k + vw data (k + 1)

/-- Value of the virtual bytes `0 … k`, read with stuffing (exactly what the decoder
accumulates). -/
def vval : Nat → Nat
  | 0 => vb data 0
  | k + 1 => vval k * 2 ^ vw data (k + 1) + vb data (k + 1)

/-- Byte syntax of an MQ code-word: a `0xFF` is followed by a byte `≤ 0x8F` (so the decoder
never mistakes data for a marker), and the last byte is not `0xFF`. -/
def Syntax : Prop :=
  ∀ i, i < data.length → byteAt data i = 0xFF →
    i + 1 < data.length ∧ byteAt data (i + 1) ≤ 0x8F

end Data

private theorem byteAt_lt (data : List UInt8) (i : Nat) : byteAt data i < 256 := by
  unfold byteAt; exact UInt8.toNat_lt _

private theorem byteAt_past (data : List UInt8) (i : Nat) (h : data.length ≤ i) :
    byteAt data i = 0xFF := by
  unfold byteAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

private theorem vb_lt (data : List UInt8) (j : Nat) : vb data j < 256 := by
  unfold vb; split
  · omega
  · exact byteAt_lt _ _

private theorem vw_bounds (data : List UInt8) (j : Nat) : 7 ≤ vw data j ∧ vw data j ≤ 8 := by
  unfold vw; split <;> omega

private theorem vpos_le (data : List UInt8) (a : Nat) :
    ∀ d, vpos data a + 7 * d ≤ vpos data (a + d)
  | 0 => by simp
  | d + 1 => by
    have := vpos_le data a d
    have := (vw_bounds data (a + d + 1)).1
    rw [← Nat.add_assoc, vpos]; omega

private theorem lt_of_vpos_lt (data : List UInt8) (a b : Nat) (h : vpos data a < vpos data b) :
    a < b := by
  apply Nat.lt_of_not_le
  intro hle
  have := vpos_le data b (a - b)
  rw [Nat.add_sub_cancel' hle] at this
  omega

private theorem vval_succ_ge (data : List UInt8) (k : Nat) :
    vval data k * 2 ^ vw data (k + 1) ≤ vval data (k + 1) := by
  simp only [vval]; omega

/-- The width rule: the width of byte `m + 1` is 7 exactly when byte `m` is `0xFF`, as long
as `m` is a real byte or the first padding byte. -/
private theorem wOf_vb (data : List UInt8) (hs : Syntax data) (m : Nat) (hm : m ≤ data.length)
    (l : List Nat) : wOf (vb data m :: l) = vw data (m + 1) := by
  rw [wOf_cons]
  unfold vb vw
  by_cases h0 : m = 0
  · subst h0; simp
  · simp only [h0, ↓reduceIte]
    by_cases hf : byteAt data (m - 1) = 0xFF
    · have := hs (m - 1) (by omega) hf
      have e : m + 1 - 2 = m - 1 := by omega
      have hc : (2 ≤ m + 1 ∧ m + 1 ≤ data.length ∧ byteAt data (m + 1 - 2) = 0xFF) :=
        ⟨by omega, by omega, by rw [e]; exact hf⟩
      simp only [hf, hc, ↓reduceIte, and_self]
    · have e : m + 1 - 2 = m - 1 := by omega
      simp only [hf, ↓reduceIte, e, and_false]

/-- The bridge between the encoder's own bytes and the decoder's virtual stream: if the
bytes written so far are the virtual bytes `0 … k − 1`, then the encoder's positions and
values are the decoder's. -/
private theorem bridge (data : List UInt8) (hs : Syntax data) :
    ∀ (l : List Nat), l.reverse = (List.range l.length).map (vb data) →
      l.length ≤ data.length + 1 → ∀ x,
      pR (x :: l) = vpos data l.length ∧ dvR (x :: l) + vb data l.length = vval data l.length + x
  | [], _, _, x => by
    simp [pR, dvR, vpos, vval, vw, vb, wOf]
  | d :: l, h, hl, x => by
    simp only [List.reverse_cons, List.length_cons, List.range_succ, List.map_append,
      List.map_cons, List.map_nil] at h
    obtain ⟨h1, h2⟩ := List.append_inj' h (by simp)
    simp only [List.cons.injEq, and_true] at h2
    simp only [List.length_cons] at hl
    obtain ⟨ih1, ih2⟩ := bridge data hs l h1 (by omega) d
    have hw : wOf (d :: l) = vw data (l.length + 1) := by
      rw [h2]; exact wOf_vb data hs _ (by omega) l
    simp only [pR, dvR, List.length_cons, vpos, vval] at ih1 ih2 ⊢
    rw [hw, ih1]
    constructor
    · rfl
    · have : dvR l * 2 ^ wOf l + d = vval data l.length := by omega
      rw [this]; omega

/-- Past the end of the data the decoder reads only `1` bits. -/
private theorem vval_ones (data : List UInt8) (k0 : Nat) (hk : data.length ≤ k0) :
    ∀ j, vpos data k0 ≤ vpos data (k0 + j) ∧
      vval data (k0 + j) + 1 = (vval data k0 + 1) * 2 ^ (vpos data (k0 + j) - vpos data k0)
  | 0 => by simp
  | j + 1 => by
    obtain ⟨h1, h2⟩ := vval_ones data k0 hk j
    have hb : vb data (k0 + j + 1) = 255 := by
      unfold vb; simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte]
      exact byteAt_past _ _ (by omega)
    have hw : vw data (k0 + j + 1) = 8 := by
      unfold vw; split
      · omega
      · rfl
    rw [← Nat.add_assoc]
    simp only [vval, vpos, hb, hw]
    have e : vpos data (k0 + j) + 8 - vpos data k0 = (vpos data (k0 + j) - vpos data k0) + 8 := by
      omega
    refine ⟨by omega, ?_⟩
    rw [e, Nat.pow_add, ← Nat.mul_assoc, ← h2]
    omega

/-! ## Facts about the final byte string seen from an encoder state -/

section Q

variable (data : List UInt8)

/-- The bytes the encoder has already written are the first virtual bytes, and the final
value of the buffered byte `B` is `B` or `B + 1` (a later carry). -/
def Ext (s : EncState) : Prop :=
  s.outRev.reverse = (List.range s.outRev.length).map (vb data) ∧
  (vb data s.outRev.length = s.B ∨ (s.B ≠ 0xFF ∧ vb data s.outRev.length = s.B + 1)) ∧
  s.outRev.length ≤ data.length + 1

/-- Lower bound: whenever the decoder, at some frame not later than the encoder's, has read
up to a byte the encoder has not finished yet (virtual byte `k`, `c` bits below the frame
unit), every lower interval end `ℓ` that grows into `Lx s` by now is below what the
decoder has read. -/
def PLB (s : EncState) : Prop :=
  ∀ k c ℓ, s.outRev.length < k → vpos data k ≤ piE s + c →
    ℓ * 2 ^ (piE s + c - vpos data k) ≤ Lx s → ℓ * 2 ^ c ≤ vval data k

/-- Upper bound: what the decoder has read at the encoder's frame is below the upper end of
the encoder's interval. -/
def PUB (s : EncState) : Prop :=
  ∀ k c, vpos data k = piE s + c → vval data k < (Lx s + s.A) * 2 ^ c

/-- Everything the decoder needs to know about the final byte string at an encoder state. -/
def Q (s : EncState) : Prop := Ext data s ∧ PLB data s ∧ PUB data s

end Q

private theorem Q_add (data : List UInt8) (s s' : EncState) (hO : s'.outRev = s.outRev)
    (hB : s'.B = s.B) (hCT : s'.CT = s.CT) (hC : s.C ≤ s'.C) (hU : s'.C + s'.A ≤ s.C + s.A)
    (hq : Q data s') : Q data s := by
  obtain ⟨he, hl, hu⟩ := hq
  have hpi : piE s' = piE s := by simp only [piE, hO, hB, hCT]
  have hL : Lx s ≤ Lx s' := by simp only [Lx, hO, hB, hCT]; omega
  have hL2 : Lx s' + s'.A ≤ Lx s + s.A := by simp only [Lx, hO, hB, hCT]; omega
  refine ⟨?_, ?_, ?_⟩
  · simpa [Ext, hO, hB] using he
  · intro k c ℓ hk hv h
    exact hl k c ℓ (by rw [hO]; exact hk) (by rw [hpi]; exact hv) (by rw [hpi]; omega)
  · intro k c hv
    have := hu k c (by rw [hpi]; exact hv)
    exact Nat.lt_of_lt_of_le this (Nat.mul_le_mul_right _ hL2)

private theorem Q_shift (data : List UInt8) (s : EncState) (a : Nat) (h1 : 1 ≤ s.CT)
    (h2 : s.CT ≤ 27)
    (ha : a ≤ 2 * s.A) (hq : Q data (shift1 s a)) : Q data s := by
  obtain ⟨he, hl, hu⟩ := hq
  have hpi := piE_shift1 s a h1 h2
  have hL := Lx_shift1 s a h1 h2
  have hA : (shift1 s a).A = a := rfl
  refine ⟨?_, ?_, ?_⟩
  · simpa [Ext, shift1] using he
  · intro k c ℓ hk hv h
    apply hl k c ℓ (by simpa [shift1] using hk) (by omega)
    have e : piE (shift1 s a) + c - vpos data k = (piE s + c - vpos data k) + 1 := by omega
    rw [e, Nat.pow_succ, hL, ← Nat.mul_assoc, Nat.mul_comm _ 2]
    omega
  · intro k c hv
    cases c with
    | zero =>
      have hw := vw_bounds data (k + 1)
      have := hu (k + 1) (vw data (k + 1) - 1) (by simp only [vpos]; omega)
      rw [hL, hA] at this
      have h3 : (2 * Lx s + a) * 2 ^ (vw data (k + 1) - 1) ≤
          (Lx s + s.A) * 2 ^ vw data (k + 1) := by
        have e : vw data (k + 1) = (vw data (k + 1) - 1) + 1 := by omega
        conv => rhs; rw [e, Nat.pow_succ]
        rw [Nat.mul_comm (2 ^ _) 2, ← Nat.mul_assoc]
        exact Nat.mul_le_mul_right _ (by omega)
      have h4 := vval_succ_ge data k
      have : vval data k * 2 ^ vw data (k + 1) < (Lx s + s.A) * 2 ^ vw data (k + 1) := by
        omega
      have := Nat.lt_of_mul_lt_mul_right this
      simpa using this
    | succ c =>
      have := hu k c (by omega)
      rw [hL, hA] at this
      have h3 : (2 * Lx s + a) * 2 ^ c ≤ (Lx s + s.A) * 2 ^ (c + 1) := by
        rw [Nat.pow_succ, Nat.mul_comm (2 ^ c) 2, ← Nat.mul_assoc]
        exact Nat.mul_le_mul_right _ (by omega)
      omega

private theorem Q_byteout (data : List UInt8) (hs : Syntax data) (s : EncState) (h0 : s.CT = 0)
    (hC : s.C < 2 ^ 28) (hB : s.B < 256) (hq : Q data (byteout s)) : Q data s := by
  obtain ⟨bf, hO, hbf, hbf256, hCT, hA, hB', hC', hv, -⟩ := byteout_cases s h0 hC hB
  obtain ⟨hLx, hpi⟩ := byteout_Lx s h0 hC hB
  obtain ⟨⟨he1, he2, he3⟩, hl, hu⟩ := hq
  rw [hO] at he1 he2 he3
  have he1' := he1
  simp only [List.reverse_cons, List.length_cons, List.range_succ, List.map_append,
    List.map_cons, List.map_nil] at he1'
  obtain ⟨hr, hlast⟩ := List.append_inj' he1' (by simp)
  simp only [List.cons.injEq, and_true] at hlast
  simp only [List.length_cons] at he3
  refine ⟨⟨hr, ?_, by omega⟩, ?_, ?_⟩
  · rcases hbf with h | ⟨h1, h2⟩
    · left; omega
    · right; exact ⟨h1, by omega⟩
  · intro k c ℓ hk hv h
    rcases Nat.lt_or_ge (s.outRev.length + 1) k with hk' | hk'
    · exact hl k c ℓ (by rw [hO]; simpa using hk') (by omega) (by rw [hpi, hLx]; exact h)
    · have hkk : k = (bf :: s.outRev).length := by simp; omega
      subst hkk
      obtain ⟨hp, hd⟩ := bridge data hs (bf :: s.outRev) he1 (by simpa using he3) (byteout s).B
      have hpi' : piE (byteout s) = vpos data (bf :: s.outRev).length + 27 - (byteout s).CT := by
        simp only [piE, hO, hp]
      have hct : (byteout s).CT ≤ 8 := by rw [hCT]; split <;> omega
      have e : piE s + c - vpos data (bf :: s.outRev).length = c + (27 - (byteout s).CT) := by
        omega
      rw [e, Nat.pow_add, ← Nat.mul_assoc, ← hLx] at h
      simp only [Lx, hO] at h
      have h5 : ℓ * 2 ^ c * 2 ^ (27 - (byteout s).CT) <
          (dvR ((byteout s).B :: bf :: s.outRev) + 1) * 2 ^ (27 - (byteout s).CT) := by
        rw [Nat.add_mul]; omega
      have h6 := Nat.lt_of_mul_lt_mul_right h5
      have h7 : dvR ((byteout s).B :: bf :: s.outRev) ≤ vval data (bf :: s.outRev).length := by
        rcases he2 with h8 | ⟨-, h8⟩ <;> omega
      omega
  · intro k c hv
    have := hu k c (by rw [hpi]; exact hv)
    rwa [hLx, hA] at this

/-! ## Encoder register invariants and the `RENORME` loop -/

/-- Register invariant of the encoder between two `RENORME` iterations: `CT ∈ [1, 12]`,
`0 < A < 2^16`, the interval `[C, C + A)` fits below the carry bit at the next
`BYTEOUT` (`(C + A) · 2^CT ≤ 2^28`), and `B` is a byte. -/
def InvR (s : EncState) : Prop :=
  1 ≤ s.CT ∧ s.CT ≤ 12 ∧ 0 < s.A ∧ s.A < 2 ^ 16 ∧ (s.C + s.A) * 2 ^ s.CT ≤ 2 ^ 28 ∧
    s.B < 256

/-- `InvR` plus `A ≥ 0x8000`: the invariant at symbol boundaries. -/
def InvB (s : EncState) : Prop := InvR s ∧ 0x8000 ≤ s.A

private theorem two_pow_pos (n : Nat) : 0 < 2 ^ n := Nat.pow_pos (by omega)

private theorem two_le_pow (n : Nat) (h : 1 ≤ n) : 2 ≤ 2 ^ n := by
  have := Nat.pow_le_pow_right (n := 2) (by omega) h; simpa using this

private theorem InvR_C (s : EncState) (h : InvR s) : s.C + s.A ≤ 2 ^ 27 := by
  obtain ⟨h1, -, -, -, h5, -⟩ := h
  have := Nat.mul_le_mul_left (s.C + s.A) (two_le_pow s.CT h1)
  omega

private theorem renormeStep_eq (s : EncState) (hA : s.A < 0x8000) (hC : s.C < 2 ^ 31) :
    renormeStep s =
      if s.CT - 1 = 0 then byteout (shift1 s (2 * s.A)) else shift1 s (2 * s.A) := by
  have e1 : s.A * 2 % 0x10000 = 2 * s.A := by omega
  have e2 : s.C * 2 % 0x100000000 = s.C * 2 := by omega
  simp only [renormeStep, shift1, e1, e2]

private theorem shift_mul (C A m : Nat) : (C * 2 + 2 * A) * 2 ^ m = (C + A) * 2 ^ (m + 1) := by
  rw [Nat.pow_succ]; generalize 2 ^ m = p; grind

private theorem InvR_step (s : EncState) (h : InvR s) (hA : s.A < 0x8000) :
    InvR (renormeStep s) ∧ (renormeStep s).A = 2 * s.A := by
  have hc := InvR_C s h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  rw [renormeStep_eq s hA (by omega)]
  split
  · rename_i hct
    have hct1 : s.CT = 1 := by omega
    rw [hct1] at h5
    obtain ⟨bf, -, -, -, hCT, hA', hB', hC', -⟩ :=
      byteout_cases (shift1 s (2 * s.A)) (by simp [shift1]; omega) (by simp [shift1]; omega)
        (by simp [shift1]; omega)
    generalize byteout (shift1 s (2 * s.A)) = t at *
    have hA'' : t.A = 2 * s.A := hA'
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, hB'⟩, hA''⟩
    all_goals by_cases hf : bf = 0xFF
    all_goals simp only [hf, ↓reduceIte] at hCT
    all_goals simp only [hCT, hA'', Nat.reducePow, Nat.reduceSub] at hC' ⊢
    all_goals omega
  · rename_i hct
    refine ⟨⟨by simp [shift1]; omega, by simp [shift1]; omega, by simp [shift1]; omega,
      by simp [shift1]; omega, ?_, by simp [shift1]; omega⟩, rfl⟩
    simp only [shift1]
    have e : s.CT = (s.CT - 1) + 1 := by omega
    rw [shift_mul, ← e]; exact h5

private theorem Q_renormeStep (data : List UInt8) (hs : Syntax data) (s : EncState) (h : InvR s)
    (hA : s.A < 0x8000) (hq : Q data (renormeStep s)) : Q data s := by
  have hc := InvR_C s h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  rw [renormeStep_eq s hA (by omega)] at hq
  split at hq
  · rename_i hct
    have hct1 : s.CT = 1 := by omega
    rw [hct1] at h5
    exact Q_shift data s _ h1 (by omega) (by omega)
      (Q_byteout data hs _ (by simp [shift1]; omega) (by simp [shift1]; omega)
        (by simp [shift1]; omega) hq)
  · exact Q_shift data s _ h1 (by omega) (by omega) hq

private theorem InvR_loop :
    ∀ (n : Nat) (s : EncState), InvR s → s.A < 0x8000 → InvR (renormeLoop n s)
  | 0, s, h, _ => by simpa [renormeLoop] using h
  | n + 1, s, h, hA => by
    obtain ⟨hi, -⟩ := InvR_step s h hA
    simp only [renormeLoop]
    split
    · exact hi
    · rename_i hb
      rw [bit15_iff _ hi.2.2.2.1] at hb
      exact InvR_loop n _ hi (by omega)

private theorem Q_loop (data : List UInt8) (hs : Syntax data) :
    ∀ (n : Nat) (s : EncState), InvR s → s.A < 0x8000 → Q data (renormeLoop n s) → Q data s
  | 0, s, _, _, hq => by simpa [renormeLoop] using hq
  | n + 1, s, h, hA, hq => by
    obtain ⟨hi, -⟩ := InvR_step s h hA
    simp only [renormeLoop] at hq
    apply Q_renormeStep data hs s h hA
    split at hq
    · exact hq
    · rename_i hb
      rw [bit15_iff _ hi.2.2.2.1] at hb
      exact Q_loop data hs n _ hi (by omega) hq

/-- A symbol step that ends with `RENORME`: the state `s'` after the interval update. -/
private theorem via_renorm (data : List UInt8) (s s' : EncState) (h : InvB s)
    (hO : s'.outRev = s.outRev)
    (hB : s'.B = s.B) (hCT : s'.CT = s.CT) (hC : s.C ≤ s'.C) (hU : s'.C + s'.A ≤ s.C + s.A)
    (hA0 : 0 < s'.A) (hA1 : s'.A < 0x8000) :
    InvR s' ∧ InvB (renorme s') ∧ (Syntax data → Q data (renorme s') → Q data s) := by
  obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, h7⟩ := h
  have hi : InvR s' := by
    refine ⟨by omega, by omega, hA0, by omega, ?_, by omega⟩
    rw [hCT]; exact Nat.le_trans (Nat.mul_le_mul_right _ hU) h5
  refine ⟨hi, ⟨InvR_loop _ _ hi hA1, (renorme_fuel_suffices s' hA0 hA1).1⟩, ?_⟩
  intro hs hq
  exact Q_add data s s' hO hB hCT hC hU (Q_loop data hs _ _ hi hA1 hq)

/-- A symbol step without `RENORME`. -/
private theorem no_renorm (data : List UInt8) (s s' : EncState) (h : InvB s)
    (hO : s'.outRev = s.outRev)
    (hB : s'.B = s.B) (hCT : s'.CT = s.CT) (hC : s.C ≤ s'.C) (hU : s'.C + s'.A ≤ s.C + s.A)
    (hA1 : 0x8000 ≤ s'.A) (hA2 : s'.A < 2 ^ 16) :
    InvB s' ∧ (Q data s' → Q data s) := by
  obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, h7⟩ := h
  refine ⟨⟨⟨by omega, by omega, by omega, hA2, ?_, by omega⟩, hA1⟩, ?_⟩
  · rw [hCT]; exact Nat.le_trans (Nat.mul_le_mul_right _ hU) h5
  · exact Q_add data s s' hO hB hCT hC hU

private theorem encode_step (data : List UInt8) (s : EncState) (cxs : Contexts) (cx : Nat)
    (d : Bool)
    (h : InvB s) :
    InvB (encode s cxs cx d).1 ∧ (Syntax data → Q data (encode s cxs cx d).1 → Q data s) := by
  have hq := qeAt_qe_bounds (cxs.get cx).index
  have hc := InvR_C s h.1
  have hA := h.1.2.2.2.1
  have hA8 := h.2
  simp only [encode]
  split
  · simp only [codeMps]
    split
    · rename_i hb
      rw [bit15_iff _ (by omega)] at hb
      obtain ⟨r1, r2⟩ := no_renorm data s
        { s with C := (s.C + (qeAt (cxs.get cx).index).qe) % 4294967296,
                 A := (s.A - (qeAt (cxs.get cx).index).qe) % 65536 } h rfl rfl rfl
        (by simp only; omega) (by simp only; omega) (by simp only; omega) (by simp only; omega)
      exact ⟨r1, fun _ => r2⟩
    · rename_i hb
      rw [bit15_iff _ (by omega)] at hb
      split
      · obtain ⟨-, r1, r2⟩ := via_renorm data s { s with A := (qeAt (cxs.get cx).index).qe }
          h rfl rfl rfl (by simp only; omega) (by simp only; omega) (by simp only; omega)
          (by simp only; omega)
        exact ⟨r1, r2⟩
      · obtain ⟨-, r1, r2⟩ := via_renorm data s
          { s with C := (s.C + (qeAt (cxs.get cx).index).qe) % 4294967296,
                   A := (s.A - (qeAt (cxs.get cx).index).qe) % 65536 }
          h rfl rfl rfl (by simp only; omega) (by simp only; omega) (by simp only; omega)
          (by simp only; omega)
        exact ⟨r1, r2⟩
  · simp only [codeLps]
    split
    · obtain ⟨-, r1, r2⟩ := via_renorm data s
        { s with C := (s.C + (qeAt (cxs.get cx).index).qe) % 4294967296,
                 A := (s.A - (qeAt (cxs.get cx).index).qe) % 65536 }
        h rfl rfl rfl (by simp only; omega) (by simp only; omega) (by simp only; omega)
        (by simp only; omega)
      exact ⟨r1, r2⟩
    · obtain ⟨-, r1, r2⟩ := via_renorm data s { s with A := (qeAt (cxs.get cx).index).qe }
        h rfl rfl rfl (by simp only; omega) (by simp only; omega) (by simp only; omega)
        (by simp only; omega)
      exact ⟨r1, r2⟩

/-! ## Byte syntax of the encoder output (no marker codes inside the code-word) -/

/-- Forward byte syntax: a `0xFF` is followed by a byte `< 0x90`. -/
def SynF (l : List Nat) : Prop := ∀ i (h : i + 1 < l.length), l[i] = 0xFF → l[i + 1] < 0x90

private theorem SynF_append (l : List Nat) (b : Nat) (h : SynF l)
    (hb : l.getLast? = some 0xFF → b < 0x90) : SynF (l ++ [b]) := by
  intro i hi heq
  simp only [List.length_append, List.length_cons, List.length_nil] at hi
  by_cases h1 : i + 1 < l.length
  · rw [List.getElem_append_left (by omega)] at heq
    rw [List.getElem_append_left h1]
    exact h i h1 heq
  · have hi' : i + 1 = l.length := by omega
    rw [List.getElem_append_left (by omega)] at heq
    rw [List.getElem_append_right (by omega)]
    simp only [hi', Nat.sub_self, List.getElem_cons_zero]
    apply hb
    rw [List.getLast?_eq_getElem?]
    have : l.length - 1 = i := by omega
    rw [this, List.getElem?_eq_getElem (by omega), heq]

/-- `(C + A) · 2^CT` bounded by the next carry position, and `A > 0`. -/
def InvC (s : EncState) : Prop := (s.C + s.A) * 2 ^ s.CT ≤ 2 ^ 28 ∧ 0 < s.A

/-- The syntax invariant: bytes are bytes, the written bytes have the syntax, the byte after
a written `0xFF` will be `< 0x90` (even after a carry), the dummy byte is `0` and no carry
reaches it. -/
def InvS0 (s : EncState) : Prop :=
  s.B < 256 ∧ (∀ x ∈ s.outRev, x < 256) ∧ SynF s.outRev.reverse ∧
  (s.outRev.head? = some 0xFF → s.B * 2 ^ 27 + (s.C + s.A) * 2 ^ s.CT ≤ 0x90 * 2 ^ 27) ∧
  (s.outRev = [] → s.B = 0 ∧ (s.C + s.A) * 2 ^ s.CT ≤ 2 ^ 27) ∧
  (s.B :: s.outRev).getLast? = some 0

/-- A buffered `0xFF` leaves room for at most `0x8F` in the next byte. -/
def InvF1 (s : EncState) : Prop := s.B = 0xFF → (s.C + s.A) * 2 ^ s.CT ≤ 2 ^ 27 + 2 ^ 24

/-- The full syntax invariant. -/
def InvS (s : EncState) : Prop := InvC s ∧ InvS0 s ∧ InvF1 s

private theorem InvS_mono (s s' : EncState) (hO : s'.outRev = s.outRev) (hB : s'.B = s.B)
    (hU : (s'.C + s'.A) * 2 ^ s'.CT ≤ (s.C + s.A) * 2 ^ s.CT) (hA : 0 < s'.A)
    (h : InvS s) : InvS s' := by
  obtain ⟨⟨c1, -⟩, ⟨s1, s2, s3, s4, s5, s6⟩, f1⟩ := h
  refine ⟨⟨by omega, hA⟩, ⟨by rw [hB]; exact s1, by rw [hO]; exact s2, by rw [hO]; exact s3,
    ?_, ?_, by rw [hO, hB]; exact s6⟩, ?_⟩
  · intro h; rw [hO] at h; have := s4 h; rw [hB]; omega
  · intro h; rw [hO] at h; have := s5 h; rw [hB]; omega
  · intro h; rw [hB] at h; have := f1 h; omega

private theorem InvS_byteout (s : EncState) (h0 : s.CT = 0) (h : InvS s) :
    InvS0 (byteout s) ∧ (s.A ≤ 2 ^ 16 → InvC (byteout s) ∧ InvF1 (byteout s)) := by
  obtain ⟨⟨c1, c2⟩, ⟨s1, s2, s3, s4, s5, s6⟩, f1⟩ := h
  simp only [InvF1] at f1
  rw [h0, Nat.pow_zero, Nat.mul_one] at c1 s4 s5 f1
  obtain ⟨bf, hO, hbf, hbf256, hCT, hA, hB', hC', hv, hnc, h7, h8⟩ :=
    byteout_cases s h0 (by lia) s1
  generalize byteout s = t at *
  simp only [InvC, InvF1]
  simp only [Nat.reducePow, Nat.reduceMul] at *
  have hbf_le : bf * 134217728 ≤ s.B * 134217728 + s.C := by lia
  refine ⟨⟨hB', ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [hO]; intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hbf256
    · exact s2 x hx
  · rw [hO, List.reverse_cons]
    apply SynF_append _ _ s3
    intro hh
    rw [List.getLast?_reverse] at hh
    have := s4 hh
    lia
  · intro hh
    rw [hO] at hh
    simp only [List.head?_cons, Option.some.injEq] at hh
    have hct : t.CT = 7 := by rw [hCT]; simp [hh]
    rw [hct] at hC' hv ⊢
    simp only [Nat.reducePow, Nat.reduceSub] at hC' hv ⊢
    rcases h7 hh with e | e
    · rcases hbf with h9 | ⟨h9, h10⟩
      · lia
      · lia
    · rcases hbf with h9 | ⟨h9, h10⟩
      · have := f1 (by lia); rw [hA]; lia
      · lia
  · intro hh; rw [hO] at hh; simp at hh
  · rw [hO]
    cases hr : s.outRev with
    | nil =>
      have := s5 hr
      have : bf = s.B := hnc (by lia)
      simp only [hr, List.getLast?_cons_cons, List.getLast?_singleton] at s6 ⊢
      rw [this]; exact s6
    | cons y l =>
      rw [hr] at s6
      simp only [List.getLast?_cons_cons] at s6 ⊢
      exact s6
  · intro hA16
    have hA16' : t.A ≤ 65536 := by rw [hA]; lia
    have hA0 : 0 < t.A := by rw [hA]; lia
    by_cases hf : bf = 0xFF
    · have hct : t.CT = 7 := by rw [hCT]; simp [hf]
      rw [hct] at hC' hv ⊢
      simp only [Nat.reducePow, Nat.reduceSub] at hC' hv ⊢
      refine ⟨⟨by lia, hA0⟩, ?_⟩
      intro hB'f
      exfalso
      rcases h7 hf with e | e
      · lia
      · rcases hbf with h9 | ⟨h9, h10⟩
        · have := f1 (by lia); lia
        · lia
    · have hct : t.CT = 8 := by rw [hCT]; simp [hf]
      rw [hct] at hC' hv ⊢
      simp only [Nat.reducePow, Nat.reduceSub] at hC' hv ⊢
      refine ⟨⟨by lia, hA0⟩, ?_⟩
      intro _
      lia

private theorem InvS_step (s : EncState) (h : InvR s) (hA : s.A < 0x8000) (hs : InvS s) :
    InvS (renormeStep s) := by
  have hc := InvR_C s h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have hsh : InvS (shift1 s (2 * s.A)) := by
    apply InvS_mono s (shift1 s (2 * s.A)) rfl rfl _ (by simp [shift1]; omega) hs
    simp only [shift1]
    have e : s.CT = (s.CT - 1) + 1 := by omega
    rw [shift_mul, ← e]
    exact Nat.le_refl _
  rw [renormeStep_eq s hA (by omega)]
  split
  · obtain ⟨r1, r2⟩ := InvS_byteout _ (by simp [shift1]; omega) hsh
    obtain ⟨r3, r4⟩ := r2 (by simp [shift1]; omega)
    exact ⟨r3, r1, r4⟩
  · exact hsh

private theorem InvS_loop : ∀ (n : Nat) (s : EncState), InvR s → s.A < 0x8000 → InvS s →
    InvS (renormeLoop n s)
  | 0, s, _, _, hs => by simpa [renormeLoop] using hs
  | n + 1, s, h, hA, hs => by
    obtain ⟨hi, -⟩ := InvR_step s h hA
    have hs' := InvS_step s h hA hs
    simp only [renormeLoop]
    split
    · exact hs'
    · rename_i hb
      rw [bit15_iff _ hi.2.2.2.1] at hb
      exact InvS_loop n _ hi (by omega) hs'

private theorem encode_stepS (s : EncState) (cxs : Contexts) (cx : Nat) (d : Bool)
    (h : InvB s) (hs : InvS s) : InvS (encode s cxs cx d).1 := by
  have hq := qeAt_qe_bounds (cxs.get cx).index
  have hc := InvR_C s h.1
  have hA := h.1.2.2.2.1
  have hA8 := h.2
  have hmono : ∀ s' : EncState, s'.outRev = s.outRev → s'.B = s.B → s'.CT = s.CT →
      s'.C + s'.A ≤ s.C + s.A → 0 < s'.A → InvS s' := by
    intro s' h1 h2 h3 h4 h5
    exact InvS_mono s s' h1 h2 (by rw [h3]; exact Nat.mul_le_mul_right _ h4) h5 hs
  have hren : ∀ s' : EncState, s'.outRev = s.outRev → s'.B = s.B → s'.CT = s.CT →
      s.C ≤ s'.C →
      s'.C + s'.A ≤ s.C + s.A → 0 < s'.A → s'.A < 0x8000 → InvS (renorme s') := by
    intro s' h1 h2 h3 h4 h5 h6 h7
    obtain ⟨hi, -, -⟩ := via_renorm [] s s' h h1 h2 h3 h4 h5 h6 h7
    exact InvS_loop _ _ hi h7 (hmono s' h1 h2 h3 h5 h6)
  simp only [encode]
  split
  · simp only [codeMps]
    split
    · rename_i hb
      rw [bit15_iff _ (by omega)] at hb
      exact hmono _ rfl rfl rfl (by simp only; omega) (by simp only; omega)
    · rename_i hb
      rw [bit15_iff _ (by omega)] at hb
      split
      · exact hren { s with A := (qeAt (cxs.get cx).index).qe } rfl rfl rfl
          (by simp only; omega) (by simp only; omega) (by simp only; omega) (by simp only; omega)
      · exact hren { s with C := (s.C + (qeAt (cxs.get cx).index).qe) % 4294967296,
                            A := (s.A - (qeAt (cxs.get cx).index).qe) % 65536 } rfl rfl rfl
          (by simp only; omega) (by simp only; omega) (by simp only; omega) (by simp only; omega)
  · simp only [codeLps]
    split
    · exact hren { s with C := (s.C + (qeAt (cxs.get cx).index).qe) % 4294967296,
                          A := (s.A - (qeAt (cxs.get cx).index).qe) % 65536 } rfl rfl rfl
        (by simp only; omega) (by simp only; omega) (by simp only; omega) (by simp only; omega)
    · exact hren { s with A := (qeAt (cxs.get cx).index).qe } rfl rfl rfl
        (by simp only; omega) (by simp only; omega) (by simp only; omega) (by simp only; omega)

private theorem initenc_inv : InvB initenc ∧ InvS initenc := by
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ⟨?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;>
    simp [initenc, SynF, InvF1]

private theorem encodeMany_inv : ∀ (ps : List (Nat × Bool)) (s : EncState) (cxs : Contexts),
    InvB s → InvS s → InvB (encodeMany s cxs ps).1 ∧ InvS (encodeMany s cxs ps).1
  | [], s, cxs, h1, h2 => ⟨h1, h2⟩
  | (cx, d) :: rest, s, cxs, h1, h2 => by
    simp only [encodeMany]
    exact encodeMany_inv rest _ _ (encode_step [] s cxs cx d h1).1 (encode_stepS s cxs cx d h1 h2)

/-! ## `FLUSH` -/

/-- `m` doublings of the frame at once (`C`, `A` scaled, `CT` decreased). -/
def shiftN (s : EncState) (m : Nat) : EncState :=
  { s with C := s.C * 2 ^ m, A := s.A * 2 ^ m, CT := s.CT - m }

/-- The code-word `FLUSH` emits from its final state `t` (the last `B` is dropped when it is
`0xFF`, the dummy byte is dropped). -/
def outOf (t : EncState) : List UInt8 :=
  (((if t.B = 0xFF then t.outRev else t.B :: t.outRev).reverse).drop 1).map UInt8.ofNat

/-- `FLUSH` as a sequence of exact-interval steps: after `SETBITS` the interval is the single
point `[X, X + 1)` (`A := 1`), then the two shift-and-`BYTEOUT` rounds. -/
def fl0 (s : EncState) : EncState := { setbits s with A := 1 }
/-- First shift round of `FLUSH`. -/
def fl1 (s : EncState) : EncState := shiftN (fl0 s) s.CT
/-- First `BYTEOUT` of `FLUSH`. -/
def fl2 (s : EncState) : EncState := byteout (fl1 s)
/-- Second shift round of `FLUSH`. -/
def fl3 (s : EncState) : EncState := shiftN (fl2 s) (fl2 s).CT
/-- Second `BYTEOUT` of `FLUSH`. -/
def fl4 (s : EncState) : EncState := byteout (fl3 s)

private theorem setbits_facts (s : EncState) (h : InvB s) :
    s.C ≤ (setbits s).C ∧ (setbits s).C + 1 ≤ s.C + s.A ∧ (setbits s).C % 32768 = 32767 ∧
    (setbits s).B = s.B ∧ (setbits s).outRev = s.outRev ∧ (setbits s).CT = s.CT := by
  have hc := InvR_C s h.1
  have h8 := h.2
  refine ⟨?_, ?_, ?_, rfl, rfl, rfl⟩ <;> simp only [setbits] <;> split <;> omega

private theorem Lx_shiftN (s : EncState) (m : Nat) (hm : m ≤ s.CT) (h : s.CT ≤ 27) :
    Lx (shiftN s m) = Lx s * 2 ^ m ∧ piE (shiftN s m) = piE s + m := by
  simp only [Lx, piE, shiftN]
  constructor
  · have e : 27 - (s.CT - m) = (27 - s.CT) + m := by omega
    rw [e, Nat.pow_add]
    generalize dvR (s.B :: s.outRev) = d
    generalize 2 ^ (27 - s.CT) = p
    generalize 2 ^ m = q
    grind
  · omega

private theorem shiftN_succ (s : EncState) (m : Nat) :
    shiftN s (m + 1) = shiftN (shift1 s (2 * s.A)) m := by
  simp only [shiftN, shift1, EncState.mk.injEq]
  refine ⟨?_, ?_, by omega, trivial, trivial⟩
  · rw [Nat.pow_succ]; generalize 2 ^ m = p; grind
  · rw [Nat.pow_succ]; generalize 2 ^ m = p; grind

private theorem shiftN_zero (s : EncState) : shiftN s 0 = s := by
  simp [shiftN]

private theorem Q_shiftN (data : List UInt8) :
    ∀ (m : Nat) (s : EncState), m ≤ s.CT → s.CT ≤ 27 → Q data (shiftN s m) → Q data s
  | 0, s, _, _, hq => by rwa [shiftN_zero] at hq
  | m + 1, s, hm, h27, hq => by
    rw [shiftN_succ] at hq
    exact Q_shift data s _ (by omega) h27 (Nat.le_refl _)
      (Q_shiftN data m _ (by simp [shift1]; omega) (by simp [shift1]; omega) hq)

private theorem InvS_shiftN (s : EncState) (m : Nat) (hm : m ≤ s.CT) (h : InvS s) :
    InvS (shiftN s m) := by
  apply InvS_mono s (shiftN s m) rfl rfl _ _ h
  · simp only [shiftN]
    have e : s.CT = (s.CT - m) + m := by omega
    conv => rhs; rw [e, Nat.pow_add]
    generalize 2 ^ m = p
    generalize 2 ^ (s.CT - m) = q
    apply Nat.le_of_eq; grind
  · simp only [shiftN]
    exact Nat.mul_pos h.1.2 (two_pow_pos _)

private theorem byteout_congr (s t : EncState) (hB : s.B = t.B) (hC : s.C = t.C)
    (hO : s.outRev = t.outRev) :
    (byteout s).B = (byteout t).B ∧ (byteout s).C = (byteout t).C ∧
    (byteout s).outRev = (byteout t).outRev ∧ (byteout s).CT = (byteout t).CT := by
  obtain ⟨C, A, CT, B, O⟩ := s
  obtain ⟨C', A', CT', B', O'⟩ := t
  simp only at hB hC hO
  subst hB hC hO
  simp only [byteout, byteout7, byteout8]
  by_cases h1 : B = 0xFF <;> by_cases h2 : C < 0x8000000 <;> by_cases h3 : B + 1 = 0xFF <;>
    simp [h1, h2, h3]

private theorem outOf_congr (t t' : EncState) (hB : t.B = t'.B) (hO : t.outRev = t'.outRev) :
    outOf t = outOf t' := by
  simp [outOf, hB, hO]

private theorem mul_pow_lt (c k : Nat) (hk : k ≤ 27) (h : c < 2 ^ (27 - k)) :
    c * 2 ^ k < 2 ^ 27 := by
  have : 2 ^ 27 = 2 ^ (27 - k) * 2 ^ k := by rw [← Nat.pow_add]; congr 1; omega
  rw [this]
  exact Nat.mul_lt_mul_of_pos_right h (two_pow_pos _)

private theorem flush_eq (s : EncState) (h : InvB s) : flush s = outOf (fl4 s) := by
  obtain ⟨sb1, sb2, sb3, sbB, sbO, sbCT⟩ := setbits_facts s h
  have hR := h.1
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hR
  have hX : (setbits s).C * 2 ^ s.CT < 2 ^ 28 := by
    have h7 := Nat.mul_le_mul_right (2 ^ s.CT) sb2
    have h8 := two_pow_pos s.CT
    rw [Nat.add_mul] at h7
    omega
  have e1 := byteout_congr
    { setbits s with C := (setbits s).C * 2 ^ (setbits s).CT % 0x100000000 } (fl1 s)
    (by simp [fl1, fl0, shiftN, sbB]) (by simp only [fl1, fl0, shiftN, sbCT]; omega)
    (by simp [fl1, fl0, shiftN, sbO])
  have hf1 : (fl1 s).CT = 0 ∧ (fl1 s).C < 2 ^ 28 ∧ (fl1 s).B < 256 := by
    simp only [fl1, fl0, shiftN, sbCT, sbB]; omega
  obtain ⟨bf2, -, -, -, hCT2, -, -, hC2, -⟩ := byteout_cases (fl1 s) hf1.1 hf1.2.1 hf1.2.2
  have hct2 : (fl2 s).CT ≤ 27 := by
    simp only [fl2] at hCT2 ⊢; rw [hCT2]; split <;> omega
  have hlt := mul_pow_lt _ _ hct2 hC2
  show outOf (byteout { (byteout
    { setbits s with C := (setbits s).C * 2 ^ (setbits s).CT % 0x100000000 }) with
    C := (byteout { setbits s with C := (setbits s).C * 2 ^ (setbits s).CT % 0x100000000 }).C *
      2 ^ (byteout { setbits s with C := (setbits s).C * 2 ^ (setbits s).CT % 0x100000000 }).CT %
      0x100000000 }) = _
  generalize byteout { setbits s with C := (setbits s).C * 2 ^ (setbits s).CT % 0x100000000 } = b1
    at e1 ⊢
  obtain ⟨eB, eC, eO, eCT⟩ := e1
  have e2 := byteout_congr { b1 with C := b1.C * 2 ^ b1.CT % 0x100000000 } (fl3 s)
    (by simp [fl3, shiftN, fl2, eB]) (by simp only [fl3, shiftN, fl2, eC, eCT] at hlt ⊢; omega)
    (by simp [fl3, shiftN, fl2, eO])
  exact outOf_congr _ _ e2.1 e2.2.2.1

private theorem outOf_getD (t : EncState) (i : Nat) :
    (outOf t).getD i 0xFF =
      (((if t.B = 0xFF then t.outRev else t.B :: t.outRev).reverse)[i + 1]?.map
        UInt8.ofNat).getD 0xFF := by
  simp only [outOf, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_drop]
  rw [Nat.add_comm 1 i]

private theorem outOf_length (t : EncState) :
    (outOf t).length + 1 = (if t.B = 0xFF then t.outRev.length else t.outRev.length + 1) ∨
      (outOf t).length = 0 ∧ t.B = 0xFF ∧ t.outRev = [] := by
  simp only [outOf, List.length_map, List.length_drop, List.length_reverse]
  split
  · cases t.outRev with
    | nil => right; simp_all
    | cons _ _ => left; simp
  · left; simp

private theorem outOf_vb (t : EncState) (hB : t.B < 256) (hall : ∀ x ∈ t.outRev, x < 256)
    (hlast : (t.B :: t.outRev).getLast? = some 0) (j : Nat) (hj : j < t.outRev.length + 1) :
    vb (outOf t) j = (t.outRev.reverse ++ [t.B])[j]'(by simp; omega) := by
  have hR : t.outRev.reverse ++ [t.B] = (t.B :: t.outRev).reverse := by simp
  unfold vb
  split
  · rename_i h0
    subst h0
    have : (t.B :: t.outRev).reverse[0]? = some 0 := by
      rw [← List.head?_eq_getElem?, List.head?_reverse, hlast]
    simp only [hR]
    rw [List.getElem?_eq_getElem (by simp)] at this
    simp only [Option.some.injEq] at this
    exact this.symm
  · rename_i h0
    unfold byteAt
    rw [outOf_getD]
    have e : j - 1 + 1 = j := by omega
    rw [e]
    have hlt : (t.outRev.reverse ++ [t.B])[j]'(by simp; omega) < 256 := by
      rw [List.getElem_append]
      split
      · exact hall _ (by simp)
      · simpa using hB
    split
    · rename_i hf
      by_cases hjk : j < t.outRev.length
      · rw [List.getElem?_eq_getElem (by simpa using hjk)]
        simp only [Option.map_some, Option.getD_some, UInt8.toNat_ofNat']
        rw [List.getElem_append_left (by simpa using hjk)] at hlt ⊢
        omega
      · rw [List.getElem?_eq_none (by simp; omega)]
        rw [List.getElem_append_right (by simp; omega)]
        simp [hf]
    · rw [List.getElem?_eq_getElem (by simp; omega)]
      simp only [Option.map_some, Option.getD_some, UInt8.toNat_ofNat']
      simp only [hR] at hlt ⊢
      omega

private theorem ones_lemma (X m u : Nat) (hX : X % 32768 = 32767) (hu : u ≤ m + 15) :
    2 ^ u ≤ X * 2 ^ m % 2 ^ u + 2 ^ m := by
  by_cases hmu : u ≤ m
  · have := Nat.pow_le_pow_right (n := 2) (by omega) hmu; omega
  · obtain ⟨r, rfl⟩ : ∃ r, u = m + r := ⟨u - m, by omega⟩
    have hr : r ≤ 15 := by omega
    rw [Nat.pow_add, Nat.mul_comm (2 ^ m) (2 ^ r), Nat.mul_mod_mul_right]
    have h1 : X % 2 ^ r = 2 ^ r - 1 := by
      rw [← Nat.mod_mod_of_dvd X (Nat.pow_dvd_pow 2 hr)]
      have : X % 2 ^ 15 = 32767 := hX
      rw [this]
      have key : ∀ r, r ≤ 15 → 32767 % 2 ^ r = 2 ^ r - 1 := by decide
      exact key r hr
    rw [h1]
    have := two_pow_pos r
    rw [Nat.sub_mul, Nat.one_mul]
    have : 2 ^ m ≤ 2 ^ r * 2 ^ m := Nat.le_mul_of_pos_left _ this
    omega

/-- The final state of `FLUSH` satisfies `Q` against its own output. -/
private theorem Q_base (t : EncState) (hB : t.B < 256) (hall : ∀ x ∈ t.outRev, x < 256)
    (hlast : (t.B :: t.outRev).getLast? = some 0) (hCT : t.CT ≤ 8)
    (hC : t.C < 2 ^ (27 - t.CT)) (hU : 2 ^ (27 - t.CT) ≤ t.C + t.A)
    (hs : Syntax (outOf t)) : Q (outOf t) t := by
  have hvb := outOf_vb t hB hall hlast
  have hlen := outOf_length t
  have hk : t.outRev.length ≤ (outOf t).length + 1 := by
    rcases hlen with h | ⟨h1, h2, h3⟩
    · split at h <;> omega
    · simp [h3]
  have hn : (outOf t).length ≤ t.outRev.length := by
    rcases hlen with h | ⟨h1, h2, h3⟩
    · split at h <;> omega
    · omega
  have hext1 : t.outRev.reverse = (List.range t.outRev.length).map (vb (outOf t)) := by
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [hvb i (by simp at h1; omega), List.getElem_append_left h1]
  have hext2 : vb (outOf t) t.outRev.length = t.B := by
    rw [hvb _ (by omega), List.getElem_append_right (by simp)]
    simp
  obtain ⟨hp, hd⟩ := bridge (outOf t) hs t.outRev hext1 hk t.B
  rw [hext2] at hd
  have hG : dvR (t.B :: t.outRev) = vval (outOf t) t.outRev.length := by omega
  have hpi : piE t = vpos (outOf t) t.outRev.length + (27 - t.CT) := by
    simp only [piE, hp]; omega
  have hLx : Lx t = vval (outOf t) t.outRev.length * 2 ^ (27 - t.CT) + t.C := by
    simp only [Lx, hG]
  refine ⟨⟨hext1, .inl hext2, hk⟩, ?_, ?_⟩
  · intro k c ℓ hkk hv hl
    obtain ⟨-, hones⟩ := vval_ones (outOf t) _ hn (k - t.outRev.length)
    rw [Nat.add_sub_cancel' (by omega)] at hones
    generalize vval (outOf t) t.outRev.length = G at *
    generalize hD : vpos (outOf t) k - vpos (outOf t) t.outRev.length = D at *
    have hD' : vpos (outOf t) t.outRev.length ≤ vpos (outOf t) k := by
      have := vpos_le (outOf t) t.outRev.length (k - t.outRev.length)
      rw [Nat.add_sub_cancel' (by omega)] at this; omega
    have e : piE t + c - vpos (outOf t) k + D = c + (27 - t.CT) := by omega
    have h1 : Lx t < (G + 1) * 2 ^ (27 - t.CT) := by rw [hLx, Nat.add_mul]; omega
    have h2 : ℓ * 2 ^ (piE t + c - vpos (outOf t) k) * 2 ^ D <
        (G + 1) * 2 ^ (27 - t.CT) * 2 ^ D :=
      Nat.mul_lt_mul_of_pos_right (Nat.lt_of_le_of_lt hl h1) (two_pow_pos _)
    rw [Nat.mul_assoc, ← Nat.pow_add, e, Nat.pow_add] at h2
    have h3 : ℓ * 2 ^ c * 2 ^ (27 - t.CT) < (G + 1) * 2 ^ D * 2 ^ (27 - t.CT) := by
      simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h2
    have h3 := Nat.lt_of_mul_lt_mul_right h3
    omega
  · intro k c hv
    have hkk : t.outRev.length < k := by
      apply lt_of_vpos_lt; rw [hv, hpi]; omega
    obtain ⟨-, hones⟩ := vval_ones (outOf t) _ hn (k - t.outRev.length)
    rw [Nat.add_sub_cancel' (by omega)] at hones
    have hD : vpos (outOf t) k - vpos (outOf t) t.outRev.length = (27 - t.CT) + c := by omega
    rw [hD, Nat.pow_add] at hones
    rw [hLx]
    generalize vval (outOf t) t.outRev.length = G at *
    have h1 : (G + 1) * 2 ^ (27 - t.CT) ≤ G * 2 ^ (27 - t.CT) + t.C + t.A := by
      rw [Nat.add_mul]; omega
    have h2 := Nat.mul_le_mul_right (2 ^ c) h1
    rw [Nat.mul_assoc] at h2
    omega

/-- The output byte syntax of the final `FLUSH` state. -/
private theorem syntax_outOf (t : EncState) (hB : t.B < 256) (hall : ∀ x ∈ t.outRev, x < 256)
    (hsyn : SynF t.outRev.reverse) (hhead : t.outRev.head? = some 0xFF → t.B < 0x90) :
    Syntax (outOf t) := by
  generalize hM : (if t.B = 0xFF then t.outRev else t.B :: t.outRev).reverse = M
  have hMs : SynF M := by
    rw [← hM]; split
    · exact hsyn
    · rw [List.reverse_cons]
      exact SynF_append _ _ hsyn (by rw [List.getLast?_reverse]; exact hhead)
  have hMl : M.getLast? ≠ some 0xFF := by
    rw [← hM, List.getLast?_reverse]
    split
    · rename_i hf; intro h; have := hhead h; omega
    · rename_i hf; simp [hf]
  have hMa : ∀ x ∈ M, x < 256 := by
    rw [← hM]; split
    · simpa using hall
    · intro x hx
      simp only [List.mem_reverse, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hB
      · exact hall x hx
  have hget : ∀ i (h : i + 1 < M.length), byteAt (outOf t) i = M[i + 1] := by
    intro i h
    unfold byteAt
    rw [outOf_getD, hM, List.getElem?_eq_getElem h]
    simp only [Option.map_some, Option.getD_some, UInt8.toNat_ofNat']
    have := hMa _ (List.getElem_mem h)
    omega
  have hlen : (outOf t).length = M.length - 1 := by
    simp [outOf, ← hM]
  intro i hi hf
  rw [hlen] at hi ⊢
  rw [hget i (by omega)] at hf
  by_cases h2 : i + 2 < M.length
  · refine ⟨by omega, ?_⟩
    rw [hget (i + 1) h2]
    have := hMs (i + 1) h2 hf
    omega
  · exfalso
    apply hMl
    rw [List.getLast?_eq_getElem?]
    have : M.length - 1 = i + 1 := by omega
    rw [this, List.getElem?_eq_getElem (by omega), hf]

/-- `FLUSH` from a symbol boundary: its output has the byte syntax and satisfies `Q` at the
boundary state. -/
private theorem flush_Q (s : EncState) (h : InvB s) (hS : InvS s) :
    Syntax (flush s) ∧ Q (flush s) s := by
  rw [flush_eq s h]
  obtain ⟨sb1, sb2, sb3, sbB, sbO, sbCT⟩ := setbits_facts s h
  obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, h8⟩ := h
  have f0CT : (fl0 s).CT = s.CT := sbCT
  have f0B : (fl0 s).B = s.B := sbB
  have f0O : (fl0 s).outRev = s.outRev := sbO
  have f0C : (fl0 s).C = (setbits s).C := rfl
  have f0A : (fl0 s).A = 1 := rfl
  have hX : (setbits s).C * 2 ^ s.CT < 2 ^ 28 := by
    have h7 := Nat.mul_le_mul_right (2 ^ s.CT) sb2
    have h9 := two_pow_pos s.CT
    rw [Nat.add_mul] at h7
    omega
  have S0 : InvS (fl0 s) := InvS_mono s (fl0 s) f0O f0B
    (by rw [f0CT, f0C, f0A]; exact Nat.mul_le_mul_right _ sb2) (by rw [f0A]; omega) hS
  have S1 : InvS (fl1 s) := InvS_shiftN (fl0 s) s.CT (by rw [f0CT]; exact Nat.le_refl _) S0
  have f1CT : (fl1 s).CT = 0 := by simp [fl1, shiftN, f0CT]
  have f1C : (fl1 s).C = (setbits s).C * 2 ^ s.CT := rfl
  have f1A : (fl1 s).A = 2 ^ s.CT := by simp [fl1, shiftN, f0A]
  have f1B : (fl1 s).B = s.B := sbB
  obtain ⟨bf2, -, -, -, hCT2, hA2, hB2, hC2, -⟩ :=
    byteout_cases (fl1 s) f1CT (by rw [f1C]; exact hX) (by rw [f1B]; exact h6)
  obtain ⟨S2a, S2b⟩ := InvS_byteout (fl1 s) f1CT S1
  have hA16 : (fl1 s).A ≤ 2 ^ 16 := by
    rw [f1A]; exact Nat.pow_le_pow_right (by omega) (by omega)
  have S2 : InvS (fl2 s) := ⟨(S2b hA16).1, S2a, (S2b hA16).2⟩
  have hct2 : (fl2 s).CT = 7 ∨ (fl2 s).CT = 8 := by
    show (byteout (fl1 s)).CT = 7 ∨ (byteout (fl1 s)).CT = 8
    rw [hCT2]; split <;> simp
  have S3 : InvS (fl3 s) := InvS_shiftN (fl2 s) (fl2 s).CT (Nat.le_refl _) S2
  have f3CT : (fl3 s).CT = 0 := by simp [fl3, shiftN]
  have f3C : (fl3 s).C < 2 ^ 28 := by
    have hct2' : (byteout (fl1 s)).CT ≤ 27 := by rw [hCT2]; split <;> omega
    have := mul_pow_lt _ _ hct2' hC2
    show (fl2 s).C * 2 ^ (fl2 s).CT < 2 ^ 28
    exact Nat.lt_trans this (by decide)
  have f3B : (fl3 s).B < 256 := hB2
  obtain ⟨bf4, -, -, -, hCT4, hA4, hB4, hC4, -⟩ := byteout_cases (fl3 s) f3CT f3C f3B
  obtain ⟨⟨s4B, s4all, s4syn, s4head, -, s4last⟩, -⟩ := InvS_byteout (fl3 s) f3CT S3
  have hA4' : (fl4 s).A = (fl3 s).A := hA4
  have hC4' : (fl4 s).C < 2 ^ (27 - (fl4 s).CT) := hC4
  have hCT4' : (fl4 s).CT = if bf4 = 255 then 7 else 8 := hCT4
  have hA4pos : 0 < (fl4 s).A := by rw [show (fl4 s).A = (fl3 s).A from hA4]; exact S3.1.2
  have hsyn : Syntax (outOf (fl4 s)) := by
    apply syntax_outOf (fl4 s) s4B s4all s4syn
    intro hh
    have := s4head hh
    show (byteout (fl3 s)).B < 0x90
    have h9 : 0 < ((byteout (fl3 s)).C + (byteout (fl3 s)).A) * 2 ^ (byteout (fl3 s)).CT :=
      Nat.mul_pos (Nat.add_pos_right _ hA4pos) (two_pow_pos _)
    simp only [Nat.reducePow] at this
    lia
  have hct4 : (fl4 s).CT ≤ 8 := by
    rw [hCT4']; split <;> omega
  -- the ones below the last byte come from `SETBITS`
  have hU : 2 ^ (27 - (fl4 s).CT) ≤ (fl4 s).C + (fl4 s).A := by
    have L1 : Lx (fl4 s) = Lx (fl3 s) := (byteout_Lx (fl3 s) f3CT f3C f3B).1
    have L2 : Lx (fl3 s) = Lx (fl2 s) * 2 ^ (fl2 s).CT :=
      (Lx_shiftN (fl2 s) (fl2 s).CT (Nat.le_refl _) (by omega)).1
    have L3 : Lx (fl2 s) = Lx (fl1 s) :=
      (byteout_Lx (fl1 s) f1CT (by rw [f1C]; exact hX) (by rw [f1B]; exact h6)).1
    have L4 : Lx (fl1 s) = Lx (fl0 s) * 2 ^ s.CT :=
      (Lx_shiftN (fl0 s) s.CT (by rw [f0CT]; exact Nat.le_refl _) (by rw [f0CT]; omega)).1
    have L5 : Lx (fl0 s) = dvR (s.B :: s.outRev) * 2 ^ (27 - s.CT) + (setbits s).C := by
      simp only [Lx, f0B, f0O, f0CT, f0C]
    have A4 : (fl4 s).A = 2 ^ s.CT * 2 ^ (fl2 s).CT := by
      rw [hA4']; show (fl2 s).A * 2 ^ (fl2 s).CT = _
      rw [show (fl2 s).A = (fl1 s).A from hA2, f1A]
    rw [A4]
    have hu' : 19 ≤ 27 - (fl4 s).CT ∧ 27 - (fl4 s).CT ≤ 20 := by
      rw [hCT4']; split <;> simp
    generalize hu : 27 - (fl4 s).CT = u at hC4' hu' ⊢
    have hLx4 : Lx (fl4 s) = dvR ((fl4 s).B :: (fl4 s).outRev) * 2 ^ u + (fl4 s).C := by
      simp only [Lx, hu]
    have hmod : Lx (fl4 s) % 2 ^ u = (fl4 s).C := by
      rw [hLx4, Nat.mul_comm, Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hC4'
    rw [L1, L2, L3, L4, L5] at hmod
    generalize dvR (s.B :: s.outRev) = d0 at hmod
    generalize (setbits s).C = X at hmod sb3
    have e : (d0 * 2 ^ (27 - s.CT) + X) * 2 ^ s.CT * 2 ^ (fl2 s).CT =
        2 ^ u * (d0 * 2 ^ (27 + (fl2 s).CT - u)) + X * (2 ^ s.CT * 2 ^ (fl2 s).CT) := by
      have e1 : 2 ^ (27 - s.CT) * 2 ^ s.CT * 2 ^ (fl2 s).CT =
          2 ^ u * 2 ^ (27 + (fl2 s).CT - u) := by
        rw [← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
      generalize 2 ^ (27 - s.CT) = p at e1
      generalize 2 ^ s.CT = q at e1
      generalize 2 ^ (fl2 s).CT = r at e1
      generalize 2 ^ u = v at e1
      generalize 2 ^ (27 + (fl2 s).CT - u) = w at e1
      grind
    rw [e, Nat.mul_add_mod, ← Nat.pow_add] at hmod
    rw [← Nat.pow_add, ← hmod]
    exact ones_lemma X _ u sb3 (by omega)
  have hq4 : Q (outOf (fl4 s)) (fl4 s) := Q_base (fl4 s) s4B s4all s4last hct4 hC4' hU hsyn
  refine ⟨hsyn, ?_⟩
  have hq3 : Q (outOf (fl4 s)) (fl3 s) := Q_byteout _ hsyn (fl3 s) f3CT f3C f3B hq4
  have hq2 : Q (outOf (fl4 s)) (fl2 s) :=
    Q_shiftN _ (fl2 s).CT (fl2 s) (Nat.le_refl _) (by omega) hq3
  have hq1 : Q (outOf (fl4 s)) (fl1 s) :=
    Q_byteout _ hsyn (fl1 s) f1CT (by rw [f1C]; exact hX) (by rw [f1B]; exact h6) hq2
  have hq0 : Q (outOf (fl4 s)) (fl0 s) :=
    Q_shiftN _ s.CT (fl0 s) (by rw [f0CT]; exact Nat.le_refl _) (by rw [f0CT]; omega) hq1
  exact Q_add _ s (fl0 s) f0O f0B f0CT (by rw [f0C]; exact sb1) (by rw [f0C, f0A]; exact sb2) hq0

/-- The encoder output satisfies `Q` at every symbol boundary of the run, and has the byte
syntax. -/
theorem run_Q : ∀ (ps : List (Nat × Bool)) (s : EncState) (cxs : Contexts), InvB s → InvS s →
    Syntax (flush (encodeMany s cxs ps).1) ∧ Q (flush (encodeMany s cxs ps).1) s
  | [], s, _, h1, h2 => flush_Q s h1 h2
  | (cx, d) :: rest, s, cxs, h1, h2 => by
    simp only [encodeMany]
    have i1 := (encode_step [] s cxs cx d h1).1
    have i2 := encode_stepS s cxs cx d h1 h2
    obtain ⟨hs, hq⟩ := run_Q rest _ _ i1 i2
    exact ⟨hs, (encode_step _ s cxs cx d h1).2 hs hq⟩

/-! ## The decoder simulates the encoder -/

/-- `BYTEIN` reads the next virtual byte: positioned at virtual byte `k` (`BP = min (k − 1) n`),
it adds byte `k + 1` with its width. -/
private theorem bytein_spec (data : List UInt8) (hs : Syntax data) (D : State) (k : Nat)
    (hk : 1 ≤ k)
    (hd : D.data = data) (hp : D.pos = min (k - 1) data.length) :
    (bytein D).C = (D.C + vb data (k + 1) * 2 ^ (16 - vw data (k + 1))) % 0x100000000 ∧
    (bytein D).CT = vw data (k + 1) ∧ (bytein D).pos = min k data.length ∧
    (bytein D).A = D.A ∧ (bytein D).data = D.data := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hvb : vb data (j + 1 + 1) = byteAt data (j + 1) := by simp [vb]
  rw [hvb]
  simp only [Nat.add_sub_cancel] at hp
  unfold bytein
  rw [hd]
  by_cases hlt : j < data.length
  · have hp' : D.pos = j := by rw [hp]; omega
    rw [hp']
    by_cases hf : byteAt data j = 0xFF
    · obtain ⟨h1, h2⟩ := hs j hlt hf
      have hw : vw data (j + 1 + 1) = 7 := by
        unfold vw
        rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega, by simpa using hf⟩)]
      simp only [hf, ↓reduceIte]
      rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [hw]
      · exact hw.symm
      · show j + 1 = _; omega
      all_goals first | trivial | rfl
    · have hw : vw data (j + 1 + 1) = 8 := by
        unfold vw; rw [ite_eq_right_of_eq_false _ _ (eq_false ?_)]; intro ⟨_, _, h3⟩
        have e : j + 1 + 1 - 2 = j := by omega
        rw [e] at h3; exact hf h3
      simp only [hf, ↓reduceIte]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [hw]
      · exact hw.symm
      · show j + 1 = _; omega
      all_goals first | trivial | rfl
  · have hp' : D.pos = data.length := by rw [hp]; omega
    rw [hp']
    have h1 : byteAt data data.length = 0xFF := byteAt_past _ _ (by omega)
    have h2 : byteAt data (data.length + 1) = 0xFF := byteAt_past _ _ (by omega)
    have h3 : byteAt data (j + 1) = 0xFF := byteAt_past _ _ (by omega)
    have hw : vw data (j + 1 + 1) = 8 := by
      unfold vw; rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
    simp only [h1, h2, h3, hw, ↓reduceIte, Nat.reduceSub, Nat.reducePow]
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by decide))]
    have : min (j + 1) data.length = data.length := Nat.min_eq_right (by omega)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · rfl
    · exact this.symm
    all_goals first | trivial | rfl

/-- The decoder state `D` corresponds to the encoder state `E` on `data`: same `A`; the
decoder has read up to virtual byte `k` with `CT` bits pending, at the encoder's frame; and
`C ≡ (what was read) − Lx E` modulo `2^32` (in the decoder's 16-bit-shifted units). -/
def Corr (data : List UInt8) (D : State) (E : EncState) : Prop :=
  D.data = data ∧ D.A = E.A ∧ D.C < 0x100000000 ∧ D.CT ≤ 8 ∧
  ∃ k, 1 ≤ k ∧ D.pos = min (k - 1) data.length ∧ vpos data k = piE E + D.CT ∧
    (D.C + Lx E * 65536) % 0x100000000 = vval data k * 2 ^ (16 - D.CT) % 0x100000000

private theorem renormeStep_facts (E : EncState) (h : InvR E) (hA : E.A < 0x8000) :
    Lx (renormeStep E) = 2 * Lx E ∧ piE (renormeStep E) = piE E + 1 ∧
    (renormeStep E).A = 2 * E.A := by
  have hc := InvR_C E h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have hL := Lx_shift1 E (2 * E.A) h1 (by omega)
  have hp := piE_shift1 E (2 * E.A) h1 (by omega)
  rw [renormeStep_eq E hA (by omega)]
  split
  · rename_i hct
    have hct1 : E.CT = 1 := by omega
    rw [hct1] at h5
    obtain ⟨b1, b2⟩ := byteout_Lx (shift1 E (2 * E.A)) (by simp [shift1]; omega)
      (by simp [shift1]; omega) (by simp [shift1]; omega)
    obtain ⟨-, -, -, -, -, hA', -⟩ := byteout_cases (shift1 E (2 * E.A))
      (by simp [shift1]; omega) (by simp [shift1]; omega) (by simp [shift1]; omega)
    exact ⟨b1.trans hL, b2.trans hp, hA'⟩
  · exact ⟨hL, hp, rfl⟩

private theorem corr_step (data : List UInt8) (hs : Syntax data) (D : State) (E : EncState)
    (h : InvR E) (hA : E.A < 0x8000) (hc : Corr data D E) :
    Corr data (renormStep D) (renormeStep E) := by
  obtain ⟨hL, hp, hA'⟩ := renormeStep_facts E h hA
  obtain ⟨hd, hAD, hC32, hct, k, hk1, hpos, hv, hcong⟩ := hc
  simp only [Corr]
  rw [hL, hp, hA']
  simp only [renormStep]
  split
  · rename_i h0
    obtain ⟨b1, b2, b3, b4, b5⟩ := bytein_spec data hs D k hk1 hd hpos
    have hw := vw_bounds data (k + 1)
    refine ⟨by rw [b5]; exact hd, by simp only [b4]; omega, by omega,
      by simp only [b2]; omega, k + 1, by omega, by simp only [b3]; omega, ?_, ?_⟩
    · simp only [b2, vpos]; omega
    · simp only [b1, b2, vval]
      rw [h0] at hcong
      simp only [Nat.sub_zero, Nat.reducePow] at hcong
      generalize vval data k = V at *
      generalize vb data (k + 1) = b at *
      generalize Lx E = L at *
      rcases (show vw data (k + 1) = 7 ∨ vw data (k + 1) = 8 by omega) with e | e <;>
        simp only [e, Nat.reducePow, Nat.reduceSub] <;> lia
  · rename_i h0
    refine ⟨hd, by omega, by omega, by omega, k, hk1, hpos,
      by omega, ?_⟩
    have e : 16 - (D.CT - 1) = (16 - D.CT) + 1 := by omega
    rw [e, Nat.pow_succ, ← Nat.mul_assoc]
    generalize vval data k * 2 ^ (16 - D.CT) = Y at *
    generalize Lx E = L at *
    lia

private theorem corr_loop (data : List UInt8) (hs : Syntax data) :
    ∀ (n : Nat) (D : State) (E : EncState), InvR E → E.A < 0x8000 → Corr data D E →
      Corr data (renormLoop n D) (renormeLoop n E)
  | 0, D, E, _, _, hc => by simpa [renormLoop, renormeLoop] using hc
  | n + 1, D, E, h, hA, hc => by
    have hc' := corr_step data hs D E h hA hc
    obtain ⟨hi, -⟩ := InvR_step E h hA
    have hAeq : (renormStep D).A = (renormeStep E).A := hc'.2.1
    simp only [renormLoop, renormeLoop, hAeq]
    by_cases hb : bit15 (renormeStep E).A
    · simp only [hb, ↓reduceIte]; exact hc'
    · simp only [hb, Bool.false_eq_true, ↓reduceIte]
      rw [bit15_iff _ hi.2.2.2.1] at hb
      exact corr_loop data hs n _ _ hi (by omega) hc'

private theorem put_get (cxs : Contexts) (cx : Nat) : cxs.put cx (cxs.get cx) = cxs := by
  unfold Contexts.put Contexts.get
  by_cases h : cx < cxs.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
    exact List.set_getElem_self h
  · exact List.set_eq_of_length_le (by omega)

private theorem corr_update (data : List UInt8) (D D' : State) (E E' : EncState)
    (hc : Corr data D E)
    (hd : D'.data = D.data) (hct : D'.CT = D.CT) (hpos : D'.pos = D.pos) (hA : D'.A = E'.A)
    (hO : E'.outRev = E.outRev) (hB : E'.B = E.B) (hCT : E'.CT = E.CT)
    (hC : D'.C + E'.C * 65536 = D.C + E.C * 65536) (hlt : D'.C < 0x100000000) :
    Corr data D' E' := by
  obtain ⟨h1, -, -, h4, k, hk1, hp, hv, hcong⟩ := hc
  have hpi : piE E' = piE E := by simp only [piE, hO, hB, hCT]
  have hL : D'.C + Lx E' * 65536 = D.C + Lx E * 65536 := by
    simp only [Lx, hO, hB, hCT]
    generalize dvR (E.B :: E.outRev) * 2 ^ (27 - E.CT) = X
    rw [Nat.add_mul, Nat.add_mul]; lia
  refine ⟨by rw [hd]; exact h1, hA, hlt, by omega, k, hk1, by rw [hpos]; exact hp,
    by rw [hpi, hct]; exact hv, ?_⟩
  rw [hL, hct]; exact hcong

/-- What the decoder's `C` register holds, relative to the encoder's next interval `E'`
(the interval after the current decision, before `RENORME`): `C` lies in that sub-interval. -/
private theorem window (data : List UInt8) (hs : Syntax data) (D : State) (E E' : EncState)
    (h : InvB E)
    (hc : Corr data D E) (hO : E'.outRev = E.outRev) (hB : E'.B = E.B) (hCT : E'.CT = E.CT)
    (hCle : E.C ≤ E'.C) (hU : E'.C + E'.A ≤ E.C + E.A) (hQ : Q data E') :
    (E'.C - E.C) * 65536 ≤ D.C ∧ D.C < (E'.C - E.C + E'.A) * 65536 := by
  obtain ⟨hd, hAD, hC32, hct, k, hk1, hpos, hv, hcong⟩ := hc
  obtain ⟨⟨he1, he2, he3⟩, hl, hu⟩ := hQ
  have hpi : piE E' = piE E := by simp only [piE, hO, hB, hCT]
  have hLx : Lx E' = Lx E + (E'.C - E.C) := by simp only [Lx, hO, hB, hCT]; omega
  obtain ⟨hp, -⟩ := bridge data hs E'.outRev he1 he3 E'.B
  have hkk : E'.outRev.length < k := by
    apply lt_of_vpos_lt data
    have : piE E = pR (E'.B :: E'.outRev) + 27 - E.CT := by simp [piE, hO, hB]
    have := h.1.2.1
    omega
  have LB := hl k D.CT (Lx E') hkk (by omega)
    (by rw [show piE E' + D.CT - vpos data k = 0 by omega, Nat.pow_zero, Nat.mul_one]
        exact Nat.le_refl _)
  have UB := hu k D.CT (by omega)
  have hP : 2 ^ D.CT * 2 ^ (16 - D.CT) = 65536 := by
    rw [← Nat.pow_add, show D.CT + (16 - D.CT) = 16 by omega]
  have LB' := Nat.mul_le_mul_right (2 ^ (16 - D.CT)) LB
  have UB' := Nat.mul_lt_mul_of_pos_right UB (two_pow_pos (16 - D.CT))
  rw [Nat.mul_assoc, hP] at LB' UB'
  generalize vval data k * 2 ^ (16 - D.CT) = Y at *
  rw [hLx] at LB' UB'
  generalize Lx E = L at *
  have hA16 := h.1.2.2.2.1
  lia

private theorem decode_eq (D : State) (cxs : Contexts) (cx : Nat) :
    decode D cxs cx =
      if D.chigh < (qeAt (cxs.get cx).index).qe then
        ((lpsExchange ((D.A - (qeAt (cxs.get cx).index).qe) % 65536) (cxs.get cx)).1,
         renormd { D with A := (qeAt (cxs.get cx).index).qe },
         cxs.put cx (lpsExchange ((D.A - (qeAt (cxs.get cx).index).qe) % 65536) (cxs.get cx)).2.2)
      else if bit15 ((D.A - (qeAt (cxs.get cx).index).qe) % 65536) then
        ((cxs.get cx).mps,
         { D with A := (D.A - (qeAt (cxs.get cx).index).qe) % 65536,
                  C := (D.chigh - (qeAt (cxs.get cx).index).qe) * 65536 + D.C % 65536 }, cxs)
      else
        ((mpsExchange ((D.A - (qeAt (cxs.get cx).index).qe) % 65536) (cxs.get cx)).1,
         renormd { D with A := (D.A - (qeAt (cxs.get cx).index).qe) % 65536,
                          C := (D.chigh - (qeAt (cxs.get cx).index).qe) * 65536 + D.C % 65536 },
         cxs.put cx
           (mpsExchange ((D.A - (qeAt (cxs.get cx).index).qe) % 65536) (cxs.get cx)).2) := by
  simp only [decode, lpsExchange_A]

/-- One decision: the decoder returns the encoded decision, the same contexts, and a state
corresponding to the encoder's next state. -/
private theorem dec_step (data : List UInt8) (hs : Syntax data) (E : EncState) (cxs : Contexts)
    (cx : Nat) (d : Bool) (D : State) (hI : InvB E) (hc : Corr data D E)
    (hQ : Q data (encode E cxs cx d).1) :
    (decode D cxs cx).1 = d ∧ (decode D cxs cx).2.2 = (encode E cxs cx d).2 ∧
      Corr data (decode D cxs cx).2.1 (encode E cxs cx d).1 := by
  have hq := qeAt_qe_bounds (cxs.get cx).index
  have hc' := hc
  obtain ⟨hd, hAD, hC32, hct, -⟩ := hc'
  have hcA := InvR_C E hI.1
  have hA16 := hI.1.2.2.2.1
  have hA8 := hI.2
  have hchigh : D.chigh = D.C / 65536 := by simp only [State.chigh]; omega
  rw [decode_eq, hchigh, hAD]
  simp only [encode, codeMps, codeLps] at hQ ⊢
  have hput := put_get cxs cx
  generalize cxs.get cx = st at *
  simp only [lpsExchange, mpsExchange]
  generalize qeAt st.index = e at *
  by_cases hm : (d == st.mps) = true
  · have hdm : d = st.mps := by simpa using hm
    simp only [hm, ↓reduceIte] at hQ ⊢
    by_cases hb : bit15 ((E.A - e.qe) % 65536) = true
    · simp only [hb, ↓reduceIte] at hQ ⊢
      have hb' := (bit15_iff _ (by omega)).1 hb
      have w := window data hs D E
        { E with C := (E.C + e.qe) % 4294967296, A := (E.A - e.qe) % 65536 } hI hc rfl rfl rfl
        (by simp only; omega) (by simp only; omega) hQ
      simp only at w
      have hch : ¬ D.C / 65536 < e.qe := by omega
      simp only [hch, ↓reduceIte]
      refine ⟨hdm.symm, hput.symm, ?_⟩
      exact corr_update data D _ E _ hc rfl rfl rfl rfl rfl rfl rfl (by simp only; omega)
        (by simp only; omega)
    · simp only [hb, Bool.false_eq_true, ↓reduceIte] at hQ ⊢
      have hb' : (E.A - e.qe) % 65536 < 0x8000 := by
        have := bit15_iff ((E.A - e.qe) % 65536) (by omega)
        rcases Nat.lt_or_ge ((E.A - e.qe) % 65536) 0x8000 with hh | hh
        · exact hh
        · exact absurd (this.2 hh) hb
      by_cases hlt : (E.A - e.qe) % 65536 < e.qe
      · simp only [hlt, ↓reduceIte] at hQ ⊢
        obtain ⟨hi, -, hback⟩ := via_renorm data E { E with A := e.qe } hI rfl rfl rfl
          (by simp only; omega) (by simp only; omega) (by simp only; omega)
          (by simp only; omega)
        have hQ' := Q_loop data hs _ _ hi (by simp only; omega) hQ
        have w := window data hs D E { E with A := e.qe } hI hc rfl rfl rfl
          (by simp only; omega) (by simp only; omega) hQ'
        simp only at w
        have hch : D.C / 65536 < e.qe := by omega
        simp only [hch, ↓reduceIte]
        refine ⟨hdm.symm, by first | trivial | rfl, ?_⟩
        exact corr_loop data hs _ _ _ hi (by simp only; omega)
          (corr_update data D _ E _ hc rfl rfl rfl rfl rfl rfl rfl (by simp only) (by omega))
      · simp only [hlt, ↓reduceIte] at hQ ⊢
        obtain ⟨hi, -, hback⟩ := via_renorm data E
          { E with C := (E.C + e.qe) % 4294967296, A := (E.A - e.qe) % 65536 } hI rfl rfl rfl
          (by simp only; omega) (by simp only; omega) (by simp only; omega)
          (by simp only; omega)
        have hQ' := Q_loop data hs _ _ hi (by simp only; omega) hQ
        have w := window data hs D E
          { E with C := (E.C + e.qe) % 4294967296, A := (E.A - e.qe) % 65536 } hI hc rfl rfl rfl
          (by simp only; omega) (by simp only; omega) hQ'
        simp only at w
        have hch : ¬ D.C / 65536 < e.qe := by omega
        simp only [hch, ↓reduceIte]
        refine ⟨hdm.symm, by first | trivial | rfl, ?_⟩
        exact corr_loop data hs _ _ _ hi (by simp only; omega)
          (corr_update data D _ E _ hc rfl rfl rfl rfl rfl rfl rfl (by simp only; omega)
            (by simp only; omega))
  · have hdm : d = !st.mps := by cases d <;> cases h : st.mps <;> simp_all
    simp only [hm, Bool.false_eq_true, ↓reduceIte] at hQ ⊢
    by_cases hlt : (E.A - e.qe) % 65536 < e.qe
    · simp only [hlt, ↓reduceIte] at hQ ⊢
      obtain ⟨hi, -, hback⟩ := via_renorm data E
        { E with C := (E.C + e.qe) % 4294967296, A := (E.A - e.qe) % 65536 } hI rfl rfl rfl
        (by simp only; omega) (by simp only; omega) (by simp only; omega)
        (by simp only; omega)
      have hQ' := Q_loop data hs _ _ hi (by simp only; omega) hQ
      have w := window data hs D E
        { E with C := (E.C + e.qe) % 4294967296, A := (E.A - e.qe) % 65536 } hI hc rfl rfl rfl
        (by simp only; omega) (by simp only; omega) hQ'
      simp only at w
      have hch : ¬ D.C / 65536 < e.qe := by omega
      have hb : bit15 ((E.A - e.qe) % 65536) = false := by
        have := bit15_iff ((E.A - e.qe) % 65536) (by omega)
        cases h : bit15 ((E.A - e.qe) % 65536)
        · rfl
        · exfalso; have := this.1 h; omega
      simp only [hch, ↓reduceIte, hb, Bool.false_eq_true]
      refine ⟨hdm.symm, by first | trivial | rfl, ?_⟩
      exact corr_loop data hs _ _ _ hi (by simp only; omega)
        (corr_update data D _ E _ hc rfl rfl rfl rfl rfl rfl rfl (by simp only; omega)
          (by simp only; omega))
    · simp only [hlt, ↓reduceIte] at hQ ⊢
      obtain ⟨hi, -, hback⟩ := via_renorm data E { E with A := e.qe } hI rfl rfl rfl
        (by simp only; omega) (by simp only; omega) (by simp only; omega)
        (by simp only; omega)
      have hQ' := Q_loop data hs _ _ hi (by simp only; omega) hQ
      have w := window data hs D E { E with A := e.qe } hI hc rfl rfl rfl
        (by simp only; omega) (by simp only; omega) hQ'
      simp only at w
      have hch : D.C / 65536 < e.qe := by omega
      simp only [hch, ↓reduceIte]
      refine ⟨hdm.symm, by first | trivial | rfl, ?_⟩
      exact corr_loop data hs _ _ _ hi (by simp only; omega)
        (corr_update data D _ E _ hc rfl rfl rfl rfl rfl rfl rfl (by simp only) (by omega))

/-- The decoder side: started in a state corresponding to an encoder state `E` of a run whose
output is `data`, the decoder returns the decisions the encoder codes from `E` on. -/
theorem dec_many (data : List UInt8) (hs : Syntax data) :
    ∀ (ps : List (Nat × Bool)) (E : EncState) (cxs : Contexts) (D : State), InvB E → InvS E →
      data = flush (encodeMany E cxs ps).1 → Corr data D E →
      (decodeMany D cxs (ps.map (·.1))).1 = ps.map (·.2)
  | [], _, _, _, _, _, _, _ => by simp [decodeMany]
  | (cx, d) :: rest, E, cxs, D, h1, h2, hd, hc => by
    have i1 := (encode_step data E cxs cx d h1).1
    have i2 := encode_stepS E cxs cx d h1 h2
    have hd' : data = flush (encodeMany (encode E cxs cx d).1 (encode E cxs cx d).2 rest).1 := by
      rw [hd]; rfl
    have hQ := (run_Q rest _ (encode E cxs cx d).2 i1 i2).2
    rw [← hd'] at hQ
    obtain ⟨r1, r2, r3⟩ := dec_step data hs E cxs cx d D h1 hc hQ
    simp only [List.map_cons, decodeMany]
    rw [r1, r2, dec_many data hs rest _ _ _ i1 i2 hd' r3]

private theorem corr_init (data : List UInt8) (hs : Syntax data) :
    Corr data (initdec data) initenc := by
  obtain ⟨b1, b2, b3, b4, b5⟩ := bytein_spec data hs
    { C := byteAt data 0 * 0x10000, A := 0, CT := 0, pos := 0, data } 1 (Nat.le_refl _) rfl
    (by simp)
  simp only [Nat.reduceAdd] at b1 b2 b3
  have hw := vw_bounds data 2
  have hw0 : vw data 0 = 8 := by simp [vw]
  have hw1 : vw data 1 = 8 := by simp [vw]
  have key : initdec data =
      { C := (bytein { C := byteAt data 0 * 0x10000, A := 0, CT := 0, pos := 0, data }).C *
          0x80 % 0x100000000,
        A := 0x8000,
        CT := (bytein { C := byteAt data 0 * 0x10000, A := 0, CT := 0, pos := 0, data }).CT - 7,
        pos := (bytein { C := byteAt data 0 * 0x10000, A := 0, CT := 0, pos := 0, data }).pos,
        data := (bytein { C := byteAt data 0 * 0x10000, A := 0, CT := 0, pos := 0, data }).data } :=
    rfl
  rw [key]
  generalize bytein { C := byteAt data 0 * 0x10000, A := 0, CT := 0, pos := 0, data } = t at *
  simp only at b1 b5
  refine ⟨b5, rfl, ?_, ?_, 2, by omega, ?_, ?_, ?_⟩
  · show t.C * 128 % 4294967296 < 4294967296; omega
  · show t.CT - 7 ≤ 8; omega
  · show t.pos = _; rw [b3]
  · show vpos data 2 = piE initenc + (t.CT - 7)
    simp only [vpos, hw0, hw1, piE, initenc, pR, wOf, b2]
    simp; omega
  · show (t.C * 128 % 4294967296 + Lx initenc * 65536) % 4294967296 =
      vval data 2 * 2 ^ (16 - (t.CT - 7)) % 4294967296
    have hL : Lx initenc = 0 := by simp [Lx, initenc, dvR]
    have hv2 : vval data 2 = byteAt data 0 * 2 ^ vw data 2 + vb data 2 := by
      simp [vval, vb, hw1]
    rw [hL, hv2, b1, b2]
    generalize byteAt data 0 = b0
    generalize vb data 2 = b
    rcases (show vw data 2 = 7 ∨ vw data 2 = 8 by omega) with e | e <;>
      simp only [e, Nat.reducePow, Nat.reduceSub, Nat.zero_mul, Nat.add_zero] <;> lia

/-- **C1 (MQ round trip).** For every list of initial context states and every sequence of
`(context, decision)` pairs, decoding the reference encoder's output (T.800 Annex C encoder,
terminated by `FLUSH`) with the Annex C decoder, in the same contexts, returns exactly the
encoded decisions. No side condition is needed: out-of-range context numbers and
out-of-range state indices are handled identically (and totally) by both sides. -/
theorem roundTrip (inits : List Nat) (pairs : List (Nat × Bool)) :
    decodeAll (encodeAll inits pairs) inits (pairs.map (·.1)) = pairs.map (·.2) := by
  obtain ⟨i1, i2⟩ := initenc_inv
  have hs := (run_Q pairs initenc (initContexts inits) i1 i2).1
  exact dec_many _ hs pairs initenc (initContexts inits) (initdec _) i1 i2 rfl (corr_init _ hs)

end JPEG2000.Spec.MQRoundTrip
