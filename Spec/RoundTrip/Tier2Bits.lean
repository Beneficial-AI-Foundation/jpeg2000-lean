import Encode.Tier2
import Spec.Tier2

/-!
# C10, layer 2 (part): packet-header bits — the writer against the spec reader

Plan.md §4 (C10), §5.3 (reference encoder). Task 7.3, layer 2, first part. T.800 B.10.1
(bit stuffing), B.10.6 (Table B.4, number of coding passes), B.10.7.1 (the `Lblock`
comma code), B.10.7.2 (length fields).

* **B.10.1.** `WInv w B`: the reference encoder's `Encode.Tier2.BitWriter` `w` holds the
  header bits `B` — its complete bytes un-stuffed by the spec (`Spec.Tier2.unstuff`), then the
  bits of the byte being filled; `winv_init`, `winv_bit`, `winv_bits`. `finish_spec`: the
  finished header bytes followed by any bytes `T` un-stuff to `B`, some padding, then the
  bits of `T`, and the spec's `alignedLength` finds exactly the header's bytes after the bits
  of `B` (also when the last byte is `0xFF` and the stuffed `0x00` follows).
* **Header fields.** `field_natBits` (a length field of `n ≤ 32` bits), `numPasses_passBits`
  (Table B.4, `1 ≤ n ≤ 164`), `commaCode_replicate` (the `Lblock` increment).

The tag-tree fields are C4 (`Spec.TagTree.decode_encode`). The packet-level composition
(`blocksHeader`/`bandsHeader`/`readBody` against `Encode.Tier2.encodePacket`) is the next
step of layer 2.
-/

namespace JPEG2000.Spec.RoundTrip

open JPEG2000
open JPEG2000.Spec.Tier2 (bitsOf unstuffAux unstuff alignedLength)
open JPEG2000.Encode.Tier2 (BitWriter)

/-- Whether the byte after the list `l` (read with incoming flag `ff`) carries only 7 bits. -/
def lastFF (ff : Bool) (l : List UInt8) : Bool :=
  match l.getLast? with
  | none => ff
  | some x => x == 0xFF

/-- `bitsOf v n` has `n` bits. -/
theorem length_bitsOf (v n : Nat) : (bitsOf v n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [bitsOf, ih]

/-- Appending bit `b` below `c`: the bits of `2c + b` are those of `c`, then `b`. -/
theorem bitsOf_double (c : Nat) (b : Bool) :
    ∀ n, bitsOf (2 * c + (if b then 1 else 0)) (n + 1) = bitsOf c n ++ [b]
  | 0 => by cases b <;> simp [bitsOf, Nat.testBit_zero] <;> omega
  | n + 1 => by
    rw [bitsOf, bitsOf_double c b n, bitsOf, Nat.testBit_succ]
    have : (2 * c + (if b then 1 else 0)) / 2 = c := by cases b <;> simp <;> omega
    rw [this]; rfl

/-- The bits of `0` are zeros. -/
theorem bitsOf_zero (n : Nat) : bitsOf 0 n = List.replicate n false := by
  induction n with
  | zero => rfl
  | succ n ih => simp [bitsOf, ih, List.replicate_succ]

/-- Un-stuffing a concatenation: the second part starts with the flag of the last byte of the first. -/
theorem unstuffAux_append (ff : Bool) (l t : List UInt8) :
    unstuffAux ff (l ++ t) = unstuffAux ff l ++ unstuffAux (lastFF ff l) t := by
  induction l generalizing ff with
  | nil => rfl
  | cons b l ih =>
    simp only [List.cons_append, unstuffAux, ih, List.append_assoc]
    congr 2
    cases l with
    | nil => simp [lastFF]
    | cons c l =>
      simp only [lastFF]
      cases h : (c :: l).getLast? with
      | none => simp at h
      | some x =>
        have h' : (b :: c :: l).getLast? = some x := by
          rw [List.getLast?_cons, h]; rfl
        rw [h']


/-- The flag after a list ending in `x`. -/
theorem lastFF_snoc (ff : Bool) (l : List UInt8) (x : UInt8) : lastFF ff (l ++ [x]) = (x == 0xFF) := by
  simp [lastFF]

/-- Un-stuffing one more byte. -/
theorem unstuffAux_snoc (ff : Bool) (l : List UInt8) (x : UInt8) :
    unstuffAux ff (l ++ [x]) = unstuffAux ff l ++ bitsOf x.toNat (if lastFF ff l then 7 else 8) := by
  rw [unstuffAux_append]; simp [unstuffAux]

/-- The bit writer `w` holds the header bits `B`: the complete bytes (read back with
B.10.1 un-stuffing) followed by the bits of the byte being filled. -/
def WInv (w : BitWriter) (B : List Bool) : Prop :=
  unstuff w.out.toList ++ bitsOf w.cur w.cnt = B ∧ w.cnt < w.cap ∧ w.cur < 2 ^ w.cnt ∧
    w.cap = (if lastFF false w.out.toList then 7 else 8)

/-- The empty writer holds no bits. -/
theorem winv_init : WInv {} [] := by
  refine ⟨rfl, by decide, by decide, rfl⟩

/-- Writing one bit appends it (B.10.1). -/
theorem winv_bit {w : BitWriter} {B : List Bool} (h : WInv w B) (b : Bool) :
    WInv (w.bit b) (B ++ [b]) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hcap : w.cap ≤ 8 := by rw [h4]; split <;> omega
  have hlt : w.cur * 2 + (if b then 1 else 0) < 2 ^ (w.cnt + 1) := by
    rw [Nat.pow_succ]; cases b <;> simp <;> omega
  have hbits : bitsOf (w.cur * 2 + (if b then 1 else 0)) (w.cnt + 1) = bitsOf w.cur w.cnt ++ [b] := by
    rw [Nat.mul_comm]; exact bitsOf_double _ _ _
  unfold BitWriter.bit
  simp only
  split
  · rename_i hge
    have hc : w.cnt + 1 = w.cap := by omega
    have h256 : w.cur * 2 + (if b then 1 else 0) < 256 := by
      have : 2 ^ (w.cnt + 1) ≤ 2 ^ 8 := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    have htn : (w.cur * 2 + (if b then 1 else 0)).toUInt8.toNat = w.cur * 2 + (if b then 1 else 0) := by
      simp; omega
    refine ⟨?_, by dsimp only; split <;> simp <;> split <;> decide, by simp, ?_⟩
    · simp only [Array.toList_push, unstuff, unstuffAux_snoc, htn, bitsOf]
      rw [show (if lastFF false w.out.toList = true then 7 else 8) = w.cnt + 1 by rw [hc, h4]]
      rw [hbits, ← h1]; simp; rfl
    · simp only [Array.toList_push, lastFF_snoc]
      congr 1
      apply propext
      constructor
      · intro hh; rw [hh]; rfl
      · intro hh
        have := congrArg UInt8.toNat (beq_iff_eq.1 hh)
        rw [htn] at this; exact this
  · rename_i hlt'
    refine ⟨?_, by simp only; omega, hlt, h4⟩
    simp only
    rw [hbits, ← h1, List.append_assoc]

/-- Writing a list of bits appends it (B.10.1). -/
theorem winv_bits {w : BitWriter} {B : List Bool} (h : WInv w B) :
    ∀ bs : List Bool, WInv (w.bits bs) (B ++ bs)
  | [] => by simpa [BitWriter.bits] using h
  | b :: bs => by
    have := winv_bits (winv_bit h b) bs
    simpa [BitWriter.bits, List.foldl_cons] using this


/-- Bit count of a byte list with its first byte split off. -/
theorem length_unstuffAux_cons (ff : Bool) (p : UInt8) (l : List UInt8) :
    (unstuffAux ff (p :: l)).length = (if ff then 7 else 8) + (unstuffAux (p == 0xFF) l).length := by
  simp [unstuffAux, length_bitsOf]

/-- The flag after `p :: l` is the flag after `l` read from `p`. -/
theorem lastFF_cons (ff : Bool) (p : UInt8) (l : List UInt8) :
    lastFF ff (p :: l) = lastFF (p == 0xFF) l := by
  cases l with
  | nil => rfl
  | cons c l =>
    simp only [lastFF]
    cases h : (c :: l).getLast? with
    | none => simp at h
    | some x =>
      have h' : (p :: c :: l).getLast? = some x := by rw [List.getLast?_cons, h]; rfl
      rw [h']

/-- `alignedLength` stops at the byte `x` holding the last header bit, plus the stuffed byte
after an `0xFF` (B.10.1). -/
theorem alignedLength_at (x : UInt8) (T : List UInt8) :
    ∀ (P : List UInt8) (ff : Bool) (j : Nat), 1 ≤ j → j ≤ (if lastFF ff P then 7 else 8) →
      alignedLength ff (P ++ x :: T) ((unstuffAux ff P).length + j) =
        if x == 0xFF then (if T.isEmpty then none else some (P.length + 2))
        else some (P.length + 1)
  | [], ff, j, h1, h2 => by
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    simp only [lastFF, List.getLast?_nil] at h2
    simp only [List.nil_append, unstuffAux, List.length_nil, Nat.zero_add, alignedLength]
    have hc : j' + 1 ≤ (if ff then 7 else 8) := h2
    simp only [hc, ↓reduceIte]
  | p :: P, ff, j, h1, h2 => by
    rw [lastFF_cons] at h2
    have ih := alignedLength_at x T P (p == 0xFF) j h1 h2
    rw [length_unstuffAux_cons]
    obtain ⟨m, hm⟩ : ∃ m, (if ff then 7 else 8) + (unstuffAux (p == 0xFF) P).length + j = m + 1 :=
      ⟨_, (Nat.succ_pred_eq_of_pos (by omega)).symm⟩
    rw [hm, List.cons_append, alignedLength]
    have hc : ¬ (m + 1 ≤ (if ff then 7 else 8)) := by omega
    simp only [hc, ↓reduceIte]
    rw [show m + 1 - (if ff then 7 else 8) = (unstuffAux (p == 0xFF) P).length + j by omega, ih]
    split
    · split <;> simp
    · simp

/-- Padding with `k` zero bits multiplies by `2^k`. -/
theorem bitsOf_shift (c n : Nat) : ∀ k, bitsOf (c * 2 ^ k) (n + k) = bitsOf c n ++ List.replicate k false
  | 0 => by simp
  | k + 1 => by
    have := bitsOf_double (c * 2 ^ k) false (n + k)
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at this
    rw [show c * 2 ^ (k + 1) = 2 * (c * 2 ^ k) by rw [Nat.pow_succ]; ac_rfl,
      show n + (k + 1) = n + k + 1 by omega, this, bitsOf_shift c n k, List.replicate_succ',
      List.append_assoc]


/-- Un-stuffing a concatenation whose first part does not end in `0xFF`. -/
theorem unstuff_append_noFF (H T : List UInt8) (h : lastFF false H = false) :
    unstuff (H ++ T) = unstuff H ++ unstuff T := by
  simp only [unstuff, unstuffAux_append, h]

/-- **B.10.1 round trip for a finished packet header.** If the writer holds the header bits
`B` (non-empty), then the finished header bytes, followed by any bytes `T`, un-stuff to `B`,
some padding bits, then the bits of `T`; and `alignedLength` finds exactly the header's
bytes after `B`. -/
theorem finish_spec {w : BitWriter} {B : List Bool} (h : WInv w B) (hB : B ≠ [])
    (T : List UInt8) :
    ∃ pad, unstuff (w.finish.toList ++ T) = B ++ pad ++ unstuff T ∧
      alignedLength false (w.finish.toList ++ T) B.length = some w.finish.toList.length := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hcap : w.cap ≤ 8 := by rw [h4]; split <;> omega
  unfold BitWriter.finish
  by_cases hc : w.cnt = 0
  · -- the last byte is complete
    simp only [hc, ↓reduceIte]
    rw [hc] at h1
    simp only [bitsOf, List.append_nil] at h1
    rcases List.eq_nil_or_concat w.out.toList with ho | ⟨P, x, ho⟩
    · rw [ho] at h1; subst h1; simp [unstuff, unstuffAux] at hB
    · simp only [List.concat_eq_append] at ho
      have hback : w.out.back? = some x := by
        rw [← Array.getLast?_toList, ho]; simp
      have hlen : B.length = (unstuffAux false P).length + (if lastFF false P then 7 else 8) := by
        rw [← h1, unstuff, ho, unstuffAux_snoc]; simp [length_bitsOf]
      by_cases hx : x = 0xFF
      · subst hx
        simp only [hback, ↓reduceIte, Array.toList_push, ho]
        refine ⟨List.replicate 7 false, ?_, ?_⟩
        · rw [unstuff_append_noFF _ _ (by simp [lastFF]), unstuff, unstuffAux_snoc, ← h1, unstuff, ho]
          simp [bitsOf_zero, lastFF]; rfl
        · rw [hlen, List.append_assoc, List.append_assoc, List.singleton_append,
            List.singleton_append, alignedLength_at _ _ P false _ (by split <;> omega) (Nat.le_refl _)]
          simp
      · have hx' : (w.out.back? = some 0xFF) = False := by rw [hback]; simp [hx]
        simp only [hx', ↓reduceIte, ho]
        refine ⟨[], ?_, ?_⟩
        · rw [unstuff_append_noFF _ _ (by simp [lastFF, hx]), ← h1, unstuff, ho]; simp; rfl
        · rw [hlen, List.append_assoc, List.singleton_append,
            alignedLength_at _ _ P false _ (by split <;> omega) (Nat.le_refl _)]
          simp [hx]
  · -- a partial last byte, padded with zeros
    simp only [hc, ↓reduceIte, Array.back?_push]
    have hk : w.cnt + (w.cap - w.cnt) = w.cap := by omega
    have hlt : w.cur * 2 ^ (w.cap - w.cnt) < 256 := by
      have : w.cur * 2 ^ (w.cap - w.cnt) < 2 ^ w.cnt * 2 ^ (w.cap - w.cnt) :=
        Nat.mul_lt_mul_of_pos_right h3 (Nat.two_pow_pos _)
      rw [← Nat.pow_add, hk] at this
      have : 2 ^ w.cap ≤ 2 ^ 8 := Nat.pow_le_pow_right (by decide) hcap
      omega
    have htn : (w.cur * 2 ^ (w.cap - w.cnt)).toUInt8.toNat = w.cur * 2 ^ (w.cap - w.cnt) := by
      simp; omega
    generalize hxd : (w.cur * 2 ^ (w.cap - w.cnt)).toUInt8 = x at htn
    have hbx : bitsOf x.toNat w.cap = bitsOf w.cur w.cnt ++ List.replicate (w.cap - w.cnt) false := by
      rw [htn, ← bitsOf_shift, hk]
    have hlen : B.length = (unstuffAux false w.out.toList).length + w.cnt := by
      rw [← h1]; simp [unstuff, length_bitsOf]
    have hu : unstuff (w.out.toList ++ [x]) =
        B ++ List.replicate (w.cap - w.cnt) false := by
      rw [unstuff, unstuffAux_snoc, ← h4, hbx, ← h1, unstuff, List.append_assoc]
    have hj : w.cnt ≤ (if lastFF false w.out.toList then 7 else 8) := by rw [← h4]; omega
    by_cases hx : x = 0xFF
    · subst hx
      simp only [↓reduceIte, Array.toList_push]
      refine ⟨List.replicate (w.cap - w.cnt) false ++ List.replicate 7 false, ?_, ?_⟩
      · rw [unstuff_append_noFF _ _ (by simp [lastFF]), unstuff, unstuffAux_append, ← unstuff, hu,
          lastFF_snoc]
        simp [unstuffAux, bitsOf_zero, List.append_assoc]
      · rw [hlen, List.append_assoc, List.append_assoc, List.singleton_append,
          List.singleton_append, alignedLength_at _ _ _ false _ (by omega) hj]
        simp
    · have hx' : (some x = some (0xFF : UInt8)) = False := by simp [hx]
      simp only [hx', ↓reduceIte, Array.toList_push]
      refine ⟨List.replicate (w.cap - w.cnt) false, ?_, ?_⟩
      · rw [unstuff_append_noFF _ _ (by simp [lastFF, hx]), hu]
      · rw [hlen, List.append_assoc, List.singleton_append,
          alignedLength_at _ _ _ false _ (by omega) hj]
        simp [hx]

end JPEG2000.Spec.RoundTrip

namespace JPEG2000.Spec.RoundTrip

open JPEG2000
open JPEG2000.Encode.Tier2 (natBits passBits)

/-- `natBits` peels off its most significant bit. -/
theorem natBits_succ (v n : Nat) : natBits v (n + 1) = (v / 2 ^ n % 2 == 1) :: natBits v n := by
  simp [natBits, List.range_succ]

/-- Reading `n` bits written by `natBits` appends their value. -/
theorem bitsVal_natBits (v : Nat) (rest : List Bool) :
    ∀ n acc, Spec.Tier2.bitsVal acc n (natBits v n ++ rest) = .ok (acc * 2 ^ n + v % 2 ^ n, rest)
  | 0, acc => by simp [Spec.Tier2.bitsVal, natBits, Nat.mod_one]
  | n + 1, acc => by
    rw [natBits_succ, List.cons_append]
    simp only [Spec.Tier2.bitsVal, Spec.Tier2.bit, Spec.TagTree.listNext, bind, Except.bind]
    rw [bitsVal_natBits v rest n]
    congr 2
    rw [Nat.mod_pow_succ, Nat.pow_succ]
    have : v / 2 ^ n % 2 = 0 ∨ v / 2 ^ n % 2 = 1 := by omega
    rcases this with h | h <;> simp [h, Nat.add_mul, Nat.mul_comm, Nat.mul_assoc] <;> omega

/-- A length field written with `natBits` reads back (B.10.7.2). -/
theorem field_natBits (v n : Nat) (rest : List Bool) (hn : n ≤ 32) (hv : v < 2 ^ n) :
    Spec.Tier2.field n (natBits v n ++ rest) = .ok (v, rest) := by
  simp only [Spec.Tier2.field, hn, ↓reduceIte, bitsVal_natBits, Nat.zero_mul, Nat.zero_add,
    Nat.mod_eq_of_lt hv]

/-- Table B.4: the pass-count codeword reads back. -/
theorem numPasses_passBits (n : Nat) (rest : List Bool) (h1 : 1 ≤ n) (h2 : n ≤ 164) :
    Spec.Tier2.numPasses (passBits n ++ rest) = .ok (n, rest) := by
  unfold passBits
  by_cases c1 : n ≤ 1
  · have : n = 1 := by omega
    subst this
    simp [Spec.Tier2.numPasses, Spec.Tier2.bit, Spec.TagTree.listNext, bind, Except.bind, pure,
      Except.pure]
  by_cases c2 : n = 2
  · subst c2
    simp [Spec.Tier2.numPasses, Spec.Tier2.bit, Spec.TagTree.listNext, bind, Except.bind, pure,
      Except.pure]
  by_cases c3 : n ≤ 5
  · simp only [c1, c2, c3, ↓reduceIte, List.cons_append, List.nil_append]
    simp only [Spec.Tier2.numPasses, Spec.Tier2.bit, Spec.TagTree.listNext, bind, Except.bind,
      pure, Except.pure, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [field_natBits _ _ _ (by decide) (by omega)]
    simp only
    have : (n - 3 != 3) = true := by simp; omega
    simp only [this, ↓reduceIte]
    congr; omega
  by_cases c4 : n ≤ 36
  · simp only [c1, c2, c3, c4, ↓reduceIte, List.cons_append, List.nil_append]
    simp only [Spec.Tier2.numPasses, Spec.Tier2.bit, Spec.TagTree.listNext, bind, Except.bind,
      pure, Except.pure, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [show true :: true :: (natBits (n - 6) 5 ++ rest) = natBits 3 2 ++ (natBits (n - 6) 5 ++ rest)
      by rfl, field_natBits _ _ _ (by decide) (by decide)]
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    rw [field_natBits _ _ _ (by decide) (by omega)]
    simp only
    have : (n - 6 != 31) = true := by simp; omega
    simp only [this, ↓reduceIte]
    congr; omega
  · simp only [c1, c2, c3, c4, ↓reduceIte, List.cons_append, List.nil_append, List.append_assoc]
    simp only [Spec.Tier2.numPasses, Spec.Tier2.bit, Spec.TagTree.listNext, bind, Except.bind,
      pure, Except.pure, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [show true :: true :: (natBits 31 5 ++ (natBits (min (n - 37) 127) 7 ++ rest)) =
      natBits 3 2 ++ (natBits 31 5 ++ (natBits (min (n - 37) 127) 7 ++ rest)) by rfl,
      field_natBits _ _ _ (by decide) (by decide)]
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    rw [field_natBits _ _ _ (by decide) (by decide)]
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    rw [field_natBits _ _ _ (by decide) (by omega)]
    simp only [Except.ok.injEq, Prod.mk.injEq, and_true]; omega

/-- B.10.7.1: the `Lblock` increment (comma code) reads back. -/
theorem commaCode_replicate (rest : List Bool) :
    ∀ k fuel acc, k < fuel →
      Spec.Tier2.commaCode fuel acc (List.replicate k true ++ false :: rest) = .ok (acc + k, rest)
  | 0, fuel + 1, acc, _ => by
    simp [Spec.Tier2.commaCode, Spec.Tier2.bit, Spec.TagTree.listNext, bind, Except.bind, pure,
      Except.pure]
  | k + 1, fuel + 1, acc, h => by
    simp only [Spec.Tier2.commaCode, List.replicate_succ, List.cons_append, Spec.Tier2.bit,
      Spec.TagTree.listNext, bind, Except.bind, ↓reduceIte]
    rw [commaCode_replicate rest k fuel (acc + 1) (by omega)]
    congr 2; omega

end JPEG2000.Spec.RoundTrip

