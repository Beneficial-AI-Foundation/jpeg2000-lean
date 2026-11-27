import Spec.Tier2

/-!
# Tier-2 equivalence, layer (a): the bit reader reads the un-stuffed bit list
(Plan.md §4 C9, §5.1, §5.2 "Tier-2"; T.800 B.10.1)

Task 7.1b. The fast `Bytes.BitReader` (a loaded byte `buf` with `ct` unread bits, and the
next byte at `pos`) and the spec's `Spec.Tier2.unstuff` are linked by

  `rem b = bitsOf buf ct ++ unstuffAux (buf = 0xFF) (bytes of [pos, stop))`,

the bits the reader will still deliver. `bit_rem`: one `bit` read takes the head of
`rem b` (and fails exactly when `rem b` is empty); `bitsAux_rem`/`bits_rem`: a field read is
`Spec.Tier2.field` over `rem b`. For the end of a packet header, `HR p0 b` records where the
reader stands relative to its start `p0`; `align_rem` shows that the byte position after
`BitReader.align` is `p0 + alignedLength false B n`, `n` the number of bits read and `B` the
bytes from `p0`. This is the link that `Spec.TagTree` left tested only (progress.md 4.1).
-/

namespace JPEG2000.Spec.Tier2Equiv

open JPEG2000 JPEG2000.Bytes JPEG2000.Spec.Tier2

/-! ## Byte lists of buffers -/

/-- The bytes `[pos, stop)` of a buffer as a list. -/
def bytesFrom (data : ByteArray) (pos stop : Nat) : List UInt8 :=
  (data.data.toList.take stop).drop pos

/-- No bytes from `pos ≥ stop`. -/
theorem bytesFrom_of_le {d : ByteArray} {p s : Nat} (h : s ≤ p) : bytesFrom d p s = [] := by
  simp only [bytesFrom, List.drop_eq_nil_iff, List.length_take]; omega

/-- The first byte of a non-empty range. -/
theorem bytesFrom_cons {d : ByteArray} {p s : Nat} (h1 : p < s) (h2 : s ≤ d.size) :
    bytesFrom d p s = d.data[p]'(by have : d.size = d.data.size := rfl; omega) ::
      bytesFrom d (p + 1) s := by
  have hsz : d.size = d.data.size := rfl
  unfold bytesFrom
  have hl : p < (d.data.toList.take s).length := by
    simp only [List.length_take, Array.length_toList]; omega
  rw [List.drop_eq_getElem_cons hl]
  simp

/-- Dropping `n` bytes of the list advances the start. -/
theorem bytesFrom_add {d : ByteArray} (p n s : Nat) : bytesFrom d (p + n) s = (bytesFrom d p s).drop n := by
  simp only [bytesFrom, List.drop_drop]

/-- Length of a byte range list. -/
theorem length_bytesFrom {d : ByteArray} (p s : Nat) (h : s ≤ d.size) :
    (bytesFrom d p s).length = s - p := by
  have hsz : d.size = d.data.size := rfl
  simp only [bytesFrom, List.length_drop, List.length_take, Array.length_toList]
  omega

/-- The bytes of a whole buffer. -/
theorem bytesFrom_all (d : ByteArray) : bytesFrom d 0 d.size = d.data.toList := by
  have hsz : d.size = d.data.toList.length := by rw [Array.length_toList]; rfl
  simp only [bytesFrom, List.drop_zero]; rw [hsz, List.take_length]

/-! ## Results that follow the list -/

/-- A fast result over a bit reader and a spec result over a bit list correspond: both fail,
or both succeed with related values (`R`) and the list result's rest is `rem` of the
reader. -/
def Fol {α β σ : Type} (rem : σ → List Bool) (I : σ → Prop) (R : α → β → Prop) :
    Except Error (α × σ) → Except Error (β × List Bool) → Prop
  | .error _, .error _ => True
  | .ok (a, s), .ok (b, l) => R a b ∧ l = rem s ∧ I s
  | _, _ => False

/-! ## The bits a reader will deliver -/

/-- The bits `b` will still deliver: the `ct` unread bits of `buf`, then the un-stuffed
bytes `[pos, stop)` (the flag: `buf` was `0xFF`). -/
def rem (b : BitReader) : List Bool :=
  bitsOf b.buf.toNat b.ct.toNat ++ unstuffAux (b.buf == 0xFF) (bytesFrom b.data b.pos b.stop)

/-- A reader state reachable by reading: at most 8 pending bits of a byte value. -/
def Ok (b : BitReader) : Prop := b.ct.toNat ≤ 8 ∧ b.buf.toNat < 256

/-- `(v.toUInt32 == 0xFF) = (v == 0xFF)` for a byte. -/
theorem toUInt32_eq_FF (v : UInt8) : (v.toUInt32 == 0xFF) = (v == 0xFF) := by
  have : (v.toUInt32 = 0xFF) ↔ (v = 0xFF) := by
    constructor
    · intro h; apply UInt8.toNat_inj.mp; have := congrArg UInt32.toNat h; simp at this; simp [this]
    · intro h; subst h; rfl
  by_cases h : v = 0xFF
  · have h' := this.mpr h; rw [h']; subst h; decide
  · have h' : ¬ v.toUInt32 = 0xFF := fun e => h (this.mp e)
    simp only [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr h']

/-- The bit extracted by `BitReader.bit`. -/
theorem shift_and_one (buf ct : UInt32) (hc : ct.toNat < 32) :
    ((buf >>> ct) &&& 1) = if buf.toNat.testBit ct.toNat then 1 else 0 := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_and, UInt32.toNat_shiftRight, Nat.mod_eq_of_lt hc]
  have : (1 : UInt32).toNat = 1 := rfl
  rw [this, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (buf.toNat / 2 ^ ct.toNat) with h | h <;> simp [h]

/-- `bit` with pending bits. -/
theorem bit_ne (b : BitReader) (h0 : b.ct ≠ 0) :
    b.bit = .ok ((b.buf >>> (b.ct - 1)) &&& 1, { b with ct := b.ct - 1 }) := by
  simp [BitReader.bit, h0, bind, Except.bind, pure, Except.pure]

/-- `bit` loading a byte. -/
theorem bit_load (b : BitReader) (h0 : b.ct = 0) (hp : b.pos + 1 ≤ b.stop) :
    ∃ b', b.bit = .ok (((b.data.get b.pos (by have := b.stop_le; omega)).toUInt32 >>>
        ((if b.buf == 0xFF then (7 : UInt32) else 8) - 1)) &&& 1, b') ∧
      b'.buf = (b.data.get b.pos (by have := b.stop_le; omega)).toUInt32 ∧
      b'.ct = (if b.buf == 0xFF then (7 : UInt32) else 8) - 1 ∧ b'.pos = b.pos + 1 ∧
      b'.data = b.data ∧ b'.stop = b.stop := by
  simp only [BitReader.bit, h0, BitReader.load, hp, bind, Except.bind, pure, Except.pure]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `bit` at the end of the range. -/
theorem bit_end (b : BitReader) (h0 : b.ct = 0) (hp : ¬ b.pos + 1 ≤ b.stop) :
    ∃ e, b.bit = .error e := by
  simp only [BitReader.bit, h0, BitReader.load, hp, bind, Except.bind]
  exact ⟨_, rfl⟩

/-- `ByteArray.get` is the underlying array's element. -/
theorem get_eq_data (d : ByteArray) (p : Nat) (h : p < d.size) :
    d.get p h = d.data[p]'(by have : d.size = d.data.size := rfl; omega) := by
  cases d; rfl

/-- **One bit.** `bit` fails exactly when `rem b` is empty; otherwise it returns `0`/`1`
for the head of `rem b`, and `rem` of the new state is the tail. -/
theorem bit_rem (b : BitReader) (hb : Ok b) :
    match b.bit with
    | .error _ => rem b = []
    | .ok (x, b') => x = (if (rem b).head? = some true then 1 else 0) ∧
        rem b = (x != 0) :: rem b' ∧ Ok b' ∧ b'.data = b.data ∧ b'.stop = b.stop ∧
        b.pos ≤ b'.pos ∧ b'.pos ≤ b.pos + 1 := by
  obtain ⟨hct, hbuf⟩ := hb
  by_cases h0 : b.ct = 0
  · have hc0 : b.ct.toNat = 0 := by simp [h0]
    by_cases hp : b.pos + 1 ≤ b.stop
    · obtain ⟨b', hbit, hbuf', hct', hpos', hd', hs'⟩ := bit_load b h0 hp
      rw [hbit]
      have hcons := bytesFrom_cons (d := b.data) (p := b.pos) (s := b.stop) (by omega) b.stop_le
      rw [← get_eq_data b.data b.pos (by have := b.stop_le; omega)] at hcons
      generalize b.data.get b.pos (by have := b.stop_le; omega) = v at hcons hbuf' ⊢
      generalize hff : (b.buf == 0xFF) = ff at hct' ⊢
      have hw : (if ff = true then (7 : UInt32) else 8) - 1 = if ff = true then 6 else 7 := by
        cases ff <;> rfl
      have hwn : (if ff = true then (6 : UInt32) else 7).toNat = if ff = true then 6 else 7 := by
        cases ff <;> rfl
      rw [hw] at hct' ⊢
      have hsh := shift_and_one v.toUInt32 (if ff = true then 6 else 7) (by rw [hwn]; split <;> omega)
      rw [hwn, UInt8.toNat_toUInt32] at hsh
      rw [hsh]
      have hrem : rem b = v.toNat.testBit (if ff = true then 6 else 7) ::
          (bitsOf v.toNat (if ff = true then 6 else 7) ++
            unstuffAux (v == 0xFF) (bytesFrom b.data (b.pos + 1) b.stop)) := by
        simp only [rem, hc0, bitsOf, List.nil_append, hcons, unstuffAux, hff]
        cases ff <;> rfl
      have hrem' : rem b' = bitsOf v.toNat (if ff = true then 6 else 7) ++
            unstuffAux (v == 0xFF) (bytesFrom b.data (b.pos + 1) b.stop) := by
        simp only [rem, hbuf', hct', hwn, UInt8.toNat_toUInt32, toUInt32_eq_FF, hpos', hd', hs']
      refine ⟨?_, ?_, ⟨?_, ?_⟩, hd', hs', by omega, by omega⟩
      · rw [hrem]; cases v.toNat.testBit (if ff = true then 6 else 7) <;> simp
      · rw [hrem, hrem']; cases v.toNat.testBit (if ff = true then 6 else 7) <;> simp
      · rw [hct', hwn]; split <;> omega
      · rw [hbuf']; simpa using v.toNat_lt
    · obtain ⟨e, he⟩ := bit_end b h0 hp
      rw [he]
      simp only [rem, hc0, bitsOf, List.nil_append]
      rw [bytesFrom_of_le (by omega)]; rfl
  · rw [bit_ne b h0]
    have hpos : 0 < b.ct.toNat := by
      rcases Nat.eq_zero_or_pos b.ct.toNat with h | h
      · exact absurd (UInt32.toNat_inj.mp (by simp [h])) h0
      · exact h
    obtain ⟨c, hc⟩ : ∃ c, b.ct.toNat = c + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
    have hsub : (b.ct - 1).toNat = c := by
      rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp; omega)]; simp; omega
    have hsh := shift_and_one b.buf (b.ct - 1) (by omega)
    rw [hsub] at hsh
    rw [hsh]
    have hrem : rem b = b.buf.toNat.testBit c :: (bitsOf b.buf.toNat c ++
        unstuffAux (b.buf == 0xFF) (bytesFrom b.data b.pos b.stop)) := by
      simp only [rem, hc, bitsOf, List.cons_append]
    refine ⟨?_, ?_, ⟨?_, hbuf⟩, rfl, rfl, by simp, by simp⟩
    · rw [hrem]; cases b.buf.toNat.testBit c <;> simp
    · rw [hrem]; simp only [rem, hsub]; cases b.buf.toNat.testBit c <;> simp
    · simp only [hsub]; omega

/-- **One bit as a `Bool`** (`TagTree.bitNext`, the bit source of the fast tag-tree decoder):
it follows `Spec.TagTree.listNext` over `rem`. -/
theorem bitNext_rem (b : BitReader) (hb : Ok b) :
    match JPEG2000.TagTree.bitNext b with
    | .error _ => rem b = []
    | .ok (x, b') => rem b = x :: rem b' ∧ Ok b' ∧ b'.data = b.data ∧ b'.stop = b.stop ∧
        b.pos ≤ b'.pos ∧ b'.pos ≤ b.pos + 1 := by
  have h := bit_rem b hb
  unfold JPEG2000.TagTree.bitNext
  revert h
  cases b.bit with
  | error e => exact id
  | ok r =>
    obtain ⟨x, b'⟩ := r
    intro ⟨_, h2, h3, h4, h5, h6, h7⟩
    exact ⟨h2, h3, h4, h5, h6, h7⟩

/-! ## Invariants that follow the bit list -/

/-- An invariant `I` of reader states **simulates** the bit list `rem`: from a state in `I`,
`bit` fails exactly when `rem` is empty, and otherwise reads the head of `rem` (as `0`/`1`)
into a state in `I` whose `rem` is the tail. -/
def BitSim (I : BitReader → Prop) : Prop :=
  ∀ b, I b → match b.bit with
    | .error _ => rem b = []
    | .ok (x, b') => x = (if (rem b).head? = some true then 1 else 0) ∧
        rem b = (x != 0) :: rem b' ∧ I b'

/-- `bitNext` under a simulating invariant. -/
theorem bitNext_sim {I : BitReader → Prop} (hI : BitSim I) (b : BitReader) (hb : I b) :
    Fol rem I (· = ·) (JPEG2000.TagTree.bitNext b) (Spec.TagTree.listNext (rem b)) := by
  have h := hI b hb
  unfold JPEG2000.TagTree.bitNext
  revert h
  cases b.bit with
  | error e => intro h; rw [h]; trivial
  | ok r =>
    obtain ⟨x, b'⟩ := r
    intro ⟨_, h2, h3⟩
    rw [h2]; exact ⟨rfl, rfl, h3⟩

/-- `bitNext` is `readBit` of the packet decoder. -/
theorem readBit_sim {I : BitReader → Prop} (hI : BitSim I) (b : BitReader) (hb : I b) :
    Fol rem I (· = ·) (JPEG2000.Tier2.Packet.readBit b) (Spec.Tier2.bit (rem b)) :=
  bitNext_sim hI b hb

/-- Appending a bit to a field value. -/
theorem shl_or (acc x : UInt32) (h1 : acc.toNat * 2 < 2 ^ 32) (h2 : x.toNat < 2) :
    ((acc <<< 1) ||| x).toNat = 2 * acc.toNat + x.toNat := by
  rw [UInt32.toNat_or, UInt32.toNat_shiftLeft]
  have : (1 : UInt32).toNat % 32 = 1 := rfl
  rw [this, Nat.shiftLeft_eq, Nat.pow_one, Nat.mod_eq_of_lt h1]
  rw [← Nat.pow_one 2, ← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt (by simpa using h2)]
  rw [Nat.shiftLeft_eq]; simp; omega

/-- **A field of `k` bits**: `bitsAux` follows `Spec.Tier2.bitsVal` (no overflow while the
value fits 32 bits). -/
theorem bitsAux_sim {I : BitReader → Prop} (hI : BitSim I) :
    ∀ (k : Nat) (b : BitReader) (acc : UInt32) (j : Nat), I b → acc.toNat < 2 ^ j → j + k ≤ 32 →
      Fol rem I (fun (v : UInt32) (n : Nat) => v.toNat = n) (b.bitsAux acc k)
        (bitsVal acc.toNat k (rem b))
  | 0, b, acc, _, hb, _, _ => by simp only [BitReader.bitsAux, bitsVal]; exact ⟨rfl, rfl, hb⟩
  | k + 1, b, acc, j, hb, hacc, hjk => by
    have h := hI b hb
    simp only [BitReader.bitsAux, bitsVal]
    revert h
    cases b.bit with
    | error e => intro h; rw [h]; trivial
    | ok r =>
      obtain ⟨x, b'⟩ := r
      intro ⟨h1, h2, h3⟩
      rw [h2]
      have hx : x.toNat = if (x != 0) = true then 1 else 0 := by
        rw [h1]; split <;> simp
      have hx2 : x.toNat < 2 := by rw [hx]; split <;> omega
      have hj : 2 ^ j * 2 ≤ 2 ^ 32 := by
        rw [← Nat.pow_succ]; exact Nat.pow_le_pow_right (by omega) (by omega)
      have hacc2 : acc.toNat * 2 < 2 ^ 32 := by omega
      have hv := shl_or acc x hacc2 hx2
      show Fol rem I _ (b'.bitsAux ((acc <<< 1) ||| x) k)
        (bitsVal (2 * acc.toNat + if (x != 0) = true then 1 else 0) k (rem b'))
      rw [← hx, ← hv]
      apply bitsAux_sim hI k b' _ (j + 1) h3 _ (by omega)
      rw [hv, Nat.pow_succ]; omega

/-- **A field of `n ≤ 32` bits** (`BitReader.bits`) follows `Spec.Tier2.field`. -/
theorem bits_sim {I : BitReader → Prop} (hI : BitSim I) (b : BitReader) (n : Nat) (hb : I b) :
    Fol rem I (fun (v : UInt32) (m : Nat) => v.toNat = m) (b.bits n) (field n (rem b)) := by
  unfold BitReader.bits field
  by_cases hn : n ≤ 32
  · simp only [hn, ↓reduceIte]
    have := bitsAux_sim hI n b 0 0 hb (by simp) (by omega)
    simpa using this
  · simp only [hn, ↓reduceIte]; trivial

/-! ## The end of a packet header -/

/-- `bitsOf v n` has `n` bits. -/
theorem length_bitsOf (v : Nat) : ∀ n, (bitsOf v n).length = n
  | 0 => rfl
  | n + 1 => by simp [bitsOf, length_bitsOf v n]

/-- Width (7 or 8 bits) of byte `j - 1` of `B` read with initial flag `ff`. -/
def wdAt : Bool → List UInt8 → Nat → Nat
  | _, _, 0 => 8
  | ff, _, 1 => if ff then 7 else 8
  | _, [], _ + 2 => 8
  | _, b :: B, j + 2 => wdAt (b == 0xFF) B (j + 1)

/-- The bits of the first `j` bytes include the whole last one. -/
theorem wdAt_le : ∀ (B : List UInt8) (ff : Bool) (j : Nat), 1 ≤ j → j ≤ B.length →
    wdAt ff B j ≤ (unstuffAux ff (B.take j)).length
  | [], _, j, h1, h2 => by simp at h2; omega
  | b :: B, ff, 1, _, _ => by
    simp only [wdAt, List.take_succ_cons, List.take_zero, unstuffAux, List.length_append,
      length_bitsOf]; omega
  | b :: B, ff, j + 2, _, h2 => by
    have ih := wdAt_le B (b == 0xFF) (j + 1) (by omega) (by simp at h2; omega)
    simp only [wdAt, List.take_succ_cons, unstuffAux, List.length_append, length_bitsOf] at ih ⊢
    omega

/-- **Alignment count.** Reading all but `ct` of the bits of the first `j` bytes (`ct` below
the width of byte `j − 1`), the header occupies `j` bytes, plus one after an `0xFF`. -/
theorem align_count : ∀ (B : List UInt8) (ff : Bool) (j ct : Nat), 1 ≤ j → j ≤ B.length →
    ct < wdAt ff B j →
    alignedLength ff B ((unstuffAux ff (B.take j)).length - ct) =
      if B[j - 1]? = some 0xFF then (if j < B.length then some (j + 1) else none) else some j
  | [], _, j, _, h1, h2, _ => by simp at h2; omega
  | b :: B, ff, 1, ct, _, _, hct => by
    simp only [wdAt] at hct
    simp only [List.take_succ_cons, List.take_zero, unstuffAux, List.length_append, length_bitsOf,
      List.length_nil, Nat.add_zero]
    obtain ⟨n, hn⟩ : ∃ n, (if ff = true then 7 else 8) - ct = n + 1 :=
      ⟨_, (Nat.succ_pred_eq_of_pos (by omega)).symm⟩
    rw [hn]
    simp only [alignedLength, show n + 1 ≤ (if ff = true then 7 else 8) by omega, ↓reduceIte,
      List.getElem?_cons_zero, Nat.sub_self, List.length_cons]
    by_cases hb : b = 0xFF
    · subst hb; cases B <;> simp
    · simp [hb]
  | b :: B, ff, j + 2, ct, _, h2, hct => by
    simp only [wdAt] at hct
    have hl := wdAt_le B (b == 0xFF) (j + 1) (by omega) (by simp at h2; omega)
    have ih := align_count B (b == 0xFF) (j + 1) ct (by omega) (by simp at h2; omega) hct
    simp only [List.take_succ_cons, unstuffAux, List.length_append, length_bitsOf]
    obtain ⟨n, hn⟩ : ∃ n, (if ff = true then 7 else 8) +
        (unstuffAux (b == 0xFF) (List.take (j + 1) B)).length - ct = n + 1 :=
      ⟨_, (Nat.succ_pred_eq_of_pos (by omega)).symm⟩
    rw [hn]
    have hgt : ¬ n + 1 ≤ (if ff = true then 7 else 8) := by omega
    have he : n + 1 - (if ff = true then 7 else 8) =
        (unstuffAux (b == 0xFF) (List.take (j + 1) B)).length - ct := by omega
    simp only [alignedLength, hgt, ↓reduceIte, he, ih]
    have e1 : (b :: B)[j + 2 - 1]? = B[j]? := by simp
    rw [e1, show j + 1 - 1 = j by omega]
    by_cases hB : B[j]? = some 0xFF
    · simp only [hB, ↓reduceIte, List.length_cons]
      by_cases hj : j + 1 < B.length
      · simp [hj, show j + 2 < B.length + 1 by omega]
      · simp [hj, show ¬ j + 2 < B.length + 1 by omega]
    · simp [hB]

/-- The flag after reading a byte list (was its last byte `0xFF`). -/
def flagAfter : Bool → List UInt8 → Bool
  | ff, [] => ff
  | _, b :: bs => flagAfter (b == 0xFF) bs

/-- Un-stuffing a concatenation. -/
theorem unstuffAux_append : ∀ (ff : Bool) (l1 l2 : List UInt8),
    unstuffAux ff (l1 ++ l2) = unstuffAux ff l1 ++ unstuffAux (flagAfter ff l1) l2
  | _, [], _ => rfl
  | ff, b :: l1, l2 => by
    simp only [List.cons_append, unstuffAux, flagAfter, unstuffAux_append (b == 0xFF) l1 l2,
      List.append_assoc]

/-- The flag after `j ≥ 1` bytes: byte `j − 1` was `0xFF`. -/
theorem flagAfter_take : ∀ (B : List UInt8) (ff : Bool) (j : Nat), 1 ≤ j → j ≤ B.length →
    flagAfter ff (B.take j) = (B[j - 1]? == some 0xFF)
  | [], _, j, _, h => by simp at h; omega
  | b :: B, ff, 1, _, _ => by
    simp only [List.take_succ_cons, List.take_zero, flagAfter, Nat.sub_self, List.getElem?_cons_zero]
    by_cases hb : b = 0xFF <;> simp [hb]
  | b :: B, ff, j + 2, _, h => by
    simp only [List.take_succ_cons, flagAfter]
    rw [flagAfter_take B (b == 0xFF) (j + 1) (by omega) (by simp at h; omega)]
    simp

/-- The width of byte `j − 1 ≥ 1`: 7 after an `0xFF`, else 8. -/
theorem wdAt_eq : ∀ (B : List UInt8) (ff : Bool) (j : Nat), 2 ≤ j →
    wdAt ff B j = if B[j - 2]? = some 0xFF then 7 else 8
  | [], _, j + 2, _ => by simp [wdAt]
  | b :: B, ff, 2, _ => by
    simp only [wdAt, Nat.sub_self, List.getElem?_cons_zero]
    by_cases hb : b = 0xFF <;> simp [hb, wdAt]
  | b :: B, ff, j + 3, _ => by
    simp only [wdAt]
    rw [wdAt_eq B (b == 0xFF) (j + 2) (by omega)]
    simp

/-- `getD` in range. -/
theorem getD_of_lt (a : Array UInt8) (i : Nat) (h : i < a.size) : a.getD i 0 = a[i] := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h]; rfl

/-- Indexing the byte list of a range. -/
theorem getElem?_bytesFrom {D : ByteArray} {p S i : Nat} (hS : S ≤ D.size) (hi : p + i < S) :
    (bytesFrom D p S)[i]? = some (D.data.getD (p + i) 0) := by
  have hsz : D.size = D.data.size := rfl
  simp only [bytesFrom, List.getElem?_drop, List.getElem?_take, show p + i < S from hi, ↓reduceIte,
    Array.getElem?_toList]
  rw [getD_of_lt _ _ (by omega)]; exact Array.getElem?_eq_getElem _

/-- Where a header reader stands relative to its start `p0`: at the start nothing is
loaded; afterwards `buf` is the byte before `pos` and `ct` is below its width (7 after an
`0xFF` byte read in this header, else 8). -/
def HR (p0 : Nat) (b : BitReader) : Prop :=
  p0 ≤ b.pos ∧ (b.pos = p0 → b.buf = 0 ∧ b.ct = 0) ∧
  (p0 < b.pos → b.buf = (b.data.data.getD (b.pos - 1) 0).toUInt32 ∧
     b.ct.toNat < (if p0 + 1 < b.pos ∧ b.data.data.getD (b.pos - 2) 0 = 0xFF then 7 else 8))

/-- The invariant of a packet-header reader started at `p0` over `data[·, S)`. -/
def Inv (p0 : Nat) (D : ByteArray) (S : Nat) (b : BitReader) : Prop :=
  Ok b ∧ HR p0 b ∧ b.data = D ∧ b.stop = S

/-- `bit` keeps `HR`. -/
theorem bit_hr (p0 : Nat) (b : BitReader) (_hb : Ok b) (hr : HR p0 b) {x : UInt32} {b' : BitReader}
    (h : b.bit = .ok (x, b')) : HR p0 b' := by
  obtain ⟨hp0, hstart, hlater⟩ := hr
  by_cases h0 : b.ct = 0
  · by_cases hp : b.pos + 1 ≤ b.stop
    · obtain ⟨b'', hbit, hbuf', hct', hpos', hd', hs'⟩ := bit_load b h0 hp
      rw [hbit] at h; cases h
      refine ⟨by omega, fun e => by omega, fun _ => ⟨?_, ?_⟩⟩
      · rw [hbuf', hpos', hd', get_eq_data b.data b.pos (by have := b.stop_le; omega)]
        rw [show b.pos + 1 - 1 = b.pos by omega,
          getD_of_lt _ _ (by have := b.stop_le; have : b.data.size = b.data.data.size := rfl; omega)]
      · rw [hct', hpos', hd']
        by_cases he : b.pos = p0
        · obtain ⟨hb0, -⟩ := hstart he
          rw [hb0]; simp only [show ¬ (p0 + 1 < b.pos + 1) by omega, false_and, ↓reduceIte]
          decide
        · obtain ⟨hb1, -⟩ := hlater (by omega)
          rw [hb1, toUInt32_eq_FF]
          simp only [show p0 + 1 < b.pos + 1 by omega, true_and, show b.pos + 1 - 2 = b.pos - 1 by omega]
          split <;> split <;> first | decide | (exfalso; simp_all)
    · obtain ⟨e, he⟩ := bit_end b h0 hp; rw [he] at h; cases h
  · rw [bit_ne b h0] at h; cases h
    refine ⟨hp0, fun e => absurd (hstart e).2 h0, fun hlt => ?_⟩
    obtain ⟨h1, h2⟩ := hlater hlt
    refine ⟨h1, ?_⟩
    have : (b.ct - 1).toNat ≤ b.ct.toNat := by
      rw [UInt32.toNat_sub_of_le _ _ (by
        rw [UInt32.le_iff_toNat_le]
        have : b.ct.toNat ≠ 0 := fun e => h0 (UInt32.toNat_inj.mp (by simp [e]))
        show 1 ≤ b.ct.toNat; omega)]
      show b.ct.toNat - 1 ≤ b.ct.toNat; omega
    exact Nat.lt_of_le_of_lt this h2

/-- The header-reader invariant simulates the bit list. -/
theorem inv_sim (p0 : Nat) (D : ByteArray) (S : Nat) : BitSim (Inv p0 D S) := by
  intro b ⟨hok, hr, hd, hs⟩
  have h := bit_rem b hok
  have hh : ∀ x b', b.bit = .ok (x, b') → HR p0 b' := fun x b' e => bit_hr p0 b hok hr e
  revert h hh
  cases b.bit with
  | error e => intro h _; exact h
  | ok r =>
    obtain ⟨x, b'⟩ := r
    intro ⟨h1, h2, h3, h4, h5, _, _⟩ hh
    exact ⟨h1, h2, h3, hh x b' rfl, h4.trans hd, h5.trans hs⟩

/-- **The end of a packet header** (B.10.1). For a header reader started at `p0`, `align`
fails exactly when `alignedLength` does, and otherwise stops at
`p0 + alignedLength false B n`, `B` the bytes from `p0` and `n` the number of bits read
(`|unstuff B| − |rem b|`). -/
theorem align_sim {p0 S : Nat} {D : ByteArray} {b : BitReader} (hb : Inv p0 D S b) :
    match b.align with
    | .error _ => alignedLength false (bytesFrom D p0 S)
        ((unstuff (bytesFrom D p0 S)).length - (rem b).length) = none
    | .ok b' => alignedLength false (bytesFrom D p0 S)
        ((unstuff (bytesFrom D p0 S)).length - (rem b).length) = some (b'.pos - p0) ∧
        b'.data = D ∧ b'.stop = S ∧ p0 ≤ b'.pos := by
  obtain ⟨hok, ⟨hp0, hstart, hlater⟩, hd, hs⟩ := hb
  subst hd hs
  have hsz := b.stop_le
  have hpos := b.pos_le
  have hdrop : bytesFrom b.data b.pos b.stop = (bytesFrom b.data p0 b.stop).drop (b.pos - p0) := by
    rw [← bytesFrom_add]; congr 1; omega
  have hlen : (bytesFrom b.data p0 b.stop).length = b.stop - p0 := length_bytesFrom _ _ hsz
  generalize hB : bytesFrom b.data p0 b.stop = B at hdrop hlen ⊢
  by_cases hj : b.pos = p0
  · obtain ⟨hb0, hc0⟩ := hstart hj
    have hrem : rem b = unstuff B := by
      simp only [rem, hb0, hc0]; rw [hj, hB]; rfl
    rw [hrem, Nat.sub_self]
    unfold BitReader.align
    simp only [hb0, show ((0 : UInt32) == 0xFF) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    exact ⟨by simp [alignedLength, hj], trivial, trivial, by simp [hj]⟩
  · have hj1 : p0 < b.pos := by omega
    obtain ⟨hbuf, hct⟩ := hlater hj1
    have hlast : B[b.pos - p0 - 1]? = some (b.data.data.getD (b.pos - 1) 0) := by
      rw [← hB, getElem?_bytesFrom hsz (by omega), show p0 + (b.pos - p0 - 1) = b.pos - 1 by omega]
    have hflag : flagAfter false (B.take (b.pos - p0)) = (b.buf == 0xFF) := by
      rw [flagAfter_take B false _ (by omega) (by omega), hlast, hbuf, toUInt32_eq_FF]
      by_cases h : b.data.data.getD (b.pos - 1) 0 = 0xFF <;> simp [h]
    have hsplit : unstuff B = unstuffAux false (B.take (b.pos - p0)) ++
        unstuffAux (b.buf == 0xFF) (B.drop (b.pos - p0)) := by
      rw [← hflag, ← unstuffAux_append, List.take_append_drop]; rfl
    have hwd : b.ct.toNat < wdAt false B (b.pos - p0) := by
      rcases Nat.lt_or_ge (b.pos - p0) 2 with h2 | h2
      · have : b.pos - p0 = 1 := by omega
        rw [this]; simp only [wdAt, Bool.false_eq_true, ↓reduceIte]
        have := hct; split at this <;> omega
      · rw [wdAt_eq B false _ h2]
        have h2' : B[b.pos - p0 - 2]? = some (b.data.data.getD (b.pos - 2) 0) := by
          rw [← hB, getElem?_bytesFrom hsz (by omega), show p0 + (b.pos - p0 - 2) = b.pos - 2 by omega]
        rw [h2']
        simp only [show p0 + 1 < b.pos by omega, true_and] at hct
        by_cases hf : b.data.data.getD (b.pos - 2) 0 = 0xFF <;> simp_all
    have hle := wdAt_le B false (b.pos - p0) (by omega) (by omega)
    have hcount : (unstuff B).length - (rem b).length =
        (unstuffAux false (B.take (b.pos - p0))).length - b.ct.toNat := by
      rw [hsplit]; simp only [rem, hdrop, List.length_append, length_bitsOf]; omega
    rw [hcount, align_count B false _ _ (by omega) (by omega) hwd, hlast]
    have hff : (b.buf == 0xFF) = (b.data.data.getD (b.pos - 1) 0 == 0xFF) := by
      rw [hbuf, toUInt32_eq_FF]
    unfold BitReader.align
    generalize b.data.data.getD (b.pos - 1) 0 = v at hff
    by_cases hf : v = 0xFF
    · have hbf : (b.buf == 0xFF) = true := by rw [hff, hf]; rfl
      simp only [hbf, ↓reduceIte, hf]
      by_cases hp : b.pos + 1 ≤ b.stop
      · simp only [hp, ↓reduceDIte, show b.pos - p0 < B.length by omega, ↓reduceIte]
        refine ⟨?_, trivial, trivial, ?_⟩
        · show some (b.pos - p0 + 1) = some (b.pos + 1 - p0); congr 1; omega
        · show p0 ≤ b.pos + 1; omega
      · simp only [hp, ↓reduceDIte, show ¬ b.pos - p0 < B.length by omega, ↓reduceIte]
    · have hbf : (b.buf == 0xFF) = false := by rw [hff]; simp [hf]
      have : ¬ (some v = some (0xFF : UInt8)) := by simp [hf]
      simp only [hbf, Bool.false_eq_true, ↓reduceIte, this]
      exact ⟨by first | trivial | rfl, trivial, trivial, by omega⟩

/-- A fresh header reader satisfies the invariant, and its bits are the un-stuffed bytes. -/
theorem ofReader_inv (r : Reader) :
    Inv r.pos r.data r.stop (BitReader.ofReader r) ∧
      rem (BitReader.ofReader r) = unstuff (bytesFrom r.data r.pos r.stop) := by
  refine ⟨⟨⟨show (0 : UInt32).toNat ≤ 8 by decide, show (0 : UInt32).toNat < 256 by decide⟩, ⟨Nat.le_refl _, fun _ => ⟨rfl, rfl⟩, fun h => absurd h (Nat.lt_irrefl _)⟩,
    rfl, rfl⟩, rfl⟩

end JPEG2000.Spec.Tier2Equiv
