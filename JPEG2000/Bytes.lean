import JPEG2000.Error
import JPEG2000.Limits

/-!
# Byte reader, packet-header bit reader, `Int32` planes (Plan.md §3, §4 S1/S3, §5.4, §6)

Three low-level building blocks shared by every stage (task 1.1):

* `Reader` — a big-endian byte reader over a `ByteArray` with a current position and an
  end (`stop`), so that a marker segment or box body can be read as a sub-range
  (`Reader.take`). Every read is checked against `stop`; running past it returns
  `Error.truncated` with the reader's stage and the absolute byte offset of the failed read.
  T.800 A.1: marker segment parameters are big-endian; Annex I box lengths are big-endian
  32-bit, or 64-bit for XL boxes (`u64be`).
* `BitReader` — the MSB-first bit reader for packet headers with the bit-stuffing rule of
  T.800 B.10.1: after a `0xFF` byte, the next byte contributes only its 7 low bits (its MSB
  is a stuffed 0). `align` skips to the next byte boundary and, when the last byte read was
  `0xFF`, also consumes the stuffed byte that must follow it (B.10.1: the packet header never
  ends in `0xFF`; OpenJPEG `opj_bio_inalign`). Reading past the end is `Error.truncated`
  (OpenJPEG instead reads zeros).
* `Plane` — a `ByteArray`-backed plane of `Int32` cells (little-endian 4-byte cells), with the
  size invariant `data.size = 4 * (width * height)` carried in the structure, so `get`/`set`
  take an index proof and compile to unchecked `ByteArray.get`/`ByteArray.set`
  (`lean_byte_array_fget`/`fset`): proved bounds remove checks (Plan.md §6 items 2–3, S1).

Hot paths use only `UInt8`/`UInt32`/`UInt64` arithmetic for values; no `Nat` `<<<`/`^`
(Plan.md §6 item 1). Positions are `Nat` (small scalars, no GMP in practice).

Invariants are structural: a `Reader`/`BitReader` always satisfies `pos ≤ stop ≤ data.size`,
and the lemmas below state that each successful read advances by exactly the bytes it
consumes and never changes the buffer or the end.
-/

namespace JPEG2000.Bytes

/-! ## Byte reader -/

/-- A big-endian byte reader over `data[pos, stop)`. Offsets are absolute indices into
`data`, so errors of sub-readers report positions in the whole input. -/
structure Reader where
  /-- The underlying buffer (shared by sub-readers, never copied). -/
  data : ByteArray
  /-- The next byte to read. -/
  pos : Nat
  /-- One past the last readable byte. -/
  stop : Nat
  /-- The stage reported in errors. -/
  stage : Stage := .marker
  /-- The end lies within the buffer. -/
  stop_le : stop ≤ data.size
  /-- The position never exceeds the end. -/
  pos_le : pos ≤ stop

namespace Reader

/-- A reader over the whole buffer, starting at offset 0. -/
def ofByteArray (data : ByteArray) (stage : Stage := .marker) : Reader :=
  { data, pos := 0, stop := data.size, stage, stop_le := Nat.le_refl _,
    pos_le := Nat.zero_le _ }

/-- Number of bytes left before the end. -/
def remaining (r : Reader) : Nat := r.stop - r.pos

/-- Whether no bytes are left. -/
def atEnd (r : Reader) : Bool := r.stop ≤ r.pos

/-- The `truncated` error at the reader's current position. -/
def truncErr (r : Reader) (what : String) : Error :=
  .truncated (.atOffset r.stage r.pos) what

/-- The same reader with another error stage. -/
def withStage (r : Reader) (stage : Stage) : Reader := { r with stage }

/-- Reads one byte. -/
@[inline] def u8 (r : Reader) : Except Error (UInt8 × Reader) :=
  if h : r.pos + 1 ≤ r.stop then
    .ok (r.data.get r.pos (by have := r.stop_le; omega),
      { r with pos := r.pos + 1, pos_le := h })
  else .error (r.truncErr "u8")

/-- Reads a big-endian 16-bit value (T.800 A.1). -/
@[inline] def u16be (r : Reader) : Except Error (UInt16 × Reader) :=
  if h : r.pos + 2 ≤ r.stop then
    have hs := r.stop_le
    let b0 := (r.data.get r.pos (by omega)).toUInt16
    let b1 := (r.data.get (r.pos + 1) (by omega)).toUInt16
    .ok ((b0 <<< 8) ||| b1, { r with pos := r.pos + 2, pos_le := h })
  else .error (r.truncErr "u16")

/-- Reads a big-endian 32-bit value (T.800 A.1, I.4 box lengths). -/
@[inline] def u32be (r : Reader) : Except Error (UInt32 × Reader) :=
  if h : r.pos + 4 ≤ r.stop then
    have hs := r.stop_le
    let b0 := (r.data.get r.pos (by omega)).toUInt32
    let b1 := (r.data.get (r.pos + 1) (by omega)).toUInt32
    let b2 := (r.data.get (r.pos + 2) (by omega)).toUInt32
    let b3 := (r.data.get (r.pos + 3) (by omega)).toUInt32
    .ok ((b0 <<< 24) ||| (b1 <<< 16) ||| (b2 <<< 8) ||| b3,
      { r with pos := r.pos + 4, pos_le := h })
  else .error (r.truncErr "u32")

/-- Reads a big-endian 64-bit value (T.800 I.4: `XLBox` extended box lengths). -/
@[inline] def u64be (r : Reader) : Except Error (UInt64 × Reader) :=
  if h : r.pos + 8 ≤ r.stop then
    have hs := r.stop_le
    let g (k : Nat) (hk : k < 8) : UInt64 := (r.data.get (r.pos + k) (by omega)).toUInt64
    let hi := (g 0 (by decide) <<< 56) ||| (g 1 (by decide) <<< 48) |||
      (g 2 (by decide) <<< 40) ||| (g 3 (by decide) <<< 32)
    let lo := (g 4 (by decide) <<< 24) ||| (g 5 (by decide) <<< 16) |||
      (g 6 (by decide) <<< 8) ||| g 7 (by decide)
    .ok (hi ||| lo, { r with pos := r.pos + 8, pos_le := h })
  else .error (r.truncErr "u64")

/-- Skips `n` bytes. -/
@[inline] def skip (r : Reader) (n : Nat) : Except Error Reader :=
  if h : r.pos + n ≤ r.stop then .ok { r with pos := r.pos + n, pos_le := h }
  else .error (r.truncErr s!"skip {n}")

/-- Splits off the next `n` bytes as a sub-reader over `[pos, pos + n)` (same buffer, same
stage) and returns it with this reader advanced past them. Used for marker segments and box
bodies whose length the stream declares. -/
@[inline] def take (r : Reader) (n : Nat) : Except Error (Reader × Reader) :=
  if h : r.pos + n ≤ r.stop then
    let sub : Reader :=
      { data := r.data, pos := r.pos, stop := r.pos + n, stage := r.stage,
        stop_le := Nat.le_trans h r.stop_le, pos_le := Nat.le_add_right _ _ }
    .ok (sub, { r with pos := r.pos + n, pos_le := h })
  else .error (r.truncErr s!"take {n}")

/-- Copies the remaining bytes `[pos, stop)` out as a fresh `ByteArray`. -/
def rest (r : Reader) : ByteArray := r.data.extract r.pos r.stop

/-! ### Reader lemmas -/

/-- The end lies within the buffer (restating the structure invariant). -/
theorem pos_le_size (r : Reader) : r.pos ≤ r.data.size := Nat.le_trans r.pos_le r.stop_le

/-- A successful `u8` advances by exactly 1 and keeps buffer, end and stage. -/
theorem u8_pos {r r' : Reader} {v : UInt8} (h : r.u8 = .ok (v, r')) :
    r'.pos = r.pos + 1 ∧ r'.stop = r.stop ∧ r'.data = r.data ∧ r'.stage = r.stage := by
  unfold u8 at h; split at h
  · cases h; exact ⟨rfl, rfl, rfl, rfl⟩
  · cases h

/-- A successful `u16be` advances by exactly 2 and keeps buffer, end and stage. -/
theorem u16be_pos {r r' : Reader} {v : UInt16} (h : r.u16be = .ok (v, r')) :
    r'.pos = r.pos + 2 ∧ r'.stop = r.stop ∧ r'.data = r.data ∧ r'.stage = r.stage := by
  unfold u16be at h; split at h
  · cases h; exact ⟨rfl, rfl, rfl, rfl⟩
  · cases h

/-- A successful `u32be` advances by exactly 4 and keeps buffer, end and stage. -/
theorem u32be_pos {r r' : Reader} {v : UInt32} (h : r.u32be = .ok (v, r')) :
    r'.pos = r.pos + 4 ∧ r'.stop = r.stop ∧ r'.data = r.data ∧ r'.stage = r.stage := by
  unfold u32be at h; split at h
  · cases h; exact ⟨rfl, rfl, rfl, rfl⟩
  · cases h

/-- A successful `u64be` advances by exactly 8 and keeps buffer, end and stage. -/
theorem u64be_pos {r r' : Reader} {v : UInt64} (h : r.u64be = .ok (v, r')) :
    r'.pos = r.pos + 8 ∧ r'.stop = r.stop ∧ r'.data = r.data ∧ r'.stage = r.stage := by
  unfold u64be at h; split at h
  · cases h; exact ⟨rfl, rfl, rfl, rfl⟩
  · cases h

/-- A successful `skip n` advances by exactly `n` and keeps buffer, end and stage. -/
theorem skip_pos {r r' : Reader} {n : Nat} (h : r.skip n = .ok r') :
    r'.pos = r.pos + n ∧ r'.stop = r.stop ∧ r'.data = r.data ∧ r'.stage = r.stage := by
  unfold skip at h; split at h
  · cases h; exact ⟨rfl, rfl, rfl, rfl⟩
  · cases h

/-- A successful `take n` yields a sub-reader over exactly `[pos, pos + n)` of the same
buffer, lying within the parent's range, and advances the parent by exactly `n`. -/
theorem take_spec {r sub r' : Reader} {n : Nat} (h : r.take n = .ok (sub, r')) :
    sub.pos = r.pos ∧ sub.stop = r.pos + n ∧ sub.data = r.data ∧ sub.stop ≤ r.stop ∧
    r'.pos = r.pos + n ∧ r'.stop = r.stop ∧ r'.data = r.data := by
  unfold take at h; split at h
  · rename_i hle; cases h; exact ⟨rfl, rfl, rfl, hle, rfl, rfl, rfl⟩
  · cases h

/-- `u8` fails exactly when no byte is left, and then with `truncated` at the current
offset. -/
theorem u8_error {r : Reader} {e : Error} (h : r.u8 = .error e) :
    r.stop ≤ r.pos ∧ e = .truncated (.atOffset r.stage r.pos) "u8" := by
  unfold u8 at h; split at h
  · cases h
  · rename_i hn; cases h; exact ⟨by omega, rfl⟩

end Reader

/-! ## Packet-header bit reader (T.800 B.10.1) -/

/-- MSB-first bit reader with `0xFF` bit stuffing (T.800 B.10.1). `buf` holds the byte most
recently loaded and `ct` the number of its bits not yet consumed (0…8). -/
structure BitReader where
  /-- The underlying buffer. -/
  data : ByteArray
  /-- The next byte to load. -/
  pos : Nat
  /-- One past the last readable byte. -/
  stop : Nat
  /-- The byte most recently loaded (0 before the first load and after `align`). -/
  buf : UInt32 := 0
  /-- Unconsumed bits of `buf`. -/
  ct : UInt32 := 0
  /-- The stage reported in errors. -/
  stage : Stage := .tier2
  /-- The end lies within the buffer. -/
  stop_le : stop ≤ data.size
  /-- The position never exceeds the end. -/
  pos_le : pos ≤ stop

namespace BitReader

/-- Starts a bit reader at a byte reader's position, over the same range (stage `tier2`). -/
def ofReader (r : Reader) (stage : Stage := .tier2) : BitReader :=
  { data := r.data, pos := r.pos, stop := r.stop, stage, stop_le := r.stop_le,
    pos_le := r.pos_le }

/-- A byte reader at the bit reader's byte position (call after `align`). -/
def toReader (b : BitReader) (stage : Stage := .marker) : Reader :=
  { data := b.data, pos := b.pos, stop := b.stop, stage, stop_le := b.stop_le,
    pos_le := b.pos_le }

/-- Loads the next byte. After a `0xFF` byte only 7 bits of the new byte count (its MSB is
the stuffed 0 of B.10.1); otherwise 8. -/
@[inline] def load (b : BitReader) : Except Error BitReader :=
  if h : b.pos + 1 ≤ b.stop then
    let v := (b.data.get b.pos (by have := b.stop_le; omega)).toUInt32
    .ok { b with buf := v, ct := if b.buf == 0xFF then 7 else 8, pos := b.pos + 1,
                 pos_le := h }
  else .error (.truncated (.atOffset b.stage b.pos) "packet header")

/-- Reads one bit (MSB first). -/
@[inline] def bit (b : BitReader) : Except Error (UInt32 × BitReader) := do
  let b ← if b.ct == 0 then b.load else pure b
  let ct := b.ct - 1
  return ((b.buf >>> ct) &&& 1, { b with ct })

/-- Reads `k` bits MSB first, appending them to `acc` (structural recursion on `k`). -/
def bitsAux (b : BitReader) (acc : UInt32) : Nat → Except Error (UInt32 × BitReader)
  | 0 => .ok (acc, b)
  | k + 1 => do
    let (x, b) ← b.bit
    bitsAux b ((acc <<< 1) ||| x) k

/-- Reads `n ≤ 32` bits as an unsigned value, first bit most significant. `n > 32` is a
caller error reported as `malformed` (never silently truncated). -/
def bits (b : BitReader) (n : Nat) : Except Error (UInt32 × BitReader) :=
  if n ≤ 32 then bitsAux b 0 n
  else .error (.malformed (.atOffset b.stage b.pos) s!"bit field of {n} > 32 bits")

/-- Ends the packet header: drops the rest of the current byte and, if that byte was `0xFF`,
consumes the following byte too (it holds the stuffed bit; T.800 B.10.1, OpenJPEG
`opj_bio_inalign`). Afterwards `pos` is the first byte of the packet body. -/
def align (b : BitReader) : Except Error BitReader :=
  if b.buf == 0xFF then
    if h : b.pos + 1 ≤ b.stop then
      .ok { b with buf := 0, ct := 0, pos := b.pos + 1, pos_le := h }
    else .error (.truncated (.atOffset b.stage b.pos) "packet header stuffing byte")
  else .ok { b with buf := 0, ct := 0 }

/-! ### Bit reader lemmas: the byte position is monotone and the range is fixed. -/

/-- `load` advances by exactly one byte and keeps buffer and end. -/
theorem load_pos {b b' : BitReader} (h : b.load = .ok b') :
    b'.pos = b.pos + 1 ∧ b'.stop = b.stop ∧ b'.data = b.data := by
  unfold load at h; split at h
  · cases h; exact ⟨rfl, rfl, rfl⟩
  · cases h

/-- `bit` advances by at most one byte and keeps buffer and end. -/
theorem bit_pos {b b' : BitReader} {x : UInt32} (h : b.bit = .ok (x, b')) :
    b.pos ≤ b'.pos ∧ b'.pos ≤ b.pos + 1 ∧ b'.stop = b.stop ∧ b'.data = b.data := by
  unfold bit at h
  by_cases hc : (b.ct == 0) = true
  · simp only [hc, ↓reduceIte] at h
    cases hl : b.load with
    | error e => rw [hl] at h; cases h
    | ok b1 =>
      rw [hl] at h; cases h
      have := load_pos hl
      exact ⟨by simp; omega, by simp; omega, by simp [this.2.1], by simp [this.2.2]⟩
  · simp only [hc] at h
    cases h; exact ⟨by simp, by simp, rfl, rfl⟩

/-- `bitsAux` never moves the byte position backwards and keeps buffer and end. -/
theorem bitsAux_pos {b b' : BitReader} {acc x : UInt32} :
    ∀ {k : Nat}, b.bitsAux acc k = .ok (x, b') →
      b.pos ≤ b'.pos ∧ b'.pos ≤ b.pos + k ∧ b'.stop = b.stop ∧ b'.data = b.data
  | 0, h => by simp [bitsAux] at h; obtain ⟨-, rfl⟩ := h; exact ⟨by simp, by simp, rfl, rfl⟩
  | k + 1, h => by
    simp only [bitsAux] at h
    cases hb : b.bit with
    | error e => rw [hb] at h; cases h
    | ok p =>
      obtain ⟨y, b1⟩ := p
      rw [hb] at h
      have h1 := bit_pos hb
      have h2 := bitsAux_pos (b := b1) h
      exact ⟨by omega, by omega, h2.2.2.1.trans h1.2.2.1, h2.2.2.2.trans h1.2.2.2⟩

/-- `bits n` advances by at most `n` bytes, never backwards, and keeps buffer and end. -/
theorem bits_pos {b b' : BitReader} {n : Nat} {x : UInt32} (h : b.bits n = .ok (x, b')) :
    b.pos ≤ b'.pos ∧ b'.pos ≤ b.pos + n ∧ b'.stop = b.stop ∧ b'.data = b.data := by
  unfold bits at h; split at h
  · exact bitsAux_pos h
  · cases h

/-- `align` advances by at most one byte, leaves no pending bits, and keeps buffer and
end. -/
theorem align_pos {b b' : BitReader} (h : b.align = .ok b') :
    b.pos ≤ b'.pos ∧ b'.pos ≤ b.pos + 1 ∧ b'.ct = 0 ∧ b'.stop = b.stop ∧ b'.data = b.data := by
  unfold align at h; split at h
  · split at h
    · cases h; exact ⟨by simp, by simp, rfl, rfl, rfl⟩
    · cases h
  · cases h; exact ⟨by simp, by simp, rfl, rfl, rfl⟩

end BitReader

/-! ## `Int32` planes (Plan.md §6 item 2) -/

/-- `n` zero bytes appended to `acc` (structural recursion on `n`). -/
def pushZeros (acc : ByteArray) : Nat → ByteArray
  | 0 => acc
  | n + 1 => pushZeros (acc.push 0) n

/-- `pushZeros` adds exactly `n` bytes. -/
theorem size_pushZeros (acc : ByteArray) (n : Nat) : (pushZeros acc n).size = acc.size + n := by
  induction n generalizing acc with
  | zero => rfl
  | succ n ih => simp only [pushZeros, ih, ByteArray.size_push]; omega

/-- Reading a `ByteArray.push` (not in v4.36 core). -/
private theorem bget_push (a : ByteArray) (b : UInt8) (j : Nat) (hj : j < (a.push b).size) :
    (a.push b).get j hj = if h : j < a.size then a.get j h else b := by
  cases a with
  | mk bs => simp only [ByteArray.push, ByteArray.get, Array.getElem_push]; rfl

/-- The bytes added by `pushZeros` read as 0; the old bytes are unchanged. -/
theorem get_pushZeros (acc : ByteArray) (n j : Nat) (hj : j < (pushZeros acc n).size) :
    (pushZeros acc n).get j hj = if h : j < acc.size then acc.get j h else 0 := by
  induction n generalizing acc with
  | zero =>
    simp only [pushZeros] at hj ⊢
    simp [hj]
  | succ n ih =>
    simp only [pushZeros]
    rw [ih]
    by_cases h1 : j < acc.size
    · have h2 : j < (acc.push 0).size := by rw [ByteArray.size_push]; omega
      simp only [h1, h2, ↓reduceDIte, bget_push]
    · by_cases h2 : j < (acc.push 0).size
      · simp only [h1, h2, dite_false, dite_true, bget_push]
      · simp only [h1, h2, dite_false]

/-- A `width × height` plane of `Int32` cells stored row-major as little-endian 4-byte cells
in a `ByteArray`; the size invariant is part of the structure. -/
structure Plane where
  /-- Width in samples. -/
  width : Nat
  /-- Height in samples. -/
  height : Nat
  /-- The cells, 4 bytes each, little-endian. -/
  data : ByteArray
  /-- Size invariant: exactly four bytes per cell. -/
  size_eq : data.size = 4 * (width * height)

/-- Size of `ByteArray.set` (not in v4.36 core). -/
private theorem bsize_set (a : ByteArray) (i : Nat) (v : UInt8) (hi : i < a.size) :
    (a.set i v hi).size = a.size := by
  cases a; simp [ByteArray.set, ByteArray.size]

/-- Reading back a `ByteArray.set` (not in v4.36 core). -/
private theorem bget_set (a : ByteArray) (i j : Nat) (v : UInt8) (hi : i < a.size)
    (hj : j < (a.set i v hi).size) :
    (a.set i v hi).get j hj = if i = j then v else a.get j (by rw [bsize_set] at hj; exact hj) := by
  cases a with
  | mk bs =>
    simp only [ByteArray.set, ByteArray.get]
    rw [Array.getElem_set]

/-- An `if` whose condition is false (non-deprecated form, used with `disch := omega`). -/
private theorem ite_no {α : Type} {c : Prop} [Decidable c] (h : ¬c) (a b : α) :
    (if c then a else b) = b := by simp [h]

/-- Little-endian recombination inverts the byte split of a `UInt32`. -/
private theorem le_bytes (u : UInt32) :
    u.toUInt8.toUInt32 + (u >>> (8 : UInt32)).toUInt8.toUInt32 * (256 : UInt32)
      + (u >>> (16 : UInt32)).toUInt8.toUInt32 * (65536 : UInt32)
      + (u >>> (24 : UInt32)).toUInt8.toUInt32 * (16777216 : UInt32) = u := by
  apply UInt32.toNat_inj.mp
  have := u.toNat_lt
  simp [UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  omega

namespace Plane

/-- Number of cells. -/
def cells (p : Plane) : Nat := p.width * p.height

/-- An all-zero plane. The caller has already checked `width * height` against
`Limits.maxWorkSamples` (Plan.md §3 rule 3); this function allocates exactly
`4 * width * height` bytes. -/
def zero (width height : Nat) : Plane :=
  { width, height, data := pushZeros (ByteArray.emptyWithCapacity (4 * (width * height)))
      (4 * (width * height)),
    size_eq := by
      rw [size_pushZeros, show (ByteArray.emptyWithCapacity (4 * (width * height))).size = 0 from rfl,
        Nat.zero_add] }

/-- `zero` checked against `Limits.maxWorkSamples` (S3): errors with `limitExceeded` before
allocating when `width * height` exceeds it. -/
def zeroChecked (L : Limits) (loc : Location) (width height : Nat) : Except Error Plane := do
  L.check loc .workSamples (width * height)
  return zero width height

/-- The cell at index `i` (row-major), with a proof that it is in range: four unchecked
byte reads. -/
@[inline] def get (p : Plane) (i : Nat) (h : i < p.width * p.height) : Int32 :=
  have hs := p.size_eq
  let o := 4 * i
  let b0 := (p.data.get o (by omega)).toUInt32
  let b1 := (p.data.get (o + 1) (by omega)).toUInt32
  let b2 := (p.data.get (o + 2) (by omega)).toUInt32
  let b3 := (p.data.get (o + 3) (by omega)).toUInt32
  (b0 + b1 * (256 : UInt32) + b2 * (65536 : UInt32) + b3 * (16777216 : UInt32)).toInt32

/-- The cell at `(x, y)`, with proofs that both coordinates are in range. -/
@[inline] def getXY (p : Plane) (x y : Nat) (hx : x < p.width) (hy : y < p.height) : Int32 :=
  p.get (y * p.width + x) (by
    have : (y + 1) * p.width ≤ p.height * p.width := Nat.mul_le_mul_right _ hy
    rw [Nat.mul_comm p.width]; rw [Nat.succ_mul] at this; omega)

/-- Checked read: `none` out of range. -/
def get? (p : Plane) (i : Nat) : Option Int32 :=
  if h : i < p.width * p.height then some (p.get i h) else none

/-- Overwrites the cell at index `i` (in place when `p` is unique): four unchecked byte
writes. The size invariant is preserved. -/
@[inline] def set (p : Plane) (i : Nat) (v : Int32) (h : i < p.width * p.height) : Plane :=
  have hs := p.size_eq
  let u := v.toUInt32
  let o := 4 * i
  let d0 := p.data.set o u.toUInt8 (by omega)
  let d1 := d0.set (o + 1) (u >>> (8 : UInt32)).toUInt8 (by rw [bsize_set]; omega)
  let d2 := d1.set (o + 2) (u >>> (16 : UInt32)).toUInt8
    (by rw [bsize_set, bsize_set]; omega)
  let d3 := d2.set (o + 3) (u >>> (24 : UInt32)).toUInt8
    (by rw [bsize_set, bsize_set, bsize_set]; omega)
  { p with data := d3, size_eq := by simp only [d3, d2, d1, d0, bsize_set]; exact hs }

/-- Checked write: `none` out of range. -/
def set? (p : Plane) (i : Nat) (v : Int32) : Option Plane :=
  if h : i < p.width * p.height then some (p.set i v h) else none

/-! ### Plane lemmas -/

/-- `zero` has the requested dimensions. -/
theorem zero_dims (w h : Nat) : (zero w h).width = w ∧ (zero w h).height = h := ⟨rfl, rfl⟩

/-- `set` keeps the dimensions. -/
theorem set_dims (p : Plane) (i : Nat) (v : Int32) (h : i < p.width * p.height) :
    (p.set i v h).width = p.width ∧ (p.set i v h).height = p.height := ⟨rfl, rfl⟩

/-- Reading a cell just written returns the written value. -/
theorem get_set_self (p : Plane) (i : Nat) (v : Int32) (h : i < p.width * p.height)
    (h' : i < (p.set i v h).width * (p.set i v h).height) :
    (p.set i v h).get i h' = v := by
  simp (disch := omega) only [get, set, bget_set, ite_no, ↓reduceIte]
  rw [le_bytes]; exact Int32.toInt32_toUInt32 v

/-- Writing one cell leaves every other cell unchanged (frame lemma). -/
theorem get_set_ne (p : Plane) (i j : Nat) (v : Int32) (h : i < p.width * p.height)
    (hj : j < (p.set i v h).width * (p.set i v h).height) (hij : i ≠ j) :
    (p.set i v h).get j hj = p.get j hj := by
  simp (disch := omega) only [get, set, bget_set, ite_no]

/-- Every cell of `zero` is 0. -/
theorem get_zero (w h i : Nat) (hi : i < (zero w h).width * (zero w h).height) :
    (zero w h).get i hi = 0 := by
  have e0 : (ByteArray.emptyWithCapacity (4 * (w * h))).size = 0 := rfl
  simp only [get, zero, get_pushZeros, e0, Nat.not_lt_zero, dite_false]
  rfl

end Plane

end JPEG2000.Bytes
