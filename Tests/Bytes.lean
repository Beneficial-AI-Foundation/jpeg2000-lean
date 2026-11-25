import JPEG2000.Bytes

/-!
# Unit tests: byte reader, packet-header bit reader, `Int32` planes (task 1.1)

Plan.md §4 S1/S3, §6 items 1–3; T.800 A.1 (big-endian marker fields), I.4 (XL box lengths),
B.10.1 (bit stuffing after `0xFF` in packet headers).
-/

namespace JPEG2000.Tests.Bytes

open JPEG2000 JPEG2000.Bytes

/-- Runs one named check, printing a line on failure; returns 1 on failure, 0 on success. -/
def expect (name : String) (ok : Bool) : IO Nat := do
  if ok then return 0
  IO.eprintln s!"  FAIL bytes: {name}"
  return 1

/-- The error of an `Except`, if any (`Except` has no `BEq` instance). -/
def err? {ε α : Type} : Except ε α → Option ε
  | .ok _ => none
  | .error e => some e

/-- The value of an `Except`, if any. -/
def ok? {ε α : Type} : Except ε α → Option α
  | .ok a => some a
  | .error _ => none

/-- A reader over a list of bytes. -/
def rd (bs : List UInt8) (stage : Stage := .marker) : Reader :=
  Reader.ofByteArray bs.toByteArray stage

/-- A bit reader over a list of bytes. -/
def brd (bs : List UInt8) : BitReader := BitReader.ofReader (rd bs)

/-- Value and byte position after `bits n`. -/
def bitsAt (b : BitReader) (n : Nat) : Option (UInt32 × Nat) :=
  (ok? (b.bits n)).map fun (v, b') => (v, b'.pos)

/-- Reads `n₁` bits then `n₂` bits; returns both values and the final byte position. -/
def bits2 (b : BitReader) (n₁ n₂ : Nat) : Option (UInt32 × UInt32 × Nat) :=
  match b.bits n₁ with
  | .error _ => none
  | .ok (x, b) => match b.bits n₂ with
    | .error _ => none
    | .ok (y, b) => some (x, y, b.pos)

/-- Byte position after reading `n` bits and aligning. -/
def alignAfter (bs : List UInt8) (n : Nat) : Option Nat :=
  match (brd bs).bits n with
  | .error _ => none
  | .ok (_, b) => (ok? b.align).map (·.pos)

/-- Runs the suite; returns the number of failures. -/
def run : IO Nat := do
  let mut f := 0
  let bytes : List UInt8 := [0x12, 0x34, 0x56, 0x78, 0x9A, 0xBC, 0xDE, 0xF0]
  let r := rd bytes
  -- big-endian reads
  f := f + (← expect "u8" ((ok? r.u8).map (fun p => (p.1, p.2.pos)) == some (0x12, 1)))
  f := f + (← expect "u16be" ((ok? r.u16be).map (fun p => (p.1, p.2.pos)) == some (0x1234, 2)))
  f := f + (← expect "u32be"
    ((ok? r.u32be).map (fun p => (p.1, p.2.pos)) == some (0x12345678, 4)))
  f := f + (← expect "u64be"
    ((ok? r.u64be).map (fun p => (p.1, p.2.pos)) == some (0x123456789ABCDEF0, 8)))
  f := f + (← expect "u16 then u16"
    (match r.u16be with
     | .ok (_, r) => (ok? r.u16be).map (·.1) == some 0x5678
     | .error _ => false))
  f := f + (← expect "remaining" (r.remaining == 8 && !r.atEnd))
  f := f + (← expect "rest" ((ok? (r.skip 6)).map (·.rest.toList) == some [0xDE, 0xF0]))
  -- truncation errors carry stage and offset
  f := f + (← expect "u32 on 3 bytes: truncated @0"
    ((err? (rd [1, 2, 3]).u32be).map (·.loc) == some (.atOffset .marker 0)))
  f := f + (← expect "u16 after u8 on 2 bytes: truncated @1"
    (match (rd [1, 2] .box).u8 with
     | .ok (_, r) => (err? r.u16be).map (fun e => (e.isTruncated, e.loc)) ==
         some (true, .atOffset .box 1)
     | .error _ => false))
  f := f + (← expect "u8 on empty: truncated @0"
    ((err? (rd []).u8).map (·.offset?) == some (some 0)))
  f := f + (← expect "u64 on 7 bytes fails" ((err? (rd (bytes.take 7)).u64be).isSome))
  f := f + (← expect "skip past end fails @0" ((err? (r.skip 9)).map (·.offset?) == some (some 0)))
  f := f + (← expect "skip to end" ((ok? (r.skip 8)).map (·.atEnd) == some true))
  -- sub-readers
  f := f + (← expect "take: sub-range [2,5) and parent advanced"
    (match r.skip 2 with
     | .ok r2 => match r2.take 3 with
       | .ok (sub, r') =>
         sub.pos == 2 && sub.stop == 5 && r'.pos == 5 && sub.remaining == 3 &&
         (ok? sub.u16be).map (·.1) == some 0x5678 &&
         -- the sub-reader cannot read past its own end, though the buffer goes on
         (err? sub.u32be).map (·.offset?) == some (some 2) &&
         (match sub.u16be with
          | .ok (_, s) => (err? s.u16be).map (·.offset?) == some (some 4)
          | .error _ => false) &&
         (ok? r'.u8).map (·.1) == some 0xBC
       | .error _ => false
     | .error _ => false))
  f := f + (← expect "take past end fails" ((err? (r.take 9)).isSome))
  f := f + (← expect "nested take bounded by parent"
    (match r.take 4 with
     | .ok (sub, _) => (err? (sub.take 5)).isSome && (ok? (sub.take 4)).isSome
     | .error _ => false))
  -- bit reader: plain bytes, MSB first
  f := f + (← expect "bits 8 of A5" (bitsAt (brd [0xA5]) 8 == some (0xA5, 1)))
  f := f + (← expect "bits 3 then 5 of A5" (bits2 (brd [0xA5]) 3 5 == some (5, 5, 1)))
  f := f + (← expect "bits 12 across bytes" (bitsAt (brd [0xAB, 0xCD]) 12 == some (0xABC, 2)))
  f := f + (← expect "bits 32" (bitsAt (brd [0x12, 0x34, 0x56, 0x78]) 32 == some (0x12345678, 4)))
  f := f + (← expect "bits 0" (bitsAt (brd []) 0 == some (0, 0)))
  -- bit stuffing (B.10.1): after 0xFF the next byte gives 7 bits
  f := f + (← expect "FF 7F: 15 bits = 0x7FFF" (bitsAt (brd [0xFF, 0x7F]) 15 == some (0x7FFF, 2)))
  f := f + (← expect "FF 7F: 16th bit needs a new byte"
    ((err? ((brd [0xFF, 0x7F]).bits 16)).map (fun e => (e.isTruncated, e.loc)) ==
      some (true, .atOffset .tier2 2)))
  f := f + (← expect "FF 7F 80: 15 bits then 8 bits (no stuffing after 7F)"
    (bits2 (brd [0xFF, 0x7F, 0x80]) 15 8 == some (0x7FFF, 0x80, 3)))
  f := f + (← expect "FF 40: 9th bit is bit 6 of 0x40"
    (bits2 (brd [0xFF, 0x40]) 8 1 == some (0xFF, 1, 2)))
  f := f + (← expect "FF 7F 7F: 8 bits, then 7 (stuffed) + 7 of 8"
    (bits2 (brd [0xFF, 0x7F, 0x7F]) 8 14 == some (0xFF, 0x3FBF, 3)))
  f := f + (← expect "FE 80: no stuffing after FE"
    (bits2 (brd [0xFE, 0x80]) 8 1 == some (0xFE, 1, 2)))
  -- align
  f := f + (← expect "align at start: no-op" ((ok? (brd [0x12]).align).map (·.pos) == some 0))
  f := f + (← expect "align after 1 bit of 80: pos 1" (alignAfter [0x80, 0xAB] 1 == some 1))
  f := f + (← expect "align after 8 bits of 80: pos 1" (alignAfter [0x80, 0xAB] 8 == some 1))
  f := f + (← expect "align after FF: consumes stuffed byte" (alignAfter [0xFF, 0x00, 0xAB] 8 == some 2))
  f := f + (← expect "align after 3 bits of FF: consumes stuffed byte"
    (alignAfter [0xFF, 0x00, 0xAB] 3 == some 2))
  f := f + (← expect "align after FF at end: truncated"
    (match (brd [0xFF]).bits 8 with
     | .ok (_, b) => (err? b.align).map (·.isTruncated) == some true
     | .error _ => false))
  f := f + (← expect "align after FF 7F (7 bits of 7F): pos 2, no extra byte"
    (alignAfter [0xFF, 0x7F, 0xAB] 15 == some 2))
  f := f + (← expect "align then toReader reads body"
    (match (brd [0xC0, 0x55]).bits 2 with
     | .ok (_, b) => match b.align with
       | .ok b => (ok? b.toReader.u8).map (·.1) == some 0x55
       | .error _ => false
     | .error _ => false))
  f := f + (← expect "align, then new bits start fresh"
    (match (brd [0xFF, 0x00, 0xFF, 0x7F]).bits 4 with
     | .ok (_, b) => match b.align with
       | .ok b => bitsAt b 15 == some (0x7FFF, 4)
       | .error _ => false
     | .error _ => false))
  -- bit reader errors
  f := f + (← expect "bits past end: truncated @1"
    ((err? ((brd [0xAA]).bits 9)).map (·.offset?) == some (some 1)))
  f := f + (← expect "bits 33: malformed"
    (match err? ((brd [0, 0, 0, 0, 0]).bits 33) with
     | some (.malformed _ _) => true
     | _ => false))
  f := f + (← expect "bit reader honours sub-range end"
    (match (rd [0x12, 0x34, 0x56]).take 1 with
     | .ok (sub, _) => (err? ((BitReader.ofReader sub).bits 9)).isSome
     | .error _ => false))
  -- planes
  let p := Plane.zero 3 2
  f := f + (← expect "zero: size 4*w*h" (p.data.size == 24 && p.cells == 6))
  f := f + (← expect "zero: all cells 0"
    ((List.range 6).all fun i => p.get? i == some 0))
  f := f + (← expect "get? out of range" (p.get? 6 == none))
  f := f + (← expect "set? out of range" ((p.set? 6 1).isNone))
  let vals : List Int32 := [7, -1, 2147483647, -2147483648, 0x01020304, -256]
  let q := (List.range 6).zip vals |>.foldl (fun q (i, v) => (q.set? i v).getD q) p
  f := f + (← expect "set/get round trip (6 cells, extremes)"
    ((List.range 6).zip vals |>.all fun (i, v) => q.get? i == some v))
  f := f + (← expect "set keeps size and dims" (q.data.size == 24 && q.width == 3 && q.height == 2))
  f := f + (← expect "little-endian cell layout"
    ((q.data.extract 16 20).toList == [0x04, 0x03, 0x02, 0x01]))
  let q2 := (q.set? 1 42).getD q
  f := f + (← expect "overwrite one cell, others unchanged"
    (q2.get? 1 == some 42 && q2.get? 0 == some 7 && q2.get? 2 == some 2147483647))
  f := f + (← expect "getXY row-major"
    (if hx : 1 < q.width then if hy : 1 < q.height then q.getXY 1 1 hx hy == 0x01020304
      else false else false))
  f := f + (← expect "zeroChecked within limit" ((ok? (Plane.zeroChecked Limits.strict
    (.at .dwt) 16 16)).map (·.data.size) == some 1024))
  f := f + (← expect "zeroChecked over limit: limitExceeded"
    ((err? (Plane.zeroChecked Limits.strict (.at .dwt) 4096 4096)).map (·.isLimit) == some true))
  f := f + (← expect "empty plane" ((Plane.zero 0 5).data.size == 0 && (Plane.zero 0 5).get? 0 == none))
  return f

end JPEG2000.Tests.Bytes
