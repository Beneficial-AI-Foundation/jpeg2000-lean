import Fuzz.Rng

/-!
# Structure-aware mutators for the fuzz harness (task 9.1)

Plan.md §8.6; T.800 Annex A (marker segments, `Lxxx`, `Psot`, `Nppm`) and Annex I (box
lengths). `scan` finds the "units" of an input (JP2 boxes, codestream marker segments) with
the offsets of their length fields; the mutators flip bits, set or insert or delete bytes and
runs, duplicate / remove / splice units, rewrite length fields and truncate. Every function
is total; none of them needs the input to be well formed (a scan of garbage yields few units
and the byte-level mutators take over).
-/

namespace Fuzz

/-- One structural unit: a JP2 box or a codestream marker segment. -/
structure Seg where
  /-- Offset of the first byte (`LBox`, or the `0xFF` of the marker). -/
  off : Nat
  /-- Total length in bytes, clipped to the input. -/
  len : Nat
  /-- Length-like fields inside the unit: (absolute offset, width in bytes). -/
  fields : Array (Nat × Nat) := #[]
  deriving Inhabited

/-- The byte at `i` (0 past the end). -/
def byteAt (d : ByteArray) (i : Nat) : Nat := (d.data.getD i 0).toNat

/-- Big-endian number of `w` bytes at `off` (missing bytes read 0). -/
def be (d : ByteArray) (off w : Nat) : Nat := Id.run do
  let mut v := 0
  for k in [0:w] do v := v * 256 + byteAt d (off + k)
  return v

/-- Overwrites `w` bytes at `off` with the big-endian `v` (clipped to the input). -/
def putBE (d : ByteArray) (off w v : Nat) : ByteArray := Id.run do
  let mut d := d
  for k in [0:w] do
    let i := off + k
    if i < d.size then
      d := d.set! i ((v >>> (8 * (w - 1 - k))) % 256).toUInt8
  return d

/-- The input without bytes `a … b-1`. -/
def cut (d : ByteArray) (a b : Nat) : ByteArray :=
  d.extract 0 a ++ d.extract b d.size

/-- The input with `ins` inserted at `pos`. -/
def insertAt (d : ByteArray) (pos : Nat) (ins : ByteArray) : ByteArray :=
  d.extract 0 pos ++ ins ++ d.extract pos d.size

/-- JP2 boxes (top level, and the children of `jp2h`) and the offset of the codestream
(the contents of `jp2c`), if any. -/
def scanBoxes (d : ByteArray) : Array Seg × Option Nat := Id.run do
  let mut units : Array Seg := #[]
  let mut cs : Option Nat := none
  -- worklist of (start, stop, depth)
  let mut work : Array (Nat × Nat × Nat) := #[(0, d.size, 0)]
  let mut fuel := 4 * d.size + 8
  while fuel > 0 && !work.isEmpty do
    fuel := fuel - 1
    let (start, stop, depth) := work.back?.getD (0, 0, 0)
    work := work.pop
    let mut pos := start
    let mut inner := 0
    while pos + 8 ≤ stop && inner < 512 do
      inner := inner + 1
      let lbox := be d pos 4
      let tbox := be d (pos + 4) 4
      let (hdr, total, fields) : Nat × Nat × Array (Nat × Nat) :=
        if lbox == 1 then (16, be d (pos + 8) 8, #[(pos, 4), (pos + 8, 8)])
        else if lbox == 0 then (8, stop - pos, #[(pos, 4)])
        else (8, lbox, #[(pos, 4)])
      let len := min (if total < hdr then hdr else total) (stop - pos)
      units := units.push { off := pos, len, fields }
      if tbox == 0x6A703263 && cs.isNone then cs := some (pos + hdr)
      if tbox == 0x6A703268 && depth < 2 then work := work.push (pos + hdr, pos + len, depth + 1)
      pos := pos + len
  return (units, cs)

/-- Marker segments of the codestream starting at `start` (SOC, main header, tile-part
headers, `SOD` and `EOC` markers; tile-part bodies are skipped with `Psot`). -/
def scanCodestream (d : ByteArray) (start : Nat) : Array Seg := Id.run do
  let mut units : Array Seg := #[]
  let mut pos := start
  let mut tpEnd := 0
  for _ in [0:d.size + 1] do
    if pos + 2 > d.size || byteAt d pos != 0xFF then break
    let m := byteAt d (pos + 1)
    if m == 0x93 then
      units := units.push { off := pos, len := 2 }
      let e := if tpEnd > pos + 2 then tpEnd else d.size
      pos := min e d.size
    else if m == 0xD9 then
      units := units.push { off := pos, len := 2 }
      break
    else if m == 0x4F || (0x30 ≤ m && m ≤ 0x3F) then
      units := units.push { off := pos, len := 2 }
      pos := pos + 2
    else
      let l := be d (pos + 2) 2
      let len := min (2 + l) (d.size - pos)
      let mut fields : Array (Nat × Nat) := #[(pos + 2, 2)]
      if m == 0x90 then
        fields := fields.push (pos + 6, 4)
        let psot := be d (pos + 6) 4
        tpEnd := if psot == 0 then d.size else pos + psot
      if m == 0x60 then fields := fields.push (pos + 5, 4)
      units := units.push { off := pos, len := max len 2, fields }
      pos := pos + max len 2
  return units

/-- All units of an input (JP2 boxes plus codestream segments) and the codestream offset. -/
def scan (d : ByteArray) : Array Seg × Option Nat :=
  if byteAt d 0 == 0xFF && byteAt d 1 == 0x4F then (scanCodestream d 0, some 0)
  else
    let (bs, cs) := scanBoxes d
    match cs with
    | some o => (bs ++ scanCodestream d o, some o)
    | none => (bs, none)

/-- The codestream of an input: itself if raw, else the contents of the `jp2c` box. -/
def codestreamOf (d : ByteArray) : Option ByteArray :=
  if byteAt d 0 == 0xFF && byteAt d 1 == 0x4F then some d
  else (scanBoxes d).2.map fun o => d.extract o d.size

/-- A random byte-level position, biased towards the first 512 bytes (headers). -/
def randPos (d : ByteArray) : R Nat := do
  let early ← chance 1 2
  if early then below (min d.size 512) else below d.size

/-- Flips 1 … 8 random bits. -/
def bitFlip (d : ByteArray) : R (String × ByteArray) := do
  let k ← between 1 8
  let mut d := d
  for _ in [0:k] do
    if d.size > 0 then
      let p ← randPos d
      let b ← below 8
      d := d.set! p (d.data.getD p 0 ^^^ (1 <<< b.toUInt8))
  return (s!"bitflip×{k}", d)

/-- Sets a byte to 0x00, 0xFF or random. -/
def setByte (d : ByteArray) : R (String × ByteArray) := do
  if d.size == 0 then return ("setbyte(empty)", d)
  let p ← randPos d
  let w ← below 3
  let v ← if w == 0 then pure 0 else if w == 1 then pure 255 else below 256
  return (s!"setbyte@{p}={v}", d.set! p v.toUInt8)

/-- Inserts a run of random, constant or repeated bytes. -/
def insertRun (d : ByteArray) : R (String × ByteArray) := do
  let p ← randPos d
  let big ← chance 1 8
  let n ← if big then between 1 300 else between 1 16
  let kind ← below 3
  let c ← below 256
  let mut run := ByteArray.empty
  for _ in [0:n] do
    let v ← if kind == 0 then below 256 else if kind == 1 then pure c else pure (byteAt d p)
    run := run.push v.toUInt8
  return (s!"insert@{p}+{n}", insertAt d (min p d.size) run)

/-- Deletes a run of bytes. -/
def deleteRun (d : ByteArray) : R (String × ByteArray) := do
  let p ← randPos d
  let big ← chance 1 8
  let n ← if big then between 1 300 else between 1 16
  return (s!"delete@{p}-{n}", cut d p (min d.size (p + n)))

/-- Duplicates a unit in place. -/
def dupUnit (d : ByteArray) (us : Array Seg) : R (String × ByteArray) := do
  if us.isEmpty then return (← bitFlip d)
  let u ← pick us
  let seg := d.extract u.off (u.off + u.len)
  return (s!"dupunit@{u.off}+{u.len}", insertAt d (min d.size (u.off + u.len)) seg)

/-- Removes a unit. -/
def removeUnit (d : ByteArray) (us : Array Seg) : R (String × ByteArray) := do
  if us.isEmpty then return (← bitFlip d)
  let u ← pick us
  return (s!"rmunit@{u.off}+{u.len}", cut d u.off (u.off + u.len))

/-- Inserts a unit of another seed at a unit boundary of this input. -/
def spliceUnit (d : ByteArray) (us : Array Seg) (donor : ByteArray) (dus : Array Seg) :
    R (String × ByteArray) := do
  if dus.isEmpty then return (← bitFlip d)
  let u ← pick dus
  let seg := donor.extract u.off (u.off + u.len)
  let at_ ← if us.isEmpty then pure 0 else do
    let t ← pick us
    let after ← chance 1 2
    pure (if after then t.off + t.len else t.off)
  return (s!"splice@{at_}+{u.len}", insertAt d (min d.size at_) seg)

/-- Rewrites a length-like field (`Lxxx`, `Psot`, `Nppm`, box lengths) to a boundary value. -/
def lengthField (d : ByteArray) (us : Array Seg) : R (String × ByteArray) := do
  let fs := us.foldl (fun a u => a ++ u.fields) #[]
  if fs.isEmpty then return (← bitFlip d)
  let (off, w) ← pick fs
  let v := be d off w
  let top := 256 ^ w - 1
  let k ← below 10
  let nv ← match k with
    | 0 => pure 0
    | 1 => pure 1
    | 2 => pure (v + 1)
    | 3 => pure (v - 1)
    | 4 => pure (v * 2)
    | 5 => pure (v / 2)
    | 6 => pure top
    | 7 => pure (top - 1)
    | 8 => pure (d.size - off)
    | _ => do let r ← rnd64; pure (r.toNat % (top + 1))
  let nv := nv % (top + 1)
  return (s!"lenfield@{off}w{w}:{v}->{nv}", putBE d off w nv)

/-- Truncates, often near the end. -/
def truncate (d : ByteArray) : R (String × ByteArray) := do
  let near ← chance 1 2
  let n ← if near then below (min d.size 64) else below d.size
  return (s!"truncate-{n}", d.extract 0 (d.size - n))

/-- One random mutation of `d` (`donor` supplies spliced units). -/
def mutate1 (d : ByteArray) (donor : ByteArray) : R (String × ByteArray) := do
  let (us, _) := scan d
  let (dus, _) := scan donor
  let k ← below 20
  if k < 4 then bitFlip d
  else if k < 6 then setByte d
  else if k < 8 then insertRun d
  else if k < 10 then deleteRun d
  else if k < 11 then dupUnit d us
  else if k < 12 then removeUnit d us
  else if k < 14 then spliceUnit d us donor dus
  else if k < 18 then lengthField d us
  else truncate d

/-- 1 … 3 stacked mutations; the description lists them. -/
def mutate (d donor : ByteArray) : R (String × ByteArray) := do
  let single ← chance 3 5
  let n ← if single then pure 1 else between 2 3
  let mut d := d
  let mut desc : Array String := #[]
  for _ in [0:n] do
    let (s, d') ← mutate1 d donor
    desc := desc.push s
    d := d'
  return (", ".intercalate desc.toList, d)

end Fuzz
