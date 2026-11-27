import JPEG2000.Error
import JPEG2000.Limits
import JPEG2000.Bytes

/-!
# JP2/JPX box parser (Plan.md §1, §3, §9; T.800 Annex I)

Task 1.2. Locates the codestream inside a JP2 file (or recognises a raw codestream) and reads
the JP2 header box into typed records:

* **Box structure** (T.800 I.4): `LBox` (u32), `TBox` (u32), optional `XLBox` (u64).
  `LBox = 0`: the box extends to the end of its container (the file, for the last box);
  `LBox = 1`: the 64-bit `XLBox` holds the length; `LBox ∈ 2…7` is malformed.
* **Signature box** (I.5.1): exactly `0000000C 6A502020 0D0A870A` at offset 0.
* **File type box** (I.5.2): must be the second box; brand, minor version, compatibility list.
  The brand is not enforced (`jp2 ` for JP2, `jpx ` for JPX files compatible with JP2).
* **JP2 header superbox `jp2h`** (I.5.3): `ihdr` (I.5.3.1), `bpcc` (I.5.3.2), `colr`
  (I.5.3.3; METH 1 enumerated — 16 sRGB, 17 greyscale, 18 sYCC, others such as CIELab
  passed through; METH 2 restricted ICC; JPX METH 3 any ICC and METH 4 vendor: bytes passed
  through as a byte range), `pclr` (I.5.3.4), `cmap` (I.5.3.5), `cdef` (I.5.3.6). The `res `
  superbox (I.5.3.7) and unknown boxes are skipped.
* **Contiguous codestream box `jp2c`** (I.5.4): the first one is the codestream; its body is
  returned as a byte range into the input (no copy).
* **Raw codestream**: an input starting with `FF 4F FF 51` (SOC then SIZ, T.800 A.4.1, A.5.1)
  is a codestream by itself.

Tolerance follows OpenJPEG's `opj_jp2.c`: only the first `colr` box counts (later ones are
kept for JPX readers but a malformed later one is skipped, and a `colr` with an unknown METH
is ignored); a second `ihdr` or `bpcc` is ignored; a second `pclr`, `cmap` or `cdef` is an
error; parsing stops at the first `jp2c`, which must come after `jp2h`; `ihdr` is required.
The relationships between `pclr`, `cmap`, `cdef` and the codestream are checked when they are
applied (Phase 6), except that `cmap` without `pclr` is rejected here.

Bounds (Plan.md §3 rules 2 and 3): the input length is checked against
`Limits.maxInputBytes`; every box loop runs on fuel `Limits.maxBoxes + 1` and counts boxes
over the whole file against `maxBoxes`; entering `jp2h` checks depth 1 against
`maxBoxDepth` (no deeper superbox is entered); `ihdr.NC` is checked against `maxComponents`
and `pclr.NE` against `maxPaletteEntries` (NE ≤ 1024, NPC ≥ 1, every `Bi` depth ≤ 38) before
anything is allocated, and every array read from a box is first checked to fit in the box.
-/

namespace JPEG2000.Box

open JPEG2000.Bytes

/-! ## Box types (T.800 Table I.2) -/

/-- `'jP  '` — JPEG 2000 signature box. -/
def tSignature : UInt32 := 0x6A502020
/-- `'ftyp'` — file type box. -/
def tFtyp : UInt32 := 0x66747970
/-- `'jp2h'` — JP2 header superbox. -/
def tJp2h : UInt32 := 0x6A703268
/-- `'ihdr'` — image header box. -/
def tIhdr : UInt32 := 0x69686472
/-- `'bpcc'` — bits per component box. -/
def tBpcc : UInt32 := 0x62706363
/-- `'colr'` — colour specification box. -/
def tColr : UInt32 := 0x636F6C72
/-- `'pclr'` — palette box. -/
def tPclr : UInt32 := 0x70636C72
/-- `'cmap'` — component mapping box. -/
def tCmap : UInt32 := 0x636D6170
/-- `'cdef'` — channel definition box. -/
def tCdef : UInt32 := 0x63646566
/-- `'res '` — resolution superbox (ignored). -/
def tRes : UInt32 := 0x72657320
/-- `'jp2c'` — contiguous codestream box. -/
def tJp2c : UInt32 := 0x6A703263

/-- The four characters of a box type (non-printable bytes shown as `.`), for messages. -/
def typeName (t : UInt32) : String :=
  let c (s : UInt32) : Char :=
    let b := ((t >>> s) &&& 0xFF).toNat
    if 32 ≤ b ∧ b < 127 then Char.ofNat b else '.'
  String.ofList [c 24, c 16, c 8, c 0]

/-! ## Records -/

/-- A byte range `[start, start + len)` of the input (no copy). -/
structure ByteRange where
  /-- Offset of the first byte in the input. -/
  start : Nat
  /-- Number of bytes. -/
  len : Nat
  deriving Repr, DecidableEq, Inhabited

/-- File type box contents (T.800 I.5.2). -/
structure FileType where
  /-- Brand (`'jp2 '` = `0x6A703220`, `'jpx '` for JPX). -/
  brand : UInt32
  /-- Minor version. -/
  minorVersion : UInt32
  /-- Compatibility list. -/
  compat : Array UInt32
  deriving Repr, DecidableEq, Inhabited

/-- Image header box (T.800 I.5.3.1). -/
structure Ihdr where
  /-- Image height (`HEIGHT`). -/
  height : UInt32
  /-- Image width (`WIDTH`). -/
  width : UInt32
  /-- Number of components (`NC`, ≥ 1). -/
  nc : UInt16
  /-- Bits per component (`BPC`): bit 7 = signed, bits 0–6 = depth − 1; 255 = varies (see
  `bpcc`). -/
  bpc : UInt8
  /-- Compression type (`C`, 7 for JPEG 2000; other values are tolerated as by OpenJPEG). -/
  c : UInt8
  /-- Colourspace unknown (`UnkC`). -/
  unkC : UInt8
  /-- Intellectual property (`IPR`). -/
  ipr : UInt8
  deriving Repr, DecidableEq, Inhabited

/-- The method-specific part of a colour specification (T.800 I.5.3.3; ISO 15444-2 M.11.7). -/
inductive ColourMethod where
  /-- METH 1: enumerated colourspace `EnumCS` (16 sRGB, 17 greyscale, 18 sYCC; JPX adds
  others, e.g. 14 CIELab). `params` are the bytes after `EnumCS` (JPX enumerated
  parameters, e.g. for CIELab); empty for JP2. -/
  | enumerated (enumCs : UInt32) (params : ByteRange)
  /-- METH 2 (restricted ICC) or 3 (any ICC, JPX): the profile bytes, passed through. -/
  | icc (restricted : Bool) (profile : ByteRange)
  /-- METH 4 (vendor colour method, JPX): the UUID and data bytes, passed through. -/
  | vendor (data : ByteRange)
  deriving Repr, DecidableEq, Inhabited

/-- Colour specification box (T.800 I.5.3.3). -/
structure ColourSpec where
  /-- Specification method (`METH`, 1…4). -/
  meth : UInt8
  /-- Precedence (`PREC`, a signed byte, stored raw). -/
  prec : UInt8
  /-- Colourspace approximation (`APPROX`). -/
  approx : UInt8
  /-- The method-specific data. -/
  method : ColourMethod
  deriving Repr, DecidableEq, Inhabited

/-- Enumerated colourspace sRGB (T.800 Table I.10). -/
def enumSRGB : UInt32 := 16
/-- Enumerated colourspace greyscale (T.800 Table I.10). -/
def enumGrey : UInt32 := 17
/-- Enumerated colourspace sYCC (T.800 Table I.10). -/
def enumSYCC : UInt32 := 18

/-- The `EnumCS` of an enumerated colour specification. -/
def ColourSpec.enumCs? (c : ColourSpec) : Option UInt32 :=
  match c.method with
  | .enumerated cs _ => some cs
  | _ => none

/-- Palette box (T.800 I.5.3.4). -/
structure Palette where
  /-- Number of entries (`NE`, 1…1024). -/
  ne : Nat
  /-- Number of palette columns (`NPC`, 1…255). -/
  npc : Nat
  /-- `B_i` per column: bit 7 = signed, bits 0–6 = depth − 1 (depth ≤ 38). -/
  bits : Array UInt8
  /-- Entries `C_ji`, row-major: entry `j`, column `i` at index `j * npc + i`. -/
  entries : Array UInt64
  deriving Repr, DecidableEq, Inhabited

/-- One component mapping entry (T.800 I.5.3.5). -/
structure CmapEntry where
  /-- Codestream component (`CMP`). -/
  cmp : UInt16
  /-- Mapping type (`MTYP`: 0 direct, 1 palette). -/
  mtyp : UInt8
  /-- Palette column (`PCOL`). -/
  pcol : UInt8
  deriving Repr, DecidableEq, Inhabited

/-- Component mapping box (T.800 I.5.3.5): one entry per channel. -/
abbrev ComponentMapping := Array CmapEntry

/-- One channel definition (T.800 I.5.3.6). -/
structure ChannelDef where
  /-- Channel index (`Cn`). -/
  cn : UInt16
  /-- Channel type (`Typ`: 0 colour, 1 opacity, 2 premultiplied opacity, 65535 unknown). -/
  typ : UInt16
  /-- Association (`Asoc`: 0 whole image, 65535 none, else colour number). -/
  asoc : UInt16
  deriving Repr, DecidableEq, Inhabited

/-- The JP2 header superbox contents (T.800 I.5.3). -/
structure Jp2Header where
  /-- Image header. -/
  ihdr : Ihdr
  /-- Bits per component (`bpcc`), one byte per component, if present. -/
  bpcc : Option (Array UInt8) := none
  /-- Colour specifications in file order; JP2 readers use the first (`colour?`). -/
  colr : Array ColourSpec := #[]
  /-- Palette. -/
  pclr : Option Palette := none
  /-- Component mapping. -/
  cmap : Option ComponentMapping := none
  /-- Channel definitions. -/
  cdef : Option (Array ChannelDef) := none
  deriving Repr, DecidableEq, Inhabited

/-- The colour specification a JP2 reader uses: the first `colr` box (T.800 I.5.3.3). -/
def Jp2Header.colour? (h : Jp2Header) : Option ColourSpec := h.colr[0]?

/-- The result of `parseFile`: where the codestream is and what the JP2 boxes say. -/
structure Container where
  /-- The codestream bytes in the input (the whole input for a raw codestream, else the
  body of the first `jp2c` box). -/
  codestream : ByteRange
  /-- File type box (`none` for a raw codestream). -/
  fileType : Option FileType := none
  /-- JP2 header (`none` for a raw codestream). -/
  header : Option Jp2Header := none
  deriving Repr, DecidableEq, Inhabited

/-! ## Helpers -/

/-- `malformed` at an offset of the box stage. -/
def malformedAt (pos : Nat) (what : String) : Error := .malformed (.atOffset .box pos) what

/-- Reads `k` bytes big-endian into a `UInt64` (k ≤ 8 by the callers), appending to `acc`. -/
def readBE (r : Reader) (acc : UInt64) : Nat → Except Error (UInt64 × Reader)
  | 0 => .ok (acc, r)
  | k + 1 => do
    let (b, r) ← r.u8
    readBE r ((acc <<< 8) ||| b.toUInt64) k

/-- Reads `n` items with `f`, appending to `acc` (structural recursion on `n`). Callers
check beforehand that the bytes for `n` items are present. -/
def readMany {α : Type} (f : Reader → Except Error (α × Reader)) (r : Reader) (acc : Array α) :
    Nat → Except Error (Array α × Reader)
  | 0 => .ok (acc, r)
  | n + 1 => do
    let (a, r) ← f r
    readMany f r (acc.push a) n

/-- One box: its type, the offset of its `LBox` field, and a sub-reader over its body. -/
structure BoxHdr where
  /-- `TBox`. -/
  tbox : UInt32
  /-- Offset of the box in the input. -/
  start : Nat
  /-- Reader over the box contents (after `LBox`, `TBox` and any `XLBox`). -/
  body : Reader

/-- Reads one box header and splits off its body (T.800 I.4). `LBox = 0` extends the box to
the end of the enclosing reader; `LBox = 1` reads `XLBox`; `LBox ∈ 2…7` and `XLBox < 16` are
malformed; a body running past the end is `truncated`. -/
def readBox (r : Reader) : Except Error (BoxHdr × Reader) := do
  let start := r.pos
  let (lbox, r) ← r.u32be
  let (tbox, r) ← r.u32be
  let (bodyLen, r) ←
    if lbox == 0 then pure (r.remaining, r)
    else if lbox == 1 then do
      let (xl, r) ← r.u64be
      if xl < 16 then throw (malformedAt start s!"XLBox {xl} < 16")
      pure (xl.toNat - 16, r)
    else if lbox < 8 then throw (malformedAt start s!"LBox {lbox} in 2..7")
    else pure (lbox.toNat - 8, r)
  match r.take bodyLen with
  | .ok (body, r) => return ({ tbox, start, body }, r)
  | .error _ =>
    throw (.truncated (.atOffset .box start)
      s!"box '{typeName tbox}' body of {bodyLen} bytes, {r.remaining} left")

/-! ## Boxes of the JP2 header -/

/-- Parses an `ihdr` body (T.800 I.5.3.1): exactly 14 bytes; `HEIGHT`, `WIDTH`, `NC` ≥ 1
(`NC` ≤ `maxComponents`); `BPC` = 255 or depth ≤ 38. -/
def parseIhdr (L : Limits) (b : BoxHdr) : Except Error Ihdr := do
  let r := b.body
  if r.remaining != 14 then
    throw (malformedAt b.start s!"ihdr of {r.remaining} bytes, expected 14")
  let (height, r) ← r.u32be
  let (width, r) ← r.u32be
  let (nc, r) ← r.u16be
  let (bpc, r) ← r.u8
  let (c, r) ← r.u8
  let (unkC, r) ← r.u8
  let (ipr, _) ← r.u8
  if height == 0 || width == 0 || nc == 0 then
    throw (malformedAt b.start s!"ihdr: zero height, width or NC")
  L.check (.atOffset .box b.start) .components nc.toNat
  if bpc != 255 && (bpc &&& 0x7F) + 1 > 38 then
    throw (malformedAt b.start s!"ihdr: BPC {bpc} depth > 38")
  return { height, width, nc, bpc, c, unkC, ipr }

/-- Parses a `bpcc` body (T.800 I.5.3.2): one `B_i` per component, each depth ≤ 38. The
count is the body length (checked against `ihdr.NC` after the header). -/
def parseBpcc (b : BoxHdr) : Except Error (Array UInt8) := do
  let n := b.body.remaining
  let (bs, _) ← readMany Reader.u8 b.body (Array.emptyWithCapacity n) n
  if bs.any (fun x => (x &&& 0x7F) + 1 > 38) then
    throw (malformedAt b.start "bpcc: depth > 38")
  return bs

/-- Parses a `colr` body (T.800 I.5.3.3). `none` for an unknown METH (ignored, as
OpenJPEG). METH 1 needs `EnumCS`; the rest of the body is passed through as a range. -/
def parseColr (b : BoxHdr) : Except Error (Option ColourSpec) := do
  let r := b.body
  if r.remaining < 3 then throw (malformedAt b.start "colr shorter than 3 bytes")
  let (meth, r) ← r.u8
  let (prec, r) ← r.u8
  let (approx, r) ← r.u8
  match meth with
  | 1 =>
    if r.remaining < 4 then throw (malformedAt b.start "colr METH 1 without EnumCS")
    let (cs, r) ← r.u32be
    return some { meth, prec, approx, method := .enumerated cs ⟨r.pos, r.remaining⟩ }
  | 2 => return some { meth, prec, approx, method := .icc true ⟨r.pos, r.remaining⟩ }
  | 3 => return some { meth, prec, approx, method := .icc false ⟨r.pos, r.remaining⟩ }
  | 4 => return some { meth, prec, approx, method := .vendor ⟨r.pos, r.remaining⟩ }
  | _ => return none

/-- Bytes per palette entry of a column with `B_i` = `bi` (T.800 I.5.3.4: ⌈depth / 8⌉). -/
def entryBytes (bi : UInt8) : Nat := ((bi &&& 0x7F).toNat + 1 + 7) / 8

/-- Parses a `pclr` body (T.800 I.5.3.4). `NE` ∈ 1…1024 and ≤ `maxPaletteEntries`,
`NPC` ≥ 1, every depth ≤ 38; the body must hold all `NE × NPC` entries before they are
read. -/
def parsePclr (L : Limits) (b : BoxHdr) : Except Error Palette := do
  let r := b.body
  let loc := Location.atOffset .box b.start
  let (ne16, r) ← r.u16be
  let (npc8, r) ← r.u8
  let ne := ne16.toNat
  let npc := npc8.toNat
  if ne == 0 || ne > 1024 then throw (malformedAt b.start s!"pclr: NE {ne} not in 1..1024")
  L.check loc .paletteEntries ne
  if npc == 0 then throw (malformedAt b.start "pclr: NPC = 0")
  if r.remaining < npc then throw (.truncated loc "pclr: B_i")
  let (bits, r) ← readMany Reader.u8 r (Array.emptyWithCapacity npc) npc
  if bits.any (fun x => (x &&& 0x7F) + 1 > 38) then
    throw (malformedAt b.start "pclr: depth > 38")
  let rowBytes := bits.foldl (fun s x => s + entryBytes x) 0
  if r.remaining < ne * rowBytes then throw (.truncated loc "pclr: entries")
  let readRow (r : Reader) (acc : Array UInt64) : Except Error (Array UInt64 × Reader) :=
    bits.foldlM (fun (acc, r) bi => do
      let (v, r) ← readBE r 0 (entryBytes bi)
      pure (acc.push v, r)) (acc, r)
  let rec rows (r : Reader) (acc : Array UInt64) : Nat → Except Error (Array UInt64 × Reader)
    | 0 => .ok (acc, r)
    | k + 1 => do
      let (acc, r) ← readRow r acc
      rows r acc k
  let (entries, _) ← rows r (Array.emptyWithCapacity (ne * npc)) ne
  return { ne, npc, bits, entries }

/-- Reads one `cmap` entry. -/
def readCmapEntry (r : Reader) : Except Error (CmapEntry × Reader) := do
  let (cmp, r) ← r.u16be
  let (mtyp, r) ← r.u8
  let (pcol, r) ← r.u8
  return ({ cmp, mtyp, pcol }, r)

/-- Parses a `cmap` body (T.800 I.5.3.5): 4 bytes per channel. -/
def parseCmap (b : BoxHdr) : Except Error ComponentMapping := do
  let n := b.body.remaining
  if n % 4 != 0 then throw (malformedAt b.start s!"cmap of {n} bytes, not a multiple of 4")
  let (es, _) ← readMany readCmapEntry b.body (Array.emptyWithCapacity (n / 4)) (n / 4)
  return es

/-- Reads one `cdef` entry. -/
def readCdefEntry (r : Reader) : Except Error (ChannelDef × Reader) := do
  let (cn, r) ← r.u16be
  let (typ, r) ← r.u16be
  let (asoc, r) ← r.u16be
  return ({ cn, typ, asoc }, r)

/-- Parses a `cdef` body (T.800 I.5.3.6): `N` ≥ 1, then `N` entries of 6 bytes, which must
fit in the body. -/
def parseCdef (b : BoxHdr) : Except Error (Array ChannelDef) := do
  let (n16, r) ← b.body.u16be
  let n := n16.toNat
  if n == 0 then throw (malformedAt b.start "cdef: N = 0")
  if r.remaining < 6 * n then throw (.truncated (.atOffset .box b.start) "cdef: entries")
  let (es, _) ← readMany readCdefEntry r (Array.emptyWithCapacity n) n
  return es

/-- The JP2 header being accumulated while reading `jp2h`. -/
structure HdrAcc where
  /-- First `ihdr`. -/
  ihdr : Option Ihdr := none
  /-- First `bpcc` (with its box offset). -/
  bpcc : Option (Array UInt8 × Nat) := none
  /-- `colr` boxes. -/
  colr : Array ColourSpec := #[]
  /-- `pclr`. -/
  pclr : Option Palette := none
  /-- `cmap`. -/
  cmap : Option ComponentMapping := none
  /-- `cdef`. -/
  cdef : Option (Array ChannelDef) := none

/-- Adds one box of `jp2h` to the accumulator. -/
def addHeaderBox (L : Limits) (acc : HdrAcc) (b : BoxHdr) : Except Error HdrAcc := do
  let dup : Except Error HdrAcc :=
    throw (malformedAt b.start s!"duplicate '{typeName b.tbox}' box")
  if b.tbox == tIhdr then
    if acc.ihdr.isSome then return acc
    return { acc with ihdr := some (← parseIhdr L b) }
  else if b.tbox == tBpcc then
    if acc.bpcc.isSome then return acc
    return { acc with bpcc := some (← parseBpcc b, b.start) }
  else if b.tbox == tColr then
    if acc.colr.isEmpty then
      match ← parseColr b with
      | some c => return { acc with colr := acc.colr.push c }
      | none => return acc
    else
      -- Later `colr` boxes do not affect a JP2 reader: keep the well-formed ones.
      match parseColr b with
      | .ok (some c) => return { acc with colr := acc.colr.push c }
      | _ => return acc
  else if b.tbox == tPclr then
    if acc.pclr.isSome then dup else return { acc with pclr := some (← parsePclr L b) }
  else if b.tbox == tCmap then
    if acc.cmap.isSome then dup else return { acc with cmap := some (← parseCmap b) }
  else if b.tbox == tCdef then
    if acc.cdef.isSome then dup else return { acc with cdef := some (← parseCdef b) }
  else
    -- `res ` superbox (I.5.3.7) and unknown boxes: skipped.
    return acc

/-- Reads the boxes of `jp2h` (fuel `n`; `count` boxes read so far in the file, checked
against `maxBoxes`). Returns the accumulator and the new count. -/
def headerLoop (L : Limits) (r : Reader) (acc : HdrAcc) (count : Nat) :
    Nat → Except Error (HdrAcc × Nat)
  | 0 =>
    if r.atEnd then .ok (acc, count)
    else .error (.limitExceeded (.atOffset .box r.pos) .boxes (count + 1) L.maxBoxes)
  | n + 1 =>
    if r.atEnd then .ok (acc, count) else do
      L.check (.atOffset .box r.pos) .boxes (count + 1)
      let (b, r) ← readBox r
      let acc ← addHeaderBox L acc b
      headerLoop L r acc (count + 1) n

/-- Parses a `jp2h` superbox (depth 1, checked against `maxBoxDepth`): requires `ihdr`; a
`bpcc` must have `NC` entries; a `cmap` requires a `pclr`. -/
def parseJp2h (L : Limits) (b : BoxHdr) (count : Nat) : Except Error (Jp2Header × Nat) := do
  L.check (.atOffset .box b.start) .boxDepth 1
  let (acc, count) ← headerLoop L b.body {} count (L.maxBoxes + 1)
  let some ihdr := acc.ihdr | throw (malformedAt b.start "jp2h without ihdr")
  let bpcc ← match acc.bpcc with
    | none => pure none
    | some (bs, pos) =>
      if bs.size != ihdr.nc.toNat then
        throw (malformedAt pos s!"bpcc of {bs.size} entries, NC = {ihdr.nc}")
      else pure (some bs)
  if acc.cmap.isSome && acc.pclr.isNone then
    throw (malformedAt b.start "cmap without pclr")
  return ({ ihdr, bpcc, colr := acc.colr, pclr := acc.pclr, cmap := acc.cmap,
            cdef := acc.cdef }, count)

/-! ## File level -/

/-- Parses an `ftyp` body (T.800 I.5.2): `BR`, `MinV`, then 4-byte `CL` entries. -/
def parseFtyp (b : BoxHdr) : Except Error FileType := do
  let n := b.body.remaining
  if n < 8 || n % 4 != 0 then throw (malformedAt b.start s!"ftyp of {n} bytes")
  let (brand, r) ← b.body.u32be
  let (minorVersion, r) ← r.u32be
  let k := (n - 8) / 4
  let (compat, _) ← readMany Reader.u32be r (Array.emptyWithCapacity k) k
  return { brand, minorVersion, compat }

/-- Reads the top-level boxes after `ftyp` up to the first `jp2c` (fuel `n`; `count` boxes
so far). Returns the header and the codestream range. A `jp2c` before `jp2h` and a file
without `jp2c` are malformed. -/
def topLoop (L : Limits) (r : Reader) (hdr : Option Jp2Header) (count : Nat) :
    Nat → Except Error (Jp2Header × ByteRange)
  | 0 =>
    if r.atEnd then .error (malformedAt r.pos "no jp2c box")
    else .error (.limitExceeded (.atOffset .box r.pos) .boxes (count + 1) L.maxBoxes)
  | n + 1 =>
    if r.atEnd then .error (malformedAt r.pos "no jp2c box") else do
      L.check (.atOffset .box r.pos) .boxes (count + 1)
      let (b, r) ← readBox r
      if b.tbox == tJp2c then
        match hdr with
        | none => throw (malformedAt b.start "jp2c before jp2h")
        | some h => return (h, ⟨b.body.pos, b.body.remaining⟩)
      else if b.tbox == tJp2h && hdr.isNone then
        let (h, count) ← parseJp2h L b (count + 1)
        topLoop L r (some h) count n
      else
        -- Later `jp2h`, metadata (`xml `, `uuid`, `rreq`, …) and unknown boxes: skipped.
        topLoop L r hdr (count + 1) n

/-- Whether the input starts with `FF 4F FF 51` (SOC then SIZ): a raw codestream. -/
def isRawCodestream (d : ByteArray) : Bool :=
  match (Reader.ofByteArray d .box).u32be with
  | .ok (v, _) => v == 0xFF4FFF51
  | .error _ => false

/-- Locates the codestream and reads the JP2 boxes, before the final range check. -/
def parseFileAux (L : Limits) (d : ByteArray) : Except Error Container := do
  L.check (.atOffset .box 0) .inputBytes d.size
  if isRawCodestream d then return { codestream := ⟨0, d.size⟩ }
  let r := Reader.ofByteArray d .box
  let notJp2 := malformedAt 0 "neither a JP2 signature box nor a raw codestream (FF4F FF51)"
  let (sig, r) ← match readBox r with
    | .ok p => pure p
    | .error _ => throw notJp2
  if sig.tbox != tSignature || sig.start != 0 || sig.body.remaining != 4 then throw notJp2
  let (v, _) ← sig.body.u32be
  if v != 0x0D0A870A then throw notJp2
  let (fb, r) ← readBox r
  if fb.tbox != tFtyp then throw (malformedAt fb.start "ftyp must be the second box")
  let ft ← parseFtyp fb
  let (h, cs) ← topLoop L r none 2 (L.maxBoxes + 1)
  return { codestream := cs, fileType := some ft, header := some h }

/-- Parses a JP2/JPX file or recognises a raw codestream (T.800 Annex I): returns the
codestream's byte range in `d` and the JP2 header (`none` for a raw codestream). -/
def parseFile (L : Limits) (d : ByteArray) : Except Error Container := do
  let c ← parseFileAux L d
  if c.codestream.start + c.codestream.len ≤ d.size then return c
  else throw (malformedAt c.codestream.start "codestream range outside the input")

/-- The codestream range returned by `parseFile` lies within the input. -/
theorem parseFile_range {L : Limits} {d : ByteArray} {c : Container}
    (h : parseFile L d = .ok c) : c.codestream.start + c.codestream.len ≤ d.size := by
  unfold parseFile at h
  cases hA : parseFileAux L d with
  | error e => rw [hA] at h; cases h
  | ok c' =>
    rw [hA] at h
    simp only [bind, Except.bind] at h
    split at h
    · rename_i hle; cases h; exact hle
    · cases h

end JPEG2000.Box
