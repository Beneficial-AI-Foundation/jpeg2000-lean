import JPEG2000.Box

/-!
# Unit and corpus tests: JP2/JPX box parser (task 1.2)

Plan.md §1, §3; T.800 Annex I (I.4 box structure, I.5 JP2 boxes). Hand-built files cover the
signature, `ftyp`, `jp2h` (`ihdr`, `colr`, `pclr`, `cmap`, `cdef`, `bpcc`, `res `), `jp2c`,
XL boxes, `LBox = 0`, truncation, bad signatures and raw codestreams. The corpus test parses
the nine JP2 conformance files and compares with values observed with `opj_dump -i`
(OpenJPEG 2.5): image size, component count and precision, and the codestream offset that
`opj_dump` prints as "Start to read j2k main header (N)".
-/

namespace JPEG2000.Tests.Box

open JPEG2000 JPEG2000.Box

/-- Runs one named check, printing a line on failure; returns 1 on failure, 0 on success. -/
def expect (name : String) (ok : Bool) : IO Nat := do
  if ok then return 0
  IO.eprintln s!"  FAIL box: {name}"
  return 1

/-- The error of an `Except`, if any. -/
def err? {ε α : Type} : Except ε α → Option ε
  | .ok _ => none
  | .error e => some e

/-- The value of an `Except`, if any. -/
def ok? {ε α : Type} : Except ε α → Option α
  | .ok a => some a
  | .error _ => none

/-- Big-endian bytes of a 16-bit value. -/
def be16 (v : Nat) : List UInt8 := [(v / 256 % 256).toUInt8, (v % 256).toUInt8]

/-- Big-endian bytes of a 32-bit value. -/
def be32 (v : Nat) : List UInt8 := be16 (v / 65536 % 65536) ++ be16 (v % 65536)

/-- Big-endian bytes of a 64-bit value. -/
def be64 (v : Nat) : List UInt8 := be32 (v / 4294967296) ++ be32 (v % 4294967296)

/-- The bytes of a four-character code. -/
def cc (s : String) : List UInt8 := s.toList.map (·.toNat.toUInt8)

/-- A box with an ordinary 32-bit length. -/
def box (t : String) (body : List UInt8) : List UInt8 := be32 (body.length + 8) ++ cc t ++ body

/-- A box with `LBox = 1` and a 64-bit `XLBox`. -/
def xlBox (t : String) (body : List UInt8) : List UInt8 :=
  be32 1 ++ cc t ++ be64 (body.length + 16) ++ body

/-- A box with `LBox = 0` (to the end of the file). -/
def box0 (t : String) (body : List UInt8) : List UInt8 := be32 0 ++ cc t ++ body

/-- The signature box. -/
def sig : List UInt8 := box "jP  " [0x0D, 0x0A, 0x87, 0x0A]

/-- A `jp2 ` file type box. -/
def ftyp : List UInt8 := box "ftyp" (cc "jp2 " ++ be32 0 ++ cc "jp2 ")

/-- An `ihdr` box. -/
def ihdr (h w nc bpc : Nat) : List UInt8 :=
  box "ihdr" (be32 h ++ be32 w ++ be16 nc ++ [bpc.toUInt8, 7, 0, 0])

/-- An enumerated `colr` box. -/
def colrEnum (cs : Nat) : List UInt8 := box "colr" ([1, 0, 0] ++ be32 cs)

/-- A tiny codestream prefix (SOC, start of SIZ). -/
def cs : List UInt8 := [0xFF, 0x4F, 0xFF, 0x51, 0x00, 0x29]

/-- Parses a byte list with default limits. -/
def parse (bs : List UInt8) (L : Limits := {}) : Except Error Container :=
  parseFile L bs.toByteArray

/-- Codestream range of a successful parse. -/
def range? (bs : List UInt8) : Option (Nat × Nat) :=
  (ok? (parse bs)).map fun c => (c.codestream.start, c.codestream.len)

/-- Whether parsing fails with a `malformed` error. -/
def isMalformed (bs : List UInt8) : Bool :=
  match parse bs with
  | .error (.malformed ..) => true
  | _ => false

/-- Whether parsing fails with a `truncated` error. -/
def isTrunc (bs : List UInt8) : Bool :=
  match parse bs with
  | .error e => e.isTruncated
  | _ => false

/-- Whether parsing fails with a `limitExceeded` error of the given kind. -/
def isLimit (bs : List UInt8) (L : Limits) (k : LimitKind) : Bool :=
  match parse bs L with
  | .error (.limitExceeded _ k' _ _) => k' == k
  | _ => false

/-- Header of a successful parse. -/
def hdr? (bs : List UInt8) : Option Jp2Header := (ok? (parse bs)).bind (·.header)

/-- Hand-built files. -/
def unitTests : IO Nat := do
  let mut f := 0
  let jp2h := box "jp2h" (ihdr 4 6 3 7 ++ colrEnum 16)
  let pre := sig ++ ftyp ++ jp2h
  let basic := pre ++ box "jp2c" cs
  f := f + (← expect "basic: range" (range? basic == some (pre.length + 8, cs.length)))
  f := f + (← expect "basic: ihdr"
    ((hdr? basic).map (fun h => (h.ihdr.height, h.ihdr.width, h.ihdr.nc, h.ihdr.bpc, h.ihdr.c))
      == some (4, 6, 3, 7, 7)))
  f := f + (← expect "basic: colr sRGB"
    ((((hdr? basic).bind (·.colour?)).bind (·.enumCs?)) == some enumSRGB))
  f := f + (← expect "basic: ftyp"
    ((((ok? (parse basic)).bind (·.fileType)).map (fun t => (t.brand, t.compat.toList)))
      == some (0x6A703220, [0x6A703220])))
  -- range lands on SOC
  f := f + (← expect "basic: range starts with FF4F"
    (match range? basic with
     | some (s, _) => basic[s]? == some 0xFF && basic[s+1]? == some 0x4F
     | none => false))
  -- XL box and LBox = 0
  f := f + (← expect "XL jp2c" (range? (pre ++ xlBox "jp2c" cs) == some (pre.length + 16, cs.length)))
  f := f + (← expect "XL jp2h"
    (range? (sig ++ ftyp ++ xlBox "jp2h" (ihdr 4 6 3 7 ++ colrEnum 16) ++ box "jp2c" cs)
      == some (pre.length + 8 + 8, cs.length)))
  f := f + (← expect "LBox=0 jp2c" (range? (pre ++ box0 "jp2c" cs) == some (pre.length + 8, cs.length)))
  f := f + (← expect "XLBox < 16" (isMalformed (pre ++ be32 1 ++ cc "jp2c" ++ be64 8 ++ cs)))
  f := f + (← expect "LBox = 5" (isMalformed (pre ++ be32 5 ++ cc "jp2c" ++ cs)))
  -- metadata boxes and trailing data
  f := f + (← expect "xml/uuid skipped, trailing box ignored"
    (range? (sig ++ ftyp ++ box "xml " [1, 2, 3] ++ jp2h ++ box "uuid" (List.replicate 16 0)
      ++ box "jp2c" cs ++ box "xml " [9]) ==
      some (pre.length + 11 + 24 + 8, cs.length)))
  -- truncation
  f := f + (← expect "truncated jp2c" (isTrunc (pre ++ be32 100 ++ cc "jp2c" ++ cs)))
  f := f + (← expect "truncated box header" (isTrunc (pre ++ [0, 0, 0])))
  f := f + (← expect "truncated ihdr in jp2h"
    (isTrunc (sig ++ ftyp ++ be32 60 ++ cc "jp2h" ++ ihdr 4 6 3 7)))
  f := f + (← expect "short ihdr" (isMalformed
    (sig ++ ftyp ++ box "jp2h" (box "ihdr" [0, 0, 0, 4]) ++ box "jp2c" cs)))
  -- signature, ftyp, structure
  f := f + (← expect "bad signature"
    (isMalformed (box "jP  " [0x0D, 0x0A, 0x87, 0x0B] ++ ftyp ++ jp2h ++ box "jp2c" cs)))
  f := f + (← expect "empty input" (isMalformed []))
  f := f + (← expect "garbage" (isMalformed [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]))
  f := f + (← expect "missing ftyp" (isMalformed (sig ++ jp2h ++ box "jp2c" cs)))
  f := f + (← expect "bad ftyp size"
    (isMalformed (sig ++ box "ftyp" (cc "jp2 " ++ be32 0 ++ [1, 2]) ++ jp2h ++ box "jp2c" cs)))
  f := f + (← expect "jp2c before jp2h" (isMalformed (sig ++ ftyp ++ box "jp2c" cs ++ jp2h)))
  f := f + (← expect "no jp2c" (isMalformed pre))
  f := f + (← expect "jp2h without ihdr"
    (isMalformed (sig ++ ftyp ++ box "jp2h" (colrEnum 16) ++ box "jp2c" cs)))
  f := f + (← expect "ihdr NC = 0"
    (isMalformed (sig ++ ftyp ++ box "jp2h" (ihdr 4 6 0 7) ++ box "jp2c" cs)))
  f := f + (← expect "ihdr BPC depth 39"
    (isMalformed (sig ++ ftyp ++ box "jp2h" (ihdr 4 6 1 38) ++ box "jp2c" cs)))
  -- raw codestream
  f := f + (← expect "raw J2K" (range? cs == some (0, cs.length)))
  f := f + (← expect "raw J2K has no header"
    ((ok? (parse cs)).map (fun c => c.header.isNone && c.fileType.isNone) == some true))
  f := f + (← expect "FF4F without SIZ" (isMalformed [0xFF, 0x4F, 0xFF, 0x52, 0, 0]))
  -- colr variants: first wins, unknown METH ignored, ICC range
  let icc : List UInt8 := [10, 20, 30, 40, 50]
  let hICC := hdr? (sig ++ ftyp ++ box "jp2h" (ihdr 4 6 3 7 ++ box "colr" ([2, 0, 0] ++ icc)
    ++ colrEnum 17 ++ box "colr" [9, 0, 0]) ++ box "jp2c" cs)
  let iccStart := 12 + 20 + 8 + 22 + 8 + 3
  f := f + (← expect "colr ICC first, enumerated second, METH 9 ignored"
    ((hICC.map (·.colr.map (·.method))) ==
      some #[.icc true ⟨iccStart, 5⟩, .enumerated enumGrey ⟨iccStart + 5 + 8 + 7, 0⟩]))
  f := f + (← expect "malformed later colr skipped"
    ((hdr? (sig ++ ftyp ++ box "jp2h" (ihdr 4 6 3 7 ++ colrEnum 18 ++ box "colr" [1, 0, 0])
      ++ box "jp2c" cs)).map (·.colr.size) == some 1))
  f := f + (← expect "malformed first colr"
    (isMalformed (sig ++ ftyp ++ box "jp2h" (ihdr 4 6 3 7 ++ box "colr" [1, 0, 0])
      ++ box "jp2c" cs)))
  -- pclr + cmap + cdef + bpcc + res
  let pclr := box "pclr" (be16 2 ++ [2] ++ [7, 0x8F] ++ [1, 0x00, 0x10, 2, 0xFF, 0xFE])
  let cmap := box "cmap" ([0, 0, 1, 0] ++ [0, 0, 1, 1])
  let cdef := box "cdef" (be16 1 ++ be16 0 ++ be16 0 ++ be16 1)
  let bpcc := box "bpcc" [7]
  let res := box "res " (box "resc" (List.replicate 10 0))
  let hP := hdr? (sig ++ ftyp ++ box "jp2h" (ihdr 4 6 1 255 ++ bpcc ++ colrEnum 16 ++ pclr
    ++ cmap ++ cdef ++ res) ++ box "jp2c" cs)
  f := f + (← expect "pclr"
    ((hP.bind (·.pclr)).map (fun p => (p.ne, p.npc, p.bits.toList, p.entries.toList)) ==
      some (2, 2, [7, 0x8F], [1, 0x0010, 2, 0xFFFE])))
  f := f + (← expect "cmap"
    ((hP.bind (·.cmap)).map (·.toList.map (fun e => (e.cmp, e.mtyp, e.pcol)))
      == some [(0, 1, 0), (0, 1, 1)]))
  f := f + (← expect "cdef"
    ((hP.bind (·.cdef)).map (·.toList.map (fun e => (e.cn, e.typ, e.asoc)))
      == some [(0, 0, 1)]))
  f := f + (← expect "bpcc" ((hP.bind (·.bpcc)).map (·.toList) == some [7]))
  f := f + (← expect "bpcc count ≠ NC" (isMalformed
    (sig ++ ftyp ++ box "jp2h" (ihdr 4 6 2 255 ++ bpcc) ++ box "jp2c" cs)))
  f := f + (← expect "cmap without pclr" (isMalformed
    (sig ++ ftyp ++ box "jp2h" (ihdr 4 6 1 7 ++ cmap) ++ box "jp2c" cs)))
  f := f + (← expect "duplicate pclr" (isMalformed
    (sig ++ ftyp ++ box "jp2h" (ihdr 4 6 1 7 ++ pclr ++ pclr) ++ box "jp2c" cs)))
  f := f + (← expect "pclr NE = 1025" (isMalformed
    (sig ++ ftyp ++ box "jp2h" (ihdr 4 6 1 7 ++ box "pclr" (be16 1025 ++ [1, 7])) ++ box "jp2c" cs)))
  f := f + (← expect "pclr NPC = 0" (isMalformed
    (sig ++ ftyp ++ box "jp2h" (ihdr 4 6 1 7 ++ box "pclr" (be16 2 ++ [0])) ++ box "jp2c" cs)))
  f := f + (← expect "pclr depth 39" (isMalformed
    (sig ++ ftyp ++ box "jp2h" (ihdr 4 6 1 7 ++ box "pclr" (be16 1 ++ [1, 38, 0, 0, 0, 0, 0]))
      ++ box "jp2c" cs)))
  f := f + (← expect "pclr 38-bit entries" (((hdr? (sig ++ ftyp ++ box "jp2h" (ihdr 4 6 1 7 ++
      box "pclr" (be16 1 ++ [1, 37, 0x3F, 0xFF, 0xFF, 0xFF, 0xFF])) ++ box "jp2c" cs)).bind
      (·.pclr) |>.map (·.entries.toList)) == some [0x3FFFFFFFFF]))
  f := f + (← expect "pclr entries truncated" (isTrunc
    (sig ++ ftyp ++ box "jp2h" (ihdr 4 6 1 7 ++ box "pclr" (be16 4 ++ [1, 7, 1, 2])) ++ box "jp2c" cs)))
  f := f + (← expect "pclr NE over strict limit"
    (isLimit (sig ++ ftyp ++ box "jp2h" (ihdr 4 6 1 7 ++ box "pclr" (be16 300 ++ [1, 7]))
      ++ box "jp2c" cs) Limits.strict .paletteEntries))
  f := f + (← expect "cdef N = 0" (isMalformed
    (sig ++ ftyp ++ box "jp2h" (ihdr 4 6 1 7 ++ box "cdef" (be16 0)) ++ box "jp2c" cs)))
  f := f + (← expect "cdef entries truncated" (isTrunc
    (sig ++ ftyp ++ box "jp2h" (ihdr 4 6 1 7 ++ box "cdef" (be16 2 ++ List.replicate 6 0))
      ++ box "jp2c" cs)))
  f := f + (← expect "cmap length not multiple of 4" (isMalformed
    (sig ++ ftyp ++ box "jp2h" (ihdr 4 6 1 7 ++ pclr ++ box "cmap" [0, 0, 1]) ++ box "jp2c" cs)))
  -- limits
  let many := sig ++ ftyp ++ jp2h ++ (List.range 70).foldl (fun acc _ => acc ++ box "xml " []) []
    ++ box "jp2c" cs
  f := f + (← expect "maxBoxes (strict)" (isLimit many Limits.strict .boxes))
  f := f + (← expect "many boxes fine with default limits" ((range? many).isSome))
  f := f + (← expect "NC over strict maxComponents"
    (isLimit (sig ++ ftyp ++ box "jp2h" (ihdr 4 6 5 7) ++ box "jp2c" cs) Limits.strict .components))
  f := f + (← expect "maxBoxDepth 0"
    (isLimit basic { maxBoxDepth := 0 } .boxDepth))
  f := f + (← expect "maxInputBytes"
    (isLimit basic { maxInputBytes := 10 } .inputBytes))
  return f

/-- Expected values for one conformance file, observed with `opj_dump -i` (OpenJPEG 2.5):
height `y1`, width `x1`, `numcomps`, `prec` (= BPC + 1, all components equal), the
codestream offset ("Start to read j2k main header (N)") and the codestream length (the
`jp2c` body), plus the first `colr` (`some EnumCS` or `none` for ICC). -/
structure Expected where
  /-- File name. -/
  name : String
  /-- Image height. -/
  height : Nat
  /-- Image width. -/
  width : Nat
  /-- Number of components. -/
  nc : Nat
  /-- Component precision. -/
  prec : Nat
  /-- Offset of the codestream. -/
  csStart : Nat
  /-- Length of the codestream. -/
  csLen : Nat
  /-- First `colr`: `some EnumCS`, or `none` for an ICC profile. -/
  enumCs : Option UInt32

/-- The nine JP2 conformance files (T.803). -/
def expected : List Expected :=
  [ ⟨"file1.jp2", 512, 768, 3, 8, 1277, 649401, some 16⟩,
    ⟨"file2.jp2", 640, 480, 3, 8, 117, 451887, some 18⟩,
    ⟨"file3.jp2", 640, 480, 3, 8, 89, 242124, some 18⟩,
    ⟨"file4.jp2", 512, 768, 1, 8, 89, 220354, some 17⟩,
    ⟨"file5.jp2", 512, 768, 3, 8, 678, 585882, none⟩,
    ⟨"file6.jp2", 512, 768, 1, 12, 89, 394453, some 17⟩,
    ⟨"file7.jp2", 640, 480, 3, 16, 13464, 1354631, none⟩,
    ⟨"file8.jp2", 400, 700, 1, 8, 884, 148825, none⟩,
    ⟨"file9.jp2", 512, 768, 1, 8, 891, 299317, some 16⟩ ]

/-- Directory of the conformance files, relative to the repository root. -/
def corpusDir : System.FilePath := "corpus/files/openjpeg-data/input/conformance"

/-- Checks one parsed conformance file against its expected values. -/
def checkFile (e : Expected) (d : ByteArray) : IO Nat := do
  match parseFile {} d with
  | .error err => expect s!"{e.name}: parse ({err})" false
  | .ok c =>
    let mut f := 0
    f := f + (← expect s!"{e.name}: codestream range"
      (c.codestream.start == e.csStart && c.codestream.len == e.csLen))
    f := f + (← expect s!"{e.name}: starts with FF4F"
      (d[c.codestream.start]? == some 0xFF && d[c.codestream.start + 1]? == some 0x4F))
    match c.header with
    | none => f := f + (← expect s!"{e.name}: header" false)
    | some h =>
      let i := h.ihdr
      f := f + (← expect s!"{e.name}: ihdr"
        (i.height.toNat == e.height && i.width.toNat == e.width && i.nc.toNat == e.nc &&
          (i.bpc &&& 0x7F).toNat + 1 == e.prec && i.bpc &&& 0x80 == 0))
      f := f + (← expect s!"{e.name}: first colr"
        (match h.colour? with
         | some cs => match e.enumCs with
           | some v => cs.enumCs? == some v
           | none => cs.meth == 2
         | none => false))
    return f

/-- Parses the nine conformance files; skips (0 failures) when the corpus is absent. -/
def corpusTests : IO Nat := do
  if !(← corpusDir.pathExists) then
    IO.println s!"  box: corpus not present at {corpusDir}, skipping corpus tests"
    return 0
  let mut f := 0
  for e in expected do
    let p := corpusDir / e.name
    if !(← p.pathExists) then
      IO.println s!"  box: {p} missing, skipped"
      continue
    f := f + (← checkFile e (← IO.FS.readBinFile p))
  -- file9: palette and component mapping (T.803)
  let p9 := corpusDir / "file9.jp2"
  if ← p9.pathExists then
    let d ← IO.FS.readBinFile p9
    f := f + (← expect "file9: pclr 256×3, cmap 3 entries"
      (match (ok? (parseFile {} d)).bind (·.header) with
       | some h => (h.pclr.map (fun p => (p.ne, p.npc, p.entries.size)) == some (256, 3, 768)) &&
           (h.cmap.map (·.size) == some 3)
       | none => false))
  let p2 := corpusDir / "file2.jp2"
  if ← p2.pathExists then
    let d ← IO.FS.readBinFile p2
    f := f + (← expect "file2: cdef 3 entries"
      (((((ok? (parseFile {} d)).bind (·.header)).bind (·.cdef)).map (·.size)) == some 3))
  return f

/-- Runs the suite; returns the number of failures. -/
def run : IO Nat := do
  return (← unitTests) + (← corpusTests)

end JPEG2000.Tests.Box
