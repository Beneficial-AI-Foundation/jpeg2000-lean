import JPEG2000.Marker

/-!
# Marker-segment serialiser (Plan.md §4 M1, §5.1, §5.3; T.800 Annex A)

Task 1.6: the inverse of the per-segment parsers of `JPEG2000.Marker`. Each `serializeX`
produces the segment **body** (the bytes after `Lxxx`, T.800 A.1.4), i.e. exactly what
`parseX` consumes; `segment` adds the 2-byte marker and the 2-byte length `Lxxx`.

Field layouts follow T.800 A.5.1 (SIZ, Tables A.9–A.11), A.6.1 (COD, Tables A.12–A.21),
A.6.2 (COC, Tables A.22–A.23), A.6.3 (RGN, Tables A.24–A.26), A.6.4 (QCD, Tables
A.27–A.30), A.6.5 (QCC, Table A.31), A.6.6 (POC, Table A.32), A.9.1 (CRG, Table A.40) and
A.9.2 (COM, Table A.41). All values are big-endian (T.800 A.1). Component indices are 1 byte
when `Csiz < 257` and 2 bytes otherwise.

Each body is first built as a `List UInt8` (`…Bytes`), which is what the round-trip proofs
of `Spec.MarkerRoundTrip` reason about; `serializeX` packs it into a `ByteArray`. This is a
reference encoder for tests and proofs only (Plan.md §5.3), not a fast path.
-/

namespace JPEG2000.Encode.Marker

open JPEG2000.Marker

/-! ## Byte helpers -/

/-- Big-endian bytes of a 16-bit value (T.800 A.1). -/
def be16 (v : UInt16) : List UInt8 := [(v >>> 8).toUInt8, v.toUInt8]

/-- Big-endian bytes of a 32-bit value (T.800 A.1). -/
def be32 (v : UInt32) : List UInt8 :=
  [(v >>> 24).toUInt8, (v >>> 16).toUInt8, (v >>> 8).toUInt8, v.toUInt8]

/-- A component index: 1 byte when `Csiz < 257`, else 2 bytes (T.800 A.6.2). -/
def compIndex (csiz : Nat) (c : UInt16) : List UInt8 :=
  if csiz < 257 then [c.toUInt8] else be16 c

/-- Packs a byte list into a `ByteArray`. -/
def pack (l : List UInt8) : ByteArray := ⟨l.toArray⟩

/-! ## Segment bodies as byte lists -/

/-- `Ssiz`, `XRsiz`, `YRsiz` of one component (T.800 Table A.9). -/
def componentBytes (c : Component) : List UInt8 := [c.ssiz, c.dx, c.dy]

/-- SIZ body (T.800 A.5.1): `Rsiz`, the eight 32-bit grid fields, `Csiz`, components. -/
def sizBytes (s : SIZ) : List UInt8 :=
  be16 s.rsiz ++ be32 s.xsiz ++ be32 s.ysiz ++ be32 s.xosiz ++ be32 s.yosiz ++
    be32 s.xtsiz ++ be32 s.ytsiz ++ be32 s.xtosiz ++ be32 s.ytosiz ++
    be16 s.components.size.toUInt16 ++ s.components.toList.flatMap componentBytes

/-- The precinct-size bytes of a coding style (empty when none are defined). -/
def precinctBytes : Option (Array Precinct) → List UInt8
  | none => []
  | some ps => ps.toList.flatMap fun p => [p.toUInt8]

/-- `SPcod`/`SPcoc` (T.800 Table A.15). -/
def codingStyleBytes (s : CodingStyle) : List UInt8 :=
  [s.levels, s.xcb, s.ycb, s.cbStyle, s.transform.toUInt8] ++ precinctBytes s.precincts

/-- COD body (T.800 A.6.1): `Scod`, `SGcod`, `SPcod`. -/
def codBytes (c : COD) : List UInt8 :=
  [c.scod, c.progression.toUInt8] ++ be16 c.layers ++ [if c.mct then 1 else 0] ++
    codingStyleBytes c.style

/-- COC body (T.800 A.6.2): `Ccoc`, `Scoc`, `SPcoc`. -/
def cocBytes (csiz : Nat) (c : COC) : List UInt8 :=
  compIndex csiz c.component ++ [if c.style.precincts.isSome then 1 else 0] ++
    codingStyleBytes c.style

/-- `SPqcd`/`SPqcc` (T.800 Tables A.29–A.30). -/
def quantBytes : Quantization → List UInt8
  | .none es => es.toList.map (· * 8)
  | .derived b => be16 b.toUInt16
  | .expounded ss => ss.toList.flatMap fun s => be16 s.toUInt16

/-- QCD body (T.800 A.6.4): `Sqcd`, `SPqcd`. -/
def qcdBytes (q : QCD) : List UInt8 := [q.sqcd] ++ quantBytes q.quant

/-- QCC body (T.800 A.6.5): `Cqcc`, `Sqcc`, `SPqcc`. -/
def qccBytes (csiz : Nat) (q : QCC) : List UInt8 :=
  compIndex csiz q.component ++ qcdBytes q.params

/-- RGN body (T.800 A.6.3): `Crgn`, `Srgn = 0`, `SPrgn`. -/
def rgnBytes (csiz : Nat) (g : RGN) : List UInt8 :=
  compIndex csiz g.component ++ [0, g.shift]

/-- One POC entry (T.800 Table A.32). -/
def pocEntryBytes (csiz : Nat) (e : PocEntry) : List UInt8 :=
  [e.resStart] ++ compIndex csiz e.compStart ++ be16 e.layerEnd ++ [e.resEnd] ++
    compIndex csiz e.compEndRaw ++ [e.order.toUInt8]

/-- POC body (T.800 A.6.6). -/
def pocBytes (csiz : Nat) (p : POC) : List UInt8 :=
  p.entries.toList.flatMap (pocEntryBytes csiz)

/-- COM body (T.800 A.9.2): `Rcom`, `Ccom`. -/
def comBytes (c : COM) : List UInt8 := be16 c.rcom ++ c.data.data.toList

/-- One `(Xcrg, Ycrg)` pair. -/
def crgPairBytes (p : UInt16 × UInt16) : List UInt8 := be16 p.1 ++ be16 p.2

/-- CRG body (T.800 A.9.1). -/
def crgBytes (c : CRG) : List UInt8 := c.offsets.toList.flatMap crgPairBytes

/-! ## Serialisers -/

/-- Serialises a SIZ body. -/
def serializeSIZ (s : SIZ) : ByteArray := pack (sizBytes s)
/-- Serialises a COD body. -/
def serializeCOD (c : COD) : ByteArray := pack (codBytes c)
/-- Serialises a COC body (`csiz` selects the width of `Ccoc`). -/
def serializeCOC (csiz : Nat) (c : COC) : ByteArray := pack (cocBytes csiz c)
/-- Serialises a QCD body. -/
def serializeQCD (q : QCD) : ByteArray := pack (qcdBytes q)
/-- Serialises a QCC body (`csiz` selects the width of `Cqcc`). -/
def serializeQCC (csiz : Nat) (q : QCC) : ByteArray := pack (qccBytes csiz q)
/-- Serialises an RGN body (`csiz` selects the width of `Crgn`). -/
def serializeRGN (csiz : Nat) (g : RGN) : ByteArray := pack (rgnBytes csiz g)
/-- Serialises a POC body (`csiz` selects the width of `CSpoc`/`CEpoc`). -/
def serializePOC (csiz : Nat) (p : POC) : ByteArray := pack (pocBytes csiz p)
/-- Serialises a COM body. -/
def serializeCOM (c : COM) : ByteArray := pack (comBytes c)
/-- Serialises a CRG body. -/
def serializeCRG (c : CRG) : ByteArray := pack (crgBytes c)

/-- A whole marker segment (T.800 A.1.4): the marker, `Lxxx` = body size + 2, the body.
The body must be at most 65533 bytes for `Lxxx` to be representable. -/
def segment (code : UInt16) (body : ByteArray) : ByteArray :=
  pack (be16 code ++ be16 (body.size + 2).toUInt16) ++ body

end JPEG2000.Encode.Marker
