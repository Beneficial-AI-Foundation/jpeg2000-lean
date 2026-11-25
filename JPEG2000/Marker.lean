import JPEG2000.Error
import JPEG2000.Limits
import JPEG2000.Bytes

/-!
# Main-header marker segments (Plan.md §3 rules 1–3, §4 S2/S3, §5.1; T.800 Annex A)

Task 1.3: typed records for the marker segments of a codestream's main header and one
simple, total parser per segment type, plus the main-header driver.

* **Segment parsers** (`parseSIZ`, `parseCOD`, `parseCOC`, `parseQCD`, `parseQCC`,
  `parseRGN`, `parsePOC`, `parseCOM`, `parseCRG`) each take a `Reader` over exactly the
  segment **body** (the bytes after the 2-byte length field `Lxxx`, T.800 A.1.4) and must
  consume all of it: trailing bytes are `Error.malformed`. The records hold exactly the
  fields of the syntax of T.800 A.5.1 (SIZ), A.6.1 (COD), A.6.2 (COC), A.6.3 (RGN),
  A.6.4 (QCD), A.6.5 (QCC), A.6.6 (POC), A.9.1 (CRG), A.9.2 (COM), so that the serialiser of
  task 1.6 is a clean inverse (a field the parser interprets, such as `Ssiz`, is stored in a
  form from which the byte is recomputed uniquely; `CEpoc`'s "0 means 256/16384" is stored
  raw and interpreted by `PocEntry.compEnd`).
* The component index fields (`Ccoc`, `Cqcc`, `Crgn`, `CSpoc`, `CEpoc`) are 1 byte when
  `Csiz < 257` and 2 bytes otherwise (T.800 Tables A.20, A.27, A.25, A.32), so those parsers
  take `csiz` from SIZ.
* **Driver** `parseMainHeader`: `SOC`, then `SIZ` (required, immediately after `SOC`,
  T.800 A.3), then marker segments until the first `SOT` (`0xFF90`), which is left unread.
  The loop carries fuel = the remaining byte count; each iteration consumes at least the
  2-byte marker (Plan.md §3 rule 2). Exactly one `COD` and one `QCD` are required; `COC`,
  `QCC`, `RGN`, `POC`, `COM` are collected in stream order (precedence between them is
  resolved later, task 1.5). `TLM`/`PLM`/`PPM` are kept as raw body ranges for task 1.4;
  `CAP` (Part 2/15) is tolerated and kept raw.

Limits (Plan.md §3 rule 3), each checked before the corresponding array is read:
`Csiz ≤ maxComponents`, decomposition levels ≤ `maxDecompLevels`, layers ≤ `maxLayers`,
`POC` entries (per segment and in total) ≤ `maxPocEntries`.

Strictness choices (Part 1 only; recorded for the ledger):
* **Lenient:** unknown marker segments in the main header are kept (`MainHeader.unknown`)
  rather than rejected; markers `0xFF30–0xFF3F` (no parameters, T.800 A.1.4) are skipped;
  `COM.rcom` values other than 0/1 are kept; `MCT = 1` with `Csiz < 3`, `POC` component
  ranges beyond `Csiz`, and band counts vs. decomposition levels are not checked here
  (cross-segment validation is task 1.5).
* **Strict:** reserved bits of `Scod`, `Scoc`, `Sqcd` style values and the low 3 bits of
  the "no quantisation" exponent bytes must be zero; `PPx`/`PPy` = 0 only at resolution 0
  (as OpenJPEG); a second `SIZ`, `COD`, `QCD`, `CAP` or `CRG`, and `SOC`/`SOD`/`EOC`/`SOP`/
  `EPH`/`PLT`/`PPT` in the main header are malformed.
* **Unsupported** (Part 2/15, Plan.md §1): code-block style bit 6 (HT), wavelet
  transforms other than 9/7 and 5/3, `SGcod` MCT values > 1, `Srgn ≠ 0`.
-/

namespace JPEG2000.Marker

open JPEG2000.Bytes

/-! ## Marker codes (T.800 A.2, Table A.2) -/

/-! Marker codes (T.800 Table A.2). -/
namespace Code
/-- Start of codestream. -/
def SOC : UInt16 := 0xFF4F
/-- Capabilities (Part 2/15; tolerated). -/
def CAP : UInt16 := 0xFF50
/-- Image and tile size. -/
def SIZ : UInt16 := 0xFF51
/-- Coding style default. -/
def COD : UInt16 := 0xFF52
/-- Coding style component. -/
def COC : UInt16 := 0xFF53
/-- Tile-part lengths. -/
def TLM : UInt16 := 0xFF55
/-- Packet length, main header. -/
def PLM : UInt16 := 0xFF57
/-- Packet length, tile-part header. -/
def PLT : UInt16 := 0xFF58
/-- Quantisation default. -/
def QCD : UInt16 := 0xFF5C
/-- Quantisation component. -/
def QCC : UInt16 := 0xFF5D
/-- Region of interest. -/
def RGN : UInt16 := 0xFF5E
/-- Progression order change. -/
def POC : UInt16 := 0xFF5F
/-- Packed packet headers, main header. -/
def PPM : UInt16 := 0xFF60
/-- Packed packet headers, tile-part header. -/
def PPT : UInt16 := 0xFF61
/-- Component registration. -/
def CRG : UInt16 := 0xFF63
/-- Comment. -/
def COM : UInt16 := 0xFF64
/-- Start of tile-part. -/
def SOT : UInt16 := 0xFF90
/-- Start of packet. -/
def SOP : UInt16 := 0xFF91
/-- End of packet header. -/
def EPH : UInt16 := 0xFF92
/-- Start of data. -/
def SOD : UInt16 := 0xFF93
/-- End of codestream. -/
def EOC : UInt16 := 0xFFD9
end Code

/-! ## Typed records -/

/-- One component of SIZ (T.800 A.5.1, Table A.11): `Ssiz` split into sign and bit depth,
and the sub-sampling factors `XRsiz`, `YRsiz`. -/
structure Component where
  /-- `Ssiz` bit 7: samples are signed. -/
  signed : Bool
  /-- Bit depth 1…38 (`Ssiz` bits 0–6 plus one). -/
  depth : UInt8
  /-- Horizontal separation `XRsiz`, 1…255. -/
  dx : UInt8
  /-- Vertical separation `YRsiz`, 1…255. -/
  dy : UInt8
  deriving Repr, DecidableEq, Inhabited

/-- The `Ssiz` byte of a component (T.800 Table A.11). -/
def Component.ssiz (c : Component) : UInt8 :=
  (if c.signed then 0x80 else 0) + (c.depth - 1)

/-- Image and tile size, SIZ (T.800 A.5.1). `Csiz` is `components.size`; `Lsiz` is
`38 + 3·Csiz`. -/
structure SIZ where
  /-- Capabilities `Rsiz` (kept raw). -/
  rsiz : UInt16
  /-- Reference grid width `Xsiz`. -/
  xsiz : UInt32
  /-- Reference grid height `Ysiz`. -/
  ysiz : UInt32
  /-- Image area horizontal offset `XOsiz`. -/
  xosiz : UInt32
  /-- Image area vertical offset `YOsiz`. -/
  yosiz : UInt32
  /-- Tile width `XTsiz`. -/
  xtsiz : UInt32
  /-- Tile height `YTsiz`. -/
  ytsiz : UInt32
  /-- Tile grid horizontal offset `XTOsiz`. -/
  xtosiz : UInt32
  /-- Tile grid vertical offset `YTOsiz`. -/
  ytosiz : UInt32
  /-- Per-component `Ssiz`, `XRsiz`, `YRsiz`; `Csiz` = its size (1…16384). -/
  components : Array Component
  deriving Repr, DecidableEq, Inhabited

/-- Number of components `Csiz`. -/
def SIZ.csiz (s : SIZ) : Nat := s.components.size

/-- Progression order (T.800 Table A.16). -/
inductive Progression where
  /-- Layer-resolution-component-position (0). -/
  | lrcp
  /-- Resolution-layer-component-position (1). -/
  | rlcp
  /-- Resolution-position-component-layer (2). -/
  | rpcl
  /-- Position-component-resolution-layer (3). -/
  | pcrl
  /-- Component-position-resolution-layer (4). -/
  | cprl
  deriving Repr, DecidableEq, Inhabited

/-- Decodes a progression order byte (values 0…4). -/
def Progression.ofUInt8? : UInt8 → Option Progression
  | 0 => some .lrcp
  | 1 => some .rlcp
  | 2 => some .rpcl
  | 3 => some .pcrl
  | 4 => some .cprl
  | _ => none

/-- The byte value of a progression order. -/
def Progression.toUInt8 : Progression → UInt8
  | .lrcp => 0
  | .rlcp => 1
  | .rpcl => 2
  | .pcrl => 3
  | .cprl => 4

/-- Wavelet transform (T.800 Table A.20). -/
inductive Transform where
  /-- 9-7 irreversible filter (0). -/
  | irreversible97
  /-- 5-3 reversible filter (1). -/
  | reversible53
  deriving Repr, DecidableEq, Inhabited

/-- The byte value of a transform. -/
def Transform.toUInt8 : Transform → UInt8
  | .irreversible97 => 0
  | .reversible53 => 1

/-- Precinct size exponents of one resolution level (T.800 Table A.21): `PPx` in bits
0–3, `PPy` in bits 4–7. Each is < 16. -/
structure Precinct where
  /-- Width exponent `PPx`. -/
  ppx : UInt8
  /-- Height exponent `PPy`. -/
  ppy : UInt8
  deriving Repr, DecidableEq, Inhabited

/-- The byte of a precinct size. -/
def Precinct.toUInt8 (p : Precinct) : UInt8 := p.ppx + 16 * p.ppy

/-- The default precinct size `PPx = PPy = 15` (T.800 A.6.1, no precincts defined). -/
def Precinct.default : Precinct := ⟨15, 15⟩

/-- Coding style parameters shared by COD (`SPcod`) and COC (`SPcoc`)
(T.800 Tables A.15, A.18–A.21), with the precinct flag (`Scod`/`Scoc` bit 0). -/
structure CodingStyle where
  /-- Number of decomposition levels `NL`, 0…32. -/
  levels : UInt8
  /-- Code-block width field `xcb` (exponent − 2); `xcb ≤ 8`, `xcb + ycb ≤ 8`. -/
  xcb : UInt8
  /-- Code-block height field `ycb` (exponent − 2). -/
  ycb : UInt8
  /-- Code-block style (T.800 Table A.19), bits 0–5. -/
  cbStyle : UInt8
  /-- Wavelet transform. -/
  transform : Transform
  /-- Precinct sizes for resolutions 0…NL when `Scod`/`Scoc` bit 0 is set (`levels + 1`
  entries), else `none` (maximal precincts, `PPx = PPy = 15`). -/
  precincts : Option (Array Precinct)
  deriving Repr, DecidableEq, Inhabited

namespace CodingStyle
/-- Code-block width exponent `xcb + 2`. -/
def cbWidthExp (s : CodingStyle) : Nat := s.xcb.toNat + 2
/-- Code-block height exponent `ycb + 2`. -/
def cbHeightExp (s : CodingStyle) : Nat := s.ycb.toNat + 2
/-- Selective arithmetic coding bypass (bit 0). -/
def bypass (s : CodingStyle) : Bool := s.cbStyle &&& 0x01 != 0
/-- Reset of context probabilities on coding-pass boundaries (bit 1). -/
def reset (s : CodingStyle) : Bool := s.cbStyle &&& 0x02 != 0
/-- Termination on each coding pass (bit 2). -/
def termAll (s : CodingStyle) : Bool := s.cbStyle &&& 0x04 != 0
/-- Vertically causal context (bit 3). -/
def vertCausal (s : CodingStyle) : Bool := s.cbStyle &&& 0x08 != 0
/-- Predictable termination (bit 4). -/
def predTerm (s : CodingStyle) : Bool := s.cbStyle &&& 0x10 != 0
/-- Segmentation symbols (bit 5). -/
def segSymbols (s : CodingStyle) : Bool := s.cbStyle &&& 0x20 != 0
/-- The precinct size of resolution `res` (the default 15/15 when none are defined). -/
def precinct (s : CodingStyle) (res : Nat) : Precinct :=
  match s.precincts with
  | none => Precinct.default
  | some ps => ps.getD res Precinct.default
end CodingStyle

/-- Coding style default, COD (T.800 A.6.1). `Scod` bit 0 is `style.precincts.isSome`. -/
structure COD where
  /-- `Scod` bit 1: SOP marker segments may be used. -/
  sop : Bool
  /-- `Scod` bit 2: EPH markers are used. -/
  eph : Bool
  /-- `SGcod` progression order. -/
  progression : Progression
  /-- `SGcod` number of layers, 1…65535. -/
  layers : UInt16
  /-- `SGcod` multiple component transform (0 or 1). -/
  mct : Bool
  /-- `SPcod`. -/
  style : CodingStyle
  deriving Repr, DecidableEq, Inhabited

/-- The `Scod` byte (T.800 Table A.13). -/
def COD.scod (c : COD) : UInt8 :=
  (if c.style.precincts.isSome then 1 else 0) + (if c.sop then 2 else 0) +
    (if c.eph then 4 else 0)

/-- Coding style component, COC (T.800 A.6.2). `Scoc` bit 0 is `style.precincts.isSome`. -/
structure COC where
  /-- `Ccoc` component index (< Csiz). -/
  component : UInt16
  /-- `SPcoc`. -/
  style : CodingStyle
  deriving Repr, DecidableEq, Inhabited

/-- A quantisation step size (T.800 Table A.30): exponent `εb` (5 bits) and mantissa
`μb` (11 bits). -/
structure StepSize where
  /-- Exponent `εb`, < 32. -/
  exponent : UInt8
  /-- Mantissa `μb`, < 2048. -/
  mantissa : UInt16
  deriving Repr, DecidableEq, Inhabited

/-- The 16-bit field of a step size. -/
def StepSize.toUInt16 (s : StepSize) : UInt16 := s.exponent.toUInt16 * 2048 + s.mantissa

/-- Quantisation style and its `SPqcd`/`SPqcc` values (T.800 Tables A.28–A.30). -/
inductive Quantization where
  /-- Style 0, no quantisation: one exponent `εb` (< 32) per sub-band. -/
  | none (exponents : Array UInt8)
  /-- Style 1, scalar derived: the `N_L LL` step size only. -/
  | derived (base : StepSize)
  /-- Style 2, scalar expounded: one step size per sub-band. -/
  | expounded (steps : Array StepSize)
  deriving Repr, DecidableEq, Inhabited

/-- Quantisation default, QCD (T.800 A.6.4); also the parameters of QCC. -/
structure QCD where
  /-- Number of guard bits (`Sqcd` bits 5–7), < 8. -/
  guardBits : UInt8
  /-- Style and step sizes. -/
  quant : Quantization
  deriving Repr, DecidableEq, Inhabited

/-- The `Sqcd` byte (T.800 Table A.28). -/
def QCD.sqcd (q : QCD) : UInt8 :=
  q.guardBits * 32 +
    match q.quant with
    | .none _ => 0
    | .derived _ => 1
    | .expounded _ => 2

/-- Quantisation component, QCC (T.800 A.6.5). -/
structure QCC where
  /-- `Cqcc` component index (< Csiz). -/
  component : UInt16
  /-- `Sqcc`, `SPqcc`. -/
  params : QCD
  deriving Repr, DecidableEq, Inhabited

/-- Region of interest, RGN (T.800 A.6.3), with `Srgn = 0` (implicit ROI, max-shift). -/
structure RGN where
  /-- `Crgn` component index (< Csiz). -/
  component : UInt16
  /-- `SPrgn` ROI shift value. -/
  shift : UInt8
  deriving Repr, DecidableEq, Inhabited

/-- One progression order change (T.800 Table A.32). Fields are stored raw. -/
structure PocEntry where
  /-- `RSpoc` resolution start, 0…32. -/
  resStart : UInt8
  /-- `CSpoc` component start. -/
  compStart : UInt16
  /-- `LYEpoc` layer end, ≥ 1. -/
  layerEnd : UInt16
  /-- `REpoc` resolution end (exclusive), `RSpoc < REpoc ≤ 33`. -/
  resEnd : UInt8
  /-- `CEpoc` component end (exclusive), raw: 0 means 256 (1-byte form) or 16384 (2-byte
  form); see `compEnd`. -/
  compEndRaw : UInt16
  /-- `Ppoc` progression order. -/
  order : Progression
  deriving Repr, DecidableEq, Inhabited

/-- The component end of a POC entry: `CEpoc`, with 0 read as 256 when `Csiz < 257`
and as 16384 otherwise (T.800 Table A.32). -/
def PocEntry.compEnd (csiz : Nat) (e : PocEntry) : Nat :=
  if e.compEndRaw = 0 then (if csiz < 257 then 256 else 16384) else e.compEndRaw.toNat

/-- Progression order change, POC (T.800 A.6.6). -/
structure POC where
  /-- The entries, at least one. -/
  entries : Array PocEntry
  deriving Repr, DecidableEq, Inhabited

/-- Comment, COM (T.800 A.9.2). -/
structure COM where
  /-- `Rcom` registration value (0 binary, 1 ISO/IEC 8859-15 text; others kept). -/
  rcom : UInt16
  /-- `Ccom` bytes. -/
  data : ByteArray
  deriving DecidableEq, Inhabited

/-- Component registration, CRG (T.800 A.9.1): `(Xcrg, Ycrg)` per component. -/
structure CRG where
  /-- One offset pair per component (`Csiz` entries). -/
  offsets : Array (UInt16 × UInt16)
  deriving Repr, DecidableEq, Inhabited

/-- A marker segment kept unparsed: the marker and the absolute byte range of its body
(after `Lxxx`) in the input buffer. -/
structure RawSegment where
  /-- The marker code. -/
  code : UInt16
  /-- Absolute offset of the body (after the length field). -/
  offset : Nat
  /-- Body length (`Lxxx − 2`). -/
  length : Nat
  deriving Repr, DecidableEq, Inhabited

/-- The body bytes of a raw segment, copied out of the input buffer. -/
def RawSegment.bytes (s : RawSegment) (data : ByteArray) : ByteArray :=
  data.extract s.offset (s.offset + s.length)

/-- One entry of the marker index (like OpenJPEG's codestream index): the marker, its
absolute position and its total length in bytes including the marker (2 for `SOC`). -/
structure MarkerPos where
  /-- The marker code. -/
  code : UInt16
  /-- Absolute offset of the marker. -/
  pos : Nat
  /-- Total length: 2 + `Lxxx` (2 for markers without parameters). -/
  len : Nat
  deriving Repr, DecidableEq, Inhabited

/-- The parsed main header (T.800 A.3, Table A.3). -/
structure MainHeader where
  /-- Image and tile size. -/
  siz : SIZ
  /-- Coding style default (exactly one). -/
  cod : COD
  /-- Coding style overrides per component, in stream order. -/
  coc : Array COC
  /-- Quantisation default (exactly one). -/
  qcd : QCD
  /-- Quantisation overrides per component, in stream order. -/
  qcc : Array QCC
  /-- Regions of interest, in stream order. -/
  rgn : Array RGN
  /-- Progression order changes, in stream order. -/
  poc : Array POC
  /-- Comments, in stream order. -/
  com : Array COM
  /-- Capabilities segment (Part 2/15), kept raw. -/
  cap : Option RawSegment
  /-- Component registration. -/
  crg : Option CRG
  /-- `TLM`, `PLM`, `PPM` segments, raw, in stream order (parsed by task 1.4). -/
  pointers : Array RawSegment
  /-- Unknown marker segments, raw, in stream order (lenient). -/
  unknown : Array RawSegment
  /-- Every marker of the main header from `SOC` on, in stream order. -/
  markers : Array MarkerPos
  /-- Absolute offset of the first `SOT` marker (the end of the main header). -/
  endPos : Nat
  deriving DecidableEq, Inhabited

/-! ## Helpers -/

/-- Hexadecimal rendering `0x…` of a number, for error messages. -/
def hex (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

/-- `Error.malformed` at the reader's current position. -/
def malformedAt (r : Reader) (what : String) : Error :=
  .malformed (.atOffset r.stage r.pos) what

/-- `Error.unsupported` at the reader's current position. -/
def unsupportedAt (r : Reader) (what : String) : Error :=
  .unsupported (.atOffset r.stage r.pos) what

/-- Fails with `malformed` at `r` unless the condition holds. -/
@[inline] def require (r : Reader) (c : Bool) (what : String) : Except Error Unit :=
  if c then .ok () else .error (malformedAt r what)

/-- Requires that the body has been consumed exactly. -/
def expectEnd (r : Reader) (what : String) : Except Error Unit :=
  if r.atEnd then .ok () else .error (malformedAt r s!"{what}: {r.remaining} trailing bytes")

/-- Reads `n` items with `f`, appending them to `acc` (tail recursive, structural on `n`). -/
def readArray {α : Type} (f : Reader → Except Error (α × Reader)) :
    Array α → Nat → Reader → Except Error (Array α × Reader)
  | acc, 0, r => .ok (acc, r)
  | acc, n + 1, r =>
    match f r with
    | .error e => .error e
    | .ok (a, r') => readArray f (acc.push a) n r'

/-- Reads a component index: 1 byte when `Csiz < 257`, else 2 bytes (T.800 A.6.2). -/
def readCompIndex (csiz : Nat) (r : Reader) : Except Error (UInt16 × Reader) :=
  if csiz < 257 then
    match r.u8 with
    | .error e => .error e
    | .ok (b, r') => .ok (b.toUInt16, r')
  else r.u16be

/-- Reads a component index and requires it to be `< csiz`. -/
def readComponent (csiz : Nat) (r : Reader) : Except Error (UInt16 × Reader) := do
  let (c, r') ← readCompIndex csiz r
  require r (c.toNat < csiz) s!"component index {c} ≥ Csiz {csiz}"
  return (c, r')

/-! ## SIZ (T.800 A.5.1) -/

/-- Reads one component's `Ssiz`, `XRsiz`, `YRsiz`. -/
def readSizComponent (r : Reader) : Except Error (Component × Reader) := do
  let (s, r1) ← r.u8
  require r ((s &&& 0x7F) < 38) s!"Ssiz bit depth {(s &&& 0x7F).toNat + 1} > 38"
  let (dx, r2) ← r1.u8
  require r1 (dx ≠ 0) "XRsiz = 0"
  let (dy, r3) ← r2.u8
  require r2 (dy ≠ 0) "YRsiz = 0"
  return ({ signed := s ≥ 0x80, depth := (s &&& 0x7F) + 1, dx, dy }, r3)

/-- Parses a SIZ body (T.800 A.5.1). Checks `1 ≤ Csiz ≤ 16384`, `Csiz ≤ maxComponents`
(before reading the components), `Lsiz = 38 + 3·Csiz`, `XOsiz < Xsiz`, `YOsiz < Ysiz`,
nonzero tile sizes, `XTOsiz ≤ XOsiz`, `XTOsiz + XTsiz > XOsiz` (and for Y), bit depths
1…38 and nonzero sub-sampling. -/
def parseSIZ (L : Limits) (r : Reader) : Except Error SIZ := do
  let (rsiz, r) ← r.u16be
  let (xsiz, r) ← r.u32be
  let (ysiz, r) ← r.u32be
  let (xosiz, r) ← r.u32be
  let (yosiz, r) ← r.u32be
  let (xtsiz, r) ← r.u32be
  let (ytsiz, r) ← r.u32be
  let (xtosiz, r) ← r.u32be
  let (ytosiz, r) ← r.u32be
  let r0 := r
  let (csiz, r) ← r.u16be
  let n := csiz.toNat
  require r0 (1 ≤ n ∧ n ≤ 16384) s!"Csiz = {n} not in 1…16384"
  L.check (.atOffset r0.stage r0.pos) .components n
  require r0 (r.remaining = 3 * n) s!"Lsiz ≠ 38 + 3·Csiz (Csiz = {n})"
  require r0 (xosiz < xsiz ∧ yosiz < ysiz) "image offset ≥ reference grid size"
  require r0 (xtsiz ≠ 0 ∧ ytsiz ≠ 0) "tile size 0"
  require r0 (xtosiz ≤ xosiz ∧ ytosiz ≤ yosiz) "tile offset > image offset"
  require r0 (xtosiz.toNat + xtsiz.toNat > xosiz.toNat ∧
    ytosiz.toNat + ytsiz.toNat > yosiz.toNat) "first tile does not meet the image area"
  let (components, r) ← readArray readSizComponent (Array.mkEmpty n) n r
  expectEnd r "SIZ"
  return { rsiz, xsiz, ysiz, xosiz, yosiz, xtsiz, ytsiz, xtosiz, ytosiz, components }

/-! ## COD, COC (T.800 A.6.1, A.6.2) -/

/-- Reads one precinct size byte. -/
def readPrecinct (r : Reader) : Except Error (Precinct × Reader) := do
  let (b, r') ← r.u8
  return ({ ppx := b &&& 0x0F, ppy := b >>> 4 }, r')

/-- Reads `SPcod`/`SPcoc` (T.800 Table A.15). `defined` is `Scod`/`Scoc` bit 0. Checks
levels ≤ 32 and ≤ `maxDecompLevels` (before the precinct array), `xcb ≤ 8`, `ycb ≤ 8`,
`xcb + ycb ≤ 8`, code-block style bits 6–7 clear (bit 6, HT, is unsupported), transform
0 or 1, and `PPx, PPy ≥ 1` above resolution 0. -/
def readCodingStyle (L : Limits) (defined : Bool) (r : Reader) :
    Except Error (CodingStyle × Reader) := do
  let r0 := r
  let (levels, r) ← r.u8
  require r0 (levels ≤ 32) s!"decomposition levels {levels} > 32"
  L.check (.atOffset r0.stage r0.pos) .decompLevels levels.toNat
  let r1 := r
  let (xcb, r) ← r.u8
  let (ycb, r) ← r.u8
  require r1 (xcb ≤ 8 ∧ ycb ≤ 8 ∧ xcb.toNat + ycb.toNat ≤ 8)
    s!"code-block size exponents {xcb.toNat + 2}, {ycb.toNat + 2} (each ≤ 10, sum ≤ 12)"
  let r2 := r
  let (cbStyle, r) ← r.u8
  if cbStyle &&& 0x40 ≠ 0 then
    throw (unsupportedAt r2 "HT code-block coding (Part 15)")
  require r2 (cbStyle &&& 0x80 = 0) s!"reserved code-block style bit ({hex cbStyle.toNat})"
  let r3 := r
  let (tb, r) ← r.u8
  let transform ← match tb with
    | 0 => pure Transform.irreversible97
    | 1 => pure Transform.reversible53
    | _ => throw (unsupportedAt r3 s!"wavelet transform {tb} (Part 2)")
  if defined then
    let r4 := r
    let (ps, r) ← readArray readPrecinct (Array.mkEmpty (levels.toNat + 1)) (levels.toNat + 1) r
    require r4 ((ps.toList.drop 1).all fun p => p.ppx ≠ 0 && p.ppy ≠ 0)
      "precinct size exponent 0 above resolution 0"
    return ({ levels, xcb, ycb, cbStyle, transform, precincts := some ps }, r)
  else
    return ({ levels, xcb, ycb, cbStyle, transform, precincts := none }, r)

/-- Parses a COD body (T.800 A.6.1). Checks reserved `Scod` bits, progression order 0…4,
layers ≥ 1 and ≤ `maxLayers`, MCT 0/1 (other values are Part 2: unsupported), and the
`SPcod` checks of `readCodingStyle`. -/
def parseCOD (L : Limits) (r : Reader) : Except Error COD := do
  let r0 := r
  let (scod, r) ← r.u8
  require r0 (scod &&& 0xF8 = 0) s!"reserved Scod bits ({hex scod.toNat})"
  let r1 := r
  let (pb, r) ← r.u8
  let progression ← match Progression.ofUInt8? pb with
    | some p => pure p
    | none => throw (malformedAt r1 s!"progression order {pb}")
  let r2 := r
  let (layers, r) ← r.u16be
  require r2 (layers ≠ 0) "0 layers"
  L.check (.atOffset r2.stage r2.pos) .layers layers.toNat
  let r3 := r
  let (mb, r) ← r.u8
  if mb > 1 then throw (unsupportedAt r3 s!"multiple component transform {mb} (Part 2)")
  let (style, r) ← readCodingStyle L (scod &&& 1 ≠ 0) r
  expectEnd r "COD"
  return { sop := scod &&& 2 ≠ 0, eph := scod &&& 4 ≠ 0, progression, layers,
           mct := mb = 1, style }

/-- Parses a COC body (T.800 A.6.2): `Ccoc` (1 or 2 bytes by `csiz`, < `csiz`), `Scoc`
(only bit 0 may be set), `SPcoc`. -/
def parseCOC (L : Limits) (csiz : Nat) (r : Reader) : Except Error COC := do
  let (component, r) ← readComponent csiz r
  let r0 := r
  let (scoc, r) ← r.u8
  require r0 (scoc &&& 0xFE = 0) s!"reserved Scoc bits ({hex scoc.toNat})"
  let (style, r) ← readCodingStyle L (scoc = 1) r
  expectEnd r "COC"
  return { component, style }

/-! ## QCD, QCC (T.800 A.6.4, A.6.5) -/

/-- The largest number of sub-bands: `3·32 + 1` (T.800 A.6.4). -/
def maxBands : Nat := 97

/-- Reads a "no quantisation" exponent byte (`εb` in bits 3–7, bits 0–2 zero). -/
def readExponent (r : Reader) : Except Error (UInt8 × Reader) := do
  let (b, r') ← r.u8
  require r (b &&& 7 = 0) s!"reserved bits in exponent byte {hex b.toNat}"
  return (b >>> 3, r')

/-- Reads a 16-bit step size (`εb` in bits 11–15, `μb` in bits 0–10). -/
def readStepSize (r : Reader) : Except Error (StepSize × Reader) := do
  let (v, r') ← r.u16be
  return ({ exponent := (v >>> 11).toUInt8, mantissa := v &&& 0x7FF }, r')

/-- Reads `Sqcd`/`Sqcc` and `SPqcd`/`SPqcc` up to the end of the body (T.800 Tables
A.28–A.30). Style 0: one byte per band; style 1: one 16-bit value; style 2: 16 bits per
band; 1…97 bands. -/
def readQuant (r : Reader) : Except Error QCD := do
  let r0 := r
  let (s, r) ← r.u8
  let guardBits := s >>> 5
  match s &&& 0x1F with
  | 0 =>
    let n := r.remaining
    require r0 (1 ≤ n ∧ n ≤ maxBands) s!"{n} sub-band exponents (1…97)"
    let (es, r) ← readArray readExponent (Array.mkEmpty n) n r
    expectEnd r "QCD/QCC"
    return { guardBits, quant := .none es }
  | 1 =>
    let (b, r) ← readStepSize r
    expectEnd r "QCD/QCC"
    return { guardBits, quant := .derived b }
  | 2 =>
    let n := r.remaining / 2
    require r0 (r.remaining % 2 = 0 ∧ 1 ≤ n ∧ n ≤ maxBands)
      s!"{r.remaining} bytes of expounded step sizes (even, 2…194)"
    let (ss, r) ← readArray readStepSize (Array.mkEmpty n) n r
    expectEnd r "QCD/QCC"
    return { guardBits, quant := .expounded ss }
  | st => throw (malformedAt r0 s!"quantisation style {st}")

/-- Parses a QCD body (T.800 A.6.4). -/
def parseQCD (r : Reader) : Except Error QCD := readQuant r

/-- Parses a QCC body (T.800 A.6.5): `Cqcc` (1 or 2 bytes by `csiz`, < `csiz`), then as
QCD. -/
def parseQCC (csiz : Nat) (r : Reader) : Except Error QCC := do
  let (component, r) ← readComponent csiz r
  let params ← readQuant r
  return { component, params }

/-! ## RGN, POC (T.800 A.6.3, A.6.6) -/

/-- Parses an RGN body (T.800 A.6.3): `Crgn` (1 or 2 bytes by `csiz`), `Srgn` (only 0,
implicit ROI, is Part 1), `SPrgn`. -/
def parseRGN (csiz : Nat) (r : Reader) : Except Error RGN := do
  let (component, r) ← readComponent csiz r
  let r0 := r
  let (srgn, r) ← r.u8
  if srgn ≠ 0 then throw (unsupportedAt r0 s!"ROI style {srgn} (Part 2)")
  let (shift, r) ← r.u8
  expectEnd r "RGN"
  return { component, shift }

/-- Reads one POC entry (T.800 Table A.32) and checks `RSpoc ≤ 32`,
`RSpoc < REpoc ≤ 33`, `LYEpoc ≥ 1`, `CSpoc < CEpoc` (interpreted), `Ppoc ≤ 4`. -/
def readPocEntry (csiz : Nat) (r : Reader) : Except Error (PocEntry × Reader) := do
  let r0 := r
  let (resStart, r) ← r.u8
  let (compStart, r) ← readCompIndex csiz r
  let (layerEnd, r) ← r.u16be
  let (resEnd, r) ← r.u8
  let (compEndRaw, r) ← readCompIndex csiz r
  let r5 := r
  let (pb, r) ← r.u8
  let order ← match Progression.ofUInt8? pb with
    | some p => pure p
    | none => throw (malformedAt r5 s!"POC progression order {pb}")
  let e : PocEntry := { resStart, compStart, layerEnd, resEnd, compEndRaw, order }
  require r0 (resStart ≤ 32 ∧ resStart < resEnd ∧ resEnd ≤ 33)
    s!"POC resolutions {resStart}…{resEnd}"
  require r0 (layerEnd ≠ 0) "POC layer end 0"
  require r0 (compStart.toNat < e.compEnd csiz) s!"POC components {compStart}…{e.compEnd csiz}"
  return (e, r)

/-- The size of a POC entry: 7 bytes, or 9 when `Csiz ≥ 257`. -/
def pocEntrySize (csiz : Nat) : Nat := if csiz < 257 then 7 else 9

/-- Parses a POC body (T.800 A.6.6): a nonzero whole number of entries, at most
`maxPocEntries` (checked before reading). -/
def parsePOC (L : Limits) (csiz : Nat) (r : Reader) : Except Error POC := do
  let sz := pocEntrySize csiz
  let n := r.remaining / sz
  require r (r.remaining % sz = 0 ∧ 1 ≤ n) s!"POC body of {r.remaining} bytes (entries of {sz})"
  L.check (.atOffset r.stage r.pos) .pocEntries n
  let (entries, r) ← readArray (readPocEntry csiz) (Array.mkEmpty n) n r
  expectEnd r "POC"
  return { entries }

/-! ## COM, CRG (T.800 A.9) -/

/-- Parses a COM body (T.800 A.9.2): `Rcom` and the remaining bytes. -/
def parseCOM (r : Reader) : Except Error COM := do
  let (rcom, r) ← r.u16be
  return { rcom, data := r.rest }

/-- Reads one `(Xcrg, Ycrg)` pair. -/
def readCrgPair (r : Reader) : Except Error ((UInt16 × UInt16) × Reader) := do
  let (x, r) ← r.u16be
  let (y, r) ← r.u16be
  return ((x, y), r)

/-- Parses a CRG body (T.800 A.9.1): exactly `Csiz` offset pairs. -/
def parseCRG (csiz : Nat) (r : Reader) : Except Error CRG := do
  require r (r.remaining = 4 * csiz) s!"CRG body of {r.remaining} bytes, expected 4·Csiz"
  let (offsets, r) ← readArray readCrgPair (Array.mkEmpty csiz) csiz r
  expectEnd r "CRG"
  return { offsets }

/-! ## Main header driver (T.800 A.3) -/

/-- Main-header segments collected so far (COD and QCD optional until the end). -/
structure Acc where
  /-- COD, once seen. -/
  cod : Option COD := none
  /-- COC segments. -/
  coc : Array COC := #[]
  /-- QCD, once seen. -/
  qcd : Option QCD := none
  /-- QCC segments. -/
  qcc : Array QCC := #[]
  /-- RGN segments. -/
  rgn : Array RGN := #[]
  /-- POC segments. -/
  poc : Array POC := #[]
  /-- Total POC entries so far. -/
  pocEntries : Nat := 0
  /-- COM segments. -/
  com : Array COM := #[]
  /-- CAP segment. -/
  cap : Option RawSegment := none
  /-- CRG segment. -/
  crg : Option CRG := none
  /-- TLM/PLM/PPM segments. -/
  pointers : Array RawSegment := #[]
  /-- Unknown segments. -/
  unknown : Array RawSegment := #[]
  /-- Marker index. -/
  markers : Array MarkerPos := #[]

/-- Reads `Lxxx` (≥ 2) after a marker and splits off the body: returns the body reader,
`Lxxx`, and the reader after the segment. -/
def readSegment (r : Reader) : Except Error (Reader × Nat × Reader) := do
  let (len, r1) ← r.u16be
  require r (len ≥ 2) s!"segment length {len} < 2"
  let (body, r2) ← r1.take (len.toNat - 2)
  return (body, len.toNat, r2)

/-- Whether a marker may not appear in a main header (T.800 Table A.3). -/
def forbiddenInMain (m : UInt16) : Bool :=
  m == Code.SOC || m == Code.SIZ || m == Code.SOD || m == Code.EOC || m == Code.SOP ||
    m == Code.EPH || m == Code.PLT || m == Code.PPT

/-- Adds one parsed segment with marker `m` and body `body` to the accumulator. -/
def addSegment (L : Limits) (csiz : Nat) (acc : Acc) (m : UInt16) (body : Reader) :
    Except Error Acc := do
  if m == Code.COD then
    require body acc.cod.isNone "second COD in main header"
    return { acc with cod := some (← parseCOD L body) }
  else if m == Code.COC then
    return { acc with coc := acc.coc.push (← parseCOC L csiz body) }
  else if m == Code.QCD then
    require body acc.qcd.isNone "second QCD in main header"
    return { acc with qcd := some (← parseQCD body) }
  else if m == Code.QCC then
    return { acc with qcc := acc.qcc.push (← parseQCC csiz body) }
  else if m == Code.RGN then
    return { acc with rgn := acc.rgn.push (← parseRGN csiz body) }
  else if m == Code.POC then
    let p ← parsePOC L csiz body
    let total := acc.pocEntries + p.entries.size
    L.check (.atOffset body.stage body.pos) .pocEntries total
    return { acc with poc := acc.poc.push p, pocEntries := total }
  else if m == Code.COM then
    return { acc with com := acc.com.push (← parseCOM body) }
  else if m == Code.CRG then
    require body acc.crg.isNone "second CRG in main header"
    return { acc with crg := some (← parseCRG csiz body) }
  else
    let raw : RawSegment := { code := m, offset := body.pos, length := body.remaining }
    if m == Code.CAP then
      require body acc.cap.isNone "second CAP in main header"
      return { acc with cap := some raw }
    else if m == Code.TLM || m == Code.PLM || m == Code.PPM then
      return { acc with pointers := acc.pointers.push raw }
    else
      return { acc with unknown := acc.unknown.push raw }

/-- The segment loop after SIZ: reads marker segments until `SOT`, which it leaves unread.
`fuel` starts at the remaining byte count; every iteration consumes ≥ 2 bytes. -/
def segmentLoop (L : Limits) (csiz : Nat) : Nat → Acc → Reader → Except Error (Acc × Reader)
  | 0, _, r => .error (r.truncErr "main header: no SOT")
  | fuel + 1, acc, r =>
    match r.u16be with
    | .error e => .error e
    | .ok (m, r1) =>
      if m == Code.SOT then .ok (acc, r)
      else if m < 0xFF01 then .error (malformedAt r s!"expected a marker, found {hex m.toNat}")
      else if 0xFF30 ≤ m ∧ m ≤ 0xFF3F then
        segmentLoop L csiz fuel
          { acc with markers := acc.markers.push { code := m, pos := r.pos, len := 2 } } r1
      else if forbiddenInMain m then
        .error (malformedAt r s!"marker {hex m.toNat} not allowed in the main header")
      else
        match readSegment r1 with
        | .error e => .error e
        | .ok (body, len, r2) =>
          let acc := { acc with markers := acc.markers.push { code := m, pos := r.pos,
                                                               len := len + 2 } }
          match addSegment L csiz acc m body with
          | .error e => .error e
          | .ok acc => segmentLoop L csiz fuel acc r2

/-- Parses a main header (T.800 A.3): `SOC`, `SIZ`, then marker segments up to the first
`SOT`. Returns the header and the reader positioned at that `SOT`. -/
def parseMainHeader (L : Limits) (r : Reader) : Except Error (MainHeader × Reader) := do
  let r0 := r
  let (soc, r) ← r.u16be
  require r0 (soc == Code.SOC) "codestream does not start with SOC"
  let r1 := r
  let (m, r) ← r.u16be
  require r1 (m == Code.SIZ) "SIZ does not follow SOC"
  let (body, len, r) ← readSegment r
  let siz ← parseSIZ L body
  let acc : Acc := { markers := #[{ code := Code.SOC, pos := r0.pos, len := 2 },
                                  { code := Code.SIZ, pos := r1.pos, len := len + 2 }] }
  let (acc, r) ← segmentLoop L siz.csiz r.remaining acc r
  let some cod := acc.cod | throw (malformedAt r "main header without COD")
  let some qcd := acc.qcd | throw (malformedAt r "main header without QCD")
  return ({ siz, cod, coc := acc.coc, qcd, qcc := acc.qcc, rgn := acc.rgn, poc := acc.poc,
            com := acc.com, cap := acc.cap, crg := acc.crg, pointers := acc.pointers,
            unknown := acc.unknown, markers := acc.markers, endPos := r.pos }, r)

end JPEG2000.Marker
