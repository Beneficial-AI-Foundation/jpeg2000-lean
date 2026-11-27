import JPEG2000.TilePart
import Encode.Marker

/-!
# Tile-part marker-segment serialiser (Plan.md §4 M1, §5.1, §5.3; T.800 A.4.2, A.7)

Task 1.10: the inverse of the segment parsers of `JPEG2000.TilePart` — `SOT` (T.800 A.4.2,
Table A.5), `TLM` (A.7.1, Tables A.33–A.34), `PLT` (A.7.3, Tables A.36–A.37), `PPM` (A.7.4,
Table A.38) and `PPT` (A.7.5, Table A.39). As in `Encode.Marker`, each `serializeX` produces
the segment **body** (the bytes after `Lxxx`), built first as a `List UInt8` (`…Bytes`) for
the proofs of `Spec.TilePartRoundTrip`, then packed with `Encode.Marker.pack`;
`Encode.Marker.segment` adds the marker and `Lxxx`.

* `TLM`: `Stlm = ST·16 + SP·64`; `Ttlm` is written in `ST` bytes (0, 1 or 2) and `Ptlm`
  in 2 or 4 bytes (`SP`).
* `PLT`: every packet length is written in the canonical (shortest) form of the 7-bit
  continuation code of T.800 A.7.3: groups of 7 bits, most significant first, bit 7 set on
  every byte but the last.
* `PPM`/`PPT`: the parsed records hold their `Ippm`/`Ippt` data as an absolute byte range of
  the input (no copy), so the serialisers take the source buffer the range refers to.

Reference encoder for tests and proofs only (Plan.md §5.3).
-/

namespace JPEG2000.Encode.TilePart

open JPEG2000.TilePart JPEG2000.Encode.Marker

/-! ## SOT and TLM -/

/-- SOT body (T.800 A.4.2): `Isot`, `Psot`, `TPsot`, `TNsot`. -/
def sotBytes (s : SOT) : List UInt8 := be16 s.isot ++ be32 s.psot ++ [s.tpsot, s.tnsot]

/-- The `Ttlm` bytes of a TLM entry: none for `ST = 0`, one for `ST = 1`, two otherwise
(T.800 Table A.34). A missing tile index is written as 0. -/
def tlmTileBytes (st : UInt8) (tile : Option UInt16) : List UInt8 :=
  match st with
  | 0 => []
  | 1 => [(tile.getD 0).toUInt8]
  | _ => be16 (tile.getD 0)

/-- One TLM entry (T.800 Table A.34): `Ttlm` then `Ptlm` (4 bytes when `SP`, else 2). -/
def tlmEntryBytes (st : UInt8) (sp : Bool) (e : TlmEntry) : List UInt8 :=
  tlmTileBytes st e.tile ++ (if sp then be32 e.length else be16 e.length.toUInt16)

/-- TLM body (T.800 A.7.1): `Ztlm`, `Stlm`, the entries. -/
def tlmBytes (t : TLM) : List UInt8 :=
  [t.ztlm, t.stlm] ++ t.entries.toList.flatMap (tlmEntryBytes t.st t.sp)

/-! ## PLT: the 7-bit continuation code -/

/-- The leading bytes of the canonical code of a value whose high part is `m`: the 7-bit
groups of `m`, most significant first, each with bit 7 set; empty for `m = 0`. -/
def varintHigh (m : Nat) : List UInt8 :=
  if m = 0 then [] else varintHigh (m / 128) ++ [(m % 128 + 128).toUInt8]
termination_by m
decreasing_by omega

/-- The canonical (shortest) 7-bit continuation code of `n` (T.800 A.7.3, Table A.37). -/
def encodeVarint (n : Nat) : List UInt8 := varintHigh (n / 128) ++ [(n % 128).toUInt8]

/-- PLT body (T.800 A.7.3): `Zplt`, then the packet lengths. -/
def pltBytes (p : PLT) : List UInt8 := [p.zplt] ++ p.lengths.toList.flatMap encodeVarint

/-! ## PPM and PPT -/

/-- PPM body (T.800 A.7.4): `Zppm` followed by the bytes of its range in `src`. -/
def ppmBytes (p : PPM) (src : ByteArray) : List UInt8 :=
  p.zppm :: (p.body.bytes src).data.toList

/-- PPT body (T.800 A.7.5): `Zppt` followed by the bytes of its range in `src`. -/
def pptBytes (p : PPT) (src : ByteArray) : List UInt8 :=
  p.zppt :: (p.body.bytes src).data.toList

/-! ## Serialisers -/

/-- Serialises a SOT body. -/
def serializeSOT (s : SOT) : ByteArray := pack (sotBytes s)
/-- Serialises a TLM body. -/
def serializeTLM (t : TLM) : ByteArray := pack (tlmBytes t)
/-- Serialises a PLT body (canonical packet-length code). -/
def serializePLT (p : PLT) : ByteArray := pack (pltBytes p)
/-- Serialises a PPM body; `src` is the buffer `p.body` refers to. -/
def serializePPM (p : PPM) (src : ByteArray) : ByteArray := pack (ppmBytes p src)
/-- Serialises a PPT body; `src` is the buffer `p.body` refers to. -/
def serializePPT (p : PPT) (src : ByteArray) : ByteArray := pack (pptBytes p src)

end JPEG2000.Encode.TilePart
