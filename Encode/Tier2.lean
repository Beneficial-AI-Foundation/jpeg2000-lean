import Spec.TagTree

/-!
# Reference Tier-2 encoder: packets of one layer (T.800 B.9, B.10, B.12.1.1)

Plan.md §5.3 (reference encoder: tests and proofs only, never in the public API), §4 (C4 and
C10: the packet headers written here are what `JPEG2000.Tier2.Packet` reads back). Task 7.2.

The encoder is the mirror of the decoder `JPEG2000.Tier2.Packet` restricted to what the
reference encoder needs: **one quality layer**, every coding pass of a code-block in that
layer, plain code-block style (one codeword segment per code-block), no `SOP`/`EPH`, no
packed headers.

* **Bit writer** (B.10.1): bits MSB first; after a `0xFF` byte the next byte carries only 7
  bits (its MSB is a stuffed `0`). `BitWriter.finish` pads the last byte with zeros and, when
  the last byte written is `0xFF`, appends the `0x00` byte that the decoder's `align`
  consumes after it (as OpenJPEG `opj_bio_flush`).
* **Packet header** (B.10.3–B.10.7), for every sub-band of the precinct and every code-block
  of the precinct-band in raster order:
  * inclusion (B.10.4): the inclusion tag tree's leaf is `0` for a code-block with coding
    passes (included in layer 0), `1` otherwise; the bits answer the query "leaf `< 1`?"
    (`Spec.TagTree.encodeAll` on `Query.lt x y 1`, threshold `layer + 1`);
  * on inclusion, the zero bit-planes `P` (B.10.5): `Spec.TagTree.encodeAll` on
    `Query.exact x y maxZero` (the decoder reads it with the same bound, `Mb + roiShift`);
  * the number of passes (Table B.4) — `passBits`;
  * the `Lblock` increment (B.10.7.1): the fewest `1`s so that the length fits in
    `Lblock + ⌊log₂ passes⌋` bits (`Lblock` starts at 3), then a `0`;
  * the length of the single codeword segment (B.10.7.2, plain mode: `segmentPasses 0 n 0 =
    [n]` for `n ≤ 109`, which holds as `n ≤ 3K − 2` and `K ≤ Mb ≤ 37` without ROI).
  A precinct none of whose code-blocks has passes gets a zero-length packet (one `0` bit,
  B.10.3) — also when it has no code-blocks at all (empty precinct-bands, B.6).
* **Packet body** (B.10.8): the included code-blocks' codewords in header order.
* **Tile** (B.12.1.1): LRCP order with one layer — resolution, then component, then precinct.

The tag-tree bits come from the reference encoder `Spec.TagTree.encodeAll`, whose inverse
property is C4 (`Spec.TagTree.decode_encode`); the spec state is a function-update chain, so
the cost is quadratic in the code-blocks of a precinct-band (fine for test images). Every
loop is a fold over a list or an array: structural, total.
-/

namespace JPEG2000.Encode.Tier2

open JPEG2000.Spec.TagTree (St Query encodeAll)

/-! ## Bit writer (B.10.1) -/

/-- An MSB-first bit writer with the `0xFF` bit-stuffing rule of B.10.1. -/
structure BitWriter where
  /-- Complete bytes written. -/
  out : Array UInt8 := #[]
  /-- The bits of the byte being filled. -/
  cur : Nat := 0
  /-- Number of bits in `cur`. -/
  cnt : Nat := 0
  /-- Bits the current byte holds: 7 after an `0xFF` byte, else 8. -/
  cap : Nat := 8
  deriving Inhabited

/-- Writes one bit. -/
def BitWriter.bit (w : BitWriter) (b : Bool) : BitWriter :=
  let cur := w.cur * 2 + (if b then 1 else 0)
  let cnt := w.cnt + 1
  if cnt ≥ w.cap then
    { out := w.out.push cur.toUInt8, cur := 0, cnt := 0, cap := if cur = 0xFF then 7 else 8 }
  else { w with cur, cnt }

/-- Writes a list of bits in order. -/
def BitWriter.bits (w : BitWriter) (bs : List Bool) : BitWriter := bs.foldl BitWriter.bit w

/-- The bytes written: the last byte padded with zeros, and a `0x00` appended when the last
byte is `0xFF` (the stuffed byte the decoder's `align` consumes). -/
def BitWriter.finish (w : BitWriter) : Array UInt8 :=
  let out := if w.cnt = 0 then w.out else w.out.push (w.cur * 2 ^ (w.cap - w.cnt)).toUInt8
  if out.back? = some 0xFF then out.push 0 else out

/-- `v` in `n` bits, MSB first (the low `n` bits of `v`). -/
def natBits (v n : Nat) : List Bool := (List.range n).reverse.map fun i => v / 2 ^ i % 2 == 1

/-- Number of bits of `v` (`0` for `0`). -/
def bitLen (v : Nat) : Nat := if v = 0 then 0 else Nat.log2 v + 1

/-- The Table B.4 codeword of `n` coding passes (`1 ≤ n ≤ 164`; larger values are written
as 164 — callers check the range). -/
def passBits (n : Nat) : List Bool :=
  if n ≤ 1 then [false]
  else if n = 2 then [true, false]
  else if n ≤ 5 then [true, true] ++ natBits (n - 3) 2
  else if n ≤ 36 then [true, true, true, true] ++ natBits (n - 6) 5
  else [true, true, true, true] ++ natBits 31 5 ++ natBits (min (n - 37) 127) 7

/-! ## Inputs -/

/-- One code-block as Tier-2 sees it: its coding passes, its missing most significant
bit-planes and its (single, plain-mode) codeword. -/
structure BlockIn where
  /-- Number of coding passes (`0`: not included). -/
  numPasses : Nat := 0
  /-- Zero bit-planes `P = Mb − K` (B.10.5). -/
  zeroBitPlanes : Nat := 0
  /-- The codeword (all passes, one segment). -/
  data : ByteArray := ByteArray.empty
  deriving Inhabited

/-- One precinct-band: its code-block grid `cw × ch`, the bound on zero bit-planes the
decoder uses (`Mb + roiShift`) and the code-blocks in raster order. -/
structure BandIn where
  /-- Code-blocks across. -/
  cw : Nat
  /-- Code-blocks down. -/
  ch : Nat
  /-- `Mb + roiShift` (the decoder's `maxZero`). -/
  maxZero : Nat
  /-- The `cw · ch` code-blocks in raster order. -/
  blocks : Array BlockIn
  deriving Inhabited

/-! ## Packet header and body -/

/-- The inclusion tag-tree leaves of a precinct-band in layer 0: `0` for an included
code-block, `1` otherwise. -/
def BandIn.inclLeaf (b : BandIn) (x y : Nat) : Nat :=
  if (b.blocks.getD (y * b.cw + x) default).numPasses > 0 then 0 else 1

/-- The zero bit-plane tag-tree leaves of a precinct-band. -/
def BandIn.zbpLeaf (b : BandIn) (x y : Nat) : Nat :=
  (b.blocks.getD (y * b.cw + x) default).zeroBitPlanes

/-- The `Lblock` increment for a segment of `len` bytes and `n` passes (B.10.7.1): the
fewest extra bits so that `len < 2^(3 + inc + ⌊log₂ n⌋)`. -/
def lblockInc (n len : Nat) : Nat := bitLen len - (3 + Nat.log2 n)

/-- The header bits of code-block `k` of a precinct-band in layer 0 (B.10.4–B.10.7), with
the two tag-tree states before and after. -/
def blockBits (b : BandIn) (k : Nat) (incl zbp : St) : List Bool × St × St :=
  let x := k % b.cw
  let y := k / b.cw
  let blk := b.blocks.getD k default
  let (ib, _, incl') := encodeAll b.cw b.ch b.inclLeaf [Query.lt x y 1] incl
  if blk.numPasses = 0 then (ib, incl', zbp)
  else
    let (zb, _, zbp') := encodeAll b.cw b.ch b.zbpLeaf [Query.exact x y b.maxZero] zbp
    let n := blk.numPasses
    let len := blk.data.size
    let inc := lblockInc n len
    (ib ++ zb ++ passBits n ++ List.replicate inc true ++ [false] ++
       natBits len (3 + inc + Nat.log2 n), incl', zbp')

/-- Writes the header bits of every code-block of a precinct-band. -/
def bandBits (w : BitWriter) (b : BandIn) : BitWriter :=
  let step (acc : BitWriter × St × St) (k : Nat) :=
    let (bits, incl, zbp) := blockBits b k acc.2.1 acc.2.2
    (acc.1.bits bits, incl, zbp)
  ((List.range b.blocks.size).foldl step (w, Spec.TagTree.init, Spec.TagTree.init)).1

/-- Whether a precinct contributes any coding pass. -/
def nonEmpty (bands : Array BandIn) : Bool :=
  bands.any fun b => b.blocks.any (·.numPasses > 0)

/-- The packet header of a precinct in layer 0 (B.10): the "non-empty" bit, then every band;
byte-aligned with B.10.1 stuffing. -/
def packetHeader (bands : Array BandIn) : Array UInt8 :=
  if nonEmpty bands then (bands.foldl bandBits (({} : BitWriter).bit true)).finish
  else (({} : BitWriter).bit false).finish

/-- The packet body (B.10.8): the included code-blocks' codewords in header order. -/
def packetBody (bands : Array BandIn) : ByteArray :=
  bands.foldl (fun acc b =>
    b.blocks.foldl (fun acc blk => if blk.numPasses > 0 then acc ++ blk.data else acc) acc)
    ByteArray.empty

/-- **One packet** (B.9) of a precinct in layer 0: header then body. -/
def encodePacket (bands : Array BandIn) : ByteArray :=
  ⟨packetHeader bands⟩ ++ packetBody bands

/-- **The packets of one tile** in LRCP order with one layer (B.12.1.1): `prec[c][r][p]` is
the bands of precinct `p` of resolution `r` of component `c`; resolutions in increasing
order, then components, then precincts. A component with fewer resolutions is skipped at
the higher ones. -/
def encodeTileLRCP (prec : Array (Array (Array (Array BandIn)))) : ByteArray :=
  let numRes := prec.foldl (fun m rs => max m rs.size) 0
  (List.range numRes).foldl (fun acc r =>
    prec.foldl (fun acc rs =>
      (rs.getD r #[]).foldl (fun acc bands => acc ++ encodePacket bands) acc) acc)
    ByteArray.empty

end JPEG2000.Encode.Tier2
