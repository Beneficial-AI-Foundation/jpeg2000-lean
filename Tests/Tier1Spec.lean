import Spec.Tier1.Decode
import Encode.MQ

/-!
# Tests: Tier-1 spec decoder, all code-block styles (tasks 3.2, 3.3)

Plan.md §4 (C3), §5.2 "Tier-1 / EBCOT"; T.800 Annex D (D.1–D.7).

1. **Scan order (D.1).** `scanOrder w h` is a permutation of the `w × h` positions and is
   sorted by (stripe, column, row) for all shapes up to 9 × 13 (heights not multiples of 4
   included); two shapes are compared with literal lists.
2. **Mode structure (D.4–D.6).** `isRawPass`, `segmentPasses` (plain, termall, bypass,
   bypass + termall, a later-layer `firstPass`) against literal lists; the raw bit reader
   `rawBit` on hand-made byte strings (bit-unstuffing after `0xFF`, a marker after `0xFF`,
   `0xFF` padding past the end).
3. **Hand-traced blocks.** Tiny blocks whose `(context, decision)` sequences were worked out
   by hand from Tables D.1–D.4 are MQ-encoded with `Encode.MQ` and decoded: plain mode, a
   bypass block with a raw refinement bit, segmentation symbols (good and bad; lenient and
   strict decoding), vertically causal context formation (the same block with and without
   the flag gives different decision sequences), reset and termall.
4. **Argument checks** (`CodeBlock.validate`, including segment structure).
5. **Random round trips against a test-only reference encoder, for all 64 code-block
   styles.** `encodeBlock` below is an independent Tier-1 encoder written in OpenJPEG's
   style (significance and sign in arrays padded by one coefficient on each side; the sign
   contributions computed as clamped sums `σ·(1 − 2·neg)` rather than via Table D.2;
   vertically causal formation as a mask on the padded row below a stripe; raw passes chosen
   by OpenJPEG's bit-plane rule `p + 1 ≤ K − 4`; codeword segments by OpenJPEG's `maxpasses`
   rule 10/2/1; raw bytes written with OpenJPEG's bypass packing (`0xFF` → next byte 7 bits,
   final partial byte padded `0101…`, a final `0xFF` dropped); MQ segments terminated with
   `FLUSH`, or with OpenJPEG's `ERTERM` procedure in predictable-termination mode). It shares
   only the context tables of `Spec.Tier1.Context` and the MQ coder. Random blocks (sizes
   1–64 per side with area ≤ 4096, all four orientations, 1–14 coded bit-planes, sparse to
   dense, 0–3 zero bit-planes), block `i` in style `i mod 64`, are encoded with all
   `3K − 2` passes and with random truncated pass counts. The strict decode must succeed,
   the decoded state must equal the encoder's model of what the decoder knows (every field
   of every coefficient), and the decoded magnitudes must equal the original's bits above
   the truncation point. A dense all-ones block per bypass style forces `0xFF` bytes (and
   hence stuffed bits) in raw segments.

The official reference Tier-1 encoder is task 3.5 (`Encode/Tier1.lean`); this one is
test-only.
-/

namespace JPEG2000.Tests.Tier1Spec

open JPEG2000
open JPEG2000.Spec.Tier1
open JPEG2000.Spec.MQ (Contexts initContexts)

/-- Runs one named check, printing a line on failure; returns 1 on failure, 0 on success. -/
def expect (name : String) (ok : Bool) : IO Nat := do
  if ok then return 0
  IO.eprintln s!"  FAIL tier1spec: {name}"
  return 1

/-- The error of an `Except`, if any (`Except` has no `BEq`). -/
def err? {α : Type} : Except Error α → Option Error
  | .error e => some e
  | .ok _ => none

/-- The value of an `Except`, if any. -/
def ok? {α : Type} : Except Error α → Option α
  | .error _ => none
  | .ok a => some a

/-! ## 1. Scan order -/

/-- `l` has no duplicates (quadratic; small lists only). -/
def nodup : List (Nat × Nat) → Bool
  | [] => true
  | a :: rest => !rest.contains a && nodup rest

/-- The D.1 sort key: stripe, then column, then row. -/
def scanKey (p : Nat × Nat) : Nat × Nat × Nat := (p.2 / 4, p.1, p.2)

/-- Lexicographic `<` on scan keys. -/
def keyLt (a b : Nat × Nat × Nat) : Bool :=
  a.1 < b.1 || (a.1 == b.1 && (a.2.1 < b.2.1 || (a.2.1 == b.2.1 && a.2.2 < b.2.2)))

/-- Consecutive elements are strictly increasing in the D.1 key. -/
def sortedByKey : List (Nat × Nat) → Bool
  | a :: b :: rest => keyLt (scanKey a) (scanKey b) && sortedByKey (b :: rest)
  | _ => true

/-- `scanOrder w h` is a permutation of the block's positions in D.1 order. -/
def scanOk (w h : Nat) : Bool :=
  let l := scanOrder w h
  l.length == w * h && nodup l && l.all (fun (x, y) => x < w && y < h) && sortedByKey l

/-! ## MQ and raw coding helpers (shared by the hand-traced and random tests) -/

/-- A coded symbol: an MQ decision in a context, or a raw bit (D.6). -/
inductive Sym where
  /-- MQ decision `d` in context `cx`. -/
  | mq (cx : Nat) (d : Bool)
  /-- Raw bit. -/
  | raw (b : Bool)
  deriving Repr, BEq, Inhabited

/-- The MQ pairs of a symbol list. -/
def mqPairs (syms : List Sym) : List (Nat × Bool) :=
  syms.filterMap fun | .mq cx d => some (cx, d) | .raw _ => none

/-- The raw bits of a symbol list. -/
def rawBitsOf (syms : List Sym) : List Bool :=
  syms.filterMap fun | .raw b => some b | .mq _ _ => none

/-- OpenJPEG's `opj_mqc_erterm_enc` (predictable termination, D.4.2): output bytes until at
least 12 bits of `C` are out, then one more `BYTEOUT` unless the current byte is `0xFF`. -/
def erterm (s : Encode.MQ.EncState) : List UInt8 :=
  let rec loop : Nat → Int → Encode.MQ.EncState → Encode.MQ.EncState
    | 0, _, s => s
    | f + 1, k, s =>
      if k > 0 then
        let s := Encode.MQ.byteout { s with C := s.C * 2 ^ s.CT % 0x100000000, CT := 0 }
        loop f (k - s.CT) s
      else s
  let s := loop 4 (12 - (s.CT : Int)) s
  let s := if s.B = 0xFF then s else Encode.MQ.byteout s
  (s.outRev.reverse.drop 1).map UInt8.ofNat

/-- MQ-encode one codeword segment holding the given passes, starting from the context
states `cxs`; with `reset`, contexts go back to Table D.7 after each pass; terminated with
`FLUSH` or (`predTerm`) `ERTERM`. Returns the bytes and the final context states. -/
def mqSegment (cxs : Contexts) (passes : List (List (Nat × Bool))) (reset predTerm : Bool) :
    List UInt8 × Contexts :=
  let (s, cxs) := passes.foldl (fun (s, cxs) pairs =>
      let (s, cxs) := Encode.MQ.encodeMany s cxs pairs
      (s, if reset then initContexts initialStates else cxs))
    (Encode.MQ.initenc, cxs)
  ((if predTerm then erterm s else Encode.MQ.flush s), cxs)

/-- OpenJPEG-style raw (bypass) packing: bits MSB first; after an `0xFF` byte the next byte
holds 7 bits (its MSB is a stuffed 0); a final partial byte is padded with `0101…`; a final
`0xFF` is dropped (the decoder pads with `0xFF`). -/
def rawPack (bits : List Bool) : List UInt8 :=
  let step := fun (st : Array Nat × Nat × Nat × Nat) (b : Bool) =>
    let (out, acc, n, cap) := st
    let acc := acc * 2 + (if b then 1 else 0)
    if n + 1 == cap then (out.push acc, 0, 0, if acc == 0xFF then 7 else 8)
    else (out, acc, n + 1, cap)
  let (out, acc, n, cap) := bits.foldl step (#[], 0, 0, 8)
  let out := if n == 0 then out else
    let pad := (List.range (cap - n)).map fun j => j % 2 == 1
    let (o, _, _, _) := pad.foldl step (out, acc, n, cap)
    o
  let out := if out.back? == some 0xFF then out.pop else out
  out.toList.map UInt8.ofNat

/-! ## 2. Mode structure and the raw bit reader -/

/-- `n` raw bits of `data` and the final reader state. -/
def readRaw (data : List UInt8) (n : Nat) : List Bool × RawState :=
  rawBits (RawState.init data) n

/-- Bits of a string of `0`/`1`. -/
def bitsS (s : String) : List Bool := s.toList.filterMap fun
  | '0' => some false | '1' => some true | _ => none

/-- Mode-structure and raw-reader unit tests. -/
def runModeUnits : IO Nat := do
  let mut f := 0
  let byp : Mode := { bypass := true }
  let ta : Mode := { termAll := true }
  f := f + (← expect "isRawPass bypass, passes 0..15"
    ((List.range 16).map (isRawPass byp) ==
      (List.replicate 10 false ++ [true, true, false, true, true, false])))
  f := f + (← expect "isRawPass plain never" ((List.range 40).all fun i => !isRawPass {} i))
  f := f + (← expect "segmentPasses plain 0" (segmentPasses Mode.plain 0 0 == []))
  f := f + (← expect "segmentPasses plain 7" (segmentPasses Mode.plain 7 0 == [7]))
  f := f + (← expect "segmentPasses plain from pass 5" (segmentPasses Mode.plain 3 5 == [3]))
  f := f + (← expect "segmentPasses predTerm+reset+causal+segsym = plain"
    (segmentPasses (Mode.ofStyle 0x3A) 9 0 == [9]))
  f := f + (← expect "segmentPasses termall 3" (segmentPasses ta 3 4 == [1, 1, 1]))
  f := f + (← expect "segmentPasses bypass 20"
    (segmentPasses byp 20 0 == [10, 2, 1, 2, 1, 2, 1, 1]))
  f := f + (← expect "segmentPasses bypass 9" (segmentPasses byp 9 0 == [9]))
  f := f + (← expect "segmentPasses bypass 11" (segmentPasses byp 11 0 == [10, 1]))
  f := f + (← expect "segmentPasses bypass, layer starting at pass 8"
    (segmentPasses byp 5 8 == [2, 2, 1]))
  f := f + (← expect "segmentPasses bypass, layer starting at pass 11"
    (segmentPasses byp 4 11 == [1, 1, 2]))
  f := f + (← expect "segmentPasses bypass+termall 12"
    (segmentPasses (Mode.ofStyle 5) 12 0 == List.replicate 12 1))
  f := f + (← expect "segmentPasses sums and positivity (all styles, n ≤ 40, first ≤ 30)"
    ((List.range 64).all fun st => (List.range 41).all fun n => (List.range 31).all fun i =>
      let l := segmentPasses (Mode.ofStyle st) n i
      l.sum == n && l.all (· > 0)))
  -- raw bit reader (D.6)
  f := f + (← expect "rawBit: 0xA5 0xFF 0x2A, then padding"
    ((readRaw [0xA5, 0xFF, 0x2A] 26).1 ==
      bitsS "10100101" ++ bitsS "11111111" ++ bitsS "0101010" ++ bitsS "111"))
  f := f + (← expect "rawBit: 0xFF 0x7F 0x80 (stuffed bit skipped)"
    ((readRaw [0xFF, 0x7F, 0x80] 23).1 ==
      bitsS "11111111" ++ bitsS "1111111" ++ bitsS "10000000"))
  f := f + (← expect "rawBit: 0xFF then marker 0x90: ones, not consumed"
    (let (bs, s) := readRaw [0xFF, 0x90, 0x00] 20
     bs == List.replicate 20 true && s.pos == 1))
  f := f + (← expect "rawBit: 0xFF 0x8F is data (7 bits 0001111)"
    ((readRaw [0xFF, 0x8F] 15).1 == bitsS "11111111" ++ bitsS "0001111"))
  f := f + (← expect "rawBit: empty segment reads ones"
    ((readRaw [] 17).1 == List.replicate 17 true))
  f := f + (← expect "rawPack / rawBit round trip with stuffing"
    (let bits := List.replicate 30 true ++ bitsS "0110" ++ List.replicate 9 true
     let bytes := rawPack bits
     (readRaw bytes bits.length).1 == bits && bytes.take 2 == [0xFF, 0x7F]))
  return f

/-! ## 3. Hand-traced blocks -/

/-- Encode hand-written `(context, decision)` pairs as one MQ codeword and decode them as the
given plain-mode block. -/
def handDecode (w h : Nat) (o : Orientation) (K passes : Nat) (pairs : List (Nat × Bool)) :
    Option (Array Int) :=
  ok? (decodeValues (CodeBlock.ofData w h o K 0 passes (Encode.MQ.encodeAll initialStates pairs)))

/-- As `handDecode`, in mode `m` (single codeword, so no termall/bypass). -/
def handDecodeM (m : Mode) (w h : Nat) (o : Orientation) (K passes : Nat)
    (pairs : List (Nat × Bool)) : Option (Array Int) :=
  ok? (decodeValues
    (CodeBlock.ofData w h o K 0 passes (Encode.MQ.encodeAll initialStates pairs) m))

/-- Hand-traced plain-mode cases: `(name, result, expected)`. -/
def handCases : List (String × Option (Array Int) × Array Int) :=
  [ -- 1×1, K = 1, value −1: cleanup, ZC context 0 (all neighbours insignificant, column
    -- shorter than 4 so no run-length), sign context 9 with XORbit 0.
    ("1x1 value -1", handDecode 1 1 .LL 1 1 [(0, true), (9, true)], #[-1]),
    -- 1×1, K = 2, value 3: cleanup p=1 (ZC 0, sign 9), SP p=0 (nothing: no insignificant
    -- coefficient), MR p=0 first refinement with no neighbour → context 14, cleanup p=0
    -- (nothing).
    ("1x1 value 3, all 4 passes",
      handDecode 1 1 .HH 2 4 [(0, true), (9, false), (14, true)], #[3]),
    ("1x1 value 3 truncated after pass 0",
      handDecode 1 1 .HH 2 1 [(0, true), (9, false)], #[2]),
    -- 2×1 LL, K = 1, values [1, −1]: (0,0) ZC 0, sign 9; (1,0) ΣH = 1 → context 5; sign:
    -- W positive → H = 1, V = 0 → context 12, XORbit 0, negative → decision 1.
    ("2x1 LL [1,-1]", handDecode 2 1 .LL 1 1 [(0, true), (9, false), (5, true), (12, true)],
      #[1, -1]),
    -- 1×2 HL, values [1, 1]: (0,1) has ΣV = 1; HL swaps H and V → row "ΣH = 1, ΣV = 0,
    -- ΣD = 0" → context 5; sign: V = 1, H = 0 → context 10, XORbit 0.
    ("1x2 HL [1,1]", handDecode 1 2 .HL 1 1 [(0, true), (9, false), (5, true), (10, false)],
      #[1, 1]),
    -- 1×2 LH: ΣV = 1 → context 3 (LL/LH table).
    ("1x2 LH [1,0]", handDecode 1 2 .LH 1 1 [(0, true), (9, false), (3, false)], #[1, 0]),
    -- 1×4 column, all zero: run-length decision 0.
    ("1x4 run of zeros", handDecode 1 4 .LL 1 1 [(17, false)], #[0, 0, 0, 0]),
    -- 1×4 [0, 0, −1, 0]: run-length 1, UNIFORM 1 then 0 → row 2, sign context 9 (negative →
    -- 1), then row 3 normally: ΣV = 1 → context 3, decision 0.
    ("1x4 run interrupted at row 2",
      handDecode 1 4 .LL 1 1 [(17, true), (18, true), (18, false), (9, true), (3, false)],
      #[0, 0, -1, 0]),
    -- 1×5: one full stripe column (run-length) and a 1-high column (never run-length).
    ("1x5 run + short column",
      handDecode 1 5 .LL 1 1 [(17, false), (0, true), (9, false)], #[0, 0, 0, 0, 1]),
    -- 1×4 K = 2, values [2, 1, 0, 0]: cleanup p=1: run-length 1, row 0, sign 9; rows 1–3
    -- normal: (0,1) ΣV=1 → 3, decision 0; (0,2), (0,3) context 0, decision 0.
    -- SP p=0: (0,1) has a significant neighbour: context 3, decision 1, sign: V = 1 → 10.
    -- (0,2): neighbour (0,1) now significant → context 3, decision 0. (0,3): no
    -- significant neighbour → skipped. MR p=0: (0,0) first refinement, neighbour (0,1)
    -- significant → 15, decision 0. Cleanup p=0: the column is not run-length (others are
    -- significant or visited); only (0,3) is coded: N = (0,2) insignificant → context 0,
    -- decision 0.
    ("1x4 K=2 [2,1,0,0]",
      handDecode 1 4 .LL 2 4 [(17, true), (18, false), (18, false), (9, false),
        (3, false), (0, false), (0, false),
        (3, true), (10, false), (3, false),
        (15, false),
        (0, false)],
      #[2, 1, 0, 0]),
    -- Vertically causal (D.7), 1×5 LL, K = 2, values [0, 0, 0, 1, 2].
    -- Without the flag: cleanup p=1: stripe 0 run-length 0; row 4: ZC 0 → 1, sign 9 → 0.
    -- SP p=0: row 2 has no significant neighbour (skipped); row 3 sees row 4 (S): ZC 3 → 1,
    -- sign V = +1 → 10, 0. MR p=0: row 4, first refinement, N = row 3 significant → 15, 0.
    -- Cleanup p=0: stripe 0 not run-length (row 3 significant): rows 0, 1 ZC 0 → 0; row 2
    -- is visited? no — row 2 was skipped in SP, so it is coded: N insignificant, S = row 3
    -- significant → ZC 3 → 0.
    ("1x5 [0,0,0,1,2] not causal",
      handDecode 1 5 .LL 2 4 [(17, false), (0, true), (9, false),
        (3, true), (10, false),
        (15, false),
        (0, false), (0, false), (3, false)],
      #[0, 0, 0, 1, 2]),
    -- With the flag: row 3 does not see row 4 (next stripe), so SP p=0 codes nothing; MR
    -- p=0: row 4 (stripe 1) still sees row 3 above, insignificant → 14, 0. Cleanup p=0:
    -- stripe 0 is run-length (row 3's S neighbour is hidden): run 1, UNIFORM 1, 1 → row 3,
    -- sign context 9 (S hidden), positive → 0.
    ("1x5 [0,0,0,1,2] vertically causal",
      handDecodeM { vertCausal := true } 1 5 .LL 2 4 [(17, false), (0, true), (9, false),
        (14, false),
        (17, true), (18, true), (18, true), (9, false)],
      #[0, 0, 0, 1, 2]),
    -- Segmentation symbols (D.5): 1×1 value −1 followed by 1010 in the UNIFORM context.
    ("1x1 -1 with segmentation symbol",
      handDecodeM { segSymbols := true } 1 1 .LL 1 1
        [(0, true), (9, true), (18, true), (18, false), (18, true), (18, false)],
      #[-1]) ]

/-- A 1×1 bypass block with `K = 5`, value `±17 = ±0b10001`: passes 0–9 in one MQ segment
(cleanup p=4: ZC 0 → 1, sign 9; MR p=3: context 14 → 0; MR p=2, p=1: context 16 → 0); pass
10 (raw SP p=0) codes nothing, pass 11 (raw MR p=0) reads one raw bit from `rawByte`
(its MSB); pass 12 (MQ cleanup p=0) codes nothing. -/
def bypassBlock (neg : Bool) (rawByte : UInt8) (passes : Nat) : CodeBlock :=
  let mq := Encode.MQ.encodeAll initialStates [(0, true), (9, neg), (14, false), (16, false),
    (16, false)]
  { width := 1, height := 1, orient := .LH, mode := { bypass := true }, numBitPlanes := 5,
    zeroBitPlanes := 0,
    segments := ([⟨mq, 10⟩, ⟨[rawByte], 2⟩, ⟨[], 1⟩].take
      (if passes ≤ 10 then 1 else if passes ≤ 12 then 2 else 3)).map fun s =>
        if s.passes == 10 then { s with passes := min passes 10 }
        else if s.passes == 2 then { s with passes := min (passes - 10) 2 } else s }

/-- The 1×1 `K = 2` value-3 block (`(0,T) (9,F)`, ∅, `(14,T)`, ∅) in mode `m`, its MQ passes
coded with `mqSegment` and split as `segmentPasses` says. -/
def value3Block (m : Mode) : CodeBlock :=
  let passes : List (List (Nat × Bool)) := [[(0, true), (9, false)], [], [(14, true)], []]
  let sizes := segmentPasses m 4 0
  let (segs, _, _) := sizes.foldl (fun (acc, rest, cxs) k =>
      let (bytes, cxs) := mqSegment cxs (rest.take k) m.reset m.predTerm
      (acc ++ [(⟨bytes, k⟩ : Segment)], rest.drop k, cxs))
    (([] : List Segment), passes, initContexts initialStates)
  { width := 1, height := 1, orient := .HH, mode := m, numBitPlanes := 2, zeroBitPlanes := 0,
    segments := segs }

/-- Hand-traced cases in the other modes. -/
def runModeHand : IO Nat := do
  let mut f := 0
  for (name, got, want) in handCases do
    f := f + (← expect s!"hand: {name} (got {got})" (got == some want))
  f := f + (← expect "bypass 1x1 17 (raw bit 1)"
    (ok? (decodeValues (bypassBlock false 0x80 13)) == some #[17]))
  f := f + (← expect "bypass 1x1 -16 (raw bit 0)"
    (ok? (decodeValues (bypassBlock true 0x7F 13)) == some #[-16]))
  f := f + (← expect "bypass 1x1 17 truncated after the raw MR pass"
    (ok? (decodeValues (bypassBlock false 0xC0 12)) == some #[17]))
  f := f + (← expect "bypass 1x1 truncated after pass 9"
    (ok? (decodeValues (bypassBlock false 0x80 10)) == some #[16]))
  f := f + (← expect "bypass 1x1 raw segment past its end reads 1"
    (ok? (decodeValues { bypassBlock false 0x00 13 with
      segments := (bypassBlock false 0 13).segments.map fun s =>
        if s.passes == 2 then { s with data := [] } else s }) == some #[17]))
  -- segmentation symbols: bad symbol tolerated by default, an error when strict
  let segGood := CodeBlock.ofData 1 1 .LL 1 0 1 (Encode.MQ.encodeAll initialStates
    [(0, true), (9, true), (18, true), (18, false), (18, true), (18, false)])
    { segSymbols := true }
  let segBad := CodeBlock.ofData 1 1 .LL 1 0 1 (Encode.MQ.encodeAll initialStates
    [(0, true), (9, true), (18, true), (18, true), (18, true), (18, false)])
    { segSymbols := true }
  f := f + (← expect "segsym good: strict ok, no bad symbols"
    ((ok? (decodeCodeBlockStrict segGood)).isSome && (decodeState segGood).badSegSymbols == 0))
  f := f + (← expect "segsym bad: lenient decode ok, value kept"
    ((ok? (decodeValues segBad)) == some #[-1] && (decodeState segBad).badSegSymbols == 1))
  f := f + (← expect "segsym bad: strict decode is malformed"
    (match err? (decodeCodeBlockStrict segBad) with
     | some (.malformed _ _) => true
     | _ => false))
  -- reset / termall / predictable termination on the value-3 block
  for st in [0, 2, 4, 6, 16, 18, 20, 22] do
    f := f + (← expect s!"value-3 block, style {st}"
      (ok? (decodeValues (value3Block (Mode.ofStyle st))) == some #[3]))
  f := f + (← expect "termall value-3 block has 4 segments"
    ((value3Block { termAll := true }).segments.length == 4))
  return f

/-! ## 5. Test-only reference encoder (all modes) -/

/-- A block to encode: geometry, coded bit-planes `K`, zero bit-planes, magnitudes and signs
in raster order (`mags[i] < 2^K`). -/
structure Blk where
  /-- Width. -/
  w : Nat
  /-- Height. -/
  h : Nat
  /-- Orientation. -/
  orient : Orientation
  /-- Coded bit-planes. -/
  K : Nat
  /-- Zero (missing) bit-planes. -/
  zbp : Nat
  /-- Magnitudes, raster order. -/
  mags : Array Nat
  /-- Signs (`true` = negative), raster order. -/
  negs : Array Bool

/-- Encoder state: padded significance/sign arrays (`(w+2) × (h+2)`), raster arrays for the
pass marks, the decoder-visible magnitude and its last plane, the symbols of the current
pass, and the mode switches. -/
structure E where
  /-- Significance, padded. -/
  sig : Array Bool
  /-- Sign, padded. -/
  neg : Array Bool
  /-- Coded in this bit-plane's SP pass, raster. -/
  vis : Array Bool
  /-- Refined at least once, raster. -/
  refd : Array Bool
  /-- Magnitude bits the decoder knows, raster. -/
  known : Array Nat
  /-- Last decoded plane, raster. -/
  lsb : Array Nat
  /-- Coded symbols of the current pass, in order. -/
  out : Array Sym
  /-- The current pass is raw (bypass). -/
  raw : Bool := false
  /-- Vertically causal context formation. -/
  vsc : Bool := false
  /-- Segmentation symbols after cleanup passes. -/
  segsym : Bool := false

/-- Padded index of raster position `(x, y)` shifted by `(dx, dy) ∈ {0,1,2}²` (1 = centre). -/
def pidx (b : Blk) (x y dx dy : Nat) : Nat := (y + dy) * (b.w + 2) + (x + dx)

/-- Raster index. -/
def ridx (b : Blk) (x y : Nat) : Nat := y * b.w + x

/-- The padded neighbour is masked by vertically causal formation: the row below the last
row of a stripe. -/
def masked (e : E) (y dy : Nat) : Bool := e.vsc && dy == 2 && y % 4 == 3

/-- Significance at padded offset, as 0/1. -/
def s01 (b : Blk) (e : E) (x y dx dy : Nat) : Nat :=
  if !masked e y dy && e.sig.getD (pidx b x y dx dy) false then 1 else 0

/-- `(ΣH, ΣV, ΣD)` from the padded array. -/
def counts (b : Blk) (e : E) (x y : Nat) : Nat × Nat × Nat :=
  (s01 b e x y 0 1 + s01 b e x y 2 1,
   s01 b e x y 1 0 + s01 b e x y 1 2,
   s01 b e x y 0 0 + s01 b e x y 2 0 + s01 b e x y 0 2 + s01 b e x y 2 2)

/-- Total number of significant neighbours. -/
def nsig (b : Blk) (e : E) (x y : Nat) : Nat :=
  let (h, v, d) := counts b e x y
  h + v + d

/-- Signed contribution `σ·(1 − 2·neg)` of a padded neighbour. -/
def contrib (b : Blk) (e : E) (x y dx dy : Nat) : Int :=
  if !masked e y dy && e.sig.getD (pidx b x y dx dy) false then
    (if e.neg.getD (pidx b x y dx dy) false then -1 else 1)
  else 0

/-- Clamp to `[-1, 1]`. -/
def clamp1 (v : Int) : Int := max (-1) (min 1 v)

/-- Bit `p` of the magnitude at `(x, y)`. -/
def magBit (b : Blk) (x y p : Nat) : Bool := (b.mags.getD (ridx b x y) 0) / 2 ^ p % 2 == 1

/-- Append one decision: an MQ decision in `cx`, or a raw bit in a raw pass. -/
def emit (e : E) (cx : Nat) (d : Bool) : E :=
  { e with out := e.out.push (if e.raw then .raw d else .mq cx d) }

/-- The coefficient becomes significant at plane `p`: code its sign, update the model. -/
def makeSig (b : Blk) (e : E) (x y p : Nat) (vis : Bool) : E :=
  let hc := clamp1 (contrib b e x y 0 1 + contrib b e x y 2 1)
  let vc := clamp1 (contrib b e x y 1 0 + contrib b e x y 1 2)
  let (cx, xr) := scContext hc vc
  let ng := b.negs.getD (ridx b x y) false
  let e := if e.raw then { e with out := e.out.push (.raw ng) } else emit e cx (ng != xr)
  let i := ridx b x y
  let pi := pidx b x y 1 1
  { e with
    sig := e.sig.setIfInBounds pi true, neg := e.neg.setIfInBounds pi ng,
    known := e.known.setIfInBounds i (e.known.getD i 0 + 2 ^ p),
    lsb := e.lsb.setIfInBounds i p, vis := e.vis.setIfInBounds i vis }

/-- Zero-code `(x, y)` at plane `p` (both SP and cleanup). -/
def zc (b : Blk) (e : E) (x y p : Nat) (vis : Bool) : E :=
  let (hh, vv, dd) := counts b e x y
  let bit := magBit b x y p
  let e := emit e (zcContext b.orient hh vv dd) bit
  if bit then makeSig b e x y p vis else { e with vis := e.vis.setIfInBounds (ridx b x y) vis }

/-- Is `(x, y)` significant in the model? -/
def isSig (b : Blk) (e : E) (x y : Nat) : Bool := e.sig.getD (pidx b x y 1 1) false

/-- Was `(x, y)` coded in this plane's SP pass? -/
def isVis (b : Blk) (e : E) (x y : Nat) : Bool := e.vis.getD (ridx b x y) false

/-- Significance propagation pass at plane `p`. -/
def encSP (b : Blk) (e : E) (p : Nat) : E := Id.run do
  let mut e := e
  for s in [0:(b.h + 3) / 4] do
    for x in [0:b.w] do
      for y in [4 * s:min (4 * s + 4) b.h] do
        if !isSig b e x y && nsig b e x y > 0 then
          e := zc b e x y p true
  return e

/-- Magnitude refinement pass at plane `p`. -/
def encMR (b : Blk) (e : E) (p : Nat) : E := Id.run do
  let mut e := e
  for s in [0:(b.h + 3) / 4] do
    for x in [0:b.w] do
      for y in [4 * s:min (4 * s + 4) b.h] do
        if isSig b e x y && !isVis b e x y then
          let i := ridx b x y
          let bit := magBit b x y p
          e := emit e (mrContext (!e.refd.getD i false) (nsig b e x y > 0)) bit
          let k := e.known.getD i 0 + if bit then 2 ^ p else 0
          e := { e with
            refd := e.refd.setIfInBounds i true, lsb := e.lsb.setIfInBounds i p,
            known := e.known.setIfInBounds i k }
  return e

/-- Cleanup pass at plane `p` (with run-length coding), then the segmentation symbol (if
enabled), then clear the SP marks. -/
def encCU (b : Blk) (e : E) (p : Nat) : E := Id.run do
  let mut e := e
  for s in [0:(b.h + 3) / 4] do
    for x in [0:b.w] do
      let y0 := 4 * s
      let full := y0 + 4 ≤ b.h
      let quiet := (List.range 4).all fun r =>
        !isSig b e x (y0 + r) && !isVis b e x (y0 + r) && nsig b e x (y0 + r) == 0
      let mut start := y0
      if full && quiet then
        match (List.range 4).find? (fun r => magBit b x (y0 + r) p) with
        | none =>
          e := emit e 17 false
          start := y0 + 4
        | some r =>
          e := emit e 17 true
          e := emit e 18 (r / 2 == 1)
          e := emit e 18 (r % 2 == 1)
          e := makeSig b e x (y0 + r) p false
          start := y0 + r + 1
      for y in [start:min (y0 + 4) b.h] do
        if !isSig b e x y && !isVis b e x y then
          e := zc b e x y p false
  if e.segsym then
    for d in [true, false, true, false] do
      e := emit e 18 d
  return { e with vis := e.vis.map fun _ => false }

/-- The pass list of a block with `K` coded planes: `(kind, plane)` with kind 0 = SP,
1 = MR, 2 = CU. -/
def encPasses (K : Nat) : List (Nat × Nat) :=
  if K = 0 then []
  else [(2, K - 1)] ++ ((List.range (K - 1)).reverse.flatMap fun p => [(0, p), (1, p), (2, p)])

/-- OpenJPEG's raw-pass rule (`opj_t1_decode_cblk`): bypass, an SP or MR pass, and
`bpno_plus_one ≤ numbps − 4`, i.e. `p + 1 + 4 ≤ K`. -/
def encIsRaw (m : Mode) (K kind p : Nat) : Bool := m.bypass && kind < 2 && p + 5 ≤ K

/-- Run the first `n` passes in mode `m`; returns the model and, per pass, whether it is raw
and its coded symbols. -/
def encodeBlock (m : Mode) (b : Blk) (n : Nat) : E × List (Bool × List Sym) :=
  let e0 : E := {
    sig := Array.replicate ((b.w + 2) * (b.h + 2)) false,
    neg := Array.replicate ((b.w + 2) * (b.h + 2)) false,
    vis := Array.replicate (b.w * b.h) false,
    refd := Array.replicate (b.w * b.h) false,
    known := Array.replicate (b.w * b.h) 0,
    lsb := Array.replicate (b.w * b.h) 0, out := #[],
    vsc := m.vertCausal, segsym := m.segSymbols }
  let (e, acc) := (encPasses b.K).take n |>.foldl (fun (e, acc) (k, p) =>
      let raw := encIsRaw m b.K k p
      let e := { e with out := #[], raw }
      let e := if k == 0 then encSP b e p else if k == 1 then encMR b e p else encCU b e p
      (e, acc.push (raw, e.out.toList)))
    (e0, (#[] : Array (Bool × List Sym)))
  (e, acc.toList)

/-- The MQ decision trace of the first `n` plain-mode passes of `b` (all passes are MQ-coded
in plain mode): the form `Encode.MQ.encodeAll initialStates` takes. -/
def plainTrace (b : Blk) (n : Nat) : List (Nat × Bool) :=
  (encodeBlock Mode.plain b n).2.flatMap fun p => mqPairs p.2

/-- OpenJPEG's codeword-segment rule (`opj_t2_init_seg`): `maxpasses` 1 with termall; with
bypass 10 for the first segment, then 2 after a segment of 1 or 10, else 1; otherwise
unbounded. Returns the pass counts of the segments holding `n` passes. -/
def encSegSizes (m : Mode) (n : Nat) : List Nat :=
  let rec go : Nat → Nat → Nat → List Nat
    | 0, _, _ => []
    | fuel + 1, rem, prevMax =>
      if rem = 0 then [] else
      let mx := if m.termAll then 1 else if m.bypass then
          (if prevMax == 0 then 10 else if prevMax == 1 || prevMax == 10 then 2 else 1)
        else rem
      let k := min mx rem
      k :: go fuel (rem - k) mx
  go (n + 1) n 0

/-- Build the codeword segments of the coded passes (each segment raw iff its passes are). -/
def buildSegments (m : Mode) (passes : List (Bool × List Sym)) : List Segment :=
  let (segs, _, _) := (encSegSizes m passes.length).foldl (fun (acc, rest, cxs) k =>
      let ps := rest.take k
      let isRaw := ps.any (·.1)
      if isRaw then
        (acc.push ⟨rawPack (ps.flatMap fun (_, s) => rawBitsOf s), k⟩, rest.drop k,
          if m.reset then initContexts initialStates else cxs)
      else
        let (bytes, cxs) := mqSegment cxs (ps.map fun (_, s) => mqPairs s) m.reset m.predTerm
        (acc.push ⟨bytes, k⟩, rest.drop k, cxs))
    ((#[] : Array Segment), passes, initContexts initialStates)
  segs.toList

/-- The encoder's model of the decoder state at raster index `i`. -/
def modelCoeff (b : Blk) (e : E) (i : Nat) : Coeff :=
  let x := i % b.w
  let y := i / b.w
  let sg := isSig b e x y
  {
    sig := sg, sign := sg && e.neg.getD (pidx b x y 1 1) false,
    mag := e.known.getD i 0, visited := e.vis.getD i false, refined := e.refd.getD i false,
    lsbPlane := if sg then e.lsb.getD i 0 else 0 }

/-! ## Random blocks -/

/-- One splitmix64 step: the output word and the next state. -/
def splitmix (s : UInt64) : UInt64 × UInt64 :=
  let s := s + 0x9E3779B97F4A7C15
  let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), s)

/-- A pseudo-random value below `m` (`m > 0`) and the next state. -/
def below (s : UInt64) (m : Nat) : Nat × UInt64 :=
  let (z, s) := splitmix s
  ((z >>> 11).toNat % m, s)

/-- A side length: mostly small, sometimes up to 64. -/
def genSide (s : UInt64) : Nat × UInt64 :=
  let (sel, s) := below s 10
  if sel < 5 then let (v, s) := below s 8; (v + 1, s)
  else if sel < 8 then let (v, s) := below s 24; (v + 1, s)
  else let (v, s) := below s 64; (v + 1, s)

/-- Draw a random block. -/
def genBlk (s : UInt64) : Blk × UInt64 := Id.run do
  let (w, s) := genSide s
  let (h, s) := genSide s
  let h := if w * h > 4096 then 4096 / w else h
  let (oi, s) := below s 4
  let (K, s) := below s 14
  let K := K + 1
  let (zbp, s) := below s 4
  let (density, s) := below s 5       -- 0: very sparse … 4: dense
  let (topBits, s) := below s K       -- most magnitudes use fewer than K bits
  let mut s := s
  let mut mags : Array Nat := #[]
  let mut negs : Array Bool := #[]
  for _ in [0:w * h] do
    let (r, s1) := below s 8
    let (big, s2) := below s1 16
    let bits := if big == 0 then K else topBits + 1
    let (m, s3) := below s2 (2 ^ bits)
    let (ng, s4) := below s3 2
    s := s4
    mags := mags.push (if r < density + 2 then m else 0)
    negs := negs.push (ng == 1)
  return ({ w, h, orient := Orientation.all.getD oi .LL, K, zbp, mags, negs }, s)

/-- `m` with the bits below plane `q` cleared. -/
def truncAt (m q : Nat) : Nat := m / 2 ^ q * 2 ^ q

/-- Statistics of a check: raw segments, `0xFF` bytes in raw segments. -/
structure Stats where
  /-- Raw segments decoded. -/
  rawSegs : Nat := 0
  /-- `0xFF` bytes inside raw segments. -/
  rawFF : Nat := 0
  /-- Segments in all. -/
  segs : Nat := 0

/-- Encode the first `n` passes of `b` in mode `m`, decode them with the spec (strict); the
error description if any check fails, and statistics. -/
def checkBlk (m : Mode) (b : Blk) (n : Nat) : Option String × Stats :=
  let (e, passes) := encodeBlock m b n
  let segments := buildSegments m passes
  let rawIdx := (List.range segments.length).filter fun j =>
    let start := ((segments.take j).map (·.passes)).sum
    isRawPass m start
  let st : Stats := {
    rawSegs := rawIdx.length,
    rawFF := (rawIdx.map fun j => ((segments.getD j default).data.filter (· == 0xFF)).length).sum,
    segs := segments.length }
  let cb : CodeBlock := {
    width := b.w, height := b.h, orient := b.orient, mode := m, numBitPlanes := b.K + b.zbp,
    zeroBitPlanes := b.zbp, segments }
  let res := match decodeCodeBlockStrict cb with
    | .error err => some s!"decode error {repr err}"
    | .ok cs =>
      let total := 3 * b.K - 2
      let p := passPlane b.K (n - 1)
      let bad := (List.range (b.w * b.h)).filter fun i =>
        let c := cs.getD i {}
        let orig := b.mags.getD i 0
        let model := c == modelCoeff b e i
        let prefixOk :=
          if n == total then c.mag == orig
          else c.mag == truncAt orig p || c.mag == truncAt orig (p + 1)
        let signOk := c.mag == 0 || c.sign == b.negs.getD i false
        let sigOk := c.sig == (c.mag != 0)
        !(model && prefixOk && signOk && sigOk && cs.size == b.w * b.h)
      if bad.isEmpty then none
      else some s!"{b.w}x{b.h} {repr b.orient} K={b.K} passes {n}/{total}: {bad.length} bad coefficients (first {bad.head?})"
  (res.map fun msg => s!"style {repr m}: {msg}", st)

/-! ## Runner -/

/-- Default number of random blocks (block `i` uses style `i mod 64`). -/
def defaultN : Nat := 640

/-- Number of random blocks: `JPEG2000_TIER1_BLOCKS` if set to a number, else `defaultN`. -/
def numBlocks : IO Nat := do
  match ← IO.getEnv "JPEG2000_TIER1_BLOCKS" with
  | some v => return v.trimAscii.toString.toNat?.getD defaultN
  | none => return defaultN

/-- `cb` in style `st`, with empty segments structured as `segmentPasses` says. -/
def styled (cb : CodeBlock) (st : Nat) : CodeBlock :=
  { cb with
    mode := Mode.ofStyle st
    segments := (segmentPasses (Mode.ofStyle st) cb.numPasses 0).map fun k => ⟨[], k⟩ }

/-- Scan-order and argument-check unit tests. -/
def runUnits : IO Nat := do
  let mut f := 0
  let bad := (List.range 10).flatMap fun w => (List.range 14).filterMap fun h =>
    if scanOk w h then none else some (w, h)
  f := f + (← expect s!"scanOrder is a D.1 permutation for all w ≤ 9, h ≤ 13 (bad: {bad})"
    bad.isEmpty)
  f := f + (← expect "scanOrder 2 5 literal" (scanOrder 2 5 ==
    [(0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (1, 3), (0, 4), (1, 4)]))
  f := f + (← expect "scanOrder 3 2 literal" (scanOrder 3 2 ==
    [(0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (2, 1)]))
  f := f + (← expect "stripeColumns 1 9 shape"
    ((stripeColumns 1 9).map List.length == [4, 4, 1]))
  f := f + (← expect "scanOrder 64 64 permutation" (scanOk 64 64))
  f := f + (← expect "passKind / passPlane, K = 3"
    ((List.range 7).map (fun i => (passKind i, passPlane 3 i)) ==
      [(.cleanup, 2), (.sigProp, 1), (.magRef, 1), (.cleanup, 1),
       (.sigProp, 0), (.magRef, 0), (.cleanup, 0)]))
  f := f + (← expect "Mode.ofStyle 0 is plain, 1..63 are not"
    ((Mode.ofStyle 0).isPlain && (List.range 63).all fun b => !(Mode.ofStyle (b + 1)).isPlain))
  f := f + (← expect "Mode.ofStyle 0x28" (Mode.ofStyle 0x28 == { vertCausal := true, segSymbols := true }))
  -- argument checks
  let base := CodeBlock.ofData 4 4 .LL 3 1 4 []
  f := f + (← expect "3K-2 passes accepted" ((err? (decodeCodeBlock base)).isNone))
  f := f + (← expect "3K-1 passes rejected (exact)"
    ((err? (decodeCodeBlockExact { base with segments := Segment.single 5 [] })).isSome))
  f := f + (← expect "3K-1 passes: the extra pass dropped (task 5.8)"
    ((ok? (decodeCodeBlock { base with segments := Segment.single 5 [] })).isSome &&
      ok? (decodeCodeBlock { base with segments := Segment.single 5 [] }) ==
        ok? (decodeCodeBlock base)))
  f := f + (← expect "passes with K = 0 rejected (exact)"
    ((err? (decodeCodeBlockExact { base with zeroBitPlanes := 3, segments := Segment.single 1 [] }))
      |>.isSome))
  f := f + (← expect "passes with K = 0 dropped: zeros (task 5.8)"
    ((ok? (decodeValues { base with zeroBitPlanes := 3, segments := Segment.single 1 [] })) ==
      some (Array.replicate 16 0)))
  f := f + (← expect "K = 0, no passes: zeros"
    ((ok? (decodeValues { base with zeroBitPlanes := 5, segments := [] })) ==
      some (Array.replicate 16 0)))
  f := f + (← expect "1025 wide rejected"
    ((err? (decodeCodeBlock { base with width := 1025, height := 1 })).isSome))
  f := f + (← expect "64 x 65 rejected"
    ((err? (decodeCodeBlock { base with width := 64, height := 65 })).isSome))
  let wide : CodeBlock := { base with width := 1024, height := 4, segments := Segment.single 1 [] }
  f := f + (← expect "1024 x 4 accepted" ((err? (decodeCodeBlock wide)).isNone))
  f := f + (← expect "every style accepted with its segmentPasses structure"
    ((List.range 64).all fun st => (err? (decodeCodeBlock (styled base st))).isNone))
  f := f + (← expect "termall with one segment rejected"
    (match err? (decodeCodeBlock { base with mode := { termAll := true } }) with
     | some (.malformed _ _) => true
     | _ => false))
  f := f + (← expect "plain with two segments rejected"
    ((err? (decodeCodeBlock { base with segments := [⟨[], 2⟩, ⟨[], 2⟩] })).isSome))
  f := f + (← expect "zero-pass segment rejected"
    ((err? (decodeCodeBlock { base with segments := [⟨[], 4⟩, ⟨[1], 0⟩] })).isSome))
  f := f + (← expect "0 x 7 block: empty"
    ((ok? (decodeValues { base with width := 0, height := 7 })).map (·.size) == some 0))
  return f

/-- A dense block with every magnitude `2^K − 1`: raw refinement passes are all ones, so raw
segments contain `0xFF` bytes and stuffed bits. -/
def onesBlk (w h K : Nat) : Blk :=
  { w, h, orient := .HH, K, zbp := 0, mags := Array.replicate (w * h) (2 ^ K - 1),
    negs := (Array.range (w * h)).map (· % 3 == 0) }

/-- Runs the suite; returns the number of failures. -/
def run : IO Nat := do
  let mut f ← runUnits
  f := f + (← runModeUnits)
  f := f + (← runModeHand)
  let n ← numBlocks
  let mut s : UInt64 := 0x2026_0302
  let mut fails := 0
  let mut checks := 0
  let mut coeffs := 0
  let mut rawSegs := 0
  let mut rawFF := 0
  let mut segs := 0
  let t0 ← IO.monoMsNow
  -- all-ones blocks in every bypass style
  for st in (List.range 32).map (2 * · + 1) do
    for (w, h, K) in [(8, 8, 8), (5, 13, 9)] do
      let b := onesBlk w h K
      for np in [3 * K - 2, 11, 14] do
        checks := checks + 1
        let (r, stt) := checkBlk (Mode.ofStyle st) b np
        rawSegs := rawSegs + stt.rawSegs
        rawFF := rawFF + stt.rawFF
        segs := segs + stt.segs
        if let some msg := r then
          fails := fails + 1
          if fails ≤ 5 then IO.eprintln s!"  mismatch: {msg}"
  for i in [0:n] do
    let m := Mode.ofStyle (i % 64)
    let (b, s1) := genBlk s
    let total := 3 * b.K - 2
    let (t1, s2) := below s1 total
    let (t2, s3) := below s2 total
    s := s3
    for np in [total, t1 + 1, t2 + 1, 1] do
      checks := checks + 1
      coeffs := coeffs + b.w * b.h
      let (r, stt) := checkBlk m b np
      rawSegs := rawSegs + stt.rawSegs
      rawFF := rawFF + stt.rawFF
      segs := segs + stt.segs
      match r with
      | none => pure ()
      | some msg =>
        fails := fails + 1
        if fails ≤ 5 then IO.eprintln s!"  mismatch: {msg}"
  let t1 ← IO.monoMsNow
  IO.println s!"  tier1 spec round trips (64 styles): {checks - fails}/{checks} ok ({n} random blocks, {coeffs} coefficients, {segs} segments, {rawSegs} raw, {rawFF} raw 0xFF bytes, {t1 - t0} ms)"
  f := f + (← expect s!"random encode/decode round trips ({fails} failures)" (fails == 0))
  f := f + (← expect "raw segments with 0xFF bytes were exercised" (rawFF > 0))
  return f

end JPEG2000.Tests.Tier1Spec
