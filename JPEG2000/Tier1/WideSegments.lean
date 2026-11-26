import JPEG2000.Tier1.WideModes

/-!
# Wide segmented code-block decoding (Plan.md §§4, 5.1, 5.4, 7; T.800 D.3–D.7)

Tier-2 supplies byte ranges and pass counts. Each segment restarts the reader at its own
range, carrying the MQ contexts, coefficient raster, absolute pass index and D.5 error
count across the boundary. The wide plain decoder handles the plain-like styles.
-/

namespace JPEG2000.Tier1.WideSegments

open JPEG2000.Tier2.Geometry (Band)

/-- Restart the reader for the first pass of a D.4 codeword segment. -/
def restart (m : Style) (data : ByteArray) (sg : Seg) (first : Nat) (s : WideModes.State) :
    WideModes.State :=
  let cx := s.block.mq.cx
  let mq := if isRawPass m first then rawInit data sg.start sg.stop cx
            else MQ.Dec.init data sg.start sg.stop cx
  { s with block.mq := mq }

/-- Traverse a validated D.4 partition. The stripe columns are shared by all its passes. -/
def runSegments (m : Style) (data : ByteArray) (w h : Nat) (b : Band) (K : Nat)
    (cols : List (List (Nat × Nat))) : List Seg → Nat → WideModes.State → WideModes.State
  | [], _, s => s
  | sg :: rest, first, s =>
    let s := restart m data sg first s
    let s := (List.range' first sg.passes).foldl (WideModes.runPass m w h b K cols) s
    runSegments m data w h b K cols rest (first + sg.passes) s

/-- Check the header plane budget and the pass counts of the retained segments before
building the stripe columns or allocating the raster. -/
def validatePasses (m : Style) (kept : Array Seg) (K : Nat) : Except Error Unit := do
  let n := segsPasses kept
  if 0 < n ∧ K > WidePlain.maxCodedPlanes then
    throw (.malformed tier1Loc "coded bit-plane count exceeds the E-2 and RGN header fields")
  if 0 < n ∧ n > 3 * K - 2 then
    throw (.malformed tier1Loc "more coding passes than 3K - 2 for K coded bit-planes")
  if kept.toList.map (·.passes) != segmentPasses m n 0 then
    throw (.malformed tier1Loc "codeword segments do not match the code-block style")

/-- Decode the Tier-2 ranges of an ordinary block in any Table A.19 style, with exact
wide coefficients. Every supplied range is checked before dropping passes below plane
zero. Set `strict` to reject a bad D.5 segmentation symbol. -/
def decodeCodeBlockSegs (data : ByteArray) (segments : Array Seg) (w h : Nat) (b : Band)
    (style : UInt8) (Mb zbp : Nat) (strict : Bool := false) : Except Error (Array WidePlain.Cell) := do
  let m := Style.ofByte style
  if m.decodesAsPlain then
    return ← WidePlain.decodeCodeBlockSegs data segments w h b Mb zbp
  if badRange data segments then
    throw (.malformed tier1Loc "code-block data range outside the buffer")
  WidePlain.validateSize w h
  let K := Mb - zbp
  let kept := clampSegs segments K
  validatePasses m kept K
  let initial : WideModes.State :=
    ⟨⟨MQ.Dec.init data 0 0 MQ.tier1Contexts, Array.replicate (w * h) {}⟩, 0⟩
  let s := runSegments m data w h b K (WidePlain.columns w h) kept.toList 0 initial
  if strict && s.badSegSymbols != 0 then
    throw (.malformed tier1Loc "bad segmentation symbol")
  return s.block.cells

end JPEG2000.Tier1.WideSegments
