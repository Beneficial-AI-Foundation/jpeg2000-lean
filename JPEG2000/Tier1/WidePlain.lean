import JPEG2000.Tier1.Modes

/-!
# Wide plain-mode Tier-1 decoding (Plan.md §§4, 5.1, 5.4; T.800 Annexes C, D, H)

The wide fallback uses the production MQ decoder and Table D.1 functions. A raster cell
stores its exact magnitude and the last plane that contributed a decision, including a zero
refinement. Neighbours are read from the raster as needed. The stripe columns are built once
per segment and reused for each pass. Allocation is bounded by the A.6.1 block dimensions and
the E-2 and RGN header fields. The pass kernel also accepts a starting pass index for use
across MQ codeword boundaries.
-/

namespace JPEG2000.Tier1.WidePlain

open JPEG2000.Tier2.Geometry (Band)

/-- The largest coded-plane count representable by E-2 plus an eight-bit RGN max-shift. -/
def maxCodedPlanes : Nat := 7 + 31 - 1 + 255

/-- A raster coefficient and its Annex D coding state. -/
structure Cell where
  /-- Magnitude at the quantisation-index scale. -/
  mag : Nat := 0
  /-- Sign decision, true for a negative coefficient. -/
  sign : Bool := false
  /-- Plane of the latest significance or refinement bit, zero while insignificant. -/
  lsbPlane : Nat := 0
  /-- Significance state. -/
  sig : Bool := false
  /-- Coded in this plane's significance propagation pass. -/
  visited : Bool := false
  /-- At least one refinement bit has been decoded. -/
  refined : Bool := false
  deriving Inhabited, Repr, DecidableEq

/-- Signed quantisation index, before the Annex E reconstruction offset. -/
def Cell.value (c : Cell) : Int := if c.sign then -(c.mag : Int) else c.mag

/-- State carried from one coding pass to the next. -/
structure State where
  /-- Production MQ registers and contexts. -/
  mq : MQ.Dec
  /-- Coefficient array in raster order. -/
  cells : Array Cell

/-- Read one neighbour, treating coordinates outside the block as insignificant. -/
def readCell (w h : Nat) (cs : Array Cell) (x y : Int) : Cell :=
  if 0 ≤ x ∧ x < w ∧ 0 ≤ y ∧ y < h then cs.getD (y.toNat * w + x.toNat) {} else {}

/-- Horizontal, vertical and diagonal significance counts. -/
def counts (w h : Nat) (cs : Array Cell) (x y : Int) : Nat × Nat × Nat :=
  let bit := fun u v => (readCell w h cs u v).sig.toNat
  (bit (x - 1) y + bit (x + 1) y, bit x (y - 1) + bit x (y + 1),
   bit (x - 1) (y - 1) + bit (x + 1) (y - 1) + bit (x - 1) (y + 1) + bit (x + 1) (y + 1))

/-- Table D.1 for the selected band. -/
def zeroContext (b : Band) (n : Nat × Nat × Nat) : Nat :=
  let (h, v, d) := n
  match b with
  | .LL | .LH => zcLLLH h v d
  | .HL => zcLLLH v h d
  | .HH => zcHHcol (h + v) d

/-- Table D.2 contribution of an adjacent coefficient. -/
def Cell.contribution (c : Cell) : Int :=
  if c.sig then (if c.sign then -1 else 1) else 0

/-- Table D.3 sign context and XOR predictor. -/
def signCoding (w h : Nat) (cs : Array Cell) (x y : Int) : Nat × Bool :=
  let c := fun u v => (readCell w h cs u v).contribution
  let hc := pairContrib (c (x - 1) y) (c (x + 1) y)
  let vc := pairContrib (c x (y - 1)) (c x (y + 1))
  let ctx := if hc = 0 then (if vc = 0 then 9 else 10)
             else if vc = 0 then 12 else if (hc < 0) = (vc < 0) then 13 else 11
  (ctx, decide (hc < 0 ∨ hc = 0 ∧ vc < 0))

/-- Decode an MQ decision, advancing the coder and retaining the coefficient array. -/
def bit (s : State) (cx : Nat) : Bool × State :=
  let (v, mq) := s.mq.decode cx
  (v, { s with mq })

/-- Record one updated cell. -/
def put (s : State) (w : Nat) (pos : Nat × Nat) (c : Cell) : State :=
  { s with cells := s.cells.setIfInBounds (pos.2 * w + pos.1) c }

/-- D.3.2 sign decision and first nonzero magnitude bit. -/
def become (w h p : Nat) (vis : Bool) (s : State) (pos : Nat × Nat) : State :=
  let (x, y) := pos
  let (cx, pred) := signCoding w h s.cells x y
  let (v, s) := bit s cx
  let c := readCell w h s.cells x y
  put s w pos { c with sig := true, sign := v != pred, visited := vis, lsbPlane := p,
                        mag := c.mag + (1 <<< p) }

/-- D.3.1 zero coding, also used by the ordinary cleanup step. -/
def zeroCode (w h : Nat) (b : Band) (p : Nat) (vis : Bool) (s : State) (pos : Nat × Nat) : State :=
  let (x, y) := pos
  let (v, s) := bit s (zeroContext b (counts w h s.cells x y))
  if v then become w h p vis s pos
  else put s w pos { readCell w h s.cells x y with visited := vis }

/-- Whether the coefficient has any significant neighbour. -/
def hasNeighbour (w h : Nat) (cs : Array Cell) (pos : Nat × Nat) : Bool :=
  let (a, b, c) := counts w h cs pos.1 pos.2
  a + b + c != 0

/-- One significance propagation decision, when eligible. -/
def propagate (w h : Nat) (b : Band) (p : Nat) (s : State) (pos : Nat × Nat) : State :=
  if !(readCell w h s.cells pos.1 pos.2).sig && hasNeighbour w h s.cells pos then
    zeroCode w h b p true s pos else s

/-- D.3.3 refinement advances the last plane on either MQ decision. -/
def refineCell (w h p : Nat) (s : State) (pos : Nat × Nat) : State :=
  let c := readCell w h s.cells pos.1 pos.2
  if c.sig && !c.visited then
    let cx := if c.refined then 16 else if hasNeighbour w h s.cells pos then 15 else 14
    let (v, s) := bit s cx
    put s w pos { c with mag := c.mag + (if v then 1 <<< p else 0), refined := true, lsbPlane := p }
  else s

/-- One ordinary cleanup step. -/
def cleanupCell (w h : Nat) (b : Band) (p : Nat) (s : State) (pos : Nat × Nat) : State :=
  let c := readCell w h s.cells pos.1 pos.2
  if !c.sig && !c.visited then zeroCode w h b p false s pos else s

/-- One D.3.4 column, including run interruption and its uncoded prefix. -/
def cleanupColumn (w h : Nat) (b : Band) (p : Nat) (s : State) (col : List (Nat × Nat)) : State :=
  let ordinary := cleanupCell w h b p
  let eligible := fun (x, y) =>
    let c := readCell w h s.cells x y
    !c.sig && !c.visited && !hasNeighbour w h s.cells (x, y)
  if col.length == 4 && col.all eligible then
    let (run, s) := bit s 17
    if !run then s else
      let (hi, s) := bit s 18
      let (lo, s) := bit s 18
      match col.drop ((if hi then 2 else 0) + (if lo then 1 else 0)) with
      | [] => s
      | pos :: rest => rest.foldl ordinary (become w h p false s pos)
  else col.foldl ordinary s

/-- D.1 columns in stripe order, clipping the bottom stripe to the block height. -/
def columns (w h : Nat) : List (List (Nat × Nat)) :=
  (List.range ((h + 3) / 4)).flatMap fun stripe =>
    let y := 4 * stripe
    (List.range w).map fun x => (List.range (min 4 (h - y))).map fun r => (x, y + r)

/-- D.2 dispatch over the precomputed stripe columns. -/
def runPass (w h : Nat) (b : Band) (K : Nat) (cols : List (List (Nat × Nat)))
    (s : State) (i : Nat) : State :=
  let p := passPlane K i
  match passKind i with
  | 0 => cols.foldl (fun t col => col.foldl (propagate w h b p) t) s
  | 1 => cols.foldl (fun t col => col.foldl (refineCell w h p) t) s
  | _ =>
    let t := cols.foldl (cleanupColumn w h b p) s
    { t with cells := t.cells.map fun c => { c with visited := false } }

/-- Decode a consecutive range of passes, preserving the last coded plane at truncation. -/
def runPasses (w h : Nat) (b : Band) (K first n : Nat) (s : State) : State :=
  (List.range' first n).foldl (runPass w h b K (columns w h)) s

/-- Restart the MQ registers on each segment, retaining the contexts, raster, and absolute
pass index. Plain ROI blocks can extend beyond the first 109-pass segment. -/
def runSegments (data : ByteArray) (w h : Nat) (b : Band) (K : Nat) :
    List Seg → Nat → State → Array Cell
  | [], _, s => s.cells
  | sg :: rest, first, s =>
    let mq := MQ.Dec.init data sg.start sg.stop s.mq.cx
    let s := runPasses w h b K first sg.passes { s with mq }
    runSegments data w h b K rest (first + sg.passes) s

/-- The Annex A.6.1 dimension and coefficient-count bounds, checked before allocation. -/
def validateSize (w h : Nat) : Except Error Unit :=
  if w > 1024 ∨ h > 1024 ∨ w * h > 4096 then
    .error (.malformed tier1Loc "code-block larger than 1024 x 1024 or 4096 coefficients")
  else .ok ()

/-- Decode a plain block from its Tier-2 segments. Check every original byte range, including
discarded segments. Clamp surplus passes before checking D.4 segment structure. Validate
the geometry and coded-plane budget before allocating the coefficient raster. -/
def decodeCodeBlockSegs (data : ByteArray) (segments : Array Seg) (w h : Nat) (b : Band)
    (Mb zbp : Nat) : Except Error (Array Cell) := do
  if badRange data segments then
    throw (.malformed tier1Loc "code-block data range outside the buffer")
  validateSize w h
  let K := Mb - zbp
  let kept := clampSegs segments K
  let n := segsPasses kept
  if 0 < n ∧ K > maxCodedPlanes then
    throw (.malformed tier1Loc "coded bit-plane count exceeds the E-2 and RGN header fields")
  if 0 < n ∧ n > 3 * K - 2 then
    throw (.malformed tier1Loc "more coding passes than 3K - 2 for K coded bit-planes")
  if kept.toList.map (·.passes) != segmentPasses {} n 0 then
    throw (.malformed tier1Loc "codeword segments do not match the code-block style")
  let initial : State := ⟨MQ.Dec.init data 0 0 MQ.tier1Contexts, Array.replicate (w * h) {}⟩
  return runSegments data w h b K kept.toList 0 initial

/-- Decode a plain block supplied as one codeword. An empty pass prefix has no segments,
but its supplied byte range is still checked. -/
def decodeCodeBlock (data : ByteArray) (start stop w h : Nat) (b : Band)
    (Mb zbp numPasses : Nat) : Except Error (Array Cell) :=
  if start > stop ∨ stop > data.size then do
    -- The single-codeword API reports an invalid block size before its range error.
    validateSize w h
    throw (.malformed tier1Loc "code-block data range outside the buffer")
  else
    let segments := if numPasses = 0 then #[] else #[⟨start, stop, numPasses⟩]
    decodeCodeBlockSegs data segments w h b Mb zbp

end JPEG2000.Tier1.WidePlain
