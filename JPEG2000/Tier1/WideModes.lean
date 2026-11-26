import JPEG2000.Tier1.WidePlain

/-!
# Wide Tier-1 coding passes with style flags (Plan.md §§4, 5.1, 7; T.800 D.3–D.7)

A stripe column can use the ordinary wide MQ kernels even in vertically causal mode:
clipping their read height at the end of the stripe removes precisely the hidden
neighbours. Writes still use the full raster stride. The raw passes use the production
D.6 reader, storing exact magnitude and last coded plane in the same raster.
-/

namespace JPEG2000.Tier1.WideModes

open JPEG2000.Tier2.Geometry (Band)

/-- Wide pass state across MQ or raw segments, including the cumulative D.5 error count. -/
structure State where
  /-- Active reader, saved MQ contexts and exact coefficient raster. -/
  block : WidePlain.State
  /-- Number of cleanup segmentation symbols different from 1010. -/
  badSegSymbols : Nat := 0

/-- Exclusive visible row limit for a stripe column under the D.7 causal flag. -/
def visibleHeight (vc : Bool) (h : Nat) (col : List (Nat × Nat)) : Nat :=
  if vc then min h (4 * ((col.headD (0, 0)).2 / 4 + 1)) else h

/-- A raw D.6 decision on the wide state, retaining the saved MQ contexts. -/
def rawDecision (s : WidePlain.State) : Bool × WidePlain.State :=
  let (v, mq) := rawBit s.mq
  (v, { s with mq })

/-- Raw significance propagation. The sign immediately follows a positive significance
decision, with no sign prediction. -/
def rawPropagate (w h p : Nat) (s : WidePlain.State) (pos : Nat × Nat) : WidePlain.State :=
  let c := WidePlain.readCell w h s.cells pos.1 pos.2
  if !c.sig && WidePlain.hasNeighbour w h s.cells pos then
    let (v, s) := rawDecision s
    if v then
      let (neg, s) := rawDecision s
      WidePlain.put s w pos { c with sig := true, sign := neg, mag := c.mag + (1 <<< p),
                                     visited := true, lsbPlane := p }
    else WidePlain.put s w pos { c with visited := true }
  else s

/-- Raw magnitude refinement. Even a zero refinement records the plane that was read. -/
def rawRefine (w h p : Nat) (s : WidePlain.State) (pos : Nat × Nat) : WidePlain.State :=
  let c := WidePlain.readCell w h s.cells pos.1 pos.2
  if c.sig && !c.visited then
    let (v, s) := rawDecision s
    WidePlain.put s w pos { c with mag := c.mag + (if v then 1 <<< p else 0),
                                   refined := true, lsbPlane := p }
  else s

/-- Decode the coefficient decisions of an absolute pass, using precomputed stripe columns.
Cleanup always uses MQ. -/
def passBody (vc raw : Bool) (w h : Nat) (b : Band) (K : Nat)
    (cols : List (List (Nat × Nat))) (s : WidePlain.State) (i : Nat) : WidePlain.State :=
  let p := passPlane K i
  match passKind i with
  | 0 => cols.foldl (fun t col =>
      let limit := visibleHeight vc h col
      col.foldl (if raw then rawPropagate w limit p else WidePlain.propagate w limit b p) t) s
  | 1 => cols.foldl (fun t col =>
      let limit := visibleHeight vc h col
      col.foldl (if raw then rawRefine w limit p else WidePlain.refineCell w limit p) t) s
  | _ =>
    let t := cols.foldl (fun t col => WidePlain.cleanupColumn w (visibleHeight vc h col) b p t col) s
    { t with cells := t.cells.map fun c => { c with visited := false } }

/-- Consume the four UNIFORM decisions, including the low zero of the D.5 symbol. -/
def segSymbol (s : State) : State :=
  let (b3, t) := WidePlain.bit s.block 18
  let (b2, t) := WidePlain.bit t 18
  let (b1, t) := WidePlain.bit t 18
  let (b0, t) := WidePlain.bit t 18
  ⟨t, if b3 && !b2 && b1 && !b0 then s.badSegSymbols else s.badSegSymbols + 1⟩

/-- One pass of any style. The segment driver supplies the active reader and absolute
pass number. Segmentation symbols precede the Table D.7 context reset. -/
def runPass (m : Style) (w h : Nat) (b : Band) (K : Nat) (cols : List (List (Nat × Nat)))
    (s : State) (i : Nat) : State :=
  let t := { s with block := passBody m.vertCausal (isRawPass m i) w h b K cols s.block i }
  let t := if m.segSymbols && passKind i == 2 then segSymbol t else t
  if m.reset then { t with block.mq.cx := MQ.tier1Contexts } else t

end JPEG2000.Tier1.WideModes
