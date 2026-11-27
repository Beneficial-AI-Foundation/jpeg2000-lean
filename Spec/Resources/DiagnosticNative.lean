import Spec.Resources.DiagnosticHeader
import Spec.Resources.DiagnosticOutput
import Spec.Resources.DiagnosticColour
import Spec.Resources.DiagnosticReconstruction

/-!
# Public native diagnostic composition (Plan.md §§3–5, 7, S3)

The actual output allocator, centred tile, and destination writer instantiate the native
traversal. The header trace precedes that traversal on every admitted reduction. A caller
reduction above its ceiling is handled by `DiagnosticHeader.public_refusal` before parsing.
-/

namespace JPEG2000.Spec.Resources.DiagnosticNative

open DiagnosticCost

/-- Public limits bound the source axes and all proposed output sizes at each callback.
Allocation constructs no text. Tile and write allowances count all reached constructions. -/
def allowances : DiagnosticReconstruction.Allowances where
  scalar := fun L _ => max (DiagnosticOutput.scalarCap L) (DiagnosticColour.scalarCap L)
  allocation := fun _ _ => 0
  tile := fun L _ => DiagnosticColour.eventCap L
  placement := fun L _ => DiagnosticOutput.writeCount L

/-- The three concrete continuations of native traversal on these bytes and reduction. -/
noncomputable def callbacks (L : Limits) (data : ByteArray) (red : Nat) :
    DiagnosticReconstruction.Callbacks allowances L data red where
  allocation admitted parsed :=
    (DiagnosticOutput.allocationTrace admitted parsed).raiseCap (Nat.le_max_left ..)
  tile r := (DiagnosticReconstruction.tileTraceOfCentered r.layout
    (DiagnosticColour.centeredTrace r.hit r.prepared r.rank r.store r.layout).trace).raiseCap
      (Nat.le_max_right ..)
  placement := by
    intro h initial idx v cb g c dst sat sources pre tail r visited _ before _ _ _
    let tile : JPEG2000.Decode.CenteredTile := ⟨g,c,sources,0⟩
    exact (DiagnosticOutput.publicWriteTrace visited r.prepared r.rank before tile).raiseCap
      (Nat.le_max_left ..)

/-- A common bound for scalar leaves throughout header and native image reconstruction. -/
def scalarCap (L : Limits) (bytes : Nat) :=
  max (DiagnosticHeader.scalarCap L bytes) (DiagnosticReconstruction.scalarCap allowances L bytes)

/-- Maximum header and traversal event count, including all preceding successful tiles. -/
def eventBudget (L : Limits) (bytes : Nat) :=
  DiagnosticReconstruction.countBound allowances L bytes + DiagnosticHeader.eventBudget L bytes

private noncomputable def suffix {L : Limits} {data : ByteArray} {red : Nat}
    (admitted : red ≤ L.maxDecompLevels) {h : Header.Header} (parsed : Header.parse L data = .ok h) :
    Trace (scalarCap L data.size) (JPEG2000.Decode.nativeFromHeader L h data red)
      (DiagnosticReconstruction.countBound allowances L data.size) :=
  let t := DiagnosticReconstruction.nativeTrace (callbacks L data red) admitted parsed
  widen (t.raiseCap (Nat.le_max_right ..))
    (DiagnosticReconstruction.public_bounds (callbacks L data red) admitted parsed).2.1

/-- Ordered diagnostic expressions of the complete native API after the caller's
reduction check passes. A failed header prevents all allocation and tile callbacks. -/
noncomputable def nativeTrace {L : Limits} (data : ByteArray) {red : Nat}
    (admitted : red ≤ L.maxDecompLevels) :
    Trace (scalarCap L data.size) (decodeCodestream L data red) (eventBudget L data.size) := by
  let t := bindTrace ((DiagnosticHeader.headerTrace L data).raiseCap (Nat.le_max_left ..))
    (fun _ parsed => suffix admitted parsed)
  refine ⟨t.messages,t.countBound,fun e err => t.origin e ?_⟩
  have gate := (Limits.check_eq_ok_iff L JPEG2000.Decode.loc .decompLevels red).2 admitted
  simpa only [decodeCodestream, gate, Equiv.ok_bind] using err

private theorem stages {α β : Type} {i j cap : Nat} {r : Except Error α} {f : α → Except Error β}
    (t : Trace cap r i) (k : ∀ a, r = .ok a → Trace cap (f a) j) :
    (∀ e, r = .error e → (bindTrace t k).messages = t.messages) ∧
    (∀ a (ok : r = .ok a), (bindTrace t k).messages = t.messages ++ (k a ok).messages) := by
  constructor
  · intro e h; cases h; rfl
  · intro a h; cases h; rfl

/-- The complete native trace is precisely the header trace up to a failed header.
On a valid header it appends all messages of the reached native suffix in order. -/
theorem native_events {L : Limits} (data : ByteArray) {red : Nat} (admitted : red ≤ L.maxDecompLevels) :
    let first := (DiagnosticHeader.headerTrace L data).raiseCap (Nat.le_max_left _ _ :
      DiagnosticHeader.scalarCap L data.size ≤ scalarCap L data.size)
    let t := nativeTrace data admitted
    (∀ e, Header.parse L data = .error e → t.messages = first.messages) ∧
    (∀ h (parsed : Header.parse L data = .ok h), t.messages = first.messages ++
      ((DiagnosticReconstruction.nativeTrace (callbacks L data red) admitted parsed).raiseCap
        (Nat.le_max_right _ _ : _ ≤ scalarCap L data.size)).messages) :=
  stages _ (fun _ p => suffix admitted p)

/-- Work, cumulative temporary storage and the final retained native error have closed
bounds in the input length and the caller's limits, before any error rendering. -/
theorem native_bounds {L : Limits} (data : ByteArray) {red : Nat} (admitted : red ≤ L.maxDecompLevels) :
    let t := nativeTrace data admitted
    let cap := scalarCap L data.size
    let budget := eventBudget L data.size * Text.workBound cap 128 24
    (t.messages.map (fun m => m.2.tree.work)).sum ≤ budget ∧
    (t.messages.map (fun m => m.2.tree.storage)).sum ≤ budget ∧
    (∀ e, decodeCodestream L data red = .error e →
      storedPayload false e ≤ 6 + Text.byteBound cap 128 24 + 2 * bits cap) :=
  ⟨(trace_cost _).1,trace_storage _,fun _ e => trace_retained (nativeTrace data admitted) e⟩

end JPEG2000.Spec.Resources.DiagnosticNative
