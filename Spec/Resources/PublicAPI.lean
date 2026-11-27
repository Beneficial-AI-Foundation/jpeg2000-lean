import Spec.Resources.NativeCost
import Spec.Resources.DiagnosticNative
import Spec.ColorResources.DiagnosticImage

/-!
# Resource bounds at the byte-input APIs (Plan.md §§3–4, S2/S3)

The observations count the source operations and logical allocations in the native,
mapping and display meters once each. Diagnostic construction adds work, temporary
storage and the final retained record. Optional interleaving uses its own byte limit.
-/

namespace JPEG2000.Spec.Resources.PublicAPI

open DiagnosticCost ColorResources

/-- Largest computed diagnostic scalar in the native and image stages. -/
def scalarCap (L : Limits) (n : Nat) :=
  max (DiagnosticNative.scalarCap L n) (DiagnosticImage.imageCap L n)

/-- Actual native trace under the common scalar bound used at the image API. -/
noncomputable def native {L : Limits} {data : ByteArray} {opts : DecodeOptions} (ok : opts.reduce ≤ L.maxDecompLevels) :=
  (DiagnosticNative.nativeTrace (L := L) data (red := opts.reduce) ok).raiseCap
    (Nat.le_max_left _ (DiagnosticImage.imageCap L data.size))

/-- Complete ordered expression trace after reduction admission, on any image result. -/
noncomputable def trace {L : Limits} {data : ByteArray} {opts : DecodeOptions}
    (ok : opts.reduce ≤ L.maxDecompLevels) :
    Trace (scalarCap L data.size) (JPEG2000.decode L data opts)
      (DiagnosticNative.eventBudget L data.size + 1) :=
  (DiagnosticImage.compose_native (native (data := data) ok) (Nat.le_max_right ..)).choose

/-- Native failure propagates with its entire trace. Native success appends the
actual image suffix and preserves messages from earlier successful retries. -/
theorem trace_stages {L : Limits} {data : ByteArray} {opts : DecodeOptions}
    (ok : opts.reduce ≤ L.maxDecompLevels) :
    let first := native (data := data) ok
    (∀ e, decodeCodestream L data opts.reduce = .error e →
      JPEG2000.decode L data opts = .error e ∧ (trace (data := data) ok).messages = first.messages) ∧
    (∀ d (hd : decodeCodestream L data opts.reduce = .ok d),
      (trace (data := data) ok).messages =
        first.messages ++ ((DiagnosticImage.imageTrace (opts := opts) hd).raiseCap
          (Nat.le_max_right ..)).messages) :=
  (DiagnosticImage.compose_native (native (data := data) ok) (Nat.le_max_right ..)).choose_spec

/-- Every source-stage charge already includes its own logical allocations. -/
def sourceCharge (L : Limits) (data : ByteArray) (opts : DecodeOptions) :=
  (NativeCost.measure L data opts.reduce).2 + (MappingPrefix.measuredPrefix L data opts).2 +
    (DisplayPrefix.measuredDisplay L data opts).2

/-- Closed reservation for the three non-diagnostic source meters. -/
def sourceBudget (L : Limits) (n : Nat) :=
  NativeCost.budget L n + MappingPrefix.metadataBudget L n + DisplayPrefix.displayBudget L n

private theorem source_bound (L : Limits) (data : ByteArray) (opts : DecodeOptions) :
    sourceCharge L data opts ≤ sourceBudget L data.size :=
  Nat.add_le_add (Nat.add_le_add (NativeCost.decode_work L data opts.reduce).2.2.2.1
    (MappingPrefix.image_mapping_work L data opts).2) (DisplayPrefix.display_work L data opts).2

/-- Diagnostic construction work, cumulative temporary storage and the retained
error. A successful API result has no retained error record. -/
structure Diagnostics where
  /-- Cost of the reached text constructors. -/
  work : Nat
  /-- Temporary storage for the same constructors. -/
  temporary : Nat
  /-- Retained error fields, including binary widths of internally computed values. -/
  record : Nat

private def retained {α : Type} (borrow : Bool) : Except Error α → Nat
  | .ok _ => 0
  | .error e => storedPayload borrow e

private def ofTrace {α : Type} {cap k : Nat} {r : Except Error α} (t : Trace cap r k) : Diagnostics :=
  ⟨(t.messages.map (fun m => m.2.tree.work)).sum,
    (t.messages.map (fun m => m.2.tree.storage)).sum, retained false r⟩

private theorem ofTrace_bound {α : Type} {cap k : Nat} {r : Except Error α} (t : Trace cap r k) :
    (ofTrace t).work ≤ k * Text.workBound cap 128 24 ∧
    (ofTrace t).temporary ≤ k * Text.workBound cap 128 24 ∧
    (ofTrace t).record ≤ 6 + Text.byteBound cap 128 24 + 2 * bits cap := by
  refine ⟨(trace_cost t).1, trace_storage t, ?_⟩
  change retained false r ≤ _
  cases h : r with
  | ok => exact Nat.zero_le _
  | error e => exact trace_retained t h

/-- Observe the reached decode diagnostics. Excess caller reduction is rejected before
any construction, and the original caller value is borrowed by the error record. -/
noncomputable def diagnostics (L : Limits) (data : ByteArray) (opts : DecodeOptions) : Diagnostics :=
  if ok : opts.reduce ≤ L.maxDecompLevels then
    ofTrace (trace (data := data) ok)
  else ⟨0,0,retained true (JPEG2000.decode L data opts)⟩

/-- Explicit bound for temporary storage or work of every reached expression. -/
def expressionBudget (L : Limits) (n : Nat) :=
  (DiagnosticNative.eventBudget L n + 1) * Text.workBound (scalarCap L n) 128 24

/-- Retained record budget including the early caller-owned reduction case. -/
def recordBudget (L : Limits) (n : Nat) :=
  max 7 (6 + Text.byteBound (scalarCap L n) 128 24 + 2 * bits (scalarCap L n))

/-- An excessive caller reduction returns its exact typed error with seven units
of retained storage and no text construction, regardless of the reduction's width. -/
theorem reduction_refusal {L : Limits} {data : ByteArray} {opts : DecodeOptions}
    (excess : L.maxDecompLevels < opts.reduce) :
    JPEG2000.decode L data opts =
      .error (.limitExceeded Decode.loc .decompLevels opts.reduce L.maxDecompLevels) ∧
    diagnostics L data opts = ⟨0,0,7⟩ := by
  have result := (DiagnosticBox.public_admission_excess (d := data) (opts := opts) (.inl excess)).2.2.1
  rw [ite_eq_left excess] at result
  exact ⟨result, by rw [diagnostics, dite_eq_right (Nat.not_le_of_lt excess), result]; rfl⟩

private theorem diagnostics_bound (L : Limits) (data : ByteArray) (opts : DecodeOptions) :
    let d := diagnostics L data opts
    d.work ≤ expressionBudget L data.size ∧ d.temporary ≤ expressionBudget L data.size ∧
      d.record ≤ recordBudget L data.size := by
  dsimp only
  by_cases ok : opts.reduce ≤ L.maxDecompLevels
  · rw [diagnostics, dite_eq_left ok]
    obtain ⟨w,s,r⟩ := ofTrace_bound (trace (data := data) ok)
    exact ⟨w,s,Nat.le_trans r (Nat.le_max_right ..)⟩
  · rw [(reduction_refusal (data := data) (Nat.lt_of_not_ge ok)).2]
    exact ⟨Nat.zero_le _, Nat.zero_le _, Nat.le_max_left ..⟩

/-- The public value and two inclusive resource observations. The source charge
bounds operations and logical allocation, so it contributes to each column. -/
structure Observation (α : Type) where
  /-- Result of the observed API. -/
  result : Except Error α
  /-- Source charge plus text construction and retained fields. -/
  work : Nat
  /-- Cumulative logical storage, including the final owned record. -/
  storage : Nat

/-- Resource observation of the actual public image call on any input. -/
noncomputable def measure (L : Limits) (data : ByteArray) (opts : DecodeOptions) : Observation Image :=
  let src := sourceCharge L data opts
  let d := diagnostics L data opts
  ⟨(DisplayPrefix.measuredDisplay L data opts).1, src+d.work+d.record, src+d.temporary+d.record⟩

/-- Work and cumulative logical storage ceiling, determined before inspecting input contents. -/
def budget (L : Limits) (bytes : Nat) :=
  sourceBudget L bytes + expressionBudget L bytes + recordBudget L bytes

/-- S2/S3 for the public image decoder: the measured result equals the total public
call on every byte string, both charges fit the closed budget, and every returned
image satisfies its native, colour, channel and output allocation certificates. -/
theorem decode_resources (L : Limits) (data : ByteArray) (opts : DecodeOptions) :
    let m := measure L data opts
    m.result = JPEG2000.decode L data opts ∧ m.work ≤ budget L data.size ∧
      m.storage ≤ budget L data.size ∧
      ∀ img, m.result = .ok img → ColorResources.Within L data opts img := by
  obtain ⟨w,s,r⟩ := diagnostics_bound L data opts
  have src := source_bound L data opts
  have eqn := (DisplayPrefix.display_work L data opts).1
  exact ⟨eqn,Nat.add_le_add (Nat.add_le_add src w) r,Nat.add_le_add (Nat.add_le_add src s) r,
    fun _ h => ColorResources.decode_resources (eqn.symm.trans h)⟩

/-- The public image observation preserves the first reached limit at entry, native
allocation and display allocation. Each stage uses its own proposed sizes. -/
theorem allocation_limits (L : Limits) (data : ByteArray) (opts : DecodeOptions) :
    let run := (measure L data opts).result
    (L.maxDecompLevels < opts.reduce ∨ L.maxInputBytes < data.size →
      run = .error (if L.maxDecompLevels < opts.reduce then
        .limitExceeded Decode.loc .decompLevels opts.reduce L.maxDecompLevels else
        .limitExceeded (.atOffset .box 0) .inputBytes data.size L.maxInputBytes)) ∧
    (∀ h, opts.reduce ≤ L.maxDecompLevels → Header.parse L data = .ok h →
      let rs := JPEG2000.NativeOutput.layout h.siz opts.reduce
      let cells := JPEG2000.NativeOutput.cells rs
      let bytes := JPEG2000.NativeOutput.decodedBytes rs
      L.maxWorkSamples < cells ∨ L.maxDecodedBytes < bytes →
      run = .error (if L.maxWorkSamples < cells then
        .limitExceeded Decode.loc .workSamples cells L.maxWorkSamples else
        .limitExceeded Decode.loc .decodedBytes bytes L.maxDecodedBytes)) ∧
    (∀ r cs, DiagnosticImage.displayInputs L data opts = .ok (r,cs) →
      let cells := DiagnosticImage.cells r cs
      let bytes := DiagnosticImage.byteCount r cs
      L.maxWorkSamples < cells ∨ L.maxDecodedBytes < bytes →
      run = .error (if L.maxWorkSamples < cells then
        .limitExceeded Image.loc .workSamples cells L.maxWorkSamples else
        .limitExceeded Image.loc .decodedBytes bytes L.maxDecodedBytes)) := by
  dsimp only
  rw [(decode_resources L data opts).1]
  refine ⟨fun h => (DiagnosticBox.public_admission_excess h).2.2.1, ?_,
    fun _ _ reached => (DiagnosticImage.display_refusal reached).2.2⟩
  intro h ok parsed excess
  let rs := JPEG2000.NativeOutput.layout h.siz opts.reduce
  let cells := JPEG2000.NativeOutput.cells rs
  let bytes := JPEG2000.NativeOutput.decodedBytes rs
  have failure := fun e (he : JPEG2000.NativeOutput.allocOutput L h.siz opts.reduce = .error e) =>
    ((DiagnosticOutput.public_allocation (opts := opts) ok parsed).2 e he).2.2.1
  split
  next over =>
    exact failure _ ((DiagnosticOutput.allocation_refusal ok parsed _).2 (.inl ⟨over,rfl⟩))
  next fit =>
    exact failure _ ((DiagnosticOutput.allocation_refusal ok parsed _).2
      (.inr ⟨Nat.le_of_not_gt fit,excess.resolve_left fit,rfl⟩))

/-- Native diagnostics on any requested reduction. The initial refusal borrows the
caller's value before header parsing, as at the image boundary. -/
noncomputable def nativeDiagnostics (L : Limits) (data : ByteArray) (red : Nat) : Diagnostics :=
  if ok : red ≤ L.maxDecompLevels then ofTrace (DiagnosticNative.nativeTrace data ok)
  else ⟨0,0,retained true (decodeCodestream L data red)⟩

/-- Work or storage ceiling at the native API. This excludes the JP2 display suffix. -/
def nativeBudget (L : Limits) (n : Nat) :=
  let cap := DiagnosticNative.scalarCap L n
  NativeCost.budget L n + DiagnosticNative.eventBudget L n * Text.workBound cap 128 24 +
    max 7 (6 + Text.byteBound cap 128 24 + 2 * bits cap)

/-- The native value and inclusive work and logical storage, with all diagnostics. -/
noncomputable def measureNative (L : Limits) (data : ByteArray) (red : Nat) :
    Observation CodestreamImage :=
  let src := NativeCost.measure L data red
  let d := nativeDiagnostics L data red
  ⟨src.1,src.2+d.work+d.record,src.2+d.temporary+d.record⟩

/-- The native bounds hold even when an earlier caller, header or tile check refuses. -/
theorem codestream_resources (L : Limits) (data : ByteArray) (red : Nat) :
    let m := measureNative L data red
    m.result = decodeCodestream L data red ∧ m.work ≤ nativeBudget L data.size ∧
      m.storage ≤ nativeBudget L data.size ∧
      ∀ img, m.result = .ok img → NativeResources.Within L data red img := by
  obtain ⟨erases,_,_,src,returned⟩ := NativeCost.decode_work L data red
  refine ⟨erases,?_,?_,returned⟩ <;> unfold measureNative nativeDiagnostics nativeBudget <;> dsimp only
  all_goals
    split
    next ok =>
      obtain ⟨w,s,r⟩ := ofTrace_bound (DiagnosticNative.nativeTrace data ok)
      first
      | exact Nat.add_le_add (Nat.add_le_add src w) (Nat.le_trans r (Nat.le_max_right ..))
      | exact Nat.add_le_add (Nat.add_le_add src s) (Nat.le_trans r (Nat.le_max_right ..))
    next no =>
      have over := Nat.lt_of_not_ge no
      let opts : DecodeOptions := { reduce := red }
      have raw := (DiagnosticBox.public_admission_excess (opts := opts) (d := data) (.inl over)).2.1
      rw [ite_eq_left over] at raw
      change decodeCodestream L data red = _ at raw
      rw [raw]
      exact Nat.add_le_add (Nat.add_le_add src (Nat.zero_le _)) (Nat.le_max_left ..)

/-- Charge the independent byte conversion's retained record only on paths reaching
that conversion. A propagated image error has already been charged. -/
def interleaveRecord (L : Limits) (data : ByteArray) (opts : DecodeOptions) (external : Limits)
    (alpha wide : Bool) (mode : Scaling) : Nat :=
  match JPEG2000.decode L data opts with
  | .error _ => 0
  | .ok img => retained false
      (if wide then img.interleaved16 external alpha mode else img.interleaved8 external alpha mode)

/-- Observation of decoding followed by either public interleaver, with its independently
chosen limit record, channel selection and scaling. -/
noncomputable def measureInterleaved (L : Limits) (data : ByteArray) (opts : DecodeOptions)
    (external : Limits) (alpha wide : Bool) (mode : Scaling) : Observation ByteArray :=
  let image := measure L data opts
  let suffix := DisplayPrefix.measuredInterleaving L data opts external alpha wide mode
  let extra := suffix.2 + interleaveRecord L data opts external alpha wide mode
  ⟨suffix.1,image.work+extra,image.storage+extra⟩

/-- Complete public byte-buffer bound. Eight extra units and the maximum proposed
byte count bound the binary field of a refusing conversion, even before allocation. -/
def interleavedBudget (L external : Limits) (n : Nat) :=
  budget L n + (DisplayPrefix.interleavingBudget L external + (8 + 2*L.maxImageArea*(L.maxComponents+2)))

private theorem interleave_record_bound (L : Limits) (data : ByteArray) (opts : DecodeOptions)
    (external : Limits) (alpha wide : Bool) (mode : Scaling) :
    interleaveRecord L data opts external alpha wide mode ≤ 8 + 2*L.maxImageArea*(L.maxComponents+2) := by
  unfold interleaveRecord
  cases h : JPEG2000.decode L data opts with
  | error => exact Nat.zero_le _
  | ok img =>
    obtain ⟨_,_,_,_,refuses⟩ := DiagnosticImage.interleaver_diagnostics h external alpha wide mode
    dsimp only
    cases he : (if wide then img.interleaved16 external alpha mode else img.interleaved8 external alpha mode) with
    | ok => exact Nat.zero_le _
    | error e =>
      obtain ⟨_,hc,record⟩ := refuses _ he
      change storedPayload false e ≤ _
      rw [record]
      have factor : (if wide then 2 else 1) ≤ 2 := by cases wide <;> decide
      have count := Nat.le_trans hc (Nat.mul_le_mul_left _ factor)
      rw [Nat.mul_comm _ 2, ← Nat.mul_assoc] at count
      unfold bits
      have hl := Nat.log2_le_self (img.width * img.height * (img.outChannels alpha).size * (if wide then 2 else 1))
      omega

/-- Both independent output formats on every byte string. Earlier decode errors
propagate with zero additional charge. A reached interleaver returns an exact-size
buffer or its exact typed byte-limit refusal, with a bounded combined observation. -/
theorem interleaved_resources (L : Limits) (data : ByteArray) (opts : DecodeOptions)
    (external : Limits) (alpha wide : Bool) (mode : Scaling) :
    let m := measureInterleaved L data opts external alpha wide mode
    let run := fun (img : Image) =>
      if wide then img.interleaved16 external alpha mode else img.interleaved8 external alpha mode
    m.result = (JPEG2000.decode L data opts).bind run ∧
      m.work ≤ interleavedBudget L external data.size ∧ m.storage ≤ interleavedBudget L external data.size ∧
      (∀ e, JPEG2000.decode L data opts = .error e → m.result = .error e ∧
        m.work = (measure L data opts).work ∧ m.storage = (measure L data opts).storage) ∧
      ∀ img, JPEG2000.decode L data opts = .ok img →
        DisplayWithin external (img.width*img.height*(img.outChannels alpha).size*(if wide then 2 else 1)) m.result := by
  obtain ⟨eqn,suffix⟩ := DisplayPrefix.public_interleaving_work L data opts external alpha wide mode
  obtain ⟨_,w,s,_⟩ := decode_resources L data opts
  have extra := Nat.add_le_add suffix (interleave_record_bound L data opts external alpha wide mode)
  refine ⟨eqn,Nat.add_le_add w extra,Nat.add_le_add s extra,?_,?_⟩
  · intro e h
    simp only [measureInterleaved, interleaveRecord, DisplayPrefix.measuredInterleaving,h]
    exact ⟨rfl,rfl,rfl⟩
  · intro img h
    have cert := (DisplayPrefix.interleaving_work h external alpha wide mode).2.1
    simpa only [measureInterleaved,eqn,h,Except.bind] using cert

end JPEG2000.Spec.Resources.PublicAPI
