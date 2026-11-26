import Spec.Resources.WaveletCost.Wide

/-!
# Inverse-wavelet resource bounds (Plan.md §§3–5, 7, S3; T.800 B.5, F.3)

One packed attempt at area A and remaining depth D reserves at most 8A scratch
cells and charges 4 + 32A + D(5D + 4500A + 5) visits. One wide attempt charges
at most 5 + 2A + D(10 + 100A) visits. Wide headers, line references and integer
cells have independent prices. The integer payload is parameterised by the
dequantised coefficient exponent, before either synthesis or inverse colour.

These are source-level charges for the transform alone. Wide storage sums the logical
slots of every fresh array and therefore bounds concurrently live new slots as well.
The caller's borrowed Mallat input, allocator metadata, machine stack and limb
representation are outside the array counts. Packed writes admit a separate worst-case
copy price. Dispatch charges the packed attempt and any wide retry separately.
-/

namespace JPEG2000.Spec.Resources.WaveletCost

open JPEG2000.Header (Rect)
open JPEG2000.Tier2.Geometry (rectArea TileCompGeom)
open JPEG2000.Tier2.Packet (PrecinctOut)
open WideArithmetic (RasterFits)

/-- Total newly materialised arbitrary integer array slots, including intermediate
passes and the final flat raster. Unit vectors in the meter separate this quantity
from both line references and array headers. -/
def integerCells (A D : Nat) := A+D*(13*A)

/-- One sign bit and enough magnitude bits for every coefficient, lifting operand
and biased pre-division product. The input hypothesis is `|x| ≤ 2^b`. -/
def signedBits (irrev : Bool) (b D : Nat) := b+(if irrev then 540 else 12)*D+2

/-- The four unit-price projections and a payload-bit price. The same meter erases
to the production result at every price, on success and failure. -/
structure WideCounts {α : Type} (x : α) (A D : Nat)
    (m : (p : Prices) → Run x (wideBudget p A D)) : Prop where
  erases : ∀ p, (m p).value = x
  weighted : ∀ p, (m p).visits ≤ wideBudget p A D
  visits : (m ⟨1,0,0,0⟩).visits ≤ 5+2*A+D*(10+100*A)
  headers : (m ⟨0,1,0,0⟩).visits ≤ 1+D*(3+12*A)
  lineRefs : (m ⟨0,0,1,0⟩).visits ≤ D*(2*A)
  cells : (m ⟨0,0,0,1⟩).visits ≤ integerCells A D
  payload : ∀ bits, (m ⟨0,0,0,1⟩).visits * bits ≤ integerCells A D * bits

private theorem projections {α : Type} {x : α} {A D : Nat}
    (m : (p : Prices) → Run x (wideBudget p A D)) : WideCounts x A D m := by
  have hb := fun p => (m p).bounded
  have cells : (m ⟨0,0,0,1⟩).visits ≤ integerCells A D := by
    simpa [wideBudget,levelBudget,integerCells] using hb ⟨0,0,0,1⟩
  refine ⟨fun p => (m p).erase,hb,?_,?_,?_,cells,fun bits => Nat.mul_le_mul_right bits cells⟩
  · have h := hb ⟨1,0,0,0⟩; simp [wideBudget,levelBudget] at h; omega
  · simpa [wideBudget,levelBudget] using hb ⟨0,1,0,0⟩
  · simpa [wideBudget,levelBudget] using hb ⟨0,0,1,0⟩

/-- Resource projections of the wide 5/3 entry, before inverse RCT. The signed
width applies to the output and `operands53` discharges both axes at every
intermediate level with the same input exponent. -/
theorem wide53_work (L : Limits) (r : Rect) (nl : Nat) (xs : Array Int) :
    WideCounts (JPEG2000.WideReversible.idwt53 L r nl xs) (min (rectArea r) L.maxWorkSamples)
      (min nl L.maxDecompLevels) (fun p => wide53Run p L r nl xs) ∧
    ∀ b, RasterFits b xs →
      let D := min nl L.maxDecompLevels
      let A := min (rectArea r) L.maxWorkSamples
      (wide53Run ⟨0,0,0,1⟩ L r nl xs).visits * signedBits false b D ≤
        integerCells A D * signedBits false b D ∧
      (∀ s k, k < D → Level53Fits (b+12*D) xs r.width s k) ∧
      ∀ ys, JPEG2000.WideReversible.idwt53 L r nl xs = .ok ys →
      ∀ z ∈ ys, z.natAbs.log2 + 2 ≤ signedBits false b nl := by
  have counts := projections (fun p => wide53Run p L r nl xs)
  refine ⟨counts,fun b h => ⟨counts.payload _,?_,?_⟩⟩
  · intro s k hk
    exact operands53 h s _ k _ (by omega)
  intro ys ok z hz
  have := WideArithmetic.magnitude_bits (WideArithmetic.idwt53_bounds h ok z hz)
  unfold signedBits; simp; omega

/-- Resource projections of the wide 9/7 entry, before inverse ICT. Each non-singleton
line materialises an input array and five further arrays. The pre-rounded arithmetic
bound for their construction is `operands97`. -/
theorem wide97_work (L : Limits) (q : JPEG2000.WideQuant.Plane) (nl : Nat) :
    WideCounts (JPEG2000.WideDWT97.idwt97 L q nl) (min (rectArea q.rect) L.maxWorkSamples)
      (min nl L.maxDecompLevels) (fun p => wide97Run p L q nl) ∧
    ∀ b, RasterFits b q.samples.toArray →
      let D := min nl L.maxDecompLevels
      let A := min (rectArea q.rect) L.maxWorkSamples
      (wide97Run ⟨0,0,0,1⟩ L q nl).visits * signedBits true b D ≤
        integerCells A D * signedBits true b D ∧
      (∀ s k, k < D → Level97Fits (b+540*D) q.samples.toArray q.rect.width s k) ∧
      ∀ out, JPEG2000.WideDWT97.idwt97 L q nl = .ok out →
      ∀ z ∈ out.samples.toArray, z.natAbs.log2 + 2 ≤ signedBits true b nl := by
  have counts := projections (fun p => wide97Run p L q nl)
  refine ⟨counts,fun b h => ⟨counts.payload _,?_,?_⟩⟩
  · intro s k hk
    exact operands97 h s _ k _ (by omega)
  intro out ok z hz
  have := WideArithmetic.magnitude_bits (WideArithmetic.idwt97_bounds h ok z hz)
  unfold signedBits; simp; omega

/-- Conservative packed allocation in Int32-cell equivalents. Reserve the scratch,
then allow every charged visit to copy an entire plane or scratch buffer, covering
copy-on-write at each individual byte update or zero push. -/
def packedCells (irrev : Bool) (p : Bytes.Plane) (r : Rect) (nl : Nat) :=
  let t := scratchCells p r
  if t = 0 then 0 else t + (compactRun irrev p r nl).visits * max (rectArea r) t

/-- Total logical payload even if every packed byte mutation copies its entire
backing. Multiplication by four prices the resulting Int32 cells in bytes. -/
theorem compact_allocation (irrev : Bool) (p : Bytes.Plane) (r : Rect) (nl A D : Nat)
    (ha : rectArea r ≤ A) (hd : nl ≤ D) :
    packedCells irrev p r nl ≤ 8*A + compactBudget A D * (8*A) := by
  obtain ⟨_,work,scratch⟩ := compact_work irrev p r nl A D ha hd
  unfold packedCells; dsimp only; split
  · exact Nat.zero_le _
  · exact Nat.add_le_add scratch (Nat.mul_le_mul work (by omega))

/-- Which precision attempts the component dispatcher entered. An attempt may
reject coefficient assembly before reaching its inverse wavelet. -/
structure Attempts (α : Type) where
  result : Except Error α
  compact : Bool
  wide : Bool

private def selectAttempt {α : Type} (allow : Bool) (first : Unit → Except Error (Option α))
    (retry : Unit → Except Error α) : Attempts α :=
  if allow then
    match first () with
    | .error e => ⟨.error e,true,false⟩
    | .ok (some v) => ⟨.ok v,true,false⟩
    | .ok none => ⟨retry (),true,true⟩
  else ⟨retry (),false,true⟩

/-- The transform share of a retry pays at most one packed and one wide attempt. -/
def Attempts.charge {α : Type} (a : Attempts α) (packed wide : Nat) :=
  (if a.compact then packed else 0) + (if a.wide then wide else 0)

/-- Reversible dispatch with its two precision attempts exposed. -/
def dispatch53 (L : Limits) (data : ByteArray) (tc : TileCompGeom) (depth F red : Nat)
    (ps : Array (Array PrecinctOut)) : Attempts JPEG2000.NativeOutput.Source :=
  if tc.params.transform != .reversible53 then
    ⟨.error (.malformed Assemble.loc "expected a reversible tile-component"),false,false⟩
  else selectAttempt true
    (fun _ => .ok ((JPEG2000.ReversibleDispatch.compactPlane? L data tc depth F red ps).map
      JPEG2000.NativeOutput.Source.plane))
    (fun _ => do
      let bands ← JPEG2000.WideAssembly.tileComp L data tc depth F red ps
      JPEG2000.ReversibleDispatch.wideSource L bands (tc.params.levels-red))

/-- Irreversible dispatch, including direct-wide selection and validation errors
before either precision attempt. -/
def dispatch97 (L : Limits) (data : ByteArray) (tc : TileCompGeom) (depth F red : Nat)
    (ps : Array (Array PrecinctOut)) (allow : Bool) : Attempts JPEG2000.IrreversibleDispatch.Spatial :=
  if tc.params.transform != .irreversible97 then
    ⟨.error (.unsupported Assemble.loc "irreversible reconstruction requires the 9/7 transform"),false,false⟩
  else if red > tc.params.levels then
    ⟨.error (.unsupported Assemble.loc "resolution reduction exceeds tile-component levels"),false,false⟩
  else match L.check Assemble.loc .decompLevels tc.params.levels with
  | .error e => ⟨.error e,false,false⟩
  | .ok () =>
    let r := JPEG2000.Assemble.reduceRect tc.rect red
    if r.x1 < r.x0 ∨ r.y1 < r.y0 then
      ⟨.error (.malformed Assemble.loc "inverted component rectangle"),false,false⟩
    else selectAttempt allow (fun _ => JPEG2000.IrreversibleDispatch.tryCompact L data tc depth F red ps)
      (fun _ => do
        let bands ← JPEG2000.WideAssembly.tileComp L data tc depth F red ps
        let q ← JPEG2000.WideDWT97.idwt97 L bands (tc.params.levels-red)
        return .wide ⟨q,F⟩)

private theorem charge_le {α : Type} (a : Attempts α) (c w : Nat) : a.charge c w ≤ c+w := by
  unfold Attempts.charge; split <;> split <;> omega

/-- The reversible retry schedule erases on every path. Its charge adds the
two per-attempt allowances only on a fallback. -/
theorem retry53_work (L : Limits) (data : ByteArray) (tc : TileCompGeom) (depth F red : Nat)
    (ps : Array (Array PrecinctOut)) (c w : Nat) :
    let a := dispatch53 L data tc depth F red ps
    a.result = JPEG2000.ReversibleDispatch.tileComp L data tc depth F red ps ∧ a.charge c w ≤ c+w := by
  refine ⟨?_,charge_le ..⟩
  unfold dispatch53 JPEG2000.ReversibleDispatch.tileComp
  split <;> try rfl
  unfold selectAttempt
  cases JPEG2000.ReversibleDispatch.compactPlane? L data tc depth F red ps <;> rfl

/-- Exact-result erasure of the irreversible retry schedule for either setting
of the compact flag. The cost of packet assembly is outside these DWT charges. -/
theorem retry97_work (L : Limits) (data : ByteArray) (tc : TileCompGeom) (depth F red : Nat)
    (ps : Array (Array PrecinctOut)) (allow : Bool) (c w : Nat) :
    let a := dispatch97 L data tc depth F red ps allow
    a.result = JPEG2000.IrreversibleDispatch.component L data tc depth F red ps allow ∧ a.charge c w ≤ c+w := by
  refine ⟨?_,charge_le ..⟩
  unfold dispatch97 JPEG2000.IrreversibleDispatch.component
  dsimp only
  split <;> try rfl
  split <;> try rfl
  cases he : L.check Assemble.loc .decompLevels tc.params.levels with
  | error e => rfl
  | ok u =>
    cases u
    simp only [bind,Except.bind]
    split <;> try rfl
    cases allow
    · rfl
    · unfold selectAttempt
      cases JPEG2000.IrreversibleDispatch.tryCompact L data tc depth F red ps with
      | error e => rfl
      | ok o => cases o <;> rfl

end JPEG2000.Spec.Resources.WaveletCost
