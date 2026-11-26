import Spec.Resources.AssemblyCost
import Spec.Resources.WaveletCost
import Spec.Resources.PublicPacketWork

/-!
# Reconstruction on the admitted tile prefix (Plan.md §§3–5, 7; T.800 B, D–H)

The assembly meter and the transform meter observe the same component dispatch.
Their charges survive a compact miss independently. The component loop stops at
the first error, before the colour and native placement continuations. Prices
count source-level visits, reference slots, array headers and logical payload.
-/

namespace JPEG2000.Spec.Resources.ReconstructionCost

open JPEG2000.Header JPEG2000.Bytes
open JPEG2000.Tier2.Geometry (TileCompGeom rectArea)
open JPEG2000.Tier2.Packet (TileCodeBlocks)
open WaveletCost

/-- The reversible packed walk before the saturation test and checked transform. -/
private def revBands (L : Limits) (data : ByteArray) (tc : TileCompGeom) (d F red : Nat)
    (ps : AssemblyCost.Store) : Except Error (Plane × Nat) := do
  let p := tc.params
  if red > p.levels then
    throw (.unsupported Assemble.loc
      s!"resolution reduction {red} exceeds the {p.levels} decomposition levels of a tile-component")
  let nl := p.levels-red
  let r := Assemble.reduceRect tc.rect red
  let plane ← Plane.zeroChecked L Assemble.loc r.width r.height
  JPEG2000.WideAssembly.visitBlocks nl ps (plane,0) fun (dst,sat) res b cb => do
    let o ← JPEG2000.ReversibleDispatch.checkedBlock data p res b cb
    let (pl,ok) ← JPEG2000.Quant.dequantBlock dst r nl res b cb.geom.rect
      (Spec.Quant.bandQuant p d res b) F o
    return (pl, if ok then sat else sat+1)

private theorem narrow_eq (L : Limits) (data : ByteArray) (tc : TileCompGeom) (d F red : Nat)
    (ps : AssemblyCost.Store) :
    JPEG2000.ReversibleDispatch.narrow L data tc d F red ps =
      (revBands L data tc d F red ps >>= fun (p,sat) => pure
        (if sat = 0 then JPEG2000.DWT53.idwt53Fast p (Assemble.reduceRect tc.rect red)
          (tc.params.levels-red) else none,sat)) := by
  unfold JPEG2000.ReversibleDispatch.narrow revBands
  dsimp only
  split <;> simp only [bind_assoc] <;> rfl

/-- The actual reversible Mallat plane when the packed DWT is reached. -/
def input53 (L : Limits) (data : ByteArray) (tc : TileCompGeom) (d F red : Nat)
    (ps : AssemblyCost.Store) : Option Plane := do
  guard (red ≤ tc.params.levels && tc.params.levels ≤ L.maxDecompLevels)
  let r := Assemble.reduceRect tc.rect red
  guard (r.x0 ≤ r.x1 && r.y0 ≤ r.y1)
  let (p,sat) ← (revBands L data tc d F red ps).toOption
  if sat = 0 then some p else none

private theorem input53_eq (L : Limits) (data : ByteArray) (tc : TileCompGeom) (d F red : Nat)
    (ps : AssemblyCost.Store) :
    (input53 L data tc d F red ps).bind (fun p => JPEG2000.DWT53.idwt53Fast p
      (Assemble.reduceRect tc.rect red) (tc.params.levels-red)) =
      JPEG2000.ReversibleDispatch.compactPlane? L data tc d F red ps := by
  unfold input53 JPEG2000.ReversibleDispatch.compactPlane?
  rw [narrow_eq]
  dsimp only
  cases h₁ : (decide (red ≤ tc.params.levels) && decide (tc.params.levels ≤ L.maxDecompLevels)) <;>
    cases h₂ : (decide ((Assemble.reduceRect tc.rect red).x0 ≤ (Assemble.reduceRect tc.rect red).x1)
      && decide ((Assemble.reduceRect tc.rect red).y0 ≤ (Assemble.reduceRect tc.rect red).y1)) <;>
    cases h₃ : revBands L data tc d F red ps with
    | error e => rfl
    | ok pair => obtain ⟨p,sat⟩ := pair; cases sat <;> rfl

/-- Prices of visits, array headers, line references and bytes of logical payload.
Unit prices select work, storage or operand-byte charges. The component loop
also records a unit for each entered callback. -/
structure Prices where
  /-- Source-level structural and cell visits. -/
  visits : Nat
  /-- Wavelet array objects and an allowance for assembly records. -/
  headers : Nat
  /-- Line references and component or assembly descriptors. -/
  refs : Nat
  /-- Logical bytes materialised in raster and gather operations. -/
  bytes : Nat
  /-- Visits weighted by the byte width of sample arithmetic. -/
  operandBytes : Nat

/-- Wavelet input and intermediate signed width at the parsed depth limit. -/
def waveBits (L : Limits) (irrev : Bool) := signedBits irrev 372 L.maxDecompLevels

/-- Apply the signed width of this filter to every freshly materialised wide slot. -/
def widePrices (p : Prices) (L : Limits) (irrev : Bool) : WaveletCost.Prices :=
  ⟨p.visits+((waveBits L irrev + 7)/8)*p.operandBytes,p.headers,p.refs,((waveBits L irrev + 7)/8)*p.bytes⟩

/-- Per-slot byte price for colour, including the G.3 products and biased sums. -/
def colourBytes (L : Limits) := (395+540*L.maxDecompLevels+7)/8

private def packedCharge (p : Prices) (irrev : Bool) (z : Plane) (r : Rect) (nl : Nat) :=
  (compactRun irrev z r nl).visits * (p.visits+8*p.operandBytes) + packedCells irrev z r nl * (4*p.bytes)

private def packedDue (p : Prices) (irrev : Bool) (z : Option Plane) (r : Rect) (nl : Nat) :=
  match z with
  | none => 0
  | some plane => packedCharge p irrev plane r nl

private def wideDue (p : Prices) (L : Limits) (irrev : Bool) (nl : Nat)
    (z : Except Error JPEG2000.WideQuant.Plane) :=
  match z with
  | .error _ => 0
  | .ok q =>
    let rates := widePrices p L irrev
    if irrev then (wide97Run rates L q nl).visits
    else (wide53Run rates L q.rect nl q.samples.toArray).visits

/-- The exact wavelet charge for both attempts. In particular a false packed flag
still pays for the checked transform. An assembly error skips only that transform.
The wide attempt reads the same packet store from the beginning. -/
def transforms (p : Prices) (L : Limits) (data : ByteArray) (tc : TileCompGeom)
    (d F red : Nat) (ps : AssemblyCost.Store) :=
  let nl := tc.params.levels-red
  let r := Assemble.reduceRect tc.rect red
  let wide := fun irrev => wideDue p L irrev nl (JPEG2000.WideAssembly.tileComp L data tc d F red ps)
  match tc.params.transform with
  | .reversible53 =>
    let a := dispatch53 L data tc d F red ps
    a.charge (packedDue p false (input53 L data tc d F red ps) r nl) (wide false)
  | .irreversible97 =>
    let a := dispatch97 L data tc d F red ps true
    let compact := JPEG2000.IrreversibleDispatch.compactBands L data tc d F red ps
    a.charge (packedDue p true compact.toOption r nl) (wide true)

/-- Maximum possible visits and cumulative packed byte-copy payload of one
checked transform, plus one wide transform at the larger of the two widths. -/
def transformBudget (p : Prices) (L : Limits) :=
  let A := L.maxWorkSamples
  let D := L.maxDecompLevels
  let c := compactBudget A D
  c*(p.visits+8*p.operandBytes) + (8*A+c*(8*A))*(4*p.bytes) + wideBudget (widePrices p L true) A D

private theorem wide_mono (p : WaveletCost.Prices) {a A d D : Nat} (ha : a ≤ A) (hd : d ≤ D) :
    wideBudget p a d ≤ wideBudget p A D := by
  unfold wideBudget levelBudget
  repeat' first | apply Nat.add_le_add | apply Nat.mul_le_mul
  all_goals omega

private theorem wideDue_bound (p : Prices) (L : Limits) (irrev : Bool) (nl : Nat)
    (z : Except Error JPEG2000.WideQuant.Plane) :
    wideDue p L irrev nl z ≤ wideBudget (widePrices p L true) L.maxWorkSamples L.maxDecompLevels := by
  cases z with
  | error => exact Nat.zero_le _
  | ok q =>
    cases irrev
    · have h := (wide53_work L q.rect nl q.samples.toArray).1.weighted (widePrices p L false)
      apply Nat.le_trans h
      apply Nat.le_trans (wide_mono _ (Nat.min_le_right ..) (Nat.min_le_right ..))
      unfold wideBudget levelBudget widePrices waveBits signedBits
      simp only [Bool.false_eq_true,↓reduceIte]
      repeat' first | apply Nat.add_le_add | apply Nat.mul_le_mul
      all_goals omega
    · exact Nat.le_trans ((wide97_work L q nl).1.weighted _)
        (wide_mono _ (Nat.min_le_right ..) (Nat.min_le_right ..))

private theorem packedDue_bound (p : Prices) (L : Limits) (irrev : Bool) (z : Option Plane)
    (r : Rect) (nl : Nat) (ha : rectArea r ≤ L.maxWorkSamples) (hd : nl ≤ L.maxDecompLevels) :
    packedDue p irrev z r nl ≤ compactBudget L.maxWorkSamples L.maxDecompLevels*(p.visits+8*p.operandBytes) +
      (8*L.maxWorkSamples+compactBudget L.maxWorkSamples L.maxDecompLevels*(8*L.maxWorkSamples))*(4*p.bytes) := by
  cases z with
  | none => exact Nat.zero_le _
  | some z =>
    exact Nat.add_le_add (Nat.mul_le_mul_right _ (compact_work irrev z r nl _ _ ha hd).2.1)
      (Nat.mul_le_mul_right _ (compact_allocation irrev z r nl _ _ ha hd))

private theorem transforms_bound (p : Prices) (L : Limits) (data : ByteArray) (tc : TileCompGeom)
    (d F red : Nat) (ps : AssemblyCost.Store) (ha : AssemblyCost.planeArea tc red ≤ L.maxWorkSamples)
    (hd : tc.params.levels-red ≤ L.maxDecompLevels) :
    transforms p L data tc d F red ps ≤ transformBudget p L := by
  unfold transforms transformBudget
  dsimp only
  split
  · apply Nat.le_trans (retry53_work ..).2
    exact Nat.add_le_add (packedDue_bound _ _ _ _ _ _ ha hd) (wideDue_bound ..)
  · apply Nat.le_trans (retry97_work ..).2
    exact Nat.add_le_add (packedDue_bound _ _ _ _ _ _ ha hd) (wideDue_bound ..)

/-- Numeric interface to the translated packet store. The segment and range caps
count materialised descriptors after splitting at tile-part boundaries. -/
structure StoreCaps where
  precincts : Nat
  bands : Nat
  blocks : Nat
  segments : Nat
  ranges : Nat

/-- The five independent shape obligations for each component actually selected. -/
def StoreCaps.Holds (caps : StoreCaps) (g : Progression.Layout) (a : Option TileCodeBlocks) :=
  ∀ i : Fin g.numComps, AssemblyCost.StoreBounds (AssemblyCost.selected a i)
    caps.precincts caps.bands caps.blocks caps.segments caps.ranges

/-- Cost of both traversals including Tier-1, the rejected prefix and its gather. -/
def assemblyBudget (L : Limits) (n : Nat) (caps : StoreCaps) :=
  let D := L.maxDecompLevels
  5*L.maxWorkSamples + 2*((D+1)*(1+caps.precincts*(1+caps.bands*(1+caps.blocks*
    (1+AssemblyCost.blockBudget n D caps.segments caps.ranges)))))

private theorem assembly_le (n d D : Nat) (caps : StoreCaps) (hd : d ≤ D) :
    (d+1)*(1+caps.precincts*(1+caps.bands*(1+caps.blocks*(1+AssemblyCost.blockBudget n d
      caps.segments caps.ranges)))) ≤
    (D+1)*(1+caps.precincts*(1+caps.bands*(1+caps.blocks*(1+AssemblyCost.blockBudget n D
      caps.segments caps.ranges)))) := by
  unfold AssemblyCost.blockBudget
  repeat' first | apply Nat.mul_le_mul | apply Nat.add_le_add
  all_goals omega

/-- Assembly charges both attempts before discarding a failed compact result.
A visit can touch a descriptor, copy a byte, or process a coefficient. At the
byte projection allow a full 47-byte coefficient payload for each charged unit. -/
def assemblyRate (p : Prices) := p.visits+p.headers+p.refs+47*(p.bytes+p.operandBytes)

private def component (p : Prices) (L : Limits) (h : Header) (data : ByteArray)
    (g : Progression.Layout) (c : Coding) (a : Option TileCodeBlocks) (red : Nat) (i : Fin g.numComps) :=
  let tc := g.comp i
  let m := AssemblyCost.component L h data g c a i red
  let w := transforms p L data tc (h.siz.components.getD i default).depth.toNat
    (Assemble.fracBitsOf h.siz (c.mctApplies h.siz) i) red (AssemblyCost.selected a i)
  -- Reserve both Mallat inputs, even if only one attempt gets past allocation.
  (m.1, m.2*(assemblyRate p) + w + (4+47)*p.bytes*AssemblyCost.planeArea tc red)

private def perComponent (p : Prices) (L : Limits) (n : Nat) (caps : StoreCaps) :=
  assemblyBudget L n caps*(assemblyRate p) + transformBudget p L + 1

private theorem component_le {L : Limits} {h : Header} {data : ByteArray} {t : Nat}
    {g : Progression.Layout} {c : Coding} (parsed : Header.parse L data = .ok h)
    (layout : Progression.Layout.ofHeader h t = .ok (g,c)) (a : Option TileCodeBlocks)
    (red : Nat) (p : Prices) (caps : StoreCaps) (stores : caps.Holds g a)
    (admitted : Resources.tileCells g red ≤ L.maxWorkSamples) (i : Fin g.numComps) :
    let m := component p L h data g c a red i
    m.1 = JPEG2000.TileDispatch.component L h data g c a i red ∧
    m.2+1 ≤ perComponent p L data.size caps + (4+47)*p.bytes*AssemblyCost.planeArea (g.comp i) red := by
  obtain ⟨erase,cost⟩ := AssemblyCost.component_budget parsed layout a i red _ _ _ _ _ (stores i) admitted
  have within := AssemblyCost.native_budget parsed layout a i red
  simp only [admitted,↓reduceIte] at within
  have hd := Nat.le_trans (Nat.sub_le (g.comp i).params.levels red)
    (WideHeaderBounds.parsed_component_bounds parsed layout i red).1.levels
  have top := assembly_le data.size _ _ caps hd
  have bound : (AssemblyCost.component L h data g c a i red).2 ≤ assemblyBudget L data.size caps := by
    exact Nat.le_trans cost (Nat.add_le_add_left (Nat.mul_le_mul_left 2 top) _)
  have weighted := Nat.mul_le_mul_right (assemblyRate p) bound
  have wave := transforms_bound p L data (g.comp i) (h.siz.components.getD i default).depth.toNat
    (Assemble.fracBitsOf h.siz (c.mctApplies h.siz) i) red (AssemblyCost.selected a i) within.1 hd
  exact ⟨erase, by dsimp only [component,perComponent]; omega⟩

private def gridArea (g : Progression.Layout) (red j : Nat) := AssemblyCost.planeArea (g.comp j) red

private theorem gridTotal (g : Progression.Layout) (red u v : Nat) :
    ((List.range' 0 g.numComps).map (fun i => u+v*gridArea g red i)).sum =
      u*g.numComps+v*Resources.tileCells g red := by
  have same : (List.range' 0 g.numComps).map (fun i => u+v*gridArea g red i) =
      g.comps.toList.map (fun tc => u+v*AssemblyCost.planeArea tc red) := by
    apply List.ext_getElem <;> simp [Progression.Layout.numComps,gridArea,Progression.Layout.comp,
      Array.getD_eq_getD_getElem?]
    intro i hi _
    rw [Array.getElem?_eq_getElem hi]; rfl
  have linear (xs : List TileCompGeom) :
      (xs.map fun tc => u+v*AssemblyCost.planeArea tc red).sum =
        u*xs.length+v*(xs.map (fun tc => AssemblyCost.planeArea tc red)).sum := by
    induction xs with
    | nil => simp
    | cons tc xs ih => simp only [List.map_cons,List.sum_cons,List.length_cons,ih,Nat.mul_add,Nat.mul_succ]; omega
  rw [same,linear]
  rfl

private theorem loop_spec {α β : Type} {xs : Array α}
    (f : (i : Nat) → α → i < xs.size → Except Error β × Nat)
    (step : (i : Nat) → α → i < xs.size → Except Error β) (cap : Nat → Nat)
    (each : ∀ i (hi : i < xs.size), (f i xs[i] hi).1 = step i xs[i] hi ∧
      (f i xs[i] hi).2+1 ≤ cap i) (k j : Nat) (len : k+j = xs.size) (acc : Array β) :
    let m := TileColorPlacement.componentLoop xs f k j len acc
    m.1 = Array.mapFinIdxM.map xs step k j len acc ∧ m.2 ≤ ((List.range' j k).map cap).sum := by
  induction k generalizing j acc with
  | zero => exact ⟨rfl,Nat.le_refl _⟩
  | succ k ih =>
    have cur := each j (by omega)
    simp only [TileColorPlacement.componentLoop,Array.mapFinIdxM.map,← cur.1,List.range'_succ,
      List.map_cons,List.sum_cons]
    cases res : (f j xs[j] (by omega)).1 with
    | error e => exact ⟨rfl,by dsimp only; omega⟩
    | ok z => exact ⟨(ih (j+1) (by omega) (acc.push z)).1,
        Nat.add_le_add cur.2 (ih (j+1) (by omega) (acc.push z)).2⟩

/-- Production callback traversal, through and including the first failing
component. The original aggregate guard precedes both assembly and lifting. -/
def componentPrefix (p : Prices) (L : Limits) (h : Header) (data : ByteArray)
    (g : Progression.Layout) (c : Coding) (a : Option TileCodeBlocks) (red : Nat) :
    Except Error (Array JPEG2000.TileDispatch.Spatial) × Nat :=
  match L.check Assemble.loc .workSamples (Resources.tileCells g red) with
  | .error e => (.error e,0)
  | .ok _ => TileColorPlacement.componentLoop g.comps (fun j _ hj =>
      component p L h data g c a red ⟨j,hj⟩) g.numComps 0 rfl #[]

/-- A full component callback allowance per entered index and just one
aggregate tile-area allowance for both packed and wide Mallat inputs. -/
def prefixBudget (p : Prices) (L : Limits) (n : Nat) (caps : StoreCaps) :=
  perComponent p L n caps*L.maxComponents + (4+47)*p.bytes*L.maxWorkSamples

/-- Erasure and bound of the admitted prefix. Earlier entries and the first
rejection are charged even when no centred tile can be returned. -/
theorem prefix_work {L : Limits} {h : Header} {data : ByteArray} {t red : Nat}
    {g : Progression.Layout} {c : Coding} (parsed : Header.parse L data = .ok h)
    (layout : Progression.Layout.ofHeader h t = .ok (g,c)) (a : Option TileCodeBlocks)
    (p : Prices) (caps : StoreCaps) (stores : caps.Holds g a) :
    let m := componentPrefix p L h data g c a red
    m.1 = (do
      L.check Assemble.loc .workSamples (Resources.tileCells g red)
      g.comps.mapFinIdxM fun j _ hj => JPEG2000.TileDispatch.component L h data g c a ⟨j,hj⟩ red) ∧
    m.2 ≤ prefixBudget p L data.size caps := by
  unfold componentPrefix
  cases guard : L.check Assemble.loc .workSamples (Resources.tileCells g red) with
  | error e => exact ⟨rfl,Nat.zero_le _⟩
  | ok u =>
    cases u
    have admission := (Limits.check_eq_ok_iff ..).1 guard
    have count := (HeaderWork.layout_budget parsed layout).1
    obtain ⟨eq,bound⟩ := loop_spec (xs := g.comps) (fun j _ hj => component p L h data g c a red ⟨j,hj⟩)
      (fun j _ hj => JPEG2000.TileDispatch.component L h data g c a ⟨j,hj⟩ red)
      (fun j => perComponent p L data.size caps + (4+47)*p.bytes*gridArea g red j)
      (fun j hj => component_le parsed layout a red p caps stores admission ⟨j,hj⟩) g.numComps 0 rfl #[]
    rw [gridTotal] at bound
    exact ⟨eq,Nat.le_trans bound (Nat.add_le_add (Nat.mul_le_mul_left _ count) (Nat.mul_le_mul_left _ admission))⟩

/-- The charge of an actual packed call is attached to its input. This equality
also holds when the flag goes false after all lifting iterations have run. -/
theorem packed_entry (L : Limits) (data : ByteArray) (tc : TileCompGeom) (d F red : Nat)
    (ps : AssemblyCost.Store) :
    (input53 L data tc d F red ps).bind (fun p => (compactRun false p (Assemble.reduceRect tc.rect red)
      (tc.params.levels-red)).value) = JPEG2000.ReversibleDispatch.compactPlane? L data tc d F red ps ∧
    JPEG2000.IrreversibleDispatch.tryCompact L data tc d F red ps = .ok
      ((JPEG2000.IrreversibleDispatch.compactBands L data tc d F red ps).toOption.bind fun p => do
        let r := Assemble.reduceRect tc.rect red
        let q ← (compactRun true p r (tc.params.levels-red)).value
        if h : q.width = r.width ∧ q.height = r.height then
          some (.compact r F q h.1 h.2) else none) := by
  simp only [(compactRun ..).erase]
  refine ⟨input53_eq ..,?_⟩
  unfold JPEG2000.IrreversibleDispatch.tryCompact
  cases JPEG2000.IrreversibleDispatch.compactBands L data tc d F red ps <;> rfl

/-- All coefficients handed to the wide placement loop, including the H.2
shifts, E.1 scale product and biased numerator, fit the Mallat price of 47 bytes. -/
theorem block_operands {L : Limits} {h : Header} {data : ByteArray} {t : Nat}
    {g : Progression.Layout} {c : Coding} (parsed : Header.parse L data = .ok h)
    (layout : Progression.Layout.ofHeader h t = .ok (g,c)) (i : Fin g.numComps)
    (r : Nat) (b : JPEG2000.Tier2.Geometry.Band) (cb : JPEG2000.Tier2.Packet.CodeBlock)
    {cs : Array JPEG2000.Tier1.WidePlain.Cell}
    (ok : JPEG2000.WideAssembly.decodeBlock data (g.comp i).params r b cb = .ok cs) :
    ∀ z ∈ cs, WideArithmetic.QuantOperands
      (Spec.Quant.bandQuant (g.comp i).params (h.siz.components.getD i default).depth.toNat r b)
      (Assemble.fracBitsOf h.siz (c.mctApplies h.siz) i) z WideArithmetic.part1QuantLimit ∧
      WideArithmetic.part1QuantLimit ≤ 2^372 := by
  intro z hz
  obtain ⟨mag,lsb,_⟩ := (Tier1Work.parsed_cells (WideHeaderBounds.parsed_component_bounds
    parsed layout i 0).1 data r b cb cs ok).2 z hz
  exact (WideArithmetic.parsed_quant parsed layout i r b z mag lsb).2.2

/-- The wide meter's integer prices cover the actual two-axis operands at
every recursive level, including every 9/7 product before rounding. This
requires only entry into the DWT, even if a later stage rejects. -/
theorem wave_operands {L : Limits} {h : Header} {data : ByteArray} {t red : Nat}
    {g : Progression.Layout} {c : Coding} (parsed : Header.parse L data = .ok h)
    (layout : Progression.Layout.ofHeader h t = .ok (g,c)) (i : Fin g.numComps)
    (ps : AssemblyCost.Store) {q : JPEG2000.WideQuant.Plane}
    (ok : JPEG2000.WideAssembly.tileComp L data (g.comp i) (h.siz.components.getD i default).depth.toNat
      (Assemble.fracBitsOf h.siz (c.mctApplies h.siz) i) red ps = .ok q) :
    WideArithmetic.RasterFits 372 q.samples.toArray ∧
    ∀ s k, k < (g.comp i).params.levels-red →
      Level53Fits (372+12*L.maxDecompLevels) q.samples.toArray q.rect.width s k ∧
      Level97Fits (372+540*L.maxDecompLevels) q.samples.toArray q.rect.width s k := by
  have hq := AssemblyCost.mallat_width parsed layout i red ps ok
  have hd := (WideHeaderBounds.parsed_component_bounds parsed layout i red).1.levels
  exact ⟨hq,fun s k hk => ⟨operands53 hq s _ k _ (by omega),operands97 hq s _ k _ (by omega)⟩⟩

private theorem parsedBlocks {L : Limits} {h : Header} {data : ByteArray} {t : Nat}
    {g : Progression.Layout} {c : Coding} (parsed : Header.parse L data = .ok h)
    (layout : Progression.Layout.ofHeader h t = .ok (g,c)) (i : Fin g.numComps) :
    WideArithmetic.BlockBounds data (g.comp i).params (2^292-1) 291 := by
  intro r b cb cs dec z hz
  obtain ⟨hm,hl,_⟩ := (Tier1Work.parsed_cells (WideHeaderBounds.parsed_component_bounds
    parsed layout i 0).1 data r b cb cs dec).2 z hz
  exact ⟨by omega,hl⟩

private theorem source_bound {L : Limits} {h : Header} {data : ByteArray} {t red : Nat}
    {g : Progression.Layout} {c : Coding} (parsed : Header.parse L data = .ok h)
    (layout : Progression.Layout.ofHeader h t = .ok (g,c)) (a : Option TileCodeBlocks) (i : Fin g.numComps)
    {v : JPEG2000.TileDispatch.Spatial} (ok : JPEG2000.TileDispatch.component L h data g c a i red = .ok v) :
    WideArithmetic.SourceFits (372+540*L.maxDecompLevels) v.source := by
  obtain ⟨hd,base⟩ := WideArithmetic.parsed_spatial parsed layout i a red (parsedBlocks parsed layout i) ok
  intro j
  apply Nat.le_trans (base j)
  apply Nat.pow_le_pow_right (by decide)
  split <;> omega

/-- The zero-default read used by both checked G.3 packing and G.2 views. -/
def sourceAt (s : JPEG2000.NativeOutput.Source) (j : Nat) := (s.get? j).getD 0

private theorem atFits {b : Nat} {s : JPEG2000.NativeOutput.Source}
    (bound : WideArithmetic.SourceFits b s) (j : Nat) : WideArithmetic.Fits b (sourceAt s j) := by
  unfold sourceAt JPEG2000.NativeOutput.Source.get?
  split
  · exact bound _
  · exact Nat.zero_le _

/-- G.2 neighbour sum, quotient and all G.3 matrix operands on the returned
component rasters. The colour meter uses 21 more exponent bits than the DWT.
The same bounds apply to a rejected compact ICT pack and a lazy RCT read. -/
theorem colour_operands {L : Limits} {h : Header} {data : ByteArray} {t red : Nat}
    {g : Progression.Layout} {c : Coding} (parsed : Header.parse L data = .ok h)
    (layout : Progression.Layout.ofHeader h t = .ok (g,c)) (a : Option TileCodeBlocks)
    (iy ic ir : Fin g.numComps) {y cb cr : JPEG2000.TileDispatch.Spatial}
    (hy : JPEG2000.TileDispatch.component L h data g c a iy red = .ok y)
    (hc : JPEG2000.TileDispatch.component L h data g c a ic red = .ok cb)
    (hr : JPEG2000.TileDispatch.component L h data g c a ir red = .ok cr) (j : Nat) :
    let Y := sourceAt y.source j
    let C := sourceAt cb.source j
    let R := sourceAt cr.source j
    let b := 372+540*L.maxDecompLevels
    WideArithmetic.ICTOperands (b+21) Y C R ∧ WideArithmetic.Fits (b+1) (R+C) ∧
      WideArithmetic.Fits (b+1) ((R+C)/4) ∧ WideArithmetic.Fits (b+2) (Y-(R+C)/4) ∧
      WideArithmetic.Fits (b+3) (R+(Y-(R+C)/4)) ∧ WideArithmetic.Fits (b+3) (C+(Y-(R+C)/4)) := by
  have yBound := atFits (source_bound parsed layout a iy hy) j
  have cbBound := atFits (source_bound parsed layout a ic hc) j
  have crBound := atFits (source_bound parsed layout a ir hr) j
  exact ⟨by simpa only [Nat.max_self] using WideArithmetic.ict_operands yBound cbBound crBound,
    WideArithmetic.rct_operands yBound cbBound crBound⟩

private theorem componentArea {L : Limits} {h : Header} {data : ByteArray} {t red : Nat}
    {g : Progression.Layout} {c : Coding} {a : Option TileCodeBlocks} {b : Option Spec.Tier2.TileOut}
    (parsed : Header.parse L data = .ok h) (layout : Progression.Layout.ofHeader h t = .ok (g,c))
    (origin : TileDispatch.Packets L h data t a b) (i : Fin g.numComps)
    {v : JPEG2000.TileDispatch.Spatial} (ok : JPEG2000.TileDispatch.component L h data g c a i red = .ok v) :
    TileColorPlacement.area v.source = gridArea g red i := by
  have rel := TileDispatch.parsed_component parsed layout origin i red
  dsimp only at rel
  rw [ok] at rel
  generalize hz : Spec.Decode.tileComp .. = result at rel
  cases result with
  | error => contradiction
  | ok pair =>
    rw [WideAssembly.tileComp_eq_finish] at hz
    obtain ⟨q,_,last⟩ := Tier2Equiv.bind_ok hz
    cases last
    have shape := rel.centered
    unfold TileColorPlacement.area
    rw [shape.1,shape.2.1]
    unfold Spec.Decode.idwt
    split <;> rfl

private theorem sumSub {xs ys : List Nat} (h : xs.Sublist ys) : xs.sum ≤ ys.sum := by
  induction h with
  | slnil => exact Nat.le_refl _
  | cons _ _ ih => exact Nat.le_add_left_of_le ih
  | cons_cons _ _ ih => exact Nat.add_le_add_left ih _

/-- Actual predecessor backings at any point in the component loop. The domain
can be the successful prefix of a subsequently rejected tile. Packed bytes and
rounded signed-magnitude payloads are summed over the original physical rasters. -/
theorem prefix_backing {L : Limits} {h : Header} {data : ByteArray} {t red : Nat}
    {g : Progression.Layout} {c : Coding} {a : Option TileCodeBlocks} {b : Option Spec.Tier2.TileOut}
    (parsed : Header.parse L data = .ok h) (layout : Progression.Layout.ofHeader h t = .ok (g,c))
    (origin : TileDispatch.Packets L h data t a b) (admitted : Resources.tileCells g red ≤ L.maxWorkSamples)
    (done : List (Fin g.numComps × JPEG2000.TileDispatch.Spatial))
    (order : (done.map fun e => e.1.val).Sublist (List.range' 0 g.numComps))
    (calls : ∀ e ∈ done, JPEG2000.TileDispatch.component L h data g c a e.1 red = .ok e.2) :
    ∃ bs : List TileColorPlacement.Backing,
      bs.map (·.source) = done.map (fun e => e.2.source) ∧
      (bs.map (·.logicalBytes)).sum ≤ (4+TileColorPlacement.componentBytes L)*L.maxWorkSamples := by
  let B := 4+TileColorPlacement.componentBytes L
  let weight := fun j => 0+B*gridArea g red j
  have back (es : List (Fin g.numComps × JPEG2000.TileDispatch.Spatial))
      (hs : ∀ e ∈ es, JPEG2000.TileDispatch.component L h data g c a e.1 red = .ok e.2) :
      ∃ bs : List TileColorPlacement.Backing, bs.map (·.source) = es.map (fun e => e.2.source) ∧
        (bs.map (·.logicalBytes)).sum ≤ ((es.map (fun e => e.1.val)).map weight).sum := by
    induction es with
    | nil => exact ⟨[],rfl,Nat.le_refl _⟩
    | cons e es ih =>
      have ok := hs e (by simp)
      obtain ⟨bk,eq,bound⟩ := TileColorPlacement.component_backing_bytes parsed layout e.1 ok
      rw [componentArea parsed layout origin e.1 ok] at bound
      obtain ⟨bs,src,tail⟩ := ih (fun e he => hs e (by simp [he]))
      refine ⟨bk::bs,by simp [eq,src],?_⟩
      simpa only [List.map_cons,List.sum_cons,weight,Nat.zero_add] using Nat.add_le_add bound tail
  obtain ⟨bs,src,cap⟩ := back done calls
  have limit := sumSub (order.map weight)
  change _ ≤ ((List.range' 0 g.numComps).map (fun j => 0+B*gridArea g red j)).sum at limit
  rw [gridTotal,Nat.zero_mul,Nat.zero_add] at limit
  exact ⟨bs,src,Nat.le_trans cap (Nat.le_trans limit (Nat.mul_le_mul_left B admitted))⟩

/-- Both precision paths use the actual gathered buffer and segment array. A
rejection following preflight can already own both bordered packed arrays or the
wide block raster. These are peak per-block domains, independent of tile area. -/
theorem block_workspace {L : Limits} {h : Header} {data : ByteArray} {t : Nat}
    {g : Progression.Layout} {c : Coding} (parsed : Header.parse L data = .ok h)
    (layout : Progression.Layout.ofHeader h t = .ok (g,c)) (i : Fin g.numComps)
    (a : Option TileCodeBlocks) (caps : StoreCaps) (stores : caps.Holds g a)
    (r : Nat) (pr : JPEG2000.Tier2.Packet.PrecinctOut) (hp : pr ∈ (AssemblyCost.selected a i).getD r #[])
    (bo : JPEG2000.Tier2.Packet.BandOut) (hb : bo ∈ pr.bands)
    (cb : JPEG2000.Tier2.Packet.CodeBlock) (hc : cb ∈ bo.blocks) :
    let inp := Assemble.tier1Input data cb
    let p := (g.comp i).params
    inp.1.size ≤ max 1 caps.ranges*data.size ∧ inp.2.size ≤ caps.segments ∧
    ∀ wide kept, (Tier1Work.preflight wide inp.1 inp.2 cb.geom.rect.width cb.geom.rect.height
      (JPEG2000.Tier1.Style.ofByte p.cbStyle) ((JPEG2000.Tier2.Packet.bandMb p r bo.band+p.roiShift)-
      (if cb.included then cb.zeroBitPlanes else 0))).1 = .ok kept →
      kept.size ≤ caps.segments ∧ rectArea cb.geom.rect ≤ 4096 ∧
      2*((cb.geom.rect.width+2)*(cb.geom.rect.height+2)) ≤ 16392 := by
  obtain ⟨hs,hk⟩ := (((stores i r).2 pr hp).2 bo hb).2 cb hc
  obtain ⟨sz,bytes,_⟩ := AssemblyCost.block_storage (WideHeaderBounds.parsed_component_bounds
    parsed layout i 0).1 data r bo.band cb
  refine ⟨Nat.le_trans bytes (Nat.mul_le_mul_right _ (by omega)),sz ▸ hs,?_⟩
  intro wide kept ok
  obtain ⟨len,_,area,border⟩ := AssemblyCost.block_workspace wide data (g.comp i).params r bo.band cb kept ok
  exact ⟨Nat.le_trans len hs,area,border⟩

/-- Rounded operand width for G.1. Rounding adds half a unit and the final
unsigned level shift adds an offset after division. -/
def placementBytes (L : Limits) := (397+540*L.maxDecompLevels+7)/8

private def nativeRate (p : Prices) (L : Limits) :=
  p.visits+p.refs+placementBytes L*p.operandBytes

/-- Per-tile bound for the colour and placement projections at their parsed widths. -/
def nativeBudget (p : Prices) (L : Limits) :=
  PacketTraversal.placementBudget 0 L*nativeRate p L +
    PacketTraversal.placementBudget (colourBytes L) L*p.bytes

/-- Reconstruction and native placement for one layout. The two colour meter
projections separate structural work from the per-slot logical byte price. -/
def tile (p : Prices) (L : Limits) (h : Header) (data : ByteArray) (red : Nat)
    (g : Progression.Layout) (c : Coding) (a : Option TileCodeBlocks)
    (dst : Array JPEG2000.NativeOutput.OutputComponent) :=
  let components := componentPrefix p L h data g c a red
  let work := TileColorPlacement.nativeTileMeter 0 L h data red g c a dst
  let storage := TileColorPlacement.nativeTileMeter (colourBytes L) L h data red g c a dst
  let result := do
    let ps ← components.1
    let sources ← (TileColorPlacement.sourcesMeter (colourBytes L) L (c.mctApplies h.siz) ps).1
    (TileColorPlacement.writeTileMeter L h.siz red g c dst sources).1
  (result,components.2 + (work.2*nativeRate p L + storage.2*p.bytes))

/-- Both precision attempts, retained spatial components, G.2/G.3 and the
G.1 writer. The destination may reject after earlier writes. On successful
centring the actual predecessor rasters of each lazy reader are identified. -/
theorem tile_work {L : Limits} {h : Header} {data : ByteArray} {t red : Nat}
    {g : Progression.Layout} {c : Coding} {a : Option TileCodeBlocks} {b : Option Spec.Tier2.TileOut}
    (parsed : Header.parse L data = .ok h) (layout : Progression.Layout.ofHeader h t = .ok (g,c))
    (origin : TileDispatch.Packets L h data t a b) (p : Prices) (caps : StoreCaps) (stores : caps.Holds g a)
    (dst : Array JPEG2000.NativeOutput.OutputComponent) :
    let m := tile p L h data red g c a dst
    m.1 = (JPEG2000.Decode.centeredTile L h data red t a >>= fun out =>
      JPEG2000.NativeOutput.writeTile L h.siz red out.layout out.coding dst out.sources) ∧
    m.2 ≤ prefixBudget p L data.size caps + nativeBudget p L ∧
    ∀ out, JPEG2000.Decode.centeredTile L h data red t a = .ok out →
      ∃ (ps : Array JPEG2000.TileDispatch.Spatial) (bs : List TileColorPlacement.Backing),
        (TileColorPlacement.preColourMeter (TileColorPlacement.componentBytes L)
          L h data out.layout out.coding a red).1 = .ok ps ∧
        bs.map (·.source) = ps.toList.map (·.source) ∧
        (bs.map (·.logicalBytes)).sum ≤ (4+TileColorPlacement.componentBytes L)*L.maxWorkSamples ∧
        ∀ s ∈ out.sources, TileColorPlacement.Reader ps s := by
  have components := prefix_work parsed layout a p caps stores (red := red)
  have work := TileColorPlacement.native_tile_work 0 parsed layout origin dst (red := red)
  have bytes := TileColorPlacement.native_tile_work (colourBytes L) parsed layout origin dst (red := red)
  refine ⟨?_,Nat.add_le_add components.2 (Nat.add_le_add (Nat.mul_le_mul_right _ work.2)
    (Nat.mul_le_mul_right _ bytes.2)),fun _ ok => TileColorPlacement.centeredTile_backing_bytes parsed origin ok⟩
  have fold : (g.comps.foldl (fun n tc => n+rectArea (Assemble.reduceRect tc.rect red)) 0) =
      Resources.tileCells g red := Resources.array_foldl_sum _ _ (fun _ _ => rfl) _
  simp only [tile,components.1,(TileColorPlacement.sources_work ..).1,
    (TileColorPlacement.writeTile_work parsed layout ..).1,JPEG2000.Decode.centeredTile,layout,
    JPEG2000.TileDispatch.tile,fold,Equiv.ok_bind,bind_assoc,pure_bind]

/-- Required packet-history bridge for a parsed input. Only actual successful
packet outputs and their matching layouts occur. Omitted tiles have empty stores. -/
def ParsedStores (caps : StoreCaps) (L : Limits) (h : Header) (data : ByteArray) : Prop :=
  ∀ (tp : TileParams) hs incoming a, JPEG2000.Tier2.Headers.decodeWithStream L h data tp hs incoming = .ok a →
    ∀ g c, Progression.Layout.ofHeader h tp.index = .ok (g,c) → caps.Holds g (some a)

private theorem emptyStore (caps : StoreCaps) (g : Progression.Layout) : caps.Holds g none := by
  intro i r
  simp [AssemblyCost.selected,Array.getD_eq_getD_getElem?]

/-- Recover the component charge from the packet trace at its actual cursor and
incoming pass count. A failed header gather or packet callback reaches no component. -/
private def visitCharge (p : Prices) (L : Limits) (h : Header) (data : ByteArray) (red : Nat)
    (idx : Array (Array Nat)) (v : PacketTraversal.TileVisit) :=
  let afterPackets := fun a => match Progression.Layout.ofHeader h v.tile with
    | .error _ => 0
    | .ok (g,c) => (componentPrefix p L h data g c a red).2
  match PacketTraversal.presentAt h v.tile v.cursor with
  | none => afterPackets none
  | some tp =>
    match JPEG2000.Tier2.Headers.headerStreamAt h data tp (idx.getD v.cursor #[]) with
    | .error _ => 0
    | .ok hs =>
      match JPEG2000.Tier2.Headers.decodeWithStream L h data tp hs v.passesBefore with
      | .error _ => 0
      | .ok a => afterPackets (some a)

private theorem visit_le {L : Limits} {h : Header} {data : ByteArray} (parsed : Header.parse L data = .ok h)
    (p : Prices) (caps : StoreCaps) (stores : ParsedStores caps L h data) (red : Nat)
    (idx : Array (Array Nat)) (v : PacketTraversal.TileVisit) :
    visitCharge p L h data red idx v ≤ prefixBudget p L data.size caps := by
  unfold visitCharge
  dsimp only
  cases pick : PacketTraversal.presentAt h v.tile v.cursor with
  | none =>
    cases layout : Progression.Layout.ofHeader h v.tile with
    | error => exact Nat.zero_le _
    | ok pair => obtain ⟨g,c⟩ := pair; exact (prefix_work parsed layout none p caps (emptyStore caps g)).2
  | some tp =>
    have atTile : tp.index = v.tile := by
      unfold PacketTraversal.presentAt at pick
      split at pick <;> try contradiction
      split at pick <;> simp_all
    dsimp only
    cases head : JPEG2000.Tier2.Headers.headerStreamAt h data tp (idx.getD v.cursor #[]) with
    | error => exact Nat.zero_le _
    | ok hs =>
      dsimp only
      cases packet : JPEG2000.Tier2.Headers.decodeWithStream L h data tp hs v.passesBefore with
      | error => exact Nat.zero_le _
      | ok a =>
        dsimp only
        cases layout : Progression.Layout.ofHeader h v.tile with
        | error => exact Nat.zero_le _
        | ok pair =>
          obtain ⟨g,c⟩ := pair
          exact (prefix_work parsed layout (some a) p caps
            (stores tp hs v.passesBefore a packet g c (atTile ▸ layout))).2

/-- Sum the two observations on the public prefix. Proof instrumentation replays
the packet selection to recover the original store. Packet decoding itself has
its independent work theorem. -/
def measure (p : Prices) (L : Limits) (data : ByteArray) (red : Nat) :=
  let work := PublicPacketWork.measurePlacement 0 L data red
  let bytes := PublicPacketWork.measurePlacement (colourBytes L) L data red
  let vs := (PublicPacketWork.measure L data red).1
  let components := match PublicPacketWork.prepareTiles L data red with
    | .error _ => 0
    | .ok (h,_) =>
      let index : Except Error (Array (Array Nat)) :=
        if h.ppm.segments.isEmpty then pure #[] else JPEG2000.Tier2.Headers.ppmChunkIndex L h
      match index with
      | .error _ => 0
      | .ok idx => (vs.map (visitCharge p L h data red idx)).sum
  (work.1,components + (work.2*nativeRate p L + bytes.2*p.bytes))

private theorem sumCap {α : Type} (xs : List α) (f : α → Nat) (cap : Nat) (h : ∀ x ∈ xs, f x ≤ cap) :
    (xs.map f).sum ≤ xs.length*cap := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.succ_mul]
    have := h x (by simp)
    have := ih (fun y hy => h y (by simp [hy]))
    omega

/-- Public reconstruction work and logical workspace charges on the exact visited
prefix, including its first failure. Instantiating the five translated store caps
with functions of limits and input length is the packet-history obligation. -/
theorem decode_work (p : Prices) (L : Limits) (data : ByteArray) (red : Nat) (caps : StoreCaps)
    (stores : ∀ h, Header.parse L data = .ok h → ParsedStores caps L h data) :
    let m := measure p L data red
    let vs := (PublicPacketWork.measure L data red).1
    let budget := prefixBudget p L data.size caps + nativeBudget p L
    m.1 = decodeCodestream L data red ∧ m.2 ≤ vs.length*budget ∧ m.2 ≤ L.maxTiles*budget := by
  let vs := (PublicPacketWork.measure L data red).1
  have num := (PublicPacketWork.decode_packet_work L data red).2.1
  have work := PublicPacketWork.decode_placement_work 0 L data red
  have bytes := PublicPacketWork.decode_placement_work (colourBytes L) L data red
  have hnative : (PublicPacketWork.measurePlacement 0 L data red).2*nativeRate p L +
      (PublicPacketWork.measurePlacement (colourBytes L) L data red).2*p.bytes ≤ vs.length*nativeBudget p L := by
    unfold nativeBudget
    rw [Nat.mul_add,← Nat.mul_assoc,← Nat.mul_assoc]
    exact Nat.add_le_add (Nat.mul_le_mul_right _ work.2.1) (Nat.mul_le_mul_right _ bytes.2.1)
  have total : (measure p L data red).2 ≤ vs.length*(prefixBudget p L data.size caps+nativeBudget p L) := by
    unfold measure
    dsimp only
    rw [Nat.mul_add]
    apply Nat.add_le_add _ hnative
    cases entry : PublicPacketWork.prepareTiles L data red with
    | error => exact Nat.zero_le _
    | ok pair =>
      unfold PublicPacketWork.prepareTiles at entry
      obtain ⟨_,_,tail⟩ := Tier2Equiv.bind_ok entry
      obtain ⟨h,parsed,tail⟩ := Tier2Equiv.bind_ok tail
      obtain ⟨dst,_,last⟩ := Tier2Equiv.bind_ok tail
      cases last
      dsimp only
      split
      · exact Nat.zero_le _
      · exact sumCap vs _ _ (fun v _ => visit_le parsed p caps (stores _ parsed) red _ v)
  exact ⟨work.1,total,Nat.le_trans total (Nat.mul_le_mul_right _ num)⟩

private theorem fits_add {b : Nat} {x y : Int} (hx : WideArithmetic.Fits b x)
    (hy : WideArithmetic.Fits b y) : WideArithmetic.Fits (b+1) (x+y) := by
  unfold WideArithmetic.Fits at *
  have := Int.natAbs_add_le x y
  rw [Nat.pow_succ]
  omega

/-- Source, shift, half-unit, biased numerator, quotient and unsigned offset of
the native G.1 placement kernel at its actual fractional precision. -/
theorem placement_operands {L : Limits} {h : Header} {data : ByteArray} {t red : Nat}
    {a : Option TileCodeBlocks} {out : JPEG2000.Decode.CenteredTile}
    (parsed : Header.parse L data = .ok h) (ok : JPEG2000.Decode.centeredTile L h data red t a = .ok out)
    (i : Nat) (s : JPEG2000.NativeOutput.Source) (hs : s ∈ out.sources)
    (j : Fin (s.width*s.height)) (r : NativeSampleRange) :
    let F := if (out.layout.comp i).params.transform == .reversible53 then 0 else
      Assemble.fracBitsOf h.siz (out.coding.mctApplies h.siz) i
    let scale := (2 : Int)^F
    let half := scale/2
    let z := s.read j
    let off := Spec.MCT.dcOffset r.signed r.depth
    ∀ x ∈ [z,scale,half,z+half,(z+half)/scale,off,z+off,((z+half)/scale)+off],
      TileColorPlacement.signedBytes x ≤ placementBytes L := by
  obtain ⟨⟨g,c⟩,layout,tail⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨sources,tileOk,last⟩ := Tier2Equiv.bind_ok tail
  cases last
  let b := 393+540*L.maxDecompLevels
  let F := if (g.comp i).params.transform == .reversible53 then 0 else
      Assemble.fracBitsOf h.siz (c.mctApplies h.siz) i
  let scale := (2 : Int)^F
  let z := s.read j
  let off := Spec.MCT.dcOffset r.signed r.depth
  have hz : WideArithmetic.Fits b z := WideArithmetic.parsed_tile parsed layout a red (parsedBlocks parsed layout) tileOk s hs j
  have hF : F ≤ 26 := by
    unfold F
    split <;> try omega
    unfold Assemble.fracBitsOf
    split <;> apply Nat.sub_le
  have powFit (k : Nat) (hk : k ≤ b) : WideArithmetic.Fits b ((2 : Int)^k) := by
    simpa using Nat.pow_le_pow_right (n := 2) (by decide) hk
  have hscale : WideArithmetic.Fits b scale := powFit _ (by dsimp [b]; omega)
  have hoff : WideArithmetic.Fits b off := by
    unfold off Spec.MCT.dcOffset
    split
    · exact Nat.zero_le _
    · exact powFit _ (by have := r.valid.2; dsimp [b]; omega)
  have half : WideArithmetic.Fits b (scale/2) := Nat.le_trans (Int.natAbs_ediv_le_natAbs ..) hscale
  have bias := fits_add hz half
  have quot : WideArithmetic.Fits (b+1) ((z+scale/2)/scale) := Nat.le_trans (Int.natAbs_ediv_le_natAbs ..) bias
  have grow {k : Nat} {x : Int} (hx : WideArithmetic.Fits k x) : WideArithmetic.Fits (k+1) x :=
    Nat.le_trans hx (Nat.pow_le_pow_right (by decide) (Nat.le_succ k))
  have endpt := fits_add quot (grow hoff)
  have rounded {x : Int} (hx : WideArithmetic.Fits (b+2) x) :
      TileColorPlacement.signedBytes x ≤ placementBytes L := by
    have w := WideArithmetic.magnitude_bits hx
    unfold b at w
    unfold TileColorPlacement.signedBytes placementBytes
    omega
  change ∀ x ∈ [z,scale,scale/2,z+scale/2,(z+scale/2)/scale,off,z+off,(z+scale/2)/scale+off], _
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  apply rounded
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact grow (grow hz)
  · exact grow (grow hscale)
  · exact grow (grow half)
  · exact grow bias
  · exact grow quot
  · exact grow (grow hoff)
  · exact grow (fits_add hz hoff)
  · exact endpt

/-- Invariant for a partly filled wide Mallat raster. It starts at zero, and the
step holds for each completed block before a later decode or placement failure. -/
def Mallat (rect : Rect) (q : JPEG2000.WideQuant.Plane) : Prop :=
  q.rect = rect ∧ WideArithmetic.RasterFits 372 q.samples.toArray

private theorem writeBound {n area : Nat} (index : Fin n → Fin area) (value : Fin n → Int)
    (hv : ∀ i, WideArithmetic.Fits 372 (value i)) (k : Nat) (hk : k ≤ n) (dst : Vector Int area)
    (old : WideArithmetic.RasterFits 372 dst.toArray) :
    WideArithmetic.RasterFits 372 (JPEG2000.WideQuant.writeCells index value k hk dst).toArray := by
  induction k generalizing dst with
  | zero => exact old
  | succ k ih =>
    apply ih
    intro x hx
    rcases Array.mem_or_eq_of_mem_set (w := by rw [dst.size_toArray]; exact (index ⟨k,hk⟩).isLt) hx with hx | rfl
    · exact old _ hx
    · exact hv _

/-- Parsed assembly establishes and preserves the Mallat invariant across each
individual placement, without requiring a final plane from the entire traversal. -/
theorem mallat_prefix {L : Limits} {h : Header} {data : ByteArray} {t red : Nat}
    {g : Progression.Layout} {c : Coding} (parsed : Header.parse L data = .ok h)
    (layout : Progression.Layout.ofHeader h t = .ok (g,c)) (i : Fin g.numComps) :
    let tc := g.comp i
    let rect := Assemble.reduceRect tc.rect red
    let d := (h.siz.components.getD i default).depth.toNat
    let F := Assemble.fracBitsOf h.siz (c.mctApplies h.siz) i
    (∀ q, JPEG2000.WideQuant.zeroChecked L rect = .ok q → Mallat rect q) ∧
    ∀ dst r band cb cs out, Mallat rect dst →
      JPEG2000.WideAssembly.decodeBlock data tc.params r band cb = .ok cs →
      JPEG2000.WideQuant.dequantBlock L dst tc.params d red r band cb.geom.rect F cs = .ok out →
      Mallat rect out := by
  dsimp only
  constructor
  · intro q start
    unfold JPEG2000.WideQuant.zeroChecked at start
    obtain ⟨_,_,rest⟩ := Tier2Equiv.bind_ok start
    split at rest <;> try contradiction
    cases rest
    refine ⟨rfl,?_⟩
    intro z hz
    change z ∈ Array.replicate _ 0 at hz
    obtain ⟨_,rfl⟩ := Array.mem_replicate.mp hz
    exact Nat.zero_le _
  · intro dst r band cb cs out old dec place
    refine ⟨(AssemblyCost.wide_storage place).1.trans old.1,?_⟩
    have fits (z) (hz : z ∈ cs) :
        WideArithmetic.Fits 372 (JPEG2000.WideQuant.prepare (Spec.Quant.bandQuant (g.comp i).params
          (h.siz.components.getD i default).depth.toNat r band)
          (Assemble.fracBitsOf h.siz (c.mctApplies h.siz) i) z) := by
      obtain ⟨terms,cap⟩ := block_operands parsed layout i r band cb dec z hz
      obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,value⟩ := terms
      exact Nat.le_trans value cap
    unfold JPEG2000.WideQuant.dequantBlock at place
    obtain ⟨_,_,tail⟩ := Tier2Equiv.bind_ok place
    obtain ⟨_,_,tail⟩ := Tier2Equiv.bind_ok tail
    dsimp only at tail
    repeat' (split at tail <;> try contradiction)
    cases tail
    exact writeBound _ _ (fun _ => fits _ (Array.getElem_mem _)) _ _ _ old.2

private theorem mallatBytes {r : Rect} {q : JPEG2000.WideQuant.Plane} (within : Mallat r q) :
    (q.samples.toArray.toList.map TileColorPlacement.signedBytes).sum ≤ 47*rectArea r := by
  have each (z : Int) (hz : z ∈ q.samples.toArray.toList) : TileColorPlacement.signedBytes z ≤ 47 := by
    have bits := WideArithmetic.magnitude_bits (within.2 z (Array.mem_toList_iff.mp hz))
    unfold TileColorPlacement.signedBytes
    omega
  have total := sumCap q.samples.toArray.toList TileColorPlacement.signedBytes 47 each
  simpa only [Array.length_toList,Vector.size_toArray,within.1,Nat.mul_comm 47] using total

/-- Logical payload of retained earlier rasters together with the Mallat
inputs and all newly materialised transform cells of the current callback.
A packed buffer may be copied on every write. The wide charge includes both
axis families and intermediate passes. Block-local domains are in `block_workspace`. -/
theorem live_workspace {L : Limits} {h : Header} {data : ByteArray} {t red : Nat}
    {g : Progression.Layout} {c : Coding} {a : Option TileCodeBlocks} {b : Option Spec.Tier2.TileOut}
    (parsed : Header.parse L data = .ok h) (layout : Progression.Layout.ofHeader h t = .ok (g,c))
    (origin : TileDispatch.Packets L h data t a b) (admission : Resources.tileCells g red ≤ L.maxWorkSamples)
    (done : List (Fin g.numComps × JPEG2000.TileDispatch.Spatial))
    (order : (done.map fun e => e.1.val).Sublist (List.range' 0 g.numComps))
    (calls : ∀ e ∈ done, JPEG2000.TileDispatch.component L h data g c a e.1 red = .ok e.2)
    (i : Fin g.numComps) (packed : Option Plane) (wide : Option JPEG2000.WideQuant.Plane)
    (dims : ∀ z, packed = some z → z.width*z.height = AssemblyCost.planeArea (g.comp i) red)
    (mallat : ∀ q, wide = some q → Mallat (Assemble.reduceRect (g.comp i).rect red) q) :
    let payload : Prices := ⟨0,0,0,1,0⟩
    let wave := transforms payload L data (g.comp i) (h.siz.components.getD i default).depth.toNat
      (Assemble.fracBitsOf h.siz (c.mctApplies h.siz) i) red (AssemblyCost.selected a i)
    ∃ bs : List TileColorPlacement.Backing,
      bs.map (·.source) = done.map (fun e => e.2.source) ∧
      (bs.map (·.logicalBytes)).sum + (packed.map (·.data.size)).getD 0 +
        (wide.map (fun q => (q.samples.toArray.toList.map TileColorPlacement.signedBytes).sum)).getD 0 + wave ≤
          (4+TileColorPlacement.componentBytes L+4+47)*L.maxWorkSamples + transformBudget payload L := by
  obtain ⟨bs,src,previous⟩ := prefix_backing parsed layout origin admission done order calls
  have entry := AssemblyCost.native_budget parsed layout a i red
  simp only [admission,↓reduceIte] at entry
  have depth := (WideHeaderBounds.parsed_component_bounds parsed layout i red).1.levels
  have wave := transforms_bound (⟨0,0,0,1,0⟩ : Prices) L data (g.comp i)
    (h.siz.components.getD i default).depth.toNat (Assemble.fracBitsOf h.siz (c.mctApplies h.siz) i)
    red (AssemblyCost.selected a i) entry.1 (by omega)
  have wideBound : (wide.map (fun q => (q.samples.toArray.toList.map TileColorPlacement.signedBytes).sum)).getD 0 ≤
      47*L.maxWorkSamples := by
    cases wide with
    | none => exact Nat.zero_le _
    | some q => exact Nat.le_trans (mallatBytes (mallat q rfl)) (Nat.mul_le_mul_left 47 entry.1)
  have packedBound : (packed.map (·.data.size)).getD 0 ≤ 4*L.maxWorkSamples := by
    cases packed with
    | none => exact Nat.zero_le _
    | some z =>
      change z.data.size ≤ _
      rw [z.size_eq,dims z rfl]
      exact Nat.mul_le_mul_left _ entry.1
  refine ⟨bs,src,?_⟩
  have total := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add previous packedBound) wideBound) wave
  simpa only [Nat.add_mul] using total

private theorem promotedFits {b : Nat} {s : JPEG2000.IrreversibleDispatch.Spatial}
    (h : WideArithmetic.SourceFits b s.source) (i : Fin (rectArea s.toWide.rect)) :
    WideArithmetic.Fits b (s.toWide.samples.get i) := by
  cases s with
  | compact r f p hw hh =>
    change Fin (rectArea r) at i
    change WideArithmetic.Fits b ((Vector.ofFn (n := rectArea r) _)[i.val])
    rw [Vector.getElem_ofFn]
    exact h ⟨i.val,by change i.val < p.width*p.height; rw [hw,hh]; exact i.isLt⟩
  | wide => exact h i

/-- At the wide ICT call site, promotion preserves every operand bound even
when its peers have different original backings. The bound covers every biased
numerator and product in the matrix before the channel vectors exist. -/
theorem promoted_operands {L : Limits} {h : Header} {data : ByteArray} {t red : Nat}
    {g : Progression.Layout} {c : Coding} (parsed : Header.parse L data = .ok h)
    (layout : Progression.Layout.ofHeader h t = .ok (g,c)) (a : Option TileCodeBlocks)
    (iy ic ir : Fin g.numComps) {y cb cr : JPEG2000.IrreversibleDispatch.Spatial}
    (hy : JPEG2000.TileDispatch.component L h data g c a iy red = .ok (.irrev y))
    (hc : JPEG2000.TileDispatch.component L h data g c a ic red = .ok (.irrev cb))
    (hr : JPEG2000.TileDispatch.component L h data g c a ir red = .ok (.irrev cr))
    (j : Fin (rectArea y.toWide.rect)) (k : Fin (rectArea cb.toWide.rect)) (l : Fin (rectArea cr.toWide.rect)) :
    WideArithmetic.ICTOperands (372+540*L.maxDecompLevels+21)
      (y.toWide.samples.get j) (cb.toWide.samples.get k) (cr.toWide.samples.get l) := by
  simpa only [Nat.max_self] using WideArithmetic.ict_operands
    (promotedFits (s := y) (source_bound parsed layout a iy hy) j)
    (promotedFits (s := cb) (source_bound parsed layout a ic hc) k)
    (promotedFits (s := cr) (source_bound parsed layout a ir hr) l)

/-- Logical payload of one Tier-1 wide cell, allowing one byte for each of
the four Boolean fields in addition to the signed value and last-plane index. -/
def blockCellBytes (z : JPEG2000.Tier1.WidePlain.Cell) :=
  TileColorPlacement.signedBytes z.value + TileColorPlacement.signedBytes (z.lsbPlane : Int) + 4

/-- The Tier-1 raster supplied to a placement that may subsequently reject.
The 47-byte assembly price dominates each wide cell and packed word. -/
theorem block_payload {L : Limits} {h : Header} {data : ByteArray} {t : Nat}
    {g : Progression.Layout} {c : Coding} (parsed : Header.parse L data = .ok h)
    (layout : Progression.Layout.ofHeader h t = .ok (g,c)) (i : Fin g.numComps)
    (r : Nat) (band : JPEG2000.Tier2.Geometry.Band) (cb : JPEG2000.Tier2.Packet.CodeBlock) :
    let params := (g.comp i).params
    (∀ o, JPEG2000.ReversibleDispatch.checkedBlock data params r band cb = .ok o →
      o.plane.data.size ≤ 4*4096 ∧ o.flags.size ≤ 8196) ∧
    ∀ cs, JPEG2000.WideAssembly.decodeBlock data params r band cb = .ok cs →
      cs.size ≤ 4096 ∧ (∀ z ∈ cs, blockCellBytes z ≤ 43) ∧
      (cs.toList.map blockCellBytes).sum ≤ 43*4096 := by
  obtain ⟨_,_,packed,wide⟩ := AssemblyCost.block_storage
    (WideHeaderBounds.parsed_component_bounds parsed layout i 0).1 data r band cb
  constructor
  · intro o ok
    obtain ⟨sz,_,border,area⟩ := packed o ok
    exact ⟨sz ▸ Nat.mul_le_mul_left _ area,border⟩
  · intro cs ok
    obtain ⟨_,count,each⟩ := wide cs ok
    have cells (z) (hz : z ∈ cs) : blockCellBytes z ≤ 43 := by
      obtain ⟨_,lsb,mag⟩ := each z hz
      have hm := WideArithmetic.magnitude_bits (b := 292) (x := z.value) (Nat.le_of_lt mag)
      have hl := WideArithmetic.magnitude_bits (b := 9) (x := (z.lsbPlane : Int))
        (by change z.lsbPlane ≤ 512; omega)
      simp only [Int.natAbs_natCast] at hl
      unfold blockCellBytes TileColorPlacement.signedBytes
      simp only [Int.natAbs_natCast]
      omega
    refine ⟨count,cells,?_⟩
    have total := sumCap cs.toList blockCellBytes 43 (by simpa using cells)
    simpa only [Nat.mul_comm 43] using Nat.le_trans total (Nat.mul_le_mul_right 43 (by simpa using count))


end JPEG2000.Spec.Resources.ReconstructionCost
