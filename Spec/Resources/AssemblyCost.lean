import Spec.Resources.HeaderWork
import Spec.Resources.Tier1Work
import Spec.Resources.WideArithmetic
import Spec.NativeResources

/-!
# Coefficient assembly work (Plan.md §§3–5, 7; T.800 B.6–B.10, D, E.1, H.2)

The meter returns its charge alongside an `Except`, including the prefix already
spent on a rejected compact attempt. Its units are packet-record visits, segment
metadata visits, copied bytes, Tier-1 work units, level halvings and raster accesses.
The inverse transform and spatial output consume the assembled plane separately.
-/

namespace JPEG2000.Spec.Resources.AssemblyCost

open JPEG2000.Header JPEG2000.Tier2.Geometry JPEG2000.Tier2.Packet JPEG2000.Bytes

private abbrev Run (α : Type) := Except Error α × Nat

private def thenRun {α β : Type} (x : Run α) (f : α → Run β) : Run β :=
  match x.1 with
  | .error e => (.error e, x.2)
  | .ok a => let y := f a; (y.1, x.2 + y.2)

private theorem then_value {α β : Type} (x : Run α) (f : α → Run β) :
    (thenRun x f).1 = x.1.bind (fun a => (f a).1) := by
  cases x with | mk v n => cases v <;> rfl

private theorem then_bound {α β : Type} {x : Run α} {f : α → Run β} {m n : Nat}
    (ha : x.2 ≤ m) (hb : ∀ a, (f a).2 ≤ n) : (thenRun x f).2 ≤ m+n := by
  unfold thenRun
  split
  · dsimp; omega
  · exact Nat.add_le_add ha (hb _)

private def scan {α β : Type} (f : α → β → Run β) : List α → β → Run β
  | [], a => (.ok a, 0)
  | x :: xs, a => thenRun ((f x a).1, 1 + (f x a).2) (scan f xs)

private theorem scan_value {α β : Type} (f : α → β → Run β) (xs : List α) (a : β) :
    (scan f xs a).1 = forIn xs a (fun x b => do
      let z ← (f x b).1
      pure (.yield z)) := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
    rw [scan, then_value, List.forIn_cons]
    dsimp only
    cases he : (f x a).1 with
    | error e => rfl
    | ok z => exact ih z

private def visitSum {α : Type} (xs : List α) (f : α → Nat) :=
  (xs.map fun x => 1 + f x).sum

private theorem scan_bound {α β : Type} (f : α → β → Run β) (xs : List α)
    (w : α → Nat) (h : ∀ x ∈ xs, ∀ b, (f x b).2 ≤ w x) (a : β) :
    (scan f xs a).2 ≤ visitSum xs w := by
  induction xs generalizing a with
  | nil => exact Nat.le_refl _
  | cons x xs ih =>
    apply then_bound
    · exact Nat.add_le_add_left (h x (by simp) a) 1
    · exact ih (fun z hz => h z (by simp [hz]))

private def active (cb : CodeBlock) := cb.numPasses != 0 && !rectEmpty cb.geom.rect

/-- The counted production walk. Every loop iteration costs one visit. Only active
records call `step`, and a failing callback terminates all four loops. -/
def walk {α : Type} (nl : Nat) (ps : Array (Array PrecinctOut)) (init : α)
    (step : α → Nat → Band → CodeBlock → Except Error α × Nat) : Except Error α × Nat :=
  scan (fun r => scan (fun prec => scan (fun bo => scan (fun cb a =>
    if active cb then step a r bo.band cb else (.ok a, 0)) bo.blocks.toList)
    prec.bands.toList) (ps.getD r #[]).toList) (List.range' 0 (min (nl+1) ps.size)) init

/-- Erasing work returns the real result, including the exact first error. -/
theorem walk_value {α : Type} (nl : Nat) (ps : Array (Array PrecinctOut)) (a : α)
    (step : α → Nat → Band → CodeBlock → Except Error α × Nat) :
    (walk nl ps a step).1 = JPEG2000.WideAssembly.visitBlocks nl ps a
      (fun z r b cb => (step z r b cb).1) := by
  simp only [walk, scan_value, Array.forIn_toList, JPEG2000.WideAssembly.visitBlocks,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_one_sub_one, Nat.div_one, bind_pure, active]
  congr 1
  funext r a
  congr 1
  congr 1
  funext prec a
  congr 1
  congr 1
  funext bo a
  congr 1
  congr 1
  funext cb a
  split <;> simp_all only [↓reduceIte] <;> rfl

/-- Full traversal charge, parameterised by the local bound for an invoked block.
Zero-pass and empty records still pay the unit record visit. -/
def topology (nl : Nat) (ps : Array (Array PrecinctOut)) (w : Nat → Band → CodeBlock → Nat) :=
  visitSum (List.range' 0 (min (nl+1) ps.size)) fun r =>
    visitSum (ps.getD r #[]).toList fun prec =>
      visitSum prec.bands.toList fun bo =>
        visitSum bo.blocks.toList fun cb => if active cb then w r bo.band cb else 0

/-- Sum over the packet store bounds the work of any prefix of the real walk. -/
theorem walk_bound {α : Type} (nl : Nat) (ps : Array (Array PrecinctOut)) (a : α)
    (step : α → Nat → Band → CodeBlock → Except Error α × Nat)
    (w : Nat → Band → CodeBlock → Nat) (h : ∀ a r b cb, (step a r b cb).2 ≤ w r b cb) :
    (walk nl ps a step).2 ≤ topology nl ps w := by
  apply scan_bound; intro r _ a
  apply scan_bound; intro prec _ a
  apply scan_bound; intro bo _ a
  apply scan_bound; intro cb _ a
  split
  · exact h ..
  · exact Nat.le_refl _

private def row (f : Int32 → Nat → Int32 × Bool) (o : Tier1.CodeBlockOut) (y : Nat) :
    Nat → Nat → Nat → Plane → Bool → (Plane × Bool) × Nat
  | 0, _, _, p, ok => ((p,ok),0)
  | k+1, x, d, p, ok =>
    let v := (o.plane.get? (y * o.plane.width + x)).getD 0
    let t := f v (o.lsbPlane x y)
    let dst := if h : d < p.width * p.height then p.set d t.1 h else p
    let rest := row f o y k (x+1) (d+1) dst (ok && t.2)
    (rest.1, 2 + (decide (d < p.width * p.height)).toNat + rest.2)

private theorem row_spec (f : Int32 → Nat → Int32 × Bool) (o : Tier1.CodeBlockOut)
    (y k x d : Nat) (p : Plane) (ok : Bool) :
    (row f o y k x d p ok).1 = JPEG2000.Quant.blockRow f o y k x d p ok ∧
    (row f o y k x d p ok).2 ≤ 3*k := by
  induction k generalizing x d p ok with
  | zero => exact ⟨rfl, Nat.le_refl _⟩
  | succ k ih =>
    simp only [row, JPEG2000.Quant.blockRow]
    refine ⟨(ih ..).1, ?_⟩
    apply Nat.le_trans (Nat.add_le_add_left (ih ..).2 _)
    cases decide (d < p.width * p.height) <;> simp [Nat.mul_succ] <;> omega

private def rows (f : Int32 → Nat → Int32 × Bool) (o : Tier1.CodeBlockOut) (px py : Nat) :
    Nat → Nat → Plane → Bool → (Plane × Bool) × Nat
  | 0, _, p, ok => ((p,ok),0)
  | n+1, y, p, ok =>
    let head := row f o y o.plane.width 0 ((py+y)*p.width + px) p ok
    let tail := rows f o px py n (y+1) head.1.1 head.1.2
    (tail.1, 1 + head.2 + tail.2)

private theorem rows_spec (f : Int32 → Nat → Int32 × Bool) (o : Tier1.CodeBlockOut)
    (px py n y : Nat) (p : Plane) (ok : Bool) :
    (rows f o px py n y p ok).1 = JPEG2000.Quant.blockRows f o px py n y p ok ∧
    (rows f o px py n y p ok).2 ≤ n * (1 + 3 * o.plane.width) := by
  induction n generalizing y p ok with
  | zero => exact ⟨rfl, by simp [rows]⟩
  | succ n ih =>
    simp only [rows, JPEG2000.Quant.blockRows]
    have h := row_spec f o y o.plane.width 0 ((py+y)*p.width+px) p ok
    constructor
    · rw [(ih ..).1, h.1]
    · rw [Nat.succ_mul]
      apply Nat.le_trans (Nat.add_le_add (Nat.add_le_add_left h.2 1) (ih ..).2)
      omega

/-- Reverse-raster placement counted in source reads and destination writes. -/
def wideWrites {n area : Nat} (index : Fin n → Fin area) (value : Fin n → Int)
    (k : Nat) (hk : k ≤ n) (dst : Vector Int area) : Vector Int area × Nat :=
  match k with
  | 0 => (dst,0)
  | k+1 =>
    let i : Fin n := ⟨k,hk⟩
    let j := index i
    let tail := wideWrites index value k (Nat.le_of_lt hk) (dst.set j.val (value i) j.isLt)
    (tail.1,2+tail.2)

private theorem wideWrites_spec {n area : Nat} (index : Fin n → Fin area) (value : Fin n → Int)
    (k : Nat) (hk : k ≤ n) (dst : Vector Int area) :
    (wideWrites index value k hk dst).1 = JPEG2000.WideQuant.writeCells index value k hk dst ∧
    (wideWrites index value k hk dst).2 = 2*k := by
  induction k generalizing dst with
  | zero => exact ⟨rfl,rfl⟩
  | succ k ih =>
    simp only [wideWrites, JPEG2000.WideQuant.writeCells]
    exact ⟨(ih ..).1, by rw [(ih ..).2]; omega⟩

/-- Low-pass rectangle and the number of repeated F.3 halvings used to locate it. -/
def countedHalf (r : Rect) : Nat → Rect × Nat
  | 0 => (r,0)
  | n+1 => let t := countedHalf r n; (JPEG2000.DWT53.halfRect t.1,t.2+1)

private theorem countedHalf_spec (r : Rect) (n : Nat) :
    countedHalf r n = (JPEG2000.DWT53.halfN r n,n) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [countedHalf, ih, JPEG2000.DWT53.halfN]

/-- Maximum recursive halvings for a block origin in either placement path. -/
theorem origin_levels (tc : Rect) (nl r : Nat) :
    (countedHalf tc (bandLevel nl r)).1 = JPEG2000.DWT53.halfN tc (bandLevel nl r) ∧
    (countedHalf tc (bandLevel nl r)).2 ≤ nl + 1 := by
  rw [countedHalf_spec]
  constructor
  · rfl
  · change bandLevel nl r ≤ nl+1
    unfold bandLevel; split <;> omega

/-- Instrument the packed write loop after the same four checks as the decoder. -/
def compactPlacement (dst : Plane) (tc : Rect) (nl r : Nat) (b : Band)
    (cb : Rect) (q : Spec.Quant.BandQuant) (F : Nat) (o : Tier1.CodeBlockOut) : Except Error (Plane × Bool) × Nat :=
  if dst.width ≠ tc.x1-tc.x0 ∨ dst.height ≠ tc.y1-tc.y0 then
    (.error (.malformed JPEG2000.Quant.loc "dequantisation: plane size differs from the tile-component"),0)
  else if r > nl then
    (.error (.malformed JPEG2000.Quant.loc s!"dequantisation: resolution {r} > NL = {nl}"),0)
  else
    let band := bandRect tc (bandLevel nl r) b
    if o.plane.width ≠ cb.x1-cb.x0 ∨ o.plane.height ≠ cb.y1-cb.y0 then
      (.error (.malformed JPEG2000.Quant.loc "dequantisation: code-block plane size differs from its rectangle"),0)
    else if cb.x0 < band.x0 ∨ cb.y0 < band.y0 ∨ band.x1 < cb.x1 ∨ band.y1 < cb.y1 then
      (.error (.malformed JPEG2000.Quant.loc "dequantisation: code-block outside its band"),0)
    else
      let (ox,oy) := JPEG2000.Quant.bandOrigin tc nl r b
      let f := if q.reversible then JPEG2000.Quant.revCoeff q.roiShift else
        JPEG2000.Quant.irrevCoeff (JPEG2000.Quant.irrevConsts q F) q.roiShift
      let v := rows f o (ox + (cb.x0-band.x0)) (oy + (cb.y0-band.y0)) o.plane.height 0 dst true
      (.ok v.1, (if r = 0 then 0 else bandLevel nl r) + v.2)

/-- The compact kernel reads coefficient and last-plane data and conditionally writes
a packed cell. Its row visits, reads and writes cost at most height plus three times
area. All rejecting guards precede the raster loop and origin calculation. -/
theorem compact_placement (dst : Plane) (tc : Rect) (nl r : Nat) (b : Band) (cb : Rect)
    (q : Spec.Quant.BandQuant) (F : Nat) (o : Tier1.CodeBlockOut) :
    (compactPlacement dst tc nl r b cb q F o).1 = JPEG2000.Quant.dequantBlock dst tc nl r b cb q F o ∧
    (compactPlacement dst tc nl r b cb q F o).2 ≤ (nl+1) + cb.height + 3 * rectArea cb := by
  unfold compactPlacement JPEG2000.Quant.dequantBlock
  dsimp only
  by_cases hd : dst.width ≠ tc.x1-tc.x0 ∨ dst.height ≠ tc.y1-tc.y0 <;> simp only [hd, ↓reduceIte]
  · exact ⟨rfl,Nat.zero_le _⟩
  by_cases hr : r > nl <;> simp only [hr, ↓reduceIte]
  · exact ⟨rfl,Nat.zero_le _⟩
  by_cases hs : o.plane.width ≠ cb.x1-cb.x0 ∨ o.plane.height ≠ cb.y1-cb.y0 <;> simp only [hs, ↓reduceIte]
  · exact ⟨rfl,Nat.zero_le _⟩
  let band := bandRect tc (bandLevel nl r) b
  by_cases hb : cb.x0 < band.x0 ∨ cb.y0 < band.y0 ∨ band.x1 < cb.x1 ∨ band.y1 < cb.y1
  all_goals simp only [show bandRect tc (bandLevel nl r) b = band from rfl, hb, ↓reduceIte]
  · exact ⟨rfl,Nat.zero_le _⟩
  constructor
  · rw [(rows_spec ..).1]; cases q.reversible <;> rfl
  ·
    apply Nat.le_trans (Nat.add_le_add_left (rows_spec ..).2 _)
    have hw : o.plane.width = cb.width := by change _ = cb.x1-cb.x0; omega
    have hh : o.plane.height = cb.height := by change _ = cb.y1-cb.y0; omega
    rw [hw, hh, Nat.mul_add, Nat.mul_one, rectArea]
    have eq := Nat.mul_left_comm cb.height 3 cb.width
    rw [Nat.mul_comm cb.height cb.width] at eq
    rcases Nat.eq_zero_or_pos r with h|h <;> simp [bandLevel, h, Nat.ne_of_gt] <;> omega

private def widePlacement (L : Limits) (dst : JPEG2000.WideQuant.Plane) (p : CompParams)
    (depth reduce r : Nat) (b : Band) (cb : Rect) (F : Nat) (cells : Array Tier1.WidePlain.Cell) :
    Run JPEG2000.WideQuant.Plane :=
  let out := JPEG2000.WideQuant.dequantBlock L dst p depth reduce r b cb F cells
  -- Containment and size may fail after computing the origin.
  (out, (if r = 0 then 0 else bandLevel (p.levels-reduce) r) +
    (if out.isOk then 2 * rectArea cb else 0))

/-- A successful wide placement performs one source read and one destination write
per cell. The source and destination indices are the indices used by `place`. -/
theorem wide_place (dst : JPEG2000.WideQuant.Plane) (cb : Rect) (ox oy : Nat)
    (f : Tier1.WidePlain.Cell → Int) (cells : Array Tier1.WidePlain.Cell)
    (hs : cells.size = rectArea cb)
    (fit : ox + cb.width ≤ dst.rect.width ∧ oy + cb.height ≤ dst.rect.height) :
    let index (i : Fin (rectArea cb)) : Fin (rectArea dst.rect) :=
      ⟨JPEG2000.WideOutput.destIndex dst.rect.width cb.width ox oy i,
        JPEG2000.WideOutput.destIndex_lt fit.1 fit.2 i.isLt⟩
    let value (i : Fin (rectArea cb)) := f (cells[i.val]'(by rw [hs]; exact i.isLt))
    wideWrites index value (rectArea cb) (Nat.le_refl _) dst.samples =
      ((JPEG2000.WideQuant.place dst cb ox oy f cells hs fit).samples, 2 * rectArea cb) :=
  Prod.ext (wideWrites_spec ..).1 (wideWrites_spec ..).2

private def inspect {α : Type} (test : α → Bool × Nat) : List α → Bool × Nat
  | [] => (true,0)
  | x :: xs =>
    let v := test x
    if v.1 then
      let t := inspect test xs
      (t.1, 1 + v.2 + t.2)
    else (false, 1 + v.2)

private theorem inspect_spec {α : Type} (test : α → Bool × Nat) (xs : List α) (w : α → Nat)
    (h : ∀ x, (test x).2 ≤ w x) :
    (inspect test xs).1 = xs.all (fun x => (test x).1) ∧
    (inspect test xs).2 ≤ visitSum xs w := by
  induction xs with
  | nil => exact ⟨rfl,Nat.le_refl _⟩
  | cons x xs ih =>
    simp only [inspect,List.all_cons,visitSum,List.map_cons,List.sum_cons]
    cases ht : (test x).1 <;> simp only [Bool.false_eq_true,↓reduceIte,Bool.true_and,Bool.false_and]
    · exact ⟨True.intro,by have := h x; omega⟩
    · exact ⟨ih.1,Nat.add_le_add (Nat.add_le_add_left (h x) 1) ih.2⟩

private def validateRanges (data : ByteArray) (cb : CodeBlock) :=
  inspect (fun s => inspect (fun rg => (decide (rg.offset + rg.length ≤ data.size),0)) s.ranges.toList)
    cb.segments.toList

private theorem validate_spec (data : ByteArray) (cb : CodeBlock) :
    (validateRanges data cb).1 = cb.segments.all (fun s => s.ranges.all (fun rg => rg.offset+rg.length ≤ data.size)) ∧
    (validateRanges data cb).2 ≤ cb.segments.size + HeaderWork.blockRanges cb.segments.toList := by
  let test (rg : TilePart.ByteRange) := (decide (rg.offset+rg.length ≤ data.size),0)
  have inner (s : Segment) := inspect_spec test s.ranges.toList (fun _ => 0) (fun _ => Nat.le_refl _)
  have count (xs : List TilePart.ByteRange) : visitSum xs (fun _ => 0) = xs.length := by
    induction xs with
    | nil => rfl
    | cons x xs ih => change 1 + visitSum xs _ = xs.length+1; omega
  have ranges (s : Segment) : (inspect test s.ranges.toList).2 ≤ s.ranges.size := by
    simpa only [count,Array.length_toList] using (inner s).2
  have outer := inspect_spec (fun s => inspect test s.ranges.toList) cb.segments.toList (·.ranges.size) ranges
  constructor
  · exact outer.1.trans (by simp only [(inner _).1, Array.all_toList, test])
  · have sum (xs : List Segment) : visitSum xs (·.ranges.size) = xs.length + HeaderWork.blockRanges xs := by
      induction xs with
      | nil => rfl
      | cons s xs ih =>
        change 1 + s.ranges.size + visitSum xs _ = xs.length+1 + (s.ranges.size+HeaderWork.blockRanges xs)
        rw [ih]; omega
    simpa only [sum,Array.length_toList,validateRanges,test] using outer.2

private def gathered (data : ByteArray) (cb : CodeBlock) : (ByteArray × Array Tier1.Seg) × Nat :=
  if cb.segments.all (·.ranges.size ≤ 1) then ((data,cb.segments.map Assemble.directSeg),0)
  else HeaderWork.chargedBlock data cb.segments.toList (ByteArray.empty,#[])

private theorem gathered_value (data : ByteArray) (cb : CodeBlock) :
    (gathered data cb).1 = Assemble.tier1Input data cb := by
  unfold gathered
  split
  · simp_all [Assemble.tier1Input]
  · exact (HeaderWork.tier1Input_copy_charge data cb (by simp_all)).1

/-- Translated source descriptors in the packet record, counting multiplicity. -/
def rangeCount (cb : CodeBlock) := HeaderWork.blockRanges cb.segments.toList

private def gatherBound (data : ByteArray) (cb : CodeBlock) :=
  (2 * rangeCount cb + cb.segments.size) * (rangeCount cb * data.size)

private def scanCost (cb : CodeBlock) :=
  1 + 3 * cb.segments.size + 2 * rangeCount cb

private def tierBound (cb : CodeBlock) :=
  26006 + 8510 * cb.segments.size + 66002 * min (cb.segments.toList.map (·.passes)).sum 874

private theorem copy_bound (data : ByteArray) (cb : CodeBlock) :
    (gathered data cb).2 ≤ gatherBound data cb := by
  unfold gathered
  split
  · exact Nat.zero_le _
  · exact (HeaderWork.tier1Input_copy_charge data cb (by simp_all)).2

private def coefficientCall (wide : Bool) (data : ByteArray) (p : CompParams)
    (r : Nat) (b : Band) (cb : CodeBlock) :
    Run (if wide then Array Tier1.WidePlain.Cell else Tier1.CodeBlockOut) :=
  let validity := validateRanges data cb
  if validity.1 then
    let input := gathered data cb
    let (buf,segs) := input.1
    let mb := bandMb p r b + p.roiShift
    let zbp := if cb.included then cb.zeroBitPlanes else 0
    let call : Run (if wide then Array Tier1.WidePlain.Cell else Tier1.CodeBlockOut) := match wide with
      | true => Tier1Work.wideCall buf segs cb.geom.rect.width cb.geom.rect.height b p.cbStyle mb zbp false
      | false => Tier1Work.compactCall buf segs cb.geom.rect.width cb.geom.rect.height b p.cbStyle mb zbp false
    (call.1, validity.2 + (1 + 2 * cb.segments.size + rangeCount cb) + input.2 + call.2)
  else (.error (.malformed Tier1.tier1Loc "code-block data range outside the buffer"),validity.2)

private theorem call_bound {L : Limits} {p : CompParams} (bounds : WideHeaderBounds.ComponentBounds L p)
    (wide : Bool) (data : ByteArray) (r : Nat) (b : Band) (cb : CodeBlock) :
    (coefficientCall wide data p r b cb).2 ≤ scanCost cb + gatherBound data cb + tierBound cb := by
  have ht := Tier1Work.parsed_call_work bounds data r b cb false
  have hc := copy_bound data cb
  have valid : (validateRanges data cb).2 ≤ cb.segments.size + rangeCount cb := (validate_spec ..).2
  have scans : (validateRanges data cb).2 + (1 + 2 * cb.segments.size + rangeCount cb) ≤ scanCost cb := by
    unfold scanCost; omega
  cases wide <;> simp only [coefficientCall, gathered_value] <;> split
  all_goals first | exact Nat.add_le_add (Nat.add_le_add scans hc) ht.2
                  | exact Nat.add_le_add (Nat.add_le_add scans hc) ht.1
                  | dsimp only; omega

private theorem compact_value (data : ByteArray) (p : CompParams) (r : Nat) (b : Band) (cb : CodeBlock) :
    (coefficientCall false data p r b cb).1 = JPEG2000.ReversibleDispatch.checkedBlock data p r b cb := by
  simp only [coefficientCall,JPEG2000.ReversibleDispatch.checkedBlock,(validate_spec ..).1,gathered_value]
  split <;> first | exact Tier1Work.compact_value _ _ _ _ _ _ _ _ false | rfl

private theorem exact_value (data : ByteArray) (p : CompParams) (r : Nat) (b : Band) (cb : CodeBlock) :
    (coefficientCall true data p r b cb).1 = JPEG2000.WideAssembly.decodeBlock data p r b cb := by
  simp only [coefficientCall,JPEG2000.WideAssembly.decodeBlock,(validate_spec ..).1,gathered_value]
  split <;> simp_all only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
  · exact Tier1Work.wide_value ..
  · rfl

/-- Local work for one selected packet record. Includes range validation, direct
descriptor construction or fragmented copying, both Annex D preflight and decoding,
and the row/level/cell work of a successful dequantisation. The pass argument is the
sum in this block's actual gathered segments. -/
def blockBound (data : ByteArray) (nl : Nat) (cb : CodeBlock) :=
  scanCost cb + gatherBound data cb + tierBound cb +
    ((nl+1) + min cb.geom.rect.height 4096 + 3 * min (rectArea cb.geom.rect) 4096)

private def packedStep (data : ByteArray) (tc : TileCompGeom) (depth F reduce : Nat)
    (dst : Plane) (r : Nat) (b : Band) (cb : CodeBlock) : Run (Plane × Bool) :=
  thenRun (coefficientCall false data tc.params r b cb) fun o =>
    compactPlacement dst (Assemble.reduceRect tc.rect reduce) (tc.params.levels-reduce) r b cb.geom.rect
      (Spec.Quant.bandQuant tc.params depth r b) F o

private def exactStep (L : Limits) (data : ByteArray) (tc : TileCompGeom) (depth F reduce : Nat)
    (dst : JPEG2000.WideQuant.Plane) (r : Nat) (b : Band) (cb : CodeBlock) : Run JPEG2000.WideQuant.Plane :=
  thenRun (coefficientCall true data tc.params r b cb) fun cs =>
    widePlacement L dst tc.params depth reduce r b cb.geom.rect F cs

private theorem packed_bound {L : Limits} {tc : TileCompGeom} (bounds : WideHeaderBounds.ComponentBounds L tc.params)
    (data : ByteArray) (depth F reduce : Nat) (dst : Plane) (r : Nat) (b : Band) (cb : CodeBlock) :
    (packedStep data tc depth F reduce dst r b cb).2 ≤ blockBound data (tc.params.levels-reduce) cb := by
  have budget := call_bound bounds false data r b cb
  unfold packedStep thenRun
  split
  · dsimp only; unfold blockBound; omega
  · rename_i o ho
    have accepted := (compact_value data tc.params r b cb).symm.trans ho
    unfold JPEG2000.ReversibleDispatch.checkedBlock at accepted
    split at accepted <;> try contradiction
    unfold Assemble.decodeBlock at accepted
    obtain ⟨area,flags,border⟩ := Tier1Work.compact_buffers _ _ _ _ _ _ _ _ false _ accepted
    have height : cb.geom.rect.height ≤ 4096 := by
      rw [flags] at border; simp only [Nat.add_mul, Nat.mul_add] at border; omega
    unfold blockBound
    change rectArea cb.geom.rect ≤ 4096 at area
    rw [Nat.min_eq_left area,Nat.min_eq_left height]
    exact Nat.add_le_add budget (compact_placement ..).2

private theorem exact_bound {L : Limits} {tc : TileCompGeom} (bounds : WideHeaderBounds.ComponentBounds L tc.params)
    (data : ByteArray) (depth F reduce : Nat) (dst : JPEG2000.WideQuant.Plane) (r : Nat) (b : Band) (cb : CodeBlock) :
    (exactStep L data tc depth F reduce dst r b cb).2 ≤ blockBound data (tc.params.levels-reduce) cb := by
  have budget := call_bound bounds true data r b cb
  unfold exactStep thenRun
  split
  · dsimp only; unfold blockBound; omega
  · rename_i cs hs
    have accepted := (exact_value data tc.params r b cb).symm.trans hs
    unfold JPEG2000.WideAssembly.decodeBlock at accepted
    dsimp only at accepted
    split at accepted <;> try contradiction
    have area : rectArea cb.geom.rect ≤ 4096 := Tier1Work.wide_area _ _ _ _ _ _ _ _ _ _ accepted
    unfold blockBound
    rw [Nat.min_eq_left area]
    apply Nat.add_le_add budget
    unfold widePlacement
    dsimp only
    have H := (origin_levels dst.rect (tc.params.levels-reduce) r).2
    rw [countedHalf_spec] at H
    dsimp only at H
    split <;> split <;> omega

private def after {α β : Type} (x : Run α) (f : α → Except Error β) : Run β :=
  (x.1.bind f, x.2)

private def allocated {α β : Type} (setup : Except Error α) (area : Nat) (f : α → Run β) : Run β :=
  match setup with
  | .error e => (.error e,0)
  | .ok p => let y := f p; (y.1,area + y.2)

private theorem allocated_value {α β : Type} (setup : Except Error α) (area : Nat) (f : α → Run β) :
    (allocated setup area f).1 = setup.bind (fun p => (f p).1) := by cases setup <;> rfl

private theorem allocated_bound {α β : Type} (setup : Except Error α) (area n : Nat) (f : α → Run β)
    (hf : ∀ p, (f p).2 ≤ n) : (allocated setup area f).2 ≤ area+n := by
  cases setup with
  | error e => exact Nat.zero_le _
  | ok p => exact Nat.add_le_add_left (hf p) _

/-- Resolutions of one tile-component, each holding its stored precincts. -/
abbrev Store := Array (Array PrecinctOut)

private def zero (L : Limits) (tc : TileCompGeom) (reduce : Nat) :=
  let rc := Assemble.reduceRect tc.rect reduce
  Plane.zeroChecked L Assemble.loc rc.width rc.height

/-- Cells in one component's checked reduced Mallat plane. -/
def planeArea (tc : TileCompGeom) (reduce : Nat) :=
  rectArea (Assemble.reduceRect tc.rect reduce)

/-- One allocation and one full traversal of the retained topology. Packed zeroing
uses four bytes per cell and wide zeroing uses one integer slot per cell. -/
def attemptBound (data : ByteArray) (tc : TileCompGeom) (reduce : Nat) (ps : Store) (wide : Bool) :=
  let nl := tc.params.levels-reduce
  (if wide then 1 else 4) * planeArea tc reduce + topology nl ps (fun _ _ => blockBound data nl)

private def reversibleStart (L : Limits) (tc : TileCompGeom) (reduce : Nat) : Except Error Plane := do
  if reduce > tc.params.levels then
    throw (.unsupported Assemble.loc
      s!"resolution reduction {reduce} exceeds the {tc.params.levels} decomposition levels of a tile-component")
  zero L tc reduce

private def narrow (L : Limits) (data : ByteArray) (tc : TileCompGeom) (depth F reduce : Nat)
    (ps : Store) : Run (Option Plane × Nat) :=
  let nl := tc.params.levels-reduce
  allocated (reversibleStart L tc reduce) (4 * planeArea tc reduce) fun p =>
    after (walk nl ps (p,0) fun (dst,sat) r b cb =>
      after (packedStep data tc depth F reduce dst r b cb) fun (pl,ok) =>
        .ok (pl, if ok then sat else sat+1)) fun (pl,sat) =>
      .ok (if sat = 0 then JPEG2000.DWT53.idwt53Fast pl (Assemble.reduceRect tc.rect reduce) nl else none,sat)

private def bands (L : Limits) (data : ByteArray) (tc : TileCompGeom) (depth F reduce : Nat)
    (ps : Store) : Run Plane :=
  let setup := do
    L.check Assemble.loc .decompLevels (max reduce tc.params.levels)
    zero L tc reduce
  allocated setup (4 * planeArea tc reduce) fun p =>
    walk (tc.params.levels-reduce) ps p fun dst r b cb =>
      after (packedStep data tc depth F reduce dst r b cb) fun (pl,ok) =>
        if ok then .ok pl else .error (.unsupported Assemble.loc "dequantised coefficient exceeds compact precision")

private def wideBands (L : Limits) (data : ByteArray) (tc : TileCompGeom) (depth F reduce : Nat)
    (ps : Store) : Run JPEG2000.WideQuant.Plane :=
  let setup := do
    if reduce > tc.params.levels then
      throw (.unsupported Assemble.loc
        s!"resolution reduction {reduce} exceeds the {tc.params.levels} decomposition levels of a tile-component")
    L.check Assemble.loc .decompLevels tc.params.levels
    L.check Assemble.loc .workSamples (planeArea tc reduce)
    JPEG2000.WideQuant.zeroChecked L (Assemble.reduceRect tc.rect reduce)
  allocated setup (planeArea tc reduce) fun p =>
    walk (tc.params.levels-reduce) ps p (exactStep L data tc depth F reduce)

private theorem seq_assoc {α β γ : Type} (v : Except Error α) (f : α → Except Error β) (g : β → Except Error γ) :
    (v.bind f).bind g = v.bind (fun x => (f x).bind g) := by cases v <;> rfl

private theorem wideBands_value (L : Limits) (data : ByteArray) (tc : TileCompGeom) (d F red : Nat) (ps : Store) :
    (wideBands L data tc d F red ps).1 = JPEG2000.WideAssembly.tileComp L data tc d F red ps := by
  simp only [wideBands, allocated_value, walk_value, exactStep, then_value, exact_value,
    widePlacement, JPEG2000.WideAssembly.tileComp, planeArea, bind]
  split <;> simp only [seq_assoc] <;> rfl

private theorem narrow_value (L : Limits) (data : ByteArray) (tc : TileCompGeom) (d F red : Nat) (ps : Store) :
    (narrow L data tc d F red ps).1 = JPEG2000.ReversibleDispatch.narrow L data tc d F red ps := by
  simp only [narrow, allocated_value, walk_value, after, packedStep, then_value,
    compact_value, (compact_placement ..).1, reversibleStart, zero, JPEG2000.ReversibleDispatch.narrow,
    bind, seq_assoc]
  split <;> rfl

private theorem bands_value (L : Limits) (data : ByteArray) (tc : TileCompGeom) (d F red : Nat) (ps : Store) :
    (bands L data tc d F red ps).1 = JPEG2000.IrreversibleDispatch.compactBands L data tc d F red ps := by
  simp only [bands, allocated_value, walk_value, after, packedStep, then_value, compact_value,
    (compact_placement ..).1, zero, JPEG2000.IrreversibleDispatch.compactBands, bind, seq_assoc]
  congr 1
  funext u
  congr 1
  funext dst
  congr 1
  funext a r b cb
  unfold JPEG2000.ReversibleDispatch.checkedBlock
  split <;> simp_all only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte] <;> rfl

private theorem narrow_bound {L : Limits} (data : ByteArray) {tc : TileCompGeom}
    (h : WideHeaderBounds.ComponentBounds L tc.params) (d F red : Nat) (ps : Store) :
    (narrow L data tc d F red ps).2 ≤ attemptBound data tc red ps false := by
  apply allocated_bound
  intro p
  dsimp only [after]
  apply walk_bound
  intro a r b cb
  exact packed_bound h ..

private theorem bands_bound {L : Limits} (data : ByteArray) {tc : TileCompGeom}
    (h : WideHeaderBounds.ComponentBounds L tc.params) (d F red : Nat) (ps : Store) :
    (bands L data tc d F red ps).2 ≤ attemptBound data tc red ps false := by
  apply allocated_bound
  intro p
  exact walk_bound _ _ _ _ _ (fun _ _ _ _ => packed_bound h ..)

private theorem wideBands_bound {L : Limits} (data : ByteArray) {tc : TileCompGeom}
    (h : WideHeaderBounds.ComponentBounds L tc.params) (d F red : Nat) (ps : Store) :
    (wideBands L data tc d F red ps).2 ≤ attemptBound data tc red ps true := by
  unfold attemptBound
  simp only [↓reduceIte, Nat.one_mul]
  apply allocated_bound
  intro p
  exact walk_bound _ _ _ _ _ (fun _ _ _ _ => exact_bound h ..)

private def retry {α : Type} (first : Option α × Nat) (fallback : Unit → Run α) : Run α :=
  match first.1 with
  | some a => (.ok a,first.2)
  | none => let y := fallback (); (y.1,first.2 + y.2)

private theorem retry_value {α : Type} (first : Option α × Nat) (fallback : Unit → Run α) :
    (retry first fallback).1 = (match first.1 with
      | some a => .ok a | none => (fallback ()).1) := by
  unfold retry; split <;> rfl

private theorem retry_bound {α : Type} {first : Option α × Nat} {fallback : Unit → Run α}
    {m n : Nat} (h : first.2 ≤ m) (k : (fallback ()).2 ≤ n) :
    (retry first fallback).2 ≤ m + (if first.1.isSome then 0 else n) := by
  unfold retry
  split <;> simp_all <;> omega

private def firstRev (L : Limits) (data : ByteArray) (tc : TileCompGeom) (d F red : Nat) (ps : Store) :
    Option JPEG2000.NativeOutput.Source × Nat :=
  let rc := Assemble.reduceRect tc.rect red
  if (red ≤ tc.params.levels && tc.params.levels ≤ L.maxDecompLevels) &&
      (rc.x0 ≤ rc.x1 && rc.y0 ≤ rc.y1) then
    let x := narrow L data tc d F red ps
    ((x.1.toOption.bind (·.1)).map JPEG2000.NativeOutput.Source.plane,x.2)
  else (none,0)

/-- The reversible dispatcher's coefficient work. A lifting miss triggers the same
second traversal as a coefficient miss. The transform itself receives zero assembly charge. -/
def reversible (L : Limits) (data : ByteArray) (tc : TileCompGeom) (d F red : Nat) (ps : Store) :
    Except Error JPEG2000.NativeOutput.Source × Nat :=
  if tc.params.transform != .reversible53 then
    (.error (.malformed Assemble.loc "expected a reversible tile-component"),0)
  else retry (firstRev L data tc d F red ps) fun _ =>
    after (wideBands L data tc d F red ps) fun p =>
      JPEG2000.ReversibleDispatch.wideSource L p (tc.params.levels-red)

private theorem firstRev_value (L : Limits) (data : ByteArray) (tc : TileCompGeom) (d F red : Nat) (ps : Store) :
    (firstRev L data tc d F red ps).1 =
      (JPEG2000.ReversibleDispatch.compactPlane? L data tc d F red ps).map JPEG2000.NativeOutput.Source.plane := by
  unfold firstRev JPEG2000.ReversibleDispatch.compactPlane?
  dsimp only
  cases a : (decide (red ≤ tc.params.levels) && decide (tc.params.levels ≤ L.maxDecompLevels)) <;>
    cases b : (decide ((Assemble.reduceRect tc.rect red).x0 ≤ (Assemble.reduceRect tc.rect red).x1) &&
      decide ((Assemble.reduceRect tc.rect red).y0 ≤ (Assemble.reduceRect tc.rect red).y1)) <;>
    simp only [Bool.false_and, Bool.true_and, Bool.false_eq_true, ↓reduceIte, narrow_value] <;> rfl

/-- The first projection reproduces reversible dispatch on both continuations. The upper
bound drops the wide traversal whenever the compact plane survives lifting. -/
theorem reversible_work {L : Limits} (data : ByteArray) {tc : TileCompGeom}
    (h : WideHeaderBounds.ComponentBounds L tc.params) (d F red : Nat) (ps : Store) :
    let x := reversible L data tc d F red ps
    x.1 = JPEG2000.ReversibleDispatch.tileComp L data tc d F red ps ∧
    x.2 ≤ attemptBound data tc red ps false +
      (if (JPEG2000.ReversibleDispatch.compactPlane? L data tc d F red ps).isSome then 0
       else attemptBound data tc red ps true) := by
  dsimp only
  unfold reversible JPEG2000.ReversibleDispatch.tileComp
  split
  · exact ⟨rfl,Nat.zero_le _⟩
  · have hb : (firstRev L data tc d F red ps).2 ≤ attemptBound data tc red ps false := by
      unfold firstRev; dsimp only; split
      · exact narrow_bound data h ..
      · exact Nat.zero_le _
    constructor
    · rw [retry_value, firstRev_value]
      simp only [after, wideBands_value]
      cases JPEG2000.ReversibleDispatch.compactPlane? L data tc d F red ps <;> rfl
    · apply Nat.le_trans (retry_bound hb (wideBands_bound data h d F red ps))
      rw [firstRev_value, Option.isSome_map]
      exact Nat.le_refl _

private def firstIrrev (L : Limits) (data : ByteArray) (tc : TileCompGeom) (d F red : Nat) (ps : Store)
    (allow : Bool) : Option JPEG2000.IrreversibleDispatch.Spatial × Nat :=
  if allow then
    let x := bands L data tc d F red ps
    (x.1.toOption.bind (fun p => JPEG2000.IrreversibleDispatch.compactSpatial p
      (Assemble.reduceRect tc.rect red) (tc.params.levels-red) F), x.2)
  else (none,0)

/-- Coefficient meter for irreversible dispatch, including direct-wide selection. -/
def irreversible (L : Limits) (data : ByteArray) (tc : TileCompGeom) (d F red : Nat) (ps : Store)
    (allow : Bool) : Except Error JPEG2000.IrreversibleDispatch.Spatial × Nat :=
  let admission : Except Error Unit := do
    if tc.params.transform != .irreversible97 then
      throw (.unsupported Assemble.loc "irreversible reconstruction requires the 9/7 transform")
    if red > tc.params.levels then
      throw (.unsupported Assemble.loc "resolution reduction exceeds tile-component levels")
    L.check Assemble.loc .decompLevels tc.params.levels
    let rc := Assemble.reduceRect tc.rect red
    if rc.x1 < rc.x0 ∨ rc.y1 < rc.y0 then throw (.malformed Assemble.loc "inverted component rectangle")
  allocated admission 0 fun _ =>
    retry (firstIrrev L data tc d F red ps allow) fun _ =>
      after (wideBands L data tc d F red ps) fun bands => do
        let q ← JPEG2000.WideDWT97.idwt97 L bands (tc.params.levels-red)
        return .wide ⟨q,F⟩

private theorem firstIrrev_value (L : Limits) (data : ByteArray) (tc : TileCompGeom) (d F red : Nat) (ps : Store)
    (allow : Bool) :
    (if allow then JPEG2000.IrreversibleDispatch.tryCompact L data tc d F red ps else pure none) =
      .ok (firstIrrev L data tc d F red ps allow).1 := by
  cases allow <;> simp only [firstIrrev, Bool.false_eq_true, ↓reduceIte, bands_value, JPEG2000.IrreversibleDispatch.tryCompact]
  · rfl
  · cases JPEG2000.IrreversibleDispatch.compactBands L data tc d F red ps <;> rfl

/-- On both success and rejection, the irreversible dispatcher charges only attempted
paths. Turning off compact decoding drops its complete charge. -/
theorem irreversible_work {L : Limits} (data : ByteArray) {tc : TileCompGeom}
    (h : WideHeaderBounds.ComponentBounds L tc.params) (d F red : Nat) (ps : Store) (allow : Bool) :
    let first := if allow then JPEG2000.IrreversibleDispatch.tryCompact L data tc d F red ps else pure none
    let x := irreversible L data tc d F red ps allow
    x.1 = JPEG2000.IrreversibleDispatch.component L data tc d F red ps allow ∧
    x.2 ≤ (if allow then attemptBound data tc red ps false else 0) +
      (if first.toOption.join.isSome then 0 else attemptBound data tc red ps true) := by
  dsimp only
  rw [firstIrrev_value]
  constructor
  · unfold irreversible JPEG2000.IrreversibleDispatch.component
    rw [allocated_value]
    simp only [retry_value, firstIrrev_value, after, wideBands_value, bind]
    split <;> try rfl
    split <;> try rfl
    rw [seq_assoc]
    congr 1
    funext u
    split <;> try rfl
    cases (firstIrrev L data tc d F red ps allow).1 <;> rfl
  · unfold irreversible
    rw [← Nat.zero_add ((if allow then attemptBound data tc red ps false else 0) + _)]
    apply allocated_bound
    intro u
    apply retry_bound _ (wideBands_bound data h d F red ps)
    unfold firstIrrev; split <;> first | exact bands_bound data h .. | exact Nat.le_refl _

/-- The original component's packet store, empty for an omitted tile. -/
def selected (store : Option TileCodeBlocks) (i : Nat) : Store :=
  (store.map (·.comps.getD i #[])).getD #[]

/-- Meter the component at the public tile dispatcher's actual depth, fractional
precision, kernel and packet selection, including the absent-tile case. -/
def component (L : Limits) (h : Header.Header) (data : ByteArray) (g : Progression.Layout)
    (coding : Coding) (store : Option TileCodeBlocks) (i : Fin g.numComps) (red : Nat) :
    Except Error JPEG2000.TileDispatch.Spatial × Nat :=
  let tc := g.comp i
  let ps := selected store i
  let d := (h.siz.components.getD i default).depth.toNat
  let F := Assemble.fracBitsOf h.siz (coding.mctApplies h.siz) i
  match tc.params.transform with
  | .reversible53 =>
    let x := reversible L data tc d F red ps
    (JPEG2000.TileDispatch.Spatial.rev <$> x.1, x.2)
  | .irreversible97 =>
    let x := irreversible L data tc d F red ps true
    (JPEG2000.TileDispatch.Spatial.irrev <$> x.1, x.2)

/-- Uniform bound for a selected component. The first traversal may be a proper
prefix; the second restarts at the beginning of the same packet store. -/
theorem parsed_component_work {L : Limits} {data : ByteArray} {h : Header.Header}
    {t : Nat} {g : Progression.Layout} {coding : Coding} (parsed : Header.parse L data = .ok h)
    (layout : Progression.Layout.ofHeader h t = .ok (g,coding)) (store : Option TileCodeBlocks)
    (i : Fin g.numComps) (red : Nat) :
    let tc := g.comp i
    let nl := tc.params.levels-red
    let x := component L h data g coding store i red
    x.1 = JPEG2000.TileDispatch.component L h data g coding store i red ∧
    x.2 ≤ 5 * rectArea (Assemble.reduceRect tc.rect red) +
      2 * topology nl (selected store i) (fun _ _ => blockBound data nl) := by
  dsimp only
  have bounds := (WideHeaderBounds.parsed_component_bounds parsed layout i red).1
  simp only [component, JPEG2000.TileDispatch.component]
  cases tr : (g.comp i).params.transform <;> dsimp only
  case reversible53 =>
    have H := reversible_work data bounds (h.siz.components.getD i default).depth.toNat
      (Assemble.fracBitsOf h.siz (coding.mctApplies h.siz) i) red (selected store i)
    constructor
    · rw [H.1]; cases store <;> rfl
    · have hw := H.2
      simp only [attemptBound, planeArea, Bool.false_eq_true, ↓reduceIte, Nat.one_mul] at hw
      split at hw <;> omega
  case irreversible97 =>
    have H := irreversible_work data bounds (h.siz.components.getD i default).depth.toNat
      (Assemble.fracBitsOf h.siz (coding.mctApplies h.siz) i) red (selected store i) true
    constructor
    · rw [H.1]; rfl
    · have hw := H.2
      simp only [attemptBound, planeArea, Bool.false_eq_true, ↓reduceIte, Nat.one_mul] at hw
      split at hw <;> omega

private theorem area_le_tile (g : Progression.Layout) (i : Fin g.numComps) (red : Nat) :
    planeArea (g.comp i) red ≤ Resources.tileCells g red := by
  have member : g.comp i ∈ g.comps := by
    simp only [Progression.Layout.comp, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem i.isLt,
      Option.getD_some]
    exact Array.getElem_mem _
  have h := List.mem_map_of_mem (f := fun tc => planeArea tc red) (Array.mem_toList_iff.mpr member)
  change _ ≤ (g.comps.toList.map (fun tc => planeArea tc red)).sum
  generalize g.comps.toList.map (fun tc => planeArea tc red) = xs at h ⊢
  induction xs with
  | nil => cases h
  | cons x xs ih =>
    simp only [List.mem_cons] at h
    simp only [List.sum_cons]
    rcases h with eq | rest
    · omega
    · exact Nat.le_add_left_of_le (ih rest)

/-- Native layout admission covers an assembly that later rejects. If admission
itself fails, the public tile entry point returns the exact aggregate excess before
the first component. -/
theorem native_budget {L : Limits} {data : ByteArray} {h : Header.Header} {t : Nat}
    {g : Progression.Layout} {coding : Coding} (parsed : Header.parse L data = .ok h)
    (layout : Progression.Layout.ofHeader h t = .ok (g,coding)) (store : Option TileCodeBlocks)
    (i : Fin g.numComps) (red : Nat) :
    let tc := g.comp i
    let nl := tc.params.levels-red
    if Resources.tileCells g red ≤ L.maxWorkSamples then
      planeArea tc red ≤ L.maxWorkSamples ∧
      (component L h data g coding store i red).2 ≤ 5*L.maxWorkSamples +
        2 * topology nl (selected store i) (fun _ _ => blockBound data nl)
    else JPEG2000.Decode.centeredTile L h data red t store = .error
      (.limitExceeded Assemble.loc .workSamples (Resources.tileCells g red) L.maxWorkSamples) := by
  dsimp only
  split
  · rename_i ha
    have cells := Nat.le_trans (area_le_tile g i red) ha
    exact ⟨cells, Nat.le_trans (parsed_component_work parsed layout store i red).2
      (Nat.add_le_add_right (Nat.mul_le_mul_left 5 cells) _)⟩
  · exact NativeResources.centeredTile_limitExceeded layout (by omega)

/-- Actual per-block temporary storage handed to dequantisation. Direct descriptors
borrow the input; fragmented buffers are bounded by range count times input length.
Packed blocks expose two bordered work arrays during decoding and a four-byte raster.
Wide Tier-1 returns at most 4096 signed-magnitude cells. -/
theorem block_storage {L : Limits} {p : CompParams} (bounds : WideHeaderBounds.ComponentBounds L p)
    (data : ByteArray) (r : Nat) (b : Band) (cb : CodeBlock) :
    let input := Assemble.tier1Input data cb
    input.2.size = cb.segments.size ∧ input.1.size ≤ max 1 (rangeCount cb) * data.size ∧
    (∀ o, JPEG2000.ReversibleDispatch.checkedBlock data p r b cb = .ok o →
      o.plane.data.size = 4 * rectArea cb.geom.rect ∧ o.flags.size =
        (cb.geom.rect.width+2) * (cb.geom.rect.height+2) ∧ o.flags.size ≤ 8196 ∧ rectArea cb.geom.rect ≤ 4096) ∧
    (∀ cs, JPEG2000.WideAssembly.decodeBlock data p r b cb = .ok cs →
      cs.size = rectArea cb.geom.rect ∧ cs.size ≤ 4096 ∧
      ∀ c ∈ cs, c.mag < 2^292 ∧ c.lsbPlane ≤ 291 ∧ c.value.natAbs < 2^292) := by
  obtain ⟨sz,bytes⟩ := HeaderWork.tier1Input_storage data cb
  refine ⟨sz, ?_, ?_, ?_⟩
  · split at bytes
    · rw [bytes]
      exact Nat.le_trans (Nat.le_of_eq (Nat.one_mul data.size).symm) (Nat.mul_le_mul_right _ (Nat.le_max_left ..))
    · exact Nat.le_trans bytes.2 (Nat.mul_le_mul_right _ (Nat.le_max_right ..))
  · intro o ok
    unfold JPEG2000.ReversibleDispatch.checkedBlock at ok
    split at ok <;> try contradiction
    unfold Assemble.decodeBlock at ok
    obtain ⟨area, flags, bounded⟩ := Tier1Work.compact_buffers _ _ _ _ _ _ _ _ false _ ok
    exact ⟨(Tier1Work.compact_cells _ _ _ _ _ _ _ _ false _ ok).2.2.1,flags,bounded,area⟩
  · intro cs ok
    obtain ⟨sz,mag⟩ := Tier1Work.parsed_cells bounds data r b cb cs ok
    refine ⟨sz,sz ▸ ?_,mag⟩
    unfold JPEG2000.WideAssembly.decodeBlock at ok
    dsimp only at ok
    split at ok <;> try contradiction
    exact Tier1Work.wide_area _ _ _ _ _ _ _ _ _ _ ok

/-- Every integer written to a parsed wide Mallat plane has absolute value at most
`2^372`. This discharges the Tier-1 premise using the actual successful block. -/
theorem mallat_width {L : Limits} {data : ByteArray} {h : Header.Header} {t : Nat}
    {g : Progression.Layout} {coding : Coding} (parsed : Header.parse L data = .ok h)
    (layout : Progression.Layout.ofHeader h t = .ok (g,coding)) (i : Fin g.numComps)
    (red : Nat) (ps : Store) {out : JPEG2000.WideQuant.Plane}
    (ok : JPEG2000.WideAssembly.tileComp L data (g.comp i) (h.siz.components.getD i default).depth.toNat
      (Assemble.fracBitsOf h.siz (coding.mctApplies h.siz) i) red ps = .ok out) :
    WideArithmetic.RasterFits 372 out.samples.toArray := by
  apply WideArithmetic.tile_coefficients _ ok
  intro r b cb cs decoded c hc
  obtain ⟨hm,hl,_⟩ := (Tier1Work.parsed_cells (WideHeaderBounds.parsed_component_bounds parsed layout i red).1
    _ _ _ _ _ decoded).2 c hc
  obtain ⟨_,_,terms,cap⟩ := WideArithmetic.parsed_quant parsed layout i r b c hm hl
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,value⟩ := terms
  exact Nat.le_trans value cap

private theorem rows_shape (f : Int32 → Nat → Int32 × Bool) (o : Tier1.CodeBlockOut)
    (px py n y : Nat) (dst : Plane) (ok : Bool) :
    (JPEG2000.Quant.blockRows f o px py n y dst ok).1.width = dst.width ∧
    (JPEG2000.Quant.blockRows f o px py n y dst ok).1.height = dst.height := by
  induction n generalizing dst ok y with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih =>
    simp only [JPEG2000.Quant.blockRows]
    have h := QuantBlock.blockRow_spec f o y o.plane.width 0 ((py+y)*dst.width+px) dst ok
    exact ⟨(ih ..).1.trans h.1,(ih ..).2.trans h.2.1⟩

/-- Every completed packed placement keeps exactly the original Mallat allocation
shape, also when saturation is detected. The byte count prices the actual backing. -/
theorem packed_storage {dst out : Plane} {rc cb : Rect} {nl r F : Nat} {b : Band}
    {q : Spec.Quant.BandQuant} {o : Tier1.CodeBlockOut} {fits : Bool}
    (ok : JPEG2000.Quant.dequantBlock dst rc nl r b cb q F o = .ok (out,fits)) :
    out.width = dst.width ∧ out.height = dst.height ∧ out.data.size = 4 * rectArea rc := by
  unfold JPEG2000.Quant.dequantBlock at ok
  dsimp only at ok
  repeat' (split at ok <;> try contradiction)
  all_goals
    have wh := congrArg (fun z : Plane × Bool => (z.1.width,z.1.height)) (Except.ok.inj ok)
    simp only [(rows_shape ..).1,(rows_shape ..).2] at wh
    have hw := congrArg Prod.fst wh
    have hh := congrArg Prod.snd wh
    dsimp only at hw hh
    refine ⟨hw.symm,hh.symm,?_⟩
    rw [out.size_eq, ← hw, ← hh, rectArea]
    congr 2 <;> first | change _ = rc.x1-rc.x0; omega | change _ = rc.y1-rc.y0; omega

/-- Every wide write preserves the rectangle and vector length of its incoming
plane. This applies to every successful prefix before a subsequent error. -/
theorem wide_storage {L : Limits} {dst out : JPEG2000.WideQuant.Plane} {p : CompParams}
    {d red r F : Nat} {b : Band} {cb : Rect} {cs : Array Tier1.WidePlain.Cell}
    (ok : JPEG2000.WideQuant.dequantBlock L dst p d red r b cb F cs = .ok out) :
    out.rect = dst.rect ∧ out.samples.toArray.size = rectArea dst.rect := by
  have e := (WideQuant.dequantBlock_read ok).1
  exact ⟨e, out.samples.size_toArray.trans (congrArg rectArea e)⟩

/-- Across the components of a successful native tile the hypothetical two full
sets of zero buffers need at most four packed bytes and one wide integer slot per
admitted cell. This also bounds the cumulative zeroing of actual retries. -/
theorem native_plane_cells {L : Limits} {h : Header.Header} {data : ByteArray} {r t : Nat}
    {store : Option TileCodeBlocks} {out : JPEG2000.Decode.CenteredTile}
    (ok : JPEG2000.Decode.centeredTile L h data r t store = .ok out) :
    (out.layout.comps.toList.map (fun tc => 4 * planeArea tc r)).sum ≤ 4 * L.maxWorkSamples ∧
    (out.layout.comps.toList.map (fun tc => planeArea tc r)).sum ≤ L.maxWorkSamples := by
  have cells := (NativeResources.centeredTile_work ok).2
  refine ⟨?_,cells⟩
  have eq (xs : List TileCompGeom) : (xs.map (fun tc => 4 * planeArea tc r)).sum =
      4 * (xs.map (fun tc => planeArea tc r)).sum := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simp only [List.map_cons,List.sum_cons,ih,Nat.mul_add]
  rw [eq]
  exact Nat.mul_le_mul_left 4 cells

/-- Allocation domains at the actual gathered Tier-1 preflight, before scanning a
coefficient. Both bordered packed arrays together need at most 16392 slots. Each
wide coefficient array needs at most 4096 slots. The retained descriptors fit the
original segment count even when the block body subsequently rejects. -/
theorem block_workspace (wide : Bool) (data : ByteArray) (p : CompParams) (r : Nat)
    (b : Band) (cb : CodeBlock) (kept : Array Tier1.Seg)
    (ok : let input := Assemble.tier1Input data cb
          (Tier1Work.preflight wide input.1 input.2 cb.geom.rect.width cb.geom.rect.height
            (Tier1.Style.ofByte p.cbStyle) ((bandMb p r b + p.roiShift) -
              (if cb.included then cb.zeroBitPlanes else 0))).1 = .ok kept) :
    kept.size ≤ cb.segments.size ∧ Tier1.segsPasses kept ≤ (if wide then 874 else 91) ∧
    rectArea cb.geom.rect ≤ 4096 ∧
    2 * ((cb.geom.rect.width + 2) * (cb.geom.rect.height + 2)) ≤ 16392 := by
  obtain ⟨_,sz,_,passes,area,border⟩ := Tier1Work.preflight_domains ok
  exact ⟨Nat.le_trans sz (Nat.le_of_eq (HeaderWork.tier1Input_storage data cb).1),passes,area,by omega⟩

/-- A coarse local bound using just input length, retained levels, segment count
and range count. It charges at most 874 effective passes for this invocation, and
the enclosing traversal can select the same record again only on a wide retry. -/
theorem block_ceiling (data : ByteArray) (nl : Nat) (cb : CodeBlock) :
    let s := cb.segments.size
    let k := rangeCount cb
    blockBound data nl cb ≤ 1 + 3*s + 2*k + (2*k+s)*(k*data.size) +
      (26006 + 8510*s + 66002*874) + (nl+1 + 4096 + 3*4096) := by
  simp only [blockBound,scanCost,gatherBound,tierBound]
  omega

private def total {α : Type} (xs : List α) (f : α → Nat) := (xs.map f).sum

private theorem visitSum_split {α : Type} (xs : List α) (f g k : α → Nat)
    (eq : ∀ x, f x = g x + k x) :
    visitSum xs f = visitSum xs g + total xs k := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change 1 + f x + visitSum xs f = 1 + g x + visitSum xs g + (k x + total xs k)
    rw [eq,ih]; omega

/-- Sum a quantity over just the retained nonempty blocks with nonzero pass
counts. Set the weight to one to count potential coefficient calls per attempt. -/
def selectedSum (nl : Nat) (ps : Store) (weight : Nat → Band → CodeBlock → Nat) :=
  total (List.range' 0 (min (nl+1) ps.size)) fun r =>
    total (ps.getD r #[]).toList fun pr =>
      total pr.bands.toList fun bo =>
        total bo.blocks.toList fun cb => if active cb then weight r bo.band cb else 0

/-- Separate the traversal overhead on every record (including skips) from
the budget for coefficient calls on selected records. A short-circuited failure
can use only a prefix of these charges. -/
theorem topology_split (nl : Nat) (ps : Store) (w : Nat → Band → CodeBlock → Nat) :
    topology nl ps w = topology nl ps (fun _ _ _ => 0) + selectedSum nl ps w := by
  apply visitSum_split; intro r
  apply visitSum_split; intro pr
  apply visitSum_split; intro bo
  apply visitSum_split; intro cb
  split <;> simp


/-- Upper bound for one block when its history contains at most `s` segments and
`k` translated byte ranges. The gather term charges both levels of byte append. -/
def blockBudget (n nl s k : Nat) : Nat :=
  1 + 3*s + 2*k + (2*k+s)*(k*n) +
    (26006 + 8510*s + 66002*874) + (nl+1 + 4096 + 3*4096)

/-- Packet-store bounds consumed by reconstruction: precincts per resolution,
bands per precinct, blocks per band, and segment and range counts per block. -/
def StoreBounds (ps : Store) (P B C S K : Nat) : Prop :=
  ∀ r, (ps.getD r #[]).size ≤ P ∧ ∀ p ∈ ps.getD r #[],
    p.bands.size ≤ B ∧ ∀ b ∈ p.bands, b.blocks.size ≤ C ∧
      ∀ cb ∈ b.blocks, cb.segments.size ≤ S ∧ rangeCount cb ≤ K

private theorem visitSum_le {α : Type} (xs : List α) (w : α → Nat) (cap : Nat)
    (h : ∀ x ∈ xs, w x ≤ cap) : visitSum xs w ≤ xs.length * (1+cap) := by
  induction xs with
  | nil => simp [visitSum]
  | cons x xs ih =>
    have one := h x (by simp)
    have rest := ih (fun a ha => h a (by simp [ha]))
    change 1 + w x + visitSum xs w ≤ (xs.length+1)*(1+cap)
    rw [Nat.add_mul, Nat.one_mul]
    omega

private theorem arrayVisits {α : Type} (xs : Array α) (w : α → Nat) (n cap : Nat)
    (size : xs.size ≤ n) (h : ∀ x ∈ xs, w x ≤ cap) :
    visitSum xs.toList w ≤ n*(1+cap) := by
  apply Nat.le_trans (visitSum_le _ _ cap (by simpa using h))
  simpa using Nat.mul_le_mul_right (1+cap) size

/-- Work of a full assembly traversal from numeric bounds on the selected packet
store. Empty and skipped entries still pay for their visits. -/
theorem topology_budget (data : ByteArray) (nl : Nat) (ps : Store) (P B C S K : Nat)
    (store : StoreBounds ps P B C S K) :
    topology nl ps (fun _ _ => blockBound data nl) ≤
      (nl+1) * (1 + P*(1 + B*(1 + C*(1 + blockBudget data.size nl S K)))) := by
  unfold topology
  apply Nat.le_trans (visitSum_le _ _ _ ?_)
  · apply Nat.mul_le_mul_right
    simpa only [List.length_range'] using Nat.min_le_left (nl+1) ps.size
  intro r _
  obtain ⟨plen,precs⟩ := store r
  apply arrayVisits _ _ P _ plen
  intro p hp
  obtain ⟨blen,bands⟩ := precs p hp
  apply arrayVisits _ _ B _ blen
  intro b hb
  obtain ⟨clen,blocks⟩ := bands b hb
  apply arrayVisits _ _ C _ clen
  intro cb hc
  split
  · obtain ⟨hs,hk⟩ := blocks cb hc
    apply Nat.le_trans (block_ceiling data nl cb)
    unfold blockBudget
    have copy := Nat.mul_le_mul (show 2*rangeCount cb+cb.segments.size ≤ 2*K+S by omega)
      (Nat.mul_le_mul_right data.size hk)
    omega
  · exact Nat.zero_le _

/-- The ordinary tile component dispatcher preserves its exact outcome and has
an explicit assembly-work bound once packet history supplies the five counts. -/
theorem component_budget {L : Limits} {data : ByteArray} {h : Header.Header} {t : Nat}
    {g : Progression.Layout} {coding : Coding} (parsed : Header.parse L data = .ok h)
    (layout : Progression.Layout.ofHeader h t = .ok (g,coding)) (a : Option TileCodeBlocks)
    (i : Fin g.numComps) (red P B C S K : Nat) (store : StoreBounds (selected a i) P B C S K)
    (admitted : Resources.tileCells g red ≤ L.maxWorkSamples) :
    let nl := (g.comp i).params.levels-red
    let run := component L h data g coding a i red
    run.1 = JPEG2000.TileDispatch.component L h data g coding a i red ∧ run.2 ≤
      5*L.maxWorkSamples + 2*((nl+1) * (1 + P*(1 + B*(1 + C*(1 + blockBudget data.size nl S K))))) := by
  obtain ⟨erases,_⟩ := parsed_component_work parsed layout a i red
  have initial := native_budget parsed layout a i red
  simp only [admitted, ↓reduceIte] at initial
  exact ⟨erases, Nat.le_trans initial.2 (Nat.add_le_add_left
    (Nat.mul_le_mul_left 2 (topology_budget _ _ _ _ _ _ _ _ store)) _)⟩

end JPEG2000.Spec.Resources.AssemblyCost
