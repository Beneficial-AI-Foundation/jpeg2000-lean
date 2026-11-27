import JPEG2000.Tier1.WidePlain
import Spec.Tier1Equiv.Clamp

/-!
# Wide plain-mode Tier-1 equivalence (Plan.md §§4, 5.1, 5.4; T.800 Annex D)

The simulation relates the production MQ registers to Annex C and the entire wide raster
to Annex D after every step. It preserves magnitude, sign, last coded plane and the flags
used by later decisions. The block comparison covers MQ restarts,
clamping and the independent spec's segment-structure validation.
-/

namespace JPEG2000.Spec.Tier1Wide

open JPEG2000.Tier2.Geometry (Band)
open Tier1Equiv (sgeom specBlock)
open Spec.Tier1 (Coeff Geom DecState)
open JPEG2000.Tier1

/-- Field-for-field representation of an Annex D coefficient in the wide raster. -/
def cellOf (c : Coeff) : WidePlain.Cell :=
  ⟨c.mag, c.sign, c.lsbPlane, c.sig, c.visited, c.refined⟩

/-- Reading the production signed value recovers the exact Annex D quantisation index. -/
theorem cellOf_value (c : Coeff) : (cellOf c).value = c.value := rfl

private structure Sim (start : Nat) (s : WidePlain.State) (d : DecState) : Prop where
  mq : MQEquiv.Rel start s.mq d.mq d.cxs
  cells : s.cells = d.coeffs.map cellOf

private theorem read_map (w h : Nat) (b : Band) (cs : Array Coeff) (x y : Int) :
    WidePlain.readCell w h (cs.map cellOf) x y = cellOf ((sgeom w h b).coeffAt cs x y) := by
  unfold WidePlain.readCell Geom.coeffAt
  simp only [sgeom, Geom.idx]
  split <;> simp only [*, ↓reduceIte]
  · simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
    cases cs[y.toNat * w + x.toNat]? <;> rfl
  · rfl

private theorem counts_map (w h : Nat) (b : Band) (cs : Array Coeff) (x y : Nat) :
    WidePlain.counts w h (cs.map cellOf) x y = (sgeom w h b).sigCounts cs x y := by
  simp only [WidePlain.counts, read_map w h b, cellOf, Geom.sigCounts, Geom.nbSig,
    Tier1Equiv.nbAt_sgeom, show ∀ v : Bool, v.toNat = (if v then 1 else 0) by intro v; cases v <;> rfl]

private theorem zero_map (w h : Nat) (b : Band) (cs : Array Coeff) (x y : Nat) :
    WidePlain.zeroContext b (WidePlain.counts w h (cs.map cellOf) x y) = (sgeom w h b).zcCtx cs x y := by
  rw [counts_map w h b]
  unfold Geom.zcCtx
  generalize (sgeom w h b).sigCounts cs x y = n
  obtain ⟨a, v, d⟩ := n
  have ll (a v d : Nat) : JPEG2000.Tier1.zcLLLH a v d = Spec.Tier1.zcTableLLLH a v d := by
    rcases a with _ | ⟨_ | a⟩ <;> rcases v with _ | ⟨_ | v⟩ <;> rcases d with _ | ⟨_ | d⟩ <;>
      simp [JPEG2000.Tier1.zcLLLH, Spec.Tier1.zcTableLLLH]
  have hh (a d : Nat) : JPEG2000.Tier1.zcHHcol a d = Spec.Tier1.zcTableHH a d := by
    rcases a with _ | ⟨_ | a⟩ <;> rcases d with _ | ⟨_ | ⟨_ | d⟩⟩ <;>
      simp [JPEG2000.Tier1.zcHHcol, Spec.Tier1.zcTableHH]
  cases b <;> first | apply ll | apply hh

private theorem neighbour_map (w h : Nat) (b : Band) (cs : Array Coeff) (x y : Nat) :
    WidePlain.hasNeighbour w h (cs.map cellOf) (x, y) = (sgeom w h b).anySigNeighbour cs x y := by
  simp only [WidePlain.hasNeighbour, counts_map w h b, Geom.anySigNeighbour]

private theorem contribution (a b : Coeff) :
    JPEG2000.Tier1.pairContrib (cellOf a).contribution (cellOf b).contribution =
      Spec.Tier1.signContribution (Spec.Tier1.NeighbourSign.ofBits a.sig a.sign)
        (Spec.Tier1.NeighbourSign.ofBits b.sig b.sign) := by
  cases a with | mk sa na ma va ra la =>
    cases b with | mk sb nb mb vb rb lb =>
      cases sa <;> cases na <;> cases sb <;> cases nb <;> rfl

private theorem sign_map (w h : Nat) (b : Band) (cs : Array Coeff) (x y : Nat) :
    WidePlain.signCoding w h (cs.map cellOf) x y = (sgeom w h b).signContext cs x y := by
  simp only [WidePlain.signCoding, read_map w h b, contribution, Geom.signContext, Geom.nbSign,
    Tier1Equiv.nbAt_sgeom]
  generalize Spec.Tier1.signContribution _ _ = hc
  generalize Spec.Tier1.signContribution _ _ = vc
  unfold Spec.Tier1.scContext
  have signs (z : Int) : (z < 0 ∧ z ≠ 0 ∧ ¬0 < z) ∨
      (z = 0 ∧ ¬z < 0 ∧ ¬0 < z) ∨ (0 < z ∧ z ≠ 0 ∧ ¬z < 0) := by omega
  rcases signs hc with ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ <;>
    rcases signs vc with ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ <;> simp [*]

private theorem bit_sim {start : Nat} {s : WidePlain.State} {d : DecState} (R : Sim start s d) (cx : Nat) :
    (WidePlain.bit s cx).1 = (d.decodeBit cx).1 ∧ Sim start (WidePlain.bit s cx).2 (d.decodeBit cx).2 := by
  have H := MQEquiv.decode_sim R.mq cx
  exact ⟨H.1, H.2, R.cells⟩

private theorem decision {start : Nat} {s : WidePlain.State} {d : DecState} (R : Sim start s d)
    (cx : Nat) : ∃ v t z, WidePlain.bit s cx = (v, t) ∧ d.decodeBit cx = (v, z) ∧ Sim start t z := by
  obtain ⟨hb, H⟩ := bit_sim R cx
  exact ⟨(WidePlain.bit s cx).1, _, _, rfl, by rw [hb], H⟩

private theorem put_sim {start : Nat} {s : WidePlain.State} {d : DecState} (R : Sim start s d)
    (w h : Nat) (b : Band) (x y : Nat) (c : Coeff) :
    Sim start (WidePlain.put s w (x, y) (cellOf c))
      { d with coeffs := (sgeom w h b).setCoeff d.coeffs x y c } := by
  refine ⟨R.mq, ?_⟩
  simp [WidePlain.put, Geom.setCoeff, Geom.idx, sgeom, R.cells]

section steps
variable {start : Nat} {s : WidePlain.State} {d : DecState} (w h : Nat) (b : Band) (p : Nat)

private theorem become_sim (R : Sim start s d) (vis : Bool) (x y : Nat) :
    Sim start (WidePlain.become w h p vis s (x, y)) (Spec.Tier1.becomeSignificant (sgeom w h b) p vis d x y) := by
  let cx := ((sgeom w h b).signContext d.coeffs x y).1
  obtain ⟨hb, R'⟩ := bit_sim R cx
  dsimp only [cx] at hb R'
  simp only [WidePlain.become, Spec.Tier1.becomeSignificant, Spec.Tier1.decodeSign, R.cells, sign_map w h b]
  simp only [hb, R'.cells, read_map w h b, Nat.shiftLeft_eq, Nat.one_mul]
  let c := (sgeom w h b).coeffAt (d.decodeBit cx).2.coeffs x y
  exact put_sim R' w h b x y { c with sig := true, sign := (d.decodeBit cx).1 !=
      ((sgeom w h b).signContext d.coeffs x y).2, mag := c.mag + 2 ^ p, lsbPlane := p, visited := vis }

private theorem zero_sim (R : Sim start s d) (vis : Bool) (x y : Nat) :
    Sim start (WidePlain.zeroCode w h b p vis s (x, y)) (Spec.Tier1.zeroCode (sgeom w h b) p vis d x y) := by
  let cx := (sgeom w h b).zcCtx d.coeffs x y
  obtain ⟨hb, R'⟩ := bit_sim R cx
  dsimp only [cx] at hb R'
  simp only [WidePlain.zeroCode, Spec.Tier1.zeroCode, R.cells, zero_map w h b, hb]
  split
  · apply become_sim w h b p R'
  · simp only [R'.cells, read_map w h b]
    exact put_sim R' w h b x y { (sgeom w h b).coeffAt (d.decodeBit cx).2.coeffs x y with visited := vis }

private theorem propagate_sim (R : Sim start s d) (pos : Nat × Nat) :
    Sim start (WidePlain.propagate w h b p s pos) (Spec.Tier1.sigPropStep (sgeom w h b) p d pos) := by
  obtain ⟨x, y⟩ := pos
  simp only [WidePlain.propagate, Spec.Tier1.sigPropStep, R.cells, read_map w h b, neighbour_map w h b, cellOf]
  split
  · exact zero_sim w h b p R true x y
  · exact R

private theorem refine_sim (R : Sim start s d) (pos : Nat × Nat) :
    Sim start (WidePlain.refineCell w h p s pos) (Spec.Tier1.magRefStep (sgeom w h b) p d pos) := by
  obtain ⟨x, y⟩ := pos
  let cx := (sgeom w h b).mrCtx d.coeffs x y
  obtain ⟨hb, R'⟩ := bit_sim R cx
  simp only [WidePlain.refineCell, Spec.Tier1.magRefStep, R.cells, read_map w h b, neighbour_map w h b, cellOf]
  split
  · have hc : cx = (if ((sgeom w h b).coeffAt d.coeffs x y).refined then 16
        else if (sgeom w h b).anySigNeighbour d.coeffs x y then 15 else 14) := by
      simp only [cx, Geom.mrCtx, Spec.Tier1.mrContext, Bool.not_not]
    simp only [← hc, hb, Nat.shiftLeft_eq, Nat.one_mul, Tier1Equiv.decodeBit_coeffs]
    let c := (sgeom w h b).coeffAt d.coeffs x y
    simpa only [cx, c, cellOf, Tier1Equiv.decodeBit_coeffs] using put_sim R' w h b x y
      { c with mag := c.mag + (if (d.decodeBit cx).1 then 2 ^ p else 0), refined := true,
               lsbPlane := p }
  · exact R

private theorem cleanup_sim (R : Sim start s d) (pos : Nat × Nat) :
    Sim start (WidePlain.cleanupCell w h b p s pos) (Spec.Tier1.cleanupStep (sgeom w h b) p d pos) := by
  obtain ⟨x, y⟩ := pos
  simp only [WidePlain.cleanupCell, Spec.Tier1.cleanupStep, R.cells, read_map w h b, cellOf]
  split
  · exact zero_sim w h b p R false x y
  · exact R

private theorem column_sim (R : Sim start s d) (col : List (Nat × Nat)) :
    Sim start (WidePlain.cleanupColumn w h b p s col) (Spec.Tier1.cleanupColumn (sgeom w h b) p d col) := by
  have ordinary (l : List (Nat × Nat)) {t : WidePlain.State} {z : DecState} (H : Sim start t z) :
      Sim start (l.foldl (WidePlain.cleanupCell w h b p) t) (l.foldl (Spec.Tier1.cleanupStep (sgeom w h b) p) z) :=
    List.foldl_rel H (fun pos _ _ _ H' => cleanup_sim w h b p H' pos)
  have interrupted {t : WidePlain.State} {z : DecState} (H : Sim start t z) (l : List (Nat × Nat)) :
      Sim start (match l with
        | [] => t
        | pos :: rest => rest.foldl (WidePlain.cleanupCell w h b p) (WidePlain.become w h p false t pos))
        (match l with
        | [] => z
        | (x, y) :: rest => rest.foldl (Spec.Tier1.cleanupStep (sgeom w h b) p)
            (Spec.Tier1.becomeSignificant (sgeom w h b) p false z x y)) := by
    cases l with
    | nil => exact H
    | cons pos rest => exact ordinary rest (become_sim w h b p H false pos.1 pos.2)
  simp only [WidePlain.cleanupColumn, Spec.Tier1.cleanupColumn, Spec.Tier1.runLengthColumn, R.cells, read_map w h b,
    neighbour_map w h b, cellOf]
  split
  · simp only [Spec.Tier1.ctxRunLength, Spec.Tier1.ctxUniform]
    obtain ⟨run, t, z, hf, hs, H⟩ := decision R 17
    simp only [hf, hs]
    cases run
    · exact H
    · obtain ⟨hi, t', z', hf', hs', H'⟩ := decision H 18
      obtain ⟨lo, t'', z'', hf'', hs'', H''⟩ := decision H' 18
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hf', hs', hf'', hs'']
      exact interrupted H'' (col.drop ((if hi then 2 else 0) + (if lo then 1 else 0)))
  · exact ordinary _ R

end steps

private theorem columns_eq (w h : Nat) :
    WidePlain.columns w h = Spec.Tier1.stripeColumns w h := by
  simp only [WidePlain.columns, Spec.Tier1.stripeColumns, Tier1Equiv.stripeColumn_eq]

private theorem pass_sim (w h : Nat) (b : Band) (K i : Nat) {start : Nat}
    {s : WidePlain.State} {d : DecState} (R : Sim start s d) :
    Sim start (WidePlain.runPass w h b K (WidePlain.columns w h) s i) (Spec.Tier1.runPass (sgeom w h b) K d i) := by
  have pp : JPEG2000.Tier1.passPlane K i = Spec.Tier1.passPlane K i := rfl
  rcases Tier1Equiv.passKind_cases i with ⟨kf, ks⟩ | ⟨kf, ks⟩ | ⟨kf, ks⟩ <;>
    simp only [WidePlain.runPass, Spec.Tier1.runPass, columns_eq, kf, ks, pp]
  · unfold Spec.Tier1.sigPropPass Spec.Tier1.scanOrder
    rw [List.foldl_flatten]
    exact List.foldl_rel R (fun col _ _ _ H => List.foldl_rel H
      (fun pos _ _ _ H' => propagate_sim w h b _ H' pos))
  · unfold Spec.Tier1.magRefPass Spec.Tier1.scanOrder
    rw [List.foldl_flatten]
    exact List.foldl_rel R (fun col _ _ _ H => List.foldl_rel H
      (fun pos _ _ _ H' => refine_sim w h b _ H' pos))
  · unfold Spec.Tier1.cleanupPass
    have H := List.foldl_rel (l := Spec.Tier1.stripeColumns w h) R
      (fun col _ _ _ H => column_sim w h b (Spec.Tier1.passPlane K i) H col)
    refine ⟨H.mq, ?_⟩
    dsimp only
    rw [H.cells]
    simp only [Spec.Tier1.clearVisited, Array.map_map]
    rfl

/-- A consecutive range of plain passes preserves the MQ simulation and every wide coefficient
field, for arbitrary starting pass and plane count. -/
theorem runPasses_equiv (w h : Nat) (b : Band) (K first n start : Nat)
    (s : WidePlain.State) (d : DecState) (hmq : MQEquiv.Rel start s.mq d.mq d.cxs)
    (hc : s.cells = d.coeffs.map cellOf) :
    let t := WidePlain.runPasses w h b K first n s
    let z := (List.range' first n).foldl (Spec.Tier1.runPass (sgeom w h b) K) d
    MQEquiv.Rel start t.mq z.mq z.cxs ∧ t.cells = z.coeffs.map cellOf := by
  have R : Sim start s d := ⟨hmq, hc⟩
  have H := List.foldl_rel (l := List.range' first n) R
    (fun i _ _ _ H => pass_sim w h b K i H)
  exact ⟨H.mq, H.cells⟩

private theorem segments_sim (data : ByteArray) (w h : Nat) (b : Band) (K : Nat)
    (segs : List Seg) (first : Nat) (s : WidePlain.State) (d : DecState)
    (hx : MQEquiv.CxRel s.mq.cx d.cxs) (hc : s.cells = d.coeffs.map cellOf) :
    WidePlain.runSegments data w h b K segs first s =
      (Spec.Tier1.decodeSegments .plain (sgeom w h b) K (segs.map (Tier1EquivM.segOf data))
        first d).coeffs.map cellOf := by
  induction segs generalizing first s d with
  | nil => exact hc
  | cons sg rest ih =>
    let bytes := MQEquiv.segment data sg.start sg.stop
    let t : WidePlain.State := { s with mq := JPEG2000.MQ.Dec.init data sg.start sg.stop s.mq.cx }
    let z : DecState := { d with mq := Spec.MQ.initdec bytes }
    have init : MQEquiv.Rel sg.start t.mq z.mq z.cxs := MQEquiv.init_sim data sg.start sg.stop _ _ hx
    have ⟨Hmq, Hcs⟩ := runPasses_equiv w h b K first sg.passes sg.start t z init hc
    have pass : Spec.Tier1.runPassM .plain (sgeom w h b) K = Spec.Tier1.runPass (sgeom w h b) K := by
      funext d i
      exact Spec.Tier1.runPassM_plain ..
    simp only [WidePlain.runSegments, List.map_cons, Spec.Tier1.decodeSegments, pass]
    exact ih _ _ _ Hmq.cx Hcs

/-- The wide plain decoder agrees with the independently validated Annex D block, including
all MQ restarts and all six coefficient fields. The spec takes a list of bytes per segment,
hence the premise that the production slices are inside their buffer. -/
theorem decodeCodeBlockSegs_equiv (data : ByteArray) (segments : Array Seg) (w h : Nat)
    (b : Band) (Mb zbp : Nat)
    (hrange : ∀ sg ∈ segments.toList, sg.start ≤ sg.stop ∧ sg.stop ≤ data.size)
    (hK : 0 < segsPasses segments → Mb - zbp ≤ WidePlain.maxCodedPlanes) :
    WidePlain.decodeCodeBlockSegs data segments w h b Mb zbp =
      (Spec.Tier1.decodeCodeBlock (Tier1EquivM.specBlockM data segments w h b 0 Mb zbp)).map
        (·.map cellOf) := by
  unfold WidePlain.decodeCodeBlockSegs Spec.Tier1.decodeCodeBlock
  rw [Tier1EquivM.badRange_false data segments hrange, Tier1EquivM.specBlockM_clamp]
  let kept := clampSegs segments (Mb - zbp)
  let cb := Tier1EquivM.specBlockM data kept w h b 0 Mb zbp
  have count : cb.numPasses = segsPasses kept := by
    rw [Tier1EquivM.segsPasses_eq]
    exact Tier1EquivM.specBlockM_numPasses ..
  have nle : segsPasses kept ≤ segsPasses segments := by
    simp only [Tier1EquivM.segsPasses_eq]
    exact Tier1EquivM.clampSegs_sum_le ..
  have hk : ¬(0 < segsPasses kept ∧ Mb - zbp > WidePlain.maxCodedPlanes) :=
    fun ⟨hn, hbig⟩ => (Nat.not_lt.mpr (hK (Nat.lt_of_lt_of_le hn nle))) hbig
  have shape : cb.segments.map (·.passes) = kept.toList.map (·.passes) := by
    simp [cb, Tier1EquivM.specBlockM, List.map_map, Function.comp_def]
  have partition := Tier1EquivM.segmentPasses_eq
    (m := ({} : Style)) (md := Spec.Tier1.Mode.plain) ⟨rfl, rfl, rfl, rfl, rfl⟩ (segsPasses kept) 0
  have H := segments_sim data w h b (Mb - zbp) kept.toList 0
    ⟨JPEG2000.MQ.Dec.init data 0 0 JPEG2000.MQ.tier1Contexts, Array.replicate (w * h) {}⟩
    (DecState.init (sgeom w h b) []) Tier1EquivM.tier1Contexts_rel
    (by simp [DecState.init, sgeom, cellOf])
  have out : WidePlain.runSegments data w h b (Mb - zbp) kept.toList 0
      ⟨JPEG2000.MQ.Dec.init data 0 0 JPEG2000.MQ.tier1Contexts, Array.replicate (w * h) {}⟩ =
      (Spec.Tier1.decodeState cb).coeffs.map cellOf := H
  change _ = (Spec.Tier1.decodeCodeBlockExact cb).map _
  unfold Spec.Tier1.decodeCodeBlockExact Spec.Tier1.CodeBlock.validate
  rw [count, shape]
  have dims : cb.width = w ∧ cb.height = h := ⟨rfl, rfl⟩
  have mode : cb.mode = Spec.Tier1.Mode.plain := rfl
  have planes : cb.codedPlanes = Mb - zbp := rfl
  simp only [← show kept = clampSegs segments (Mb - zbp) from rfl, hk, dims.1, dims.2,
    mode, planes, partition, Bool.false_eq_true, ↓reduceIte]
  by_cases dim : w > 1024 ∨ h > 1024 ∨ w * h > 4096 <;>
    by_cases over : 0 < segsPasses kept ∧ segsPasses kept > 3 * (Mb - zbp) - 2 <;>
    by_cases seg : (kept.toList.map (·.passes) != Spec.Tier1.segmentPasses .plain (segsPasses kept) 0) = true <;>
    simp only [WidePlain.validateSize, dim, over, seg, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw, Except.map, ↓reduceIte] <;> first | rfl | exact congrArg Except.ok out

/-- One plain MQ codeword gives exactly the Annex D signed magnitude, last plane and flags,
including at truncation and after discarding surplus passes. -/
theorem decodeCodeBlock_equiv (data : ByteArray) (start stop w h : Nat) (b : Band)
    (Mb zbp numPasses : Nat) (hrange : start ≤ stop ∧ stop ≤ data.size)
    (hK : 0 < numPasses → Mb - zbp ≤ WidePlain.maxCodedPlanes) :
    WidePlain.decodeCodeBlock data start stop w h b Mb zbp numPasses =
      (Spec.Tier1.decodeCodeBlock (specBlock data start stop w h b Mb zbp numPasses)).map (·.map cellOf) := by
  let segs : Array Seg := if numPasses = 0 then #[] else #[⟨start, stop, numPasses⟩]
  have block : Tier1EquivM.specBlockM data segs w h b 0 Mb zbp =
      specBlock data start stop w h b Mb zbp numPasses := by
    by_cases hn : numPasses = 0 <;> simp [Tier1EquivM.specBlockM, segs, hn, specBlock,
      Spec.Tier1.CodeBlock.ofData, Spec.Tier1.Segment.single] <;> rfl
  have count : segsPasses segs = numPasses := by
    rw [Tier1EquivM.segsPasses_eq]
    by_cases hn : numPasses = 0 <;> simp [segs, hn]
  have ranges : ∀ sg ∈ segs.toList, sg.start ≤ sg.stop ∧ sg.stop ≤ data.size := by
    intro sg hm
    by_cases hn : numPasses = 0 <;> simp [segs, hn] at hm
    subst sg
    exact hrange
  rw [← block]
  have hr : ¬(start > stop ∨ stop > data.size) := by omega
  simpa only [WidePlain.decodeCodeBlock, hr, ↓reduceIte, segs] using
    decodeCodeBlockSegs_equiv data segs w h b Mb zbp ranges (by rw [count]; exact hK)

/-- E-2 guard bits and exponent, plus the full RGN shift, fit the production allocation
guard for any number of leading zero bit-planes. -/
theorem codedPlanes_le_of_header (guardBits exponent roiShift zeroPlanes : Nat)
    (hg : guardBits ≤ 7) (he : exponent ≤ 31) (hr : roiShift ≤ 255) :
    guardBits + exponent - 1 + roiShift - zeroPlanes ≤ WidePlain.maxCodedPlanes := by
  unfold WidePlain.maxCodedPlanes
  omega

-- Single-cell MQ fixtures, truncated immediately after the second refinement.
-- 0x01 encodes (ZC 0,1), (sign 9,0), (MR 14,1), (MR 16,0). Even the final zero
-- decision lowers the last coded plane. The positive signed value exceeds Int32.maxValue.
example : ((WidePlain.decodeCodeBlock ⟨#[0x01]⟩ 0 1 1 1 .LL 32 0 6).toOption.map
    (·.map fun c => (c.value, c.lsbPlane))) = some #[(3221225472, 29)] := by decide +kernel

-- 0x05 reverses the sign and both refinement decisions. The maximum header shift
-- places both nonzero bits above bit 255.
example : ((WidePlain.decodeCodeBlock ⟨#[0x05]⟩ 0 1 1 1 .LL (37 + 255) 0 6).toOption.map
    (·.map fun c => (c.value, c.lsbPlane))) = some #[(-(2 ^ 291 + 2 ^ 289), 289)] := by decide +kernel

-- For K = 38, [0x05, 0x3f] codes the top bit and 36 zero refinements. The second
-- segment [0x07] codes a one in the carried MR context at plane zero. Four surplus
-- passes in its signalled length are discarded.
example : ((WidePlain.decodeCodeBlockSegs ⟨#[5, 63, 7]⟩ #[⟨0, 2, 109⟩, ⟨2, 3, 7⟩]
    1 1 .LL 38 0).toOption.map (·.map fun c => (c.value, c.lsbPlane))) =
      some #[(2 ^ 37 + 1, 0)] := by decide +kernel

-- The final segment lies below plane zero, but a reversed byte range still fails validation.
example : (match WidePlain.decodeCodeBlockSegs ⟨#[5, 63, 7]⟩
    #[⟨0, 2, 109⟩, ⟨2, 3, 3⟩, ⟨3, 2, 1⟩] 1 1 .LL 38 0 with
    | .error e => some e
    | .ok _ => none) = some (.malformed JPEG2000.Tier1.tier1Loc "code-block data range outside the buffer") := by
  decide +kernel

end JPEG2000.Spec.Tier1Wide
