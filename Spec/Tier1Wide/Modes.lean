import JPEG2000.Tier1.WideModes
import Spec.Tier1Wide.Plain

/-!
# Wide pass simulation for every style (Plan.md §§4, 5.1, 7; T.800 Annexes C and D)

The active coder relation switches between Annex C and the independent D.6 raw reader.
The raster relation includes every coefficient field. A clipped read height for a whole
stripe column implements the spec's row-dependent hidden-neighbour predicate.
-/

namespace JPEG2000.Spec.Tier1Wide.Modes

open JPEG2000.Tier2.Geometry (Band)
open JPEG2000.Tier1
open Spec.Tier1 (Coeff Geom DecState Mode)
open Tier1EquivM (gV Coder StyleRel)

/-- Simulation inside a pass. The active reader and all saved MQ contexts are related,
and every cell has its exact spec magnitude, last plane, sign and coding flags. -/
structure CoreSim (start : Nat) (raw : Bool) (s : WidePlain.State) (d : DecState) : Prop where
  /-- Registers and contexts for the active MQ or raw reader. -/
  coder : Coder start raw s.mq d.mq d.cxs d.raw
  /-- Coefficients in raster order. -/
  cells : s.cells = d.coeffs.map cellOf

/-- At a pass boundary the strict-segmentation error count is also observable. -/
structure Sim (start : Nat) (raw : Bool) (s : WideModes.State) (d : DecState) : Prop where
  /-- The active reader and coefficient raster agree. -/
  core : CoreSim start raw s.block d
  /-- Cumulative segmentation-symbol errors agree. -/
  bad : s.badSegSymbols = d.badSegSymbols

/-- MQ decoding advances the related readers with the same decision. -/
theorem mqDecision_equiv {start : Nat} {s : WidePlain.State} {d : DecState}
    (R : CoreSim start false s d) (cx : Nat) :
    (WidePlain.bit s cx).1 = (d.decodeBit cx).1 ∧
    CoreSim start false (WidePlain.bit s cx).2 (d.decodeBit cx).2 := by
  have H := MQEquiv.decode_sim R.coder cx
  exact ⟨H.1, H.2, R.cells⟩

/-- Raw decoding advances the related readers with the same decision and saved contexts. -/
theorem rawDecision_equiv {start : Nat} {s : WidePlain.State} {d : DecState}
    (R : CoreSim start true s d) :
    (WideModes.rawDecision s).1 = d.rawBit.1 ∧
    CoreSim start true (WideModes.rawDecision s).2 d.rawBit.2 := by
  obtain ⟨hr, hx⟩ := R.coder
  obtain ⟨hv, hnext, hcx⟩ := Tier1EquivM.rawBit_sim hr
  rw [Tier1EquivM.rawBit_eq]
  exact ⟨hv, ⟨hnext, hcx ▸ hx⟩, R.cells⟩

private theorem decision {start : Nat} {s : WidePlain.State} {d : DecState}
    (R : CoreSim start false s d) (cx : Nat) :
    ∃ v t z, WidePlain.bit s cx = (v, t) ∧ d.decodeBit cx = (v, z) ∧ CoreSim start false t z := by
  obtain ⟨hb, H⟩ := mqDecision_equiv R cx
  exact ⟨(WidePlain.bit s cx).1, _, _, rfl, by rw [hb], H⟩

private abbrev rowLimit (vc : Bool) (h y : Nat) :=
  if vc then min h (4 * (y / 4 + 1)) else h

private theorem limit_eq {w h : Nat} {col : List (Nat × Nat)}
    (hc : col ∈ Spec.Tier1.stripeColumns w h) {pos : Nat × Nat} (hp : pos ∈ col) (vc : Bool) :
    WideModes.visibleHeight vc h col = rowLimit vc h pos.2 := by
  simp only [Spec.Tier1.stripeColumns, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨stripe, _, x, _, he⟩ := hc
  have bounds {q : Nat × Nat} (hq : q ∈ col) := Tier1Equiv.mem_stripeColumn (he ▸ hq : q ∈ _)
  cases col with
  | nil => simp at hp
  | cons hd tl =>
    have h₁ := bounds (q := hd) (by simp)
    have h₂ := bounds hp
    have eq : hd.2 / 4 = pos.2 / 4 := by omega
    simp only [WideModes.visibleHeight, List.headD_cons, rowLimit, eq]

section geometry
variable {w h limit : Nat} {b : Band} {vc : Bool} {y : Nat}

private theorem neighbour_read (hl : limit = rowLimit vc h y) (cs : Array Coeff) (nx ny : Int) :
    WidePlain.readCell w limit (cs.map cellOf) nx ny = cellOf ((gV w h b vc).nbAt cs y nx ny) := by
  subst limit
  unfold WidePlain.readCell Geom.nbAt Geom.hidden Geom.coeffAt
  simp only [gV, Geom.idx, rowLimit]
  have loadCell (k : Nat) : (cs.map cellOf).getD k {} = cellOf (cs.getD k {}) := by
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
    cases cs[k]? <;> rfl
  by_cases hi : 0 ≤ nx ∧ nx < w ∧ 0 ≤ ny ∧ ny < h
  <;> cases vc <;> simp only [Bool.false_and, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
      decide_eq_true_eq, hi, loadCell, true_and] <;> try rfl
  all_goals
    by_cases hidden : 4 * ((y : Int) / 4 + 1) ≤ ny <;> simp only [hidden, ↓reduceIte]
    <;> split <;> first | rfl | omega

private theorem own_read (hl : limit = rowLimit vc h y) (cs : Array Coeff) (x : Nat) :
    WidePlain.readCell w limit (cs.map cellOf) x y = cellOf ((gV w h b vc).coeffAt cs x y) := by
  rw [neighbour_read (b := b) hl]
  have hy : ¬ (4 * ((y : Int) / 4 + 1) ≤ y) := by omega
  simp [Geom.nbAt, Geom.hidden, hy]

private theorem counts_map (hl : limit = rowLimit vc h y) (cs : Array Coeff) (x : Nat) :
    WidePlain.counts w limit (cs.map cellOf) x y = (gV w h b vc).sigCounts cs x y := by
  simp only [WidePlain.counts, neighbour_read (b := b) hl, cellOf, Geom.sigCounts, Geom.nbSig,
    show ∀ v : Bool, v.toNat = (if v then 1 else 0) by intro v; cases v <;> rfl]

private theorem zero_map (hl : limit = rowLimit vc h y) (cs : Array Coeff) (x : Nat) :
    WidePlain.zeroContext b (WidePlain.counts w limit (cs.map cellOf) x y) = (gV w h b vc).zcCtx cs x y := by
  rw [counts_map (b := b) hl]
  unfold Geom.zcCtx
  generalize (gV w h b vc).sigCounts cs x y = n
  obtain ⟨a, v, d⟩ := n
  have ll (a v d : Nat) : JPEG2000.Tier1.zcLLLH a v d = Spec.Tier1.zcTableLLLH a v d := by
    rcases a with _ | ⟨_ | a⟩ <;> rcases v with _ | ⟨_ | v⟩ <;> rcases d with _ | ⟨_ | d⟩ <;>
      simp [JPEG2000.Tier1.zcLLLH, Spec.Tier1.zcTableLLLH]
  have hh (a d : Nat) : JPEG2000.Tier1.zcHHcol a d = Spec.Tier1.zcTableHH a d := by
    rcases a with _ | ⟨_ | a⟩ <;> rcases d with _ | ⟨_ | ⟨_ | d⟩⟩ <;>
      simp [JPEG2000.Tier1.zcHHcol, Spec.Tier1.zcTableHH]
  cases b <;> first | apply ll | apply hh

private theorem neighbour_map (hl : limit = rowLimit vc h y) (cs : Array Coeff) (x : Nat) :
    WidePlain.hasNeighbour w limit (cs.map cellOf) (x, y) = (gV w h b vc).anySigNeighbour cs x y := by
  simp only [WidePlain.hasNeighbour, counts_map (b := b) hl, Geom.anySigNeighbour]

private theorem contribution (a b : Coeff) :
    JPEG2000.Tier1.pairContrib (cellOf a).contribution (cellOf b).contribution =
      Spec.Tier1.signContribution (Spec.Tier1.NeighbourSign.ofBits a.sig a.sign)
        (Spec.Tier1.NeighbourSign.ofBits b.sig b.sign) := by
  cases a with | mk sa na ma va ra la =>
    cases b with | mk sb nb mb vb rb lb =>
      cases sa <;> cases na <;> cases sb <;> cases nb <;> rfl

private theorem sign_map (hl : limit = rowLimit vc h y) (cs : Array Coeff) (x : Nat) :
    WidePlain.signCoding w limit (cs.map cellOf) x y = (gV w h b vc).signContext cs x y := by
  simp only [WidePlain.signCoding, neighbour_read (b := b) hl, contribution, Geom.signContext, Geom.nbSign]
  generalize Spec.Tier1.signContribution _ _ = hc
  generalize Spec.Tier1.signContribution _ _ = vert
  unfold Spec.Tier1.scContext
  have signs (z : Int) : (z < 0 ∧ z ≠ 0 ∧ ¬0 < z) ∨
      (z = 0 ∧ ¬z < 0 ∧ ¬0 < z) ∨ (0 < z ∧ z ≠ 0 ∧ ¬z < 0) := by omega
  rcases signs hc with ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ <;>
    rcases signs vert with ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ <;> simp [*]

end geometry

private theorem put_sim {start : Nat} {raw : Bool} {s : WidePlain.State} {d : DecState}
    (R : CoreSim start raw s d) (w h : Nat) (b : Band) (vc : Bool) (x y : Nat) (c : Coeff) :
    CoreSim start raw (WidePlain.put s w (x, y) (cellOf c))
      { d with coeffs := (gV w h b vc).setCoeff d.coeffs x y c } := by
  refine ⟨R.coder, ?_⟩
  simp [WidePlain.put, Geom.setCoeff, Geom.idx, gV, R.cells]

section steps
variable {w h limit start : Nat} {b : Band} {vc : Bool} {s : WidePlain.State} {d : DecState} (p : Nat)

private theorem become_sim (R : CoreSim start false s d) (vis : Bool) (x y : Nat) (hl : limit = rowLimit vc h y) :
    CoreSim start false (WidePlain.become w limit p vis s (x, y)) (Spec.Tier1.becomeSignificant (gV w h b vc) p vis d x y) := by
  let cx := ((gV w h b vc).signContext d.coeffs x y).1
  obtain ⟨hb, R'⟩ := mqDecision_equiv R cx
  dsimp only [cx] at hb R'
  simp only [WidePlain.become, Spec.Tier1.becomeSignificant, Spec.Tier1.decodeSign, R.cells, sign_map (b := b) hl]
  simp only [hb, R'.cells, own_read (b := b) hl, Nat.shiftLeft_eq, Nat.one_mul]
  let c := (gV w h b vc).coeffAt (d.decodeBit cx).2.coeffs x y
  exact put_sim R' w h b vc x y { c with sig := true, sign := (d.decodeBit cx).1 !=
      ((gV w h b vc).signContext d.coeffs x y).2, mag := c.mag + 2 ^ p, lsbPlane := p, visited := vis }

private theorem zero_sim (R : CoreSim start false s d) (vis : Bool) (x y : Nat) (hl : limit = rowLimit vc h y) :
    CoreSim start false (WidePlain.zeroCode w limit b p vis s (x, y)) (Spec.Tier1.zeroCode (gV w h b vc) p vis d x y) := by
  let cx := (gV w h b vc).zcCtx d.coeffs x y
  obtain ⟨hb, R'⟩ := mqDecision_equiv R cx
  dsimp only [cx] at hb R'
  simp only [WidePlain.zeroCode, Spec.Tier1.zeroCode, R.cells, zero_map hl, hb]
  split
  · exact become_sim p R' vis x y hl
  · simp only [R'.cells, own_read (b := b) hl]
    exact put_sim R' w h b vc x y { (gV w h b vc).coeffAt (d.decodeBit cx).2.coeffs x y with visited := vis }

private theorem propagate_sim (R : CoreSim start false s d) (pos : Nat × Nat) (hl : limit = rowLimit vc h pos.2) :
    CoreSim start false (WidePlain.propagate w limit b p s pos) (Spec.Tier1.sigPropStep (gV w h b vc) p d pos) := by
  obtain ⟨x, y⟩ := pos
  simp only [WidePlain.propagate, Spec.Tier1.sigPropStep, R.cells, own_read (b := b) hl, neighbour_map (b := b) hl, cellOf]
  split
  · exact zero_sim p R true x y hl
  · exact R

private theorem refine_sim (R : CoreSim start false s d) (pos : Nat × Nat) (hl : limit = rowLimit vc h pos.2) :
    CoreSim start false (WidePlain.refineCell w limit p s pos) (Spec.Tier1.magRefStep (gV w h b vc) p d pos) := by
  obtain ⟨x, y⟩ := pos
  let cx := (gV w h b vc).mrCtx d.coeffs x y
  obtain ⟨hb, R'⟩ := mqDecision_equiv R cx
  simp only [WidePlain.refineCell, Spec.Tier1.magRefStep, R.cells, own_read (b := b) hl, neighbour_map (b := b) hl, cellOf]
  split
  · have hc : cx = (if ((gV w h b vc).coeffAt d.coeffs x y).refined then 16
        else if (gV w h b vc).anySigNeighbour d.coeffs x y then 15 else 14) := by
      simp only [cx, Geom.mrCtx, Spec.Tier1.mrContext, Bool.not_not]
    simp only [← hc, hb, Nat.shiftLeft_eq, Nat.one_mul, Tier1Equiv.decodeBit_coeffs]
    let c := (gV w h b vc).coeffAt d.coeffs x y
    simpa only [cx, c, cellOf, Tier1Equiv.decodeBit_coeffs] using put_sim R' w h b vc x y
      { c with mag := c.mag + (if (d.decodeBit cx).1 then 2 ^ p else 0), refined := true,
               lsbPlane := p }
  · exact R

private theorem cleanup_sim (R : CoreSim start false s d) (pos : Nat × Nat) (hl : limit = rowLimit vc h pos.2) :
    CoreSim start false (WidePlain.cleanupCell w limit b p s pos) (Spec.Tier1.cleanupStep (gV w h b vc) p d pos) := by
  obtain ⟨x, y⟩ := pos
  simp only [WidePlain.cleanupCell, Spec.Tier1.cleanupStep, R.cells, own_read (b := b) hl, cellOf]
  split
  · exact zero_sim p R false x y hl
  · exact R

private theorem column_sim (R : CoreSim start false s d) (col : List (Nat × Nat))
    (hl : ∀ pos ∈ col, limit = rowLimit vc h pos.2) :
    CoreSim start false (WidePlain.cleanupColumn w limit b p s col)
      (Spec.Tier1.cleanupColumn (gV w h b vc) p d col) := by
  have ordinary (l : List (Nat × Nat)) (sub : l ⊆ col) {t : WidePlain.State} {z : DecState}
      (H : CoreSim start false t z) :
      CoreSim start false (l.foldl (WidePlain.cleanupCell w limit b p) t)
        (l.foldl (Spec.Tier1.cleanupStep (gV w h b vc) p) z) :=
    List.foldl_rel H (fun pos hp _ _ H' => cleanup_sim p H' pos (hl pos (sub hp)))
  have interrupted {t : WidePlain.State} {z : DecState} (H : CoreSim start false t z)
      (l : List (Nat × Nat)) (sub : l ⊆ col) :
      CoreSim start false (match (generalizing := false) l with
        | [] => t
        | pos :: rest => rest.foldl (WidePlain.cleanupCell w limit b p) (WidePlain.become w limit p false t pos))
        (match (generalizing := false) l with
        | [] => z
        | (x, y) :: rest => rest.foldl (Spec.Tier1.cleanupStep (gV w h b vc) p)
            (Spec.Tier1.becomeSignificant (gV w h b vc) p false z x y)) := by
    cases l with
    | nil => exact H
    | cons pos rest =>
      exact ordinary rest (fun _ hp => sub (List.mem_cons_of_mem _ hp))
        (become_sim p H false pos.1 pos.2 (hl pos (sub (by simp))))
  have eligible : (col.all fun (x, y) =>
      let c := WidePlain.readCell w limit s.cells x y
      !c.sig && !c.visited && !WidePlain.hasNeighbour w limit s.cells (x, y)) =
      (col.all fun (x, y) =>
      let c := (gV w h b vc).coeffAt d.coeffs x y
      !c.sig && !c.visited && !(gV w h b vc).anySigNeighbour d.coeffs x y) := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true]
    constructor <;> intro hall ⟨x, y⟩ hp <;>
      simpa only [R.cells, own_read (b := b) (hl (x, y) hp),
        neighbour_map (b := b) (hl (x, y) hp), cellOf] using hall (x, y) hp
  simp only [WidePlain.cleanupColumn, Spec.Tier1.cleanupColumn, Spec.Tier1.runLengthColumn, eligible]
  split
  · simp only [Spec.Tier1.ctxRunLength, Spec.Tier1.ctxUniform]
    obtain ⟨run, t, z, hf, hs, H⟩ := decision R 17
    simp only [hf, hs]
    cases run
    · exact H
    · obtain ⟨hi, t', z', hf', hs', H'⟩ := decision H 18
      obtain ⟨lo, t'', z'', hf'', hs'', H''⟩ := decision H' 18
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hf', hs', hf'', hs'']
      exact interrupted H'' (col.drop ((if hi then 2 else 0) + (if lo then 1 else 0))) (fun _ hp => List.mem_of_mem_drop hp)
  · exact ordinary col (fun _ hp => hp) R

private theorem raw_coeffs (d : DecState) : d.rawBit.2.coeffs = d.coeffs := by
  rw [Tier1EquivM.rawBit_eq]

private theorem rawPropagate_sim (R : CoreSim start true s d) (pos : Nat × Nat)
    (hl : limit = rowLimit vc h pos.2) :
    CoreSim start true (WideModes.rawPropagate w limit p s pos)
      (Spec.Tier1.rawSigPropStep (gV w h b vc) p d pos) := by
  obtain ⟨x, y⟩ := pos
  obtain ⟨hv, R'⟩ := rawDecision_equiv R
  obtain ⟨hn, R''⟩ := rawDecision_equiv R'
  simp only [WideModes.rawPropagate, Spec.Tier1.rawSigPropStep, R.cells, own_read (b := b) hl,
    neighbour_map (b := b) hl, cellOf, hv, hn, raw_coeffs, Nat.shiftLeft_eq, Nat.one_mul]
  let c := (gV w h b vc).coeffAt d.coeffs x y
  split
  · split
    · simpa only [cellOf, raw_coeffs, c] using put_sim R'' w h b vc x y
        { c with sig := true, sign := d.rawBit.2.rawBit.1, mag := c.mag + 2 ^ p,
                 visited := true, lsbPlane := p }
    · simpa only [cellOf, raw_coeffs, c] using put_sim R' w h b vc x y { c with visited := true }
  · exact R

private theorem rawRefine_sim (R : CoreSim start true s d) (pos : Nat × Nat)
    (hl : limit = rowLimit vc h pos.2) :
    CoreSim start true (WideModes.rawRefine w limit p s pos)
      (Spec.Tier1.rawMagRefStep (gV w h b vc) p d pos) := by
  obtain ⟨x, y⟩ := pos
  obtain ⟨hv, R'⟩ := rawDecision_equiv R
  simp only [WideModes.rawRefine, Spec.Tier1.rawMagRefStep, R.cells, own_read (b := b) hl, cellOf,
    hv, raw_coeffs, Nat.shiftLeft_eq, Nat.one_mul]
  split
  · let c := (gV w h b vc).coeffAt d.coeffs x y
    simpa only [cellOf, raw_coeffs, c] using put_sim R' w h b vc x y
      { c with mag := c.mag + (if d.rawBit.1 then 2 ^ p else 0), refined := true, lsbPlane := p }
  · exact R

end steps

private theorem columns_eq (w h : Nat) :
    WidePlain.columns w h = Spec.Tier1.stripeColumns w h := by
  simp only [WidePlain.columns, Spec.Tier1.stripeColumns, Tier1Equiv.stripeColumn_eq]

private theorem scan_sim {w h start : Nat} {raw vc : Bool}
    (step : Nat → WidePlain.State → Nat × Nat → WidePlain.State)
    (refStep : DecState → Nat × Nat → DecState)
    (one : ∀ limit pos, limit = rowLimit vc h pos.2 → ∀ t z, CoreSim start raw t z →
      CoreSim start raw (step limit t pos) (refStep z pos))
    {s : WidePlain.State} {d : DecState} (R : CoreSim start raw s d) :
    CoreSim start raw ((WidePlain.columns w h).foldl (fun t col =>
      col.foldl (step (WideModes.visibleHeight vc h col)) t) s)
      ((Spec.Tier1.scanOrder w h).foldl refStep d) := by
  rw [columns_eq, Spec.Tier1.scanOrder, List.foldl_flatten]
  exact List.foldl_rel R (fun _ hc _ _ H => List.foldl_rel H
    (fun pos hp => one _ pos (limit_eq hc hp vc)))

/-- The wide MQ or raw coefficient pass simulates the selected independent Annex D pass,
including vertical causality, for every plane count and every absolute pass index. -/
theorem passBody_equiv {w h K i start : Nat} {b : Band} {md : Mode} {s : WidePlain.State}
    {d : DecState} (R : CoreSim start (Spec.Tier1.isRawPass md i) s d) :
    CoreSim start (Spec.Tier1.isRawPass md i)
      (WideModes.passBody md.vertCausal (Spec.Tier1.isRawPass md i) w h b K (WidePlain.columns w h) s i)
      (if Spec.Tier1.isRawPass md i then Spec.Tier1.runRawPass (gV w h b md.vertCausal) K d i
       else Spec.Tier1.runPass (gV w h b md.vertCausal) K d i) := by
  have pp : JPEG2000.Tier1.passPlane K i = Spec.Tier1.passPlane K i := rfl
  rcases Tier1Equiv.passKind_cases i with ⟨kf, ks⟩ | ⟨kf, ks⟩ | ⟨kf, ks⟩
  · cases hr : Spec.Tier1.isRawPass md i <;> rw [hr] at R <;>
      simp only [WideModes.passBody, Spec.Tier1.runRawPass, Spec.Tier1.runPass, pp, ks, kf,
        Bool.false_eq_true, ↓reduceIte, Spec.Tier1.sigPropPass, Spec.Tier1.rawSigPropPass]
    · exact scan_sim _ _ (fun _ pos hl _ _ H => propagate_sim _ H pos hl) R
    · exact scan_sim _ _ (fun _ pos hl _ _ H => rawPropagate_sim _ H pos hl) R
  · cases hr : Spec.Tier1.isRawPass md i <;> rw [hr] at R <;>
      simp only [WideModes.passBody, Spec.Tier1.runRawPass, Spec.Tier1.runPass, pp, ks, kf,
        Bool.false_eq_true, ↓reduceIte, Spec.Tier1.magRefPass, Spec.Tier1.rawMagRefPass]
    · exact scan_sim _ _ (fun _ pos hl _ _ H => refine_sim _ H pos hl) R
    · exact scan_sim _ _ (fun _ pos hl _ _ H => rawRefine_sim _ H pos hl) R
  · have hr : Spec.Tier1.isRawPass md i = false := by simp [Spec.Tier1.isRawPass, ks]
    rw [hr] at R ⊢
    simp only [WideModes.passBody, Spec.Tier1.runPass, Spec.Tier1.cleanupPass, pp, kf, ks,
      Bool.false_eq_true, ↓reduceIte, columns_eq]
    have H := List.foldl_rel (l := Spec.Tier1.stripeColumns w h) R
      (fun col hc _ _ H => column_sim (w := w) (b := b) (Spec.Tier1.passPlane K i) H col
        (fun _ hp => limit_eq hc hp md.vertCausal))
    refine ⟨H.coder, ?_⟩
    dsimp only
    rw [H.cells]
    simp only [Spec.Tier1.clearVisited, Array.map_map]
    rfl

/-- The four UNIFORM bits advance MQ and update the cumulative count on the same symbols. -/
theorem segSymbol_equiv {start : Nat} {s : WideModes.State} {d : DecState} (R : Sim start false s d) :
    Sim start false (WideModes.segSymbol s) (Spec.Tier1.segSymbol d) := by
  obtain ⟨v₃, t₃, z₃, hf₃, hs₃, H₃⟩ := decision R.core 18
  obtain ⟨v₂, t₂, z₂, hf₂, hs₂, H₂⟩ := decision H₃ 18
  obtain ⟨v₁, t₁, z₁, hf₁, hs₁, H₁⟩ := decision H₂ 18
  obtain ⟨v₀, t₀, z₀, hf₀, hs₀, H₀⟩ := decision H₁ 18
  have bad (t z : DecState) (v : Bool) (he : t.decodeBit 18 = (v, z)) :
      z.badSegSymbols = t.badSegSymbols := by simpa only [he] using Tier1EquivM.decodeBit_bad t 18
  have count : s.badSegSymbols = z₀.badSegSymbols := by
    rw [bad _ _ _ hs₀, bad _ _ _ hs₁, bad _ _ _ hs₂, bad _ _ _ hs₃, R.bad]
  simp only [WideModes.segSymbol, Spec.Tier1.segSymbol, Spec.Tier1.ctxUniform,
    hf₃, hs₃, hf₂, hs₂, hf₁, hs₁, hf₀, hs₀]
  split
  · exact ⟨H₀, count⟩
  · exact ⟨⟨H₀.coder, H₀.cells⟩, congrArg (· + 1) count⟩

/-- One full coding pass of any Table A.19 style preserves the active reader, saved
contexts, exact wide raster and bad-symbol count. There is no upper bound on `K`. -/
theorem runPass_equiv {m : Style} {md : Mode} (hm : StyleRel m md) (w h : Nat) (b : Band)
    (K i start : Nat) (s : WideModes.State) (d : DecState)
    (R : Sim start (Spec.Tier1.isRawPass md i) s d) :
    Sim start (Spec.Tier1.isRawPass md i)
      (WideModes.runPass m w h b K (WidePlain.columns w h) s i)
      (Spec.Tier1.runPassM md (gV w h b md.vertCausal) K d i) := by
  let raw := Spec.Tier1.isRawPass md i
  let g := gV w h b md.vertCausal
  let t := { s with block := WideModes.passBody md.vertCausal raw w h b K (WidePlain.columns w h) s.block i }
  let z := if raw then Spec.Tier1.runRawPass g K d i else Spec.Tier1.runPass g K d i
  have body : Sim start raw t z :=
    ⟨passBody_equiv R.core, R.bad.trans (Tier1EquivM.pass_bad g md K d i).symm⟩
  have kind : (JPEG2000.Tier1.passKind i == 2) = (Spec.Tier1.passKind i == .cleanup) := by
    rcases Tier1Equiv.passKind_cases i with ⟨kf, ks⟩ | ⟨kf, ks⟩ | ⟨kf, ks⟩ <;> rw [kf, ks] <;> rfl
  let symbol := md.segSymbols && Spec.Tier1.passKind i == .cleanup
  have afterSymbol : Sim start raw (if symbol then WideModes.segSymbol t else t)
      (if symbol then Spec.Tier1.segSymbol z else z) := by
    split
    · rename_i hs
      have hk : Spec.Tier1.passKind i = .cleanup := by simpa [symbol] using (Bool.and_eq_true_iff.mp hs).2
      have hr : raw = false := by simp [raw, Spec.Tier1.isRawPass, hk]
      rw [hr] at body ⊢
      exact segSymbol_equiv body
    · exact body
  unfold WideModes.runPass Spec.Tier1.runPassM
  rw [Tier1EquivM.isRawPass_eq hm, hm.vertCausal, hm.segSymbols, kind, hm.reset]
  cases md.reset <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact afterSymbol
  · exact ⟨⟨Tier1EquivM.coder_setcx afterSymbol.core.coder _ _ Tier1EquivM.tier1Contexts_rel,
            afterSymbol.core.cells⟩, afterSymbol.bad⟩

end JPEG2000.Spec.Tier1Wide.Modes
