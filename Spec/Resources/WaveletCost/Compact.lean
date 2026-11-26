import JPEG2000.DWT97

/-!
# Packed synthesis loop visits (Plan.md §§3–5, 7, S3; T.800 B.5 and F.3)

The meter unfolds each production recursion and uses its next buffer, flag and index.
A packed update charges twenty visits, covering the loop test and up to four byte
accesses for each of three reads and one write. These are structural visits. The
price of copying a non-unique buffer can be applied separately to every write.
-/

namespace JPEG2000.Spec.Resources.WaveletCost

open JPEG2000.Bytes JPEG2000.Header
open JPEG2000.DWT53 (Buf idx_lt batch halfN halfN_le)
open JPEG2000

/-- A measured execution indexed by its production result and visit ceiling.
Erasing a measurement returns the same value, including its overflow flag. -/
structure Run {α : Type} (result : α) (cap : Nat) where
  value : α
  visits : Nat
  erase : value = result
  bounded : visits ≤ cap

private def done {α : Type} (x : α) (n : Nat) : Run x n := ⟨x, n, rfl, Nat.le_refl _⟩

private def pay {α : Type} {x : α} {c budget : Nat} (n : Nat) (s : Run x c)
    (h : n + c ≤ budget) : Run x budget :=
  ⟨s.value, n + s.visits, s.erase, Nat.le_trans (Nat.add_le_add_left s.bounded n) h⟩

private def finish {α : Type} {x : α} {budget : Nat} (n : Nat) (h : n ≤ budget) : Run x budget :=
  ⟨x, n, rfl, h⟩

private def pass53 {N : Nat} (upd : Bool) (off n : Nat) (hN : off+n ≤ N) (hn : 2 ≤ n)
    (b : Buf N) (i : Nat) (ok : Bool) :
    Run (DWT53.liftPass upd off n hN hn b i ok) (1 + 20*(n-i)) := by
  rw [DWT53.liftPass]
  split
  · exact pay 20 (pass53 _ _ _ _ _ _ _ _) (by omega)
  · exact finish 1 (by omega)
termination_by n-i

private def pass97 {N : Nat} (cq : Int64) (off n : Nat) (hN : off+n ≤ N) (hn : 2 ≤ n)
    (b : Buf N) (i : Nat) (ok : Bool) :
    Run (DWT97.liftPass97 cq off n hN hn b i ok) (1 + 20*(n-i)) := by
  rw [DWT97.liftPass97]
  split
  · exact pay 20 (pass97 _ _ _ _ _ _ _ _) (by omega)
  · exact finish 1 (by omega)
termination_by n-i

private def scale97 {N : Nat} (qe qo : Int64) (par off n : Nat) (hN : off+n ≤ N)
    (b : Buf N) (i : Nat) (ok : Bool) :
    Run (DWT97.scalePass97 qe qo par off n hN b i ok) (1 + 20*(n-i)) := by
  rw [DWT97.scalePass97]
  split
  · exact pay 20 (scale97 _ _ _ _ _ _ _ _ _) (by omega)
  · exact finish 1 (by omega)
termination_by n-i

private def loadRow {N T : Nat} (pw : Nat) (hN : N = pw * (N / pw)) (u0 u1 y : Nat)
    (hW : u1-u0 ≤ pw) (hy : y < N / pw) (P : Buf N) (hT : u1-u0 ≤ T) (tmp : Buf T) (i : Nat) :
    Run (DWT53.loadRow pw hN u0 u1 y hW hy P hT tmp i) (1 + 20*(u1-u0-i)) := by
  rw [DWT53.loadRow]
  split
  · exact pay 20 (loadRow _ _ _ _ _ _ _ _ _ _ _) (by omega)
  · exact finish 1 (by omega)
termination_by u1-u0-i

private def storeRow {N T : Nat} (pw : Nat) (hN : N = pw * (N / pw)) (W y : Nat)
    (hW : W ≤ pw) (hy : y < N / pw) (tmp : Buf T) (hT : W ≤ T) (P : Buf N) (i : Nat) :
    Run (DWT53.storeRow pw hN W y hW hy tmp hT P i) (1 + 20*(W-i)) := by
  rw [DWT53.storeRow]
  split
  · exact pay 20 (storeRow _ _ _ _ _ _ _ _ _ _) (by omega)
  · exact finish 1 (by omega)
termination_by W-i

private def gridFuel (H bw i c : Nat) := (H-i)*(bw+1) + (bw-c)

private theorem nextRow {H i bw c : Nat} (hi : i < H) (hc : bw ≤ c) :
    gridFuel H bw (i+1) 0 < gridFuel H bw i c := by
  unfold gridFuel
  rw [show H-i = (H-(i+1))+1 by omega, Nat.succ_mul]
  omega

private def loadCols {N T : Nat} (pw : Nat) (hN : N = pw * (N / pw)) (v0 v1 x bw : Nat)
    (hx : x+bw ≤ pw) (hH : v1-v0 ≤ N / pw) (hT : bw*(v1-v0) ≤ T) (P : Buf N)
    (tmp : Buf T) (i c : Nat) :
    Run (DWT53.loadCols pw hN v0 v1 x bw hx hH hT P tmp i c)
      (1 + 20*gridFuel (v1-v0) bw i c) := by
  rw [DWT53.loadCols]
  split
  · split
    · exact pay 20 (loadCols _ _ _ _ _ _ _ _ _ _ _ _ _) (by unfold gridFuel; omega)
    · exact pay 20 (loadCols _ _ _ _ _ _ _ _ _ _ _ _ _) (by have := nextRow (H := v1-v0) (i := i) (bw := bw) (c := c) (by omega) (by omega); omega)
  · exact finish 1 (by omega)
termination_by (v1-v0-i, bw-c)

private def storeCols {N T : Nat} (pw : Nat) (hN : N = pw * (N / pw)) (H x bw : Nat)
    (hx : x+bw ≤ pw) (hH : H ≤ N / pw) (hT : bw*H ≤ T) (tmp : Buf T) (P : Buf N) (i c : Nat) :
    Run (DWT53.storeCols pw hN H x bw hx hH hT tmp P i c) (1 + 20*gridFuel H bw i c) := by
  rw [DWT53.storeCols]
  split
  · split
    · exact pay 20 (storeCols _ _ _ _ _ _ _ _ _ _ _ _) (by unfold gridFuel; omega)
    · exact pay 20 (storeCols _ _ _ _ _ _ _ _ _ _ _ _) (by have := nextRow (H := H) (i := i) (bw := bw) (c := c) (by omega) (by omega); omega)
  · exact finish 1 (by omega)
termination_by (H-i, bw-c)


private def line53 {N : Nat} (off n par : Nat) (hN : off+n ≤ N) (b : Buf N) (ok : Bool) :
    Run (DWT53.lift1d off n par hN b ok) (10 + 100*n) := by
  unfold DWT53.lift1d
  split
  · rename_i hn
    let a := pass53 true off n hN hn b (par%2) ok
    rw [← a.erase]
    exact pay (1+a.visits) (pass53 _ _ _ _ _ _ _ _) (by have := a.bounded; omega)
  · exact finish 10 (by omega)

private def line97 {N : Nat} (off n par : Nat) (hN : off+n ≤ N) (b : Buf N) (ok : Bool) :
    Run (DWT97.lift1d97 off n par hN b ok) (10 + 100*n) := by
  unfold DWT97.lift1d97
  split
  · rename_i hn
    dsimp only
    let a := scale97 DWT97.kQ64 DWT97.invKQ64 par off n hN b 0 ok
    rw [← a.erase]
    let d := pass97 DWT97.mDeltaQ64 off n hN hn a.value.1 (par%2) a.value.2
    rw [← d.erase]
    let g := pass97 DWT97.mGammaQ64 off n hN hn d.value.1 ((par+1)%2) d.value.2
    rw [← g.erase]
    let e := pass97 DWT97.mBetaQ64 off n hN hn g.value.1 (par%2) g.value.2
    rw [← e.erase]
    exact pay (1+a.visits+d.visits+g.visits+e.visits) (pass97 _ _ _ _ _ _ _ _) (by
      have := a.bounded; have := d.bounded; have := g.bounded; have := e.bounded; omega)
  · exact finish 10 (by omega)

private abbrev kernel (irrev : Bool) {N : Nat} := if irrev then @DWT97.lift1d97 N else @DWT53.lift1d N
private abbrev rows (irrev : Bool) {N T : Nat} := if irrev then @DWT97.rowPass N T else @DWT53.rowPass N T
private abbrev lifts (irrev : Bool) {T : Nat} := if irrev then @DWT97.liftCols T else @DWT53.liftCols T
private abbrev columns (irrev : Bool) {N T : Nat} := if irrev then @DWT97.colPass N T else @DWT53.colPass N T
private abbrev levels (irrev : Bool) {N T : Nat} := if irrev then @DWT97.levels N T else @DWT53.levels N T

private def line (irrev : Bool) {N : Nat} (off n par : Nat) (hN : off+n ≤ N) (b : Buf N) (ok : Bool) :
    Run (kernel irrev off n par hN b ok) (10 + 100*n) := by
  cases irrev
  · exact line53 ..
  · exact line97 ..

private theorem peel {j n : Nat} (h : j < n) (k : Nat) :
    (n-j)*k = (n-(j+1))*k+k := by
  rw [show n-j = (n-(j+1))+1 by omega, Nat.succ_mul]

private def measureRows (irrev : Bool) {N T : Nat} (pw : Nat) (hN : N = pw * (N / pw))
    (u0 u1 H : Nat) (hW : u1-u0 ≤ pw) (hH : H ≤ N / pw) (hT : u1-u0 ≤ T)
    (P : Buf N) (tmp : Buf T) (ok : Bool) (y : Nat) :
    Run (rows irrev pw hN u0 u1 H hW hH hT P tmp ok y) (1 + (H-y)*(14 + 140*(u1-u0))) := by
  have step : rows irrev pw hN u0 u1 H hW hH hT P tmp ok y =
      if hy : y < H then
        let t := DWT53.loadRow pw hN u0 u1 y hW (by omega) P hT tmp 0
        let s := kernel irrev 0 (u1-u0) (u0%2) (by omega) t ok
        let q := DWT53.storeRow pw hN (u1-u0) y hW (by omega) s.1 hT P 0
        rows irrev pw hN u0 u1 H hW hH hT q s.1 s.2 (y+1)
      else (P,tmp,ok) := by
    cases irrev
    · exact DWT53.rowPass.eq_def ..
    · exact DWT97.rowPass.eq_def ..
  rw [step]; split
  · rename_i hy
    dsimp only
    let a := loadRow pw hN u0 u1 y hW (by omega) P hT tmp 0
    rw [← a.erase]
    let b := line irrev 0 (u1-u0) (u0%2) (by omega) a.value ok
    rw [← b.erase]
    let c := storeRow pw hN (u1-u0) y hW (by omega) b.value.1 hT P 0
    rw [← c.erase]
    exact pay (1+a.visits+b.visits+c.visits) (measureRows irrev _ _ _ _ _ _ _ _ _ _ _ _) (by
      have := peel hy (14+140*(u1-u0))
      have := a.bounded; have := b.bounded; have := c.bounded; omega)
  · exact finish 1 (by omega)
termination_by H-y

private def measureLifts (irrev : Bool) {T : Nat} (H par bw : Nat) (hT : bw*H ≤ T)
    (tmp : Buf T) (ok : Bool) (c : Nat) :
    Run (lifts irrev H par bw hT tmp ok c) (1 + (bw-c)*(11+100*H)) := by
  have step : lifts irrev H par bw hT tmp ok c =
      if hc : c < bw then
        let s := kernel irrev (c*H) H par (by
          have := Nat.mul_le_mul_right H hc; rw [Nat.succ_mul] at this; omega) tmp ok
        lifts irrev H par bw hT s.1 s.2 (c+1)
      else (tmp,ok) := by
    cases irrev
    · exact DWT53.liftCols.eq_def ..
    · exact DWT97.liftCols.eq_def ..
  rw [step]; split
  · rename_i hc
    dsimp only
    let s := line irrev (c*H) H par (by
      have := Nat.mul_le_mul_right H hc; rw [Nat.succ_mul] at this; omega) tmp ok
    rw [← s.erase]
    exact pay (1+s.visits) (measureLifts irrev _ _ _ _ _ _ _) (by
      have := peel hc (11+100*H); have := s.bounded; omega)
  · exact finish 1 (by omega)
termination_by bw-c

private theorem batchPrice (H bw : Nat) (hb : bw ≤ batch) :
    1 + (1 + 20*gridFuel H bw 0 0) + (1 + (bw-0)*(11+100*H)) +
      (1 + 20*gridFuel H bw 0 0) ≤ (H+1)*2048 := by
  change bw ≤ 8 at hb
  have hg := Nat.mul_le_mul_left H (show bw+1 ≤ 9 by omega)
  have hl := Nat.mul_le_mul_right (11+100*H) hb
  simp only [gridFuel, Nat.sub_zero, Nat.succ_mul] at *
  omega

private def measureColumns (irrev : Bool) {N T : Nat} (pw : Nat) (hN : N = pw * (N / pw))
    (W v0 v1 : Nat) (hW : W ≤ pw) (hH : v1-v0 ≤ N / pw) (hT : batch*(v1-v0) ≤ T)
    (P : Buf N) (tmp : Buf T) (ok : Bool) (x : Nat) :
    Run (columns irrev pw hN W v0 v1 hW hH hT P tmp ok x) (1+(W-x)*((v1-v0+1)*2048)) := by
  have step : columns irrev pw hN W v0 v1 hW hH hT P tmp ok x =
      if hx : x < W then
        let bw := min batch (W-x)
        have ht := Nat.le_trans (Nat.mul_le_mul_right (v1-v0) (Nat.min_le_left batch (W-x))) hT
        let a := DWT53.loadCols pw hN v0 v1 x bw (by omega) hH ht P tmp 0 0
        let b := lifts irrev (v1-v0) (v0%2) bw ht a ok 0
        let c := DWT53.storeCols pw hN (v1-v0) x bw (by omega) hH ht b.1 P 0 0
        columns irrev pw hN W v0 v1 hW hH hT c b.1 b.2 (x+bw)
      else (P,tmp,ok) := by
    cases irrev
    · exact DWT53.colPass.eq_def ..
    · exact DWT97.colPass.eq_def ..
  rw [step]; split
  · rename_i hx
    dsimp only
    let bw := min batch (W-x)
    have hb : bw ≤ batch := Nat.min_le_left ..
    have pos : 0 < bw := by dsimp [bw,batch]; omega
    have ht := Nat.le_trans (Nat.mul_le_mul_right (v1-v0) hb) hT
    have hxb : x+bw ≤ pw := by dsimp [bw]; omega
    let a := loadCols pw hN v0 v1 x bw hxb hH ht P tmp 0 0
    rw [← a.erase]
    let b := measureLifts irrev (v1-v0) (v0%2) bw ht a.value ok 0
    rw [← b.erase]
    let c := storeCols pw hN (v1-v0) x bw hxb hH ht b.value.1 P 0 0
    rw [← c.erase]
    exact pay (1+a.visits+b.visits+c.visits) (measureColumns irrev _ _ _ _ _ _ _ _ _ _ _ _) (by
      have hdrop := Nat.mul_le_mul_right ((v1-v0+1)*2048)
        (show W-(x+bw)+1 ≤ W-x by omega)
      rw [Nat.succ_mul] at hdrop
      have := batchPrice (v1-v0) bw hb
      have := a.bounded; have := b.bounded; have := c.bounded
      change _ + (1+(W-(x+bw))*_) ≤ _
      omega)
  · exact finish 1 (by omega)
termination_by W-x
decreasing_by simp only [batch]; omega

/-- One recursion visit and four coordinate halvings per non-base rectangle. -/
private def coarser (r : Rect) : (k : Nat) → Run (halfN r k) (1+5*k)
  | 0 => done r 1
  | k+1 =>
    let s := coarser r k
    ⟨DWT53.halfRect s.value, 5+s.visits, congrArg DWT53.halfRect s.erase, by have := s.bounded; omega⟩

private theorem axisPrice {w h a : Nat} (hw : w ≤ a) (hh : h ≤ a) (ha : w*h ≤ a) :
    (1+(h-0)*(14+140*w)) + (1+(w-0)*((h+1)*2048)) ≤ 4500*a + 2 := by
  simp only [Nat.sub_zero, Nat.mul_add, ← Nat.mul_assoc, Nat.mul_one]
  have : h*(140*w) = (w*h)*140 := by ac_rfl
  have : h*140*w = w*h*140 := by ac_rfl
  have : w*(h+1)*2048 = (w*h+w)*2048 := by rw [Nat.mul_succ w h]
  omega

private def measureLevels (irrev : Bool) {N T : Nat} (tc : Rect) (pw : Nat) (hN : N = pw * (N / pw))
    (hpw : tc.x1-tc.x0 ≤ pw) (hph : tc.y1-tc.y0 ≤ N / pw) (hT : batch*(tc.y1-tc.y0) ≤ T)
    (hT2 : tc.x1-tc.x0 ≤ T) (wpos : 0 < tc.width) (hpos : 0 < tc.height)
    (nl : Nat) (P : Buf N) (tmp : Buf T) (ok : Bool) :
    Run (levels irrev tc pw hN hpw hph hT hT2 nl P tmp ok)
      (1+nl*(5*nl+4500*(tc.width*tc.height)+5)) := by
  cases nl with
  | zero =>
    exact finish 1 (by simp)
  | succ k =>
    obtain ⟨_,coordinateVisits,rfl,geometryBound⟩ := coarser tc k
    let r := halfN tc k
    have hr := halfN_le tc k
    have wt : r.width ≤ tc.width := hr.1
    have ht : r.height ≤ tc.height := hr.2
    have step : levels irrev tc pw hN hpw hph hT hT2 (k+1) P tmp ok =
        let a := rows irrev pw hN r.x0 r.x1 r.height (Nat.le_trans wt hpw) (Nat.le_trans ht hph)
          (Nat.le_trans wt hT2) P tmp ok 0
        let b := columns irrev pw hN r.width r.y0 r.y1 (Nat.le_trans wt hpw) (Nat.le_trans ht hph)
          (Nat.le_trans (Nat.mul_le_mul_left batch ht) hT) a.1 a.2.1 a.2.2 0
        levels irrev tc pw hN hpw hph hT hT2 k b.1 b.2.1 b.2.2 := by
      cases irrev <;> rfl
    rw [step]
    dsimp only
    let a := measureRows irrev pw hN r.x0 r.x1 r.height (Nat.le_trans wt hpw) (Nat.le_trans ht hph)
      (Nat.le_trans wt hT2) P tmp ok 0
    rw [← a.erase]
    let b := measureColumns irrev pw hN r.width r.y0 r.y1 (Nat.le_trans wt hpw) (Nat.le_trans ht hph)
      (Nat.le_trans (Nat.mul_le_mul_left batch ht) hT) a.value.1 a.value.2.1 a.value.2.2 0
    rw [← b.erase]
    exact pay (1+coordinateVisits+a.visits+b.visits) (measureLevels irrev _ _ _ _ _ _ _ wpos hpos _ _ _ _) (by
      have hac := axisPrice (Nat.le_trans wt (Nat.le_mul_of_pos_right _ hpos))
        (Nat.le_trans ht (Nat.le_mul_of_pos_left _ wpos)) (Nat.mul_le_mul wt ht)
      have av : a.visits ≤ 1+(r.height-0)*(14+140*r.width) := a.bounded
      have bv : b.visits ≤ 1+(r.width-0)*((r.height+1)*2048) := b.bounded
      have m := Nat.mul_le_mul_left k (show 5*k+4500*(tc.width*tc.height)+5 ≤
          5*(k+1)+4500*(tc.width*tc.height)+5 by omega)
      rw [Nat.succ_mul (k)]; omega)
termination_by nl

/-- Exact length of the allocated packed scratch in Int32 cells. An invalid shape
and either empty input axis return before allocation. A nonempty zero-level attempt
still asks for the scratch in the source program. -/
def scratchCells (p : Plane) (r : Rect) : Nat :=
  if p.width = r.width ∧ p.height = r.height then
    if p.width = 0 ∨ p.height = 0 then 0 else max p.width (batch*p.height)
  else 0

/-- Packed visit ceiling in terms of the area and number of remaining levels.
Four byte pushes initialize each scratch cell. Level k recomputes all k halvings. -/
def compactBudget (area nl : Nat) := 4 + 32*area + nl*(5*nl+4500*area+5)

/-- Select the packed transform exactly as the component dispatcher does. -/
abbrev fast (irrev : Bool) := if irrev then DWT97.idwt97Fast else DWT53.idwt53Fast

/-- Meter both actual packed entry points, including early failure and checked narrowing. -/
def compactRun (irrev : Bool) (p : Plane) (r : Rect) (nl : Nat) :
    Run (fast irrev p r nl) (compactBudget (r.width*r.height) nl) := by
  have entry : fast irrev p r nl =
      if hw : p.width = r.width ∧ p.height = r.height then
        if hz : p.width = 0 ∨ p.height = 0 then some p else
          let T := max p.width (batch*p.height)
          have hd : p.width*p.height/p.width = p.height := Nat.mul_div_cancel_left _ (by omega)
          let s := levels irrev r p.width (by rw [hd]) (Nat.le_of_eq hw.1.symm)
            (by rw [hd]; exact Nat.le_of_eq hw.2.symm) (by change batch*r.height ≤ T; rw [← hw.2]; exact Nat.le_max_right ..)
            (by change r.width ≤ T; rw [← hw.1]; exact Nat.le_max_left ..)
            nl ⟨p,rfl⟩ ⟨Plane.zero T 1, Nat.mul_one T⟩ true
          if s.2 then some s.1.val else none
      else none := by cases irrev <;> rfl
  rw [entry]; split
  · rename_i hw
    split
    · exact finish 2 (by unfold compactBudget; omega)
    · rename_i hz
      let T := max p.width (batch*p.height)
      have hd : p.width*p.height/p.width = p.height := Nat.mul_div_cancel_left _ (by omega)
      let s := measureLevels irrev r p.width (by rw [hd]) (Nat.le_of_eq hw.1.symm)
        (by rw [hd]; exact Nat.le_of_eq hw.2.symm)
        (by change batch*r.height ≤ T; rw [← hw.2]; exact Nat.le_max_right ..)
        (by change r.width ≤ T; rw [← hw.1]; exact Nat.le_max_left ..)
        (by omega) (by omega) nl ⟨p,rfl⟩ ⟨Plane.zero T 1, Nat.mul_one T⟩ true
      dsimp only
      rw [← s.erase]
      exact finish (3 + 4*T + s.visits) (by
        have bound := s.bounded
        have areaEq : r.width*r.height = p.width*p.height := by rw [hw.1,hw.2]
        have := Nat.le_mul_of_pos_left p.height (show 0 < p.width by omega)
        have := Nat.le_mul_of_pos_right p.width (show 0 < p.height by omega)
        unfold compactBudget; dsimp [T,batch]; simp only [areaEq] at bound ⊢; omega)
  · exact finish 1 (by unfold compactBudget; omega)

/-- Erasure, visits and scratch of either packed attempt within an area/level budget.
The scratch can exceed the full plane area by the column batch factor. -/
theorem compact_work (irrev : Bool) (p : Plane) (r : Rect) (nl A D : Nat)
    (ha : r.width*r.height ≤ A) (hd : nl ≤ D) :
    (compactRun irrev p r nl).value = fast irrev p r nl ∧
    (compactRun irrev p r nl).visits ≤ compactBudget A D ∧ scratchCells p r ≤ 8*A := by
  refine ⟨(compactRun ..).erase, Nat.le_trans (compactRun ..).bounded ?_, ?_⟩
  · unfold compactBudget
    have := Nat.mul_le_mul hd (show 5*nl+4500*(r.width*r.height)+5 ≤ 5*D+4500*A+5 by omega)
    omega
  · unfold scratchCells; split <;> try split
    all_goals first | exact Nat.zero_le _ | skip
    have := Nat.le_mul_of_pos_left p.height (show 0 < p.width by omega)
    have := Nat.le_mul_of_pos_right p.width (show 0 < p.height by omega)
    have shape : p.width = r.width ∧ p.height = r.height := by assumption
    rw [← shape.1, ← shape.2] at ha
    unfold batch; omega

end JPEG2000.Spec.Resources.WaveletCost
