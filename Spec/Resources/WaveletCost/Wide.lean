import Spec.Resources.WaveletCost.Compact
import Spec.Resources.WaveletCost.Operands

/-!
# Wide synthesis allocations and visits (Plan.md §§3–5 and 7; T.800 B.5, F.3)

A price vector keeps structural visits, array headers, outer array slots and arbitrary
integer cells independent. Tabulation sums the charges of all callbacks, including
the initial deinterleaving read and each materialised pass. Allocation is measured
in logical array slots. Summing all fresh arrays also bounds their live payload.
-/

namespace JPEG2000.Spec.Resources.WaveletCost

open JPEG2000.Header (Rect)
open JPEG2000
open JPEG2000.Tier2.Geometry (rectArea)


/-- Prices for one structural visit, array object, line reference and arbitrary integer
cell. Unit vectors extract separate counts. A cell can instead be priced in signed bits. -/
structure Prices where
  visit : Nat
  header : Nat
  reference : Nat
  integer : Nat

private def sumFin : (n : Nat) → (Fin n → Nat) → Nat
  | 0, _ => 0
  | n+1, f => sumFin n (fun i => f i.castSucc) + f (Fin.last n)

private theorem sumFin_le {n c : Nat} (f : Fin n → Nat) (h : ∀ i, f i ≤ c) :
    sumFin n f ≤ n*c := by
  induction n with
  | zero => simp [sumFin]
  | succ n ih =>
    rw [sumFin, Nat.succ_mul]
    exact Nat.add_le_add (ih _ fun _ => h _) (h _)

private def fixed {α : Type} (x : α) (k : Nat) : Run x k := ⟨x,k,rfl,Nat.le_refl _⟩

private def pad {α : Type} {x : α} {c d : Nat} (r : Run x c) (extra : Nat)
    (h : extra+c ≤ d) : Run x d :=
  ⟨r.value,extra+r.visits,r.erase,Nat.le_trans (Nat.add_le_add_left r.bounded _) h⟩

private def tab {α : Type} {n c : Nat} (p : Prices) (slot : Nat) {f : Fin n → α}
    (body : (i : Fin n) → Run (f i) c) :
    Run (Array.ofFn f) (p.header+n*(slot+p.visit+c)) :=
  ⟨Array.ofFn (fun i => (body i).value),
   p.header + n*(slot+p.visit) + sumFin n (fun i => (body i).visits),
   congrArg Array.ofFn (funext fun i => (body i).erase), by
     rw [Nat.mul_add n (slot+p.visit) c]
     have := sumFin_le (fun i => (body i).visits) (fun i => (body i).bounded)
     omega⟩

private def raster {c : Nat} (p : Prices) (w h : Nat) {f : Nat → Nat → Int}
    (sample : (x y : Nat) → Run (f x y) c) :
    Run (JPEG2000.WideReversible.raster w h f) (p.header+(w*h)*(p.integer+p.visit+c)) :=
  tab p p.integer fun i => sample (i.val%w) (i.val/w)

private def pass53 {c : Nat} (p : Prices) (upd : Bool) (n k : Nat) {f : Nat → Int}
    (read : (i : Nat) → Run (f i) c) :
    Run (DWT53.passVal upd n f k) (p.visit+3*c) :=
  let x := read k
  let l := read (DWT53.lnb k)
  let r := read (DWT53.rnb n k)
  ⟨if upd then x.value-(l.value+r.value+2)/4 else x.value+(l.value+r.value)/2,
   p.visit+x.visits+l.visits+r.visits, by simp only [x.erase,l.erase,r.erase,DWT53.passVal],
   by have := x.bounded; have := l.bounded; have := r.bounded; omega⟩

private def lift53 {c : Nat} (p : Prices) (a n k : Nat) {f : Nat → Int}
    (read : (i : Nat) → Run (f i) c) :
    Run (JPEG2000.WideReversible.lift a n f k) (10*p.visit+9*c) := by
  unfold JPEG2000.WideReversible.lift
  split
  · let s := read k
    rw [← s.erase]
    exact ⟨_,p.visit+s.visits,rfl,by have := s.bounded; omega⟩
  · let even (i : Nat) : Run (if (a+i)%2 = 0 then DWT53.passVal true n f i else f i)
          (p.visit+3*c) := by
      split
      · exact pass53 p true n i read
      · exact pad (read i) p.visit (by omega)
    split
    · exact pad (even k) p.visit (by omega)
    · exact pad (pass53 p false n k even) p.visit (by omega)

/-- A per-level budget common to both filters. Nonempty top-level area bounds
each axis at every resolution, even when a coarser rectangle has an empty axis. -/
def levelBudget (p : Prices) (A : Nat) :=
  (10+100*A)*p.visit + (3+12*A)*p.header + (2*A)*p.reference + (13*A)*p.integer

/-- The coarsest packed LL raster, followed by both axes of each requested level. -/
def wideBudget (p : Prices) (A D : Nat) :=
  4*p.visit + (p.visit+p.header+A*(p.integer+2*p.visit)) + D*levelBudget p A

private def base (p : Prices) (A : Nat) := p.visit+p.header+A*(p.integer+2*p.visit)

private theorem smaller (r : Rect) (A : Nat) (hw : r.width ≤ A) (hh : r.height ≤ A)
    (ha : rectArea r ≤ A) :
    (DWT53.halfRect r).width ≤ A ∧ (DWT53.halfRect r).height ≤ A ∧
    rectArea (DWT53.halfRect r) ≤ A := by
  obtain ⟨w,h⟩ := DWT53.halfN_le r 1
  exact ⟨Nat.le_trans w hw,Nat.le_trans h hh,Nat.le_trans (Nat.mul_le_mul w h) ha⟩

private def baseRun (p : Prices) (xs : Array Int) (stride : Nat) (r : Rect) (A : Nat)
    (ha : rectArea r ≤ A) :
    Run (JPEG2000.WideReversible.raster r.width r.height fun x y => xs.getD (y*stride+x) 0) (base p A) := by
  apply pad (raster p r.width r.height (fun x y => fixed (xs.getD (y*stride+x) 0) p.visit)) p.visit
  unfold base
  have := Nat.mul_le_mul_right (p.integer+2*p.visit) ha
  change r.width*r.height*_ ≤ _ at this
  rw [show p.integer+p.visit+p.visit = p.integer+2*p.visit by omega]; omega

private def synth53 (p : Prices) (xs : Array Int) (stride : Nat) (r : Rect) (A : Nat)
    (hw : r.width ≤ A) (hh : r.height ≤ A) (ha : rectArea r ≤ A) (nl : Nat) :
    Run (JPEG2000.WideReversible.synthesize xs stride r nl) (base p A + nl*levelBudget p A) := by
  cases nl with
  | zero => simpa only [JPEG2000.WideReversible.synthesize,Nat.zero_mul,Nat.add_zero] using baseRun p xs stride r A ha
  | succ n =>
    obtain ⟨w,h,area⟩ := smaller r A hw hh ha
    let ll := synth53 p xs stride (DWT53.halfRect r) A w h area n
    rw [JPEG2000.WideReversible.synthesize, ← ll.erase]
    dsimp only
    let read (x y : Nat) := fixed (detailRead xs ll.value stride r x y) p.visit
    let rows := raster p r.width r.height fun x y => lift53 p r.x0 r.width x (fun k => read k y)
    rw [← rows.erase]
    let cols := raster p r.width r.height fun x y => lift53 p r.y0 r.height y fun k =>
      fixed (rows.value.getD (k*r.width+x) 0) p.visit
    exact pad cols (5*p.visit+ll.visits+rows.visits) (by
      have := ll.bounded; have := rows.bounded
      have le := Nat.mul_le_mul_right (p.integer + p.visit + (10*p.visit+9*p.visit)) ha
      change (r.width*r.height)*_ ≤ _ at le
      have price : 5*p.visit + 2*(p.header + A*(p.integer+p.visit+(10*p.visit+9*p.visit))) ≤
          levelBudget p A := by unfold levelBudget; grind +ring
      rw [Nat.succ_mul n]
      omega)
termination_by nl

private def passCell (p : Prices) (s : JPEG2000.WideDWT97.Step) (even : Bool) (xs : Array Int)
    (n i : Nat) : Run (s.cell even (xs.getD i 0) (fun _ =>
      xs.getD (DWT53.lnb i) 0 + xs.getD (DWT53.rnb n i) 0)) (4*p.visit) := by
  cases s with
  | scale => exact pad (fixed _ (2*p.visit)) 0 (by omega)
  | lift active num =>
    unfold JPEG2000.WideDWT97.Step.cell
    split
    · exact fixed _ (4*p.visit)
    · exact pad (fixed _ (2*p.visit)) 0 (by omega)

private def passes (p : Prices) (a n : Nat) (ss : List JPEG2000.WideDWT97.Step) (xs : Array Int) :
    Run (JPEG2000.WideDWT97.passes a n ss xs)
      (p.visit + ss.length*(p.visit+p.header+n*(p.integer+5*p.visit))) := by
  cases ss with
  | nil => exact pad (fixed xs p.visit) 0 (by simp)
  | cons s ss =>
    rw [JPEG2000.WideDWT97.passes]
    let next := tab p p.integer (n := n) fun i => passCell p s ((a+i.val)%2 == 0) xs n i.val
    rw [← next.erase]
    exact pad (passes p a n ss next.value) (p.visit+next.visits) (by
      have := next.bounded
      rw [List.length_cons,Nat.succ_mul ss.length]
      have := congrArg (n*·) (show p.integer+p.visit+4*p.visit = p.integer+5*p.visit by omega)
      omega)
termination_by ss.length

private def linePrice (p : Prices) (n : Nat) :=
  8*p.visit+6*p.header+n*(6*p.integer+30*p.visit)

private def line97 (p : Prices) (a n : Nat) {f : Nat → Int}
    (read : (i : Nat) → Run (f i) (2*p.visit)) :
    Run (JPEG2000.WideDWT97.line a n f) (linePrice p n) := by
  unfold JPEG2000.WideDWT97.line
  split
  · let single (i : Fin n) : Run (if a%2=0 then f i else f i/2) (3*p.visit) := by
      let s := read i
      rw [← s.erase]
      exact ⟨_,p.visit+s.visits,rfl,by have := s.bounded; omega⟩
    exact pad (tab p p.integer single) p.visit (by unfold linePrice; grind +ring)
  · let init := tab p p.integer fun i : Fin n => read i.val
    rw [← init.erase]
    exact pad (passes p a n JPEG2000.WideDWT97.steps init.value) (p.visit+init.visits) (by
      have hh := init.bounded
      change _ + (p.visit+5*(p.visit+p.header+n*(p.integer+5*p.visit))) ≤ _
      unfold linePrice; grind +ring)

private def familyPrice (p : Prices) (n count : Nat) :=
  p.visit+p.header+count*(p.reference+p.visit+linePrice p n)

private def family (p : Prices) (a n count : Nat) {f : Nat → Nat → Int}
    (read : (i k : Nat) → Run (f i k) (2*p.visit)) :
    Run (JPEG2000.WideDWT97.lines a n count f) (familyPrice p n count) := by
  unfold JPEG2000.WideDWT97.lines
  split
  · exact pad (fixed #[] p.header) p.visit (by unfold familyPrice; omega)
  · exact pad (tab p p.reference fun i : Fin count => line97 p a n (read i))
      p.visit (by unfold familyPrice; omega)

/-- The actual returned family has exactly one line per requested index for
positive line length, and every materialised line has exactly that length. -/
theorem lines_shape (a n count : Nat) (f : Nat → Nat → Int) :
    let ls := JPEG2000.WideDWT97.lines a n count f
    ls.size = (if n=0 then 0 else count) ∧ ∀ xs ∈ ls, xs.size = n := by
  have ps (ss : List JPEG2000.WideDWT97.Step) (xs : Array Int) (hx : xs.size = n) :
      (JPEG2000.WideDWT97.passes a n ss xs).size = n := by
    induction ss generalizing xs with
    | nil => exact hx
    | cons s ss ih => exact ih _ (by simp)
  unfold JPEG2000.WideDWT97.lines
  split
  · simp
  · simp only [Array.size_ofFn, Array.mem_ofFn, true_and, forall_exists_index]
    intro xs i h
    subst xs
    unfold JPEG2000.WideDWT97.line
    split
    · simp
    · exact ps _ _ (by simp)

private theorem level97Price (p : Prices) {w h A : Nat} (hw : w ≤ A) (hh : h ≤ A)
    (ha : w*h ≤ A) :
    5*p.visit + familyPrice p w h + familyPrice p h w +
        (p.header+(w*h)*(p.integer+p.visit+2*p.visit)) ≤ levelBudget p A := by
  let perLine := p.reference+p.visit+(8*p.visit+6*p.header)
  let perCell := 6*p.integer+30*p.visit
  have fam (n count : Nat) : familyPrice p n count =
      p.visit+p.header+count*perLine+(count*n)*perCell := by
    unfold familyPrice linePrice perLine perCell; grind +ring
  rw [fam, fam, Nat.mul_comm h w]
  have := Nat.mul_le_mul_right perLine hw
  have := Nat.mul_le_mul_right perLine hh
  have := Nat.mul_le_mul_right perCell ha
  have := Nat.mul_le_mul_right (p.integer+p.visit+2*p.visit) ha
  have price : 5*p.visit+2*(p.visit+p.header+A*perLine+A*perCell)+
        (p.header+A*(p.integer+p.visit+2*p.visit)) ≤ levelBudget p A := by
    unfold levelBudget perCell perLine; grind +ring
  omega

private def synth97 (p : Prices) (xs : Array Int) (stride : Nat) (r : Rect) (A : Nat)
    (hw : r.width ≤ A) (hh : r.height ≤ A) (ha : rectArea r ≤ A) (nl : Nat) :
    Run (JPEG2000.WideDWT97.synthesize xs stride r nl).toArray (base p A + nl*levelBudget p A) := by
  cases nl with
  | zero =>
    let s := baseRun p xs stride r A ha
    simpa only [JPEG2000.WideDWT97.synthesize,Nat.zero_mul,Nat.add_zero] using s
  | succ n =>
    obtain ⟨w,h,area⟩ := smaller r A hw hh ha
    let ll := synth97 p xs stride (DWT53.halfRect r) A w h area n
    rw [JPEG2000.WideDWT97.synthesize]
    dsimp only
    rw [← ll.erase]
    let read (y x : Nat) := pad (fixed (detailRead xs ll.value stride r x y) p.visit) 0
      (show 0+p.visit ≤ 2*p.visit by omega)
    let rows := family p r.x0 r.width r.height read
    rw [← rows.erase]
    let cols := family p r.y0 r.height r.width fun x y => fixed (JPEG2000.WideDWT97.atLine rows.value y x) (2*p.visit)
    rw [← cols.erase]
    let out := raster p r.width r.height fun x y => fixed (JPEG2000.WideDWT97.atLine cols.value x y) (2*p.visit)
    exact pad out (5*p.visit+ll.visits+rows.visits+cols.visits) (by
        have := ll.bounded; have := rows.bounded; have := cols.bounded; have := out.bounded
        have := level97Price p hw hh ha
        rw [Nat.succ_mul n]; omega)
termination_by nl

private def early {α : Type} (p : Prices) (x : α) (A D : Nat) : Run x (wideBudget p A D) :=
  pad (fixed x (4*p.visit)) 0 (by unfold wideBudget; omega)

private theorem admittedAxes (r : Rect) (pos : rectArea r ≠ 0) :
    r.width ≤ rectArea r ∧ r.height ≤ rectArea r := by
  unfold rectArea at *
  exact ⟨Nat.le_mul_of_pos_right _ (by cases h : r.height <;> simp_all),
    Nat.le_mul_of_pos_left _ (by cases h : r.width <;> simp_all)⟩

/-- Meter the actual checked 5/3 entry, including both limit errors, malformed input,
zero levels and empty input. Rejection is priced independently of the claimed extent. -/
def wide53Run (p : Prices) (L : Limits) (r : Rect) (nl : Nat) (xs : Array Int) :
    Run (JPEG2000.WideReversible.idwt53 L r nl xs)
      (wideBudget p (min (rectArea r) L.maxWorkSamples) (min nl L.maxDecompLevels)) := by
  by_cases hd : nl ≤ L.maxDecompLevels
  · by_cases ha : rectArea r ≤ L.maxWorkSamples
    · simp only [Nat.min_eq_left hd,Nat.min_eq_left ha]
      have harea : r.width*r.height ≤ L.maxWorkSamples := ha
      simp only [JPEG2000.WideReversible.idwt53,Limits.check,Limits.checkLe,Limits.bound,hd,harea,
        ite_true,bind,pure,Except.bind,Except.pure]
      split
      · rename_i shape
        split
        · exact early ..
        · rename_i heavy
          have pos : rectArea r ≠ 0 := by
            intro zero
            have size : xs.size = 0 := shape.2.2.trans zero
            exact heavy (Or.inr (by simp [Array.isEmpty,size]))
          obtain ⟨w,h⟩ := admittedAxes r pos
          let s := synth53 p xs r.width r (rectArea r) w h (Nat.le_refl _) nl
          exact ⟨.ok s.value, 4*p.visit+s.visits, congrArg Except.ok s.erase, by
            have := s.bounded; unfold wideBudget; unfold base at this; omega⟩
      · exact early ..
    · have bad : ¬ r.width*r.height ≤ L.maxWorkSamples := ha
      simp only [JPEG2000.WideReversible.idwt53,Limits.check,Limits.checkLe,Limits.bound,hd,bad,
        ite_true,ite_false,bind,Except.bind]
      exact early ..
  · simp only [JPEG2000.WideReversible.idwt53,Limits.check,Limits.checkLe,Limits.bound,hd,
      ite_false,bind,Except.bind]
    exact early ..

/-- Meter the actual checked 9/7 entry. The dependent raster carries its exact
sample count. Bypassed or rejected calls allocate zero integer cells. -/
def wide97Run (p : Prices) (L : Limits) (q : JPEG2000.WideQuant.Plane) (nl : Nat) :
    Run (JPEG2000.WideDWT97.idwt97 L q nl)
      (wideBudget p (min (rectArea q.rect) L.maxWorkSamples) (min nl L.maxDecompLevels)) := by
  by_cases hd : nl ≤ L.maxDecompLevels
  · by_cases ha : rectArea q.rect ≤ L.maxWorkSamples
    · simp only [Nat.min_eq_left hd,Nat.min_eq_left ha]
      simp only [JPEG2000.WideDWT97.idwt97,Limits.check,Limits.checkLe,Limits.bound,hd,ha,
        ite_true, bind,pure,Except.bind,Except.pure]
      split
      · exact early ..
      · split
        · exact early ..
        · rename_i heavy
          obtain ⟨w,h⟩ := admittedAxes q.rect (by omega)
          let s := synth97 p q.samples.toArray q.rect.width q.rect (rectArea q.rect) w h (Nat.le_refl _) nl
          let samples : Vector Int (rectArea q.rect) := ⟨s.value, by rw [s.erase]; simp⟩
          exact ⟨.ok ⟨q.rect,samples⟩,4*p.visit+s.visits, by
            congr 2
            exact Vector.toArray_inj.mp s.erase, by
            have := s.bounded; unfold wideBudget; unfold base at this; omega⟩
    · simp only [JPEG2000.WideDWT97.idwt97,Limits.check,Limits.checkLe,Limits.bound,hd,ha,
        ite_true,ite_false,bind,Except.bind]
      exact early ..
  · simp only [JPEG2000.WideDWT97.idwt97,Limits.check,Limits.checkLe,Limits.bound,hd,
      ite_false,bind,Except.bind]
    exact early ..

end JPEG2000.Spec.Resources.WaveletCost
