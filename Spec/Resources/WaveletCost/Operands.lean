import Spec.Resources.WideArithmetic

/-!
# Operand widths at synthesis sites (Plan.md §§4, 5.4, 7; T.800 F.3.6–F.3.8)

Each theorem takes the original coefficient bound and the remaining recursion depth
at a resolution. Thus it applies at any recursive call, with the original stride.
Both the horizontal input and the vertical input are the actual materialised values.
-/

namespace JPEG2000.Spec.Resources.WaveletCost

open JPEG2000.Header (Rect)
open WideArithmetic (Fits RasterFits)

private theorem widen {x : Int} {a b : Nat} (h : Fits a x) (ab : a ≤ b) : Fits b x :=
  Nat.le_trans h (Nat.pow_le_pow_right (by decide) ab)

private theorem get {xs : Array Int} {b : Nat} (h : RasterFits b xs) (i : Nat) :
    Fits b (xs.getD i 0) := by
  rw [Array.getD_eq_getD_getElem?]
  cases he : xs[i]? with
  | none => exact Nat.zero_le _
  | some x => exact h _ (Array.mem_of_getElem? he)

private theorem tabFits {n b : Nat} {f : Fin n → Int} (h : ∀ i, Fits b (f i)) :
    RasterFits b (Array.ofFn f) := by
  intro x hx; obtain ⟨i,rfl⟩ := Array.mem_ofFn.mp hx; exact h i

/-- The interleaving read used by both wide synthesis recursions. -/
abbrev detailRead (xs ll : Array Int) (stride : Nat) (r : Rect) (x y : Nat) :=
  let low := DWT53.halfRect r
  let col := DWT53.srcIdx r.x0 low.width x
  let row := DWT53.srcIdx r.y0 low.height y
  if (r.x0+x)%2=0 ∧ (r.y0+y)%2=0 then ll.getD (row*low.width+col) 0
  else xs.getD (row*stride+col) 0

private theorem interleaveFits {xs ll : Array Int} {a b : Nat}
    (hp : RasterFits a xs) (hl : RasterFits b ll) (ab : a ≤ b) (stride : Nat) (r : Rect) (x y : Nat) :
    Fits b (detailRead xs ll stride r x y) := by
  unfold detailRead; split
  · exact get hl _
  · exact widen (get hp _) ab

/-- The operands of either F-5 or F-6 at a reflected position, including the
biased dividend, quotient and result. -/
def Pass53Fits (B : Nat) (upd : Bool) (n i : Nat) (f : Nat → Int) :=
  let z := f (DWT53.lnb i)+f (DWT53.rnb n i)
  Fits B (f i) ∧ Fits B z ∧ Fits B (z+2) ∧ Fits B ((z+2)/4) ∧
    Fits B (z/2) ∧ Fits B (DWT53.passVal upd n f i)

/-- Complete line allowance, including the short-line result and both stages of
the nested reversible lift. -/
def Axis53Fits (B a n : Nat) (f : Nat → Int) : Prop :=
  ∀ i, Fits B (WideReversible.lift a n f i) ∧ Pass53Fits B true n i f ∧
    Pass53Fits B false n i (fun k => if (a+k)%2=0 then DWT53.passVal true n f k else f k)

private theorem passFits {b B : Nat} (hB : b+3 ≤ B) {f : Nat → Int} (h : ∀ i, Fits b (f i))
    (upd : Bool) (n i : Nat) : Pass53Fits B upd n i f := by
  obtain ⟨s,biased,q,q',out⟩ := WideArithmetic.pass53_operands (n := n) (k := i) h upd
  exact ⟨widen (h i) (by omega), widen s (by omega), widen biased (by omega), widen q (by omega),
    widen q' (by omega), widen out hB⟩

private theorem axis53 {b B : Nat} (hB : b+6 ≤ B) (a n : Nat) {f : Nat → Int} (h : ∀ i, Fits b (f i)) :
    Axis53Fits B a n f := by
  intro i
  refine ⟨widen (WideArithmetic.lift53 a n i f h) hB,passFits (by omega) h _ _ _,
    passFits (b := b+3) (by omega) (fun k => ?_) _ _ _⟩
  split
  · exact (WideArithmetic.pass53_operands (n := n) (k := k) h true).2.2.2.2
  · exact widen (h _) (by omega)

/-- Both actual synthesis-axis operand domains at a resolution with n coarser levels. -/
def Level53Fits (B : Nat) (xs : Array Int) (stride : Nat) (r : Rect) (n : Nat) : Prop :=
    let ll := JPEG2000.WideReversible.synthesize xs stride (DWT53.halfRect r) n
    let read := detailRead xs ll stride r
    let rows := WideReversible.raster r.width r.height fun x y =>
      WideReversible.lift r.x0 r.width (fun k => read k y) x
    (∀ y, Axis53Fits B r.x0 r.width (fun k => read k y)) ∧
    (∀ x, Axis53Fits B r.y0 r.height (fun k => rows.getD (k*r.width+x) 0))

/-- Both axes at every level of wide reversible synthesis fit the same exponent
that prices its integer arrays. This covers recomputation of reflected neighbours. -/
theorem operands53 {b : Nat} {xs : Array Int} (input : RasterFits b xs) (r : Rect) (stride n B : Nat)
    (limit : b+12*(n+1) ≤ B) : Level53Fits B xs stride r n := by
  unfold Level53Fits
  dsimp only
  have ll := WideArithmetic.synthesis53 input stride (DWT53.halfRect r) n
  have read := interleaveFits input ll (by omega) stride r
  have rows := tabFits (n := r.width*r.height) fun i =>
    WideArithmetic.lift53 r.x0 r.width (i.val%r.width) _ (fun k => read k (i.val/r.width))
  exact ⟨fun y => axis53 (by omega) _ _ (fun k => read k y),
    fun x => axis53 (by omega) _ _ (fun k => get rows (k*r.width+x))⟩

/-- The exact signed multiplier and divisor of this Table F.4 update. -/
private def factors : JPEG2000.WideDWT97.Step → Bool → Int × Int
  | .scale, true => (JPEG2000.WideDWT97.kNum,JPEG2000.WideDWT97.unit)
  | .scale, false => (JPEG2000.WideDWT97.unit,JPEG2000.WideDWT97.kNum)
  | .lift _ num, _ => (num,JPEG2000.WideDWT97.unit)

/-- Actual fixed-point operands, including the biased numerator before floor
division. Inactive parities satisfy the same ceiling. -/
def StepFits (B : Nat) (s : JPEG2000.WideDWT97.Step) (even : Bool) (x u v : Int) : Prop :=
  let (num,den) := factors s even
  let arg := match s with | .scale => x | .lift .. => u+v
  Fits B num ∧ Fits B den ∧ Fits B x ∧ Fits B u ∧ Fits B v ∧ Fits B (u+v) ∧
    Fits B (num*arg) ∧ Fits B (den/2) ∧ Fits B (num*arg+den/2) ∧
    Fits B (JPEG2000.WideDWT97.product num den arg) ∧ Fits B (s.cell even x (fun _ => u+v))

private theorem stepFits {b B : Nat} {s : JPEG2000.WideDWT97.Step} (hs : s ∈ JPEG2000.WideDWT97.steps)
    (par : Bool) {x u v : Int} (hx : Fits b x) (hu : Fits b u) (hv : Fits b v) (hB : b+54 ≤ B) :
    StepFits B s par x u v := by
  have h := WideArithmetic.step97_operands hs par hx hu hv
  cases s <;> cases par <;> dsimp only [StepFits,factors,Bool.false_eq_true,Bool.true_eq,ite_false,ite_true] at *
  all_goals
    obtain ⟨num,den,sum,_,mul,half,bias,quot,out⟩ := h
    exact ⟨widen num (by omega),widen den (by omega),widen hx (by omega),widen hu (by omega),
      widen hv (by omega),widen sum (by omega),widen mul (by omega),widen half (by omega),
      widen bias (by omega),widen quot (by omega),widen out hB⟩

/-- All input, output, and pre-rounded operands in every prefix of a 9/7 line. -/
def Axis97Fits (B a n : Nat) (f : Nat → Int) : Prop :=
  (∀ i, Fits B (f i)) ∧ RasterFits B (JPEG2000.WideDWT97.line a n f) ∧
    ∀ pre s post, JPEG2000.WideDWT97.steps = pre ++ s :: post → ∀ i : Fin n,
      let xs := JPEG2000.WideDWT97.passes a n pre (Array.ofFn (fun j : Fin n => f j.val))
      StepFits B s ((a+i.val)%2 == 0) (xs.getD i.val 0)
        (xs.getD (DWT53.lnb i.val) 0) (xs.getD (DWT53.rnb n i.val) 0)

private theorem axis97 {b B : Nat} (hB : b+270 ≤ B) (a n : Nat) {f : Nat → Int}
    (h : ∀ i, Fits b (f i)) : Axis97Fits B a n f := by
  have init := tabFits (n := n) fun i => h i.val
  refine ⟨fun i => widen (h _) (by omega), ?_, ?_⟩
  · unfold JPEG2000.WideDWT97.line
    split
    · apply tabFits; intro i; split
      · exact widen (h _) (by omega)
      · exact Nat.le_trans (Int.natAbs_ediv_le_natAbs _ _) (widen (h _) (by omega))
    · have bound := WideArithmetic.passes97 a n _ (fun _ hs => hs) init
      exact fun x hx => widen (bound x hx) hB
  · intro pre s post eq i
    have len := congrArg List.length eq
    change 5 = _ at len
    simp only [List.length_append,List.length_cons] at len
    have inside : ∀ t ∈ pre, t ∈ JPEG2000.WideDWT97.steps := by
      intro t ht; rw [eq]; exact List.mem_append_left _ ht
    have hs : s ∈ JPEG2000.WideDWT97.steps := by rw [eq]; simp
    have bound := WideArithmetic.passes97 a n pre inside init
    exact stepFits hs _ (get bound _) (get bound _) (get bound _) (by omega)

private theorem linesRead {a n count b : Nat} {f : Nat → Nat → Int}
    (h : ∀ y, RasterFits b (JPEG2000.WideDWT97.line a n (f y))) (i k : Nat) :
    Fits b (JPEG2000.WideDWT97.atLine (JPEG2000.WideDWT97.lines a n count f) i k) := by
  apply get
  unfold JPEG2000.WideDWT97.lines
  split
  · simp [RasterFits]
  · rw [Array.getD_eq_getD_getElem?]
    cases he : (Array.ofFn (n := count) fun j => JPEG2000.WideDWT97.line a n (f j))[i]? with
    | none => exact fun _ hx => by simp at hx
    | some xs =>
      obtain ⟨y,rfl⟩ := Array.mem_ofFn.mp (Array.mem_of_getElem? he)
      exact h y

/-- Both actual synthesis-axis operand domains at a resolution with n coarser levels. -/
def Level97Fits (B : Nat) (xs : Array Int) (stride : Nat) (r : Rect) (n : Nat) : Prop :=
    let ll := JPEG2000.WideDWT97.synthesize xs stride (DWT53.halfRect r) n
    let read := fun y x => detailRead xs ll.toArray stride r x y
    let rows := JPEG2000.WideDWT97.lines r.x0 r.width r.height read
    (∀ y, Axis97Fits B r.x0 r.width (read y)) ∧
    (∀ x, Axis97Fits B r.y0 r.height (fun k => JPEG2000.WideDWT97.atLine rows k x))

set_option maxRecDepth 2048 in
/-- Both actual axis inputs and every 9/7 prefix's products and rounding operands.
At a recursive level with n coarser levels the two axes consume at most 540 extra
exponent bits per level, starting at the dequantised coefficient exponent b. -/
theorem operands97 {b : Nat} {xs : Array Int} (input : RasterFits b xs) (r : Rect) (stride n B : Nat)
    (limit : b+540*(n+1) ≤ B) : Level97Fits B xs stride r n := by
  rw [Nat.mul_succ] at limit
  have rowLimit : b+540*n+270 ≤ B := Nat.le_trans (by omega) limit
  have colLimit : b+540*n+270+270 ≤ B := Nat.le_trans (by omega) limit
  unfold Level97Fits
  dsimp only
  have ll := WideArithmetic.synthesis97 input stride (DWT53.halfRect r) n
  have read := interleaveFits input ll (by omega) stride r
  have row y := axis97 (B := b+540*n+270) (Nat.le_refl _) r.x0 r.width (fun k => read k y)
  exact ⟨fun y => axis97 rowLimit _ _ (fun k => read k y), fun x => axis97 colLimit _ _
    (fun k => linesRead (fun y => (row y).2.1) k x)⟩

end JPEG2000.Spec.Resources.WaveletCost
