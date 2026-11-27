import Spec.NativePlacement.Allocation
import Spec.WideHeaderBounds
import JPEG2000.WideDWT97
import Spec.WideICT
import JPEG2000.TileDispatch

/-!
# Operand widths in checked-wide reconstruction

Plan.md §§3–5, 7 (S3). T.800 B.10, E.1.1.2, H.2, F.3 and G.2–G.3.
An exponent bound `b` means absolute value at most `2^b`, hence at most
`b+1` magnitude bits plus a sign. We deliberately charge the entire pre-division
numerator to each lifting pass, even when its rounded quotient is much smaller.
All raster bounds are on the centred, unclamped integers at their working scale.

`quant_operands` and `coefficient_width` accept arbitrary Tier-1 magnitude and last-plane
ceilings. `pass53_operands` and `step97_operands` account for the divisions inside
lifting. `synthesis53` and `synthesis97` propagate these budgets through both axes
and the recursively reconstructed LL. `parsed_spatial` follows retries through the
pre-colour dispatcher. `parsed_tile` bounds each native source read after optional
colour transformation. S3 separately requires allocation and operation counts.
-/

namespace JPEG2000.Spec.Resources.WideArithmetic

open JPEG2000.Tier2.Geometry (rectArea Band)
open JPEG2000.Tier1.WidePlain (Cell)
open JPEG2000.WideReversible (raster lift)
open JPEG2000.WideDWT97 (product unit kNum)

/-- Upper exponent of a signed sample or intermediate, including negative floor rounding. -/
abbrev Fits (b : Nat) (x : Int) : Prop := x.natAbs ≤ 2 ^ b

/-- All stored samples have bounded magnitude. -/
def RasterFits (b : Nat) (xs : Array Int) : Prop := ∀ x ∈ xs, Fits b x

private theorem mono {a b : Nat} {x : Int} (hx : Fits a x) (h : a ≤ b) : Fits b x :=
  Nat.le_trans hx (Nat.pow_le_pow_right (by decide) h)

private theorem zeroFits (b : Nat) : Fits b 0 := Nat.zero_le _

private theorem addFits {b : Nat} {x y : Int} (hx : Fits b x) (hy : Fits b y) :
    Fits (b+1) (x+y) := by
  unfold Fits at *
  have := Int.natAbs_add_le x y
  rw [Nat.pow_succ]
  omega

private theorem subFits {b : Nat} {x y : Int} (hx : Fits b x) (hy : Fits b y) :
    Fits (b+1) (x-y) := by
  unfold Fits at *
  have := Int.natAbs_sub_le x y
  rw [Nat.pow_succ]
  omega

private theorem divFits {b : Nat} {x : Int} (hx : Fits b x) (d : Int) : Fits b (x/d) :=
  Nat.le_trans (Int.natAbs_ediv_le_natAbs _ _) hx

private theorem mulFits {a b : Nat} {x y : Int} (hx : Fits a x) (hy : Fits b y) :
    Fits (a+b) (x*y) := by
  unfold Fits at *
  rw [Int.natAbs_mul, Nat.pow_add]
  exact Nat.mul_le_mul hx hy

private theorem ofFnFits {n b : Nat} {f : Fin n → Int} (h : ∀ i, Fits b (f i)) :
    RasterFits b (Array.ofFn f) := by
  intro x hx
  obtain ⟨i, rfl⟩ := Array.mem_ofFn.mp hx
  exact h i

private theorem getFits {b : Nat} {xs : Array Int} (h : RasterFits b xs) (i : Nat) :
    Fits b (xs.getD i 0) := by
  rw [Array.getD_eq_getD_getElem?]
  cases e : xs[i]? with
  | none => exact zeroFits _
  | some x => exact h _ (Array.mem_of_getElem? e)

private theorem rasterMono {a b : Nat} {xs : Array Int} (h : RasterFits a xs) (le : a ≤ b) :
    RasterFits b xs := fun _ hx => mono (h _ hx) le

private theorem rasterFits {b w h : Nat} {f : Nat → Nat → Int} (hf : ∀ x y, Fits b (f x y)) :
    RasterFits b (raster w h f) := ofFnFits fun _ => hf _ _

/-- Turn an exponent estimate into a magnitude-bit budget (including zero). -/
theorem magnitude_bits {b : Nat} {x : Int} (h : Fits b x) : x.natAbs.log2 + 1 ≤ b + 1 := by
  by_cases hz : x.natAbs = 0
  · simp [hz]
  have hp := Nat.log2_self_le hz
  have le := Nat.le_log2 (Nat.ne_of_gt (Nat.two_pow_pos b)) |>.2 (Nat.le_trans hp h)
  rw [Nat.log2_two_pow] at le
  omega

/-! ## ROI and dequantisation -/

/-- One bound for the shift threshold, midpoint, scale, numerator with rounding bias,
divisor and signed result. `m` bounds the *value* of the input magnitude, `l` the
last-plane index. The extra unit makes this applicable to zero cells too. -/
def quantLimit (m l r f e mu s : Nat) : Nat :=
  (2*m + 2^l + 1) * ((2048+mu) * 2^(r+f)) + 2^(e+12) + 2^s

/-- Explicit operands computed by H.2 and E.1, including the unrounded and biased
products. The signed reconstruction applies the sign after the magnitude rounding. -/
def QuantOperands (q : Quant.BandQuant) (f : Nat) (c : Cell) (B : Nat) : Prop :=
  let ml := JPEG2000.WideQuant.unshift q.roiShift c
  let m := ml.1
  let l := ml.2
  let scale := (2048+q.mantissa)*2^(q.range+f)
  let d := (2 : Int)^(q.exponent+12)
  let t := (2*m+2^l)*scale
  2^q.roiShift ≤ B ∧ c.mag ≤ B ∧ c.lsbPlane ≤ B ∧ m ≤ B ∧ l ≤ B ∧
    2^l ≤ B ∧ m+2^l/2 ≤ B ∧ 2*m+2^l ≤ B ∧ scale ≤ B ∧ t ≤ B ∧
    d.natAbs ≤ B ∧ (d/2).natAbs ≤ B ∧ ((t : Int)+d/2).natAbs ≤ B ∧
    (JPEG2000.WideQuant.magnitude q f m l).natAbs ≤ B ∧
    (JPEG2000.WideQuant.prepare q f c).natAbs ≤ B

/-- The wide dequantiser is bounded directly from the two Tier-1 cell invariants.
The parameter maxima may be shared by every block accumulated in a Mallat plane. -/
theorem quant_operands {q : Quant.BandQuant} {f : Nat} {c : Cell}
    {M P R F E U S : Nat} (hm : c.mag ≤ M) (hp : c.lsbPlane ≤ P)
    (hr : q.range ≤ R) (hf : f ≤ F) (he : q.exponent ≤ E)
    (hu : q.mantissa ≤ U) (hs : q.roiShift ≤ S) :
    QuantOperands q f c (quantLimit M P R F E U S) := by
  let ml := JPEG2000.WideQuant.unshift q.roiShift c
  have reduced : ml.1 ≤ c.mag ∧ ml.2 ≤ c.lsbPlane := by
    dsimp [ml, JPEG2000.WideQuant.unshift]
    split
    · exact ⟨by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_le_self .., Nat.sub_le ..⟩
    · exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  let scale := (2048+q.mantissa)*2^(q.range+f)
  let maxScale := (2048+U)*2^(R+F)
  let n := 2*ml.1+2^ml.2
  let cap := 2*M+2^P+1
  let d := (2 : Int)^(q.exponent+12)
  let B := quantLimit M P R F E U S
  have pw {i j : Nat} (h : i ≤ j) : 2^i ≤ 2^j := Nat.pow_le_pow_right (by decide) h
  have hpow := pw (Nat.le_trans reduced.2 hp)
  have hscale : scale ≤ maxScale := Nat.mul_le_mul (by omega) (pw (by omega))
  have posScale : 1 ≤ maxScale := Nat.mul_pos (by omega) (Nat.two_pow_pos _)
  have hn : n ≤ cap := by dsimp [n,cap]; omega
  have hcap : cap ≤ cap*maxScale := by simpa using Nat.mul_le_mul_left cap posScale
  have hbase : maxScale ≤ cap*maxScale := by
    have hc : 1 ≤ cap := by simp [cap]
    simpa using Nat.mul_le_mul_right maxScale hc
  have hmul := Nat.mul_le_mul hn hscale
  have hd : d.natAbs ≤ 2^(E+12) := by simpa [d] using pw (Nat.add_le_add_right he 12)
  have hhalf := Int.natAbs_ediv_le_natAbs d 2
  have hsum := Int.natAbs_add_le (↑(n*scale)) (d/2)
  simp only [Int.natAbs_natCast] at hsum
  have hroi := pw hs
  have hplane := Nat.lt_two_pow_self (n := P)
  have hcapB : cap ≤ B := Nat.le_trans hcap (Nat.le_trans (Nat.le_add_right ..) (Nat.le_add_right ..))
  have hmulB : cap*maxScale ≤ B := Nat.le_trans (Nat.le_add_right ..) (Nat.le_add_right ..)
  have hdB : 2^(E+12) ≤ B := Nat.le_trans (Nat.le_add_left ..) (Nat.le_add_right ..)
  have hsB : 2^S ≤ B := Nat.le_add_left ..
  have hraw : ((↑(n*scale) : Int)+d/2).natAbs ≤ B :=
    Nat.le_trans hsum (Nat.le_trans (Nat.add_le_add hmul (Nat.le_trans hhalf hd)) (Nat.le_add_right ..))
  have hmag : (JPEG2000.WideQuant.magnitude q f ml.1 ml.2).natAbs ≤ B := by
    unfold JPEG2000.WideQuant.magnitude
    split
    · simp only [Int.natAbs_natCast]
      dsimp only [cap, n] at hcapB hn
      omega
    · exact Nat.le_trans (Int.natAbs_ediv_le_natAbs _ _) hraw
  have hprep : (JPEG2000.WideQuant.prepare q f c).natAbs ≤ B := by
    unfold JPEG2000.WideQuant.prepare
    cases h : JPEG2000.WideQuant.unshift q.roiShift c with
    | mk m l =>
      simp only [ml, h] at hmag
      dsimp only
      split <;> try exact Nat.zero_le _
      split <;> try exact Nat.zero_le _
      split <;> simpa only [Int.natAbs_neg] using hmag
  change 2^q.roiShift ≤ B ∧ c.mag ≤ B ∧ c.lsbPlane ≤ B ∧ ml.1 ≤ B ∧ ml.2 ≤ B ∧
    2^ml.2 ≤ B ∧ ml.1+2^ml.2/2 ≤ B ∧ n ≤ B ∧ scale ≤ B ∧ n*scale ≤ B ∧
    d.natAbs ≤ B ∧ (d/2).natAbs ≤ B ∧ _ ∧ _ ∧ _
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, by omega, by omega, by omega,
    by omega, by omega, hraw, hmag, hprep⟩ <;> dsimp only [cap,n] at hn hcapB <;> omega

/-! ## Reversible lifting -/

/-- F-5 and F-6 neighbour sum, biased update dividend, quotients and actual pass result. -/
theorem pass53_operands {b n k : Nat} {g : Nat → Int} (h : ∀ i, Fits b (g i)) (upd : Bool) :
    let s := g (DWT53.lnb k) + g (DWT53.rnb n k)
    Fits (b+1) s ∧ Fits (b+2) (s+2) ∧ Fits (b+2) ((s+2)/4) ∧
      Fits (b+1) (s/2) ∧ Fits (b+3) (DWT53.passVal upd n g k) := by
  dsimp only
  have sum := addFits (h (DWT53.lnb k)) (h (DWT53.rnb n k))
  have biased := addFits sum (mono (by decide : Fits 1 2) (by omega))
  refine ⟨sum, biased, divFits biased _, divFits sum _, ?_⟩
  cases upd
  · exact mono (addFits (mono (h k) (by omega)) (divFits sum 2)) (by omega)
  · exact subFits (mono (h k) (by omega)) (divFits biased 4)

/-- A full 5/3 line charges both passes and includes odd-origin singleton floor division. -/
theorem lift53 {b : Nat} (a n k : Nat) (g : Nat → Int) (h : ∀ i, Fits b (g i)) :
    Fits (b+6) (lift a n g k) := by
  have pass (upd : Bool) (i : Nat) := (pass53_operands (n := n) (k := i) h upd).2.2.2.2
  unfold lift
  split
  · split
    · exact mono (h k) (by omega)
    · exact mono (divFits (h k) 2) (by omega)
  · let e := fun i => if (a+i)%2 = 0 then DWT53.passVal true n g i else g i
    have ev (i : Nat) : Fits (b+3) (e i) := by
      dsimp [e]
      split
      · exact pass true i
      · exact mono (h i) (by omega)
    split
    · exact mono (ev k) (by omega)
    · exact (pass53_operands (n := n) (k := k) ev false).2.2.2.2

/-- Each 5/3 axis uses at most two passes. Coarser LL and original detail reads
remain bounded at the next resolution for arbitrary grid origins and empty rectangles. -/
theorem synthesis53 {b : Nat} {xs : Array Int} (h : RasterFits b xs) (stride : Nat)
    (r : Header.Rect) (nl : Nat) :
    RasterFits (b+12*nl) (JPEG2000.WideReversible.synthesize xs stride r nl) := by
  induction nl generalizing r with
  | zero => exact rasterFits fun _ _ => getFits h _
  | succ n ih =>
    let low := DWT53.halfRect r
    have coarse := ih low
    have read (x y : Nat) : Fits (b+12*n)
        (if (r.x0+x)%2 = 0 ∧ (r.y0+y)%2 = 0 then
          (JPEG2000.WideReversible.synthesize xs stride low n).getD
            (DWT53.srcIdx r.y0 low.height y * low.width + DWT53.srcIdx r.x0 low.width x) 0
         else xs.getD (DWT53.srcIdx r.y0 low.height y * stride + DWT53.srcIdx r.x0 low.width x) 0) := by
      split
      · exact getFits coarse _
      · exact mono (getFits h _) (by omega)
    have rows := rasterFits (w := r.width) (h := r.height)
      fun x y => lift53 r.x0 r.width x _ (fun k => read k y)
    exact rasterFits fun x y => mono
      (lift53 r.y0 r.height y _ (fun k => getFits rows (k*r.width+x))) (by omega)

/-! ## Fixed-point lifting -/

/-- F-7 rounded multiplication, bounding the multiplication, the divisor's half,
the biased pre-division numerator and the quotient (even for negative products). -/
theorem product_operands {b : Nat} {num den x : Int}
    (hn : Fits 51 num) (hd : Fits 51 den) (hx : Fits b x) :
    Fits (b+51) (num*x) ∧ Fits 51 (den/2) ∧ Fits (b+52) (num*x+den/2) ∧
      Fits (b+52) (product num den x) := by
  have m := mono (mulFits hn hx) (by omega : 51+b ≤ b+51)
  have half := divFits hd 2
  have biased := addFits m (mono half (by omega))
  exact ⟨m, half, biased, divFits biased den⟩

private theorem liftNumerator {p : Bool} {n : Int}
    (h : JPEG2000.WideDWT97.Step.lift p n ∈ JPEG2000.WideDWT97.steps) : Fits 51 n := by
  simp [JPEG2000.WideDWT97.steps] at h
  rcases h with h | h | h | h <;> obtain ⟨_, rfl⟩ := h <;> decide

private theorem step97 {b : Nat} {s : JPEG2000.WideDWT97.Step}
    (hs : s ∈ JPEG2000.WideDWT97.steps) (parity : Bool) {x u v : Int}
    (hx : Fits b x) (hu : Fits b u) (hv : Fits b v) :
    Fits (b+54) (s.cell parity x (fun _ => u+v)) := by
  have hd : Fits 51 unit := by decide
  have hk : Fits 51 kNum := by decide
  have adj := addFits hu hv
  cases s with
  | scale =>
    simp only [JPEG2000.WideDWT97.Step.cell]
    split
    · exact mono (product_operands (b := b) hk hd hx).2.2.2 (by omega)
    · exact mono (product_operands (b := b) hd hk hx).2.2.2 (by omega)
  | lift even num =>
    have hn := liftNumerator hs
    simp only [JPEG2000.WideDWT97.Step.cell]
    split
    · exact addFits (mono hx (by omega : b ≤ b+53)) (product_operands (b := b+1) hn hd adj).2.2.2
    · exact mono hx (by omega)

/-- The actual Table F.4 multipliers and divisors, and every value entering a
cell update. The adjacent sum is bounded even on inactive parities. -/
theorem step97_operands {b : Nat} {s : JPEG2000.WideDWT97.Step}
    (hs : s ∈ JPEG2000.WideDWT97.steps) (even : Bool) {x u v : Int}
    (hx : Fits b x) (hu : Fits b u) (hv : Fits b v) :
    let (num, den, arg) := match s with
      | .scale => if even then (kNum,unit,x) else (unit,kNum,x)
      | .lift _ n => (n,unit,u+v)
    Fits 51 num ∧ Fits 51 den ∧ Fits (b+1) (u+v) ∧ Fits (b+1) arg ∧
      Fits (b+52) (num*arg) ∧ Fits 51 (den/2) ∧ Fits (b+53) (num*arg+den/2) ∧
      Fits (b+53) (product num den arg) ∧ Fits (b+54) (s.cell even x (fun _ => u+v)) := by
  have cell := step97 hs even hx hu hv
  have adj := addFits hu hv
  have prod {n d z : Int} (hn : Fits 51 n) (hd : Fits 51 d) (hz : Fits (b+1) z) :=
    product_operands hn hd hz
  have hd : Fits 51 unit := by decide
  have hk : Fits 51 kNum := by decide
  have harg := mono hx (by omega : b ≤ b+1)
  cases s with
  | scale =>
    cases even
    · obtain ⟨m,d,z,q⟩ := prod hd hk harg
      exact ⟨hd,hk,adj,harg,m,d,z,q,cell⟩
    · obtain ⟨m,d,z,q⟩ := prod hk hd harg
      exact ⟨hk,hd,adj,harg,m,d,z,q,cell⟩
  | lift p n =>
    have hn := liftNumerator hs
    obtain ⟨m,d,z,q⟩ := prod hn hd adj
    exact ⟨hn,hd,adj,adj,m,d,z,q,cell⟩

/-- Every prefix (or subsequence) of the five actual F-7 passes on a line satisfies
the same per-pass allowance. Reflected reads and the two-neighbour sum are covered
by `getFits`, `addFits` and `product_operands`. -/
theorem passes97 (a n : Nat) (ss : List JPEG2000.WideDWT97.Step)
    (hs : ∀ s ∈ ss, s ∈ JPEG2000.WideDWT97.steps) {b : Nat} {xs : Array Int}
    (h : RasterFits b xs) :
    RasterFits (b+54*ss.length) (JPEG2000.WideDWT97.passes a n ss xs) := by
  induction ss generalizing b xs with
  | nil => exact h
  | cons s ss ih =>
    have step := ofFnFits (n := n) fun i =>
      step97 (hs s (by simp)) ((a+i.val)%2 == 0)
        (getFits h i.val) (getFits h (DWT53.lnb i.val)) (getFits h (DWT53.rnb n i.val))
    apply rasterMono (ih (fun t ht => hs t (by simp [ht])) step)
    simp only [List.length_cons]; omega

private theorem line97 {b : Nat} (a n : Nat) (read : Nat → Int) (h : ∀ i, Fits b (read i)) :
    RasterFits (b+270) (JPEG2000.WideDWT97.line a n read) := by
  unfold JPEG2000.WideDWT97.line
  split
  · apply ofFnFits
    intro i
    split
    · exact mono (h i) (by omega)
    · exact mono (divFits (h i) 2) (by omega)
  · exact passes97 a n _ (fun _ hs => hs) (ofFnFits fun i => h i)

private theorem lines97 {b : Nat} (a n count : Nat) (read : Nat → Nat → Int)
    (h : ∀ i k, Fits b (read i k)) (i k : Nat) :
    Fits (b+270) (JPEG2000.WideDWT97.atLine (JPEG2000.WideDWT97.lines a n count read) i k) := by
  unfold JPEG2000.WideDWT97.lines JPEG2000.WideDWT97.atLine
  apply getFits
  split
  · simp [RasterFits]
  · rw [Array.getD_eq_getD_getElem?]
    cases he : (Array.ofFn (n := count) fun j => JPEG2000.WideDWT97.line a n (read j))[i]? with
    | none => exact fun _ hx => by simp at hx
    | some row =>
      obtain ⟨j, rfl⟩ := Array.mem_ofFn.mp (Array.mem_of_getElem? he)
      exact line97 _ _ _ (h j)

/-- Five passes per axis and two axes per resolution, with the full fixed-point
numerators charged at each pass. This bounds centred spatial samples before ICT. -/
theorem synthesis97 {b : Nat} {xs : Array Int} (h : RasterFits b xs) (stride : Nat)
    (r : Header.Rect) (nl : Nat) :
    RasterFits (b+540*nl) (JPEG2000.WideDWT97.synthesize xs stride r nl).toArray := by
  induction nl generalizing r with
  | zero =>
    rw [JPEG2000.WideDWT97.synthesize]
    exact rasterFits (w := r.width) (h := r.height) fun x y => getFits h (y*stride+x)
  | succ n ih =>
    rw [JPEG2000.WideDWT97.synthesize]
    let low := DWT53.halfRect r
    have coarse := ih low
    have read (y x : Nat) : Fits (b+540*n)
        (if (r.x0+x)%2 = 0 ∧ (r.y0+y)%2 = 0 then
          (JPEG2000.WideDWT97.synthesize xs stride low n).toArray.getD
            (DWT53.srcIdx r.y0 low.height y * low.width + DWT53.srcIdx r.x0 low.width x) 0
         else xs.getD (DWT53.srcIdx r.y0 low.height y * stride + DWT53.srcIdx r.x0 low.width x) 0) := by
      split
      · exact getFits coarse _
      · exact mono (getFits h _) (by omega)
    have rows := lines97 r.x0 r.width r.height _ read
    have cols := lines97 r.y0 r.height r.width _ (fun x y => rows y x)
    exact rasterFits fun x y => mono (cols x y) (by omega)

/-! ## Checked synthesis and colour kernels -/

/-- Pre-MCT raster returned by the checked 5/3 transform, including zero levels. -/
theorem idwt53_bounds {L : Limits} {r : Header.Rect} {xs ys : Array Int} {b nl : Nat}
    (h : RasterFits b xs) (ok : JPEG2000.WideReversible.idwt53 L r nl xs = .ok ys) :
    RasterFits (b+12*nl) ys := by
  unfold JPEG2000.WideReversible.idwt53 at ok
  obtain ⟨_, _, ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨_, _, ok⟩ := Tier2Equiv.bind_ok ok
  split at ok <;> try contradiction
  split at ok <;> cases ok
  · exact rasterMono h (by omega)
  · exact synthesis53 h r.width r nl

/-- Pre-MCT raster returned by the checked 9/7 transform, including empty grids. -/
theorem idwt97_bounds {L : Limits} {p q : JPEG2000.WideQuant.Plane} {b nl : Nat}
    (h : RasterFits b p.samples.toArray) (ok : JPEG2000.WideDWT97.idwt97 L p nl = .ok q) :
    RasterFits (b+540*nl) q.samples.toArray := by
  unfold JPEG2000.WideDWT97.idwt97 at ok
  obtain ⟨_, _, ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨_, _, ok⟩ := Tier2Equiv.bind_ok ok
  dsimp only at ok
  split at ok <;> try contradiction
  split at ok <;> cases ok
  · exact rasterMono h (by omega)
  · exact synthesis97 h p.rect.width p.rect nl

/-- G.2 neighbour sum, its floor quotient, and the actual G, R, B sample expressions. -/
theorem rct_operands {b : Nat} {y cb cr : Int} (hy : Fits b y) (hb : Fits b cb) (hr : Fits b cr) :
    let s := cr+cb
    let g := y-s/4
    Fits (b+1) s ∧ Fits (b+1) (s/4) ∧ Fits (b+2) g ∧
      Fits (b+3) (cr+g) ∧ Fits (b+3) (cb+g) := by
  have s := addFits hr hb
  have d := divFits s 4
  have g := subFits (mono hy (by omega)) d
  exact ⟨s, d, g, addFits (mono hr (by omega)) g, addFits (mono hb (by omega)) g⟩

private theorem zipAddFits {b : Nat} {xs ys : Array Int}
    (hx : RasterFits b xs) (hy : RasterFits b ys) :
    RasterFits (b+1) (Array.zipWith (·+·) xs ys) := by
  intro z hz
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hz
  rw [Array.getElem_zipWith]
  exact addFits (hx _ (Array.getElem_mem _)) (hy _ (Array.getElem_mem _))

/-- All three actual RCT arrays before sample rounding and DC shift. -/
theorem rct_bounds {L : Limits} {r s t : Header.Rect} {y cb cr : Array Int}
    {o : Array Int × Array Int × Array Int} {b : Nat}
    (hy : RasterFits b y) (hb : RasterFits b cb) (hr : RasterFits b cr)
    (ok : JPEG2000.WideReversible.rctInverse L r s t y cb cr = .ok o) :
    RasterFits (b+3) o.1 ∧ RasterFits (b+2) o.2.1 ∧ RasterFits (b+3) o.2.2 := by
  unfold JPEG2000.WideReversible.rctInverse at ok
  obtain ⟨_, _, ok⟩ := Tier2Equiv.bind_ok ok
  split at ok <;> try contradiction
  cases ok
  have g := ofFnFits (n := y.size) fun i =>
    (rct_operands (hy _ (Array.getElem_mem i.isLt)) (getFits hb i) (getFits hr i)).2.2.1
  exact ⟨zipAddFits (rasterMono hr (by omega)) g, g, zipAddFits (rasterMono hb (by omega)) g⟩

/-- Products, partial sums, final biased numerators, and rounded outputs for G.3.
Input exponents may differ between the three reconstructed components. -/
def ICTOperands (b : Nat) (y cb cr : Int) : Prop :=
  let l := 100000*y
  let r := l+140200*cr
  let g₁ := l-34413*cb
  let g := g₁-71414*cr
  let blue := l+177200*cb
  ∀ x ∈ [l,140200*cr,34413*cb,71414*cr,177200*cb,r,g₁,g,blue,r+50000,g+50000,blue+50000,
    JPEG2000.WideICT.red y cr, JPEG2000.WideICT.green y cb cr, JPEG2000.WideICT.blue y cb],
    Fits b x

/-- The ICT costs up to 18 exponent bits for a multiplier and three for the row sums
and bias. It covers every decimal row operand even when the component levels differ. -/
theorem ict_operands {Y C R : Nat} {y cb cr : Int} (hy : Fits Y y) (hc : Fits C cb)
    (hr : Fits R cr) : ICTOperands (max Y (max C R)+21) y cb cr := by
  let b := max Y (max C R)
  have mult {n x : Int} (hn : Fits 18 n) (hx : Fits b x) : Fits (b+18) (n*x) :=
    mono (mulFits hn hx) (by omega)
  have hy' := mono hy (show Y ≤ b from Nat.le_max_left ..)
  have hc' := mono hc (show C ≤ b by dsimp [b]; omega)
  have hr' := mono hr (show R ≤ b by dsimp [b]; omega)
  have l := mult (n := 100000) (by decide) hy'
  have r := mult (n := 140200) (by decide) hr'
  have g₁ := mult (n := 34413) (by decide) hc'
  have g₂ := mult (n := 71414) (by decide) hr'
  have bl := mult (n := 177200) (by decide) hc'
  have rs := addFits l r
  have gs := subFits l g₁
  have gt := subFits gs (mono g₂ (by omega))
  have bs := addFits l bl
  have bias := mono (by decide : Fits 16 50000) (by omega : 16 ≤ b+20)
  have rb := addFits (mono rs (by omega)) bias
  have gb := addFits gt bias
  have bb := addFits (mono bs (by omega)) bias
  have red := divFits rb 100000
  have green := divFits gb 100000
  have blue := divFits bb 100000
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst x
  · exact mono l (by omega : b+18 ≤ b+21)
  · exact mono r (by omega : b+18 ≤ b+21)
  · exact mono g₁ (by omega : b+18 ≤ b+21)
  · exact mono g₂ (by omega : b+18 ≤ b+21)
  · exact mono bl (by omega : b+18 ≤ b+21)
  · exact mono rs (by omega : b+19 ≤ b+21)
  · exact mono gs (by omega : b+19 ≤ b+21)
  · exact mono gt (by omega : b+20 ≤ b+21)
  · exact mono bs (by omega : b+19 ≤ b+21)
  · exact rb
  · exact gb
  · exact bb
  · exact red
  · exact green
  · exact blue

/-- The actual successful ICT has common binary scale, three independently bounded
inputs and three bounded output planes. Physical errors at these same samples are
given by `Spec.WideICT.ictInverse_error` for arbitrary per-plane errors. -/
theorem ict_bounds {L : Limits} {y cb cr : JPEG2000.WideICT.Component}
    {o : JPEG2000.WideICT.Component × JPEG2000.WideICT.Component × JPEG2000.WideICT.Component}
    {Y C R : Nat} (hy : RasterFits Y y.samples.toArray) (hc : RasterFits C cb.samples.toArray)
    (hr : RasterFits R cr.samples.toArray)
    (ok : JPEG2000.WideICT.ictInverse L y cb cr = .ok o) :
    let b := max Y (max C R)+21
    cb.fracBits = y.fracBits ∧ cr.fracBits = y.fracBits ∧
    RasterFits b o.1.samples.toArray ∧ RasterFits b o.2.1.samples.toArray ∧
    RasterFits b o.2.2.samples.toArray := by
  obtain ⟨_, fit, rfl⟩ := (WideICT.ictInverse_ok ..).mp ok
  let b := max Y (max C R)+21
  have red {u v : Int} (hu : Fits Y u) (hv : Fits R v) : Fits b (JPEG2000.WideICT.red u v) :=
    ict_operands hu (zeroFits C) hv _ (by simp)
  have green {u v w : Int} (hu : Fits Y u) (hv : Fits C v) (hw : Fits R w) :
      Fits b (JPEG2000.WideICT.green u v w) := ict_operands hu hv hw _ (by simp)
  have blue {u v : Int} (hu : Fits Y u) (hv : Fits C v) : Fits b (JPEG2000.WideICT.blue u v) :=
    ict_operands hu hv (zeroFits R) _ (by simp)
  refine ⟨fit.2.2.2.2.1, fit.2.2.2.2.2, ?_, ?_, ?_⟩
  · apply ofFnFits
    intro i
    exact red (hy _ (Array.getElem_mem _)) (hr _ (Array.getElem_mem _))
  · apply ofFnFits
    intro i
    exact green (hy _ (Array.getElem_mem _)) (hc _ (Array.getElem_mem _)) (hr _ (Array.getElem_mem _))
  · apply ofFnFits
    intro i
    exact blue (hy _ (Array.getElem_mem _)) (hc _ (Array.getElem_mem _))

/-! ## Code-block assembly and parsed parameter substitution -/

private theorem writeFits {n area b : Nat} (idx : Fin n → Fin area) (v : Fin n → Int)
    (hv : ∀ i, Fits b (v i)) (k : Nat) (hk : k ≤ n) (dst : Vector Int area)
    (h : RasterFits b dst.toArray) :
    RasterFits b (JPEG2000.WideQuant.writeCells idx v k hk dst).toArray := by
  induction k generalizing dst with
  | zero => exact h
  | succ k ih =>
    apply ih
    intro x hx
    rcases Array.mem_or_eq_of_mem_set (w := by rw [dst.size_toArray]; exact (idx ⟨k,hk⟩).isLt) hx with hx | rfl
    · exact h _ hx
    · exact hv _

private theorem dequantFits {L : Limits} {dst out : JPEG2000.WideQuant.Plane} {p : Header.CompParams}
    {depth reduce r f b : Nat} {band : Band} {cb : Header.Rect} {cs : Array Cell}
    (old : RasterFits b dst.samples.toArray)
    (h : ∀ c ∈ cs, Fits b (JPEG2000.WideQuant.prepare (Quant.bandQuant p depth r band) f c))
    (ok : JPEG2000.WideQuant.dequantBlock L dst p depth reduce r band cb f cs = .ok out) :
    RasterFits b out.samples.toArray := by
  unfold JPEG2000.WideQuant.dequantBlock at ok
  obtain ⟨_, _, ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨_, _, ok⟩ := Tier2Equiv.bind_ok ok
  dsimp only at ok
  split at ok <;> try contradiction
  split at ok <;> try contradiction
  split at ok <;> try contradiction
  split at ok <;> try contradiction
  cases ok
  exact writeFits _ _ (fun _ => h _ (Array.getElem_mem _)) _ _ _ old

private theorem zeroCheckedFits {L : Limits} {r : Header.Rect} {p : JPEG2000.WideQuant.Plane}
    (ok : JPEG2000.WideQuant.zeroChecked L r = .ok p) (b : Nat) : RasterFits b p.samples.toArray := by
  unfold JPEG2000.WideQuant.zeroChecked at ok
  obtain ⟨_, _, ok⟩ := Tier2Equiv.bind_ok ok
  split at ok <;> try contradiction
  cases ok
  intro x hx
  change x ∈ Array.replicate _ 0 at hx
  obtain ⟨_, rfl⟩ := Array.mem_replicate.mp hx
  exact zeroFits _

private theorem visitFits {α : Type} (P : α → Prop) (nl : Nat)
    (precs : Array (Array JPEG2000.Tier2.Packet.PrecinctOut))
    (s : α → Nat → Band → JPEG2000.Tier2.Packet.CodeBlock → Except Error α) {ini out : α}
    (hi : P ini) (hs : ∀ a r band cb o, P a → s a r band cb = .ok o → P o)
    (ok : JPEG2000.WideAssembly.visitBlocks nl precs ini s = .ok out) : P out := by
  unfold JPEG2000.WideAssembly.visitBlocks at ok
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', ← Array.forIn_toList] at ok
  obtain ⟨_, loop, ret⟩ := Tier2Equiv.bind_ok ok
  cases ret
  refine Tier2Equiv.forIn_inv P _ ?_ _ _ _ hi loop
  intro i a v ha h
  obtain ⟨a', body, hv⟩ := Tier2Equiv.bind_ok h
  cases hv
  refine Tier2Equiv.forIn_inv P _ ?_ _ _ _ ha body
  intro pr a v ha h
  obtain ⟨a', body, hv⟩ := Tier2Equiv.bind_ok h
  cases hv
  refine Tier2Equiv.forIn_inv P _ ?_ _ _ _ ha body
  intro bo a v ha h
  obtain ⟨a', body, hv⟩ := Tier2Equiv.bind_ok h
  cases hv
  refine Tier2Equiv.forIn_inv P _ ?_ _ _ _ ha body
  intro cb a v ha h
  split at h
  · obtain ⟨o, call, h⟩ := Tier2Equiv.bind_ok h
    cases h; exact hs _ _ _ _ _ ha call
  · cases h; exact ha

/-- Any successful block traversal preserves a common exponent for the entire coefficient
plane if every returned code-block cell reconstructs within that exponent. Also covers
empty precincts and missing blocks in the checked zero-initialised raster. -/
theorem tile_coefficients {L : Limits} {data : ByteArray} {tc : JPEG2000.Tier2.Geometry.TileCompGeom}
    {depth f red b : Nat} {ps : Array (Array JPEG2000.Tier2.Packet.PrecinctOut)}
    {out : JPEG2000.WideQuant.Plane}
    (cells : ∀ r band cb cs, JPEG2000.WideAssembly.decodeBlock data tc.params r band cb = .ok cs →
      ∀ c ∈ cs, Fits b (JPEG2000.WideQuant.prepare (Quant.bandQuant tc.params depth r band) f c))
    (ok : JPEG2000.WideAssembly.tileComp L data tc depth f red ps = .ok out) :
    RasterFits b out.samples.toArray := by
  unfold JPEG2000.WideAssembly.tileComp at ok
  dsimp only at ok
  split at ok <;> try contradiction
  obtain ⟨_, _, ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨_, _, ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨p, init, ok⟩ := Tier2Equiv.bind_ok ok
  apply visitFits (fun pl : JPEG2000.WideQuant.Plane => RasterFits b pl.samples.toArray)
    _ _ _ (zeroCheckedFits init b) _ ok
  intro a r band cb o ha h
  obtain ⟨cs, decoded, wrote⟩ := Tier2Equiv.bind_ok h
  exact dequantFits ha (cells _ _ _ _ decoded) wrote

/-- Part 1 quantisation allowance for the 292-plane Tier-1 invariant, with at most
38 precision bits, two gain bits and 26 working fractional bits. This is a bound
on the *biased numerator*, before division by the step exponent. -/
def part1QuantLimit := quantLimit (2^292) 291 40 26 31 2047 255

set_option exponentiation.threshold 512 in
private theorem part1_limit : part1QuantLimit ≤ 2^372 := by decide

/-- For a parsed layout, the declared depth, selected fractional precision, guard,
exponent, mantissa and ROI are all discharged. The remaining cell hypotheses are
the two numeric projections of the accepted Tier-1 result (`parsed_cells`). -/
theorem parsed_quant {L : Limits} {data : ByteArray} {h : Header.Header} {t : Nat}
    {g : Progression.Layout} {coding : Header.Coding} (parsed : Header.parse L data = .ok h)
    (layout : Progression.Layout.ofHeader h t = .ok (g,coding)) (i : Fin g.numComps)
    (r : Nat) (b : Band) (c : Cell) (hm : c.mag < 2^292) (hp : c.lsbPlane ≤ 291) :
    let p := (g.comp i).params
    let depth := (h.siz.components.getD i default).depth.toNat
    let f := Assemble.fracBitsOf h.siz (coding.mctApplies h.siz) i
    let q := Quant.bandQuant p depth r b
    p.guardBits ≤ 7 ∧ JPEG2000.Tier2.Packet.bandMb p r b + p.roiShift ≤ 292 ∧
      QuantOperands q f c part1QuantLimit ∧ part1QuantLimit ≤ 2^372 := by
  let p := (g.comp i).params
  let d := (h.siz.components.getD i default).depth.toNat
  let f := Assemble.fracBitsOf h.siz (coding.mctApplies h.siz) i
  let q := Quant.bandQuant p d r b
  have pars := (WideHeaderBounds.parsed_component_bounds parsed layout i 0).1
  have mu := (HeaderWF.headerWF L data h parsed t g coding layout).1 i
  have dep : d ≤ 38 := by
    simp only [d, Array.getD_eq_getD_getElem?]
    cases e : h.siz.components[i.val]? with
    | none => decide
    | some z => exact (NativePlacement.parsed_depth parsed _ (Array.mem_of_getElem? e)).2
  have fr : f ≤ 26 := by unfold f Assemble.fracBitsOf; split <;> exact Nat.sub_le ..
  have step : q.exponent ≤ 31 ∧ q.mantissa ≤ 2047 := by
    simp only [q, Quant.bandQuant, Array.getD_eq_getD_getElem?]
    cases e : p.steps[Quant.bandIndex r b]? with
    | none => decide
    | some st =>
      have mem := Array.mem_of_getElem? e
      exact ⟨pars.exponents _ mem, Nat.le_of_lt_succ (mu _ mem)⟩
  have range : q.range ≤ 40 := by
    change d + Quant.log2Gain b ≤ 40
    cases b <;> simp only [Quant.log2Gain] <;> omega
  exact ⟨pars.guard, pars.block_planes r b, quant_operands (Nat.le_of_lt hm) hp range fr
    step.1 step.2 pars.roi, part1_limit⟩

/-- Numeric Tier-1 interface, valid for every successful decode of one component's
packet blocks. `Resources.Tier1Work.parsed_cells` supplies both projections. -/
def BlockBounds (data : ByteArray) (p : Header.CompParams) (M P : Nat) : Prop :=
  ∀ r band cb cs, JPEG2000.WideAssembly.decodeBlock data p r band cb = .ok cs →
    ∀ c ∈ cs, c.mag ≤ M ∧ c.lsbPlane ≤ P

private theorem prepared {q : Quant.BandQuant} {f : Nat} {c : Cell} {B : Nat}
    (h : QuantOperands q f c B) : (JPEG2000.WideQuant.prepare q f c).natAbs ≤ B := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, result⟩ := h
  exact result

/-- Parametric bound on the actual assembled coefficient plane. Its exponent is the
binary width of the quantiser allowance at this component's depth, maximum band gain
and selected fractional precision. Compose it with `idwt53_bounds` or `idwt97_bounds`. -/
theorem coefficient_width {L : Limits} {data : ByteArray} {tc : JPEG2000.Tier2.Geometry.TileCompGeom}
    {M P E U depth f red : Nat} {ps : Array (Array JPEG2000.Tier2.Packet.PrecinctOut)}
    {p : JPEG2000.WideQuant.Plane} (blocks : BlockBounds data tc.params M P)
    (steps : ∀ r band, let q := Quant.bandQuant tc.params depth r band
      q.exponent ≤ E ∧ q.mantissa ≤ U)
    (ok : JPEG2000.WideAssembly.tileComp L data tc depth f red ps = .ok p) :
    let Q := quantLimit M P (depth+2) f E U tc.params.roiShift
    RasterFits (Q.log2+1) p.samples.toArray := by
  apply tile_coefficients _ ok
  intro r band cb cs decoded c hc
  obtain ⟨hm, hl⟩ := blocks _ _ _ _ decoded _ hc
  obtain ⟨he, hu⟩ := steps r band
  have range : (Quant.bandQuant tc.params depth r band).range ≤ depth+2 := by
    change depth+Quant.log2Gain band ≤ depth+2
    cases band <;> simp [Quant.log2Gain] <;> omega
  exact Nat.le_trans (prepared (quant_operands hm hl range (Nat.le_refl f) he hu
    (Nat.le_refl tc.params.roiShift))) (Nat.le_of_lt Nat.lt_log2_self)

/-! ## Centred sources in the tile dispatcher -/

/-- Bounds on the reconstructed sample source before any DC shift or clamp. -/
def SourceFits (b : Nat) (s : JPEG2000.NativeOutput.Source) : Prop := ∀ i, Fits b (s.read i)

private theorem compactFits (p : Bytes.Plane) : SourceFits 31 (.plane p) := by
  intro i
  let v := p.get i.val i.isLt
  change v.toInt.natAbs ≤ 2^31
  have lo := v.le_toInt
  have hi := v.toInt_lt
  omega

private theorem sourceMono {a b : Nat} {s : JPEG2000.NativeOutput.Source}
    (h : SourceFits a s) (le : a ≤ b) : SourceFits b s := fun i => mono (h i) le

private theorem sourceGet {b : Nat} {s : JPEG2000.NativeOutput.Source} (h : SourceFits b s) (i : Nat) :
    Fits b ((s.get? i).getD 0) := by
  unfold JPEG2000.NativeOutput.Source.get?
  split
  · exact h _
  · exact zeroFits _

/-- The reversible dispatcher uses views of unclamped integer samples, including
in mixed compact/wide colour triples. The same numerator and floor quotient as
`rct_operands` occur at each call to `rgbAt`. -/
theorem rct_view {b : Nat} {y cb cr : JPEG2000.NativeOutput.Source}
    (hy : SourceFits b y) (hb : SourceFits b cb) (hr : SourceFits b cr) (i : Nat) :
    let rgb := JPEG2000.ReversibleDispatch.rgbAt y cb cr i
    Fits (b+3) rgb.1 ∧ Fits (b+2) rgb.2.1 ∧ Fits (b+3) rgb.2.2 := by
  obtain ⟨_, _, g, r, blue⟩ := rct_operands (sourceGet hy i) (sourceGet hb i) (sourceGet hr i)
  exact ⟨r,g,blue⟩

private theorem revSource {L : Limits} {data : ByteArray} {tc : JPEG2000.Tier2.Geometry.TileCompGeom}
    {depth f red b : Nat} {ps : Array (Array JPEG2000.Tier2.Packet.PrecinctOut)}
    {s : JPEG2000.NativeOutput.Source} (base : 31 ≤ b)
    (bands : ∀ p, JPEG2000.WideAssembly.tileComp L data tc depth f red ps = .ok p →
      RasterFits b p.samples.toArray)
    (ok : JPEG2000.ReversibleDispatch.tileComp L data tc depth f red ps = .ok s) :
    SourceFits (b+12*(tc.params.levels-red)) s := by
  unfold JPEG2000.ReversibleDispatch.tileComp at ok
  dsimp only at ok
  split at ok <;> try contradiction
  split at ok
  · cases ok; exact sourceMono (compactFits _) (by omega)
  · obtain ⟨p, hp, ok⟩ := Tier2Equiv.bind_ok ok
    obtain ⟨q, hq, ok⟩ := Tier2Equiv.bind_ok ok
    split at ok <;> try contradiction
    cases ok
    exact fun _ => idwt53_bounds (bands _ hp) hq _ (Array.getElem_mem _)

private theorem wideSource {b : Nat} {p : JPEG2000.WideICT.Component} (h : RasterFits b p.samples.toArray) :
    SourceFits b (JPEG2000.IrreversibleDispatch.Spatial.wide p).source :=
  fun i => h _ (Array.getElem_mem (i := i.val) (by rw [Vector.size_toArray]; exact i.isLt))

private theorem irrevSource {L : Limits} {data : ByteArray} {tc : JPEG2000.Tier2.Geometry.TileCompGeom}
    {depth f red b : Nat} {ps : Array (Array JPEG2000.Tier2.Packet.PrecinctOut)}
    {s : JPEG2000.IrreversibleDispatch.Spatial} (base : 31 ≤ b)
    (bands : ∀ p, JPEG2000.WideAssembly.tileComp L data tc depth f red ps = .ok p →
      RasterFits b p.samples.toArray)
    (ok : JPEG2000.IrreversibleDispatch.component L data tc depth f red ps = .ok s) :
    SourceFits (b+540*(tc.params.levels-red)) s.source := by
  unfold JPEG2000.IrreversibleDispatch.component at ok
  dsimp only at ok
  split at ok <;> try contradiction
  split at ok <;> try contradiction
  obtain ⟨_, _, ok⟩ := Tier2Equiv.bind_ok ok
  split at ok <;> try contradiction
  obtain ⟨attempt, tried, ok⟩ := Tier2Equiv.bind_ok ok
  cases attempt with
  | none =>
    obtain ⟨p, hp, ok⟩ := Tier2Equiv.bind_ok ok
    obtain ⟨q, hq, ok⟩ := Tier2Equiv.bind_ok ok
    cases ok
    exact wideSource (idwt97_bounds (bands _ hp) hq)
  | some s' =>
    cases ok
    change JPEG2000.IrreversibleDispatch.tryCompact L data tc depth f red ps = .ok (some s) at tried
    unfold JPEG2000.IrreversibleDispatch.tryCompact at tried
    split at tried
    · cases tried
    have eq := Except.ok.inj tried
    unfold JPEG2000.IrreversibleDispatch.compactSpatial at eq
    simp only [bind, Option.bind] at eq
    split at eq <;> try contradiction
    dsimp only at eq
    split at eq <;> try contradiction
    cases eq
    exact sourceMono (compactFits _) (by omega)

/-- Component result from the actual public tile dispatcher, including compact success
and precision retry. Parsed parameters give 372 baseline exponent bits. A caller can
replace the retained level count by `L.maxDecompLevels` using the first conclusion. -/
theorem parsed_spatial {L : Limits} {data : ByteArray} {h : Header.Header} {t : Nat}
    {g : Progression.Layout} {coding : Header.Coding} (parsed : Header.parse L data = .ok h)
    (layout : Progression.Layout.ofHeader h t = .ok (g,coding)) (i : Fin g.numComps)
    (store : Option JPEG2000.Tier2.Packet.TileCodeBlocks) (red : Nat)
    (blocks : BlockBounds data (g.comp i).params (2^292-1) 291) {s : JPEG2000.TileDispatch.Spatial}
    (ok : JPEG2000.TileDispatch.component L h data g coding store i red = .ok s) :
    let tc := g.comp i
    let nl := tc.params.levels-red
    nl ≤ L.maxDecompLevels ∧ SourceFits
      (372 + (if tc.params.transform = .reversible53 then 12 else 540)*nl) s.source := by
  have lev := (WideHeaderBounds.parsed_component_bounds parsed layout i red).1.levels
  refine ⟨Nat.le_trans (Nat.sub_le ..) lev, ?_⟩
  let tc := g.comp i
  let d := (h.siz.components.getD i default).depth.toNat
  let f := Assemble.fracBitsOf h.siz (coding.mctApplies h.siz) i
  have bands (ps p) (hp : JPEG2000.WideAssembly.tileComp L data tc d f red ps = .ok p) :
      RasterFits 372 p.samples.toArray := by
    apply tile_coefficients _ hp
    intro r band cb cs decoded c hc
    obtain ⟨hm, hl⟩ := blocks _ _ _ _ decoded _ hc
    have pos := Nat.two_pow_pos 292
    have mag : c.mag < 2^292 := by omega
    obtain ⟨_, _, terms, bound⟩ := parsed_quant parsed layout i r band c mag hl
    exact Nat.le_trans (prepared terms) bound
  unfold JPEG2000.TileDispatch.component at ok
  cases tr : (g.comp i).params.transform with
  | reversible53 =>
    rw [tr] at ok
    simp only [↓reduceIte]
    cases hv : JPEG2000.ReversibleDispatch.component L data h.siz g coding store i red with
    | error e => rw [hv] at ok; cases ok
    | ok v =>
      rw [hv] at ok; cases ok
      exact revSource (by decide : 31 ≤ 372) (bands _) hv
  | irreversible97 =>
    rw [tr] at ok
    simp only [reduceCtorEq, ↓reduceIte]
    cases hv : JPEG2000.IrreversibleDispatch.component L data tc d f red
        ((store.map (·.comps.getD i #[])).getD #[]) with
    | error e => change _ <$> JPEG2000.IrreversibleDispatch.component L data tc d f red _ = _ at ok
                 rw [hv] at ok; cases ok
    | ok v =>
      change _ <$> JPEG2000.IrreversibleDispatch.component L data tc d f red _ = _ at ok
      rw [hv] at ok; cases ok
      exact irrevSource (by decide : 31 ≤ 372) (bands _) hv

private theorem promoted {s : JPEG2000.IrreversibleDispatch.Spatial} {b : Nat}
    (h : SourceFits b s.source) : RasterFits b s.toWide.samples.toArray := by
  cases s with
  | compact r f p hw hh =>
    apply ofFnFits
    intro i
    exact h ⟨i.val, by change i.val < p.width*p.height; rw [hw,hh]; exact i.isLt⟩
  | wide p =>
    intro z hz
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hz
    exact h ⟨i, by rw [Vector.size_toArray] at hi; exact hi⟩

/-- Wide ICT when a compact peer is promoted. Separate spatial bounds may come from
different depths, level counts and scales. Successful checking equates the scales.
The final conclusion propagates separate physical errors for all three inputs. -/
theorem promoted_ict {L : Limits} {y cb cr : JPEG2000.IrreversibleDispatch.Spatial}
    {Y C R : Nat} (hy : SourceFits Y y.source) (hb : SourceFits C cb.source)
    (hr : SourceFits R cr.source)
    {o : JPEG2000.WideICT.Component × JPEG2000.WideICT.Component × JPEG2000.WideICT.Component}
    (ok : JPEG2000.WideICT.ictInverse L y.toWide cb.toWide cr.toWide = .ok o) :
    let b := max Y (max C R)+21
    cb.toWide.fracBits = y.toWide.fracBits ∧ cr.toWide.fracBits = y.toWide.fracBits ∧
    RasterFits b o.1.samples.toArray ∧ RasterFits b o.2.1.samples.toArray ∧
    RasterFits b o.2.2.samples.toArray ∧
    ∀ i, i < rectArea y.toWide.rect → ∀ ref e, WideICT.Close
      (WideICT.physical y.toWide i, WideICT.physical cb.toWide i, WideICT.physical cr.toWide i) ref e →
      WideICT.Close (WideICT.physical o.1 i, WideICT.physical o.2.1 i, WideICT.physical o.2.2 i)
        (MCT.ictInv ref) (WideICT.rowErrors ((2^y.toWide.fracBits : Nat) : Rat) e) := by
  obtain ⟨cbScale, crScale, r, g, blue⟩ := ict_bounds (promoted hy) (promoted hb) (promoted hr) ok
  exact ⟨cbScale, crScale, r, g, blue, WideICT.ictInverse_error ok⟩


private theorem rctViews {b : Nat} {y cb cr : JPEG2000.NativeOutput.Source}
    (hy : SourceFits b y) (hb : SourceFits b cb) (hr : SourceFits b cr) :
    let o := JPEG2000.ReversibleDispatch.views y cb cr
    SourceFits (b+3) o.1 ∧ SourceFits (b+3) o.2.1 ∧ SourceFits (b+3) o.2.2 := by
  exact ⟨fun i => (rct_view hy hb hr i.val).1,
    fun i => mono (rct_view hy hb hr i.val).2.1 (by omega),
    fun i => (rct_view hy hb hr i.val).2.2⟩

/-- Bounds for the centred RGB sources actually dispatched by G.2, including views
on mixed backing. A checked packed RGB output always has at most 31 exponent bits. -/
theorem dispatched_rct {L : Limits} {b : Nat} {y cb cr : JPEG2000.NativeOutput.Source}
    {o : JPEG2000.NativeOutput.Source × JPEG2000.NativeOutput.Source × JPEG2000.NativeOutput.Source}
    (base : 31 ≤ b+3) (hy : SourceFits b y) (hb : SourceFits b cb) (hr : SourceFits b cr)
    (ok : JPEG2000.ReversibleDispatch.colour L y cb cr = .ok o) :
    SourceFits (b+3) o.1 ∧ SourceFits (b+3) o.2.1 ∧ SourceFits (b+3) o.2.2 := by
  unfold JPEG2000.ReversibleDispatch.colour at ok
  obtain ⟨_, _, ok⟩ := Tier2Equiv.bind_ok ok
  split at ok <;> try contradiction
  cases y <;> cases cb <;> cases cr <;> try (cases ok; exact rctViews hy hb hr)
  dsimp only at ok
  split at ok
  · obtain ⟨⟨r,g,bl⟩, _, ok⟩ := Tier2Equiv.bind_ok ok
    cases ok
    exact ⟨sourceMono (compactFits _) base, sourceMono (compactFits _) base, sourceMono (compactFits _) base⟩
  · cases ok; exact rctViews hy hb hr

private theorem packFits {r : Header.Rect} {f : Nat} {read : Nat → Int}
    {s : JPEG2000.IrreversibleDispatch.Spatial} (h : JPEG2000.IrreversibleDispatch.pack r f read = some s) :
    SourceFits 31 s.source := by
  unfold JPEG2000.IrreversibleDispatch.pack at h
  simp only [bind, Option.bind] at h
  split at h <;> try contradiction
  dsimp only at h
  split at h <;> try contradiction
  cases h; exact compactFits _

private theorem compactColour {y cb cr : JPEG2000.IrreversibleDispatch.Spatial}
    {o : JPEG2000.IrreversibleDispatch.Spatial × JPEG2000.IrreversibleDispatch.Spatial ×
      JPEG2000.IrreversibleDispatch.Spatial}
    (h : JPEG2000.IrreversibleDispatch.compactICT y cb cr = some o) :
    SourceFits 31 o.1.source ∧ SourceFits 31 o.2.1.source ∧ SourceFits 31 o.2.2.source := by
  cases y <;> cases cb <;> cases cr <;> try cases h
  unfold JPEG2000.IrreversibleDispatch.compactICT at h
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨r, hr, g, hg, b, hb, eq⟩ := h
  cases eq
  exact ⟨packFits hr, packFits hg, packFits hb⟩

/-- Both precision branches of the actual G.3 dispatcher keep their pre-output
samples within 21 extra exponent bits. The checked-wide row numerators satisfy
the same bound by `ict_operands`, including the bias before signed division. -/
theorem dispatched_ict {L : Limits} {y cb cr : JPEG2000.IrreversibleDispatch.Spatial}
    {o : JPEG2000.IrreversibleDispatch.Spatial × JPEG2000.IrreversibleDispatch.Spatial ×
      JPEG2000.IrreversibleDispatch.Spatial} {Y C R : Nat} (base : 31 ≤ max Y (max C R)+21)
    (hy : SourceFits Y y.source) (hb : SourceFits C cb.source) (hr : SourceFits R cr.source)
    (ok : JPEG2000.IrreversibleDispatch.ict L y cb cr = .ok o) :
    let b := max Y (max C R)+21
    SourceFits b o.1.source ∧ SourceFits b o.2.1.source ∧ SourceFits b o.2.2.source := by
  unfold JPEG2000.IrreversibleDispatch.ict at ok
  obtain ⟨_, _, ok⟩ := Tier2Equiv.bind_ok ok
  split at ok <;> try contradiction
  cases fast : JPEG2000.IrreversibleDispatch.compactICT y cb cr with
  | some q =>
    rw [fast] at ok
    cases ok
    obtain ⟨r,g,b⟩ := compactColour fast
    exact ⟨sourceMono r base, sourceMono g base, sourceMono b base⟩
  | none =>
    rw [fast] at ok
    obtain ⟨⟨r,g,b⟩, wide, ok⟩ := Tier2Equiv.bind_ok ok
    cases ok
    obtain ⟨_, _, hr, hg, hb⟩ := ict_bounds (promoted hy) (promoted hb) (promoted hr) wide
    exact ⟨wideSource hr, wideSource hg, wideSource hb⟩

private theorem afterColour {L : Limits} {b : Nat} {mct : Bool} {ps : Array JPEG2000.TileDispatch.Spatial}
    {out : Array JPEG2000.NativeOutput.Source} (base : 31 ≤ b) (h : ∀ p ∈ ps, SourceFits b p.source)
    (ok : JPEG2000.TileDispatch.sources L mct ps = .ok out) :
    ∀ s ∈ out, SourceFits (b+21) s := by
  have initial : ∀ s ∈ ps.map JPEG2000.TileDispatch.Spatial.source, SourceFits (b+21) s := by
    intro s hs
    obtain ⟨p, hp, rfl⟩ := Array.mem_map.mp hs
    exact sourceMono (h _ hp) (by omega)
  have replace (r g bl : JPEG2000.NativeOutput.Source)
      (hr : SourceFits (b+21) r) (hg : SourceFits (b+21) g) (hb : SourceFits (b+21) bl) :
      ∀ s ∈ (((ps.map (·.source)).setIfInBounds 0 r).setIfInBounds 1 g).setIfInBounds 2 bl,
        SourceFits (b+21) s := by
    intro s hs
    rcases Array.mem_or_eq_of_mem_setIfInBounds hs with hs | rfl
    · rcases Array.mem_or_eq_of_mem_setIfInBounds hs with hs | rfl
      · rcases Array.mem_or_eq_of_mem_setIfInBounds hs with hs | rfl
        · exact initial _ hs
        · exact hr
      · exact hg
    · exact hb
  unfold JPEG2000.TileDispatch.sources at ok
  split at ok
  · cases ok; exact initial
  dsimp only at ok
  split at ok <;> try contradiction
  · rename_i y cb cr ey eb er
    obtain ⟨⟨r,g,bl⟩, rgb, ret⟩ := Tier2Equiv.bind_ok ok
    cases ret
    obtain ⟨hr,hg,hb⟩ := dispatched_rct (by omega : 31 ≤ b+3)
      (h _ (Array.mem_of_getElem? ey)) (h _ (Array.mem_of_getElem? eb)) (h _ (Array.mem_of_getElem? er)) rgb
    exact replace _ _ _ (sourceMono hr (by omega)) (sourceMono hg (by omega)) (sourceMono hb (by omega))
  · rename_i y cb cr ey eb er
    obtain ⟨⟨r,g,bl⟩, rgb, ret⟩ := Tier2Equiv.bind_ok ok
    cases ret
    obtain ⟨hr,hg,hb⟩ := dispatched_ict (Y := b) (C := b) (R := b) (by omega)
      (h _ (Array.mem_of_getElem? ey)) (h _ (Array.mem_of_getElem? eb)) (h _ (Array.mem_of_getElem? er)) rgb
    simp only [Nat.max_self] at hr hg hb
    exact replace _ _ _ hr hg hb

private theorem mapped {α β : Type} {xs : Array α} {out : Array β} (P : β → Prop)
    (f : (i : Nat) → α → i < xs.size → Except Error β)
    (step : ∀ i a hi y, f i a hi = .ok y → P y)
    (ok : xs.mapFinIdxM f = .ok out) : ∀ y ∈ out, P y := by
  have loop (k j : Nat) (len : k+j = xs.size) (acc : Array β)
      (init : ∀ y ∈ acc, P y) (body : Array.mapFinIdxM.map xs f k j len acc = .ok out) :
      ∀ y ∈ out, P y := by
    induction k generalizing j acc with
    | zero => cases body; exact init
    | succ k ih =>
      rw [Array.mapFinIdxM.map] at body
      obtain ⟨y, call, body⟩ := Tier2Equiv.bind_ok body
      apply ih _ _ _ _ body
      intro v hv
      rcases Array.mem_push.mp hv with hv | rfl
      · exact init _ hv
      · exact step _ _ _ _ call
  exact loop _ _ _ _ (by simp) ok

/-- Uniform bound on each centred output read of the parsed tile, including
optional MCT, mixed wavelets and skipped channels. The signed-magnitude width
is at most `395 + 540 * L.maxDecompLevels` bits including the sign, or 17675
bits for the default 32 levels. The Tier-1 hypothesis is per successful block. -/
theorem parsed_tile {L : Limits} {data : ByteArray} {h : Header.Header} {t : Nat}
    {g : Progression.Layout} {coding : Header.Coding} (parsed : Header.parse L data = .ok h)
    (layout : Progression.Layout.ofHeader h t = .ok (g,coding))
    (store : Option JPEG2000.Tier2.Packet.TileCodeBlocks) (red : Nat)
    (blocks : ∀ i : Fin g.numComps, BlockBounds data (g.comp i).params (2^292-1) 291)
    {out : Array JPEG2000.NativeOutput.Source}
    (ok : JPEG2000.TileDispatch.tile L h data g coding store red = .ok out) :
    ∀ s ∈ out, SourceFits (393+540*L.maxDecompLevels) s := by
  unfold JPEG2000.TileDispatch.tile at ok
  obtain ⟨_, _, ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨ps, comps, ok⟩ := Tier2Equiv.bind_ok ok
  let b := 372+540*L.maxDecompLevels
  have before : ∀ p ∈ ps, SourceFits b p.source := by
    apply mapped (fun p : JPEG2000.TileDispatch.Spatial => SourceFits b p.source) _ _ comps
    intro i _ hi p hp
    obtain ⟨le, fit⟩ := parsed_spatial parsed layout ⟨i,hi⟩ store red (blocks _) hp
    change (g.comp i).params.levels-red ≤ L.maxDecompLevels at le
    apply sourceMono fit
    dsimp only [b]
    split <;> omega
  intro s hs
  exact sourceMono (afterColour (by dsimp [b]; omega) before ok s hs) (by dsimp [b]; omega)

end JPEG2000.Spec.Resources.WideArithmetic
