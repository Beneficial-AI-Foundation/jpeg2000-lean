import JPEG2000.WideQuant
import JPEG2000.WideReversible

/-!
# Wide fixed-point inverse 9/7 (Plan.md §§4, 5.1, 5.4, 7; T.800 F.3, Table F.4)

Each multiplication uses a ratio of integers. Rounding after the product keeps the
binary scale of the Mallat samples. Each pass materialises one bounded array per line.
-/

namespace JPEG2000.WideDWT97

open Header (Rect)
open DWT53 (halfRect srcIdx lnb rnb)
open Tier2.Geometry (rectArea)
open WideQuant (Plane)

/-- Round a product by the exact coefficient `num / den` to the nearest fixed-point
unit, taking ties toward positive infinity. The filter uses positive denominators. -/
@[inline] def product (num den x : Int) : Int := (num * x + den / 2) / den

/-- Common denominator of the five Table F.4 decimals. -/
def unit : Int := 1000000000000000

/-- Numerator of the synthesis scaling coefficient K. -/
def kNum : Int := 1230174104914001

/-- F-7 combines its two parity scalings into one pass and has four lifting passes. -/
inductive Step where
  /-- Multiply even cells by K and odd cells by its reciprocal. -/
  | scale
  /-- Add the rounded neighbour sum times `num / unit` at the selected parity. -/
  | lift (even : Bool) (num : Int)

/-- The signed lifting numerators implement subtraction of δ, γ, β and α in order. -/
def steps : List Step :=
  [.scale, .lift true (-443506852043971), .lift false (-882911075530934),
    .lift true 52980118572961, .lift false 1586134342059924]

/-- One output cell. Read the two adjacent opposite-parity samples only for an
active lifting update. -/
@[inline] def Step.cell (s : Step) (even : Bool) (x : Int) (adjacent : Unit → Int) : Int :=
  match s with
  | .scale => if even then product kNum unit x else product unit kNum x
  | .lift p num => if even = p then x + product num unit (adjacent ()) else x

/-- Apply the remaining F-7 passes to one line using the F-4 reflected neighbours. -/
def passes (a n : Nat) : List Step → Array Int → Array Int
  | [], xs => xs
  | s :: ss, xs =>
    passes a n ss (Array.ofFn (n := n) fun i =>
      s.cell ((a + i.val) % 2 == 0) (xs.getD i.val 0)
        (fun _ => xs.getD (lnb i.val) 0 + xs.getD (rnb n i.val) 0))

/-- F.3.6 on one interleaved line. An odd-origin singleton undergoes floor
division by two, including for negative inputs. -/
def line (a n : Nat) (read : Nat → Int) : Array Int :=
  if n ≤ 1 then Array.ofFn (n := n) fun i => if a % 2 = 0 then read i else read i / 2
  else passes a n steps (Array.ofFn (n := n) fun i => read i)

/-- Synthesize parallel lines, indexed by line number then local position. An empty
axis requires no line headers, even if the other dimension is large. -/
def lines (a n count : Nat) (read : Nat → Nat → Int) : Array (Array Int) :=
  if n = 0 then #[] else Array.ofFn (n := count) fun i => line a n (read i)

/-- Read one cell from a family of rows or columns. -/
@[inline] def atLine (ls : Array (Array Int)) (i k : Nat) : Int := (ls.getD i #[]).getD k 0

/-- Reconstruct the coarser LL first. Detail reads preserve the original stride.
Horizontal synthesis precedes vertical synthesis at every requested resolution. -/
def synthesize (p : Array Int) (stride : Nat) (r : Rect) : Nat → Vector Int (rectArea r)
  | 0 => ⟨WideReversible.raster r.width r.height fun x y => p.getD (y * stride + x) 0,
      by simp [WideReversible.raster, rectArea]⟩
  | n + 1 =>
    let low := halfRect r
    let ll := synthesize p stride low n
    let read := fun y x =>
      let col := srcIdx r.x0 low.width x
      let row := srcIdx r.y0 low.height y
      if (r.x0 + x) % 2 = 0 ∧ (r.y0 + y) % 2 = 0 then
        ll.toArray.getD (row * low.width + col) 0
      else p.getD (row * stride + col) 0
    let rows := lines r.x0 r.width r.height read
    let cols := lines r.y0 r.height r.width fun x y => atLine rows y x
    ⟨WideReversible.raster r.width r.height (atLine cols),
      by simp [WideReversible.raster, rectArea]⟩

/-- Checked Annex F inverse on the wide dequantiser's actual packed plane. The
type carries the raster length. Validate both endpoints and the resource ceilings
before allocating any intermediate line or raster. -/
def idwt97 (L : Limits) (p : Plane) (nl : Nat) : Except Error Plane := do
  L.check (.at .dwt) .decompLevels nl
  L.check (.at .dwt) .workSamples (rectArea p.rect)
  if p.rect.x1 < p.rect.x0 ∨ p.rect.y1 < p.rect.y0 then
    throw (.malformed (.at .dwt) "inverted wide Mallat rectangle")
  if nl = 0 ∨ rectArea p.rect = 0 then return p
  return ⟨p.rect, synthesize p.samples.toArray p.rect.width p.rect nl⟩

end JPEG2000.WideDWT97
