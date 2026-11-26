import JPEG2000.Quant
import JPEG2000.Tier1.WidePlain
import JPEG2000.WideOutput

/-!
# Wide dequantisation into the tile-component Mallat array

Plan.md §§4, 5.1, 5.4, 7; T.800 B-14, B-15, E.1.1.2 and H.2.
The coefficient raster from Tier-1 retains all coded magnitude bits and its last decoded
plane. Reconstruct in integers, including the irreversible fixed-point rounding, before
writing the block directly into the requested component grid.
-/

namespace JPEG2000.WideQuant

open Header (Rect CompParams)
open Tier2.Geometry
open Tier1.WidePlain (Cell)
open Spec.Quant (BandQuant)

/-- Annex H magnitude and last decoded plane after max-shift removal. -/
def unshift (s : Nat) : Cell → Nat × Nat :=
  let threshold := 2 ^ s
  fun c => if threshold ≤ c.mag then (c.mag >>> s, c.lsbPlane - s) else (c.mag, c.lsbPlane)

/-- Prepare a nonzero coefficient's unsigned reconstruction. The irreversible numerator is
`(2m + 2^l)(2048 + μ)2^(R+F)` and the denominator is `2^(ε+12)`.
The scale, divisor and half-divisor are shared across the block. -/
def magnitude (q : BandQuant) (F : Nat) : Nat → Nat → Int :=
  if q.reversible then fun m l => (m + 2 ^ l / 2 : Nat)
  else
    let scale := (2048 + q.mantissa) * 2 ^ (q.range + F)
    let divisor := (2 : Int) ^ (q.exponent + 12)
    let half := divisor / 2
    fun m l => (((2 * m + 2 ^ l) * scale : Nat) + half) / divisor

/-- Prepare the Annex H/E kernel for a block. Insignificant and zero cells produce zero.
The sign is applied after the reversible midpoint or irreversible magnitude rounding. -/
def prepare (q : BandQuant) (F : Nat) : Cell → Int :=
  let roi := unshift q.roiShift
  let recon := magnitude q F
  fun c =>
    if !c.sig then 0 else
      let (m, l) := roi c
      if m = 0 then 0 else
        let z := recon m l
        if c.sign then -z else z

/-- Mallat coefficients on one (possibly reduced) tile-component rectangle.
The vector is a row-major `Array Int` with its area in its type. -/
structure Plane where
  /-- Tile-component rectangle on the grid being reconstructed. -/
  rect : Rect
  /-- Row-major coefficient array, with stride `rect.width`. -/
  samples : Vector Int (rectArea rect)

/-- Allocate the absent-block value, zero, at every coefficient after checking the work
budget. Tile assembly also checks the sum of the component areas before allocating them. -/
def zeroChecked (L : Limits) (rect : Rect) : Except Error Plane := do
  L.check Quant.loc .workSamples (rectArea rect)
  if rect.x1 < rect.x0 ∨ rect.y1 < rect.y0 then
    throw (.malformed Quant.loc "inverted tile-component rectangle")
  return ⟨rect, Vector.replicate (rectArea rect) 0⟩

/-- Mallat coordinates of the first block cell: translate its band coordinates
relative to the band rectangle and add the low-pass extents in high-pass directions. -/
@[inline] def blockOffset (rect : Rect) (nl r : Nat) (b : Band) (cb : Rect) : Nat × Nat :=
  let band := bandRect rect (bandLevel nl r) b
  let origin := Quant.bandOrigin rect nl r b
  (origin.1 + (cb.x0 - band.x0), origin.2 + (cb.y0 - band.y0))

/-- Write the first `k` source cells in reverse raster order. The accumulator owns the
destination array throughout the tail recursion. Both accessors take bounded indices. -/
def writeCells {n area : Nat} (index : Fin n → Fin area) (value : Fin n → Int)
    (k : Nat) (hk : k ≤ n) (dst : Vector Int area) : Vector Int area :=
  match k with
  | 0 => dst
  | k + 1 =>
    let i : Fin n := ⟨k, hk⟩
    let j := index i
    writeCells index value k (Nat.le_of_lt hk) (dst.set j.val (value i) j.isLt)

/-- Place a raster of the checked size into a contained output rectangle. -/
def place (dst : Plane) (cb : Rect) (ox oy : Nat) (kernel : Cell → Int)
    (cells : Array Cell) (hs : cells.size = rectArea cb)
    (fit : ox + cb.width ≤ dst.rect.width ∧ oy + cb.height ≤ dst.rect.height) : Plane :=
  let index := fun (i : Fin (rectArea cb)) =>
    ⟨WideOutput.destIndex dst.rect.width cb.width ox oy i,
      WideOutput.destIndex_lt fit.1 fit.2 i.isLt⟩
  let value := fun (i : Fin (rectArea cb)) => kernel (cells[i.val]'(by rw [hs]; exact i.isLt))
  ⟨dst.rect, writeCells index value (rectArea cb) (Nat.le_refl _) dst.samples⟩

/-- Write a whole decoded block, choosing its step and range from its original resolution
and orientation. `dst.rect` is the tile-component rectangle after `reduce` halvings.
Validate work, resolution, raster length, band containment and both destination axes
before writing. An absent packet block can be skipped in the zero-initialised plane. -/
def dequantBlock (L : Limits) (dst : Plane) (p : CompParams) (depth reduce r : Nat)
    (b : Band) (cb : Rect) (F : Nat) (cells : Array Cell) : Except Error Plane := do
  L.check Quant.loc .workSamples (rectArea dst.rect)
  L.check Quant.loc .decompLevels p.levels
  let nl := p.levels - reduce
  if reduce > p.levels ∨ r > nl ∨ b ∉ bandsOf r then
    throw (.malformed Quant.loc "invalid resolution or subband for the component grid")
  let band := bandRect dst.rect (bandLevel nl r) b
  if cb.x1 < cb.x0 ∨ cb.y1 < cb.y0 ∨ cb.x0 < band.x0 ∨ cb.y0 < band.y0 ∨
      band.x1 < cb.x1 ∨ band.y1 < cb.y1 then
    throw (.malformed Quant.loc "code-block rectangle outside its subband")
  let (ox, oy) := blockOffset dst.rect nl r b cb
  if hs : cells.size = rectArea cb then
    if fit : ox + cb.width ≤ dst.rect.width ∧ oy + cb.height ≤ dst.rect.height then
      return place dst cb ox oy (prepare (Spec.Quant.bandQuant p depth r b) F) cells hs fit
    else throw (.malformed Quant.loc "code-block does not fit the Mallat array")
  else throw (.malformed Quant.loc "code-block raster size differs from its rectangle")

end JPEG2000.WideQuant
