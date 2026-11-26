import JPEG2000.WidePlane

/-!
# Wide native tile output (Plan.md §§4, 5.4, 7; T.800 B-12, B-14 and G.1)

Reconstruct directly into the checked component plane on its own (possibly
reduced) grid. The source accessor reads post-MCT integers with a component-wide
binary scale. Zero fractional bits covers the reversible path. Exact arithmetic
allows out-of-range coefficients to be shifted and clamped before narrowing.
-/

namespace JPEG2000.WideOutput

open Bytes Spec.MCT

/-- A prepared component reconstruction kernel whose samples fit its native plane. -/
structure Kernel (r : NativeSampleRange) where
  /-- Convert one centred, possibly fractional sample to its final integer value. -/
  sample : Int → {v : Int // r.lo ≤ v ∧ v ≤ r.hi}

/-- Prepare a component's G.1 shift, clamp and final rounding. The offset, scale
and half unit are shared by all samples. -/
def prepare (r : NativeSampleRange) (F : Nat) : Kernel r :=
  let off := dcOffset r.signed r.depth
  let finish := fun (x : Int) =>
    Subtype.mk (clamp r.lo r.hi (x + off)) (clamp_mem _ _ _ (by
      rw [r.lo_eq, r.hi_eq]; exact sampleMin_le_max _ _ r.valid.1))
  if F = 0 then ⟨finish⟩ else
    let scale := (2 : Int) ^ F
    let half := scale / 2
    ⟨fun z => finish ((z + half) / scale)⟩

/-- Row-major destination of a tile's linear source index. -/
@[inline] def destIndex (dw w ox oy i : Nat) : Nat :=
  dw * (oy + i / w) + (ox + i % w)

/-- Translating any source cell in a contained rectangle gives a valid destination index. -/
theorem destIndex_lt {dw dh w h ox oy i : Nat}
    (hx : ox + w ≤ dw) (hy : oy + h ≤ dh) (hi : i < w * h) :
    destIndex dw w ox oy i < dw * dh := by
  have hw : 0 < w := by cases w <;> simp_all
  have hcol := Nat.mod_lt i hw
  have hrow := Nat.div_lt_of_lt_mul hi
  have hr : oy + i / w + 1 ≤ dh := by omega
  have := Nat.mul_le_mul_left dw hr
  rw [Nat.mul_succ] at this
  unfold destIndex
  omega

/-- Write the first `n` tile samples into the destination in reverse raster order.
Only the accumulator owns the destination buffer during this tail-recursive loop. -/
def blitCells {w h : Nat} (ox oy : Nat) (r : NativeSampleRange)
    (kernel : Kernel r) (read : Fin (w * h) → Int)
    (n : Nat) (hn : n ≤ w * h) (dst : WidePlane)
    (hx : ox + w ≤ dst.width) (hy : oy + h ≤ dst.height) (hr : dst.range = r) : WidePlane :=
  match n with
  | 0 => dst
  | k + 1 =>
    let hi : k < w * h := hn
    let v := kernel.sample (read ⟨k, hi⟩)
    let dst := dst.set (destIndex dst.width w ox oy k) v.val (destIndex_lt hx hy hi)
      (hr ▸ v.property)
    blitCells ox oy r kernel read k (Nat.le_of_lt hi) dst hx hy hr

/-- Reconstruct and place a tile-component into a native plane at a relative
component-grid offset. Check destination budgets and containment before reading
any source sample. No intermediate DC-shifted tile is allocated. -/
def blit (L : Limits) (loc : Location) (dst : WidePlane) (w h ox oy F : Nat)
    (read : Fin (w * h) → Int) : Except Error WidePlane := do
  let cells := dst.width * dst.height
  L.check loc .workSamples cells
  L.check loc .decodedBytes (cells * Header.bytesPerSample dst.range.depth)
  if fit : ox + w ≤ dst.width ∧ oy + h ≤ dst.height then
    let kernel := prepare dst.range F
    return blitCells ox oy dst.range kernel read (w * h) (Nat.le_refl _)
      dst fit.1 fit.2 rfl
  else
    throw (.malformed loc "wide tile-component outside the component plane")

end JPEG2000.WideOutput
