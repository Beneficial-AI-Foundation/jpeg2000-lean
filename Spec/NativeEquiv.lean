import Spec.NativeSample
import Spec.Tier2Equiv.Header

/-!
# Public codestream sample relation

Plan.md §4 C9 and C10. Component metadata, raster length and all observable integer
samples are compared on the native output type. The selected tile transform sets the
sample's reversible flag and its irreversible precision (T.800 Annexes F and G).
-/

namespace JPEG2000.Spec.NativeEquiv

open JPEG2000.Spec.Decode

/-- A public component and its specification counterpart have the same geometry, format
and exact lookup domain. Every observed value satisfies the corresponding C9 claim. -/
structure ComponentRel (siz : Marker.SIZ) (i : Nat) (d : CodestreamComponent) (s : SpecComponent) : Prop where
  /-- Equal origins, dimensions, precision, signedness and sampling separations. -/
  metadata : d.x0 = s.info.x0 ∧ d.y0 = s.info.y0 ∧ d.width = s.info.width ∧
    d.height = s.info.height ∧ d.depth = s.info.depth ∧ d.signed = s.info.signed ∧
    d.dx = s.info.dx ∧ d.dy = s.info.dy
  /-- The reference array covers exactly the declared raster. -/
  size : s.samples.size = d.width * d.height
  /-- Every in-bounds native sample is present and meets the numerical claim. -/
  sample : ∀ j (hj : j < s.samples.size), ∃ v, d.get? j = some v ∧
    NativeSample.Agrees (Assemble.fracBitsOf siz s.samples[j].mct i) v s.samples[j]
  /-- An index outside the raster has no stored value. -/
  outside : ∀ j, s.samples.size ≤ j → d.get? j = none

/-- Complete successful-image relation at the requested codestream reduction. -/
structure ImageRel (reduce : Nat) (d : CodestreamImage) (s : SpecImage) : Prop where
  /-- The parsed headers, including boxes and tile overrides, agree. -/
  header : d.header = s.header
  /-- The native image records the requested reduction. -/
  reduction : d.reduce = reduce
  /-- Every image component occurs once and in order. -/
  count : d.comps.size = s.comps.size
  /-- Pointwise component correspondence for the complete array. -/
  component : ∀ i (hi : i < d.comps.size) (hs : i < s.comps.size),
    ComponentRel s.header.siz i d.comps[i] s.comps[i]

/-- Public C9 proposition for a particular input and limits. A successful decode on either side requires a
successful decode on the other. Rejected inputs may have different diagnostic details (Annex B). -/
def Agrees (L : Limits) (data : ByteArray) (reduce : Nat) : Prop :=
  Tier2Equiv.Res (ImageRel reduce) (decodeCodestream L data reduce)
    (Spec.Decode.decode L data reduce)

end JPEG2000.Spec.NativeEquiv
