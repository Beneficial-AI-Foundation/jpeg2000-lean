import Encode.Tier1
import Spec.RoundTrip.Tier2

/-!
# Packet bounds for a reference Tier-1 code-block

Plan.md §§4, 5.3, 7 (C10, M7). T.800 D.2 (coding passes) and B.10.5–B.10.7
(zero bit-planes, pass count and codeword length).

For the block that `Encode.encodeComp` pushes into the precinct-band, 37 coded
planes fit the single-segment cap of 109 passes. The remaining size premise
for an included block is a bound on the length in bytes of its MQ codeword.
-/

namespace JPEG2000.Spec.RoundTrip

open JPEG2000.Encode.Tier1 (EncOut encodeCodeBlock numBits maxMag)
open JPEG2000.Encode.Tier2 (lblockInc)

/-- The fields returned by a successful Tier-1 call recover the bit depth of the
source, account for all `Mb` planes, and give the exact plain-mode pass count.
Natural subtraction gives zero passes when the source has no coded planes. -/
theorem encodeCodeBlock_counts {w h Mb : Nat} {orient : Spec.Tier1.Orientation}
    {src : Array Int} {o : EncOut} (henc : encodeCodeBlock w h orient Mb src = .ok o) :
    o.codedPlanes = numBits (maxMag src) ∧ o.zeroBitPlanes + o.codedPlanes = Mb ∧
      o.numPasses = 3 * o.codedPlanes - 2 := by
  unfold encodeCodeBlock at henc
  by_cases hgeom : w > 1024 ∨ h > 1024 ∨ w * h > 4096
  · simp [hgeom] at henc; cases henc
  by_cases hsize : src.size ≠ w * h
  · simp [hgeom, hsize] at henc; cases henc
  by_cases hdepth : numBits (maxMag src) > Mb
  · simp [hgeom, hsize, hdepth] at henc; cases henc
  simp only [hgeom, hsize, hdepth, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at henc
  subst o
  dsimp only
  split <;> omega

/-- The actual block and band bound constructed by `Encode.encodeComp` satisfy
`BlockOK` when the caller admits 109 passes and each included codeword fits
the packet's 32-bit length field. -/
theorem blockOK_encodeCodeBlock {L : Limits} {w h Mb roiShift : Nat}
    {orient : Spec.Tier1.Orientation} {src : Array Int} {o : EncOut}
    (henc : encodeCodeBlock w h orient Mb src = .ok o)
    (hplanes : numBits (maxMag src) ≤ 37) (hlimit : 109 ≤ L.maxPassesPerCodeBlock)
    (hbytes : o.numPasses ≠ 0 → o.bytes.length < 2 ^ 32) :
    BlockOK L (Mb + roiShift)
      { numPasses := o.numPasses, zeroBitPlanes := o.zeroBitPlanes, data := ⟨o.bytes.toArray⟩ } := by
  obtain ⟨hc, hz, hp⟩ := encodeCodeBlock_counts henc
  intro hinc
  dsimp only at hinc ⊢
  have h109 : o.numPasses ≤ 109 := by omega
  exact ⟨by omega, h109, Nat.le_trans h109 hlimit, by simpa [ByteArray.size] using hbytes hinc⟩

/-- For a plain segment with at most 109 passes, the 32-bit width check is
equivalent to the strict byte-count bound on the codeword. -/
theorem width_le_iff_length_lt {n len : Nat} (hn : n ≤ 109) :
    3 + lblockInc n len + Nat.log2 n ≤ 32 ↔ len < 2 ^ 32 :=
  ⟨fun hw => Nat.lt_of_lt_of_le (lt_width n len) (Nat.pow_le_pow_right (by decide) hw),
   width_le hn⟩

end JPEG2000.Spec.RoundTrip
