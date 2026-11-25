import Spec.Tier2Equiv
import Spec.DWTPlane
import Spec.QuantBlock

/-!
# The real Tier-2 specification wired into C9

Plan.md §4 (C9), §5.1 (one equivalence per stage, composed into C9); T.800 B.9–B.12, A.5.1.
Task 7.1f.

`Spec.decode` (`Spec/Decode.lean`) runs the Tier-2 specification `Spec.Tier2.decodeWithStream`
and reads its per-code-block results (`Spec.Tier2.BlockSt`: rectangle, zero bit-planes,
segments as byte lists). The C9 stage hypothesis `Spec.Equiv.Tier2Equiv` states that the fast
packet decoder and that spec both fail or both succeed with the spec result the image of the
fast one, for headers with non-zero sub-sampling (which `SIZ` parsing guarantees,
`Spec.Equiv.parse_dxdy`). It is `Spec.Tier2Equiv.tier2_equiv_of_siz` (task 7.1b): `tier2Equiv`.

`c9_of_open` is `Spec.Equiv.c9_of_stages` with every stage hypothesis proved so far discharged
(Tier-2 here; the dequantisation block loop and the 5/3 and 9/7 plane transforms in task 7.1d):
what remains open is `Tier2WF` (task 7.1g), `Tier1Equiv` (task 7.1c) and `HeaderWF` (task 7.1e).
-/

namespace JPEG2000.Spec.Tier2Wire

open JPEG2000 JPEG2000.Spec.Equiv

/-- **Stage hypothesis `Tier2Equiv` of C9, proved** (B.9–B.12): the fast packet decoder and
`Spec.Tier2.decodeWithStream` both fail, or both succeed with the spec result the image of the
fast one (`Spec.Tier2Equiv.image`) and the same pass count, for every header with non-zero
sub-sampling. -/
theorem tier2Equiv : Tier2Equiv :=
  fun L h data tp hs n hd => Spec.Tier2Equiv.tier2_equiv_of_siz L h data tp hs n hd

/-- **C9 from the stage hypotheses still open** (Plan.md §4 C9): `c9_of_stages` with
`Tier2Equiv`, `DequantLoopEquiv`, `DWT53PlaneEquiv` and `DWT97PlaneErr` discharged. For every
limits, input and resolution reduction, `decodeCodestream` and `Spec.Decode.decode` are related
by `ERel C9Rel`, assuming `Tier2WF`, `Tier1Equiv` and `HeaderWF`. -/
theorem c9_of_open (hT2w : Tier2WF) (hT1 : Tier1Equiv) (hHd : HeaderWF) :
    ∀ (L : Limits) (data : ByteArray) (reduce : Nat),
      ERel C9Rel (decodeCodestream L data reduce) (Spec.Decode.decode L data reduce) :=
  c9_of_stages tier2Equiv hT2w hT1 Spec.QuantBlock.dequantLoopEquiv Spec.DWTPlane.dwt53PlaneEquiv
    Spec.DWTPlane.dwt97PlaneErr hHd

end JPEG2000.Spec.Tier2Wire
