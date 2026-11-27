import Spec.HeaderWF
import Spec.Tier2WF

/-!
# C9: implementation = spec, end to end

Plan.md §4 (C9: "end to end, `decode = Spec.decode` (exact for reversible paths; within C8's bound
for irreversible ones)"), §5.1; T.800 Annexes A–G. Task 7.1e. The plain-language statement, every
side condition and the list of stage theorems it rests on are in `docs/c9.md`.

`c9` is `Spec.Tier2WF.c9_of_hdr` (C9 from `HeaderWF` alone, every other stage hypothesis already
discharged) applied to `Spec.HeaderWF.headerWF`; it has no hypotheses.
-/

namespace JPEG2000.Spec.C9

/-- **C9 (Plan.md §4): the fast decoder agrees with the executable specification**, for every
`Limits`, input and reduction, with no hypotheses. `ERel C9Rel (decodeCodestream L data reduce)
(Spec.Decode.decode L data reduce)` means:

* **failures**: both decoders fail (any errors); or the fast one fails with an `unsupported`
  error (an implementation limit: a code-block with more than 31 coded bit-planes, components
  wider than the `Int32` pipeline) where the spec succeeds. A fast success where the spec fails
  never happens.
* **successes**: same header, same number of components, and per component the same origin,
  size, depth, signedness and sub-sampling; and **if the fast decoder reports no saturated
  code-block (`saturatedBlocks = 0`)**, every sample satisfies `SampleRel`: under C8's
  no-overflow precondition `InRangeT` (vacuous for a reversible component without MCT; otherwise
  the exact inverse-transform values the sample depends on, scaled by `2^F`, fit in `Int32`),
  * a reversible (5/3) sample **equals** the spec sample;
  * an irreversible (9/7) sample is within `cellErr F mct levels + 1` of the exact (rational)
    spec sample (C8's bound plus the two final roundings).

See `docs/c9.md` for when the side conditions can fail. -/
theorem c9 : ∀ (L : Limits) (data : ByteArray) (reduce : Nat),
    Spec.Equiv.ERel Spec.Equiv.C9Rel (JPEG2000.decodeCodestream L data reduce)
      (Spec.Decode.decode L data reduce) :=
  Spec.Tier2WF.c9_of_hdr Spec.HeaderWF.headerWF

end JPEG2000.Spec.C9
