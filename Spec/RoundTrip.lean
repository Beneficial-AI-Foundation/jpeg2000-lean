import Spec.RoundTrip.Tier1
import Spec.RoundTrip.Tier2Bits

/-!
# C10: `decode (encode img) = img` for the lossless reference encoder (in progress)

Plan.md §4 (C10), §5.3. Task 7.3. The round trip is assembled from per-stage layers under
`Spec/RoundTrip/`:

* **Layer 1 (proved)** — Tier-1, plain mode, T.800 Annex D + C1:
  `Spec.RoundTrip.decodeValues_encodeCodeBlock` (`Spec/RoundTrip/Tier1.lean`).
* **Layer 2 (partly proved)** — Tier-2 packet headers, T.800 B.10: the bit writer against the
  spec's un-stuffing and header alignment (`finish_spec`) and the header fields
  (`field_natBits`, `numPasses_passBits`, `commaCode_replicate`) in
  `Spec/RoundTrip/Tier2Bits.lean`. The packet-level round trip, the main-header round trip,
  the composed spec-level C10 and the fast-decoder C10 (via C9) are not yet proved.
-/
