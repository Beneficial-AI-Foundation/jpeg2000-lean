import Spec.RoundTrip.Tier1
import Spec.RoundTrip.Link

/-!
# C10: `decode (encode img) = img` for the lossless reference encoder (in progress)

Plan.md §4 (C10), §5.3. Task 7.3. The round trip is assembled from per-stage layers under
`Spec/RoundTrip/`:

* **Layer 1 (proved)** — Tier-1, plain mode, T.800 Annex D + C1:
  `Spec.RoundTrip.decodeValues_encodeCodeBlock` (`Spec/RoundTrip/Tier1.lean`).
* **Layers 2–3 (proved)** — `Spec.RoundTrip.reversible_tile_roundtrip` parses the
  encoded header and recovers every packet block from the actual codestream under
  the three numerical bounds in `ImageBudget` (T.800 Annexes A and B).
* **Layers 4–5 (in progress)** — reconstruct the original image samples from the
  recovered blocks in the specification, then establish the fast-decoder round trip.
-/
