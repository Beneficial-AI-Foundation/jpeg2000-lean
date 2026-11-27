import Encode.MQ
import Encode.Marker
import Encode.TilePart
import Encode.Tier1
import Encode.Tier2
import Encode.Encode

/-!
# Reference encoder

Umbrella module of `Encode/` (Plan.md §5.3): a deliberately simple encoder used only by
tests and proofs, never part of the public API. Shared registry: the orchestrator adds one
import per module.
-/
