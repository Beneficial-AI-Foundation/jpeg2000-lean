import Spec.MQ
import Spec.MQTable
import Spec.MarkerRoundTrip
import Spec.MQEquiv
import Spec.MQRoundTrip
import Spec.Tier1.Context
import Spec.Tier1.Modes
import Spec.Tier1.Decode
import Spec.TagTree
import Spec.Progression
import Spec.DWT53
import Spec.Quant
import Spec.DWT97
import Spec.MCT
import Spec.Tier1Equiv.Basic
import Spec.Tier1Equiv.Rel
import Spec.Tier1Equiv.Nb
import Spec.Tier1Equiv.Steps
import Spec.Tier1Equiv.Pass
import Spec.Tier1Equiv.Scan
import Spec.Tier1Equiv.Inv
import Spec.Tier1Equiv
import Spec.TilePartRoundTrip

/-!
# Executable specifications

Umbrella module of `Spec/` (Plan.md §5.1): near-literal transcriptions of ITU-T T.800 and
the equivalence theorems. Shared registry: the orchestrator adds one import per module.
-/
