import JPEG2000.Error
import JPEG2000.Limits
import JPEG2000.Bytes
import JPEG2000.WidePlane
import JPEG2000.WideOutput
import JPEG2000.NativeOutput
import JPEG2000.WideQuant
import JPEG2000.WideReversible
import JPEG2000.WideICT
import JPEG2000.WideDWT97
import JPEG2000.Box
import JPEG2000.Marker
import JPEG2000.TilePart
import JPEG2000.MQ
import JPEG2000.Header
import JPEG2000.TagTree
import JPEG2000.Tier2.Geometry
import JPEG2000.Tier1.Tables
import JPEG2000.Tier1.Decode
import JPEG2000.Tier1.Modes
import JPEG2000.Tier1.WidePlain
import JPEG2000.Tier1.WideModes
import JPEG2000.Tier1.WideSegments
import JPEG2000.Progression
import JPEG2000.Tier2.Packet
import JPEG2000.DWT53
import JPEG2000.Tier2.Headers
import JPEG2000.Quant
import JPEG2000.DWT97
import JPEG2000.MCT
import JPEG2000.Color
import JPEG2000.Assemble
import JPEG2000.Decode
import JPEG2000.CodestreamTraversal
import JPEG2000.WideAssembly
import JPEG2000.Image

import JPEG2000.ReversibleDispatch
import JPEG2000.IrreversibleDispatch

/-!
# jpeg2000-lean

Umbrella module of the decoder library (Plan.md §3, §12). Shared registry: the orchestrator
adds one import per module under `JPEG2000/`.
-/
