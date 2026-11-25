import JPEG2000.Error
import JPEG2000.Limits
import JPEG2000.Bytes
import JPEG2000.Box
import JPEG2000.Marker
import JPEG2000.TilePart
import JPEG2000.MQ
import JPEG2000.Header

/-!
# jpeg2000-lean

Umbrella module of the decoder library (Plan.md §3, §12). Shared registry: the orchestrator
adds one import per module under `JPEG2000/`.
-/
