import JPEG2000
import Spec
import Encode
import Tests.Basic
import Tests.Bytes
import Tests.Box
import Tests.Marker
import Tests.MQSpec
import Tests.TilePart
import Tests.MarkerRoundTrip
import Tests.MQEnc
import Tests.MQ
import Tests.Header
import Tests.Tier1Context
import Tests.TilePartRoundTrip
import Tests.Tier1Spec
import Tests.TagTree
import Tests.Geometry
import Tests.Tier1Fast
import Tests.Tier1Enc
import Tests.Progression
import Tests.Packet
import Tests.DWT53
import Tests.Tier2Headers
import Tests.Quant
import Tests.DWT97
import Tests.MCT
import Tests.Color
import Tests.Pgx
import Tests.Decode
import Tests.Encode
import Tests.MQRoundTrip
import Tests.Conformance

/-!
# Test runner

Shared registry: test suites are registered in `suites` (the orchestrator adds lines and the
matching imports). Each suite returns its number of failures; the runner exits nonzero when
any suite fails.
-/

namespace JPEG2000.Tests

/-- A named test suite returning the number of failures. -/
structure Suite where
  /-- Name printed in the report. -/
  name : String
  /-- Runs the suite; the result is the number of failed checks. -/
  run : IO Nat

/-- Registered test suites. -/
def suites : List Suite :=
  [ { name := "smoke", run := return 0 },
    { name := "basic", run := JPEG2000.Tests.Basic.run },
    { name := "bytes", run := JPEG2000.Tests.Bytes.run },
    { name := "box", run := JPEG2000.Tests.Box.run },
    { name := "marker", run := JPEG2000.Tests.Marker.run },
    { name := "mqspec", run := JPEG2000.Tests.MQSpec.run },
    { name := "tilepart", run := JPEG2000.Tests.TilePart.run },
    { name := "marker-roundtrip", run := JPEG2000.Tests.MarkerRoundTrip.run },
    { name := "mqenc", run := JPEG2000.Tests.MQEnc.run },
    { name := "mq", run := JPEG2000.Tests.MQ.run },
    { name := "header", run := JPEG2000.Tests.Header.run },
    { name := "mq-roundtrip", run := JPEG2000.Tests.MQRoundTrip.run },
    { name := "tier1ctx", run := JPEG2000.Tests.Tier1Context.run },
    { name := "tilepart-roundtrip", run := JPEG2000.Tests.TilePartRoundTrip.run },
    { name := "tier1spec", run := JPEG2000.Tests.Tier1Spec.run },
    { name := "tagtree", run := JPEG2000.Tests.TagTree.run },
    { name := "geometry", run := JPEG2000.Tests.Geometry.run },
    { name := "tier1fast", run := JPEG2000.Tests.Tier1Fast.run },
    { name := "tier1enc", run := JPEG2000.Tests.Tier1Enc.run },
    { name := "progression", run := JPEG2000.Tests.Progression.run },
    { name := "packet", run := JPEG2000.Tests.Packet.run },
    { name := "dwt53", run := JPEG2000.Tests.DWT53.run },
    { name := "tier2headers", run := JPEG2000.Tests.Tier2Headers.run },
    { name := "quant", run := JPEG2000.Tests.Quant.run },
    { name := "dwt97", run := JPEG2000.Tests.DWT97.run },
    { name := "mct", run := JPEG2000.Tests.MCT.run },
    { name := "color", run := JPEG2000.Tests.Color.run },
    { name := "pgx", run := JPEG2000.Tests.Pgx.run },
    { name := "decode", run := JPEG2000.Tests.Decode.run },
    { name := "encode", run := JPEG2000.Tests.Encode.run },
    { name := "conformance", run := JPEG2000.Tests.Conformance.run } ]

end JPEG2000.Tests

/-- Runs every registered suite and reports one line per suite. -/
def main : IO UInt32 := do
  let mut failures := 0
  for s in JPEG2000.Tests.suites do
    let f ← s.run
    IO.println s!"[{if f == 0 then "PASS" else "FAIL"}] {s.name} ({f} failures)"
    failures := failures + f
  return if failures == 0 then 0 else 1
