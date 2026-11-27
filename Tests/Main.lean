import JPEG2000
import Spec
import Encode
import Tests.Basic
import Tests.Bytes

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
    { name := "bytes", run := JPEG2000.Tests.Bytes.run } ]

end JPEG2000.Tests

/-- Runs every registered suite and reports one line per suite. -/
def main : IO UInt32 := do
  let mut failures := 0
  for s in JPEG2000.Tests.suites do
    let f ← s.run
    IO.println s!"[{if f == 0 then "PASS" else "FAIL"}] {s.name} ({f} failures)"
    failures := failures + f
  return if failures == 0 then 0 else 1
