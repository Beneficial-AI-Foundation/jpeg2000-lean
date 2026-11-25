import Lean.Data.Json

/-!
# Conformance reference-decode table (task 5.6a)

Plan.md §8.1 (conformance).  The table of reference decodes is parsed at run time from
`corpus/manifest.json`, the single source of truth: every file with role `reference-decode`
becomes a `RefEntry` (stream, class, profile, component, resolution reduction, reference file,
exact peak / MSE thresholds).  Thresholds are the T.803 Table C.1 / G.1 tolerances as passed by
OpenJPEG's `tests/conformance/CMakeLists.txt` to `compare_images` (`-p` peak, `-m` MSE, per
component); they are kept as exact decimal fractions (`Q`).  Independent of the decoder.
-/

namespace JPEG2000.Tests.ConformanceData

open Lean

/-- A non-negative exact decimal `num / den` (`den` is a power of ten, so positive). -/
structure Q where
  /-- numerator -/
  num : Nat
  /-- denominator, positive -/
  den : Nat
  deriving Repr, BEq

/-- Float view of a `Q` (for printing only). -/
def Q.toFloat (q : Q) : Float := Float.ofNat q.num / Float.ofNat q.den

/-- Exact `a / b <= q` for naturals `a`, `b > 0`. -/
def Q.divLe (q : Q) (a b : Nat) : Bool := a * q.den ≤ q.num * b

/-- Convert a JSON number (`mantissa * 10^-exponent`) to `Q`; negative numbers are rejected. -/
def Q.ofJson (j : Json) : Except String Q :=
  match j with
  | .num n =>
    if n.mantissa < 0 then .error "negative threshold"
    else .ok { num := n.mantissa.toNat, den := 10 ^ n.exponent }
  | _ => .error "threshold is not a number"

/-- One reference-decode entry of the manifest. -/
structure RefEntry where
  /-- reference file, relative to `corpus/files/` -/
  refPath : String
  /-- the codestream (`.j2k`/`.jp2`) it is the decode of, relative to `corpus/files/` -/
  stream : String
  /-- T.803 class (0 or 1); `none` for the JP2 TIFF references -/
  cls : Option Nat
  /-- T.803 profile; `none` for the JP2 TIFF references -/
  profile : Option Nat
  /-- component index compared (PGX is one file per component); `none` = all (TIFF) -/
  component : Option Nat
  /-- resolution reduction (`-r`) to decode with -/
  reduce : Nat
  /-- maximum allowed absolute sample error -/
  peak : Q
  /-- maximum allowed mean squared error (per component) -/
  mse : Q
  /-- true if the thresholds apply per component -/
  perComponent : Bool
  /-- true for a `.tif` reference, false for `.pgx` -/
  isTiff : Bool
  deriving Repr

/-- Root directory of the fetched corpus files, relative to the repository root. -/
def filesRoot : String := "corpus/files/"

/-- Default manifest path, relative to the repository root. -/
def manifestPath : String := "corpus/manifest.json"

private def optNat (j : Json) (k : String) : Option Nat :=
  match j.getObjVal? k with
  | .ok v => v.getNat?.toOption
  | .error _ => none

private def entryOf (f : Json) : Except String RefEntry := do
  let refPath ← f.getObjValAs? String "path"
  let stream ← f.getObjValAs? String "stream"
  let th ← f.getObjVal? "thresholds"
  let peak ← Q.ofJson (← th.getObjVal? "peak")
  let mse ← Q.ofJson (← th.getObjVal? "mse")
  let perComponent := (th.getObjValAs? Bool "per_component").toOption.getD false
  let reduce ← f.getObjValAs? Nat "reduce"
  pure { refPath, stream, cls := optNat f "class", profile := optNat f "profile",
         component := optNat f "component", reduce, peak, mse, perComponent,
         isTiff := refPath.endsWith ".tif" }

/-- Parse the manifest text into the reference-decode table (order of the manifest). -/
def parseManifest (txt : String) : Except String (Array RefEntry) := do
  let j ← Json.parse txt
  let files ← (← j.getObjVal? "files").getArr?
  let mut out : Array RefEntry := #[]
  for f in files do
    let roles := (f.getObjValAs? (Array String) "roles").toOption.getD #[]
    if roles.contains "reference-decode" then
      match entryOf f with
      | .ok e => out := out.push e
      | .error m => throw s!"{(f.getObjValAs? String "path").toOption.getD "?"}: {m}"
  pure out

/-- Load the table from `corpus/manifest.json` (run from the repository root). -/
def load (path : String := manifestPath) : IO (Array RefEntry) := do
  let txt ← IO.FS.readFile path
  match parseManifest txt with
  | .ok t => pure t
  | .error m => throw (IO.userError s!"manifest: {m}")

/-- Entries that are the reference decode(s) of the given stream path. -/
def forStream (t : Array RefEntry) (stream : String) : Array RefEntry :=
  t.filter (·.stream == stream)

/-- The distinct stream paths of the table, in first-occurrence order. -/
def streams (t : Array RefEntry) : Array String :=
  t.foldl (fun acc e => if acc.contains e.stream then acc else acc.push e.stream) #[]

end JPEG2000.Tests.ConformanceData
