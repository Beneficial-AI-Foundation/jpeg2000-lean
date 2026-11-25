import JPEG2000.Decode
import Tests.Pgx
import Tests.Decode

/-!
# T.803 conformance runner (task 5.6b)

Plan.md §8.1 (conformance), §7 row 5 (exit M5: "T.803 profile 0 and 1 pass — reversible
bit-exact, irreversible within class thresholds"). ITU-T T.803 | ISO/IEC 15444-4 §C (Tables
C.1, C.4: class 0; C.6, C.7: class 1).

Every reference-decode entry of `corpus/manifest.json` (task 5.6a, `Tests.ConformanceData`)
whose stream is a profile-0/1 codestream is checked: the stream is decoded with
`JPEG2000.decodeCodestream Limits.default data (reduce := entry.reduce)` (each stream once per
reduction factor), the entry's component is compared with the reference PGX and the result must
meet the entry's thresholds. This mirrors OpenJPEG's `tests/conformance/CMakeLists.txt` (at
`uclouvain/openjpeg@8314119`): `opj_decompress -i pX_YY.j2k -o out.pgx -r <ResFactor>` with no
other option (no `-p`, no component selection; class 1 compares components `0 … nbC−1`,
class 0 only component 0), then `compare_images`, which

* fails on a sign, precision or size mismatch of a component;
* computes per component `PEAK = max |base − test|` and `MSE = Σ (base − test)² / (w·h)`;
* fails when `MSE > m` or `PEAK > p` (so equality passes).

The same semantics are applied here, exactly (rational comparison, `Tests.Pgx.Metrics.within`).
Class 0 is OpenJPEG's commented-out block (it runs only class 1); both classes are run and
reported separately.

Additionally every class-1 entry whose component uses the reversible 5/3 transform in every
tile must be bit-exact (peak 0), regardless of the threshold.

The nine `jp2_N.tif` references need colour composition (palette, sYCC, `-p 8S -force-rgb`),
which belongs to the consumer API (task 6.2); they are reported as skipped.

`lake exe conformance` runs everything and exits nonzero on any class-1 failure (the M5
criterion; with `--gate-class0` also on class-0 failures); `run` (registered in
`lake exe tests`) checks a small, fast subset (both classes, all passing).

Class 0 status (2026-11-25): several class-0 references are not reproduced by OpenJPEG either
(same metrics as ours with every `-r`/`-l`): their precision is 8 (or 4) bits for 12-bit
streams, `c0p0_03r0`/`c0p0_15r0`/`c0p1_04r0` have the size of a different reduction, and
`p0_04`, `p0_10`, `p0_13`, `p0_14`, `p1_02`, `p1_05`, `p1_06` exceed the Table C.1/C.4
thresholds with OpenJPEG as with us.
-/

namespace JPEG2000.Tests.Conformance

open JPEG2000 JPEG2000.Tests.ConformanceData JPEG2000.Tests.Pgx

/-- The outcome of one reference entry. -/
structure Outcome where
  /-- The entry. -/
  entry : RefEntry
  /-- Whether the entry was skipped (not decoded). -/
  skipped : Bool := false
  /-- Whether the decode met the entry's thresholds (and bit-exactness when reversible). -/
  pass : Bool := false
  /-- The metrics, when the comparison could be made. -/
  metrics : Option Metrics := none
  /-- The component is 5/3 reversible in every tile. -/
  reversible : Bool := false
  /-- Explanation (error, mismatch or skip reason). -/
  note : String := ""

/-- `n / d` rendered with `k` decimals, rounded down (`d > 0`; `0` when `d = 0`). -/
def fmtFrac (n d : Nat) (k : Nat := 3) : String :=
  if d = 0 then "0" else
    let s := 10 ^ k
    let v := n * s / d
    let frac := toString (v % s)
    s!"{v / s}.{"".pushn '0' (k - frac.length)}{frac}"

/-- A threshold rendered as a decimal. -/
def fmtQ (q : Q) : String :=
  if q.den == 1 then toString q.num else fmtFrac q.num q.den

/-- The short name of a corpus path (`…/p0_04.j2k` → `p0_04`). -/
def shortName (p : String) : String :=
  ((p.splitOn "/").getLast?.getD p).replace ".j2k" ""

/-- Is the entry a profile-0/1 codestream entry (as opposed to a JP2 TIFF reference)? -/
def isCodestreamEntry (e : RefEntry) : Bool :=
  !e.isTiff && (e.profile == some 0 || e.profile == some 1) && e.cls.isSome

/-- A decoded component as a `PgxImage` (sign and depth from the codestream). -/
def toPgx (c : DecodedComponent) : PgxImage :=
  { width := c.width, height := c.height, depth := c.depth, signed := c.signed,
    samples := JPEG2000.Tests.Decode.samplesOf c }

/-- Compares one entry against a decode (or a decode error), as `compare_images` does. -/
def judge (e : RefEntry) (dec : Except Error DecodedImage) : IO Outcome := do
  match dec with
  | .error err => return { entry := e, note := s!"decode error: {err}" }
  | .ok img =>
    let c := e.component.getD 0
    let some d := img.comps[c]? | return { entry := e, note := s!"no component {c}" }
    let rev := JPEG2000.Tests.Decode.reversibleComp img.header c
    let refs ← loadReference e
    let some r := refs[0]? | return { entry := e, reversible := rev, note := "empty reference" }
    let ours := toPgx d
    if r.signed != ours.signed then
      return { entry := e, reversible := rev, note := s!"sign mismatch (ref {r.signed}, ours {ours.signed})" }
    if r.depth != ours.depth then
      -- `compare_images` fails here (no `-i prec`); also show the MSB-aligned metrics
      -- (its `-i prec` right shift) for information only.
      let info := if r.depth < ours.depth then
          let k := ours.depth - r.depth
          match JPEG2000.Tests.Pgx.compare r { ours with depth := r.depth, samples := ours.samples.map fun (x : Int) => x >>> k } with
          | .ok m => s!"; MSB-aligned (>> {k}, info only): peak {m.peak} mse {fmtFrac m.sumSq m.count}"
          | .error _ => ""
        else ""
      return { entry := e, reversible := rev,
               note := s!"precision mismatch (ref {r.depth}, ours {ours.depth}){info}" }
    match compare r ours with
    | .error m => return { entry := e, reversible := rev, note := m }
    | .ok m =>
      let within := m.within e
      let exactOk := !(rev && e.cls == some 1) || m.peak == 0
      let note := if !within then "outside thresholds"
        else if !exactOk then "reversible component not bit-exact" else ""
      return { entry := e, pass := within && exactOk, metrics := some m, reversible := rev, note }

/-- Why the JP2 TIFF references are skipped. -/
def skipNote : String :=
  "JP2 TIFF reference: needs colour composition (task 6.2, -p 8S -force-rgb)"

/-- Evaluates the entries (in order), decoding each `(stream, reduce)` pair once. -/
def evaluate (es : Array RefEntry) : IO (Array Outcome) := do
  let mut out : Array (Option Outcome) := Array.replicate es.size none
  -- skipped entries
  for h : i in [0:es.size] do
    let e := es[i]
    if !isCodestreamEntry e then
      let o : Outcome := { entry := e, skipped := true, note := skipNote }
      out := out.set! i (some o)
  -- distinct (stream, reduce) keys in first-occurrence order
  let mut keys : Array (String × Nat) := #[]
  for e in es do
    if isCodestreamEntry e && !keys.contains (e.stream, e.reduce) then
      keys := keys.push (e.stream, e.reduce)
  for (s, r) in keys do
    let data ← IO.FS.readBinFile (filesRoot ++ s)
    let dec := decodeCodestream Limits.default data (reduce := r)
    for h : i in [0:es.size] do
      let e := es[i]
      if isCodestreamEntry e && e.stream == s && e.reduce == r then
        out := out.set! i (some (← judge e dec))
  return out.filterMap id

/-- One report line. -/
def line (o : Outcome) : String :=
  let e := o.entry
  let tag := if o.skipped then "SKIP" else if o.pass then "PASS" else "FAIL"
  let cls := match e.cls with | some c => s!"class {c}" | none => "jp2"
  let comp := match e.component with | some c => s!"comp {c}" | none => "all"
  let m := match o.metrics with
    | some m => s!"peak {m.peak} mse {fmtFrac m.sumSq m.count}"
    | none => "-"
  let rev := if o.reversible then " 5/3" else ""
  let note := if o.note.isEmpty then "" else s!" — {o.note}"
  s!"{tag} {shortName e.stream} {comp} {cls} r{e.reduce} {m} (limits peak {fmtQ e.peak} mse {fmtQ e.mse}){rev}{note}"

/-- Prints the outcomes and per-class summaries; returns the number of failures in the
`gating` classes (failures of other classes are reported but not counted). -/
def report (os : Array Outcome) (verbose : Bool := true) (gating : List Nat := [0, 1]) :
    IO Nat := do
  let mut fails := 0
  for c in [1, 0] do
    let sel := os.filter (·.entry.cls == some c)
    if sel.isEmpty then continue
    for o in sel do
      if verbose || !o.pass then IO.println (line o)
    let n := (sel.filter (·.pass)).size
    let gate := if gating.contains c then "" else " (informational, not gating)"
    IO.println s!"class {c}: {n}/{sel.size} pass{gate}"
    if gating.contains c then fails := fails + (sel.size - n)
  -- the reversible bit-exactness check (class 1)
  let rev := os.filter fun o => o.entry.cls == some 1 && o.reversible
  let exact := rev.filter fun o => match o.metrics with | some m => m.peak == 0 | none => false
  if !rev.isEmpty then
    IO.println s!"reversible (5/3) class-1 components bit-exact: {exact.size}/{rev.size}"
  let skipped := os.filter (·.skipped)
  for o in skipped do
    if verbose then IO.println (line o)
  if !skipped.isEmpty then
    IO.println s!"skipped: {skipped.size} (JP2 TIFF references; colour composition is task 6.2)"
  return fails

/-- Whether the corpus is present (run from the repository root). -/
def haveCorpus : IO Bool := do
  let t ← load
  match t[0]? with
  | none => return false
  | some e => System.FilePath.pathExists (filesRoot ++ e.stream)

/-- Streams of the fast subset run by `lake exe tests`: small reversible profile-0 streams. -/
def subset : List String := ["p0_01", "p0_02", "p0_11", "p0_12", "p0_16"]

/-- Test-suite hook: the class-1 (and class-0) entries of the `subset` streams; returns the
number of failures (0 with a message when the corpus is absent). -/
def run : IO Nat := do
  if !(← haveCorpus) then
    IO.println "conformance: corpus/files missing, skipped"
    return 0
  let t ← load
  let es := t.filter fun e => isCodestreamEntry e && subset.contains (shortName e.stream)
  let os ← evaluate es
  report os (verbose := false) (gating := [0, 1])

end JPEG2000.Tests.Conformance
