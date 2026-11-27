import JPEG2000.Image
import Fuzz.Mutate
import Lean.Data.Json
import Std.Data.HashMap

/-!
# `fuzz`: mutation fuzzer for `JPEG2000.decode` (task 9.1)

Plan.md §8.6 (fuzzing), §4 S1–S3 (totality, no out-of-bounds, resource bounds), §3 rule 3
(limits). T.800 Annex A / I for the structure the mutators aim at.

`lake exe fuzz [--iters N] [--seed S] [--start K] [--limits tight|default] [--opj]
[--slow-factor F] [--slow-floor-ms M] [--max-seed-kb K] [--mem-cap-mb M] [--root DIR]
[--manifest FILE] [--findings DIR] [--replay FILE] [--no-inflight]`

Seeds are the manifest files with role `conformance-stream`, `jp2` or `benchmark`, and the
`pdf_jpx` list (those no larger than `--max-seed-kb`). Case `i` is a pure function of
`(seed, i)`: a seed input and a donor input are chosen and 1–3 mutations applied (bit flips,
byte set / insert / delete, duplicate / remove / splice of a marker segment or box, rewrites
of `Lxxx` / `Psot` / `Nppm` / `LBox` fields, truncation); `--start K --iters 1` replays it.

Per case the harness records

* the result class (`ok`, `truncated`, `malformed`, `unsupported`, `limit:<kind>`);
* the wall time of `decode`; a case is **slow** when it takes more than
  `max(slow-factor × the seed's unmutated time, slow-floor-ms)` (reported, not killed: pure
  code cannot be interrupted);
* a **limit escape**: an accepted image whose size breaks `Limits` (area, output bytes,
  work cells, component count, plane geometry), or process peak memory (`VmHWM`) above
  `--mem-cap-mb` (tight limits only by default);
* with `--opj`: for streams we accept, `opj_decompress` on the mutated codestream and a
  per-component comparison of the raw planes (reversible components sample by sample, others
  on the PGX header only). OpenJPEG rejections, crashes and timeouts are counted separately.

A crash cannot occur by construction; should the process die, the input being decoded is
left in `<findings>/inflight.bin` (`scripts/fuzz.sh` renames it). Slow (under 5 s) and disagreeing
inputs are minimised by chunk deletion and saved with a `.txt` description. Exit status 1 on
a limit escape (or with `--fail-on-slow` / `--fail-on-diff`).
-/

namespace Fuzz

open JPEG2000

/-- Command-line options. -/
structure Opts where
  /-- Number of cases. -/
  iters : Nat := 1000
  /-- Campaign seed. -/
  seed : Nat := 1
  /-- Index of the first case. -/
  start : Nat := 0
  /-- Tight (`Limits.strict`) or default limits. -/
  tight : Bool := true
  /-- Differential run against `opj_decompress`. -/
  opj : Bool := false
  /-- Slow threshold factor over the seed's unmutated time. -/
  slowFactor : Nat := 10
  /-- Absolute floor of the slow threshold in ms. -/
  slowFloorMs : Nat := 100
  /-- Seed files larger than this are skipped. -/
  maxSeedKb : Nat := 256
  /-- Peak-memory cap in MB (0 = off; default 1024 for tight limits). -/
  memCapMb : Option Nat := none
  /-- Corpus root. -/
  root : String := "corpus/files"
  /-- Manifest path. -/
  manifest : String := "corpus/manifest.json"
  /-- Findings directory. -/
  findings : String := "Fuzz/findings"
  /-- Replay a single file instead of fuzzing. -/
  replay : Option String := none
  /-- Keep `inflight.bin` up to date. -/
  inflight : Bool := true
  /-- Fail on slow cases. -/
  failSlow : Bool := false
  /-- Fail on differential disagreements. -/
  failDiff : Bool := false

/-- Parses the arguments. -/
def parseArgs : List String → Opts → Except String Opts
  | [], o => .ok o
  | "--iters" :: v :: r, o => match v.toNat? with
    | some n => parseArgs r { o with iters := n } | none => .error s!"bad --iters {v}"
  | "--seed" :: v :: r, o => match v.toNat? with
    | some n => parseArgs r { o with seed := n } | none => .error s!"bad --seed {v}"
  | "--start" :: v :: r, o => match v.toNat? with
    | some n => parseArgs r { o with start := n } | none => .error s!"bad --start {v}"
  | "--slow-factor" :: v :: r, o => match v.toNat? with
    | some n => parseArgs r { o with slowFactor := n } | none => .error s!"bad --slow-factor {v}"
  | "--slow-floor-ms" :: v :: r, o => match v.toNat? with
    | some n => parseArgs r { o with slowFloorMs := n } | none => .error s!"bad --slow-floor-ms"
  | "--max-seed-kb" :: v :: r, o => match v.toNat? with
    | some n => parseArgs r { o with maxSeedKb := n } | none => .error s!"bad --max-seed-kb"
  | "--mem-cap-mb" :: v :: r, o => match v.toNat? with
    | some n => parseArgs r { o with memCapMb := some n } | none => .error s!"bad --mem-cap-mb"
  | "--limits" :: v :: r, o =>
    if v == "tight" then parseArgs r { o with tight := true }
    else if v == "default" then parseArgs r { o with tight := false }
    else .error s!"bad --limits {v}"
  | "--root" :: v :: r, o => parseArgs r { o with root := v }
  | "--manifest" :: v :: r, o => parseArgs r { o with manifest := v }
  | "--findings" :: v :: r, o => parseArgs r { o with findings := v }
  | "--replay" :: v :: r, o => parseArgs r { o with replay := some v }
  | "--opj" :: r, o => parseArgs r { o with opj := true }
  | "--no-inflight" :: r, o => parseArgs r { o with inflight := false }
  | "--fail-on-slow" :: r, o => parseArgs r { o with failSlow := true }
  | "--fail-on-diff" :: r, o => parseArgs r { o with failDiff := true }
  | a :: _, _ => .error s!"unknown argument {a}"

/-! ## Classification and the limit-escape check -/

/-- Result class of an error (by constructor, never by text). -/
def errClass : Error → String
  | .truncated .. => "truncated"
  | .malformed .. => "malformed"
  | .unsupported .. => "unsupported"
  | .limitExceeded _ k _ _ => s!"limit:{k}"

/-- Checks an accepted image against `L`: the sizes `decode` promises (Plan.md §4 S3). -/
def escapeCheck (L : Limits) (img : Image) : Option String := Id.run do
  let w := img.width
  let h := img.height
  if w * h > L.maxImageArea then return some s!"image area {w * h} > {L.maxImageArea}"
  let chans := img.channels ++ img.alpha.toArray ++ img.other
  if chans.size > L.maxComponents then return some s!"{chans.size} channels"
  let mut bytes := 0
  for c in chans do
    if c.plane.width != w || c.plane.height != h then return some "channel plane geometry"
    bytes := bytes + w * h * Header.bytesPerSample c.depth
  if bytes > L.maxDecodedBytes then
    return some s!"channel bytes {bytes} > maxDecodedBytes {L.maxDecodedBytes}"
  let mut rbytes := 0
  let mut cells := 0
  for c in img.decoded.comps do
    if c.samples.width != c.width || c.samples.height != c.height then
      return some "component plane geometry"
    rbytes := rbytes + c.width * c.height * Header.bytesPerSample c.depth
    cells := cells + c.width * c.height
  if rbytes > L.maxDecodedBytes then
    return some s!"component bytes {rbytes} > maxDecodedBytes {L.maxDecodedBytes}"
  if cells > L.maxWorkSamples then
    return some s!"component cells {cells} > maxWorkSamples {L.maxWorkSamples}"
  return none

/-- Result class and escape of one decode (forces the whole result). -/
def classify (L : Limits) (r : Except Error Image) : String × Option String :=
  match r with
  | .ok img => ("ok", escapeCheck L img)
  | .error e => (errClass e, none)

/-- Decodes with a clock around it: (ns, class, escape). -/
def timedDecode (L : Limits) (data : ByteArray) : IO (Nat × String × Option String) := do
  let t0 ← IO.monoNanosNow
  let r ← IO.lazyPure fun _ => JPEG2000.decode L data
  let c ← IO.lazyPure fun _ => classify L r
  let t1 ← IO.monoNanosNow
  return (t1 - t0, c.1, c.2)

/-- Peak resident memory (`VmHWM`) of this process in kB (0 if unreadable). -/
def peakKb : IO Nat := do
  try
    let s ← IO.FS.readFile "/proc/self/status"
    for l in s.splitOn "\n" do
      if l.startsWith "VmHWM:" then
        let digits := (l.toList.drop 6).filter Char.isDigit
        return (String.ofList digits).toNat?.getD 0
    return 0
  catch _ => return 0

/-! ## Differential against opj_decompress -/

/-- PGX bytes of a component plane, as OpenJPEG writes them. -/
def pgx (c : DecodedComponent) : ByteArray := Id.run do
  let bps := Header.bytesPerSample c.depth
  let bps := if bps > 4 then 4 else bps
  let hdr := s!"PG ML {if c.signed then "-" else "+"} {c.depth} {c.width} {c.height}\n"
  let mut out := ByteArray.emptyWithCapacity (hdr.utf8ByteSize + c.width * c.height * bps)
  out := out.append hdr.toUTF8
  for i in [0:c.width * c.height] do
    let v : UInt32 := ((c.plane.get? i).getD 0).toUInt32
    if bps == 4 then out := out.push (v >>> 24).toUInt8 |>.push (v >>> 16).toUInt8
    if bps ≥ 2 then out := out.push (v >>> 8).toUInt8
    out := out.push v.toUInt8
  return out

/-- Index of the first `\n` (the end of the PGX header line). -/
def headerEnd (b : ByteArray) : Nat := Id.run do
  for i in [0:b.size] do
    if b.data.getD i 0 == 10 then return i + 1
  return b.size

/-- Whether every tile of component `c` uses the reversible 5/3 transform. -/
def reversibleComp (h : Header.Header) (c : Nat) : Bool :=
  let rev := fun (cd : Header.Coding) => ((cd.comps.getD c default).transform == .reversible53)
  rev h.defaults && h.tiles.all (rev ·.coding)

/-- Runs `opj_decompress` on the codestream of `data` and compares with our raw components:
(kind, detail); kind is `agree`, `skip`, `disagree`, `opj-reject` or `opj-crash`. -/
def opjDiff (tmp : System.FilePath) (L : Limits) (data : ByteArray) : IO (String × String) := do
  let some cs := codestreamOf data | return ("skip", "no codestream")
  let d ← match JPEG2000.decodeCodestreamNarrow L cs 0 with
    | .ok d => pure d
    | .error _ => return ("skip", "we reject the codestream")
  -- opj_decompress up-samples and colour-converts 3-component streams whose chroma is
  -- sub-sampled (its sYCC heuristic), so the raw planes are not comparable.
  if d.comps.size == 3 && ((d.comps.getD 1 default).dx > 1 || (d.comps.getD 1 default).dy > 1) then
    return ("skip", "opj sYCC heuristic")
  let inp := tmp / "in.j2k"
  for e in (← tmp.readDir) do
    if e.fileName.startsWith "out" then IO.FS.removeFile e.path
  IO.FS.writeBinFile inp cs
  let out ← IO.Process.output
    { cmd := "timeout", args := #["30", "opj_decompress", "-i", inp.toString, "-o",
        (tmp / "out.pgx").toString] }
  if out.exitCode != 0 then
    return if out.exitCode ≥ 124 then ("opj-crash", s!"exit {out.exitCode}")
      else ("opj-reject", s!"exit {out.exitCode}")
  let mut outs := 0
  for e in (← tmp.readDir) do
    if e.fileName.startsWith "out" then outs := outs + 1
  if outs != d.comps.size then
    return ("disagree", s!"component count: ours {d.comps.size}, opj {outs}")
  let mut notes : Array String := #[]
  for k in [0:d.comps.size] do
    let f := tmp / s!"out_{k}.pgx"
    let theirs ← try IO.FS.readBinFile f catch _ => pure ByteArray.empty
    let c := d.comps.getD k default
    let ours := pgx c
    if reversibleComp d.header k then
      if ours != theirs then
        let he := headerEnd ours
        let what := if ours.extract 0 he != theirs.extract 0 (headerEnd theirs)
          then "header" else "samples"
        notes := notes.push s!"comp {k} {what}"
        if what == "header" then
          notes := notes.push s!"[ours {String.fromUTF8! (ours.extract 0 (he - 1))} | opj {String.fromUTF8! (theirs.extract 0 (headerEnd theirs - 1))}]"
    else if ours.extract 0 (headerEnd ours) != theirs.extract 0 (headerEnd theirs) then
      notes := notes.push s!"comp {k} header (9/7)"
  return if notes.isEmpty then ("agree", "") else ("disagree", ", ".intercalate notes.toList)

/-! ## Minimisation -/

/-- Chunk-deletion minimiser: removes ranges while `pred` still holds (at most `budget`
predicate calls). -/
def minimize (pred : ByteArray → IO Bool) (d : ByteArray) (budget : Nat) : IO ByteArray := do
  let mut cur := d
  let mut left := budget
  let mut chunk := cur.size / 2
  while chunk > 0 && left > 0 do
    let mut i := 0
    while i < cur.size && left > 0 do
      let cand := cut cur i (min cur.size (i + chunk))
      left := left - 1
      if ← pred cand then cur := cand else i := i + chunk
    chunk := chunk / 2
  return cur

/-! ## Seeds -/

/-- Seed corpus: (name, bytes) from the manifest. -/
def loadSeeds (o : Opts) : IO (Array (String × ByteArray)) := do
  let txt ← IO.FS.readFile o.manifest
  let j ← match Lean.Json.parse txt with
    | .ok j => pure j
    | .error e => throw (IO.userError s!"manifest: {e}")
  let mut paths : Array String := #[]
  let files := (j.getObjVal? "files" >>= Lean.Json.getArr?).toOption.getD #[]
  for f in files do
    let roles := (f.getObjValAs? (Array String) "roles").toOption.getD #[]
    if roles.any (fun r => r == "conformance-stream" || r == "jp2" || r == "benchmark") then
      match f.getObjValAs? String "path" with
      | .ok p => paths := paths.push p
      | .error _ => pure ()
  let pdf := (j.getObjVal? "pdf_jpx" >>= Lean.Json.getArr?).toOption.getD #[]
  for f in pdf do
    match f.getObjValAs? String "path" with
    | .ok p => if !paths.contains p then paths := paths.push p
    | .error _ => pure ()
  let mut seeds := #[]
  for p in paths do
    let fp : System.FilePath := o.root
    let fp := fp / p
    if !(← fp.pathExists) then continue
    let b ← IO.FS.readBinFile fp
    if b.size > o.maxSeedKb * 1024 then continue
    seeds := seeds.push (p, b)
  return seeds

/-- Writes a finding (`.bin` and `.txt`). -/
def saveFinding (dir : String) (name : String) (data : ByteArray) (info : String) : IO Unit := do
  IO.FS.writeBinFile s!"{dir}/{name}.bin" data
  IO.FS.writeFile s!"{dir}/{name}.txt" (info ++ "\n")

/-- Millisecond rendering of nanoseconds. -/
def ms (ns : Nat) : String := s!"{ns / 1000000}.{(ns / 100000) % 10}"

/-- Replay one file. -/
def replay (o : Opts) (L : Limits) (f : String) : IO UInt32 := do
  let data ← IO.FS.readBinFile f
  let (ns, c, e) ← timedDecode L data
  IO.println s!"{f}: class {c}, {ms ns} ms, escape {e.getD "none"}"
  if o.opj then
    let tmp ← IO.FS.createTempDir
    let (k, dt) ← opjDiff tmp L data
    IO.println s!"opj: {k} {dt}"
    IO.FS.removeDirAll tmp
  return if e.isSome then 1 else 0

/-- The campaign. -/
def run (o : Opts) : IO UInt32 := do
  let L : Limits := if o.tight then Limits.strict else Limits.default
  if let some f := o.replay then return (← replay o L f)
  let seeds ← loadSeeds o
  if seeds.isEmpty then
    IO.eprintln "fuzz: no seed files (run scripts/fetch-corpus.py)"; return 2
  IO.FS.createDirAll o.findings
  let memCap := (o.memCapMb.getD (if o.tight then 1024 else 0)) * 1024
  -- baselines
  let mut base : Array Nat := #[]
  for (_, b) in seeds do
    let mut best := 0
    for k in [0:3] do
      let (ns, _, _) ← timedDecode L b
      if k == 0 || ns < best then best := ns
    base := base.push best
  IO.println s!"fuzz: {seeds.size} seeds, limits {if o.tight then "tight" else "default"}, seed {o.seed}, cases {o.start}..{o.start + o.iters - 1}{if o.opj then ", opj" else ""}"
  let tmp ← if o.opj then IO.FS.createTempDir else pure ""
  let mut hist : Std.HashMap String Nat := {}
  let mut slowN := 0
  let mut escapes := 0
  let mut saved := 0
  let mut slowSaved := 0
  let mut diffSaved := 0
  let mut top : Array (Nat × Nat × String) := #[]
  let mut totalNs := 0
  let mut maxPeak := 0
  let mut opjH : Std.HashMap String Nat := {}
  let mut opjDetail : Std.HashMap String Nat := {}
  let step := max 1 (o.iters / 10)
  let inflight := s!"{o.findings}/inflight.bin"
  for i in [o.start:o.start + o.iters] do
    let rng := Rng.ofCase o.seed i
    let ((si, di), rng) := Id.run ((do
      let a ← below seeds.size
      let b ← below seeds.size
      pure (a, b) : R (Nat × Nat)).run rng)
    let (sname, sdata) := seeds.getD si default
    let ((desc, data), _) := Id.run ((mutate sdata (seeds.getD di default).2).run rng)
    if o.inflight then IO.FS.writeBinFile inflight data
    let (ns, cls, esc) ← timedDecode L data
    totalNs := totalNs + ns
    hist := hist.insert cls (hist.getD cls 0 + 1)
    let info := s!"case {i} seed {o.seed} from {sname}: {desc}; class {cls}; {ms ns} ms"
    let name (k : String) := s!"{k}-s{o.seed}-i{i}"
    -- limit escapes
    if let some why := esc then
      escapes := escapes + 1
      IO.println s!"ESCAPE {info}: {why}"
      saveFinding o.findings (name "escape") data s!"{info}\n{why}"
    let pk ← peakKb
    if memCap > 0 && pk > memCap && pk > maxPeak then
      escapes := escapes + 1
      IO.println s!"ESCAPE {info}: peak memory {pk / 1024} MB > {memCap / 1024} MB"
      saveFinding o.findings (name "escape-mem") data s!"{info}\npeak {pk / 1024} MB"
    maxPeak := max maxPeak pk
    -- slow
    let b := base.getD si 0
    let thr := max (o.slowFactor * b) (o.slowFloorMs * 1000000)
    let ratio := ns * 10 / (max b 1000000)
    top := (top.push (ns, ratio, info)).qsort (fun a b => a.1 > b.1) |>.extract 0 5
    if ns > thr then
      slowN := slowN + 1
      IO.println s!"SLOW {info} (seed time {ms b} ms)"
      if slowSaved < 3 && saved < 200 then
        slowSaved := slowSaved + 1
        saved := saved + 1
        let m ← minimize (fun d => do
          let (n, _, _) ← timedDecode L d
          pure (n > thr)) data (if ns > 5000000000 then 0 else 100)
        saveFinding o.findings (name "slow") data info
        saveFinding o.findings (name "slow-min") m s!"{info}\nminimised {data.size} -> {m.size} bytes"
    -- differential
    if o.opj && cls == "ok" then
      let (k, dt) ← opjDiff tmp L data
      opjH := opjH.insert k (opjH.getD k 0 + 1)
      if k == "disagree" || k == "opj-crash" then
        let key := s!"{k}: {dt}"
        opjDetail := opjDetail.insert key (opjDetail.getD key 0 + 1)
      if k == "disagree" then
        IO.println s!"DISAGREE {info}: {dt}"
        if diffSaved < 3 && saved < 200 then
          diffSaved := diffSaved + 1
          saved := saved + 1
          let m ← minimize (fun d => do
            let (k', _) ← opjDiff tmp L d
            pure (k' == "disagree")) data 60
          saveFinding o.findings (name "diff") data s!"{info}\n{dt}"
          saveFinding o.findings (name "diff-min") m
            s!"{info}\n{dt}\nminimised {data.size} -> {m.size} bytes"
      else if k == "opj-crash" then
        saveFinding o.findings (name "opj-crash") data s!"{info}\n{dt}"
    if (i - o.start + 1) % step == 0 then
      IO.println s!"  ... {i - o.start + 1}/{o.iters}"
      (← IO.getStdout).flush
  if o.inflight then
    try IO.FS.removeFile inflight catch _ => pure ()
  if o.opj then IO.FS.removeDirAll tmp
  -- summary
  IO.println "== summary =="
  IO.println s!"cases {o.iters}, total decode time {ms totalNs} ms, peak RSS {maxPeak / 1024} MB"
  let sorted := hist.toArray.qsort (fun a b => a.2 > b.2)
  for (k, n) in sorted do IO.println s!"  {k}: {n}"
  IO.println s!"slow (> {o.slowFactor}x seed time, floor {o.slowFloorMs} ms): {slowN}"
  IO.println s!"limit escapes: {escapes}"
  if o.opj then
    IO.println "opj differential (inputs we accept):"
    for (k, n) in opjH.toArray.qsort (fun a b => a.1 < b.1) do IO.println s!"  {k}: {n}"
    for (k, n) in opjDetail.toArray.qsort (fun a b => a.2 > b.2) do IO.println s!"    {k}: {n}"
  IO.println "slowest:"
  for (ns, r, info) in top do IO.println s!"  {ms ns} ms ({r / 10}x): {info}"
  let disagreements := (opjH.getD "disagree" 0)
  return if escapes > 0 || (o.failSlow && slowN > 0) || (o.failDiff && disagreements > 0)
    then 1 else 0

end Fuzz

/-- Entry point of `lake exe fuzz`. -/
def main (args : List String) : IO UInt32 := do
  match Fuzz.parseArgs args {} with
  | .error e => IO.eprintln s!"fuzz: {e}"; return 2
  | .ok o => Fuzz.run o
