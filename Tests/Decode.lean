import JPEG2000.Decode

/-!
# Tests: the decoding pipeline `JPEG2000.decodeCodestream` (task 5.5)

Plan.md §3 (pipeline), §6 item 7 (reduced resolution), §8 (differential testing against
OpenJPEG); T.800 B.3, B-12, B-14, Annexes D–H.

1. **Structure.** Every T.803 stream (`p0_*`, `p1_*`) and `file1…9.jp2` decodes; the
   component count, sizes, depths and signedness equal what the SIZ of `opj_dump`/our header
   imply (each component on its own grid: `⌈Xsiz/XRsiz⌉ − ⌈XOsiz/XRsiz⌉`, …) and the
   dimensions of OpenJPEG's per-component output.
2. **Bit-exact vs `opj_decompress`** for every component coded with the reversible 5/3: the
   codestream (for JP2 files the `jp2c` contents, so that OpenJPEG applies no colour
   handling) is written to a scratch directory, decoded with
   `opj_decompress -i x.j2k -o x.pgx` (one `x_<c>.pgx` per component) and compared sample by
   sample.
3. **9/7 components**: the maximum absolute difference per component is printed; it fails
   only beyond a loose sanity bound (4 at depth ≤ 12, 64 above). The class thresholds are
   task 5.6b's.
4. **Reduced resolution**: `reduce = 1, 2` on a few streams vs `opj_decompress -r`
   (bit-exact for 5/3; `reduce = 0` is the full decode by definition and checked equal to the
   default call). `p1_06` (3×3 tiles, NL 4) only at `reduce = 1`: `opj_decompress -r 2`
   fails on it ("failed to decode image") while we decode it.
5. **ROI streams** (`p0_03`, `p0_06`, `p0_13`, `p0_15`): compared with OpenJPEG *and* with
   the T.803 reference decodes `baseline/conformance/c1<stream>_<c>.pgx`; differences are
   printed (Decision 5.1: our ROI follows T.800 H, OpenJPEG thresholds a doubled value) and
   are failures only against the T.803 reference (reversible components); the 9/7 sanity
   bound does not apply to them (p0_06 component 0 is a 9/7 ROI component).

The PGX reader here is private to this suite (task 5.6a writes the official one).

6. **Passes below bit-plane 0** (task 5.8): the non-regression streams `test_lossless.j2k`
   (5/3, bit-exact) and `kodak_2layers_lrcp.j2c` (9/7 + ICT, two layers) signal more passes
   than `3K − 2` for some code-blocks; they go through (1)–(3). `kodak_2layers_lrcp.j2c` is
   compared leniently (`knownDiff`: OpenJPEG's 109-pass segment cap changes its Tier-2
   parse of that stream).

Defaults keep the suite fast: the large streams `p0_07`, `p0_08`, `p0_05`, `p1_03` and
`file*.jp2` run only with `JPEG2000_DECODE_ALL=1`. Skips cleanly when `corpus/files` or
`opj_decompress` is missing (only the structure checks need no OpenJPEG).
-/

namespace JPEG2000.Tests.Decode

open JPEG2000 JPEG2000.Bytes JPEG2000.Marker JPEG2000.Header

/-- The conformance input directory. -/
def inputDir : System.FilePath := "corpus/files/openjpeg-data/input/conformance"

/-- The OpenJPEG non-regression input directory. -/
def nonregDir : System.FilePath := "corpus/files/openjpeg-data/input/nonregression"

/-- The T.803 reference decodes. -/
def baselineDir : System.FilePath := "corpus/files/openjpeg-data/baseline/conformance"

/-- A PGX image: dimensions, depth, signedness and samples (row-major). -/
structure Pgx where
  /-- Width. -/
  width : Nat
  /-- Height. -/
  height : Nat
  /-- Bit depth. -/
  depth : Nat
  /-- Signed samples. -/
  signed : Bool
  /-- Samples. -/
  samples : Array Int

/-- Skips ASCII spaces from `i`. -/
private def skipSp (b : ByteArray) : Nat → Nat → Nat
  | 0, i => i
  | k + 1, i => if b.get! i == 32 then skipSp b k (i + 1) else i

/-- Reads a decimal number from `i`. -/
private def readNum (b : ByteArray) : Nat → Nat → Nat → Nat × Nat
  | 0, i, acc => (acc, i)
  | k + 1, i, acc =>
    let c := if i < b.size then b.get! i else 0
    if 48 ≤ c ∧ c ≤ 57 then readNum b k (i + 1) (acc * 10 + (c - 48).toNat) else (acc, i)

/-- Parses a PGX file (`PG ML|LM [+|-]depth width height` then one whitespace byte, then
1/2/4-byte samples). -/
def parsePgx (b : ByteArray) : Option Pgx := do
  if b.size < 8 ∨ b.get! 0 != 80 ∨ b.get! 1 != 71 then none
  let n := b.size
  let i := skipSp b n 2
  let big := b.get! i == 77   -- 'M' of "ML"
  let i := skipSp b n (i + 2)
  let (signed, i) :=
    if b.get! i == 45 then (true, i + 1) else if b.get! i == 43 then (false, i + 1) else (false, i)
  let i := skipSp b n i
  let (depth, i) := readNum b n i 0
  let i := skipSp b n i
  let (w, i) := readNum b n i 0
  let i := skipSp b n i
  let (h, i) := readNum b n i 0
  let start := i + 1
  let bps := if depth ≤ 8 then 1 else if depth ≤ 16 then 2 else 4
  if start + w * h * bps > b.size then none
  let mut out : Array Int := Array.mkEmpty (w * h)
  for k in [0:w * h] do
    let o := start + k * bps
    let mut v : Nat := 0
    for j in [0:bps] do
      let byte := (b.get! (o + (if big then j else bps - 1 - j))).toNat
      v := v * 256 + byte
    let vi : Int := if signed ∧ v ≥ 2 ^ (8 * bps - 1) then (v : Int) - 2 ^ (8 * bps) else v
    out := out.push vi
  return { width := w, height := h, depth, signed, samples := out }

/-- Reads a PGX file. -/
def readPgx (p : System.FilePath) : IO (Option Pgx) := do
  if !(← p.pathExists) then return none
  return parsePgx (← IO.FS.readBinFile p)

/-- The samples of a decoded component as integers. -/
def samplesOf (c : DecodedComponent) : Array Int := Id.run do
  let mut out : Array Int := Array.mkEmpty (c.width * c.height)
  for i in [0:c.width * c.height] do
    out := out.push ((c.plane.get? i).getD 0).toInt
  return out

/-- Maximum absolute difference and number of differing samples (sizes must match). -/
def diff (a b : Array Int) : Nat × Nat := Id.run do
  let mut m := 0
  let mut n := 0
  for i in [0:min a.size b.size] do
    let d := ((a.getD i 0) - (b.getD i 0)).natAbs
    if d > 0 then n := n + 1
    if d > m then m := d
  return (m, n)

/-- Mean squared difference ×10, rounded down (printed with one decimal). -/
def mse10 (a b : Array Int) : Nat := Id.run do
  let mut s := 0
  for i in [0:min a.size b.size] do
    s := s + (((a.getD i 0) - (b.getD i 0)).natAbs) ^ 2
  return if a.size = 0 then 0 else s * 10 / a.size

/-- Renders a value ×10 with one decimal. -/
def dec1 (v : Nat) : String := s!"{v / 10}.{v % 10}"

/-- Whether `opj_decompress` can be run. -/
def haveOpj : IO Bool := do
  try
    let o ← IO.Process.output { cmd := "opj_decompress", args := #["-h"] }
    return o.exitCode == 0 || o.exitCode == 1
  catch _ => return false

/-- Runs `opj_decompress` on a codestream into `<dir>/<stem>.pgx` (`-r reduce` when
positive); returns the per-component PGX images (`<stem>_<c>.pgx`), `none` on failure. -/
def opjDecode (dir : System.FilePath) (stem : String) (cs : ByteArray) (nc reduce : Nat) :
    IO (Option (Array Pgx)) := do
  let src := dir / s!"{stem}.j2k"
  IO.FS.writeBinFile src cs
  let args := #["-i", src.toString, "-o", (dir / s!"{stem}.pgx").toString] ++
    (if reduce > 0 then #["-r", toString reduce] else #[])
  let o ← IO.Process.output { cmd := "opj_decompress", args }
  if o.exitCode != 0 then return none
  let mut out := #[]
  for c in [0:nc] do
    let p := dir / s!"{stem}_{c}.pgx"
    match ← readPgx p with
    | some x => out := out.push x; IO.FS.removeFile p
    | none => return none
  IO.FS.removeFile src
  return some out

/-- Whether component `c` uses the reversible 5/3 in every tile (main defaults and every
tile's merged parameters). -/
def reversibleComp (h : Header) (c : Nat) : Bool :=
  let rev := fun (cd : Coding) => ((cd.comps.getD c default).transform == .reversible53)
  rev h.defaults && h.tiles.all (rev ·.coding)

/-- Expected component geometry from SIZ: `(x0, y0, width, height)` at reduction `r`. -/
def expectedRect (s : SIZ) (c : Component) (r : Nat) : Nat × Nat × Nat × Nat :=
  let rc := compRect (imageRect s) c
  let x0 := cdivPow rc.x0 r
  let y0 := cdivPow rc.y0 r
  (x0, y0, cdivPow rc.x1 r - x0, cdivPow rc.y1 r - y0)

/-- Structure check (1): component count, rectangles, depths, signedness from SIZ. -/
def checkStructure (name : String) (img : DecodedImage) (r : Nat) : IO Nat := do
  let s := img.header.siz
  let mut fails := 0
  if img.comps.size != s.csiz then
    IO.println s!"  FAIL {name}: {img.comps.size} components, SIZ says {s.csiz}"
    return 1
  for i in [0:s.csiz] do
    let c := s.components.getD i default
    let d := img.comps.getD i default
    let (x0, y0, w, hh) := expectedRect s c r
    if d.x0 != x0 || d.y0 != y0 || d.width != w || d.height != hh || d.depth != c.depth.toNat ||
        d.signed != c.signed || d.plane.width != w || d.plane.height != hh then
      IO.println s!"  FAIL {name} comp {i}: got ({d.x0},{d.y0}) {d.width}×{d.height} depth {d.depth} signed {d.signed}, expected ({x0},{y0}) {w}×{hh} depth {c.depth.toNat}"
      fails := fails + 1
  return fails

/-- Compares a decode with OpenJPEG's output. Reversible components must be bit-exact
(unless `lenient`, for the ROI streams); 9/7 components print their maximum difference and
fail beyond the sanity bound. Returns the failures and the per-component `(max, count)`. -/
def compareOpj (name : String) (img : DecodedImage) (ref : Array Pgx) (lenient : Bool) :
    IO (Nat × Array (Nat × Nat)) := do
  let mut fails := 0
  let mut res := #[]
  if ref.size != img.comps.size then
    IO.println s!"  FAIL {name}: OpenJPEG gave {ref.size} components, we {img.comps.size}"
    return (1, #[])
  for i in [0:ref.size] do
    let d := img.comps.getD i default
    let p := ref.getD i ⟨0, 0, 0, false, #[]⟩
    if p.width != d.width || p.height != d.height then
      IO.println s!"  FAIL {name} comp {i}: OpenJPEG {p.width}×{p.height}, we {d.width}×{d.height}"
      fails := fails + 1
      res := res.push (0, 0)
      continue
    let (m, n) := diff (samplesOf d) p.samples
    res := res.push (m, n)
    if reversibleComp img.header i then
      if n != 0 then
        IO.println s!"  {if lenient then "DIFF" else "FAIL"} {name} comp {i} (5/3): {n} samples differ, max |Δ| = {m}"
        if !lenient then fails := fails + 1
    else
      let bound := if d.depth ≤ 12 then 4 else 64
      IO.println s!"  {name} comp {i} (9/7, {d.depth} bits): max |Δ| = {m}, {n} samples differ"
      if m > bound && !lenient then
        IO.println s!"  FAIL {name} comp {i}: 9/7 difference {m} > sanity bound {bound}"
        fails := fails + 1
  return (fails, res)

/-- Streams whose `opj_decompress` output is colour-converted even from the bare codestream:
three components with sub-sampled chroma are taken as sYCC and converted to RGB at full
size (`opj_decompress.c` guesses the colour space), so a per-component comparison is
impossible. Structure checks still run. -/
def opjConverts : List String := ["file3"]

/-- Streams with a known, explained difference from `opj_decompress` (compared leniently:
differences are printed, not failures). `kodak_2layers_lrcp.j2c` has a code-block
(comp 0, res 5, HL, precinct 18, block 3) that signals 172 passes in one packet; OpenJPEG
splits a plain-mode codeword segment after 109 passes (`opj_t2_init_seg`, `maxpasses = 109`)
and so reads two length fields where T.800 B.10.7.1 has one, and the two packet-header
parses diverge from there (task 5.8 report; Decision 4.4 "known difference"). -/
def knownDiff : List String := ["kodak_2layers_lrcp.j2c"]

/-- Decodes one stream and runs checks (1)–(3) (and (5) for ROI streams). -/
def checkStream (dir : System.FilePath) (opj : Bool) (name : String) (path : System.FilePath)
    (roi : Bool) : IO Nat := do
  let data ← IO.FS.readBinFile path
  let t0 ← IO.monoMsNow
  match decodeCodestream Limits.default data with
  | .error e =>
    IO.println s!"  FAIL {name}: {e}"
    return 1
  | .ok img =>
    let t1 ← IO.monoMsNow
    let mut fails ← checkStructure name img 0
    if img.saturatedBlocks != 0 then
      IO.println s!"  {name}: {img.saturatedBlocks} code-blocks saturated"
    if opj && opjConverts.contains name then
      IO.println s!"  {name}: OpenJPEG comparison skipped (opj_decompress converts sYCC 4:2:0 to RGB)"
    if opj && !opjConverts.contains name then
      let cs := data.extract img.header.codestream.start
        (img.header.codestream.start + img.header.codestream.len)
      match ← opjDecode dir name cs img.comps.size 0 with
      | none =>
        IO.println s!"  FAIL {name}: opj_decompress failed"
        fails := fails + 1
      | some ref =>
        if knownDiff.contains name then
          IO.println s!"  {name}: known Tier-2 deviation from OpenJPEG (plain-mode segments capped at 109 passes), differences reported, not failures"
        let (f, res) ← compareOpj name img ref (roi || knownDiff.contains name)
        fails := fails + f
        if roi then
          -- (5): T.803 reference decodes `c1<name>_<c>.pgx`.
          for i in [0:img.comps.size] do
            let some p ← readPgx (baselineDir / s!"c1{name}_{i}.pgx") | continue
            let d := img.comps.getD i default
            let (o, on) := res.getD i (0, 0)
            if p.width != d.width || p.height != d.height then
              IO.println s!"  FAIL {name} comp {i}: reference {p.width}×{p.height}, we {d.width}×{d.height}"
              fails := fails + 1
              continue
            let (m, n) := diff (samplesOf d) p.samples
            let os := (ref.getD i ⟨0, 0, 0, false, #[]⟩).samples
            let (mo, no) := diff os p.samples
            IO.println s!"  ROI {name} comp {i}: ours vs T.803 ref peak {m} mse {dec1 (mse10 (samplesOf d) p.samples)} ({n} differ); OpenJPEG vs ref peak {mo} mse {dec1 (mse10 os p.samples)} ({no} differ); ours vs OpenJPEG peak {o} ({on} differ)"
            if n != 0 && reversibleComp img.header i then fails := fails + 1
    IO.println s!"  {name}: {img.comps.size} components, {t1 - t0} ms"
    return fails

/-- Reduced-resolution check (4): `reduce = r` vs `opj_decompress -r r`. -/
def checkReduce (dir : System.FilePath) (opj : Bool) (name : String) (path : System.FilePath)
    (r : Nat) : IO Nat := do
  let data ← IO.FS.readBinFile path
  match decodeCodestream Limits.default data r with
  | .error e =>
    IO.println s!"  FAIL {name} reduce {r}: {e}"
    return 1
  | .ok img =>
    let mut fails ← checkStructure s!"{name} r{r}" img r
    if opj then
      let cs := data.extract img.header.codestream.start
        (img.header.codestream.start + img.header.codestream.len)
      match ← opjDecode dir s!"{name}_r{r}" cs img.comps.size r with
      | none =>
        IO.println s!"  FAIL {name} reduce {r}: opj_decompress failed"
        fails := fails + 1
      | some ref =>
        let (f, _) ← compareOpj s!"{name} r{r}" img ref false
        fails := fails + f
    return fails

/-- `reduce := 0` is the default call. -/
def checkReduceZero (path : System.FilePath) : IO Nat := do
  let data ← IO.FS.readBinFile path
  match decodeCodestream Limits.default data, decodeCodestream Limits.default data 0 with
  | .ok a, .ok b =>
    if a.comps.map (·.plane.data) == b.comps.map (·.plane.data) then return 0
    IO.println "  FAIL reduce 0 differs from the default decode"
    return 1
  | _, _ =>
    IO.println "  FAIL reduce 0 / default decode failed"
    return 1

/-- A reduction beyond NL is refused. -/
def checkReduceTooFar (path : System.FilePath) : IO Nat := do
  let data ← IO.FS.readBinFile path
  match decodeCodestream Limits.default data 40 with
  | .error _ => return 0
  | .ok _ =>
    IO.println "  FAIL reduce 40 accepted"
    return 1

/-- The streams of the default run (fast), the extra ones with `JPEG2000_DECODE_ALL=1`. -/
def defaultStreams : List String :=
  ["p0_01", "p0_02", "p0_03", "p0_04", "p0_06", "p0_09", "p0_10", "p0_11", "p0_12",
   "p0_13", "p0_14", "p0_15", "p0_16", "p1_01", "p1_02", "p1_04", "p1_05", "p1_06", "p1_07"]

/-- The large streams (only with `JPEG2000_DECODE_ALL=1`). -/
def bigStreams : List String :=
  ["p0_05", "p0_07", "p0_08", "p1_03"] ++ (List.range 9).map (s!"file{· + 1}")

/-- The ROI (RGN) streams. -/
def roiStreams : List String := ["p0_03", "p0_06", "p0_13", "p0_15"]

/-- Non-regression streams that signal more coding passes than `3K − 2` for some code-blocks
(task 5.8: the passes below bit-plane 0 are dropped, as OpenJPEG does). `test_lossless` is
5/3 (bit-exact); `kodak_2layers_lrcp` is 9/7 + ICT, 2 layers (`knownDiff`). -/
def nonregStreams : List String := ["test_lossless.j2k", "kodak_2layers_lrcp.j2c"]

/-- The file of a stream name. -/
def streamPath (n : String) : System.FilePath :=
  if nonregStreams.contains n then nonregDir / n
  else inputDir / (if n.startsWith "file" then s!"{n}.jp2" else s!"{n}.j2k")

/-- Runs the suite. -/
def run : IO Nat := do
  if !(← inputDir.pathExists) then
    IO.println "  decode: corpus/files absent, skipped"
    return 0
  let all := (← IO.getEnv "JPEG2000_DECODE_ALL").isSome
  let opj ← haveOpj
  if !opj then IO.println "  decode: opj_decompress missing, comparisons skipped"
  let dir : System.FilePath := s!".lake/tests-decode-{← IO.monoNanosNow}"
  IO.FS.createDirAll dir
  let mut fails := 0
  let streams := defaultStreams ++ nonregStreams ++ (if all then bigStreams else [])
  for n in streams do
    fails := fails + (← checkStream dir opj n (streamPath n) (roiStreams.contains n))
  -- (4) reduced resolution.
  let reduced : List (String × List Nat) :=
    [("p0_01", [1, 2]), ("p0_04", [1, 2]), ("p0_09", [1, 2]), ("p0_14", [1, 2]),
     ("p1_01", [1, 2]), ("p1_05", [1, 2]), ("p1_06", [1]), ("p1_07", [1])] ++
    (if all then [("p0_05", [1, 2]), ("p0_07", [1, 2]), ("p1_03", [1, 2]), ("file1", [1, 2]),
                  ("file6", [1, 2])] else [])
  for (n, rs) in reduced do
    for r in rs do
      fails := fails + (← checkReduce dir opj n (streamPath n) r)
  fails := fails + (← checkReduceZero (streamPath "p0_01"))
  fails := fails + (← checkReduceTooFar (streamPath "p0_01"))
  try IO.FS.removeDirAll dir catch _ => pure ()
  return fails

end JPEG2000.Tests.Decode
