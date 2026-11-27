import JPEG2000.Image
import Tests.Pgx
import Tests.ConformanceData

/-!
# JP2 conformance with colour-managed references (task 6.3a)

Plan.md §1 (ICC profiles are passed through; the library applies no ICC transform), §7 row 6
(exit M6: the JP2 conformance files render identically to OpenJPEG + colour management within
tolerance), §8.1 (conformance). ITU-T T.800 Annex I (JP2: `colr` I.5.3.3, METH 2 restricted
ICC profile; `pclr`, `cmap`, `cdef`), T.803 Table G.1 (tolerances).

Every TIFF entry of `corpus/manifest.json` (`jp2_N.tif`, the reference decodes of
`file1…9.jp2`, made by OpenJPEG with `opj_decompress -p 8S -force-rgb`) is checked:
`JPEG2000.decode` the file, render 8-bit RGB, compare each of the three reference planes
(a one-channel image is compared against each plane, as `-force-rgb` replicates grey) and
require `peak ≤ p`, `MSE ≤ m` per channel (OpenJPEG's `compare_images` semantics, exact).

**Without an ICC profile** the rendering is `Image.interleaved8` in the given `Scaling`
(default `.linear`, the library default).

**With a `colr` METH 2 profile** (file5: RGB ROMM profile, file7: 16-bit e-sRGB profile,
file8: grey profile) the harness reproduces OpenJPEG + colour management
(`color_apply_icc_profile`, `src/bin/common/color.c` at uclouvain/openjpeg@8314119), which
runs before the `-p 8S` precision step:

* profile colour space `RGB ` with three colour channels of equal depth and sign, or `GRAY`
  with one colour channel (any other combination: OpenJPEG leaves the image unconverted, and
  so does the harness);
* the raw samples (no scaling) go into an lcms2 transform embedded profile → lcms2's
  built-in sRGB at the profile header's rendering intent, 8-bit when the depth is ≤ 8 and
  16-bit otherwise (the raw values as 16-bit numbers); grey → RGB;
* the transform is done by `scripts/icc-apply.py` (lcms2's `tificc`, test-only, Debian
  package `liblcms2-utils`);
* the RGB result is then scaled from the component depth to 8 bits with `scaleNat mode`
  (`.opj` is exactly `-p 8S`).

The harness supports the depths the corpus has (8 and 16, unsigned); others fail with a
note. When `tificc` (or `python3`) is absent the ICC files are skipped with the reason; the
other files always run. Skips when the corpus is absent.

`run` (registered in `lake exe tests`) checks all nine; `Tests.Conformance` reports the same
outcomes as its `jp2` lines.
-/

namespace JPEG2000.Tests.JP2

open JPEG2000 JPEG2000.Tests.Pgx JPEG2000.Tests.ConformanceData

/-- The outcome of one JP2 TIFF reference entry. -/
structure Result where
  /-- The entry. -/
  entry : RefEntry
  /-- Not compared (corpus file missing, or ICC file without `tificc`). -/
  skipped : Bool := false
  /-- Every channel within the entry's thresholds. -/
  pass : Bool := false
  /-- Per-channel metrics (R, G, B), when compared. -/
  metrics : Array Metrics := #[]
  /-- The embedded ICC profile was applied through lcms2. -/
  icc : Bool := false
  /-- Explanation (error, skip reason, how the profile was handled). -/
  note : String := ""

/-- The helper script applying an ICC profile (relative to the repository root). -/
def iccScript : String := "scripts/icc-apply.py"

/-- Exit status of `iccScript` when `tificc` is missing. -/
def skipExit : UInt32 := 3

/-- Why the ICC harness cannot run (`none` when `scripts/icc-apply.py --check` finds
`tificc`): `tificc` or `python3` missing. -/
def iccUnavailable : IO (Option String) := do
  try
    let o ← IO.Process.output { cmd := "python3", args := #["-I", iccScript, "--check"] }
    if o.exitCode == 0 then return none
    if o.exitCode == skipExit then return some o.stdout.trimAscii.toString
    return some s!"python3 {iccScript} --check: exit {o.exitCode} {o.stderr.trimAscii.toString}"
  catch e => return some s!"cannot run python3: {e}"

/-- The colour-space signature of an ICC profile header (bytes 16–19), e.g. `"RGB "`. -/
def iccSpace (p : ByteArray) : String :=
  String.ofList ((List.range 4).map fun i => Char.ofNat (p.get! (16 + i)).toNat)

/-- The raw samples of `chs`, pixel-interleaved, each reduced modulo `2^bits` (OpenJPEG's
`(unsigned char)` / `(unsigned short)` cast), 1 byte or 2 bytes big-endian. -/
def rawSamples (chs : Array Channel) (n bits : Nat) : ByteArray := Id.run do
  let wide := bits > 8
  let mut out := ByteArray.emptyWithCapacity (n * chs.size * (if wide then 2 else 1))
  for i in [0:n] do
    for c in chs do
      let v := (((c.plane.get? i).getD 0).toInt % (2 ^ bits : Int)).toNat
      if wide then
        out := (out.push (v / 256).toUInt8).push (v % 256).toUInt8
      else
        out := out.push v.toUInt8
  return out

/-- Channel `c` of `nc` interleaved samples (`bits` 8 or 16 big-endian), as naturals. -/
def channelNat (buf : ByteArray) (nc c bits : Nat) : Array Nat := Id.run do
  let b := if bits > 8 then 2 else 1
  let n := buf.size / (nc * b)
  let mut out := Array.mkEmpty n
  for i in [0:n] do
    let p := (i * nc + c) * b
    out := out.push (if b == 2 then (buf.get! p).toNat * 256 + (buf.get! (p + 1)).toNat
                     else (buf.get! p).toNat)
  return out

/-- The outcome of applying a profile: the RGB samples, a skip, or an error. -/
inductive IccOut where
  /-- Interleaved RGB at the transform's width. -/
  | ok (rgb : ByteArray)
  /-- `tificc`/`python3` unavailable. -/
  | skip (why : String)
  /-- Failure. -/
  | error (why : String)

/-- Runs `iccScript` on raw samples (1 or 3 channels, 8 or 16 bits) in a temporary
directory. -/
def applyIcc (profile : ByteArray) (w h nc bits : Nat) (raw : ByteArray) : IO IccOut := do
  try
    IO.FS.withTempDir fun dir => do
      let prof := dir / "profile.icc"
      let src := dir / "in.raw"
      let dst := dir / "out.raw"
      IO.FS.writeBinFile prof profile
      IO.FS.writeBinFile src raw
      let o ← IO.Process.output
        { cmd := "python3",
          args := #["-I", iccScript, "--profile", prof.toString, "--width", toString w,
                    "--height", toString h, "--channels", toString nc, "--bits", toString bits,
                    src.toString, dst.toString] }
      if o.exitCode == skipExit then return .skip o.stdout.trimAscii.toString
      if o.exitCode != 0 then
        return .error s!"icc-apply exit {o.exitCode}: {o.stderr.trimAscii.toString}"
      return .ok (← IO.FS.readBinFile dst)
  catch e => return .skip s!"cannot run python3 {iccScript}: {e}"

/-- Our 8-bit rendering as three channels of naturals (or one, for grey without ICC), the
ICC handling note, and whether the profile was applied. `none` channels = skipped. -/
def render (img : JPEG2000.Image) (mode : Scaling) :
    IO (Except String (Option (Array (Array Nat)) × String × Bool)) := do
  let unmanaged (why : String) : Except String (Option (Array (Array Nat)) × String × Bool) :=
    match img.interleaved8 {} (mode := mode) with
    | .error e => .error s!"interleaved8: {e}"
    | .ok buf =>
      let nc := img.channels.size
      .ok (some ((List.range nc).toArray.map fun c => channelNat buf nc c 8), why, false)
  let some prof := img.iccProfile | return unmanaged ""
  if prof.size < 128 then return unmanaged "ICC profile too short; not applied (as OpenJPEG)"
  let sp := iccSpace prof
  let chs := img.channels
  let applicable := (sp == "RGB " && chs.size == 3) || (sp == "GRAY" && chs.size == 1)
  let some c0 := chs[0]? | return .error "no colour channel"
  if !applicable || !chs.all (fun c => c.depth == c0.depth && c.signed == c0.signed) then
    return unmanaged s!"ICC '{sp}' with {chs.size} channels: not applied (as OpenJPEG)"
  if c0.signed || !(c0.depth == 8 || c0.depth == 16) then
    return .error s!"ICC harness supports unsigned 8/16-bit only (depth {c0.depth}, signed {c0.signed})"
  let bits := c0.depth
  if let some why := ← iccUnavailable then return .ok (none, s!"ICC file: {why}", true)
  let n := img.width * img.height
  match ← applyIcc prof img.width img.height chs.size bits (rawSamples chs n bits) with
  | .skip why => return .ok (none, why, true)
  | .error why => return .error why
  | .ok rgb =>
    if rgb.size != n * 3 * (bits / 8) then return .error "icc-apply: wrong output size"
    let planes := (List.range 3).toArray.map fun c =>
      (channelNat rgb 3 c bits).map (scaleNat mode bits 8 ·)
    return .ok (some planes, s!"ICC '{sp}' {bits}-bit applied via lcms2 (tificc) → sRGB", true)

/-- Checks one TIFF entry in `mode`. -/
def check (e : RefEntry) (mode : Scaling := .linear) : IO Result := do
  let path : System.FilePath := filesRoot ++ e.stream
  if !(← path.pathExists) then
    return { entry := e, skipped := true, note := s!"{path} missing" }
  let data ← IO.FS.readBinFile path
  match decode {} data { reduce := e.reduce } with
  | .error err => return { entry := e, note := s!"decode error: {err}" }
  | .ok img =>
    match ← render img mode with
    | .error m => return { entry := e, note := m }
    | .ok (none, why, icc) => return { entry := e, skipped := true, icc, note := why }
    | .ok (some planes, why, icc) =>
      let refs ← loadReference e
      if planes.size != 1 && planes.size != refs.size then
        return { entry := e, icc, note := s!"{planes.size} channels vs {refs.size} reference planes" }
      let mut ms : Array Metrics := #[]
      for h : k in [0:refs.size] do
        let ours : PgxImage :=
          { width := img.width, height := img.height, depth := 8, signed := false,
            samples := (planes.getD (if planes.size == 1 then 0 else k) #[]).map (Int.ofNat ·) }
        match compare ours refs[k] with
        | .error m => return { entry := e, icc, note := m }
        | .ok m => ms := ms.push m
      let ok := ms.all (·.within e)
      return { entry := e, pass := ok, metrics := ms, icc,
               note := if ok then why else if why.isEmpty then "outside thresholds"
                 else s!"outside thresholds; {why}" }

/-- `n / d` with three decimals, rounded down. -/
def fmt3 (n d : Nat) : String :=
  if d = 0 then "0" else
    let v := n * 1000 / d
    let f := toString (v % 1000)
    s!"{v / 1000}.{"".pushn '0' (3 - f.length)}{f}"

/-- The file name of an entry's stream (`…/file5.jp2` → `file5.jp2`). -/
def fileName (e : RefEntry) : String := (e.stream.splitOn "/").getLast?.getD e.stream

/-- One report line. -/
def line (r : Result) : String :=
  let tag := if r.skipped then "SKIP" else if r.pass then "PASS" else "FAIL"
  let ms := if r.metrics.isEmpty then "-" else
    ", ".intercalate (r.metrics.toList.map fun m => s!"peak {m.peak} mse {fmt3 m.sumSq m.count}")
  let note := if r.note.isEmpty then "" else s!" — {r.note}"
  s!"{tag} {fileName r.entry} jp2 r{r.entry.reduce} [{ms}] (limits peak {fmt3 r.entry.peak.num r.entry.peak.den} \
    mse {fmt3 r.entry.mse.num r.entry.mse.den} per channel){note}"

/-- Checks every TIFF entry of the table (in manifest order). -/
def evaluate (t : Array RefEntry) (mode : Scaling := .linear) : IO (Array Result) :=
  (t.filter (·.isTiff)).mapM (check · mode)

/-- Test-suite hook: all nine files (default scaling `.linear`; `.opj` printed for
information); returns the number of failures (0 with a message when the corpus is absent). -/
def run : IO Nat := do
  if !(← (filesRoot : System.FilePath).pathExists) then
    IO.println "  jp2: corpus not present, skipping"
    return 0
  let t ← load
  let rs ← evaluate t
  for r in rs do IO.println s!"  {line r}"
  for r in ← evaluate t .opj do IO.println s!"  (info, -p 8S scaling) {line r}"
  let fails := (rs.filter fun r => !r.skipped && !r.pass).size
  let skipped := (rs.filter (·.skipped)).size
  IO.println s!"  jp2: {(rs.filter (·.pass)).size}/{rs.size} pass, {skipped} skipped"
  return fails

end JPEG2000.Tests.JP2
