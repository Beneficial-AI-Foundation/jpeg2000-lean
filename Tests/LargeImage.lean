import JPEG2000.Image
import Tests.Header
import Tests.Decode

/-!
# Reduce-aware resource limits and a large real image (task 6.5)

Plan.md §3 rule 3, §4 S3, §6 item 7 (reduced-resolution decoding for viewers), §8.4 (≥ 20 Mpx
benchmark candidate), §9 (safe-pdf's limits). T.800 B.2, B-12, B-14.

Since 6.5 the header (`Header.checkGeometry`) bounds what the stream **declares** (image side,
area, tiles, tile-components) and the sample and byte budgets (`maxWorkSamples`,
`maxDecodedBytes`) bound what is **allocated**: the output grids at the requested reduction
(`Decode.allocOutput`) and one tile's reduced working set (`Assemble.decodeTile`).

* Unit tests on hand-built streams (`Tests.Header` builders): a header whose full-resolution
  samples or bytes exceed the budget still parses; `decodeCodestream` at reduce 0 is refused
  with `limit workSamples` / `limit decodedBytes`; at reduce 1 (a quarter of the cells) it is
  accepted; a 4-tile image decodes with `maxWorkSamples` equal to its output cells (one tile's
  working set does not count against the output budget twice); declared-geometry limits
  (`imageArea`) still refuse a huge declared image at any reduction.
* `issue19517-8.jpx` (12608×16806, 4 components, 1 tile, 5/3, from pdf.js `issue19517.pdf`;
  `corpus/manifest.json` `pdf_jpx`): under `Limits.default` the full-resolution decode is
  refused before any plane is allocated (`workSamples 847560192 > 268435456`) and the header
  is accepted (cheap, always run). With `JPEG2000_LARGE_IMAGE=1` it is decoded at reduce 2
  (`JPEG2000.decode Limits.default`, 3152×4202) and compared bit-exactly with
  `opj_decompress -r 2` (skipped without OpenJPEG); `JPEG2000_LARGE_IMAGE_REDUCE=k` picks
  another reduction (`k = 0` uses raised limits: about 7.5 GB of memory). Skipped when the
  corpus file is absent.
-/

namespace JPEG2000.Tests.LargeImage

open JPEG2000 JPEG2000.Bytes JPEG2000.Marker JPEG2000.Header
open JPEG2000.Tests.Header (kind sizBody stream seg cod qcdNone comps3 be16 be32)

/-- Runs one named check, printing a line on failure; returns 1 on failure. -/
def expect (name : String) (ok : Bool) : IO Nat := do
  if ok then return 0
  IO.eprintln s!"  FAIL large-image: {name}"
  return 1

/-- Checks the outcome class of a computation (`Tests.Header.kind`). -/
def expectKind {α : Type} (name : String) (k : String) (x : Except Error α) : IO Nat := do
  let msg := match x with | .error e => s!" ({e})" | .ok _ => ""
  expect s!"{name}: expected {k}, got {kind x}{msg}" (kind x == k)

/-- A tile-part of tile `isot` (one tile-part, no header segments) whose body is `n` empty
packets (one zero byte each, T.800 B.10.3). -/
def tp (isot n : Nat) : List UInt8 :=
  let data : List UInt8 := List.replicate n 0
  be16 0xFF90 ++ be16 10 ++ be16 isot ++ be32 (12 + 2 + data.length) ++ [0, 1] ++
    be16 0xFF93 ++ data

/-- The corpus file. -/
def largeFile : System.FilePath := "corpus/files/pdf-jpx/issue19517-8.jpx"

/-- Unit tests of the reduce-aware checks on hand-built streams. -/
def units : IO Nat := do
  let mut f := 0
  let D := Limits.default
  -- one layer, NL 2 (3 resolutions), one precinct per resolution: 3 packets per component
  let one := tp 0 9
  let main := seg 0xFF52 (cod 0 0 1 0 2 4 4) ++ seg 0xFF5C (qcdNone (List.replicate 7 8))
  -- 64×64, three 8-bit components, one tile: 3·4096 cells at reduce 0, 3·1024 at reduce 1
  let s3 := stream (sizBody 64 64 0 0 64 64 0 0 comps3) main one
  let W : Limits := { D with maxWorkSamples := 3 * 4096 - 1 }
  f := f + (← expectKind "header ignores the sample budget" "ok" (parseCodestream W s3))
  f := f + (← expectKind "reduce 0 over the sample budget" "limit workSamples"
    (decodeCodestream W s3 0))
  f := f + (← expectKind "reduce 1 within the sample budget" "ok" (decodeCodestream W s3 1))
  f := f + (← expectKind "decode at reduce 0 over the sample budget" "limit workSamples"
    (decode W s3 {}))
  f := f + (← expectKind "decode at reduce 1 within the sample budget" "ok"
    (decode W s3 { reduce := 1 }))
  f := f + (← expectKind "exact sample budget" "ok"
    (decodeCodestream { D with maxWorkSamples := 3 * 4096 } s3 0))
  -- 16-bit samples count 2 bytes: 2·4096 at reduce 0, 2·1024 at reduce 1
  let s16 := stream (sizBody 64 64 0 0 64 64 0 0 [(15, 1, 1)]) main (tp 0 3)
  let B : Limits := { D with maxDecodedBytes := 2 * 4096 - 1 }
  f := f + (← expectKind "header ignores the byte budget" "ok" (parseCodestream B s16))
  f := f + (← expectKind "reduce 0 over the byte budget" "limit decodedBytes"
    (decodeCodestream B s16 0))
  f := f + (← expectKind "reduce 1 within the byte budget" "ok" (decodeCodestream B s16 1))
  -- four 32×32 tiles: the output (3·4096 cells) and one tile's set (3·1024) are separate
  let tiles4 := stream (sizBody 64 64 0 0 32 32 0 0 comps3) main
    (tp 0 9 ++ tp 1 9 ++ tp 2 9 ++ tp 3 9)
  f := f + (← expectKind "4 tiles at the exact output budget" "ok"
    (decodeCodestream { D with maxWorkSamples := 3 * 4096 } tiles4 0))
  f := f + (← expectKind "4 tiles, reduce 1, budget = reduced output" "ok"
    (decodeCodestream { D with maxWorkSamples := 3 * 1024 } tiles4 1))
  f := f + (← expectKind "4 tiles, reduce 1, budget below reduced output" "limit workSamples"
    (decodeCodestream { D with maxWorkSamples := 3 * 1024 - 1 } tiles4 1))
  -- declared geometry is still bounded at any reduction
  let sq := stream (sizBody 20000 20000 0 0 20000 20000 0 0 [(7, 1, 1)]) main (tp 0 3)
  f := f + (← expectKind "declared area > 2^28 at reduce 3" "limit imageArea"
    (decodeCodestream D sq 3))
  -- reduce is checked against maxDecompLevels first
  f := f + (← expectKind "reduce > maxDecompLevels" "limit decompLevels"
    (decodeCodestream D s3 33))
  return f

/-- Compares an 8-bit component plane with an 8-bit PGX file byte by byte; the number of
differing samples, or `none` when the file is not an 8-bit PGX of the plane's size. -/
def comparePgx8 (b : ByteArray) (c : CodestreamComponent) : Option Nat := Id.run do
  let n := c.width * c.height
  let mut nl := 0
  for i in [0:min b.size 64] do
    if b.get! i == 10 then nl := i; break
  if nl == 0 || b.size != nl + 1 + n || c.depth > 8 then return none
  let mut bad := 0
  for i in [0:n] do
    if (c.get? i).getD 0 != ((b.get! (nl + 1 + i)).toNat : Int) then bad := bad + 1
  return some bad

/-- Decodes the large file at reduction `r` and compares it with `opj_decompress -r r`. -/
def largeAt (data : ByteArray) (r : Nat) : IO Nat := do
  let L : Limits := if r = 0 then
    { maxWorkSamples := 1 <<< 30, maxDecodedBytes := 1 <<< 32 } else Limits.default
  let t0 ← IO.monoMsNow
  match decodeCodestream L data r with
  | .error e =>
    IO.println s!"  FAIL issue19517-8 reduce {r}: {e}"
    return 1
  | .ok img =>
    let t1 ← IO.monoMsNow
    let first := img.comps.getD 0 default
    IO.println s!"  issue19517-8 reduce {r}: {img.comps.size} × {first.width}×{first.height} in {t1 - t0} ms"
    let mut fails ← Tests.Decode.checkStructure s!"issue19517-8 r{r}" img r
    if !(← Tests.Decode.haveOpj) then
      IO.println "  issue19517-8: OpenJPEG comparison skipped (no opj_decompress)"
      return fails
    let dir : System.FilePath := s!"/tmp/jpeg2000-large-{← IO.monoNanosNow}"
    IO.FS.createDirAll dir
    let cs := data.extract img.header.codestream.start
      (img.header.codestream.start + img.header.codestream.len)
    let src := dir / "x.j2k"
    IO.FS.writeBinFile src cs
    let args := #["-i", src.toString, "-o", (dir / "x.pgx").toString] ++
      (if r > 0 then #["-r", toString r] else #[])
    let o ← IO.Process.output { cmd := "opj_decompress", args }
    if o.exitCode != 0 then
      IO.println s!"  FAIL issue19517-8 reduce {r}: opj_decompress failed"
      IO.FS.removeDirAll dir
      return fails + 1
    for k in [0:img.comps.size] do
      let p := dir / s!"x_{k}.pgx"
      let b ← if ← p.pathExists then IO.FS.readBinFile p else pure ByteArray.empty
      match comparePgx8 b (img.comps.getD k default) with
      | some 0 => pure ()
      | some n =>
        IO.println s!"  FAIL issue19517-8 reduce {r} comp {k}: {n} samples differ from OpenJPEG"
        fails := fails + 1
      | none =>
        IO.println s!"  FAIL issue19517-8 reduce {r} comp {k}: no comparable OpenJPEG output"
        fails := fails + 1
    IO.FS.removeDirAll dir
    if fails == 0 then
      IO.println s!"  issue19517-8 reduce {r}: bit-identical to opj_decompress -r {r}"
    return fails

/-- The large-file checks. -/
def large : IO Nat := do
  if !(← largeFile.pathExists) then
    IO.println "  issue19517-8: corpus file absent, skipped"
    return 0
  let data ← IO.FS.readBinFile largeFile
  let mut f := 0
  f := f + (← expectKind "issue19517-8 header under default limits" "ok"
    (Header.parse Limits.default data))
  -- full resolution: refused by the output check, before any plane is allocated
  let r0 := decodeCodestream Limits.default data 0
  let msg := match r0 with
    | .error (.limitExceeded _ .workSamples v b) => s!"{v} {b}"
    | _ => kind r0
  f := f + (← expect s!"issue19517-8 reduce 0 refused: workSamples 847560192 > 268435456 (got {msg})"
    (msg == "847560192 268435456"))
  if (← IO.getEnv "JPEG2000_LARGE_IMAGE") != some "1" then
    IO.println "  issue19517-8: full decode skipped (set JPEG2000_LARGE_IMAGE=1)"
    return f
  let r := ((← IO.getEnv "JPEG2000_LARGE_IMAGE_REDUCE").bind String.toNat?).getD 2
  f := f + (← largeAt data r)
  return f

/-- Runs the suite; returns the number of failures. -/
def run : IO Nat := do
  return (← units) + (← large)

end JPEG2000.Tests.LargeImage
