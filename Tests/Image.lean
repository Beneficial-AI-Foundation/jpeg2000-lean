import JPEG2000.Image
import Encode.Encode
import Tests.Pgx

/-!
# Tests of the consumer API `JPEG2000.decode` (task 6.2)

Plan.md §1 ("What we build": output planes + interleaved 8/16-bit buffer), §8.1 (JP2
conformance), §9 (`/SMaskInData`).

* **Scaling** (`scaleNat`, `Scaler.apply`): edges at 1, 8, 12, 16, 32 bits, signed and
  unsigned, both modes; `Scaler.apply` agrees with `scaleNat` on sweeps.
* **Interleaving**: 8-bit and 16-bit big-endian layout, alpha last, size checks.
* **Up-sampling**: replication on the reference grid, even and odd origins.
* **End to end** on codestreams from the reference encoder (`Encode.encode`), raw and
  wrapped in hand-built JP2 boxes: unknown space, 1-bit, signed, 16-bit, `cdef` reordering
  and alpha, `/SMaskInData`, palette (applied and not).
* **Limits** refusals (`maxDecodedBytes`, `maxImageArea`, `maxWorkSamples`).
* **JP2 conformance** (`file1…9.jp2` against the reference TIFFs `jp2_N.tif` of the manifest,
  thresholds `peak`/`mse` per component): `interleaved8` (default scaling) compared channel
  by channel (a one-channel image against each of the three TIFF planes, as OpenJPEG's
  `-force-rgb`); per-channel peak error and MSE printed for both scalings. The files whose
  reference depends on ICC colour management (`iccFiles`) are reported, not required to pass.
  All nine run by default (about 3 s compiled). Skips when the corpus is absent.
-/

namespace JPEG2000.Tests.Image

open JPEG2000 JPEG2000.Bytes JPEG2000.Tests.Pgx JPEG2000.Tests.ConformanceData

/-- Runs one named check, printing a line on failure; returns 1 on failure, 0 on success. -/
def expect (name : String) (ok : Bool) : IO Nat := do
  if ok then return 0
  IO.eprintln s!"  FAIL image: {name}"
  return 1

/-- Whether a result is a `limitExceeded` error. -/
def isLimit {α : Type} : Except Error α → Bool
  | .error e => e.isLimit
  | .ok _ => false

/-- A plane from row-major values. -/
def mkPlane (w h : Nat) (vs : List Int) : Plane :=
  (vs.zipIdx.foldl (fun p (v, i) => (p.set? i (Int32.ofInt v)).getD p) (Plane.zero w h))

/-- A plane's values, row-major. -/
def vals (p : Plane) : List Int :=
  (List.range (p.width * p.height)).map fun i => ((p.get? i).getD 0).toInt

/-- Bytes as a list of naturals. -/
def bytes (b : ByteArray) : List Nat := b.toList.map (·.toNat)

/-! ## Scaling -/

/-- `Scaler.apply` on a raw sample (signed offset included) as a natural. -/
def sc (mode : Scaling) (d : Nat) (s : Bool) (t : Nat) (v : Int) : Nat :=
  ((Scaler.make mode d s t).apply (Int32.ofInt v)).toNat

/-- Scaling edge cases and agreement of `Scaler.apply` with `scaleNat`. -/
def scalingTests : IO Nat := do
  let mut f := 0
  -- 1-bit
  f := f + (← expect "1-bit → 8" ([0, 1].map (sc .linear 1 false 8) == [0, 255]))
  f := f + (← expect "1-bit → 8 opj" ([0, 1].map (sc .opj 1 false 8) == [0, 255]))
  f := f + (← expect "1-bit → 16" ([0, 1].map (sc .linear 1 false 16) == [0, 65535]))
  -- 8-bit identity, signed offset
  f := f + (← expect "8 → 8" ([0, 1, 128, 255].map (sc .linear 8 false 8) == [0, 1, 128, 255]))
  f := f + (← expect "signed 8 → 8" ([-128, -1, 0, 127].map (sc .linear 8 true 8) == [0, 127, 128, 255]))
  f := f + (← expect "8 → 16" ([0, 1, 255].map (sc .linear 8 false 16) == [0, 257, 65535]))
  -- 12-bit, 16-bit down
  f := f + (← expect "12 → 8 linear" ([0, 8, 4087, 4095].map (sc .linear 12 false 8) == [0, 0, 255, 255]))
  f := f + (← expect "12 → 8 opj" ([0, 15, 16, 4095].map (sc .opj 12 false 8) == [0, 0, 1, 255]))
  f := f + (← expect "16 → 8 linear" ([0, 128, 129, 32768, 65535].map (sc .linear 16 false 8)
    == [0, 0, 1, 128, 255]))
  f := f + (← expect "16 → 8 opj" ([0, 255, 256, 65535].map (sc .opj 16 false 8) == [0, 0, 1, 255]))
  f := f + (← expect "signed 16 → 8" ([-32768, 0, 32767].map (sc .linear 16 true 8) == [0, 128, 255]))
  -- 3-bit up: linear rounds, opj floors
  f := f + (← expect "3 → 8 linear" ((List.range 8).map (fun (v : Nat) => sc .linear 3 false 8 v)
    == [0, 36, 73, 109, 146, 182, 219, 255]))
  f := f + (← expect "3 → 8 opj" ((List.range 8).map (fun (v : Nat) => sc .opj 3 false 8 v)
    == [0, 36, 72, 109, 145, 182, 218, 255]))
  -- 32-bit signed and 31-bit unsigned extremes (UInt64 headroom)
  f := f + (← expect "signed 32 → 8" ([-2147483648, 0, 2147483647].map (sc .linear 32 true 8)
    == [0, 128, 255]))
  f := f + (← expect "signed 32 → 16" ([-2147483648, 2147483647].map (sc .linear 32 true 16)
    == [0, 65535]))
  f := f + (← expect "31 → 16" ([0, 2147483647].map (sc .linear 31 false 16) == [0, 65535]))
  -- out-of-range samples clamp
  f := f + (← expect "clamp" ([-5, 300].map (sc .linear 8 false 8) == [0, 255]))
  -- agreement with the Nat specification
  let mut bad := 0
  for mode in [Scaling.linear, .opj] do
    for d in [1, 2, 3, 5, 7, 8, 9, 12, 15, 16, 17, 24, 31] do
      for t in [8, 16] do
        let top := 2 ^ d - 1
        for k in [0:67] do
          let u := (k * 0x9E3779B1) % (top + 1)
          for v in [u, top - min top k] do
            if sc mode d false t v != scaleNat mode d t v then bad := bad + 1
            if v > top || scaleNat mode d t v > 2 ^ t - 1 then bad := bad + 1
  f := f + (← expect s!"apply = scaleNat ({bad} mismatches)" (bad == 0))
  return f

/-! ## Interleaving, up-sampling, soft mask -/

/-- A full-resolution channel. -/
def chan (w h d : Nat) (s : Bool) (vs : List Int) : Channel :=
  { depth := d, signed := s, plane := mkPlane w h vs }

/-- A hand-built image around channels (no decode behind it). -/
def handImage (w h : Nat) (cs : Array Channel) (a : Option Channel) (pm : Bool) : JPEG2000.Image :=
  { width := w, height := h, x0 := 0, y0 := 0, space := .sRGB, channels := cs, alpha := a,
    premultiplied := pm,
    decoded := { header := default, reduce := 0, comps := #[], saturatedBlocks := 0 } }

/-- Interleaving layout, soft mask selection, interleave refusals. -/
def interleaveTests : IO Nat := do
  let mut f := 0
  let r := chan 2 1 8 false [1, 2]
  let g := chan 2 1 8 false [3, 4]
  let a := chan 2 1 1 false [0, 1]
  let img := handImage 2 1 #[r, g] (some a) false
  f := f + (← expect "8-bit interleave" ((img.interleaved8 {}).toOption.map bytes == some [1, 3, 2, 4]))
  f := f + (← expect "8-bit interleave + alpha"
    ((img.interleaved8 {} (withAlpha := true)).toOption.map bytes == some [1, 3, 0, 2, 4, 255]))
  f := f + (← expect "16-bit big-endian"
    ((img.interleaved16 {}).toOption.map bytes == some [1, 1, 3, 3, 2, 2, 4, 4]))
  let w16 := handImage 2 1 #[chan 2 1 16 false [0x1234, 0xFFFF]] none false
  f := f + (← expect "16-bit identity BE"
    ((w16.interleaved16 {}).toOption.map bytes == some [0x12, 0x34, 0xFF, 0xFF]))
  f := f + (← expect "interleave limit" (isLimit (img.interleaved8 { maxDecodedBytes := 3 })))
  f := f + (← expect "interleave limit at size" ((img.interleaved8 { maxDecodedBytes := 4 }).toOption.isSome))
  let bad := handImage 2 1 #[r, chan 1 1 8 false [0]] none false
  f := f + (← expect "size mismatch refused" ((bad.interleaved8 {}).toOption.isNone))
  -- /SMaskInData
  f := f + (← expect "smask 0" (img.smaskInData 0).isNone)
  f := f + (← expect "smask 3" (img.smaskInData 3).isNone)
  f := f + (← expect "smask 1" ((img.smaskInData 1).map (fun m => (vals m.channel.plane, m.premultiplied))
    == some ([0, 1], false)))
  f := f + (← expect "smask 2" ((img.smaskInData 2).map (·.premultiplied) == some true))
  f := f + (← expect "smask 1, cdef premultiplied"
    (((handImage 2 1 #[r] (some a) true).smaskInData 1).map (·.premultiplied) == some true))
  f := f + (← expect "smask without alpha" ((handImage 2 1 #[r] none false).smaskInData 1).isNone)
  return f

/-- A sub-sampled colour channel. -/
def sub (w h dx dy : Nat) (vs : List Int) : Color.Channel :=
  { plane := mkPlane w h vs, format := { depth := 8, signed := false, dx, dy } }

/-- Replication on the reference grid. -/
def upsampleTests : IO Nat := do
  let mut f := 0
  -- origin 0, 4 × 2 image, 2 × 1 component with dx = dy = 2
  f := f + (← expect "2×2 replication, origin 0"
    ((Image.upsample 0 0 4 2 (sub 2 1 2 2 [7, 9])).toOption.map vals
      == some [7, 7, 9, 9, 7, 7, 9, 9]))
  -- origin (1, 1), image columns 1…4, rows 1…3: component columns ⌈1/2⌉ = 1 … ⌈5/2⌉ = 3 (2
  -- samples at X = 2, 4), rows 1 … 2 (1 sample at Y = 2); X = 1 clamps to the first column
  f := f + (← expect "odd origin"
    ((Image.upsample 1 1 4 3 (sub 2 1 2 2 [5, 6])).toOption.map vals
      == some [5, 5, 5, 6, 5, 5, 5, 6, 5, 5, 5, 6]))
  -- dx = 3, dy = 1
  f := f + (← expect "dx 3"
    ((Image.upsample 0 0 5 1 (sub 2 1 3 1 [1, 2])).toOption.map vals == some [1, 1, 1, 2, 2]))
  -- full resolution: plane shared
  f := f + (← expect "identity" ((Image.upsample 0 0 2 1 (sub 2 1 1 1 [3, 4])).toOption.map vals
    == some [3, 4]))
  f := f + (← expect "empty component refused"
    ((Image.upsample 1 0 1 1 (sub 0 0 4 1 [])).toOption.isNone))
  return f

/-! ## End to end on encoder output -/

/-- Big-endian bytes of `v` (`n` bytes). -/
def be (n v : Nat) : List UInt8 :=
  (List.range n).reverse.map fun k => (v / 2 ^ (8 * k) % 256).toUInt8

/-- A box with type `t` (4 ASCII characters). -/
def box (t : String) (body : List UInt8) : List UInt8 :=
  be 4 (8 + body.length) ++ t.toList.map (·.toNat.toUInt8) ++ body

/-- A JP2 file around a codestream: `ihdr`, an enumerated `colr`, and extra `jp2h` boxes. -/
def jp2 (w h nc bpc : Nat) (enumCs : Nat) (extra : List UInt8) (cs : ByteArray) : ByteArray :=
  let sig := box "jP  " [0x0D, 0x0A, 0x87, 0x0A]
  let ftyp := box "ftyp" (be 4 0x6A703220 ++ be 4 0 ++ be 4 0x6A703220)
  let ihdr := box "ihdr" (be 4 h ++ be 4 w ++ be 2 nc ++ [bpc.toUInt8, 7, 0, 0])
  let colr := box "colr" ([1, 0, 0] ++ be 4 enumCs)
  let jp2h := box "jp2h" (ihdr ++ colr ++ extra)
  ByteArray.mk (sig ++ ftyp ++ jp2h ++ box "jp2c" cs.toList).toArray

/-- A `cdef` box from `(Cn, Typ, Asoc)` triples. -/
def cdef (ds : List (Nat × Nat × Nat)) : List UInt8 :=
  box "cdef" (be 2 ds.length ++ ds.flatMap fun (c, t, a) => be 2 c ++ be 2 t ++ be 2 a)

/-- A component of `w × h` samples. -/
def comp (d : Nat) (s : Bool) (vs : List Int) : Encode.Component :=
  { depth := d, signed := s, samples := vs.toArray }

/-- Encodes a lossless image (2 levels, no MCT). -/
def enc (w h : Nat) (cs : List Encode.Component) : Except Error ByteArray :=
  Encode.encode { levels := 2, mct := false } { width := w, height := h, comps := cs.toArray }

/-- Decodes and returns the interleaved 8-bit bytes, if all succeeds. -/
def dec8 (d : ByteArray) (opts : DecodeOptions := {}) (withAlpha := false) : Option (List Nat) :=
  match decode {} d opts with
  | .ok img => (img.interleaved8 {} withAlpha).toOption.map bytes
  | .error _ => none

/-- End-to-end cases on reference-encoder codestreams. -/
def endToEndTests : IO Nat := do
  let mut f := 0
  let w := 4
  let h := 3
  let n := w * h
  let ramp (k : Nat) (m : Nat) : List Int := (List.range n).map fun i => Int.ofNat ((i * k + 3) % m)
  -- raw codestream, 8-bit grey
  match enc w h [comp 8 false (ramp 23 256)] with
  | .error e => f := f + (← expect s!"encode grey ({e})" false)
  | .ok cs =>
    match decode {} cs with
    | .error e => f := f + (← expect s!"decode raw grey ({e})" false)
    | .ok img =>
      f := f + (← expect "raw: unknown space, 1 channel, size"
        (img.space == .unknown && img.channels.size == 1 && img.width == w && img.height == h
          && img.alpha.isNone && img.iccProfile.isNone && img.decodedComponents.size == 1))
      f := f + (← expect "raw: interleaved8 = samples"
        ((img.interleaved8 {}).toOption.map bytes == some ((ramp 23 256).map Int.toNat)))
    -- the same in a JP2 container, greyscale
    match decode {} (jp2 w h 1 7 17 [] cs) with
    | .error e => f := f + (← expect s!"decode jp2 grey ({e})" false)
    | .ok img => f := f + (← expect "jp2: greyscale" (img.space == .greyscale && img.channels.size == 1))
    -- limits
    f := f + (← expect "limit: decoded bytes" (isLimit (decode { maxDecodedBytes := n - 1 } cs)))
    f := f + (← expect "limit: image area" (isLimit (decode { maxImageArea := n - 1 } cs)))
    f := f + (← expect "limit: work samples" (isLimit (decode { maxWorkSamples := n - 1 } cs)))
    f := f + (← expect "limit: exactly enough" ((decode { maxDecodedBytes := n } cs).toOption.isSome))
    -- palette: indices 0…3 → (R, G, B) columns
    let idx := (List.range n).map fun i => Int.ofNat (i % 4)
    match enc w h [comp 8 false idx] with
    | .error e => f := f + (← expect s!"encode idx ({e})" false)
    | .ok cs2 =>
      let entries : List (List Nat) := [[10, 20, 30], [40, 50, 60], [70, 80, 90], [255, 0, 128]]
      let pclr := box "pclr" (be 2 4 ++ [3, 7, 7, 7] ++ entries.flatMap (·.map Nat.toUInt8))
      let cmap := box "cmap" ([0, 0, 1, 0] ++ [0, 0, 1, 1] ++ [0, 0, 1, 2])
      let file := jp2 w h 3 7 16 (pclr ++ cmap) cs2
      f := f + (← expect "palette applied"
        (dec8 file == some ((List.range n).flatMap fun i => entries.getD (i % 4) [])))
      f := f + (← expect "palette not applied"
        (dec8 file { applyPalette := false } == some ((List.range n).map (· % 4))))
  -- RGBA with cdef: colours in reverse channel order, channel 3 = opacity
  let cr := ramp 5 256
  let cg := ramp 7 256
  let cb := ramp 11 256
  let ca := ramp 13 256
  match enc w h [comp 8 false cb, comp 8 false cg, comp 8 false cr, comp 8 false ca] with
  | .error e => f := f + (← expect s!"encode rgba ({e})" false)
  | .ok cs =>
    let rgb (a : Bool) : List Nat := (List.range n).flatMap fun i =>
      [cr, cg, cb].map (fun c => (c.getD i 0).toNat) ++ (if a then [(ca.getD i 0).toNat] else [])
    let file (typ : Nat) := jp2 w h 4 7 16 (cdef [(0, 0, 3), (1, 0, 2), (2, 0, 1), (3, typ, 0)]) cs
    f := f + (← expect "cdef order" (dec8 (file 1) == some (rgb false)))
    f := f + (← expect "cdef order + alpha" (dec8 (file 1) (withAlpha := true) == some (rgb true)))
    match decode {} (file 2) with
    | .error e => f := f + (← expect s!"decode rgba ({e})" false)
    | .ok img =>
      f := f + (← expect "premultiplied alpha" (img.premultiplied && img.alpha.isSome))
      f := f + (← expect "smask from file"
        ((img.smaskInData 1).map (fun m => (vals m.channel.plane, m.premultiplied)) == some (ca, true)))
    match decode {} (jp2 w h 4 7 16 [] cs) with
    | .error e => f := f + (← expect s!"decode no cdef ({e})" false)
    | .ok img => f := f + (← expect "no cdef: 3 colours, 1 other, no alpha"
        (img.channels.size == 3 && img.other.size == 1 && img.alpha.isNone && (img.smaskInData 1).isNone))
  -- 1-bit, signed 8-bit, 16-bit
  match enc w h [comp 1 false (ramp 1 2)] with
  | .error e => f := f + (← expect s!"encode 1-bit ({e})" false)
  | .ok cs => f := f + (← expect "1-bit → 0/255" (dec8 cs == some ((ramp 1 2).map fun v => v.toNat * 255)))
  let sv := (ramp 37 256).map (· - 128)
  match enc w h [comp 8 true sv] with
  | .error e => f := f + (← expect s!"encode signed ({e})" false)
  | .ok cs => f := f + (← expect "signed 8 → +128" (dec8 cs == some (sv.map fun v => (v + 128).toNat)))
  let wv := ramp 4099 65536
  match enc w h [comp 16 false wv] with
  | .error e => f := f + (← expect s!"encode 16-bit ({e})" false)
  | .ok cs =>
    match decode {} cs with
    | .error e => f := f + (← expect s!"decode 16-bit ({e})" false)
    | .ok img =>
      f := f + (← expect "16-bit interleaved16 = samples"
        ((img.interleaved16 {}).toOption.map bytes == some (wv.flatMap fun v => (be 2 v.toNat).map (·.toNat))))
      f := f + (← expect "16-bit interleaved8 linear"
        ((img.interleaved8 {}).toOption.map bytes == some (wv.map fun v => scaleNat .linear 16 8 v.toNat)))
  -- reduce: half size
  match enc 8 6 [comp 8 false ((List.range 48).map fun i => Int.ofNat (i * 5 % 256))] with
  | .error e => f := f + (← expect s!"encode 8×6 ({e})" false)
  | .ok cs =>
    f := f + (← expect "reduce 1 → 4×3"
      ((decode {} cs { reduce := 1 }).toOption.map (fun i => (i.width, i.height)) == some (4, 3)))
  return f

/-! ## JP2 conformance (`file1…9.jp2` against `jp2_N.tif`) -/

/-- Files whose reference TIFF is presumably colour-managed through the file's restricted
ICC profile (`colr` METH 2): file5 (ROMM-RGB profile), file7 (e-sRGB profile, 16-bit), file8
(grey ICC). `decode` passes the profile through without conversion, so these are reported,
not required to pass. (OpenJPEG's `opj_decompress` with lcms2 applies these profiles: its
output differs from ours on exactly these three files, peak 126 / 96 / 255.) -/
def iccFiles : List String := ["file5.jp2", "file7.jp2", "file8.jp2"]

/-- Our 8-bit samples of channel `c` from an interleaved buffer of `nc` channels. -/
def channelOf (buf : ByteArray) (nc c : Nat) : Array Int := Id.run do
  let mut out := Array.mkEmpty (buf.size / max nc 1)
  for i in [0:buf.size / max nc 1] do
    out := out.push ((buf.get! (i * nc + c)).toNat : Int)
  return out

/-- Compares one file's `interleaved8` (in `mode`) with its reference planes; returns the
per-channel metrics. -/
def compareFile (img : JPEG2000.Image) (refs : Array PgxImage) (mode : Scaling) :
    Except String (Array Metrics) := do
  let buf ← match img.interleaved8 {} (mode := mode) with
    | .ok b => pure b
    | .error e => throw s!"interleaved8: {e}"
  let nc := img.channels.size
  if nc != 1 && nc != refs.size then throw s!"{nc} channels vs {refs.size} reference planes"
  refs.mapIdxM fun k r => do
    let ours : PgxImage := { width := img.width, height := img.height, depth := 8, signed := false,
                             samples := channelOf buf nc (if nc == 1 then 0 else k) }
    compare ours r

/-- Formats metrics for a report line. -/
def showMetrics (ms : Array Metrics) : String :=
  ", ".intercalate (ms.toList.map fun m => s!"peak {m.peak} mse {m.mseFloat}")

/-- Runs the JP2 conformance comparison; skips when the corpus is absent. -/
def conformanceTests : IO Nat := do
  if !(← (filesRoot : System.FilePath).pathExists) then
    IO.println "  image: corpus not present, skipping JP2 conformance"
    return 0
  let table ← load
  let mut f := 0
  for e in table.filter (·.isTiff) do
    let name := (e.stream.splitOn "/").getLast!
    let path : System.FilePath := filesRoot ++ e.stream
    if !(← path.pathExists) then
      IO.println s!"  image: {path} missing, skipped"
      continue
    let refs ← loadReference e
    let data ← IO.FS.readBinFile path
    match decode {} data { reduce := e.reduce } with
    | .error err => f := f + (← expect s!"{name}: decode ({err})" false)
    | .ok img =>
      let icc := iccFiles.contains name
      for mode in [Scaling.linear, .opj] do
        match compareFile img refs mode with
        | .error m => f := f + (← expect s!"{name}: compare ({m})" false)
        | .ok ms =>
          let ok := ms.all (·.within e)
          IO.println s!"  image: {name} {img.width}×{img.height} {repr img.space |>.pretty 80} \
            {img.channels.size} ch, {repr mode}: {showMetrics ms} \
            → {if ok then "within" else "OUTSIDE"} peak {e.peak.toFloat} mse {e.mse.toFloat}\
            {if icc then " (needs ICC; reported only)" else ""}"
          if mode == .linear && !icc then
            f := f + (← expect s!"{name}: within thresholds" ok)
  return f

/-- Runs every test; returns the number of failures. -/
def run : IO Nat := do
  return (← scalingTests) + (← interleaveTests) + (← upsampleTests) + (← endToEndTests)
    + (← conformanceTests)

end JPEG2000.Tests.Image
