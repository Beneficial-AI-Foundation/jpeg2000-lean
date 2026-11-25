import Tests.ConformanceData

/-!
# Reference-decode reader and metrics (task 5.6a)

Plan.md §8.1.  Independent of the decoder: PGX reader/writer, an uncompressed/LZW baseline TIFF
reader (the nine `jp2_N.tif` references), and OpenJPEG-`compare_images` metrics (peak error and
MSE per component, exact).

PGX: `PG <ML|LM> [+|-]<depth> <width> <height>` + newline (possibly CRLF; the sign may be fused
with the depth, separated by a space, or absent = unsigned; `-` = signed), then samples of 1
(depth <= 8), 2 (<= 16) or 4 bytes; signed samples are sign-extended from the storage width
(as OpenJPEG does).  ML = big-endian, LM = little-endian.
-/

namespace JPEG2000.Tests.Pgx

open JPEG2000.Tests.ConformanceData

/-- A decoded component plane. -/
structure PgxImage where
  /-- width in samples -/
  width : Nat
  /-- height in samples -/
  height : Nat
  /-- bit depth -/
  depth : Nat
  /-- signed samples -/
  signed : Bool
  /-- row-major samples -/
  samples : Array Int
  deriving Repr, BEq, Inhabited

/-- Storage bytes per sample for a bit depth. -/
def bytesPer (depth : Nat) : Nat := if depth ≤ 8 then 1 else if depth ≤ 16 then 2 else 4

private def isWs (c : Char) : Bool := c == ' ' || c == '\t' || c == '\r'

private def rdU (d : ByteArray) (p n : Nat) (be : Bool) : Nat := Id.run do
  let mut v := 0
  for k in [0:n] do
    let b := (d.get! (if be then p + k else p + n - 1 - k)).toNat
    v := v * 256 + b
  return v

/-- Parse a PGX file. -/
def parse (d : ByteArray) : Except String PgxImage := do
  let some nl := (List.range d.size).find? (fun i => d.get! i == 10) | throw "no header newline"
  let hdr := String.fromUTF8! (d.extract 0 nl)
  let toks := ((hdr.split isWs).toList.map (·.toString)).filter (· ≠ "") |>.toArray
  if toks.size < 5 || toks[0]! ≠ "PG" then throw s!"bad header: {hdr}"
  let be ← match toks[1]! with
    | "ML" => pure true | "LM" => pure false | _ => throw s!"bad byte order: {hdr}"
  let (sgn, dtok, rest) :=
    if toks[2]! == "+" || toks[2]! == "-" then (toks[2]!, toks[3]!, toks.extract 4 toks.size)
    else if toks[2]!.startsWith "+" || toks[2]!.startsWith "-" then
      ((toks[2]!.take 1).toString, (toks[2]!.drop 1).toString, toks.extract 3 toks.size)
    else ("+", toks[2]!, toks.extract 3 toks.size)
  let some depth := dtok.toNat? | throw s!"bad depth: {hdr}"
  if rest.size ≠ 2 then throw s!"bad header: {hdr}"
  let some w := rest[0]!.toNat? | throw s!"bad width: {hdr}"
  let some h := rest[1]!.toNat? | throw s!"bad height: {hdr}"
  if depth == 0 || depth > 32 then throw "bad depth"
  let bps := bytesPer depth
  let signed := sgn == "-"
  let n := w * h
  if nl + 1 + n * bps ≠ d.size then
    throw s!"size mismatch: header {hdr}, file {d.size} bytes"
  let mut s : Array Int := Array.mkEmpty n
  for i in [0:n] do
    let u := rdU d (nl + 1 + i * bps) bps be
    let v : Int := if signed && u ≥ 2 ^ (8 * bps - 1) then (u : Int) - 2 ^ (8 * bps) else u
    s := s.push v
  pure { width := w, height := h, depth, signed, samples := s }

/-- Serialise as big-endian PGX (`PG ML +8 w h`); samples are stored in two's complement. -/
def write (img : PgxImage) : ByteArray := Id.run do
  let bps := bytesPer img.depth
  let hdr := s!"PG ML {if img.signed then "-" else "+"}{img.depth} {img.width} {img.height}\n"
  let mut out := hdr.toUTF8
  for v in img.samples do
    let u : Nat := (v % (2 ^ (8 * bps) : Nat)).toNat
    for k in [0:bps] do
      out := out.push (UInt8.ofNat ((u / 256 ^ (bps - 1 - k)) % 256))
  return out

/-- Read and parse a PGX file. -/
def readFile (path : System.FilePath) : IO PgxImage := do
  match parse (← IO.FS.readBinFile path) with
  | .ok i => pure i
  | .error m => throw (IO.userError s!"{path}: {m}")

/-- Write a PGX file. -/
def writeFile (path : System.FilePath) (img : PgxImage) : IO Unit :=
  IO.FS.writeBinFile path (write img)

/-! ## Metrics (OpenJPEG `compare_images` semantics, per component) -/

/-- Exact comparison result: peak = max |a-b|; MSE = `sumSq / count`. -/
structure Metrics where
  /-- maximum absolute sample difference -/
  peak : Nat
  /-- sum of squared differences -/
  sumSq : Nat
  /-- number of samples -/
  count : Nat
  deriving Repr, BEq

/-- MSE as a float (printing only). -/
def Metrics.mseFloat (m : Metrics) : Float :=
  if m.count == 0 then 0 else Float.ofNat m.sumSq / Float.ofNat m.count

/-- Exact MSE as a reduced-free fraction `(sumSq, count)`. -/
def Metrics.mse (m : Metrics) : Nat × Nat := (m.sumSq, m.count)

/-- Peak error of two equally long sample arrays (`0` if lengths differ is NOT assumed:
see `compare`). -/
def peakError (a b : Array Int) : Nat := Id.run do
  let mut p := 0
  for i in [0:min a.size b.size] do
    p := max p (a[i]! - b[i]!).natAbs
  return p

/-- Sum of squared differences and count, as the exact MSE numerator/denominator. -/
def mse (a b : Array Int) : Nat × Nat := Id.run do
  let mut s := 0
  for i in [0:min a.size b.size] do
    s := s + (a[i]! - b[i]!).natAbs ^ 2
  return (s, min a.size b.size)

/-- Compare two component planes; error when dimensions differ. -/
def compare (a b : PgxImage) : Except String Metrics :=
  if a.width ≠ b.width || a.height ≠ b.height || a.samples.size ≠ b.samples.size then
    .error s!"dimension mismatch: {a.width}x{a.height} vs {b.width}x{b.height}"
  else
    let (s, n) := mse a.samples b.samples
    .ok { peak := peakError a.samples b.samples, sumSq := s, count := n }

/-- Does `m` meet the entry's thresholds (`peak <= peak`, `MSE <= mse`, exactly)? -/
def Metrics.within (m : Metrics) (e : RefEntry) : Bool :=
  e.peak.divLe m.peak 1 && (m.count == 0 || e.mse.divLe m.sumSq m.count)

/-! ## Baseline TIFF reader (the `jp2_N.tif` references) -/

private structure Ifd where
  be : Bool
  d : ByteArray

private def Ifd.u (t : Ifd) (p n : Nat) : Nat := rdU t.d p n t.be

/-- LZW decode (TIFF flavour: MSB-first codes, 256 = clear, 257 = end, early change). -/
private def lzw (src : ByteArray) (cap : Nat) : ByteArray := Id.run do
  let totalBits := src.size * 8
  let getCode (pos w : Nat) : Nat := Id.run do
    let mut v := 0
    for k in [0:w] do
      let bit := pos + k
      let byte := (src.get! (bit / 8)).toNat
      v := v * 2 + (byte >>> (7 - bit % 8)) % 2
    return v
  let widthFor (n : Nat) : Nat := if n < 511 then 9 else if n < 1023 then 10 else if n < 2047 then 11 else 12
  let mut out := ByteArray.empty
  let mut tbl : Array ByteArray := #[]
  let mut prev : Option ByteArray := none
  let mut pos := 0
  for _ in [0:totalBits / 9 + 1] do
    let w := widthFor (258 + tbl.size)
    if pos + w > totalBits || out.size ≥ cap then break
    let code := getCode pos w
    pos := pos + w
    if code == 257 then break
    else if code == 256 then
      tbl := #[]; prev := none
    else
      let ent : Option ByteArray :=
        if code < 256 then some (ByteArray.empty.push code.toUInt8)
        else if code - 258 < tbl.size then some tbl[code - 258]!
        else match prev with
          | some p => if code == 258 + tbl.size then some (p.push (p.get! 0)) else none
          | none => none
      match ent with
      | none => break
      | some e =>
        out := out.append e
        if let some p := prev then
          if tbl.size < 4094 - 258 then tbl := tbl.push (p.push (e.get! 0))
        prev := some e
  return out

/-- Parse a baseline TIFF: 8/16-bit, chunky, one or more samples per pixel, strips, no
compression or LZW (optionally horizontal predictor on 8-bit).  Returns one plane per sample. -/
def parseTiff (d : ByteArray) : Except String (Array PgxImage) := do
  if d.size < 8 then throw "tiff: too short"
  let be ← match (d.get! 0, d.get! 1) with
    | (0x4D, 0x4D) => pure true | (0x49, 0x49) => pure false | _ => throw "tiff: bad byte order"
  let t : Ifd := { be, d }
  if t.u 2 2 ≠ 42 then throw "tiff: bad magic"
  let off := t.u 4 4
  if off + 2 > d.size then throw "tiff: bad IFD offset"
  let cnt := t.u off 2
  if off + 2 + 12 * cnt > d.size then throw "tiff: truncated IFD"
  let tag (id : Nat) : Option (Array Nat) := Id.run do
    for i in [0:cnt] do
      let e := off + 2 + 12 * i
      if t.u e 2 == id then
        let ty := t.u (e + 2) 2
        let n := t.u (e + 4) 4
        let sz := if ty == 3 then 2 else if ty == 4 then 4 else 1
        let base := if n * sz ≤ 4 then e + 8 else t.u (e + 8) 4
        if base + n * sz > d.size then return none
        return some ((Array.range n).map fun k => t.u (base + k * sz) sz)
    return none
  let one (id : Nat) (dflt : Nat) : Nat := ((tag id).bind (·[0]?)).getD dflt
  let w := one 256 0
  let h := one 257 0
  let spp := one 277 1
  let bits := ((tag 258).bind (·[0]?)).getD 8
  let comp := one 259 1
  let rps := one 278 h
  let pred := one 317 1
  if one 284 1 ≠ 1 then throw "tiff: planar configuration not supported"
  if bits ≠ 8 && bits ≠ 16 then throw s!"tiff: {bits}-bit not supported"
  if comp ≠ 1 && comp ≠ 5 then throw s!"tiff: compression {comp} not supported"
  if pred ≠ 1 && !(pred == 2 && bits == 8) then throw "tiff: predictor not supported"
  if w == 0 || h == 0 || spp == 0 || rps == 0 then throw "tiff: bad dimensions"
  let some offs := tag 273 | throw "tiff: no strip offsets"
  let some lens := tag 279 | throw "tiff: no strip byte counts"
  let bpp := spp * (bits / 8)
  let rowBytes := w * bpp
  let mut raw := ByteArray.empty
  for i in [0:offs.size] do
    let o := offs[i]!
    let l := lens[i]!
    if o + l > d.size then throw "tiff: strip out of range"
    let rows := min rps (h - min h (i * rps))
    let chunk := d.extract o (o + l)
    let dec := if comp == 5 then lzw chunk (rows * rowBytes) else chunk
    if dec.size < rows * rowBytes then throw "tiff: short strip"
    let mut dec := dec.extract 0 (rows * rowBytes)
    if pred == 2 then
      for r in [0:rows] do
        for x in [1:w] do
          for c in [0:spp] do
            let p := r * rowBytes + x * spp + c
            dec := dec.set! p ((dec.get! p) + dec.get! (p - spp))
    raw := raw.append dec
  if raw.size ≠ h * rowBytes then throw "tiff: image data size mismatch"
  let mut planes : Array PgxImage := #[]
  for c in [0:spp] do
    let mut s : Array Int := Array.mkEmpty (w * h)
    for i in [0:w * h] do
      s := s.push (rdU raw (i * bpp + c * (bits / 8)) (bits / 8) be : Nat)
    planes := planes.push { width := w, height := h, depth := bits, signed := false, samples := s }
  pure planes

/-- Read a reference decode (PGX or TIFF) as component planes (PGX gives a single plane). -/
def loadReference (e : RefEntry) : IO (Array PgxImage) := do
  let p : System.FilePath := filesRoot ++ e.refPath
  if e.isTiff then
    match parseTiff (← IO.FS.readBinFile p) with
    | .ok i => pure i
    | .error m => throw (IO.userError s!"{p}: {m}")
  else pure #[← readFile p]

/-! ## Self-test -/

private def check (name : String) (ok : Bool) : IO Nat := do
  if !ok then IO.eprintln s!"FAIL: {name}"
  pure (if ok then 0 else 1)

/-- Self-test suite; returns the number of failures. -/
def run : IO Nat := do
  let mut bad := 0
  -- hand cases
  let mk (xs : List Int) : PgxImage := { width := xs.length, height := 1, depth := 8, signed := true, samples := xs.toArray }
  let a := mk [1, 2, 3, -4]
  bad := bad + (← check "identical" (match compare a a with | .ok m => m == { peak := 0, sumSq := 0, count := 4 } | _ => false))
  bad := bad + (← check "diff" (match compare a (mk [1, 4, 3, 0]) with
    | .ok m => m == { peak := 4, sumSq := 20, count := 4 } | _ => false))
  bad := bad + (← check "dim mismatch" (match compare a (mk [1]) with | .error _ => true | _ => false))
  let m : Metrics := { peak := 4, sumSq := 20, count := 4 }
  let q (n d : Nat) : Q := { num := n, den := d }
  let ent : RefEntry := { refPath := "", stream := "", cls := none, profile := none, component := none, reduce := 0, peak := q 4 1, mse := q 5 1, perComponent := false, isTiff := false }
  bad := bad + (← check "within eq" (m.within ent))
  bad := bad + (← check "mse over" (!(m.within { ent with mse := q 49 10 })))
  bad := bad + (← check "peak over" (!(m.within { ent with peak := q 3 1 })))
  -- round trips
  for img in [a, { width := 3, height := 2, depth := 12, signed := false, samples := #[0, 4095, 7, 8, 9, 10] },
              { width := 2, height := 1, depth := 12, signed := true, samples := #[-2048, 2047] },
              { width := 2, height := 1, depth := 20, signed := true, samples := #[-70000, 70000] }] do
    bad := bad + (← check s!"roundtrip depth {img.depth}" (match parse (write img) with | .ok i => i == img | _ => false))
  -- table
  let t ← load
  let c0 := t.filter (·.cls == some 0)
  let c1 := t.filter (·.cls == some 1)
  let tif := t.filter (·.isTiff)
  IO.println s!"pgx: table {t.size} entries (class 0: {c0.size}, class 1: {c1.size}, tif: {tif.size}), streams {(streams t).size}"
  bad := bad + (← check "table counts" (t.size == 87 && c0.size == 26 && c1.size == 52 && tif.size == 9))
  -- every reference parses; every stream exists
  let mut nPgx := 0
  let mut nPix := 0
  for e in t do
    let ex ← (filesRoot ++ e.stream : System.FilePath).pathExists
    bad := bad + (← check s!"stream exists {e.stream}" ex)
    match ← (loadReference e).toBaseIO with
    | .error err => IO.eprintln s!"FAIL: {e.refPath}: {err}"; bad := bad + 1
    | .ok planes =>
      if e.isTiff then
        bad := bad + (← check s!"tif planes {e.refPath}" (planes.size == 3 && planes.all (·.depth == 8)))
      else
        nPgx := nPgx + 1
        for p in planes do
          nPix := nPix + p.samples.size
          let lim : Int := 2 ^ p.depth
          let okr := p.samples.all fun v => if p.signed then -lim ≤ 2 * v && 2 * v < lim else 0 ≤ v && v < lim
          bad := bad + (← check s!"range {e.refPath}" okr)
          let rt := match parse (write p) with | .ok i => i == p | _ => false
          bad := bad + (← check s!"rt {e.refPath}" rt)
  IO.println s!"pgx: parsed {nPgx} PGX references ({nPix} samples), {tif.size} TIFFs"
  return bad

end JPEG2000.Tests.Pgx
