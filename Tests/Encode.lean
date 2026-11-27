import Encode.Encode
import JPEG2000.Tier2.Headers
import JPEG2000.Tier1.WidePlain
import JPEG2000.Decode
import Tests.SpecDecode

/-!
# Tests: the reference encoder (task 7.2)

Plan.md §5.3, §4 C10, §8; T.800 Annexes A, B, D, E, F, G (encoder side).

1. **Lossless (5/3 + RCT), random images**: 1–3 components, bit depth 1–12, signed or
   unsigned, sizes 1×1 … 64×64 (odd sizes included), `NL` 0–5 capped by the size, random
   code-block exponents; content mixes gradients, flat areas and noise. For each image:
   * our parser accepts the codestream (`Header.parse`) and Tier-2 decodes every packet
     (`Tier2.Headers.decodeAllTileCodeBlocks`) with the tile data consumed exactly; every
     code-block's passes, zero bit-planes and segment bytes equal what the encoder produced
     (one segment per included code-block);
   * when `opj_decompress` is installed: OpenJPEG decodes it (to PGX, read back by a small
     private reader) **bit-exactly**.
2. **Lossy (9/7 + ICT)**: same, decoded by OpenJPEG within a bound; the maximum error is
   printed.
3. **Determinism**: encoding twice gives the same bytes.
4. Argument errors.

`JPEG2000_ENCODE_CASES` (default 24 lossless + 8 lossy) for more; `JPEG2000_ENCODE_MAXSIZE`
(default 64) for the largest side.

5. **Our full decoder** (`JPEG2000.decodeCodestream`, task 5.5) on every case: bit-exact for
   5/3 + RCT, within the lossy bound for 9/7 + ICT (`checkDecoder`). This is the executable
   form of C10 (`decode (encode img) = img`, proved in task 7.3).
-/

namespace JPEG2000.Tests.Encode

open JPEG2000 JPEG2000.Encode

/-- Prints a failure line and returns 1 when `ok` is false. -/
def expect (name : String) (ok : Bool) : IO Nat := do
  if ok then return 0
  IO.eprintln s!"  FAIL encode: {name}"
  return 1

/-! ## Random images -/

/-- One splitmix64 step. -/
def splitmix (s : UInt64) : UInt64 × UInt64 :=
  let s := s + 0x9E3779B97F4A7C15
  let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), s)

/-- A pseudo-random value below `m` (`m > 0`). -/
def below (s : UInt64) (m : Nat) : Nat × UInt64 :=
  let (z, s) := splitmix s
  ((z >>> 11).toNat % (max m 1), s)

/-- A random component of `w × h` samples: a gradient, flat blocks or noise (mixed). -/
def randComp (w h depth : Nat) (signed : Bool) (s : UInt64) : Component × UInt64 := Id.run do
  let (kind, s) := below s 4
  let (a, s) := below s 7
  let (b, s) := below s 5
  let mut s := s
  let lo : Int := if signed then -((2 : Int) ^ (depth - 1)) else 0
  let span : Nat := 2 ^ depth
  let mut out : Array Int := Array.mkEmpty (w * h)
  for y in [0:h] do
    for x in [0:w] do
      let (n, s1) := below s span
      s := s1
      let v : Nat := match kind with
        | 0 => (x * a + y * b) % span
        | 1 => ((x / 4 + y / 4) % 3) * (span / 3)
        | 2 => n
        | _ => ((x * a + y * b) * 3 + n % (max 1 (span / 8))) % span
      out := out.push (lo + v)
  return ({ depth, signed, samples := out }, s)

/-- A random image and parameters. -/
def randCase (reversible : Bool) (maxSide : Nat) (s : UInt64) : Image × Params × UInt64 :=
  Id.run do
  let (big, s) := below s 4
  let side := if big = 0 then maxSide else min maxSide 17
  let (w, s) := below s side
  let (h, s) := below s side
  let w := w + 1
  let h := h + 1
  let (nc, s) := below s 3
  let nc := nc + 1
  let (depth, s) := below s 12
  let depth := depth + 1
  let (sg, s0) := below s 3
  let mut st := s0
  let mut comps := #[]
  for _ in [0:nc] do
    let (c, s1) := randComp w h depth (sg = 0) st
    st := s1
    comps := comps.push c
  let s := st
  let maxNl := Nat.log2 (min w h)
  let (nl, s) := below s (min 5 maxNl + 1)
  let (cbw, s) := below s 5
  let (cbh, s) := below s 5
  let (mct, s) := below s 4
  let (stp, s) := below s 3
  let p : Params := { levels := nl, cbWidthExp := cbw + 2, cbHeightExp := cbh + 2, reversible,
                      mct := mct ≠ 0, stepLog2 := (stp : Int) - 2 }
  return ({ width := w, height := h, comps }, p, s)

/-- A short description of a case. -/
def descr (img : Image) (p : Params) : String :=
  let c := img.comps.getD 0 default
  s!"{img.width}x{img.height}x{img.comps.size} depth {c.depth}{if c.signed then "s" else "u"} NL {p.levels} cb {p.cbWidthExp}/{p.cbHeightExp} mct {p.mct} rev {p.reversible}"

/-- Largest absolute difference between two sample arrays (`none` on a size mismatch). -/
def maxErr (a b : Array Int) : Option Nat :=
  if a.size ≠ b.size then none
  else some ((a.zip b).foldl (fun m (x, y) => max m (x - y).natAbs) 0)

/-! ## Our parser and Tier-2 -/

/-- Parses the codestream with our header parser and Tier-2, compares every code-block with
the encoder's records. Returns an error description or `none`. -/
def checkOurs (enc : Encoded) : Option String :=
  match Header.parse Limits.default enc.codestream with
  | .error e => some s!"header: {repr e}"
  | .ok h =>
    match Tier2.Headers.decodeAllTileCodeBlocks Limits.default h enc.codestream with
    | .error e => some s!"tier2: {repr e}"
    | .ok ts =>
      match ts.toList with
      | [t] =>
        if t.consumed ≠ t.dataLength then some s!"tier2 consumed {t.consumed} of {t.dataLength}"
        else
          let got := t.blocks.toArray
          if got.size ≠ enc.blocks.size then
            some s!"{got.size} code-blocks decoded, {enc.blocks.size} encoded"
          else
            let bad := (got.zip enc.blocks).toList.findIdx? fun (g, e) =>
              let cb := g.block
              let bytes := cb.segments.foldl (fun a sg => a ++ sg.bytes enc.codestream)
                ByteArray.empty
              !(g.comp == e.comp && g.res == e.res && g.prec == e.prec && g.bandIdx == e.band &&
                cb.geom.index == e.block && cb.numPasses == e.numPasses &&
                (e.numPasses == 0 || (cb.zeroBitPlanes == e.zeroBitPlanes &&
                  cb.segments.size == 1)) &&
                bytes == e.data)
            bad.map fun i => s!"code-block {i} differs"
      | _ => some s!"{ts.size} tiles"

/-! ## Our full decoder -/

/-- The lossy error bound of a component: generous, relative to the bit depth. -/
def lossyBound (depth : Nat) : Nat := max 8 (2 ^ depth / 16)

/-- Decodes with `JPEG2000.decodeCodestream` and compares with the source: bit-exact when
`exact`, else within `lossyBound`. Returns an error description or `none`, and the largest
error seen. -/
def checkDecoder (img : Image) (exact : Bool) (cs : ByteArray) : Option String × Nat :=
  match decodeCodestream Limits.default cs with
  | .error e => (some s!"decodeCodestream: {repr e}", 0)
  | .ok di =>
    if di.comps.size ≠ img.comps.size then (some s!"{di.comps.size} components decoded", 0)
    else
      (List.range img.comps.size).foldl (fun (acc : Option String × Nat) c =>
        let src := (img.comps.getD c default).samples
        let dc := di.comps.getD c default
        let got := (Array.range (dc.width * dc.height)).map fun k =>
          (dc.get? k).getD 0
        match maxErr got src with
        | none => (acc.1 <|> some s!"component {c}: size {dc.width}x{dc.height}", acc.2)
        | some e =>
          let ok := if exact then e == 0 else e ≤ lossyBound (img.comps.getD c default).depth
          (if ok then acc.1 else acc.1 <|> some s!"component {c}: max err {e} (ours)", max acc.2 e))
        (none, 0)

/-! ## OpenJPEG -/

/-- Big-endian / little-endian unsigned integer of `n` bytes at `p`. -/
private def rdU (d : ByteArray) (p n : Nat) (be : Bool) : Nat :=
  (List.range n).foldl (fun v k => v * 256 + ((d.data[if be then p + k else p + n - 1 - k]?).getD 0).toNat) 0

/-- A minimal PGX reader (`PG ML|LM [+|-]depth width height`, then samples of 1, 2 or 4
bytes). Returns `(signed, width, height, samples)`. -/
def readPgx (d : ByteArray) : Except String (Bool × Nat × Nat × Array Int) := do
  let some nl := (List.range d.size).find? (fun i => d.data[i]? == some 10) | throw "no newline"
  let hdr := String.fromUTF8? (d.extract 0 nl) |>.getD ""
  let toks := (hdr.splitToList (fun c => c == ' ' || c == '\r' || c == '\t')).filter (· ≠ "")
  let be ← match toks[1]? with
    | some "ML" => pure true
    | some "LM" => pure false
    | _ => throw s!"bad PGX header {hdr}"
  let rest := toks.drop 2
  let (signed, rest) := match rest with
    | "+" :: r => (false, r)
    | "-" :: r => (true, r)
    | t :: r =>
      if t.startsWith "-" then (true, (t.drop 1).toString :: r)
      else if t.startsWith "+" then (false, (t.drop 1).toString :: r)
      else (false, t :: r)
    | [] => (false, [])
  let [ds, ws, hs] := rest | throw s!"bad PGX header {hdr}"
  let (some depth, some w, some h) := (ds.toNat?, ws.toNat?, hs.toNat?) | throw "bad numbers"
  let nb := if depth ≤ 8 then 1 else if depth ≤ 16 then 2 else 4
  let base := nl + 1
  if d.size < base + w * h * nb then throw "PGX data too short"
  let samples := (Array.range (w * h)).map fun i =>
    let u := rdU d (base + i * nb) nb be
    if signed && u ≥ 2 ^ (8 * nb - 1) then (u : Int) - 2 ^ (8 * nb) else (u : Int)
  return (signed, w, h, samples)

/-- Whether `opj_decompress` can be run. -/
def haveOpj : IO Bool := do
  try
    let out ← IO.Process.output { cmd := "opj_decompress", args := #["-h"] }
    return out.exitCode == 0 || out.exitCode == 1
  catch _ => return false

/-- Decodes a codestream with OpenJPEG; returns per component its samples. -/
def opjDecode (dir : System.FilePath) (name : String) (cs : ByteArray) (nc : Nat) :
    IO (Except String (Array (Array Int))) := do
  let j2k := dir / s!"{name}.j2k"
  IO.FS.writeBinFile j2k cs
  let out ← IO.Process.output
    { cmd := "opj_decompress", args := #["-i", j2k.toString, "-o", (dir / s!"{name}.pgx").toString] }
  if out.exitCode != 0 then return .error s!"opj_decompress: {out.stderr.take 300}"
  let mut comps := #[]
  for c in [0:nc] do
    let f := dir / (if nc = 1 then s!"{name}.pgx" else s!"{name}_{c}.pgx")
    let f ← if (← f.pathExists) then pure f else pure (dir / s!"{name}_{c}.pgx")
    match readPgx (← IO.FS.readBinFile f) with
    | .error e => return .error s!"{f}: {e}"
    | .ok (_, _, _, smp) => comps := comps.push smp
  return .ok comps

/-! ## Suites -/

/-- Runs `n` random cases of one kind. Returns failures and the maximum error seen
(OpenJPEG, ours). -/
def randomCases (reversible : Bool) (n maxSide : Nat) (seed : UInt64) (opj : Bool)
    (dir : System.FilePath) : IO (Nat × Nat × Nat) := do
  let mut s := seed
  let mut f := 0
  let mut worst := 0
  let mut worstOurs := 0
  for i in [0:n] do
    let (img, p, s1) := randCase reversible maxSide s
    s := s1
    let d := descr img p
    match encodeDetailed p img with
    | .error e => f := f + (← expect s!"case {i} ({d}): encode error {repr e}" false)
    | .ok enc =>
      if let some m := checkOurs enc then
        f := f + (← expect s!"case {i} ({d}): {m}" false)
      let (dm, de) := checkDecoder img reversible enc.codestream
      if !reversible then worstOurs := max worstOurs de
      if let some m := dm then
        f := f + (← expect s!"case {i} ({d}): {m}" false)
      if opj then
        match ← opjDecode dir s!"c{i}" enc.codestream img.comps.size with
        | .error m => f := f + (← expect s!"case {i} ({d}): {m}" false)
        | .ok comps =>
          for c in [0:img.comps.size] do
            let src := (img.comps.getD c default).samples
            match maxErr (comps.getD c #[]) src with
            | none => f := f + (← expect s!"case {i} ({d}): component {c} size" false)
            | some e =>
              worst := max worst e
              if reversible then
                f := f + (← expect s!"case {i} ({d}): component {c} not bit-exact (max err {e})" (e == 0))
              else
                -- Lossy bound: generous, relative to the bit depth.
                let bound := lossyBound (img.comps.getD c default).depth
                f := f + (← expect s!"case {i} ({d}): component {c} max err {e} > {bound}" (e ≤ bound))
  return (f, worst, worstOurs)

/-- Encoding is deterministic. -/
def determinism : IO Nat := do
  let (img, p, _) := randCase true 32 77
  let a := encode p img
  let b := encode p img
  let (img2, p2, _) := randCase false 32 78
  let c := encode p2 img2
  let d := encode p2 img2
  let same : Except Error ByteArray → Except Error ByteArray → Bool
    | .ok x, .ok y => x == y
    | _, _ => false
  return (← expect "deterministic (5/3)" (same a b)) + (← expect "deterministic (9/7)" (same c d))

/-- Argument errors are reported. -/
def argErrors : IO Nat := do
  let img : Image := { width := 2, height := 2, comps := #[{ depth := 8, samples := #[0, 1, 2, 3] }] }
  let isErr : Except Error ByteArray → Bool
    | .error _ => true
    | .ok _ => false
  let mut f := 0
  f := f + (← expect "ok image" (!isErr (encode {} img)))
  f := f + (← expect "size mismatch" (isErr (encode {} { img with width := 3 })))
  f := f + (← expect "no components" (isErr (encode {} { img with comps := #[] })))
  f := f + (← expect "sample out of range"
    (isErr (encode {} { img with comps := #[{ depth := 1, samples := #[0, 1, 2, 0] }] })))
  f := f + (← expect "code-block too large" (isErr (encode { cbWidthExp := 7, cbHeightExp := 7 } img)))
  f := f + (← expect "NL > 32" (isErr (encode { levels := 33 } img)))
  return f

/-- A lossless 29-bit image whose second-level HH coefficient needs 32 coded planes.
The separable sign pattern follows the second-level 5/3 analysis filter. Opposite
RGB channels double its amplitude under the forward RCT. -/
private def coded32 : IO Nat := do
  let signs : Array Int := #[0, 0, 1, -1, -1, 1, 1, 1, -1, -1, 1, 0]
  let samples := Array.ofFn (n := 12 * 12) fun i =>
    signs.getD (i.val % 12) 0 * signs.getD (i.val / 12) 0 * (2^28 - 1)
  let c : Component := { depth := 29, signed := true, samples }
  let img : Image := { width := 12, height := 12, comps := #[c, { c with samples := samples.map (- ·) }, c] }
  let name := "32-plane lossless reference round trip"
  let params : Params := { levels := 2, mct := true }
  let .ok enc := encodeDetailed params img
    | return ← expect (name ++ ": encoding failed") false
  let .ok si := Spec.Decode.decode Limits.default enc.codestream 0
    | return ← expect (name ++ ": spec decode failed") false
  let actual := si.comps.map fun comp => comp.samples.map Spec.Decode.SpecSample.value
  let wideBlocks := enc.blocks.filter (·.numPasses == 3 * 32 - 2)
  let bands := bands53 params img true
  for block in wideBlocks do
    let band := (JPEG2000.Tier2.Geometry.bandsOf block.res).getD block.band .LL
    let src := (((bands.getD block.comp #[]).getD block.res #[]).getD block.band default)
    let mb := JPEG2000.Tier2.Packet.bandMb (si.header.defaults.comps.getD block.comp default)
      block.res band
    let .ok cells := JPEG2000.Tier1.WidePlain.decodeCodeBlock block.data 0 block.data.size
        src.rect.width src.rect.height band mb block.zeroBitPlanes block.numPasses
      | return ← expect (name ++ ": wide block decode failed") false
    if cells.map (·.value) != src.vals then
      return ← expect (name ++ ": wide coefficients differ") false
  let .ok (compact, reconstructed) := Tests.SpecDecode.reversibleRGB enc.codestream
    | return ← expect (name ++ ": reversible packet dispatch failed") false
  let .ok decoded := decodeCodestream Limits.default enc.codestream
    | return ← expect (name ++ ": public decoder rejected the stream") false
  let observed := decoded.comps.map fun c => (Array.range (c.width * c.height)).map c.get?
  let expected := img.comps.map (·.samples)
  return ← expect name (enc.codestream.size == 704 && wideBlocks.size == 2 &&
    observed == expected.map (·.map some) && compact == #[true, false, false] && reconstructed == expected && actual == expected)

/-- Runs the suite. -/
def run : IO Nat := do
  let n := ((← IO.getEnv "JPEG2000_ENCODE_CASES").bind String.toNat?).getD 24
  let maxSide := ((← IO.getEnv "JPEG2000_ENCODE_MAXSIZE").bind String.toNat?).getD 64
  let opj ← haveOpj
  if !opj then IO.println "  encode: opj_decompress not found, OpenJPEG checks skipped"
  let out ← IO.Process.output { cmd := "mktemp", args := #["-d"] }
  let dir : System.FilePath := out.stdout.trimAscii.toString
  let mut f := 0
  let (f1, _, _) ← randomCases true n maxSide 1 opj dir
  f := f + f1
  let (f2, worst, worstOurs) ← randomCases false (max 1 (n / 3)) maxSide 2 opj dir
  f := f + f2
  IO.println s!"  encode: lossy 9/7 max error {worstOurs} (ours){if opj then s!", {worst} (OpenJPEG)" else ""}"
  f := f + (← coded32)
  f := f + (← determinism)
  f := f + (← argErrors)
  try IO.FS.removeDirAll dir catch _ => pure ()
  return f

end JPEG2000.Tests.Encode
