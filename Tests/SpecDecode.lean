import Spec.Decode
import Encode.Encode
import JPEG2000.ReversibleDispatch

/-!
# Tests: `Spec.decode` against `decodeCodestream` (tasks 7.1a, 7.1f)

Plan.md §4 (C9), §5.1; T.800 Annexes B, D, E, F, G.

The executable form of C9 on tiny streams: the specification decoder `Spec.Decode.decode`
(with the real Tier-2 spec `Spec.Tier2.decodeWithStream` since task 7.1f; it re-un-stuffs per
packet, so inputs stay tiny) and the fast `decodeCodestream` must agree — every reversible sample equal, every
irreversible sample within 1 (the measured error; the proved bound is in `Spec/Equiv.lean`).

1. **Reference-encoder streams** (`Encode.encode`, task 7.2): tiny images with 1 or 3
   components, 5/3 + RCT (lossless: the spec samples must also equal the source image) and
   9/7 + ICT, several sizes and decomposition levels, one with a resolution reduction.
2. **T.803 streams** (when `corpus/files` is present): `p0_01.j2k` (5/3, 128×128, decoded
   at `reduce = 2` to keep the spec fast), `p0_09.j2k` (9/7, 17×37, 5 levels), `p0_12.j2k`
   (5/3, 3×5, 3 levels on a tiny image), `p0_14.j2k` (5/3 + RCT, 49×49, `reduce = 1`).
   Skipped cleanly without the corpus.
-/

namespace JPEG2000.Tests.SpecDecode

open JPEG2000 JPEG2000.Spec.Decode

/-- Compares the two decoders on one stream; `none` when they agree (reversible samples
equal, irreversible ones within `tol`), else a description. Also returns the maximum
irreversible difference. -/
def compare (cs : ByteArray) (reduce : Nat) (tol : Int) : Option String × Int :=
  match decodeCodestream Limits.default cs reduce, Spec.Decode.decode Limits.default cs reduce with
  | .error e1, .error e2 => (some s!"both failed: {repr e1} / {repr e2}", 0)
  | .error e, .ok _ => (some s!"fast failed: {repr e}", 0)
  | .ok _, .error e => (some s!"spec failed: {repr e}", 0)
  | .ok f, .ok s =>
    if f.comps.size ≠ s.comps.size then (some "component counts differ", 0)
    else
      (List.range f.comps.size).foldl (fun (acc : Option String × Int) c =>
        let fc := f.comps.getD c default
        let sc := (s.comps[c]?).map (·.samples) |>.getD #[]
        if sc.size ≠ fc.width * fc.height then
          (acc.1 <|> some s!"component {c}: sizes differ", acc.2)
        else
          (List.range sc.size).foldl (fun (acc : Option String × Int) k =>
            let fv := (fc.get? k).getD 0
            let sv := sc.getD k default
            let d := (fv - sv.value).natAbs
            if sv.reversible then
              if d = 0 then acc else (acc.1 <|> some s!"component {c} sample {k}: {fv} vs {sv.value}", acc.2)
            else if d ≤ tol then (acc.1, max acc.2 d)
            else (acc.1 <|> some s!"component {c} sample {k}: {fv} vs {sv.value} (irreversible)", max acc.2 d))
            acc)
        (none, 0)

/-- The spec samples of every component equal the source image (lossless streams). -/
def specEqualsImage (cs : ByteArray) (img : Encode.Image) : Bool :=
  match Spec.Decode.decode Limits.default cs 0 with
  | .error _ => false
  | .ok s =>
    s.comps.size == img.comps.size &&
    (List.range s.comps.size).all fun c =>
      ((s.comps.getD c default).samples.map (·.value)) == (img.comps.getD c default).samples

/-- A deterministic test image: `n` components of depth `d`, a gradient plus a pattern. -/
def image (w h n d : Nat) (signed : Bool := false) : Encode.Image :=
  { width := w, height := h,
    comps := Array.ofFn (n := n) fun c =>
      { depth := d, signed,
        samples := Array.ofFn (n := w * h) fun k =>
          let x := k.val % w
          let y := k.val / w
          let v : Int := ((x * 37 + y * 53 + c.val * 91 + x * y * 7) % (2 ^ d) : Nat)
          if signed then v - 2 ^ (d - 1) else v } }

/-- Prints a failure and returns 1. -/
def fail (name msg : String) : IO Nat := do
  IO.eprintln s!"  FAIL spec-decode {name}: {msg}"
  return 1

/-- One encoder case. -/
def encCase (name : String) (p : Encode.Params) (img : Encode.Image) (reduce : Nat := 0) :
    IO Nat := do
  match Encode.encode p img with
  | .error e => fail name s!"encoder: {repr e}"
  | .ok cs =>
    let (r, m) := compare cs reduce 1
    let mut n := 0
    if let some msg := r then n := n + (← fail name msg)
    if p.reversible && reduce == 0 && !specEqualsImage cs img then
      n := n + (← fail name "spec samples differ from the source image")
    if !p.reversible then IO.println s!"  spec-decode {name}: max irreversible difference {m}"
    return n

/-- Serialize a one-row, three-component image from its LL quantisation indices.
At higher resolutions each detail coefficient is the opposite of its LL value. -/
private def cancellationStream (w : Nat) (depth : UInt8) (params : Encode.Params)
    (qcd : Marker.QCD) (ll : Array Int) : Except Error ByteArray := do
  let comp : Encode.Component := { depth := 8, signed := true, samples := Array.replicate w 0 }
  let base ← Encode.encode params { width := w, height := 1, comps := #[comp, comp, comp] }
  let header ← Header.parse Limits.default base
  let siz := { header.siz with components := header.siz.components.map fun c => { c with depth } }
  let cod := header.main.cod
  let coding ← Header.mkComp 0 cod.style qcd 0
  let rect : Header.Rect := ⟨0, 0, w, 1⟩
  let mut precs := #[]
  for index in [0:ll.size] do
    let low := ll.getD index 0
    let tc := Tier2.Geometry.tileComp rect (siz.components.getD index default) coding
    let bands := Encode.compBands w 1 params.levels fun _ b _ _ => if b == .LL then low else -low
    let (prec, _) ← Encode.encodeComp Limits.default tc index bands
    precs := precs.push prec
  let data := Encode.Tier2.encodeTileLRCP precs
  let sot : TilePart.SOT := { isot := 0, psot := (14 + data.size).toUInt32, tpsot := 0, tnsot := 1 }
  let marker := fun k => Encode.Marker.pack (Encode.Marker.be16 k)
  let seg := Encode.Marker.segment
  return marker Marker.Code.SOC ++ seg Marker.Code.SIZ (Encode.Marker.serializeSIZ siz) ++
    seg Marker.Code.COD (Encode.Marker.serializeCOD cod) ++ seg Marker.Code.QCD (Encode.Marker.serializeQCD qcd) ++
    seg Marker.Code.SOT (Encode.TilePart.serializeSOT sot) ++ marker Marker.Code.SOD ++ data ++ marker Marker.Code.EOC

/-- Two 31-bit signed pixels with 31 coded planes, reversible 5/3 and RCT.
The Y and Cr low/high subbands are opposite, so intermediate values can exceed
Int32 and still produce a final red sample strictly inside the declared range. -/
def rctCancellationStream : Except Error ByteArray :=
  let m : Int := 2 ^ 31 - 1
  cancellationStream 2 31 { levels := 1, mct := true }
    { guardBits := 2, quant := .none #[30, 30, 30, 30] } #[m, 0, -m]

/-- One signed 8-bit RGB pixel whose Y and Cr fixed-point inputs exceed the Int32
range. Annex G yields red −201/1000 before rounding. -/
def ictCancellationStream : Except Error ByteArray :=
  cancellationStream 1 8 { levels := 0, reversible := false, mct := true }
    { guardBits := 7, quant := .expounded #[{ exponent := 8, mantissa := 0 }] } #[14020, 0, -10000]

/-- Exercise reversible dispatch on the first tile's parsed packet store and native G.1
writer. Return the compact spatial branches alongside the final three rasters. -/
def reversibleRGB (data : ByteArray) : Except Error (Array Bool × Array (Array Int)) := do
  let L := Limits.default
  let h ← Header.parse L data
  let blocks ← Tier2.Headers.decodeAllTileCodeBlocks L h data
  let (g, coding) ← Progression.Layout.ofHeader h 0
  let dst ← NativeOutput.allocOutput L h.siz 0
  let spatial ← (Array.ofFn (n := g.numComps) id).mapM fun c =>
    ReversibleDispatch.component L data h.siz g coding blocks[0]? c 0
  let #[y, cb, cr] := spatial | throw (.malformed Assemble.loc "expected three components")
  let (r, green, b) ← ReversibleDispatch.colour L y cb cr
  let dst ← NativeOutput.writeTile L h.siz 0 g coding dst #[r, green, b]
  let values ← dst.mapM fun p =>
    (Array.range (p.rect.width * p.rect.height)).mapM fun i =>
      (p.get? i).elim (.error (.malformed Assemble.loc "missing output cell")) Except.ok
  return (spatial.map (fun | .plane _ => true | .exact .. => false), values)

/-- Check all six final values using the codestream specification and the wide
spatial/colour kernels on the defining Mallat coefficients. -/
private def rctCancellation : Except Error Bool := do
  let L := Limits.default
  let cs ← rctCancellationStream
  let spec ← Spec.Decode.decode L cs 0
  let r : Header.Rect := ⟨0, 0, 2, 1⟩
  let m : Int := 2 ^ 31 - 1
  let y ← WideReversible.idwt53 L r 1 #[m, -m]
  let cb ← WideReversible.idwt53 L r 1 #[0, 0]
  let cr ← WideReversible.idwt53 L r 1 #[-m, m]
  let (red, green, blue) ← WideReversible.rctInverse L r r r y cb cr
  let exact := #[red, green, blue].map fun c => c.map (Spec.MCT.reconRev true 31)
  let expected := #[#[805306367, 268435455], #[1073741823, 1073741823], #[1073741823, 1073741823]]
  let (compact, actual) ← reversibleRGB cs
  let legacy ← decodeCodestreamNarrow L cs
  return legacy.saturatedBlocks == 0 && compact == #[false, true, false] &&
    actual == expected && exact == expected && spec.comps.map (fun c => c.samples.map (·.value)) == expected

-- Compact spatial inputs can produce a colour outside Int32. Inspect centred RGB before G.1.
private def compactColour : Except Error Bool := do
  let pixel (v : Int32) : NativeOutput.Source := .plane ((Bytes.Plane.zero 1 1).set 0 v (by decide))
  let (r, g, b) ← ReversibleDispatch.colour Limits.default
    (pixel 2147483647) (pixel (-2147483647)) (pixel 2147483647)
  let (r', g', b') ← ReversibleDispatch.colour Limits.default (pixel 2) (pixel (-4)) (pixel 8)
  let packed : NativeOutput.Source → Bool | .plane _ => true | .exact .. => false
  return !packed r && r.get? 0 == some 4294967294 && g.get? 0 == some 2147483647 &&
    b.get? 0 == some 0 && packed r' && packed g' && packed b' &&
    r'.get? 0 == some 9 && g'.get? 0 == some 1 && b'.get? 0 == some (-3)

/-- The conformance directory. -/
def inputDir : System.FilePath := "corpus/files/openjpeg-data/input/conformance"

/-- One corpus case (skipped without the file). -/
def corpusCase (file : String) (reduce : Nat) : IO Nat := do
  let path := inputDir / file
  if !(← path.pathExists) then
    IO.println s!"  spec-decode {file}: corpus absent, skipped"
    return 0
  let cs ← IO.FS.readBinFile path
  let (r, m) := compare cs reduce 1
  match r with
  | some msg => fail file msg
  | none =>
    IO.println s!"  spec-decode {file} (reduce {reduce}): agree, max irreversible difference {m}"
    return 0

-- Replace only SIZ on neutral, single-tile encoder output.
private def wideZero (signed : Bool) : Except Error ByteArray := do
  let img : Encode.Image := { width := 1, height := 1, comps := #[{ depth := 8, samples := #[128] }] }
  let s ← Encode.encode { levels := 0, mct := false } img
  let h ← Header.parse Limits.default s
  let wide := { h.siz with components := h.siz.components.map fun c => { c with depth := 38, signed } }
  let oldSegment := Encode.Marker.segment Marker.Code.SIZ (Encode.Marker.serializeSIZ h.siz)
  let newSegment := Encode.Marker.segment Marker.Code.SIZ (Encode.Marker.serializeSIZ wide)
  return s.extract 0 2 ++ newSegment ++ s.extract (2 + oldSegment.size) s.size

-- Assemble two real packet bodies with distinct values in all three components.
private def tile (a b c : Int) : Except Error ByteArray :=
  let comp := fun (signed : Bool) (v : Int) =>
    ({ depth := 8, signed, samples := Array.replicate 8 v } : Encode.Component)
  let input : Encode.Image := { width := 4, height := 2, comps := #[comp false a, comp true b, comp true c] }
  Encode.encode {levels := 1, mct := false} input

private def twoTiles : Except Error ByteArray := do
  let a ← tile 128 2 (-5)
  let b ← tile 129 (-3) 7
  let ha ← Header.parse Limits.default a
  let hb ← Header.parse Limits.default b
  if ha.main.cod != hb.main.cod || ha.main.qcd != hb.main.qcd then
    throw (.malformed (.at .marker) "inconsistent tile coding")
  let comps := ha.siz.components.mapIdx fun i c => if i == 1 then c else {c with depth := 38}
  let siz := {ha.siz with xsiz := 8, components := comps}
  let sz := fun x => Encode.Marker.segment Marker.Code.SIZ (Encode.Marker.serializeSIZ x)
  -- The SOT marker is followed by Lsot then the two-byte Isot.
  let bp := hb.main.endPos
  return a.extract 0 2 ++ sz siz ++ a.extract (2 + (sz ha.siz).size) (a.size - 2) ++
    b.extract bp (bp + 4) ++ Encode.Marker.pack (Encode.Marker.be16 1) ++
    b.extract (bp + 6) b.size

private def checkNative (data : ByteArray) (reduce w h : Nat) (L : Limits)
    (expected : Array (Int × Int)) : Except Error Bool := do
  let img ← decodeCodestream L data reduce
  let spec ← Spec.Decode.decode L data reduce
  return img.reduce == reduce && img.comps.size == expected.size &&
    spec.comps.size == expected.size && img.saturatedBlocks == 0 &&
    (Array.range expected.size).all fun k => Id.run do
      let some component := img.comps[k]? | return false
      let .native c := component | return false
      let some s := spec.comps[k]? | return false
      let fits := match c.storage with
        | .narrow _ => c.format.depth == 8
        | .wide _ => c.format.depth == 38
      let (left, right) := expected.getD k (0, 0)
      let some format := img.header.siz.components[k]? | return false
      return fits && c.format == format && component.width == w && component.height == h &&
        component.x0 == 0 && component.y0 == 0 && component.dx == 1 && component.dy == 1 &&
        component.get? (w * h) == none &&
        (Array.range (w * h)).all fun j =>
          let v := if j % w < (w + 1) / 2 then left else right
          component.get? j == some v && (s.samples[j]?).map (·.value) == some v

private def checkWideFixtures : Except Error Bool := do
  for signed in [false, true] do
    let v : Int := if signed then 0 else 2^37
    if !(← checkNative (← wideZero signed) 0 1 1 Limits.default #[(v, v)]) then return false
  let data ← twoTiles
  for (r, bytes, cells) in [(0, 272, 48), (1, 68, 12)] do
    let L := {Limits.default with maxDecodedBytes := bytes, maxWorkSamples := cells}
    if !(← checkNative data r (8 / 2^r) (2 / 2^r) L #[(2^37, 2^37 + 1), (2, -3), (-5, 7)]) then
      return false
    match decodeCodestream {L with maxDecodedBytes := bytes - 1} data r with
    | .error (.limitExceeded _ .decodedBytes v b) => if v != bytes || b != bytes - 1 then return false
    | _ => return false
    match decodeCodestream {L with maxWorkSamples := cells - 1} data r with
    | .error (.limitExceeded _ .workSamples v b) => if v != cells || b != cells - 1 then return false
    | _ => return false
  return true

/-- Runs the suite; returns the number of failures. -/
def run : IO Nat := do
  let mut n ← match checkWideFixtures with
    | .ok true => pure 0
    | other => fail "native codestream fixtures" (reprStr other)
  n := n + (← encCase "5/3 1 comp 7x5 NL2" { levels := 2, cbWidthExp := 2, cbHeightExp := 2 }
    (image 7 5 1 8))
  n := n + (← encCase "5/3+RCT 3 comp 9x6 NL2" { levels := 2, cbWidthExp := 2, cbHeightExp := 2 }
    (image 9 6 3 8))
  n := n + (← encCase "5/3 signed 1 comp 5x4 NL1" { levels := 1 } (image 5 4 1 6 true))
  n := n + (← encCase "5/3+RCT reduce 1" { levels := 2, cbWidthExp := 2, cbHeightExp := 2 }
    (image 8 8 3 8) 1)
  n := n + (← encCase "9/7 1 comp 8x6 NL2" { levels := 2, reversible := false, stepLog2 := -2 }
    (image 8 6 1 8))
  n := n + (← encCase "9/7+ICT 3 comp 7x7 NL2"
    { levels := 2, reversible := false, stepLog2 := -2, cbWidthExp := 2, cbHeightExp := 2 }
    (image 7 7 3 8))
  if compactColour.toOption != some true then n := n + (← fail "compact-input RCT" "centred RGB differs")
  match rctCancellation with
  | .ok true => pure ()
  | .ok false => n := n + (← fail "31-plane RCT cancellation" "samples differ")
  | .error e => n := n + (← fail "31-plane RCT cancellation" (toString e))
  match ictCancellationStream >>= fun cs => Spec.Decode.decode Limits.default cs 0 with
  | .error e => n := n + (← fail "ICT cancellation" (toString e))
  | .ok img =>
    let samples := img.comps.map fun c => c.samples.map (·.value)
    let red := ((img.comps.getD 0 default).samples.getD 0 default).exact
    if red != -201 / 1000 || samples != #[#[0], #[127], #[127]] then
      n := n + (← fail "ICT cancellation" s!"pre-DC red {red}, samples {samples}")
  n := n + (← corpusCase "p0_01.j2k" 2)
  n := n + (← corpusCase "p0_09.j2k" 0)
  n := n + (← corpusCase "p0_12.j2k" 0)
  n := n + (← corpusCase "p0_14.j2k" 1)
  return n

end JPEG2000.Tests.SpecDecode
