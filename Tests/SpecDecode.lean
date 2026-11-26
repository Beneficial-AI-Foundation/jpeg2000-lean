import Spec.Decode
import Encode.Encode
import JPEG2000.WideReversible

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
            let fv := ((fc.plane.get? k).getD 0).toInt
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

/-- Two 31-bit signed pixels with 31 coded planes, reversible 5/3 and RCT.
The Y and Cr low/high subbands are opposite, so intermediate values can exceed
Int32 and still produce a final red sample strictly inside the declared range. -/
def rctCancellationStream : Except Error ByteArray := do
  let comp : Encode.Component := { depth := 8, signed := true, samples := #[0, 0] }
  let base ← Encode.encode { levels := 1, mct := true }
    { width := 2, height := 1, comps := #[comp, comp, comp] }
  let header ← Header.parse Limits.default base
  let siz := { header.siz with components := header.siz.components.map fun c => { c with depth := 31 } }
  let cod := header.main.cod
  let qcd : Marker.QCD := { guardBits := 2, quant := .none #[30, 30, 30, 30] }
  let params ← Header.mkComp 0 cod.style qcd 0
  let rect : Header.Rect := ⟨0, 0, 2, 1⟩
  let m : Int := 2 ^ 31 - 1
  let mut precs := #[]
  for (index, low) in (#[(0, m), (1, 0), (2, -m)] : Array (Nat × Int)) do
    let tc := Tier2.Geometry.tileComp rect (siz.components.getD index default) params
    let bands := Encode.compBands 2 1 1 fun _ b _ _ => if b == .LL then low else -low
    let (prec, _) ← Encode.encodeComp Limits.default tc index bands
    precs := precs.push prec
  let data := Encode.Tier2.encodeTileLRCP precs
  let sot : TilePart.SOT := { isot := 0, psot := (14 + data.size).toUInt32, tpsot := 0, tnsot := 1 }
  let marker := fun k => Encode.Marker.pack (Encode.Marker.be16 k)
  let seg := Encode.Marker.segment
  return marker Marker.Code.SOC ++ seg Marker.Code.SIZ (Encode.Marker.serializeSIZ siz) ++
    seg Marker.Code.COD (Encode.Marker.serializeCOD cod) ++ seg Marker.Code.QCD (Encode.Marker.serializeQCD qcd) ++
    seg Marker.Code.SOT (Encode.TilePart.serializeSOT sot) ++ marker Marker.Code.SOD ++ data ++ marker Marker.Code.EOC

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
  return exact == expected && spec.comps.map (fun c => c.samples.map (·.value)) == expected

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

/-- Runs the suite; returns the number of failures. -/
def run : IO Nat := do
  let mut n := 0
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
  match rctCancellation with
  | .ok true => pure ()
  | .ok false => n := n + (← fail "31-plane RCT cancellation" "samples differ")
  | .error e => n := n + (← fail "31-plane RCT cancellation" (toString e))
  n := n + (← corpusCase "p0_01.j2k" 2)
  n := n + (← corpusCase "p0_09.j2k" 0)
  n := n + (← corpusCase "p0_12.j2k" 0)
  n := n + (← corpusCase "p0_14.j2k" 1)
  return n

end JPEG2000.Tests.SpecDecode
