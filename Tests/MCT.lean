import JPEG2000.MCT
import Spec.MCT
import Tests.DWT53

/-!
# Component transforms, DC shift, clamping (task 5.4)

Plan.md §4 (C7, C8), §5.4, §8; T.800 Annex G.

1. C7 on random and extreme integer triples (`rctInv ∘ rctFwd = id`, `rctFwd ∘ rctInv = id`).
2. Fast RCT `rctSample` = `rctInv` + `Int32` clamp on random and extreme `Int32` triples;
   exact on `|y| < 2^29`.
3. Fast ICT `ictSample` = `ictQ` + clamp; measured C8 error ≤ `ictGain·e + ictRnd/2^F`
   (printed: measured vs bound); lossy round trip of random 8-bit RGB (forward ICT in `Rat`,
   fixed point at `F = fracBits 8`, `ictInverse`, `dcShiftClampIrrev`) gives the image back.
4. DC shift and clamp: `DcShift.make` accepts / refuses bit depths 1, 8, 12, 16, 31, 32, 38
   (signed and unsigned), spec edge values (38 bits in the spec only), fast `rev`/`irrev` =
   `reconRev`/`reconIrrev` on random and extreme cells, `reconIrrev_sat` numerically.
5. OpenJPEG cross-check: `opj_mct_decode` (integer RCT), `opj_mct_decode_real` (`float`
   ICT, compared in `Float` with a tolerance) and the `opj_lrintf` + shift + clamp of
   `opj_tcd_dc_level_shift_decode` (ties excluded: we round ties up, `lrintf` to even).
6. Plane level: `rctInverse`/`ictInverse`/`dcShiftClamp*` = the per-cell kernels; a size
   mismatch is `malformed`.
-/

namespace JPEG2000.Tests.MCT

open JPEG2000 JPEG2000.Bytes JPEG2000.MCT JPEG2000.Spec.MCT
open JPEG2000.Tests.DWT53 (below randInt randPlane envNat)

/-- Runs one named check, printing a line on failure; returns 1 on failure, 0 on success. -/
def expect (name : String) (ok : Bool) : IO Nat := do
  if ok then return 0
  IO.eprintln s!"  FAIL mct: {name}"
  return 1

/-- A rational as a `Float` (via a `2^-40` rounding). -/
def toF (q : Rat) : Float := Float.ofInt (q * 1099511627776).floor / 1099511627776

/-- `|x|` for rationals as a decidable comparison helper. -/
def ratAbs (x : Rat) : Rat := if x < 0 then -x else x

/-- Extreme integers for C7. -/
def extremes : List Int :=
  [0, 1, -1, 2, -2, 3, -3, 4, -4, 2147483647, -2147483648, 1099511627776, -1099511627776,
   (2 : Int) ^ 62, -(2 : Int) ^ 62, 255, -128, 127, 65535]

/-! ## 1. C7 -/

/-- C7 on random and extreme triples. -/
def c7 (cases : Nat) : IO Nat := do
  let mut f := 0
  let mut s : UInt64 := 0xC7
  for _ in [0:cases] do
    let (a, s1) := randInt s 20 true
    let (b, s2) := randInt s1 20 true
    let (c, s3) := randInt s2 20 true
    s := s3
    let t := (a, b, c)
    if rctInv (rctFwd t) != t || rctFwd (rctInv t) != t then
      f := f + (← expect s!"C7 random {t}" false)
  for a in extremes do
    for b in extremes do
      for c in extremes do
        let t := (a, b, c)
        if rctInv (rctFwd t) != t || rctFwd (rctInv t) != t then
          f := f + (← expect s!"C7 extreme {t}" false)
  return f

/-! ## 2. Fast RCT -/

/-- `Int32` extremes. -/
def ext32 : List Int32 := [0, 1, -1, 2147483647, -2147483648, 2147483646, -2147483647,
  536870911, -536870911, 1073741824, -1073741824, 3, -3]

/-- Fast RCT = spec + clamp; exact on small inputs. -/
def fastRct (cases : Nat) : IO Nat := do
  let mut f := 0
  let mut s : UInt64 := 0x5C7
  let check (y0 y1 y2 : Int32) : Bool :=
    let o := rctSample y0 y1 y2
    let t := rctInv (y0.toInt, y1.toInt, y2.toInt)
    o.1.toInt == clamp32 t.1 && o.2.1.toInt == clamp32 t.2.1 && o.2.2.toInt == clamp32 t.2.2
  let exact (y0 y1 y2 : Int32) : Bool :=
    let o := rctSample y0 y1 y2
    let t := rctInv (y0.toInt, y1.toInt, y2.toInt)
    o.1.toInt == t.1 && o.2.1.toInt == t.2.1 && o.2.2.toInt == t.2.2
  for k in [0:cases] do
    let bits := if k % 3 == 0 then 30 else 16
    let (a, s1) := randInt s bits (k % 4 == 0)
    let (b, s2) := randInt s1 bits (k % 4 == 0)
    let (c, s3) := randInt s2 bits (k % 4 == 0)
    s := s3
    let (y0, y1, y2) := (Int32.ofInt a, Int32.ofInt b, Int32.ofInt c)
    if !check y0 y1 y2 then f := f + (← expect s!"rct fast=spec {a} {b} {c}" false)
    if bits == 16 && !exact y0 y1 y2 then f := f + (← expect s!"rct exact {a} {b} {c}" false)
  for a in ext32 do
    for b in ext32 do
      for c in ext32 do
        if !check a b c then f := f + (← expect s!"rct fast=spec extreme {a} {b} {c}" false)
  -- lossless round trip through the forward spec and the fast inverse (16-bit samples)
  for k in [0:cases] do
    let (a, s1) := randInt s 15 false
    let (b, s2) := randInt s1 15 false
    let (c, s3) := randInt s2 15 false
    s := s3
    let y := rctFwd (a, b, c)
    let o := rctSample (Int32.ofInt y.1) (Int32.ofInt y.2.1) (Int32.ofInt y.2.2)
    if (o.1.toInt, o.2.1.toInt, o.2.2.toInt) != (a, b, c) then
      f := f + (← expect s!"rct lossless {k}" false)
  return f

/-! ## 3. Fast ICT, C8 measured -/

/-- `round(q · 2^F)` (ties up). -/
def fix (F : Nat) (q : Rat) : Int := (q * (2 ^ F : Nat) + 1 / 2).floor

/-- Fast ICT = model + clamp on random and extreme cells. -/
def fastIct (cases : Nat) : IO Nat := do
  let mut f := 0
  let mut s : UInt64 := 0x1C7
  let check (y0 y1 y2 : Int32) : Bool :=
    let o := ictSample y0 y1 y2
    let t := ictQ (y0.toInt, y1.toInt, y2.toInt)
    o.1.toInt == clamp32 t.1 && o.2.1.toInt == clamp32 t.2.1 && o.2.2.toInt == clamp32 t.2.2
  for k in [0:cases] do
    let bits := if k % 3 == 0 then 31 else 26
    let (a, s1) := randInt s bits (k % 4 == 0)
    let (b, s2) := randInt s1 bits (k % 4 == 0)
    let (c, s3) := randInt s2 bits (k % 4 == 0)
    s := s3
    if !check (Int32.ofInt a) (Int32.ofInt b) (Int32.ofInt c) then
      f := f + (← expect s!"ict fast=model {a} {b} {c}" false)
  for a in ext32 do
    for b in ext32 do
      for c in ext32 do
        if !check a b c then f := f + (← expect s!"ict fast=model extreme {a} {b} {c}" false)
  return f

/-- The measured C8 error of the ICT against the bound, for `F` fractional bits and an input
error of up to `eUlps` ulps. -/
def ictErr (cases F eUlps : Nat) : IO Nat := do
  let mut f := 0
  let mut s : UInt64 := 0xE8 + F.toUInt64
  let D : Rat := (2 ^ F : Nat)
  let e : Rat := (eUlps : Rat) / D
  let bound := ictGain * e + ictRnd / D
  let mut worst : Rat := 0
  for _ in [0:cases] do
    -- exact inputs: random rationals with denominator 997 in about ±2^(26−F) samples
    let mut ys : Array Rat := #[]
    let mut zs : Array Int := #[]
    for _ in [0:3] do
      let (n, s1) := randInt s (26 - F + 10) false
      let (d, s2) := below s1 (2 * eUlps + 1)
      s := s2
      let y : Rat := (n : Rat) / 997 / 1024
      ys := ys.push y
      -- the fixed-point input: exact value rounded, plus a perturbation of at most `eUlps`
      -- (clamped so the total stays within `e`)
      let z0 := fix F y
      let z := z0 + (d : Int) - eUlps
      let z := if ratAbs ((z : Rat) / D - y) ≤ e then z else z0
      zs := zs.push z
    let o := ictQ (zs.getD 0 0, zs.getD 1 0, zs.getD 2 0)
    let x := ictInv (ys.getD 0 0, ys.getD 1 0, ys.getD 2 0)
    for (oi, xi) in [(o.1, x.1), (o.2.1, x.2.1), (o.2.2, x.2.2)] do
      let err := ratAbs ((oi : Rat) / D - xi)
      if err > worst then worst := err
      if err > bound then f := f + (← expect s!"ict C8 F={F} e={eUlps}: {toF err} > {toF bound}" false)
  IO.println s!"  mct: ICT F={F} input error {eUlps} ulps: measured {toF (worst * D)} ulps, bound {toF (bound * D)} ulps"
  return f

/-- Lossy round trip of random 8-bit RGB through the fixed-point ICT and reconstruction. -/
def ictRoundTrip (cases : Nat) : IO Nat := do
  let mut f := 0
  let mut s : UInt64 := 0x8B
  let F := DWT97.fracBits 8
  match DcShift.make false 8 F with
  | .error _ => return (← expect "DcShift.make 8-bit" false)
  | .ok p =>
    for _ in [0:cases] do
      let (r, s1) := below s 256
      let (g, s2) := below s1 256
      let (b, s3) := below s2 256
      s := s3
      let y := ictFwd ((r : Rat) - 128, (g : Rat) - 128, (b : Rat) - 128)
      let o := ictSample (Int32.ofInt (fix F y.1)) (Int32.ofInt (fix F y.2.1))
        (Int32.ofInt (fix F y.2.2))
      let back := ((p.irrev o.1).toInt, (p.irrev o.2.1).toInt, (p.irrev o.2.2).toInt)
      if back != ((r : Int), (g : Int), (b : Int)) then
        f := f + (← expect s!"ict round trip {r} {g} {b} → {back}" false)
    return f

/-! ## 4. DC shift and clamp -/

/-- `make` accepts exactly the ranges that fit `Int32`. -/
def makeCases : IO Nat := do
  let mut f := 0
  for (sg, d, ok) in ([(false, 1, true), (false, 8, true), (false, 12, true), (false, 16, true),
      (false, 31, true), (false, 32, false), (false, 38, false), (false, 0, false),
      (true, 1, true), (true, 8, true), (true, 16, true), (true, 32, true), (true, 33, false),
      (true, 38, false)] : List (Bool × Nat × Bool)) do
    let got := match DcShift.make sg d 0 with | .ok _ => true | .error _ => false
    f := f + (← expect s!"make signed={sg} depth={d}" (got == ok))
  f := f + (← expect "make F=32 refused"
    (match DcShift.make false 8 32 with | .ok _ => false | .error _ => true))
  return f

/-- Spec edge values (all depths, 38 bits included). -/
def specEdges : IO Nat := do
  let mut f := 0
  -- 38-bit unsigned: offset 2^37, range [0, 2^38 − 1]
  f := f + (← expect "38u zero" (reconRev false 38 0 == 2 ^ 37))
  f := f + (← expect "38u low" (reconRev false 38 (-(2 ^ 37)) == 0))
  f := f + (← expect "38u high" (reconRev false 38 (2 ^ 37 - 1) == 2 ^ 38 - 1))
  f := f + (← expect "38u clamp high" (reconRev false 38 (2 ^ 40) == 2 ^ 38 - 1))
  f := f + (← expect "38s clamp low" (reconRev true 38 (-(2 ^ 40)) == -(2 ^ 37)))
  -- 1-bit
  f := f + (← expect "1u" ([(-2 : Int), -1, 0, 1, 2].map (reconRev false 1) == [0, 0, 1, 1, 1]))
  f := f + (← expect "1s" ([(-2 : Int), -1, 0, 1].map (reconRev true 1) == [-1, -1, 0, 0]))
  -- 8-bit
  f := f + (← expect "8u" ([(-200 : Int), -128, -1, 0, 127, 128, 500].map (reconRev false 8)
    == [0, 0, 127, 128, 255, 255, 255]))
  f := f + (← expect "8s" ([(-200 : Int), -128, 127, 128].map (reconRev true 8)
    == [-128, -128, 127, 127]))
  -- 12-, 16-bit
  f := f + (← expect "12u" (reconRev false 12 0 == 2048 ∧ reconRev false 12 5000 == 4095))
  f := f + (← expect "16s" (reconRev true 16 40000 == 32767 ∧ reconRev true 16 (-40000) == -32768))
  -- rounding: F = 2, values 1.25 → 1, 1.5 → 2 (ties up), −1.5 → −1, −1.75 → −2
  f := f + (← expect "roundFix" ([(5 : Int), 6, -6, -7].map (roundFix 2) == [1, 2, -1, -2]))
  f := f + (← expect "roundFix F=0" ([(5 : Int), -7].map (roundFix 0) == [5, -7]))
  return f

/-- Fast `rev`/`irrev` = spec on random and extreme cells; `reconIrrev_sat` numerically. -/
def fastDc (cases : Nat) : IO Nat := do
  let mut f := 0
  let mut s : UInt64 := 0xDC
  for (sg, d) in ([(false, 1), (false, 8), (false, 12), (false, 16), (false, 31), (true, 1),
      (true, 8), (true, 12), (true, 16), (true, 32)] : List (Bool × Nat)) do
    for F in [0, 1, DWT97.fracBits d, 30, 31] do
      match DcShift.make sg d F with
      | .error _ => f := f + (← expect s!"make {sg} {d} {F}" false)
      | .ok p =>
        let mut xs : List Int32 := ext32
        for k in [0:cases] do
          let (v, s1) := randInt s (if k % 2 == 0 then d + F else 31) (k % 7 == 0)
          s := s1
          xs := Int32.ofInt v :: xs
        for x in xs do
          if (p.rev x).toInt != reconRev sg d x.toInt then
            f := f + (← expect s!"rev {sg} {d} {x}" false)
          if (p.irrev x).toInt != reconIrrev sg d F x.toInt then
            f := f + (← expect s!"irrev {sg} {d} F={F} {x}" false)
        -- saturation invisible when F + d ≤ 32
        if F + d ≤ 32 then
          for v in ([(2 : Int) ^ 31, (2 : Int) ^ 40, -(2 : Int) ^ 31 - 1, -(2 : Int) ^ 40] : List Int) do
            if reconIrrev sg d F (clamp32 v) != reconIrrev sg d F v then
              f := f + (← expect s!"sat {sg} {d} F={F} {v}" false)
  return f

/-! ## 5. OpenJPEG cross-check -/

/-- `opj_mct_decode` (one sample): `g = y − ((u + v) >> 2); r = v + g; b = u + g`, in
`Int` (OpenJPEG computes in `OPJ_INT32`). -/
def opjMctDecode (y u v : Int) : Int × Int × Int :=
  let g := y - Int.shiftRight (u + v) 2
  (v + g, g, u + g)

/-- `opj_mct_decode_real` (one sample, `float`): `r = y + v·1.402`,
`g = y − u·0.34413 − v·0.71414`, `b = y + u·1.772`. -/
def opjMctDecodeReal (y u v : Float) : Float × Float × Float :=
  (y + v * 1.402, y - u * 0.34413 - v * 0.71414, y + u * 1.772)

/-- `opj_lrintf`: round to nearest, ties to even. -/
def lrint (x : Float) : Int :=
  let r := x.floor
  let d := x - r
  let ri : Int := if r < 0 then -((-r).toUInt64.toNat : Int) else (r.toUInt64.toNat : Int)
  if d > 0.5 then ri + 1 else if d < 0.5 then ri else if ri % 2 == 0 then ri else ri + 1

/-- OpenJPEG formulas vs ours. -/
def openjpeg (cases : Nat) : IO Nat := do
  let mut f := 0
  let mut s : UInt64 := 0x0B1
  let F := 18
  let D : Float := 262144
  for _ in [0:cases] do
    let (a, s1) := randInt s 17 false
    let (b, s2) := randInt s1 17 false
    let (c, s3) := randInt s2 17 false
    s := s3
    -- RCT
    if opjMctDecode a b c != rctInv (a, b, c) then
      f := f + (← expect s!"opj rct {a} {b} {c}" false)
    -- ICT: inputs as fixed point (F = 18) of values a/2^8 etc.
    let z0 := a * 1024; let z1 := b * 1024; let z2 := c * 1024
    let o := ictQ (z0, z1, z2)
    let fo := opjMctDecodeReal (Float.ofInt z0 / D) (Float.ofInt z1 / D) (Float.ofInt z2 / D)
    let x := ictInv ((z0 : Rat) / 262144, (z1 : Rat) / 262144, (z2 : Rat) / 262144)
    for (oi, fi, xi) in [(o.1, fo.1, x.1), (o.2.1, fo.2.1, x.2.1), (o.2.2, fo.2.2, x.2.2)] do
      let ours := Float.ofInt oi / D
      -- float32 constants/arithmetic in OpenJPEG; our Float transcription is double: compare
      -- both with the exact value and with each other at 1e-5 relative + 1e-5 absolute
      let tol := 1e-5 * (fi.abs + 1)
      if (ours - fi).abs > tol || (toF xi - fi).abs > tol then
        f := f + (← expect s!"opj ict {a} {b} {c}: {ours} vs {fi}" false)
      -- DC shift + clamp as `opj_tcd_dc_level_shift_decode` (8-bit unsigned), ties excluded
      let fr := fi + 128
      if (fr - fr.floor - 0.5).abs > 1e-3 then
        let opj := clamp 0 255 (lrint fi + 128)
        if reconIrrev false 8 F oi != opj then
          f := f + (← expect s!"opj dc {fi}: {reconIrrev false 8 F oi} vs {opj}" false)
  return f

/-! ## 6. Plane level -/

/-- A plane from a list of cells. -/
def planeOf (w h : Nat) (xs : List Int32) : Plane := Id.run do
  let mut p := Plane.zero w h
  for i in [0:w * h] do
    p := (p.set? i (xs.getD i 0)).getD p
  return p

/-- The cells of a plane. -/
def cellsOf (p : Plane) : List Int32 := (List.range (p.width * p.height)).map fun i => (p.get? i).getD 0

/-- Plane-level transforms = per-cell kernels; size mismatch is an error. -/
def planes : IO Nat := do
  let mut f := 0
  let mut s : UInt64 := 0x91A
  for (w, h) in ([(1, 1), (5, 3), (17, 9), (0, 4)] : List (Nat × Nat)) do
    let (p0, s1) := randPlane s w h 28 true
    let (p1, s2) := randPlane s1 w h 28 true
    let (p2, s3) := randPlane s2 w h 28 true
    s := s3
    let c0 := cellsOf p0; let c1 := cellsOf p1; let c2 := cellsOf p2
    let trip := (c0.zip (c1.zip c2))
    for (name, op, k) in ([("rct", rctInverse, rctSample), ("ict", ictInverse, ictSample)] :
        List (String × (Plane → Plane → Plane → Except Error (Plane × Plane × Plane)) ×
          (Int32 → Int32 → Int32 → Int32 × Int32 × Int32))) do
      match op p0 p1 p2 with
      | .error _ => f := f + (← expect s!"{name} plane {w}×{h}" false)
      | .ok (q0, q1, q2) =>
        let exp := trip.map fun (a, b, c) => k a b c
        f := f + (← expect s!"{name} plane {w}×{h} cells"
          (cellsOf q0 == exp.map (·.1) && cellsOf q1 == exp.map (·.2.1) &&
            cellsOf q2 == exp.map (·.2.2)))
    match DcShift.make false 12 (DWT97.fracBits 12) with
    | .error _ => f := f + (← expect "make 12" false)
    | .ok p =>
      f := f + (← expect s!"dc rev plane {w}×{h}" (cellsOf (dcShiftClampRev p p0) == c0.map p.rev))
      f := f + (← expect s!"dc irrev plane {w}×{h}"
        (cellsOf (dcShiftClampIrrev p p0) == c0.map p.irrev))
  let bad := planeOf 2 2 [1, 2, 3, 4]
  let good := planeOf 4 1 [1, 2, 3, 4]
  f := f + (← expect "size mismatch" (match rctInverse good bad good with
    | .error (.malformed _ _) => true | _ => false))
  return f

/-- Runs the suite; returns the number of failures. -/
def run : IO Nat := do
  let n ← envNat "JPEG2000_MCT_CASES" 400
  let mut f := 0
  f := f + (← c7 n)
  f := f + (← fastRct n)
  f := f + (← fastIct n)
  f := f + (← ictErr n 18 0)
  f := f + (← ictErr n 18 100)
  f := f + (← ictErr n 10 3)
  f := f + (← ictRoundTrip n)
  f := f + (← makeCases)
  f := f + (← specEdges)
  f := f + (← fastDc (n / 20 + 5))
  f := f + (← openjpeg n)
  f := f + (← planes)
  return f

end JPEG2000.Tests.MCT
