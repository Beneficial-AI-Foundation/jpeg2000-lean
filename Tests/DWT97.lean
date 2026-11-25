import JPEG2000.DWT97
import Spec.DWT97
import Tests.DWT53

/-!
# 9/7 wavelet (task 5.3): `Rat` round trips, OpenJPEG cross-check, fast = model, C8 bound

Plan.md §4 (C8), §5.2 "DWT", §5.4, §8; T.800 Annex F.3.8.2 / F.4.8.2.

1. `Rat` round trips: `sr1d ∘ sd1d = id` (proved as `Spec.DWT97.sr1d_sd1d`) on random
   lengths 0–24 and starts 0–5; multi-level `srMulti ∘ sdMulti = id` on small rectangles.
2. OpenJPEG cross-check (`Float`, tests only): `opj_v8dwt_decode` for one lane (`cas`,
   `sn`, `dn`, `K`, `two_invK = 2/K`, mirrored ends, a lone sample untouched) transcribed
   below and compared with `Spec.DWT97.sr1d` after halving the high-pass input (OpenJPEG's
   gain-0 step sizes are half of T.800's for HL/LH and the `2/K` compensates; module doc of
   `Spec.DWT97`).
3. The `Int32` kernel `lift1d97` equals the fixed-point model `qsr1d` on random signals.
4. 2-D, NL 0–4, random tile-component rectangles: `idwt97Fast = idwt97Model` (the plane
   loops = `qsrMulti`), and the measured error against the exact `Rat` `srMulti` is at most
   the proved bound `En nl 0` (printed: measured vs bound).
5. A random 8-bit image: forward `Rat` 9/7, coefficients rounded to `F = fracBits 8` bits,
   Mallat layout, `idwt97`: the reconstruction rounds back to the image.
6. Near-overflow planes: the fast path refuses and `idwt97` = the `Rat` slow path.
-/

namespace JPEG2000.Tests.DWT97

open JPEG2000 JPEG2000.Bytes JPEG2000.DWT97
open JPEG2000.Header (Rect)
open JPEG2000.Tests.DWT53 (below randList randPlane randRect fromDec planeEq envNat)
open JPEG2000.DWT53 (Buf halfN toDec specRect)

/-- A rational as a `Float` (printing and the OpenJPEG comparison only; via a 2^-40
rounding so huge denominators do not overflow). -/
def toF (q : Rat) : Float := Float.ofInt (q * 1099511627776).floor / 1099511627776

/-- Runs one named check, printing a line on failure; returns 1 on failure, 0 on success. -/
def expect (name : String) (ok : Bool) : IO Nat := do
  if ok then return 0
  IO.eprintln s!"  FAIL dwt97: {name}"
  return 1

/-- The values of a rational signal on `[i0, i0 + n)`. -/
def sigList (i0 : Int) (n : Nat) (f : Spec.DWT97.Sig) : List Rat :=
  (List.range n).map fun (k : Nat) => f (i0 + (k : Int))

/-- A list as a rational signal starting at `i0` (0 outside). -/
def ofListR (i0 : Int) (xs : List Rat) : Spec.DWT97.Sig := fun j =>
  if i0 ≤ j then xs.getD (j - i0).toNat 0 else 0

/-! ## 1. Rat round trips -/

/-- `sr1d (sd1d x) = x` on random signals. -/
def roundTrip1d (cases : Nat) : IO Nat := do
  let mut f := 0
  let mut s : UInt64 := 0x97A
  for _ in [0:cases] do
    let (n, s1) := below s 25
    let (i0, s2) := below s1 6
    let (xs, s3) := randList s2 n 12 false
    s := s3
    let x := ofListR i0 (xs.map fun (v : Int) => (v : Rat))
    let y := Spec.DWT97.sd1d i0 (i0 + n) x
    let z := Spec.DWT97.sr1d i0 (i0 + n) y
    f := f + (← expect s!"rat roundtrip 1d n={n} i0={i0}"
      (sigList i0 n z == xs.map fun (v : Int) => (v : Rat)))
  return f

/-- A rational image grid from an integer array (row-major on `tc`). -/
def gridR (tc : Rect) (xs : Array Int) (scale : Rat) : Spec.DWT97.Grid := ⟨fun u v =>
  let w : Int := tc.x1 - tc.x0
  (xs.getD ((v - tc.y0) * w + (u - tc.x0)).toNat 0 : Rat) * scale⟩

/-- `srMulti (sdMulti g) = g` on small random rectangles. -/
def roundTrip2d (cases : Nat) : IO Nat := do
  let mut f := 0
  let mut s : UInt64 := 0x97B
  for _ in [0:cases] do
    let (x0, s1) := below s 5
    let (y0, s2) := below s1 5
    let (w, s3) := below s2 9
    let (h, s4) := below s3 9
    let (nl, s5) := below s4 4
    s := s5
    let tc : Rect := ⟨x0, y0, x0 + w, y0 + h⟩
    let (xs, s6) := randList s (w * h) 8 false
    s := s6
    let g := gridR tc xs.toArray 1
    let r := specRect tc
    let back := Spec.DWT97.memo r (Spec.DWT97.srMulti r nl (Spec.DWT97.sdMulti r nl g))
    let ok := (List.range h).all fun j => (List.range w).all fun i =>
      back.get (x0 + i) (y0 + j) == g.get (x0 + i) (y0 + j)
    f := f + (← expect s!"rat roundtrip 2d tc=({x0},{y0},{w}x{h}) nl={nl}" ok)
  return f

/-! ## 2. OpenJPEG `opj_v8dwt_decode`, one lane, transcribed (`Float`) -/

/-- OpenJPEG's constants (`opj_dwt_alpha` … `opj_K`, `two_invK`). -/
def oAlpha : Float := -1.586134342
/-- `opj_dwt_beta`. -/ def oBeta : Float := -0.052980118
/-- `opj_dwt_gamma`. -/ def oGamma : Float := 0.882911075
/-- `opj_dwt_delta`. -/ def oDelta : Float := 0.443506852
/-- `opj_K`. -/ def oK : Float := 1.230174105
/-- `two_invK`. -/ def oTwoInvK : Float := 1.625732422

/-- `opj_v8dwt_decode_step2` for one lane: `w[2i+1 − 1]` (the sample before each `w` slot)
gets `c·(l + w)`, the last one mirrored (`2c·l`) when `m < end`. `l` and `w` are the array
offsets of the first neighbour and the first updated slot's successor. -/
def oStep2 (a : Array Float) (lOff wOff : Nat) (start end_ m : Nat) (c : Float) : Array Float :=
  Id.run do
    let mut a := a
    let imax := min end_ m
    let mut fl := lOff
    let mut fw := wOff
    if start > 0 then
      fw := wOff + 2 * start
      fl := fw - 2
    for _ in [start:imax] do
      a := a.setIfInBounds (fw - 1) (a.getD (fw - 1) 0 + (a.getD (fl) 0 + a.getD (fw) 0) * c)
      fl := fw
      fw := fw + 2
    if m < end_ then
      a := a.setIfInBounds (fw - 1) (a.getD (fw - 1) 0 + a.getD (fl) 0 * (c + c))
    return a

/-- `opj_v8dwt_decode` for one lane on the interleaved array `w` (`cas` = parity of the
first sample, `sn` low and `dn` high samples). -/
def oDecode (twoInvK : Float) (w : Array Float) (sn dn cas : Nat) : Array Float := Id.run do
  let (a, b) := if cas == 0 then (0, 1) else (1, 0)
  if cas == 0 && !(dn > 0 || sn > 1) then return w
  if cas == 1 && !(sn > 0 || dn > 1) then return w
  let mut w := w
  for i in [0:sn] do w := w.setIfInBounds (a + 2 * i) (w.getD (a + 2 * i) 0 * oK)
  for i in [0:dn] do w := w.setIfInBounds (b + 2 * i) (w.getD (b + 2 * i) 0 * twoInvK)
  let mL := min sn (dn - a)
  let mH := min dn (sn - b)
  -- step2(l = wavelet + b, w = wavelet + a + 1, …): the low samples get the δ step.
  w := oStep2 w b (a + 1) 0 sn mL (-oDelta)
  w := oStep2 w a (b + 1) 0 dn mH (-oGamma)
  w := oStep2 w b (a + 1) 0 sn mL (-oBeta)
  w := oStep2 w a (b + 1) 0 dn mH (-oAlpha)
  return w

/-- OpenJPEG (high-pass input halved) agrees with `sr1d`: within `1e−3` (inputs ≤ 1024;
OpenJPEG's constants have 9–10 digits) when its `two_invK` is replaced by `2/K`, and within
`0.2` with its historic `two_invK = 1.625732422` (`2/K = 1.6257861…`: 3·10⁻⁵ relative). -/
def opjChecks (cases : Nat) : IO Nat := do
  let mut f := 0
  let mut s : UInt64 := 0x97C
  let mut worstExact : Float := 0
  let mut worstHist : Float := 0
  for _ in [0:cases] do
    let (n, s1) := below s 20
    let (i0, s2) := below s1 4
    let (xs, s3) := randList s2 (n + 1) 10 false
    s := s3
    let n := n + 1
    let cas := i0 % 2
    let sn := (i0 + n + 1) / 2 - (i0 + 1) / 2
    let dn := n - sn
    -- T.800 input: interleaved coefficients at absolute positions i0 … i0 + n − 1.
    let y := ofListR i0 (xs.map fun (v : Int) => (v : Rat))
    let exact := sigList i0 n (Spec.DWT97.sr1d i0 (i0 + n) y)
    -- OpenJPEG input: high-pass (odd absolute positions) halved.
    let wIn : Array Float := (xs.toArray.mapIdx fun k v =>
      if (i0 + k) % 2 == 1 then Float.ofInt v / 2 else Float.ofInt v)
    let errOf := fun (out : Array Float) => (List.range n).foldl (fun m k =>
      max m (Float.abs (out.getD k 0 - toF (exact.getD k 0)))) 0
    let eE := errOf (oDecode (2 / oK) wIn sn dn cas)
    let eH := errOf (oDecode oTwoInvK wIn sn dn cas)
    worstExact := max worstExact eE
    worstHist := max worstHist eH
    f := f + (← expect s!"opj 9/7 (exact 2/K) n={n} i0={i0} err={eE}" (eE < 1e-3))
    f := f + (← expect s!"opj 9/7 (two_invK) n={n} i0={i0} err={eH}" (eH < 0.2))
  IO.println s!"  dwt97: OpenJPEG float vs Rat spec, max |diff| = {worstExact} (exact 2/K), {worstHist} (OpenJPEG's two_invK), inputs |y| ≤ 1024"
  return f

/-! ## 3. Kernel = model -/

/-- `lift1d97` on a fresh buffer holding `ys`, read back (`none` if the flag dropped). -/
def fast1d (par : Nat) (ys : List Int) : Option (List Int) := Id.run do
  let n := ys.length
  let mut p := Plane.zero n 1
  for i in [0:n] do
    p := (p.set? i (Int32.ofInt (ys.getD i 0))).getD p
  if h : p.width * p.height = n * 1 then
    let b : Buf (n * 1) := ⟨p, h⟩
    let (b, ok) := lift1d97 0 n par (by omega) b true
    if ok then
      return some ((List.range n).map fun i => ((b.1.get? i).map (·.toInt)).getD 0)
    else return none
  else return none

/-- `lift1d97 = qsr1d` and its error against `sr1d` is within `E1 0`. -/
def kernelChecks (cases : Nat) : IO Nat := do
  let mut f := 0
  let mut s : UInt64 := 0x97D
  let mut worst : Rat := 0
  for _ in [0:cases] do
    let (n, s1) := below s 30
    let (i0, s2) := below s1 6
    let (ys, s3) := randList s2 n 26 false
    s := s3
    let y : Int → Int := fun j => if i0 ≤ j then ys.getD (j - i0).toNat 0 else 0
    let model := (List.range n).map fun (k : Nat) => qsr1d i0 (i0 + n) y (i0 + (k : Int))
    match fast1d i0 ys with
    | some out =>
      f := f + (← expect s!"kernel = model n={n} i0={i0}" (out == model))
      let exact := sigList i0 n (Spec.DWT97.sr1d i0 (i0 + n) (castS y))
      for k in [0:n] do
        let e := ((out.getD k 0 : Rat) - exact.getD k 0).abs
        if worst < e then worst := e
    | none => f := f + (← expect s!"kernel refused n={n} i0={i0}" false)
  let b := E1 0
  IO.println s!"  dwt97: 1-D kernel max error {toF worst} ulp, proved bound E1 0 = {toF b}"
  f := f + (← expect "1-D error within E1 0" (worst ≤ b))
  return f

/-! ## 4–6. Planes -/

/-- Fast = model, measured error vs the proved bound, near-overflow fallback. -/
def planeChecks (cases : Nat) : IO Nat := do
  let mut f := 0
  let mut s : UInt64 := 0x97E
  let mut refusals := 0
  let mut worst : Array Rat := Array.replicate 5 0
  for c in [0:cases] do
    let (tc, s1) := randRect s
    let (nl, s2) := below s1 5
    s := s2
    let w := tc.x1 - tc.x0
    let h := tc.y1 - tc.y0
    let nm := s!"tc=({tc.x0},{tc.y0},{tc.x1},{tc.y1}) nl={nl}"
    let (p, s3) := randPlane s w h 22 false
    s := s3
    match idwt97Fast p tc nl with
    | some q =>
      f := f + (← expect s!"fast = model {nm}" (planeEq q (idwt97Model p tc nl)))
      let r := specRect tc
      let g := Spec.DWT97.memo r (Spec.DWT97.srMulti r nl (castDec (toDec p tc nl)))
      let mut m : Rat := 0
      for j in [0:h] do
        for i in [0:w] do
          let fv := ((q.get? (j * w + i)).map (·.toInt)).getD 0
          let e := ((fv : Rat) - g.get (tc.x0 + i) (tc.y0 + j)).abs
          if m < e then m := e
      if worst.getD nl 0 < m then worst := worst.setIfInBounds nl m
      f := f + (← expect s!"error within En {nm}: {toF m}" (m ≤ En nl 0))
    | none => f := f + (← expect s!"fast refused {nm}" false)
    if c % 4 == 0 then
      let (p, s4) := randPlane s w h 30 true
      s := s4
      if (idwt97Fast p tc nl).isNone then refusals := refusals + 1
      match idwt97 p tc nl with
      | .ok q =>
        match idwt97Fast p tc nl with
        | some q' => f := f + (← expect s!"idwt97 = fast {nm}" (planeEq q q'))
        | none => f := f + (← expect s!"idwt97 = spec {nm}" (planeEq q (idwt97Spec p tc nl)))
      | .error _ => f := f + (← expect s!"error {nm}" false)
  f := f + (← expect s!"some fast-path refusals exercised ({refusals})" (refusals > 0))
  for nl in [0:5] do
    IO.println s!"  dwt97: NL={nl} measured max error {toF (worst.getD nl 0)} ulp, proved bound En = {toF (En nl 0)} ulp"
  let bad := idwt97 (Plane.zero 3 3) ⟨0, 0, 4, 3⟩ 1
  f := f + (← expect "size mismatch" (match bad with | .error _ => true | .ok _ => false))
  return f

/-- A rational band grid (band coordinates within `[−1, 40)²`) evaluated once (in `IO`, so
the compiler cannot move the work into the reading closure) and rounded to integers. -/
def roundGrid (g : Spec.DWT97.Grid) : IO Spec.DWT53.Grid := do
  let mut a : Array Int := Array.mkEmpty (41 * 41)
  for j in [0:41] do
    for i in [0:41] do
      a := a.push (roundRat (g.get ((i : Int) - 1) ((j : Int) - 1)))
  return ⟨fun u v => a.getD ((v + 1) * 41 + (u + 1)).toNat 0⟩

/-- An 8-bit image through forward `Rat` 9/7, fixed point with `F = fracBits 8`, `idwt97`:
every sample rounds back to the image. -/
def imageChecks (cases : Nat) : IO Nat := do
  let mut f := 0
  let mut s : UInt64 := 0x97F
  let F := fracBits 8
  let sc : Rat := ((2 ^ F : Nat) : Rat)
  let mut worst : Rat := 0
  for _ in [0:cases] do
    let (tc, s1) := randRect s
    let (nl, s2) := below s1 4
    s := s2
    let w := tc.x1 - tc.x0
    let h := tc.y1 - tc.y0
    let (xs, s3) := randList s (w * h) 7 false
    s := s3
    let r := specRect tc
    let d := Spec.DWT97.sdMulti r nl (gridR tc xs.toArray sc)
    let ll ← roundGrid d.ll
    let mut det := #[]
    for b in d.details do
      det := det.push ((← roundGrid b.1), (← roundGrid b.2.1), (← roundGrid b.2.2))
    let dq : Spec.DWT53.Dec := ⟨ll, det.toList⟩
    let p := fromDec dq tc nl
    match idwt97 p tc nl with
    | .ok q =>
      let mut ok := true
      for i in [0:w * h] do
        let fv := ((q.get? i).map (·.toInt)).getD 0
        let e := ((fv : Rat) / sc - (xs.getD i 0 : Rat)).abs
        if worst < e then worst := e
        if roundRat ((fv : Rat) / sc) != xs.getD i 0 then ok := false
      f := f + (← expect s!"image round trip tc=({tc.x0},{tc.y0},{tc.x1},{tc.y1}) nl={nl}" ok)
    | .error _ => f := f + (← expect "image idwt97 error" false)
  IO.println s!"  dwt97: 8-bit image (F = {F}) max |decoded − image| = {toF worst} samples"
  return f

/-- Prints the proved bound `En nl 0 · 2^−F` for typical bit depths. -/
def printBounds : IO Unit := do
  for depth in [8, 12, 16] do
    let F := fracBits depth
    let row := (List.range 8).map fun nl => toF (En nl 0 / ((2 ^ F : Nat) : Rat))
    IO.println s!"  dwt97: proved bound (samples), depth {depth}, F = {F}, NL 0..7: {row}"

/-- Runs the suite; returns the number of failures. -/
def run : IO Nat := do
  let n1 ← envNat "JPEG2000_DWT97_CASES1D" 150
  let n2 ← envNat "JPEG2000_DWT97_CASES2D" 24
  let mut f := 0
  let t0 ← IO.monoMsNow
  f := f + (← roundTrip1d n1)
  f := f + (← roundTrip2d 6)
  let t1 ← IO.monoMsNow
  f := f + (← opjChecks n1)
  f := f + (← kernelChecks n1)
  let t2 ← IO.monoMsNow
  f := f + (← planeChecks n2)
  let t3 ← IO.monoMsNow
  f := f + (← imageChecks 4)
  let t4 ← IO.monoMsNow
  printBounds
  IO.println s!"  dwt97: times (ms) roundtrips {t1 - t0}, 1-D {t2 - t1}, planes {t3 - t2}, image {t4 - t3}"
  return f

end JPEG2000.Tests.DWT97
