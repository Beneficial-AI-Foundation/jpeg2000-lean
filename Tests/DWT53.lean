import JPEG2000.DWT53
import JPEG2000.Tier2.Geometry
import Spec.DWT53

/-!
# 5/3 wavelet (task 5.2): spec round trips, OpenJPEG cross-check, fast = spec

Plan.md §4 (C6), §5.2 "DWT", §8; T.800 Annex F.3/F.4, B.5/B.15.

1. Spec round trips `sr1dList ∘ sd1dList = id` (proved as `sr1dList_sd1dList`; tested anyway)
   on random lengths 0–70, start parities 0–9 and values including `±2^31`, `±2^40`.
2. OpenJPEG cross-check: `opj_dwt_encode_1` / `opj_dwt_decode_1` (5/3, `cas` = start parity,
   clamped neighbours, `S(0) *= 2` / `S(0) /= 2` for a lone odd sample) transcribed below and
   compared with `sd1dList` / `sr1dList` on hand-picked and random signals.
3. Fast 1-D kernel `lift1d` (Int32 cells) = `sr1dList` on random signals.
4. Mallat layout vs `Tier2.Geometry.bandRect` (B-15) for random tile-components and levels.
5. 2-D, NL 0–5, random tile-component rectangles (odd/even offsets, 1×1, 1×N, N×1):
   (a) an image is decomposed with `sdMulti`, written into the Mallat layout, and `idwt53`
   must give the image back (fast path); (b) random Mallat planes: `idwt53Fast` = the spec
   slow path `idwt53Spec`; (c) values near `±2^31` force the fast path to refuse, and `idwt53`
   then equals `idwt53Spec`.
-/

namespace JPEG2000.Tests.DWT53

open JPEG2000 JPEG2000.Bytes JPEG2000.DWT53
open JPEG2000.Header (Rect resRect)
open JPEG2000.Spec.DWT53 (sd1dList sr1dList sdMulti Grid Dec)

/-- Runs one named check, printing a line on failure; returns 1 on failure, 0 on success. -/
def expect (name : String) (ok : Bool) : IO Nat := do
  if ok then return 0
  IO.eprintln s!"  FAIL dwt53: {name}"
  return 1

/-- One splitmix64 step: the output word and the next state. -/
def splitmix (s : UInt64) : UInt64 × UInt64 :=
  let s := s + 0x9E3779B97F4A7C15
  let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), s)

/-- A pseudo-random value below `m` (`m > 0`) and the next state. -/
def below (s : UInt64) (m : Nat) : Nat × UInt64 :=
  let (z, s) := splitmix s
  ((z >>> 11).toNat % m, s)

/-- A random integer: mostly `±2^bits`, sometimes an extreme value. -/
def randInt (s : UInt64) (bits : Nat) (extremes : Bool) : Int × UInt64 :=
  let (k, s) := below s 16
  if extremes && k == 0 then
    let (e, s) := below s 6
    ([2147483647, -2147483648, 1099511627776, -1099511627776, 2147483646, -2147483647].getD e 0, s)
  else
    let (v, s) := below s (2 ^ (bits + 1))
    ((v : Int) - 2 ^ bits, s)

/-- A random list of `n` integers. -/
def randList (s : UInt64) (n bits : Nat) (extremes : Bool) : List Int × UInt64 := Id.run do
  let mut s := s
  let mut out : Array Int := #[]
  for _ in [0:n] do
    let (v, s') := randInt s bits extremes
    s := s'
    out := out.push v
  return (out.toList, s)

/-! ## OpenJPEG transcription (`opj_dwt_encode_1` / `opj_dwt_decode_1`, 5/3) -/

/-- OpenJPEG's interleaved array accessors: `S(i) = a[2i]`, `D(i) = a[2i+1]`, clamped
variants `S_`, `D_`, `SS_`, `DD_`. -/
structure Opj where
  /-- The interleaved array. -/
  a : Array Int
  /-- `dn`. -/
  dn : Int
  /-- `sn`. -/
  sn : Int

/-- `S(i)`. -/ def Opj.S (o : Opj) (i : Int) : Int := o.a.getD (2 * i).toNat 0
/-- `D(i)`. -/ def Opj.D (o : Opj) (i : Int) : Int := o.a.getD (1 + 2 * i).toNat 0
/-- `S_(i)`. -/ def Opj.S_ (o : Opj) (i : Int) : Int :=
  if i < 0 then o.S 0 else if i ≥ o.sn then o.S (o.sn - 1) else o.S i
/-- `D_(i)`. -/ def Opj.D_ (o : Opj) (i : Int) : Int :=
  if i < 0 then o.D 0 else if i ≥ o.dn then o.D (o.dn - 1) else o.D i
/-- `SS_(i)`. -/ def Opj.SS_ (o : Opj) (i : Int) : Int :=
  if i < 0 then o.S 0 else if i ≥ o.dn then o.S (o.dn - 1) else o.S i
/-- `DD_(i)`. -/ def Opj.DD_ (o : Opj) (i : Int) : Int :=
  if i < 0 then o.D 0 else if i ≥ o.sn then o.D (o.sn - 1) else o.D i
/-- Sets `S(i)`. -/ def Opj.setS (o : Opj) (i v : Int) : Opj :=
  { o with a := o.a.setIfInBounds (2 * i).toNat v }
/-- Sets `D(i)`. -/ def Opj.setD (o : Opj) (i v : Int) : Opj :=
  { o with a := o.a.setIfInBounds (1 + 2 * i).toNat v }

/-- `>>` on C `int` (arithmetic shift = floor division). -/
def asr (v : Int) (k : Nat) : Int := v / 2 ^ k

/-- `opj_dwt_encode_1` (5/3) on an interleaved signal starting at absolute parity `cas`. -/
def opjEncode (xs : List Int) (cas : Nat) : List Int := Id.run do
  let n := xs.length
  let sn : Nat := if cas = 0 then (n + 1) / 2 else n / 2
  let dn : Nat := n - sn
  let mut o : Opj := { a := xs.toArray, dn, sn }
  if cas = 0 then
    if dn > 0 || sn > 1 then
      for i in [0:dn] do o := o.setD i (o.D i - asr (o.S_ i + o.S_ (i + 1)) 1)
      for i in [0:sn] do o := o.setS i (o.S i + asr (o.D_ (i - 1) + o.D_ i + 2) 2)
  else
    if sn == 0 && dn == 1 then o := o.setS 0 (o.S 0 * 2)
    else
      for i in [0:dn] do o := o.setS i (o.S i - asr (o.DD_ i + o.DD_ (i - 1)) 1)
      for i in [0:sn] do o := o.setD i (o.D i + asr (o.SS_ i + o.SS_ (i + 1) + 2) 2)
  return o.a.toList

/-- `opj_dwt_decode_1` (5/3) on an interleaved signal starting at absolute parity `cas`
(`/= 2` is C division, truncating). -/
def opjDecode (xs : List Int) (cas : Nat) : List Int := Id.run do
  let n := xs.length
  let sn : Nat := if cas = 0 then (n + 1) / 2 else n / 2
  let dn : Nat := n - sn
  let mut o : Opj := { a := xs.toArray, dn, sn }
  if cas = 0 then
    if dn > 0 || sn > 1 then
      for i in [0:sn] do o := o.setS i (o.S i - asr (o.D_ (i - 1) + o.D_ i + 2) 2)
      for i in [0:dn] do o := o.setD i (o.D i + asr (o.S_ i + o.S_ (i + 1)) 1)
  else
    if sn == 0 && dn == 1 then o := o.setS 0 (Int.tdiv (o.S 0) 2)
    else
      for i in [0:sn] do o := o.setD i (o.D i - asr (o.SS_ i + o.SS_ (i + 1) + 2) 2)
      for i in [0:dn] do o := o.setS i (o.S i + asr (o.DD_ i + o.DD_ (i - 1)) 1)
  return o.a.toList

/-- Hand-picked signals for the OpenJPEG cross-check (with expected forward outputs for the
first two, worked by hand from F-9/F-10). -/
def handChecks : IO Nat := do
  let mut f := 0
  -- [1,2,3,4] at i0 = 0: d0 = 2 − ⌊(1+3)/2⌋ = 0, d1 = 4 − ⌊(3+3)/2⌋ = 1,
  -- s0 = 1 + ⌊(0+0+2)/4⌋ = 1, s1 = 3 + ⌊(0+1+2)/4⌋ = 3.
  f := f + (← expect "hand [1,2,3,4]@0" (sd1dList 0 [1, 2, 3, 4] == [1, 0, 3, 1]))
  -- [5] at i0 = 1 (lone odd sample doubled).
  f := f + (← expect "hand [5]@1" (sd1dList 1 [5] == [10] && sr1dList 1 [10] == [5]))
  f := f + (← expect "hand []" (sd1dList 3 [] == [] && sr1dList 3 [] == []))
  let sigs : List (List Int) :=
    [[7], [1, 2], [9, -3], [1, 2, 3], [10, 20, 30, 40, 50], [-5, 100, -7, 3, 3, 8],
     [0, 255, 0, 255, 0, 255, 0], [128, 129, 130, 250, 3, 0, 77, 81]]
  for xs in sigs do
    for i0 in ([0, 1, 2, 3] : List Nat) do
      let fw := sd1dList (i0 : Int) xs
      f := f + (← expect s!"opj encode {xs}@{i0}" (fw == opjEncode xs (i0 % 2)))
      f := f + (← expect s!"opj decode {xs}@{i0}" (opjDecode fw (i0 % 2) == xs))
      f := f + (← expect s!"spec decode {xs}@{i0}" (sr1dList (i0 : Int) fw == xs))
  return f

/-! ## 1-D random checks -/

/-- Runs the fast kernel `lift1d` on a list (cells as `Int32`) at absolute start `i0`. -/
def fast1d (i0 : Nat) (ys : List Int) : Option (List Int) := Id.run do
  let n := ys.length
  let mut b : Buf n := ⟨Plane.zero n 1, Nat.mul_one n⟩
  for h : i in [0:n] do
    b := b.set i (Int32.ofInt (ys.getD i 0)) h.upper
  let (b2, ok) := lift1d 0 n i0 (by omega) b true
  if !ok then return none
  return some ((List.range n).map fun i => ((b2.1.get? i).map (·.toInt)).getD 0)

/-- Random 1-D checks: spec round trip, OpenJPEG agreement, fast kernel = spec. -/
def random1d (cases : Nat) : IO Nat := do
  let mut f := 0
  let mut s : UInt64 := 0x5EED53
  for c in [0:cases] do
    let (n, s1) := below s 71
    let (i0, s2) := below s1 10
    let (xs, s3) := randList s2 n (if c % 3 == 0 then 30 else 12) (c % 5 == 0)
    s := s3
    let fw := sd1dList (i0 : Int) xs
    f := f + (← expect s!"roundtrip n={n} i0={i0}" (sr1dList (i0 : Int) fw == xs))
    f := f + (← expect s!"opj encode n={n} i0={i0}" (fw == opjEncode xs (i0 % 2)))
    f := f + (← expect s!"opj decode n={n} i0={i0}" (opjDecode fw (i0 % 2) == xs))
    -- Fast kernel on random Int32 coefficients (not necessarily a forward image).
    let (ys, s4) := randList s n 20 false
    s := s4
    match fast1d i0 ys with
    | some zs => f := f + (← expect s!"fast1d n={n} i0={i0}" (zs == sr1dList (i0 : Int) ys))
    | none => f := f + (← expect s!"fast1d overflow n={n} i0={i0}" false)
    -- And on forward coefficients of an image near the Int32 limits (may refuse).
    let (zs, s5) := randList s n 29 true
    s := s5
    let fz := sd1dList (i0 : Int) zs
    if fz.all (fun v => -2147483648 ≤ v && v ≤ 2147483647) then
      match fast1d i0 fz with
      | some r => f := f + (← expect s!"fast1d big n={n} i0={i0}" (r == zs))
      | none =>
        -- In 1-D every stored value is a final output sample, so refusal is allowed
        -- exactly when some sample of the image leaves the Int32 range.
        let inRange := zs.all (fun v => -2147483648 ≤ v && v ≤ 2147483647)
        f := f + (← expect s!"fast1d refused n={n} i0={i0}" (!inRange))
  return f

/-! ## Mallat layout -/

/-- Writes a spec decomposition of `tc` with `nl` levels into a Mallat-layout plane (the
inverse of `toDec`). -/
def fromDec (d : Dec) (tc : Rect) (nl : Nat) : Plane := Id.run do
  let w := tc.x1 - tc.x0
  let h := tc.y1 - tc.y0
  let mut p := Plane.zero w h
  let put := fun (p : Plane) (x y : Nat) (v : Int) =>
    (p.set? (y * w + x) (Int32.ofInt v)).getD p
  let L := halfN tc nl
  for y in [L.y0:L.y1] do
    for x in [L.x0:L.x1] do
      p := put p (x - L.x0) (y - L.y0) (d.ll.get x y)
  for l in [1:nl + 1] do
    let R := halfN tc (l - 1)
    let Lr := halfN tc l
    let sn := Lr.x1 - Lr.x0
    let sv := Lr.y1 - Lr.y0
    let (hl, lh, hh) := d.details.getD (l - 1) (⟨fun _ _ => 0⟩, ⟨fun _ _ => 0⟩, ⟨fun _ _ => 0⟩)
    for v in [Lr.y0:Lr.y1] do
      for u in [R.x0 / 2:R.x1 / 2] do
        p := put p (sn + u - R.x0 / 2) (v - Lr.y0) (hl.get u v)
    for v in [R.y0 / 2:R.y1 / 2] do
      for u in [Lr.x0:Lr.x1] do
        p := put p (u - Lr.x0) (sv + v - R.y0 / 2) (lh.get u v)
    for v in [R.y0 / 2:R.y1 / 2] do
      for u in [R.x0 / 2:R.x1 / 2] do
        p := put p (sn + u - R.x0 / 2) (sv + v - R.y0 / 2) (hh.get u v)
  return p

/-- The band rectangles implied by the Mallat layout agree with `Tier2.Geometry.bandRect`
(B-15) and the resolution rectangles with `Header.resRect` (B-14). -/
def layoutChecks (cases : Nat) : IO Nat := do
  let mut f := 0
  let mut s : UInt64 := 0xB15
  for _ in [0:cases] do
    let (x0, s1) := below s 300
    let (y0, s2) := below s1 300
    let (w, s3) := below s2 200
    let (h, s4) := below s3 200
    let (nl, s5) := below s4 7
    s := s5
    let tc : Rect := ⟨x0, y0, x0 + w, y0 + h⟩
    for l in [1:nl + 1] do
      let R := halfN tc (l - 1)
      let L := halfN tc l
      let hl := Tier2.Geometry.bandRect tc l .HL
      let lh := Tier2.Geometry.bandRect tc l .LH
      let hh := Tier2.Geometry.bandRect tc l .HH
      let ll := Tier2.Geometry.bandRect tc l .LL
      f := f + (← expect s!"layout tc={repr tc} l={l}"
        (resRect tc nl (nl - l) == L && resRect tc nl (nl - l + 1) == R && ll == L &&
         hl == ⟨R.x0 / 2, L.y0, R.x1 / 2, L.y1⟩ && lh == ⟨L.x0, R.y0 / 2, L.x1, R.y1 / 2⟩ &&
         hh == ⟨R.x0 / 2, R.y0 / 2, R.x1 / 2, R.y1 / 2⟩))
  return f

/-! ## 2-D random checks -/

/-- Plane equality (dimensions and cells). -/
def planeEq (p q : Plane) : Bool := p.width == q.width && p.height == q.height && p.data == q.data

/-- A random plane of `w × h` cells. -/
def randPlane (s : UInt64) (w h bits : Nat) (extremes : Bool) : Plane × UInt64 := Id.run do
  let (xs, s) := randList s (w * h) bits extremes
  let mut p := Plane.zero w h
  for i in [0:w * h] do
    p := (p.set? i (Int32.ofInt (xs.getD i 0))).getD p
  return (p, s)

/-- A random image as a grid on `tc` (row-major array lookup). -/
def gridOf (tc : Rect) (xs : Array Int) : Grid := ⟨fun u v =>
  let w : Int := tc.x1 - tc.x0
  xs.getD ((v - tc.y0) * w + (u - tc.x0)).toNat 0⟩

/-- Random tile-component rectangles: odd/even offsets, tiny shapes. -/
def randRect (s : UInt64) : Rect × UInt64 :=
  let (x0, s) := below s 12
  let (y0, s) := below s 12
  let (kind, s) := below s 6
  let (w, s) := below s 24
  let (h, s) := below s 24
  let (w, h) := match kind with
    | 0 => (1, 1)
    | 1 => (1, h + 1)
    | 2 => (w + 1, 1)
    | _ => (w, h)
  (⟨x0, y0, x0 + w, y0 + h⟩, s)

/-- 2-D checks (a), (b), (c) of the module doc. -/
def random2d (cases : Nat) : IO Nat := do
  let mut f := 0
  let mut s : UInt64 := 0x2D53
  let mut refusals := 0
  for c in [0:cases] do
    let (tc, s1) := randRect s
    let (nl, s2) := below s1 6
    s := s2
    let w := tc.x1 - tc.x0
    let h := tc.y1 - tc.y0
    let nm := s!"tc=({tc.x0},{tc.y0},{tc.x1},{tc.y1}) nl={nl}"
    -- (a) forward spec → Mallat plane → idwt53 = image.
    let (xs, s3) := randList s (w * h) 12 false
    s := s3
    let img := gridOf tc xs.toArray
    let d := sdMulti (JPEG2000.DWT53.specRect tc) nl img
    let p := fromDec d tc nl
    match idwt53 p tc nl, idwt53Fast p tc nl with
    | .ok q, some _ =>
      let ok := (List.range (w * h)).all fun i =>
        (q.get? i).map (·.toInt) == some (xs.getD i 0)
      f := f + (← expect s!"(a) roundtrip {nm}" ok)
    | _, _ => f := f + (← expect s!"(a) fast path refused {nm}" false)
    -- (b) random Mallat plane: fast = spec.
    let (p, s4) := randPlane s w h 20 false
    s := s4
    match idwt53Fast p tc nl with
    | some q => f := f + (← expect s!"(b) fast = spec {nm}" (planeEq q (idwt53Spec p tc nl)))
    | none => f := f + (← expect s!"(b) fast refused {nm}" false)
    -- (c) near-overflow planes: idwt53 = spec, whichever path is taken.
    if c % 4 == 0 then
      let (p, s5) := randPlane s w h 30 true
      s := s5
      if (idwt53Fast p tc nl).isNone then refusals := refusals + 1
      match idwt53 p tc nl with
      | .ok q => f := f + (← expect s!"(c) idwt53 = spec {nm}" (planeEq q (idwt53Spec p tc nl)))
      | .error _ => f := f + (← expect s!"(c) error {nm}" false)
  f := f + (← expect s!"(c) some fast-path refusals exercised ({refusals})" (refusals > 0))
  -- Wrong plane size is an error.
  let bad := idwt53 (Plane.zero 3 3) ⟨0, 0, 4, 3⟩ 1
  f := f + (← expect "size mismatch" (match bad with | .error _ => true | .ok _ => false))
  return f

/-- Reads a case count from the environment, with a default. -/
def envNat (name : String) (dflt : Nat) : IO Nat := do
  match (← IO.getEnv name) with
  | some v => return v.toNat?.getD dflt
  | none => return dflt

/-- Runs the suite; returns the number of failures. -/
def run : IO Nat := do
  let n1 ← envNat "JPEG2000_DWT53_CASES1D" 400
  let n2 ← envNat "JPEG2000_DWT53_CASES2D" 120
  let mut f := 0
  f := f + (← handChecks)
  f := f + (← random1d n1)
  f := f + (← layoutChecks 300)
  f := f + (← random2d n2)
  return f

end JPEG2000.Tests.DWT53
