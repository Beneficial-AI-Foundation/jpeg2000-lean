import JPEG2000.Tier1.Decode
import Spec.Tier1.Decode
import Encode.MQ
import Tests.Tier1Spec

/-!
# Tests: fast Tier-1 decoder, plain mode (task 3.4a)

Plan.md §4 (C3), §5.2 "Tier-1 / EBCOT", §6 item 4; T.800 Annex D.

1. **Look-up tables = spec, exhaustively.** For every one of the 256 neighbourhoods of each
   table, a 3 × 3 spec block (`Spec.Tier1.Geom`, `Array Coeff`) is built whose centre has
   exactly the neighbours the flag word describes, and the spec's own context functions
   (`Geom.zcCtx`, `Geom.signContext`, `Geom.mrCtx`, which count neighbours themselves) are
   compared with the fast flag-word look-ups (`zcCtx (zcFor b)`, `scEntry`, `mrCtxOf`) on the
   corresponding flag word — for all four orientations, with and without unrelated bits set.
2. **Fast = spec on random plain-mode blocks.** Blocks (sizes 1×1 … 64×64, plus the
   4096-coefficient shapes 128×32, 32×128, 256×16, 1024×4, 4×1024), all orientations,
   `K = 1 … 16` coded planes, 0–3 zero bit-planes, sparse to dense, are coded with the
   test-only encoder of `Tests.Tier1Spec` (all `3K − 2` passes and random truncated pass
   counts) and decoded by both decoders; the codeword is embedded at a random offset in a
   buffer with random trailing bytes (the fast decoder reads `data[start, stop)` only). Every
   coefficient's value, significance and `lsbPlane` must agree.
3. **Argument checks** agree with the spec's (`validate`), plus the fast decoder's own ones.
4. **Throughput** on dense 64×64 blocks (printed, not checked).

Environment: `JPEG2000_TIER1FAST_BLOCKS` (random blocks, default 400),
`JPEG2000_TIER1FAST_REPS` (throughput repetitions, default 100).
-/

namespace JPEG2000.Tests.Tier1Fast

open JPEG2000 JPEG2000.Bytes
open JPEG2000.Tier2.Geometry (Band)
open JPEG2000.Tests.Tier1Spec (Blk plainTrace below err?)

/-- Runs one named check, printing a line on failure; returns 1 on failure, 0 on success. -/
def expect (name : String) (ok : Bool) : IO Nat := do
  if ok then return 0
  IO.eprintln s!"  FAIL tier1fast: {name}"
  return 1

/-- The spec orientation of a band. -/
def orientOf : Band → Spec.Tier1.Orientation
  | .LL => .LL
  | .HL => .HL
  | .LH => .LH
  | .HH => .HH

/-- All four bands. -/
def bands : List Band := [.LL, .HL, .LH, .HH]

/-! ## 1. Look-up tables against the spec -/

/-- A 3 × 3 spec block whose cells `(x, y)` are given by `cell x y`. -/
def block3 (cell : Nat → Nat → Spec.Tier1.Coeff) : Array Spec.Tier1.Coeff :=
  Array.ofFn (n := 9) fun i => cell (i.val % 3) (i.val / 3)

/-- Is bit `i` of `n` set? -/
def bitSet (n i : Nat) : Bool := n / 2 ^ i % 2 == 1

/-- The neighbourhood position of each flag bit 0–7: N, W, E, S, NW, NE, SW, SE. -/
def nbrPos : List (Nat × Nat) := [(1, 0), (0, 1), (2, 1), (1, 2), (0, 0), (2, 0), (0, 2), (2, 2)]

/-- Spec block: neighbour `k` significant iff bit `k` of `n` (centre insignificant). -/
def zcBlock (n : Nat) : Array Spec.Tier1.Coeff :=
  block3 fun x y =>
    match nbrPos.findIdx? (· == (x, y)) with
    | some k => { sig := bitSet n k }
    | none => {}

/-- Spec block for a sign index: N, W, E, S significant per bits 0–3, negative per 4–7. -/
def scBlock (n : Nat) : Array Spec.Tier1.Coeff :=
  block3 fun x y =>
    match (nbrPos.take 4).findIdx? (· == (x, y)) with
    | some k => { sig := bitSet n k, sign := bitSet n (k + 4) }
    | none => {}

/-- The flag word with sign index `n`: bits 0–3 stay, bits 4–7 move to 8–11. -/
def scFlag (n : Nat) : UInt32 := (n % 16 + n / 16 * 256).toUInt32

/-- Unrelated flag bits (own state) that the look-ups must ignore. -/
def junk : UInt32 := Tier1.SIG ||| Tier1.NEG ||| Tier1.VIS

/-- The LUT checks; returns the number of failures. -/
def runLuts : IO Nat := do
  let mut f := 0
  for b in bands do
    let g : Spec.Tier1.Geom := { width := 3, height := 3, orient := orientOf b }
    let bad := (List.range 256).filter fun n =>
      let want := g.zcCtx (zcBlock n) 1 1
      let fw := n.toUInt32
      Tier1.zcCtx (Tier1.zcFor b) (Tier1.zcFor_size b) fw != want ||
        Tier1.zcCtx (Tier1.zcFor b) (Tier1.zcFor_size b) (fw ||| junk ||| 0xF00) != want ||
        Tier1.zcOf b n != want
    f := f + (← expect s!"zero-coding LUT {repr b} = Table D.1 spec (bad {bad.take 5})" bad.isEmpty)
  let g : Spec.Tier1.Geom := { width := 3, height := 3, orient := .LL }
  let bad := (List.range 256).filter fun n =>
    let (cx, xr) := g.signContext (scBlock n) 1 1
    let want := cx * 2 + (if xr then 1 else 0)
    let fw := scFlag n
    (Tier1.scEntry fw).toNat != want || (Tier1.scEntry (fw ||| junk ||| 0xF0)).toNat != want
  f := f + (← expect s!"sign-coding LUT = Tables D.2/D.3 spec (bad {bad.take 5})" bad.isEmpty)
  -- Table D.4: all 2^8 neighbourhoods × refined
  let bad := (List.range 512).filter fun m =>
    let n := m % 256
    let refd := m / 256 == 1
    let cs := (zcBlock n).set! 4 { sig := true, refined := refd }
    let fw := n.toUInt32 ||| Tier1.SIG ||| (if refd then Tier1.REF else 0)
    Tier1.mrCtxOf fw != g.mrCtx cs 1 1
  f := f + (← expect s!"refinement contexts = Table D.4 spec (bad {bad.take 5})" bad.isEmpty)
  return f

/-! ## 2. Random blocks: fast = spec -/

/-- The 4096-coefficient shapes. -/
def bigShapes : List (Nat × Nat) := [(128, 32), (32, 128), (256, 16), (1024, 4), (4, 1024)]

/-- A side length: mostly small, sometimes up to 64. -/
def genSide (s : UInt64) : Nat × UInt64 :=
  let (sel, s) := below s 10
  if sel < 4 then let (v, s) := below s 8; (v + 1, s)
  else if sel < 7 then let (v, s) := below s 24; (v + 1, s)
  else let (v, s) := below s 64; (v + 1, s)

/-- Random magnitudes and signs for `w · h` coefficients with `K` planes. -/
def genMags (s : UInt64) (n K : Nat) : Array Nat × Array Bool × UInt64 := Id.run do
  let (density, s) := below s 6
  let (topBits, s) := below s K
  let mut s := s
  let mut mags : Array Nat := Array.mkEmpty n
  let mut negs : Array Bool := Array.mkEmpty n
  for _ in [0:n] do
    let (r, s1) := below s 8
    let (big, s2) := below s1 16
    let bits := if big == 0 then K else topBits + 1
    let (m, s3) := below s2 (2 ^ bits)
    let (ng, s4) := below s3 2
    s := s4
    mags := mags.push (if r < density + 2 then m else 0)
    negs := negs.push (ng == 1)
  return (mags, negs, s)

/-- A random block; `big` selects one of the 4096-coefficient shapes. -/
def genBlk (s : UInt64) (big : Bool) : Blk × UInt64 :=
  let (w, h, s) :=
    if big then
      let (k, s) := below s bigShapes.length
      let (w, h) := bigShapes.getD k (64, 64)
      (w, h, s)
    else
      let (w, s) := genSide s
      let (h, s) := genSide s
      (w, if w * h > 4096 then 4096 / w else h, s)
  let (oi, s) := below s 4
  let (K, s) := below s 16
  let K := K + 1
  let (zbp, s) := below s 4
  let (mags, negs, s) := genMags s (w * h) K
  ({ w, h, orient := Spec.Tier1.Orientation.all.getD oi .LL, K, zbp, mags, negs }, s)

/-- The band of a spec orientation. -/
def bandOf : Spec.Tier1.Orientation → Band
  | .LL => .LL
  | .HL => .HL
  | .LH => .LH
  | .HH => .HH

/-- Random bytes (with plenty of `0xFF`). -/
def randBytes (s : UInt64) (n : Nat) : ByteArray × UInt64 := Id.run do
  let mut s := s
  let mut out := ByteArray.empty
  for _ in [0:n] do
    let (v, s1) := below s 512
    s := s1
    out := out.push (if v ≥ 256 then 0xFF else v.toUInt8)
  return (out, s)

/-- The spec code-block of `b` with `n` passes and codeword `data`. -/
def specBlock (b : Blk) (n : Nat) (data : List UInt8) : Spec.Tier1.CodeBlock :=
  { width := b.w, height := b.h, orient := b.orient, numBitPlanes := b.K + b.zbp,
    zeroBitPlanes := b.zbp, segments := Spec.Tier1.Segment.single n data }

/-- Encode the first `n` passes of `b`, decode with both decoders (the fast one on the
codeword embedded at offset `pre` before `post` random bytes); `none` if they agree. -/
def checkBlk (b : Blk) (n : Nat) (s : UInt64) : Option String :=
  let code := Encode.MQ.encodeAll Spec.Tier1.initialStates (plainTrace b n)
  let (pl, s) := below s 4
  let (ql, s) := below s 4
  let (pre, s) := randBytes s pl
  let (post, _) := randBytes s ql
  let buf := pre ++ ⟨code.toArray⟩ ++ post
  let fast := Tier1.decodeCodeBlock buf pl (pl + code.length) b.w b.h (bandOf b.orient)
    (b.K + b.zbp) b.zbp n
  match Spec.Tier1.decodeCodeBlock (specBlock b n code), fast with
  | .error e1, _ => some s!"spec error {repr e1}"
  | _, .error e2 => some s!"fast error {repr e2}"
  | .ok cs, .ok o =>
    let bad := (List.range (b.w * b.h)).filter fun i =>
      let c := cs.getD i {}
      let x := i % b.w
      let y := i / b.w
      let v := (o.plane.get? i).map Int32.toInt
      !(v == some c.value && o.sig x y == c.sig && o.lsbPlane x y == c.lsbPlane)
    if bad.isEmpty && cs.size == b.w * b.h && o.plane.width == b.w && o.plane.height == b.h then
      none
    else
      some s!"{b.w}x{b.h} {repr b.orient} K={b.K} passes {n}/{3 * b.K - 2}: {bad.length} bad coefficients (first {bad.head?})"

/-- Number from an environment variable, or a default. -/
def envNat (name : String) (dflt : Nat) : IO Nat := do
  match ← IO.getEnv name with
  | some v => return v.trimAscii.toString.toNat?.getD dflt
  | none => return dflt

/-- Random fast-vs-spec checks; returns the number of failures. -/
def runRandom : IO Nat := do
  let n ← envNat "JPEG2000_TIER1FAST_BLOCKS" 400
  let mut s : UInt64 := 0x3_4A_2026
  let mut fails := 0
  let mut checks := 0
  let mut coeffs := 0
  let t0 ← IO.monoMsNow
  for k in [0:n] do
    let (b, s1) := genBlk s (k % 25 == 0)
    let total := 3 * b.K - 2
    let (t1, s2) := below s1 total
    let (t2, s3) := below s2 total
    s := s3
    for np in [total, t1 + 1, t2] do
      checks := checks + 1
      coeffs := coeffs + b.w * b.h
      let (_, s4) := splitmixStep s
      s := s4
      match checkBlk b np s with
      | none => pure ()
      | some msg =>
        fails := fails + 1
        if fails ≤ 5 then IO.eprintln s!"  mismatch: {msg}"
  let t1 ← IO.monoMsNow
  IO.println s!"  tier1 fast = spec: {checks - fails}/{checks} ok ({n} blocks, {coeffs} coefficients, {t1 - t0} ms)"
  expect s!"random blocks: fast = spec ({fails} failures)" (fails == 0)
where
  /-- Advance the generator. -/
  splitmixStep (s : UInt64) : UInt64 × UInt64 := JPEG2000.Tests.Tier1Spec.splitmix s

/-! ## 3. Argument checks -/

/-- Fast-decoder argument checks, compared with the spec's where both apply. -/
def runChecks : IO Nat := do
  let mut f := 0
  let buf : ByteArray := ⟨#[1, 2, 3]⟩
  let fast (w h Mb zbp n : Nat) := Tier1.decodeCodeBlock buf 0 3 w h .LL Mb zbp n
  let spec (w h Mb zbp n : Nat) : Spec.Tier1.CodeBlock :=
    { width := w, height := h, orient := .LL, numBitPlanes := Mb, zeroBitPlanes := zbp,
      segments := Spec.Tier1.Segment.single n [1, 2, 3] }
  let cases : List (Nat × Nat × Nat × Nat × Nat) :=
    [(4, 4, 3, 1, 4), (4, 4, 3, 1, 5), (4, 4, 3, 3, 1), (4, 4, 3, 5, 0), (1025, 1, 3, 1, 1),
     (64, 65, 3, 1, 1), (1024, 4, 3, 1, 1), (0, 7, 3, 1, 4), (7, 0, 3, 1, 4), (1, 1, 31, 0, 91)]
  for (w, h, mb, zbp, n) in cases do
    let a := (err? (fast w h mb zbp n)).isSome
    let b := (err? (Spec.Tier1.decodeCodeBlock (spec w h mb zbp n))).isSome
    f := f + (← expect s!"validation agrees on {w}x{h} Mb={mb} zbp={zbp} passes={n}" (a == b))
  f := f + (← expect "K = 32 with passes unsupported"
    (match err? (fast 4 4 32 0 1) with | some (.unsupported _ _) => true | _ => false))
  f := f + (← expect "K = 32 without passes: zeros"
    ((err? (fast 4 4 32 0 0)).isNone))
  f := f + (← expect "range past the buffer rejected"
    ((err? (Tier1.decodeCodeBlock buf 0 4 4 4 .LL 3 1 1)).isSome))
  f := f + (← expect "start > stop rejected"
    ((err? (Tier1.decodeCodeBlock buf 2 1 4 4 .LL 3 1 1)).isSome))
  return f

/-! ## 4. Throughput -/

/-- Decode `reps` times a set of dense 64×64 blocks with `K = 12` (all passes); print
coefficients and MQ decisions per second. -/
def runBench : IO Unit := do
  let reps ← envNat "JPEG2000_TIER1FAST_REPS" 100
  let mut s : UInt64 := 0xBE_7C_4A
  let mut blocks : Array (Band × ByteArray × Nat) := #[]
  for k in [0:4] do
    let (mags, negs, s1) := genMags s (64 * 64) 12
    s := s1
    let b : Blk := { w := 64, h := 64, orient := Spec.Tier1.Orientation.all.getD k .LL, K := 12,
                     zbp := 0, mags, negs }
    let tr := plainTrace b (3 * 12 - 2)
    let code := Encode.MQ.encodeAll Spec.Tier1.initialStates tr
    blocks := blocks.push (bandOf b.orient, ⟨code.toArray⟩, tr.length)
  let t0 ← IO.monoNanosNow
  let mut acc : Int := 0
  let mut decisions := 0
  for r in [0:reps] do
    let (band, data, nd) := blocks[r % blocks.size]!
    decisions := decisions + nd
    match Tier1.decodeCodeBlock data 0 data.size 64 64 band 12 0 34 with
    | .ok o => acc := acc + ((o.plane.get? (r % 4096)).map Int32.toInt).getD 0
    | .error _ => pure ()
  let t1 ← IO.monoNanosNow
  let ns := max 1 (t1 - t0)
  let cf := reps * 4096
  IO.println s!"  tier1 fast throughput: {cf * 1000000000 / ns} coefficients/s, {decisions * 1000000000 / ns} MQ decisions/s ({reps} blocks of 64x64, K = 12, {ns / 1000000} ms, checksum {acc})"

/-- Runs the suite; returns the number of failures. -/
def run : IO Nat := do
  let mut f ← runLuts
  f := f + (← runChecks)
  f := f + (← runRandom)
  runBench
  return f

end JPEG2000.Tests.Tier1Fast
