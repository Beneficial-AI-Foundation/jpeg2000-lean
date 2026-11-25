import JPEG2000.Tier1.Decode
import JPEG2000.Tier1.Modes
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
5. **Every code-block style (task 3.4b).** The style flags, `isRawPass` and `segmentPasses`
   of `JPEG2000.Tier1.Modes` = the spec's (all 64 styles); the raw bit reader = `Spec.Tier1.rawBit`
   on random byte strings full of `0xFF` and markers; random blocks in all 64 styles (block
   `k` has style `k mod 64`) are coded by the all-mode test encoder
   (`Tests.Tier1Spec.encodeBlock` + `buildSegments`, all passes and truncated pass counts),
   the codeword segments are placed at random offsets of one buffer with random bytes between
   them (as Tier-2 delivers them), and `decodeCodeBlockSegs` must give the same values,
   significance and `lsbPlane` as `Spec.Tier1.decodeCodeBlock`; every eighth block has one
   segment byte corrupted (both decoders see the same bytes; this drives bad segmentation
   symbols and raw markers), and the strict variants must agree on acceptance. Argument
   checks of the segment interface.

Environment: `JPEG2000_TIER1FAST_BLOCKS` (random blocks, default 400),
`JPEG2000_TIER1FAST_REPS` (throughput repetitions, default 100),
`JPEG2000_TIER1FAST_MODE_BLOCKS` (random all-style blocks, default 320).
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

/-! ## 5. Every code-block style (task 3.4b) -/

/-- The spec mode and the fast style of style byte `st` have the same six flags. -/
def sameFlags (st : Nat) : Bool :=
  let m := Spec.Tier1.Mode.ofStyle st
  let s := Tier1.Style.ofByte st.toUInt8
  m.bypass == s.bypass && m.reset == s.reset && m.termAll == s.termAll &&
    m.vertCausal == s.vertCausal && m.predTerm == s.predTerm && m.segSymbols == s.segSymbols

/-- Mode-structure checks: flags, raw passes, segment structure, plain dispatch condition, and
the raw bit reader against the spec. -/
def runModeStructure : IO Nat := do
  let mut f := 0
  let styles := List.range 64
  f := f + (← expect "Style.ofByte = Mode.ofStyle (64 styles)" (styles.all sameFlags))
  f := f + (← expect "isRawPass = spec (64 styles, passes < 100)"
    (styles.all fun st => (List.range 100).all fun i =>
      Tier1.isRawPass (Tier1.Style.ofByte st.toUInt8) i ==
        Spec.Tier1.isRawPass (Spec.Tier1.Mode.ofStyle st) i))
  f := f + (← expect "segmentPasses = spec (64 styles, n ≤ 60, first ≤ 40)"
    (styles.all fun st => (List.range 61).all fun n => (List.range 41).all fun i =>
      Tier1.segmentPasses (Tier1.Style.ofByte st.toUInt8) n i ==
        Spec.Tier1.segmentPasses (Spec.Tier1.Mode.ofStyle st) n i))
  f := f + (← expect "decodesAsPlain exactly for styles 0 and 16"
    (styles.all fun st => (Tier1.Style.ofByte st.toUInt8).decodesAsPlain == (st == 0 || st == 16)))
  -- raw bit reader: random byte strings rich in 0xFF and markers, read past the end
  let mut s : UInt64 := 0x5EED_3B
  let mut bad := 0
  for _ in [0:300] do
    let (len, s1) := below s 12
    let (pre, s2) := below s1 3
    let mut s3 := s2
    let mut bytes : Array UInt8 := #[]
    for _ in [0:len] do
      let (sel, t1) := below s3 4
      let (v, t2) := below t1 256
      s3 := t2
      bytes := bytes.push (if sel == 0 then 0xFF else if sel == 1 then (0x80 + v % 32).toUInt8 else v.toUInt8)
    s := s3
    let nbits := 8 * len + 20
    let want := (Spec.Tier1.rawBits (Spec.Tier1.RawState.init bytes.toList) nbits).1
    -- the segment sits at offset `pre` of a buffer with junk around it
    let buf : ByteArray := ⟨(Array.replicate pre (0x55 : UInt8)) ++ bytes ++ #[0x00, 0x12]⟩
    let d0 := Tier1.rawInit buf pre (pre + len) (ByteArray.mk #[])
    let (got, _) := (List.range nbits).foldl (fun (acc, d) _ =>
      let (b, d) := Tier1.rawBit d
      (acc.push b, d)) ((#[] : Array Bool), d0)
    if got.toList != want then bad := bad + 1
  f := f + (← expect s!"raw bit reader = Spec.Tier1.rawBit ({bad}/300 strings differ)" (bad == 0))
  return f

/-- Lay the segments out in one buffer: random prefix, then each segment followed by 0–3
random bytes; the `Seg` ranges and the buffer. -/
def layout (segs : List Spec.Tier1.Segment) (s : UInt64) : ByteArray × Array Tier1.Seg × UInt64 :=
  Id.run do
    let (pl, s) := below s 5
    let (pre, s) := randBytes s pl
    let mut s := s
    let mut buf := pre
    let mut out : Array Tier1.Seg := #[]
    for sg in segs do
      let start := buf.size
      buf := buf ++ ⟨sg.data.toArray⟩
      out := out.push { start, stop := buf.size, passes := sg.passes }
      let (gl, s1) := below s 4
      let (gap, s2) := randBytes s1 gl
      s := s2
      buf := buf ++ gap
    return (buf, out, s)

/-- Flip one random byte of one random non-empty segment (by XOR with a random non-zero
byte). -/
def corrupt (segs : List Spec.Tier1.Segment) (s : UInt64) : List Spec.Tier1.Segment × UInt64 :=
  let nonEmpty := (List.range segs.length).filter fun j => (segs.getD j default).data.length > 0
  if nonEmpty.isEmpty then (segs, s) else
  let (k, s) := below s nonEmpty.length
  let j := nonEmpty.getD k 0
  let sg := segs.getD j default
  let (pos, s) := below s sg.data.length
  let (x, s) := below s 255
  let data := sg.data.set pos (sg.data.getD pos 0 ^^^ (x + 1).toUInt8)
  (segs.set j { sg with data }, s)

/-- Outcome counters of the all-style checks. -/
structure ModeStats where
  /-- Checks run. -/
  checks : Nat := 0
  /-- Failed checks. -/
  fails : Nat := 0
  /-- Segments decoded. -/
  segs : Nat := 0
  /-- Raw segments. -/
  rawSegs : Nat := 0
  /-- Corrupted checks where the spec's strict decoder rejected a bad segmentation symbol. -/
  badSym : Nat := 0
  /-- Coefficients compared. -/
  coeffs : Nat := 0

/-- Encode the first `n` passes of `b` in style `st` (optionally corrupt one byte), decode with
both decoders from the same bytes; `none` if they agree. Also returns (segments, raw
segments, strict rejection). -/
def checkModeBlk (st : Nat) (b : Blk) (n : Nat) (bad : Bool) (s : UInt64) :
    Option String × Nat × Nat × Bool :=
  let m := Spec.Tier1.Mode.ofStyle st
  let (_, passes) := Tests.Tier1Spec.encodeBlock m b n
  let segs := Tests.Tier1Spec.buildSegments m passes
  let (segs, s) := if bad then corrupt segs s else (segs, s)
  let (buf, fsegs, _) := layout segs s
  let rawN := ((List.range segs.length).filter fun j =>
    Spec.Tier1.isRawPass m ((segs.take j).map (·.passes)).sum).length
  let cb : Spec.Tier1.CodeBlock := {
    width := b.w, height := b.h, orient := b.orient, mode := m, numBitPlanes := b.K + b.zbp,
    zeroBitPlanes := b.zbp, segments := segs }
  let fast := Tier1.decodeCodeBlockSegs buf fsegs b.w b.h (bandOf b.orient) st.toUInt8
    (b.K + b.zbp) b.zbp
  let fastStrict := (err? (Tier1.decodeCodeBlockSegsStrict buf fsegs b.w b.h (bandOf b.orient)
    st.toUInt8 (b.K + b.zbp) b.zbp)).isSome
  let specStrict := (err? (Spec.Tier1.decodeCodeBlockStrict cb)).isSome
  let tag := s!"style {st} {b.w}x{b.h} {repr b.orient} K={b.K} passes {n}/{3 * b.K - 2}{if bad then " corrupted" else ""}"
  let res : Option String :=
    match Spec.Tier1.decodeCodeBlock cb, fast with
    | .error e1, _ => some s!"{tag}: spec error {repr e1}"
    | _, .error e2 => some s!"{tag}: fast error {repr e2}"
    | .ok cs, .ok o =>
      let badIdx := (List.range (b.w * b.h)).filter fun i =>
        let c := cs.getD i {}
        let x := i % b.w
        let y := i / b.w
        let v := (o.plane.get? i).map Int32.toInt
        !(v == some c.value && o.sig x y == c.sig && o.lsbPlane x y == c.lsbPlane)
      if !badIdx.isEmpty || cs.size != b.w * b.h || o.plane.width != b.w ||
          o.plane.height != b.h then
        some s!"{tag}: {badIdx.length} bad coefficients (first {badIdx.head?})"
      else if fastStrict != specStrict then
        some s!"{tag}: strict decoders disagree (fast rejects: {fastStrict}, spec rejects: {specStrict})"
      else if !bad && specStrict then some s!"{tag}: clean segments rejected by the strict spec"
      else none
  (res, segs.length, rawN, specStrict)

/-- Random all-style checks; returns the number of failures. -/
def runModesRandom : IO Nat := do
  let n ← envNat "JPEG2000_TIER1FAST_MODE_BLOCKS" 320
  let mut s : UInt64 := 0x3_4B_2026
  let mut stt : ModeStats := {}
  let t0 ← IO.monoMsNow
  for k in [0:n] do
    let st := k % 64
    let (b, s1) := genBlk s (k % 97 == 50)
    let total := 3 * b.K - 2
    let (t1, s2) := below s1 total
    let (t2, s3) := below s2 total
    s := s3
    for np in [total, t1 + 1, t2] do
      let bad := k % 8 == 7 && np > 0
      let (_, s4) := Tests.Tier1Spec.splitmix s
      s := s4
      let (r, ns, nr, rej) := checkModeBlk st b np bad s
      stt := { stt with
        checks := stt.checks + 1, segs := stt.segs + ns, rawSegs := stt.rawSegs + nr,
        badSym := stt.badSym + (if bad && rej then 1 else 0), coeffs := stt.coeffs + b.w * b.h }
      if let some msg := r then
        stt := { stt with fails := stt.fails + 1 }
        if stt.fails ≤ 5 then IO.eprintln s!"  mismatch: {msg}"
  let t1 ← IO.monoMsNow
  IO.println s!"  tier1 fast = spec, 64 styles: {stt.checks - stt.fails}/{stt.checks} ok ({n} blocks, {stt.coeffs} coefficients, {stt.segs} segments, {stt.rawSegs} raw, {stt.badSym} corrupted blocks rejected by strict, {t1 - t0} ms)"
  let mut f ← expect s!"random blocks, all styles: fast = spec ({stt.fails} failures)" (stt.fails == 0)
  f := f + (← expect "raw segments were exercised" (stt.rawSegs > 0))
  f := f + (← expect "bad segmentation symbols were exercised" (stt.badSym > 0))
  return f

/-- Hand-made vertically causal case: a 1×8 block (two stripes), only row 4 significant in
the first cleanup pass. Without vertically causal formation row 3 sees it as its south
neighbour in the next significance propagation pass; with it, row 3 does not — the flag word
of row 3 must not carry `SIG_S`. -/
def runCausalUnit : IO Nat := do
  let b : Blk := { w := 1, h := 8, orient := .LL, K := 2, zbp := 0,
                   mags := #[0, 0, 0, 1, 2, 0, 0, 0], negs := Array.replicate 8 false }
  let mut f := 0
  for st in [0, 8] do
    let m := Spec.Tier1.Mode.ofStyle st
    let segs := Tests.Tier1Spec.buildSegments m (Tests.Tier1Spec.encodeBlock m b 4).2
    let (buf, fsegs, _) := layout segs 7
    let spec := Spec.Tier1.decodeValues
      { width := 1, height := 8, orient := .LL, mode := m, numBitPlanes := 2, zeroBitPlanes := 0,
        segments := segs }
    match spec, Tier1.decodeCodeBlockSegs buf fsegs 1 8 .LL st.toUInt8 2 0 with
    | .ok vs, .ok o =>
      let got := (List.range 8).map fun i => ((o.plane.get? i).map Int32.toInt).getD 99
      let row3 := Tier1.fget o.flags (4 * 3 + 1)
      f := f + (← expect s!"causal unit, style {st}: values {got} = spec {vs.toList} = original"
        (got == vs.toList && got == [0, 0, 0, 1, 2, 0, 0, 0]))
      f := f + (← expect s!"causal unit, style {st}: row 3 flag SIG_S {st == 0}"
        ((row3 &&& Tier1.SIG_S != 0) == (st == 0)))
    | _, _ => f := f + (← expect s!"causal unit, style {st}: both decode" false)
  return f

/-- Argument checks of the segment interface. -/
def runSegChecks : IO Nat := do
  let mut f := 0
  let buf : ByteArray := ⟨#[1, 2, 3, 4, 5, 6]⟩
  let dec (segs : Array Tier1.Seg) (st : UInt8) :=
    err? (Tier1.decodeCodeBlockSegs buf segs 4 4 .LL st 3 0)
  f := f + (← expect "termall: one segment of 3 passes rejected" ((dec #[⟨0, 3, 3⟩] 4).isSome))
  f := f + (← expect "termall: three segments of 1 pass accepted"
    ((dec #[⟨0, 2, 1⟩, ⟨2, 4, 1⟩, ⟨4, 6, 1⟩] 4).isNone))
  f := f + (← expect "plain: two segments rejected" ((dec #[⟨0, 2, 1⟩, ⟨2, 4, 1⟩] 0).isSome))
  f := f + (← expect "plain: no segment accepted (zeros)" ((dec #[] 0).isNone))
  f := f + (← expect "segment with 0 passes rejected" ((dec #[⟨0, 2, 0⟩] 2).isSome))
  f := f + (← expect "segment past the buffer rejected" ((dec #[⟨0, 7, 2⟩] 2).isSome))
  f := f + (← expect "segment start > stop rejected" ((dec #[⟨3, 2, 2⟩] 2).isSome))
  f := f + (← expect "segment past the buffer rejected (termall, last segment)"
    ((dec #[⟨0, 2, 1⟩, ⟨2, 9, 1⟩] 4).isSome))
  f := f + (← expect "too many passes rejected (K = 3: 7 passes max)" ((dec #[⟨0, 6, 8⟩] 2).isSome))
  f := f + (← expect "K = 32 with passes unsupported"
    (match err? (Tier1.decodeCodeBlockSegs buf #[⟨0, 6, 1⟩] 4 4 .LL 2 32 0) with
     | some (.unsupported _ _) => true | _ => false))
  -- plain dispatch: style 0 and 16 give exactly `decodeCodeBlock`'s output
  let (mags, negs, _) := genMags 0x77 (16 * 16) 9
  let b : Blk := { w := 16, h := 16, orient := .HL, K := 9, zbp := 1, mags, negs }
  let code := Encode.MQ.encodeAll Spec.Tier1.initialStates (plainTrace b 20)
  let cbuf : ByteArray := ⟨#[9, 9] ++ code.toArray ++ #[7]⟩
  let ref := Tier1.decodeCodeBlock cbuf 2 (2 + code.length) 16 16 .HL 10 1 20
  for st in [0, 16] do
    let got := Tier1.decodeCodeBlockSegs cbuf #[⟨2, 2 + code.length, 20⟩] 16 16 .HL st 10 1
    f := f + (← expect s!"style {st} dispatches to the plain decodeCodeBlock"
      (match ref, got with
       | .ok a, .ok b => a.plane.data == b.plane.data && a.flags == b.flags &&
           a.numPasses == b.numPasses && a.codedPlanes == b.codedPlanes
       | _, _ => false))
  return f

/-- Runs the suite; returns the number of failures. -/
def run : IO Nat := do
  let mut f ← runLuts
  f := f + (← runChecks)
  f := f + (← runRandom)
  runBench
  f := f + (← runModeStructure)
  f := f + (← runCausalUnit)
  f := f + (← runSegChecks)
  f := f + (← runModesRandom)
  return f

end JPEG2000.Tests.Tier1Fast
