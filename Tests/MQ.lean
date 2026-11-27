import JPEG2000.MQ
import Spec.MQ

/-!
# Unit tests: fast MQ decoder (task 2.3)

Plan.md §4 (C2), §5.2 "MQ decoder", §6; T.800 Annex C (C.3.1–C.3.5, Table C.2), D.7.

1. Known answer: the ITU-T T.88 Annex H.2 test sequence.
2. Differential against the flowchart spec `JPEG2000.Spec.MQ`: thousands of deterministic
   pseudo-random segments (uniform, `0xFF`-heavy, `0xFF` followed by bytes `> 0x8F`, empty,
   length 1, segments inside a larger buffer) and context sequences over the 19 Tier-1
   contexts (plus a few out-of-range ones), comparing every decision, every register
   (`C`, `A`, `CT`, `BP`) and every context state in lockstep.
3. A throughput measurement on a 1 MB random segment without markers (printed, never
   fails): the UNIFORM context (about one bit per decision) and the 19 contexts cyclically.
-/

namespace JPEG2000.Tests.MQ

open JPEG2000

/-- Runs one named check, printing a line on failure; returns 1 on failure, 0 on success. -/
def expect (name : String) (ok : Bool) : IO Nat := do
  if ok then return 0
  IO.eprintln s!"  FAIL mq: {name}"
  return 1

/-- A deterministic linear congruential generator (state → next state). -/
def lcg (x : Nat) : Nat := (x * 1103515245 + 12345) % 2147483648

/-- `n` pseudo-random values below `m` from seed `seed`, and the final seed. -/
def randoms (seed n m : Nat) : List Nat × Nat :=
  let (xs, s) := (List.range n).foldl (fun (acc : List Nat × Nat) _ =>
    let x := lcg acc.2; (x / 65536 % m :: acc.1, x)) ([], seed)
  (xs.reverse, s)

/-- Pseudo-random segment of `n` bytes in byte-distribution `mode`:
0 uniform; 1 half `0xFF`; 2 `0xFF` pairs followed by `0x90…0xFF`, mixed with stuffing
(`0xFF 0x00…0x8F`); 3 only `0x00`/`0xFF`/`0x7F`/`0x80`/`0x8F`/`0x90`. -/
def genBytes (mode seed n : Nat) : List UInt8 × Nat :=
  let (xs, s) := randoms seed (2 * n) 65536
  let rec go : List Nat → List UInt8
    | x :: y :: rest =>
      let b : Nat :=
        match mode with
        | 0 => x % 256
        | 1 => if x % 2 = 0 then 0xFF else y % 256
        | 2 => if x % 3 = 0 then 0xFF else if x % 3 = 1 then 0x90 + y % 0x70 else y % 0x90
        | _ => [0x00, 0xFF, 0x7F, 0x80, 0x8F, 0x90].getD (x % 6) 0
      b.toUInt8 :: go rest
    | _ => []
  (go xs, s)

/-- Pseudo-random context sequence of length `n` over the 19 Tier-1 contexts in `mode`:
0 uniform; 1 skewed to a few contexts (so states adapt deep into Table C.2); 2 with
occasional out-of-range contexts (19, 31). -/
def genCxs (mode seed n : Nat) : List Nat × Nat :=
  let (xs, s) := randoms seed n 1000
  (xs.map fun x =>
    match mode with
    | 0 => x % 19
    | 1 => if x < 700 then x % 3 else x % 19
    | _ => if x < 30 then 19 + (x % 2) * 12 else x % 19, s)

/-- Lockstep comparison of the fast decoder (segment `buf[start, start + seg.length)`) with
`Spec.MQ` (on `seg`) for the context list `cxs`: every decision, register and context. -/
def lockstep (buf : ByteArray) (start : Nat) (seg : List UInt8) (inits : List Nat)
    (cxs : List Nat) : Bool :=
  let agree (d : MQ.Dec) (s : Spec.MQ.State) (sc : Spec.MQ.Contexts) : Bool :=
    d.c.toNat == s.C && d.a.toNat == s.A && d.ct.toNat == s.CT && d.pos - start == s.pos &&
      d.pos ≥ start && d.cx.size == sc.length &&
      (List.range sc.length).all fun k =>
        let b := (MQ.ctxGet d.cx k).toNat
        let st := Spec.MQ.Contexts.get sc k
        b / 2 == st.index && (b % 2 == 1) == st.mps
  let d0 := MQ.Dec.init buf start (start + seg.length) (MQ.initContexts inits)
  let s0 := Spec.MQ.initdec seg
  let c0 := Spec.MQ.initContexts inits
  (cxs.foldl (fun (acc : Bool × MQ.Dec × Spec.MQ.State × Spec.MQ.Contexts) cx =>
    let (ok, d, s, sc) := acc
    if !ok then acc else
    let (b, d) := d.decode cx
    let (b', s, sc) := Spec.MQ.decode s sc cx
    (b == b' && agree d s sc, d, s, sc)) (agree d0 s0 c0, d0, s0, c0)).1

/-- Tail-recursive decode loop for the throughput test (contexts cycle through `0 … 18`, or
stay on the UNIFORM context 18 when `uniform`): decode until `fuel` runs out or the
segment is exhausted; returns the number of decisions, the number of `1` decisions and
the final byte pointer. -/
def benchLoop (uniform : Bool) (stop : Nat) : Nat → MQ.Dec → UInt32 → Nat → Nat → Nat × Nat × Nat
  | 0, d, _, n, ones => (n, ones, d.pos)
  | fuel + 1, d, k, n, ones =>
    if d.pos ≥ stop then (n, ones, d.pos) else
    let (b, d) := d.decode k.toNat
    let k := if uniform then 18 else if k == 18 then 0 else k + 1
    benchLoop uniform stop fuel d k (n + 1) (if b then ones + 1 else ones)

/-- Runs the suite; returns the number of failures. -/
def run : IO Nat := do
  let mut f := 0
  -- (1) Known answer: T.88 H.2.
  let t88 : ByteArray := ⟨Spec.MQ.t88Encoded.toArray⟩
  f := f + (← expect "T.88 H.2 decodes to the reference data"
    (MQ.decodeAll t88 [0] (List.replicate 256 0) == Spec.MQ.bitsOf Spec.MQ.t88Data))
  f := f + (← expect "T.88 H.2 lockstep with the spec"
    (lockstep t88 0 Spec.MQ.t88Encoded [0] (List.replicate 256 0)))
  -- Tier-1 initial contexts (T.800 D.7).
  f := f + (← expect "tier1Contexts packs D.7 states"
    (MQ.tier1Contexts.toList == [8] ++ List.replicate 16 0 ++ [6, 92]))
  -- Fixed edge cases.
  let edge : List (List UInt8) :=
    [[], [0x00], [0xFF], [0x7F], [0xFF, 0xFF], [0xFF, 0x8F], [0xFF, 0x90], [0xFF, 0x00],
     [0xFF, 0x7F, 0xFF, 0x7F], [0x00, 0x00, 0x00], List.replicate 8 0xFF,
     [0xFF, 0xD9], [0x12, 0xFF, 0x91, 0x34]]
  let mut edgeFail := 0
  let mut seed := 12345
  for seg in edge do
    for mode in [0, 1, 2] do
      let (cxs, s) := genCxs mode seed 300
      seed := s
      unless lockstep ⟨seg.toArray⟩ 0 seg MQ.tier1Inits cxs do
        edgeFail := edgeFail + 1
  f := f + (← expect s!"edge segments lockstep ({edgeFail} mismatches)" (edgeFail == 0))
  -- (2) Differential: random segments and context sequences.
  let mut cases := 0
  let mut fails := 0
  for i in [0:3000] do
    let mode := i % 4
    let len := if i % 50 = 0 then 0 else if i % 50 = 1 then 1 else (lcg (i + 7)) / 65536 % 80
    let (seg, s) := genBytes mode seed len
    let (cxs, s) := genCxs (i % 3) s (50 + s / 65536 % 400)
    seed := s
    -- Every 5th case: the segment sits inside a larger buffer (junk before and after).
    let (buf, start) :=
      if i % 5 = 0 then
        let (pre, _) := genBytes 1 (s + 1) 7
        let (post, _) := genBytes 0 (s + 2) 5
        ((⟨(pre ++ seg ++ post).toArray⟩ : ByteArray), pre.length)
      else ((⟨seg.toArray⟩ : ByteArray), 0)
    cases := cases + 1
    unless lockstep buf start seg MQ.tier1Inits cxs do
      fails := fails + 1
      if fails ≤ 5 then IO.eprintln s!"  mismatch: case {i} mode {mode} len {len}"
  f := f + (← expect s!"differential vs Spec.MQ ({fails}/{cases} mismatches)" (fails == 0))
  -- (3) Throughput on a 1 MB random segment (print only).
  let mb := 1 <<< 20
  let (bytes, _) := genBytes 0 99 mb
  -- No `0xFF` bytes, so the decoder never meets a marker and reads the whole megabyte.
  let buf : ByteArray := ⟨(bytes.map fun b => if b == 0xFF then 0xFE else b).toArray⟩
  for uniform in [true, false] do
    let d := MQ.Dec.init buf 0 buf.size MQ.tier1Contexts
    let t0 ← IO.monoNanosNow
    let (n, ones, pos) := benchLoop uniform buf.size (64 * mb) d (if uniform then 18 else 0) 0 0
    let t1 ← IO.monoNanosNow
    let ns := max (t1 - t0) 1
    let what := if uniform then "UNIFORM context" else "contexts 0..18 cyclic"
    IO.println s!"  mq throughput ({what}): {n} decisions ({ones} ones, {pos} bytes) in {ns / 1000000} ms = {n * 1000 / ns} M decisions/s, {pos * 1000 / ns} MB/s"
  return f

end JPEG2000.Tests.MQ
