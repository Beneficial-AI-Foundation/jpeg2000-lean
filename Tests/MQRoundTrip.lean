import JPEG2000.MQ
import Spec.MQ
import Encode.MQ

/-!
# MQ round trips: reference encoder → spec decoder and fast decoder (task 2.6)

Plan.md §4 (C1, C2), §5.2 "MQ decoder", §5.3, §8 item 5; T.800 Annex C (C.2 encoder,
C.3 decoder), Table D.7 (Tier-1 initial context states).

1. Fixed vectors: the ITU-T T.88 Annex H.2 sequence (encoded, then decoded by both
   decoders), and edge sequences (empty, one decision, long MPS/LPS runs, out-of-range
   contexts).
2. `N` random round trips: a deterministic splitmix64 generator draws, per case, a length
   (mostly 1–64 decisions, some up to 4096), a context mode (one context in a random initial
   state; the 19 Tier-1 contexts in their D.7 states; the 19 contexts in random states;
   optionally with out-of-range contexts `19 … 26`, which read as state 0 and are never
   written) and a decision model (uniform, or skewed with `p(LPS)` from `1/1024` to `1/2`,
   per case or per context). Each sequence is encoded with `Encode.MQ.encodeAll` and decoded
   with both `Spec.MQ.decodeAll` and the fast `JPEG2000.MQ.decodeAll`; both must return the
   input decisions.

`N` defaults to 20 000 (a few seconds); the environment variable `JPEG2000_MQ_ROUNDTRIPS`
overrides it (the M2 run uses `JPEG2000_MQ_ROUNDTRIPS=1000000`). The suite prints
`mq round trips: K/N ok`.
-/

namespace JPEG2000.Tests.MQRoundTrip

open JPEG2000

/-- Default number of random round trips for `lake exe tests`. -/
def defaultN : Nat := 20000

/-- Runs one named check, printing a line on failure; returns 1 on failure, 0 on success. -/
def expect (name : String) (ok : Bool) : IO Nat := do
  if ok then return 0
  IO.eprintln s!"  FAIL mq-roundtrip: {name}"
  return 1

/-- One splitmix64 step: the output word and the next state. -/
def splitmix (s : UInt64) : UInt64 × UInt64 :=
  let s := s + 0x9E3779B97F4A7C15
  let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), s)

/-- A pseudo-random value below `m` (`m > 0`; the modulo bias is irrelevant here) and the
next generator state. -/
def below (s : UInt64) (m : Nat) : Nat × UInt64 :=
  let (z, s) := splitmix s
  ((z >>> 11).toNat % m, s)

/-- Tier-1 initial states (T.800 Table D.7). -/
def tier1Inits : List Nat := [4] ++ List.replicate 16 0 ++ [3, 46]

/-- `p(LPS)` values (out of 1024) used for skewed decisions. -/
def skews : List Nat := [1, 4, 20, 51, 102, 205, 307, 410, 512]

/-- One random test case: initial context states and `(context, decision)` pairs. -/
structure Case where
  /-- Initial states `I(CX)` (MPS 0). -/
  inits : List Nat
  /-- The coded `(context, decision)` pairs. -/
  pairs : List (Nat × Bool)
  /-- Short description for failure reports. -/
  desc : String

/-- Draw `n` pairs: context from `cxOf`, decision `true` with probability `pOf cx / 1024`
when the context's preferred value is `false` (flipped for odd preferred contexts). -/
def genPairs (cxOf : UInt64 → Nat × UInt64) (pOf : Nat → Nat) (pref : Nat → Bool) :
    Nat → UInt64 → List (Nat × Bool) → List (Nat × Bool) × UInt64
  | 0, s, acc => (acc.reverse, s)
  | n + 1, s, acc =>
    let (cx, s) := cxOf s
    let (r, s) := below s 1024
    let d := (r < pOf cx) != pref cx
    genPairs cxOf pOf pref n s ((cx, d) :: acc)

/-- Draw one random case from generator state `s`. -/
def genCase (s : UInt64) : Case × UInt64 :=
  -- length: 96 % in 1–64, 4 % in 1–4096
  let (lsel, s) := below s 100
  let (len, s) := if lsel < 96 then below s 64 else below s 4096
  let len := len + 1
  -- context mode
  let (mode, s) := below s 4
  let (oor, s) := below s 8          -- 1 in 8 cases has out-of-range contexts
  let (single, s) := splitmix s
  let st0 := (single >>> 11).toNat % 47
  let (randInits, s) := (List.range 19).foldl (fun (acc : List Nat × UInt64) _ =>
    let (v, s) := below acc.2 47; (v :: acc.1, s)) ([], s)
  let inits := match mode with
    | 0 => [st0]
    | 1 => tier1Inits
    | 2 => randInits
    | _ => tier1Inits
  let ncx := if mode == 0 then 1 else 19
  let cxOf (t : UInt64) : Nat × UInt64 :=
    let (r, t) := below t 1000
    if oor == 0 && r < 30 then (19 + r % 8, t)
    else if mode == 3 && r < 600 then (r % 3, t)   -- a few hot contexts adapt deep
    else (r % ncx, t)
  -- decision model
  let (dsel, s) := below s 4
  let (pi, s) := below s skews.length
  let p := skews.getD pi 512
  let (seedP, s) := splitmix s
  let pOf (cx : Nat) : Nat := match dsel with
    | 0 => 512                                  -- uniform
    | 1 => p                                    -- one skew for all contexts
    | 2 => skews.getD ((cx + seedP.toNat) % skews.length) 512  -- per-context skew
    | _ => if cx == 18 then 512 else p          -- UNIFORM context really uniform
  let pref (cx : Nat) : Bool := (seedP >>> (cx % 64).toUInt64) &&& 1 == 1
  let (pairs, s) := genPairs cxOf pOf pref len s []
  ({ inits, pairs, desc := s!"len {len} mode {mode} oor {oor == 0} dsel {dsel} p {p}" }, s)

/-- Encode `c` and decode it with the spec and the fast decoder; returns
`(spec ok, fast ok, coded length)`. -/
def check (inits : List Nat) (pairs : List (Nat × Bool)) : Bool × Bool × Nat :=
  let enc := Encode.MQ.encodeAll inits pairs
  let cxs := pairs.map (·.1)
  let ds := pairs.map (·.2)
  (Spec.MQ.decodeAll enc inits cxs == ds,
   MQ.decodeAll ⟨enc.toArray⟩ inits cxs == ds, enc.length)

/-- Round trip through both decoders. -/
def roundTrip (inits : List Nat) (pairs : List (Nat × Bool)) : Bool :=
  let (a, b, _) := check inits pairs
  a && b

/-- Number of random round trips: `JPEG2000_MQ_ROUNDTRIPS` if set to a number, else
`defaultN`. -/
def numTrips : IO Nat := do
  match ← IO.getEnv "JPEG2000_MQ_ROUNDTRIPS" with
  | some v => return v.trimAscii.toString.toNat?.getD defaultN
  | none => return defaultN

/-- Runs the suite; returns the number of failures. -/
def run : IO Nat := do
  let mut f := 0
  -- (1) Fixed vectors.
  let t88Bits := Spec.MQ.bitsOf Spec.MQ.t88Data
  let t88Pairs := t88Bits.map (0, ·)
  let enc := Encode.MQ.encodeAll [0] t88Pairs
  f := f + (← expect "T.88 H.2 encodes to the reference prefix"
    (enc == Spec.MQ.t88Encoded.take 28))
  f := f + (← expect "T.88 H.2 round trip (spec and fast)" (roundTrip [0] t88Pairs))
  f := f + (← expect "T.88 reference stream, fast decoder"
    (MQ.decodeAll ⟨Spec.MQ.t88Encoded.toArray⟩ [0] (List.replicate 256 0) == t88Bits))
  let fixed : List (String × List Nat × List (Nat × Bool)) :=
    [ ("empty", tier1Inits, []),
      ("one MPS", tier1Inits, [(0, false)]),
      ("one LPS", tier1Inits, [(0, true)]),
      ("10000 MPS ctx 0", tier1Inits, List.replicate 10000 (0, false)),
      ("4096 UNIFORM ones", tier1Inits, List.replicate 4096 (18, true)),
      ("4096 LPS-ish ctx 17", tier1Inits, List.replicate 4096 (17, true)),
      ("alternating 19 ctx", tier1Inits, (List.range 4096).map fun i => (i % 19, i % 3 == 0)),
      ("out-of-range only", tier1Inits, (List.range 500).map fun i => (19 + i % 5, i % 7 == 0)),
      ("no contexts at all", [], (List.range 300).map fun i => (i % 4, i % 2 == 0)),
      ("state 46 single", [46], (List.range 300).map fun i => (0, i % 5 == 0)) ]
  for (name, inits, pairs) in fixed do
    f := f + (← expect s!"fixed: {name}" (roundTrip inits pairs))
  -- (2) Random round trips.
  let n ← numTrips
  let mut s : UInt64 := 0x2026_0006
  let mut specFail := 0
  let mut fastFail := 0
  let mut ok := 0
  let mut decisions := 0
  let mut bytes := 0
  let t0 ← IO.monoMsNow
  for _ in [0:n] do
    let (c, s') := genCase s
    s := s'
    let (a, b, len) := check c.inits c.pairs
    decisions := decisions + c.pairs.length
    bytes := bytes + len
    if a && b then ok := ok + 1
    if !a then specFail := specFail + 1
    if !b then fastFail := fastFail + 1
    if (!a || !b) && specFail + fastFail ≤ 5 then
      IO.eprintln s!"  mismatch (spec ok {a}, fast ok {b}): {c.desc}"
  let t1 ← IO.monoMsNow
  IO.println s!"  mq round trips: {ok}/{n} ok ({decisions} decisions, {bytes} coded bytes, {t1 - t0} ms)"
  f := f + (← expect s!"random round trips, spec decoder ({specFail} failures)" (specFail == 0))
  f := f + (← expect s!"random round trips, fast decoder ({fastFail} failures)" (fastFail == 0))
  return f

end JPEG2000.Tests.MQRoundTrip
