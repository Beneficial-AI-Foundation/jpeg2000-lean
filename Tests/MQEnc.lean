import Encode.MQ

/-!
# Unit tests: reference MQ encoder (task 2.2)

Plan.md §4 (C1), §5.3; T.800 Annex C encoder (C.2.1–C.2.9).

* Known answer: the ITU-T T.88 Annex H.2 test sequence (256 bits, one context in state 0).
  `encodeAll` yields exactly the first 28 bytes of `t88Encoded`; the T.88 reference stream
  carries two more bytes, `0xFF 0xAC`, which are not produced by `FLUSH` (whose last byte
  here is `B = 0xDF`, written because it is not `0xFF`) but appended by T.88 after the coded
  data as a terminating marker code (`0xAC > 0x8F`). The T.800 decoder reads `0xFF` past the
  end of a segment, which a marker code also produces, so both streams decode identically
  (checked below).
* Round trips `decodeAll (encodeAll inits pairs) inits (pairs.map (·.1)) = pairs.map (·.2)`
  on thousands of deterministic pseudo-random `(context, decision)` sequences over the 19
  Tier-1 contexts with the T.800 D.7 initial states, with varied lengths and skewed
  probabilities, plus edge cases (empty, all-MPS, all-LPS, alternating, long runs that make
  `0xFF` bytes and carries); every run also checks the encoder register invariants and the
  output byte syntax (bytes `< 256`, a `0xFF` is followed by a byte `< 0x90`, no trailing
  `0xFF`).
-/

namespace JPEG2000.Tests.MQEnc

open JPEG2000.Spec.MQ JPEG2000.Encode.MQ

/-- Runs one named check, printing a line on failure; returns 1 on failure, 0 on success. -/
def expect (name : String) (ok : Bool) : IO Nat := do
  if ok then return 0
  IO.eprintln s!"  FAIL mqenc: {name}"
  return 1

/-- Tier-1 initial states (T.800 D.7): 19 contexts, context 0 (all-zero neighbours) in
state 4, context 17 (run-length) in state 3, context 18 (UNIFORM) in state 46. -/
def tier1Inits : List Nat := [4] ++ List.replicate 16 0 ++ [3, 46]

/-- A deterministic linear congruential generator (state → next state). -/
def lcg (x : Nat) : Nat := (x * 1103515245 + 12345) % 2147483648

/-- `n` pseudo-random `(context, decision)` pairs from `seed`: contexts below `ncx`, and a
decision `true` with probability `p / 1024`. -/
def randomPairs (seed n ncx p : Nat) : List (Nat × Bool) :=
  ((List.range n).foldl (fun (acc : List (Nat × Bool) × Nat) _ =>
    let x := lcg acc.2
    let y := lcg x
    ((x / 65536 % ncx, y / 65536 % 1024 < p) :: acc.1, y)) ([], seed)).1

/-- The round trip property C1 on one sequence. -/
def roundTrip (inits : List Nat) (pairs : List (Nat × Bool)) : Bool :=
  decodeAll (encodeAll inits pairs) inits (pairs.map (·.1)) == pairs.map (·.2)

/-- Statistics of one encoder run: whether the invariants held, whether a carry reached an
already-buffered byte `B`, whether a `0xFF` byte was produced. -/
structure Stats where
  /-- Register invariants and byte syntax held throughout. -/
  ok : Bool
  /-- A carry propagated into `B` at some `BYTEOUT`. -/
  carry : Bool
  /-- The output contains a `0xFF` byte. -/
  ff : Bool

/-- The output byte syntax: every byte `< 256`, a `0xFF` is followed by a byte `< 0x90`. -/
def byteSyntax : List Nat → Bool
  | [] => true
  | [b] => b < 256
  | b :: c :: rest => b < 256 && (b != 0xFF || c < 0x90) && byteSyntax (c :: rest)

/-- Encode `pairs` step by step, checking `0x8000 ≤ A < 0x10000`, `C < 2^28`, `1 ≤ CT ≤ 12`,
`B < 256` after every decision, detecting carries into `B`, then checking the byte syntax
of the flushed output. -/
def stats (inits : List Nat) (pairs : List (Nat × Bool)) : Stats :=
  let inv (s : EncState) : Bool :=
    0x8000 ≤ s.A && s.A < 0x10000 && s.C < 0x10000000 && 1 ≤ s.CT && s.CT ≤ 12 && s.B < 256
  let r := pairs.foldl (fun (acc : Bool × Bool × EncState × Contexts) (cx, d) =>
    let (ok, carry, s, cxs) := acc
    let (s', cxs') := encode s cxs cx d
    let k := s'.outRev.length - s.outRev.length
    -- the oldest byte finished during this step is the old `B`, unless a carry hit it
    let carry := carry || (k > 0 && s'.outRev.getD (k - 1) 0 != s.B)
    (ok && inv s', carry, s', cxs')) (inv initenc, false, initenc, initContexts inits)
  let out := (encodeAll inits pairs).map (·.toNat)
  let raw := r.2.2.1.outRev
  { ok := r.1 && raw.all (· < 256) && byteSyntax out && out.getLast? != some 0xFF
    carry := r.2.1
    ff := out.contains 0xFF }

/-- Runs the suite; returns the number of failures. -/
def run : IO Nat := do
  let mut f := 0
  -- Known answer: T.88 H.2 (single context, state 0, MPS 0).
  let t88Pairs := (bitsOf t88Data).map (0, ·)
  let enc := encodeAll [0] t88Pairs
  f := f + (← expect "T.88 H.2: encoder output = reference without its trailing 0xFF 0xAC"
    (enc == t88Encoded.take 28 && t88Encoded.drop 28 == [0xFF, 0xAC]))
  f := f + (← expect "T.88 H.2: encoder output decodes to the reference data"
    (decodeAll enc [0] (List.replicate 256 0) == bitsOf t88Data))
  f := f + (← expect "T.88 H.2: round trip" (roundTrip [0] t88Pairs))
  f := f + (← expect "T.88 H.2: invariants" (stats [0] t88Pairs).ok)
  -- INITENC (Figure C.10).
  f := f + (← expect "INITENC registers"
    (initenc.A == 0x8000 && initenc.C == 0 && initenc.CT == 12 && initenc.B == 0))
  -- BYTEOUT cases (Figure C.9).
  let st (b c : Nat) : EncState := { C := c, A := 0x8000, CT := 0, B := b, outRev := [] }
  let o1 := byteout (st 0x12 0x1234567)
  f := f + (← expect "BYTEOUT 8 bits"
    (o1.outRev == [0x12] && o1.B == 0x1234567 / 0x80000 && o1.C == 0x1234567 % 0x80000 &&
      o1.CT == 8))
  let o2 := byteout (st 0xFF 0x1234567)
  f := f + (← expect "BYTEOUT after 0xFF: 7 bits"
    (o2.outRev == [0xFF] && o2.B == 0x1234567 / 0x100000 && o2.CT == 7))
  let o3 := byteout (st 0x12 0x8123456)
  f := f + (← expect "BYTEOUT carry"
    (o3.outRev == [0x13] && o3.B == 0x8123456 / 0x80000 % 0x100 && o3.B < 256 && o3.CT == 8))
  let o4 := byteout (st 0xFE 0x8123456)
  f := f + (← expect "BYTEOUT carry into 0xFF: 7 bits"
    (o4.outRev == [0xFF] && o4.B == 0x0123456 / 0x100000 && o4.C == 0x0123456 % 0x100000 &&
      o4.CT == 7))
  -- Edge cases over the Tier-1 contexts.
  let mut edges : List (String × List Nat × List (Nat × Bool)) := [
    ("empty", tier1Inits, []),
    ("empty, one context", [0], []),
    ("all MPS, context 0", tier1Inits, List.replicate 5000 (0, false)),
    ("all MPS, UNIFORM", tier1Inits, List.replicate 3000 (18, false)),
    ("all LPS, context 5", tier1Inits, List.replicate 3000 (5, true)),
    ("all ones, context 0 (MPS switches)", tier1Inits, List.replicate 3000 (0, true)),
    ("alternating", tier1Inits, (List.range 3000).map fun i => (i % 19, i % 2 == 0)),
    ("single decision 0", tier1Inits, [(0, false)]),
    ("single decision 1", tier1Inits, [(0, true)]),
    ("UNIFORM ones", tier1Inits, List.replicate 2000 (18, true)) ]
  for n in [1, 2, 3, 7, 8, 9, 15, 16, 17, 31, 32, 33] do
    edges := edges ++ [(s!"{n} UNIFORM ones", tier1Inits, List.replicate n (18, true)),
      (s!"{n} MPS then one LPS", tier1Inits, List.replicate n (17, false) ++ [(17, true)])]
  for (name, inits, pairs) in edges do
    f := f + (← expect s!"edge round trip: {name}" (roundTrip inits pairs))
    f := f + (← expect s!"edge invariants: {name}" (stats inits pairs).ok)
  -- Pseudo-random sequences: varied lengths, context counts and skews.
  let skews := [0, 1, 8, 64, 256, 512, 768, 960, 1016, 1023, 1024]
  let mut count := 0
  let mut carries := 0
  let mut ffs := 0
  for seed in List.range 3000 do
    let n := (lcg (seed + 77)) / 65536 % (if seed % 10 == 0 then 2000 else 200)
    let ncx := if seed % 3 == 0 then 1 else 19
    let p := skews.getD (seed % skews.length) 512
    let pairs := randomPairs (seed * 2654435761 + 1) n ncx p
    let ok := roundTrip tier1Inits pairs
    let s := stats tier1Inits pairs
    if !ok then
      f := f + (← expect s!"random round trip seed {seed} (n {n}, p {p})" false)
    if !s.ok then
      f := f + (← expect s!"random invariants seed {seed} (n {n}, p {p})" false)
    count := count + 1
    if s.carry then carries := carries + 1
    if s.ff then ffs := ffs + 1
  -- The corpus exercised the rare paths of BYTEOUT.
  f := f + (← expect s!"random runs: {count} sequences" (count == 3000))
  f := f + (← expect s!"random runs exercised carries ({carries})" (carries > 0))
  f := f + (← expect s!"random runs produced 0xFF bytes ({ffs})" (ffs > 0))
  return f

end JPEG2000.Tests.MQEnc
