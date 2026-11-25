import Spec.MQ

/-!
# Unit tests: MQ decoder spec (task 2.1)

Plan.md §4 (C1, C2), §5.2 "MQ decoder"; T.800 Annex C (Table C.2, C.3.1–C.3.5). The known
answer is the ITU-T T.88 Annex H.2 test sequence (JBIG2 uses the same MQ coder with the same
`INITDEC`/`BYTEIN`); the other checks exercise totality on arbitrary bytes, the synthetic
`0xFF` padding and the register range invariants.
-/

namespace JPEG2000.Tests.MQSpec

open JPEG2000.Spec.MQ

/-- Runs one named check, printing a line on failure; returns 1 on failure, 0 on success. -/
def expect (name : String) (ok : Bool) : IO Nat := do
  if ok then return 0
  IO.eprintln s!"  FAIL mqspec: {name}"
  return 1

/-- Tier-1 initial states (T.800 D.7): 19 contexts, context 0 (all-zero neighbours) in
state 4, context 17 (run-length) in state 3, context 18 (UNIFORM) in state 46. -/
def tier1Inits : List Nat := [4] ++ List.replicate 16 0 ++ [3, 46]

/-- A deterministic linear congruential generator (state → next state). -/
def lcg (x : Nat) : Nat := (x * 1103515245 + 12345) % 2147483648

/-- `n` pseudo-random values below `m` from seed `seed`. -/
def randoms (seed n m : Nat) : List Nat :=
  ((List.range n).foldl (fun (acc : List Nat × Nat) _ =>
    let x := lcg acc.2; (x / 65536 % m :: acc.1, x)) ([], seed)).1

/-- Decode `cxList` from `data`, checking the register invariants after every decision:
`0x8000 ≤ A < 0x10000`, `C < 2^32`, `CT ≤ 8`, `BP ≤ data.length + 1`. -/
def invariantsHold (data : List UInt8) (cxList : List Nat) : Bool :=
  let ok (s : State) : Bool :=
    0x8000 ≤ s.A && s.A < 0x10000 && s.C < 0x100000000 && s.CT ≤ 8 &&
      s.pos ≤ data.length + 1
  let s0 := initdec data
  (cxList.foldl (fun (acc : Bool × State × Contexts) cx =>
    let (d, s, cxs) := decode acc.2.1 acc.2.2 cx
    let _ := d
    (acc.1 && ok s, s, cxs)) (ok s0, s0, initContexts tier1Inits)).1

/-- Runs the suite; returns the number of failures. -/
def run : IO Nat := do
  let mut f := 0
  -- Known answer: T.88 H.2 (single context, state 0, MPS 0).
  let out := decodeAll t88Encoded [0] (List.replicate 256 0)
  f := f + (← expect "T.88 H.2 decodes to the reference data" (out == bitsOf t88Data))
  f := f + (← expect "T.88 H.2 first byte 0x00, second 0x02"
    (out.take 16 == bitsOf [0x00, 0x02]))
  -- INITDEC register values on the T.88 vector: C = (0x84 << 16 + 0xC7 << 8) << 7, CT = 1.
  let s0 := initdec t88Encoded
  f := f + (← expect "INITDEC C" (s0.C == (0x840000 + 0xC700) * 0x80 % 0x100000000))
  f := f + (← expect "INITDEC A, CT, BP" (s0.A == 0x8000 && s0.CT == 1 && s0.pos == 1))
  -- BYTEIN cases (Figure C.19).
  let st (d : List UInt8) (p : Nat) : State := { C := 0, A := 0x8000, CT := 0, pos := p, data := d }
  let b1 := bytein (st [0x12, 0x34] 0)
  f := f + (← expect "BYTEIN plain" (b1.pos == 1 && b1.C == 0x3400 && b1.CT == 8))
  let b2 := bytein (st [0xFF, 0x7F] 0)
  f := f + (← expect "BYTEIN stuffed" (b2.pos == 1 && b2.C == 0x7F * 0x200 && b2.CT == 7))
  let b3 := bytein (st [0xFF, 0x90] 0)
  f := f + (← expect "BYTEIN marker" (b3.pos == 0 && b3.C == 0xFF00 && b3.CT == 8))
  let b4 := bytein (st [0x12] 0)
  f := f + (← expect "BYTEIN reads 0xFF past the end" (b4.pos == 1 && b4.C == 0xFF00))
  let b5 := bytein (st [0x12] 5)
  f := f + (← expect "BYTEIN past the end is a marker" (b5.pos == 5 && b5.C == 0xFF00 && b5.CT == 8))
  -- Totality and invariants on empty, all-0xFF and pseudo-random inputs with Tier-1 contexts.
  f := f + (← expect "empty segment" (invariantsHold [] (randoms 1 500 19)))
  f := f + (← expect "all-0xFF segment" (invariantsHold (List.replicate 20 0xFF) (randoms 2 500 19)))
  for seed in [3, 4, 5, 6, 7, 8, 9, 10] do
    let data := (randoms (seed * 7919) 200 256).map Nat.toUInt8
    f := f + (← expect s!"random segment seed {seed}"
      (invariantsHold data (randoms seed 2000 19)))
  -- Context table helpers.
  let cxs := initContexts tier1Inits
  f := f + (← expect "19 Tier-1 contexts" (cxs.length == 19))
  f := f + (← expect "context getters" ((cxs.get 0).index == 4 && (cxs.get 17).index == 3 &&
    (cxs.get 18).index == 46 && (cxs.get 99) == { index := 0, mps := false }))
  f := f + (← expect "context put out of range is a no-op" (cxs.put 99 ⟨5, true⟩ == cxs))
  -- The UNIFORM context (state 46) never adapts.
  let (_, _, cxsU) := decodeMany (initdec t88Encoded) cxs (List.replicate 100 18)
  f := f + (← expect "UNIFORM context stays in state 46" ((cxsU.get 18).index == 46))
  return f

end JPEG2000.Tests.MQSpec
