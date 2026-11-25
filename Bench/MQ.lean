import JPEG2000.MQ
import Spec.MQ
import Encode.MQ

/-!
# MQ decoder throughput benchmark (task 2.6): `lake exe bench-mq`

Plan.md §6 (items 1–3, 8: fixed-width registers, `ByteArray` buffers, measured speed),
§8 item 4; T.800 Annex C.3 (decoder), Table D.7 (Tier-1 initial context states).

Uniformly random bytes are useless MQ benchmark input (an `0xFF` followed by a byte `> 0x8F`
reads as a marker and the decoder then consumes almost nothing), so the data is produced by
the reference encoder `Encode.MQ.encodeAll`:

* four data sets of skewed random decisions over the 19 Tier-1 contexts (D.7 initial
  states), `p(LPS)` ∈ {0.02, 0.1, 0.3, 0.5}, each split into segments of 16 384 decisions
  (about a 64×64 code-block's worth), with up to 1 MB of coded bytes or 8 M decisions per
  set;
* the ITU-T T.88 H.2 vector (30 bytes, 256 decisions, one context) repeated 20 000 times,
  which measures the per-segment overhead (`INITDEC`, context-array copy).

Each set is decoded with the fast decoder `JPEG2000.MQ.Dec.decode` (one `Dec.init` per
segment, contexts from a shared array, as Tier-1 will do) 5 times; the median wall time
gives M decisions/s and MB/s (MB = 10⁶ coded bytes). The count of `1` decisions is checked
against the generated data on every run. For comparison the flowchart spec
`Spec.MQ.decodeAll` (lists and `Nat`; `byteAt` is linear in the position) and the fast
decoder's list API `JPEG2000.MQ.decodeAll` are timed on one small segment.
-/

namespace JPEG2000.Bench.MQ

open JPEG2000

/-- One splitmix64 step: the output word and the next state. -/
def splitmix (s : UInt64) : UInt64 × UInt64 :=
  let s := s + 0x9E3779B97F4A7C15
  let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), s)

/-- Tier-1 initial states (T.800 Table D.7). -/
def tier1Inits : List Nat := [4] ++ List.replicate 16 0 ++ [3, 46]

/-- A benchmark data set: segments concatenated in `coded` (segment `k` is
`coded[starts[k], starts[k+1])`), its decisions' contexts concatenated in `cxs`
(`counts[k]` per segment), the packed initial context array and the expected number of
`1` decisions. -/
structure Dataset where
  /-- Row label. -/
  name : String
  /-- Concatenated coded segments. -/
  coded : ByteArray
  /-- Segment boundaries (`nseg + 1` entries). -/
  starts : Array Nat
  /-- Decisions per segment. -/
  counts : Array Nat
  /-- Contexts of all decisions, in order. -/
  cxs : ByteArray
  /-- Packed initial context states (`JPEG2000.MQ.initContexts`). -/
  ctx0 : ByteArray
  /-- Expected number of `1` decisions. -/
  ones : Nat

/-- `n` random `(context, decision)` pairs over the 19 contexts: decision = LPS with
probability `p / 1024`, the MPS value fixed per context. -/
def genPairs (p : Nat) : Nat → UInt64 → List (Nat × Bool) → List (Nat × Bool) × UInt64
  | 0, s, acc => (acc.reverse, s)
  | n + 1, s, acc =>
    let (z, s) := splitmix s
    let cx := (z >>> 40).toNat % 19
    let lps := (z &&& 1023).toNat < p
    genPairs p n s ((cx, lps != (cx % 3 == 0)) :: acc)

/-- Build a data set of segments of `segLen` decisions with `p(LPS) = p / 1024`, until
`maxBytes` coded bytes or `maxDecisions` decisions. Returns it with the encoding time (ns). -/
def mkDataset (name : String) (p segLen maxBytes maxDecisions : Nat) (seed : UInt64) :
    IO (Dataset × Nat) := do
  let mut s := seed
  let mut coded := ByteArray.empty
  let mut starts : Array Nat := #[0]
  let mut counts : Array Nat := #[]
  let mut cxs := ByteArray.empty
  let mut ones := 0
  let mut decisions := 0
  let mut encNs := 0
  while coded.size < maxBytes && decisions < maxDecisions do
    let (pairs, s') := genPairs p segLen s []
    s := s'
    let t0 ← IO.monoNanosNow
    let enc := Encode.MQ.encodeAll tier1Inits pairs
    let encLen := enc.length
    let t1 ← IO.monoNanosNow
    encNs := encNs + (t1 - t0) + (if encLen == 0 then 1 else 0)
    coded := coded ++ ⟨enc.toArray⟩
    starts := starts.push coded.size
    counts := counts.push segLen
    for (cx, d) in pairs do
      cxs := cxs.push cx.toUInt8
      if d then ones := ones + 1
    decisions := decisions + segLen
  return ({ name, coded, starts, counts, cxs, ctx0 := MQ.initContexts tier1Inits, ones }, encNs)

/-- The T.88 H.2 segment repeated `reps` times (one context, state 0). -/
def t88Dataset (reps : Nat) : Dataset :=
  let seg : ByteArray := ⟨Spec.MQ.t88Encoded.toArray⟩
  let bits := Spec.MQ.bitsOf Spec.MQ.t88Data
  { name := s!"T.88 H.2 x {reps}"
    coded := (List.replicate reps seg).foldl (· ++ ·) ByteArray.empty
    starts := (List.range (reps + 1)).toArray.map (· * seg.size)
    counts := Array.replicate reps 256
    cxs := ⟨Array.replicate (reps * 256) 0⟩
    ctx0 := MQ.initContexts [0]
    ones := reps * (bits.filter id).length }

/-- Decode `fuel` decisions of one segment, contexts from `cxs` starting at `i`; returns
the updated count of `1` decisions and the next context offset. -/
def decodeSeg (cxs : ByteArray) : Nat → Nat → MQ.Dec → Nat → Nat × Nat
  | 0, i, _, ones => (ones, i)
  | fuel + 1, i, d, ones =>
    if h : i < cxs.size then
      let (b, d) := d.decode (cxs.get i h).toNat
      decodeSeg cxs fuel (i + 1) d (if b then ones + 1 else ones)
    else (ones, i)

/-- Decode segments `k, k+1, …` of `ds` (`fuel` of them); `ones` starts at the caller's
value (the run number, so the call cannot be hoisted out of the timing loop). -/
def decodeSegs (ds : Dataset) : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, ones => ones
  | fuel + 1, k, i, ones =>
    let start := ds.starts.getD k 0
    let stop := ds.starts.getD (k + 1) 0
    let d := MQ.Dec.init ds.coded start stop ds.ctx0
    let (ones, i) := decodeSeg ds.cxs (ds.counts.getD k 0) i d ones
    decodeSegs ds fuel (k + 1) i ones

/-- Median of a non-empty list of naturals. -/
def median (xs : List Nat) : Nat :=
  let a := xs.toArray.qsort (· < ·)
  a.getD (a.size / 2) 0

/-- `num / den` with one decimal (integer arithmetic). -/
def fmt1 (num den : Nat) : String :=
  let t := (num * 10 + den / 2) / max den 1
  s!"{t / 10}.{t % 10}"

/-- `num / den` with two decimals (integer arithmetic). -/
def fmt2 (num den : Nat) : String :=
  let t := (num * 100 + den / 2) / max den 1
  s!"{t / 100}.{if t % 100 < 10 then "0" else ""}{t % 100}"

/-- Time `runs` decodes of `ds`; returns the median ns, or an error when a run's count of
`1` decisions differs from the expected one. -/
def timeDataset (ds : Dataset) (runs : Nat) : IO Nat := do
  let nseg := ds.counts.size
  let mut times : List Nat := []
  for r in [0:runs] do
    let t0 ← IO.monoNanosNow
    let ones := decodeSegs ds nseg 0 0 r
    let t1 ← IO.monoNanosNow
    if ones != ds.ones + r then
      throw (IO.userError s!"{ds.name}: decoded {ones - r} ones, expected {ds.ones}")
    times := (t1 - t0) :: times
  return max (median times) 1

/-- One Markdown table row. -/
def row (name : String) (decisions bytes ns : Nat) (bitsPerDec : Bool := true) : String :=
  let bpd := if bitsPerDec then fmt2 (bytes * 8) decisions else "–"
  s!"| {name} | {decisions} | {bytes} | {bpd} | {fmt1 ns 1000000} | " ++
    s!"{fmt1 (decisions * 1000) ns} | {fmt1 (bytes * 1000) ns} |"

end JPEG2000.Bench.MQ

open JPEG2000 JPEG2000.Bench.MQ in
/-- Builds the data sets, times the decoders, prints a Markdown table. -/
def main : IO UInt32 := do
  let runs := 5
  IO.println "MQ decoder throughput (median of 5 runs; MB = 10^6 coded bytes)\n"
  IO.println "| data | decisions | coded bytes | bits/decision | ms | M decisions/s | MB/s |"
  IO.println "|---|---|---|---|---|---|---|"
  let mut totalBytes := 0
  let mut encInfo : List String := []
  for (label, p, seed) in [("p(LPS) 0.02", 20, 1), ("p(LPS) 0.1", 102, 2),
                           ("p(LPS) 0.3", 307, 3), ("p(LPS) 0.5", 512, 4)] do
    let (ds, encNs) ← mkDataset s!"fast, {label}, 19 ctx" p 16384 1000000 8000000 (seed : UInt64)
    let ns ← timeDataset ds runs
    let decisions := ds.cxs.size
    totalBytes := totalBytes + ds.coded.size
    IO.println (row ds.name decisions ds.coded.size ns)
    encInfo := encInfo ++ [s!"{label}: {fmt1 (decisions * 1000) (max encNs 1)} M decisions/s"]
  let t88 := t88Dataset 20000
  let ns ← timeDataset t88 runs
  IO.println (row s!"fast, {t88.name} (init per segment)" t88.cxs.size t88.coded.size ns)
  -- Spec vs fast list API on one small segment.
  let (pairs, _) := genPairs 102 20000 (7 : UInt64) []
  let enc := Encode.MQ.encodeAll tier1Inits pairs
  let cxList := pairs.map (·.1)
  let expect := pairs.map (·.2)
  let encArr : ByteArray := ⟨enc.toArray⟩
  let mut specT : List Nat := []
  let mut listT : List Nat := []
  for r in [0:runs] do
    let t0 ← IO.monoNanosNow
    let a := Spec.MQ.decodeAll enc tier1Inits (cxList ++ List.replicate (r % 1) 0)
    let ok := a == expect
    let t1 ← IO.monoNanosNow
    let b := MQ.decodeAll encArr tier1Inits (cxList ++ List.replicate (r % 1) 0)
    let ok2 := b == expect
    let t2 ← IO.monoNanosNow
    unless ok && ok2 do throw (IO.userError "spec/list comparison: wrong decisions")
    specT := (t1 - t0) :: specT
    listT := (t2 - t1) :: listT
  IO.println (row "spec `Spec.MQ.decodeAll`, p(LPS) 0.1, 1 segment" 20000 enc.length
    (max (median specT) 1))
  IO.println (row "fast list API `MQ.decodeAll`, same segment" 20000 enc.length
    (max (median listT) 1))
  IO.println s!"\nTotal coded bytes in the four skewed sets: {totalBytes}"
  IO.println s!"Reference encoder (`Encode.MQ.encodeAll`, data generation): {String.intercalate "; " encInfo}"
  return 0
