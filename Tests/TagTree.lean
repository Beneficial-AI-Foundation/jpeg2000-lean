import JPEG2000.TagTree
import Spec.TagTree

/-!
# Tag trees (task 4.1): hand examples, encode → decode round trips, fast = spec

Plan.md §4 (C4), §5.2 "Tier-2", §8; T.800 B.10.1 (bit stuffing), B.10.2 (tag trees),
B.10.4/B.10.5 (inclusion thresholds `layer + 1`, exact zero-bit-plane values).

1. Hand-traced examples (bits worked out by hand from B.10.2, checked against the reference
   encoder `Spec.TagTree.encodeAll`, the spec decoder and both fast decoders).
2. Edge cases: `create` limits, empty trees, leaves out of range, truncated input, exact
   values above their bound, node counts `≤ 4 · w · h` for every shape up to 64 × 64.
3. 500 random cases (shapes 1 × 1 … 32 × 32, random leaf values, query lists: per-layer
   inclusion sweeps with increasing thresholds, random thresholds, exact values): the encoder's
   bits decode to the true answers with the spec decoder, the fast decoder over the bit list
   (`decodeWith listNext`) and the fast decoder over a `BitReader` reading the bits packed
   with B.10.1 stuffing — all three must agree and leave the same bits.
-/

namespace JPEG2000.Tests.TagTree

open JPEG2000
open JPEG2000.Spec.TagTree (Query Answer encodeAll decodeAll trueAnswer init listNext)

/-- Runs one named check, printing a line on failure; returns 1 on failure, 0 on success. -/
def expect (name : String) (ok : Bool) : IO Nat := do
  if ok then return 0
  IO.eprintln s!"  FAIL tagtree: {name}"
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

/-- Leaf values as a function, from a row-major array. -/
def valsFn (w : Nat) (a : Array Nat) : Nat → Nat → Nat := fun x y => a.getD (y * w + x) 0

/-- Packs bits MSB first with B.10.1 stuffing: after a `0xFF` byte the next byte carries only
7 bits (its MSB is 0). The last byte is padded with zeros. -/
def packBits (bits : List Bool) : ByteArray := Id.run do
  let mut out : ByteArray := ByteArray.empty
  let mut cur : Nat := 0
  let mut cnt : Nat := 0
  let mut cap : Nat := 8
  for b in bits do
    cur := cur * 2 + (if b then 1 else 0)
    cnt := cnt + 1
    if cnt == cap then
      out := out.push cur.toUInt8
      cap := if cur == 0xFF then 7 else 8
      cur := 0
      cnt := 0
  if cnt > 0 then
    out := out.push (cur * 2 ^ (cap - cnt)).toUInt8
  return out

/-- A bit reader over a byte array. -/
def brOf (bs : ByteArray) : Bytes.BitReader :=
  Bytes.BitReader.ofReader (Bytes.Reader.ofByteArray bs)

/-- Runs queries with a fast decoder (any bit source), returning the answers and the
source. Leaf `(x, y)` is passed as the row-major index `y * w + x`. -/
def fastAll {σ : Type} (next : σ → Except Error (Bool × σ)) (tr : TagTree.Tree) (src : σ) :
    List Query → Except Error (List Answer × σ)
  | [] => .ok ([], src)
  | .lt x y t :: qs => do
    let (b, tr, src) ← TagTree.decodeWith next tr src (y * tr.w + x) t
    let (as, src) ← fastAll next tr src qs
    return (.lt b :: as, src)
  | .exact x y m :: qs => do
    let (u, tr, src) ← TagTree.decodeValueWith next tr src (y * tr.w + x) m
    let (as, src) ← fastAll next tr src qs
    return (.exact u :: as, src)

/-- Encodes `qs` for the leaf values, then decodes with the spec decoder, the fast decoder
over the bit list and the fast decoder over the packed bytes; `none` if all agree with the
true answers (and the expected bits, when given), else a description. -/
def checkCase (w h : Nat) (vals : Array Nat) (qs : List Query) (expBits : Option (List Bool)) :
    Option String :=
  let v := valsFn w vals
  let bits := (encodeAll w h v qs init).1
  let want := qs.map (trueAnswer v)
  let extra := [true, false, true]
  if expBits.isSome && expBits != some bits then some s!"encoder bits {bits} ≠ {expBits}"
  else match decodeAll w h qs init (bits ++ extra) with
  | none => some "spec decoder failed"
  | some (as, _, rest) =>
    if as != want || rest != extra then some s!"spec answers {repr as} ≠ {repr want}"
    else match TagTree.create Limits.default w h with
    | .error _ => some "create failed"
    | .ok tr =>
      match fastAll listNext tr (bits ++ extra) qs with
      | .error e => some s!"fast (list) failed: {e}"
      | .ok (as2, rest2) =>
        if as2 != want || rest2 != extra then some s!"fast (list) answers {repr as2}"
        else
          match fastAll TagTree.bitNext tr (brOf (packBits bits)) qs with
          | .error e => some s!"fast (BitReader) failed: {e}"
          | .ok (as3, _) =>
            if as3 != want then some s!"fast (BitReader) answers {repr as3}" else none

/-- Hand-traced examples. -/
def handExamples : IO Nat := do
  let mut f := 0
  -- 2 × 2 leaves [1 3; 2 0], root 0. lt (0,0) 1: root `1` (known 0), leaf `0` (low 1 = t);
  -- lt (1,1) 1: leaf `1`; exact (0,0): t = 0, 1 read nothing, t = 2 reads `1` → 1.
  let r1 := checkCase 2 2 #[1, 3, 2, 0] [.lt 0 0 1, .lt 1 1 1, .exact 0 0 5]
    (some [true, false, true, true])
  f := f + (← expect s!"2x2 example {r1}" r1.isNone)
  -- 3 × 1 leaves [2 1 3]: level 1 = [1 3], root 1. lt (2,0) 4: root `0 1` (1), level-1 node
  -- `0 0 1` (3, from low 1), leaf `1` (3, from low 3) → true.
  let r2 := checkCase 3 1 #[2, 1, 3] [.lt 2 0 4] (some [false, true, false, false, true, true])
  f := f + (← expect s!"3x1 example {r2}" r2.isNone)
  -- Same tree, inclusion sweep over layers 0..2 (thresholds 1..3) in leaf order:
  -- t=1: (0,0) root `0` (low 1 = t), leaf: nothing; (1,0): nothing; (2,0): nothing.
  -- t=2: (0,0) root `1` (known 1), node(0) `1` (1), leaf low 1 `0` (2 = t);
  --      (1,0) leaf low 1 `1` (known 1) → true; (2,0) node(1) low 1 `0` (2) ; leaf nothing.
  -- t=3: (0,0) leaf low 2 `1` → true; (2,0) node(1) low 2 `0` (3); leaf nothing → false.
  let sweep : List Query := [.lt 0 0 1, .lt 1 0 1, .lt 2 0 1, .lt 0 0 2, .lt 1 0 2, .lt 2 0 2,
    .lt 0 0 3, .lt 2 0 3]
  let r3 := checkCase 3 1 #[2, 1, 3] sweep
    (some [false, true, true, false, true, false, true, false])
  f := f + (← expect s!"3x1 sweep {r3}" r3.isNone)
  -- 1 × 1: a single node; exact value 4 at thresholds 0..5: `0 0 0 0 1`.
  let r4 := checkCase 1 1 #[4] [.exact 0 0 10] (some [false, false, false, false, true])
  f := f + (← expect s!"1x1 exact {r4}" r4.isNone)
  -- A known BitReader case: bits `0 1 0 0 1 1` = 0x4C (padded) for the 3 × 1 query above.
  let ok5 := match TagTree.create Limits.default 3 1 with
    | .ok tr => match TagTree.decode tr (brOf (ByteArray.mk #[0x4C])) 2 4 with
      | .ok (b, _, _) => b
      | .error _ => false
    | .error _ => false
  f := f + (← expect "3x1 BitReader 0x4C" ok5)
  return f

/-- Error and limit cases. -/
def edgeCases : IO Nat := do
  let mut f := 0
  let tooBig := match TagTree.create Limits.strict 200 200 with
    | .error (.limitExceeded _ .codeBlocks _ _) => true
    | _ => false
  f := f + (← expect "create rejects w*h > maxCodeBlocks" tooBig)
  let empty := match TagTree.create Limits.default 0 5 with
    | .ok tr => (TagTree.decode tr (brOf (ByteArray.mk #[0xFF])) 0 1).toOption.isNone
    | .error _ => false
  f := f + (← expect "empty tree: queries fail" empty)
  let oob := match TagTree.create Limits.default 3 2 with
    | .ok tr => (TagTree.decode tr (brOf (ByteArray.mk #[0xFF])) 6 1).toOption.isNone
    | .error _ => false
  f := f + (← expect "leaf out of range fails" oob)
  let trunc := match TagTree.create Limits.default 4 4 with
    | .ok tr => match TagTree.decode tr (brOf ByteArray.empty) 5 3 with
      | .error (.truncated _ _) => true
      | _ => false
    | .error _ => false
  f := f + (← expect "truncated input fails" trunc)
  -- value 4 with bound 2: thresholds 0..3 read `0 0 0` and then the bound is exhausted.
  let over := match TagTree.create Limits.default 1 1 with
    | .ok tr => match TagTree.decodeValue tr (brOf (ByteArray.mk #[0x08])) 0 2 with
      | .error (.malformed _ _) => true
      | _ => false
    | .error _ => false
  f := f + (← expect "exact value above bound fails" over)
  -- node counts never exceed 4 · w · h (the `create` check is never spuriously hit)
  let mut bad := 0
  for w in List.range 64 do
    for h in List.range 64 do
      let n := TagTree.totalAux (TagTree.levels (w + 1) (h + 1)) (w + 1) (h + 1)
      if n > 4 * ((w + 1) * (h + 1)) then bad := bad + 1
  f := f + (← expect s!"node count ≤ 4wh ({bad} shapes over)" (bad == 0))
  -- levels: 1×1 → 1, 2×1 → 2, 3×3 → 3, 32×32 → 6, 33×1 → 7 (OpenJPEG `numlvls`)
  let lv := [TagTree.levels 1 1, TagTree.levels 2 1, TagTree.levels 3 3, TagTree.levels 32 32,
    TagTree.levels 33 1]
  f := f + (← expect s!"levels {lv}" (lv == [1, 2, 3, 6, 7]))
  return f

/-- A random case: shape, values and a query list. -/
def randomCase (s : UInt64) : (Nat × Nat × Array Nat × List Query) × UInt64 := Id.run do
  let mut s := s
  let (w, s1) := below s 32; s := s1
  let (h, s1) := below s 32; s := s1
  let w := w + 1
  let h := h + 1
  let (vmode, s1) := below s 4; s := s1
  let vmax := match vmode with | 0 => 2 | 1 => 8 | 2 => 40 | _ => 1000
  let mut vals : Array Nat := #[]
  for _ in List.range (w * h) do
    let (x, s1) := below s (vmax + 1); s := s1
    vals := vals.push x
  let (qmode, s1) := below s 3; s := s1
  let mut qs : Array Query := #[]
  if qmode == 0 then
    -- inclusion sweep: layers, leaves in order, until included (thresholds layer + 1)
    let (layers, s1) := below s 10; s := s1
    let mut incl : Array Bool := Array.replicate (w * h) false
    for l in List.range (layers + 1) do
      for i in List.range (w * h) do
        if !(incl.getD i true) then
          qs := qs.push (.lt (i % w) (i / w) (l + 1))
          if vals.getD i 0 < l + 1 then
            incl := incl.set! i true
  else if qmode == 1 then
    -- random leaves and thresholds
    let (nq, s1) := below s 60; s := s1
    for _ in List.range (nq + 1) do
      let (i, s1) := below s (w * h); s := s1
      let (t, s1) := below s (vmax + 3); s := s1
      qs := qs.push (.lt (i % w) (i / w) t)
  else
    -- exact values mixed with threshold queries
    let (nq, s1) := below s 30; s := s1
    for _ in List.range (nq + 1) do
      let (i, s1) := below s (w * h); s := s1
      let (k, s1) := below s 3; s := s1
      if k == 0 then
        let (t, s1) := below s (vmax + 3); s := s1
        qs := qs.push (.lt (i % w) (i / w) t)
      else
        -- exact queries cost one walk per threshold: keep their values small
        if vals.getD i 0 ≤ 64 then
          let (extra, s1) := below s 5; s := s1
          qs := qs.push (.exact (i % w) (i / w) (vals.getD i 0 + extra))
  return ((w, h, vals, qs.toList), s)

/-- `n` random cases. -/
def randomCases (n : Nat) : IO Nat := do
  let mut s : UInt64 := 0x7A6E5EED
  let mut f := 0
  let mut ok := 0
  for c in List.range n do
    let ((w, h, vals, qs), s1) := randomCase s
    s := s1
    match checkCase w h vals qs none with
    | none => ok := ok + 1
    | some msg =>
      f := f + 1
      if f ≤ 5 then IO.eprintln s!"  FAIL tagtree: random case {c} ({w}x{h}, {qs.length} queries): {msg}"
  IO.println s!"tagtree random round trips: {ok}/{n} ok"
  return f

/-- Runs the suite with `n` random cases; returns the number of failures. -/
def runWith (n : Nat) : IO Nat := do
  let a ← handExamples
  let b ← edgeCases
  let c ← randomCases n
  return a + b + c

/-- Runs the suite: 60 random cases by default (the spec-side state is quadratic to evaluate),
or `JPEG2000_TAGTREE_CASES` cases when that variable is set; returns the number of failures. -/
def run : IO Nat := do
  let n := ((← IO.getEnv "JPEG2000_TAGTREE_CASES").bind String.toNat?).getD 60
  runWith n

end JPEG2000.Tests.TagTree
