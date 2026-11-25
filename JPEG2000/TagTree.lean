import JPEG2000.Bytes
import JPEG2000.Limits

/-!
# Tag trees (T.800 B.10.2): the decoder

Plan.md §3 rules 2–3, §4 (theorem C4), §5.1, §5.2 "Tier-2"; ITU-T T.800 B.10.2 (tag trees),
B.10.4 (code-block inclusion: threshold `layer + 1`), B.10.5 (zero bit-planes: exact value).

A tag tree over a `w × h` array of non-negative integers has level 0 = the leaves and each
node of level `k + 1` is the minimum of its (at most 2 × 2) children `(2x + i, 2y + j)` of
level `k`; the top level is a single node (OpenJPEG `opj_tgt_create`: levels are added while
a level has more than one node). The decoder state of each node is a lower bound `low` and,
once known, its value. A query `(leaf, t)` walks from the root to the leaf; at each node the
running lower bound is `max (parent's final low) (node's low)`, and while it is `< t` and the
node's value is unknown one bit is read: `1` fixes the value at the running bound, `0`
increments the bound. The answer is "the leaf's value is known and `< t`" — exactly OpenJPEG
`opj_tgt_decode(bio, tree, leafno, threshold)`, with an explicit "unknown" instead of its
sentinel value 999. The state persists across queries (it belongs to the precinct).

## Layout

Nodes live in two flat arrays, level after level, row-major within a level: the node
`(k, x, y)` has index `off k + y · dimW k + x`, where `dimW (k + 1) = ⌈dimW k / 2⌉` and
`off (k + 1) = off k + dimW k · dimH k`. A query computes the path arithmetically: `walk`
recurses from the leaf to the root (one level per call, structural recursion on the number
of levels) and processes the nodes while returning, root first. `low[i]` is the node's lower
bound; `val[i]` is `0` while unknown and `v + 1` once its value `v` is known.

## Bounds (Plan.md §3 rules 2–3)

* `create` checks the number of leaves against `Limits.maxCodeBlocks` (the leaves are the
  code-blocks of one precinct) and the node count `total ≤ 4 · maxCodeBlocks` before
  allocating `total` cells per array.
* Per node, at most `t - low` bits are read (`readLoop` is structurally recursive on that
  count), so a query reads at most `numLevels · t` bits; `walk` is structurally recursive on
  the number of levels; `decodeValue` makes at most `maxValue + 2` queries.

The bit source is a parameter (`decodeWith`): production code reads a `Bytes.BitReader`
(B.10.1 bit stuffing, `decode`); `Spec.TagTree` instantiates it with a list of bits to prove
it equal to the specification decoder.
-/

namespace JPEG2000.TagTree

open JPEG2000.Bytes

/-- Number of levels of a tag tree over `dw × dh` leaves, with `fuel` bounding the number of
halvings (`levels` passes `w + h`, enough since each halving step lowers `dw + dh`). A level
with at most one node is the top. -/
def levelsAux : Nat → Nat → Nat → Nat
  | 0, _, _ => 1
  | fuel + 1, dw, dh =>
    if dw ≤ 1 ∧ dh ≤ 1 then 1 else levelsAux fuel ((dw + 1) / 2) ((dh + 1) / 2) + 1

/-- Number of levels of the tag tree over a `w × h` leaf array (OpenJPEG `numlvls`). -/
def levels (w h : Nat) : Nat := levelsAux (w + h) w h

/-- Number of nodes of `n` levels starting at a `dw × dh` level. -/
def totalAux : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | n + 1, dw, dh => dw * dh + totalAux n ((dw + 1) / 2) ((dh + 1) / 2)

/-- A tag tree with its decoding state (flat arrays; see the module doc). -/
structure Tree where
  /-- Leaves per row. -/
  w : Nat
  /-- Leaf rows. -/
  h : Nat
  /-- Number of levels (`levels w h`). -/
  numLevels : Nat
  /-- Current lower bound of each node. -/
  low : Array Nat
  /-- `0` while a node's value is unknown, `v + 1` once it is known to be `v`. -/
  val : Array Nat

/-- Where tag-tree errors are reported. -/
def loc : Location := .at .tier2

/-- A fresh tag tree over `w × h` leaves (all values unknown, all lower bounds 0). Checks
`w · h ≤ L.maxCodeBlocks` and the node count `≤ 4 · L.maxCodeBlocks` before allocating. -/
def create (L : Limits) (w h : Nat) : Except Error Tree := do
  L.check loc .codeBlocks (w * h)
  let n := levels w h
  let total := totalAux n w h
  Limits.checkLe loc .codeBlocks total (4 * L.maxCodeBlocks)
  return { w, h, numLevels := n, low := Array.replicate total 0, val := Array.replicate total 0 }

section Generic

variable {σ : Type} (next : σ → Except Error (Bool × σ))

/-- The bit loop at one node of unknown value: at most `n` bits (`n = t - low`), stopping at
the first `1` (value known, `= low`) or when `low` reaches the threshold. Returns the final
bound, whether the value became known, and the source. -/
@[specialize] def readLoop : Nat → Nat → σ → Except Error (Nat × Bool × σ)
  | 0, low, s => .ok (low, false, s)
  | n + 1, low, s =>
    match next s with
    | .error e => .error e
    | .ok (b, s) => if b then .ok (low, true, s) else readLoop n (low + 1) s

/-- One node of a query with threshold `t`: node index `i`, incoming bound `inLow` (the
parent's final bound, `0` at the root). Returns the node's final bound and value code. -/
@[inline] def nodeStep (t i inLow : Nat) (lo va : Array Nat) (s : σ) :
    Except Error (Nat × Nat × Array Nat × Array Nat × σ) :=
  let low := max inLow (lo.getD i 0)
  let ve := va.getD i 0
  if ve != 0 then .ok (low, ve, lo.setIfInBounds i low, va, s)
  else
    match readLoop next (t - low) low s with
    | .error e => .error e
    | .ok (low', kn, s) =>
      if kn then .ok (low', low' + 1, lo.setIfInBounds i low', va.setIfInBounds i (low' + 1), s)
      else .ok (low', 0, lo.setIfInBounds i low', va, s)

/-- The query path through the node `(x, y)` of a `dw × dh` level at offset `off`, with `n`
levels from this one to the root: the ancestors first (recursively), then this node.
Returns this node's final bound and value code. -/
@[specialize] def walk (t : Nat) : Nat → Nat → Nat → Nat → Nat → Nat → Array Nat → Array Nat → σ →
    Except Error (Nat × Nat × Array Nat × Array Nat × σ)
  | 0, _, _, _, _, _, _, _, _ => .error (.malformed loc "empty tag tree")
  | 1, off, dw, _, x, y, lo, va, s => nodeStep next t (off + y * dw + x) 0 lo va s
  | n + 2, off, dw, dh, x, y, lo, va, s =>
    match walk t (n + 1) (off + dw * dh) ((dw + 1) / 2) ((dh + 1) / 2) (x / 2) (y / 2) lo va s with
    | .error e => .error e
    | .ok (low, _, lo, va, s) => nodeStep next t (off + y * dw + x) low lo va s

/-- Query "is the value of leaf `leaf` (row-major) `< t`?" over the bit source `next`,
updating the tree (OpenJPEG `opj_tgt_decode`). -/
def decodeWith (tr : Tree) (s : σ) (leaf t : Nat) : Except Error (Bool × Tree × σ) :=
  if leaf < tr.w * tr.h then
    match walk next t tr.numLevels 0 tr.w tr.h (leaf % tr.w) (leaf / tr.w) tr.low tr.val s with
    | .error e => .error e
    | .ok (_, ve, lo, va, s) => .ok (decide (0 < ve ∧ ve ≤ t), { tr with low := lo, val := va }, s)
  else .error (.malformed loc "tag-tree leaf out of range")

/-- Tries thresholds `t, t + 1, …` (at most `n` of them) until the leaf is known to be below
the threshold; returns its value. -/
def valueLoop (leaf : Nat) : Nat → Nat → Tree → σ → Except Error (Nat × Tree × σ)
  | 0, _, _, _ => .error (.malformed loc "tag-tree value exceeds its bound")
  | n + 1, t, tr, s =>
    match decodeWith next tr s leaf t with
    | .error e => .error e
    | .ok (b, tr, s) => if b then .ok (t - 1, tr, s) else valueLoop leaf n (t + 1) tr s

/-- Decodes the exact value of a leaf known to be `≤ maxValue` (OpenJPEG's zero-bit-plane
loop `while (!opj_tgt_decode(bio, tree, leaf, i)) ++i`, thresholds `0, 1, …`); a larger
value is `malformed`. -/
def decodeValueWith (tr : Tree) (s : σ) (leaf maxValue : Nat) : Except Error (Nat × Tree × σ) :=
  valueLoop next leaf (maxValue + 2) 0 tr s

end Generic

/-- One bit of a packet header (B.10.1) as a `Bool`. -/
@[inline] def bitNext (b : BitReader) : Except Error (Bool × BitReader) :=
  match b.bit with
  | .error e => .error e
  | .ok (x, b) => .ok (x != 0, b)

/-- Query "is the value of leaf `leaf` `< threshold`?" reading packet-header bits
(code-block inclusion, B.10.4: `threshold = layer + 1`). -/
def decode (tr : Tree) (br : BitReader) (leaf threshold : Nat) :
    Except Error (Bool × Tree × BitReader) :=
  decodeWith bitNext tr br leaf threshold

/-- The exact value of a leaf, at most `maxValue` (number of zero bit-planes, B.10.5). -/
def decodeValue (tr : Tree) (br : BitReader) (leaf maxValue : Nat) :
    Except Error (Nat × Tree × BitReader) :=
  decodeValueWith bitNext tr br leaf maxValue

end JPEG2000.TagTree
