import JPEG2000.TagTree

/-!
# Tag trees (T.800 B.10.2): specification, reference encoder, theorem C4

Plan.md §4 (theorem C4: "tag-tree decoding inverts encoding; values are monotone down the
tree"), §5.1 (spec / implementation / equivalence), §5.2 "Tier-2", §5.3 (reference encoder);
ITU-T T.800 B.10.2 (tag trees), B.10.4 (inclusion, threshold `layer + 1`), B.10.5 (zero
bit-planes, exact value).

* **Tree.** `value w h v k x y` is the node `(x, y)` of level `k` of the tag tree over the
  leaf array `v` (`w × h`): level 0 is `v`, a node of level `k + 1` is the minimum of its
  children `(2x + i, 2y + j)` that lie in level `k` (`dimAt w k × dimAt h k`).
  `value_monotone`: a parent is `≤` each of its children.
* **Decoder.** The state maps each node `(k, x, y)` to its lower bound and its value once
  known (`NodeSt`). `walk` processes the path of a leaf root first (it recurses to the parent,
  then handles the node); `nodeDec` is B.10.2's procedure at one node, over a list of bits.
  `query` answers "is the leaf `< t`?", `exact` finds the value by thresholds `0, 1, …`
  (OpenJPEG's zero-bit-plane loop), `decodeAll` runs a list of `Query`s.
* **Reference encoder.** `encodeAll` runs the same walk with the true node values, emitting
  at each read `1` iff the running bound equals the node's value.
* **C4.** `decode_encode`: decoding `encodeAll … ++ rest` answers every query correctly
  (`trueAnswer`: `v x y < t`, resp. `v x y`) and leaves `rest`, for every leaf array, every
  in-range query list (exact queries with a bound `≥` the value) and any further bits.
  `value_monotone` is C4's second half.
* **Fast = spec.** `fast_decode_eq` / `fast_decodeValue_eq`: the flat-array decoder
  `JPEG2000.TagTree.decodeWith` instantiated with a list-of-bits source agrees with `query` /
  `exact` (same answers, same remaining bits, same errors) for every bit list, through the
  state relation `Rel` (`create` starts related: `create_rel`).

The bits are a `List Bool`, i.e. after B.10.1 un-stuffing. Production code reads them from a
`Bytes.BitReader` (`TagTree.decode`); relating the `BitReader` to the bit list of its bytes is
B.10.1's business, not proved here (the tests check it on packed, stuffed byte strings).
-/

namespace JPEG2000.Spec.TagTree

/-! ## The tree -/

/-- Width (or height) of level `k` of the tag tree over a side of `w` leaves:
`⌈w / 2^k⌉`, by repeated halving. -/
def dimAt (w : Nat) : Nat → Nat
  | 0 => w
  | k + 1 => (dimAt w k + 1) / 2

/-- Number of levels of the tag tree over `dw × dh` leaves (`fuel` bounds the halvings; a
level with at most one node is the top). -/
def levelsAux : Nat → Nat → Nat → Nat
  | 0, _, _ => 1
  | fuel + 1, dw, dh =>
    if dw ≤ 1 ∧ dh ≤ 1 then 1 else levelsAux fuel ((dw + 1) / 2) ((dh + 1) / 2) + 1

/-- Number of levels of the tag tree over a `w × h` leaf array. -/
def levels (w h : Nat) : Nat := levelsAux (w + h) w h

/-- Node `(x, y)` of level `k` of the tag tree over the leaves `v` (`w × h`): `v x y` at
level 0, the minimum of the children inside level `k` at level `k + 1` (T.800 B.10.2). -/
def value (w h : Nat) (v : Nat → Nat → Nat) : Nat → Nat → Nat → Nat
  | 0, x, y => v x y
  | k + 1, x, y =>
    let a := value w h v k (2 * x) (2 * y)
    let a := if 2 * x + 1 < dimAt w k then min a (value w h v k (2 * x + 1) (2 * y)) else a
    let a := if 2 * y + 1 < dimAt h k then min a (value w h v k (2 * x) (2 * y + 1)) else a
    if 2 * x + 1 < dimAt w k ∧ 2 * y + 1 < dimAt h k then
      min a (value w h v k (2 * x + 1) (2 * y + 1)) else a

/-- C4 (monotonicity): every node of the tag tree is `≤` each of its children, i.e. the
parent `(k + 1, x / 2, y / 2)` of a node `(k, x, y)` inside level `k` is not larger. -/
theorem value_monotone (w h : Nat) (v : Nat → Nat → Nat) (k x y : Nat)
    (hx : x < dimAt w k) (hy : y < dimAt h k) :
    value w h v (k + 1) (x / 2) (y / 2) ≤ value w h v k x y := by
  obtain ⟨p, hp⟩ : ∃ p, x = 2 * p ∨ x = 2 * p + 1 := ⟨x / 2, by omega⟩
  obtain ⟨q, hq⟩ : ∃ q, y = 2 * q ∨ y = 2 * q + 1 := ⟨y / 2, by omega⟩
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;>
  · simp only [value, show ∀ a, (2 * a) / 2 = a by omega, show ∀ a, (2 * a + 1) / 2 = a by omega]
    repeat' split
    all_goals omega

/-- `dimAt` at level `k + 1` halves level `k` (rounding up). -/
private theorem dimAt_succ (w k : Nat) : dimAt w (k + 1) = (dimAt w k + 1) / 2 := rfl

/-- The ancestor of an in-range node is in range. -/
private theorem half_lt_dimAt {w k x : Nat} (hx : x < dimAt w k) : x / 2 < dimAt w (k + 1) := by
  rw [dimAt_succ]; omega

/-- A tag tree has at least one level. -/
private theorem levelsAux_pos : ∀ (f dw dh : Nat), 0 < levelsAux f dw dh
  | 0, _, _ => by simp [levelsAux]
  | f + 1, dw, dh => by simp only [levelsAux]; split <;> omega

/-! ## The decoder (B.10.2) over a list of bits -/

/-- Decoding state of one node: its lower bound and, once known, its value. -/
structure NodeSt where
  /-- The node's value is known to be `≥ low`. -/
  low : Nat := 0
  /-- The node's value, once known. -/
  val : Option Nat := none
  deriving DecidableEq, Repr

/-- A node: (level, x, y). -/
abbrev Node := Nat × Nat × Nat

/-- Decoding state of a whole tag tree. -/
abbrev St := Node → NodeSt

/-- The initial state: every value unknown, every bound 0. -/
def init : St := fun _ => {}

/-- Replaces the state of one node. -/
def St.set (s : St) (n : Node) (e : NodeSt) : St := fun m => if m = n then e else s m

/-- The bit loop at a node of unknown value with running bound `low`, at most `n` bits:
`1` → the value is `low`; `0` → `low + 1`. `none` when the bits run out. -/
def readLoop : Nat → Nat → List Bool → Option (Nat × Option Nat × List Bool)
  | 0, low, bs => some (low, none, bs)
  | _ + 1, _, [] => none
  | n + 1, low, b :: bs => if b then some (low, some low, bs) else readLoop n (low + 1) bs

/-- B.10.2 at one node `nd` with threshold `t` and incoming bound `inLow` (the parent's final
bound, `0` at the root): the running bound is `max inLow low`; while it is `< t` and the value
unknown, read bits (`readLoop` with `t - low` steps). Returns the final bound, the value if
known, the new state and the remaining bits. -/
def nodeDec (t : Nat) (nd : Node) (inLow : Nat) (s : St) (bs : List Bool) :
    Option (Nat × Option Nat × St × List Bool) :=
  let low := max inLow (s nd).low
  match (s nd).val with
  | some u => some (low, some u, s.set nd { low, val := some u }, bs)
  | none =>
    match readLoop (t - low) low bs with
    | none => none
    | some (low', vo, bs') => some (low', vo, s.set nd { low := low', val := vo }, bs')

/-- The path of node `(k, x, y)` with `n` levels from level `k` to the root: the ancestors
first (the parent is `(k + 1, x / 2, y / 2)`), then the node itself. -/
def walk (t : Nat) : Nat → Nat → Nat → Nat → St → List Bool →
    Option (Nat × Option Nat × St × List Bool)
  | 0, _, _, _, _, _ => none
  | 1, k, x, y, s, bs => nodeDec t (k, x, y) 0 s bs
  | n + 2, k, x, y, s, bs =>
    match walk t (n + 1) (k + 1) (x / 2) (y / 2) s bs with
    | none => none
    | some (low, _, s, bs) => nodeDec t (k, x, y) low s bs

/-- The answer to "is the value `< t`?" given what is known about it. -/
def answerOf (t : Nat) : Option Nat → Bool
  | some u => decide (u < t)
  | none => false

/-- Query "is leaf `(x, y)` `< t`?" on the tag tree over `w × h` leaves (OpenJPEG
`opj_tgt_decode`); `none` for a leaf out of range or when the bits run out. -/
def query (w h : Nat) (s : St) (x y t : Nat) (bs : List Bool) : Option (Bool × St × List Bool) :=
  if x < w ∧ y < h then
    match walk t (levels w h) 0 x y s bs with
    | none => none
    | some (_, vo, s, bs) => some (answerOf t vo, s, bs)
  else none

/-- Thresholds `t, t + 1, …` (at most `n`) until the leaf is below the threshold. -/
def exactAux (w h x y : Nat) : Nat → Nat → St → List Bool → Option (Nat × St × List Bool)
  | 0, _, _, _ => none
  | n + 1, t, s, bs =>
    match query w h s x y t bs with
    | none => none
    | some (b, s, bs) => if b then some (t - 1, s, bs) else exactAux w h x y n (t + 1) s bs

/-- The exact value of leaf `(x, y)`, known to be `≤ maxValue` (thresholds `0, 1, …`, as
OpenJPEG decodes the number of zero bit-planes). -/
def exact (w h : Nat) (s : St) (x y maxValue : Nat) (bs : List Bool) :
    Option (Nat × St × List Bool) :=
  exactAux w h x y (maxValue + 2) 0 s bs

/-- A tag-tree query: inclusion-style "is leaf `(x, y)` `< t`?", or the exact value of a leaf
known to be `≤ maxValue`. -/
inductive Query where
  /-- Is leaf `(x, y)` `< t`? -/
  | lt (x y t : Nat)
  /-- The value of leaf `(x, y)` (at most `maxValue`). -/
  | exact (x y maxValue : Nat)
  deriving DecidableEq, Repr

/-- The answer to a `Query`. -/
inductive Answer where
  /-- Answer to `Query.lt`. -/
  | lt (b : Bool)
  /-- Answer to `Query.exact`. -/
  | exact (v : Nat)
  deriving DecidableEq, Repr

/-- Runs a list of queries in order, the state carried from one to the next. -/
def decodeAll (w h : Nat) : List Query → St → List Bool → Option (List Answer × St × List Bool)
  | [], s, bs => some ([], s, bs)
  | .lt x y t :: qs, s, bs =>
    match query w h s x y t bs with
    | none => none
    | some (b, s, bs) =>
      match decodeAll w h qs s bs with
      | none => none
      | some (as, s, bs) => some (.lt b :: as, s, bs)
  | .exact x y m :: qs, s, bs =>
    match exact w h s x y m bs with
    | none => none
    | some (u, s, bs) =>
      match decodeAll w h qs s bs with
      | none => none
      | some (as, s, bs) => some (.exact u :: as, s, bs)

/-! ## The reference encoder -/

/-- The encoder's bit loop at a node of true value `tv`: emits `1` when the running bound
reaches `tv`, else `0` and increments it (at most `n` bits). Returns the bits, the final
bound and the value if it became known. -/
def encLoop (tv : Nat) : Nat → Nat → List Bool × Nat × Option Nat
  | 0, low => ([], low, none)
  | n + 1, low =>
    if low = tv then ([true], low, some low)
    else let r := encLoop tv n (low + 1); (false :: r.1, r.2)

/-- The encoder at one node (true value `tv`), mirroring `nodeDec`. -/
def nodeEnc (tv t : Nat) (nd : Node) (inLow : Nat) (s : St) : List Bool × Nat × Option Nat × St :=
  let low := max inLow (s nd).low
  match (s nd).val with
  | some u => ([], low, some u, s.set nd { low, val := some u })
  | none =>
    let r := encLoop tv (t - low) low
    (r.1, r.2.1, r.2.2, s.set nd { low := r.2.1, val := r.2.2 })

/-- The encoder along a path (true node values `tv k x y`), mirroring `walk`. -/
def walkEnc (tv : Nat → Nat → Nat → Nat) (t : Nat) :
    Nat → Nat → Nat → Nat → St → List Bool × Nat × Option Nat × St
  | 0, _, _, _, s => ([], 0, none, s)
  | 1, k, x, y, s => nodeEnc (tv k x y) t (k, x, y) 0 s
  | n + 2, k, x, y, s =>
    let r := walkEnc tv t (n + 1) (k + 1) (x / 2) (y / 2) s
    let r2 := nodeEnc (tv k x y) t (k, x, y) r.2.1 r.2.2.2
    (r.1 ++ r2.1, r2.2)

/-- The encoder for "is leaf `(x, y)` `< t`?": the bits, the answer, the new state. -/
def queryEnc (w h : Nat) (v : Nat → Nat → Nat) (s : St) (x y t : Nat) :
    List Bool × Bool × St :=
  let r := walkEnc (value w h v) t (levels w h) 0 x y s
  (r.1, answerOf t r.2.2.1, r.2.2.2)

/-- The encoder for the exact value of leaf `(x, y)`, mirroring `exactAux`. -/
def exactEnc (w h : Nat) (v : Nat → Nat → Nat) (x y : Nat) :
    Nat → Nat → St → List Bool × Nat × St
  | 0, _, s => ([], 0, s)
  | n + 1, t, s =>
    let r := queryEnc w h v s x y t
    if r.2.1 then (r.1, t - 1, r.2.2)
    else let r2 := exactEnc w h v x y n (t + 1) r.2.2; (r.1 ++ r2.1, r2.2)

/-- The reference encoder for a list of queries on the leaf array `v`: the bits, the answers
(as the decoder will compute them) and the final state. -/
def encodeAll (w h : Nat) (v : Nat → Nat → Nat) : List Query → St → List Bool × List Answer × St
  | [], s => ([], [], s)
  | .lt x y t :: qs, s =>
    let r := queryEnc w h v s x y t
    let r2 := encodeAll w h v qs r.2.2
    (r.1 ++ r2.1, .lt r.2.1 :: r2.2.1, r2.2.2)
  | .exact x y m :: qs, s =>
    let r := exactEnc w h v x y (m + 2) 0 s
    let r2 := encodeAll w h v qs r.2.2
    (r.1 ++ r2.1, .exact r.2.1 :: r2.2.1, r2.2.2)

/-- The correct answer to a query about the leaf array `v`. -/
def trueAnswer (v : Nat → Nat → Nat) : Query → Answer
  | .lt x y t => .lt (decide (v x y < t))
  | .exact x y _ => .exact (v x y)

/-- A query is valid for the `w × h` leaf array `v`: the leaf is in range, and an exact
query's bound covers the value. -/
def Query.Valid (w h : Nat) (v : Nat → Nat → Nat) : Query → Prop
  | .lt x y _ => x < w ∧ y < h
  | .exact x y m => x < w ∧ y < h ∧ v x y ≤ m

/-! ## Round trip: the decoder follows the encoder (independent of the values) -/

/-- The bit loop round trip. -/
private theorem readLoop_encLoop (tv : Nat) (rest : List Bool) :
    ∀ n low, readLoop n low ((encLoop tv n low).1 ++ rest) =
      some ((encLoop tv n low).2.1, (encLoop tv n low).2.2, rest)
  | 0, low => by simp [readLoop, encLoop]
  | n + 1, low => by
    by_cases h : low = tv
    · simp [readLoop, encLoop, h]
    · simp only [encLoop, h, ↓reduceIte, List.cons_append, readLoop, Bool.false_eq_true]
      exact readLoop_encLoop tv rest n (low + 1)

/-- One node: the decoder reproduces the encoder's bound, value and state. -/
private theorem nodeDec_nodeEnc (tv t : Nat) (nd : Node) (inLow : Nat) (s : St) (rest : List Bool) :
    nodeDec t nd inLow s ((nodeEnc tv t nd inLow s).1 ++ rest) =
      some ((nodeEnc tv t nd inLow s).2.1, (nodeEnc tv t nd inLow s).2.2.1,
        (nodeEnc tv t nd inLow s).2.2.2, rest) := by
  cases hv : (s nd).val with
  | some u => simp [nodeDec, nodeEnc, hv]
  | none => simp [nodeDec, nodeEnc, hv, readLoop_encLoop]

/-- A path: the decoder reproduces the encoder's bound, value and state. -/
private theorem walk_walkEnc (tv : Nat → Nat → Nat → Nat) (t : Nat) (rest : List Bool) :
    ∀ n k x y (s : St), 0 < n → walk t n k x y s ((walkEnc tv t n k x y s).1 ++ rest) =
      some ((walkEnc tv t n k x y s).2.1, (walkEnc tv t n k x y s).2.2.1,
        (walkEnc tv t n k x y s).2.2.2, rest)
  | 0, _, _, _, _, h => absurd h (Nat.lt_irrefl 0)
  | 1, k, x, y, s, _ => by simp only [walk, walkEnc]; exact nodeDec_nodeEnc _ _ _ _ _ _
  | n + 2, k, x, y, s, _ => by
    simp only [walk, walkEnc, List.append_assoc]
    rw [walk_walkEnc tv t _ (n + 1) (k + 1) (x / 2) (y / 2) s (by omega)]
    exact nodeDec_nodeEnc _ _ _ _ _ _

/-- A query: the decoder reproduces the encoder's answer and state. -/
private theorem query_queryEnc (w h : Nat) (v : Nat → Nat → Nat) (s : St) (x y t : Nat)
    (rest : List Bool) (hx : x < w) (hy : y < h) :
    query w h s x y t ((queryEnc w h v s x y t).1 ++ rest) =
      some ((queryEnc w h v s x y t).2.1, (queryEnc w h v s x y t).2.2, rest) := by
  simp only [query, hx, hy, and_self, ↓reduceIte, queryEnc]
  rw [walk_walkEnc _ _ _ (levels w h) _ _ _ _ (levelsAux_pos _ _ _)]

/-! ## Correctness: the encoder's state never contradicts the true values -/

/-- The invariant: every in-range node's bound is at most its true value, and a known value
is the true value. -/
def Inv (w h : Nat) (v : Nat → Nat → Nat) (s : St) : Prop :=
  ∀ k x y, x < dimAt w k → y < dimAt h k →
    (s (k, x, y)).low ≤ value w h v k x y ∧ ∀ u, (s (k, x, y)).val = some u → u = value w h v k x y

/-- The initial state satisfies the invariant. -/
theorem inv_init (w h : Nat) (v : Nat → Nat → Nat) : Inv w h v init := by
  intro k x y _ _; simp [init]

/-- Setting an in-range node to an entry consistent with its true value keeps the
invariant. -/
private theorem inv_set {w h : Nat} {v : Nat → Nat → Nat} {s : St} {k x y : Nat} {e : NodeSt}
    (hs : Inv w h v s) (hl : e.low ≤ value w h v k x y)
    (hv : ∀ u, e.val = some u → u = value w h v k x y) : Inv w h v (s.set (k, x, y) e) := by
  intro k' x' y' hx' hy'
  simp only [St.set]
  split
  · next heq =>
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    exact ⟨hl, hv⟩
  · exact hs k' x' y' hx' hy'

/-- The encoder's bit loop from a bound `≤ tv`: the final bound is `≤ tv`, a value found is
`tv`, and if none is found the bound advanced by `n`. -/
private theorem encLoop_spec (tv : Nat) : ∀ n low, low ≤ tv →
    (encLoop tv n low).2.1 ≤ tv ∧ (∀ u, (encLoop tv n low).2.2 = some u → u = tv) ∧
      ((encLoop tv n low).2.2 = none → (encLoop tv n low).2.1 = low + n)
  | 0, low, h => by simp [encLoop, h]
  | n + 1, low, h => by
    by_cases he : low = tv
    · simp [encLoop, he]
    · have ih := encLoop_spec tv n (low + 1) (by omega)
      simp only [encLoop, he, ↓reduceIte]
      refine ⟨ih.1, ih.2.1, fun hn => ?_⟩
      have := ih.2.2 hn; omega

/-- One node of the encoder, entered with a bound `≤` the node's true value, keeps the
invariant, ends with a bound `≤` the value, a correct value if known, and a bound `≥ t` if
unknown. -/
private theorem nodeEnc_spec {w h : Nat} {v : Nat → Nat → Nat} {s : St} (t k x y inLow : Nat)
    (hs : Inv w h v s) (hx : x < dimAt w k) (hy : y < dimAt h k)
    (hin : inLow ≤ value w h v k x y) :
    let r := nodeEnc (value w h v k x y) t (k, x, y) inLow s
    Inv w h v r.2.2.2 ∧ r.2.1 ≤ value w h v k x y ∧
      (∀ u, r.2.2.1 = some u → u = value w h v k x y) ∧ (r.2.2.1 = none → t ≤ r.2.1) := by
  have h0 := hs k x y hx hy
  cases hv : (s (k, x, y)).val with
  | some u =>
    have hu := h0.2 u hv
    simp only [nodeEnc, hv]
    refine ⟨inv_set hs (by simp only; omega) (by simpa using hu), by omega,
      by simpa using hu, by simp⟩
  | none =>
    simp only [nodeEnc, hv]
    have hl := encLoop_spec (value w h v k x y) (t - max inLow (s (k, x, y)).low)
      (max inLow (s (k, x, y)).low) (by omega)
    refine ⟨inv_set hs hl.1 hl.2.1, hl.1, hl.2.1, fun hn => ?_⟩
    have := hl.2.2 hn; omega

/-- A path of the encoder (`n ≥ 1` levels, an in-range node) keeps the invariant and ends at
the node with the conclusions of `nodeEnc_spec`. Uses `value_monotone`: the parent's final
bound is `≤` the parent's value `≤` the node's value. -/
private theorem walkEnc_spec {w h : Nat} {v : Nat → Nat → Nat} (t : Nat) :
    ∀ n k x y (s : St), 0 < n → Inv w h v s → x < dimAt w k → y < dimAt h k →
      let r := walkEnc (value w h v) t n k x y s
      Inv w h v r.2.2.2 ∧ r.2.1 ≤ value w h v k x y ∧
        (∀ u, r.2.2.1 = some u → u = value w h v k x y) ∧ (r.2.2.1 = none → t ≤ r.2.1)
  | 0, _, _, _, _, h, _, _, _ => absurd h (Nat.lt_irrefl 0)
  | 1, k, x, y, s, _, hs, hx, hy => by
    simp only [walkEnc]; exact nodeEnc_spec t k x y 0 hs hx hy (Nat.zero_le _)
  | n + 2, k, x, y, s, _, hs, hx, hy => by
    have ih := walkEnc_spec t (n + 1) (k + 1) (x / 2) (y / 2) s (by omega) hs
      (half_lt_dimAt hx) (half_lt_dimAt hy)
    have hm := value_monotone w h v k x y hx hy
    simp only [walkEnc]
    exact nodeEnc_spec t k x y _ ih.1 hx hy (Nat.le_trans ih.2.1 hm)

/-- The encoder's answer to "is leaf `(x, y)` `< t`?" is correct and the invariant is kept. -/
private theorem queryEnc_spec {w h : Nat} {v : Nat → Nat → Nat} {s : St} {x y : Nat} (t : Nat)
    (hs : Inv w h v s) (hx : x < w) (hy : y < h) :
    (queryEnc w h v s x y t).2.1 = decide (v x y < t) ∧ Inv w h v (queryEnc w h v s x y t).2.2 := by
  have hw := walkEnc_spec (v := v) t (levels w h) 0 x y s (levelsAux_pos _ _ _) hs hx hy
  simp only [queryEnc]
  refine ⟨?_, hw.1⟩
  revert hw
  generalize walkEnc (value w h v) t (levels w h) 0 x y s = r
  intro hw
  obtain ⟨_, hl, hv, hn⟩ := hw
  cases hr : r.2.2.1 with
  | some u => have := hv u hr; simp only [answerOf]; rw [this]; rfl
  | none =>
    have := hn hr
    simp only [answerOf]
    have : ¬ v x y < t := by simp only [value] at hl; omega
    simp [this]

/-- The encoder's exact-value loop recovers the value when the fuel covers it, keeping the
invariant. -/
private theorem exactEnc_spec {w h : Nat} {v : Nat → Nat → Nat} {x y : Nat} (hx : x < w) (hy : y < h) :
    ∀ n t (s : St), Inv w h v s → t ≤ v x y + 1 → v x y + 2 ≤ n + t →
      (exactEnc w h v x y n t s).2.1 = v x y ∧ Inv w h v (exactEnc w h v x y n t s).2.2
  | 0, t, s, _, h1, h2 => by omega
  | n + 1, t, s, hs, h1, h2 => by
    have hq := queryEnc_spec t hs hx hy
    simp only [exactEnc]
    split
    · next hb =>
      rw [hq.1] at hb
      have : v x y < t := by simpa using hb
      exact ⟨show t - 1 = v x y by omega, hq.2⟩
    · next hb =>
      rw [hq.1] at hb
      have : ¬ v x y < t := by simpa using hb
      exact exactEnc_spec hx hy n (t + 1) _ hq.2 (by omega) (by omega)

/-- The encoder's answers to valid queries are the true answers; the invariant is kept. -/
theorem encodeAll_spec {w h : Nat} {v : Nat → Nat → Nat} :
    ∀ (qs : List Query) (s : St), (∀ q ∈ qs, q.Valid w h v) → Inv w h v s →
      (encodeAll w h v qs s).2.1 = qs.map (trueAnswer v) ∧ Inv w h v (encodeAll w h v qs s).2.2
  | [], s, _, hs => by simp [encodeAll, hs]
  | .lt x y t :: qs, s, hq, hs => by
    have h1 := hq _ List.mem_cons_self
    simp only [Query.Valid] at h1
    have hr := queryEnc_spec t hs h1.1 h1.2
    have ih := encodeAll_spec qs _ (fun q hm => hq q (List.mem_cons_of_mem _ hm)) hr.2
    simp only [encodeAll, List.map_cons, trueAnswer, hr.1, ih.1]
    exact ⟨trivial, ih.2⟩
  | .exact x y m :: qs, s, hq, hs => by
    have h1 := hq _ List.mem_cons_self
    simp only [Query.Valid] at h1
    have hr := exactEnc_spec h1.1 h1.2.1 (m + 2) 0 s hs (by omega) (by omega)
    have ih := encodeAll_spec qs _ (fun q hm => hq q (List.mem_cons_of_mem _ hm)) hr.2
    simp only [encodeAll, List.map_cons, trueAnswer, hr.1, ih.1]
    exact ⟨trivial, ih.2⟩

/-! ## Round trip for exact values and query lists -/

/-- Exact values: the decoder reproduces the encoder's value and state (when the fuel covers
the value, so that the encoder does not run out). -/
private theorem exactAux_exactEnc {w h : Nat} {v : Nat → Nat → Nat} {x y : Nat} (rest : List Bool)
    (hx : x < w) (hy : y < h) :
    ∀ n t (s : St), Inv w h v s → t ≤ v x y + 1 → v x y + 2 ≤ n + t →
      exactAux w h x y n t s ((exactEnc w h v x y n t s).1 ++ rest) =
        some ((exactEnc w h v x y n t s).2.1, (exactEnc w h v x y n t s).2.2, rest)
  | 0, t, s, _, h1, h2 => by omega
  | n + 1, t, s, hs, h1, h2 => by
    have hq := queryEnc_spec t hs hx hy
    simp only [exactEnc]
    split
    · next hb => simp only [exactAux, query_queryEnc w h v s x y t rest hx hy, hb, ↓reduceIte]
    · next hb =>
      simp only [exactAux, List.append_assoc, query_queryEnc w h v s x y t _ hx hy, hb,
        Bool.false_eq_true, ↓reduceIte]
      rw [hq.1] at hb
      have : ¬ v x y < t := by simpa using hb
      exact exactAux_exactEnc rest hx hy n (t + 1) _ hq.2 (by omega) (by omega)

/-- A list of valid queries: the decoder reproduces the encoder's answers and state. -/
theorem decodeAll_encodeAll {w h : Nat} {v : Nat → Nat → Nat} (rest : List Bool) :
    ∀ (qs : List Query) (s : St), (∀ q ∈ qs, q.Valid w h v) → Inv w h v s →
      decodeAll w h qs s ((encodeAll w h v qs s).1 ++ rest) =
        some ((encodeAll w h v qs s).2.1, (encodeAll w h v qs s).2.2, rest)
  | [], s, _, _ => by simp [decodeAll, encodeAll]
  | .lt x y t :: qs, s, hq, hs => by
    have h1 := hq _ List.mem_cons_self
    simp only [Query.Valid] at h1
    have hr := queryEnc_spec t hs h1.1 h1.2
    simp only [encodeAll, decodeAll, List.append_assoc, query_queryEnc w h v s x y t _ h1.1 h1.2]
    rw [decodeAll_encodeAll rest qs _ (fun q hm => hq q (List.mem_cons_of_mem _ hm)) hr.2]
  | .exact x y m :: qs, s, hq, hs => by
    have h1 := hq _ List.mem_cons_self
    simp only [Query.Valid] at h1
    have hr := exactEnc_spec h1.1 h1.2.1 (m + 2) 0 s hs (by omega) (by omega)
    simp only [encodeAll, decodeAll, exact, List.append_assoc,
      exactAux_exactEnc _ h1.1 h1.2.1 (m + 2) 0 s hs (by omega) (by omega)]
    rw [decodeAll_encodeAll rest qs _ (fun q hm => hq q (List.mem_cons_of_mem _ hm)) hr.2]

/-- **C4 (tag-tree decoding inverts encoding).** For every `w × h` leaf array `v`, every list
of valid queries `qs` (leaves in range; exact queries with a bound `≥` the value), every
state `s` consistent with `v` (e.g. `init`, `inv_init`) and any following bits `rest`:
decoding the reference encoder's bits answers every query correctly — `v x y < t` for
`Query.lt`, the value `v x y` for `Query.exact` — and leaves exactly `rest`, in the
encoder's state. -/
theorem decode_encode (w h : Nat) (v : Nat → Nat → Nat) (qs : List Query) (s : St)
    (rest : List Bool) (hq : ∀ q ∈ qs, q.Valid w h v) (hs : Inv w h v s) :
    decodeAll w h qs s ((encodeAll w h v qs s).1 ++ rest) =
      some (qs.map (trueAnswer v), (encodeAll w h v qs s).2.2, rest) := by
  rw [decodeAll_encodeAll rest qs s hq hs, (encodeAll_spec qs s hq hs).1]

/-- C4 from a fresh tree: decoding the encoder's bits for valid queries returns the true
answers. -/
theorem decode_encode_init (w h : Nat) (v : Nat → Nat → Nat) (qs : List Query)
    (rest : List Bool) (hq : ∀ q ∈ qs, q.Valid w h v) :
    (decodeAll w h qs init ((encodeAll w h v qs init).1 ++ rest)).map (·.1) =
      some (qs.map (trueAnswer v)) := by
  rw [decode_encode w h v qs init rest hq (inv_init w h v)]; rfl

/-! ## The fast decoder equals the specification decoder

`JPEG2000.TagTree` stores node `(k, x, y)` at the flat index `idx w h k x y`; `Rel` says that
the arrays hold exactly the spec state of every node of the tree's levels. With the bits
taken from a list (`listNext`), every step of the fast decoder corresponds to the spec step
(`Corr`), and the error is always "out of bits" (`eBits`). -/

/-- First flat index of level `k`. -/
def off (w h : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => off w h k + dimAt w k * dimAt h k

/-- Flat index of node `(k, x, y)`: levels in order, rows in order within a level. -/
def idx (w h k x y : Nat) : Nat := off w h k + y * dimAt w k + x

/-- How the fast decoder codes a node's value: `0` unknown, `v + 1` known `v`. -/
def encV : Option Nat → Nat
  | none => 0
  | some u => u + 1

/-- The error of a list bit source that has run out. -/
def eBits : Error := .truncated (.at .tier2) "tag-tree bits"

/-- A list of bits as a bit source for `JPEG2000.TagTree.decodeWith`. -/
def listNext : List Bool → Except Error (Bool × List Bool)
  | [] => .error eBits
  | b :: bs => .ok (b, bs)

/-- The arrays `lo`, `va` hold the state `s` of every node of the first `L` levels. -/
def RelA (w h L : Nat) (lo va : Array Nat) (s : St) : Prop :=
  ∀ k x y, k < L → x < dimAt w k → y < dimAt h k →
    lo[idx w h k x y]? = some (s (k, x, y)).low ∧ va[idx w h k x y]? = some (encV (s (k, x, y)).val)

/-- A fast tree represents the spec state `s`: its level count is `levels w h` and its
arrays hold `s`. -/
def Rel (tr : JPEG2000.TagTree.Tree) (s : St) : Prop :=
  tr.numLevels = levels tr.w tr.h ∧ RelA tr.w tr.h tr.numLevels tr.low tr.val s

/-- A fast step result corresponds to a spec step result: both fail (the fast one with
`eBits`), or both succeed with the same bound, value, remaining bits, and related states. -/
def Corr (w h L : Nat) : Except Error (Nat × Nat × Array Nat × Array Nat × List Bool) →
    Option (Nat × Option Nat × St × List Bool) → Prop
  | .error e, none => e = eBits
  | .ok (l', ve, lo', va', bs''), some (l, vo, s', bs') =>
    l' = l ∧ ve = encV vo ∧ bs'' = bs' ∧ RelA w h L lo' va' s'
  | _, _ => False

/-- Within a level, the flat index stays below the next level's offset. -/
private theorem idx_lt_off_succ {w h k x y : Nat} (hx : x < dimAt w k) (hy : y < dimAt h k) :
    idx w h k x y < off w h (k + 1) := by
  simp only [idx, off]
  have : (y + 1) * dimAt w k ≤ dimAt h k * dimAt w k := Nat.mul_le_mul_right _ hy
  rw [Nat.succ_mul, Nat.mul_comm (dimAt h k)] at this
  omega

/-- Level offsets are monotone. -/
private theorem off_mono (w h : Nat) {k k' : Nat} (hk : k ≤ k') : off w h k ≤ off w h k' := by
  induction k' with
  | zero => have : k = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ k' ih =>
    by_cases he : k = k' + 1
    · subst he; exact Nat.le_refl _
    · have := ih (by omega); simp only [off]; omega

/-- Row-major positions inside one level are distinct. -/
private theorem rowMajor_inj {d x y x' y' : Nat} (hx : x < d) (hx' : x' < d)
    (he : y * d + x = y' * d + x') : x = x' ∧ y = y' := by
  have hyy : y = y' := by
    rcases Nat.lt_trichotomy y y' with hl | hl | hl
    · have : (y + 1) * d ≤ y' * d := Nat.mul_le_mul_right _ hl
      rw [Nat.succ_mul] at this; omega
    · exact hl
    · have : (y' + 1) * d ≤ y * d := Nat.mul_le_mul_right _ hl
      rw [Nat.succ_mul] at this; omega
  subst hyy; exact ⟨by omega, rfl⟩

/-- The flat index is injective on in-range nodes. -/
theorem idx_inj {w h k x y k' x' y' : Nat} (hx : x < dimAt w k) (hy : y < dimAt h k)
    (hx' : x' < dimAt w k') (hy' : y' < dimAt h k')
    (he : idx w h k x y = idx w h k' x' y') : k = k' ∧ x = x' ∧ y = y' := by
  have h1 := idx_lt_off_succ (h := h) hx hy
  have h2 := idx_lt_off_succ (h := h) hx' hy'
  have hkk : k = k' := by
    rcases Nat.lt_trichotomy k k' with hl | hl | hl
    · have := off_mono w h (show k + 1 ≤ k' by omega)
      simp only [idx] at he h1 h2; omega
    · exact hl
    · have := off_mono w h (show k' + 1 ≤ k by omega)
      simp only [idx] at he h1 h2; omega
  subst hkk
  simp only [idx] at he
  have := rowMajor_inj (y := y) (y' := y') hx hx' (by omega)
  exact ⟨rfl, this.1, this.2⟩

/-- Updating the arrays at one node's index (and nowhere else of relevance) to a new entry
corresponds to `St.set`. -/
private theorem relA_set {w h L : Nat} {lo va lo' va' : Array Nat} {s : St} {k x y : Nat} {e : NodeSt}
    (hR : RelA w h L lo va s) (hx : x < dimAt w k) (hy : y < dimAt h k)
    (hlo : ∀ j, j ≠ idx w h k x y → lo'[j]? = lo[j]?) (hlo' : lo'[idx w h k x y]? = some e.low)
    (hva : ∀ j, j ≠ idx w h k x y → va'[j]? = va[j]?)
    (hva' : va'[idx w h k x y]? = some (encV e.val)) :
    RelA w h L lo' va' (s.set (k, x, y) e) := by
  intro k' x' y' hk' hx' hy'
  simp only [St.set]
  split
  · next heq =>
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    exact ⟨hlo', hva'⟩
  · next hne =>
    have hi : idx w h k' x' y' ≠ idx w h k x y := by
      intro he
      have := idx_inj hx' hy' hx hy he
      apply hne; rw [this.1, this.2.1, this.2.2]
    rw [hlo _ hi, hva _ hi]
    exact hR k' x' y' hk' hx' hy'

/-- The fast bit loop over a list is the spec bit loop. -/
private theorem readLoop_fast : ∀ n low (bs : List Bool),
    JPEG2000.TagTree.readLoop listNext n low bs =
      match readLoop n low bs with
      | none => .error eBits
      | some (l, vo, bs') => .ok (l, vo.isSome, bs')
  | 0, low, bs => by simp [JPEG2000.TagTree.readLoop, readLoop]
  | n + 1, low, [] => by simp [JPEG2000.TagTree.readLoop, readLoop, listNext]
  | n + 1, low, b :: bs => by
    cases b
    · simp only [JPEG2000.TagTree.readLoop, readLoop, listNext, Bool.false_eq_true, ↓reduceIte]
      exact readLoop_fast n (low + 1) bs
    · simp [JPEG2000.TagTree.readLoop, readLoop, listNext]

/-- A value found by the bit loop is the final bound. -/
private theorem readLoop_val : ∀ n low (bs : List Bool) l vo bs',
    readLoop n low bs = some (l, vo, bs') → vo = none ∨ vo = some l
  | 0, low, bs, l, vo, bs', h => by simp [readLoop] at h; exact Or.inl h.2.1.symm
  | n + 1, low, [], l, vo, bs', h => by simp [readLoop] at h
  | n + 1, low, b :: bs, l, vo, bs', h => by
    cases b
    · simp only [readLoop, Bool.false_eq_true, ↓reduceIte] at h
      exact readLoop_val n (low + 1) bs l vo bs' h
    · simp only [readLoop, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h; exact Or.inr rfl

/-- One node: the fast step corresponds to `nodeDec`. -/
private theorem nodeStep_corr {w h L : Nat} {lo va : Array Nat} {s : St} {k x y : Nat}
    (t inLow : Nat) (bs : List Bool) (hR : RelA w h L lo va s) (hk : k < L)
    (hx : x < dimAt w k) (hy : y < dimAt h k) :
    Corr w h L (JPEG2000.TagTree.nodeStep listNext t (idx w h k x y) inLow lo va bs)
      (nodeDec t (k, x, y) inLow s bs) := by
  obtain ⟨hl, hv⟩ := hR k x y hk hx hy
  have hlsz : idx w h k x y < lo.size := by
    rcases Nat.lt_or_ge (idx w h k x y) lo.size with h1 | h1
    · exact h1
    · rw [Array.getElem?_eq_none h1] at hl; cases hl
  have hvsz : idx w h k x y < va.size := by
    rcases Nat.lt_or_ge (idx w h k x y) va.size with h1 | h1
    · exact h1
    · rw [Array.getElem?_eq_none h1] at hv; cases hv
  have hlo := fun j (hj : j ≠ idx w h k x y) (a : Nat) =>
    Array.getElem?_setIfInBounds_ne (xs := lo) (a := a) (Ne.symm hj)
  have hva := fun j (hj : j ≠ idx w h k x y) (a : Nat) =>
    Array.getElem?_setIfInBounds_ne (xs := va) (a := a) (Ne.symm hj)
  simp only [JPEG2000.TagTree.nodeStep, nodeDec, Array.getD_eq_getD_getElem?, hl, hv,
    Option.getD_some]
  cases hsv : (s (k, x, y)).val with
  | some u =>
    simp only [encV, bne_iff_ne, ne_eq, Nat.add_one_ne_zero, not_false_eq_true, ↓reduceIte,
      Corr, true_and]
    exact relA_set hR hx hy (fun j hj => hlo j hj _)
      (Array.getElem?_setIfInBounds_self_of_lt hlsz) (fun j _ => rfl) (by rw [hv, hsv])
  | none =>
    simp only [encV, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    rw [readLoop_fast]
    cases hr : readLoop (t - max inLow (s (k, x, y)).low) (max inLow (s (k, x, y)).low) bs with
    | none => simp [Corr]
    | some r =>
      obtain ⟨l, vo, bs'⟩ := r
      rcases readLoop_val _ _ _ _ _ _ hr with rfl | rfl
      · simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Corr, true_and]
        refine ⟨rfl, relA_set hR hx hy (fun j hj => hlo j hj _)
          (Array.getElem?_setIfInBounds_self_of_lt hlsz) (fun j _ => rfl) ?_⟩
        rw [hv, hsv]
      · simp only [Option.isSome_some, ↓reduceIte, Corr, encV, true_and]
        exact relA_set hR hx hy (fun j hj => hlo j hj _)
          (Array.getElem?_setIfInBounds_self_of_lt hlsz) (fun j hj => hva j hj _)
          (Array.getElem?_setIfInBounds_self_of_lt hvsz)

/-- A path: the fast `walk` (offset, dimensions computed level by level) corresponds to the
spec `walk`, for `n ≥ 1` levels from an in-range node of level `k` with `k + n ≤ L`. -/
theorem walk_corr {w h L : Nat} (t : Nat) : ∀ n k x y (lo va : Array Nat) (s : St)
    (bs : List Bool), 0 < n → k + n ≤ L → RelA w h L lo va s → x < dimAt w k → y < dimAt h k →
    Corr w h L
      (JPEG2000.TagTree.walk listNext t n (off w h k) (dimAt w k) (dimAt h k) x y lo va bs)
      (walk t n k x y s bs)
  | 0, _, _, _, _, _, _, _, h, _, _, _, _ => absurd h (Nat.lt_irrefl 0)
  | 1, k, x, y, lo, va, s, bs, _, hk, hR, hx, hy => by
    simp only [JPEG2000.TagTree.walk, walk]
    exact nodeStep_corr t 0 bs hR (by omega) hx hy
  | n + 2, k, x, y, lo, va, s, bs, _, hk, hR, hx, hy => by
    have ih := walk_corr t (n + 1) (k + 1) (x / 2) (y / 2) lo va s bs (by omega) (by omega) hR
      (half_lt_dimAt hx) (half_lt_dimAt hy)
    simp only [JPEG2000.TagTree.walk, walk]
    simp only [off, dimAt] at ih
    revert ih
    cases JPEG2000.TagTree.walk listNext t (n + 1) (off w h k + dimAt w k * dimAt h k)
        ((dimAt w k + 1) / 2) ((dimAt h k + 1) / 2) (x / 2) (y / 2) lo va bs with
    | error e =>
      cases walk t (n + 1) (k + 1) (x / 2) (y / 2) s bs with
      | none => intro ih; simpa [Corr] using ih
      | some r => intro ih; simp [Corr] at ih
    | ok r =>
      obtain ⟨l', ve, lo', va', bs''⟩ := r
      cases walk t (n + 1) (k + 1) (x / 2) (y / 2) s bs with
      | none => intro ih; simp [Corr] at ih
      | some r =>
        obtain ⟨l, vo, s', bs'⟩ := r
        intro ih
        simp only [Corr] at ih
        obtain ⟨rfl, -, rfl, hR'⟩ := ih
        exact nodeStep_corr t _ _ hR' (by omega) hx hy

/-- The fast decoder's level count is the spec's. -/
private theorem levelsAux_fast : ∀ f dw dh, JPEG2000.TagTree.levelsAux f dw dh = levelsAux f dw dh
  | 0, _, _ => rfl
  | f + 1, dw, dh => by
    simp only [JPEG2000.TagTree.levelsAux, levelsAux, levelsAux_fast f]

/-- The fast decoder's node count over `n` levels from level `k` ends at offset `k + n`. -/
private theorem totalAux_off (w h : Nat) : ∀ n k,
    off w h k + JPEG2000.TagTree.totalAux n (dimAt w k) (dimAt h k) = off w h (k + n)
  | 0, k => by simp [JPEG2000.TagTree.totalAux]
  | n + 1, k => by
    have ih := totalAux_off w h n (k + 1)
    rw [show k + (n + 1) = (k + 1) + n by omega, ← ih]
    simp only [JPEG2000.TagTree.totalAux, off, dimAt]; omega

/-- A tree made by `create` represents the initial spec state. -/
theorem create_rel {L : Limits} {w h : Nat} {tr : JPEG2000.TagTree.Tree}
    (hc : JPEG2000.TagTree.create L w h = .ok tr) : Rel tr init ∧ tr.w = w ∧ tr.h = h := by
  simp only [JPEG2000.TagTree.create, Limits.check, Limits.checkLe, bind, Except.bind, pure,
    Except.pure] at hc
  by_cases h1 : w * h ≤ L.bound .codeBlocks
  · by_cases h2 : JPEG2000.TagTree.totalAux (JPEG2000.TagTree.levels w h) w h ≤ 4 * L.maxCodeBlocks
    · simp only [h1, h2, ↓reduceIte] at hc
      cases hc
      refine ⟨⟨by simp [JPEG2000.TagTree.levels, levels, levelsAux_fast], ?_⟩, rfl, rfl⟩
      intro k x y hk hx hy
      dsimp only at hk hx hy ⊢
      have h1 := idx_lt_off_succ (h := h) hx hy
      have h2 := off_mono w h (show k + 1 ≤ JPEG2000.TagTree.levels w h by omega)
      have h3 := totalAux_off w h (JPEG2000.TagTree.levels w h) 0
      simp only [off, dimAt, Nat.zero_add] at h3
      have hi : idx w h k x y < JPEG2000.TagTree.totalAux (JPEG2000.TagTree.levels w h) w h := by
        omega
      simp [hi, init, encV]
    · simp [h1, h2] at hc
  · simp [h1] at hc

/-- The fast answer code agrees with `answerOf`. -/
private theorem answer_encV (t : Nat) (vo : Option Nat) :
    decide (0 < encV vo ∧ encV vo ≤ t) = answerOf t vo := by
  cases vo <;> simp [encV, answerOf]; omega

/-- **Fast = spec (queries).** For a fast tree representing the spec state `s` and any list
of bits, `JPEG2000.TagTree.decodeWith` on an in-range leaf (row-major index `leaf`) fails
exactly when the spec `query` does (with "out of bits"), and otherwise returns the same
answer and remaining bits and a tree representing the spec's new state. -/
theorem fast_decode_eq (tr : JPEG2000.TagTree.Tree) (s : St) (hR : Rel tr s) (bs : List Bool)
    (leaf t : Nat) (hl : leaf < tr.w * tr.h) :
    match query tr.w tr.h s (leaf % tr.w) (leaf / tr.w) t bs with
    | none => JPEG2000.TagTree.decodeWith listNext tr bs leaf t = .error eBits
    | some (b, s', bs') => ∃ tr', JPEG2000.TagTree.decodeWith listNext tr bs leaf t = .ok (b, tr', bs') ∧
        Rel tr' s' ∧ tr'.w = tr.w ∧ tr'.h = tr.h := by
  have hw : 0 < tr.w := by
    rcases Nat.eq_zero_or_pos tr.w with h0 | h0
    · rw [h0, Nat.zero_mul] at hl; omega
    · exact h0
  have hx : leaf % tr.w < tr.w := Nat.mod_lt _ hw
  have hy : leaf / tr.w < tr.h := (Nat.div_lt_iff_lt_mul hw).mpr (by rw [Nat.mul_comm]; exact hl)
  have hc := walk_corr t tr.numLevels 0 (leaf % tr.w) (leaf / tr.w) tr.low tr.val s bs
    (by rw [hR.1]; exact levelsAux_pos _ _ _) (by omega) hR.2 hx hy
  simp only [off, dimAt] at hc
  simp only [JPEG2000.TagTree.decodeWith, hl, ↓reduceIte, query, hx, hy, and_self, ← hR.1]
  revert hc
  cases JPEG2000.TagTree.walk listNext t tr.numLevels 0 tr.w tr.h (leaf % tr.w) (leaf / tr.w)
      tr.low tr.val bs with
  | error e =>
    cases walk t tr.numLevels 0 (leaf % tr.w) (leaf / tr.w) s bs with
    | none => intro hc; simp only [Corr] at hc; simp [hc]
    | some r => intro hc; simp [Corr] at hc
  | ok r =>
    obtain ⟨l', ve, lo', va', bs''⟩ := r
    cases walk t tr.numLevels 0 (leaf % tr.w) (leaf / tr.w) s bs with
    | none => intro hc; simp [Corr] at hc
    | some r =>
      obtain ⟨l, vo, s', bs'⟩ := r
      intro hc
      simp only [Corr] at hc
      obtain ⟨-, rfl, rfl, hR'⟩ := hc
      exact ⟨{ tr with low := lo', val := va' }, by rw [← answer_encV], ⟨hR.1, hR'⟩, rfl, rfl⟩

/-- Fast = spec for the exact-value loop (any fuel `n`, any start threshold). -/
private theorem valueLoop_eq (leaf : Nat) : ∀ n t (tr : JPEG2000.TagTree.Tree) (s : St) (bs : List Bool),
    Rel tr s → leaf < tr.w * tr.h →
    match exactAux tr.w tr.h (leaf % tr.w) (leaf / tr.w) n t s bs with
    | none => ∃ e, JPEG2000.TagTree.valueLoop listNext leaf n t tr bs = .error e
    | some (u, s', bs') => ∃ tr', JPEG2000.TagTree.valueLoop listNext leaf n t tr bs = .ok (u, tr', bs') ∧
        Rel tr' s' ∧ tr'.w = tr.w ∧ tr'.h = tr.h
  | 0, t, tr, s, bs, _, _ => by simp [exactAux, JPEG2000.TagTree.valueLoop]
  | n + 1, t, tr, s, bs, hR, hl => by
    have hq := fast_decode_eq tr s hR bs leaf t hl
    simp only [exactAux, JPEG2000.TagTree.valueLoop]
    revert hq
    cases query tr.w tr.h s (leaf % tr.w) (leaf / tr.w) t bs with
    | none => intro hq; simp [hq]
    | some r =>
      obtain ⟨b, s', bs'⟩ := r
      intro hq
      obtain ⟨tr', hd, hR', hw', hh'⟩ := hq
      rw [hd]
      cases b
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have ih := valueLoop_eq leaf n (t + 1) tr' s' bs' hR' (by rw [hw', hh']; exact hl)
        rw [hw', hh'] at ih
        revert ih
        cases exactAux tr.w tr.h (leaf % tr.w) (leaf / tr.w) n (t + 1) s' bs' with
        | none => exact id
        | some r =>
          obtain ⟨u, s'', bs''⟩ := r
          intro ⟨tr'', h1, h2, h3, h4⟩
          exact ⟨tr'', h1, h2, h3, h4⟩
      · simp only [↓reduceIte]
        exact ⟨tr', rfl, hR', hw', hh'⟩

/-- **Fast = spec (exact values).** `JPEG2000.TagTree.decodeValueWith` over a list of bits
agrees with the spec `exact`: both fail together, or return the same value and remaining
bits with related states. -/
theorem fast_decodeValue_eq (tr : JPEG2000.TagTree.Tree) (s : St) (hR : Rel tr s)
    (bs : List Bool) (leaf maxValue : Nat) (hl : leaf < tr.w * tr.h) :
    match exact tr.w tr.h s (leaf % tr.w) (leaf / tr.w) maxValue bs with
    | none => ∃ e, JPEG2000.TagTree.decodeValueWith listNext tr bs leaf maxValue = .error e
    | some (u, s', bs') => ∃ tr', JPEG2000.TagTree.decodeValueWith listNext tr bs leaf maxValue =
        .ok (u, tr', bs') ∧ Rel tr' s' ∧ tr'.w = tr.w ∧ tr'.h = tr.h :=
  valueLoop_eq leaf (maxValue + 2) 0 tr s bs hR hl

end JPEG2000.Spec.TagTree
