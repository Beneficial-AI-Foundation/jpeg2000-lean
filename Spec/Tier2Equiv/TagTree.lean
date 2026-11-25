import Spec.Tier2Equiv.Bits

/-!
# Tier-2 equivalence, layer (b): the fast tag-tree decoder over the bit reader
(Plan.md §4 C4, C9, §5.1; T.800 B.10.2, B.10.4, B.10.5)

Task 7.1b. `JPEG2000.TagTree.decodeWith` is generic in its bit source. Any source whose
states `s` (under an invariant `I`) deliver the bits `ρ s` (`NextSim`) runs every step of the
tag-tree decoder exactly as the list source `Spec.TagTree.listNext` over `ρ s` does (`Sim`):
both fail, or both succeed with the same results and the list result's rest is `ρ` of the
state. Instantiated with the packet-header reader (`BitReader`, `rem`, layer (a)) and
composed with `Spec.TagTree.fast_decode_eq`, the fast tag-tree decoder over the bit reader is
the spec decoder over the un-stuffed bit list (`decode_spec`, `decodeValue_spec`).
-/

namespace JPEG2000.Spec.Tier2Equiv

open JPEG2000 JPEG2000.Bytes JPEG2000.Spec.Tier2

section Generic

variable {σ : Type} (ρ : σ → List Bool) (I : σ → Prop)

/-- A fast result (over states `σ`) and a list result correspond: both fail, or the list
result is the fast one mapped by `f` (the state replaced by its bits) and the fast state
`g x` satisfies `I`. -/
def Sim {X Y : Type} (f : X → Y) (g : X → σ) : Except Error X → Except Error Y → Prop
  | .error _, .error _ => True
  | .ok x, .ok y => y = f x ∧ I (g x)
  | _, _ => False

/-- A bit source `next` simulates the list source on `ρ` under `I`. -/
def NextSim (next : σ → Except Error (Bool × σ)) : Prop :=
  ∀ s, I s → Fol ρ I (· = ·) (next s) (Spec.TagTree.listNext (ρ s))

variable {ρ I} {next : σ → Except Error (Bool × σ)}

/-- The bit loop at one node. -/
theorem readLoop_sim (hN : NextSim ρ I next) : ∀ (n low : Nat) (s : σ), I s →
    Sim I (fun (x : Nat × Bool × σ) => (x.1, x.2.1, ρ x.2.2)) (·.2.2)
      (JPEG2000.TagTree.readLoop next n low s)
      (JPEG2000.TagTree.readLoop Spec.TagTree.listNext n low (ρ s))
  | 0, low, s, hs => by simp only [JPEG2000.TagTree.readLoop]; exact ⟨rfl, hs⟩
  | n + 1, low, s, hs => by
    have h := hN s hs
    simp only [JPEG2000.TagTree.readLoop]
    revert h
    cases next s with
    | error e =>
      cases Spec.TagTree.listNext (ρ s) with
      | error _ => intro _; trivial
      | ok _ => intro h; exact absurd h id
    | ok r =>
      obtain ⟨b, s'⟩ := r
      cases Spec.TagTree.listNext (ρ s) with
      | error _ => intro h; exact absurd h id
      | ok r' =>
        obtain ⟨b', l⟩ := r'
        intro ⟨hb, hl, hs'⟩
        subst hb hl
        cases b
        · exact readLoop_sim hN n (low + 1) s' hs'
        · exact ⟨rfl, hs'⟩

/-- One node of a query. -/
theorem nodeStep_sim (hN : NextSim ρ I next) (t i inLow : Nat) (lo va : Array Nat) (s : σ)
    (hs : I s) :
    Sim I (fun (x : Nat × Nat × Array Nat × Array Nat × σ) => (x.1, x.2.1, x.2.2.1, x.2.2.2.1, ρ x.2.2.2.2))
      (·.2.2.2.2)
      (JPEG2000.TagTree.nodeStep next t i inLow lo va s)
      (JPEG2000.TagTree.nodeStep Spec.TagTree.listNext t i inLow lo va (ρ s)) := by
  simp only [JPEG2000.TagTree.nodeStep]
  split
  · exact ⟨rfl, hs⟩
  · have h := readLoop_sim hN (t - max inLow (lo.getD i 0)) (max inLow (lo.getD i 0)) s hs
    revert h
    cases JPEG2000.TagTree.readLoop next (t - max inLow (lo.getD i 0)) (max inLow (lo.getD i 0)) s with
    | error e =>
      cases JPEG2000.TagTree.readLoop Spec.TagTree.listNext (t - max inLow (lo.getD i 0))
          (max inLow (lo.getD i 0)) (ρ s) with
      | error _ => intro _; trivial
      | ok _ => intro h; exact absurd h id
    | ok r =>
      obtain ⟨l, kn, s'⟩ := r
      cases JPEG2000.TagTree.readLoop Spec.TagTree.listNext (t - max inLow (lo.getD i 0))
          (max inLow (lo.getD i 0)) (ρ s) with
      | error _ => intro h; exact absurd h id
      | ok r' =>
        intro ⟨he, hs'⟩
        subst he
        dsimp only
        split <;> exact ⟨rfl, hs'⟩

/-- A query path. -/
theorem walk_sim (hN : NextSim ρ I next) (t : Nat) : ∀ (n off dw dh x y : Nat) (lo va : Array Nat)
    (s : σ), I s →
    Sim I (fun (x : Nat × Nat × Array Nat × Array Nat × σ) => (x.1, x.2.1, x.2.2.1, x.2.2.2.1, ρ x.2.2.2.2))
      (·.2.2.2.2)
      (JPEG2000.TagTree.walk next t n off dw dh x y lo va s)
      (JPEG2000.TagTree.walk Spec.TagTree.listNext t n off dw dh x y lo va (ρ s))
  | 0, _, _, _, _, _, _, _, _, _ => by simp only [JPEG2000.TagTree.walk]; trivial
  | 1, off, dw, _, x, y, lo, va, s, hs => by
    simp only [JPEG2000.TagTree.walk]; exact nodeStep_sim hN t _ 0 lo va s hs
  | n + 2, off, dw, dh, x, y, lo, va, s, hs => by
    have h := walk_sim hN t (n + 1) (off + dw * dh) ((dw + 1) / 2) ((dh + 1) / 2) (x / 2) (y / 2)
      lo va s hs
    simp only [JPEG2000.TagTree.walk]
    revert h
    cases JPEG2000.TagTree.walk next t (n + 1) (off + dw * dh) ((dw + 1) / 2) ((dh + 1) / 2)
        (x / 2) (y / 2) lo va s with
    | error e =>
      cases JPEG2000.TagTree.walk Spec.TagTree.listNext t (n + 1) (off + dw * dh) ((dw + 1) / 2)
          ((dh + 1) / 2) (x / 2) (y / 2) lo va (ρ s) with
      | error _ => intro _; trivial
      | ok _ => intro h; exact absurd h id
    | ok r =>
      obtain ⟨l, v, lo', va', s'⟩ := r
      cases JPEG2000.TagTree.walk Spec.TagTree.listNext t (n + 1) (off + dw * dh) ((dw + 1) / 2)
          ((dh + 1) / 2) (x / 2) (y / 2) lo va (ρ s) with
      | error _ => intro h; exact absurd h id
      | ok r' =>
        intro ⟨he, hs'⟩
        subst he
        exact nodeStep_sim hN t _ l lo' va' s' hs'

/-- A query (`decodeWith`). -/
theorem decodeWith_sim (hN : NextSim ρ I next) (tr : JPEG2000.TagTree.Tree) (s : σ) (hs : I s)
    (leaf t : Nat) :
    Sim I (fun (x : Bool × JPEG2000.TagTree.Tree × σ) => (x.1, x.2.1, ρ x.2.2)) (·.2.2)
      (JPEG2000.TagTree.decodeWith next tr s leaf t)
      (JPEG2000.TagTree.decodeWith Spec.TagTree.listNext tr (ρ s) leaf t) := by
  simp only [JPEG2000.TagTree.decodeWith]
  split
  · have h := walk_sim hN t tr.numLevels 0 tr.w tr.h (leaf % tr.w) (leaf / tr.w) tr.low tr.val s hs
    revert h
    cases JPEG2000.TagTree.walk next t tr.numLevels 0 tr.w tr.h (leaf % tr.w) (leaf / tr.w)
        tr.low tr.val s with
    | error e =>
      cases JPEG2000.TagTree.walk Spec.TagTree.listNext t tr.numLevels 0 tr.w tr.h (leaf % tr.w)
          (leaf / tr.w) tr.low tr.val (ρ s) with
      | error _ => intro _; trivial
      | ok _ => intro h; exact absurd h id
    | ok r =>
      obtain ⟨l, v, lo', va', s'⟩ := r
      cases JPEG2000.TagTree.walk Spec.TagTree.listNext t tr.numLevels 0 tr.w tr.h (leaf % tr.w)
          (leaf / tr.w) tr.low tr.val (ρ s) with
      | error _ => intro h; exact absurd h id
      | ok r' =>
        intro ⟨he, hs'⟩
        subst he
        exact ⟨rfl, hs'⟩
  · trivial

/-- The exact-value loop. -/
theorem valueLoop_sim (hN : NextSim ρ I next) (leaf : Nat) : ∀ (n t : Nat)
    (tr : JPEG2000.TagTree.Tree) (s : σ), I s →
    Sim I (fun (x : Nat × JPEG2000.TagTree.Tree × σ) => (x.1, x.2.1, ρ x.2.2)) (·.2.2)
      (JPEG2000.TagTree.valueLoop next leaf n t tr s)
      (JPEG2000.TagTree.valueLoop Spec.TagTree.listNext leaf n t tr (ρ s))
  | 0, _, _, _, _ => by simp only [JPEG2000.TagTree.valueLoop]; trivial
  | n + 1, t, tr, s, hs => by
    have h := decodeWith_sim hN tr s hs leaf t
    simp only [JPEG2000.TagTree.valueLoop]
    revert h
    cases JPEG2000.TagTree.decodeWith next tr s leaf t with
    | error e =>
      cases JPEG2000.TagTree.decodeWith Spec.TagTree.listNext tr (ρ s) leaf t with
      | error _ => intro _; trivial
      | ok _ => intro h; exact absurd h id
    | ok r =>
      obtain ⟨b, tr', s'⟩ := r
      cases JPEG2000.TagTree.decodeWith Spec.TagTree.listNext tr (ρ s) leaf t with
      | error _ => intro h; exact absurd h id
      | ok r' =>
        intro ⟨he, hs'⟩
        subst he
        dsimp only
        cases b
        · exact valueLoop_sim hN leaf n (t + 1) tr' s' hs'
        · exact ⟨rfl, hs'⟩

/-- The exact value (`decodeValueWith`). -/
theorem decodeValueWith_sim (hN : NextSim ρ I next) (tr : JPEG2000.TagTree.Tree) (s : σ)
    (hs : I s) (leaf maxValue : Nat) :
    Sim I (fun (x : Nat × JPEG2000.TagTree.Tree × σ) => (x.1, x.2.1, ρ x.2.2)) (·.2.2)
      (JPEG2000.TagTree.decodeValueWith next tr s leaf maxValue)
      (JPEG2000.TagTree.decodeValueWith Spec.TagTree.listNext tr (ρ s) leaf maxValue) :=
  valueLoop_sim hN leaf (maxValue + 2) 0 tr s hs

end Generic

/-- The packet-header bit reader is a bit source simulating `rem` under any `BitSim`
invariant. -/
theorem bitNext_nextSim {I : BitReader → Prop} (hI : BitSim I) :
    NextSim rem I JPEG2000.TagTree.bitNext :=
  fun b hb => bitNext_sim hI b hb

/-- An out-of-range leaf: the spec query fails. -/
theorem query_out {w h : Nat} (s : Spec.TagTree.St) (leaf t : Nat) (bs : List Bool)
    (hl : ¬ leaf < w * h) : Spec.TagTree.query w h s (leaf % w) (leaf / w) t bs = none := by
  have hn : ¬ (leaf % w < w ∧ leaf / w < h) := by
    intro ⟨hx, hy⟩
    have hw : 0 < w := by omega
    exact hl (by
      have := (Nat.div_lt_iff_lt_mul hw).mp hy
      rw [Nat.mul_comm]; exact this)
  simp only [Spec.TagTree.query, hn, ↓reduceIte]

/-- An out-of-range leaf: the spec exact value fails. -/
theorem exact_out {w h : Nat} (s : Spec.TagTree.St) (leaf m : Nat) (bs : List Bool)
    (hl : ¬ leaf < w * h) : Spec.TagTree.exact w h s (leaf % w) (leaf / w) m bs = none := by
  simp only [Spec.TagTree.exact, Spec.TagTree.exactAux, query_out s leaf 0 bs hl]

/-- **The fast tag-tree query over the packet-header reader = the spec query over the bit
list** (B.10.2, B.10.4). -/
theorem decode_spec {I : BitReader → Prop} (hI : BitSim I) (tr : JPEG2000.TagTree.Tree)
    (s : Spec.TagTree.St) (hR : Spec.TagTree.Rel tr s) (b : BitReader) (hb : I b) (leaf t : Nat) :
    match Spec.TagTree.query tr.w tr.h s (leaf % tr.w) (leaf / tr.w) t (rem b) with
    | none => ∃ e, JPEG2000.TagTree.decode tr b leaf t = .error e
    | some (x, s', l) => ∃ tr' b', JPEG2000.TagTree.decode tr b leaf t = .ok (x, tr', b') ∧
        l = rem b' ∧ I b' ∧ Spec.TagTree.Rel tr' s' ∧ tr'.w = tr.w ∧ tr'.h = tr.h := by
  by_cases hl : leaf < tr.w * tr.h
  · have h1 := decodeWith_sim (bitNext_nextSim hI) tr b hb leaf t
    have h2 := Spec.TagTree.fast_decode_eq tr s hR (rem b) leaf t hl
    unfold JPEG2000.TagTree.decode
    revert h1 h2
    cases Spec.TagTree.query tr.w tr.h s (leaf % tr.w) (leaf / tr.w) t (rem b) with
    | none =>
      intro h1 h2
      rw [h2] at h1
      revert h1
      cases JPEG2000.TagTree.decodeWith JPEG2000.TagTree.bitNext tr b leaf t with
      | error e => intro _; exact ⟨e, rfl⟩
      | ok _ => intro h; exact absurd h id
    | some r =>
      obtain ⟨x, s', l⟩ := r
      intro h1 ⟨tr', h2, hR', hw, hh⟩
      rw [h2] at h1
      revert h1
      cases JPEG2000.TagTree.decodeWith JPEG2000.TagTree.bitNext tr b leaf t with
      | error e => intro h; exact absurd h id
      | ok r =>
        obtain ⟨x', tr'', b'⟩ := r
        intro ⟨he, hb'⟩
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl, rfl⟩ := he
        exact ⟨tr', b', rfl, rfl, hb', hR', hw, hh⟩
  · rw [query_out s leaf t (rem b) hl]
    simp only [JPEG2000.TagTree.decode, JPEG2000.TagTree.decodeWith, hl, ↓reduceIte]
    exact ⟨_, rfl⟩

/-- **The fast exact-value decoding over the packet-header reader = the spec over the bit
list** (B.10.2, B.10.5). -/
theorem decodeValue_spec {I : BitReader → Prop} (hI : BitSim I) (tr : JPEG2000.TagTree.Tree)
    (s : Spec.TagTree.St) (hR : Spec.TagTree.Rel tr s) (b : BitReader) (hb : I b) (leaf m : Nat) :
    match Spec.TagTree.exact tr.w tr.h s (leaf % tr.w) (leaf / tr.w) m (rem b) with
    | none => ∃ e, JPEG2000.TagTree.decodeValue tr b leaf m = .error e
    | some (x, s', l) => ∃ tr' b', JPEG2000.TagTree.decodeValue tr b leaf m = .ok (x, tr', b') ∧
        l = rem b' ∧ I b' ∧ Spec.TagTree.Rel tr' s' ∧ tr'.w = tr.w ∧ tr'.h = tr.h := by
  by_cases hl : leaf < tr.w * tr.h
  · have h1 := decodeValueWith_sim (bitNext_nextSim hI) tr b hb leaf m
    have h2 := Spec.TagTree.fast_decodeValue_eq tr s hR (rem b) leaf m hl
    unfold JPEG2000.TagTree.decodeValue
    revert h1 h2
    cases Spec.TagTree.exact tr.w tr.h s (leaf % tr.w) (leaf / tr.w) m (rem b) with
    | none =>
      intro h1 ⟨e', h2⟩
      rw [h2] at h1
      revert h1
      cases JPEG2000.TagTree.decodeValueWith JPEG2000.TagTree.bitNext tr b leaf m with
      | error e => intro _; exact ⟨e, rfl⟩
      | ok _ => intro h; exact absurd h id
    | some r =>
      obtain ⟨x, s', l⟩ := r
      intro h1 ⟨tr', h2, hR', hw, hh⟩
      rw [h2] at h1
      revert h1
      cases JPEG2000.TagTree.decodeValueWith JPEG2000.TagTree.bitNext tr b leaf m with
      | error e => intro h; exact absurd h id
      | ok r =>
        obtain ⟨x', tr'', b'⟩ := r
        intro ⟨he, hb'⟩
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl, rfl⟩ := he
        exact ⟨tr', b', rfl, rfl, hb', hR', hw, hh⟩
  · rw [exact_out s leaf m (rem b) hl]
    simp only [JPEG2000.TagTree.decodeValue, JPEG2000.TagTree.decodeValueWith,
      JPEG2000.TagTree.valueLoop, JPEG2000.TagTree.decodeWith, hl, ↓reduceIte]
    exact ⟨_, rfl⟩

end JPEG2000.Spec.Tier2Equiv
