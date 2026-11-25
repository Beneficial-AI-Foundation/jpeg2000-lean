import JPEG2000.Progression

/-!
# Progression orders: B.12 as list comprehensions, C5, fast = spec
(Plan.md §4 C5, §5.1, §5.2 "Tier-2"; T.800 B.9, B.12.1.1–B.12.1.5, B.12.2, A.6.6)

Task 4.3. The packet sequence of a tile, specified as explicit list comprehensions that
follow the loops of T.800 B.12 literally:

* `lrcp` (B.12.1.1) and `rlcp` (B.12.1.2): `l`, `r`, `i`, `k` (resp. `r`, `l`, `i`, `k`),
  resolutions above `NL_i` skipped;
* `rpclPrecincts` (B.12.1.3), `pcrlPrecincts` (B.12.1.4), `cprlPrecincts` (B.12.1.5): every
  reference-grid point `y = ty0 … ty1 − 1`, `x = tx0 … tx1 − 1` of the tile, and the precinct
  "at" that point for component `i` / resolution `r` when the B.12.1.3 divisibility
  condition holds (`precAt`), then the layers (`withLayers`);
* a POC progression volume (B.12.2) restricts the loop ranges to layers `[0, LYEpoc)`,
  resolutions `[RSpoc, REpoc)`, components `[CSpoc, CEpoc)` (`volume`); the tile's packet
  sequence is the volumes in turn, each packet at its first occurrence (`packets`, `dedup`).

Theorems:

* `Axis.ref_spec`, `Axis.col_spec` (one axis of B.12.1.3) and `precAt_ref`, `precAt_some`:
  each precinct is visited at exactly one point of the tile, its reference position
  (`Layout.refX`, `refY`), under `Layout.WF` (non-zero sub-sampling; tile-component
  rectangle as B-12);
* **C5**: `c5` — for each of the five orders without POC, the sequence has no duplicates and
  its members are exactly the packet set; `c5_perm` — hence a permutation of the LRCP
  sequence; `c5_volume` — the same for any progression volume, restricted to the volume;
  `c5_poc` — with POC the emitted sequence has no duplicates and consists of exactly the
  packets of the packet set lying in some volume (packets in no volume are never emitted);
* **fast = spec**: `forVolume_eq_spec`, `forPackets_eq_spec` — the lazy iterator of
  `JPEG2000.Progression` folds a callback over exactly these sequences, in order. For the
  position-driven orders the iterator sorts the precincts by their key; `sortedPrecincts_eq`
  shows this equals the point-by-point scan (both lists are strictly increasing for the key
  and have the same members, `eq_of_pairwise_key`).
-/


namespace JPEG2000.Spec.Progression

open JPEG2000 JPEG2000.Header JPEG2000.Marker JPEG2000.Tier2.Geometry JPEG2000.Progression

/-! ## The B.12 comprehensions -/

/-- The precinct of resolution `r` of component `i` visited at reference-grid point `(x, y)`
by the position-driven orders, "if any" (B.12.1.3): `r ≤ NL_i`, the visiting condition
holds along both axes — `x` divisible by `XRsiz · 2^(PPx + NL − r)`, or `x = tx0` and
`trx0 · 2^(NL − r)` not divisible by `2^(PPx + NL − r)` (likewise `y`) — and the precinct
column `⌊⌈x / (XRsiz · 2^(NL − r))⌉ / 2^PPx⌋ − ⌊trx0 / 2^PPx⌋` and row exist. -/
def precAt (g : Layout) (i r x y : Nat) : Option Nat :=
  let tc := g.comp i
  let l := g.levels i - r
  let rr := g.resRect i r
  let px := g.ppx i r
  let py := g.ppy i r
  let vx := x % (tc.dx * 2 ^ (px + l)) = 0 ∨ (x = g.tile.x0 ∧ rr.x0 * 2 ^ l % 2 ^ (px + l) ≠ 0)
  let vy := y % (tc.dy * 2 ^ (py + l)) = 0 ∨ (y = g.tile.y0 ∧ rr.y0 * 2 ^ l % 2 ^ (py + l) ≠ 0)
  let col := cdiv x (tc.dx * 2 ^ l) / 2 ^ px - rr.x0 / 2 ^ px
  let row := cdiv y (tc.dy * 2 ^ l) / 2 ^ py - rr.y0 / 2 ^ py
  if r ≤ g.levels i ∧ vx ∧ vy ∧ col < g.pw i r ∧ row < g.ph i r then some (row * g.pw i r + col)
  else none

/-- Layers `[0, min(LYEpoc, L))` of a volume. -/
def layerRange (g : Layout) (v : Volume) : List Nat := List.range (v.le g)
/-- Resolutions `[RSpoc, min(REpoc, Nmax + 1))`. -/
def resRange (g : Layout) (v : Volume) : List Nat := List.range' v.resStart (v.re g - v.resStart)
/-- Components `[CSpoc, min(CEpoc, Csiz))`. -/
def compRange (g : Layout) (v : Volume) : List Nat :=
  List.range' v.compStart (v.ce g - v.compStart)
/-- Reference-grid columns of the tile, `tx0 … tx1 − 1`. -/
def xRange (g : Layout) : List Nat := List.range' g.tile.x0 (g.tile.x1 - g.tile.x0)
/-- Reference-grid rows of the tile, `ty0 … ty1 − 1`. -/
def yRange (g : Layout) : List Nat := List.range' g.tile.y0 (g.tile.y1 - g.tile.y0)

/-- The precincts `k < numprecincts(i, r)` of resolution `r` of component `i` as packets of
layer `l`, none when `r > NL_i` (B.12.1.1: "skip"). -/
def precinctsOf (g : Layout) (l r i : Nat) : List PacketId :=
  if r ≤ g.levels i then (List.range (g.pw i r * g.ph i r)).map fun k => ⟨l, r, i, k⟩ else []

/-- B.12.1.1 layer-resolution-component-position over a volume. -/
def lrcp (g : Layout) (v : Volume) : List PacketId :=
  (layerRange g v).flatMap fun l => (resRange g v).flatMap fun r =>
    (compRange g v).flatMap fun i => precinctsOf g l r i

/-- B.12.1.2 resolution-layer-component-position over a volume. -/
def rlcp (g : Layout) (v : Volume) : List PacketId :=
  (resRange g v).flatMap fun r => (layerRange g v).flatMap fun l =>
    (compRange g v).flatMap fun i => precinctsOf g l r i

/-- The precinct visited at `(x, y)` for `(i, r)`, as a list of at most one `PrecRef`. -/
def visit (g : Layout) (i r x y : Nat) : List PrecRef :=
  (precAt g i r x y).toList.map fun k => ⟨i, r, k⟩

/-- B.12.1.3 resolution-position-component-layer, precinct level: `r`, `y`, `x`, `i`. -/
def rpclPrecincts (g : Layout) (v : Volume) : List PrecRef :=
  (resRange g v).flatMap fun r => (yRange g).flatMap fun y => (xRange g).flatMap fun x =>
    (compRange g v).flatMap fun i => visit g i r x y

/-- B.12.1.4 position-component-resolution-layer, precinct level: `y`, `x`, `i`, `r`. -/
def pcrlPrecincts (g : Layout) (v : Volume) : List PrecRef :=
  (yRange g).flatMap fun y => (xRange g).flatMap fun x => (compRange g v).flatMap fun i =>
    (resRange g v).flatMap fun r => visit g i r x y

/-- B.12.1.5 component-position-resolution-layer, precinct level: `i`, `y`, `x`, `r`. -/
def cprlPrecincts (g : Layout) (v : Volume) : List PrecRef :=
  (compRange g v).flatMap fun i => (yRange g).flatMap fun y => (xRange g).flatMap fun x =>
    (resRange g v).flatMap fun r => visit g i r x y

/-- The layers of each precinct, innermost (B.12.1.3–B.12.1.5). -/
def withLayers (g : Layout) (v : Volume) (ps : List PrecRef) : List PacketId :=
  ps.flatMap fun e => (layerRange g v).map e.packet

/-- The precinct sequence of a position-driven order over a volume. -/
def posPrecincts (g : Layout) (v : Volume) : List PrecRef :=
  match v.order with
  | .rpcl => rpclPrecincts g v
  | .pcrl => pcrlPrecincts g v
  | _ => cprlPrecincts g v

/-- The packet sequence of a volume in its order (B.12.1, B.12.2). -/
def volume (g : Layout) (v : Volume) : List PacketId :=
  match v.order with
  | .lrcp => lrcp g v
  | .rlcp => rlcp g v
  | _ => withLayers g v (posPrecincts g v)

/-- The packet sequence of a tile without POC in order `o`. -/
def order (g : Layout) (o : Progression) : List PacketId := volume g (Volume.full g o)

/-- First occurrences only: drops every packet already in `seen` or earlier in the list. -/
def dedup : List PacketId → List PacketId → List PacketId
  | _, [] => []
  | seen, p :: ps => if p ∈ seen then dedup seen ps else p :: dedup (p :: seen) ps

/-- The packet sequence of a tile (B.12.2): the volumes in turn, each packet at its first
occurrence. -/
def packets (g : Layout) (o : Progression) (poc : Array PocEntry) : List PacketId :=
  dedup [] ((volumes g o poc).flatMap (volume g))


/-! ## Generic list lemmas -/

section Generic

/-- `forRange` is a fold over `List.range'`. -/
theorem forRange_eq {m : Type → Type} [Monad m] [LawfulMonad m] {β : Type} (s n : Nat)
    (f : β → Nat → m β) (b : β) : forRange s n f b = (List.range' s n).foldlM f b := by
  induction n generalizing s b with
  | zero => simp [forRange]
  | succ n ih => simp [forRange, List.range'_succ, ih]

private theorem foldlM_flatMap {m : Type → Type} [Monad m] [LawfulMonad m] {α γ β : Type}
    (l : List α) (g : α → List γ) (f : β → γ → m β) (b : β) :
    (l.flatMap g).foldlM f b = l.foldlM (fun b a => (g a).foldlM f b) b := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, List.foldlM_append, ih]

private theorem foldlM_skip {m : Type → Type} [Monad m] [LawfulMonad m] {α β : Type}
    (l : List α) (c : α → Bool) (f : β → α → m β) (b : β) :
    l.foldlM (fun b p => if c p then pure b else f b p) b =
      (l.filter fun p => !c p).foldlM f b := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih =>
    by_cases h : c a = true
    · simp [h, ih]
    · simp [h, ih]

/-- Two lists strictly increasing for the same key with the same members are equal. -/
private theorem eq_of_pairwise_key {α : Type} (key : α → List Nat) : ∀ {l1 l2 : List α},
    l1.Pairwise (fun a b => key a < key b) → l2.Pairwise (fun a b => key a < key b) →
    (∀ x, x ∈ l1 ↔ x ∈ l2) → l1 = l2
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, h => absurd ((h b).2 (by simp)) (by simp)
  | a :: _, [], _, _, h => absurd ((h a).1 (by simp)) (by simp)
  | a :: t1, b :: t2, h1, h2, h => by
    rw [List.pairwise_cons] at h1 h2
    have hab : a = b := by
      by_cases hab : a = b
      · exact hab
      have ha : a ∈ t2 := by
        have := (h a).1 (by simp)
        rcases List.mem_cons.1 this with h' | h'
        · exact absurd h' hab
        · exact h'
      have hb : b ∈ t1 := by
        have := (h b).2 (by simp)
        rcases List.mem_cons.1 this with h' | h'
        · exact absurd h'.symm hab
        · exact h'
      exact absurd (h1.1 b hb) (List.lt_asymm (h2.1 a ha))
    subst hab
    have ht : ∀ x, x ∈ t1 ↔ x ∈ t2 := by
      intro x
      constructor
      · intro hx
        rcases List.mem_cons.1 ((h x).1 (List.mem_cons_of_mem _ hx)) with h' | h'
        · subst h'; exact absurd (h1.1 x hx) (List.lt_irrefl _)
        · exact h'
      · intro hx
        rcases List.mem_cons.1 ((h x).2 (List.mem_cons_of_mem _ hx)) with h' | h'
        · subst h'; exact absurd (h2.1 x hx) (List.lt_irrefl _)
        · exact h'
    rw [eq_of_pairwise_key key h1.2 h2.2 ht]

/-- A `flatMap` over a strictly increasing list of blocks is strictly increasing for a key
whose entry after the common prefix `pre` is the block's index. -/
private theorem pairwise_flatMap_key {α : Type} (key : α → List Nat) (pre : List Nat)
    {xs : List Nat} (hxs : xs.Pairwise (· < ·)) {f : Nat → List α}
    (hf : ∀ a ∈ xs, (f a).Pairwise (fun u w => key u < key w))
    (hk : ∀ a ∈ xs, ∀ u ∈ f a, ∃ t, key u = pre ++ a :: t) :
    (xs.flatMap f).Pairwise (fun u w => key u < key w) := by
  rw [List.pairwise_flatMap]
  refine ⟨hf, hxs.imp_of_mem fun ha hb hab u hu w hw => ?_⟩
  obtain ⟨t, ht⟩ := hk _ ha u hu
  obtain ⟨t', ht'⟩ := hk _ hb w hw
  rw [ht, ht']
  exact List.append_left_lt (List.cons_lt_cons_of_lt hab)

private theorem nodup_flatMap_proj {α β : Type} (proj : β → α) {l : List α} {f : α → List β}
    (hl : l.Nodup) (hf : ∀ a ∈ l, (f a).Nodup) (hp : ∀ a ∈ l, ∀ x ∈ f a, proj x = a) :
    (l.flatMap f).Nodup := by
  rw [List.nodup_iff_pairwise_ne] at hl ⊢
  rw [List.pairwise_flatMap]
  refine ⟨fun a ha => List.nodup_iff_pairwise_ne.1 (hf a ha), ?_⟩
  refine hl.imp_of_mem (fun ha hb hne x hx y hy hxy => hne ?_)
  rw [← hp _ ha x hx, ← hp _ hb y hy, hxy]

private theorem pairwise_range' (s n : Nat) : (List.range' s n).Pairwise (· < ·) :=
  List.pairwise_lt_range' 1 (by decide)

end Generic

/-! ## First occurrences -/

section Dedup

/-- Membership in `dedup`. -/
theorem mem_dedup (p : PacketId) : ∀ (S l : List PacketId), p ∈ dedup S l ↔ p ∈ l ∧ p ∉ S
  | _, [] => by simp [dedup]
  | S, q :: l => by
    by_cases hq : q ∈ S
    · simp only [dedup, hq, ↓reduceIte, mem_dedup p S l, List.mem_cons]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨Or.inr h1, h2⟩
      · rintro ⟨h1 | h1, h2⟩
        · subst h1; exact absurd hq h2
        · exact ⟨h1, h2⟩
    · simp only [dedup, hq, ↓reduceIte, List.mem_cons, mem_dedup p (q :: S) l]
      by_cases hpq : p = q
      · subst hpq; simp [hq]
      · simp [hpq]

/-- `dedup` has no duplicates. -/
theorem nodup_dedup : ∀ (S l : List PacketId), (dedup S l).Nodup
  | _, [] => by simp [dedup]
  | S, q :: l => by
    by_cases hq : q ∈ S
    · simp only [dedup, hq, ↓reduceIte]; exact nodup_dedup S l
    · simp only [dedup, hq, ↓reduceIte]
      rw [List.nodup_cons]
      exact ⟨fun h => ((mem_dedup q _ _).1 h).2 (by simp), nodup_dedup _ l⟩

private theorem dedup_congr : ∀ {S1 S2 : List PacketId} (l : List PacketId),
    (∀ p, p ∈ S1 ↔ p ∈ S2) → dedup S1 l = dedup S2 l
  | _, _, [], _ => by simp [dedup]
  | S1, S2, q :: l, h => by
    simp only [dedup, h q]
    split
    · exact dedup_congr l h
    · rw [dedup_congr (S1 := q :: S1) (S2 := q :: S2) l (by intro p; simp [h p])]

private theorem dedup_append : ∀ (S A B : List PacketId),
    dedup S (A ++ B) = dedup S A ++ dedup (S ++ A) B
  | S, [], B => by simp [dedup]
  | S, q :: A, B => by
    by_cases hq : q ∈ S
    · simp only [List.cons_append, dedup, hq, ↓reduceIte, dedup_append S A B]
      rw [dedup_congr (S1 := S ++ q :: A) (S2 := S ++ A) B (by
        intro p; simp only [List.mem_append, List.mem_cons]
        constructor
        · rintro (h | h | h)
          · exact Or.inl h
          · subst h; exact Or.inl hq
          · exact Or.inr h
        · rintro (h | h)
          · exact Or.inl h
          · exact Or.inr (Or.inr h))]
    · simp only [List.cons_append, dedup, hq, ↓reduceIte, dedup_append (q :: S) A B,
        List.cons_append]
      rw [dedup_congr (S1 := q :: (S ++ A)) (S2 := S ++ q :: A) B (by
        intro p; simp only [List.mem_append, List.mem_cons]
        constructor
        · rintro (h | h | h)
          · exact Or.inr (Or.inl h)
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
        · rintro (h | h | h)
          · exact Or.inr (Or.inl h)
          · exact Or.inl h
          · exact Or.inr (Or.inr h))]

private theorem dedup_of_nodup : ∀ (S A : List PacketId), A.Nodup →
    dedup S A = A.filter fun p => !decide (p ∈ S)
  | S, [], _ => by simp [dedup]
  | S, q :: A, h => by
    rw [List.nodup_cons] at h
    by_cases hq : q ∈ S
    · simp [dedup, hq, dedup_of_nodup S A h.2]
    · simp only [dedup, hq, ↓reduceIte, dedup_of_nodup (q :: S) A h.2, List.filter_cons,
        decide_false, Bool.not_false]
      congr 1
      apply List.filter_congr
      intro x hx
      have : x ≠ q := fun e => h.1 (e ▸ hx)
      simp [this]

end Dedup

/-! ## One axis of the position-driven orders (B.12.1.3) -/

namespace Axis

/-- `⌊tr0 / p⌋` with `tr0 = ⌈t0 / m⌉`: the column of the first precinct
(`m = XRsiz · 2^(NL − r)`, `p = 2^PPx`). -/
def k0 (t0 m p : Nat) : Nat := cdiv t0 m / p

/-- Number of precinct columns (B-16) of the resolution `[⌈t0/m⌉, ⌈t1/m⌉)`. -/
def pw (t0 t1 m p : Nat) : Nat :=
  if cdiv t1 m ≤ cdiv t0 m then 0 else cdiv (cdiv t1 m) p - k0 t0 m p

/-- The B.12.1.3 visiting condition along one axis. -/
def visits (t0 m p x : Nat) : Prop := x % (m * p) = 0 ∨ (x = t0 ∧ cdiv t0 m % p ≠ 0)

instance (t0 m p x : Nat) : Decidable (visits t0 m p x) := by unfold visits; infer_instance

/-- The precinct column visited at `x`. -/
def col (t0 m p x : Nat) : Nat := cdiv x m / p - k0 t0 m p

/-- The reference position of precinct column `px`. -/
def ref (t0 m p px : Nat) : Nat := max t0 (m * p * (k0 t0 m p + px))

private theorem lt_cdiv_iff {q t m : Nat} (hm : 0 < m) : q < cdiv t m ↔ q * m < t := by
  unfold cdiv
  constructor
  · intro h
    have h1 : q + 1 ≤ (t + m - 1) / m := h
    have h2 := (Nat.le_div_iff_mul_le hm).1 h1
    rw [Nat.succ_mul] at h2; omega
  · intro h
    have : (q + 1) * m ≤ t + m - 1 := by rw [Nat.succ_mul]; omega
    exact (Nat.le_div_iff_mul_le hm).2 this

private theorem eq_of_lt_iff {a b : Nat} (h : ∀ q, q < a ↔ q < b) : a = b := by
  rcases Nat.lt_trichotomy a b with h3 | h3 | h3
  · exact absurd ((h a).2 h3) (Nat.lt_irrefl _)
  · exact h3
  · exact absurd ((h b).1 h3) (Nat.lt_irrefl _)

/-- `⌈⌈t/a⌉/b⌉ = ⌈t/(a·b)⌉`. -/
theorem cdiv_cdiv {t a b : Nat} (ha : 0 < a) (hb : 0 < b) :
    cdiv (cdiv t a) b = cdiv t (a * b) := by
  apply eq_of_lt_iff; intro q
  rw [lt_cdiv_iff hb, lt_cdiv_iff ha, lt_cdiv_iff (Nat.mul_pos ha hb), Nat.mul_assoc,
    Nat.mul_comm b a]

private theorem cdiv_mul {b m : Nat} (hm : 0 < m) : cdiv (b * m) m = b := by
  apply eq_of_lt_iff; intro q
  rw [lt_cdiv_iff hm]
  exact ⟨fun h => Nat.lt_of_mul_lt_mul_right h, fun h => Nat.mul_lt_mul_of_pos_right h hm⟩

private theorem cdiv_mono {s t m : Nat} (h : s ≤ t) : cdiv s m ≤ cdiv t m := by
  unfold cdiv; exact Nat.div_le_div_right (by omega)

/-- Every precinct column `px < pw` is visited at its reference position, which lies in
`[t0, t1)`, satisfies the visiting condition and maps back to `px`. -/
theorem ref_spec {t0 t1 m p : Nat} (hm : 0 < m) (hp : 0 < p) {px : Nat}
    (h : px < pw t0 t1 m p) :
    t0 ≤ ref t0 m p px ∧ ref t0 m p px < t1 ∧ visits t0 m p (ref t0 m p px) ∧
      col t0 m p (ref t0 m p px) = px := by
  unfold pw at h
  split at h
  · omega
  rename_i hne
  have hk := Nat.div_add_mod (cdiv t0 m) p
  rw [Nat.mul_comm] at hk
  have hk' := Nat.mod_lt (cdiv t0 m) hp
  generalize ha : k0 t0 m p + px = a
  have hka : k0 t0 m p ≤ a := by omega
  have ha1 : a * p < cdiv t1 m := (lt_cdiv_iff hp).1 (by omega)
  have ha2 : a * p * m < t1 := (lt_cdiv_iff hm).1 ha1
  have hS : m * p * a = a * p * m := by ac_rfl
  unfold ref col visits
  rw [ha]
  by_cases hc : t0 ≤ m * p * a
  · rw [Nat.max_eq_right hc]
    refine ⟨hc, by omega, Or.inl (Nat.mul_mod_right _ _), ?_⟩
    rw [hS, cdiv_mul hm, Nat.mul_div_cancel _ hp]
    omega
  · rw [Nat.max_eq_left (by omega)]
    have h1 : a * p < cdiv t0 m := (lt_cdiv_iff hm).2 (by omega)
    have h2 : a < k0 t0 m p + 1 := by
      apply Nat.lt_of_mul_lt_mul_right (a := p)
      unfold k0; rw [Nat.succ_mul]; omega
    have hpx : px = 0 := by omega
    have hmod : cdiv t0 m % p ≠ 0 := by
      intro h0; unfold k0 at hka; rw [h0] at hk
      have : cdiv t0 m / p * p ≤ a * p := Nat.mul_le_mul_right _ hka
      omega
    have ht : t0 < t1 := by
      apply Nat.lt_of_not_le; intro hle
      exact hne (cdiv_mono hle)
    refine ⟨Nat.le_refl _, ht, Or.inr ⟨rfl, hmod⟩, ?_⟩
    unfold k0; omega

/-- A visited position `x ≥ t0` is the reference position of the column visited there. -/
theorem col_spec {t0 m p : Nat} (hm : 0 < m) (hp : 0 < p) {x : Nat} (hx : t0 ≤ x)
    (hv : visits t0 m p x) : ref t0 m p (col t0 m p x) = x := by
  have hk := Nat.div_add_mod (cdiv t0 m) p
  rw [Nat.mul_comm] at hk
  unfold visits at hv
  unfold ref col
  rcases hv with hv | ⟨hx0, hmod⟩
  · have hx' := Nat.div_add_mod x (m * p)
    rw [hv, Nat.add_zero] at hx'
    generalize x / (m * p) = b at hx'
    subst hx'
    have hS : m * p * b = (p * b) * m := by ac_rfl
    rw [hS, cdiv_mul hm, Nat.mul_div_cancel_left _ hp]
    have hb : k0 t0 m p ≤ b := by
      have : p * b * m ≥ t0 := by rw [← hS]; exact hx
      have h1 : cdiv t0 m ≤ p * b := by
        apply Nat.le_of_not_lt; intro h2
        have := (lt_cdiv_iff hm).1 h2; omega
      unfold k0
      exact Nat.div_le_of_le_mul h1
    rw [Nat.add_sub_cancel' hb, hS]
    exact Nat.max_eq_right (by omega)
  · rw [hx0]
    have hc : cdiv t0 m / p - k0 t0 m p = 0 := by unfold k0; omega
    rw [hc, Nat.add_zero]
    apply Nat.max_eq_left
    have h1 : k0 t0 m p * p < cdiv t0 m := by
      unfold k0; omega
    have := (lt_cdiv_iff hm).1 h1
    have e : ∀ u, m * p * u = u * p * m := fun u => by ac_rfl
    rw [e]
    omega

end Axis

/-! ## Precinct positions of a tile (B.12.1.3) -/

section Positions

variable {g : Layout}

private theorem resRect_eq (hwf : g.WF) {i : Nat} (hi : i < g.numComps) (r : Nat) :
    (g.resRect i r).x0 = cdiv g.tile.x0 ((g.comp i).dx * 2 ^ (g.levels i - r)) ∧
    (g.resRect i r).x1 = cdiv g.tile.x1 ((g.comp i).dx * 2 ^ (g.levels i - r)) ∧
    (g.resRect i r).y0 = cdiv g.tile.y0 ((g.comp i).dy * 2 ^ (g.levels i - r)) ∧
    (g.resRect i r).y1 = cdiv g.tile.y1 ((g.comp i).dy * 2 ^ (g.levels i - r)) := by
  obtain ⟨hdx, hdy, hrect⟩ := hwf i hi
  simp only [Layout.resRect, Header.resRect, cdivPow, hrect]
  exact ⟨Axis.cdiv_cdiv (by omega) (Nat.two_pow_pos _),
    Axis.cdiv_cdiv (by omega) (Nat.two_pow_pos _),
    Axis.cdiv_cdiv (by omega) (Nat.two_pow_pos _),
    Axis.cdiv_cdiv (by omega) (Nat.two_pow_pos _)⟩

private theorem visits_iff {x t0 d l P a0 : Nat} (ha : a0 = cdiv t0 (d * 2 ^ l)) :
    (x % (d * 2 ^ (P + l)) = 0 ∨ (x = t0 ∧ a0 * 2 ^ l % 2 ^ (P + l) ≠ 0)) ↔
      Axis.visits t0 (d * 2 ^ l) (2 ^ P) x := by
  subst ha
  have e1 : d * 2 ^ (P + l) = d * 2 ^ l * 2 ^ P := by rw [Nat.pow_add]; ac_rfl
  have e2 : cdiv t0 (d * 2 ^ l) * 2 ^ l % 2 ^ (P + l) =
      (cdiv t0 (d * 2 ^ l) % 2 ^ P) * 2 ^ l := by
    rw [Nat.pow_add, Nat.mul_mod_mul_right]
  unfold Axis.visits
  rw [e1, e2]
  simp [Nat.mul_eq_zero]

private theorem pw_eq (hwf : g.WF) {i : Nat} (hi : i < g.numComps) (r : Nat) :
    g.pw i r = Axis.pw g.tile.x0 g.tile.x1 ((g.comp i).dx * 2 ^ (g.levels i - r))
      (2 ^ g.ppx i r) := by
  obtain ⟨h0, h1, -, -⟩ := resRect_eq hwf hi r
  simp only [Layout.pw, gridCount, Axis.pw, Axis.k0, cdivPow, h0, h1]

private theorem ph_eq (hwf : g.WF) {i : Nat} (hi : i < g.numComps) (r : Nat) :
    g.ph i r = Axis.pw g.tile.y0 g.tile.y1 ((g.comp i).dy * 2 ^ (g.levels i - r))
      (2 ^ g.ppy i r) := by
  obtain ⟨-, -, h0, h1⟩ := resRect_eq hwf hi r
  simp only [Layout.ph, gridCount, Axis.pw, Axis.k0, cdivPow, h0, h1]

private theorem refX_eq (hwf : g.WF) {i : Nat} (hi : i < g.numComps) (r px : Nat) :
    g.refX i r px = Axis.ref g.tile.x0 ((g.comp i).dx * 2 ^ (g.levels i - r))
      (2 ^ g.ppx i r) px := by
  obtain ⟨h0, -, -, -⟩ := resRect_eq hwf hi r
  simp only [Layout.refX, Axis.ref, Axis.k0, h0]
  rw [Nat.pow_add]
  congr 2
  ac_rfl

private theorem refY_eq (hwf : g.WF) {i : Nat} (hi : i < g.numComps) (r py : Nat) :
    g.refY i r py = Axis.ref g.tile.y0 ((g.comp i).dy * 2 ^ (g.levels i - r))
      (2 ^ g.ppy i r) py := by
  obtain ⟨-, -, h0, -⟩ := resRect_eq hwf hi r
  simp only [Layout.refY, Axis.ref, Axis.k0, h0]
  rw [Nat.pow_add]
  congr 2
  ac_rfl

/-- `precAt` in terms of the one-axis functions. -/
private theorem precAt_eq (hwf : g.WF) {i : Nat} (hi : i < g.numComps) (r x y : Nat) :
    precAt g i r x y =
      let mx := (g.comp i).dx * 2 ^ (g.levels i - r)
      let my := (g.comp i).dy * 2 ^ (g.levels i - r)
      let px := 2 ^ g.ppx i r
      let py := 2 ^ g.ppy i r
      if r ≤ g.levels i ∧ Axis.visits g.tile.x0 mx px x ∧ Axis.visits g.tile.y0 my py y ∧
          Axis.col g.tile.x0 mx px x < g.pw i r ∧ Axis.col g.tile.y0 my py y < g.ph i r then
        some (Axis.col g.tile.y0 my py y * g.pw i r + Axis.col g.tile.x0 mx px x)
      else none := by
  obtain ⟨h0, -, h2, -⟩ := resRect_eq hwf hi r
  simp only [precAt, visits_iff (P := g.ppx i r) (x := x) h0,
    visits_iff (P := g.ppy i r) (x := y) h2]
  simp only [Axis.col, Axis.k0, h0, h2]
  split <;> rename_i h <;> simp only [h, and_self, ↓reduceIte]

/-- Under `WF`, a precinct visited at a point of the tile exists (`r ≤ NL_i`,
`k < numprecincts`) and has that point as its reference position. -/
theorem precAt_some (hwf : g.WF) {i r x y k : Nat} (hi : i < g.numComps)
    (hx : g.tile.x0 ≤ x) (hy : g.tile.y0 ≤ y) (h : precAt g i r x y = some k) :
    r ≤ g.levels i ∧ k < g.pw i r * g.ph i r ∧ g.refX i r (k % g.pw i r) = x ∧
      g.refY i r (k / g.pw i r) = y := by
  obtain ⟨hdx, hdy, -⟩ := hwf i hi
  have hmx : 0 < (g.comp i).dx * 2 ^ (g.levels i - r) := Nat.mul_pos hdx (Nat.two_pow_pos _)
  have hmy : 0 < (g.comp i).dy * 2 ^ (g.levels i - r) := Nat.mul_pos hdy (Nat.two_pow_pos _)
  rw [precAt_eq hwf hi] at h
  simp only at h
  split at h
  · rename_i hc
    obtain ⟨hr, hvx, hvy, hcol, hrow⟩ := hc
    injection h with h
    subst h
    generalize hcw : Axis.col g.tile.x0 _ _ x = c at hcol ⊢
    generalize hrw : Axis.col g.tile.y0 _ _ y = w at hrow
    have hpw : 0 < g.pw i r := by omega
    have e1 : (w * g.pw i r + c) % g.pw i r = c := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hcol]
    have e2 : (w * g.pw i r + c) / g.pw i r = w := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpw, Nat.div_eq_of_lt hcol, Nat.zero_add]
    refine ⟨hr, ?_, ?_, ?_⟩
    · have : (w + 1) * g.pw i r ≤ g.ph i r * g.pw i r := Nat.mul_le_mul_right _ hrow
      rw [Nat.succ_mul, Nat.mul_comm (g.ph i r)] at this
      omega
    · rw [e1, refX_eq hwf hi, ← hcw]
      exact Axis.col_spec hmx (Nat.two_pow_pos _) hx hvx
    · rw [e2, refY_eq hwf hi, ← hrw]
      exact Axis.col_spec hmy (Nat.two_pow_pos _) hy hvy
  · exact absurd h (by simp)

/-- Under `WF`, every precinct `k < numprecincts(i, r)` is visited at its reference position,
which lies in the tile. -/
theorem precAt_ref (hwf : g.WF) {i r k : Nat} (hi : i < g.numComps) (hr : r ≤ g.levels i)
    (hk : k < g.pw i r * g.ph i r) :
    g.tile.x0 ≤ g.refX i r (k % g.pw i r) ∧ g.refX i r (k % g.pw i r) < g.tile.x1 ∧
    g.tile.y0 ≤ g.refY i r (k / g.pw i r) ∧ g.refY i r (k / g.pw i r) < g.tile.y1 ∧
    precAt g i r (g.refX i r (k % g.pw i r)) (g.refY i r (k / g.pw i r)) = some k := by
  obtain ⟨hdx, hdy, -⟩ := hwf i hi
  have hmx : 0 < (g.comp i).dx * 2 ^ (g.levels i - r) := Nat.mul_pos hdx (Nat.two_pow_pos _)
  have hmy : 0 < (g.comp i).dy * 2 ^ (g.levels i - r) := Nat.mul_pos hdy (Nat.two_pow_pos _)
  have hpw : 0 < g.pw i r := Nat.pos_of_ne_zero (fun h => by rw [h, Nat.zero_mul] at hk; omega)
  have hph : 0 < g.ph i r := Nat.pos_of_ne_zero (fun h => by rw [h, Nat.mul_zero] at hk; omega)
  have hpx : k % g.pw i r < g.pw i r := Nat.mod_lt _ hpw
  have hpy : k / g.pw i r < g.ph i r := (Nat.div_lt_iff_lt_mul hpw).2 (by
    rw [Nat.mul_comm]; exact hk)
  have hpx' : k % g.pw i r < Axis.pw g.tile.x0 g.tile.x1
      ((g.comp i).dx * 2 ^ (g.levels i - r)) (2 ^ g.ppx i r) := by
    rw [← pw_eq hwf hi r]; exact hpx
  have hpy' : k / g.pw i r < Axis.pw g.tile.y0 g.tile.y1
      ((g.comp i).dy * 2 ^ (g.levels i - r)) (2 ^ g.ppy i r) := by
    rw [← ph_eq hwf hi r]; exact hpy
  have ax := Axis.ref_spec hmx (Nat.two_pow_pos (g.ppx i r)) hpx'
  have ay := Axis.ref_spec hmy (Nat.two_pow_pos (g.ppy i r)) hpy'
  rw [refX_eq hwf hi, refY_eq hwf hi]
  refine ⟨ax.1, ax.2.1, ay.1, ay.2.1, ?_⟩
  rw [precAt_eq hwf hi]
  simp only
  rw [ax.2.2.2, ay.2.2.2]
  have hc : r ≤ g.levels i ∧
      Axis.visits g.tile.x0 ((g.comp i).dx * 2 ^ (g.levels i - r)) (2 ^ g.ppx i r)
        (Axis.ref g.tile.x0 ((g.comp i).dx * 2 ^ (g.levels i - r)) (2 ^ g.ppx i r)
          (k % g.pw i r)) ∧
      Axis.visits g.tile.y0 ((g.comp i).dy * 2 ^ (g.levels i - r)) (2 ^ g.ppy i r)
        (Axis.ref g.tile.y0 ((g.comp i).dy * 2 ^ (g.levels i - r)) (2 ^ g.ppy i r)
          (k / g.pw i r)) ∧
      k % g.pw i r < g.pw i r ∧ k / g.pw i r < g.ph i r :=
    ⟨hr, ax.2.2.1, ay.2.2.1, hpx, hpy⟩
  simp only [hc, and_self, ↓reduceIte]
  have := Nat.div_add_mod k (g.pw i r)
  rw [Nat.mul_comm] at this
  rw [this]

end Positions

/-! ## Membership and order of the comprehensions -/

section Members

variable {g : Layout}

private theorem le_foldr_max {x : Nat} : ∀ {l : List Nat}, x ∈ l → x ≤ l.foldr max 0
  | [], h => by simp at h
  | a :: l, h => by
    rcases List.mem_cons.1 h with h | h
    · subst h; simp only [List.foldr_cons]; omega
    · have := le_foldr_max h; simp only [List.foldr_cons]; omega

private theorem levels_le_max {i : Nat} (hi : i < g.numComps) : g.levels i ≤ g.maxLevels := by
  unfold Layout.levels Layout.comp Layout.maxLevels
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi, Option.getD_some]
  apply le_foldr_max
  exact List.mem_map.2 ⟨_, Array.getElem_mem_toList hi, rfl⟩

/-- The precinct of a packet. -/
def prOf (p : PacketId) : PrecRef := ⟨p.comp, p.res, p.prec⟩

private theorem lt_numPrecincts {i r k : Nat} :
    k < g.numPrecincts i r ↔ r ≤ g.levels i ∧ k < g.pw i r * g.ph i r := by
  unfold Layout.numPrecincts
  split
  · rename_i h; exact ⟨fun hk => ⟨h, hk⟩, fun hk => hk.2⟩
  · rename_i h; exact ⟨fun hk => absurd hk (Nat.not_lt_zero _), fun hk => absurd hk.1 h⟩

private theorem mem_precRefs (v : Volume) (e : PrecRef) :
    e ∈ precRefs g v ↔ v.compStart ≤ e.comp ∧ e.comp < v.ce g ∧ v.resStart ≤ e.res ∧
      e.res < v.re g ∧ e.res ≤ g.levels e.comp ∧ e.prec < g.pw e.comp e.res * g.ph e.comp e.res := by
  rcases e with ⟨i, r, k⟩
  simp only [precRefs, List.mem_flatMap, List.mem_map, List.mem_range, List.mem_range'_1,
    PrecRef.mk.injEq]
  constructor
  · rintro ⟨i', ⟨h1, h2⟩, r', ⟨h3, h4⟩, k', h5, rfl, rfl, rfl⟩
    exact ⟨h1, by omega, h3, by omega, lt_numPrecincts.1 h5⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨i, ⟨h1, by omega⟩, r, ⟨h3, by omega⟩, k, lt_numPrecincts.2 ⟨h5, h6⟩, rfl, rfl, rfl⟩

private theorem nodup_precRefs (v : Volume) : (precRefs g v).Nodup := by
  unfold precRefs
  refine nodup_flatMap_proj PrecRef.comp (List.nodup_range' _) (fun i _ => ?_) ?_
  · refine nodup_flatMap_proj PrecRef.res (List.nodup_range' _) (fun r _ => ?_) ?_
    · rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
      exact (List.nodup_iff_pairwise_ne.1 List.nodup_range).imp fun h e => h (by
        injection e)
    · intro r _ x hx
      obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx; rfl
  · intro i _ x hx
    obtain ⟨r, -, hx⟩ := List.mem_flatMap.1 hx
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx; rfl

/-- The packet set restricted to a volume, in terms of precincts and layers. -/
private theorem inSet_iff (v : Volume) (p : PacketId) :
    g.InPacketSet p ∧ v.InVolume p ↔ p.layer < v.le g ∧ prOf p ∈ precRefs g v := by
  rw [mem_precRefs]
  simp only [Layout.InPacketSet, Volume.InVolume, Volume.le, Volume.re, Volume.ce, prOf]
  constructor
  · rintro ⟨⟨h1, h2, h3, h4⟩, h5, h6, h7, h8, h9⟩
    have := levels_le_max h2
    exact ⟨by omega, h8, by omega, h6, by omega, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨⟨by omega, by omega, h6, h7⟩, by omega, h4, by omega, h2, by omega⟩

private theorem mem_precinctsOf (l r i : Nat) (p : PacketId) :
    p ∈ precinctsOf g l r i ↔
      p.layer = l ∧ p.res = r ∧ p.comp = i ∧ r ≤ g.levels i ∧ p.prec < g.pw i r * g.ph i r := by
  unfold precinctsOf
  split
  · rcases p with ⟨l', r', i', k⟩
    simp only [List.mem_map, List.mem_range, PacketId.mk.injEq]
    constructor
    · rintro ⟨k', h, rfl, rfl, rfl, rfl⟩; exact ⟨rfl, rfl, rfl, by assumption, h⟩
    · rintro ⟨rfl, rfl, rfl, -, h⟩; exact ⟨k, h, rfl, rfl, rfl, rfl⟩
  · simp only [List.not_mem_nil, false_iff]
    rintro ⟨-, -, -, h, -⟩; contradiction

private theorem nodup_precinctsOf (l r i : Nat) : (precinctsOf g l r i).Nodup := by
  unfold precinctsOf
  split
  · rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
    exact (List.nodup_iff_pairwise_ne.1 List.nodup_range).imp fun h e => h (by injection e)
  · exact List.nodup_nil

private theorem mem_lrcp (v : Volume) (p : PacketId) :
    p ∈ lrcp g v ↔ g.InPacketSet p ∧ v.InVolume p := by
  rw [inSet_iff, mem_precRefs]
  simp only [lrcp, List.mem_flatMap, layerRange, resRange, compRange, List.mem_range,
    List.mem_range'_1, mem_precinctsOf, prOf]
  constructor
  · rintro ⟨l, hl, r, hr, i, hi, rfl, rfl, rfl, h1, h2⟩
    exact ⟨hl, by omega, by omega, by omega, by omega, h1, h2⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨_, h1, _, ⟨h4, by omega⟩, _, ⟨h2, by omega⟩, rfl, rfl, rfl, h6, h7⟩

private theorem mem_rlcp (v : Volume) (p : PacketId) :
    p ∈ rlcp g v ↔ g.InPacketSet p ∧ v.InVolume p := by
  rw [← mem_lrcp]
  simp only [lrcp, rlcp, List.mem_flatMap]
  constructor
  · rintro ⟨r, hr, l, hl, h⟩; exact ⟨l, hl, r, hr, h⟩
  · rintro ⟨l, hl, r, hr, h⟩; exact ⟨r, hr, l, hl, h⟩

private theorem nodup_lrcp (v : Volume) : (lrcp g v).Nodup := by
  unfold lrcp
  refine nodup_flatMap_proj PacketId.layer List.nodup_range (fun l _ => ?_) ?_
  · refine nodup_flatMap_proj PacketId.res (List.nodup_range' _) (fun r _ => ?_) ?_
    · refine nodup_flatMap_proj PacketId.comp (List.nodup_range' _)
        (fun i _ => nodup_precinctsOf _ _ _) ?_
      intro i _ x hx; exact ((mem_precinctsOf _ _ _ _).1 hx).2.2.1
    · intro r _ x hx
      obtain ⟨i, -, hx⟩ := List.mem_flatMap.1 hx
      exact ((mem_precinctsOf _ _ _ _).1 hx).2.1
  · intro l _ x hx
    obtain ⟨r, -, hx⟩ := List.mem_flatMap.1 hx
    obtain ⟨i, -, hx⟩ := List.mem_flatMap.1 hx
    exact ((mem_precinctsOf _ _ _ _).1 hx).1

private theorem nodup_rlcp (v : Volume) : (rlcp g v).Nodup := by
  unfold rlcp
  refine nodup_flatMap_proj PacketId.res (List.nodup_range' _) (fun r _ => ?_) ?_
  · refine nodup_flatMap_proj PacketId.layer List.nodup_range (fun l _ => ?_) ?_
    · refine nodup_flatMap_proj PacketId.comp (List.nodup_range' _)
        (fun i _ => nodup_precinctsOf _ _ _) ?_
      intro i _ x hx; exact ((mem_precinctsOf _ _ _ _).1 hx).2.2.1
    · intro l _ x hx
      obtain ⟨i, -, hx⟩ := List.mem_flatMap.1 hx
      exact ((mem_precinctsOf _ _ _ _).1 hx).1
  · intro r _ x hx
    obtain ⟨l, -, hx⟩ := List.mem_flatMap.1 hx
    obtain ⟨i, -, hx⟩ := List.mem_flatMap.1 hx
    exact ((mem_precinctsOf _ _ _ _).1 hx).2.1

private theorem mem_visit {i r x y : Nat} {e : PrecRef} :
    e ∈ visit g i r x y ↔ e.comp = i ∧ e.res = r ∧ precAt g i r x y = some e.prec := by
  rcases e with ⟨i', r', k⟩
  unfold visit
  cases precAt g i r x y <;> simp [eq_comm, and_comm]

private theorem comp_lt {v : Volume} {i : Nat} (h : i ∈ compRange g v) : i < g.numComps := by
  simp only [compRange, List.mem_range'_1, Volume.ce] at h; omega

/-- The precincts visited by the B.12.1.3 scan over all points, components and resolutions
of a volume are exactly the volume's precincts. -/
private theorem visit_iff (hwf : g.WF) (v : Volume) (e : PrecRef) :
    (∃ i ∈ compRange g v, ∃ r ∈ resRange g v, ∃ x ∈ xRange g, ∃ y ∈ yRange g,
      e ∈ visit g i r x y) ↔ e ∈ precRefs g v := by
  rw [mem_precRefs]
  constructor
  · rintro ⟨i, hi, r, hr, x, hx, y, hy, he⟩
    obtain ⟨rfl, rfl, h⟩ := mem_visit.1 he
    simp only [xRange, yRange, List.mem_range'_1] at hx hy
    obtain ⟨h1, h2, -, -⟩ := precAt_some hwf (comp_lt hi) hx.1 hy.1 h
    simp only [compRange, resRange, List.mem_range'_1] at hi hr
    exact ⟨hi.1, by omega, hr.1, by omega, h1, h2⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    have hi : e.comp < g.numComps := by simp only [Volume.ce] at h2; omega
    obtain ⟨hx0, hx1, hy0, hy1, hp⟩ := precAt_ref hwf hi h5 h6
    refine ⟨e.comp, ?_, e.res, ?_, _, ?_, _, ?_, mem_visit.2 ⟨rfl, rfl, hp⟩⟩
    · simp only [compRange, List.mem_range'_1]; omega
    · simp only [resRange, List.mem_range'_1]; omega
    · simp only [xRange, List.mem_range'_1]; omega
    · simp only [yRange, List.mem_range'_1]; omega

private theorem visit_key (hwf : g.WF) {v : Volume} {i r x y : Nat} {u : PrecRef}
    (hi : i ∈ compRange g v) (hx : x ∈ xRange g) (hy : y ∈ yRange g)
    (hu : u ∈ visit g i r x y) :
    posKey g .rpcl u = [r, y, x, i, u.prec] ∧ posKey g .pcrl u = [y, x, i, r, u.prec] ∧
      posKey g .cprl u = [i, y, x, r, u.prec] := by
  obtain ⟨h1, h2, h⟩ := mem_visit.1 hu
  simp only [xRange, yRange, List.mem_range'_1] at hx hy
  obtain ⟨-, -, hX, hY⟩ := precAt_some hwf (comp_lt hi) hx.1 hy.1 h
  simp only [posKey, h1, h2, hX, hY, and_self]

private theorem visit_pairwise {R : PrecRef → PrecRef → Prop} (i r x y : Nat) :
    (visit g i r x y).Pairwise R := by
  unfold visit; cases precAt g i r x y <;> simp

private theorem rpcl_sorted (hwf : g.WF) (v : Volume) :
    (rpclPrecincts g v).Pairwise (fun a b => posKey g .rpcl a < posKey g .rpcl b) := by
  unfold rpclPrecincts
  refine pairwise_flatMap_key _ [] (pairwise_range' _ _) (fun r _ => ?_) ?_
  · refine pairwise_flatMap_key _ [r] (pairwise_range' _ _) (fun y hy => ?_) ?_
    · refine pairwise_flatMap_key _ [r, y] (pairwise_range' _ _) (fun x hx => ?_) ?_
      · refine pairwise_flatMap_key _ [r, y, x] (pairwise_range' _ _)
          (fun i _ => visit_pairwise _ _ _ _) ?_
        intro i hi u hu
        exact ⟨[u.prec], (visit_key hwf hi hx hy hu).1⟩
      · intro x hx u hu
        obtain ⟨i, hi, hu⟩ := List.mem_flatMap.1 hu
        exact ⟨[i, u.prec], (visit_key hwf hi hx hy hu).1⟩
    · intro y hy u hu
      obtain ⟨x, hx, hu⟩ := List.mem_flatMap.1 hu
      obtain ⟨i, hi, hu⟩ := List.mem_flatMap.1 hu
      exact ⟨[x, i, u.prec], (visit_key hwf hi hx hy hu).1⟩
  · intro r _ u hu
    obtain ⟨y, hy, hu⟩ := List.mem_flatMap.1 hu
    obtain ⟨x, hx, hu⟩ := List.mem_flatMap.1 hu
    obtain ⟨i, hi, hu⟩ := List.mem_flatMap.1 hu
    exact ⟨[y, x, i, u.prec], (visit_key hwf hi hx hy hu).1⟩

private theorem pcrl_sorted (hwf : g.WF) (v : Volume) :
    (pcrlPrecincts g v).Pairwise (fun a b => posKey g .pcrl a < posKey g .pcrl b) := by
  unfold pcrlPrecincts
  refine pairwise_flatMap_key _ [] (pairwise_range' _ _) (fun y hy => ?_) ?_
  · refine pairwise_flatMap_key _ [y] (pairwise_range' _ _) (fun x hx => ?_) ?_
    · refine pairwise_flatMap_key _ [y, x] (pairwise_range' _ _) (fun i hi => ?_) ?_
      · refine pairwise_flatMap_key _ [y, x, i] (pairwise_range' _ _)
          (fun r _ => visit_pairwise _ _ _ _) ?_
        intro r _ u hu
        exact ⟨[u.prec], (visit_key hwf hi hx hy hu).2.1⟩
      · intro i hi u hu
        obtain ⟨r, -, hu⟩ := List.mem_flatMap.1 hu
        exact ⟨[r, u.prec], (visit_key hwf hi hx hy hu).2.1⟩
    · intro x hx u hu
      obtain ⟨i, hi, hu⟩ := List.mem_flatMap.1 hu
      obtain ⟨r, -, hu⟩ := List.mem_flatMap.1 hu
      exact ⟨[i, r, u.prec], (visit_key hwf hi hx hy hu).2.1⟩
  · intro y hy u hu
    obtain ⟨x, hx, hu⟩ := List.mem_flatMap.1 hu
    obtain ⟨i, hi, hu⟩ := List.mem_flatMap.1 hu
    obtain ⟨r, -, hu⟩ := List.mem_flatMap.1 hu
    exact ⟨[x, i, r, u.prec], (visit_key hwf hi hx hy hu).2.1⟩

private theorem cprl_sorted (hwf : g.WF) (v : Volume) :
    (cprlPrecincts g v).Pairwise (fun a b => posKey g .cprl a < posKey g .cprl b) := by
  unfold cprlPrecincts
  refine pairwise_flatMap_key _ [] (pairwise_range' _ _) (fun i hi => ?_) ?_
  · refine pairwise_flatMap_key _ [i] (pairwise_range' _ _) (fun y hy => ?_) ?_
    · refine pairwise_flatMap_key _ [i, y] (pairwise_range' _ _) (fun x hx => ?_) ?_
      · refine pairwise_flatMap_key _ [i, y, x] (pairwise_range' _ _)
          (fun r _ => visit_pairwise _ _ _ _) ?_
        intro r _ u hu
        exact ⟨[u.prec], (visit_key hwf hi hx hy hu).2.2⟩
      · intro x hx u hu
        obtain ⟨r, -, hu⟩ := List.mem_flatMap.1 hu
        exact ⟨[r, u.prec], (visit_key hwf hi hx hy hu).2.2⟩
    · intro y hy u hu
      obtain ⟨x, hx, hu⟩ := List.mem_flatMap.1 hu
      obtain ⟨r, -, hu⟩ := List.mem_flatMap.1 hu
      exact ⟨[x, r, u.prec], (visit_key hwf hi hx hy hu).2.2⟩
  · intro i hi u hu
    obtain ⟨y, hy, hu⟩ := List.mem_flatMap.1 hu
    obtain ⟨x, hx, hu⟩ := List.mem_flatMap.1 hu
    obtain ⟨r, -, hu⟩ := List.mem_flatMap.1 hu
    exact ⟨[y, x, r, u.prec], (visit_key hwf hi hx hy hu).2.2⟩

private theorem posPrecincts_sorted (hwf : g.WF) (v : Volume) :
    (posPrecincts g v).Pairwise (fun a b => posKey g v.order a < posKey g v.order b) := by
  unfold posPrecincts
  cases v.order
  · exact cprl_sorted hwf v
  · exact cprl_sorted hwf v
  · exact rpcl_sorted hwf v
  · exact pcrl_sorted hwf v
  · exact cprl_sorted hwf v

private theorem mem_posPrecincts (hwf : g.WF) (v : Volume) (e : PrecRef) :
    e ∈ posPrecincts g v ↔ e ∈ precRefs g v := by
  rw [← visit_iff hwf]
  unfold posPrecincts
  cases v.order <;>
  simp only [rpclPrecincts, pcrlPrecincts, cprlPrecincts, List.mem_flatMap] <;>
  constructor
  all_goals first
    | (rintro ⟨i, hi, y, hy, x, hx, r, hr, h⟩; exact ⟨i, hi, r, hr, x, hx, y, hy, h⟩)
    | (rintro ⟨i, hi, r, hr, x, hx, y, hy, h⟩; exact ⟨i, hi, y, hy, x, hx, r, hr, h⟩)
    | (rintro ⟨r, hr, y, hy, x, hx, i, hi, h⟩; exact ⟨i, hi, r, hr, x, hx, y, hy, h⟩)
    | (rintro ⟨i, hi, r, hr, x, hx, y, hy, h⟩; exact ⟨r, hr, y, hy, x, hx, i, hi, h⟩)
    | (rintro ⟨y, hy, x, hx, i, hi, r, hr, h⟩; exact ⟨i, hi, r, hr, x, hx, y, hy, h⟩)
    | (rintro ⟨i, hi, r, hr, x, hx, y, hy, h⟩; exact ⟨y, hy, x, hx, i, hi, r, hr, h⟩)

private theorem posKey_inj {o : Progression} {a b : PrecRef} (h : posKey g o a = posKey g o b) :
    a = b := by
  rcases a with ⟨i, r, k⟩
  rcases b with ⟨i', r', k'⟩
  cases o <;> simp only [posKey, List.cons.injEq] at h <;> simp only [PrecRef.mk.injEq] <;>
    omega

/-- The sorted precinct list of `forPosition` is the B.12.1.3–B.12.1.5 scan (for the volume's
order; LRCP/RLCP volumes fall back to CPRL in both). -/
theorem sortedPrecincts_eq (hwf : g.WF) (v : Volume) :
    sortedPrecincts g v = posPrecincts g v := by
  let le := fun (a b : List Nat × PrecRef) => decide (a.1 ≤ b.1)
  let S := ((precRefs g v).map fun e => (posKey g v.order e, e)).mergeSort le
  have hS : S.Pairwise (fun a b => le a b = true) := by
    apply List.pairwise_mergeSort
    · intro a b c h1 h2
      simp only [le, decide_eq_true_eq] at h1 h2 ⊢
      exact List.le_trans h1 h2
    · intro a b
      simp only [le, Bool.or_eq_true, decide_eq_true_eq]
      exact List.le_total _ _
  have hmemS : ∀ s ∈ S, s.1 = posKey g v.order s.2 ∧ s.2 ∈ precRefs g v := by
    intro s hs
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 (List.mem_mergeSort.1 hs)
    exact ⟨rfl, he⟩
  have hperm : (S.map Prod.snd).Perm (precRefs g v) := by
    have := (List.mergeSort_perm ((precRefs g v).map fun e => (posKey g v.order e, e)) le).map
      Prod.snd
    rw [List.map_map] at this
    have hid : (Prod.snd ∘ fun e : PrecRef => (posKey g v.order e, e)) = id := rfl
    rw [hid, List.map_id] at this
    exact this
  have hnd : (S.map Prod.snd).Nodup := hperm.nodup_iff.2 (nodup_precRefs v)
  show S.map Prod.snd = posPrecincts g v
  apply eq_of_pairwise_key (posKey g v.order)
  · rw [List.pairwise_map]
    rw [List.nodup_iff_pairwise_ne, List.pairwise_map] at hnd
    refine (hS.and hnd).imp_of_mem fun ha hb ⟨h1, h2⟩ => ?_
    simp only [le, decide_eq_true_eq] at h1
    rw [(hmemS _ ha).1, (hmemS _ hb).1] at h1
    rcases List.le_iff_lt_or_eq.1 h1 with h | h
    · exact h
    · exact absurd (posKey_inj h) h2
  · exact posPrecincts_sorted hwf v
  · intro e
    rw [mem_posPrecincts hwf, ← hperm.mem_iff]

end Members

/-! ## C5 and fast = spec -/

section Main

variable {g : Layout}

private theorem mem_withLayers (v : Volume) (ps : List PrecRef) (p : PacketId) :
    p ∈ withLayers g v ps ↔ p.layer < v.le g ∧ prOf p ∈ ps := by
  rcases p with ⟨l, r, i, k⟩
  simp only [withLayers, layerRange, List.mem_flatMap, List.mem_map, List.mem_range, prOf]
  constructor
  · rintro ⟨e, he, l', hl, h⟩
    simp only [PrecRef.packet, PacketId.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    exact ⟨hl, he⟩
  · rintro ⟨hl, he⟩
    exact ⟨_, he, l, hl, rfl⟩

private theorem nodup_withLayers (v : Volume) {ps : List PrecRef} (h : ps.Nodup) :
    (withLayers g v ps).Nodup := by
  unfold withLayers
  refine nodup_flatMap_proj prOf h (fun e _ => ?_) ?_
  · rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
    exact (List.nodup_iff_pairwise_ne.1 List.nodup_range).imp fun h e => h (by
      simp only [PrecRef.packet, PacketId.mk.injEq] at e; exact e.1)
  · intro e _ x hx
    obtain ⟨l, -, rfl⟩ := List.mem_map.1 hx
    rfl

private theorem nodup_posPrecincts (hwf : g.WF) (v : Volume) : (posPrecincts g v).Nodup :=
  List.nodup_iff_pairwise_ne.2 ((posPrecincts_sorted hwf v).imp fun h e => by
    rw [e] at h; exact List.lt_irrefl _ h)

/-- **C5 for one volume** (B.12.1, B.12.2): the packet sequence of any progression volume
visits every packet of the packet set lying in the volume exactly once — it has no
duplicates and its members are exactly those packets. -/
theorem c5_volume (hwf : g.WF) (v : Volume) :
    (volume g v).Nodup ∧ ∀ p, p ∈ volume g v ↔ g.InPacketSet p ∧ v.InVolume p := by
  unfold volume
  split
  · exact ⟨nodup_lrcp v, mem_lrcp v⟩
  · exact ⟨nodup_rlcp v, mem_rlcp v⟩
  · refine ⟨nodup_withLayers v (nodup_posPrecincts hwf v), fun p => ?_⟩
    rw [mem_withLayers, inSet_iff, mem_posPrecincts hwf]

private theorem inVolume_full (o : Progression) {p : PacketId} (h : g.InPacketSet p) :
    (Volume.full g o).InVolume p := by
  have := levels_le_max h.2.1
  simp only [Layout.InPacketSet] at h
  simp only [Volume.InVolume, Volume.full]
  omega

/-- **C5** (Plan.md §4; T.800 B.12.1.1–B.12.1.5): without POC, the packet sequence of each
of the five progression orders visits every `(layer, resolution, component, precinct)` of
the tile's packet set exactly once. For RPCL/PCRL/CPRL the sequence is the literal
point-by-point scan of B.12.1.3–B.12.1.5 over the tile; `WF` (non-zero sub-sampling, B-12
tile-component rectangles) is what makes each precinct visited exactly once. -/
theorem c5 (hwf : g.WF) (o : Progression) :
    (order g o).Nodup ∧ ∀ p, p ∈ order g o ↔ g.InPacketSet p := by
  obtain ⟨h1, h2⟩ := c5_volume hwf (Volume.full g o)
  refine ⟨h1, fun p => ?_⟩
  unfold order
  rw [h2]
  exact ⟨fun h => h.1, fun h => ⟨h, inVolume_full o h⟩⟩

/-- C5 as a bijection: every order's sequence is a permutation of the LRCP sequence. -/
theorem c5_perm (hwf : g.WF) (o : Progression) : (order g o).Perm (order g .lrcp) := by
  rw [List.perm_ext_iff_of_nodup (c5 hwf o).1 (c5 hwf .lrcp).1]
  intro p
  rw [(c5 hwf o).2, (c5 hwf .lrcp).2]

/-- **C5 with POC** (B.12.2): the emitted sequence (each packet at its first occurrence over
the volumes in turn) has no duplicates and consists exactly of the packets of the packet set
lying in at least one volume. -/
theorem c5_poc (hwf : g.WF) (o : Progression) (poc : Array PocEntry) :
    (packets g o poc).Nodup ∧ ∀ p, p ∈ packets g o poc ↔
      g.InPacketSet p ∧ ∃ v ∈ volumes g o poc, v.InVolume p := by
  refine ⟨nodup_dedup _ _, fun p => ?_⟩
  unfold packets
  rw [mem_dedup, List.mem_flatMap]
  simp only [List.not_mem_nil, not_false_eq_true, and_true, (c5_volume hwf _).2]
  constructor
  · rintro ⟨v, hv, h1, h2⟩; exact ⟨h1, v, hv, h2⟩
  · rintro ⟨h1, v, hv, h2⟩; exact ⟨v, hv, h1, h2⟩

/-- Without POC the emitted sequence is the order's sequence. -/
theorem packets_noPoc (hwf : g.WF) (o : Progression) : packets g o #[] = order g o := by
  simp only [packets, volumes, Array.isEmpty_empty, ↓reduceIte, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, order]
  rw [dedup_of_nodup _ _ (c5_volume hwf _).1]
  simp

section Fast
variable {m : Type → Type} [Monad m] [LawfulMonad m] {β : Type}

omit [LawfulMonad m] in
private theorem foldlM_precinctsOf (f : β → PacketId → m β) (l r i : Nat) (b : β) :
    (precinctsOf g l r i).foldlM f b =
      (List.range' 0 (g.numPrecincts i r)).foldlM (fun b k => f b ⟨l, r, i, k⟩) b := by
  unfold precinctsOf Layout.numPrecincts
  split
  · rw [List.foldlM_map, List.range_eq_range']
  · simp

/-- **Fast = spec** for one volume: `forVolume` folds `f` over exactly the B.12 sequence of
the volume, in order. -/
theorem forVolume_eq_spec (hwf : g.WF) (v : Volume) (f : β → PacketId → m β) (b : β) :
    forVolume g v f b = (volume g v).foldlM f b := by
  unfold forVolume volume
  split <;> rename_i hv
  · simp only [hv, forLRCP, lrcp, forRange_eq, foldlM_flatMap, layerRange, resRange, compRange,
      foldlM_precinctsOf, List.range_eq_range']
  · simp only [hv, forRLCP, rlcp, forRange_eq, foldlM_flatMap, layerRange, resRange, compRange,
      foldlM_precinctsOf, List.range_eq_range']
  · simp only [forPosition, withLayers, foldlM_flatMap, sortedPrecincts_eq hwf, forRange_eq,
      layerRange, List.foldlM_map, List.range_eq_range']

private theorem forVolumes_eq (hwf : g.WF) (f : β → PacketId → m β) :
    ∀ (prev vs : List Volume) (b : β), forVolumes g prev vs f b =
      (dedup (prev.flatMap (volume g)) (vs.flatMap (volume g))).foldlM f b
  | _, [], b => by simp [forVolumes, dedup]
  | prev, v :: vs, b => by
    simp only [forVolumes, List.flatMap_cons, dedup_append, List.foldlM_append]
    rw [forVolume_eq_spec hwf, foldlM_skip, dedup_of_nodup _ _ (c5_volume hwf v).1]
    simp only [forVolumes_eq hwf f (prev ++ [v]) vs]
    have hf : (List.filter (fun p => !prev.any (·.contains p)) (volume g v)) =
        List.filter (fun p => !decide (p ∈ List.flatMap (volume g) prev)) (volume g v) := by
      apply List.filter_congr
      intro p hp
      have hp' := ((c5_volume hwf v).2 p).1 hp
      congr 1
      simp only [Volume.contains, List.mem_flatMap, (c5_volume hwf _).2, hp'.1, true_and]
      rw [Bool.eq_iff_iff]
      simp [List.any_eq_true]
    rw [hf, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- **Fast = spec**: `forPackets` folds `f` over exactly the specified packet sequence of
the tile (B.12, with POC volumes and first occurrences). -/
theorem forPackets_eq_spec (hwf : g.WF) (o : Progression) (poc : Array PocEntry)
    (f : β → PacketId → m β) (b : β) :
    forPackets g o poc f b = (packets g o poc).foldlM f b := by
  unfold forPackets packets
  rw [forVolumes_eq hwf f [] _ b]
  rfl

end Fast

end Main

end JPEG2000.Spec.Progression
