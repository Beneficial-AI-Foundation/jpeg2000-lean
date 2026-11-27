/-!
# Deterministic PRNG for the fuzz harness (task 9.1)

Plan.md §8.6. SplitMix64: a pure state transformer, so a case is a function of `(seed, index)`
and can be replayed with `fuzz --seed S --start I --iters 1`.
-/

namespace Fuzz

/-- SplitMix64 state. -/
structure Rng where
  /-- The 64-bit state. -/
  s : UInt64

/-- Mixes a seed and a case index into the state of that case. -/
def Rng.ofCase (seed idx : Nat) : Rng :=
  ⟨seed.toUInt64 * 0x2545F4914F6CDD1D + idx.toUInt64 * 0x9E3779B97F4A7C15 + 1⟩

/-- The next 64 random bits and the new state. -/
def Rng.next (r : Rng) : UInt64 × Rng :=
  let s := r.s + 0x9E3779B97F4A7C15
  let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), ⟨s⟩)

/-- The random monad of the mutators. -/
abbrev R := StateM Rng

/-- 64 random bits. -/
def rnd64 : R UInt64 := modifyGet Rng.next

/-- A uniform number below `n` (0 when `n = 0`). -/
def below (n : Nat) : R Nat := do
  let v ← rnd64
  pure (if n == 0 then 0 else v.toNat % n)

/-- A uniform number in `lo … hi` (inclusive). -/
def between (lo hi : Nat) : R Nat := do
  let v ← below (hi + 1 - lo)
  pure (lo + v)

/-- True with probability `num / den`. -/
def chance (num den : Nat) : R Bool := do
  let v ← below den
  pure (v < num)

/-- A uniformly chosen element (the default for an empty array). -/
def pick {α : Type} [Inhabited α] (xs : Array α) : R α := do
  let i ← below xs.size
  pure (xs.getD i default)

end Fuzz
