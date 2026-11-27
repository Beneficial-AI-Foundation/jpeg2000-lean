import Spec.DWTPlane.Kernels

/-!
# Plane bookkeeping for the inverse DWT entry points

Plan.md §4 (C9), §5.4 (checked slow path); T.800 Annex F.3.1. Task 7.1d.

The loops keep the plane's width (`levelsG_width`); a buffer cell read through `Plane.get?`
is `rd` (`get?_rd`); `DWT53.cellInt` on the plane is `rd` (`cellInt_rd`); the slow-path
writer `DWT53.ofGrid` stores `sat32` of the grid at every cell (`ofGrid_spec`), and `sat32`
is the `Int32` clamp (`sat32_clamp`).
-/

namespace JPEG2000.Spec.DWTPlane

open JPEG2000 JPEG2000.Bytes
open JPEG2000.DWT53 (Buf loadRow storeRow loadCols storeCols srcIdx batch halfN halfN_le
  cellInt sat32 ofGrid)

/-! ## The loops keep the width -/

/-- `storeRow` keeps the width. -/
theorem storeRow_width {N T : Nat} (pw : Nat) (hN : N = pw * (N / pw)) (W y : Nat) (hW : W ≤ pw)
    (hy : y < N / pw) (tmp : Buf T) (hT : W ≤ T) (P : Buf N) (i : Nat) :
    (storeRow pw hN W y hW hy tmp hT P i).1.width = P.1.width := by
  rw [storeRow]
  split
  · rw [storeRow_width]; rfl
  · rfl
termination_by W - i

/-- `storeCols` keeps the width. -/
theorem storeCols_width {N T : Nat} (pw : Nat) (hN : N = pw * (N / pw)) (H x bw : Nat)
    (hx : x + bw ≤ pw) (hH : H ≤ N / pw) (hT : bw * H ≤ T) (tmp : Buf T) (P : Buf N)
    (i c : Nat) : (storeCols pw hN H x bw hx hH hT tmp P i c).1.width = P.1.width := by
  rw [storeCols]
  split
  · split
    · rw [storeCols_width]; rfl
    · rw [storeCols_width]
  · rfl
termination_by (H - i, bw - c)

/-- `rowPassG` keeps the width. -/
theorem rowPassG_width (K : Kern) {N T : Nat} (pw : Nat) (hN : N = pw * (N / pw)) (u0 u1 H : Nat)
    (hW : u1 - u0 ≤ pw) (hH : H ≤ N / pw) (hT : u1 - u0 ≤ T) (P : Buf N) (tmp : Buf T)
    (ok : Bool) (y : Nat) : (rowPassG K pw hN u0 u1 H hW hH hT P tmp ok y).1.1.width = P.1.width := by
  rw [rowPassG]
  split
  · dsimp only
    rw [rowPassG_width, storeRow_width]
  · rfl
termination_by H - y

/-- `colPassG` keeps the width. -/
theorem colPassG_width (K : Kern) {N T : Nat} (pw : Nat) (hN : N = pw * (N / pw)) (W v0 v1 : Nat)
    (hW : W ≤ pw) (hH : v1 - v0 ≤ N / pw) (hT : batch * (v1 - v0) ≤ T) (P : Buf N) (tmp : Buf T)
    (ok : Bool) (x : Nat) :
    (colPassG K pw hN W v0 v1 hW hH hT P tmp ok x).1.1.width = P.1.width := by
  rw [colPassG]
  split
  · dsimp only
    rw [colPassG_width, storeCols_width]
  · rfl
termination_by W - x
decreasing_by all_goals (simp only [batch]; omega)

/-- `levelsG` keeps the width. -/
theorem levelsG_width (K : Kern) {N T : Nat} (tc : Header.Rect) (pw : Nat) (hN : N = pw * (N / pw))
    (hpw : tc.x1 - tc.x0 ≤ pw) (hph : tc.y1 - tc.y0 ≤ N / pw) (hT : batch * (tc.y1 - tc.y0) ≤ T)
    (hT2 : tc.x1 - tc.x0 ≤ T) (k : Nat) :
    ∀ (P : Buf N) (tmp : Buf T) (ok : Bool),
      (levelsG K tc pw hN hpw hph hT hT2 k P tmp ok).1.1.width = P.1.width := by
  induction k with
  | zero => intro P tmp ok; rfl
  | succ k ih =>
    intro P tmp ok
    simp only [levelsG]
    rw [ih, colPassG_width, rowPassG_width]

/-! ## Reading cells -/

/-- `Plane.get?` on a buffer in range. -/
theorem get?_buf {N : Nat} (b : Buf N) (j : Nat) (hj : j < N) : b.1.get? j = some (b.get j hj) := by
  simp only [Plane.get?, b.2, hj, ↓reduceDIte]; rfl

/-- `Plane.get?` on a buffer in range, as `rd`. -/
theorem get?_rd {N : Nat} (b : Buf N) (j : Nat) (hj : j < N) :
    (b.1.get? j).map Int32.toInt = some (rd b j) := by
  rw [get?_buf b j hj, rd_get b j hj]; rfl

/-- `cellInt` of a plane is `rd` of the plane as a buffer, inside the width. -/
theorem cellInt_rd (p : Plane) (x y : Nat) (hx : x < p.width) :
    cellInt p x y = rd (⟨p, rfl⟩ : Buf (p.width * p.height)) (y * p.width + x) := by
  unfold cellInt
  rw [if_t ⟨by omega, by omega, by omega⟩]
  simp only [Int.toNat_natCast, rd, Plane.get?]
  by_cases h : y * p.width + x < p.width * p.height
  · simp only [h, ↓reduceDIte]; rfl
  · simp only [h, ↓reduceDIte]

/-- `sat32` is the `Int32` clamp. -/
theorem sat32_clamp (z : Int) : (sat32 z).toInt = MCT.clamp32 z := by
  unfold sat32 MCT.clamp32 Spec.MCT.clamp
  by_cases h1 : z < -2147483648
  · simp only [h1, ↓reduceIte]; rfl
  · by_cases h2 : 2147483647 < z
    · simp only [h1, h2, ↓reduceIte]; rfl
    · simp only [h1, h2, ↓reduceIte]
      exact Int32.toInt_ofInt_of_le (by omega) (by omega)

/-! ## `ofGrid` -/

/-- An invariant through a yield-only `for` loop over `List.range' s n` in `Id`. -/
theorem forIn'_range'_inv {β : Type} (P : Nat → β → Prop) (n : Nat) :
    ∀ (s : Nat) (f : (a : Nat) → a ∈ List.range' s n → β → Id (ForInStep β)) (b : β),
    (∀ a h b, P a b → ∃ b', f a h b = ForInStep.yield b' ∧ P (a + 1) b') → P s b →
    P (s + n) (Id.run (forIn' (List.range' s n) b f)) := by
  induction n with
  | zero => intro s f b _ hb; exact hb
  | succ n ih =>
    intro s f b hf hb
    generalize hl : List.range' s (n + 1) = l at f hf
    rw [List.range'_succ] at hl
    subst hl
    rw [List.forIn'_cons]
    obtain ⟨b', he, hp⟩ := hf s List.mem_cons_self b hb
    rw [he]
    have := ih (s + 1) (fun a m b => f a (List.mem_cons_of_mem _ m) b) b'
      (fun a h b hb => hf a _ b hb) hp
    rw [show s + 1 + n = s + (n + 1) by omega] at this
    exact this

/-- Row-major index arithmetic. -/
theorem divmod_idx {x y w : Nat} (hx : x < w) : (y * w + x) / w = y ∧ (y * w + x) % w = x := by
  have hw : 0 < w := by omega
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt hx, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx]

/-- An invariant through a yield-only `for` loop over `[0:n]` in `Id`. -/
theorem forIn'_range_inv {β : Type} (P : Nat → β → Prop) (n : Nat)
    (f : (a : Nat) → a ∈ [0:n] → β → Id (ForInStep β)) (b : β)
    (hf : ∀ a h b, P a b → ∃ b', f a h b = ForInStep.yield b' ∧ P (a + 1) b') (hb : P 0 b) :
    P n (Id.run (forIn' [0:n] b f)) := by
  rw [Std.Legacy.Range.forIn'_eq_forIn'_range']
  have hs : Std.Legacy.Range.size [0:n] = n := by simp [Std.Legacy.Range.size]
  have key : ∀ (m : Nat) (g : (a : Nat) → a ∈ List.range' 0 m 1 → β → Id (ForInStep β)),
      (∀ a h b, P a b → ∃ b', g a h b = ForInStep.yield b' ∧ P (a + 1) b') → m = n →
      P n (Id.run (forIn' (List.range' 0 m 1) b g)) := by
    intro m g hg hm
    have := forIn'_range'_inv P m 0 g b hg hb
    subst hm; rw [Nat.zero_add] at this; exact this
  exact key _ _ (fun a h b hb => hf a _ b hb) hs

/-- The loops of `ofGrid`. -/
def ofGridLoop (g : Spec.DWT53.Grid) (x0 y0 : Int) (w h : Nat) : Buf (w * h) :=
  Id.run (forIn' [0:h] (⟨Plane.zero w h, rfl⟩ : Buf (w * h)) fun y hy out =>
    ForInStep.yield (Id.run (forIn' [0:w] out fun x hx out =>
      ForInStep.yield (out.set (y * w + x) (sat32 (g.get (x0 + x) (y0 + y)))
        (DWT53.idx_lt hx.upper hy.upper)))))

/-- `ofGrid` is `ofGridLoop`. -/
theorem ofGrid_eq (g : Spec.DWT53.Grid) (x0 y0 : Int) (w h : Nat) :
    ofGrid g x0 y0 w h = (ofGridLoop g x0 y0 w h).1 := rfl

/-- **`ofGrid` writes `sat32 (g (x0 + x) (y0 + y))` at every cell** and has size `w × h`. -/
theorem ofGrid_spec (g : Spec.DWT53.Grid) (x0 y0 : Int) (w h : Nat) :
    (ofGrid g x0 y0 w h).width = w ∧ (ofGrid g x0 y0 w h).height = h ∧
    ∀ j, j < w * h → (ofGrid g x0 y0 w h).get? j =
      some (sat32 (g.get (x0 + (j % w : Nat)) (y0 + (j / w : Nat)))) := by
  let V : Nat → Int32 := fun j => sat32 (g.get (x0 + (j % w : Nat)) (y0 + (j / w : Nat)))
  let Q : Nat → Buf (w * h) → Prop := fun y out =>
    out.1.width = w ∧ out.1.height = h ∧ ∀ j, j < y * w → j < w * h → rd out j = (V j).toInt
  have hout : Q h (ofGridLoop g x0 y0 w h) := by
    refine forIn'_range_inv Q h _ _ ?_ ⟨rfl, rfl, fun j hj _ => by simp at hj⟩
    intro y hy out hQ
    refine ⟨_, rfl, ?_⟩
    have hy' : y < h := hy.upper
    let Qi : Nat → Buf (w * h) → Prop := fun x o =>
      o.1.width = w ∧ o.1.height = h ∧ ∀ j, j < y * w + x → j < w * h → rd o j = (V j).toInt
    have key : ∀ o, Qi w o → Q (y + 1) o := by
      intro o hi
      refine ⟨hi.1, hi.2.1, fun j hj hj' => hi.2.2 j ?_ hj'⟩
      rw [Nat.succ_mul] at hj
      exact hj
    apply key
    refine forIn'_range_inv Qi w _ out ?_ ⟨hQ.1, hQ.2.1, fun j hj hj' => hQ.2.2 j (by omega) hj'⟩
    intro x hx o hQi
    refine ⟨_, rfl, ?_⟩
    refine ⟨hQi.1, hQi.2.1, fun j hj hj' => ?_⟩
    have hx' : x < w := hx.upper
    rw [rd_set]
    by_cases he : y * w + x = j
    · subst he
      rw [if_t rfl]
      simp only [V, (divmod_idx hx').1, (divmod_idx hx').2]
    · rw [if_f he]; exact hQi.2.2 j (by omega) hj'
  rw [ofGrid_eq]
  obtain ⟨h1, h2, h3⟩ := hout
  refine ⟨h1, h2, fun j hj => ?_⟩
  rw [get?_buf _ j hj]
  congr 1
  apply Int32.toInt_inj.mp
  rw [← rd_get]
  exact h3 j (by rw [Nat.mul_comm]; exact hj) hj

end JPEG2000.Spec.DWTPlane
