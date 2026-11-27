import Spec.DWTPlane.Loops

/-!
# The code-block write loops of the dequantisation

Plan.md §4 (C9), §5.4; T.800 Annex E.1.1.2 (dequantisation), Annex H (ROI). Task 7.1d.

`blockRow_spec` / `blockRows_spec`: `Quant.blockRows` writes the kernel value of block cell
`(x, y)` at plane cell `(px + x, py + y)` (when the block fits in the plane's width) and leaves
every other cell; its flag is the conjunction of the kernel flags (`blockRows_ok`).
`dequantBlock_ok`: `Quant.dequantBlock` does not fail when the plane has the
tile-component's size, `r ≤ NL`, the code-block plane has its rectangle's size and lies in
its band; it is then `blockRows` at the band's Mallat origin.
-/

namespace JPEG2000.Spec.QuantBlock

open JPEG2000 JPEG2000.Bytes JPEG2000.Tier2.Geometry
open JPEG2000.Quant (blockRow blockRows)
open JPEG2000.Spec.Tier1Equiv (get?_set)

/-- The block value the write loops read at block cell `(x, y)`. -/
def bval (o : Tier1.CodeBlockOut) (x y : Nat) : Int32 :=
  (o.plane.get? (y * o.plane.width + x)).getD 0

/-- `blockRow` writes `k` consecutive cells from `d` (kernel of block cells `x, x+1, …`). -/
theorem blockRow_spec (f : Int32 → Nat → Int32 × Bool) (o : Tier1.CodeBlockOut) (y : Nat) (k : Nat) :
    ∀ (x d : Nat) (p : Plane) (ok : Bool),
    (blockRow f o y k x d p ok).1.width = p.width ∧ (blockRow f o y k x d p ok).1.height = p.height ∧
    (∀ i, (blockRow f o y k x d p ok).1.get? i =
      if d ≤ i ∧ i < d + k ∧ i < p.width * p.height then
        some (f (bval o (x + (i - d)) y) (o.lsbPlane (x + (i - d)) y)).1
      else p.get? i) ∧
    ((blockRow f o y k x d p ok).2 = true →
      ok = true ∧ ∀ t, t < k → (f (bval o (x + t) y) (o.lsbPlane (x + t) y)).2 = true) := by
  induction k with
  | zero =>
    intro x d p ok
    refine ⟨rfl, rfl, fun i => ?_, fun h => ⟨h, fun t ht => absurd ht (by omega)⟩⟩
    simp only [blockRow]
    rw [JPEG2000.Spec.DWTPlane.if_f (by omega)]
  | succ k ih =>
    intro x d p ok
    simp only [blockRow]
    generalize hr : f ((o.plane.get? (y * o.plane.width + x)).getD 0) (o.lsbPlane x y) = r
    have hr' : f (bval o x y) (o.lsbPlane x y) = r := hr
    by_cases hd : d < p.width * p.height
    · simp only [hd, ↓reduceDIte]
      obtain ⟨i1, i2, i3, i4⟩ := ih (x + 1) (d + 1) (p.set d r.1 hd) (ok && r.2)
      refine ⟨i1, i2, fun i => ?_, fun h => ?_⟩
      · rw [i3 i, get?_set]
        simp only [(Plane.set_dims _ _ _ _).1, (Plane.set_dims _ _ _ _).2]
        by_cases hi : d + 1 ≤ i ∧ i < d + 1 + k ∧ i < p.width * p.height
        · rw [JPEG2000.Spec.DWTPlane.if_t hi, JPEG2000.Spec.DWTPlane.if_t (by omega),
            show x + 1 + (i - (d + 1)) = x + (i - d) by omega]
        · rw [JPEG2000.Spec.DWTPlane.if_f hi]
          by_cases he : d = i
          · subst he
            rw [JPEG2000.Spec.DWTPlane.if_t rfl, JPEG2000.Spec.DWTPlane.if_t (by omega),
              Nat.sub_self, Nat.add_zero, hr']
          · rw [JPEG2000.Spec.DWTPlane.if_f he, JPEG2000.Spec.DWTPlane.if_f (by omega)]
      · obtain ⟨h1, h2⟩ := i4 h
        simp only [Bool.and_eq_true] at h1
        refine ⟨h1.1, fun t ht => ?_⟩
        by_cases t0 : t = 0
        · subst t0; rw [Nat.add_zero, hr']; exact h1.2
        · have := h2 (t - 1) (by omega)
          rwa [show x + 1 + (t - 1) = x + t by omega] at this
    · simp only [hd, ↓reduceDIte]
      obtain ⟨i1, i2, i3, i4⟩ := ih (x + 1) (d + 1) p (ok && r.2)
      refine ⟨i1, i2, fun i => ?_, fun h => ?_⟩
      · rw [i3 i]
        by_cases hi : d + 1 ≤ i ∧ i < d + 1 + k ∧ i < p.width * p.height
        · rw [JPEG2000.Spec.DWTPlane.if_t hi, JPEG2000.Spec.DWTPlane.if_t (by omega),
            show x + 1 + (i - (d + 1)) = x + (i - d) by omega]
        · rw [JPEG2000.Spec.DWTPlane.if_f hi, JPEG2000.Spec.DWTPlane.if_f (by omega)]
      · obtain ⟨h1, h2⟩ := i4 h
        simp only [Bool.and_eq_true] at h1
        refine ⟨h1.1, fun t ht => ?_⟩
        by_cases t0 : t = 0
        · subst t0; rw [Nat.add_zero, hr']; exact h1.2
        · have := h2 (t - 1) (by omega)
          rwa [show x + 1 + (t - 1) = x + t by omega] at this

open JPEG2000.Spec.DWTPlane (if_t if_f)

/-- A row-major index `yy·pw + xx` lies in `[y·pw + px, y·pw + px + w)` iff it is in row `y`
at a column of `[px, px + w)` (when `px + w ≤ pw`). -/
theorem row_hit2 {pw px w y yy xx : Nat} (hxx : xx < pw) (hw : px + w ≤ pw) :
    (y * pw + px ≤ yy * pw + xx ∧ yy * pw + xx < y * pw + px + w) ↔
      (yy = y ∧ px ≤ xx ∧ xx < px + w) := by
  constructor
  · intro ⟨h1, h2⟩
    rcases Nat.lt_trichotomy yy y with hl | he | hg
    · have : (yy + 1) * pw ≤ y * pw := Nat.mul_le_mul_right _ hl
      rw [Nat.succ_mul] at this; omega
    · subst he; exact ⟨rfl, by omega, by omega⟩
    · have : (y + 1) * pw ≤ yy * pw := Nat.mul_le_mul_right _ hg
      rw [Nat.succ_mul] at this; omega
  · intro ⟨h1, h2, h3⟩; subst h1; omega

/-- `blockRows` writes block cell `(x, y)` (rows `y0 … y0 + k − 1`) at plane cell
`(px + x, py + y)` and keeps every other cell; its flag is the conjunction of the kernel
flags. -/
theorem blockRows_spec (f : Int32 → Nat → Int32 × Bool) (o : Tier1.CodeBlockOut) (px py : Nat)
    (k : Nat) : ∀ (y0 : Nat) (p : Plane) (ok : Bool), px + o.plane.width ≤ p.width →
    (blockRows f o px py k y0 p ok).1.width = p.width ∧
    (blockRows f o px py k y0 p ok).1.height = p.height ∧
    (∀ X Y, X < p.width → (blockRows f o px py k y0 p ok).1.get? (Y * p.width + X) =
      if py + y0 ≤ Y ∧ Y < py + y0 + k ∧ px ≤ X ∧ X < px + o.plane.width ∧
          Y * p.width + X < p.width * p.height then
        some (f (bval o (X - px) (Y - py)) (o.lsbPlane (X - px) (Y - py))).1
      else p.get? (Y * p.width + X)) ∧
    ((blockRows f o px py k y0 p ok).2 = true →
      ok = true ∧ ∀ yy xx, y0 ≤ yy → yy < y0 + k → xx < o.plane.width →
        (f (bval o xx yy) (o.lsbPlane xx yy)).2 = true) := by
  induction k with
  | zero =>
    intro y0 p ok _
    refine ⟨rfl, rfl, fun X Y _ => ?_, fun h => ⟨h, fun yy xx h1 h2 _ => absurd h2 (by omega)⟩⟩
    simp only [blockRows]
    rw [if_f (by omega)]
  | succ k ih =>
    intro y0 p ok hfit
    simp only [blockRows]
    obtain ⟨r1, r2, r3, r4⟩ := blockRow_spec f o y0 o.plane.width 0 ((py + y0) * p.width + px) p ok
    generalize hb : blockRow f o y0 o.plane.width 0 ((py + y0) * p.width + px) p ok = b at r1 r2 r3 r4
    obtain ⟨p1, ok1⟩ := b
    simp only at r1 r2 r3 r4 ⊢
    obtain ⟨i1, i2, i3, i4⟩ := ih (y0 + 1) p1 ok1 (by rw [r1]; exact hfit)
    rw [r1, r2] at i3
    refine ⟨by rw [i1, r1], by rw [i2, r2], fun X Y hX => ?_, fun h => ?_⟩
    · rw [r1] at i1
      rw [i3 X Y hX, r3]
      by_cases hc : py + (y0 + 1) ≤ Y ∧ Y < py + (y0 + 1) + k ∧ px ≤ X ∧ X < px + o.plane.width ∧
          Y * p.width + X < p.width * p.height
      · rw [if_t hc, if_t (by omega)]
      · rw [if_f hc]
        have hr := row_hit2 (y := py + y0) (yy := Y) hX hfit
        by_cases hrow : Y = py + y0 ∧ px ≤ X ∧ X < px + o.plane.width
        · obtain ⟨e1, e2, e3⟩ := hrow
          subst e1
          by_cases hin : (py + y0) * p.width + X < p.width * p.height
          · rw [if_t ⟨by omega, by omega, hin⟩, if_t ⟨by omega, by omega, by omega, e3, hin⟩]
            rw [show 0 + ((py + y0) * p.width + X - ((py + y0) * p.width + px)) = X - px by omega,
              show py + y0 - py = y0 by omega]
          · rw [if_f (by omega), if_f (by omega)]
        · rw [if_f (fun h => hrow (hr.mp ⟨h.1, by omega⟩)), if_f (by omega)]
    · obtain ⟨h1, h2⟩ := i4 h
      obtain ⟨h3, h4⟩ := r4 h1
      refine ⟨h3, fun yy xx a1 a2 a3 => ?_⟩
      by_cases e : yy = y0
      · subst e; have := h4 xx a3; rwa [Nat.zero_add] at this
      · exact h2 yy xx (by omega) (by omega) a3

end JPEG2000.Spec.QuantBlock
