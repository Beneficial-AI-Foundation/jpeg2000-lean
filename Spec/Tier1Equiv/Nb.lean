import Spec.Tier1Equiv.Rel

/-!
# C3 (plain mode), part 3a: publishing a new significance into the neighbours

Plan.md §4 (C3), §5.2 "Tier-1 / EBCOT"; T.800 D.3.2 (a coefficient becomes significant).
Task 3.6.

`JPEG2000.Tier1.becomeSig` writes the coefficient's own word and ORs one mask into each of its
eight neighbours' words (bordered indices `i ± st ± 1`). `flags_after` computes every
in-block word of the result: the own word, or the old word OR `nbMask` of its offset from
the coefficient. `bt_nbMask` says which bits a mask sets: bit `j < 12` exactly when the
neighbour read by bit `j` (`nbPos j`) is the new significant coefficient (sign bits only when
it is negative).
-/

namespace JPEG2000.Spec.Tier1Equiv

open JPEG2000
open JPEG2000.Tier2.Geometry (Band)
open JPEG2000.Spec.Tier1 (Coeff Geom DecState)

/-- A one-bit word has exactly that bit. -/
theorem bt_pow (c : UInt32) (k j : Nat) (h : c.toNat = 2 ^ k) : bt c j = decide (k = j) := by
  simp [bt, h, Nat.testBit_two_pow]

/-- Bits of an `if`. -/
theorem bt_ite (c : Prop) [Decidable c] (a b : UInt32) (j : Nat) :
    bt (if c then a else b) j = if c then bt a j else bt b j := by
  split <;> rfl

/-- Bits of `0`. -/
@[simp] theorem bt_zero (j : Nat) : bt 0 j = false := Nat.zero_testBit j

/-- The bit of `SIG_N`. -/
@[simp] theorem bt_SIG_N (j : Nat) : bt Tier1.SIG_N j = decide (0 = j) := bt_pow _ 0 j rfl

/-- The bit of `SIG_W`. -/
@[simp] theorem bt_SIG_W (j : Nat) : bt Tier1.SIG_W j = decide (1 = j) := bt_pow _ 1 j rfl

/-- The bit of `SIG_E`. -/
@[simp] theorem bt_SIG_E (j : Nat) : bt Tier1.SIG_E j = decide (2 = j) := bt_pow _ 2 j rfl

/-- The bit of `SIG_S`. -/
@[simp] theorem bt_SIG_S (j : Nat) : bt Tier1.SIG_S j = decide (3 = j) := bt_pow _ 3 j rfl

/-- The bit of `SIG_NW`. -/
@[simp] theorem bt_SIG_NW (j : Nat) : bt Tier1.SIG_NW j = decide (4 = j) := bt_pow _ 4 j rfl

/-- The bit of `SIG_NE`. -/
@[simp] theorem bt_SIG_NE (j : Nat) : bt Tier1.SIG_NE j = decide (5 = j) := bt_pow _ 5 j rfl

/-- The bit of `SIG_SW`. -/
@[simp] theorem bt_SIG_SW (j : Nat) : bt Tier1.SIG_SW j = decide (6 = j) := bt_pow _ 6 j rfl

/-- The bit of `SIG_SE`. -/
@[simp] theorem bt_SIG_SE (j : Nat) : bt Tier1.SIG_SE j = decide (7 = j) := bt_pow _ 7 j rfl

/-- The bit of `NEG_N`. -/
@[simp] theorem bt_NEG_N (j : Nat) : bt Tier1.NEG_N j = decide (8 = j) := bt_pow _ 8 j rfl

/-- The bit of `NEG_W`. -/
@[simp] theorem bt_NEG_W (j : Nat) : bt Tier1.NEG_W j = decide (9 = j) := bt_pow _ 9 j rfl

/-- The bit of `NEG_E`. -/
@[simp] theorem bt_NEG_E (j : Nat) : bt Tier1.NEG_E j = decide (10 = j) := bt_pow _ 10 j rfl

/-- The bit of `NEG_S`. -/
@[simp] theorem bt_NEG_S (j : Nat) : bt Tier1.NEG_S j = decide (11 = j) := bt_pow _ 11 j rfl

/-- The bit of `SIG`. -/
@[simp] theorem bt_SIG (j : Nat) : bt Tier1.SIG j = decide (12 = j) := bt_pow _ 12 j rfl

/-- The bit of `NEG`. -/
@[simp] theorem bt_NEG (j : Nat) : bt Tier1.NEG j = decide (13 = j) := bt_pow _ 13 j rfl

/-- The bit of `VIS`. -/
@[simp] theorem bt_VIS (j : Nat) : bt Tier1.VIS j = decide (14 = j) := bt_pow _ 14 j rfl

/-- The bit of `REF`. -/
@[simp] theorem bt_REF (j : Nat) : bt Tier1.REF j = decide (15 = j) := bt_pow _ 15 j rfl

/-- The mask `becomeSig` ORs into the word at offset `(dx, dy)` from a coefficient that becomes
significant (sign `neg`); `0` for any other offset. -/
def nbMask (neg : Bool) (dx dy : Int) : UInt32 :=
  if dx = -1 ∧ dy = -1 then Tier1.SIG_SE
  else if dx = 0 ∧ dy = -1 then (if neg then Tier1.SIG_S ||| Tier1.NEG_S else Tier1.SIG_S)
  else if dx = 1 ∧ dy = -1 then Tier1.SIG_SW
  else if dx = -1 ∧ dy = 0 then (if neg then Tier1.SIG_E ||| Tier1.NEG_E else Tier1.SIG_E)
  else if dx = 1 ∧ dy = 0 then (if neg then Tier1.SIG_W ||| Tier1.NEG_W else Tier1.SIG_W)
  else if dx = -1 ∧ dy = 1 then Tier1.SIG_NE
  else if dx = 0 ∧ dy = 1 then (if neg then Tier1.SIG_N ||| Tier1.NEG_N else Tier1.SIG_N)
  else if dx = 1 ∧ dy = 1 then Tier1.SIG_NW
  else 0

/-- The offset `(x' − x, y' − y)` of a word `(x', y')` whose bit `j` reads the coefficient
`(x, y)` (inverse of `nbPos`). -/
def nbOff (j : Nat) : Int × Int :=
  match j % 8 with
  | 0 => (0, 1)
  | 1 => (1, 0)
  | 2 => (-1, 0)
  | 3 => (0, -1)
  | 4 => (1, 1)
  | 5 => (-1, 1)
  | 6 => (1, -1)
  | _ => (-1, -1)

/-- `nbPos` and `nbOff` are inverse. -/
theorem nbPos_eq_iff (j : Nat) (X Y X' Y' : Int) :
    nbPos j X' Y' = (X, Y) ↔ nbOff j = (X' - X, Y' - Y) := by
  unfold nbPos nbOff
  rcases (by omega : j % 8 = 0 ∨ j % 8 = 1 ∨ j % 8 = 2 ∨ j % 8 = 3 ∨ j % 8 = 4 ∨ j % 8 = 5 ∨
    j % 8 = 6 ∨ j % 8 = 7) with h | h | h | h | h | h | h | h <;>
  simp only [h, Prod.mk.injEq] <;> omega

/-- Bits of `nbMask`: bit `j < 12` is set iff the offset is the one from which bit `j` reads
the coefficient (and, for the sign bits 8–11, it is negative). -/
theorem bt_nbMask (neg : Bool) (dx dy : Int) (j : Nat) (hj : j < 12) :
    bt (nbMask neg dx dy) j = (decide (nbOff j = (dx, dy)) && (decide (j < 8) || neg)) := by
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨
    j = 9 ∨ j = 10 ∨ j = 11) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases (by omega : dx = -1 ∨ dx = 0 ∨ dx = 1 ∨ (dx ≠ -1 ∧ dx ≠ 0 ∧ dx ≠ 1)) with
    h | h | h | h <;>
  rcases (by omega : dy = -1 ∨ dy = 0 ∨ dy = 1 ∨ (dy ≠ -1 ∧ dy ≠ 0 ∧ dy ≠ 1)) with
    h' | h' | h' | h' <;>
  cases neg <;> simp [nbMask, nbOff, h, h', bt_ite] <;> omega

/-- Bits 12–15 of a mask are clear. -/
theorem bt_nbMask_hi (neg : Bool) (dx dy : Int) (j : Nat) (hj1 : 12 ≤ j) :
    bt (nbMask neg dx dy) j = false := by
  simp only [nbMask]
  cases neg <;> (repeat' split) <;> simp <;> omega

/-- No neighbour of a position is the position itself. -/
theorem nbPos_ne (j : Nat) (X Y : Int) : nbPos j X Y ≠ (X, Y) := by
  unfold nbPos
  split <;> simp only [ne_eq, Prod.mk.injEq] <;> omega

/-- The nine indices written by `becomeSig`, as bordered row/column pairs. -/
theorem bidx_forms (w x y : Nat) :
    bidx w x y - (w + 2) - 1 = (y + 0) * (w + 2) + (x + 0) ∧
    bidx w x y - (w + 2) = (y + 0) * (w + 2) + (x + 1) ∧
    bidx w x y - (w + 2) + 1 = (y + 0) * (w + 2) + (x + 2) ∧
    bidx w x y - 1 = (y + 1) * (w + 2) + (x + 0) ∧
    bidx w x y + 1 = (y + 1) * (w + 2) + (x + 2) ∧
    bidx w x y + (w + 2) - 1 = (y + 2) * (w + 2) + (x + 0) ∧
    bidx w x y + (w + 2) = (y + 2) * (w + 2) + (x + 1) ∧
    bidx w x y + (w + 2) + 1 = (y + 2) * (w + 2) + (x + 2) ∧
    bidx w x y = (y + 1) * (w + 2) + (x + 1) := by
  unfold bidx
  have e1 : (y + 1) * (w + 2) = y * (w + 2) + (w + 2) := Nat.succ_mul _ _
  have e2 : (y + 2) * (w + 2) = y * (w + 2) + (w + 2) + (w + 2) := by
    rw [show y + 2 = (y + 1) + 1 from rfl, Nat.succ_mul, e1]
  simp only [Nat.add_zero, e1, e2]
  omega

/-- Equality of a written index with an in-block index, as coordinates. -/
theorem idx_eq_iff {w x y x' y' a c : Nat} (hx : x < w) (hx' : x' < w) (ha : a ≤ 2) :
    (y + c) * (w + 2) + (x + a) = (y' + 1) * (w + 2) + (x' + 1) ↔
      ((x' : Int) - x = a - 1 ∧ (y' : Int) - y = c - 1) := by
  constructor
  · intro e
    obtain ⟨e1, e2⟩ := rowcol_inj (by omega) (by omega) e
    omega
  · intro ⟨e1, e2⟩
    have : x + a = x' + 1 := by omega
    have : y + c = y' + 1 := by omega
    simp only [*]

/-- **The flag words after `becomeSig`**: at the coefficient itself its new own word; at any
other in-block position the old word OR the mask of its offset (`0` if not a neighbour). -/
theorem flags_after (fl0 : Array UInt32) {w h x y : Nat} (hsz : fl0.size = (w + 2) * (h + 2))
    (hx : x < w) (hy : y < h) (own : UInt32) (neg : Bool) {x' y' : Nat} (hx' : x' < w)
    (_hy' : y' < h) :
    let i := bidx w x y
    let st := w + 2
    let fl := Tier1.fset fl0 i own
    let fl := Tier1.fadd fl (i - st - 1) Tier1.SIG_SE
    let fl := Tier1.fadd fl (i - st) (if neg then Tier1.SIG_S ||| Tier1.NEG_S else Tier1.SIG_S)
    let fl := Tier1.fadd fl (i - st + 1) Tier1.SIG_SW
    let fl := Tier1.fadd fl (i - 1) (if neg then Tier1.SIG_E ||| Tier1.NEG_E else Tier1.SIG_E)
    let fl := Tier1.fadd fl (i + 1) (if neg then Tier1.SIG_W ||| Tier1.NEG_W else Tier1.SIG_W)
    let fl := Tier1.fadd fl (i + st - 1) Tier1.SIG_NE
    let fl := Tier1.fadd fl (i + st) (if neg then Tier1.SIG_N ||| Tier1.NEG_N else Tier1.SIG_N)
    let fl := Tier1.fadd fl (i + st + 1) Tier1.SIG_NW
    Tier1.fget fl (bidx w x' y') =
      if x' = x ∧ y' = y then own
      else Tier1.fget fl0 (bidx w x' y') ||| nbMask neg ((x' : Int) - x) ((y' : Int) - y) := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ := bidx_forms w x y
  have k9 : bidx w x' y' = (y' + 1) * (w + 2) + (x' + 1) := (bidx_forms w x' y').2.2.2.2.2.2.2.2
  intro i st
  simp only [i, st]
  rw [f1, f3, f2, f6, f8, f7, f4, f5, f9, k9]
  have L : ∀ a c, a ≤ 2 → c ≤ 2 → (y + c) * (w + 2) + (x + a) < fl0.size := by
    intro a c ha hc; rw [hsz]; exact nb_lt_size hx hy a c ha hc
  rw [fget_fadd _ _ _ _ (by simp only [fadd_size, fset_size]; exact L 2 2 (by decide) (by decide)),
    fget_fadd _ _ _ _ (by simp only [fadd_size, fset_size]; exact L 1 2 (by decide) (by decide)),
    fget_fadd _ _ _ _ (by simp only [fadd_size, fset_size]; exact L 0 2 (by decide) (by decide)),
    fget_fadd _ _ _ _ (by simp only [fadd_size, fset_size]; exact L 2 1 (by decide) (by decide)),
    fget_fadd _ _ _ _ (by simp only [fadd_size, fset_size]; exact L 0 1 (by decide) (by decide)),
    fget_fadd _ _ _ _ (by simp only [fadd_size, fset_size]; exact L 2 0 (by decide) (by decide)),
    fget_fadd _ _ _ _ (by simp only [fadd_size, fset_size]; exact L 1 0 (by decide) (by decide)),
    fget_fadd _ _ _ _ (by simp only [fadd_size, fset_size]; exact L 0 0 (by decide) (by decide)),
    fget_fset _ _ _ _ (L 1 1 (by decide) (by decide))]
  simp only [idx_eq_iff hx hx' (show 0 ≤ 2 by decide), idx_eq_iff hx hx' (show 1 ≤ 2 by decide),
    idx_eq_iff hx hx' (show 2 ≤ 2 by decide)]
  have hs : (x' = x ∧ y' = y) ↔ ((x' : Int) - x = 0 ∧ (y' : Int) - y = 0) := by omega
  simp only [hs]
  generalize (x' : Int) - x = dx
  generalize (y' : Int) - y = dy
  rcases (by omega : dx = -1 ∨ dx = 0 ∨ dx = 1 ∨ (dx ≠ -1 ∧ dx ≠ 0 ∧ dx ≠ 1)) with
    h | h | h | h <;>
  rcases (by omega : dy = -1 ∨ dy = 0 ∨ dy = 1 ∨ (dy ≠ -1 ∧ dy ≠ 0 ∧ dy ≠ 1)) with
    h' | h' | h' | h' <;>
  simp [nbMask, h, h']

end JPEG2000.Spec.Tier1Equiv
