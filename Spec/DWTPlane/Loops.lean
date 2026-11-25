import Spec.Equiv
import Spec.DWTPlane.Geometry

/-!
# The plane loops of the inverse DWT (rows, column batches, levels), proved

Plan.md §4 (C6, C8, C9), §5.2 "DWT", §6 item 5 (row pass, then column pass over batches of
columns); T.800 Annex F.3 (`IDWT`, `2D_SR`, `2D_INTERLEAVE`, `HOR_SR`, `VER_SR`). Task 7.1d.

The 5/3 (`JPEG2000.DWT53`) and 9/7 (`JPEG2000.DWT97`) fast paths share their load/store loops
and differ only in the 1-D kernel (`lift1d` / `lift1d97`). This file restates their row pass,
column-batch pass and level loop with the kernel as a parameter (`rowPassG`, `liftColsG`,
`colPassG`, `levelsG`; the fast definitions are these instances, `rowPass53_eq` …, proved by
unfolding) and proves them once for every kernel satisfying `KSpec` (cell-wise contract of a
1-D in-place kernel: it computes a 1-D operator `op` on its range, leaves the other cells
alone, only clears its flag, and `op` is local).

Cells are read with `rd` (the cell as an `Int`, 0 out of range).
-/

namespace JPEG2000.Spec.DWTPlane

open JPEG2000 JPEG2000.Bytes
open JPEG2000.DWT53 (Buf loadRow storeRow loadCols storeCols srcIdx batch halfN halfN_le idx_lt)

/-- `if` with a true condition (non-deprecated `if_pos`). -/
theorem if_t {α : Type} {c : Prop} [Decidable c] (h : c) {a b : α} : (if c then a else b) = a := by
  simp [h]

/-- `if` with a false condition (non-deprecated `if_neg`). -/
theorem if_f {α : Type} {c : Prop} [Decidable c] (h : ¬c) {a b : α} : (if c then a else b) = b := by
  simp [h]

/-! ## Cells -/

/-- Cell `i` of a buffer as an `Int` (0 out of range). -/
def rd {N : Nat} (b : Buf N) (i : Nat) : Int := if h : i < N then (b.get i h).toInt else 0

/-- Reading back a write. -/
theorem rd_set {N : Nat} (b : Buf N) (i : Nat) (v : Int32) (h : i < N) (j : Nat) :
    rd (b.set i v h) j = if i = j then v.toInt else rd b j := by
  unfold rd
  by_cases hj : j < N
  · simp only [hj, ↓reduceDIte, DWT53.Buf.get_set]; split <;> rfl
  · have : i ≠ j := by omega
    simp [hj, this]

/-- `rd` in range is the cell. -/
theorem rd_get {N : Nat} (b : Buf N) (i : Nat) (h : i < N) : rd b i = (b.get i h).toInt := by
  simp [rd, h]

/-- Row-major indices determine their coordinates. -/
theorem idx_inj {x x' y y' w : Nat} (hx : x < w) (hx' : x' < w) (h : y * w + x = y' * w + x') :
    y = y' ∧ x = x' := by
  have hy : y = y' := by
    rcases Nat.lt_trichotomy y y' with hl | he | hg
    · have : (y + 1) * w ≤ y' * w := Nat.mul_le_mul_right _ hl
      rw [Nat.succ_mul] at this; omega
    · exact he
    · have : (y' + 1) * w ≤ y * w := Nat.mul_le_mul_right _ hg
      rw [Nat.succ_mul] at this; omega
  subst hy; exact ⟨rfl, by omega⟩

/-! ## Load / store loops -/

/-- `loadRow` loads row `y` interleaved: cell `k` of `tmp` is the Mallat cell `srcIdx k`. -/
theorem loadRow_spec {N T : Nat} (pw : Nat) (hN : N = pw * (N / pw)) (u0 u1 y : Nat)
    (hW : u1 - u0 ≤ pw) (hy : y < N / pw) (P : Buf N) (hT : u1 - u0 ≤ T) (tmp : Buf T) (i : Nat) :
    ∀ k, k < u1 - u0 → rd (loadRow pw hN u0 u1 y hW hy P hT tmp i) k =
      if k < i then rd tmp k else rd P (y * pw + srcIdx u0 ((u1 + 1) / 2 - (u0 + 1) / 2) k) := by
  rw [loadRow]
  split
  · rename_i hi
    intro k hk
    rw [loadRow_spec pw hN u0 u1 y hW hy P hT _ (i + 1) k hk, rd_set]
    by_cases hki : k < i
    · simp [hki, show k < i + 1 by omega, show i ≠ k by omega]
    · by_cases hke : k = i
      · subst hke
        simp only [show k < k + 1 by omega, ↓reduceIte, hki]
        rw [rd_get]
      · simp only [hki, show ¬ k < i + 1 by omega, ↓reduceIte]
  · rename_i hi
    intro k hk
    simp only [show k < i by omega, ↓reduceIte]
termination_by u1 - u0 - i

/-- `storeRow` writes `tmp[0, W)` to row `y`. -/
theorem storeRow_spec {N T : Nat} (pw : Nat) (hN : N = pw * (N / pw)) (W y : Nat) (hW : W ≤ pw)
    (hy : y < N / pw) (tmp : Buf T) (hT : W ≤ T) (P : Buf N) (i : Nat) :
    ∀ j, rd (storeRow pw hN W y hW hy tmp hT P i) j =
      if y * pw + i ≤ j ∧ j < y * pw + W then rd tmp (j - y * pw) else rd P j := by
  rw [storeRow]
  split
  · rename_i hi
    intro j
    rw [storeRow_spec pw hN W y hW hy tmp hT _ (i + 1) j, rd_set]
    by_cases hj : j = y * pw + i
    · subst hj
      simp only [show ¬ (y * pw + (i + 1) ≤ y * pw + i) by omega, false_and, ↓reduceIte,
        show y * pw + i ≤ y * pw + i by omega, show y * pw + i < y * pw + W by omega, and_self,
        Nat.add_sub_cancel_left]
      rw [rd_get _ _ (by omega)]
    · simp only [show y * pw + i ≠ j by omega, ↓reduceIte]
      by_cases hc : y * pw + i ≤ j ∧ j < y * pw + W
      · simp only [hc, show y * pw + (i + 1) ≤ j ∧ j < y * pw + W by omega, and_self, ↓reduceIte]
      · simp only [hc, show ¬ (y * pw + (i + 1) ≤ j ∧ j < y * pw + W) by omega, ↓reduceIte]
  · rename_i hi
    intro j
    simp only [show ¬ (y * pw + i ≤ j ∧ j < y * pw + W) by omega, ↓reduceIte]
termination_by W - i

/-- `loadCols` loads the column batch: cell `cc·H + ii` of `tmp` is the Mallat cell
`(x + cc, srcIdx ii)`. -/
theorem loadCols_spec {N T : Nat} (pw : Nat) (hN : N = pw * (N / pw)) (v0 v1 x bw : Nat)
    (hx : x + bw ≤ pw) (hH : v1 - v0 ≤ N / pw) (hT : bw * (v1 - v0) ≤ T) (P : Buf N)
    (tmp : Buf T) (i c : Nat) :
    ∀ cc ii, cc < bw → ii < v1 - v0 →
      rd (loadCols pw hN v0 v1 x bw hx hH hT P tmp i c) (cc * (v1 - v0) + ii) =
        if ii < i ∨ (ii = i ∧ cc < c) then rd tmp (cc * (v1 - v0) + ii)
        else rd P (srcIdx v0 ((v1 + 1) / 2 - (v0 + 1) / 2) ii * pw + (x + cc)) := by
  rw [loadCols]
  split
  · rename_i hi
    split
    · rename_i hc
      intro cc ii hcc hii
      rw [loadCols_spec pw hN v0 v1 x bw hx hH hT P _ i (c + 1) cc ii hcc hii, rd_set]
      by_cases he : c * (v1 - v0) + i = cc * (v1 - v0) + ii
      · obtain ⟨h1, h2⟩ := idx_inj hi hii he
        subst h1; subst h2
        simp only [Nat.lt_irrefl, false_or, true_and, Nat.lt_succ_self, ↓reduceIte]
        have := idx_lt (x := i) (y := c) (w := v1 - v0) (h := bw) hi hc
        rw [Nat.mul_comm (v1 - v0) bw] at this
        rw [rd_get]
      · simp only [he, ↓reduceIte]
        have hne : ¬ (ii = i ∧ cc = c) := fun ⟨a, b⟩ => he (by rw [a, b])
        by_cases h1 : ii < i ∨ (ii = i ∧ cc < c)
        · simp only [h1, show ii < i ∨ (ii = i ∧ cc < c + 1) by omega, ↓reduceIte]
        · simp only [h1, show ¬ (ii < i ∨ (ii = i ∧ cc < c + 1)) by omega, ↓reduceIte]
    · rename_i hc
      intro cc ii hcc hii
      rw [loadCols_spec pw hN v0 v1 x bw hx hH hT P _ (i + 1) 0 cc ii hcc hii]
      by_cases h1 : ii < i ∨ (ii = i ∧ cc < c)
      · simp only [h1, show ii < i + 1 ∨ (ii = i + 1 ∧ cc < 0) by omega, ↓reduceIte]
      · simp only [h1, show ¬ (ii < i + 1 ∨ (ii = i + 1 ∧ cc < 0)) by omega, ↓reduceIte]
  · rename_i hi
    intro cc ii hcc hii
    simp only [show ii < i ∨ (ii = i ∧ cc < c) by omega, ↓reduceIte]
termination_by (v1 - v0 - i, bw - c)

/-- `storeCols` writes the batch back: plane cell `(xx, ii)` for `x ≤ xx < x + bw`, `ii < H`
is `tmp[(xx − x)·H + ii]`. -/
theorem storeCols_spec {N T : Nat} (pw : Nat) (hN : N = pw * (N / pw)) (H x bw : Nat)
    (hx : x + bw ≤ pw) (hH : H ≤ N / pw) (hT : bw * H ≤ T) (tmp : Buf T) (P : Buf N)
    (i c : Nat) :
    ∀ ii xx, xx < pw → rd (storeCols pw hN H x bw hx hH hT tmp P i c) (ii * pw + xx) =
      if ii < H ∧ x ≤ xx ∧ xx < x + bw ∧ (i < ii ∨ (ii = i ∧ c ≤ xx - x)) then
        rd tmp ((xx - x) * H + ii)
      else rd P (ii * pw + xx) := by
  rw [storeCols]
  split
  · rename_i hi
    split
    · rename_i hc
      intro ii xx hxx
      rw [storeCols_spec pw hN H x bw hx hH hT tmp _ i (c + 1) ii xx hxx, rd_set]
      by_cases he : i * pw + (x + c) = ii * pw + xx
      · obtain ⟨h1, h2⟩ := idx_inj (by omega) hxx he
        subst h1; subst h2
        have e1 : x + c - x = c := by omega
        simp only [e1, Nat.lt_irrefl, false_or, true_and, ↓reduceIte, hi,
          show ¬ (c + 1 ≤ c) by omega, show x ≤ x + c by omega, show x + c < x + bw by omega,
          Nat.le_refl, and_self]
        have := idx_lt (x := i) (y := c) (w := H) (h := bw) hi hc
        rw [Nat.mul_comm H bw] at this
        rw [rd_get _ _ (by omega)]
      · simp only [he, ↓reduceIte]
        have hne : ¬ (ii = i ∧ xx = x + c) := fun ⟨a, b⟩ => he (by rw [a, b])
        by_cases h1 : ii < H ∧ x ≤ xx ∧ xx < x + bw ∧ (i < ii ∨ (ii = i ∧ c ≤ xx - x))
        · simp only [h1, show ii < H ∧ x ≤ xx ∧ xx < x + bw ∧ (i < ii ∨ (ii = i ∧ c + 1 ≤ xx - x))
            by omega]
        · simp only [h1, show ¬ (ii < H ∧ x ≤ xx ∧ xx < x + bw ∧
            (i < ii ∨ (ii = i ∧ c + 1 ≤ xx - x))) by omega, ↓reduceIte]
    · rename_i hc
      intro ii xx hxx
      rw [storeCols_spec pw hN H x bw hx hH hT tmp _ (i + 1) 0 ii xx hxx]
      by_cases h1 : ii < H ∧ x ≤ xx ∧ xx < x + bw ∧ (i < ii ∨ (ii = i ∧ c ≤ xx - x))
      · simp only [h1, show ii < H ∧ x ≤ xx ∧ xx < x + bw ∧ (i + 1 < ii ∨ (ii = i + 1 ∧ 0 ≤ xx - x))
          by omega]
      · simp only [h1, show ¬ (ii < H ∧ x ≤ xx ∧ xx < x + bw ∧
          (i + 1 < ii ∨ (ii = i + 1 ∧ 0 ≤ xx - x))) by omega, ↓reduceIte]
  · rename_i hi
    intro ii xx hxx
    simp only [show ¬ (ii < H ∧ x ≤ xx ∧ xx < x + bw ∧ (i < ii ∨ (ii = i ∧ c ≤ xx - x))) by omega,
      ↓reduceIte]
termination_by (H - i, bw - c)

/-! ## Kernels and the generic loops -/

/-- An in-place 1-D kernel on cells `[off, off + n)` of a buffer with start parity `par` and an
overflow flag (`DWT53.lift1d`, `DWT97.lift1d97`). -/
abbrev Kern := ∀ {N : Nat} (off n : Nat), Nat → off + n ≤ N → Buf N → Bool → Buf N × Bool

/-- The contract of a kernel: when its flag stays `true` it computes the 1-D operator `op` on
its range (and the overflow predicate `okP` holds of its input signal), it never touches
cells outside its range, it only clears its flag; `op` and `okP` read their signal only on
the range. -/
structure KSpec (K : Kern) (op : Int → Int → (Int → Int) → Int → Int)
    (okP : Int → Int → (Int → Int) → Prop) : Prop where
  /-- The flag only goes from `true` to `false`. -/
  mono : ∀ {N : Nat} (off n par : Nat) (hN : off + n ≤ N) (b : Buf N) (ok : Bool),
    (K off n par hN b ok).2 = true → ok = true
  /-- Cells outside the range are unchanged. -/
  frame : ∀ {N : Nat} (off n par : Nat) (hN : off + n ≤ N) (b : Buf N) (ok : Bool) (j : Nat),
    (j < off ∨ off + n ≤ j) → rd (K off n par hN b ok).1 j = rd b j
  /-- Cells inside the range hold `op` of the input signal. -/
  val : ∀ {N : Nat} (off n par : Nat) (hN : off + n ≤ N) (b : Buf N) (ok : Bool) (i0 : Int),
    i0 % 2 = ((par % 2 : Nat) : Int) → ∀ y : Int → Int,
    (∀ k, k < n → rd b (off + k) = y (i0 + k)) → (K off n par hN b ok).2 = true →
    (∀ k, k < n → rd (K off n par hN b ok).1 (off + k) = op i0 (i0 + n) y (i0 + k)) ∧
      okP i0 (i0 + n) y
  /-- `okP` holds of an empty range. -/
  triv : ∀ (i0 i1 : Int) (y : Int → Int), i1 ≤ i0 → okP i0 i1 y
  /-- `op` and `okP` are local to the range. -/
  loc : ∀ (i0 i1 : Int) (y y' : Int → Int), (∀ k, i0 ≤ k → k < i1 → y k = y' k) →
    (∀ j, i0 ≤ j → j < i1 → op i0 i1 y j = op i0 i1 y' j) ∧ (okP i0 i1 y → okP i0 i1 y')

/-- `HOR_SR` on rows `y, …, H − 1` with kernel `K` (`DWT53.rowPass` with the kernel as a
parameter). -/
def rowPassG (K : Kern) {N T : Nat} (pw : Nat) (hN : N = pw * (N / pw)) (u0 u1 H : Nat)
    (hW : u1 - u0 ≤ pw) (hH : H ≤ N / pw) (hT : u1 - u0 ≤ T) (P : Buf N) (tmp : Buf T)
    (ok : Bool) (y : Nat) : Buf N × Buf T × Bool :=
  if hy : y < H then
    let tmp := loadRow pw hN u0 u1 y hW (by omega) P hT tmp 0
    let (tmp, ok) := K 0 (u1 - u0) (u0 % 2) (by omega) tmp ok
    let P := storeRow pw hN (u1 - u0) y hW (by omega) tmp hT P 0
    rowPassG K pw hN u0 u1 H hW hH hT P tmp ok (y + 1)
  else (P, tmp, ok)
termination_by H - y

/-- `DWT53.liftCols` with the kernel as a parameter. -/
def liftColsG (K : Kern) {T : Nat} (H par bw : Nat) (hT : bw * H ≤ T) (tmp : Buf T) (ok : Bool)
    (c : Nat) : Buf T × Bool :=
  if hc : c < bw then
    have : c * H + H ≤ bw * H := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hc
    let (tmp, ok) := K (c * H) H par (by omega) tmp ok
    liftColsG K H par bw hT tmp ok (c + 1)
  else (tmp, ok)
termination_by bw - c

/-- `DWT53.colPass` with the kernel as a parameter. -/
def colPassG (K : Kern) {N T : Nat} (pw : Nat) (hN : N = pw * (N / pw)) (W v0 v1 : Nat)
    (hW : W ≤ pw) (hH : v1 - v0 ≤ N / pw) (hT : batch * (v1 - v0) ≤ T) (P : Buf N) (tmp : Buf T)
    (ok : Bool) (x : Nat) : Buf N × Buf T × Bool :=
  if hx : x < W then
    let bw := min batch (W - x)
    have hbw : bw * (v1 - v0) ≤ T :=
      Nat.le_trans (Nat.mul_le_mul_right _ (Nat.min_le_left _ _)) hT
    have hxb : x + bw ≤ pw := by omega
    let tmp := loadCols pw hN v0 v1 x bw hxb hH hbw P tmp 0 0
    let (tmp, ok) := liftColsG K (v1 - v0) (v0 % 2) bw hbw tmp ok 0
    let P := storeCols pw hN (v1 - v0) x bw hxb hH hbw tmp P 0 0
    have : 0 < bw := by simp only [bw, batch]; omega
    colPassG K pw hN W v0 v1 hW hH hT P tmp ok (x + bw)
  else (P, tmp, ok)
termination_by W - x

/-- `DWT53.levels` with the kernel as a parameter. -/
def levelsG (K : Kern) {N T : Nat} (tc : Header.Rect) (pw : Nat) (hN : N = pw * (N / pw))
    (hpw : tc.x1 - tc.x0 ≤ pw) (hph : tc.y1 - tc.y0 ≤ N / pw)
    (hT : batch * (tc.y1 - tc.y0) ≤ T) (hT2 : tc.x1 - tc.x0 ≤ T) :
    Nat → Buf N → Buf T → Bool → Buf N × Bool
  | 0, P, _, ok => (P, ok)
  | k + 1, P, tmp, ok =>
    let r := halfN tc k
    have hr : r.x1 - r.x0 ≤ tc.x1 - tc.x0 ∧ r.y1 - r.y0 ≤ tc.y1 - tc.y0 := halfN_le tc k
    let (P, tmp, ok) := rowPassG K pw hN r.x0 r.x1 (r.y1 - r.y0) (by omega) (by omega) (by omega)
      P tmp ok 0
    let (P, tmp, ok) := colPassG K pw hN (r.x1 - r.x0) r.y0 r.y1 (by omega) (by omega)
      (Nat.le_trans (Nat.mul_le_mul_left _ hr.2) hT) P tmp ok 0
    levelsG K tc pw hN hpw hph hT hT2 k P tmp ok

/-! ### The fast loops are instances -/

section Instances
variable {N T : Nat} (pw : Nat) (hN : N = pw * (N / pw))

/-- `DWT53.rowPass` is `rowPassG` with `lift1d`. -/
theorem rowPass53_eq (u0 u1 H : Nat) (hW : u1 - u0 ≤ pw) (hH : H ≤ N / pw) (hT : u1 - u0 ≤ T)
    (P : Buf N) (tmp : Buf T) (ok : Bool) (y : Nat) :
    DWT53.rowPass pw hN u0 u1 H hW hH hT P tmp ok y =
      rowPassG (fun off n par hN b ok => DWT53.lift1d off n par hN b ok) pw hN u0 u1 H hW hH hT
        P tmp ok y := by
  rw [DWT53.rowPass, rowPassG]
  split
  · dsimp only; rw [rowPass53_eq]
  · rfl
termination_by H - y

/-- `DWT97.rowPass` is `rowPassG` with `lift1d97`. -/
theorem rowPass97_eq (u0 u1 H : Nat) (hW : u1 - u0 ≤ pw) (hH : H ≤ N / pw) (hT : u1 - u0 ≤ T)
    (P : Buf N) (tmp : Buf T) (ok : Bool) (y : Nat) :
    DWT97.rowPass pw hN u0 u1 H hW hH hT P tmp ok y =
      rowPassG (fun off n par hN b ok => DWT97.lift1d97 off n par hN b ok) pw hN u0 u1 H hW hH hT
        P tmp ok y := by
  rw [DWT97.rowPass, rowPassG]
  split
  · dsimp only; rw [rowPass97_eq]
  · rfl
termination_by H - y

/-- `DWT53.liftCols` is `liftColsG` with `lift1d`. -/
theorem liftCols53_eq (H par bw : Nat) (hT : bw * H ≤ T) (tmp : Buf T) (ok : Bool) (c : Nat) :
    DWT53.liftCols H par bw hT tmp ok c =
      liftColsG (fun off n par hN b ok => DWT53.lift1d off n par hN b ok) H par bw hT tmp ok c := by
  rw [DWT53.liftCols, liftColsG]
  split
  · dsimp only; rw [liftCols53_eq]
  · rfl
termination_by bw - c

/-- `DWT97.liftCols` is `liftColsG` with `lift1d97`. -/
theorem liftCols97_eq (H par bw : Nat) (hT : bw * H ≤ T) (tmp : Buf T) (ok : Bool) (c : Nat) :
    DWT97.liftCols H par bw hT tmp ok c =
      liftColsG (fun off n par hN b ok => DWT97.lift1d97 off n par hN b ok) H par bw hT tmp ok c := by
  rw [DWT97.liftCols, liftColsG]
  split
  · dsimp only; rw [liftCols97_eq]
  · rfl
termination_by bw - c

/-- `DWT53.colPass` is `colPassG` with `lift1d`. -/
theorem colPass53_eq (W v0 v1 : Nat) (hW : W ≤ pw) (hH : v1 - v0 ≤ N / pw)
    (hT : batch * (v1 - v0) ≤ T) (P : Buf N) (tmp : Buf T) (ok : Bool) (x : Nat) :
    DWT53.colPass pw hN W v0 v1 hW hH hT P tmp ok x =
      colPassG (fun off n par hN b ok => DWT53.lift1d off n par hN b ok) pw hN W v0 v1 hW hH hT
        P tmp ok x := by
  rw [DWT53.colPass, colPassG]
  split
  · dsimp only; rw [liftCols53_eq, colPass53_eq]
  · rfl
termination_by W - x
decreasing_by all_goals (simp only [batch]; omega)

/-- `DWT97.colPass` is `colPassG` with `lift1d97`. -/
theorem colPass97_eq (W v0 v1 : Nat) (hW : W ≤ pw) (hH : v1 - v0 ≤ N / pw)
    (hT : batch * (v1 - v0) ≤ T) (P : Buf N) (tmp : Buf T) (ok : Bool) (x : Nat) :
    DWT97.colPass pw hN W v0 v1 hW hH hT P tmp ok x =
      colPassG (fun off n par hN b ok => DWT97.lift1d97 off n par hN b ok) pw hN W v0 v1 hW hH hT
        P tmp ok x := by
  rw [DWT97.colPass, colPassG]
  split
  · dsimp only; rw [liftCols97_eq, colPass97_eq]
  · rfl
termination_by W - x
decreasing_by all_goals (simp only [batch]; omega)

/-- `DWT53.levels` is `levelsG` with `lift1d`. -/
theorem levels53_eq (tc : Header.Rect) (hpw : tc.x1 - tc.x0 ≤ pw) (hph : tc.y1 - tc.y0 ≤ N / pw)
    (hT : batch * (tc.y1 - tc.y0) ≤ T) (hT2 : tc.x1 - tc.x0 ≤ T) (k : Nat) (P : Buf N)
    (tmp : Buf T) (ok : Bool) :
    DWT53.levels tc pw hN hpw hph hT hT2 k P tmp ok =
      levelsG (fun off n par hN b ok => DWT53.lift1d off n par hN b ok) tc pw hN hpw hph hT hT2
        k P tmp ok := by
  induction k generalizing P tmp ok with
  | zero => rfl
  | succ k ih => simp only [DWT53.levels, levelsG, rowPass53_eq, colPass53_eq, ih]

/-- `DWT97.levels` is `levelsG` with `lift1d97`. -/
theorem levels97_eq (tc : Header.Rect) (hpw : tc.x1 - tc.x0 ≤ pw) (hph : tc.y1 - tc.y0 ≤ N / pw)
    (hT : batch * (tc.y1 - tc.y0) ≤ T) (hT2 : tc.x1 - tc.x0 ≤ T) (k : Nat) (P : Buf N)
    (tmp : Buf T) (ok : Bool) :
    DWT97.levels tc pw hN hpw hph hT hT2 k P tmp ok =
      levelsG (fun off n par hN b ok => DWT97.lift1d97 off n par hN b ok) tc pw hN hpw hph hT hT2
        k P tmp ok := by
  induction k generalizing P tmp ok with
  | zero => rfl
  | succ k ih => simp only [DWT97.levels, levelsG, rowPass97_eq, colPass97_eq, ih]

end Instances

/-! ## The row pass -/

/-- A row-major index `yy·pw + xx` (`xx < pw`) lies in `[y·pw, y·pw + W)` iff it is in row `y`
at a column `< W`. -/
theorem row_hit {pw W y yy xx : Nat} (hxx : xx < pw) (hW : W ≤ pw) :
    (y * pw ≤ yy * pw + xx ∧ yy * pw + xx < y * pw + W) ↔ (yy = y ∧ xx < W) := by
  constructor
  · intro ⟨h1, h2⟩
    rcases Nat.lt_trichotomy yy y with hl | he | hg
    · have : (yy + 1) * pw ≤ y * pw := Nat.mul_le_mul_right _ hl
      rw [Nat.succ_mul] at this; omega
    · subst he; exact ⟨rfl, by omega⟩
    · have : (y + 1) * pw ≤ yy * pw := Nat.mul_le_mul_right _ hg
      rw [Nat.succ_mul] at this; omega
  · intro ⟨h1, h2⟩; subst h1; omega

/-- Row `yy` of the level `[u0, u1)` in the Mallat layout, read as an interleaved signal
(absolute column `u` ↦ Mallat cell `srcIdx (u − u0)` of row `yy`). -/
def rowSig {N : Nat} (pw u0 u1 : Nat) (P : Buf N) (yy : Nat) : Int → Int := fun u =>
  rd P (yy * pw + srcIdx u0 ((u1 + 1) / 2 - (u0 + 1) / 2) (u - u0).toNat)

/-- **The row pass** (`HOR_SR`): when the flag stays set, every row `yy ∈ [y, H)` of the
level holds `op` of its interleaved signal at columns `[0, W)`; every other cell is
unchanged; `okP` holds of every row signal. -/
theorem rowPassG_spec {K : Kern} {op : Int → Int → (Int → Int) → Int → Int}
    {okP : Int → Int → (Int → Int) → Prop} (hK : KSpec K op okP) {N T : Nat} (pw : Nat)
    (hN : N = pw * (N / pw)) (u0 u1 H : Nat) (hW : u1 - u0 ≤ pw) (hH : H ≤ N / pw)
    (hT : u1 - u0 ≤ T) (P : Buf N) (tmp : Buf T) (ok : Bool) (y : Nat)
    (hok : (rowPassG K pw hN u0 u1 H hW hH hT P tmp ok y).2.2 = true) :
    ok = true ∧
    (∀ yy, y ≤ yy → yy < H → okP u0 (u0 + ((u1 - u0 : Nat) : Int)) (rowSig pw u0 u1 P yy)) ∧
    ∀ yy xx, xx < pw → rd (rowPassG K pw hN u0 u1 H hW hH hT P tmp ok y).1 (yy * pw + xx) =
      if y ≤ yy ∧ yy < H ∧ xx < u1 - u0 then
        op u0 (u0 + ((u1 - u0 : Nat) : Int)) (rowSig pw u0 u1 P yy) (u0 + xx)
      else rd P (yy * pw + xx) := by
  rw [rowPassG] at hok ⊢
  split
  · rename_i hy
    simp only [hy, ↓reduceDIte] at hok
    have hl := loadRow_spec pw hN u0 u1 y hW (by omega) P hT tmp 0
    rcases hres : K 0 (u1 - u0) (u0 % 2) (by omega) (loadRow pw hN u0 u1 y hW (by omega) P hT tmp 0) ok
      with ⟨t2, ok2⟩
    dsimp only at hok ⊢
    rw [hres] at hok ⊢
    dsimp only at hok ⊢
    obtain ⟨ih1, ih2, ih3⟩ := rowPassG_spec hK pw hN u0 u1 H hW hH hT _ t2 ok2 (y + 1) hok
    have hok2 : (K 0 (u1 - u0) (u0 % 2) (by omega)
        (loadRow pw hN u0 u1 y hW (by omega) P hT tmp 0) ok).2 = true := by rw [hres]; exact ih1
    have hok0 := hK.mono _ _ _ _ _ _ hok2
    obtain ⟨hv, hp⟩ := hK.val 0 (u1 - u0) (u0 % 2) (by omega)
      (loadRow pw hN u0 u1 y hW (by omega) P hT tmp 0) ok (u0 : Int) (by omega)
      (rowSig pw u0 u1 P y) (by
        intro k hk
        rw [Nat.zero_add, hl k hk]
        simp only [Nat.not_lt_zero, ↓reduceIte, rowSig, show ((u0 : Int) + k - u0).toNat = k by omega])
      hok2
    rw [hres] at hv
    have hst := storeRow_spec pw hN (u1 - u0) y hW (by omega) t2 hT P 0
    -- rows other than `y` keep their signals on the range
    have hsig : ∀ yy, yy ≠ y → ∀ k, (u0 : Int) ≤ k → k < u0 + ((u1 - u0 : Nat) : Int) →
        rowSig pw u0 u1 (storeRow pw hN (u1 - u0) y hW (by omega) t2 hT P 0) yy k =
          rowSig pw u0 u1 P yy k := by
      intro yy hne k hk0 hk1
      simp only [rowSig]
      rw [hst]
      have hs := DWT53.srcIdx_lt (a0 := u0) (a1 := u1) (i := (k - u0).toNat) (by omega)
      rw [if_f (by rw [Nat.add_zero, row_hit (by omega) hW]; omega)]
    refine ⟨hok0, ?_, ?_⟩
    · intro yy h1 h2
      by_cases he : yy = y
      · subst he; exact hp
      · exact (hK.loc _ _ _ _ (hsig yy he)).2 (ih2 yy (by omega) h2)
    · intro yy xx hxx
      rw [ih3 yy xx hxx]
      by_cases he : yy = y
      · subst he
        simp only [show ¬ (yy + 1 ≤ yy) by omega, false_and, ↓reduceIte, Nat.le_refl, hy,
          true_and]
        rw [hst, Nat.add_zero]
        by_cases hx : xx < u1 - u0
        · rw [if_t ((row_hit hxx hW).mpr ⟨rfl, hx⟩), if_t hx, Nat.add_sub_cancel_left]
          have := hv xx hx
          rw [Nat.zero_add] at this
          exact this
        · rw [if_f (fun h => hx ((row_hit hxx hW).mp h).2), if_f hx]
      · by_cases hc : y + 1 ≤ yy ∧ yy < H ∧ xx < u1 - u0
        · rw [if_t hc, if_t (by omega)]
          exact (hK.loc _ _ _ _ (hsig yy he)).1 _ (by omega) (by omega)
        · rw [if_f hc, if_f (by omega), hst, Nat.add_zero,
            if_f (fun h => he ((row_hit hxx hW).mp h).1)]
  · rename_i hy
    simp only [hy, ↓reduceDIte] at hok
    refine ⟨hok, fun yy h1 h2 => absurd h2 (by omega), fun yy xx _ => ?_⟩
    simp only [show ¬ (y ≤ yy ∧ yy < H ∧ xx < u1 - u0) by omega, ↓reduceIte]
termination_by H - y

/-! ## The column pass -/

/-- **Lifting a batch of columns**: column `cc` of `tmp` (cells `[cc·H, cc·H + H)`), holding
the signal `sig cc` from absolute index `i0`, gets `op` of it. -/
theorem liftColsG_spec {K : Kern} {op : Int → Int → (Int → Int) → Int → Int}
    {okP : Int → Int → (Int → Int) → Prop} (hK : KSpec K op okP) {T : Nat} (H par bw : Nat)
    (hT : bw * H ≤ T) (tmp : Buf T) (ok : Bool) (c : Nat) (i0 : Int)
    (hpar : i0 % 2 = ((par % 2 : Nat) : Int)) (sig : Nat → Int → Int)
    (hsig : ∀ cc ii, c ≤ cc → cc < bw → ii < H → rd tmp (cc * H + ii) = sig cc (i0 + ii))
    (hok : (liftColsG K H par bw hT tmp ok c).2 = true) :
    ok = true ∧ (∀ cc, c ≤ cc → cc < bw → okP i0 (i0 + H) (sig cc)) ∧
    ∀ cc ii, cc < bw → ii < H → rd (liftColsG K H par bw hT tmp ok c).1 (cc * H + ii) =
      if c ≤ cc then op i0 (i0 + H) (sig cc) (i0 + ii) else rd tmp (cc * H + ii) := by
  rw [liftColsG] at hok ⊢
  split
  · rename_i hc
    simp only [hc, ↓reduceDIte] at hok
    have hcH : c * H + H ≤ bw * H := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hc
    rcases hres : K (c * H) H par (by omega) tmp ok with ⟨t2, ok2⟩
    dsimp only at hok ⊢
    rw [hres] at hok ⊢
    dsimp only at hok ⊢
    have hok2 : (K (c * H) H par (by omega) tmp ok).2 = true := by
      rw [hres]; exact (liftColsG_spec hK H par bw hT t2 ok2 (c + 1) i0 hpar sig (by
        intro cc ii h1 h2 h3
        have := hK.frame (c * H) H par (by omega) tmp ok (cc * H + ii)
          (Classical.byContradiction fun hcon => absurd
            ((row_hit (pw := H) (W := H) (y := c) (yy := cc) h3 (Nat.le_refl _)).mp (by omega)).1
            (by omega))
        rw [hres] at this
        rw [this]; exact hsig cc ii (by omega) h2 h3) hok).1
    obtain ⟨hv, hp⟩ := hK.val (c * H) H par (by omega) tmp ok i0 hpar (sig c)
      (fun k hk => hsig c k (Nat.le_refl _) hc hk) hok2
    rw [hres] at hv
    have hfr : ∀ cc ii, cc ≠ c → ii < H → rd t2 (cc * H + ii) = rd tmp (cc * H + ii) := by
      intro cc ii hne hii
      have := hK.frame (c * H) H par (by omega) tmp ok (cc * H + ii)
        (Classical.byContradiction fun hcon => absurd
          ((row_hit (pw := H) (W := H) (y := c) (yy := cc) hii (Nat.le_refl _)).mp (by omega)).1
          hne)
      rw [hres] at this; exact this
    obtain ⟨ih1, ih2, ih3⟩ := liftColsG_spec hK H par bw hT t2 ok2 (c + 1) i0 hpar sig (by
      intro cc ii h1 h2 h3
      rw [hfr cc ii (by omega) h3]; exact hsig cc ii (by omega) h2 h3) hok
    refine ⟨hK.mono _ _ _ _ _ _ hok2, ?_, ?_⟩
    · intro cc h1 h2
      by_cases he : cc = c
      · subst he; exact hp
      · exact ih2 cc (by omega) h2
    · intro cc ii h1 h2
      rw [ih3 cc ii h1 h2]
      by_cases he : cc = c
      · subst he
        rw [if_f (by omega), if_t (Nat.le_refl _)]
        exact hv ii h2
      · by_cases hlt : c + 1 ≤ cc
        · rw [if_t hlt, if_t (by omega)]
        · rw [if_f hlt, if_f (by omega), hfr cc ii he h2]
  · rename_i hc
    simp only [hc, ↓reduceDIte] at hok
    refine ⟨hok, fun cc h1 h2 => absurd h2 (by omega), fun cc ii h1 h2 => ?_⟩
    rw [if_f (by omega)]
termination_by bw - c

/-- Column `xx` of the level `[v0, v1)` in the Mallat layout, read as an interleaved signal
(absolute row `v` ↦ Mallat cell `(xx, srcIdx (v − v0))`). -/
def colSig {N : Nat} (pw v0 v1 : Nat) (P : Buf N) (xx : Nat) : Int → Int := fun v =>
  rd P (srcIdx v0 ((v1 + 1) / 2 - (v0 + 1) / 2) (v - v0).toNat * pw + xx)

/-- **The column pass** (`VER_SR`): when the flag stays set, every column `xx ∈ [x, W)` of the
level holds `op` of its interleaved signal at rows `[0, H)`; every other cell is unchanged;
`okP` holds of every column signal. -/
theorem colPassG_spec {K : Kern} {op : Int → Int → (Int → Int) → Int → Int}
    {okP : Int → Int → (Int → Int) → Prop} (hK : KSpec K op okP) {N T : Nat} (pw : Nat)
    (hN : N = pw * (N / pw)) (W v0 v1 : Nat) (hW : W ≤ pw) (hH : v1 - v0 ≤ N / pw)
    (hT : batch * (v1 - v0) ≤ T) (P : Buf N) (tmp : Buf T) (ok : Bool) (x : Nat)
    (hok : (colPassG K pw hN W v0 v1 hW hH hT P tmp ok x).2.2 = true) :
    ok = true ∧
    (∀ xx, x ≤ xx → xx < W → okP v0 (v0 + ((v1 - v0 : Nat) : Int)) (colSig pw v0 v1 P xx)) ∧
    ∀ yy xx, xx < pw → rd (colPassG K pw hN W v0 v1 hW hH hT P tmp ok x).1 (yy * pw + xx) =
      if x ≤ xx ∧ xx < W ∧ yy < v1 - v0 then
        op v0 (v0 + ((v1 - v0 : Nat) : Int)) (colSig pw v0 v1 P xx) (v0 + yy)
      else rd P (yy * pw + xx) := by
  rw [colPassG] at hok ⊢
  split
  · rename_i hx
    simp only [hx, ↓reduceDIte] at hok
    have hbw0 : 0 < min batch (W - x) := by simp only [batch]; omega
    have hbw : min batch (W - x) * (v1 - v0) ≤ T :=
      Nat.le_trans (Nat.mul_le_mul_right _ (Nat.min_le_left _ _)) hT
    have hxb : x + min batch (W - x) ≤ pw := by omega
    have hl := loadCols_spec pw hN v0 v1 x (min batch (W - x)) hxb hH hbw P tmp 0 0
    rcases hres : liftColsG K (v1 - v0) (v0 % 2) (min batch (W - x)) hbw
      (loadCols pw hN v0 v1 x (min batch (W - x)) hxb hH hbw P tmp 0 0) ok 0 with ⟨t2, ok2⟩
    dsimp only at hok ⊢
    rw [hres] at hok ⊢
    dsimp only at hok ⊢
    have hst := storeCols_spec pw hN (v1 - v0) x (min batch (W - x)) hxb hH hbw t2 P 0 0
    obtain ⟨ih1, ih2, ih3⟩ := colPassG_spec hK pw hN W v0 v1 hW hH hT _ t2 ok2
      (x + min batch (W - x)) hok
    have hok2 : (liftColsG K (v1 - v0) (v0 % 2) (min batch (W - x)) hbw
        (loadCols pw hN v0 v1 x (min batch (W - x)) hxb hH hbw P tmp 0 0) ok 0).2 = true := by
      rw [hres]; exact ih1
    obtain ⟨hl1, hl2, hl3⟩ := liftColsG_spec hK (v1 - v0) (v0 % 2) (min batch (W - x)) hbw
      (loadCols pw hN v0 v1 x (min batch (W - x)) hxb hH hbw P tmp 0 0) ok 0 (v0 : Int)
      (by omega) (fun cc => colSig pw v0 v1 P (x + cc)) (by
        intro cc ii _ h2 h3
        rw [hl cc ii h2 h3, if_f (by omega)]
        simp only [colSig, show ((v0 : Int) + ii - v0).toNat = ii by omega]) hok2
    rw [hres] at hl3
    -- columns at or after `x + bw` keep their signals on the range
    have hsig : ∀ xx, x + min batch (W - x) ≤ xx → xx < pw → ∀ k, (v0 : Int) ≤ k →
        k < v0 + ((v1 - v0 : Nat) : Int) →
        colSig pw v0 v1 (storeCols pw hN (v1 - v0) x (min batch (W - x)) hxb hH hbw t2 P 0 0) xx k =
          colSig pw v0 v1 P xx k := by
      intro xx h1 h2 k hk0 hk1
      simp only [colSig]
      rw [hst _ xx h2, if_f (by omega)]
    refine ⟨hl1, ?_, ?_⟩
    · intro xx h1 h2
      by_cases hb : xx < x + min batch (W - x)
      · have := hl2 (xx - x) (by omega) (by omega)
        rw [show x + (xx - x) = xx by omega] at this
        exact this
      · exact (hK.loc _ _ _ _ (hsig xx (by omega) (by omega))).2 (ih2 xx (by omega) h2)
    · intro yy xx hxx
      rw [ih3 yy xx hxx]
      by_cases hb : x ≤ xx ∧ xx < x + min batch (W - x)
      · rw [if_f (by omega), hst yy xx hxx]
        by_cases hy : yy < v1 - v0
        · rw [if_t (by omega), if_t (by omega), hl3 (xx - x) yy (by omega) hy, if_t (Nat.zero_le _),
            show x + (xx - x) = xx by omega]
        · rw [if_f (by omega), if_f (by omega)]
      · by_cases hc : x + min batch (W - x) ≤ xx ∧ xx < W ∧ yy < v1 - v0
        · rw [if_t hc, if_t (by omega)]
          exact (hK.loc _ _ _ _ (hsig xx hc.1 hxx)).1 _ (by omega) (by omega)
        · rw [if_f hc, if_f (by omega), hst yy xx hxx, if_f (by omega)]
  · rename_i hx
    simp only [hx, ↓reduceDIte] at hok
    refine ⟨hok, fun xx h1 h2 => absurd h2 (by omega), fun yy xx _ => ?_⟩
    rw [if_f (by omega)]
termination_by W - x
decreasing_by all_goals (simp only [batch]; omega)

/-! ## One level and the level loop -/

open JPEG2000.Spec.DWT53 (Grid Dec interleave)

/-- `HOR_SR` with the 1-D operator `op`. -/
def ghor (op : Int → Int → (Int → Int) → Int → Int) (r : Spec.DWT53.Rect) (g : Grid) : Grid :=
  ⟨fun u v => op r.u0 r.u1 (fun u' => g.get u' v) u⟩

/-- `2D_SR` with the 1-D operator `op`: rows, then columns. -/
def g2d (op : Int → Int → (Int → Int) → Int → Int) (r : Spec.DWT53.Rect) (g : Grid) : Grid :=
  ⟨fun u v => op r.v0 r.v1 (fun v' => (ghor op r g).get u v') v⟩

/-- `okP` holds of every row and every column signal of one level. -/
def gOk2d (op : Int → Int → (Int → Int) → Int → Int) (okP : Int → Int → (Int → Int) → Prop)
    (r : Spec.DWT53.Rect) (g : Grid) : Prop :=
  (∀ v, r.v0 ≤ v → v < r.v1 → okP r.u0 r.u1 (fun u' => g.get u' v)) ∧
  (∀ u, r.u0 ≤ u → u < r.u1 → okP r.v0 r.v1 (fun v' => (ghor op r g).get u v'))

/-- `IDWT` over `n` levels with the 1-D operator `op` (the structure of `Spec.DWT53.srMulti`). -/
def gMulti (op : Int → Int → (Int → Int) → Int → Int) : Spec.DWT53.Rect → Nat → Dec → Grid
  | _, 0, d => d.ll
  | r, n + 1, ⟨ll, (hl, lh, hh) :: rest⟩ => g2d op r (interleave (gMulti op r.half n ⟨ll, rest⟩) hl lh hh)
  | _, _ + 1, ⟨ll, []⟩ => ll

/-- `okP` holds of every 1-D pass of `gMulti`. -/
def gOk (op : Int → Int → (Int → Int) → Int → Int) (okP : Int → Int → (Int → Int) → Prop) :
    Spec.DWT53.Rect → Nat → Dec → Prop
  | _, 0, _ => True
  | r, n + 1, ⟨ll, (hl, lh, hh) :: rest⟩ =>
    gOk op okP r.half n ⟨ll, rest⟩ ∧ gOk2d op okP r (interleave (gMulti op r.half n ⟨ll, rest⟩) hl lh hh)
  | _, _ + 1, ⟨_, []⟩ => True

/-- Peeling the **coarsest** level of `gMulti`. -/
theorem gMulti_snoc (op : Int → Int → (Int → Int) → Int → Int) (k : Nat) :
    ∀ (r : Spec.DWT53.Rect) (G : Grid) (ds : List (Grid × Grid × Grid)) (d : Grid × Grid × Grid),
    ds.length = k →
    gMulti op r (k + 1) ⟨G, ds ++ [d]⟩ =
      gMulti op r k ⟨g2d op (rhalf r k) (interleave G d.1 d.2.1 d.2.2), ds⟩ := by
  induction k with
  | zero =>
    intro r G ds d hl
    cases ds with
    | nil => rfl
    | cons _ _ => simp at hl
  | succ k ih =>
    intro r G ds d hl
    cases ds with
    | nil => simp at hl
    | cons e ds =>
      obtain ⟨a, b, c⟩ := e
      simp only [List.cons_append, gMulti]
      rw [ih r.half G ds d (by simpa using hl)]
      rfl

/-- Peeling the coarsest level of `gOk`. -/
theorem gOk_snoc (op : Int → Int → (Int → Int) → Int → Int) (okP : Int → Int → (Int → Int) → Prop)
    (k : Nat) : ∀ (r : Spec.DWT53.Rect) (G : Grid) (ds : List (Grid × Grid × Grid))
    (d : Grid × Grid × Grid), ds.length = k →
    (gOk op okP r k ⟨g2d op (rhalf r k) (interleave G d.1 d.2.1 d.2.2), ds⟩ ∧
      gOk2d op okP (rhalf r k) (interleave G d.1 d.2.1 d.2.2)) →
    gOk op okP r (k + 1) ⟨G, ds ++ [d]⟩ := by
  induction k with
  | zero =>
    intro r G ds d hl h
    cases ds with
    | nil => exact ⟨trivial, h.2⟩
    | cons _ _ => simp at hl
  | succ k ih =>
    intro r G ds d hl h
    cases ds with
    | nil => simp at hl
    | cons e ds =>
      obtain ⟨a, b, c⟩ := e
      simp only [List.cons_append, gOk]
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      refine ⟨ih r.half G ds d (by simpa using hl) ⟨h1, h3⟩, ?_⟩
      rw [gMulti_snoc op k r.half G ds d (by simpa using hl)]
      exact h2

end JPEG2000.Spec.DWTPlane
