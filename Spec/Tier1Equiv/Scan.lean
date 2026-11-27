import Spec.Tier1Equiv.Pass

/-!
# C3 (plain mode), part 3d: scan order, whole passes, pass sequences

Plan.md §4 (C3), §5.2 "Tier-1 / EBCOT"; T.800 D.1 (scan order), D.2 (pass sequence), D.3.
Task 3.6.

* `scanBlock_rel` — the fast loops `scanStripes`/`scanCols` visit exactly the stripe columns of
  `Spec.Tier1.stripeColumns`, in order.
* `clearVis_rel` — clearing the `VIS` bits is `Spec.Tier1.clearVisited`.
* `sigPropPass_rel`, `magRefPass_rel`, `cleanupPass_rel`, `runPass_rel`, `runPasses_rel`.
-/

namespace JPEG2000.Spec.Tier1Equiv

open JPEG2000
open JPEG2000.Tier2.Geometry (Band)
open JPEG2000.Spec.Tier1 (Coeff Geom DecState)

section scan
variable {w h : Nat} {b : Band} {start : Nat}
variable (colF : Tier1.St → Nat → Nat → Tier1.St) (colS : DecState → List (Nat × Nat) → DecState)
variable (hcol : ∀ s d x y0, Rel w h b start s d → x < w → y0 < h →
  Rel w h b start (colF s (bidx w x y0) (min 4 (h - y0))) (colS d (Spec.Tier1.stripeColumn h x y0)))
include hcol

/-- The columns of one stripe. -/
theorem scanCols_rel (y0 : Nat) (hy : y0 < h) :
    ∀ k s d x0, Rel w h b start s d → x0 + k ≤ w →
      Rel w h b start (Tier1.scanCols colF (min 4 (h - y0)) k s (bidx w x0 y0))
        (((List.range k).map fun x => Spec.Tier1.stripeColumn h (x0 + x) y0).foldl colS d) := by
  intro k
  induction k with
  | zero => intro s d x0 R _; exact R
  | succ k ih =>
    intro s d x0 R hk
    simp only [Tier1.scanCols]
    rw [List.range_succ_eq_map, List.map_cons, List.foldl_cons, List.map_map, bidx_right]
    have e : ((fun x => Spec.Tier1.stripeColumn h (x0 + x) y0) ∘ Nat.succ) =
        fun x => Spec.Tier1.stripeColumn h ((x0 + 1) + x) y0 := by
      funext r; simp only [Function.comp, Nat.succ_eq_add_one]; congr 1; omega
    rw [e]
    simp only [Nat.add_zero]
    exact ih _ _ (x0 + 1) (hcol s d x0 y0 R (by omega) hy) (by omega)

/-- The stripes `j, j + 1, …, j + k − 1`. -/
theorem scanStripes_rel :
    ∀ k s d j, Rel w h b start s d → j + k ≤ (h + 3) / 4 →
      Rel w h b start (Tier1.scanStripes colF (fgeo w h b) k s (4 * j))
        (((List.range' j k).flatMap fun t =>
          (List.range w).map fun x => Spec.Tier1.stripeColumn h x (4 * t)).foldl colS d) := by
  intro k
  induction k with
  | zero => intro s d j R _; exact R
  | succ k ih =>
    intro s d j R hk
    simp only [Tier1.scanStripes]
    rw [List.range'_succ, List.flatMap_cons, List.foldl_append]
    have hy : 4 * j < h := by omega
    have hs := scanCols_rel colF colS hcol (4 * j) hy w s d 0 R (by omega)
    simp only [Nat.zero_add] at hs
    have e1 : (4 * j + 1) * (fgeo w h b).st + 1 = bidx w 0 (4 * j) := bidx_zero w (4 * j)
    simp only [fgeo] at e1 ⊢
    rw [e1, show 4 * j + 4 = 4 * (j + 1) by omega]
    exact ih _ _ (j + 1) hs (by omega)

/-- **D.1 scan**: `scanBlock` simulates the fold over `stripeColumns`. -/
theorem scanBlock_rel (s : Tier1.St) (d : DecState) (R : Rel w h b start s d) :
    Rel w h b start (Tier1.scanBlock colF (fgeo w h b) s)
      ((Spec.Tier1.stripeColumns w h).foldl colS d) := by
  have := scanStripes_rel colF colS hcol ((h + 3) / 4) s d 0 R (by omega)
  simp only [Nat.mul_zero] at this
  simp only [Tier1.scanBlock, Spec.Tier1.stripeColumns]
  rw [List.range_eq_range' (n := (h + 3) / 4)]
  exact this

end scan

/-! ## Clearing the visited marks -/

/-- `clearVisFrom` keeps the size. -/
theorem clearVisFrom_size (fl : Array UInt32) (n i : Nat) :
    (Tier1.clearVisFrom fl n i).size = fl.size := by
  induction n generalizing fl i with
  | zero => rfl
  | succ n ih => simp only [Tier1.clearVisFrom]; rw [ih, fset_size]

/-- Reading after `fset`, any index. -/
theorem fget_fset' (a : Array UInt32) (i k : Nat) (v : UInt32) :
    Tier1.fget (Tier1.fset a i v) k = if i = k ∧ i < a.size then v else Tier1.fget a k := by
  by_cases hi : i < a.size
  · rw [fget_fset _ _ _ _ hi]; simp [hi]
  · have : Tier1.fset a i v = a := by unfold Tier1.fset; simp [hi]
    rw [this]; simp [hi]

/-- `clearVisFrom` clears bit 14 of words `i, …, i + n − 1`. -/
theorem clearVisFrom_get (fl : Array UInt32) (n i k : Nat) (hk : k < fl.size) :
    Tier1.fget (Tier1.clearVisFrom fl n i) k =
      if i ≤ k ∧ k < i + n then Tier1.fget fl k &&& ~~~Tier1.VIS else Tier1.fget fl k := by
  induction n generalizing fl i with
  | zero =>
    simp only [Tier1.clearVisFrom]
    have : ¬ (i ≤ k ∧ k < i + 0) := by omega
    rw [ite_neg' this]
  | succ n ih =>
    simp only [Tier1.clearVisFrom]
    rw [ih _ _ (by rw [fset_size]; exact hk), fget_fset']
    by_cases hik : i = k
    · subst hik
      have : ¬ (i + 1 ≤ i ∧ i < i + 1 + n) := by omega
      simp [this, hk]
    · simp only [hik, false_and, ↓reduceIte]
      have e : (i + 1 ≤ k ∧ k < i + 1 + n) ↔ (i ≤ k ∧ k < i + (n + 1)) := by omega
      simp only [e]

/-- Reading a mapped spec coefficient array (in or out of the block). -/
theorem coeffAt_map (g : Geom) (cs : Array Coeff) (f : Coeff → Coeff) (hf : f {} = {}) (X Y : Int) :
    g.coeffAt (cs.map f) X Y = f (g.coeffAt cs X Y) := by
  unfold Geom.coeffAt
  split
  · rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_map]
    cases cs[g.idx X.toNat Y.toNat]? <;> simp [hf]
  · exact hf.symm

/-- **Clearing the visited marks** (end of a cleanup pass): `clearVis` simulates
`clearVisited`. -/
theorem clearVis_rel {w h : Nat} {b : Band} {start : Nat} {s : Tier1.St} {d : DecState}
    (R : Rel w h b start s d) :
    Rel w h b start (Tier1.clearVis s) { d with coeffs := Spec.Tier1.clearVisited d.coeffs } := by
  obtain ⟨mq, fl, mags⟩ := s
  have hm : ∀ X Y, (sgeom w h b).coeffAt (Spec.Tier1.clearVisited d.coeffs) X Y =
      { (sgeom w h b).coeffAt d.coeffs X Y with visited := false } :=
    fun X Y => coeffAt_map _ _ _ rfl X Y
  refine ⟨R.mq, by simp [Tier1.clearVis, clearVisFrom_size, R.fsize], R.msize,
    by simp [Spec.Tier1.clearVisited, R.csize], ?_, ?_⟩
  · intro x y j hx hy hj
    have hk : bidx w x y < fl.size := by rw [R.fsize]; exact bidx_lt hx hy
    simp only [Tier1.clearVis]
    rw [clearVisFrom_get _ _ _ _ hk, ite_pos' ⟨Nat.zero_le _, by omega⟩, bt_and, bt_notVIS j hj,
      R.flag x y j hx hy hj]
    simp only [specBit, hm]
    by_cases hj12 : j < 12
    · have : ¬ (14 = j) := by omega
      simp [hj12, this]
    · rcases (by omega : j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15) with rfl | rfl | rfl | rfl <;> simp
  · intro x y hx hy
    simp only [Tier1.clearVis]
    rw [R.mag x y hx hy, hm]

/-! ## Whole passes -/

section passes
variable {w h : Nat} {b : Band} {start : Nat}

/-- **Significance propagation pass** (D.3.1). -/
theorem sigPropPass_rel (one : UInt32) (p : Nat) (hone : HOne one p) (s : Tier1.St)
    (d : DecState) (R : Rel w h b start s d) :
    Rel w h b start (JPEG2000.Tier1.sigPropPass (fgeo w h b) one s)
      (Spec.Tier1.sigPropPass (sgeom w h b) p d) := by
  unfold JPEG2000.Tier1.sigPropPass Spec.Tier1.sigPropPass Spec.Tier1.scanOrder
  rw [List.foldl_flatten]
  exact scanBlock_rel _ (fun d col => col.foldl (Spec.Tier1.sigPropStep (sgeom w h b) p) d)
    (fun s d x y0 R hx hy => spCol_rel one p hone s d R x y0 hx hy) s d R

/-- **Magnitude refinement pass** (D.3.3). -/
theorem magRefPass_rel (one : UInt32) (p : Nat) (hone : HOne one p) (s : Tier1.St)
    (d : DecState) (R : Rel w h b start s d) :
    Rel w h b start (JPEG2000.Tier1.magRefPass (fgeo w h b) one s)
      (Spec.Tier1.magRefPass (sgeom w h b) p d) := by
  unfold JPEG2000.Tier1.magRefPass Spec.Tier1.magRefPass Spec.Tier1.scanOrder
  rw [List.foldl_flatten]
  exact scanBlock_rel _ (fun d col => col.foldl (Spec.Tier1.magRefStep (sgeom w h b) p) d)
    (fun s d x y0 R hx hy => mrCol_rel one p hone s d R x y0 hx hy) s d R

/-- **Cleanup pass** (D.3.4), including the final clearing of the visited marks. -/
theorem cleanupPass_rel (one : UInt32) (p : Nat) (hone : HOne one p) (s : Tier1.St)
    (d : DecState) (R : Rel w h b start s d) :
    Rel w h b start (JPEG2000.Tier1.cleanupPass (fgeo w h b) one s)
      (Spec.Tier1.cleanupPass (sgeom w h b) p d) := by
  unfold JPEG2000.Tier1.cleanupPass Spec.Tier1.cleanupPass
  exact clearVis_rel (scanBlock_rel _ (Spec.Tier1.cleanupColumn (sgeom w h b) p)
    (fun s d x y0 R hx hy => cuCol_rel one p hone s d R x y0 hx hy) s d R)

/-- The fast bit-plane weight `1 <<< p` is `2^p` for `p < 32`. -/
theorem hone_of (p : Nat) (hp : p < 32) : HOne ((1 : UInt32) <<< p.toUInt32) p := by
  unfold HOne
  rw [UInt32.toNat_shiftLeft]
  have e : p.toUInt32.toNat = p := by
    simp only [Nat.toUInt32, UInt32.toNat_ofNat']; omega
  rw [e, Nat.mod_eq_of_lt hp, Nat.shiftLeft_eq]
  simp

/-- The pass types agree. -/
theorem passKind_cases (i : Nat) :
    (JPEG2000.Tier1.passKind i = 0 ∧ Spec.Tier1.passKind i = .sigProp) ∨
    (JPEG2000.Tier1.passKind i = 1 ∧ Spec.Tier1.passKind i = .magRef) ∨
    (JPEG2000.Tier1.passKind i = 2 ∧ Spec.Tier1.passKind i = .cleanup) := by
  unfold JPEG2000.Tier1.passKind Spec.Tier1.passKind
  by_cases i0 : i = 0
  · simp [i0]
  · rcases (by omega : (i - 1) % 3 = 0 ∨ (i - 1) % 3 = 1 ∨ (i - 1) % 3 = 2) with e | e | e <;>
      simp [i0, e]

/-- **One pass** (D.2) of a block with `K ≤ 32` coded planes. -/
theorem runPass_rel (K : Nat) (hK : K ≤ 32) (s : Tier1.St) (d : DecState)
    (R : Rel w h b start s d) (i : Nat) :
    Rel w h b start (JPEG2000.Tier1.runPass (fgeo w h b) K s i)
      (Spec.Tier1.runPass (sgeom w h b) K d i) := by
  have hp : Spec.Tier1.passPlane K i < 32 := by unfold Spec.Tier1.passPlane; omega
  have hone := hone_of _ hp
  unfold JPEG2000.Tier1.runPass Spec.Tier1.runPass
  rcases passKind_cases i with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> simp only [e1, e2]
  · exact sigPropPass_rel _ _ hone s d R
  · exact magRefPass_rel _ _ hone s d R
  · exact cleanupPass_rel _ _ hone s d R

/-- **A sequence of passes** `i, …, i + n − 1`. -/
theorem runPasses_rel (K : Nat) (hK : K ≤ 32) :
    ∀ n s d i, Rel w h b start s d →
      Rel w h b start (JPEG2000.Tier1.runPasses (fgeo w h b) K n s i)
        ((List.range' i n).foldl (Spec.Tier1.runPass (sgeom w h b) K) d) := by
  intro n
  induction n with
  | zero => intro s d i R; exact R
  | succ n ih =>
    intro s d i R
    simp only [JPEG2000.Tier1.runPasses, List.range'_succ, List.foldl_cons]
    exact ih _ _ _ (runPass_rel K hK s d R i)

end passes

end JPEG2000.Spec.Tier1Equiv
