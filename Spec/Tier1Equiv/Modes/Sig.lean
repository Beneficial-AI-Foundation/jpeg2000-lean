import Spec.Tier1Equiv.Modes.Rel

/-!
# C3 (all code-block styles), part 2: publishing a new significance, vertically causal

Plan.md §4 (C3), §5.2 "Tier-1 / EBCOT"; T.800 D.3.2 (a coefficient becomes significant), D.7
(vertically causal context formation). Task 7.1c.

`JPEG2000.Tier1.setSig` writes the own word of a coefficient that becomes significant and ORs
one mask into each neighbour word — except, with vertically causal formation and a
coefficient in the first row of a stripe below the first (`causalTop`), into the three words
of the row above. `flags_afterM` computes every in-block word afterwards (`nbMaskV`: the plain
`nbMask`, or `0` for the skipped row), and `setSig_rel` shows that the result is related by
`RelM` to the spec state where the coefficient is significant — the skipped bits are exactly
the ones `Geom.hidden` hides (`hidden_iff`). The sign `neg` and the new coder state are
arguments, so the lemma serves both the MQ path (`becomeSigM`) and the raw path
(`rawSpStep`).
-/

namespace JPEG2000.Spec.Tier1EquivM

open JPEG2000
open JPEG2000.Tier2.Geometry (Band)
open JPEG2000.Spec.Tier1 (Coeff Geom DecState RawState)
open JPEG2000.Spec.Tier1Equiv

/-! ## The masks -/

/-- The mask `setSig` ORs into the word at offset `(dx, dy)`: `nbMask`, except `0` for the row
above (`dy = −1`) when that row is skipped. -/
def nbMaskV (skip neg : Bool) (dx dy : Int) : UInt32 :=
  if skip = true ∧ dy = -1 then 0 else nbMask neg dx dy

/-- Bits 0–11 of `nbMaskV`. -/
theorem bt_nbMaskV (skip neg : Bool) (dx dy : Int) (j : Nat) (hj : j < 12) :
    bt (nbMaskV skip neg dx dy) j =
      (!(skip && decide (dy = -1)) && decide (nbOff j = (dx, dy)) && (decide (j < 8) || neg)) := by
  unfold nbMaskV
  by_cases hc : skip = true ∧ dy = -1
  · rw [ite_pos' hc]; obtain ⟨rfl, rfl⟩ := hc; simp
  · rw [ite_neg' hc, bt_nbMask _ _ _ _ hj]
    have : (skip && decide (dy = -1)) = false := by
      cases skip <;> simp_all
    rw [this]; simp

/-- Bits 12–15 of `nbMaskV` are clear. -/
theorem bt_nbMaskV_hi (skip neg : Bool) (dx dy : Int) (j : Nat) (hj : 12 ≤ j) :
    bt (nbMaskV skip neg dx dy) j = false := by
  unfold nbMaskV; split
  · simp
  · exact bt_nbMask_hi _ _ _ _ hj

/-- **The flag words after `setSig`** (with `skip` = "vertically causal and stripe top"). -/
theorem flags_afterM (fl0 : Array UInt32) {w h x y : Nat} (hsz : fl0.size = (w + 2) * (h + 2))
    (hx : x < w) (hy : y < h) (own : UInt32) (neg skip : Bool) {x' y' : Nat} (hx' : x' < w)
    (hy' : y' < h) :
    let i := bidx w x y
    let st := w + 2
    let fl := JPEG2000.Tier1.fset fl0 i own
    let fl := if skip = true then fl else
      JPEG2000.Tier1.fadd (JPEG2000.Tier1.fadd (JPEG2000.Tier1.fadd fl (i - st - 1)
        JPEG2000.Tier1.SIG_SE) (i - st)
        (if neg = true then JPEG2000.Tier1.SIG_S ||| JPEG2000.Tier1.NEG_S else JPEG2000.Tier1.SIG_S))
        (i - st + 1) JPEG2000.Tier1.SIG_SW
    let fl := JPEG2000.Tier1.fadd fl (i - 1)
      (if neg = true then JPEG2000.Tier1.SIG_E ||| JPEG2000.Tier1.NEG_E else JPEG2000.Tier1.SIG_E)
    let fl := JPEG2000.Tier1.fadd fl (i + 1)
      (if neg = true then JPEG2000.Tier1.SIG_W ||| JPEG2000.Tier1.NEG_W else JPEG2000.Tier1.SIG_W)
    let fl := JPEG2000.Tier1.fadd fl (i + st - 1) JPEG2000.Tier1.SIG_NE
    let fl := JPEG2000.Tier1.fadd fl (i + st)
      (if neg = true then JPEG2000.Tier1.SIG_N ||| JPEG2000.Tier1.NEG_N else JPEG2000.Tier1.SIG_N)
    let fl := JPEG2000.Tier1.fadd fl (i + st + 1) JPEG2000.Tier1.SIG_NW
    JPEG2000.Tier1.fget fl (bidx w x' y') =
      if x' = x ∧ y' = y then own
      else JPEG2000.Tier1.fget fl0 (bidx w x' y') |||
        nbMaskV skip neg ((x' : Int) - x) ((y' : Int) - y) := by
  cases skip
  · have FA := flags_after fl0 hsz hx hy own neg hx' hy'
    simp only at FA
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [FA]
    split
    · rfl
    · simp [nbMaskV]
  · obtain ⟨-, -, -, f4, f5, f6, f7, f8, f9⟩ := bidx_forms w x y
    have k9 : bidx w x' y' = (y' + 1) * (w + 2) + (x' + 1) := (bidx_forms w x' y').2.2.2.2.2.2.2.2
    simp only [↓reduceIte]
    rw [f6, f8, f7, f4, f5, f9, k9]
    have L : ∀ a c, a ≤ 2 → c ≤ 2 → (y + c) * (w + 2) + (x + a) < fl0.size := by
      intro a c ha hc; rw [hsz]; exact nb_lt_size hx hy a c ha hc
    rw [fget_fadd _ _ _ _ (by simp only [fadd_size, fset_size]; exact L 2 2 (by decide) (by decide)),
      fget_fadd _ _ _ _ (by simp only [fadd_size, fset_size]; exact L 1 2 (by decide) (by decide)),
      fget_fadd _ _ _ _ (by simp only [fadd_size, fset_size]; exact L 0 2 (by decide) (by decide)),
      fget_fadd _ _ _ _ (by simp only [fadd_size, fset_size]; exact L 2 1 (by decide) (by decide)),
      fget_fadd _ _ _ _ (by simp only [fadd_size, fset_size]; exact L 0 1 (by decide) (by decide)),
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
    simp [nbMaskV, nbMask, h, h']

/-! ## Vertically causal: the skipped bits are the hidden ones -/

/-- The fast stripe-top test on a bordered index. -/
theorem causalTop_bidx (w h : Nat) (b : Band) (x y : Nat) (hx : x < w) :
    JPEG2000.Tier1.causalTop (fgeo w h b) (bidx w x y) = (decide (0 < y) && y % 4 == 0) := by
  unfold JPEG2000.Tier1.causalTop
  have e : bidx w x y / (fgeo w h b).st = y + 1 := by
    simp only [fgeo, bidx]
    rw [Nat.add_assoc, Nat.mul_comm, Nat.add_comm, Nat.add_mul_div_left _ _ (by omega),
      Nat.div_eq_of_lt (by omega)]
    omega
  simp only [e]
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  omega

/-- If bit `j` of the word at `(x', y')` reads `(x, y)`, the neighbour is hidden exactly when
`(x, y)` is a stripe top (below the first stripe) and `(x', y')` is in the row above. -/
theorem hidden_iff (w h : Nat) (b : Band) (vc : Bool) (x y x' y' j : Nat)
    (hp : nbPos j x' y' = ((x : Int), (y : Int))) :
    (gV w h b vc).hidden y' (y : Int) =
      ((vc && (decide (0 < y) && y % 4 == 0)) && decide ((y' : Int) - y = -1)) := by
  have ho := (nbPos_eq_iff j x y x' y').mp hp
  have hd : (y' : Int) - y = -1 ∨ (y' : Int) - y = 0 ∨ (y' : Int) - y = 1 := by
    unfold nbOff at ho
    split at ho <;> simp only [Prod.mk.injEq] at ho <;> omega
  unfold Geom.hidden
  simp only [gV]
  cases vc
  · simp
  · rw [Bool.eq_iff_iff]
    simp only [Bool.true_and, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    omega

/-- Reading a hidden-aware neighbour after writing one coefficient. -/
theorem nbAt_setCoeff (w h : Nat) (b : Band) (vc : Bool) (cs : Array Coeff) (hs : cs.size = w * h)
    (x y : Nat) (hx : x < w) (hy : y < h) (c : Coeff) (y' : Nat) (P : Int × Int) :
    (gV w h b vc).nbAt ((gV w h b vc).setCoeff cs x y c) y' P.1 P.2 =
      if P = ((x : Int), (y : Int)) then (if (gV w h b vc).hidden y' P.2 then {} else c)
      else (gV w h b vc).nbAt cs y' P.1 P.2 := by
  unfold Geom.nbAt
  rw [coeffAt_setCoeff_pair (gV w h b vc) cs hs x y hx hy]
  by_cases hp : P = ((x : Int), (y : Int)) <;> by_cases hh : (gV w h b vc).hidden y' P.2 <;>
    simp [hp, hh]

/-- `specBitV` of bits 0–11. -/
theorem specBitV_lo (g : Geom) (cs : Array Coeff) (x y j : Nat) (hj : j < 12) :
    specBitV g cs x y j =
      (if j < 8 then (g.nbAt cs y (nbPos j x y).1 (nbPos j x y).2).sig
       else (g.nbAt cs y (nbPos j x y).1 (nbPos j x y).2).sig &&
         (g.nbAt cs y (nbPos j x y).1 (nbPos j x y).2).sign) := by
  simp [specBitV, hj]

/-- `specBitV` of bits 12–15. -/
theorem specBitV_hi (g : Geom) (cs : Array Coeff) (x y j : Nat) (hj : 12 ≤ j) :
    specBitV g cs x y j = ownBit (g.coeffAt cs x y) j := by
  simp [specBitV, show ¬ j < 12 by omega]

/-! ## Becoming significant -/

/-- **`setSig` simulates making a coefficient significant**: from `RelM`-related states, with
an insignificant in-block coefficient, a new fast coder state `mq'` related to a spec state
`d'` with the same coefficients, the sign `neg` and the plane weight `one = 2^p`, the fast
`setSig` and the spec update `{sig, sign := neg, mag + 2^p, visited := vis, lsbPlane := p}`
are related (the coder relation is the one of `mq'`/`d'`). -/
theorem setSig_rel {w h : Nat} {b : Band} {vc : Bool} {start : Nat} {raw : Bool}
    {mq : MQ.Dec} {fl mags : Array UInt32} {d : DecState}
    (R : RelM w h b vc start raw ⟨mq, fl, mags⟩ d) {x y : Nat} (hx : x < w) (hy : y < h)
    (hsig : ((gV w h b vc).coeffAt d.coeffs x y).sig = false)
    (one : UInt32) (p : Nat) (hone : one.toNat = 2 ^ p % 2 ^ 32) (vis neg : Bool)
    {start' : Nat} {raw' : Bool} (mq' : MQ.Dec) (d' : DecState)
    (hcd : Coder start' raw' mq' d'.mq d'.cxs d'.raw) (hcs : d'.coeffs = d.coeffs) :
    RelM w h b vc start' raw'
      (JPEG2000.Tier1.setSig (fgeo w h b) vc one vis neg mq' fl mags (bidx w x y))
      { d' with coeffs := ((gV w h b vc).setCoeff d'.coeffs x y
          (sigC ((gV w h b vc).coeffAt d'.coeffs x y) neg p vis)) } := by
  rw [hcs]
  unfold sigC
  have hcsz := R.csize
  have hi : bidx w x y < (w + 2) * (h + 2) := bidx_lt hx hy
  have hsk := causalTop_bidx w h b x y hx
  simp only [JPEG2000.Tier1.setSig]
  rw [hsk]
  simp only [fgeo]
  generalize hskip : (vc && (decide (0 < y) && y % 4 == 0)) = skip
  refine ⟨hcd, by split <;> simp [R.fsize], by simp [R.msize], by simp [hcsz], ?_, ?_⟩
  · intro x' y' j hx' hy' hj
    have FA := flags_afterM fl R.fsize hx hy
      ((JPEG2000.Tier1.fget fl (bidx w x y) &&& ~~~JPEG2000.Tier1.VIS ||| JPEG2000.Tier1.SIG |||
          if neg = true then JPEG2000.Tier1.NEG else 0) |||
        if vis = true then JPEG2000.Tier1.VIS else 0) neg skip hx' hy'
    simp only at FA
    simp only
    rw [FA]
    by_cases he : x' = x ∧ y' = y
    · obtain ⟨rfl, rfl⟩ := he
      simp only [and_self, ↓reduceIte]
      by_cases hj12 : j < 12
      · have n12 : ¬ (12 = j) := by omega
        have n13 : ¬ (13 = j) := by omega
        rw [specBitV_lo _ _ _ _ _ hj12, nbAt_setCoeff w h b vc _ hcsz _ _ hx hy,
          ite_neg' (nbPos_ne _ _ _)]
        simp only [bt_or, bt_and, bt_ite, bt_SIG, bt_NEG, bt_VIS, bt_zero, n12, n13,
          bt_notVIS j hj, decide_false, Bool.and_false, Bool.or_false]
        have hv : (decide (14 = j)) = false := by simp; omega
        rw [hv]
        simp only [Bool.not_false, Bool.and_true]
        cases vis <;> cases neg <;> simp only [Bool.false_eq_true, ↓reduceIte, bt_zero, bt_VIS,
          bt_NEG, hv, n13, decide_false, Bool.or_false] <;>
          rw [R.flag x' y' j hx hy hj, specBitV_lo _ _ _ _ _ hj12]
      · have o := bitV_own R hx hy
        simp only at o
        obtain ⟨o1, o2, o3, o4⟩ := o
        rw [specBitV_hi _ _ _ _ _ (by omega), coeffAt_setCoeff _ _ hcsz _ _ hx hy]
        rcases (by omega : j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15) with rfl | rfl | rfl | rfl <;>
          simp [ownBit, bt_ite, bt_notVIS, o1, o2, o3, o4, hsig] <;> cases vis <;> cases neg <;>
          simp_all
    · simp only [he, ↓reduceIte, bt_or]
      rw [R.flag x' y' j hx' hy' hj]
      by_cases hj12 : j < 12
      · rw [bt_nbMaskV _ _ _ _ _ hj12, specBitV_lo _ _ _ _ _ hj12, specBitV_lo _ _ _ _ _ hj12,
          nbAt_setCoeff w h b vc _ hcsz _ _ hx hy]
        by_cases hp : nbPos j x' y' = ((x : Int), (y : Int))
        · have ho : nbOff j = ((x' : Int) - x, (y' : Int) - y) := (nbPos_eq_iff _ _ _ _ _).mp hp
          have hh := hidden_iff w h b vc x y x' y' j hp
          rw [hskip] at hh
          simp only [hp, ↓reduceIte, ho, decide_true, Bool.and_true]
          unfold Geom.nbAt
          rw [hh]
          cases hk : (skip && decide ((y' : Int) - y = -1))
          · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_and]
            by_cases h8 : j < 8 <;> simp [h8, hsig]
          · simp
        · have ho : ¬ nbOff j = ((x' : Int) - x, (y' : Int) - y) :=
            fun e => hp ((nbPos_eq_iff _ _ _ _ _).mpr e)
          simp only [hp, ↓reduceIte, ho, decide_false, Bool.and_false, Bool.false_and,
            Bool.or_false]
      · rw [bt_nbMaskV_hi _ _ _ _ _ (by omega), specBitV_hi _ _ _ _ _ (by omega),
          specBitV_hi _ _ _ _ _ (by omega), coeffAt_setCoeff _ _ hcsz _ _ hx hy]
        have : ¬ ((x' : Int) = x ∧ (y' : Int) = y) := by omega
        simp [this]
  · intro x' y' hx' hy'
    simp only
    rw [fget_fset _ _ _ _ (by rw [R.msize]; exact hi), coeffAt_setCoeff _ _ hcsz _ _ hx hy]
    by_cases he : x' = x ∧ y' = y
    · obtain ⟨rfl, rfl⟩ := he
      simp only [↓reduceIte, and_self]
      rw [UInt32.toNat_add, R.mag x' y' hx hy, hone]
      simp [Nat.add_mod]
    · have hne : bidx w x y ≠ bidx w x' y' := fun e => he (by
        obtain ⟨a, b⟩ := (bidx_eq_iff hx hx').mp e; exact ⟨a.symm, b.symm⟩)
      have : ¬ ((x' : Int) = x ∧ (y' : Int) = y) := by omega
      simp only [hne, ↓reduceIte, this]
      exact R.mag x' y' hx' hy'

end JPEG2000.Spec.Tier1EquivM
