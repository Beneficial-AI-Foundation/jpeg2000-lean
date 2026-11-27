import Spec.Tier1Equiv.Nb

/-!
# C3 (plain mode), part 3b: one coding step preserves the simulation

Plan.md §4 (C3), §5.2 "Tier-1 / EBCOT" ("preserved by each pass"); T.800 D.3.1–D.3.4.
Task 3.6.

For an in-block position `(x, y)` (bordered index `bidx w x y`), each fast coding primitive
maps `Rel`-related states to `Rel`-related states, against the spec primitive at `(x, y)`:

| fast (`JPEG2000.Tier1`) | spec (`Spec.Tier1`) | lemma |
|---|---|---|
| `MQ.Dec.decode` | `DecState.decodeBit` | `decode_rel` |
| `becomeSig` | `becomeSignificant` | `becomeSig_rel` |
| `zeroCode` | `zeroCode` | `zeroCode_rel` |
| `spStep` | `sigPropStep` | `spStep_rel` |
| `mrStep` | `magRefStep` | `mrStep_rel` |
| `cuStep` | `cleanupStep` | `cuStep_rel` |

The bit-plane weight is `one` with `one.toNat = 2^p mod 2^32` (`p` the spec's plane).
-/

namespace JPEG2000.Spec.Tier1Equiv

open JPEG2000
open JPEG2000.Tier2.Geometry (Band)
open JPEG2000.Spec.Tier1 (Coeff Geom DecState)

/-! ## Helpers -/

/-- Bordered indices of in-block positions are distinct. -/
theorem bidx_eq_iff {w x y x' y' : Nat} (hx : x < w) (hx' : x' < w) :
    bidx w x y = bidx w x' y' ↔ x = x' ∧ y = y' := by
  unfold bidx
  constructor
  · intro e
    rw [Nat.add_assoc, Nat.add_assoc] at e
    obtain ⟨a, b⟩ := rowcol_inj (by omega) (by omega) e
    omega
  · intro ⟨rfl, rfl⟩; rfl

/-- Bits 0–15 of `~~~VIS`. -/
theorem bt_notVIS : ∀ j < 16, bt (~~~Tier1.VIS) j = !decide (14 = j) := by decide

/-- Read after write of spec coefficients, at a neighbour given as a pair. -/
theorem coeffAt_setCoeff_pair (g : Geom) (cs : Array Coeff) (hs : cs.size = g.width * g.height)
    (x y : Nat) (hx : x < g.width) (hy : y < g.height) (c : Coeff) (P : Int × Int) :
    g.coeffAt (g.setCoeff cs x y c) P.1 P.2 =
      if P = ((x : Int), (y : Int)) then c else g.coeffAt cs P.1 P.2 := by
  rw [coeffAt_setCoeff g cs hs x y hx hy]
  obtain ⟨X, Y⟩ := P
  simp [Prod.mk.injEq]

/-- The own bits 12–15 of a coefficient. -/
def ownBit (c : Coeff) (j : Nat) : Bool :=
  if j = 12 then c.sig
  else if j = 13 then c.sig && c.sign
  else if j = 14 then c.visited
  else if j = 15 then c.refined
  else false

/-- `specBit` for the own bits. -/
theorem specBit_hi (g : Geom) (cs : Array Coeff) (x y j : Nat) (hj : 12 ≤ j) :
    specBit g cs x y j = ownBit (g.coeffAt cs x y) j := by
  simp [specBit, ownBit, show ¬ j < 12 by omega]

/-- `specBit` for the neighbour bits. -/
theorem specBit_lo (g : Geom) (cs : Array Coeff) (x y j : Nat) (hj : j < 12) :
    specBit g cs x y j =
      (if j < 8 then (g.coeffAt cs (nbPos j x y).1 (nbPos j x y).2).sig
       else (g.coeffAt cs (nbPos j x y).1 (nbPos j x y).2).sig &&
         (g.coeffAt cs (nbPos j x y).1 (nbPos j x y).2).sign) := by
  simp [specBit, hj]

/-- Coefficient sizes of the plain geometry. -/
theorem sgeom_size (w h : Nat) (b : Band) :
    (sgeom w h b).width = w ∧ (sgeom w h b).height = h := ⟨rfl, rfl⟩

/-! ## Updating one coefficient without changing its significance -/

/-- **Own update**: rewriting the word and magnitude of one in-block coefficient, and its spec
state to `c'` with the same `sig` and `sign`, preserves the relation when the new word keeps
bits 0–11 and has `c'`'s own bits 12–15 and the new magnitude is `c'.mag` modulo `2^32`. -/
theorem rel_own {w h : Nat} {b : Band} {start : Nat} {mq : MQ.Dec} {fl mags : Array UInt32}
    {d : DecState} (R : Rel w h b start ⟨mq, fl, mags⟩ d) {x y : Nat} (hx : x < w) (hy : y < h)
    (fl' mags' : Array UInt32) (hfs : fl'.size = fl.size) (hms : mags'.size = mags.size)
    (hfo : ∀ k, k ≠ bidx w x y → Tier1.fget fl' k = Tier1.fget fl k)
    (hmo : ∀ k, k ≠ bidx w x y → Tier1.fget mags' k = Tier1.fget mags k)
    (c' : Coeff) (hsig : c'.sig = ((sgeom w h b).coeffAt d.coeffs x y).sig)
    (hsign : c'.sign = ((sgeom w h b).coeffAt d.coeffs x y).sign)
    (hbits : ∀ j < 16, bt (Tier1.fget fl' (bidx w x y)) j =
      if j < 12 then bt (Tier1.fget fl (bidx w x y)) j else ownBit c' j)
    (hmag : (Tier1.fget mags' (bidx w x y)).toNat = c'.mag % 2 ^ 32) :
    Rel w h b start ⟨mq, fl', mags'⟩
      { d with coeffs := (sgeom w h b).setCoeff d.coeffs x y c' } := by
  have hcs := R.csize
  refine ⟨R.mq, by rw [hfs]; exact R.fsize, by rw [hms]; exact R.msize, by simp [hcs], ?_, ?_⟩
  · intro x' y' j hx' hy' hj
    simp only
    by_cases he : x' = x ∧ y' = y
    · obtain ⟨rfl, rfl⟩ := he
      rw [hbits j hj]
      by_cases hj12 : j < 12
      · rw [ite_pos' hj12, R.flag x' y' j hx hy hj]
        simp only [specBit_lo _ _ _ _ _ hj12]
        rw [coeffAt_setCoeff_pair _ _ hcs _ _ hx hy, ite_neg' (nbPos_ne _ _ _)]
      · rw [ite_neg' hj12, specBit_hi _ _ _ _ _ (by omega)]
        rw [coeffAt_setCoeff _ _ hcs _ _ hx hy]
        simp
    · have hne : bidx w x' y' ≠ bidx w x y := fun e => he ((bidx_eq_iff hx' hx).mp e)
      rw [hfo _ hne, R.flag x' y' j hx' hy' hj]
      by_cases hj12 : j < 12
      · simp only [specBit_lo _ _ _ _ _ hj12]
        rw [coeffAt_setCoeff_pair _ _ hcs _ _ hx hy]
        by_cases hp : nbPos j x' y' = ((x : Int), (y : Int))
        · simp only [hp, ↓reduceIte, hsig, hsign]
        · simp only [hp, ↓reduceIte]
      · rw [specBit_hi _ _ _ _ _ (by omega), specBit_hi _ _ _ _ _ (by omega),
          coeffAt_setCoeff _ _ hcs _ _ hx hy]
        have : ¬ ((x' : Int) = x ∧ (y' : Int) = y) := by omega
        simp [this]
  · intro x' y' hx' hy'
    simp only
    rw [coeffAt_setCoeff _ _ hcs _ _ hx hy]
    by_cases he : x' = x ∧ y' = y
    · obtain ⟨rfl, rfl⟩ := he
      simp [hmag]
    · have hne : bidx w x' y' ≠ bidx w x y := fun e => he ((bidx_eq_iff hx' hx).mp e)
      have : ¬ ((x' : Int) = x ∧ (y' : Int) = y) := by omega
      rw [hmo _ hne, R.mag x' y' hx' hy']
      simp [this]

/-! ## One MQ decision -/

/-- A spec decision leaves the coefficients alone. -/
@[simp] theorem decodeBit_coeffs (d : DecState) (cx : Nat) : (d.decodeBit cx).2.coeffs = d.coeffs := by
  unfold DecState.decodeBit
  generalize Spec.MQ.decode d.mq d.cxs cx = r
  obtain ⟨_, _, _⟩ := r
  rfl

/-- A decision decoded on both sides: same bit, and the relation holds for the new MQ states
(flags, magnitudes and coefficients untouched). -/
theorem decode_rel {w h : Nat} {b : Band} {start : Nat} {mq : MQ.Dec} {fl mags : Array UInt32}
    {d : DecState} (R : Rel w h b start ⟨mq, fl, mags⟩ d) (cx : Nat) :
    (mq.decode cx).1 = (d.decodeBit cx).1 ∧
    Rel w h b start ⟨(mq.decode cx).2, fl, mags⟩ (d.decodeBit cx).2 := by
  obtain ⟨e1, e2⟩ := MQEquiv.decode_sim R.mq cx
  exact ⟨e1, ⟨e2, R.fsize, R.msize, R.csize, R.flag, R.mag⟩⟩

/-! ## A coefficient becomes significant -/

/-- **`becomeSig` simulates `becomeSignificant`** at an insignificant in-block coefficient. -/
theorem becomeSig_rel {w h : Nat} {b : Band} {start : Nat} {s : Tier1.St} {d : DecState}
    (R : Rel w h b start s d) {x y : Nat} (hx : x < w) (hy : y < h)
    (hsig : ((sgeom w h b).coeffAt d.coeffs x y).sig = false)
    (one : UInt32) (p : Nat) (hone : one.toNat = 2 ^ p % 2 ^ 32) (vis : Bool) :
    Rel w h b start (Tier1.becomeSig (fgeo w h b) one vis s (bidx w x y))
      (Spec.Tier1.becomeSignificant (sgeom w h b) p vis d x y) := by
  obtain ⟨mq, fl, mags⟩ := s
  obtain ⟨hcx, hxor⟩ := sign_rel' R hx hy
  simp only at hcx hxor
  simp only [Tier1.becomeSig, Spec.Tier1.becomeSignificant, Spec.Tier1.decodeSign]
  generalize hsc : (sgeom w h b).signContext d.coeffs x y = sc at hcx hxor
  obtain ⟨cx, xb⟩ := sc
  simp only at hcx hxor ⊢
  rw [hcx, hxor]
  obtain ⟨e1, R1⟩ := decode_rel R cx
  generalize mq.decode cx = rf at e1 R1 ⊢
  generalize hrs : d.decodeBit cx = rs at e1 R1 ⊢
  obtain ⟨bf, mq'⟩ := rf
  obtain ⟨bs, d'⟩ := rs
  have hc : d'.coeffs = d.coeffs := by rw [← decodeBit_coeffs d cx, hrs]
  simp only at e1 R1 ⊢
  subst e1
  rw [hc]
  generalize (bf != xb) = neg
  simp only [fgeo]
  have hcs := R.csize
  have hi : bidx w x y < (w + 2) * (h + 2) := by
    rw [(bidx_forms w x y).2.2.2.2.2.2.2.2]; exact nb_lt_size hx hy 1 1 (by decide) (by decide)
  refine ⟨R1.mq, by simp [R.fsize], by simp [R.msize], by simp [hcs], ?_, ?_⟩
  · intro x' y' j hx' hy' hj
    have FA := flags_after fl R.fsize hx hy
      ((Tier1.fget fl (bidx w x y) &&& ~~~Tier1.VIS ||| Tier1.SIG |||
          if neg = true then Tier1.NEG else 0) ||| if vis = true then Tier1.VIS else 0) neg hx' hy'
    simp only at FA
    simp only
    rw [FA]
    by_cases he : x' = x ∧ y' = y
    · obtain ⟨rfl, rfl⟩ := he
      simp only [and_self, ↓reduceIte]
      by_cases hj12 : j < 12
      · have n12 : ¬ (12 = j) := by omega
        have n13 : ¬ (13 = j) := by omega
        have n15 : ¬ (15 = j) := by omega
        rw [specBit_lo _ _ _ _ _ hj12, coeffAt_setCoeff_pair _ _ hcs _ _ hx hy,
          ite_neg' (nbPos_ne _ _ _)]
        simp only [bt_or, bt_and, bt_ite, bt_SIG, bt_NEG, bt_VIS, bt_zero, n12, n13,
          bt_notVIS j hj, decide_false, Bool.and_false, Bool.or_false]
        have hv : (decide (14 = j)) = false := by simp; omega
        rw [hv]
        simp only [Bool.not_false, Bool.and_true]
        cases vis <;> cases neg <;> simp only [Bool.false_eq_true, ↓reduceIte, bt_zero, bt_VIS,
          bt_NEG, hv, n13, decide_false, Bool.or_false] <;>
          rw [R.flag x' y' j hx hy hj, specBit_lo _ _ _ _ _ hj12]
      · have o := bit_own R hx hy
        simp only at o
        obtain ⟨o1, o2, o3, o4⟩ := o
        rw [specBit_hi _ _ _ _ _ (by omega), coeffAt_setCoeff _ _ hcs _ _ hx hy]
        rcases (by omega : j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15) with rfl | rfl | rfl | rfl <;>
          simp [ownBit, bt_ite, bt_notVIS, o1, o2, o3, o4, hsig] <;> cases vis <;> cases neg <;>
          simp_all
    · simp only [he, ↓reduceIte, bt_or]
      rw [R.flag x' y' j hx' hy' hj]
      by_cases hj12 : j < 12
      · rw [bt_nbMask _ _ _ _ hj12, specBit_lo _ _ _ _ _ hj12, specBit_lo _ _ _ _ _ hj12,
          coeffAt_setCoeff_pair _ _ hcs _ _ hx hy]
        by_cases hp : nbPos j x' y' = ((x : Int), (y : Int))
        · have ho : nbOff j = ((x' : Int) - x, (y' : Int) - y) := (nbPos_eq_iff _ _ _ _ _).mp hp
          simp only [hp, ↓reduceIte, ho, decide_true, Bool.true_and]
          by_cases h8 : j < 8 <;> simp [h8, hsig]
        · have ho : ¬ nbOff j = ((x' : Int) - x, (y' : Int) - y) :=
            fun e => hp ((nbPos_eq_iff _ _ _ _ _).mpr e)
          simp only [hp, ↓reduceIte, ho, decide_false, Bool.false_and, Bool.or_false]
      · rw [bt_nbMask_hi _ _ _ _ (by omega), specBit_hi _ _ _ _ _ (by omega),
          specBit_hi _ _ _ _ _ (by omega), coeffAt_setCoeff _ _ hcs _ _ hx hy]
        have : ¬ ((x' : Int) = x ∧ (y' : Int) = y) := by omega
        simp [this]
  · intro x' y' hx' hy'
    simp only
    rw [fget_fset _ _ _ _ (by rw [R.msize]; exact hi), coeffAt_setCoeff _ _ hcs _ _ hx hy]
    by_cases he : x' = x ∧ y' = y
    · obtain ⟨rfl, rfl⟩ := he
      simp only [↓reduceIte, and_self]
      rw [UInt32.toNat_add, R.mag x' y' hx hy, hone]
      simp [Nat.add_mod]
    · have hne : bidx w x y ≠ bidx w x' y' := fun e => he (by obtain ⟨a, b⟩ := (bidx_eq_iff hx hx').mp e; exact ⟨a.symm, b.symm⟩)
      have : ¬ ((x' : Int) = x ∧ (y' : Int) = y) := by omega
      simp only [hne, ↓reduceIte, this]
      exact R.mag x' y' hx' hy'

/-! ## Zero coding and the pass steps -/

/-- The bordered index of an in-block position is in range. -/
theorem bidx_lt {w h x y : Nat} (hx : x < w) (hy : y < h) : bidx w x y < (w + 2) * (h + 2) := by
  rw [(bidx_forms w x y).2.2.2.2.2.2.2.2]; exact nb_lt_size hx hy 1 1 (by decide) (by decide)

/-- **`zeroCode` simulates the spec `zeroCode`** at an insignificant in-block coefficient (when
`vis` is false the coefficient must not be visited: the fast decoder then writes nothing). -/
theorem zeroCode_rel {w h : Nat} {b : Band} {start : Nat} {s : Tier1.St} {d : DecState}
    (R : Rel w h b start s d) {x y : Nat} (hx : x < w) (hy : y < h)
    (hsig : ((sgeom w h b).coeffAt d.coeffs x y).sig = false)
    (one : UInt32) (p : Nat) (hone : one.toNat = 2 ^ p % 2 ^ 32) (vis : Bool)
    (hvis : vis = false → ((sgeom w h b).coeffAt d.coeffs x y).visited = false) :
    Rel w h b start (JPEG2000.Tier1.zeroCode (fgeo w h b) one vis s (bidx w x y))
      (Spec.Tier1.zeroCode (sgeom w h b) p vis d x y) := by
  obtain ⟨mq, fl, mags⟩ := s
  have hz : Tier1.zcCtx (fgeo w h b).zc (fgeo w h b).hzc (Tier1.fget fl (bidx w x y)) =
      (sgeom w h b).zcCtx d.coeffs x y := zc_rel R hx hy
  simp only [JPEG2000.Tier1.zeroCode, Spec.Tier1.zeroCode]
  rw [hz]
  obtain ⟨e1, R1⟩ := decode_rel R ((sgeom w h b).zcCtx d.coeffs x y)
  generalize mq.decode ((sgeom w h b).zcCtx d.coeffs x y) = rf at e1 R1 ⊢
  generalize hrs : d.decodeBit ((sgeom w h b).zcCtx d.coeffs x y) = rs at e1 R1 ⊢
  obtain ⟨bf, mq'⟩ := rf
  obtain ⟨bs, d'⟩ := rs
  have hc : d'.coeffs = d.coeffs := by rw [← decodeBit_coeffs d _, hrs]
  simp only at e1 R1 ⊢
  subst e1
  have hi : bidx w x y < fl.size := by rw [R.fsize]; exact bidx_lt hx hy
  have o := bit_own R1 hx hy
  simp only [hc] at o
  obtain ⟨o1, o2, o3, o4⟩ := o
  cases bf
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases vis
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hv := hvis rfl
      have := rel_own R1 hx hy fl mags rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
        { (sgeom w h b).coeffAt d'.coeffs x y with visited := false } rfl rfl
        (by
          intro j hj
          split
          · rfl
          · rw [hc]
            rcases (by omega : j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15) with rfl | rfl | rfl | rfl <;>
              simp [ownBit, o1, o2, o3, o4, hv])
        (by rw [R1.mag x y hx hy])
      exact this
    · simp only [↓reduceIte]
      have := rel_own R1 hx hy (Tier1.fset fl (bidx w x y) (Tier1.fget fl (bidx w x y) ||| Tier1.VIS))
        mags (by simp) rfl
        (fun k hk => by rw [fget_fset _ _ _ _ hi]; simp [Ne.symm hk]) (fun _ _ => rfl)
        { (sgeom w h b).coeffAt d'.coeffs x y with visited := true } rfl rfl
        (by
          intro j hj
          rw [fget_fset _ _ _ _ hi]
          simp only [↓reduceIte, bt_or, bt_VIS]
          split
          · have : ¬ (14 = j) := by omega
            simp [this]
          · rw [hc]
            rcases (by omega : j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15) with rfl | rfl | rfl | rfl <;>
              simp [ownBit, o1, o2, o3, o4])
        (by rw [R1.mag x y hx hy])
      exact this
  · simp only [↓reduceIte]
    exact becomeSig_rel R1 hx hy (by rw [hc]; exact hsig) one p hone vis

/-- **`spStep` simulates `sigPropStep`** (D.3.1) at an in-block position. -/
theorem spStep_rel {w h : Nat} {b : Band} {start : Nat} {s : Tier1.St} {d : DecState}
    (R : Rel w h b start s d) {x y : Nat} (hx : x < w) (hy : y < h)
    (one : UInt32) (p : Nat) (hone : one.toNat = 2 ^ p % 2 ^ 32) :
    Rel w h b start (Tier1.spStep (fgeo w h b) one s (bidx w x y))
      (Spec.Tier1.sigPropStep (sgeom w h b) p d (x, y)) := by
  simp only [Tier1.spStep, Spec.Tier1.sigPropStep]
  rw [sigTest_rel R hx hy, nbrTest_rel R hx hy]
  by_cases hc : (!((sgeom w h b).coeffAt d.coeffs x y).sig &&
      (sgeom w h b).anySigNeighbour d.coeffs x y) = true
  · simp only [hc, ↓reduceIte]
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
    exact zeroCode_rel R hx hy hc.1 one p hone true (fun h => by cases h)
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]
    exact R

/-- **`mrStep` simulates `magRefStep`** (D.3.3) at an in-block position. -/
theorem mrStep_rel {w h : Nat} {b : Band} {start : Nat} {s : Tier1.St} {d : DecState}
    (R : Rel w h b start s d) {x y : Nat} (hx : x < w) (hy : y < h)
    (one : UInt32) (p : Nat) (hone : one.toNat = 2 ^ p % 2 ^ 32) :
    Rel w h b start (Tier1.mrStep one s (bidx w x y))
      (Spec.Tier1.magRefStep (sgeom w h b) p d (x, y)) := by
  obtain ⟨mq, fl, mags⟩ := s
  have hs := sigTest_rel R hx hy
  have hv := visTest_rel R hx hy
  have hm : Tier1.mrCtxOf (Tier1.fget fl (bidx w x y)) = (sgeom w h b).mrCtx d.coeffs x y :=
    mr_rel R hx hy
  simp only at hs hv
  simp only [Tier1.mrStep, Spec.Tier1.magRefStep]
  have hne : (Tier1.fget fl (bidx w x y) &&& Tier1.SIG != 0) =
      !(Tier1.fget fl (bidx w x y) &&& Tier1.SIG == 0) := rfl
  rw [hne, hs, hv, Bool.not_not, hm]
  by_cases hc : (((sgeom w h b).coeffAt d.coeffs x y).sig &&
      !((sgeom w h b).coeffAt d.coeffs x y).visited) = true
  · simp only [hc, ↓reduceIte]
    obtain ⟨e1, R1⟩ := decode_rel R ((sgeom w h b).mrCtx d.coeffs x y)
    generalize mq.decode ((sgeom w h b).mrCtx d.coeffs x y) = rf at e1 R1 ⊢
    generalize hrs : d.decodeBit ((sgeom w h b).mrCtx d.coeffs x y) = rs at e1 R1 ⊢
    obtain ⟨bf, mq'⟩ := rf
    obtain ⟨bs, d'⟩ := rs
    have hcs : d'.coeffs = d.coeffs := by rw [← decodeBit_coeffs d _, hrs]
    simp only at e1 R1 ⊢
    subst e1
    have hi : bidx w x y < fl.size := by rw [R.fsize]; exact bidx_lt hx hy
    have hmi : bidx w x y < mags.size := by rw [R.msize]; exact bidx_lt hx hy
    have o := bit_own R1 hx hy
    obtain ⟨o1, o2, o3, o4⟩ := o
    simp only at o1 o2 o3 o4
    have := rel_own R1 hx hy
      (Tier1.fset fl (bidx w x y) (Tier1.fget fl (bidx w x y) ||| Tier1.REF))
      (if bf = true then Tier1.fset mags (bidx w x y) (Tier1.fget mags (bidx w x y) + one) else mags)
      (by simp) (by split <;> simp)
      (fun k hk => by rw [fget_fset _ _ _ _ hi]; simp [Ne.symm hk])
      (fun k hk => by split
                      · rw [fget_fset _ _ _ _ hmi]; simp [Ne.symm hk]
                      · rfl)
      { (sgeom w h b).coeffAt d'.coeffs x y with
          mag := ((sgeom w h b).coeffAt d'.coeffs x y).mag + (if bf = true then 2 ^ p else 0),
          refined := true, lsbPlane := p } rfl rfl
      (by
        intro j hj
        rw [fget_fset _ _ _ _ hi]
        simp only [↓reduceIte, bt_or, bt_REF]
        split
        · have : ¬ (15 = j) := by omega
          simp [this]
        · rcases (by omega : j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15) with rfl | rfl | rfl | rfl <;>
            simp [ownBit, o1, o2, o3, o4])
      (by
        cases bf
        · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]; exact R1.mag x y hx hy
        · simp only [↓reduceIte]
          rw [fget_fset _ _ _ _ hmi]
          simp only [↓reduceIte]
          rw [UInt32.toNat_add, R1.mag x y hx hy, hone]
          simp [Nat.add_mod])
    exact this
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]
    exact R

/-- **`cuStep` simulates `cleanupStep`** (D.3.4, normal coding) at an in-block position. -/
theorem cuStep_rel {w h : Nat} {b : Band} {start : Nat} {s : Tier1.St} {d : DecState}
    (R : Rel w h b start s d) {x y : Nat} (hx : x < w) (hy : y < h)
    (one : UInt32) (p : Nat) (hone : one.toNat = 2 ^ p % 2 ^ 32) :
    Rel w h b start (Tier1.cuStep (fgeo w h b) one s (bidx w x y))
      (Spec.Tier1.cleanupStep (sgeom w h b) p d (x, y)) := by
  simp only [Tier1.cuStep, Spec.Tier1.cleanupStep]
  rw [sigVisTest_rel R hx hy]
  by_cases hc : (!((sgeom w h b).coeffAt d.coeffs x y).sig &&
      !((sgeom w h b).coeffAt d.coeffs x y).visited) = true
  · simp only [hc, ↓reduceIte]
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
    exact zeroCode_rel R hx hy hc.1 one p hone false (fun _ => hc.2)
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]
    exact R

end JPEG2000.Spec.Tier1Equiv
