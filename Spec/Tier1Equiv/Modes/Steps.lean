import Spec.Tier1Equiv.Modes.Sig

/-!
# C3 (all code-block styles), part 3: one coding step, MQ or raw

Plan.md §4 (C3), §5.2 "Tier-1 / EBCOT"; T.800 D.3.1–D.3.4, D.6 (raw bit reader and raw
passes), D.7 (vertically causal). Task 7.1c.

For an in-block position, each mode-aware fast primitive maps `RelM`-related states to
`RelM`-related states, against the spec primitive under the geometry `gV w h b vc`:

| fast (`JPEG2000.Tier1`) | spec (`Spec.Tier1`) | lemma | coder |
|---|---|---|---|
| `MQ.Dec.decode` | `DecState.decodeBit` | `decode_relM` | MQ |
| `rawBit` | `rawBit`, `DecState.rawBit` | `rawBit_sim`, `rawBit_relM` | raw |
| `becomeSigM` | `becomeSignificant` | `becomeSigM_rel` | MQ |
| `zeroCodeM` | `zeroCode` | `zeroCodeM_rel` | MQ |
| `spStepM` | `sigPropStep` | `spStepM_rel` | MQ |
| `mrStep` | `magRefStep` | `mrStep_relM` | MQ |
| `cuStepM` | `cleanupStep` | `cuStepM_rel` | MQ |
| `rawSpStep` | `rawSigPropStep` | `rawSpStep_rel` | raw |
| `rawMrStep` | `rawMagRefStep` | `rawMrStep_rel` | raw |
-/

namespace JPEG2000.Spec.Tier1EquivM

open JPEG2000
open JPEG2000.Tier2.Geometry (Band)
open JPEG2000.Spec.Tier1 (Coeff Geom DecState RawState)
open JPEG2000.Spec.Tier1Equiv

/-! ## Updating one coefficient without changing its significance -/

/-- **Own update** (`rel_own` for `RelM`): rewriting the word and magnitude of one in-block
coefficient, and its spec state to `c'` with the same `sig` and `sign`, preserves the
relation when the new word keeps bits 0–11 and has `c'`'s own bits. -/
theorem rel_ownM {w h : Nat} {b : Band} {vc : Bool} {start : Nat} {raw : Bool} {mq : MQ.Dec}
    {fl mags : Array UInt32} {d : DecState} (R : RelM w h b vc start raw ⟨mq, fl, mags⟩ d)
    {x y : Nat} (hx : x < w) (hy : y < h)
    (fl' mags' : Array UInt32) (hfs : fl'.size = fl.size) (hms : mags'.size = mags.size)
    (hfo : ∀ k, k ≠ bidx w x y → JPEG2000.Tier1.fget fl' k = JPEG2000.Tier1.fget fl k)
    (hmo : ∀ k, k ≠ bidx w x y → JPEG2000.Tier1.fget mags' k = JPEG2000.Tier1.fget mags k)
    (c' : Coeff) (hsig : c'.sig = ((gV w h b vc).coeffAt d.coeffs x y).sig)
    (hsign : c'.sign = ((gV w h b vc).coeffAt d.coeffs x y).sign)
    (hbits : ∀ j < 16, bt (JPEG2000.Tier1.fget fl' (bidx w x y)) j =
      if j < 12 then bt (JPEG2000.Tier1.fget fl (bidx w x y)) j else ownBit c' j)
    (hmag : (JPEG2000.Tier1.fget mags' (bidx w x y)).toNat = c'.mag % 2 ^ 32) :
    RelM w h b vc start raw ⟨mq, fl', mags'⟩
      { d with coeffs := (gV w h b vc).setCoeff d.coeffs x y c' } := by
  have hcs := R.csize
  refine ⟨R.coder, by rw [hfs]; exact R.fsize, by rw [hms]; exact R.msize, by simp [hcs], ?_, ?_⟩
  · intro x' y' j hx' hy' hj
    simp only
    by_cases he : x' = x ∧ y' = y
    · obtain ⟨rfl, rfl⟩ := he
      rw [hbits j hj]
      by_cases hj12 : j < 12
      · rw [ite_pos' hj12, R.flag x' y' j hx hy hj]
        simp only [specBitV_lo _ _ _ _ _ hj12]
        rw [nbAt_setCoeff w h b vc _ hcs _ _ hx hy, ite_neg' (nbPos_ne _ _ _)]
      · rw [ite_neg' hj12, specBitV_hi _ _ _ _ _ (by omega)]
        rw [coeffAt_setCoeff _ _ hcs _ _ hx hy]
        simp
    · have hne : bidx w x' y' ≠ bidx w x y := fun e => he ((bidx_eq_iff hx' hx).mp e)
      rw [hfo _ hne, R.flag x' y' j hx' hy' hj]
      by_cases hj12 : j < 12
      · simp only [specBitV_lo _ _ _ _ _ hj12]
        rw [nbAt_setCoeff w h b vc _ hcs _ _ hx hy]
        by_cases hp : nbPos j x' y' = ((x : Int), (y : Int))
        · rw [hp]
          simp only [↓reduceIte]
          cases hh : (gV w h b vc).hidden y' (y : Int) <;> simp [Geom.nbAt, hh, hsig, hsign]
        · simp only [hp, ↓reduceIte]
      · rw [specBitV_hi _ _ _ _ _ (by omega), specBitV_hi _ _ _ _ _ (by omega),
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

/-- A spec decision as a record update. -/
theorem decodeBit_eq (d : DecState) (cx : Nat) :
    d.decodeBit cx = ((Spec.MQ.decode d.mq d.cxs cx).1,
      { d with mq := (Spec.MQ.decode d.mq d.cxs cx).2.1, cxs := (Spec.MQ.decode d.mq d.cxs cx).2.2 }) := by
  unfold DecState.decodeBit
  generalize Spec.MQ.decode d.mq d.cxs cx = r
  obtain ⟨_, _, _⟩ := r
  rfl

/-- A decision decoded on both sides (MQ coder): same bit, related states. -/
theorem decode_relM {w h : Nat} {b : Band} {vc : Bool} {start : Nat} {mq : MQ.Dec}
    {fl mags : Array UInt32} {d : DecState} (R : RelM w h b vc start false ⟨mq, fl, mags⟩ d)
    (cx : Nat) :
    (mq.decode cx).1 = (d.decodeBit cx).1 ∧
    RelM w h b vc start false ⟨(mq.decode cx).2, fl, mags⟩ (d.decodeBit cx).2 := by
  obtain ⟨e1, e2⟩ := MQEquiv.decode_sim (show MQEquiv.Rel start mq d.mq d.cxs from R.coder) cx
  rw [decodeBit_eq]
  exact ⟨e1, ⟨e2, R.fsize, R.msize, R.csize, R.flag, R.mag⟩⟩

/-! ## One raw bit -/

/-- **The raw bit reader** (D.6): the fast `rawBit` on the `MQ.Dec` record simulates the spec
`rawBit` — same bit, related readers, contexts untouched. -/
theorem rawBit_sim {start : Nat} {d : MQ.Dec} {r : RawState} (h : RawSim start d r) :
    (JPEG2000.Tier1.rawBit d).1 = (Spec.Tier1.rawBit r).1 ∧
    RawSim start (JPEG2000.Tier1.rawBit d).2 (Spec.Tier1.rawBit r).2 ∧
    (JPEG2000.Tier1.rawBit d).2.cx = d.cx := by
  -- the final step, after a byte is available
  have fin : ∀ (d1 : MQ.Dec) (s1 : RawState), RawSim start d1 s1 → 1 ≤ s1.ct →
      ((d1.c >>> (d1.ct - 1)) &&& 1 != 0) = (s1.byte / 2 ^ (s1.ct - 1) % 2 == 1) ∧
      RawSim start { d1 with ct := d1.ct - 1 } { s1 with ct := s1.ct - 1 } := by
    intro d1 s1 h1 hc1
    have hle : (1 : UInt32) ≤ d1.ct := by
      rw [UInt32.le_iff_toNat_le, h1.ct]; simpa using hc1
    have ect : (d1.ct - 1).toNat = s1.ct - 1 := by
      rw [UInt32.toNat_sub_of_le _ _ hle, h1.ct]; rfl
    refine ⟨?_, ⟨h1.c, by simpa using ect, by show s1.ct - 1 ≤ 8; have := h1.ctle; omega, h1.blt, h1.pos,
      fun j => by simpa [MQ.Dec.byteAt] using h1.data j⟩⟩
    have e : ((d1.c >>> (d1.ct - 1)) &&& 1).toNat = s1.byte / 2 ^ (s1.ct - 1) % 2 := by
      rw [UInt32.toNat_and, UInt32.toNat_shiftRight, ect, h1.c]
      have : (s1.ct - 1) % 32 = s1.ct - 1 := Nat.mod_eq_of_lt (by have := h1.ctle; omega)
      rw [this, Nat.shiftRight_eq_div_pow]
      exact Nat.and_two_pow_sub_one_eq_mod _ 1
    have : ((d1.c >>> (d1.ct - 1)) &&& 1 != 0) =
        !decide (((d1.c >>> (d1.ct - 1)) &&& 1).toNat = 0) := by
      generalize (d1.c >>> (d1.ct - 1)) &&& 1 = u
      by_cases hu : u = 0
      · subst hu; rfl
      · have : u.toNat ≠ 0 := fun h' => hu (UInt32.toNat_inj.mp (by simpa using h'))
        simp [hu, this]
    rw [this, e]
    have := Nat.mod_lt (s1.byte / 2 ^ (s1.ct - 1)) (show 0 < 2 by decide)
    by_cases hz : s1.byte / 2 ^ (s1.ct - 1) % 2 = 0
    · simp [hz]
    · have : s1.byte / 2 ^ (s1.ct - 1) % 2 = 1 := by omega
      simp [this]
  have hb0 : (d.byteAt d.pos).toNat = Spec.MQ.byteAt r.data r.pos := by rw [h.pos]; exact h.data _
  have hblt : Spec.MQ.byteAt r.data r.pos < 256 := by
    unfold Spec.MQ.byteAt; exact UInt8.toNat_lt _
  have e1 : (d.ct == 0) = decide (r.ct = 0) := by
    rw [Bool.eq_iff_iff]
    simp only [beq_iff_eq, decide_eq_true_eq, ← h.ct]
    constructor
    · intro e; rw [e]; rfl
    · intro e; exact UInt32.toNat_inj.mp (by simpa using e)
  have e2 : (d.c == 0xFF) = decide (r.byte = 0xFF) := by
    rw [Bool.eq_iff_iff]
    simp only [beq_iff_eq, decide_eq_true_eq, ← h.c]
    constructor
    · intro e; rw [e]; rfl
    · intro e; exact UInt32.toNat_inj.mp (by simpa using e)
  have e3 : (d.byteAt d.pos > 0x8F) ↔ (Spec.MQ.byteAt r.data r.pos > 0x8F) := by
    rw [← hb0, GT.gt, UInt32.lt_iff_toNat_lt]; rfl
  unfold JPEG2000.Tier1.rawBit Spec.Tier1.rawBit
  dsimp only
  by_cases hct : r.ct = 0
  · simp only [e1, hct, decide_true, ↓reduceIte]
    by_cases hc : r.byte = 0xFF
    · simp only [e2, hc, decide_true, ↓reduceIte]
      by_cases hb : Spec.MQ.byteAt r.data r.pos > 0x8F
      · have hb' := e3.mpr hb
        simp only [hb, hb', ↓reduceIte]
        obtain ⟨f1, f2⟩ := fin { d with c := 0xFF, ct := 8 } { r with byte := 0xFF, ct := 8 }
          ⟨rfl, rfl, by dsimp only; decide, by dsimp only; decide, h.pos, fun j => by simpa [MQ.Dec.byteAt] using h.data j⟩
          (by dsimp only; decide)
        first | exact ⟨f1, f2, rfl⟩ | exact ⟨f1, f2, trivial⟩
      · have hb' : ¬ (d.byteAt d.pos > 0x8F) := fun e => hb (e3.mp e)
        simp only [hb, hb', ↓reduceIte]
        obtain ⟨f1, f2⟩ := fin { d with c := d.byteAt d.pos, pos := d.pos + 1, ct := 7 }
          { r with byte := Spec.MQ.byteAt r.data r.pos, pos := r.pos + 1, ct := 7 }
          ⟨hb0, rfl, by dsimp only; decide, hblt, by simp [h.pos]; omega,
            fun j => by simpa [MQ.Dec.byteAt] using h.data j⟩ (by dsimp only; decide)
        first | exact ⟨f1, f2, rfl⟩ | exact ⟨f1, f2, trivial⟩
    · simp only [e2, hc, decide_false, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨f1, f2⟩ := fin { d with c := d.byteAt d.pos, pos := d.pos + 1, ct := 8 }
        { r with byte := Spec.MQ.byteAt r.data r.pos, pos := r.pos + 1, ct := 8 }
        ⟨hb0, rfl, by dsimp only; decide, hblt, by simp [h.pos]; omega,
          fun j => by simpa [MQ.Dec.byteAt] using h.data j⟩ (by dsimp only; decide)
      first | exact ⟨f1, f2, rfl⟩ | exact ⟨f1, f2, trivial⟩
  · simp only [e1, hct, decide_false, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨f1, f2⟩ := fin d r h (by omega)
    first | exact ⟨f1, f2, rfl⟩ | exact ⟨f1, f2, trivial⟩

/-- A spec raw bit as a record update. -/
theorem rawBit_eq (d : DecState) :
    d.rawBit = ((Spec.Tier1.rawBit d.raw).1, { d with raw := (Spec.Tier1.rawBit d.raw).2 }) := by
  unfold DecState.rawBit
  generalize Spec.Tier1.rawBit d.raw = r
  obtain ⟨_, _⟩ := r
  rfl

/-- A raw bit read on both sides (raw coder): same bit, related states. -/
theorem rawBit_relM {w h : Nat} {b : Band} {vc : Bool} {start : Nat} {mq : MQ.Dec}
    {fl mags : Array UInt32} {d : DecState} (R : RelM w h b vc start true ⟨mq, fl, mags⟩ d) :
    (JPEG2000.Tier1.rawBit mq).1 = d.rawBit.1 ∧
    RelM w h b vc start true ⟨(JPEG2000.Tier1.rawBit mq).2, fl, mags⟩ d.rawBit.2 := by
  have hc : RawSim start mq d.raw ∧ MQEquiv.CxRel mq.cx d.cxs := R.coder
  obtain ⟨e1, e2, e3⟩ := rawBit_sim hc.1
  rw [rawBit_eq]
  refine ⟨e1, ⟨⟨e2, by rw [e3]; exact hc.2⟩, R.fsize, R.msize, R.csize, R.flag, R.mag⟩⟩

/-! ## Becoming significant, zero coding, the MQ pass steps -/

section mq
variable {w h : Nat} {b : Band} {vc : Bool} {start : Nat}

/-- **`becomeSigM` simulates `becomeSignificant`** at an insignificant in-block coefficient. -/
theorem becomeSigM_rel {s : JPEG2000.Tier1.St} {d : DecState}
    (R : RelM w h b vc start false s d) {x y : Nat} (hx : x < w) (hy : y < h)
    (hsig : ((gV w h b vc).coeffAt d.coeffs x y).sig = false)
    (one : UInt32) (p : Nat) (hone : one.toNat = 2 ^ p % 2 ^ 32) (vis : Bool) :
    RelM w h b vc start false (JPEG2000.Tier1.becomeSigM (fgeo w h b) vc one vis s (bidx w x y))
      (Spec.Tier1.becomeSignificant (gV w h b vc) p vis d x y) := by
  obtain ⟨mq, fl, mags⟩ := s
  obtain ⟨hcx, hxor⟩ := sign_relM' R hx hy
  simp only at hcx hxor
  simp only [JPEG2000.Tier1.becomeSigM, Spec.Tier1.becomeSignificant, Spec.Tier1.decodeSign]
  generalize hsc : (gV w h b vc).signContext d.coeffs x y = sc at hcx hxor
  obtain ⟨cx, xb⟩ := sc
  simp only at hcx hxor ⊢
  rw [hcx, hxor]
  obtain ⟨e1, R1⟩ := decode_relM R cx
  generalize mq.decode cx = rf at e1 R1 ⊢
  generalize hrs : d.decodeBit cx = rs at e1 R1 ⊢
  obtain ⟨bf, mq'⟩ := rf
  obtain ⟨bs, d'⟩ := rs
  have hc : d'.coeffs = d.coeffs := by rw [← decodeBit_coeffs d cx, hrs]
  simp only at e1 R1 ⊢
  subst e1
  exact setSig_rel R hx hy hsig one p hone vis (bf != xb) mq' d' R1.coder hc

/-- **`zeroCodeM` simulates the spec `zeroCode`** at an insignificant in-block coefficient
(when `vis` is false it must not be visited). -/
theorem zeroCodeM_rel {s : JPEG2000.Tier1.St} {d : DecState}
    (R : RelM w h b vc start false s d) {x y : Nat} (hx : x < w) (hy : y < h)
    (hsig : ((gV w h b vc).coeffAt d.coeffs x y).sig = false)
    (one : UInt32) (p : Nat) (hone : one.toNat = 2 ^ p % 2 ^ 32) (vis : Bool)
    (hvis : vis = false → ((gV w h b vc).coeffAt d.coeffs x y).visited = false) :
    RelM w h b vc start false (JPEG2000.Tier1.zeroCodeM (fgeo w h b) vc one vis s (bidx w x y))
      (Spec.Tier1.zeroCode (gV w h b vc) p vis d x y) := by
  obtain ⟨mq, fl, mags⟩ := s
  have hz : JPEG2000.Tier1.zcCtx (fgeo w h b).zc (fgeo w h b).hzc
      (JPEG2000.Tier1.fget fl (bidx w x y)) = (gV w h b vc).zcCtx d.coeffs x y := zc_relM R hx hy
  simp only [JPEG2000.Tier1.zeroCodeM, Spec.Tier1.zeroCode]
  rw [hz]
  obtain ⟨e1, R1⟩ := decode_relM R ((gV w h b vc).zcCtx d.coeffs x y)
  generalize mq.decode ((gV w h b vc).zcCtx d.coeffs x y) = rf at e1 R1 ⊢
  generalize hrs : d.decodeBit ((gV w h b vc).zcCtx d.coeffs x y) = rs at e1 R1 ⊢
  obtain ⟨bf, mq'⟩ := rf
  obtain ⟨bs, d'⟩ := rs
  have hc : d'.coeffs = d.coeffs := by rw [← decodeBit_coeffs d _, hrs]
  simp only at e1 R1 ⊢
  subst e1
  have hi : bidx w x y < fl.size := by rw [R.fsize]; exact bidx_lt hx hy
  have o := bitV_own R1 hx hy
  simp only [hc] at o
  obtain ⟨o1, o2, o3, o4⟩ := o
  cases bf
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases vis
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hv := hvis rfl
      have := rel_ownM R1 hx hy fl mags rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
        { (gV w h b vc).coeffAt d'.coeffs x y with visited := false } rfl rfl
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
      have := rel_ownM R1 hx hy
        (JPEG2000.Tier1.fset fl (bidx w x y) (JPEG2000.Tier1.fget fl (bidx w x y) ||| JPEG2000.Tier1.VIS))
        mags (by simp) rfl
        (fun k hk => by rw [fget_fset _ _ _ _ hi]; simp [Ne.symm hk]) (fun _ _ => rfl)
        { (gV w h b vc).coeffAt d'.coeffs x y with visited := true } rfl rfl
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
    exact becomeSigM_rel R1 hx hy (by rw [hc]; exact hsig) one p hone vis

/-- **`spStepM` simulates `sigPropStep`** (D.3.1). -/
theorem spStepM_rel {s : JPEG2000.Tier1.St} {d : DecState}
    (R : RelM w h b vc start false s d) {x y : Nat} (hx : x < w) (hy : y < h)
    (one : UInt32) (p : Nat) (hone : one.toNat = 2 ^ p % 2 ^ 32) :
    RelM w h b vc start false (JPEG2000.Tier1.spStepM (fgeo w h b) vc one s (bidx w x y))
      (Spec.Tier1.sigPropStep (gV w h b vc) p d (x, y)) := by
  simp only [JPEG2000.Tier1.spStepM, Spec.Tier1.sigPropStep]
  rw [sigTest_relM R hx hy, nbrTest_relM R hx hy]
  by_cases hc : (!((gV w h b vc).coeffAt d.coeffs x y).sig &&
      (gV w h b vc).anySigNeighbour d.coeffs x y) = true
  · simp only [hc, ↓reduceIte]
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
    exact zeroCodeM_rel R hx hy hc.1 one p hone true (fun h => by cases h)
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]
    exact R

/-- **`cuStepM` simulates `cleanupStep`** (D.3.4, normal coding). -/
theorem cuStepM_rel {s : JPEG2000.Tier1.St} {d : DecState}
    (R : RelM w h b vc start false s d) {x y : Nat} (hx : x < w) (hy : y < h)
    (one : UInt32) (p : Nat) (hone : one.toNat = 2 ^ p % 2 ^ 32) :
    RelM w h b vc start false (JPEG2000.Tier1.cuStepM (fgeo w h b) vc one s (bidx w x y))
      (Spec.Tier1.cleanupStep (gV w h b vc) p d (x, y)) := by
  simp only [JPEG2000.Tier1.cuStepM, Spec.Tier1.cleanupStep]
  rw [sigVisTest_relM R hx hy]
  by_cases hc : (!((gV w h b vc).coeffAt d.coeffs x y).sig &&
      !((gV w h b vc).coeffAt d.coeffs x y).visited) = true
  · simp only [hc, ↓reduceIte]
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
    exact zeroCodeM_rel R hx hy hc.1 one p hone false (fun _ => hc.2)
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]
    exact R

/-- **`mrStep` simulates `magRefStep`** (D.3.3) under `RelM`. -/
theorem mrStep_relM {s : JPEG2000.Tier1.St} {d : DecState}
    (R : RelM w h b vc start false s d) {x y : Nat} (hx : x < w) (hy : y < h)
    (one : UInt32) (p : Nat) (hone : one.toNat = 2 ^ p % 2 ^ 32) :
    RelM w h b vc start false (JPEG2000.Tier1.mrStep one s (bidx w x y))
      (Spec.Tier1.magRefStep (gV w h b vc) p d (x, y)) := by
  obtain ⟨mq, fl, mags⟩ := s
  have hs := sigTest_relM R hx hy
  have hv := visTest_relM R hx hy
  have hm : JPEG2000.Tier1.mrCtxOf (JPEG2000.Tier1.fget fl (bidx w x y)) =
      (gV w h b vc).mrCtx d.coeffs x y := mr_relM R hx hy
  simp only at hs hv
  simp only [JPEG2000.Tier1.mrStep, Spec.Tier1.magRefStep]
  have hne : (JPEG2000.Tier1.fget fl (bidx w x y) &&& JPEG2000.Tier1.SIG != 0) =
      !(JPEG2000.Tier1.fget fl (bidx w x y) &&& JPEG2000.Tier1.SIG == 0) := rfl
  rw [hne, hs, hv, Bool.not_not, hm]
  by_cases hc : (((gV w h b vc).coeffAt d.coeffs x y).sig &&
      !((gV w h b vc).coeffAt d.coeffs x y).visited) = true
  · simp only [hc, ↓reduceIte]
    obtain ⟨e1, R1⟩ := decode_relM R ((gV w h b vc).mrCtx d.coeffs x y)
    generalize mq.decode ((gV w h b vc).mrCtx d.coeffs x y) = rf at e1 R1 ⊢
    generalize hrs : d.decodeBit ((gV w h b vc).mrCtx d.coeffs x y) = rs at e1 R1 ⊢
    obtain ⟨bf, mq'⟩ := rf
    obtain ⟨bs, d'⟩ := rs
    have hcs : d'.coeffs = d.coeffs := by rw [← decodeBit_coeffs d _, hrs]
    simp only at e1 R1 ⊢
    subst e1
    have hi : bidx w x y < fl.size := by rw [R.fsize]; exact bidx_lt hx hy
    have hmi : bidx w x y < mags.size := by rw [R.msize]; exact bidx_lt hx hy
    have o := bitV_own R1 hx hy
    obtain ⟨o1, o2, o3, o4⟩ := o
    simp only at o1 o2 o3 o4
    have := rel_ownM R1 hx hy
      (JPEG2000.Tier1.fset fl (bidx w x y) (JPEG2000.Tier1.fget fl (bidx w x y) ||| JPEG2000.Tier1.REF))
      (if bf = true then JPEG2000.Tier1.fset mags (bidx w x y)
        (JPEG2000.Tier1.fget mags (bidx w x y) + one) else mags)
      (by simp) (by split <;> simp)
      (fun k hk => by rw [fget_fset _ _ _ _ hi]; simp [Ne.symm hk])
      (fun k hk => by split
                      · rw [fget_fset _ _ _ _ hmi]; simp [Ne.symm hk]
                      · rfl)
      { (gV w h b vc).coeffAt d'.coeffs x y with
          mag := ((gV w h b vc).coeffAt d'.coeffs x y).mag + (if bf = true then 2 ^ p else 0),
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

end mq

/-! ## The raw pass steps (D.6) -/

section raw
variable {w h : Nat} {b : Band} {vc : Bool} {start : Nat}

/-- **`rawSpStep` simulates `rawSigPropStep`** (D.6). -/
theorem rawSpStep_rel {s : JPEG2000.Tier1.St} {d : DecState}
    (R : RelM w h b vc start true s d) {x y : Nat} (hx : x < w) (hy : y < h)
    (one : UInt32) (p : Nat) (hone : one.toNat = 2 ^ p % 2 ^ 32) :
    RelM w h b vc start true (JPEG2000.Tier1.rawSpStep (fgeo w h b) vc one s (bidx w x y))
      (Spec.Tier1.rawSigPropStep (gV w h b vc) p d (x, y)) := by
  obtain ⟨mq, fl, mags⟩ := s
  have hs := sigTest_relM R hx hy
  have hn := nbrTest_relM R hx hy
  simp only at hs hn
  simp only [JPEG2000.Tier1.rawSpStep, Spec.Tier1.rawSigPropStep]
  rw [hs, hn]
  by_cases hc : (!((gV w h b vc).coeffAt d.coeffs x y).sig &&
      (gV w h b vc).anySigNeighbour d.coeffs x y) = true
  · simp only [hc, ↓reduceIte]
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
    obtain ⟨e1, R1⟩ := rawBit_relM R
    generalize JPEG2000.Tier1.rawBit mq = rf at e1 R1 ⊢
    generalize hrs : d.rawBit = rs at e1 R1 ⊢
    obtain ⟨bf, mq1⟩ := rf
    obtain ⟨bs, d1⟩ := rs
    have hc1 : d1.coeffs = d.coeffs := by
      simp only [rawBit_eq, Prod.mk.injEq] at hrs; rw [← hrs.2]
    simp only at e1 R1 ⊢
    subst e1
    cases bf
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hi : bidx w x y < fl.size := by rw [R.fsize]; exact bidx_lt hx hy
      have o := bitV_own R1 hx hy
      simp only [hc1] at o
      obtain ⟨o1, o2, o3, o4⟩ := o
      exact rel_ownM R1 hx hy
        (JPEG2000.Tier1.fset fl (bidx w x y) (JPEG2000.Tier1.fget fl (bidx w x y) ||| JPEG2000.Tier1.VIS))
        mags (by simp) rfl
        (fun k hk => by rw [fget_fset _ _ _ _ hi]; simp [Ne.symm hk]) (fun _ _ => rfl)
        { (gV w h b vc).coeffAt d1.coeffs x y with visited := true } rfl rfl
        (by
          intro j hj
          rw [fget_fset _ _ _ _ hi]
          simp only [↓reduceIte, bt_or, bt_VIS]
          split
          · have : ¬ (14 = j) := by omega
            simp [this]
          · rw [hc1]
            rcases (by omega : j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15) with rfl | rfl | rfl | rfl <;>
              simp [ownBit, o1, o2, o3, o4])
        (by rw [R1.mag x y hx hy])
    · simp only [↓reduceIte]
      obtain ⟨e2, R2⟩ := rawBit_relM R1
      generalize JPEG2000.Tier1.rawBit mq1 = rf at e2 R2 ⊢
      generalize hrs2 : d1.rawBit = rs at e2 R2 ⊢
      obtain ⟨neg, mq2⟩ := rf
      obtain ⟨bs2, d2⟩ := rs
      have hc2 : d2.coeffs = d1.coeffs := by
        simp only [rawBit_eq, Prod.mk.injEq] at hrs2; rw [← hrs2.2]
      simp only at e2 R2 ⊢
      subst e2
      exact setSig_rel R1 hx hy (by rw [hc1]; exact hc.1) one p hone true neg mq2 d2 R2.coder hc2
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]
    exact R

/-- **`rawMrStep` simulates `rawMagRefStep`** (D.6). -/
theorem rawMrStep_rel {s : JPEG2000.Tier1.St} {d : DecState}
    (R : RelM w h b vc start true s d) {x y : Nat} (hx : x < w) (hy : y < h)
    (one : UInt32) (p : Nat) (hone : one.toNat = 2 ^ p % 2 ^ 32) :
    RelM w h b vc start true (JPEG2000.Tier1.rawMrStep one s (bidx w x y))
      (Spec.Tier1.rawMagRefStep (gV w h b vc) p d (x, y)) := by
  obtain ⟨mq, fl, mags⟩ := s
  have hs := sigTest_relM R hx hy
  have hv := visTest_relM R hx hy
  simp only at hs hv
  simp only [JPEG2000.Tier1.rawMrStep, Spec.Tier1.rawMagRefStep]
  have hne : (JPEG2000.Tier1.fget fl (bidx w x y) &&& JPEG2000.Tier1.SIG != 0) =
      !(JPEG2000.Tier1.fget fl (bidx w x y) &&& JPEG2000.Tier1.SIG == 0) := rfl
  rw [hne, hs, hv, Bool.not_not]
  by_cases hc : (((gV w h b vc).coeffAt d.coeffs x y).sig &&
      !((gV w h b vc).coeffAt d.coeffs x y).visited) = true
  · simp only [hc, ↓reduceIte]
    obtain ⟨e1, R1⟩ := rawBit_relM R
    generalize JPEG2000.Tier1.rawBit mq = rf at e1 R1 ⊢
    generalize hrs : d.rawBit = rs at e1 R1 ⊢
    obtain ⟨bf, mq'⟩ := rf
    obtain ⟨bs, d'⟩ := rs
    have hcs : d'.coeffs = d.coeffs := by
      simp only [rawBit_eq, Prod.mk.injEq] at hrs; rw [← hrs.2]
    simp only at e1 R1 ⊢
    subst e1
    have hi : bidx w x y < fl.size := by rw [R.fsize]; exact bidx_lt hx hy
    have hmi : bidx w x y < mags.size := by rw [R.msize]; exact bidx_lt hx hy
    have o := bitV_own R1 hx hy
    obtain ⟨o1, o2, o3, o4⟩ := o
    simp only at o1 o2 o3 o4
    have := rel_ownM R1 hx hy
      (JPEG2000.Tier1.fset fl (bidx w x y) (JPEG2000.Tier1.fget fl (bidx w x y) ||| JPEG2000.Tier1.REF))
      (if bf = true then JPEG2000.Tier1.fset mags (bidx w x y)
        (JPEG2000.Tier1.fget mags (bidx w x y) + one) else mags)
      (by simp) (by split <;> simp)
      (fun k hk => by rw [fget_fset _ _ _ _ hi]; simp [Ne.symm hk])
      (fun k hk => by split
                      · rw [fget_fset _ _ _ _ hmi]; simp [Ne.symm hk]
                      · rfl)
      { (gV w h b vc).coeffAt d'.coeffs x y with
          mag := ((gV w h b vc).coeffAt d'.coeffs x y).mag + (if bf = true then 2 ^ p else 0),
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

end raw

end JPEG2000.Spec.Tier1EquivM
