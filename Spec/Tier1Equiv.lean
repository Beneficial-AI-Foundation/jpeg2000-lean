import Spec.Tier1Equiv.Inv

/-!
# C3 (plain mode): the fast Tier-1 decoder equals the spec decoder

Plan.md §4 (C3: "the fast EBCOT decoder equals the spec decoder (Annex D, coefficient by
coefficient, pass by pass)"), §5.1, §5.2 "Tier-1 / EBCOT"; T.800 Annex D, E.1.1.2. Task 3.6.

`c3_plain_exact` (task 5.8 renamed it; `c3_plain` in `Spec.Tier1Equiv.Clamp` is the same
statement for the decoders that first drop passes beyond `3K − 2`): for every buffer `data`, segment bounds `start ≤ stop ≤ data.size`, block size
`w × h`, band, `Mb`, zero bit-planes and pass count `n` with `K = Mb − zeroBitPlanes ≤ 31`
whenever `n > 0`, the fast `JPEG2000.Tier1.decodeCodeBlockExact data start stop w h band Mb zbp n`
and the spec `Spec.Tier1.decodeCodeBlockExact (CodeBlock.ofData w h (orientOf band) Mb zbp n
(segment data start stop))` (plain mode, one codeword segment) either both fail with the same
error, or both succeed and agree on every coefficient `(x, y)`: the fast `Int32` value is the
spec `Coeff.value`, the fast `sig` is the spec `sig` and the fast `lsbPlane` (recomputed from
the flag words) is the spec `lsbPlane`.

The two side conditions are exactly the fast decoder's own extra checks (`validate`): it reads
its segment from a buffer (the spec takes the segment as a list) and refuses more than 31
coded bit-planes (its output is `Int32`). Under them the argument checks coincide.

Proof: `init_rel` (initial states related), `runPasses_rel` (the simulation, parts 2–3),
`decodePasses_inv` (spec invariant, part 4) and the output lemmas below (`fillRows_get`,
`val_toInt`, the `lsbPlane` recomputation).
-/

namespace JPEG2000.Spec.Tier1Equiv

open JPEG2000
open JPEG2000.Bytes (Plane)
open JPEG2000.Tier2.Geometry (Band)
open JPEG2000.Spec.Tier1 (Coeff Geom DecState CodeBlock)

/-! ## Initial states -/

/-- Every coefficient of the initial spec array is `{}` (in or out of the block). -/
theorem coeffAt_replicate (g : Geom) (X Y : Int) :
    g.coeffAt (Array.replicate (g.width * g.height) ({} : Coeff)) X Y = {} := by
  unfold Geom.coeffAt
  split
  · rw [Array.getD_eq_getD_getElem?]
    by_cases hl : g.idx X.toNat Y.toNat < (Array.replicate (g.width * g.height) ({} : Coeff)).size
    · rw [Array.getElem?_eq_getElem hl]; simp
    · rw [Array.getElem?_eq_none (Nat.le_of_not_lt hl)]; rfl
  · rfl

/-- Every word of a zero array is 0. -/
theorem fget_replicate (n k : Nat) : Tier1.fget (Array.replicate n 0) k = 0 := by
  unfold Tier1.fget; split <;> simp

/-- The initial fast state (as `decodeCodeBlockExact` builds it) is related to the spec's initial
state on the segment `data[start, stop)`. -/
theorem init_rel (data : ByteArray) (start stop w h : Nat) (b : Band) :
    Rel w h b start
      { mq := MQ.Dec.init data start stop MQ.tier1Contexts,
        flags := Array.replicate ((w + 2) * (h + 2)) 0,
        mags := Array.replicate ((w + 2) * (h + 2)) 0 }
      (DecState.init (sgeom w h b) (MQEquiv.segment data start stop)) := by
  have hcx : MQEquiv.CxRel MQ.tier1Contexts (Spec.MQ.initContexts Spec.Tier1.initialStates) := by
    rw [Spec.Tier1.initialStates_eq]
    exact MQEquiv.initContexts_rel _ (by decide)
  have hc : ∀ X Y : Int, (sgeom w h b).coeffAt
      (DecState.init (sgeom w h b) (MQEquiv.segment data start stop)).coeffs X Y = {} :=
    fun X Y => coeffAt_replicate _ X Y
  refine ⟨MQEquiv.init_sim data start stop _ _ hcx, by simp, by simp,
    by simp [DecState.init, sgeom], ?_, ?_⟩
  · intro x y j _ _ _
    simp only [fget_replicate, bt_zero, specBit, hc]
    split
    · split <;> rfl
    · repeat' split
      all_goals rfl
  · intro x y _ _
    simp only [fget_replicate, hc]
    rfl

/-! ## Output: the plane -/

/-- The output value the fast decoder writes for bordered index `i`. -/
def val (fl mags : Array UInt32) (i : Nat) : Int32 :=
  if Tier1.fget fl i &&& Tier1.NEG != 0 then -(Tier1.fget mags i).toInt32
  else (Tier1.fget mags i).toInt32

/-- Checked read after `Plane.set`. -/
theorem get?_set (p : Plane) (j t : Nat) (v : Int32) (hj : j < p.width * p.height) :
    (p.set j v hj).get? t = if j = t then some v else p.get? t := by
  unfold Plane.get?
  have hd := Plane.set_dims p j v hj
  by_cases ht : t < p.width * p.height
  · have ht' : t < (p.set j v hj).width * (p.set j v hj).height := by rw [hd.1, hd.2]; exact ht
    simp only [ht', ht, ↓reduceDIte]
    by_cases e : j = t
    · subst e; simp [Plane.get_set_self]
    · simp [e, Plane.get_set_ne _ _ _ _ _ _ e]
  · have ht' : ¬ t < (p.set j v hj).width * (p.set j v hj).height := by rw [hd.1, hd.2]; exact ht
    have : j ≠ t := by omega
    simp [ht', ht, this]

/-- `fillRow` keeps the dimensions. -/
theorem fillRow_dims (fl mags : Array UInt32) :
    ∀ k p j i, (Tier1.fillRow fl mags k p j i).width = p.width ∧
      (Tier1.fillRow fl mags k p j i).height = p.height := by
  intro k
  induction k with
  | zero => intro p j i; exact ⟨rfl, rfl⟩
  | succ k ih =>
    intro p j i
    simp only [Tier1.fillRow]
    rw [(ih _ _ _).1, (ih _ _ _).2]
    split
    · exact Plane.set_dims _ _ _ _
    · exact ⟨rfl, rfl⟩

/-- `fillRow` writes cells `j, …, j + k − 1` from bordered indices `i, …`. -/
theorem fillRow_get (fl mags : Array UInt32) :
    ∀ k p j i t, (Tier1.fillRow fl mags k p j i).get? t =
      if j ≤ t ∧ t < j + k ∧ t < p.width * p.height then some (val fl mags (i + (t - j)))
      else p.get? t := by
  intro k
  induction k with
  | zero =>
    intro p j i t
    have : ¬ (j ≤ t ∧ t < j + 0 ∧ t < p.width * p.height) := by omega
    simp only [Tier1.fillRow, this, ↓reduceIte]
  | succ k ih =>
    intro p j i t
    simp only [Tier1.fillRow]
    rw [ih]
    split
    · rename_i hj
      rw [get?_set, (Plane.set_dims _ _ _ _).1, (Plane.set_dims _ _ _ _).2]
      by_cases e : j = t
      · subst e
        have : ¬ (j + 1 ≤ j) := by omega
        simp [this, hj, val]
      · have e2 : (j + 1 ≤ t ∧ t < j + 1 + k ∧ t < p.width * p.height) ↔
            (j ≤ t ∧ t < j + (k + 1) ∧ t < p.width * p.height) := by omega
        simp only [e2, e, ↓reduceIte]
        split
        · congr 2; omega
        · rfl
    · rename_i hj
      have e2 : (j + 1 ≤ t ∧ t < j + 1 + k ∧ t < p.width * p.height) →
          (j ≤ t ∧ t < j + (k + 1) ∧ t < p.width * p.height) := by omega
      by_cases c : j ≤ t ∧ t < j + (k + 1) ∧ t < p.width * p.height
      · have : j ≠ t := by omega
        have c' : j + 1 ≤ t ∧ t < j + 1 + k ∧ t < p.width * p.height := by omega
        simp only [c, c', ↓reduceIte]
        congr 2; omega
      · have c' : ¬ (j + 1 ≤ t ∧ t < j + 1 + k ∧ t < p.width * p.height) := fun h' => c (e2 h')
        simp only [c, c', ↓reduceIte]

/-- Rows of a raster: `y'·w + x` lies in row `y` iff `y' = y` (for `x < w`). -/
theorem row_iff {w x y y' : Nat} (hx : x < w) :
    (y * w ≤ y' * w + x ∧ y' * w + x < y * w + w) ↔ y' = y := by
  constructor
  · intro ⟨h1, h2⟩
    rcases Nat.lt_trichotomy y' y with hl | he | hg
    · have : (y' + 1) * w ≤ y * w := Nat.mul_le_mul_right _ hl
      rw [Nat.succ_mul] at this; omega
    · exact he
    · have : (y + 1) * w ≤ y' * w := Nat.mul_le_mul_right _ hg
      rw [Nat.succ_mul] at this; omega
  · intro e; subst e; omega

/-- `fillRows` keeps the dimensions. -/
theorem fillRows_dims (w h : Nat) (b : Band) (fl mags : Array UInt32) :
    ∀ k p y, (Tier1.fillRows (fgeo w h b) fl mags k p y).width = p.width ∧
      (Tier1.fillRows (fgeo w h b) fl mags k p y).height = p.height := by
  intro k
  induction k with
  | zero => intro p y; exact ⟨rfl, rfl⟩
  | succ k ih =>
    intro p y
    simp only [Tier1.fillRows]
    rw [(ih _ _).1, (ih _ _).2]
    exact fillRow_dims _ _ _ _ _ _

/-- `fillRows` writes the cell of `(x, y')` from the bordered word of `(x, y')`, for the rows
`y, …, y + k − 1`. -/
theorem fillRows_get (w h : Nat) (b : Band) (fl mags : Array UInt32) (x : Nat) (hx : x < w) :
    ∀ k p y y', (Tier1.fillRows (fgeo w h b) fl mags k p y).get? (y' * w + x) =
      if y ≤ y' ∧ y' < y + k ∧ y' * w + x < p.width * p.height then
        some (val fl mags (bidx w x y'))
      else p.get? (y' * w + x) := by
  intro k
  induction k with
  | zero =>
    intro p y y'
    have : ¬ (y ≤ y' ∧ y' < y + 0 ∧ y' * w + x < p.width * p.height) := by omega
    simp only [Tier1.fillRows, this, ↓reduceIte]
  | succ k ih =>
    intro p y y'
    simp only [Tier1.fillRows]
    rw [ih, fillRow_get, (fillRow_dims _ _ _ _ _ _).1, (fillRow_dims _ _ _ _ _ _).2]
    simp only [fgeo]
    have hr := row_iff (y := y) (y' := y') hx
    by_cases e : y' = y
    · subst e
      have : ¬ (y' + 1 ≤ y') := by omega
      have c : y' * w ≤ y' * w + x ∧ y' * w + x < y' * w + w := hr.mpr rfl
      by_cases hs : y' * w + x < p.width * p.height
      · simp only [this, false_and, ↓reduceIte, c, hs, and_self, Nat.le_refl,
          show y' < y' + (k + 1) by omega]
        congr 2
        unfold bidx; omega
      · simp [hs]
    · have c : ¬ (y * w ≤ y' * w + x ∧ y' * w + x < y * w + w ∧ y' * w + x < p.width * p.height) :=
        fun h' => e (hr.mp ⟨h'.1, h'.2.1⟩)
      have e2 : (y + 1 ≤ y' ∧ y' < y + 1 + k) ↔ (y ≤ y' ∧ y' < y + (k + 1)) := by omega
      simp only [c, ↓reduceIte, ← and_assoc, e2]

/-! ## Output: values -/

/-- A `UInt32` below `2^31` read as `Int32`. -/
theorem toInt_toInt32 (u : UInt32) (hu : u.toNat < 2 ^ 31) : u.toInt32.toInt = (u.toNat : Int) := by
  show u.toBitVec.toInt = _
  rw [BitVec.toInt_eq_toNat_of_lt (by simp; omega)]
  rfl

/-- Its negation. -/
theorem toInt_neg_toInt32 (u : UInt32) (hu : u.toNat < 2 ^ 31) :
    (-u.toInt32).toInt = -(u.toNat : Int) := by
  rw [Int32.toInt_neg, toInt_toInt32 u hu, Int.bmod_def]
  split <;> omega

/-- `f &&& NEG != 0` is "significant and negative". -/
theorem negTest_rel {w h : Nat} {b : Band} {start : Nat} {s : Tier1.St} {d : DecState}
    (R : Rel w h b start s d) {x y : Nat} (hx : x < w) (hy : y < h) :
    (Tier1.fget s.flags (bidx w x y) &&& Tier1.NEG != 0) =
      (((sgeom w h b).coeffAt d.coeffs x y).sig && ((sgeom w h b).coeffAt d.coeffs x y).sign) := by
  have : (Tier1.fget s.flags (bidx w x y) &&& Tier1.NEG != 0) =
      !(Tier1.fget s.flags (bidx w x y) &&& Tier1.NEG == 0) := rfl
  rw [this, and_eq_zero_iff _ _ (by decide)]
  obtain ⟨-, o2, -, -⟩ := bit_own R hx hy
  simp only [bt] at o2
  simp [List.range, List.range.loop, Tier1.NEG, testBit_lit, bt, o2]

/-- **The output value**: under `Base` with `K ≤ 31` for significant coefficients, the fast
value is the spec `Coeff.value`. -/
theorem val_toInt {w h : Nat} {b : Band} {start : Nat} {s : Tier1.St} {d : DecState}
    (R : Rel w h b start s d) {x y : Nat} (hx : x < w) (hy : y < h) (K : Nat)
    (hb : Base K ((sgeom w h b).coeffAt d.coeffs x y))
    (hK : ((sgeom w h b).coeffAt d.coeffs x y).sig = true → K ≤ 31) :
    (val s.flags s.mags (bidx w x y)).toInt = ((sgeom w h b).coeffAt d.coeffs x y).value := by
  have hm := R.mag x y hx hy
  have hneg := negTest_rel R hx hy
  generalize (sgeom w h b).coeffAt d.coeffs x y = c at hm hneg hb hK
  have hlt : c.mag < 2 ^ 31 := by
    cases hs : c.sig
    · rw [(hb.1 hs).1]; decide
    · have := (hb.2 hs).1
      have := Nat.pow_le_pow_right (show 0 < 2 by decide) (hK hs)
      omega
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  have hu : (Tier1.fget s.mags (bidx w x y)).toNat < 2 ^ 31 := by omega
  unfold val Spec.Tier1.Coeff.value
  rw [hneg]
  cases hs : c.sig <;> cases hn : c.sign <;>
    simp [toInt_toInt32 _ hu, toInt_neg_toInt32 _ hu, hm, (hb.1 _).1, hs]
  all_goals first | rfl | (have := (hb.1 hs).1; omega)


/-! ## Argument checks -/

/-- The spec code-block of the theorem: plain mode, one codeword segment. -/
abbrev specBlock (data : ByteArray) (start stop w h : Nat) (band : Band) (Mb zbp n : Nat) :
    CodeBlock :=
  CodeBlock.ofData w h (orientOf band) Mb zbp n (MQEquiv.segment data start stop)

/-- Its pass count. -/
theorem specBlock_numPasses (data : ByteArray) (start stop w h : Nat) (band : Band)
    (Mb zbp n : Nat) : (specBlock data start stop w h band Mb zbp n).numPasses = n := by
  simp only [specBlock, CodeBlock.numPasses, CodeBlock.ofData, Spec.Tier1.Segment.single]
  split <;> simp_all

/-- **The argument checks agree** when the segment lies in the buffer and `K ≤ 31` for a
non-empty block. -/
theorem validate_eq (data : ByteArray) (start stop w h : Nat) (band : Band) (Mb zbp n : Nat)
    (hrange : start ≤ stop ∧ stop ≤ data.size) (hK : 0 < n → Mb - zbp ≤ 31) :
    JPEG2000.Tier1.validate data start stop w h (Mb - zbp) n =
      (specBlock data start stop w h band Mb zbp n).validate := by
  have hn := specBlock_numPasses data start stop w h band Mb zbp n
  have hseg : ((specBlock data start stop w h band Mb zbp n).segments.map (·.passes) !=
      Spec.Tier1.segmentPasses (specBlock data start stop w h band Mb zbp n).mode
        (specBlock data start stop w h band Mb zbp n).numPasses 0) = false := by
    rw [hn, Spec.Tier1.segmentPasses_plain _ rfl rfl]
    simp only [specBlock, CodeBlock.ofData, Spec.Tier1.Segment.single]
    split <;> simp
  rw [hn] at hseg
  unfold JPEG2000.Tier1.validate Spec.Tier1.CodeBlock.validate
  rw [hn]
  have h3 : ¬ (start > stop ∨ stop > data.size) := by omega
  have h4 : ¬ (n > 0 ∧ Mb - zbp > 31) := fun ⟨a, c⟩ => by have := hK a; omega
  simp only [hseg, h3, h4, Bool.false_eq_true, ↓reduceIte]
  by_cases c1 : w > 1024 ∨ h > 1024 ∨ w * h > 4096 <;>
    by_cases c2 : n > 0 ∧ n > 3 * (Mb - zbp) - 2 <;>
    simp [c1, c2, specBlock, CodeBlock.ofData, CodeBlock.codedPlanes, JPEG2000.Tier1.tier1Loc,
      Spec.Tier1.tier1Loc]

/-! ## The successful case -/

/-- The spec result of the plain one-segment block is `decodePasses` from the initial state on
the segment (also for `n = 0`, where both are the initial coefficients). -/
theorem specBlock_coeffs (data : ByteArray) (start stop w h : Nat) (band : Band)
    (Mb zbp n : Nat) :
    (Spec.Tier1.decodeState (specBlock data start stop w h band Mb zbp n)).coeffs =
      (Spec.Tier1.decodePasses (sgeom w h band) (Mb - zbp) n
        (DecState.init (sgeom w h band) (MQEquiv.segment data start stop))).coeffs := by
  by_cases n0 : n = 0
  · subst n0
    rfl
  · rw [Spec.Tier1.decodeState_plain _ rfl (MQEquiv.segment data start stop) n
      (by simp [specBlock, CodeBlock.ofData, Spec.Tier1.Segment.single, n0])]
    rfl

/-- **The successful case**: the fast output (as `decodeCodeBlockExact` builds it) agrees with the
spec coefficients after `decodePasses`, coefficient by coefficient. -/
theorem out_ok (data : ByteArray) (start stop w h : Nat) (band : Band) (Mb zbp n : Nat)
    (hK : 0 < n → Mb - zbp ≤ 31) (hnK : 0 < n → n ≤ 3 * (Mb - zbp) - 2) :
    let K := Mb - zbp
    let s0 : Tier1.St :=
      { mq := MQ.Dec.init data start stop MQ.tier1Contexts,
        flags := Array.replicate ((w + 2) * (h + 2)) 0,
        mags := Array.replicate ((w + 2) * (h + 2)) 0 }
    let sF := JPEG2000.Tier1.runPasses (fgeo w h band) K n s0 0
    let o : JPEG2000.Tier1.CodeBlockOut :=
      { plane := JPEG2000.Tier1.fillRows (fgeo w h band) sF.flags sF.mags h (Plane.zero w h) 0,
        flags := sF.flags, codedPlanes := K, numPasses := n }
    let cs := (Spec.Tier1.decodePasses (sgeom w h band) K n
        (DecState.init (sgeom w h band) (MQEquiv.segment data start stop))).coeffs
    cs.size = w * h ∧ o.plane.width = w ∧ o.plane.height = h ∧
      ∀ x y, x < w → y < h →
        (o.plane.get? (y * w + x)).map Int32.toInt = some (cs.getD (y * w + x) {}).value ∧
        o.sig x y = (cs.getD (y * w + x) {}).sig ∧
        o.lsbPlane x y = (cs.getD (y * w + x) {}).lsbPlane := by
  intro K s0 sF o cs
  have R0 := init_rel data start stop w h band
  have RF : Rel w h band start sF
      (Spec.Tier1.decodePasses (sgeom w h band) K n
        (DecState.init (sgeom w h band) (MQEquiv.segment data start stop))) := by
    by_cases n0 : n = 0
    · subst n0; exact R0
    · have := runPasses_rel (w := w) (h := h) (b := band) (start := start) K
        (by have := hK (by omega); omega) n s0 _ 0 R0
      unfold Spec.Tier1.decodePasses
      rw [List.range_eq_range']
      exact this
  generalize hdF : Spec.Tier1.decodePasses (sgeom w h band) K n
    (DecState.init (sgeom w h band) (MQEquiv.segment data start stop)) = dF at RF
  have hcs : cs = dF.coeffs := by simp only [cs, K, hdF]
  have hdims := fillRows_dims w h band sF.flags sF.mags h (Plane.zero w h) 0
  -- the spec invariant, per coefficient
  have hinv : ∀ x y, x < w → y < h →
      (n = 0 → (sgeom w h band).coeffAt dF.coeffs x y = {}) ∧
      (0 < n → Post K (n - 1) ((sgeom w h band).coeffAt dF.coeffs x y)) := by
    intro x y hx hy
    refine ⟨fun n0 => ?_, fun hn => ?_⟩
    · subst n0; rw [← hdF]; exact coeffAt_replicate _ _ _
    · rw [← hdF]
      exact (decodePasses_inv K _ rfl n hn (hnK hn)).2 x y hx hy
  have hbase : ∀ x y, x < w → y < h →
      Base K ((sgeom w h band).coeffAt dF.coeffs x y) ∧
      (((sgeom w h band).coeffAt dF.coeffs x y).sig = true → 0 < n) := by
    intro x y hx hy
    by_cases n0 : n = 0
    · rw [(hinv x y hx hy).1 n0]
      exact ⟨⟨fun _ => ⟨rfl, rfl⟩, fun h0 => by cases h0⟩, fun h0 => by cases h0⟩
    · have hp := (hinv x y hx hy).2 (by omega)
      refine ⟨?_, fun _ => by omega⟩
      unfold Post at hp
      split at hp
      · exact hp.1
      · exact hp.1
      · exact hp.1.1
  refine ⟨by rw [hcs]; exact RF.csize, hdims.1, hdims.2, fun x y hx hy => ?_⟩
  have hget : ∀ c : Coeff, cs.getD (y * w + x) {} = c ↔ (sgeom w h band).coeffAt dF.coeffs x y = c := by
    intro c
    rw [hcs, coeffAt_nat _ _ _ _ hx hy]; rfl
  generalize hc : (sgeom w h band).coeffAt dF.coeffs x y = c at hget
  have hcg : cs.getD (y * w + x) {} = c := (hget c).mpr rfl
  rw [hcg]
  obtain ⟨hb, hsn⟩ := hbase x y hx hy
  rw [hc] at hb hsn
  have hsig := sigTest_rel RF hx hy
  have hvis := visTest_rel RF hx hy
  rw [hc] at hsig hvis
  have hw : o.plane.width = w := hdims.1
  refine ⟨?_, ?_, ?_⟩
  · -- the value
    have hg := fillRows_get w h band sF.flags sF.mags x hx h (Plane.zero w h) 0 y
    have hlt : y * w + x < (Plane.zero w h).width * (Plane.zero w h).height := by
      have := idx_lt (sgeom w h band) hx hy
      simpa [Geom.idx, sgeom, Plane.zero] using this
    rw [ite_pos' ⟨Nat.zero_le _, by omega, hlt⟩] at hg
    show Option.map Int32.toInt
      ((JPEG2000.Tier1.fillRows (fgeo w h band) sF.flags sF.mags h (Plane.zero w h) 0).get?
        (y * w + x)) = _
    rw [hg]
    simp only [Option.map_some]
    have := val_toInt RF hx hy K (by rw [hc]; exact hb)
      (fun hs => by rw [hc] at hs; have := hsn hs; exact hK this)
    rw [this, hc]
  · -- significance
    show (Tier1.fget sF.flags ((y + 1) * (o.plane.width + 2) + x + 1) &&& Tier1.SIG != 0) = c.sig
    rw [hw]
    have e : (Tier1.fget sF.flags ((y + 1) * (w + 2) + x + 1) &&& Tier1.SIG != 0) =
        !(Tier1.fget sF.flags (bidx w x y) &&& Tier1.SIG == 0) := rfl
    rw [e, hsig, Bool.not_not]
  · -- lsbPlane
    show (let f := Tier1.fget sF.flags ((y + 1) * (o.plane.width + 2) + x + 1)
      if (f &&& Tier1.SIG == 0 || n == 0) = true then 0
      else
        if (JPEG2000.Tier1.passKind (n - 1) == 0 && f &&& Tier1.VIS == 0) = true then
          JPEG2000.Tier1.passPlane K (n - 1) + 1
        else JPEG2000.Tier1.passPlane K (n - 1)) = c.lsbPlane
    rw [hw]
    have e : Tier1.fget sF.flags ((y + 1) * (w + 2) + x + 1) = Tier1.fget sF.flags (bidx w x y) := rfl
    simp only [e, hsig, hvis]
    cases hs : c.sig
    · simp [(hb.1 hs).2]
    · have hn := hsn hs
      have hn' : (n == 0) = false := by simp; omega
      simp only [hn', Bool.not_true, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
      have hp := (hinv x y hx hy).2 hn
      rw [hc] at hp
      have epp : JPEG2000.Tier1.passPlane K (n - 1) = Spec.Tier1.passPlane K (n - 1) := rfl
      rw [epp]
      unfold Post at hp
      rcases passKind_cases (n - 1) with ⟨k1, k2⟩ | ⟨k1, k2⟩ | ⟨k1, k2⟩ <;>
        simp only [k2] at hp <;> simp only [k1]
      · cases hv : c.visited
        · simp [hp.2.2 hs hv]
        · simp [hp.2.1 hs hv]
      · simp [hp.2 hs]
      · simp [hp.1.2 hs]

/-! ## The theorem -/

/-- **C3 for plain mode** (Plan.md §4): the fast Tier-1 decoder equals the Annex D reference
decoder on every plain-mode code-block with one codeword segment `data[start, stop)` — both
fail with the same error, or both succeed and agree, coefficient by coefficient, on the value,
the significance and `lsbPlane` (the decoded bit count `Nb = Mb − lsbPlane` of E.1.1.2).
Side conditions: the segment lies in the buffer and at most 31 bit-planes are coded when a
pass is decoded (the fast decoder's two extra checks). -/
theorem c3_plain_exact (data : ByteArray) (start stop w h : Nat) (band : Band) (Mb zbp n : Nat)
    (hrange : start ≤ stop ∧ stop ≤ data.size) (hK : 0 < n → Mb - zbp ≤ 31) :
    match JPEG2000.Tier1.decodeCodeBlockExact data start stop w h band Mb zbp n,
      Spec.Tier1.decodeCodeBlockExact (specBlock data start stop w h band Mb zbp n) with
    | .error e1, .error e2 => e1 = e2
    | .ok o, .ok cs =>
      cs.size = w * h ∧ o.plane.width = w ∧ o.plane.height = h ∧
      ∀ x y, x < w → y < h →
        (o.plane.get? (y * w + x)).map Int32.toInt = some (cs.getD (y * w + x) {}).value ∧
        o.sig x y = (cs.getD (y * w + x) {}).sig ∧
        o.lsbPlane x y = (cs.getD (y * w + x) {}).lsbPlane
    | _, _ => False := by
  have hv := validate_eq data start stop w h band Mb zbp n hrange hK
  unfold JPEG2000.Tier1.decodeCodeBlockExact Spec.Tier1.decodeCodeBlockExact
  dsimp only
  rw [hv]
  cases hval : (specBlock data start stop w h band Mb zbp n).validate with
  | error e => simp [bind, Except.bind]
  | ok u =>
    simp only [bind, Except.bind, pure, Except.pure]
    have hnK : 0 < n → n ≤ 3 * (Mb - zbp) - 2 := by
      intro hn
      apply Classical.byContradiction
      intro hc
      rw [← hv] at hval
      unfold JPEG2000.Tier1.validate at hval
      have c2 : n > 0 ∧ n > 3 * (Mb - zbp) - 2 := ⟨hn, by omega⟩
      by_cases c1 : w > 1024 ∨ h > 1024 ∨ w * h > 4096 <;>
        simp [c1, c2, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hval
    rw [specBlock_coeffs]
    exact out_ok data start stop w h band Mb zbp n hK hnK

end JPEG2000.Spec.Tier1Equiv
