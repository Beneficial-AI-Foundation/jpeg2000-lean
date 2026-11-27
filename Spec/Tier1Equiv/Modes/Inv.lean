import Spec.Tier1Equiv.Modes.Segs

/-!
# C3 (all code-block styles), part 6: the spec invariant in every style

Plan.md §4 (C3), §5.2 "Tier-1 / EBCOT"; T.800 D.2, D.3, D.5–D.7, E.1.1.2 (`Nb(u, v)`).
Task 7.1c.

The invariant of the reference decoder used to read the fast decoder's output (task 3.6,
`Spec.Tier1Equiv.Base`/`Post`: magnitudes below `2^K`, `lsbPlane` determined by the last pass
and the `visited` mark), now for the geometry `gV w h b vc` (vertically causal formation
changes contexts only, never which coefficients a pass writes) and for the mode-aware pass
`Spec.Tier1.runPassM`: raw passes write exactly what the MQ passes write (`rawSigPropStep_invV`,
`rawMagRefPass_invV`), and segmentation symbols, context resets and segment starts do not
touch the coefficients. Main result: `decodeSegments_inv`. The plain-mode lemmas are
transcribed with the geometry generalised (suffix `V`).
-/

namespace JPEG2000.Spec.Tier1EquivM

open JPEG2000
open JPEG2000.Tier2.Geometry (Band)
open JPEG2000.Spec.Tier1 (Coeff Geom DecState RawState Mode)
open JPEG2000.Spec.Tier1Equiv

/-- A predicate holds for every in-block coefficient (geometry `gV`), and the array has
`w · h` entries. -/
def AllPV (w h : Nat) (b : Band) (vc : Bool) (P : Coeff → Prop) (cs : Array Coeff) : Prop :=
  cs.size = w * h ∧ ∀ x y, x < w → y < h → P ((gV w h b vc).coeffAt cs x y)

/-! ## Setting one coefficient -/

section set
variable {w h : Nat} {b : Band} {vc : Bool}

/-- Writing a coefficient satisfying `P` keeps `AllP P`. -/
theorem allP_setV {P : Coeff → Prop} {cs : Array Coeff} (H : AllPV w h b vc P cs) {x y : Nat}
    (hx : x < w) (hy : y < h) (c' : Coeff) (hc : P c') :
    AllPV w h b vc P ((gV w h b vc).setCoeff cs x y c') := by
  refine ⟨by simp [H.1], fun x' y' hx' hy' => ?_⟩
  rw [coeffAt_setCoeff _ _ H.1 _ _ hx hy]
  split
  · exact hc
  · exact H.2 x' y' hx' hy'

/-- What `becomeSignificant` writes. -/
theorem becomeSignificant_coeffsV (p : Nat) (vis : Bool) (d : DecState) (x y : Nat) :
    ∃ neg, (Spec.Tier1.becomeSignificant (gV w h b vc) p vis d x y).coeffs =
      (gV w h b vc).setCoeff d.coeffs x y (sigC ((gV w h b vc).coeffAt d.coeffs x y) neg p vis) := by
  simp only [Spec.Tier1.becomeSignificant, Spec.Tier1.decodeSign]
  generalize (gV w h b vc).signContext d.coeffs x y = sc
  obtain ⟨cx, xb⟩ := sc
  obtain ⟨bb, d', e, hc⟩ := decodeBit_split d cx
  simp only [e, hc]
  exact ⟨_, rfl⟩

/-- `becomeSignificant` at an insignificant coefficient of an array satisfying `Base`. -/
theorem becomeSignificant_baseV {K q : Nat} (hq : q < K) {P : Coeff → Prop} (vis : Bool)
    (hP : ∀ c : Coeff, Base K c → c.sig = true → c.lsbPlane = q → c.visited = vis → P c) {d : DecState} (H : AllPV w h b vc P d.coeffs) {x y : Nat} (hx : x < w)
    (hy : y < h) (hb : Base K ((gV w h b vc).coeffAt d.coeffs x y))
    (hs : ((gV w h b vc).coeffAt d.coeffs x y).sig = false) :
    AllPV w h b vc P (Spec.Tier1.becomeSignificant (gV w h b vc) q vis d x y).coeffs := by
  obtain ⟨neg, e⟩ := becomeSignificant_coeffsV (w := w) (h := h) (b := b) (vc := vc) q vis d x y
  rw [e]
  apply allP_setV H hx hy
  apply hP _ _ rfl rfl rfl
  have hm := (hb.1 hs).1
  refine ⟨fun h0 => by simp [sigC] at h0, fun _ => ⟨?_, ?_⟩⟩
  · simp only [sigC, hm, Nat.zero_add]; exact Nat.pow_lt_pow_right (by decide) hq
  · simp [sigC, hm]

/-- What `zeroCode` writes: the coefficient visited (`vis`), or significant. -/
theorem zeroCode_casesV (p : Nat) (vis : Bool) (d : DecState) (x y : Nat) :
    (Spec.Tier1.zeroCode (gV w h b vc) p vis d x y).coeffs =
      (gV w h b vc).setCoeff d.coeffs x y (visC ((gV w h b vc).coeffAt d.coeffs x y) vis) ∨
    ∃ d' : DecState, d'.coeffs = d.coeffs ∧
      Spec.Tier1.zeroCode (gV w h b vc) p vis d x y =
        Spec.Tier1.becomeSignificant (gV w h b vc) p vis d' x y := by
  simp only [Spec.Tier1.zeroCode]
  obtain ⟨bb, d', e, hc⟩ := decodeBit_split d ((gV w h b vc).zcCtx d.coeffs x y)
  simp only [e]
  cases bb
  · left; simp [hc, visC]
  · right; exact ⟨d', hc, rfl⟩

end set

/-! ## The three passes -/

section passes
variable {w h : Nat} {b : Band} {vc : Bool}

/-- One significance propagation step keeps `ISP`. -/
theorem sigPropStep_invV {K q : Nat} (hq : q < K) (d : DecState) (H : AllPV w h b vc (ISP K q) d.coeffs)
    (pos : Nat × Nat) (hpos : pos.1 < w ∧ pos.2 < h) :
    AllPV w h b vc (ISP K q) (Spec.Tier1.sigPropStep (gV w h b vc) q d pos).coeffs := by
  obtain ⟨x, y⟩ := pos
  obtain ⟨hx, hy⟩ := hpos
  simp only [Spec.Tier1.sigPropStep]
  split
  · rename_i hc
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
    have hI := H.2 x y hx hy
    rcases zeroCode_casesV (w := w) (h := h) (b := b) (vc := vc) q true d x y with e | ⟨d', hd', e⟩
    · rw [e]
      apply allP_setV H hx hy
      refine ⟨⟨fun h0 => hI.1.1 (by simpa [visC] using h0), fun h1 => by simp [visC, hc.1] at h1⟩,
        fun h1 => by simp [visC, hc.1] at h1, fun h1 => by simp [visC, hc.1] at h1⟩
    · rw [e]
      rw [← hd'] at H hI hc
      exact becomeSignificant_baseV hq true (fun c hb _ hl hv => ⟨hb, fun _ _ => hl,
        fun _ hv' => by rw [hv] at hv'; cases hv'⟩) H hx hy hI.1 hc.1
  · exact H

/-- Order-free fold: a step that keeps `AllP P` at every position of the list keeps it over
the fold. -/
theorem foldl_allPV {α : Type} (P : Coeff → Prop) (step : DecState → α → DecState) :
    ∀ (l : List α) (d : DecState), (∀ d' a, a ∈ l → AllPV w h b vc P d'.coeffs →
      AllPV w h b vc P (step d' a).coeffs) → AllPV w h b vc P d.coeffs →
      AllPV w h b vc P (l.foldl step d).coeffs := by
  intro l
  induction l with
  | nil => intro d _ H; exact H
  | cons a l ih =>
    intro d hs H
    simp only [List.foldl_cons]
    exact ih _ (fun d' a' ha' => hs d' a' (by simp [ha'])) (hs d a (by simp) H)

/-- **Significance propagation pass** (D.3.1) keeps `ISP q`. -/
theorem sigPropPass_invV {K q : Nat} (hq : q < K) (d : DecState) (H : AllPV w h b vc (ISP K q) d.coeffs) :
    AllPV w h b vc (ISP K q) (Spec.Tier1.sigPropPass (gV w h b vc) q d).coeffs := by
  unfold Spec.Tier1.sigPropPass
  apply foldl_allPV _ _ _ _ _ H
  intro d' a ha H'
  exact sigPropStep_invV hq d' H' a (Spec.Tier1.mem_scanOrder ha)

/-- Ordered fold: along a list without repetition, each position is changed exactly once, by a
step that only changes that position and takes `Q1` to `Q2` there. -/
theorem foldl_orderedV (Q1 Q2 : Coeff → Prop) (step : DecState → Nat × Nat → DecState)
    (hloc : ∀ (d : DecState) (x y : Nat), x < w → y < h → d.coeffs.size = w * h →
      (step d (x, y)).coeffs.size = w * h ∧ ∀ X Y : Nat, X < w → Y < h → (X, Y) ≠ (x, y) →
        (gV w h b vc).coeffAt (step d (x, y)).coeffs X Y = (gV w h b vc).coeffAt d.coeffs X Y)
    (htr : ∀ (d : DecState) (x y : Nat), x < w → y < h → d.coeffs.size = w * h →
      Q1 ((gV w h b vc).coeffAt d.coeffs x y) →
      Q2 ((gV w h b vc).coeffAt (step d (x, y)).coeffs x y)) :
    ∀ (l : List (Nat × Nat)) (d : DecState), l.Nodup → (∀ p ∈ l, p.1 < w ∧ p.2 < h) →
      d.coeffs.size = w * h → (∀ p ∈ l, Q1 ((gV w h b vc).coeffAt d.coeffs p.1 p.2)) →
      (l.foldl step d).coeffs.size = w * h ∧
      (∀ p ∈ l, Q2 ((gV w h b vc).coeffAt (l.foldl step d).coeffs p.1 p.2)) ∧
      (∀ X Y : Nat, X < w → Y < h → (X, Y) ∉ l →
        (gV w h b vc).coeffAt (l.foldl step d).coeffs X Y = (gV w h b vc).coeffAt d.coeffs X Y) := by
  intro l
  induction l with
  | nil => intro d _ _ hs _; exact ⟨hs, by simp, fun _ _ _ _ _ => rfl⟩
  | cons a l ih =>
    intro d hnd hin hs hq
    obtain ⟨x, y⟩ := a
    rw [List.nodup_cons] at hnd
    obtain ⟨hx, hy⟩ := hin (x, y) (by simp)
    obtain ⟨hs1, hl1⟩ := hloc d x y hx hy hs
    have hq' : ∀ p ∈ l, Q1 ((gV w h b vc).coeffAt (step d (x, y)).coeffs p.1 p.2) := by
      intro p hp
      have hne : (p.1, p.2) ≠ (x, y) := fun e => hnd.1 (by rw [← e]; exact hp)
      obtain ⟨hpx, hpy⟩ := hin p (by simp [hp])
      rw [hl1 p.1 p.2 hpx hpy hne]
      exact hq p (by simp [hp])
    obtain ⟨r1, r2, r3⟩ := ih (step d (x, y)) hnd.2 (fun p hp => hin p (by simp [hp])) hs1 hq'
    simp only [List.foldl_cons]
    refine ⟨r1, ?_, ?_⟩
    · intro p hp
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · rw [r3 x y hx hy hnd.1]
        exact htr d x y hx hy hs (hq (x, y) (by simp))
      · exact r2 p hp
    · intro X Y hX hY hn
      simp only [List.mem_cons, not_or] at hn
      rw [r3 X Y hX hY hn.2, hl1 X Y hX hY hn.1]

/-- **Magnitude refinement pass** (D.3.3): from `ISP q` to `IMR q`. -/
theorem magRefPass_invV {K q : Nat} (hq : q < K) (d : DecState) (H : AllPV w h b vc (ISP K q) d.coeffs) :
    AllPV w h b vc (IMR K q) (Spec.Tier1.magRefPass (gV w h b vc) q d).coeffs := by
  unfold Spec.Tier1.magRefPass
  have hloc : ∀ (d : DecState) (x y : Nat), x < w → y < h → d.coeffs.size = w * h →
      (Spec.Tier1.magRefStep (gV w h b vc) q d (x, y)).coeffs.size = w * h ∧
      ∀ X Y : Nat, X < w → Y < h → (X, Y) ≠ (x, y) →
        (gV w h b vc).coeffAt (Spec.Tier1.magRefStep (gV w h b vc) q d (x, y)).coeffs X Y =
          (gV w h b vc).coeffAt d.coeffs X Y := by
    intro d x y hx hy hs
    simp only [Spec.Tier1.magRefStep]
    split
    · obtain ⟨bb, d', e, hc⟩ := decodeBit_split d ((gV w h b vc).mrCtx d.coeffs x y)
      simp only [e, hc]
      refine ⟨by simp [hs], fun X Y hX hY hne => ?_⟩
      rw [coeffAt_setCoeff _ _ hs _ _ hx hy]
      have : ¬ ((X : Int) = x ∧ (Y : Int) = y) := by
        intro ⟨a, c⟩; apply hne; simp only [Prod.mk.injEq]; omega
      simp [this]
    · exact ⟨hs, fun _ _ _ _ _ => rfl⟩
  have htr : ∀ (d : DecState) (x y : Nat), x < w → y < h → d.coeffs.size = w * h →
      ISP K q ((gV w h b vc).coeffAt d.coeffs x y) →
      IMR K q ((gV w h b vc).coeffAt (Spec.Tier1.magRefStep (gV w h b vc) q d (x, y)).coeffs x y) := by
    intro d x y hx hy hs hI
    simp only [Spec.Tier1.magRefStep]
    split
    · rename_i hc
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
      obtain ⟨bb, d', e, hc'⟩ := decodeBit_split d ((gV w h b vc).mrCtx d.coeffs x y)
      simp only [e, hc']
      rw [coeffAt_setCoeff _ _ hs _ _ hx hy]
      simp only [and_self, ↓reduceIte]
      have hl := hI.2.2 hc.1 hc.2
      have hb := (hI.1.2 hc.1)
      rw [hl] at hb
      refine ⟨⟨fun h0 => by simp [hc.1] at h0, fun _ => ⟨?_, ?_⟩⟩, fun _ => rfl⟩
      · have := add_pow_lt _ _ _ hq hb.1 hb.2
        cases bb <;> simp <;> omega
      · have h1 : ((gV w h b vc).coeffAt d.coeffs x y).mag % 2 ^ q = 0 := by
          have : 2 ^ q ∣ 2 ^ (q + 1) := Nat.pow_dvd_pow 2 (by omega)
          rw [← Nat.mod_mod_of_dvd _ this, hb.2]; rfl
        cases bb <;> simp [h1]
    · rename_i hc
      refine ⟨hI.1, fun hs1 => ?_⟩
      have hv : ((gV w h b vc).coeffAt d.coeffs x y).visited = true := by
        cases hv : ((gV w h b vc).coeffAt d.coeffs x y).visited <;> simp_all
      exact hI.2.1 hs1 hv
  obtain ⟨r1, r2, _⟩ := foldl_orderedV (w := w) (h := h) (b := b) (vc := vc) (ISP K q) (IMR K q)
    (Spec.Tier1.magRefStep (gV w h b vc) q) hloc htr (Spec.Tier1.scanOrder w h) d
    (scanOrder_nodup w h) (fun p hp => Spec.Tier1.mem_scanOrder hp) H.1
    (fun p _ => H.2 p.1 p.2 (Spec.Tier1.mem_scanOrder (by simpa using ‹p ∈ _›)).1
      (Spec.Tier1.mem_scanOrder (by simpa using ‹p ∈ _›)).2)
  exact ⟨r1, fun x y hx hy => r2 (x, y) (mem_scanOrder_iff.mpr ⟨hx, hy⟩)⟩

/-- One normal cleanup step keeps `IMR q`. -/
theorem cleanupStep_invV {K q : Nat} (hq : q < K) (d : DecState) (H : AllPV w h b vc (IMR K q) d.coeffs)
    (pos : Nat × Nat) (hpos : pos.1 < w ∧ pos.2 < h) :
    AllPV w h b vc (IMR K q) (Spec.Tier1.cleanupStep (gV w h b vc) q d pos).coeffs := by
  obtain ⟨x, y⟩ := pos
  obtain ⟨hx, hy⟩ := hpos
  simp only [Spec.Tier1.cleanupStep]
  split
  · rename_i hc
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
    have hI := H.2 x y hx hy
    rcases zeroCode_casesV (w := w) (h := h) (b := b) (vc := vc) q false d x y with e | ⟨d', hd', e⟩
    · rw [e]
      apply allP_setV H hx hy
      refine ⟨⟨fun h0 => hI.1.1 (by simpa [visC] using h0), fun h1 => by simp [visC, hc.1] at h1⟩,
        fun h1 => by simp [visC, hc.1] at h1⟩
    · rw [e]
      rw [← hd'] at H hI hc
      exact becomeSignificant_baseV hq false (fun c hb _ hl _ => ⟨hb, fun _ => hl⟩) H hx hy
        hI.1 hc.1
  · exact H

/-- The cleanup pass on one stripe column (D.3.4, run-length mode included) keeps `IMR q`. -/
theorem cleanupColumn_invV {K q : Nat} (hq : q < K) (d : DecState)
    (H : AllPV w h b vc (IMR K q) d.coeffs) (col : List (Nat × Nat))
    (hcol : ∀ p ∈ col, p.1 < w ∧ p.2 < h) :
    AllPV w h b vc (IMR K q) (Spec.Tier1.cleanupColumn (gV w h b vc) q d col).coeffs := by
  have fold : ∀ (l : List (Nat × Nat)) (d : DecState), (∀ p ∈ l, p.1 < w ∧ p.2 < h) →
      AllPV w h b vc (IMR K q) d.coeffs →
      AllPV w h b vc (IMR K q) (l.foldl (Spec.Tier1.cleanupStep (gV w h b vc) q) d).coeffs :=
    fun l d hl H => foldl_allPV _ _ l d (fun d' a ha H' => cleanupStep_invV hq d' H' a (hl a ha)) H
  unfold Spec.Tier1.cleanupColumn
  split
  · rename_i hrl
    obtain ⟨b1, d1, e1, c1⟩ := decodeBit_split d Spec.Tier1.ctxRunLength
    simp only [e1]
    cases b1
    · simp only [Bool.not_false, ↓reduceIte]; rw [c1]; exact H
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨b2, d2, e2, c2⟩ := decodeBit_split d1 Spec.Tier1.ctxUniform
      simp only [e2]
      obtain ⟨b3, d3, e3, c3⟩ := decodeBit_split d2 Spec.Tier1.ctxUniform
      simp only [e3]
      have hc3 : d3.coeffs = d.coeffs := by rw [c3, c2, c1]
      split
      · rw [hc3]; exact H
      · rename_i x y rest heq
        have hmem : (x, y) ∈ col := List.mem_of_mem_drop (by rw [heq]; simp)
        have hrest : ∀ p ∈ rest, p.1 < w ∧ p.2 < h :=
          fun p hp => hcol p (List.mem_of_mem_drop (by rw [heq]; simp [hp]))
        obtain ⟨hx, hy⟩ := hcol _ hmem
        apply fold rest _ hrest
        have hall := hrl
        simp only [Spec.Tier1.runLengthColumn, Bool.and_eq_true, List.all_eq_true] at hall
        have hxy := hall.2 (x, y) hmem
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hxy
        rw [← hc3] at H hxy
        exact becomeSignificant_baseV hq false (fun c hb _ hl _ => ⟨hb, fun _ => hl⟩) H hx hy
          (H.2 x y hx hy).1 hxy.1.1
  · exact fold col d hcol H

/-- **Cleanup pass** (D.3.4): from `IMR q` to `IMR q` with nothing visited. -/
theorem cleanupPass_invV {K q : Nat} (hq : q < K) (d : DecState) (H : AllPV w h b vc (IMR K q) d.coeffs) :
    AllPV w h b vc (fun c => IMR K q c ∧ c.visited = false)
      (Spec.Tier1.cleanupPass (gV w h b vc) q d).coeffs := by
  unfold Spec.Tier1.cleanupPass
  have H' := foldl_allPV (w := w) (h := h) (b := b) (vc := vc) (IMR K q) (Spec.Tier1.cleanupColumn (gV w h b vc) q)
    (Spec.Tier1.stripeColumns w h) d
    (fun d' col hc H' => cleanupColumn_invV hq d' H' col (mem_stripeColumns hc)) H
  rw [show (gV w h b vc).width = w from rfl, show (gV w h b vc).height = h from rfl]
  generalize (Spec.Tier1.stripeColumns w h).foldl (Spec.Tier1.cleanupColumn (gV w h b vc) q) d = d' at H'
  refine ⟨by simp [Spec.Tier1.clearVisited, H'.1], fun x y hx hy => ?_⟩
  simp only
  rw [show Spec.Tier1.clearVisited d'.coeffs = d'.coeffs.map fun c => { c with visited := false }
    from rfl, coeffAt_map _ _ _ rfl]
  have := H'.2 x y hx hy
  exact ⟨⟨this.1, this.2⟩, rfl⟩

/-- **One pass keeps the invariant**: before pass `i` the invariant after pass `i − 1` holds (for
`i = 0`: every significant coefficient has `lsbPlane = K − 1`, vacuous on the initial state);
after it, `Post K i`. Requires `i < 3K − 2`. -/
theorem runPass_invV (K i : Nat) (hi : i < 3 * K - 2) (d : DecState)
    (H : AllPV w h b vc (if i = 0 then IMR K (K - 1) else Post K (i - 1)) d.coeffs) :
    AllPV w h b vc (Post K i) (Spec.Tier1.runPass (gV w h b vc) K d i).coeffs := by
  unfold Spec.Tier1.runPass
  by_cases i0 : i = 0
  · subst i0
    simp only [↓reduceIte] at H
    have hk : Spec.Tier1.passKind 0 = .cleanup := rfl
    have hp : Spec.Tier1.passPlane K 0 = K - 1 := by simp [Spec.Tier1.passPlane]
    simp only [hk, hp]
    unfold Post; simp only [hk, hp]
    exact cleanupPass_invV (by omega) d H
  · simp only [i0, ↓reduceIte] at H
    obtain ⟨j, hj⟩ : ∃ j, i = 3 * j + 1 ∨ i = 3 * j + 2 ∨ i = 3 * j + 3 :=
      ⟨(i - 1) / 3, by omega⟩
    obtain ⟨k1, k2, k3⟩ := Spec.Tier1.passKind_cycle j
    obtain ⟨p1, p2, p3⟩ := Spec.Tier1.passPlane_group K j
    rcases hj with rfl | rfl | rfl
    · -- significance propagation after a cleanup
      have hk0 := passKind_mul3 j
      have hp0 : Spec.Tier1.passPlane K (3 * j) = K - 1 - j := by
        simp only [Spec.Tier1.passPlane]; omega
      simp only [Nat.add_sub_cancel] at H
      unfold Post at H ⊢
      simp only [hk0, hp0] at H
      simp only [k1, p1]
      apply sigPropPass_invV (by omega)
      refine ⟨H.1, fun x y hx hy => ?_⟩
      obtain ⟨⟨hb, hl⟩, hv⟩ := H.2 x y hx hy
      refine ⟨hb, ?_, ?_⟩
      · intro _ hv'; rw [hv] at hv'; cases hv'
      · intro hs _; rw [hl hs]; omega
    · simp only [show 3 * j + 2 - 1 = 3 * j + 1 by omega] at H
      unfold Post at H ⊢
      simp only [k1, p1] at H
      simp only [k2, p2]
      rw [← p1] at H ⊢
      exact magRefPass_invV (by simp only [Spec.Tier1.passPlane]; omega) d H
    · simp only [show 3 * j + 3 - 1 = 3 * j + 2 by omega] at H
      unfold Post at H ⊢
      simp only [k2, p2] at H
      simp only [k3, p3]
      exact cleanupPass_invV (by omega) d H

/-! ## Raw passes -/

/-- A raw bit splits into a bit and a state with the same coefficients. -/
theorem rawBit_split (d : DecState) :
    ∃ bb d', d.rawBit = (bb, d') ∧ d'.coeffs = d.coeffs :=
  ⟨(Spec.Tier1.rawBit d.raw).1, { d with raw := (Spec.Tier1.rawBit d.raw).2 }, rawBit_eq d, rfl⟩

/-- One raw significance propagation step keeps `ISP` (as `sigPropStep_invV`). -/
theorem rawSigPropStep_invV {K q : Nat} (hq : q < K) (d : DecState)
    (H : AllPV w h b vc (ISP K q) d.coeffs) (pos : Nat × Nat) (hpos : pos.1 < w ∧ pos.2 < h) :
    AllPV w h b vc (ISP K q) (Spec.Tier1.rawSigPropStep (gV w h b vc) q d pos).coeffs := by
  obtain ⟨x, y⟩ := pos
  obtain ⟨hx, hy⟩ := hpos
  simp only [Spec.Tier1.rawSigPropStep]
  split
  · rename_i hc
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
    have hI := H.2 x y hx hy
    obtain ⟨bb, d1, e1, c1⟩ := rawBit_split d
    simp only [e1]
    cases bb
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [c1]
      apply allP_setV H hx hy
      refine ⟨⟨fun h0 => hI.1.1 (by simpa using h0), fun h1 => by simp [hc.1] at h1⟩,
        fun h1 => by simp [hc.1] at h1, fun h1 => by simp [hc.1] at h1⟩
    · simp only [↓reduceIte]
      obtain ⟨neg, d2, e2, c2⟩ := rawBit_split d1
      simp only [e2]
      rw [c2, c1]
      apply allP_setV H hx hy
      have hm := (hI.1.1 hc.1).1
      refine ⟨⟨fun h0 => by simp at h0, fun _ => ⟨?_, ?_⟩⟩, fun _ _ => rfl,
        fun _ hv => by simp at hv⟩
      · simp only [hm, Nat.zero_add]; exact Nat.pow_lt_pow_right (by decide) hq
      · simp [hm]
  · exact H

/-- **Raw significance propagation pass** (D.6) keeps `ISP q`. -/
theorem rawSigPropPass_invV {K q : Nat} (hq : q < K) (d : DecState)
    (H : AllPV w h b vc (ISP K q) d.coeffs) :
    AllPV w h b vc (ISP K q) (Spec.Tier1.rawSigPropPass (gV w h b vc) q d).coeffs := by
  unfold Spec.Tier1.rawSigPropPass
  apply foldl_allPV _ _ _ _ _ H
  intro d' a ha H'
  exact rawSigPropStep_invV hq d' H' a (Spec.Tier1.mem_scanOrder ha)

/-- **Raw magnitude refinement pass** (D.6): from `ISP q` to `IMR q`. -/
theorem rawMagRefPass_invV {K q : Nat} (hq : q < K) (d : DecState)
    (H : AllPV w h b vc (ISP K q) d.coeffs) :
    AllPV w h b vc (IMR K q) (Spec.Tier1.rawMagRefPass (gV w h b vc) q d).coeffs := by
  unfold Spec.Tier1.rawMagRefPass
  have hloc : ∀ (d : DecState) (x y : Nat), x < w → y < h → d.coeffs.size = w * h →
      (Spec.Tier1.rawMagRefStep (gV w h b vc) q d (x, y)).coeffs.size = w * h ∧
      ∀ X Y : Nat, X < w → Y < h → (X, Y) ≠ (x, y) →
        (gV w h b vc).coeffAt (Spec.Tier1.rawMagRefStep (gV w h b vc) q d (x, y)).coeffs X Y =
          (gV w h b vc).coeffAt d.coeffs X Y := by
    intro d x y hx hy hs
    simp only [Spec.Tier1.rawMagRefStep]
    split
    · obtain ⟨bb, d', e, hc⟩ := rawBit_split d
      simp only [e, hc]
      refine ⟨by simp [hs], fun X Y hX hY hne => ?_⟩
      rw [coeffAt_setCoeff _ _ hs _ _ hx hy]
      have : ¬ ((X : Int) = x ∧ (Y : Int) = y) := by
        intro ⟨a, c⟩; apply hne; simp only [Prod.mk.injEq]; omega
      simp [this]
    · exact ⟨hs, fun _ _ _ _ _ => rfl⟩
  have htr : ∀ (d : DecState) (x y : Nat), x < w → y < h → d.coeffs.size = w * h →
      ISP K q ((gV w h b vc).coeffAt d.coeffs x y) →
      IMR K q ((gV w h b vc).coeffAt (Spec.Tier1.rawMagRefStep (gV w h b vc) q d (x, y)).coeffs x y) := by
    intro d x y hx hy hs hI
    simp only [Spec.Tier1.rawMagRefStep]
    split
    · rename_i hc
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
      obtain ⟨bb, d', e, hc'⟩ := rawBit_split d
      simp only [e, hc']
      rw [coeffAt_setCoeff _ _ hs _ _ hx hy]
      simp only [and_self, ↓reduceIte]
      have hl := hI.2.2 hc.1 hc.2
      have hb := (hI.1.2 hc.1)
      rw [hl] at hb
      refine ⟨⟨fun h0 => by simp [hc.1] at h0, fun _ => ⟨?_, ?_⟩⟩, fun _ => rfl⟩
      · have := add_pow_lt _ _ _ hq hb.1 hb.2
        cases bb <;> simp <;> omega
      · have h1 : ((gV w h b vc).coeffAt d.coeffs x y).mag % 2 ^ q = 0 := by
          have : 2 ^ q ∣ 2 ^ (q + 1) := Nat.pow_dvd_pow 2 (by omega)
          rw [← Nat.mod_mod_of_dvd _ this, hb.2]; rfl
        cases bb <;> simp [h1]
    · rename_i hc
      refine ⟨hI.1, fun hs1 => ?_⟩
      have hv : ((gV w h b vc).coeffAt d.coeffs x y).visited = true := by
        cases hv : ((gV w h b vc).coeffAt d.coeffs x y).visited <;> simp_all
      exact hI.2.1 hs1 hv
  obtain ⟨r1, r2, _⟩ := foldl_orderedV (w := w) (h := h) (b := b) (vc := vc) (ISP K q) (IMR K q)
    (Spec.Tier1.rawMagRefStep (gV w h b vc) q) hloc htr (Spec.Tier1.scanOrder w h) d
    (scanOrder_nodup w h) (fun p hp => Spec.Tier1.mem_scanOrder hp) H.1
    (fun p _ => H.2 p.1 p.2 (Spec.Tier1.mem_scanOrder (by simpa using ‹p ∈ _›)).1
      (Spec.Tier1.mem_scanOrder (by simpa using ‹p ∈ _›)).2)
  exact ⟨r1, fun x y hx hy => r2 (x, y) (mem_scanOrder_iff.mpr ⟨hx, hy⟩)⟩

/-- **One raw pass keeps the invariant** (as `runPass_invV`). -/
theorem runRawPass_invV (K i : Nat) (hi : i < 3 * K - 2) (d : DecState)
    (H : AllPV w h b vc (if i = 0 then IMR K (K - 1) else Post K (i - 1)) d.coeffs) :
    AllPV w h b vc (Post K i) (Spec.Tier1.runRawPass (gV w h b vc) K d i).coeffs := by
  unfold Spec.Tier1.runRawPass
  by_cases i0 : i = 0
  · subst i0
    simp only [↓reduceIte] at H
    have hk : Spec.Tier1.passKind 0 = .cleanup := rfl
    have hp : Spec.Tier1.passPlane K 0 = K - 1 := by simp [Spec.Tier1.passPlane]
    simp only [hk, hp]
    unfold Post; simp only [hk, hp]
    exact cleanupPass_invV (by omega) d H
  · simp only [i0, ↓reduceIte] at H
    obtain ⟨j, hj⟩ : ∃ j, i = 3 * j + 1 ∨ i = 3 * j + 2 ∨ i = 3 * j + 3 :=
      ⟨(i - 1) / 3, by omega⟩
    obtain ⟨k1, k2, k3⟩ := Spec.Tier1.passKind_cycle j
    obtain ⟨p1, p2, p3⟩ := Spec.Tier1.passPlane_group K j
    rcases hj with rfl | rfl | rfl
    · have hk0 := passKind_mul3 j
      have hp0 : Spec.Tier1.passPlane K (3 * j) = K - 1 - j := by
        simp only [Spec.Tier1.passPlane]; omega
      simp only [Nat.add_sub_cancel] at H
      unfold Post at H ⊢
      simp only [hk0, hp0] at H
      simp only [k1, p1]
      apply rawSigPropPass_invV (by omega)
      refine ⟨H.1, fun x y hx hy => ?_⟩
      obtain ⟨⟨hb, hl⟩, hv⟩ := H.2 x y hx hy
      refine ⟨hb, ?_, ?_⟩
      · intro _ hv'; rw [hv] at hv'; cases hv'
      · intro hs _; rw [hl hs]; omega
    · simp only [show 3 * j + 2 - 1 = 3 * j + 1 by omega] at H
      unfold Post at H ⊢
      simp only [k1, p1] at H
      simp only [k2, p2]
      rw [← p1] at H ⊢
      exact rawMagRefPass_invV (by simp only [Spec.Tier1.passPlane]; omega) d H
    · simp only [show 3 * j + 3 - 1 = 3 * j + 2 by omega] at H
      unfold Post at H ⊢
      simp only [k2, p2] at H
      simp only [k3, p3]
      exact cleanupPass_invV (by omega) d H

/-! ## Segmentation symbols, resets, segment starts -/

/-- A segmentation symbol leaves the coefficients alone. -/
theorem segSymbol_coeffs (d : DecState) : (Spec.Tier1.segSymbol d).coeffs = d.coeffs := by
  simp only [Spec.Tier1.segSymbol, decodeBit_eq]
  split <;> rfl

/-- The coefficients after `runPassM` are those after its pass. -/
theorem runPassM_coeffs (md : Mode) (g : Geom) (K : Nat) (d : DecState) (i : Nat) :
    (Spec.Tier1.runPassM md g K d i).coeffs =
      (if Spec.Tier1.isRawPass md i then Spec.Tier1.runRawPass g K d i
       else Spec.Tier1.runPass g K d i).coeffs := by
  unfold Spec.Tier1.runPassM
  dsimp only
  generalize (if Spec.Tier1.isRawPass md i = true then Spec.Tier1.runRawPass g K d i
    else Spec.Tier1.runPass g K d i) = D
  have hs : (if (md.segSymbols && Spec.Tier1.passKind i == .cleanup) = true then
      Spec.Tier1.segSymbol D else D).coeffs = D.coeffs := by
    split
    · exact segSymbol_coeffs D
    · rfl
  split
  · exact hs
  · exact hs

/-- The invariant before pass `i`. -/
def Pre (K i : Nat) : Coeff → Prop := if i = 0 then IMR K (K - 1) else Post K (i - 1)

/-- **One pass of any style keeps the invariant.** -/
theorem runPassM_invV (md : Mode) (K i : Nat) (hi : i < 3 * K - 2) (d : DecState)
    (H : AllPV w h b vc (Pre K i) d.coeffs) :
    AllPV w h b vc (Pre K (i + 1)) (Spec.Tier1.runPassM md (gV w h b vc) K d i).coeffs := by
  rw [runPassM_coeffs]
  have e : Pre K (i + 1) = Post K i := by simp [Pre]
  rw [e]
  unfold Pre at H
  split
  · exact runRawPass_invV K i hi d H
  · exact runPass_invV K i hi d H

/-- A segment start leaves the coefficients alone. -/
theorem startSegment_coeffs (md : Mode) (d : DecState) (i : Nat) (data : List UInt8) :
    (Spec.Tier1.startSegment md d i data).coeffs = d.coeffs := by
  unfold Spec.Tier1.startSegment; split <;> rfl

/-- Passes `i, …, i + n − 1` keep the invariant. -/
theorem passes_invV (md : Mode) (K : Nat) :
    ∀ n i (d : DecState), i + n ≤ 3 * K - 2 → AllPV w h b vc (Pre K i) d.coeffs →
      AllPV w h b vc (Pre K (i + n))
        ((List.range' i n).foldl (Spec.Tier1.runPassM md (gV w h b vc) K) d).coeffs := by
  intro n
  induction n with
  | zero => intro i d _ H; exact H
  | succ n ih =>
    intro i d hn H
    rw [List.range'_succ, List.foldl_cons, show i + (n + 1) = (i + 1) + n by omega]
    exact ih (i + 1) _ (by omega) (runPassM_invV md K i (by omega) d H)

/-- **The invariant after all segments**: from `Pre K i`, decoding segments holding
`(L.map (·.passes)).sum` passes (within `3K − 2`) gives `Pre` of the pass count. -/
theorem decodeSegments_inv (md : Mode) (K : Nat) :
    ∀ (L : List Spec.Tier1.Segment) i (d : DecState),
      i + (L.map (·.passes)).sum ≤ 3 * K - 2 → AllPV w h b vc (Pre K i) d.coeffs →
      AllPV w h b vc (Pre K (i + (L.map (·.passes)).sum))
        (Spec.Tier1.decodeSegments md (gV w h b vc) K L i d).coeffs := by
  intro L
  induction L with
  | nil => intro i d _ H; simpa [Spec.Tier1.decodeSegments] using H
  | cons sg rest ih =>
    intro i d hn H
    simp only [List.map_cons, List.sum_cons] at hn ⊢
    simp only [Spec.Tier1.decodeSegments]
    rw [show i + (sg.passes + (rest.map (·.passes)).sum) =
      (i + sg.passes) + (rest.map (·.passes)).sum by omega]
    apply ih _ _ (by omega)
    apply passes_invV md K sg.passes i _ (by omega)
    rw [startSegment_coeffs]; exact H

end passes

end JPEG2000.Spec.Tier1EquivM
