import Spec.Tier1Equiv.Scan

/-!
# C3 (plain mode), part 4: an invariant of the spec decoder (magnitude bound, `lsbPlane`)

Plan.md §4 (C3), §5.2 "Tier-1 / EBCOT"; T.800 D.2, D.3, E.1.1.2 (`Nb(u, v)`). Task 3.6.

A property of the reference decoder alone, needed to read the fast decoder's output:

* every insignificant coefficient has `mag = 0` and `lsbPlane = 0`; every significant one has
  `mag < 2^K` (so `K ≤ 31` makes every magnitude fit an `Int32`) and `2^lsbPlane ∣ mag`
  (`Base`);
* after pass `i` of plane `q` (`Post K i`): after a significance propagation pass, a
  significant coefficient has `lsbPlane = q` if it was coded in that pass (`visited`) and
  `q + 1` otherwise; after a magnitude refinement or cleanup pass, every significant
  coefficient has `lsbPlane = q` (and after cleanup nothing is visited).

This is exactly what `JPEG2000.Tier1.CodeBlockOut.lsbPlane` recomputes from the last pass
index and the `VIS` bit (decision recorded with task 3.4a). Main result: `decodePasses_inv`.

The magnitude refinement pass needs the scan order to visit every position exactly once
(`scanOrder_nodup`, `mem_scanOrder_iff`): a coefficient refined twice in one pass would break
the bound; the significance propagation and cleanup steps are harmless if repeated.
-/

namespace JPEG2000.Spec.Tier1Equiv

open JPEG2000
open JPEG2000.Tier2.Geometry (Band)
open JPEG2000.Spec.Tier1 (Coeff Geom DecState)

/-! ## Scan order: every in-block position exactly once -/

/-- Positions of a stripe column. -/
theorem mem_stripeColumn {h x y0 : Nat} {p : Nat × Nat} (hp : p ∈ Spec.Tier1.stripeColumn h x y0) :
    p.1 = x ∧ y0 ≤ p.2 ∧ p.2 < y0 + 4 ∧ p.2 < h := by
  simp only [Spec.Tier1.stripeColumn, List.mem_map, List.mem_filter, List.mem_range,
    decide_eq_true_eq] at hp
  obtain ⟨r, ⟨hr, hh⟩, rfl⟩ := hp
  simp; omega

/-- The scan order as one `flatMap`. -/
theorem scanOrder_eq (w h : Nat) : Spec.Tier1.scanOrder w h =
    (List.range ((h + 3) / 4)).flatMap fun s =>
      (List.range w).flatMap fun x => Spec.Tier1.stripeColumn h x (4 * s) := by
  unfold Spec.Tier1.scanOrder Spec.Tier1.stripeColumns
  generalize List.range ((h + 3) / 4) = L
  induction L with
  | nil => rfl
  | cons a L ih =>
    rw [List.flatMap_cons, List.flatten_append, ih, List.flatMap_cons]
    congr 1

/-- **D.1**: the scan order has no repetition. -/
theorem scanOrder_nodup (w h : Nat) : (Spec.Tier1.scanOrder w h).Nodup := by
  rw [scanOrder_eq]
  unfold List.Nodup
  rw [List.pairwise_flatMap]
  refine ⟨fun s _ => ?_, ?_⟩
  · rw [List.pairwise_flatMap]
    refine ⟨fun x _ => ?_, ?_⟩
    · unfold Spec.Tier1.stripeColumn
      rw [List.pairwise_map]
      exact (List.pairwise_lt_range.sublist List.filter_sublist).imp
        (fun hab e => by simp at e; omega)
    · exact List.pairwise_lt_range.imp (fun hab p hp q hq e => by
        have := mem_stripeColumn hp; have := mem_stripeColumn hq; subst e; omega)
  · exact List.pairwise_lt_range.imp (fun hab p hp q hq e => by
      simp only [List.mem_flatMap, List.mem_range] at hp hq
      obtain ⟨x1, _, hp⟩ := hp
      obtain ⟨x2, _, hq⟩ := hq
      have := mem_stripeColumn hp; have := mem_stripeColumn hq; subst e; omega)

/-- **D.1**: the scan order contains exactly the in-block positions. -/
theorem mem_scanOrder_iff {w h x y : Nat} : (x, y) ∈ Spec.Tier1.scanOrder w h ↔ x < w ∧ y < h := by
  constructor
  · exact Spec.Tier1.mem_scanOrder
  · intro ⟨hx, hy⟩
    rw [scanOrder_eq]
    simp only [List.mem_flatMap, List.mem_range]
    refine ⟨y / 4, by omega, x, hx, ?_⟩
    simp only [Spec.Tier1.stripeColumn, List.mem_map, List.mem_filter, List.mem_range,
      decide_eq_true_eq, Prod.mk.injEq]
    exact ⟨y % 4, ⟨by omega, by omega⟩, trivial, by omega⟩

/-! ## Coefficient invariants -/

/-- A predicate holds for every in-block coefficient, and the array has `w · h` entries. -/
def AllP (w h : Nat) (b : Band) (P : Coeff → Prop) (cs : Array Coeff) : Prop :=
  cs.size = w * h ∧ ∀ x y, x < w → y < h → P ((sgeom w h b).coeffAt cs x y)

/-- The pass-independent part: magnitudes of insignificant coefficients are 0, significant
ones are below `2^K` and multiples of `2^lsbPlane`. -/
def Base (K : Nat) (c : Coeff) : Prop :=
  (c.sig = false → c.mag = 0 ∧ c.lsbPlane = 0) ∧
  (c.sig = true → c.mag < 2 ^ K ∧ c.mag % 2 ^ c.lsbPlane = 0)

/-- After the significance propagation pass of plane `q`. -/
def ISP (K q : Nat) (c : Coeff) : Prop :=
  Base K c ∧ (c.sig = true → c.visited = true → c.lsbPlane = q) ∧
    (c.sig = true → c.visited = false → c.lsbPlane = q + 1)

/-- After the magnitude refinement (or cleanup) pass of plane `q`. -/
def IMR (K q : Nat) (c : Coeff) : Prop := Base K c ∧ (c.sig = true → c.lsbPlane = q)

/-- The invariant after pass `i` (plane `passPlane K i`). -/
def Post (K i : Nat) (c : Coeff) : Prop :=
  match Spec.Tier1.passKind i with
  | .sigProp => ISP K (Spec.Tier1.passPlane K i) c
  | .magRef => IMR K (Spec.Tier1.passPlane K i) c
  | .cleanup => IMR K (Spec.Tier1.passPlane K i) c ∧ c.visited = false

/-! ## Setting one coefficient -/

section set
variable {w h : Nat} {b : Band}

/-- Writing a coefficient satisfying `P` keeps `AllP P`. -/
theorem allP_set {P : Coeff → Prop} {cs : Array Coeff} (H : AllP w h b P cs) {x y : Nat}
    (hx : x < w) (hy : y < h) (c' : Coeff) (hc : P c') :
    AllP w h b P ((sgeom w h b).setCoeff cs x y c') := by
  refine ⟨by simp [H.1], fun x' y' hx' hy' => ?_⟩
  rw [coeffAt_setCoeff _ _ H.1 _ _ hx hy]
  split
  · exact hc
  · exact H.2 x' y' hx' hy'

/-- A decision splits into a bit and a state with the same coefficients. -/
theorem decodeBit_split (d : DecState) (cx : Nat) :
    ∃ bb d', d.decodeBit cx = (bb, d') ∧ d'.coeffs = d.coeffs :=
  ⟨(d.decodeBit cx).1, (d.decodeBit cx).2, rfl, decodeBit_coeffs d cx⟩

/-- The coefficient written by `becomeSignificant`. -/
def sigC (c : Coeff) (neg : Bool) (p : Nat) (vis : Bool) : Coeff :=
  { c with sig := true, sign := neg, mag := c.mag + 2 ^ p, visited := vis, lsbPlane := p }

/-- The coefficient written by a zero-coding decision `0`. -/
def visC (c : Coeff) (vis : Bool) : Coeff := { c with visited := vis }

/-- What `becomeSignificant` writes. -/
theorem becomeSignificant_coeffs (p : Nat) (vis : Bool) (d : DecState) (x y : Nat) :
    ∃ neg, (Spec.Tier1.becomeSignificant (sgeom w h b) p vis d x y).coeffs =
      (sgeom w h b).setCoeff d.coeffs x y (sigC ((sgeom w h b).coeffAt d.coeffs x y) neg p vis) := by
  simp only [Spec.Tier1.becomeSignificant, Spec.Tier1.decodeSign]
  generalize (sgeom w h b).signContext d.coeffs x y = sc
  obtain ⟨cx, xb⟩ := sc
  obtain ⟨bb, d', e, hc⟩ := decodeBit_split d cx
  simp only [e, hc]
  exact ⟨_, rfl⟩

/-- `becomeSignificant` at an insignificant coefficient of an array satisfying `Base`. -/
theorem becomeSignificant_base {K q : Nat} (hq : q < K) {P : Coeff → Prop} (vis : Bool)
    (hP : ∀ c : Coeff, Base K c → c.sig = true → c.lsbPlane = q → c.visited = vis → P c) {d : DecState} (H : AllP w h b P d.coeffs) {x y : Nat} (hx : x < w)
    (hy : y < h) (hb : Base K ((sgeom w h b).coeffAt d.coeffs x y))
    (hs : ((sgeom w h b).coeffAt d.coeffs x y).sig = false) :
    AllP w h b P (Spec.Tier1.becomeSignificant (sgeom w h b) q vis d x y).coeffs := by
  obtain ⟨neg, e⟩ := becomeSignificant_coeffs (w := w) (h := h) (b := b) q vis d x y
  rw [e]
  apply allP_set H hx hy
  apply hP _ _ rfl rfl rfl
  have hm := (hb.1 hs).1
  refine ⟨fun h0 => by simp [sigC] at h0, fun _ => ⟨?_, ?_⟩⟩
  · simp only [sigC, hm, Nat.zero_add]; exact Nat.pow_lt_pow_right (by decide) hq
  · simp [sigC, hm]

/-- What `zeroCode` writes: the coefficient visited (`vis`), or significant. -/
theorem zeroCode_cases (p : Nat) (vis : Bool) (d : DecState) (x y : Nat) :
    (Spec.Tier1.zeroCode (sgeom w h b) p vis d x y).coeffs =
      (sgeom w h b).setCoeff d.coeffs x y (visC ((sgeom w h b).coeffAt d.coeffs x y) vis) ∨
    ∃ d' : DecState, d'.coeffs = d.coeffs ∧
      Spec.Tier1.zeroCode (sgeom w h b) p vis d x y =
        Spec.Tier1.becomeSignificant (sgeom w h b) p vis d' x y := by
  simp only [Spec.Tier1.zeroCode]
  obtain ⟨bb, d', e, hc⟩ := decodeBit_split d ((sgeom w h b).zcCtx d.coeffs x y)
  simp only [e]
  cases bb
  · left; simp [hc, visC]
  · right; exact ⟨d', hc, rfl⟩

end set

/-! ## The three passes -/

section passes
variable {w h : Nat} {b : Band}

/-- `Base` from the stronger invariants. -/
theorem ISP.base {K q : Nat} {c : Coeff} (h : ISP K q c) : Base K c := h.1

/-- One significance propagation step keeps `ISP`. -/
theorem sigPropStep_inv {K q : Nat} (hq : q < K) (d : DecState) (H : AllP w h b (ISP K q) d.coeffs)
    (pos : Nat × Nat) (hpos : pos.1 < w ∧ pos.2 < h) :
    AllP w h b (ISP K q) (Spec.Tier1.sigPropStep (sgeom w h b) q d pos).coeffs := by
  obtain ⟨x, y⟩ := pos
  obtain ⟨hx, hy⟩ := hpos
  simp only [Spec.Tier1.sigPropStep]
  split
  · rename_i hc
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
    have hI := H.2 x y hx hy
    rcases zeroCode_cases (w := w) (h := h) (b := b) q true d x y with e | ⟨d', hd', e⟩
    · rw [e]
      apply allP_set H hx hy
      refine ⟨⟨fun h0 => hI.1.1 (by simpa [visC] using h0), fun h1 => by simp [visC, hc.1] at h1⟩,
        fun h1 => by simp [visC, hc.1] at h1, fun h1 => by simp [visC, hc.1] at h1⟩
    · rw [e]
      rw [← hd'] at H hI hc
      exact becomeSignificant_base hq true (fun c hb _ hl hv => ⟨hb, fun _ _ => hl,
        fun _ hv' => by rw [hv] at hv'; cases hv'⟩) H hx hy hI.1 hc.1
  · exact H

/-- Order-free fold: a step that keeps `AllP P` at every position of the list keeps it over
the fold. -/
theorem foldl_allP {α : Type} (P : Coeff → Prop) (step : DecState → α → DecState) :
    ∀ (l : List α) (d : DecState), (∀ d' a, a ∈ l → AllP w h b P d'.coeffs →
      AllP w h b P (step d' a).coeffs) → AllP w h b P d.coeffs →
      AllP w h b P (l.foldl step d).coeffs := by
  intro l
  induction l with
  | nil => intro d _ H; exact H
  | cons a l ih =>
    intro d hs H
    simp only [List.foldl_cons]
    exact ih _ (fun d' a' ha' => hs d' a' (by simp [ha'])) (hs d a (by simp) H)

/-- **Significance propagation pass** (D.3.1) keeps `ISP q`. -/
theorem sigPropPass_inv {K q : Nat} (hq : q < K) (d : DecState) (H : AllP w h b (ISP K q) d.coeffs) :
    AllP w h b (ISP K q) (Spec.Tier1.sigPropPass (sgeom w h b) q d).coeffs := by
  unfold Spec.Tier1.sigPropPass
  apply foldl_allP _ _ _ _ _ H
  intro d' a ha H'
  exact sigPropStep_inv hq d' H' a (Spec.Tier1.mem_scanOrder ha)

/-- Ordered fold: along a list without repetition, each position is changed exactly once, by a
step that only changes that position and takes `Q1` to `Q2` there. -/
theorem foldl_ordered (Q1 Q2 : Coeff → Prop) (step : DecState → Nat × Nat → DecState)
    (hloc : ∀ (d : DecState) (x y : Nat), x < w → y < h → d.coeffs.size = w * h →
      (step d (x, y)).coeffs.size = w * h ∧ ∀ X Y : Nat, X < w → Y < h → (X, Y) ≠ (x, y) →
        (sgeom w h b).coeffAt (step d (x, y)).coeffs X Y = (sgeom w h b).coeffAt d.coeffs X Y)
    (htr : ∀ (d : DecState) (x y : Nat), x < w → y < h → d.coeffs.size = w * h →
      Q1 ((sgeom w h b).coeffAt d.coeffs x y) →
      Q2 ((sgeom w h b).coeffAt (step d (x, y)).coeffs x y)) :
    ∀ (l : List (Nat × Nat)) (d : DecState), l.Nodup → (∀ p ∈ l, p.1 < w ∧ p.2 < h) →
      d.coeffs.size = w * h → (∀ p ∈ l, Q1 ((sgeom w h b).coeffAt d.coeffs p.1 p.2)) →
      (l.foldl step d).coeffs.size = w * h ∧
      (∀ p ∈ l, Q2 ((sgeom w h b).coeffAt (l.foldl step d).coeffs p.1 p.2)) ∧
      (∀ X Y : Nat, X < w → Y < h → (X, Y) ∉ l →
        (sgeom w h b).coeffAt (l.foldl step d).coeffs X Y = (sgeom w h b).coeffAt d.coeffs X Y) := by
  intro l
  induction l with
  | nil => intro d _ _ hs _; exact ⟨hs, by simp, fun _ _ _ _ _ => rfl⟩
  | cons a l ih =>
    intro d hnd hin hs hq
    obtain ⟨x, y⟩ := a
    rw [List.nodup_cons] at hnd
    obtain ⟨hx, hy⟩ := hin (x, y) (by simp)
    obtain ⟨hs1, hl1⟩ := hloc d x y hx hy hs
    have hq' : ∀ p ∈ l, Q1 ((sgeom w h b).coeffAt (step d (x, y)).coeffs p.1 p.2) := by
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

/-- Adding the bit of plane `q` to a multiple of `2^(q+1)` below `2^K` stays below `2^K`. -/
theorem add_pow_lt (m q K : Nat) (hq : q < K) (hm : m < 2 ^ K) (hd : m % 2 ^ (q + 1) = 0) :
    m + 2 ^ q < 2 ^ K := by
  have hK : 2 ^ K = 2 ^ (q + 1) * 2 ^ (K - (q + 1)) := by
    rw [← Nat.pow_add]; congr 1; omega
  have hm' : m = 2 ^ (q + 1) * (m / 2 ^ (q + 1)) := (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hd)).symm
  have hpos : 0 < 2 ^ (q + 1) := Nat.two_pow_pos _
  have ht : m / 2 ^ (q + 1) < 2 ^ (K - (q + 1)) := by
    apply Nat.lt_of_mul_lt_mul_left (a := 2 ^ (q + 1))
    rw [← hm', ← hK]; exact hm
  have h2 : 2 ^ (q + 1) * (m / 2 ^ (q + 1) + 1) ≤ 2 ^ (q + 1) * 2 ^ (K - (q + 1)) :=
    Nat.mul_le_mul_left _ ht
  rw [Nat.mul_succ, ← hm', ← hK] at h2
  have h3 : 2 ^ (q + 1) = 2 * 2 ^ q := by rw [Nat.pow_succ, Nat.mul_comm]
  have : 0 < 2 ^ q := Nat.two_pow_pos _
  omega

/-- **Magnitude refinement pass** (D.3.3): from `ISP q` to `IMR q`. -/
theorem magRefPass_inv {K q : Nat} (hq : q < K) (d : DecState) (H : AllP w h b (ISP K q) d.coeffs) :
    AllP w h b (IMR K q) (Spec.Tier1.magRefPass (sgeom w h b) q d).coeffs := by
  unfold Spec.Tier1.magRefPass
  have hloc : ∀ (d : DecState) (x y : Nat), x < w → y < h → d.coeffs.size = w * h →
      (Spec.Tier1.magRefStep (sgeom w h b) q d (x, y)).coeffs.size = w * h ∧
      ∀ X Y : Nat, X < w → Y < h → (X, Y) ≠ (x, y) →
        (sgeom w h b).coeffAt (Spec.Tier1.magRefStep (sgeom w h b) q d (x, y)).coeffs X Y =
          (sgeom w h b).coeffAt d.coeffs X Y := by
    intro d x y hx hy hs
    simp only [Spec.Tier1.magRefStep]
    split
    · obtain ⟨bb, d', e, hc⟩ := decodeBit_split d ((sgeom w h b).mrCtx d.coeffs x y)
      simp only [e, hc]
      refine ⟨by simp [hs], fun X Y hX hY hne => ?_⟩
      rw [coeffAt_setCoeff _ _ hs _ _ hx hy]
      have : ¬ ((X : Int) = x ∧ (Y : Int) = y) := by
        intro ⟨a, c⟩; apply hne; simp only [Prod.mk.injEq]; omega
      simp [this]
    · exact ⟨hs, fun _ _ _ _ _ => rfl⟩
  have htr : ∀ (d : DecState) (x y : Nat), x < w → y < h → d.coeffs.size = w * h →
      ISP K q ((sgeom w h b).coeffAt d.coeffs x y) →
      IMR K q ((sgeom w h b).coeffAt (Spec.Tier1.magRefStep (sgeom w h b) q d (x, y)).coeffs x y) := by
    intro d x y hx hy hs hI
    simp only [Spec.Tier1.magRefStep]
    split
    · rename_i hc
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
      obtain ⟨bb, d', e, hc'⟩ := decodeBit_split d ((sgeom w h b).mrCtx d.coeffs x y)
      simp only [e, hc']
      rw [coeffAt_setCoeff _ _ hs _ _ hx hy]
      simp only [and_self, ↓reduceIte]
      have hl := hI.2.2 hc.1 hc.2
      have hb := (hI.1.2 hc.1)
      rw [hl] at hb
      refine ⟨⟨fun h0 => by simp [hc.1] at h0, fun _ => ⟨?_, ?_⟩⟩, fun _ => rfl⟩
      · have := add_pow_lt _ _ _ hq hb.1 hb.2
        cases bb <;> simp <;> omega
      · have h1 : ((sgeom w h b).coeffAt d.coeffs x y).mag % 2 ^ q = 0 := by
          have : 2 ^ q ∣ 2 ^ (q + 1) := Nat.pow_dvd_pow 2 (by omega)
          rw [← Nat.mod_mod_of_dvd _ this, hb.2]; rfl
        cases bb <;> simp [h1]
    · rename_i hc
      refine ⟨hI.1, fun hs1 => ?_⟩
      have hv : ((sgeom w h b).coeffAt d.coeffs x y).visited = true := by
        cases hv : ((sgeom w h b).coeffAt d.coeffs x y).visited <;> simp_all
      exact hI.2.1 hs1 hv
  obtain ⟨r1, r2, _⟩ := foldl_ordered (w := w) (h := h) (b := b) (ISP K q) (IMR K q)
    (Spec.Tier1.magRefStep (sgeom w h b) q) hloc htr (Spec.Tier1.scanOrder w h) d
    (scanOrder_nodup w h) (fun p hp => Spec.Tier1.mem_scanOrder hp) H.1
    (fun p _ => H.2 p.1 p.2 (Spec.Tier1.mem_scanOrder (by simpa using ‹p ∈ _›)).1
      (Spec.Tier1.mem_scanOrder (by simpa using ‹p ∈ _›)).2)
  exact ⟨r1, fun x y hx hy => r2 (x, y) (mem_scanOrder_iff.mpr ⟨hx, hy⟩)⟩

/-- One normal cleanup step keeps `IMR q`. -/
theorem cleanupStep_inv {K q : Nat} (hq : q < K) (d : DecState) (H : AllP w h b (IMR K q) d.coeffs)
    (pos : Nat × Nat) (hpos : pos.1 < w ∧ pos.2 < h) :
    AllP w h b (IMR K q) (Spec.Tier1.cleanupStep (sgeom w h b) q d pos).coeffs := by
  obtain ⟨x, y⟩ := pos
  obtain ⟨hx, hy⟩ := hpos
  simp only [Spec.Tier1.cleanupStep]
  split
  · rename_i hc
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
    have hI := H.2 x y hx hy
    rcases zeroCode_cases (w := w) (h := h) (b := b) q false d x y with e | ⟨d', hd', e⟩
    · rw [e]
      apply allP_set H hx hy
      refine ⟨⟨fun h0 => hI.1.1 (by simpa [visC] using h0), fun h1 => by simp [visC, hc.1] at h1⟩,
        fun h1 => by simp [visC, hc.1] at h1⟩
    · rw [e]
      rw [← hd'] at H hI hc
      exact becomeSignificant_base hq false (fun c hb _ hl _ => ⟨hb, fun _ => hl⟩) H hx hy
        hI.1 hc.1
  · exact H

/-- The cleanup pass on one stripe column (D.3.4, run-length mode included) keeps `IMR q`. -/
theorem cleanupColumn_inv {K q : Nat} (hq : q < K) (d : DecState)
    (H : AllP w h b (IMR K q) d.coeffs) (col : List (Nat × Nat))
    (hcol : ∀ p ∈ col, p.1 < w ∧ p.2 < h) :
    AllP w h b (IMR K q) (Spec.Tier1.cleanupColumn (sgeom w h b) q d col).coeffs := by
  have fold : ∀ (l : List (Nat × Nat)) (d : DecState), (∀ p ∈ l, p.1 < w ∧ p.2 < h) →
      AllP w h b (IMR K q) d.coeffs →
      AllP w h b (IMR K q) (l.foldl (Spec.Tier1.cleanupStep (sgeom w h b) q) d).coeffs :=
    fun l d hl H => foldl_allP _ _ l d (fun d' a ha H' => cleanupStep_inv hq d' H' a (hl a ha)) H
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
        exact becomeSignificant_base hq false (fun c hb _ hl _ => ⟨hb, fun _ => hl⟩) H hx hy
          (H.2 x y hx hy).1 hxy.1.1
  · exact fold col d hcol H

/-- Columns of the scan are in the block. -/
theorem mem_stripeColumns {w h : Nat} {col : List (Nat × Nat)}
    (hc : col ∈ Spec.Tier1.stripeColumns w h) : ∀ p ∈ col, p.1 < w ∧ p.2 < h := by
  simp only [Spec.Tier1.stripeColumns, List.mem_flatMap, List.mem_map, List.mem_range] at hc
  obtain ⟨s, _, x, hx, rfl⟩ := hc
  intro p hp
  have := mem_stripeColumn hp
  omega

/-- **Cleanup pass** (D.3.4): from `IMR q` to `IMR q` with nothing visited. -/
theorem cleanupPass_inv {K q : Nat} (hq : q < K) (d : DecState) (H : AllP w h b (IMR K q) d.coeffs) :
    AllP w h b (fun c => IMR K q c ∧ c.visited = false)
      (Spec.Tier1.cleanupPass (sgeom w h b) q d).coeffs := by
  unfold Spec.Tier1.cleanupPass
  have H' := foldl_allP (w := w) (h := h) (b := b) (IMR K q) (Spec.Tier1.cleanupColumn (sgeom w h b) q)
    (Spec.Tier1.stripeColumns w h) d
    (fun d' col hc H' => cleanupColumn_inv hq d' H' col (mem_stripeColumns hc)) H
  rw [show (sgeom w h b).width = w from rfl, show (sgeom w h b).height = h from rfl]
  generalize (Spec.Tier1.stripeColumns w h).foldl (Spec.Tier1.cleanupColumn (sgeom w h b) q) d = d' at H'
  refine ⟨by simp [Spec.Tier1.clearVisited, H'.1], fun x y hx hy => ?_⟩
  simp only
  rw [show Spec.Tier1.clearVisited d'.coeffs = d'.coeffs.map fun c => { c with visited := false }
    from rfl, coeffAt_map _ _ _ rfl]
  have := H'.2 x y hx hy
  exact ⟨⟨this.1, this.2⟩, rfl⟩

/-! ## The pass sequence -/

/-- Pass `3j` is a cleanup pass. -/
theorem passKind_mul3 (j : Nat) : Spec.Tier1.passKind (3 * j) = .cleanup := by
  unfold Spec.Tier1.passKind
  by_cases hj : 3 * j = 0
  · simp [hj]
  · have : (3 * j - 1) % 3 = 2 := by omega
    simp [hj, this]

/-- **One pass keeps the invariant**: before pass `i` the invariant after pass `i − 1` holds (for
`i = 0`: every significant coefficient has `lsbPlane = K − 1`, vacuous on the initial state);
after it, `Post K i`. Requires `i < 3K − 2`. -/
theorem runPass_inv (K i : Nat) (hi : i < 3 * K - 2) (d : DecState)
    (H : AllP w h b (if i = 0 then IMR K (K - 1) else Post K (i - 1)) d.coeffs) :
    AllP w h b (Post K i) (Spec.Tier1.runPass (sgeom w h b) K d i).coeffs := by
  unfold Spec.Tier1.runPass
  by_cases i0 : i = 0
  · subst i0
    simp only [↓reduceIte] at H
    have hk : Spec.Tier1.passKind 0 = .cleanup := rfl
    have hp : Spec.Tier1.passPlane K 0 = K - 1 := by simp [Spec.Tier1.passPlane]
    simp only [hk, hp]
    unfold Post; simp only [hk, hp]
    exact cleanupPass_inv (by omega) d H
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
      apply sigPropPass_inv (by omega)
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
      exact magRefPass_inv (by simp only [Spec.Tier1.passPlane]; omega) d H
    · simp only [show 3 * j + 3 - 1 = 3 * j + 2 by omega] at H
      unfold Post at H ⊢
      simp only [k2, p2] at H
      simp only [k3, p3]
      exact cleanupPass_inv (by omega) d H

/-- **The invariant after `n` passes** (`1 ≤ n ≤ 3K − 2`), from the initial all-`{}` state. -/
theorem decodePasses_inv (K : Nat) (d : DecState) (hd : d.coeffs = Array.replicate (w * h) {}) :
    ∀ n, 1 ≤ n → n ≤ 3 * K - 2 →
      AllP w h b (Post K (n - 1)) (Spec.Tier1.decodePasses (sgeom w h b) K n d).coeffs := by
  intro n
  induction n with
  | zero => intro h0; omega
  | succ n ih =>
    intro _ hn
    unfold Spec.Tier1.decodePasses
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp only [Nat.add_sub_cancel]
    apply runPass_inv K n (by omega)
    by_cases n0 : n = 0
    · subst n0
      simp only [↓reduceIte, List.range_zero, List.foldl_nil]
      refine ⟨by simp [hd], fun x y hx hy => ?_⟩
      have : (sgeom w h b).coeffAt d.coeffs x y = {} := by
        rw [coeffAt_nat _ _ _ _ hx hy, hd]
        have hl : (sgeom w h b).idx x y < (Array.replicate (w * h) ({} : Coeff)).size := by
          simp only [Array.size_replicate]; exact idx_lt (sgeom w h b) hx hy
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hl]
        simp
      rw [this]
      exact ⟨⟨fun _ => ⟨rfl, rfl⟩, fun h0 => by cases h0⟩, fun h0 => by cases h0⟩
    · simp only [n0, ↓reduceIte]
      exact ih (by omega) (by omega)

end passes

end JPEG2000.Spec.Tier1Equiv
