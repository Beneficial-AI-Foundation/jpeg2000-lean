import Spec.RoundTrip.Header
import Spec.Decode

/-!
# Reversible display reconstruction (Plan.md §§4, 5.3, 7; T.800 G.1–G.2)

The full-resolution inverse DWT supplies row-major integer values in spec cell planes.
The encoder's component check supplies the shape and sample range needed to undo the
optional RCT and DC shift on those planes.
-/

namespace JPEG2000.Spec.RoundTrip

open JPEG2000.Encode
open JPEG2000.Spec.Decode

private theorem bindOk {α β : Type} {x : Except Error α} {f : α → Except Error β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

private theorem skipError {α β : Type} {g : Prop} [Decidable g] {err : Error}
    {f : α → Except Error β} {y : Except Error β} {b : β}
    (h : (if g then (throw err >>= f) else y) = .ok b) : y = .ok b := by
  by_cases hg : g
  · rw [ite_eq_left hg] at h
    cases h
  · rwa [ite_eq_right hg] at h

private theorem requireGuard {α β : Type} {g : Prop} [Decidable g] {err : Error}
    {f : α → Except Error β} {y : Except Error β} {b : β}
    (h : (if g then y else (throw err >>= f)) = .ok b) : g ∧ y = .ok b := by
  by_cases hg : g
  · exact ⟨hg, (ite_eq_left hg).symm.trans h⟩
  · rw [ite_eq_right hg] at h
    cases h

private theorem checkedLoop {α : Type} (P : α → Prop)
    (f : α → Unit → Except Error (ForInStep Unit))
    (step : ∀ a u r, f a u = .ok r → P a ∧ r = .yield ()) :
    ∀ xs : List α, forIn xs () f = .ok () → ∀ a ∈ xs, P a := by
  intro xs
  induction xs with
  | nil => simp
  | cons a as ih =>
    intro h b hb
    rw [List.forIn_cons] at h
    obtain ⟨r, hr, ht⟩ := bindOk h
    obtain ⟨ha, rfl⟩ := step a () r hr
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ha
    · exact ih ht b hb

/-- Every checked component has the declared sample count and contains only samples in its bit-depth range. -/
theorem check_component_samples {L : Limits} {p : Params} {img : Image}
    (h : Encode.check L p img = .ok ()) (c : Encode.Component) (hc : c ∈ img.comps) :
    (1 ≤ c.depth ∧ c.depth ≤ 38) ∧ c.samples.size = img.width * img.height ∧
    ∀ s ∈ c.samples, Spec.MCT.sampleMin c.signed c.depth ≤ s ∧
      s ≤ Spec.MCT.sampleMax c.signed c.depth := by
  unfold Encode.check at h
  dsimp only at h
  have h := skipError h
  iterate 3 obtain ⟨_, _, h⟩ := bindOk h
  obtain ⟨_, _, h⟩ := bindOk (skipError h)
  obtain ⟨u, hu, _⟩ := bindOk (requireGuard (skipError h)).2
  cases u
  rw [← Array.forIn_toList] at hu
  refine checkedLoop (fun c : Encode.Component =>
    (1 ≤ c.depth ∧ c.depth ≤ 38) ∧ c.samples.size = img.width * img.height ∧
    ∀ s ∈ c.samples, Spec.MCT.sampleMin c.signed c.depth ≤ s ∧
      s ≤ Spec.MCT.sampleMax c.signed c.depth) _ ?_ _ hu c (by simpa using hc)
  intro x u r hr
  repeat' (split at hr <;> try (obtain ⟨_, he, _⟩ := bindOk hr; cases he))
  rename_i ha
  exact ⟨⟨by assumption, by omega,
    by simpa only [Array.all_eq_true_iff_forall_mem, decide_eq_true_eq] using ha⟩,
    Except.ok.inj hr.symm⟩

private theorem three_entries {α : Type} (xs : Array α) (d : α) (hs : xs.size = 3) :
    ∃ a b c, xs = #[a, b, c] := by
  refine ⟨xs.getD 0 d, xs.getD 1 d, xs.getD 2 d, ?_⟩
  apply Array.ext (by simpa using hs)
  intro i hi _
  have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases this with rfl | rfl | rfl <;> exact Array.getElem_eq_getD d

private def fwdTriples (a b c : Array Int) :=
  Array.ofFn (n := a.size) fun i =>
    Spec.MCT.rctFwd (a.getD i 0, b.getD i 0, c.getD i 0)

private theorem mct3_three (a b c : Array Int) :
    mct3 Spec.MCT.rctFwd #[a, b, c] =
      #[(fwdTriples a b c).map (·.1), (fwdTriples a b c).map (·.2.1),
        (fwdTriples a b c).map (·.2.2)] := by rfl

private def invTriples (a b c : CellPlane) :=
  Array.ofFn (n := a.width * a.height) fun i =>
    rctCells (a.cells.getD i default) (b.cells.getD i default) (c.cells.getD i default)

private theorem mctSpec_three (a b c : CellPlane)
    (hd : b.width = a.width ∧ b.height = a.height ∧ c.width = a.width ∧ c.height = a.height) :
    mctSpec true #[a, b, c] = .ok #[{a with cells := (invTriples a b c).map (·.1)},
      {b with cells := (invTriples a b c).map (·.2.1)},
      {c with cells := (invTriples a b c).map (·.2.2)}] := by
  unfold mctSpec
  dsimp only
  split
  · rfl
  · rename_i h
    exact (h hd).elim

/-- A full component plane and its row-major integer values, as read by the display stages. -/
structure ReversibleRow (w h : Nat) (pl : CellPlane) (xs : Array Int) : Prop where
  /-- Full-resolution component width. -/
  width : pl.width = w
  /-- Full-resolution component height. -/
  height : pl.height = h
  /-- One spec cell per pixel. -/
  size : pl.cells.size = w * h
  /-- The reversible value at each linear index. -/
  value : ∀ j, j < w * h → (pl.cells.getD j default).ival = xs.getD j 0

private theorem map_ofFn_getD {α β : Type} (f : α → β) {n j : Nat} (g : Fin n → α)
    (d : β) (hj : j < n) : ((Array.ofFn g).map f).getD j d = f (g ⟨j, hj⟩) := by
  simp [Array.getD_eq_getD_getElem?, hj]

private theorem invertThree {w h : Nat} (a b c : Array Int) (x y z : CellPlane)
    (hn : a.size = w * h)
    (hx : ReversibleRow w h x ((fwdTriples a b c).map (·.1)))
    (hy : ReversibleRow w h y ((fwdTriples a b c).map (·.2.1)))
    (hz : ReversibleRow w h z ((fwdTriples a b c).map (·.2.2))) :
    ReversibleRow w h {x with cells := (invTriples x y z).map (·.1)} a ∧
    ReversibleRow w h {y with cells := (invTriples x y z).map (·.2.1)} b ∧
    ReversibleRow w h {z with cells := (invTriples x y z).map (·.2.2)} c := by
  have key (j : Nat) (hj : j < w * h) :
      Spec.MCT.rctInv ((x.cells.getD j default).ival, (y.cells.getD j default).ival,
        (z.cells.getD j default).ival) = (a.getD j 0, b.getD j 0, c.getD j 0) := by
    rw [hx.value j hj, hy.value j hj, hz.value j hj]
    simp only [fwdTriples, map_ofFn_getD _ _ _ (hn ▸ hj)]
    exact Spec.MCT.rctInv_rctFwd (a.getD j 0, b.getD j 0, c.getD j 0)
  refine ⟨⟨hx.width, hx.height, by simp [invTriples, hx.width, hx.height], ?_⟩,
    ⟨hy.width, hy.height, by simp [invTriples, hx.width, hx.height], ?_⟩,
    ⟨hz.width, hz.height, by simp [invTriples, hx.width, hx.height], ?_⟩⟩
  all_goals
    intro j hj
    have hj' : j < x.width * x.height := by rwa [hx.width, hx.height]
    simp only [invTriples, map_ofFn_getD _ _ _ hj', rctCells, key j hj]

/-- The integer rows passed to the reversible forward DWT by `Encode.bands53`. -/
def reversibleRows (p : Params) (img : Image) : Array (Array Int) :=
  if encMct p img then mct3 Spec.MCT.rctFwd (shifted img) else shifted img

private theorem shifted_at (img : Image) {i : Nat} (hi : i < img.comps.size) :
    (shifted img).getD i #[] = img.comps[i].samples.map
      (· - Spec.MCT.dcOffset img.comps[i].signed img.comps[i].depth) := by
  simp [shifted, Array.getD_eq_getD_getElem?, hi]

private theorem shifted_size_at {L : Limits} {p : Params} {img : Image}
    (hc : Encode.check L p img = .ok ()) {i : Nat} (hi : i < img.comps.size) :
    ((shifted img).getD i #[]).size = img.width * img.height := by
  rw [shifted_at img hi, Array.size_map]
  exact (check_component_samples hc _ (Array.getElem_mem hi)).2.1

private theorem three_cases {P : Nat → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2)
    (i : Nat) (hi : i < 3) : P i := by
  have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases this with rfl | rfl | rfl <;> assumption

private theorem rct_rows_size {w h : Nat} {rows : Array (Array Int)} (hs : rows.size = 3)
    (hn : (rows.getD 0 #[]).size = w * h) :
    (mct3 Spec.MCT.rctFwd rows).size = 3 ∧
    ∀ i, i < 3 → ((mct3 Spec.MCT.rctFwd rows).getD i #[]).size = w * h := by
  obtain ⟨a, b, c, rfl⟩ := three_entries rows #[] hs
  change a.size = w * h at hn
  rw [mct3_three]
  refine ⟨rfl, three_cases ?_ ?_ ?_⟩
  all_goals change (Array.map _ (fwdTriples a b c)).size = w * h
  all_goals simpa only [Array.size_map, fwdTriples, Array.size_ofFn] using hn

private theorem three_of_encMct {p : Params} {img : Image}
    (hn : img.comps.size = 1 ∨ img.comps.size = 3) (hm : encMct p img = true) :
    img.comps.size = 3 := by
  simp only [encMct, Bool.and_eq_true, decide_eq_true_eq] at hm
  omega

/-- `bands53` receives one integer array per component and one entry per image pixel,
including when a requested MCT is skipped on a single component. -/
theorem reversibleRows_size {L : Limits} {p : Params} {img : Image}
    (hc : Encode.check L p img = .ok ()) (hn : img.comps.size = 1 ∨ img.comps.size = 3) :
    (reversibleRows p img).size = img.comps.size ∧ ∀ i, i < img.comps.size →
      ((reversibleRows p img).getD i #[]).size = img.width * img.height := by
  unfold reversibleRows
  split
  · rename_i hm
    have hs := three_of_encMct hn hm
    have h := rct_rows_size (by simpa [shifted] using hs : (shifted img).size = 3)
      (shifted_size_at hc (i := 0) (by omega))
    simpa only [hs] using h
  · exact ⟨by simp [shifted], fun _ hi => shifted_size_at hc hi⟩

private theorem rct_rows_inverse {w h : Nat} {rows : Array (Array Int)} {ps : Array CellPlane}
    (hr : rows.size = 3) (hp : ps.size = 3) (hn : (rows.getD 0 #[]).size = w * h)
    (hv : ∀ i, i < 3 → ReversibleRow w h (ps.getD i CellPlane.empty)
      ((mct3 Spec.MCT.rctFwd rows).getD i #[])) :
    ∃ qs, mctSpec true ps = .ok qs ∧ qs.size = 3 ∧ ∀ i, i < 3 →
      ReversibleRow w h (qs.getD i CellPlane.empty) (rows.getD i #[]) := by
  obtain ⟨a, b, c, rfl⟩ := three_entries rows #[] hr
  obtain ⟨x, y, z, rfl⟩ := three_entries ps CellPlane.empty hp
  rw [mct3_three] at hv
  have hx := hv 0 (by decide)
  have hy := hv 1 (by decide)
  have hz := hv 2 (by decide)
  have out := invertThree a b c x y z hn hx hy hz
  refine ⟨_, mctSpec_three x y z ⟨hy.width.trans hx.width.symm, hy.height.trans hx.height.symm,
    hz.width.trans hx.width.symm, hz.height.trans hx.height.symm⟩, rfl, ?_⟩
  exact three_cases out.1 out.2.1 out.2.2

/-- The optional inverse MCT in `decodeTile` succeeds on the reconstructed forward
rows and returns the encoder's DC-shifted integers in every component. -/
theorem mctSpec_reversibleRows {L : Limits} {p : Params} {img : Image} {ps : Array CellPlane}
    (hc : Encode.check L p img = .ok ()) (hn : img.comps.size = 1 ∨ img.comps.size = 3)
    (hp : ps.size = img.comps.size)
    (hv : ∀ i, i < img.comps.size → ReversibleRow img.width img.height
      (ps.getD i CellPlane.empty) ((reversibleRows p img).getD i #[])) :
    ∃ qs, (if encMct p img then mctSpec true ps else .ok ps) = .ok qs ∧
      qs.size = img.comps.size ∧ ∀ i, i < img.comps.size →
        ReversibleRow img.width img.height (qs.getD i CellPlane.empty) ((shifted img).getD i #[]) := by
  split
  · rename_i hm
    have hs := three_of_encMct hn hm
    rw [hs]
    apply rct_rows_inverse (by simp [shifted, hs]) (hp.trans hs)
      (shifted_size_at hc (i := 0) (by omega))
    simpa only [reversibleRows, hm, ↓reduceIte, hs] using hv
  · rename_i hm
    exact ⟨ps, rfl, hp, by simpa [reversibleRows, hm] using hv⟩

/-- The reversible DC stage of `decodeTile`, with the signedness and depth read from
the encoded SIZ, recovers each checked sample at its original linear index. -/
theorem dcSpec_shifted {L : Limits} {p : Params} {img : Image} {pl : CellPlane}
    (hc : Encode.check L p img = .ok ()) {i : Nat} (hi : i < img.comps.size)
    (hpl : ReversibleRow img.width img.height pl ((shifted img).getD i #[])) :
    let comp := (encSIZ img).components.getD i default
    let out := dcSpec (comp.signed, comp.depth.toNat) true pl
    out.width = img.width ∧ out.height = img.height ∧ out.samples.size = img.width * img.height ∧
      ∀ j, j < img.width * img.height → (out.samples.getD j default).value =
        img.comps[i].samples.getD j 0 := by
  obtain ⟨hd, hn, hval⟩ := check_component_samples hc _ (Array.getElem_mem hi)
  have hmeta : ((encSIZ img).components.getD i default).signed = img.comps[i].signed ∧
      ((encSIZ img).components.getD i default).depth.toNat = img.comps[i].depth := by
    have hbyte : img.comps[i].depth < 256 := by omega
    simp [encSIZ, Array.getD_eq_getD_getElem?, hi, Nat.mod_eq_of_lt hbyte]
  dsimp only
  rw [hmeta.1, hmeta.2]
  refine ⟨hpl.width, hpl.height, by simpa [dcSpec] using hpl.size, ?_⟩
  intro j hj
  have hjp : j < pl.cells.size := hpl.size ▸ hj
  have hjs : j < img.comps[i].samples.size := hn ▸ hj
  have hsub := hpl.value j hj
  rw [shifted_at img hi] at hsub
  simp [Array.getD_eq_getD_getElem?, hjp, hjs] at hsub
  obtain ⟨lo, hi'⟩ := hval _ (Array.getElem_mem hjs)
  simp [dcSpec, SpecCell.toSample, Array.getD_eq_getD_getElem?, hjp, hjs, hsub,
    Spec.MCT.reconRev, Spec.MCT.clamp_of_mem _ _ _ lo hi']

/-- Display reconstruction of the full reversible tile. Given the inverse-DWT planes
in component order, the optional RCT succeeds and the DC output of every plane has
the image dimensions and exactly the original row-major sample array. -/
theorem display_reconstruction {L : Limits} {p : Params} {img : Image} {ps : Array CellPlane}
    (hc : Encode.check L p img = .ok ()) (hn : img.comps.size = 1 ∨ img.comps.size = 3)
    (hp : ps.size = img.comps.size)
    (hv : ∀ i, i < img.comps.size → ReversibleRow img.width img.height
      (ps.getD i CellPlane.empty) ((reversibleRows p img).getD i #[])) :
    ∃ qs, (if encMct p img then mctSpec true ps else .ok ps) = .ok qs ∧
      qs.size = img.comps.size ∧ ∀ i (hi : i < img.comps.size),
        let comp := (encSIZ img).components.getD i default
        let out := dcSpec (comp.signed, comp.depth.toNat) true (qs.getD i CellPlane.empty)
        out.width = img.width ∧ out.height = img.height ∧ out.samples.size = img.width * img.height ∧
          out.samples.map SpecSample.value = img.comps[i].samples := by
  obtain ⟨qs, hm, hq, hrows⟩ := mctSpec_reversibleRows hc hn hp hv
  refine ⟨qs, hm, hq, fun i hi => ?_⟩
  obtain ⟨hw, hh, hs, hv⟩ := dcSpec_shifted hc hi (hrows i hi)
  refine ⟨hw, hh, hs, ?_⟩
  have hn := (check_component_samples hc _ (Array.getElem_mem hi)).2.1
  apply Array.ext (by rw [Array.size_map, hs, hn])
  intro j hj hsrc
  rw [Array.size_map, hs] at hj
  simp only [Array.getElem_map]
  rw [Array.getElem_eq_getD (fallback := (default : SpecSample)),
    Array.getElem_eq_getD (xs := img.comps[i].samples) 0]
  exact hv j hj

end JPEG2000.Spec.RoundTrip
