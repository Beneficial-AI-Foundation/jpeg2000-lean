import Spec.RoundTrip.DisplayReconstruction
import Spec.RoundTrip.SingleTile

/-!
# Full-resolution reconstruction of the encoder tile (Plan.md §§1, 4, 5, 7)

The component loop of the specification gathers the inverse 5/3 planes in
component order. The inverse RCT and DC shift (T.800 Annex G) then recover the
input samples on the full tile rectangle for every checked component count.
-/

namespace JPEG2000.Spec.RoundTrip

open JPEG2000.Encode JPEG2000.Spec.Decode JPEG2000.Header

private theorem range_success {α : Type} {n : Nat} {init : α}
    {f : Nat → α → Except Error (ForInStep α)} (P : Nat → α → Prop) (start : P 0 init)
    (step : ∀ i < n, ∀ a, P i a → ∃ b, f i a = .ok (.yield b) ∧ P (i+1) b) :
    ∃ b, forIn [0:n] init f = .ok b ∧ P n b := by
  have go (k : Nat) : ∀ i a, i+k ≤ n → P i a →
      ∃ b, forIn (List.range' i k) a f = .ok b ∧ P (i+k) b := by
    induction k with
    | zero => intro i a _ ha; exact ⟨a, rfl, ha⟩
    | succ k ih =>
      intro i a hi ha
      obtain ⟨b, hb, pb⟩ := step i (by omega) a ha
      obtain ⟨v, hv, pv⟩ := ih (i+1) b (by omega) pb
      rw [List.range'_succ, List.forIn_cons, hb]
      exact ⟨v, hv, by rwa [show i+(k+1) = i+1+k by omega]⟩
  simpa [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size] using
    go n 0 init (by simp) start

private theorem push_prefix {α : Type} {xs : Array α} {v : α} (P : Nat → α → Prop)
    (prev : ∀ j (hj : j < xs.size), P j xs[j]) (next : P xs.size v) :
    ∀ j (hj : j < (xs.push v).size), P j (xs.push v)[j] := by
  intro j hj
  by_cases h : j < xs.size
  · simpa only [Array.getElem_push_lt h] using prev j h
  · have he : j = xs.size := by simp only [Array.size_push] at hj; omega
    subst j
    simpa using next

private theorem reconstruction_loop {n : Nat} (recon : Nat → Except Error (CellPlane × Nat))
    (row : Nat → CellPlane → Prop) (step : ∀ i < n, ∃ pl, recon i = .ok (pl, 0) ∧ row i pl) :
    let f := fun c (s : Array CellPlane × Nat) => do
      let (pl, sat) ← recon c
      pure (ForInStep.yield (s.1.push pl, s.2 + sat))
    ∃ ps, forIn [0:n] (#[], 0) f = .ok (ps, 0) ∧
      ps.size = n ∧ ∀ i, i < n → row i (ps.getD i CellPlane.empty) := by
  intro f
  let P (i : Nat) (s : Array CellPlane × Nat) :=
    s.1.size = i ∧ s.2 = 0 ∧ ∀ j (hj : j < s.1.size), row j s.1[j]
  suffices h : ∃ s, forIn [0:n] (#[], 0) f = .ok s ∧ P n s by
    obtain ⟨⟨ps, sat⟩, hr, hs, hz, hp⟩ := h
    change sat = 0 at hz
    subst sat
    refine ⟨ps, hr, hs, fun i hi => ?_⟩
    rw [← Array.getElem_eq_getD (h := hs ▸ hi)]
    exact hp i (hs ▸ hi)
  apply range_success P
  · exact ⟨rfl, rfl, by simp⟩
  · intro i hi s ⟨hs, hz, hp⟩
    obtain ⟨pl, hr, hpl⟩ := step i hi
    refine ⟨(s.1.push pl, 0), ?_, by simp [hs], rfl, push_prefix row hp (hs ▸ hpl)⟩
    simp [f, hr, hz, bind, Except.bind, pure, Except.pure]

private theorem display_loop {n : Nat} (qs : Array CellPlane)
    (make : Nat → CellPlane → Rect × SamplePlane) :
    ∃ st, (forIn (m := Except Error) [0:n] (qs, #[]) fun c s =>
      pure (.yield (s.1.setIfInBounds c CellPlane.empty,
        s.2.push (make c (s.1.getD c CellPlane.empty))))) = .ok st ∧
      st.2.size = n ∧ ∀ j (hj : j < st.2.size), st.2[j] = make j (qs.getD j CellPlane.empty) := by
  let P (i : Nat) (s : Array CellPlane × Array (Rect × SamplePlane)) :=
    s.2.size = i ∧ (∀ j, i ≤ j → s.1.getD j CellPlane.empty = qs.getD j CellPlane.empty) ∧
    ∀ j (hj : j < s.2.size), s.2[j] = make j (qs.getD j CellPlane.empty)
  suffices h : ∃ s, _ ∧ P n s by
    obtain ⟨s, hr, hs, _, hp⟩ := h
    exact ⟨s, hr, hs, hp⟩
  apply range_success P
  · exact ⟨rfl, by simp, by simp⟩
  · intro i _ s ⟨hs, htail, hp⟩
    refine ⟨_, rfl, by simp [hs], ?_,
      push_prefix (fun j x => x = make j (qs.getD j CellPlane.empty)) hp ?_⟩
    · intro j hj
      simpa only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_ne (by omega : i ≠ j)]
        using htail j (by omega)
    · rw [hs, htail i (Nat.le_refl i)]

private theorem full_rect (r : Rect) : Assemble.reduceRect r 0 = r := by
  cases r
  simp [Assemble.reduceRect, cdivPow, cdiv]

private theorem layout_cells (p : Params) (img : Encode.Image) (guard : Nat) (exps : Array Nat) :
    (encLayout p img guard exps).comps.foldl (fun a tc => a +
      (Assemble.reduceRect tc.rect 0).width * (Assemble.reduceRect tc.rect 0).height) 0 =
      img.comps.size * (img.width * img.height) := by
  rw [← Array.foldl_toList]
  simp only [encLayout, Array.toList_replicate, full_rect]
  rw [← List.foldl_map (f := fun tc : Tier2.Geometry.TileCompGeom => tc.rect.width * tc.rect.height),
    ← List.sum_eq_foldl_nat]
  simp [encGeom, encRect, Rect.width, Rect.height, List.sum_replicate_nat]

/-- At zero reduction the spec reconstructs the full encoder tile whenever each
tile-component call returns its reversible row and the combined planes fit the
decoder's work limit. The component calls and work limit use the same limits. -/
theorem decodeTile_reconstructedEncoderTile {L : Limits} {p : Params} {img : Encode.Image}
    {guard : Nat} {exps : Array Nat} {data : ByteArray} {out : Spec.Tier2.TileOut}
    (checked : Encode.check Limits.default p img = .ok ()) (hrev : p.reversible = true)
    (work : img.comps.size * (img.width * img.height) ≤ L.maxWorkSamples)
    (rows : ∀ c < img.comps.size, ∃ pl,
      Decode.tileComp L (encGeom p img guard exps) ((encSIZ img).components.getD c default).depth.toNat
        (Assemble.fracBitsOf (encSIZ img) (encMct p img) c) 0 (out.comps.getD c []) = .ok (pl, 0) ∧
      ReversibleRow img.width img.height pl ((reversibleRows p img).getD c #[])) :
    ∃ t, Decode.decodeTile L (encHeader p img guard exps data) 0 0 (some out) = .ok t ∧
      ReconstructedEncoderTile img t := by
  let g := encLayout p img guard exps
  let comp (i : Nat) := (encSIZ img).components.getD i default
  let recon (i : Nat) := Decode.tileComp L (g.comp i) (comp i).depth.toNat
    (Assemble.fracBitsOf (encSIZ img) (encMct p img) i) 0 (out.comps.getD i [])
  let row (i : Nat) (pl : CellPlane) :=
    ReversibleRow img.width img.height pl ((reversibleRows p img).getD i #[])
  have hc := checkFacts_of_ok checked
  have hgeom (i : Nat) (hi : i < img.comps.size) : g.comp i = encGeom p img guard exps :=
    encLayout_comp p img guard exps i hi
  have hr (i : Nat) (hi : i < img.comps.size) : ∃ pl, recon i = .ok (pl, 0) ∧ row i pl := by
    simpa only [recon, comp, row, hgeom i hi] using rows i hi
  obtain ⟨ps, hloop, hcount, hrows⟩ := reconstruction_loop recon row hr
  obtain ⟨qs, hmct, _, hdisplay⟩ := display_reconstruction_all_components checked hcount hrows
  let rev (i : Nat) := (g.comp i).params.transform == Marker.Transform.reversible53
  let make (i : Nat) (pl : CellPlane) :=
    (Assemble.reduceRect (g.comp i).rect 0, dcSpec ((comp i).signed, (comp i).depth.toNat) (rev i) pl)
  have hrevAt (i : Nat) (hi : i < img.comps.size) : rev i = true := by
    simp [rev, hgeom i hi, encGeom, encParams, hrev]
  obtain ⟨st, hdc, hs, hpair⟩ := display_loop (n := img.comps.size) qs make
  refine ⟨⟨0, st.2⟩, ?_, hs, ?_, ?_⟩
  · have hl := layout_ofHeader_enc p img guard exps data hc
    have hn := (encLayout_coding p img guard exps).1
    have hm : (encCoding p img guard exps).mctApplies (encSIZ img) = encMct p img := by
      simp [Coding.mctApplies, encCoding, encSIZ, Marker.SIZ.csiz, encMct]
    have hw := (Limits.check_eq_ok_iff L Assemble.loc .workSamples _).2 work
    unfold Decode.decodeTile tileWith
    simp only [hl, Spec.Tier2Equiv.ok_bind, layout_cells, hw, hn,
      show (encHeader p img guard exps data).siz = encSIZ img from rfl, hm]
    rw [hloop]
    dsimp only [Spec.Tier2Equiv.ok_bind]
    have finish := congrArg (fun x : Except Error (Array CellPlane × Array (Rect × SamplePlane)) =>
      x >>= fun s => pure ({ tile := 0, comps := s.2 } : Decode.TileOut)) hdc
    cases h : encMct p img with
    | false =>
      simp only [h, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at hmct
      subst qs
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact finish
    | true =>
      simp only [h, ↓reduceIte] at hmct
      simp only [↓reduceIte]
      rw [show (((encLayout p img guard exps).comp 0).params.transform == Marker.Transform.reversible53)
        = true from hrevAt 0 hc.comps_pos, hmct, Spec.Tier2Equiv.ok_bind]
      exact finish
  · intro i hi
    have h := hdisplay i (hs ▸ hi)
    rw [hpair i hi]
    simp only [make, hgeom i (hs ▸ hi), full_rect, encGeom, hrevAt i (hs ▸ hi)]
    exact ⟨trivial, h.1, h.2.1, h.2.2.1⟩
  · intro i hi
    rw [hpair i hi]
    simp only [make, hrevAt i (hs ▸ hi)]
    exact (hdisplay i (hs ▸ hi)).2.2.2

end JPEG2000.Spec.RoundTrip
