import Spec.RoundTrip.PrecinctShape

/-!
# Disjoint flat precinct spans

Plan.md §§4 (C10), 5.3 and 7 (M7), task 7.3f5a. T.800 B.6–B.9.
The decoder appends precinct states in component, resolution and precinct order.
The start of each resolution is the sum of the sizes of all preceding grids.
-/

namespace JPEG2000.Spec.RoundTrip

open JPEG2000.Progression (Layout PacketId)
open JPEG2000.Tier2.Packet (initPrecincts PrecState)
open JPEG2000.Tier2.Geometry (resolution ResolutionGeom)
open JPEG2000.Spec.Tier2Equiv (bind_ok)

private def prefixSum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => prefixSum f n + f n

private theorem prefixSum_mono (f : Nat → Nat) {i j : Nat} (h : i ≤ j) :
    prefixSum f i ≤ prefixSum f j := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans ih (Nat.le_add_right ..)

private abbrev gridSize (g : Layout) (c r : Nat) := g.pw c r * g.ph c r

private def compStart (g : Layout) :=
  prefixSum fun c => prefixSum (gridSize g c) (g.levels c + 1)

private def resStart (g : Layout) (c r : Nat) :=
  compStart g c + prefixSum (gridSize g c) r

private def Table {α : Type} (d : α) (P : Nat → α → Prop) (n : Nat) (xs : Array α) :=
  xs.size = n ∧ ∀ i < n, P i (xs.getD i d)

private theorem table_empty {α : Type} (d : α) (P : Nat → α → Prop) : Table d P 0 #[] :=
  ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩

private theorem Table.push {α : Type} {d x : α} {P : Nat → α → Prop} {n : Nat} {xs : Array α}
    (h : Table d P n xs) (hx : P n x) : Table d P (n+1) (xs.push x) := by
  refine ⟨by simp [h.1], fun i hi => ?_⟩
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_push, h.1]
  by_cases he : i = n
  · subst i
    simpa only [ite_true, Option.getD_some] using hx
  · rw [ite_eq_right he, ← Array.getD_eq_getD_getElem?]
    exact h.2 i (by omega)

private theorem loop_inv {β : Type} (P : Nat → β → Prop) {n : Nat} {init out : β}
    {f : Nat → β → Except Error (ForInStep β)} (h0 : P 0 init)
    (h : forIn [0:n] init f = .ok out)
    (step : ∀ i b t, P i b → f i b = .ok t → ∃ b', t = .yield b' ∧ P (i+1) b') :
    P n out := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at h
  simpa [Std.Legacy.Range.size] using
    Spec.Tier2WF.forIn_range'_inv P f step [0:n].size 0 init out h0 h

private theorem gridSize_of_ok {L : Limits} {g : Layout} {c r : Nat} {res : ResolutionGeom}
    (h : resolution L (g.comp c) r = .ok res) : res.numPrecincts = gridSize g c r := by
  unfold resolution at h
  dsimp only at h
  split at h
  · cases h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  cases h
  rfl

private abbrev BaseRow (g : Layout) (c : Nat) :=
  Table 0 (fun r start => start = resStart g c r)

private theorem base_prefix {L : Limits} {g : Layout} {precs base spans}
    (h : initPrecincts L g = .ok (precs, base, spans)) :
    Table #[] (fun c => BaseRow g c (g.levels c + 1)) g.numComps base := by
  unfold initPrecincts at h
  dsimp only at h
  obtain ⟨s, hs, h⟩ := bind_ok h
  cases h
  suffices s.1.size = compStart g g.numComps ∧
      Table #[] (fun c => BaseRow g c (g.levels c + 1)) g.numComps s.2.1 from this.2
  refine loop_inv (fun c (s : Array PrecState × Array (Array Nat) × Array (Array (Nat × Nat)) × Nat) =>
    s.1.size = compStart g c ∧ Table #[] (fun i => BaseRow g i (g.levels i + 1)) c s.2.1)
    ⟨rfl, table_empty ..⟩ hs ?_
  intro c b t hb ht
  obtain ⟨s, hs, ht⟩ := bind_ok ht
  cases ht
  have hr : s.1.size = resStart g c (g.levels c + 1) ∧
      BaseRow g c (g.levels c + 1) s.2.2.1 := by
    refine loop_inv (fun r (s : Array PrecState × Nat × Array Nat × Array (Nat × Nat)) =>
      s.1.size = resStart g c r ∧ BaseRow g c r s.2.2.1)
      ⟨hb.1, table_empty ..⟩ hs ?_
    intro r b' t' hb' ht'
    obtain ⟨res, hres, ht'⟩ := bind_ok ht'
    obtain ⟨_, _, ht'⟩ := bind_ok ht'
    obtain ⟨s', hs', ht'⟩ := bind_ok ht'
    cases ht'
    have hsize : s'.1.size = b'.1.size + res.numPrecincts := by
      refine loop_inv (fun p (st : Array PrecState × Nat) => st.1.size = b'.1.size + p)
        rfl hs' ?_
      intro p st u hp hu
      obtain ⟨_, _, hu⟩ := bind_ok hu
      obtain ⟨_, _, hu⟩ := bind_ok hu
      obtain ⟨_, _, hu⟩ := bind_ok hu
      cases hu
      exact ⟨_, rfl, by simp only [Array.size_push, hp, Nat.add_assoc]⟩
    refine ⟨_, rfl, ?_, hb'.2.push hb'.1⟩
    rw [hsize, gridSize_of_ok hres, hb'.1]
    exact Nat.add_assoc ..
  exact ⟨_, rfl, hr.1, hb.2.push hr.2⟩

private theorem base_ordered {L : Limits} {g : Layout} {precs base spans} {c r d s : Nat}
    (h : initPrecincts L g = .ok (precs, base, spans))
    (hc : c < g.numComps) (hr : r ≤ g.levels c) (hd : d < g.numComps) (hs : s ≤ g.levels d)
    (hlt : c < d ∨ c = d ∧ r < s) :
    (base.getD c #[]).getD r 0 + gridSize g c r ≤ (base.getD d #[]).getD s 0 := by
  have ht := base_prefix h
  rw [((ht.2 c hc).2 r (Nat.lt_succ_of_le hr)), ((ht.2 d hd).2 s (Nat.lt_succ_of_le hs))]
  unfold resStart
  rcases hlt with hcd | ⟨rfl, hrs⟩
  · have hrow := prefixSum_mono (gridSize g c) (Nat.succ_le_succ hr)
    have hcomp : compStart g (c+1) ≤ compStart g d := prefixSum_mono _ hcd
    change compStart g c + prefixSum (gridSize g c) (g.levels c + 1) ≤ compStart g d at hcomp
    change prefixSum (gridSize g c) r + gridSize g c r ≤
      prefixSum (gridSize g c) (g.levels c + 1) at hrow
    omega
  · have hrow := prefixSum_mono (gridSize g c) hrs
    change prefixSum (gridSize g c) r + gridSize g c r ≤ _ at hrow
    omega

/-- In component and resolution order, each recorded half-open span ends at or before
the next span examined begins. Either span may have length zero. -/
theorem initPrecincts_spans_disjoint {L : Limits} {g : Layout} {precs base spans} {c r d s : Nat}
    (h : initPrecincts L g = .ok (precs, base, spans))
    (hc : c < g.numComps) (hr : r ≤ g.levels c) (hd : d < g.numComps) (hs : s ≤ g.levels d)
    (hlt : c < d ∨ c = d ∧ r < s) :
    let a := (spans.getD c #[]).getD r (0, 0)
    let b := (spans.getD d #[]).getD s (0, 0)
    a.1 + a.2 ≤ b.1 := by
  obtain ⟨_, _, hn, ha, _⟩ := initPrecincts_geometry h hc hr
  obtain ⟨_, _, _, hb, _⟩ := initPrecincts_geometry h hd hs
  dsimp only
  simp only [Array.getD_eq_getD_getElem?] at ha hb ⊢
  rw [ha, hb]
  simpa only [Option.getD_some, hn, ← Array.getD_eq_getD_getElem?] using
    base_ordered h hc hr hd hs hlt

/-- On a single layer the flat precinct index identifies the packet. This supplies the
injectivity premise of `tile_enc` directly from successful decoder initialization. -/
theorem initPrecincts_precIdx_injective {L : Limits} {g : Layout} {precs base spans}
    (h : initPrecincts L g = .ok (precs, base, spans)) (hlay : g.layers = 1) :
    ∀ p q, g.InPacketSet p → g.InPacketSet q → precIdx base p = precIdx base q → p = q := by
  intro ⟨l, r, c, k⟩ ⟨m, s, d, j⟩ hp hq he
  obtain ⟨hl, hc, hr, hk⟩ := hp
  obtain ⟨hm, hd, hs, hj⟩ := hq
  dsimp only at hl hc hr hk hm hd hs hj
  change (base.getD c #[]).getD r 0 + k = (base.getD d #[]).getD s 0 + j at he
  have h₁ := base_ordered h hc hr hd hs
  have h₂ := base_ordered h hd hs hc hr
  change k < gridSize g c r at hk
  change j < gridSize g d s at hj
  obtain rfl : c = d := by omega
  obtain rfl : r = s := by omega
  obtain rfl : l = m := by omega
  obtain rfl : k = j := Nat.add_left_cancel he
  rfl

end JPEG2000.Spec.RoundTrip
