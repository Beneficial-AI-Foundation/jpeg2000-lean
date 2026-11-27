import Spec.WideHeaderBounds
import Spec.NativeOutput

/-!
# Containment on parsed reduced component grids (Plan.md §§4, 5, 7, T.800 B.2–B.3)

The same component separation and resolution divisor apply to each of the four
image and tile endpoints. Their monotonicity preserves the clipping inequalities.
-/

namespace JPEG2000.Spec.NativePlacement

open JPEG2000.NativeOutput Header
open JPEG2000.Spec.Tier2Equiv (bind_ok)

private theorem map_geometry {α β : Type} (f : α → Except Error β)
    (xs : Array α) (ys : Array β) (ok : xs.mapM f = .ok ys) :
    ys.size = xs.size ∧ ∀ i (hi : i < xs.size) (ho : i < ys.size), f xs[i] = .ok ys[i] := by
  have aux (as : List α) (bs : List β) (h : as.mapM f = .ok bs) :
      bs.length = as.length ∧ ∀ i (ha : i < as.length) (hb : i < bs.length), f as[i] = .ok bs[i] := by
    induction as generalizing bs with
    | nil => cases h; simp
    | cons a as ih =>
      rw [List.mapM_cons] at h
      obtain ⟨b, first, h⟩ := bind_ok h
      obtain ⟨bs, rest, h⟩ := bind_ok h
      cases h
      obtain ⟨sz, idx⟩ := ih bs rest
      refine ⟨by simp [sz], ?_⟩
      intro i ha hb
      cases i with
      | zero => exact first
      | succ i => exact idx i (by simpa using ha) (by simpa using hb)
  rw [Array.mapM_eq_mapM_toList] at ok
  cases h : xs.toList.mapM f with
  | error => rw [h] at ok; contradiction
  | ok bs =>
    rw [h] at ok; cases ok
    obtain ⟨sz, idx⟩ := aux _ _ h
    refine ⟨by simpa using sz, ?_⟩
    intro i hi ho
    have e := idx i (by simpa using hi) (by simpa using ho)
    simpa using e

private theorem layout_components {h : Header} {tile : Nat} {g : Progression.Layout} {coding : Coding}
    (ok : Progression.Layout.ofHeader h tile = .ok (g, coding)) :
    g.numComps = h.siz.components.size ∧ ∀ i (_hi : i < g.numComps),
      JPEG2000.Tier2.Geometry.ofHeader h tile i = .ok (g.comp i) := by
  unfold Progression.Layout.ofHeader at ok
  dsimp only at ok
  split at ok <;> try contradiction
  obtain ⟨cs, hm, ok⟩ := bind_ok ok
  cases ok
  obtain ⟨sz, idx⟩ := map_geometry _ _ _ hm
  refine ⟨by simpa [Progression.Layout.numComps, Marker.SIZ.csiz] using sz, ?_⟩
  intro i hi
  change i < cs.size at hi
  have h := idx i (sz ▸ hi) hi
  simpa [Progression.Layout.comp, Array.getD_eq_getD_getElem?, hi] using h

private theorem cdiv_mono {a b : Nat} (le : a ≤ b) (d : Nat) : cdiv a d ≤ cdiv b d :=
  Nat.div_le_div_right (Nat.sub_le_sub_right (Nat.add_le_add_right le d) 1)

/-- Every parsed tile layout has exactly the SIZ components in order. At any reduction,
its ordered B-14 endpoints lie within the corresponding reduced image rectangle. -/
theorem tile_grid {L : Limits} {data : ByteArray} {h : Header} {tile red : Nat}
    {g : Progression.Layout} {coding : Coding} (parsed : Header.parse L data = .ok h)
    (ok : Progression.Layout.ofHeader h tile = .ok (g, coding)) :
    ∃ count : g.numComps = h.siz.components.size, ∀ i (hi : i < g.numComps),
      let d := JPEG2000.Decode.compImageRect h.siz (h.siz.components[i]'(count ▸ hi)) red
      let r := Assemble.reduceRect (g.comp i).rect red
      d.x0 ≤ r.x0 ∧ r.x0 ≤ r.x1 ∧ r.x1 ≤ d.x1 ∧
      d.y0 ≤ r.y0 ∧ r.y0 ≤ r.y1 ∧ r.y1 ≤ d.y1 := by
  obtain ⟨count, idx⟩ := layout_components ok
  refine ⟨count, fun i hi => ?_⟩
  have ord := (WideHeaderBounds.parsed_component_bounds parsed ok ⟨i, hi⟩ red).2
  have geom := idx i hi
  have rect : (g.comp i).rect = compRect (tileRect h.siz tile) (h.siz.components[i]'(count ▸ hi)) := by
    unfold JPEG2000.Tier2.Geometry.ofHeader at geom
    dsimp only at geom
    split at geom <;> try contradiction
    rw [Array.getElem?_eq_getElem (count ▸ hi)] at geom
    dsimp only at geom
    split at geom <;> try contradiction
    exact congrArg JPEG2000.Tier2.Geometry.TileCompGeom.rect (Except.ok.inj geom).symm
  dsimp only
  refine ⟨?_, ord.1, ?_, ?_, ord.2, ?_⟩
  all_goals rw [rect]; apply cdiv_mono; apply cdiv_mono
  · exact Nat.le_max_right ..
  · exact Nat.min_le_right ..
  · exact Nat.le_max_right ..
  · exact Nat.min_le_right ..

private theorem loop_all {α : Type} (P : Nat → Prop) (f : Nat → α → Except Error (ForInStep α))
    (step : ∀ i b z, f i b = .ok z → ∃ b', z = .yield b' ∧ P i)
    (xs : List Nat) (b out : α) (ok : forIn xs b f = .ok out) : ∀ i ∈ xs, P i := by
  induction xs generalizing b with
  | nil => simp
  | cons i is ih =>
    rw [List.forIn_cons] at ok
    obtain ⟨z, hz, tail⟩ := bind_ok ok
    obtain ⟨b', rfl, head⟩ := step _ _ _ hz
    exact List.forall_mem_cons.mpr ⟨head, ih b' tail⟩

/-- The successful specification tile already checked the reduction against each
effective component's decomposition levels, before MCT and G.1. -/
theorem tile_reduction {L : Limits} {h : Header} {t red : Nat} {g : Progression.Layout}
    {coding : Coding} {tcb : Option Spec.Tier2.TileOut} {tile : Decode.TileOut}
    (layoutOk : Progression.Layout.ofHeader h t = .ok (g, coding))
    (decoded : Decode.decodeTile L h t red tcb = .ok tile) :
    ∀ i, i < g.numComps → red ≤ (g.comp i).params.levels := by
  unfold Decode.decodeTile Decode.tileWith at decoded
  rw [layoutOk] at decoded
  simp only [Equiv.ok_bind] at decoded
  obtain ⟨_, _, decoded⟩ := bind_ok decoded
  obtain ⟨_, loop, _⟩ := bind_ok decoded
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at loop
  have all := loop_all (fun i => red ≤ (g.comp i).params.levels) _ (by
    intro i b z step
    obtain ⟨⟨_, _⟩, cell, step⟩ := bind_ok step
    cases step
    refine ⟨_, rfl, ?_⟩
    by_cases tooHigh : red > (g.comp i).params.levels
    · simp only [Decode.tileComp, tooHigh, ↓reduceIte] at cell
      contradiction
    · omega) _ _ _ loop
  intro i hi
  apply all i
  simpa [List.mem_range', Std.Legacy.Range.size] using hi

end JPEG2000.Spec.NativePlacement
