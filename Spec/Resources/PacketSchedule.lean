import Spec.Progression

/-!
# Physical packet visits and POC iteration work

Plan.md §§3–5, 7, T.800 B.9 and B.12.1–2. A visit is one innermost packet
position of a progression volume, before the previous-volume test. Its charge
is one plus the number of previous volumes (an upper bound for the short-
circuit membership scan). Sorting precincts and preparing geometry are separate
operations. The list below is a proof model of the streaming iterator.
-/

namespace JPEG2000.Spec.Resources.PacketTraversal

open JPEG2000.Progression JPEG2000.Spec.Progression

/-- One innermost visit together with the exact POC list consulted at that visit. -/
structure Position where
  previous : List Volume
  packet : PacketId

/-- Ordered positions including duplicates across progression volumes. -/
def schedule (g : Layout) (prev : List Volume) : List Volume → List Position
  | [] => []
  | v :: vs => ((volume g v).map fun p => ⟨prev, p⟩) ++ schedule g (prev ++ [v]) vs

/-- Price of the prefix, including capacity for every previous-volume membership test. -/
def charge (ps : List Position) : Nat := (ps.map (fun p => p.previous.length + 1)).sum

/-- Count the tests performed by the short-circuit previous-volume search. -/
def inspectPrevious (p : PacketId) : List Volume → Nat × Bool
  | [] => (0, false)
  | v :: vs =>
    if v.contains p then (1, true)
    else let r := inspectPrevious p vs; (r.1 + 1, r.2)

/-- The counted search returns the exact `List.any` used by the production
iterator and stops within the number of previous volumes. -/
theorem inspectPrevious_any (p : PacketId) (prev : List Volume) :
    (inspectPrevious p prev).2 = prev.any (·.contains p) ∧
    (inspectPrevious p prev).1 ≤ prev.length := by
  induction prev with
  | nil => exact ⟨rfl, Nat.le_refl _⟩
  | cons v vs ih =>
    cases h : v.contains p <;> simp [inspectPrevious, h, ih.1, ih.2]

/-- The exact number of previous-volume membership tests across a physical prefix. -/
def membershipTests (ps : List Position) : Nat :=
  (ps.map (fun p => (inspectPrevious p.packet p.previous).1)).sum

/-- One visit plus each actually performed membership test fits the charged weight. -/
theorem visits_tests_le_charge (ps : List Position) : ps.length + membershipTests ps ≤ charge ps := by
  induction ps with
  | nil => exact Nat.le_refl _
  | cons p ps ih =>
    have h := (inspectPrevious_any p.packet p.previous).2
    simp only [membershipTests, charge, List.length_cons, List.map_cons, List.sum_cons] at *
    omega

/-- Physical visitation applies the callback only for a first occurrence. -/
def dispatch {α : Type} (f : α → PacketId → Except Error α) (a : α) (p : Position) :
    Except Error α := if p.previous.any (·.contains p.packet) then pure a else f a p.packet

private theorem volumes_fold {α : Type} (g : Layout) (wf : g.WF)
    (f : α → PacketId → Except Error α) (vs prev : List Volume) (a : α) :
    forVolumes g prev vs f a = (schedule g prev vs).foldlM (dispatch f) a := by
  induction vs generalizing prev a with
  | nil => rfl
  | cons v vs ih =>
    simp only [forVolumes, schedule, List.foldlM_append, List.foldlM_map,
      forVolume_eq_spec wf, ih, dispatch]

/-- Erasure of the physical schedule gives the production packet iterator on both outcomes. -/
theorem forPackets_schedule {α : Type} (g : Layout) (wf : g.WF) (o : Marker.Progression)
    (poc : Array Marker.PocEntry) (f : α → PacketId → Except Error α) (a : α) :
    forPackets g o poc f a = (schedule g [] (volumes g o poc)).foldlM (dispatch f) a :=
  volumes_fold g wf f _ [] a

private theorem fold_count {α : Type} (xs : List α) (f : α → Nat) (a : Nat) :
    xs.foldl (fun n x => n + f x) a = a + (xs.map f).sum := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.add_assoc]

private theorem sum_const {α : Type} (xs : List α) (n : Nat) :
    (xs.map fun _ => n).sum = xs.length * n := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.succ_mul, Nat.add_comm]

private theorem volume_length (g : Layout) (wf : g.WF) (v : Volume) :
    (volume g v).length = v.le g * (precRefs g v).length := by
  let w : Volume := { v with order := .rpcl }
  have perm : (volume g v).Perm (volume g w) := by
    rw [List.perm_ext_iff_of_nodup (c5_volume wf v).1 (c5_volume wf w).1]
    intro p
    rw [(c5_volume wf v).2, (c5_volume wf w).2]
    rfl
  rw [perm.length_eq]
  change (withLayers g w (posPrecincts g w)).length = _
  rw [← sortedPrecincts_eq wf]
  simp only [withLayers, List.length_flatMap, List.length_map, layerRange,
    List.length_range, sum_const]
  rw [Nat.mul_comm]
  simp [sortedPrecincts, w, precRefs, Volume.ce, Volume.re, Volume.le]

private theorem charge_cons_volume (g : Layout) (wf : g.WF) (v : Volume) (vs prev : List Volume) :
    charge (schedule g prev (v :: vs)) =
      (prev.length + 1) * v.le g * (precRefs g v).length +
        charge (schedule g (prev ++ [v]) vs) := by
  simp [charge, schedule, List.map_map, Function.comp_def, sum_const,
    volume_length g wf, Nat.mul_comm, Nat.mul_left_comm]

private theorem schedule_cost (g : Layout) (wf : g.WF) (vs prev : List Volume) :
    charge (schedule g prev vs) =
      ((vs.zipIdx prev.length).map (fun (v, j) => (j + 1) * v.le g * (precRefs g v).length)).sum := by
  induction vs generalizing prev with
  | nil => simp [charge, schedule]
  | cons v vs ih => simp [charge_cons_volume g wf, ih]

/-- The charge for all physical positions is exactly the quantity checked before iteration. -/
theorem schedule_charge (g : Layout) (wf : g.WF) (o : Marker.Progression) (poc : Array Marker.PocEntry) :
    charge (schedule g [] (volumes g o poc)) = iterationWork g o poc := by
  rw [schedule_cost g wf]
  simp [iterationWork, fold_count, precRefs, List.length_flatMap,
    ← List.sum_eq_foldl_nat]

end JPEG2000.Spec.Resources.PacketTraversal
