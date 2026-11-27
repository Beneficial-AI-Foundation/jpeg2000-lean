import Spec.NativeResources

/-!
# Palette construction and backing (Plan.md §§3–5, 7, S3; T.800 I.5.3.4–5)

The fold certificate tracks source channels, newly materialized cells and lookup columns
separately. The source of a lazy lookup can itself retain sample storage.
-/

namespace JPEG2000.Spec.ColorResources

open JPEG2000 JPEG2000.Color JPEG2000.Bytes

/-- Work charged for one mapped channel and its actual output record. -/
structure Mapped where
  /-- Channel appended by the mapper. -/
  channel : Color.Channel
  /-- Index samples charged by the palette area check, zero for a direct source. -/
  area : Nat
  /-- Entries constructed by this column lookup, zero for a direct source. -/
  rows : Nat
  /-- Actual source entry at this position in the mapping. -/
  source : Source

/-- The channel borrows an input, owns a four-byte palette raster, or captures its source
and a column of exact integers. The table charge also includes transient compact columns. -/
inductive MappedFrom (L : Limits) (m : Mapping) (comps : Array Color.Channel) : Mapped → Prop
  | direct (ch : Color.Channel) (i : Nat) (atIndex : comps[i]? = some ch) :
      MappedFrom L m comps ⟨ch, 0, 0, .direct i⟩
  | palette (src ch : Color.Channel) (i : Nat) (atIndex : comps[i]? = some src) (p : Box.Palette) (col : Nat)
      (palette : m.palette = some p)
      (rows : (paletteColumn p col).size ≤ L.maxPaletteEntries)
      (width : ch.plane.width = src.plane.width) (height : ch.plane.height = src.plane.height)
      (storage : (∃ dst : Plane, ch.plane = .compact dst ∧
          dst.data.size = 4 * (src.plane.width * src.plane.height) ∧
          ∃ indices, src.plane.compact? = some indices ∧
            palettePlane L ((paletteColumn p col).map Int32.ofInt) indices = .ok dst) ∨
        ch.plane = indexedPlane (paletteColumn p col) src.plane) :
      MappedFrom L m comps ⟨ch, src.plane.width * src.plane.height, (paletteColumn p col).size, .palette i col⟩

private theorem compact_dims {s : SamplePlane} {p : Plane} (ok : s.compact? = some p) :
    p.width = s.width ∧ p.height = s.height := by
  cases s with
  | compact q => cases ok; exact ⟨rfl, rfl⟩
  | view w h f => cases ok
  | native c =>
    cases c with | mk r f hd st hv =>
      cases st <;> cases ok
      exact ⟨rfl, rfl⟩

private theorem map_dims (tbl : Array Int32) (src : Plane) :
    ∀ k dst i, (mapPlane tbl src dst i k).width = dst.width ∧
      (mapPlane tbl src dst i k).height = dst.height
  | 0, _, _ => ⟨rfl, rfl⟩
  | k+1, dst, i => by
    unfold mapPlane
    split <;> first | exact ⟨rfl, rfl⟩ | split
    · exact map_dims tbl src k _ _
    · exact ⟨rfl, rfl⟩

private theorem step {L : Limits} {m : Mapping} {cs acc : Array Color.Channel}
    {n : Nat} {e : Source × Format} {res : Array Color.Channel × Nat}
    (hn : n ≤ L.maxWorkSamples) (ok : mapSource L m cs (acc, n) e = .ok res) :
    ∃ a, MappedFrom L m cs a ∧ a.source = e.1 ∧ res = (acc.push a.channel, n + a.area) ∧
      a.rows ≤ L.maxPaletteEntries ∧ n + a.area ≤ L.maxWorkSamples := by
  obtain ⟨s, f⟩ := e
  cases s with
  | direct c =>
    simp only [mapSource] at ok
    split at ok <;> try contradiction
    rename_i ch hch
    cases ok
    exact ⟨_, .direct ch c hch, rfl, rfl, Nat.zero_le _, hn⟩
  | palette c col =>
    simp only [mapSource] at ok
    split at ok <;> try contradiction
    rename_i src hs
    split at ok <;> try contradiction
    rename_i p hp
    obtain ⟨u, work, h⟩ := Tier2Equiv.bind_ok ok
    obtain ⟨v, rows, h⟩ := Tier2Equiv.bind_ok h
    have ht : (paletteColumn p col).size ≤ L.maxPaletteEntries := by
      simpa [paletteColumn, Limits.bound] using (Limits.check_eq_ok_iff ..).mp rows
    split at h
    · rename_i q hq
      split at h
      · obtain ⟨plane, hplane, hr⟩ := Tier2Equiv.bind_ok h
        cases hr
        have ck : L.check (.at .color) .workSamples (q.width*q.height) = .ok () :=
          (Limits.check_eq_ok_iff ..).2 (by
            have bound : n + src.plane.width*src.plane.height ≤ L.maxWorkSamples :=
              (Limits.check_eq_ok_iff ..).mp work
            have eq := compact_dims hq
            rw [eq.1, eq.2]
            exact Nat.le_trans (Nat.le_add_left ..) bound)
        simp only [Functor.map, Except.map, palettePlane, Plane.zeroChecked, bind, Except.bind,
          ck, pure, Except.pure, Except.ok.injEq] at hplane
        subst plane
        let dst := mapPlane ((paletteColumn p col).map Int32.ofInt) q (Plane.zero q.width q.height) 0
          (q.width*q.height)
        have d := map_dims ((paletteColumn p col).map Int32.ofInt) q (q.width*q.height)
          (Plane.zero q.width q.height) 0
        have eq := compact_dims hq
        refine ⟨_, .palette src ⟨.compact dst,f⟩ c hs p col hp ht
          (d.1.trans eq.1) (d.2.trans eq.2) (.inl ⟨dst, rfl, ?_, q, hq, ?_⟩), rfl, rfl, ht,
          (Limits.check_eq_ok_iff ..).mp work⟩
        · rw [Plane.size_eq]
          exact congrArg (4 * ·) (congr (congrArg Nat.mul (d.1.trans eq.1)) (d.2.trans eq.2))
        · simp [palettePlane, Plane.zeroChecked, ck, bind, Except.bind, pure, Except.pure, dst]
      · cases h
        exact ⟨_, .palette src ⟨indexedPlane (paletteColumn p col) src.plane,f⟩ c hs p col hp ht rfl rfl (.inr rfl),
          rfl, rfl, ht, (Limits.check_eq_ok_iff ..).mp work⟩
    · cases h
      exact ⟨_, .palette src ⟨indexedPlane (paletteColumn p col) src.plane,f⟩ c hs p col hp ht rfl rfl (.inr rfl),
        rfl, rfl, ht, (Limits.check_eq_ok_iff ..).mp work⟩

/-- All rows in order, with aggregate checked palette work and column-table entries. -/
structure MappingWithin (L : Limits) (m : Mapping) (cs out : Array Color.Channel) : Prop where
  /-- Number of sources admitted before constructing the channel arrays. -/
  count : m.sources.size ≤ L.maxComponents
  /-- One row per source, in exactly the order of the actual CMAP or identity mapping. -/
  trace : ∃ xs : List Mapped, xs.map Mapped.channel = out.toList ∧
    (∀ x ∈ xs, MappedFrom L m cs x) ∧ xs.map Mapped.source = m.sources.toList ∧ xs.length = m.sources.size ∧
    (xs.map Mapped.area).sum ≤ L.maxWorkSamples ∧
    (xs.map Mapped.rows).sum ≤ m.sources.size * L.maxPaletteEntries

/-- A successful mapping supplies one certificate per output in source order. -/
theorem applyMapping_resources {L : Limits} {m : Mapping} {cs out : Array Color.Channel}
    (ok : applyMapping L m cs = .ok out) : MappingWithin L m cs out := by
  unfold applyMapping at ok
  obtain ⟨_, count, ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨⟨result, total⟩, fold, h⟩ := Tier2Equiv.bind_ok ok
  change Except.ok result = Except.ok out at h
  injection h with he
  subst out
  rw [← Array.foldlM_toList] at fold
  have go (es : List (Source × Format)) (acc : Array Color.Channel) (n : Nat)
      (hn : n ≤ L.maxWorkSamples) (h : es.foldlM (mapSource L m cs) (acc,n) = .ok (result,total)) :
      ∃ xs : List Mapped, result.toList = acc.toList ++ xs.map Mapped.channel ∧
        (∀ x ∈ xs, MappedFrom L m cs x) ∧ xs.map Mapped.source = es.map Prod.fst ∧ xs.length = es.length ∧
        n + (xs.map Mapped.area).sum ≤ L.maxWorkSamples ∧
        (xs.map Mapped.rows).sum ≤ es.length * L.maxPaletteEntries := by
    induction es generalizing acc n with
    | nil => cases h; exact ⟨[], by simp, by simp, rfl, rfl, by simpa, by simp⟩
    | cons e es ih =>
      rw [List.foldlM_cons] at h
      obtain ⟨q, hq, hh⟩ := Tier2Equiv.bind_ok h
      obtain ⟨a, ha, source, rfl, hr, hw⟩ := step hn hq
      obtain ⟨xs, hx, all, sources, len, work, tables⟩ := ih _ _ hw hh
      refine ⟨a :: xs, by simpa using hx, ?_, by simp [sources, source], by simp [len], ?_, ?_⟩
      · intro x mem
        rcases List.mem_cons.mp mem with rfl | h
        · exact ha
        · exact all _ h
      · simpa [← Nat.add_assoc] using work
      · simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
        omega
  obtain ⟨xs, hx, all, sources, len, work, tables⟩ := go _ #[] 0 (Nat.zero_le _) fold
  refine ⟨(Limits.check_eq_ok_iff ..).mp count, xs, by simpa using hx.symm, all, ?_,
    by simpa [Mapping.formats] using len, by simpa using work, by simpa [Mapping.formats] using tables⟩
  rw [sources, Array.toList_zip, List.map_fst_zip (by simp [Mapping.formats])]

/-- Physical bytes of freshly allocated palette sample buffers for this row of the
certificate. Direct references and lazy lookups allocate their sample backing upstream. -/
def Mapped.freshBytes (x : Mapped) : Nat :=
  if x.area = 0 then 0 else
    match x.channel.plane with
    | .compact p => p.data.size
    | _ => 0

private theorem mapped_fresh {L m cs x} (h : MappedFrom L m cs x) :
    x.freshBytes ≤ 4*x.area := by
  cases h with
  | direct ch i atIndex => simp [Mapped.freshBytes]
  | palette src ch i atIndex p col hp rows hw hh storage =>
    rcases storage with ⟨dst, eq, size, _⟩ | eq
    · simp [Mapped.freshBytes, eq, size]; split <;> omega
    · simp [Mapped.freshBytes, eq, indexedPlane]

/-- Aggregate physical bytes of the actual compact palette rasters, including copies
that a subsequent conversion can release. Source backing and retained lookup columns
are accounted for separately in the mapping certificate. -/
theorem mapping_backing {L m cs out} (h : MappingWithin L m cs out) :
    ∃ xs : List Mapped, xs.map Mapped.channel = out.toList ∧
      (∀ x ∈ xs, MappedFrom L m cs x) ∧ xs.map Mapped.source = m.sources.toList ∧
      (xs.map Mapped.freshBytes).sum ≤ 4*L.maxWorkSamples ∧
      (xs.map Mapped.rows).sum ≤ L.maxComponents * L.maxPaletteEntries := by
  obtain ⟨xs, eq, all, sources, len, area, rows⟩ := h.trace
  have bound : (xs.map Mapped.freshBytes).sum ≤ 4*(xs.map Mapped.area).sum := by
    clear eq rows area len sources
    induction xs with
    | nil => simp
    | cons x xs ih =>
      have head := mapped_fresh (all x (by simp))
      have tail := ih (fun z hz => all z (by simp [hz]))
      simp only [List.map_cons, List.sum_cons, Nat.mul_add]
      omega
  exact ⟨xs, eq, all, sources, Nat.le_trans bound (Nat.mul_le_mul_left _ area),
    Nat.le_trans rows (Nat.mul_le_mul_right _ h.count)⟩

-- Neither a zero height nor a zero width exempts an index column from its limit.
private def emptyMapping (w h : Nat) :=
  let src : Color.Channel := ⟨.view w h (fun _ => 0), ⟨38, false, 1, 1⟩⟩
  let p : Box.Palette := ⟨2, 1, #[7], #[0, 255]⟩
  mapSource {maxPaletteEntries := 1} ⟨#[.palette 0 0], some p⟩ #[src] (#[], 0) (.palette 0 0, src.format)

example : emptyMapping 0 5 = .error (.limitExceeded (.at .color) .paletteEntries 2 1) := rfl
example : emptyMapping 7 0 = .error (.limitExceeded (.at .color) .paletteEntries 2 1) := rfl

end JPEG2000.Spec.ColorResources
