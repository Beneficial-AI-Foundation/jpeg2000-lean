import Spec.ColorResources
import Spec.ColorResources.MappingResolve

/-!
# The metered public mapping continuation (Plan.md §§3–5, 7, S3; T.800 Annex I)

The channel fold carries its accumulated palette area through the first error.
The raw channel descriptors, formats and zipped source/format array are built
before the fold. Direct channels borrow their original raster. A wide palette
channel owns a lookup column and defers its per-sample lookup to the consumer.
-/

namespace JPEG2000.Spec.ColorResources.MappingPrefix

open JPEG2000 JPEG2000.Color JPEG2000.Box JPEG2000.Bytes

private def fits32 (v : Int) : Bool := -2147483648 ≤ v && v ≤ 2147483647

private def columnCharge (p : Palette) (col : Nat) (plane : SamplePlane) : Nat :=
  let tbl := paletteColumn p col
  -- Range nodes, row indices, entry reads/conversions and exact column slots.
  6*p.ne + match plane.compact? with
    | none => 0
    | some _ => scan (fun v => !fits32 v) (fun _ => 1) tbl.toList +
        (if tbl.all fits32 then 2*tbl.size else 0)

private theorem column_le (p : Palette) (col : Nat) (plane : SamplePlane) :
    columnCharge p col plane ≤ 9*p.ne := by
  let tbl := paletteColumn p col
  have hv := scan_le (fun v => !fits32 v) (fun _ => 1) 1 (fun _ => Nat.le_refl _) tbl.toList
  have ht : tbl.size = p.ne := by simp [tbl,paletteColumn]
  simp only [Array.length_toList, Nat.mul_one] at hv
  change 6*p.ne + (match plane.compact? with
    | none => 0
    | some _ => scan (fun v => !fits32 v) (fun _ => 1) tbl.toList +
      (if tbl.all fits32 then 2*tbl.size else 0)) ≤ _
  cases plane.compact? with
  | none => change 6*p.ne+0 ≤ _; omega
  | some q =>
    by_cases h : tbl.all fits32
    · simp only [h, ↓reduceIte]; omega
    · simp only [h, Bool.false_eq_true, ↓reduceIte]; omega

private def stepCharge (L : Limits) (m : Mapping) (cs : Array Color.Channel)
    (n : Nat) (s : Source) : Nat :=
  1 + match s with
    | .direct _ => 0
    | .palette i col =>
      match cs[i]?, m.palette with
      | some c, some p =>
        if n + c.plane.width*c.plane.height ≤ L.maxWorkSamples ∧ p.ne ≤ L.maxPaletteEntries
        then columnCharge p col c.plane else 0
      | _, _ => 0

private theorem step_le (L : Limits) (m : Mapping) (cs : Array Color.Channel) (n : Nat)
    (s : Source) : stepCharge L m cs n s ≤ 1+9*L.maxPaletteEntries := by
  unfold stepCharge
  apply Nat.add_le_add_left
  cases s with
  | direct => exact Nat.zero_le _
  | palette i col =>
    dsimp only
    split
    · rename_i c p _ _
      split
      · rename_i h
        exact Nat.le_trans (column_le ..) (Nat.mul_le_mul_left 9 h.2)
      · exact Nat.zero_le _
    · exact Nat.zero_le _

private abbrev State := Array Color.Channel × Nat

private theorem map_progress {L m cs} {st next : State} {e : Source × Format}
    (hn : st.2 ≤ L.maxWorkSamples) (ok : mapSource L m cs st e = .ok next) :
    st.2 ≤ next.2 ∧ next.2 ≤ L.maxWorkSamples := by
  obtain ⟨acc,n⟩ := st
  obtain ⟨s,f⟩ := e
  cases s with
  | direct =>
    simp only [mapSource] at ok
    split at ok <;> cases ok
    exact ⟨Nat.le_refl _,hn⟩
  | palette =>
    simp only [mapSource] at ok
    split at ok <;> try contradiction
    split at ok <;> try contradiction
    obtain ⟨_,hw,ok⟩ := Tier2Equiv.bind_ok ok
    obtain ⟨_,_,ok⟩ := Tier2Equiv.bind_ok ok
    split at ok <;> (try split at ok)
    all_goals first | (obtain ⟨_,_,ok⟩ := Tier2Equiv.bind_ok ok; cases ok) | cases ok
    all_goals exact ⟨Nat.le_add_right ..,(Limits.check_eq_ok_iff ..).mp hw⟩

-- A completed compact palette row reserves and zero-fills four bytes, reads
-- four index bytes, looks up one entry, and writes four bytes per cell.
-- mapSource has no fallible operation after the zeroChecked allocation.
private def rasterCharge (s : Source) (old : Nat) (next : State) :=
  match s, next.1.back? with
  | .palette .., some ⟨.compact _,_⟩ => 17*(next.2-old)
  | _, _ => 0

private theorem raster_le (s : Source) (old : Nat) (next : State) :
    rasterCharge s old next ≤ 17*(next.2-old) := by
  unfold rasterCharge
  split <;> first | exact Nat.le_refl _ | exact Nat.zero_le _

private def rows (L : Limits) (m : Mapping) (cs : Array Color.Channel) :
    List (Source × Format) → State → Except Error State × Nat
  | [], st => (.ok st,0)
  | e::es, st =>
    let charge := stepCharge L m cs st.2 e.1
    match mapSource L m cs st e with
    | .error err => (.error err,charge)
    | .ok next =>
      let rest := rows L m cs es next
      (rest.1, charge + 1 + rasterCharge e.1 st.2 next + rest.2)

private theorem rows_spec (L : Limits) (m : Mapping) (cs : Array Color.Channel)
    (es : List (Source × Format)) (st : State) (hn : st.2 ≤ L.maxWorkSamples) :
    (rows L m cs es st).1 = es.foldlM (mapSource L m cs) st ∧
    (rows L m cs es st).2 ≤ es.length*(2+9*L.maxPaletteEntries) + 17*(L.maxWorkSamples-st.2) := by
  induction es generalizing st with
  | nil => exact ⟨rfl,Nat.zero_le _⟩
  | cons e es ih =>
    have hs := step_le L m cs st.2 e.1
    rw [rows, List.foldlM_cons]
    cases h : mapSource L m cs st e with
    | error err =>
      refine ⟨rfl,?_⟩
      rw [List.length_cons,Nat.succ_mul]
      dsimp only
      omega
    | ok next =>
      obtain ⟨mono,cap⟩ := map_progress hn h
      obtain ⟨eq,hr⟩ := ih next cap
      have hw := raster_le e.1 st.2 next
      refine ⟨eq,?_⟩
      rw [List.length_cons,Nat.succ_mul]
      dsimp only
      omega

/-- Apply the production mapping with its original checks, one source lookup
per visited row, conditional column construction and compact raster writes. -/
def measuredMapping (L : Limits) (m : Mapping) (cs : Array Color.Channel) :
    Except Error (Array Color.Channel) × Nat :=
  match L.check (.at .color) .components m.sources.size with
  | .error e => (.error e,1)
  | .ok _ =>
    let fmts := m.formats (cs.map (·.format))
    let out := rows L m cs (m.sources.zip fmts).toList (#[],0)
    (out.1.map Prod.fst, 1 + 2*cs.size + 5*m.sources.size + out.2)

/-- Source slots and table work are bounded per admitted source. The raster
term is aggregate over the fold, including a prefix followed by rejection. -/
def mappingBudget (L : Limits) (c : Nat) :=
  1+2*c+5*L.maxComponents + L.maxComponents*(2+9*L.maxPaletteEntries) + 17*L.maxWorkSamples

/-- Exact erasure and a success-or-error bound for any input channel array. -/
theorem mapping_work (L : Limits) (m : Mapping) (cs : Array Color.Channel) :
    (measuredMapping L m cs).1 = applyMapping L m cs ∧
    (measuredMapping L m cs).2 ≤ mappingBudget L cs.size := by
  unfold measuredMapping applyMapping mappingBudget
  cases h : L.check (.at .color) .components m.sources.size with
  | error e => exact ⟨rfl,by dsimp only; omega⟩
  | ok u =>
    have hc : m.sources.size ≤ L.maxComponents := (Limits.check_eq_ok_iff ..).mp h
    let es := (m.sources.zip (m.formats (cs.map (·.format)))).toList
    have len : es.length = m.sources.size := by simp [es,Mapping.formats]
    obtain ⟨eq,hw⟩ := rows_spec L m cs es (#[],0) (Nat.zero_le _)
    simp only [Nat.sub_zero,len] at hw
    refine ⟨?_,?_⟩
    · change ((rows L m cs es (#[],0)).1.map Prod.fst) = _
      rw [eq,Array.foldlM_toList]
      simp only [bind,Except.bind]
      cases (m.sources.zip (m.formats (cs.map (·.format)))).foldlM (mapSource L m cs) (#[],0) <;> rfl
    · change 1+2*cs.size+5*m.sources.size + (rows L m cs es (#[],0)).2 ≤ _
      have := Nat.mul_le_mul_right (2+9*L.maxPaletteEntries) hc
      omega


/-- Select the same mapping and layout as the public decoder. When palette
expansion is disabled, it constructs both the identity sources and colour indices. -/
def choice (opts : DecodeOptions) (info : Info) (d : CodestreamImage) : Mapping × ChannelLayout :=
  if opts.applyPalette || info.mapping.palette.isNone then (info.mapping,info.layout)
  else (identityMapping (rawChannels d).size,⟨(List.range (rawChannels d).size).toArray,none,false,#[]⟩)

private def prepareCharge (opts : DecodeOptions) (info : Info) (d : CodestreamImage) : Nat :=
  2*d.comps.size + if opts.applyPalette || info.mapping.palette.isNone then 0 else 5*d.comps.size

/-- Resolve JP2 metadata and map the native channels, retaining the exact
arguments needed by the subsequent display continuation. -/
def nativeContinuation (L : Limits) (data : ByteArray) (opts : DecodeOptions)
    (d : CodestreamImage) : Except Error (Info × ChannelLayout × Array Color.Channel) := do
  let info ← resolve L data (d.header.container.bind Container.header) d.header.siz.components
  let (m,layout) := choice opts info d
  let cs ← applyMapping L m (rawChannels d)
  return (info,layout,cs)

/-- All reached work from a native success to the display continuation. The
layout contribution is the existing CDEF meter, including on its first error. -/
def measuredNative (L : Limits) (data : ByteArray) (opts : DecodeOptions)
    (d : CodestreamImage) : Except Error (Info × ChannelLayout × Array Color.Channel) × Nat :=
  let hdr := d.header.container.bind Container.header
  let resolved := measuredResolver L data hdr d.header.siz.components
  let work := resolved.2
  match resolved.1 with
  | .error e => (.error e,work)
  | .ok info =>
    let (m,layout) := choice opts info d
    let mapped := measuredMapping L m (rawChannels d)
    (mapped.1.map (fun cs => (info,layout,cs)), work + prepareCharge opts info d + mapped.2)

/-- Explicit bound for resolver, layout, format arrays, mapping decisions,
table expansions and raster accesses before the display stage. -/
def metadataBudget (L : Limits) (b : Nat) :=
  resolverBudget L b + layoutBudget L.maxComponents 65535 65535 +
    7*L.maxComponents + mappingBudget L L.maxComponents

private theorem native_erases (L : Limits) (data : ByteArray) (opts : DecodeOptions)
    (d : CodestreamImage) : (measuredNative L data opts d).1 = nativeContinuation L data opts d := by
  unfold measuredNative measuredResolver nativeContinuation
  dsimp only
  rw [(resolve_layout_work ..).1]
  cases h : resolve L data (d.header.container.bind Container.header) d.header.siz.components with
  | error => rfl
  | ok info =>
    cases ml : choice opts info d with
    | mk m layout =>
      simp only [bind,Except.bind,ml]
      rw [(mapping_work ..).1]
      cases applyMapping L m (rawChannels d) <;> rfl

/-- The native-success continuation preserves the entire result, and bounds
work and logical allocation even when the final mapped channel rejects. The
CDEF cardinality also bounds the actual records retained before that rejection. -/
theorem native_mapping_work {L data opts d} (ok : decodeCodestream L data opts.reduce = .ok d) :
    (measuredNative L data opts d).1 = nativeContinuation L data opts d ∧
    (measuredNative L data opts d).2 ≤ metadataBudget L data.size ∧
    (((d.header.container.bind Container.header).bind Jp2Header.cdef).getD #[]).size ≤ 65535 := by
  obtain ⟨hc,hn,hd⟩ := retained_counts ok
  have hb := resolver_work hc (retained_palette ok) hn
  have hl := image_layout_work L data opts
  simp only [imageLayoutCharge,ok] at hl
  refine ⟨native_erases ..,?_,retained_cdef ok⟩
  unfold measuredNative measuredResolver metadataBudget
  dsimp only
  split
  · exact Nat.le_trans (Nat.add_le_add hb hl) (by omega)
  · rename_i info _
    have hp : prepareCharge opts info d ≤ 7*L.maxComponents := by
      unfold prepareCharge
      split
      · change 2*d.comps.size+0 ≤ _; omega
      · change 2*d.comps.size+5*d.comps.size ≤ _; omega
    cases ml : choice opts info d with
    | mk m lay =>
      have hw := (mapping_work L m (rawChannels d)).2
      have hm : mappingBudget L (rawChannels d).size ≤ mappingBudget L L.maxComponents := by
        simp only [mappingBudget,rawChannels,Array.size_map]
        omega
      exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hb hl) hp) (Nat.le_trans hw hm)

/-- Successful erasure identifies the resolved info, chosen layout and the
existing source-by-source backing certificate for the channels passed to display. -/
theorem native_mapping_success {L data opts d info layout cs}
    (ok : (measuredNative L data opts d).1 = .ok (info,layout,cs)) :
    resolve L data (d.header.container.bind Container.header) d.header.siz.components = .ok info ∧
    layout = (choice opts info d).2 ∧
    applyMapping L (choice opts info d).1 (rawChannels d) = .ok cs ∧
    MappingWithin L (choice opts info d).1 (rawChannels d) cs := by
  rw [native_erases] at ok
  obtain ⟨i,hi,rest⟩ := Tier2Equiv.bind_ok ok
  cases h : choice opts i d with
  | mk m lay =>
    simp only [h] at rest
    obtain ⟨mapped,hm,eq⟩ := Tier2Equiv.bind_ok rest
    cases eq
    exact ⟨hi,by simp [h],by simpa only [h] using hm,
      by simpa only [h] using applyMapping_resources hm⟩

/-- Measured byte-input prefix. Earlier native failures have zero metadata
charge. Success returns the native image and the inputs of the display stage. -/
def measuredPrefix (L : Limits) (data : ByteArray) (opts : DecodeOptions) :
    Except Error (CodestreamImage × Info × ChannelLayout × Array Color.Channel) × Nat :=
  match decodeCodestream L data opts.reduce with
  | .error e => (.error e,0)
  | .ok d =>
    let run := measuredNative L data opts d
    (run.1.map (Prod.mk d),run.2)

/-- Erasure of the byte-input prefix, including the first exact error, and
a uniform charge composable by addition with post-mapping display costs. -/
theorem image_mapping_work (L : Limits) (data : ByteArray) (opts : DecodeOptions) :
    (measuredPrefix L data opts).1 = (do
      let d ← decodeCodestream L data opts.reduce
      (nativeContinuation L data opts d).map (Prod.mk d)) ∧
    (measuredPrefix L data opts).2 ≤ metadataBudget L data.size := by
  unfold measuredPrefix
  cases h : decodeCodestream L data opts.reduce with
  | error => exact ⟨rfl,Nat.zero_le _⟩
  | ok d =>
    obtain ⟨he,hw,_⟩ := native_mapping_work (opts := opts) h
    exact ⟨congrArg (Except.map (Prod.mk d)) he,hw⟩

/-- A failed byte-input prefix yields the same error in the public decoder. -/
theorem decode_mapping_error {L data opts e} (h : (measuredPrefix L data opts).1 = .error e) :
    JPEG2000.decode L data opts = .error e := by
  rw [(image_mapping_work ..).1] at h
  unfold JPEG2000.decode
  cases raw : decodeCodestream L data opts.reduce with
  | error err => simpa [raw,bind,Except.bind] using h
  | ok d =>
    simp only [raw,bind,Except.bind,nativeContinuation] at h
    simp only [bind,Except.bind]
    cases hi : resolve L data (d.header.container.bind Container.header) d.header.siz.components with
    | error err => simpa [hi,Except.map] using h
    | ok info =>
      simp only [hi] at h
      cases ml : choice opts info d with
      | mk m layout =>
        simp only [ml] at h
        cases hm : applyMapping L m (rawChannels d) with
        | ok cs => simp [hm,Except.map,pure,Except.pure] at h
        | error err =>
          have eq : err = e := by simpa [hm,Except.map] using h
          subst e
          have hit : applyMapping L (choice opts info d).1 (rawChannels d) = .error err := by
            simpa only [ml] using hm
          dsimp only
          unfold choice rawChannels at hit
          rw [hit]

end JPEG2000.Spec.ColorResources.MappingPrefix
