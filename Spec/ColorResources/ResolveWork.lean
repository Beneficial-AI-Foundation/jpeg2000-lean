import Spec.ColorResources.Layout
import Spec.ColorResources.Palette

/-!
# Channel-layout work at the public decoder (Plan.md §4, S3; T.800 Annex I)

The JP2 mapping determines the size of the layout even when the raw component
count differs. ICC signatures request at most fifteen associations. Unknown
spaces derive their count from the channel definitions. The meter counts only
layout work and preserves errors from earlier resolution steps.
-/

namespace JPEG2000.Spec.ColorResources

open JPEG2000 JPEG2000.Box JPEG2000.Color

private theorem identity_count (n : Nat) : (identityMapping n).sources.size = n := by
  simp [identityMapping]

private theorem mapping_count (L : Limits) (p : Palette) (cm : ComponentMapping)
    (n : Nat) (m : Mapping) (ok : mappingOf L p cm n = .ok m) :
    m.sources.size ≤ L.maxComponents := by
  unfold mappingOf at ok
  obtain ⟨⟨⟩,hc,ok⟩ := Tier2Equiv.bind_ok ok
  have limit := (L.check_eq_ok_iff _ _ _).mp hc
  by_cases he : cm.isEmpty
  · simp [he,bind,Except.bind,throw] at ok
  · simp only [he, Bool.false_eq_true, ↓reduceIte] at ok
    obtain ⟨⟨⟩,_,ok⟩ := Tier2Equiv.bind_ok ok
    obtain ⟨ss,hs,eq⟩ := Tier2Equiv.bind_ok ok
    cases eq
    have len := channel_map_size hs
    have same : (fixWeirdCmap n p cm).size = cm.size := by
      unfold fixWeirdCmap
      split <;> simp
    exact (len.trans same) ▸ limit

private theorem identity_limit (L : Limits) (n : Nat)
    (ok : L.check (.at .color) .components n = .ok ()) :
    (identityMapping n).sources.size ≤ L.maxComponents := by
  rw [identity_count]
  exact (L.check_eq_ok_iff _ _ _).mp ok

private theorem checked_mapping (L : Limits) (h : Jp2Header) (n : Nat) (m : Mapping)
    (ok : resolveMapping L h n = .ok m) : m.sources.size ≤ L.maxComponents := by
  unfold resolveMapping at ok
  split at ok
  · exact mapping_count _ _ _ _ _ ok
  · obtain ⟨⟨⟩,hc,eq⟩ := Tier2Equiv.bind_ok ok
    cases eq
    exact identity_limit _ _ hc

private theorem colour_count (s : ColourSpace) (data : ByteArray) (d : Nat) :
    (s.numColours data).getD d ≤ max 15 d := by
  have hd := Nat.le_max_right 15 d
  have hf := Nat.le_max_left 15 d
  cases s <;> simp only [ColourSpace.numColours]
  case enumerated cs params =>
    unfold enumColours
    split <;> simp only [Option.getD] <;> omega
  case icc r =>
    unfold iccColours
    dsimp only
    repeat' split
    all_goals simp only [Option.getD] at * <;> omega
  all_goals simp only [Option.getD] <;> omega

private theorem budget_mono {n N d D m M : Nat} (hn : n ≤ N) (hd : d ≤ D) (hm : m ≤ M) :
    layoutBudget n d m ≤ layoutBudget N D M := by
  have h₀ := Nat.mul_le_mul (Nat.sub_le_sub_right hd 1) (Nat.add_le_add_right hd 3)
  have h₁ := Nat.mul_le_mul hm (show 1+3*d ≤ 1+3*D by omega)
  have h₂ := Nat.mul_le_mul hn (Nat.add_le_add_left hm 1)
  unfold layoutBudget
  omega

private def selection (L : Limits) (hdr : Option Jp2Header) (n : Nat) :
    Except Error (ColourSpace × Mapping × Option (Array ChannelDef)) :=
  match hdr with
  | none => do
    L.check (.at .color) .components n
    pure (.unknown, identityMapping n, none)
  | some h => do
    let m ← resolveMapping L h n
    pure (resolveColourSpace h, m, h.cdef)

private theorem selected (L : Limits) (hdr : Option Jp2Header) (n : Nat)
    (s : ColourSpace) (m : Mapping) (defs : Option (Array ChannelDef))
    (ok : selection L hdr n = .ok (s,m,defs)) :
    m.sources.size ≤ L.maxComponents ∧ defs = hdr.bind (·.cdef) := by
  cases hdr with
  | none =>
    obtain ⟨⟨⟩,hc,eq⟩ := Tier2Equiv.bind_ok ok
    cases eq
    exact ⟨identity_limit _ _ hc,rfl⟩
  | some h =>
    obtain ⟨mapping,hc,eq⟩ := Tier2Equiv.bind_ok ok
    cases eq
    exact ⟨checked_mapping _ _ _ _ hc,rfl⟩

/-- Run colour resolution and record the channel-layout charge, including a
partially processed CDEF on error. A failure before layout has zero charge. -/
def measuredResolveLayout (L : Limits) (data : ByteArray) (hdr : Option Jp2Header)
    (comps : Array Marker.Component) : Except Error Info × Nat :=
  match selection L hdr comps.size with
  | .error e => (.error e,0)
  | .ok (s,m,defs) =>
    let (out,work) := measuredLayout (s.numColours data) m.sources.size defs
    (out.map (fun layout => ⟨s,m,m.formats (componentFormats comps),layout⟩),work)

/-- Accepted palette mappings, raw identity mappings and recognised colour
spaces bound layout work for every result of the production resolver. -/
theorem resolve_layout_work (L : Limits) (data : ByteArray) (hdr : Option Jp2Header)
    (comps : Array Marker.Component) :
    let d := ((hdr.bind (·.cdef)).getD #[]).size
    let run := measuredResolveLayout L data hdr comps
    run.1 = resolve L data hdr comps ∧ run.2 ≤ layoutBudget L.maxComponents d (max 15 d) := by
  have original : resolve L data hdr comps = (do
      let (s,m,defs) ← selection L hdr comps.size
      let layout ← channelLayout (s.numColours data) m.sources.size defs
      pure ⟨s,m,m.formats (componentFormats comps),layout⟩) := by
    cases hdr <;> simp [resolve,selection]
  rw [original]
  unfold measuredResolveLayout
  cases h : selection L hdr comps.size with
  | error e => exact ⟨rfl,Nat.zero_le _⟩
  | ok v =>
    obtain ⟨s,m,defs⟩ := v
    obtain ⟨hn,rfl⟩ := selected _ _ _ _ _ _ h
    obtain ⟨out,work⟩ := layout_work (s.numColours data) m.sources.size (hdr.bind (·.cdef))
    refine ⟨?_,Nat.le_trans work (budget_mono hn (Nat.le_refl _) (colour_count _ _ _))⟩
    simp only [bind,Except.bind]
    rw [← out]
    cases (measuredLayout (s.numColours data) m.sources.size (hdr.bind (·.cdef))).1 <;> rfl

/-- A measured colour-resolution failure after native decoding is the exact
error delivered by the public display decoder, for every display option. -/
theorem decode_layout_error (L : Limits) (data : ByteArray) (opts : DecodeOptions)
    (d : CodestreamImage) (raw : decodeCodestream L data opts.reduce = .ok d) (e : Error)
    (failed : (measuredResolveLayout L data (d.header.container.bind (·.header))
      d.header.siz.components).1 = .error e) : JPEG2000.decode L data opts = .error e := by
  rw [(resolve_layout_work ..).1] at failed
  simp only [JPEG2000.decode,raw,bind,Except.bind,failed]

/-- Charge the actual layout stage of a display request. Earlier native or
mapping failure contributes zero. Later display errors keep the full charge. -/
def imageLayoutCharge (L : Limits) (data : ByteArray) (opts : DecodeOptions) : Nat :=
  match decodeCodestream L data opts.reduce with
  | .error _ => 0
  | .ok d => (measuredResolveLayout L data (d.header.container.bind (·.header))
      d.header.siz.components).2

/-- A uniform layout bound at the byte-input API, including failed requests.
Both the CDEF record count and the possible ICC association count are
discharged at the parser and resolver that feed the layout. -/
theorem image_layout_work (L : Limits) (data : ByteArray) (opts : DecodeOptions) :
    imageLayoutCharge L data opts ≤ layoutBudget L.maxComponents 65535 65535 := by
  unfold imageLayoutCharge
  cases raw : decodeCodestream L data opts.reduce with
  | error _ => exact Nat.zero_le _
  | ok d =>
    have hd := retained_cdef raw
    exact Nat.le_trans (resolve_layout_work L data _ _).2
      (budget_mono (Nat.le_refl _) hd (Nat.max_le.mpr ⟨by decide,hd⟩))

end JPEG2000.Spec.ColorResources
