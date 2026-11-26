import Spec.NativeEquiv
import Spec.RoundTrip.Spec

/-!
# Reading the lossless round trip through the public codestream accessor

Plan.md §4 C9/C10. The encoder image is reconstructed by reading each native sample
in raster order after the inverse transforms and DC level shift (T.800 Annexes F and G).
Any missing sample propagates through the optional result.
-/

namespace JPEG2000.Spec.RoundTrip

open JPEG2000 JPEG2000.Encode JPEG2000.Spec.Decode

/-- Read a public image into the reference encoder's representation. -/
def encoderImageOfNative (d : CodestreamImage) : Option Encode.Image := do
  let comps ← d.comps.mapM fun c => do
    let samples ← (Array.range (c.width * c.height)).mapM c.get?
    pure ({ depth := c.depth, signed := c.signed, samples } : Encode.Component)
  return {
    width := d.header.siz.xsiz.toNat - d.header.siz.xosiz.toNat
    height := d.header.siz.ysiz.toNat - d.header.siz.yosiz.toNat
    comps }

private theorem mapM_list {α β : Type} (f : α → Option β) :
    ∀ (as : List α) (bs : List β), as.length = bs.length →
      (∀ i (ha : i < as.length) (hb : i < bs.length), f as[i] = some bs[i]) →
      as.mapM f = some bs := by
  intro as
  induction as with
  | nil =>
    intro bs hs _
    cases bs <;> simp_all
  | cons a as ih =>
    intro bs hs h
    cases bs with
    | nil => simp at hs
    | cons b bs =>
      have first := h 0 (by simp) (by simp)
      have tail := ih bs (by simpa using hs) (fun i ha hb =>
        h (i+1) (by simpa using ha) (by simpa using hb))
      simpa [List.mapM_cons, tail] using congrArg (fun x : Option β =>
        x.bind (fun v => some (v :: bs))) first

private theorem mapM_array {α β : Type} (f : α → Option β) (as : Array α) (bs : Array β)
    (hs : as.size = bs.size)
    (h : ∀ i (ha : i < as.size) (hb : i < bs.size), f as[i] = some bs[i]) :
    as.mapM f = some bs := by
  have hl := mapM_list f as.toList bs.toList (by simpa using hs)
    (fun i ha hb => h i (by simpa using ha) (by simpa using hb))
  simp [Array.mapM_eq_mapM_toList, hl]

/-- When C9's image relation holds and every decoded sample is reversible, checked
reads recover exactly the reference image including dimensions and component format. -/
theorem encoderImageOfNative_eq {d : CodestreamImage} {s : SpecImage} {reduce : Nat}
    (h : NativeEquiv.ImageRel reduce d s)
    (lossless : ∀ i (hi : i < s.comps.size) v, v ∈ s.comps[i].samples → v.reversible = true) :
    encoderImageOfNative d = some (encoderImageOfSpec s) := by
  let read (c : CodestreamComponent) : Option Encode.Component := do
    let samples ← (Array.range (c.width * c.height)).mapM c.get?
    pure { depth := c.depth, signed := c.signed, samples }
  let ofSpec (c : SpecComponent) : Encode.Component :=
    { depth := c.info.depth, signed := c.info.signed, samples := c.samples.map SpecSample.value }
  have comps : d.comps.mapM read = some (s.comps.map ofSpec) := by
    apply mapM_array
    · simpa using h.count
    intro i hd hs
    have hi : i < s.comps.size := by simpa using hs
    let rel := h.component i hd hi
    have values : (Array.range (d.comps[i].width * d.comps[i].height)).mapM d.comps[i].get? =
        some (s.comps[i].samples.map SpecSample.value) := by
      apply mapM_array
      · simpa using rel.size.symm
      intro j _ hs'
      have hj : j < s.comps[i].samples.size := by simpa using hs'
      obtain ⟨v, hv, agrees⟩ := rel.sample j hj
      have equal : v = s.comps[i].samples[j].value := by
        simpa only [NativeSample.Agrees, lossless i hi _ (Array.getElem_mem hj), ↓reduceIte] using agrees
      simpa only [Array.getElem_range, Array.getElem_map, equal] using hv
    obtain ⟨_, _, _, _, depth, signed, _, _⟩ := rel.metadata
    simp [read, ofSpec, values, depth, signed]
  change (d.comps.mapM read >>= _) = _
  rw [comps]
  simp [encoderImageOfSpec, ofSpec, h.header]

/-- Lossless native readback under the numerical encoder and output budgets, given
the public C9 result on the actual encoded bytes at reduction zero. -/
theorem native_roundtrip_of_c9 {L : Limits} {p : Params} {img : Encode.Image} {e : Encoded}
    (he : encodeDetailed p img = .ok e) (hrev : p.reversible = true)
    (fits : HeaderFits L p img e.guardBits e.exponents e.codestream.size)
    (perBlock : 109 ≤ L.maxPassesPerCodeBlock)
    (passes : (e.blocks.toList.map BlockInfo.numPasses).sum ≤ L.maxCodingPasses)
    (work : img.comps.size * (img.width * img.height) ≤ L.maxWorkSamples)
    (bytes : (img.comps.toList.map fun c => img.width * img.height *
      Header.bytesPerSample c.depth).sum ≤ L.maxDecodedBytes)
    (agreement : NativeEquiv.Agrees L e.codestream 0) :
    ∃ d, decodeCodestream L e.codestream 0 = .ok d ∧ encoderImageOfNative d = some img := by
  obtain ⟨s, hs, image, reversible⟩ :=
    spec_roundtrip_lossless_with_limits he hrev fits perBlock passes work bytes
  unfold NativeEquiv.Agrees at agreement
  rw [hs] at agreement
  cases hd : decodeCodestream L e.codestream 0 with
  | error err => simp [hd, Tier2Equiv.Res] at agreement
  | ok d =>
    rw [hd] at agreement
    exact ⟨d, rfl, (encoderImageOfNative_eq agreement reversible).trans (congrArg some image)⟩

/-- The ordinary byte-returning encoder recovers its complete input through native
sample reads whenever C9 holds for these encoded bytes at sufficient limits. -/
theorem encode_native_roundtrip_of_c9 {p : Params} {img : Encode.Image} {data : ByteArray}
    (he : encode p img = .ok data) (hrev : p.reversible = true)
    (agreement : ∀ L, NativeEquiv.Agrees L data 0) :
    ∃ L d, decodeCodestream L data 0 = .ok d ∧ encoderImageOfNative d = some img := by
  cases h : encodeDetailed p img with
  | error err => simp [encode, h, Functor.map, Except.map] at he
  | ok e =>
    have same : e.codestream = data := by simpa [encode, h, Functor.map, Except.map] using he
    subst data
    exact ⟨encoderLimits p img e, native_roundtrip_of_c9 h hrev (headerFits_encoderLimits h)
      (by decide : 109 ≤ Limits.default.maxPassesPerCodeBlock) (Nat.le_max_right ..)
      (Nat.le_max_right ..) (Nat.le_max_right ..) (agreement _)⟩

end JPEG2000.Spec.RoundTrip
