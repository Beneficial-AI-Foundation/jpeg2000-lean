import Spec.ColorResources
import Spec.RoundTrip.Native

/-!
# C10 through the public image decoder

Plan.md §§4, 5.3 and 7. The reference encoder writes a bare codestream with
unit sampling and a zero-origin reference grid (T.800 A.5.1, B.2). The default
display pipeline uses the direct component-to-channel mapping (T.800 I.5.3.5)
and selects every reconstructed component in order.
-/

namespace JPEG2000.Spec.RoundTrip

open JPEG2000 JPEG2000.Header JPEG2000.Color

private theorem ok_map {α β : Type} (f : α → β) (x : α) :
    f <$> (.ok x : Except Error α) = .ok (f x) := rfl

private theorem ok_bind {α β : Type} (x : α) (f : α → Except Error β) :
    (.ok x >>= f) = f x := rfl

attribute [local simp] ok_map ok_bind Except.pure

private theorem apply_identity (L : Limits) (cs : Array Color.Channel)
    (bound : cs.size ≤ L.maxComponents) :
    applyMapping L (identityMapping cs.size) cs = .ok cs := by
  let m := identityMapping cs.size
  let entry (i : Nat) : Source × Format := (.direct i, (cs.map Color.Channel.format).getD i default)
  have zipped : m.sources.zip (m.formats (cs.map Color.Channel.format)) =
      ((List.range cs.size).map entry).toArray := by
    apply Array.ext
    · simp [m, identityMapping, Mapping.formats]
    · intro i h₁ h₂
      simp [m, identityMapping, Mapping.formats, entry]
  have firstChannels (k : Nat) (hk : k ≤ cs.size) :
      ((List.range k).map entry).foldlM (mapSource L m cs) (#[], 0) =
        .ok (cs.extract 0 k, 0) := by
    induction k with
    | zero => simp [pure]
    | succ k ih =>
      have lt : k < cs.size := hk
      rw [List.range_succ, List.map_append, List.foldlM_append, ih (by omega)]
      simp [entry, mapSource, Array.getElem?_eq_getElem lt, Array.push_extract_getElem lt]
  have componentsOK := (Limits.check_eq_ok_iff L (.at .color) .components cs.size).2 bound
  have size : m.sources.size = cs.size := by simp [m, identityMapping]
  change (do
    L.check (.at .color) .components m.sources.size
    let (out, _) ← (m.sources.zip (m.formats (cs.map Color.Channel.format))).foldlM
      (mapSource L m cs) (#[], 0)
    return out) = _
  rw [size, componentsOK, zipped]
  simp [firstChannels cs.size (Nat.le_refl _)]

private theorem pick_range (cs : Array JPEG2000.Channel) :
    (List.range cs.size).toArray.mapM (Image.pick cs) = .ok cs := by
  have firstChannels (k : Nat) (hk : k ≤ cs.size) :
      (List.range k).mapM (Image.pick cs) = .ok (cs.toList.take k) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      have lt : k < cs.size := hk
      rw [List.range_succ, List.mapM_append, ih (by omega)]
      simp [Image.pick, List.take_add_one, lt]
  simp [Array.mapM_eq_mapM_toList, firstChannels cs.size (Nat.le_refl _),
    List.take_of_length_le (by simp : cs.toList.length ≤ cs.size)]

private def displayChannel (c : Color.Channel) : JPEG2000.Channel :=
  { depth := c.format.depth, signed := c.format.signed, plane := c.plane }

private theorem full_channels (cs : Array Color.Channel) (w h : Nat)
    (full : ∀ c ∈ cs, Image.atFullRes w h c = true) :
    cs.mapM (Resources.upsampleChannel 0 0 w h) = .ok (cs.map displayChannel) := by
  have go (xs : List Color.Channel) (hs : ∀ c ∈ xs, Image.atFullRes w h c = true) :
      xs.mapM (Resources.upsampleChannel 0 0 w h) = .ok (xs.map displayChannel) := by
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      have first := hs x (by simp)
      simp [List.mapM_cons, Resources.upsampleChannel, Image.upsample, first, displayChannel,
        ih (fun c hc => hs c (by simp [hc]))]
  rw [Array.mapM_eq_mapM_toList, go cs.toList (by simpa using full), ok_map,
    ← Array.toList_map, Array.toArray_toList]

private def rawInfo (comps : Array Marker.Component) : Info :=
  let mapping := identityMapping comps.size
  { space := .unknown, mapping, formats := mapping.formats (componentFormats comps),
    layout := { colours := (List.range comps.size).toArray } }

private theorem resolve_bare (L : Limits) (data : ByteArray) (comps : Array Marker.Component)
    (bound : comps.size ≤ L.maxComponents) : resolve L data none comps = .ok (rawInfo comps) := by
  have componentsOK := (Limits.check_eq_ok_iff L (.at .color) .components comps.size).2 bound
  simp [resolve, componentsOK, rawInfo, channelLayout, ColourSpace.numColours, identityMapping,
    pure, List.drop_eq_nil_of_le]

private theorem display_bare {L : Limits} {data : ByteArray} {d : CodestreamImage} {w h : Nat}
    (native : decodeCodestream L data 0 = .ok d) (bare : d.header.container = none)
    (grid : Assemble.reduceRect (imageRect d.header.siz) 0 = ⟨0, 0, w, h⟩)
    (count : d.header.siz.components.size = (ColorResources.rawChannels d).size)
    (cap : d.header.siz.components.size ≤ L.maxComponents) (area : w * h ≤ L.maxImageArea)
    (space : Image.looksSycc d.comps = false)
    (full : ∀ c ∈ ColorResources.rawChannels d, Image.atFullRes w h c = true)
    (bytes : ((ColorResources.rawChannels d).toList.map fun c =>
      w * h * bytesPerSample c.format.depth).sum ≤ L.maxDecodedBytes) :
    ∃ out, JPEG2000.decode L data = .ok out ∧ out.width = w ∧ out.height = h ∧
      out.channels = (ColorResources.rawChannels d).map displayChannel := by
  let cs := ColorResources.rawChannels d
  have mapped : applyMapping L (identityMapping d.header.siz.components.size) cs = .ok cs := by
    rw [count]
    exact apply_identity _ _ (count ▸ cap)
  have up : cs.foldl (fun a c => if Image.atFullRes w h c then a else a + w * h) 0 = 0 := by
    rw [Resources.array_foldl_sum _ (fun c => if Image.atFullRes w h c then 0 else w * h)
      (fun a c => by split <;> simp)]
    have zeros : (cs.toList.map fun c => if Image.atFullRes w h c then 0 else w * h) =
        cs.toList.map (fun _ => 0) := List.map_congr_left (fun c hc => by
          simp [full c (by simpa [cs] using hc)])
    simp [zeros, List.map_const', List.sum_replicate_nat]
  have areaOK := (Limits.check_eq_ok_iff L Image.loc .imageArea _).2 area
  have workOK := (Limits.check_eq_ok_iff L Image.loc .workSamples 0).2 (Nat.zero_le _)
  have bytesOK := (Limits.check_eq_ok_iff L Image.loc .decodedBytes _).2 bytes
  have select : (List.range d.header.siz.components.size).toArray.mapM
      (Image.pick (cs.map displayChannel)) = .ok (cs.map displayChannel) := by
    simpa only [Array.size_map, ← count, cs] using pick_range (cs.map displayChannel)
  unfold JPEG2000.decode
  change ∃ out, (decodeCodestream L data 0 >>= _) = .ok out ∧ _
  rw [native, ok_bind]
  simp only [bare, Option.bind_none, resolve_bare L data _ cap, ok_bind]
  dsimp only [rawInfo, Bool.true_or, ↓reduceIte]
  change ∃ out, (applyMapping L (identityMapping d.header.siz.components.size) cs >>= _) = .ok out ∧ _
  rw [mapped, ok_bind]
  simp only [grid, Rect.width, Rect.height, Nat.sub_zero, areaOK, ok_bind, space]
  change ∃ out, (L.check Image.loc .workSamples _ >>= _) = .ok out ∧ _
  rw [up, workOK, ok_bind, Resources.array_foldl_sum _ _ (fun _ _ => rfl), bytesOK, ok_bind]
  change ∃ out, (cs.mapM (Resources.upsampleChannel 0 0 w h) >>= _) = .ok out ∧ _
  rw [full_channels cs w h full, ok_bind]
  change ∃ out, ((List.range d.header.siz.components.size).toArray.mapM
    (Image.pick (cs.map displayChannel)) >>= _) = .ok out ∧ _
  rw [select, ok_bind]
  exact ⟨{ width := w, height := h, x0 := 0, y0 := 0, space := .unknown,
           channels := cs.map displayChannel, decoded := d }, by simp [pure], rfl, rfl, rfl⟩

private theorem mapM_reads {α β : Type} (f : α → Option β) {xs : Array α} {ys : Array β}
    (ok : xs.mapM f = some ys) (i : Nat) : xs[i]?.bind f = ys[i]? := by
  have atIndex (as : List α) (bs : List β) (run : as.mapM f = some bs) (j : Nat) :
      as[j]?.bind f = bs[j]? := by
    induction as generalizing bs j with
    | nil => cases run; rfl
    | cons x as ih =>
      rw [List.mapM_cons] at run
      cases hx : f x with
      | none => simp [hx] at run
      | some y =>
        cases ht : as.mapM f with
        | none => simp [hx, ht] at run
        | some tail =>
          simp [hx, ht] at run
          subst bs
          cases j with
          | zero => simpa using hx
          | succ j => exact ih _ ht j
  rw [Array.mapM_eq_mapM_toList] at ok
  cases hr : xs.toList.mapM f with
  | none => simp [hr] at ok
  | some bs =>
    simp [hr] at ok
    subst ys
    simpa using atIndex xs.toList bs hr i

private theorem native_reads {d : CodestreamImage} {img : Encode.Image}
    (recovered : encoderImageOfNative d = some img) {i : Nat}
    (hi : i < d.comps.size) (hj : i < img.comps.size)
    (domain : ∀ j, (d.comps[i].get? j).isSome ↔ j < d.comps[i].width * d.comps[i].height) :
    ∀ j, d.comps[i].get? j = img.comps[i].samples[j]? := by
  let read (c : CodestreamComponent) : Option Encode.Component := do
    let samples ← (Array.range (c.width * c.height)).mapM c.get?
    return { depth := c.depth, signed := c.signed, samples }
  change (d.comps.mapM read >>= _) = some img at recovered
  cases hr : d.comps.mapM read with
  | none => simp [hr] at recovered
  | some comps =>
    rw [hr] at recovered
    have same : comps = img.comps :=
      congrArg Encode.Image.comps (Option.some.inj recovered)
    subst comps
    have fmt := mapM_reads read hr i
    simp only [Array.getElem?_eq_getElem hi, Array.getElem?_eq_getElem hj, Option.bind_some] at fmt
    unfold read at fmt
    cases hs : (Array.range (d.comps[i].width * d.comps[i].height)).mapM d.comps[i].get? with
    | none => simp [hs] at fmt
    | some xs =>
      rw [hs] at fmt
      have vals : xs = img.comps[i].samples :=
        congrArg Encode.Component.samples (Option.some.inj fmt)
      subst xs
      intro j
      have value := mapM_reads _ hs j
      by_cases hj' : j < d.comps[i].width * d.comps[i].height
      · simpa [Array.getElem?_eq_getElem, hj'] using value
      · have missing : d.comps[i].get? j = none := by
          cases hv : d.comps[i].get? j with
          | none => rfl
          | some v => exact (hj' ((domain j).1 (by simp [hv]))).elim
        rw [missing]
        simpa [Array.getElem?_eq_none, hj'] using value

/-- Every public colour channel, in encoder order, has the original plane dimensions,
sample format and exact checked raster reads (including reads past the end). -/
structure DisplayRecovers (out : Image) (img : Encode.Image) : Prop where
  width : out.width = img.width
  height : out.height = img.height
  count : out.channels.size = img.comps.size
  channel : ∀ (i : Nat) (hi : i < img.comps.size),
    let c := out.channels[i]'(count ▸ hi)
    let src := img.comps[i]
    c.plane.width = img.width ∧ c.plane.height = img.height ∧
    c.depth = src.depth ∧ c.signed = src.signed ∧ ∀ j, c.get? j = src.samples[j]?

/-- At the limits computed from a successful reversible encoding, the ordinary
decoder with its default options returns the encoder image through its colour channels. -/
theorem image_roundtrip {p : Encode.Params} {img : Encode.Image} {e : Encode.Encoded}
    (he : Encode.encodeDetailed p img = .ok e) (reversible : p.reversible = true) :
    ∃ out, JPEG2000.decode (encoderLimits p img e) e.codestream = .ok out ∧
      DisplayRecovers out img := by
  let L := encoderLimits p img e
  have fits := headerFits_encoderLimits he
  obtain ⟨packet, _, parsed, _⟩ := parse_encodeDetailed L p img e he fits
  obtain ⟨d, native, readback⟩ := native_roundtrip he reversible
  have header := (CodestreamDispatch.native_geometry parsed native).1
  have siz : d.header.siz = encSIZ img := congrArg Header.siz header
  have bare : d.header.container = none := congrArg Header.container header
  have checked := (encodeDetailed_shape he).check
  have facts := checkFacts_of_ok checked
  have hw : img.width < 2^32 := Nat.lt_of_le_of_lt facts.width_le (by decide)
  have hh : img.height < 2^32 := Nat.lt_of_le_of_lt facts.height_le (by decide)
  have hd (c : Encode.Component) (mem : c ∈ img.comps) : c.depth < 256 :=
    Nat.lt_trans (Nat.lt_succ_of_le (check_component_samples checked c mem).1.2) (by decide)
  have grid : Assemble.reduceRect (imageRect d.header.siz) 0 = encRect img := by
    simp [siz, encSIZ, imageRect, Assemble.reduceRect, cdivPow, cdiv, encRect,
      Nat.mod_eq_of_lt hw, Nat.mod_eq_of_lt hh]
  have cert := NativeResources.decodeCodestream_resources native
  have geom := cert.geometry
  rw [siz] at geom
  have count : d.comps.size = img.comps.size := by
    simpa [JPEG2000.NativeOutput.layout, encSIZ] using geom.1
  have metadata (i : Nat) (hi : i < img.comps.size) :
      let c := d.comps[i]'(count ▸ hi)
      c.width = img.width ∧ c.height = img.height ∧ c.dx = 1 ∧ c.dy = 1 ∧
        c.depth = img.comps[i].depth ∧ c.signed = img.comps[i].signed := by
    have idx : i < (JPEG2000.NativeOutput.layout (encSIZ img) 0).size := by
      simpa [JPEG2000.NativeOutput.layout, encSIZ] using hi
    obtain ⟨c, hc, onGrid⟩ := geom.2 ⟨i, idx⟩
    rw [Array.getElem?_eq_getElem (count ▸ hi)] at hc
    cases hc
    simp [NativeResources.OnGrid, JPEG2000.NativeOutput.layout, encSIZ, Assemble.reduceRect,
      compRect, imageRect, cdivPow, cdiv, Rect.width, Rect.height,
      Nat.mod_eq_of_lt hw, Nat.mod_eq_of_lt hh,
      Nat.mod_eq_of_lt (hd _ (Array.getElem_mem hi))] at onGrid
    obtain ⟨_, _, w, h, depth, sign, dx, dy⟩ := onGrid
    exact ⟨w, h, dx, dy, depth, sign⟩
  have dims := (Resources.publicCodestream_resources native).2.2.2.2
  have units (c : CodestreamComponent) (mem : c ∈ d.comps) :
      c.width = img.width ∧ c.height = img.height ∧ c.dx = 1 ∧ c.dy = 1 := by
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp mem
    obtain ⟨w, h, dx, dy, _, _⟩ := metadata i (count ▸ hi)
    exact ⟨w, h, dx, dy⟩
  have full (c : Color.Channel) (mem : c ∈ ColorResources.rawChannels d) :
      Image.atFullRes img.width img.height c = true := by
    obtain ⟨v, hv, rfl⟩ := Array.mem_map.mp mem
    obtain ⟨w, h, dx, dy⟩ := units v hv
    obtain ⟨pw, ph⟩ := dims v hv
    simp [Image.atFullRes, dx, dy, pw, ph, w, h]
  have space : Image.looksSycc d.comps = false := by
    unfold Image.looksSycc
    split
    · rename_i c₀ c₁ _ h₁
      simp [(units c₁ (Array.mem_of_getElem? h₁)).2.2.1]
    · rfl
  have depths : (ColorResources.rawChannels d).map (fun c => c.format.depth) =
      img.comps.map (·.depth) := by
    apply Array.ext
    · simp [ColorResources.rawChannels, count]
    · intro i h₁ h₂
      have hi : i < img.comps.size := by simpa using h₂
      obtain ⟨_, _, _, _, depth, _⟩ := metadata i hi
      simpa [ColorResources.rawChannels] using depth
  have admitted := (Resources.allocOutput_ok_iff ..).1 (output_admitted_encoderLimits he).2
  rw [outputBytes_encSIZ hw hh hd] at admitted
  have bytes := congrArg (fun ds : Array Nat =>
    (ds.toList.map fun depth => img.width * img.height * bytesPerSample depth).sum) depths
  simp only [Array.toList_map, List.map_map, Function.comp_def] at bytes
  obtain ⟨out, ok, w, h, channels⟩ := display_bare native bare grid
    (by simp [siz, encSIZ, ColorResources.rawChannels, count])
    (by simpa [siz, encSIZ] using fits.components) fits.area space full
    (bytes ▸ admitted.2)
  refine ⟨out, ok, w, h, by simp [channels, ColorResources.rawChannels, count], ?_⟩
  intro i hi
  have idc : i < d.comps.size := count ▸ hi
  have member := Array.getElem_mem idc
  obtain ⟨pw, ph⟩ := dims _ member
  obtain ⟨cw, ch, _, _, depth, sign⟩ := metadata i hi
  simp only [channels, ColorResources.rawChannels, Array.getElem_map, displayChannel]
  exact ⟨pw.trans cw, ph.trans ch, depth, sign, fun j =>
    (CodestreamComponent.samples_get? _ j).trans
      (native_reads readback idc hi (cert.readable _ member) j)⟩

/-- C10 at the public byte-string entry points. Every successful reversible encoding
admits limits at which the default display channels recover every original component. -/
theorem encode_image_roundtrip {p : Encode.Params} {img : Encode.Image} {data : ByteArray}
    (he : Encode.encode p img = .ok data) (reversible : p.reversible = true) :
    ∃ L out, JPEG2000.decode L data = .ok out ∧ DisplayRecovers out img := by
  obtain ⟨e, detailed, rfl, _⟩ := parse_encode Limits.default p img data he
  exact ⟨encoderLimits p img e, image_roundtrip detailed reversible⟩

end JPEG2000.Spec.RoundTrip
