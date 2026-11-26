import Spec.ColorResources.Mapping
import Spec.ColorResources.Views
import Spec.ColorResources.Interleave
import Spec.ColorResources.Palette
import Spec.ColorResources.Layout

/-!
# Public colour pipeline resource bounds (Plan.md §§3–5, 7, S3; T.800 B.2 and Annex I)

Raw sample backing, fresh compact rasters, captured lookup vectors, declared bytes and
display loop bounds have different units. The witnesses below follow the actual mapping,
optional conversion, full-grid replication and channel selection in `JPEG2000.decode`.
-/

namespace JPEG2000.Spec.ColorResources

open JPEG2000 JPEG2000.Color JPEG2000.Header

/-- Raw channels borrow the actual codestream storage; the metadata is copied. -/
def rawChannels (d : CodestreamImage) : Array Color.Channel :=
  d.comps.map fun c =>
    { plane := c.samples, format := { depth := c.depth, signed := c.signed, dx := c.dx, dy := c.dy } }

private theorem span (a b d : Nat) : cdiv b d - cdiv a d ≤ b-a := by
  cases d with
  | zero => simp [cdiv]
  | succ d =>
    have hm : b-a ≤ (b-a)*(d+1) := by rw [Nat.mul_succ]; omega
    have h := Nat.div_le_div_right (c := d+1)
      (show b+(d+1)-1 ≤ (a+(d+1)-1) + (b-a)*(d+1) by omega)
    rw [Nat.add_mul_div_right _ _ (Nat.succ_pos d)] at h
    exact Nat.sub_le_of_le_add (by simpa [cdiv, Nat.add_comm] using h)

/-- Reduction bounds both axis lengths independently, including degenerate rectangles. -/
theorem reduce_sides (r : Rect) (k : Nat) :
    (Assemble.reduceRect r k).width ≤ r.width ∧ (Assemble.reduceRect r k).height ≤ r.height :=
  ⟨span _ _ _, span _ _ _⟩

/-- Every constructed component grid fits the two checked reference-grid side bounds. -/
theorem raw_sides {L : Limits} {data : ByteArray} {reduce : Nat} {d : CodestreamImage}
    (ok : decodeCodestream L data reduce = .ok d) :
    ∀ c ∈ rawChannels d, c.plane.width ≤ L.maxImageSide ∧ c.plane.height ≤ L.maxImageSide := by
  have raw := NativeResources.decodeCodestream_resources ok
  have dims := (Resources.publicCodestream_resources ok).2.2.2.2
  intro c hc
  obtain ⟨dc, hdc, rfl⟩ := Array.mem_map.mp hc
  obtain ⟨i, hi, he⟩ := Array.mem_iff_getElem.mp hdc
  let rs := JPEG2000.NativeOutput.layout d.header.siz reduce
  have hsize := raw.geometry.1
  have hir : i < rs.size := hsize ▸ hi
  obtain ⟨dc', get, grid⟩ := raw.geometry.2 ⟨i,hir⟩
  simp [Array.getElem?_eq_getElem hi, he] at get
  subst dc'
  have fi : i < d.header.siz.components.size := by simpa [rs, JPEG2000.NativeOutput.layout] using hir
  have red := reduce_sides (compRect (imageRect d.header.siz) (d.header.siz.components[i])) reduce
  have side := raw.header.2.2.1
  obtain ⟨cw, ch⟩ := dims dc hdc
  dsimp only
  rw [cw, ch, grid.2.2.1, grid.2.2.2.1]
  simp only [JPEG2000.NativeOutput.layout, Fin.getElem_fin, Array.getElem_map]
  exact ⟨Nat.le_trans red.1 (Nat.le_trans (span _ _ _) side.1), Nat.le_trans red.2 (Nat.le_trans (span _ _ _) side.2.1)⟩

/-- Direct and palette channels preserve their source grid on both axes. -/
theorem mapped_sides {L : Limits} {m : Mapping} {cs mapped : Array Color.Channel}
    (map : MappingWithin L m cs mapped)
    (sides : ∀ c ∈ cs, c.plane.width ≤ L.maxImageSide ∧ c.plane.height ≤ L.maxImageSide) :
    ∀ c ∈ mapped, c.plane.width ≤ L.maxImageSide ∧ c.plane.height ≤ L.maxImageSide := by
  obtain ⟨xs, hx, hall, _⟩ := map.trace
  intro c hc
  have hmem := Array.mem_def.mp hc
  rw [← hx] at hmem
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hmem
  cases hall x hx with
  | direct src i hs => exact sides src (Array.mem_of_getElem? hs)
  | palette src ch i hs p col hp ht hw hh stor =>
    simpa only [hw, hh] using sides src (Array.mem_of_getElem? hs)

/-- Byte-array payload in an explicitly materialized sRGB channel. A lazy result's
source rasters and tables are accounted for at their own construction sites. -/
def rgbBytes (c : Color.Channel) : Nat :=
  match c.plane with
  | .compact p => p.data.size
  | _ => 0

/-- Total entries in the five arrays passed to a single sYCC conversion. -/
def SyccIndices.entries (t : SyccIndices) : Nat :=
  t.cbx.size + t.cby.size + t.crx.size + t.cry.size + t.edge.size

/-- Colour channel indices in display order after applying the palette option. -/
def chosenColours (opts : DecodeOptions) (info : Info) (d : CodestreamImage) : Array Nat :=
  if opts.applyPalette || info.mapping.palette.isNone then info.layout.colours
  else (List.range (rawChannels d).size).toArray

/-- The conversion runs when the inferred or declared colour space requests sYCC,
conversion is enabled, and the selected colour layout has exactly three entries. -/
def runsRgb (opts : DecodeOptions) (info : Info) (d : CodestreamImage) : Bool :=
  let space := if info.space == .unknown && opts.inferSycc && Image.looksSycc d.comps then .sYCC else info.space
  (space == .sYCC && opts.convertSycc) && (chosenColours opts info d).size == 3

/-- Colour conversion either passes the mapped channels through or replaces the three
selected entries. The witness includes the actual input sources and keeps the luma side
bounds separately so even an empty luma grid has bounded index vectors. -/
def Converted (L : Limits) (active : Bool) (cols : Array Nat) (ox oy : Nat) (mapped chans : Array Color.Channel) (bytes slots : Nat) : Prop :=
  (active = false ∧ mapped = chans ∧ bytes = 0 ∧ slots = 0) ∨ ∃ iy ib ir y cb cr q,
    active = true ∧ cols.toList = [iy,ib,ir] ∧ mapped[iy]? = some y ∧ mapped[ib]? = some cb ∧ mapped[ir]? = some cr ∧
    y.plane.width ≤ L.maxImageSide ∧ y.plane.height ≤ L.maxImageSide ∧
    syccToRgb L ox oy y cb cr = .ok q ∧ SyccWithin L ox oy y cb cr q ∧
    bytes = rgbBytes q.1 + rgbBytes q.2.1 + rgbBytes q.2.2 ∧
    slots = (syccIndices ox oy y cb cr).entries ∧
    chans = ((mapped.setIfInBounds iy q.1).setIfInBounds ib q.2.1).setIfInBounds ir q.2.2

private theorem converted {L : Limits} {ox oy : Nat} {cols : Array Nat} {mapped : Array Color.Channel}
    {out : ColourSpace × Array Color.Channel}
    (sides : ∀ c ∈ mapped, c.plane.width ≤ L.maxImageSide ∧ c.plane.height ≤ L.maxImageSide)
    (ok : Image.convertSycc L ox oy cols mapped = .ok out) : ∃ b s, Converted L (cols.size == 3) cols ox oy mapped out.2 b s := by
  unfold Image.convertSycc at ok
  split at ok
  · repeat' split at ok <;> try contradiction
    obtain ⟨q,hq,h⟩ := Tier2Equiv.bind_ok ok
    cases h
    refine ⟨_, _, Or.inr ⟨_, _, _, _, _, _, q, ?_, ‹_›, ‹_›, ‹_›, ‹_›, ?_, ?_, hq, sycc_resources hq, rfl, rfl, rfl⟩⟩
    · have len := congrArg List.length (show cols.toList = [_,_,_] from by assumption)
      simpa using len
    all_goals first | exact (sides _ (Array.mem_of_getElem? ‹_›)).1 | exact (sides _ (Array.mem_of_getElem? ‹_›)).2
  · cases ok
    refine ⟨0, 0, Or.inl ⟨?_,rfl,rfl,rfl⟩⟩
    rename_i no
    have hl : cols.toList.length ≠ 3 := by
      generalize hx : cols.toList = xs at *
      cases xs with
      | nil => simp
      | cons a xs =>
        cases xs with
        | nil => simp
        | cons b xs =>
          cases xs with
          | nil => simp
          | cons c xs =>
            cases xs with
            | nil => exact False.elim (no a b c rfl)
            | cons d ds => simp
    simpa using hl

private theorem conversion_bounds {L : Limits} {active : Bool} {cols : Array Nat} {ox oy bytes slots : Nat} {cs ds : Array Color.Channel}
    (h : Converted L active cols ox oy cs ds bytes slots) :
    ds.size = cs.size ∧ bytes ≤ 4*L.maxWorkSamples ∧ slots ≤ 5*L.maxImageSide := by
  rcases h with ⟨_,rfl,rfl,rfl⟩ | ⟨iy, ib, ir, y, cb, cr, q, _, _, _, _, _, hw, hh, _, sycc, rfl, rfl, rfl⟩
  · simp
  refine ⟨by simp, ?_, ?_⟩
  · obtain ⟨work, compact | rfl⟩ := sycc
    · obtain ⟨r,g,b,er,eg,eb,size⟩ := compact
      simp only [rgbBytes, er, eg, eb, size]
      exact Nat.mul_le_mul_left _ work
    · exact Nat.zero_le _
  · obtain ⟨wx, wx', hy, hy', edge⟩ := sycc_indices_size ox oy y cb cr
    unfold SyccIndices.entries
    omega

/-- The JP2 mapping selected by the decode option, including the identity mapping used
when a caller requests the raw palette indices. -/
def chosenMapping (opts : DecodeOptions) (info : Info) (d : CodestreamImage) : Mapping :=
  if opts.applyPalette || info.mapping.palette.isNone then info.mapping
  else identityMapping (rawChannels d).size

/-- Conservative total of the sample byte arrays on this path. Each construction site is
charged once, including scratch rasters that can already have been released. Array slots
for boxed Int and Nat values are a separate quantity. -/
def BackingWithin (L : Limits) (img : Image) (m : Mapping) (mapped chans : Array Color.Channel)
    (full : Array JPEG2000.Channel) (rgb indices : Nat) : Prop :=
  ∃ trace : List Mapped, trace.map Mapped.channel = mapped.toList ∧
    (∀ x ∈ trace, MappedFrom L m (rawChannels img.decoded) x) ∧ trace.map Mapped.source = m.sources.toList ∧
    (img.decoded.comps.toList.map NativeResources.backingBytes).sum +
      (trace.map Mapped.freshBytes).sum + rgb +
      (List.zipWith (replicaBytes img.width img.height) chans.toList full.toList).sum ≤
        20 * L.maxWorkSamples ∧
    2 * (trace.map Mapped.rows).sum + indices + chans.size * (img.width + img.height) ≤
      2 * (L.maxComponents * L.maxPaletteEntries) + 5 * L.maxImageSide + L.maxComponents * (2 * L.maxImageSide)

private theorem backing {L : Limits} {img : Image} {m mapped chans full rgb indices}
    (raw : (img.decoded.comps.toList.map NativeResources.backingBytes).sum ≤ 8*L.maxWorkSamples)
    (hm : MappingWithin L m (rawChannels img.decoded) mapped)
    (hr : rgb ≤ 4*L.maxWorkSamples) (hs : indices ≤ 5*L.maxImageSide)
    (hi : chans.size * (img.width + img.height) ≤ L.maxComponents * (2*L.maxImageSide))
    (up : Resources.upCells img.width img.height chans ≤ L.maxWorkSamples)
    (rep : FullWithin img.x0 img.y0 img.width img.height chans full) :
    BackingWithin L img m mapped chans full rgb indices := by
  obtain ⟨xs, eq, cert, sources, pal, rows⟩ := mapping_backing hm
  have bytes := Nat.le_trans rep.2.1 (Nat.mul_le_mul_left 4 up)
  exact ⟨xs, eq, cert, sources, by omega, Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left 2 rows) hs) hi⟩

/-- The actual bounded intermediate arrays on the path to the returned image. Each
replication call admits `upsample_resources`. The two-axis charge counts temporary and
captured vectors even for an empty output raster. -/
def ColourWithin (L : Limits) (data : ByteArray) (opts : DecodeOptions) (img : Image) : Prop :=
  ∃ info m mapped chans full rgb indices,
    resolve L data (img.decoded.header.container.bind (·.header)) img.decoded.header.siz.components = .ok info ∧
    m = chosenMapping opts info img.decoded ∧ applyMapping L m (rawChannels img.decoded) = .ok mapped ∧
    MappingWithin L m (rawChannels img.decoded) mapped ∧
    Converted L (runsRgb opts info img.decoded) (chosenColours opts info img.decoded) img.x0 img.y0 mapped chans rgb indices ∧
    rgb ≤ 4*L.maxWorkSamples ∧ indices ≤ 5*L.maxImageSide ∧
    img.channels.size ≤ L.maxComponents+1 ∧ img.other.size ≤ L.maxComponents ∧
    chans.size ≤ L.maxComponents ∧
    img.width ≤ L.maxImageSide ∧ img.height ≤ L.maxImageSide ∧
    chans.size * (img.width + img.height) ≤ L.maxComponents * (2*L.maxImageSide) ∧
    Resources.upCells img.width img.height chans ≤ L.maxWorkSamples ∧
    chans.mapM (Resources.upsampleChannel img.x0 img.y0 img.width img.height) = .ok full ∧
    FullWithin img.x0 img.y0 img.width img.height chans full ∧
    BackingWithin L img m mapped chans full rgb indices ∧
    Resources.channelBytes img.width img.height full ≤ L.maxDecodedBytes ∧
    (∀ c ∈ img.channels, c ∈ full) ∧ (∀ a, img.alpha = some a → a ∈ full) ∧
    (∀ c ∈ img.other, c ∈ full) ∧ (∀ profile, img.iccProfile = some profile → profile.size ≤ data.size)

private theorem bind_success {α β : Type} {x : Except Error α} {f : α → Except Error β} {v : β} :
    (x >>= f) = .ok v ↔ ∃ a, x = .ok a ∧ f a = .ok v := by
  cases x <;> simp [bind, Except.bind]

private theorem selected {cs : Array JPEG2000.Channel} {i : Nat} {c : JPEG2000.Channel}
    (ok : Image.pick cs i = .ok c) : c ∈ cs := by
  unfold Image.pick at ok
  split at ok <;> cases ok
  exact Array.mem_of_getElem? (by assumption)

private theorem selected_all {cs out : Array JPEG2000.Channel} {indices : Array Nat}
    (ok : indices.mapM (Image.pick cs) = .ok out) : ∀ c ∈ out, c ∈ cs := by
  intro c hc
  exact Tier2Equiv.arrayMapM_inv (· ∈ cs) _ (fun _ _ h => selected h)
    _ _ ok c (Array.mem_def.mp hc)

private theorem selected_alpha {cs : Array JPEG2000.Channel} {al : Option Nat}
    {out : Option JPEG2000.Channel}
    (ok : (match al with
      | some i => some <$> Image.pick cs i
      | none => pure none) = .ok out) : ∀ a, out = some a → a ∈ cs := by
  cases al with
  | none => cases ok; simp
  | some i =>
    cases hp : Image.pick cs i with
    | error e => simp [hp, Functor.map, Except.map] at ok
    | ok c =>
      simp [hp, Functor.map, Except.map] at ok
      subst out
      intro a h
      cases h
      exact selected hp

private theorem colour_within {L : Limits} {data : ByteArray} {opts : DecodeOptions} {img : Image}
    (ok : decode L data opts = .ok img) : ColourWithin L data opts img := by
  unfold decode at ok
  simp only [bind_success] at ok
  obtain ⟨d, hd, info, hinfo, mapped, hm, _, _, h⟩ := ok
  have cert := applyMapping_resources hm
  have srcs := mapped_sides cert (raw_sides hd)
  have layoutBound := resolved_layout_size hinfo
  let choice := if opts.applyPalette || info.mapping.palette.isNone then (info.mapping, info.layout)
    else (identityMapping (rawChannels d).size, ({colours := (List.range (rawChannels d).size).toArray} : ChannelLayout))
  have mcount : choice.1.sources.size ≤ L.maxComponents := cert.count
  have selectedCounts : choice.2.colours.size ≤ L.maxComponents+1 ∧ choice.2.other.size ≤ L.maxComponents := by
    unfold choice at *
    split at mcount <;> rename_i sel
    · simp only [sel, ↓reduceIte]
      exact ⟨Nat.le_trans layoutBound.1 (Nat.add_le_add_right mcount 1), Nat.le_trans layoutBound.2 mcount⟩
    · simp only [sel, Bool.false_eq_true, ↓reduceIte, List.size_toArray, List.length_range]
      simp only [identityMapping, Array.size_map, List.size_toArray, List.length_range] at mcount
      exact ⟨by omega, Nat.zero_le _⟩

  let rr := Assemble.reduceRect (imageRect d.header.siz) opts.reduce
  have g := (NativeResources.decodeCodestream_resources hd).header.2.2.1
  have sides := reduce_sides (imageRect d.header.siz) opts.reduce
  have wx : rr.width ≤ L.maxImageSide := Nat.le_trans sides.1 g.1
  have hy : rr.height ≤ L.maxImageSide := Nat.le_trans sides.2 g.2.1
  change (Assemble.reduceRect (imageRect d.header.siz) opts.reduce).width ≤ _ at wx
  change (Assemble.reduceRect (imageRect d.header.siz) opts.reduce).height ≤ _ at hy
  generalize Assemble.reduceRect (imageRect d.header.siz) opts.reduce = rect at wx hy h
  have axes : rect.width + rect.height ≤ 2*L.maxImageSide := by omega
  generalize hs : (if info.space == .unknown && opts.inferSycc && Image.looksSycc d.comps
    then ColourSpace.sYCC else info.space) = initialSpace at h
  have flag : runsRgb opts info d =
      ((initialSpace == .sYCC && opts.convertSycc) && choice.2.colours.size == 3) := by
    unfold runsRgb; rw [hs]; unfold choice chosenColours; split <;> rfl
  repeat' split at h
  all_goals
    simp only [bind_success] at h
    obtain ⟨q, hq, _, hw, _, hb, full, hfull, cols, hcols, h⟩ := h
    have hc : ∃ b s, Converted L (runsRgb opts info d) (chosenColours opts info d) rect.x0 rect.y0 mapped q.2 b s := by
      rw [flag]
      first
      | (cases hq; refine ⟨0,0,.inl ⟨?_,rfl,rfl,rfl⟩⟩; simp_all only [Bool.false_and])
      | (have conv := converted srcs hq
         simp_all only [choice, chosenColours, rawChannels, Bool.false_eq_true, ↓reduceIte, Bool.true_and])
    obtain ⟨rgb, slots, hc⟩ := hc
    obtain ⟨length, rgbBound, slotBound⟩ := conversion_bounds hc
    obtain ⟨al, hal, other, hother, h⟩ := h
    all_goals
      cases h
      obtain ⟨xs, hx, _, _, len, _⟩ := cert.trace
      have count := congrArg List.length hx
      simp only [List.length_map, Array.length_toList, len] at count
      have n := length.trans count.symm
      have cap : q.2.size ≤ L.maxComponents := n ▸ cert.count
      have up := (Limits.check_eq_ok_iff ..).mp hw
      rw [Resources.array_foldl_sum _ (fun c => if Image.atFullRes rect.width rect.height c = true then 0
        else rect.width * rect.height) (fun a c => by split <;> simp)] at up
      have rep := replication_resources hfull
      refine ⟨info, _, mapped, q.2, full, rgb, slots, hinfo, ?_, hm, cert, hc, rgbBound, slotBound,
        ?_, ?_, cap, wx, hy, Nat.mul_le_mul cap axes, up, hfull, rep,
        backing (NativeResources.decodeCodestream_resources hd).physical cert rgbBound slotBound
          (Nat.mul_le_mul cap axes) up rep, ?_, selected_all hcols, ?_, selected_all hother, ?_⟩
      · unfold chosenMapping; split <;> rename_i guard <;> first | rfl | simp [guard, rawChannels]
      · change cols.size ≤ _
        rw [channel_map_size hcols]
        first | exact selectedCounts.1 | simpa [choice, *, rawChannels] using selectedCounts.1
      · change other.size ≤ _
        rw [channel_map_size hother]
        first | exact selectedCounts.2 | exact Nat.zero_le _ | simpa [choice, *, rawChannels] using selectedCounts.2
      · have e := (Limits.check_eq_ok_iff ..).mp hb
        rw [Resources.array_foldl_sum _ (fun c : Color.Channel => rect.width * rect.height * bytesPerSample c.format.depth)
          (fun _ _ => rfl)] at e
        exact (replication_resources hfull).2.2.2.1 ▸ e
      · first
        | exact selected_alpha (al := some _) hal
        | exact selected_alpha (al := none) hal
      · intro profile hprofile
        simp only at hprofile
        cases hprofile <;> rw [ByteArray.size_extract] <;> omega

private theorem display_count {L data opts img} (colour : ColourWithin L data opts img) (al : Bool) :
    (img.outChannels al).size ≤ L.maxComponents + 2 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, colours, _⟩ := colour
  unfold Image.outChannels
  split <;> (try rw [Array.size_push]) <;> omega

/-- All sample reads through an image channel have the stated domain, including the
zero used by kernels that request a default outside it. -/
def ReadDomain (img : Image) (c : JPEG2000.Channel) : Prop :=
  ∀ i, ((c.get? i).isSome ↔ i < img.width*img.height) ∧
    (img.width*img.height ≤ i → c.get? i = none ∧ (c.get? i).getD 0 = 0)

/-- S3 for public image decode and subsequent display at either depth. Output budgeting
can be chosen independently of decode budgeting. The raw certificate includes the
physical byte sum of all retained native and compact component buffers. -/
structure Within (L : Limits) (data : ByteArray) (opts : DecodeOptions) (img : Image) : Prop where
  /-- Full raw codestream S3 certificate, including the buffers still owned by the image. -/
  raw : NativeResources.Within L data opts.reduce img.decoded
  /-- The original row-major JP2 palette is retained even when expansion is disabled. -/
  palette : ∀ p, ((img.decoded.header.container.bind Box.Container.header).bind Box.Jp2Header.pclr) = some p →
    PaletteWithin L p
  /-- Image area, replication cells, declared bytes and selections from the full-grid array. -/
  image : Resources.ImageWithin L img
  /-- Resource and construction evidence for the actual palette, sYCC and replication stages. -/
  colour : ColourWithin L data opts img
  /-- Exact domains for colours, whole-image alpha and every remaining channel. -/
  read : ∀ c, c ∈ img.channels ∨ img.alpha = some c ∨ c ∈ img.other → ReadDomain img c
  /-- Each successful display loop performs one sample visit per selected channel and
  pixel. Its byte writes, valid byte indices and limit refusal are exact in both modes. -/
  display : ∀ (budget : Limits) (alpha : Bool) (mode : Scaling),
    let visits := img.width*img.height*(img.outChannels alpha).size
    (img.outChannels alpha).size ≤ L.maxComponents+2 ∧
    DisplayWithin budget visits (img.interleaved8 budget alpha mode) ∧
      DisplayWithin budget (visits*2) (img.interleaved16 budget alpha mode)

  /-- Source list and exact iteration fuel of each successfully produced display buffer. -/
  loops : ∀ (budget : Limits) (al wide : Bool) (mode : Scaling) (buf : ByteArray),
    interleave budget img.width img.height (img.outChannels al) wide mode = .ok buf →
      DisplayLoop img.width img.height (img.outChannels al) wide mode buf

/-- Public image S3 theorem for raw codestreams and JP2, under all decode options. -/
theorem decode_resources {L : Limits} {data : ByteArray} {opts : DecodeOptions} {img : Image}
    (ok : JPEG2000.decode L data opts = .ok img) : Within L data opts img := by
  obtain ⟨codestream, image⟩ := Resources.decode_within ok
  have colour := colour_within ok
  refine ⟨NativeResources.decodeCodestream_resources codestream, retained_palette codestream, image, colour, ?_, ?_, fun _ _ _ _ _ h => interleave_loop h⟩
  all_goals
    obtain ⟨_, _, full, _, _, _, dims, cols, alpha, other⟩ := image
  · intro c hc i
    have mem : c ∈ full := hc.elim (cols c) (fun h => h.elim (alpha c) (other c))
    obtain ⟨hw, hh⟩ := dims c mem
    have dom := plane_domain c.plane i
    rw [hw, hh] at dom
    change ((c.plane.get? i).isSome ↔ _) ∧ _
    refine ⟨dom, fun hi => ?_⟩
    have no : (c.get? i).isSome = false := by
      change (c.plane.get? i).isSome = false
      exact Bool.eq_false_iff.mpr (fun h => Nat.not_lt_of_ge hi (dom.mp h))
    cases he : c.get? i <;> simp_all
  · intro budget al mode
    have hd : ∀ c ∈ img.outChannels al, c.plane.width = img.width ∧ c.plane.height = img.height := by
      intro c hc
      apply dims
      unfold Image.outChannels at hc
      split at hc
      · rename_i a ha
        rcases Array.mem_push.mp hc with mem | rfl
        · exact cols c mem
        · exact alpha _ ha
      · exact cols c hc
    refine ⟨display_count colour al, ?_, interleave_resources hd budget true mode⟩
    simpa only [Image.interleaved8, Bool.false_eq_true, ↓reduceIte, Nat.mul_one] using
      interleave_resources hd budget false mode

end JPEG2000.Spec.ColorResources
