import Spec.ColorResources.DisplayReads
import Spec.ColorResources.DisplayPrecision

/-!
# Post-mapping display work and allocation (Plan.md §§3–5, 7, S3; T.800 Annex I)

The first meter starts at the actual successful mapping in `decode`. Its bind retains
the charge on the first error. Units are traversal steps, array slots, byte accesses
and bounded sample kernels. The second meter prices a separate interleaving request,
including precision-dependent scaler construction and the reads of retained views.
-/

namespace JPEG2000.Spec.ColorResources.DisplayPrefix

open JPEG2000 JPEG2000.Color JPEG2000.Header

private abbrev Run (α : Type) := Except Error α × Nat

private def next {α β : Type} (x : Run α) (f : α → Run β) : Run β :=
  match x.1 with
  | .error e => (.error e,x.2)
  | .ok a => let y := f a; (y.1,x.2 + y.2)

private theorem value {α β : Type} (x : Run α) (f : α → Run β) :
    (next x f).1 = x.1.bind fun a => (f a).1 := by
  cases x with | mk v c => cases v <;> rfl

private theorem bound {α β : Type} {x : Run α} {f : α → Run β} {m n : Nat}
    (h : x.2 ≤ m) (hf : ∀ a, x.1 = .ok a → (f a).2 ≤ n) :
    (next x f).2 ≤ m+n := by
  unfold next; split
  · dsimp; omega
  · exact Nat.add_le_add h (hf _ ‹_›)

private def walk {α β : Type} (f : α → Except Error β) (price : α → Nat) : List α → Run (List β)
  | [] => (.ok [], 0)
  | a :: as => next (f a, price a) fun b =>
      let (tail, charge) := walk f price as
      (tail.map (b :: ·), charge)

private theorem walk_value {α β : Type} (f : α → Except Error β) (p : α → Nat) (xs : List α) :
    (walk f p xs).1 = xs.mapM f := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rw [walk,value,List.mapM_cons]
    cases h : f a with
    | error e => rfl
    | ok b =>
      simp only [Except.bind,bind]
      rw [← ih]
      cases (walk f p xs).1 <;> rfl

private theorem walk_bound {α β : Type} (f : α → Except Error β) (p : α → Nat)
    (xs : List α) (n : Nat) (h : ∀ a ∈ xs, p a ≤ n) : (walk f p xs).2 ≤ xs.length*n := by
  induction xs with
  | nil => simp [walk]
  | cons a xs ih =>
    simp only [walk,List.length_cons,Nat.succ_mul,Nat.add_comm (xs.length*n)]
    exact bound (h a (by simp)) (fun _ _ => ih (fun x hx => h x (by simp [hx])))

-- Array.mapM reserves its result before the first lookup, including on error.
private def scan {α β : Type} (xs : Array α) (f : α → Except Error β) (p : α → Nat) : Run (Array β) :=
  let (result, charge) := walk f p xs.toList
  (result.map List.toArray, xs.size + charge)

private theorem scan_value {α β : Type} (xs : Array α) (f : α → Except Error β) (p : α → Nat) :
    (scan xs f p).1 = xs.mapM f := by
  simp only [scan, walk_value, Array.mapM_eq_mapM_toList]
  rfl

private theorem scan_bound {α β : Type} (xs : Array α) (f : α → Except Error β) (p : α → Nat)
    (n : Nat) (h : ∀ a ∈ xs, p a ≤ n) : (scan xs f p).2 ≤ xs.size*(n+1) := by
  have ht := walk_bound f p xs.toList n (fun a ha => h a (Array.mem_def.mpr ha))
  simpa [scan,Nat.mul_add,Nat.add_comm] using Nat.add_le_add_left ht xs.size

private def choice (opts : DecodeOptions) (info : Info) (d : CodestreamImage) : Mapping × ChannelLayout :=
  if opts.applyPalette || info.mapping.palette.isNone then (info.mapping,info.layout)
  else (identityMapping (rawChannels d).size, {colours := (List.range (rawChannels d).size).toArray})

private def space (opts : DecodeOptions) (info : Info) (d : CodestreamImage) : ColourSpace :=
  if info.space == .unknown && opts.inferSycc && Image.looksSycc d.comps then .sYCC else info.space

private def profile (data : ByteArray) : ColourSpace → Option ByteArray
  | .icc pr => some (data.extract pr.start (pr.start + pr.len))
  | _ => none

private def alphaPick (cs : Array JPEG2000.Channel) : Option Nat → Except Error (Option JPEG2000.Channel)
  | some i => some <$> Image.pick cs i
  | none => pure none

private def finish (data : ByteArray) (d : CodestreamImage) (info : Info)
    (layout : ChannelLayout) (r : Rect) (sp : ColourSpace) (full : Array JPEG2000.Channel) : Run Image :=
  next (scan layout.colours (Image.pick full) (fun _ => 2)) fun cols =>
  next (alphaPick full layout.alpha,1) fun alpha =>
  next (scan layout.other (Image.pick full) (fun _ => 2)) fun other =>
    let icc := profile data info.space
    (.ok {width := r.width, height := r.height, x0 := r.x0, y0 := r.y0, space := sp,
          channels := cols, alpha, other, iccProfile := icc, decoded := d,
          premultiplied := layout.alpha.isSome && layout.premultiplied},
      1 + (icc.map ByteArray.size).getD 0)

private theorem finish_bound (data : ByteArray) (d : CodestreamImage) (info : Info)
    (layout : ChannelLayout) (r : Rect) (sp : ColourSpace) (full : Array JPEG2000.Channel) :
    (finish data d info layout r sp full).2 ≤
      layout.colours.size*3 + (1 + (layout.other.size*3 + (1+data.size))) := by
  apply bound (scan_bound _ _ _ 2 (fun _ _ => Nat.le_refl 2)); intro _ _
  apply bound (Nat.le_refl 1); intro _ _
  apply bound (scan_bound _ _ _ 2 (fun _ _ => Nat.le_refl 2)); intro _ _
  dsimp only
  cases info.space <;> simp [profile,ByteArray.size_extract] <;> omega

/-- Per-channel replication visits plus index-vector construction, raster initialization,
source reads and writes. A failed empty-source check precedes both index vectors. -/
def replicaCharge (w h : Nat) (c : Color.Channel) : Nat :=
  if Image.atFullRes w h c then 1 else
  if w*h > 0 && c.plane.width*c.plane.height == 0 then 1 else
    3 + 8*(w+h) + if c.plane.compact?.isSome then 24*(w*h) else 0

private def replicateAndPick (L : Limits) (data : ByteArray) (d : CodestreamImage) (info : Info)
    (layout : ChannelLayout) (r : Rect) (q : ColourSpace × Array Color.Channel) : Run Image :=
  let cells := q.2.foldl (fun a c => if Image.atFullRes r.width r.height c then a else a+r.width*r.height) 0
  next (L.check Image.loc .workSamples cells,1+q.2.size) fun _ =>
  let bytes := q.2.foldl (fun a c => a + r.width*r.height*bytesPerSample c.format.depth) 0
  next (L.check Image.loc .decodedBytes bytes,1+q.2.size) fun _ =>
  next (scan q.2 (Resources.upsampleChannel r.x0 r.y0 r.width r.height)
    (replicaCharge r.width r.height)) (finish data d info layout r q.1)

private def chooseSpace (L : Limits) (r : Rect) (sp : ColourSpace) (on : Bool)
    (cols : Array Nat) (cs : Array Color.Channel) : Except Error (ColourSpace × Array Color.Channel) :=
  if sp == .sYCC && on then Image.convertSycc L r.x0 r.y0 cols cs else pure (sp,cs)

private def rgbBuildCharge (ox oy : Nat) (y cb cr : Color.Channel) : Nat :=
  let tables := (syccIndices ox oy y cb cr).entries
  let compact := y.plane.compact?.isSome && cb.plane.compact?.isSome && cr.plane.compact?.isSome
  100 + 8*tables + if compact && y.format.depth ≤ 31 then 64*(y.plane.width*y.plane.height) else 0

/-- Conversion prices the pass over the colour indices even for a non-triple. A
successful triple builds the four coordinate tables and the actual edge table. Only
the compact kernel initializes and fills three four-byte rasters. Updating the three
array slots can copy the channel array. Refusal precedes the tables and rasters. -/
def conversionCharge (ox oy : Nat) (cols : Array Nat) (cs : Array Color.Channel)
    (active success : Bool) : Nat :=
  if active then 24 + cols.size + if success then
    match cols.toList with
    | [iy,ib,ir] => match cs[iy]?, cs[ib]?, cs[ir]? with
      | some y, some cb, some cr => 3*cs.size + rgbBuildCharge ox oy y cb cr
      | _,_,_ => 0
    | _ => 0
  else 0 else 1

private def suffix (L : Limits) (data : ByteArray) (opts : DecodeOptions) (d : CodestreamImage)
    (info : Info) (layout : ChannelLayout) (cs : Array Color.Channel) : Run Image :=
  let r := Assemble.reduceRect (imageRect d.header.siz) opts.reduce
  next (L.check Image.loc .imageArea (r.width*r.height), 8*(1+opts.reduce)) fun _ =>
  let sp := space opts info d
  let q := chooseSpace L r sp opts.convertSycc layout.colours cs
  next (q,conversionCharge r.x0 r.y0 layout.colours cs (sp == .sYCC && opts.convertSycc) q.isOk)
    (replicateAndPick L data d info layout r)

/-- Post-mapping work at the public byte-input boundary. An earlier codestream,
resolution or mapping error is propagated with zero suffix charge. -/
def measuredDisplay (L : Limits) (data : ByteArray) (opts : DecodeOptions) : Except Error Image × Nat :=
  next (decodeCodestream L data opts.reduce,0) fun d =>
  next (resolve L data (d.header.container.bind (·.header)) d.header.siz.components,0) fun info =>
    let ml := choice opts info d
    next (applyMapping L ml.1 (rawChannels d),0) (suffix L data opts d info ml.2)

private theorem bind_ext {α β : Type} {x : Except Error α} {f g : α → Except Error β}
    (h : ∀ a, f a = g a) : x.bind f = x.bind g := congrArg x.bind (funext h)

private theorem erases (L : Limits) (data : ByteArray) (opts : DecodeOptions) :
    (measuredDisplay L data opts).1 = JPEG2000.decode L data opts := by
  simp only [measuredDisplay,suffix,replicateAndPick,finish,value,scan_value]
  unfold JPEG2000.decode
  apply bind_ext; intro d
  apply bind_ext; intro info
  dsimp only [choice]
  split <;> rename_i sel
  all_goals
    apply bind_ext; intro cs
    apply bind_ext; intro u
    by_cases test : (space opts info d == .sYCC && opts.convertSycc) = true
    all_goals
      unfold space at test
      cases ha : info.layout.alpha <;>
        simp only [chooseSpace,space,test,↓reduceIte,alphaPick] <;> rfl

private theorem conversion_count {L r sp on cols cs q} (ok : chooseSpace L r sp on cols cs = .ok q) :
    q.2.size = cs.size := by
  simp only [chooseSpace] at ok
  split at ok
  · simp only [Image.convertSycc] at ok
    split at ok
    · repeat' split at ok <;> try contradiction
      obtain ⟨_,_,eq⟩ := Tier2Equiv.bind_ok ok
      cases eq; simp
    · cases ok; rfl
  · cases ok; rfl

private theorem convert_bound {ox oy : Nat} {L : Limits} {cols : Array Nat} {cs : Array Color.Channel}
    (cc : cols.size ≤ L.maxComponents+1) (nc : cs.size ≤ L.maxComponents)
    (sides : ∀ c ∈ cs, c.plane.width ≤ L.maxImageSide ∧ c.plane.height ≤ L.maxImageSide)
    (active success : Bool) : conversionCharge ox oy cols cs active success ≤
      125+4*L.maxComponents+40*L.maxImageSide+64*(L.maxImageSide*L.maxImageSide) := by
  unfold conversionCharge
  repeat' split
  all_goals try omega
  rename_i y cb cr hy _ _
  obtain ⟨hw,hh⟩ := sides y (Array.mem_of_getElem? hy)
  have := Nat.mul_le_mul hw hh
  obtain ⟨w₁,w₂,h₁,h₂,edge⟩ := sycc_indices_size ox oy y cb cr
  simp only [rgbBuildCharge,SyccIndices.entries]
  split <;> omega

private def tailBudget (L : Limits) (n : Nat) :=
  (1+L.maxComponents) + ((1+L.maxComponents) +
    (L.maxComponents*((3+16*L.maxImageSide+24*L.maxImageArea)+1) +
    ((L.maxComponents+1)*3+(1+(L.maxComponents*3+(1+n))))))

private theorem tail_bound {L data d info layout r q}
    (nc : q.2.size ≤ L.maxComponents) (wc : r.width ≤ L.maxImageSide) (hc : r.height ≤ L.maxImageSide)
    (area : r.width*r.height ≤ L.maxImageArea)
    (lc : layout.colours.size ≤ L.maxComponents+1) (lo : layout.other.size ≤ L.maxComponents) :
    (replicateAndPick L data d info layout r q).2 ≤ tailBudget L data.size := by
  apply bound (Nat.add_le_add_left nc 1); intro _ _
  apply bound (Nat.add_le_add_left nc 1); intro _ _
  apply bound
  · refine Nat.le_trans (scan_bound _ _ _ _ ?_) (Nat.mul_le_mul_right _ nc)
    intro c _
    unfold replicaCharge
    repeat' split
    all_goals omega
  · intro full _
    have := finish_bound data d info layout r q.1 full
    omega

/-- Uniform post-mapping bound, including the reduced-grid setup, sYCC conversion,
replication, the three selections and a possible copy of the entire input as ICC data. -/
def displayBudget (L : Limits) (n : Nat) : Nat :=
  8*(1+L.maxDecompLevels) + ((125+4*L.maxComponents+40*L.maxImageSide+
    64*(L.maxImageSide*L.maxImageSide)) + tailBudget L n)

private theorem suffix_bound {L data opts d info cs}
    (hd : decodeCodestream L data opts.reduce = .ok d)
    (hi : resolve L data (d.header.container.bind (·.header)) d.header.siz.components = .ok info)
    (hm : applyMapping L (choice opts info d).1 (rawChannels d) = .ok cs) :
    (suffix L data opts d info (choice opts info d).2 cs).2 ≤ displayBudget L data.size := by
  have raw := NativeResources.decodeCodestream_resources hd
  have cert := applyMapping_resources hm
  obtain ⟨xs,eq,_,_,len,_⟩ := cert.trace
  have size := congrArg List.length eq
  simp only [List.length_map,Array.length_toList,len] at size
  have count := cert.count
  have nc : cs.size ≤ L.maxComponents := size ▸ count
  have sides := mapped_sides cert (raw_sides hd)
  have layout := resolved_layout_size hi
  have lc : (choice opts info d).2.colours.size ≤ L.maxComponents+1 ∧
      (choice opts info d).2.other.size ≤ L.maxComponents := by
    unfold choice at count ⊢
    split at count <;> rename_i h
    · simp only [h,↓reduceIte]
      exact ⟨Nat.le_trans layout.1 (Nat.add_le_add_right count 1), Nat.le_trans layout.2 count⟩
    · simp only [h,Bool.false_eq_true,↓reduceIte,List.size_toArray,List.length_range]
      simp only [identityMapping,Array.size_map,List.size_toArray,List.length_range] at count
      exact ⟨by omega,Nat.zero_le _⟩
  have red := reduce_sides (imageRect d.header.siz) opts.reduce
  have geo := raw.header.2.2.1
  apply bound (Nat.mul_le_mul_left 8 (Nat.add_le_add_left raw.reduction.2 1))
  intro u area
  cases u
  apply bound (convert_bound lc.1 nc sides ..)
  intro q hq
  exact tail_bound ((conversion_count hq) ▸ nc) (Nat.le_trans red.1 geo.1)
    (Nat.le_trans red.2 geo.2.1) ((Limits.check_eq_ok_iff ..).mp area) lc.1 lc.2

/-- Every result of the public decoder has the actual first error or returned image
and a bounded post-mapping charge. No hypothesis on the byte string is needed. -/
theorem display_work (L : Limits) (data : ByteArray) (opts : DecodeOptions) :
    (measuredDisplay L data opts).1 = JPEG2000.decode L data opts ∧
    (measuredDisplay L data opts).2 ≤ displayBudget L data.size := by
  refine ⟨erases ..,?_⟩
  unfold measuredDisplay
  cases hd : decodeCodestream L data opts.reduce with
  | error e => exact Nat.zero_le _
  | ok d =>
    simp only [next,Nat.zero_add]
    split <;> try exact Nat.zero_le _
    split <;> try exact Nat.zero_le _
    exact suffix_bound hd ‹_› ‹_›

/-- Charges the actual exponents used in the signed offset, denominator and output
multiplier, the scaler and its list cell. Both scaling modes fit this price. -/
def scalerCharge (wide : Bool) (c : JPEG2000.Channel) :=
  12 + 3*c.depth + 2*(if wide then 16 else 8)

/-- The public interleaver validates every selected channel before the byte check.
On acceptance it builds the scaler list, tests compactness, possibly extracts compact
planes, allocates the output, visits every pixel even with zero channels, and scales
one bounded read per sample. Byte allocation and writes each count once. -/
def interleavingCharge (img : Image) (budget : Limits) (alpha wide : Bool) : Nat :=
  let cs := img.outChannels alpha
  let pixels := img.width*img.height
  let visits := pixels*cs.size
  let bytes := visits*(if wide then 2 else 1)
  2 + 2*cs.size + if bytes ≤ budget.maxDecodedBytes then
    (cs.toList.map (scalerCharge wide)).sum + 4*cs.size + pixels + (44+1)*visits + 2*bytes
  else 0

/-- Interleaving bound for a separate request. The source decode limits bound selection
and reads, while the caller's byte budget bounds allocated and written bytes. -/
def interleavingBudget (L budget : Limits) : Nat :=
  let k := L.maxComponents+2
  2+2*k + (k*(12+3*38+2*16) + 4*k + L.maxImageArea +
    (44+1)*(L.maxImageArea*k) + 2*budget.maxDecodedBytes)

private theorem out_mem {img : Image} {a : Bool} {c : JPEG2000.Channel} (h : c ∈ img.outChannels a) :
    c ∈ img.channels ∨ img.alpha = some c ∨ c ∈ img.other := by
  unfold Image.outChannels at h
  split at h
  · rename_i alpha ha
    rcases Array.mem_push.mp h with mem | rfl
    · exact Or.inl mem
    · exact Or.inr (Or.inl ha)
  · exact Or.inl h

private theorem scalers {xs : List JPEG2000.Channel} (wide : Bool)
    (hs : ∀ c ∈ xs, c.depth ≤ 38) :
    (xs.map (scalerCharge wide)).sum ≤ xs.length*(12+3*38+2*16) := by
  induction xs with
  | nil => simp
  | cons c xs ih =>
    have ht := ih (fun z hz => hs z (by simp [hz]))
    have hc := hs c (by simp)
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.succ_mul,scalerCharge]
    cases wide <;> simp only [Bool.false_eq_true,↓reduceIte] <;> omega

/-- Read charge in production pixel order and selected channel order. Each projection
has its own read, including multiple projections of a shared sYCC source. -/
def sampleReadCharge (pixels : Nat) (cs : Array JPEG2000.Channel)
    (readers : (j : Fin cs.size) → Reader cs[j].plane) : Nat :=
  ((List.range pixels).map fun i =>
    ((List.finRange cs.size).map fun j => ((readers j).measured i).2).sum).sum

private theorem mapSum {α : Type} (xs : List α) (f : α → Nat) (cap : Nat)
    (h : ∀ x ∈ xs, f x ≤ cap) : (xs.map f).sum ≤ xs.length*cap := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simpa only [List.map_cons,List.sum_cons,List.length_cons,Nat.succ_mul,Nat.add_comm cap] using
      Nat.add_le_add (h a (by simp)) (ih (fun x hx => h x (by simp [hx])))

/-- Ordered reader witnesses for the inputs of the display kernel. Their exact aggregate
charge fits the read allowance in `interleavingCharge`, and each measured value is the
selected channel's own sample. -/
theorem selected_reads {L data opts img} (ok : JPEG2000.decode L data opts = .ok img) (alpha : Bool) :
    let cs := img.outChannels alpha
    ∃ readers : (j : Fin cs.size) → Reader cs[j].plane,
      sampleReadCharge (img.width*img.height) cs readers ≤ 44*(img.width*img.height*cs.size) ∧
      ∀ j i, ((readers j).measured i).1 = cs[j].get? i := by
  let cs := img.outChannels alpha
  have source (j : Fin cs.size) : ReadsWithin cs[j].plane 44 :=
    channel_reads ok _ (out_mem (Array.getElem_mem ..))
  let rs (j : Fin cs.size) := Classical.choose (source j)
  refine ⟨rs,?_,fun j i => read_value (rs j) i⟩
  unfold sampleReadCharge
  have pixel (i : Nat) : ((List.finRange cs.size).map (fun j => ((rs j).measured i).2)).sum
      ≤ cs.size*44 := by
    simpa [rs, Reader.work] using mapSum (List.finRange cs.size) _ 44
      (fun j _ => Classical.choose_spec (source j) i)
  simpa [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using
    mapSum (List.range (img.width*img.height)) _ (cs.size*44) (fun i _ => pixel i)

/-- Both interleavers for an actual returned image, exact buffer or independent caller
refusal, exact production loop on success, and a read derivation for every selected
plane. All costs and byte sizes are bounded on empty grids too. -/
theorem interleaving_work {L data opts img} (ok : JPEG2000.decode L data opts = .ok img)
    (budget : Limits) (alpha wide : Bool) (mode : Scaling) :
    let cs := img.outChannels alpha
    let run := if wide then img.interleaved16 budget alpha mode else img.interleaved8 budget alpha mode
    interleavingCharge img budget alpha wide ≤ interleavingBudget L budget ∧
    DisplayWithin budget (img.width*img.height*cs.size*(if wide then 2 else 1)) run ∧
    (∀ buf, run = .ok buf → DisplayLoop img.width img.height cs wide mode buf) ∧
    ∀ c ∈ cs, c.depth ≤ 38 ∧ ReadsWithin c.plane 44 := by
  dsimp only
  have cert := decode_resources ok
  obtain ⟨count,h8,h16⟩ := cert.display budget alpha mode
  have mem (c) (hc : c ∈ img.outChannels alpha) := out_mem hc
  refine ⟨?_,?_,?_,fun c hc => ⟨channel_precision ok c (mem c hc),channel_reads ok c (mem c hc)⟩⟩
  · have sc := scalers (xs := (img.outChannels alpha).toList) wide
      (fun c hc => channel_precision ok c (mem c (Array.mem_def.mpr hc)))
    rw [Array.length_toList] at sc
    have total := Nat.mul_le_mul_right (12+3*38+2*16) count
    have area := cert.image.1
    have visits := Nat.mul_le_mul area count
    cases wide <;> simp only [interleavingCharge,interleavingBudget,Bool.false_eq_true,↓reduceIte] at *
    all_goals split <;> omega
  · cases wide
    · simpa only [Bool.false_eq_true,↓reduceIte,Nat.mul_one] using h8
    · exact h16
  · intro buf h
    cases wide <;> exact cert.loops budget alpha _ mode buf h

/-- Run a separate public display-buffer request after decoding. Only the interleaving
request contributes to this charge, so it can be added to the decode prefix meters. -/
def measuredInterleaving (L : Limits) (data : ByteArray) (opts : DecodeOptions)
    (budget : Limits) (alpha wide : Bool) (mode : Scaling) : Except Error ByteArray × Nat :=
  next (JPEG2000.decode L data opts,0) fun img =>
    (if wide then img.interleaved16 budget alpha mode else img.interleaved8 budget alpha mode,
      interleavingCharge img budget alpha wide)

/-- Independent interleaving charge on every byte string. A decoding error terminates
before this charge begins, and an output-budget refusal retains the validation charge. -/
theorem public_interleaving_work (L : Limits) (data : ByteArray) (opts : DecodeOptions)
    (budget : Limits) (alpha wide : Bool) (mode : Scaling) :
    let m := measuredInterleaving L data opts budget alpha wide mode
    m.1 = (JPEG2000.decode L data opts).bind (fun img =>
      if wide then img.interleaved16 budget alpha mode else img.interleaved8 budget alpha mode) ∧
    m.2 ≤ interleavingBudget L budget := by
  dsimp only [measuredInterleaving]
  refine ⟨value ..,?_⟩
  cases ok : JPEG2000.decode L data opts with
  | error e => exact Nat.zero_le _
  | ok img => simpa only [next,Nat.zero_add] using (interleaving_work ok budget alpha wide mode).1

end JPEG2000.Spec.ColorResources.DisplayPrefix
