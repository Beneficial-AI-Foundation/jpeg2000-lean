import Spec.ColorResources

/-!
# Construction bounds for display scalers (Plan.md §§3–5, 7, S3; T.800 Annex I)

SIZ precision comes from the actual native output record. A palette substitution uses
the column depth admitted by the resolver. Both bounds price the powers in
`Scaler.make` independently of image area, including an empty selected channel.
-/

namespace JPEG2000.Spec.ColorResources.DisplayPrefix

open JPEG2000 JPEG2000.Color JPEG2000.Header

private theorem rawDepth {L data red d} (ok : decodeCodestream L data red = .ok d) :
    ∀ c ∈ rawChannels d, c.format.depth ≤ 38 := by
  intro c mem
  obtain ⟨dc,hdc,rfl⟩ := Array.mem_map.mp mem
  have parse := ok
  unfold decodeCodestream at parse
  obtain ⟨_,_,parse⟩ := Tier2Equiv.bind_ok parse
  obtain ⟨_,hp,_⟩ := Tier2Equiv.bind_ok parse
  obtain ⟨_,_,⟨ds,hds,_⟩,_⟩ := CodestreamDispatch.native_geometry hp ok
  rw [hds] at hdc
  obtain ⟨v,_,rfl⟩ := Array.mem_map.mp hdc
  exact v.precision.2

private def PaletteDepth (m : Mapping) := ∀ p, m.palette = some p →
  ∀ i, (bitsDepth (p.bits.getD i 0)).1 ≤ 38

private theorem checked {p : Box.Palette} (ok : checkPalette p = .ok ()) :
    ∀ i, (bitsDepth (p.bits.getD i 0)).1 ≤ 38 := by
  simp only [checkPalette] at ok
  split at ok <;> try contradiction
  split at ok <;> try contradiction
  obtain ⟨⟨⟩,loop,_⟩ := Tier2Equiv.bind_ok ok
  rw [← Array.forIn_toList] at loop
  have all (xs : List UInt8) (h : forIn xs () (fun b _ => do
      if (bitsDepth b).1 > 38 then throw (unsupported "pclr: column depth exceeds 38 bits")
      pure (.yield ())) = (.ok () : Except Error Unit)) :
      ∀ b ∈ xs, (bitsDepth b).1 ≤ 38 := by
    induction xs with
    | nil => simp
    | cons a xs ih =>
      rw [List.forIn_cons] at h
      by_cases bad : (bitsDepth a).1 > 38
      · simp [bad,bind,Except.bind,throw] at h
      · simp only [bad,↓reduceIte,pure,Except.pure,bind,Except.bind] at h
        exact List.forall_mem_cons.mpr ⟨by omega,ih h⟩
  intro i
  by_cases hi : i < p.bits.size
  · simpa [Array.getD,hi] using all _ loop _ (Array.mem_def.mp (Array.getElem_mem hi))
  · simp only [Array.getD,hi,↓reduceDIte]; decide

private theorem mappingDepth {L h n m} (ok : resolveMapping L h n = .ok m) : PaletteDepth m := by
  unfold resolveMapping at ok
  split at ok
  · simp only [mappingOf] at ok
    obtain ⟨_,_,ok⟩ := Tier2Equiv.bind_ok ok
    split at ok <;> try contradiction
    obtain ⟨u,hp,ok⟩ := Tier2Equiv.bind_ok ok
    obtain ⟨_,_,eq⟩ := Tier2Equiv.bind_ok ok
    cases eq; cases u
    intro p e; cases e
    exact checked hp
  · obtain ⟨_,_,eq⟩ := Tier2Equiv.bind_ok ok
    cases eq; intro p e; cases e

private theorem chosenDepth {L data hdr comps info} (opts : DecodeOptions) (d : CodestreamImage)
    (ok : resolve L data hdr comps = .ok info) : PaletteDepth (chosenMapping opts info d) := by
  unfold chosenMapping
  split
  · unfold resolve at ok
    cases hdr <;> simp only at ok
    all_goals
      obtain ⟨_,first,ok⟩ := Tier2Equiv.bind_ok ok
      obtain ⟨_,eq,ok⟩ := Tier2Equiv.bind_ok ok
      cases eq
      obtain ⟨_,_,ret⟩ := Tier2Equiv.bind_ok ok
      cases ret
    · intro p e; cases e
    · exact mappingDepth first
  · intro p e; cases e

private theorem depths {L m} {cs out : Array Color.Channel} (raw : ∀ c ∈ cs, c.format.depth ≤ 38)
    (pal : PaletteDepth m) (ok : applyMapping L m cs = .ok out) : ∀ c ∈ out, c.format.depth ≤ 38 := by
  have source (i : Nat) : ((cs.map Color.Channel.format).getD i default).depth ≤ 38 := by
    by_cases hi : i < cs.size
    · simpa [Array.getD, Array.getElem?_eq_getElem,hi] using raw _ (Array.getElem_mem hi)
    · simp [Array.getD, hi, show (default : Format).depth = 0 from rfl]
  have fmts (f) (hf : f ∈ m.formats (cs.map (·.format))) : f.depth ≤ 38 := by
    obtain ⟨s,_,rfl⟩ := Array.mem_map.mp hf
    cases s with
    | direct i => exact source i
    | palette i col =>
      cases h : m.palette with
      | none => simpa [h] using source i
      | some p =>
        exact pal p h col
  unfold applyMapping at ok
  obtain ⟨_,_,ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨⟨result,total⟩,fold,ret⟩ := Tier2Equiv.bind_ok ok
  change Except.ok result = Except.ok out at ret
  injection ret with heq
  subst out
  rw [← Array.foldlM_toList] at fold
  let good (acc : Array Color.Channel) := ∀ c ∈ acc, c.format.depth ≤ 38
  have go (es : List (Source × Format)) (acc : Array Color.Channel) (n : Nat)
      (ha : good acc) (he : ∀ e ∈ es, e.2.depth ≤ 38)
      (h : es.foldlM (mapSource L m cs) (acc,n) = .ok (result,total)) : good result := by
    induction es generalizing acc n with
    | nil => cases h; exact ha
    | cons e es ih =>
      rw [List.foldlM_cons] at h
      obtain ⟨⟨next,n'⟩,step,tail⟩ := Tier2Equiv.bind_ok h
      apply ih _ _ _ (fun x hx => he x (by simp [hx])) tail
      obtain ⟨s,f⟩ := e
      have hf := he (s,f) (by simp)
      cases s with
      | direct i =>
        simp only [mapSource] at step
        split at step <;> try contradiction
        cases step
        intro v hv
        exact (Array.mem_push.mp hv).elim (ha _) (fun eq => eq ▸ raw _ (Array.mem_of_getElem? ‹_›))
      | palette i col =>
        simp only [mapSource] at step
        split at step <;> try contradiction
        split at step <;> try contradiction
        obtain ⟨_,_,step⟩ := Tier2Equiv.bind_ok step
        obtain ⟨_,_,step⟩ := Tier2Equiv.bind_ok step
        split at step <;> (try split at step) <;>
          (try obtain ⟨_,_,step⟩ := Tier2Equiv.bind_ok step) <;> cases step
        all_goals exact fun v hv => (Array.mem_push.mp hv).elim (ha _) (fun eq => eq ▸ hf)
  apply go _ #[] 0 (by simp [good]) _ fold
  rintro ⟨s,f⟩ mem
  exact fmts f (Array.of_mem_zip (Array.mem_def.mpr mem)).2

private theorem rgb_depth {L ox oy y cb cr q} (ok : syccToRgb L ox oy y cb cr = .ok q) :
    q.1.format.depth = y.format.depth ∧ q.2.1.format.depth = y.format.depth ∧
    q.2.2.format.depth = y.format.depth := by
  simp only [syccToRgb] at ok
  split at ok <;> try contradiction
  split at ok <;> try contradiction
  split at ok <;> try contradiction
  obtain ⟨_,_,ok⟩ := Tier2Equiv.bind_ok ok
  split at ok
  · split at ok <;> cases ok <;> exact ⟨rfl,rfl,rfl⟩
  · cases ok; exact ⟨rfl,rfl,rfl⟩

private theorem convertedDepth {L active cols ox oy cs out b t}
    (h : Converted L active cols ox oy cs out b t) (src : ∀ c ∈ cs, c.format.depth ≤ 38) :
    ∀ c ∈ out, c.format.depth ≤ 38 := by
  intro c mem
  rcases h with ⟨_,rfl,_,_⟩ | ⟨_,_,_,y,_,_,q,_,_,ey,_,_,_,_,ok,_,_,_,rfl⟩
  · exact src _ mem
  have v := src y (Array.mem_of_getElem? ey)
  obtain ⟨d1,d2,d3⟩ := rgb_depth ok
  rcases Array.mem_or_eq_of_mem_setIfInBounds mem with mem | rfl
  · rcases Array.mem_or_eq_of_mem_setIfInBounds mem with mem | rfl
    · rcases Array.mem_or_eq_of_mem_setIfInBounds mem with mem | rfl
      · exact src _ mem
      · omega
    · omega
  · omega

/-- The luma depth used as a diagnostic argument is already bounded when mapping
finishes, even if conversion or a subsequent display admission fails. -/
theorem mapped_precision {L data opts d info cs}
    (native : decodeCodestream L data opts.reduce = .ok d)
    (resolved : resolve L data (d.header.container.bind (·.header)) d.header.siz.components = .ok info)
    (mapped : applyMapping L (chosenMapping opts info d) (rawChannels d) = .ok cs) :
    ∀ c ∈ cs, c.format.depth ≤ 38 :=
  depths (rawDepth native) (chosenDepth opts d resolved) mapped

/-- All actual public display channels have bounded scaler exponents, regardless of the
palette option, sYCC projection, selected grid, or choice of colour/alpha/other. -/
theorem channel_precision {L data opts img} (ok : JPEG2000.decode L data opts = .ok img)
    (c : JPEG2000.Channel) (sel : c ∈ img.channels ∨ img.alpha = some c ∨ c ∈ img.other) :
    c.depth ≤ 38 := by
  obtain ⟨hd,_⟩ := Resources.decode_within ok
  obtain ⟨info,m,_,cs,full,_,_,hinfo,rfl,hm,_,hc,_,_,_,_,_,_,_,_,_,map,_,_,_,cols,alpha,other,_⟩ :=
    (decode_resources ok).colour
  have mem := sel.elim (cols c) (fun h => h.elim (alpha c) (other c))
  have cap := convertedDepth hc (mapped_precision hd hinfo hm)
  rw [Array.mapM_eq_mapM_toList] at map
  cases hl : cs.toList.mapM (Resources.upsampleChannel img.x0 img.y0 img.width img.height) with
  | error e => rw [hl] at map; cases map
  | ok ys =>
    rw [hl] at map; cases map
    have go (xs : List Color.Channel) (zs : List JPEG2000.Channel)
        (h : xs.mapM (Resources.upsampleChannel img.x0 img.y0 img.width img.height) = .ok zs)
        (hp : ∀ v ∈ xs, v.format.depth ≤ 38) : ∀ v ∈ zs, v.depth ≤ 38 := by
      induction xs generalizing zs with
      | nil => cases h; simp
      | cons x xs ih =>
        rw [List.mapM_cons] at h
        obtain ⟨v,hv,h⟩ := Tier2Equiv.bind_ok h
        obtain ⟨vs,ht,h⟩ := Tier2Equiv.bind_ok h
        obtain ⟨_,_,hv⟩ := Tier2Equiv.bind_ok hv
        cases h; cases hv
        intro z mem
        rcases List.mem_cons.mp mem with rfl | tail
        · exact hp x (by simp)
        · exact ih _ ht (fun a ha => hp a (by simp [ha])) _ tail
    exact go _ _ hl (fun x hx => cap _ (Array.mem_def.mpr hx)) _ (by simpa using mem)

end JPEG2000.Spec.ColorResources.DisplayPrefix
