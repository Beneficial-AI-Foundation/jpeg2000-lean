import Spec.Resources.DiagnosticCost
import Spec.ColorResources.DisplayPrefix

/-!
# Image diagnostic construction (Plan.md §§3–5, 7, S3; T.800 B.2, I.5.3.3–6)

After native success the image operations propagate the first error. Their text
expressions occur inside failing branches. Typed checks evaluate their numeric
arguments before admission, including both folds over the post-conversion array.
The independent interleaving request has its own decoded-byte limit.
-/

namespace JPEG2000.Spec.ColorResources.DiagnosticImage

open JPEG2000 JPEG2000.Color JPEG2000.Box JPEG2000.Bytes JPEG2000.Header
open Resources.DiagnosticCost
open Tier2Equiv (bind_ok)

/-- Numeric leaves and internally computed refusals after native success. The
summands cover wire indices, pre-admission component and CMAP counts, one more
palette raster after an admitted prefix, three luma planes and the byte fold. -/
def imageCap (L : Limits) (bytes : Nat) : Nat :=
  65535 + L.maxComponents + bytes / 4 + L.maxPaletteEntries +
    L.maxWorkSamples + 3 * (L.maxImageSide * L.maxImageSide) +
    8 * (L.maxImageArea * L.maxComponents)

/-- A refusal retains the colour location. A typed value carries the exact
corresponding caller field as its ceiling. Text retains its construction tree. -/
private inductive Refusal (L : Limits) (cap : Nat) : Error → Type where
  | malformed {s : String} (text : Built cap s) : Refusal L cap (Color.malformed s)
  | unsupported {s : String} (text : Built cap s) : Refusal L cap (Color.unsupported s)
  | limit {k : LimitKind} {v : Nat} (value : v ≤ cap) (over : L.bound k < v) :
      Refusal L cap (.limitExceeded Image.loc k v (L.bound k))

-- In this suffix no error is caught and the only expressions that build error
-- text are on refusing branches. Thread the successful prefix through each bind.
private def Stage {α : Type} (L : Limits) (cap : Nat) (P : α → Prop) : Except Error α → Type
  | .error e => Refusal L cap e
  | .ok a => PLift (P a)

private def chain {α β : Type} {L cap} {P : α → Prop} {Q : β → Prop}
    {x : Except Error α} {f : α → Except Error β} (hx : Stage L cap P x)
    (next : ∀ a, x = .ok a → P a → Stage L cap Q (f a)) :
    Stage L cap Q (x >>= f) := by
  cases x with
  | error => exact hx
  | ok a => exact next a rfl hx.down

private def checked {L : Limits} {k : LimitKind} {v cap} (hv : v ≤ cap) :
    Stage L cap (fun _ => v ≤ L.bound k) (L.check Image.loc k v) := by
  unfold Limits.check Limits.checkLe
  split
  · exact ⟨by assumption⟩
  · exact .limit hv (by omega)

-- These traversals use the same left-to-right short circuit as the production
-- for-loop and mapM. The callback supplies the expression at the refusing entry.
private def eachStage {α : Type} {L cap} (xs : Array α)
    (f : α → Unit → Except Error (ForInStep Unit))
    (one : ∀ a ∈ xs, Stage L cap (fun _ => True) (f a ())) :
    Stage L cap (fun _ => True) (forIn xs () f) := by
  rw [← Array.forIn_toList]
  let rec go (as : List α) (each : ∀ a ∈ as, Stage L cap (fun _ => True) (f a ())) :
      Stage L cap (fun _ => True) (forIn as () f) := by
    match as with
    | [] => exact ⟨True.intro⟩
    | a :: as =>
      rw [List.forIn_cons]
      apply chain (each a (.head _))
      intro step _ _
      cases step with
      | done => exact ⟨True.intro⟩
      | yield u => cases u; exact go as (fun v hv => each v (.tail _ hv))
  exact go _ (fun a ha => one a (Array.mem_def.mpr ha))

private def mapStage {α β : Type} {L cap} (xs : Array α) (f : α → Except Error β)
    (one : ∀ a ∈ xs, Stage L cap (fun _ => True) (f a)) :
    Stage L cap (fun _ => True) (xs.mapM f) := by
  let rec go (as : List α) (each : ∀ a ∈ as, Stage L cap (fun _ => True) (f a)) :
      Stage L cap (fun _ => True) (as.mapM f) := by
    match as with
    | [] => exact ⟨True.intro⟩
    | a :: as =>
      rw [List.mapM_cons]
      apply chain (each a (.head _))
      intro _ _ _
      apply chain (go as (fun v hv => each v (.tail _ hv)))
      intros; exact ⟨True.intro⟩
  rw [Array.mapM_eq_mapM_toList]
  change Stage L cap _ (xs.toList.mapM f >>= _)
  apply chain (go _ (fun a ha => one a (Array.mem_def.mpr ha)))
  intros; exact ⟨True.intro⟩

/-! ## Colour resolution -/

private def paletteStage (L : Limits) (cap : Nat) (p : Palette) :
    Stage L cap (fun _ => True) (checkPalette p) := by
  simp only [checkPalette]
  split
  · exact .malformed (oneFixed _ (by decide))
  split
  · exact .malformed (oneFixed _ (by decide))
  apply chain (P := fun _ => True)
  · apply eachStage
    intro b _
    split
    · exact .unsupported (oneFixed _ (by decide))
    · exact ⟨True.intro⟩
  · intros; exact ⟨True.intro⟩

private def entryStage (L : Limits) {cap : Nat} (wire : 65535 ≤ cap)
    (n : Nat) (p : Palette) (a : CmapEntry) : Stage L cap (fun _ => True) (entrySource n p a) := by
  have c : a.cmp.toNat ≤ cap := by have := a.cmp.toNat_lt; omega
  have k : a.pcol.toNat ≤ cap := by have := a.pcol.toNat_lt; omega
  have m : a.mtyp.toNat ≤ cap := by have := a.mtyp.toNat_lt; omega
  simp only [entrySource]
  split
  · exact .malformed (closeExpr (catExpr (catExpr (catExpr (litExpr _ "cmap: component ")
      (decExpr c)) (litExpr _ " ≥ Csiz ")) (decExpr (by omega : n ≤ cap))) (by decide) (by decide))
  split
  · split
    · exact .malformed (closeExpr (catExpr (catExpr (litExpr _ "cmap: direct use with PCOL ")
        (decExpr k)) (litExpr _ " ≠ 0")) (by decide) (by decide))
    · exact ⟨True.intro⟩
  · split
    · exact .malformed (closeExpr (catExpr (catExpr (catExpr (litExpr _ "cmap: palette column ")
        (decExpr k)) (litExpr _ " ≥ NPC ")) (decExpr (by omega : p.npc ≤ cap))) (by decide) (by decide))
    · exact ⟨True.intro⟩
  · exact .malformed (closeExpr (catExpr (catExpr (litExpr _ "cmap: MTYP ")
      (decExpr m)) (litExpr _ " not 0 or 1")) (by decide) (by decide))

private def resolveMappingStage {L : Limits} {cap n} (h : Jp2Header)
    (wire : 65535 ≤ cap) (native : n ≤ cap) (cm : (h.cmap.getD #[]).size ≤ cap) :
    Stage L cap (fun _ => True) (resolveMapping L h n) := by
  unfold resolveMapping
  split
  · rename_i p entries _ he
    unfold mappingOf
    apply chain (checked (show entries.size ≤ cap by simpa [he] using cm))
    intro _ _ _
    split
    · exact .malformed (oneFixed _ (by decide))
    apply chain (paletteStage L cap p)
    intro _ _ _
    apply chain (mapStage _ _ (fun a _ => entryStage L wire n p a))
    intros; exact ⟨True.intro⟩
  · apply chain (checked native)
    intros; exact ⟨True.intro⟩

private def cdefStage (L : Limits) {cap} (wire : 65535 ≤ cap) (n : Nat)
    (ds : Array ChannelDef) : Stage L cap (fun _ => True) (checkCdef n ds) := by
  simp only [checkCdef]
  apply chain (P := fun _ => True)
  · apply eachStage
    intro d _
    have cn : d.cn.toNat ≤ cap := by have := d.cn.toNat_lt; omega
    have ac : d.asoc.toNat ≤ cap := by have := d.asoc.toNat_lt; omega
    split
    · exact .malformed (closeExpr (catExpr (catExpr (catExpr (catExpr
        (litExpr _ "cdef: channel ") (decExpr cn)) (litExpr _ " ≥ ")) (decExpr (by omega : n ≤ cap)))
        (litExpr _ " channels")) (by decide) (by decide))
    split
    · rename_i test
      simp only [Bool.and_eq_true,decide_eq_true_eq] at test
      exact .malformed (closeExpr (catExpr (catExpr (catExpr (catExpr
        (litExpr _ "cdef: association ") (decExpr ac)) (litExpr _ " > ")) (decExpr (by omega : n ≤ cap)))
        (litExpr _ " channels")) (by decide) (by decide))
    · exact ⟨True.intro⟩
  · intro _ _ _
    split
    · exact .malformed (oneFixed _ (by decide))
    · exact ⟨True.intro⟩

private theorem colourCount (s : ColourSpace) (data : ByteArray) (d : Nat) (hd : d ≤ 65535) :
    (s.numColours data).getD d ≤ 65535 := by
  cases s <;> simp only [ColourSpace.numColours]
  case enumerated cs _ => unfold enumColours; split <;> simp only [Option.getD] <;> omega
  case icc range =>
    unfold iccColours
    dsimp only
    repeat' split
    all_goals simp only [Option.getD] at * <;> omega
  all_goals simp only [Option.getD] <;> omega

private def layoutStage (L : Limits) {cap} (wire : 65535 ≤ cap) (n : Nat)
    (s : ColourSpace) (data : ByteArray) (ds : Option (Array ChannelDef))
    (hd : (ds.getD #[]).size ≤ 65535) :
    Stage L cap (fun _ => True) (channelLayout (s.numColours data) n ds) := by
  cases ds with
  | none => exact ⟨True.intro⟩
  | some defs =>
    simp only [channelLayout]
    apply chain (cdefStage L wire n defs)
    intro _ _ _
    apply chain (P := fun _ => True)
    · apply mapStage
      intro i hi
      let f := (defs.filter fun d => d.typ == 0 && d.asoc != 0 && d.asoc != 65535).size
      have hf : f ≤ 65535 := Nat.le_trans (Array.size_filter_le ..) hd
      have lt : i < (s.numColours data).getD f := by
        cases h : s.numColours data <;> simpa [h,f] using hi
      have hk : i+1 ≤ cap := by have := colourCount s data f hf; omega
      unfold colourChannel
      split
      · exact ⟨True.intro⟩
      · exact .malformed (closeExpr (catExpr (litExpr _ "cdef: no channel for colour ") (decExpr hk))
          (by decide) (by decide))
      · exact .malformed (closeExpr (catExpr (litExpr _ "cdef: several channels for colour ") (decExpr hk))
          (by decide) (by decide))
    · intros; exact ⟨True.intro⟩

private def resolveStage {L data d} {opts : DecodeOptions}
    (hd : decodeCodestream L data opts.reduce = .ok d) :
    Stage L (imageCap L data.size) (fun _ => True)
      (resolve L data (d.header.container.bind (·.header)) d.header.siz.components) := by
  have wire : 65535 ≤ imageCap L data.size := by unfold imageCap; omega
  obtain ⟨cm,hn,_⟩ := MappingPrefix.retained_counts hd
  have native : d.header.siz.components.size ≤ imageCap L data.size := by unfold imageCap; omega
  have cdef := retained_cdef hd
  have cmap := cm.2
  unfold resolve
  cases hh : d.header.container.bind Container.header with
  | none =>
    apply chain (checked native)
    intro _ _ _
    simp only [pure_bind]
    apply chain (layoutStage L wire _ _ _ none (by decide))
    intros; exact ⟨True.intro⟩
  | some h =>
    rw [hh] at cmap cdef
    apply chain (resolveMappingStage h wire native (by
      change (h.cmap.getD #[]).size ≤ _ at cmap ⊢
      unfold imageCap; omega))
    intro m _ _
    simp only [pure_bind]
    apply chain (layoutStage L wire _ _ _ h.cdef cdef)
    intros; exact ⟨True.intro⟩

/-! ## Applying the chosen component mapping -/

private def index : Source → Nat
  | .direct i | .palette i _ => i

private structure MapBounds (cap : Nat) (m : Mapping) : Prop where
  count : m.sources.size ≤ cap
  indices : ∀ s ∈ m.sources, index s ≤ cap
  rows : ∀ p, m.palette = some p → p.ne ≤ cap

private theorem identityBounds {n cap : Nat} (h : n ≤ cap) : MapBounds cap (identityMapping n) := by
  refine ⟨by simpa [identityMapping] using h, ?_, by intros; contradiction⟩
  intro s hs
  obtain ⟨i,hi,rfl⟩ := Array.mem_map.mp hs
  have : i < n := by simpa using hi
  change i ≤ cap
  omega

private theorem entryIndex {n p a s} (ok : entrySource n p a = .ok s) : index s ≤ 65535 := by
  have hc := a.cmp.toNat_lt
  simp only [entrySource] at ok
  repeat' split at ok <;> try contradiction
  all_goals cases ok; change a.cmp.toNat ≤ 65535; omega

private theorem mappingBounds {L : Limits} {hdr : Jp2Header} {n cap m}
    (hn : n ≤ cap) (wire : 65535 ≤ cap) (comp : L.maxComponents ≤ cap)
    (rows : ∀ p, hdr.pclr = some p → p.ne ≤ cap)
    (ok : resolveMapping L hdr n = .ok m) : MapBounds cap m := by
  unfold resolveMapping at ok
  split at ok
  · rename_i p cm hp _
    unfold mappingOf at ok
    obtain ⟨⟨⟩,hc,ok⟩ := bind_ok ok
    split at ok <;> try contradiction
    obtain ⟨_,_,ok⟩ := bind_ok ok
    obtain ⟨src,hs,ret⟩ := bind_ok ok
    cases ret
    refine ⟨?_,Tier2WF.arrayMapM_mem _ _ _ (fun _ _ _ h => Nat.le_trans (entryIndex h) wire) _ hs,?_⟩
    · have sz := channel_map_size hs
      have eq : (fixWeirdCmap n p cm).size = cm.size := by
        unfold fixWeirdCmap
        split <;> simp
      exact sz ▸ eq ▸ Nat.le_trans ((Limits.check_eq_ok_iff ..).mp hc) comp
    · intro q h; cases h; exact rows p hp
  · obtain ⟨_,_,ret⟩ := bind_ok ok
    cases ret
    exact identityBounds hn

private theorem chosenBounds {L data opts d info}
    (hd : decodeCodestream L data opts.reduce = .ok d)
    (hi : resolve L data (d.header.container.bind (·.header)) d.header.siz.components = .ok info) :
    MapBounds (imageCap L data.size) (MappingPrefix.choice opts info d).1 := by
  obtain ⟨_,hn,hc⟩ := MappingPrefix.retained_counts hd
  have comp : L.maxComponents ≤ imageCap L data.size := by unfold imageCap; omega
  unfold MappingPrefix.choice
  split
  · dsimp only
    unfold resolve at hi
    generalize hh : d.header.container.bind Container.header = hdr at hi
    cases hdr with
    | none =>
      obtain ⟨_,first,hi⟩ := bind_ok hi
      obtain ⟨_,ret,hi⟩ := bind_ok hi
      cases ret
      obtain ⟨_,_,ret⟩ := bind_ok hi
      cases ret
      exact identityBounds (Nat.le_trans hn comp)
    | some h =>
      obtain ⟨_,first,hi⟩ := bind_ok hi
      obtain ⟨_,ret,hi⟩ := bind_ok hi
      cases ret
      obtain ⟨_,_,ret⟩ := bind_ok hi
      cases ret
      apply mappingBounds (Nat.le_trans hn comp) (by unfold imageCap; omega) comp _ first
      intro p hp
      have := (retained_palette hd p (by rw [hh]; exact hp)).1
      unfold imageCap
      omega
  · apply identityBounds
    simpa [rawChannels] using Nat.le_trans hc comp

private def missing {L : Limits} {i cap : Nat} (hi : i ≤ cap) :
    Refusal L cap (Color.malformed s!"component {i} missing") :=
  .malformed (closeExpr (catExpr (catExpr (litExpr _ "component ") (decExpr hi))
    (litExpr _ " missing")) (by decide) (by decide))

private theorem compact_area {s : SamplePlane} {p : Plane} (h : s.compact? = some p) :
    p.width*p.height = s.width*s.height := by
  cases s with
  | compact q => cases h; rfl
  | view => cases h
  | native c => cases c with | mk r f hd st hv => cases st <;> cases h; rfl

private def sourceStage {L : Limits} {bytes m cs acc total src fmt}
    (bounds : MapBounds (imageCap L bytes) m) (mem : src ∈ m.sources)
    (sides : ∀ c ∈ cs, c.plane.width ≤ L.maxImageSide ∧ c.plane.height ≤ L.maxImageSide)
    (prev : total ≤ L.maxWorkSamples) :
    Stage L (imageCap L bytes) (fun s => s.2 ≤ L.maxWorkSamples)
      (mapSource L m cs (acc,total) (src,fmt)) := by
  have hi := bounds.indices src mem
  cases src with
  | direct i =>
    simp only [mapSource]
    split
    · exact ⟨prev⟩
    · exact missing hi
  | palette i col =>
    simp only [mapSource]
    split
    · rename_i c hc
      split
      · rename_i p hp
        obtain ⟨hw,hh⟩ := sides c (Array.mem_of_getElem? hc)
        have cells := Nat.mul_le_mul hw hh
        have hv : total + c.plane.width*c.plane.height ≤ imageCap L bytes := by unfold imageCap; omega
        apply chain (checked hv)
        intro _ _ admitted
        apply chain (checked (bounds.rows p hp))
        intro _ _ _
        split
        · rename_i plane hit
          split
          · have le : plane.width*plane.height ≤ L.maxWorkSamples := by
              rw [compact_area hit]
              change total + _ ≤ L.maxWorkSamples at admitted
              omega
            have ha := (Limits.check_eq_ok_iff L Image.loc .workSamples _).2 le
            simp only [palettePlane,Plane.zeroChecked,show Location.at .color = Image.loc from rfl,
              ha,bind,Except.bind,pure,Except.pure,Functor.map,Except.map]
            exact ⟨admitted⟩
          · exact ⟨admitted⟩
        · exact ⟨admitted⟩
      · exact .malformed (oneFixed _ (by decide))
    · exact missing hi

private def mappingStage {L : Limits} {bytes m cs}
    (bounds : MapBounds (imageCap L bytes) m)
    (sides : ∀ c ∈ cs, c.plane.width ≤ L.maxImageSide ∧ c.plane.height ≤ L.maxImageSide) :
    Stage L (imageCap L bytes) (fun _ => True) (applyMapping L m cs) := by
  unfold applyMapping
  apply chain (checked bounds.count)
  intro _ _ _
  dsimp only
  rw [← Array.foldlM_toList]
  let rec walk (es : List (Source × Format)) (acc : Array Color.Channel) (n : Nat)
      (hn : n ≤ L.maxWorkSamples) (hs : ∀ e ∈ es, e.1 ∈ m.sources) :
      Stage L (imageCap L bytes) (fun st => st.2 ≤ L.maxWorkSamples)
        (es.foldlM (mapSource L m cs) (acc,n)) := by
    match es with
    | [] => exact ⟨hn⟩
    | e :: es =>
      rw [List.foldlM_cons]
      apply chain (sourceStage bounds (hs e (.head _)) sides hn)
      rintro ⟨next,n'⟩ _ hn'
      exact walk es next n' hn' (fun z hz => hs z (.tail _ hz))
  apply chain (walk _ #[] 0 (Nat.zero_le _) _)
  · rintro ⟨_,_⟩ _ _; exact ⟨True.intro⟩
  · intro e he
    exact (Array.of_mem_zip (Array.mem_def.mpr he)).1

/-! ## Conversion, display admission and replication -/

private def rgbStage {L : Limits} {bytes ox oy y cb cr}
    (depth : y.format.depth ≤ 38)
    (sides : y.plane.width ≤ L.maxImageSide ∧ y.plane.height ≤ L.maxImageSide) :
    Stage L (imageCap L bytes) (fun _ => True) (syccToRgb L ox oy y cb cr) := by
  unfold syccToRgb
  dsimp only
  split
  · have hd : y.format.depth ≤ imageCap L bytes := by unfold imageCap; omega
    exact .unsupported (closeExpr (catExpr (catExpr (litExpr _ "sYCC: luma depth ") (decExpr hd))
      (litExpr _ " not in 1..38")) (by decide) (by decide))
  split
  · exact .malformed (oneFixed _ (by decide))
  split
  · exact .malformed (oneFixed _ (by decide))
  have area := Nat.mul_le_mul sides.1 sides.2
  apply chain (checked (show 3 * (y.plane.width*y.plane.height) ≤ imageCap L bytes by
    unfold imageCap; omega))
  intro _ _ _
  split <;> (try split) <;> exact ⟨True.intro⟩

private def convertStage {L : Limits} {bytes ox oy cols cs}
    (depth : ∀ c ∈ cs, c.format.depth ≤ 38)
    (sides : ∀ c ∈ cs, c.plane.width ≤ L.maxImageSide ∧ c.plane.height ≤ L.maxImageSide) :
    Stage L (imageCap L bytes) (fun q => q.2.size = cs.size) (Image.convertSycc L ox oy cols cs) := by
  unfold Image.convertSycc
  split
  · split
    · rename_i y hy
      split
      · split
        · apply chain (rgbStage (depth y (Array.mem_of_getElem? hy)) (sides y (Array.mem_of_getElem? hy)))
          rintro ⟨_,_,_⟩ _ _
          constructor
          change (((cs.setIfInBounds _ _).setIfInBounds _ _).setIfInBounds _ _).size = _
          simp
        · exact .malformed (oneFixed _ (by decide))
      · exact .malformed (oneFixed _ (by decide))
    · exact .malformed (oneFixed _ (by decide))
  · exact ⟨rfl⟩

private theorem fold_bound {α : Type} (cs : Array α) (f : Nat → α → Nat) (price : Nat)
    (step : ∀ a c, f a c ≤ a + price) : cs.foldl f 0 ≤ cs.size * price := by
  rw [← Array.foldl_toList]
  have go (xs : List α) (a : Nat) : xs.foldl f a ≤ a + xs.length * price := by
    induction xs generalizing a with
    | nil => simp
    | cons x xs ih =>
      have := ih (f a x)
      have := step a x
      simp only [List.foldl_cons,List.length_cons,Nat.succ_mul]
      omega
  simpa using go cs.toList 0

private def upsampleStage (L : Limits) (cap ox oy w h : Nat) (cs : Array Color.Channel) :
    Stage L cap (fun _ => True) (cs.mapM (Resources.upsampleChannel ox oy w h)) := by
  apply mapStage
  intro c _
  unfold Resources.upsampleChannel
  apply chain (P := fun _ => True)
  · simp only [Image.upsample]
    split
    · exact ⟨True.intro⟩
    split
    · exact .unsupported (oneFixed _ (by decide))
    split <;> exact ⟨True.intro⟩
  · intros; exact ⟨True.intro⟩

private def space (opts : DecodeOptions) (info : Info) (d : CodestreamImage) :=
  if info.space == .unknown && opts.inferSycc && Image.looksSycc d.comps then .sYCC else info.space

private def convert (L : Limits) (opts : DecodeOptions) (info : Info) (d : CodestreamImage)
    (r : Rect) (cols : Array Nat) (cs : Array Color.Channel) :=
  if space opts info d == .sYCC && opts.convertSycc then Image.convertSycc L r.x0 r.y0 cols cs
  else pure (space opts info d, cs)

/-- Work cells computed before replication, omitting channels already at full resolution. -/
def cells (r : Rect) (cs : Array Color.Channel) :=
  cs.foldl (fun a c => if Image.atFullRes r.width r.height c then a else a+r.width*r.height) 0

/-- The decoded-byte operand uses every post-conversion channel at its own precision. -/
def byteCount (r : Rect) (cs : Array Color.Channel) :=
  cs.foldl (fun a c => a+r.width*r.height*bytesPerSample c.format.depth) 0

private theorem displayCounts {L : Limits} {r : Rect} {cs : Array Color.Channel}
    (hn : cs.size ≤ L.maxComponents) (ha : r.width*r.height ≤ L.maxImageArea) :
    cells r cs ≤ L.maxImageArea * L.maxComponents ∧
    byteCount r cs ≤ 8 * (L.maxImageArea * L.maxComponents) := by
  have grid := Nat.mul_le_mul hn ha
  constructor
  · refine Nat.le_trans (fold_bound cs _ (r.width*r.height) ?_) ?_
    · intro a c; split <;> omega
    · rwa [Nat.mul_comm L.maxImageArea]
  · refine Nat.le_trans (fold_bound cs _ (r.width*r.height*8) ?_) ?_
    · intro a c
      apply Nat.add_le_add_left
      apply Nat.mul_le_mul_left
      unfold bytesPerSample
      split <;> (try split) <;> (try split) <;> decide
    · simpa [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using Nat.mul_le_mul_right 8 grid

private def finish (data : ByteArray) (d : CodestreamImage) (info : Info) (r : Rect)
    (lay : ChannelLayout) (sp : ColourSpace)
    (p : Array JPEG2000.Channel × Option JPEG2000.Channel × Array JPEG2000.Channel) : Image :=
  { width := r.width, height := r.height, x0 := r.x0, y0 := r.y0, space := sp,
    channels := p.1, alpha := p.2.1, other := p.2.2,
    premultiplied := lay.alpha.isSome && lay.premultiplied, decoded := d,
    iccProfile := match info.space with
      | .icc pr => some (data.extract pr.start (pr.start + pr.len))
      | _ => none }

private def suffix (L : Limits) (data : ByteArray) (opts : DecodeOptions) (d : CodestreamImage) :
    Except Error Image := do
  let info ← resolve L data (d.header.container.bind (·.header)) d.header.siz.components
  let ml := MappingPrefix.choice opts info d
  let cs ← applyMapping L ml.1 (rawChannels d)
  let r := Assemble.reduceRect (imageRect d.header.siz) opts.reduce
  L.check Image.loc .imageArea (r.width*r.height)
  let q ← convert L opts info d r ml.2.colours cs
  L.check Image.loc .workSamples (cells r q.2)
  L.check Image.loc .decodedBytes (byteCount r q.2)
  let full ← q.2.mapM (Resources.upsampleChannel r.x0 r.y0 r.width r.height)
  let p ← pickChannels ml.2 full
  return finish data d info r ml.2 q.1 p

/-- The post-conversion grid and channels from the actual public prefix, before
either display budget has admitted its argument. -/
def displayInputs (L : Limits) (data : ByteArray) (opts : DecodeOptions) :
    Except Error (Rect × Array Color.Channel) := do
  let d ← decodeCodestream L data opts.reduce
  let info ← resolve L data (d.header.container.bind (·.header)) d.header.siz.components
  let ml := MappingPrefix.choice opts info d
  let cs ← applyMapping L ml.1 (rawChannels d)
  let r := Assemble.reduceRect (imageRect d.header.siz) opts.reduce
  L.check Image.loc .imageArea (r.width*r.height)
  let q ← convert L opts info d r ml.2.colours cs
  return (r,q.2)

private theorem suffix_eq {L data opts d} (hd : decodeCodestream L data opts.reduce = .ok d) :
    suffix L data opts d = JPEG2000.decode L data opts := by
  cases hr : resolve L data (d.header.container.bind (·.header)) d.header.siz.components with
  | error e =>
    rw [(public_resolve (opts := opts) hd hr).1]
    simp only [suffix,hr,bind,Except.bind]
  | ok info =>
    unfold suffix JPEG2000.decode
    rw [hd]
    have bindOk {α β : Type} (x : α) (f : α → Except Error β) : (Except.ok x >>= f) = f x := rfl
    simp only [bindOk,hr]
    simp only [MappingPrefix.choice,rawChannels]
    split <;> apply congrArg (Except.bind _) <;> funext cs
    all_goals
      apply congrArg (Except.bind _)
      funext u
      unfold convert space
      generalize (if info.space == .unknown && opts.inferSycc && Image.looksSycc d.comps
        then ColourSpace.sYCC else info.space) = sp
      by_cases active : (sp == .sYCC && opts.convertSycc) = true
      all_goals
        cases ha : info.layout.alpha <;>
          simp only [active,Bool.false_eq_true,↓reduceIte,pickChannels,ha,bind_assoc,pure_bind,finish] <;> rfl

private def chosenConversion {L data opts d info cs} (r : Rect) (cols : Array Nat)
    (hd : decodeCodestream L data opts.reduce = .ok d)
    (hi : resolve L data (d.header.container.bind (·.header)) d.header.siz.components = .ok info)
    (hm : applyMapping L (MappingPrefix.choice opts info d).1 (rawChannels d) = .ok cs) :
    Stage L (imageCap L data.size) (fun q => q.2.size = cs.size) (convert L opts info d r cols cs) := by
  unfold convert
  split
  · have same : (MappingPrefix.choice opts info d).1 = chosenMapping opts info d := by
      unfold MappingPrefix.choice chosenMapping
      split <;> rfl
    have sides := mapped_sides (applyMapping_resources hm) (raw_sides hd)
    rw [same] at hm
    exact convertStage (DisplayPrefix.mapped_precision hd hi hm) sides
  · exact ⟨rfl⟩

private theorem mapped_count {L m cs out} (cert : MappingWithin L m cs out) : out.size ≤ L.maxComponents := by
  obtain ⟨xs,eq,_,_,len,_⟩ := cert.trace
  have sz := congrArg List.length eq
  simp only [List.length_map,Array.length_toList,len] at sz
  exact Nat.le_trans (Nat.le_of_eq sz.symm) cert.count

/-- Both exact candidate values are bounded before the work or byte check. On
excess the public decoder stores the first refusing fold, its kind, the colour
location and the matching caller ceiling. -/
theorem display_refusal {L data opts r cs} (reached : displayInputs L data opts = .ok (r,cs)) :
    cells r cs ≤ L.maxImageArea * L.maxComponents ∧
    byteCount r cs ≤ 8 * (L.maxImageArea * L.maxComponents) ∧
    (L.maxWorkSamples < cells r cs ∨ L.maxDecodedBytes < byteCount r cs →
      JPEG2000.decode L data opts = .error (if L.maxWorkSamples < cells r cs then
        .limitExceeded Image.loc .workSamples (cells r cs) L.maxWorkSamples else
        .limitExceeded Image.loc .decodedBytes (byteCount r cs) L.maxDecodedBytes)) := by
  unfold displayInputs at reached
  obtain ⟨d,hd,reached⟩ := bind_ok reached
  obtain ⟨info,hi,reached⟩ := bind_ok reached
  obtain ⟨mapped,hm,reached⟩ := bind_ok reached
  obtain ⟨⟨⟩,area,reached⟩ := bind_ok reached
  obtain ⟨⟨sp,ch⟩,conv,ret⟩ := bind_ok reached
  cases ret
  have size : ch.size = mapped.size := by
    have stage := chosenConversion (Assemble.reduceRect (imageRect d.header.siz) opts.reduce)
      (MappingPrefix.choice opts info d).2.colours hd hi hm
    rw [conv] at stage
    exact stage.down
  have ⟨hc,hb⟩ := displayCounts (Nat.le_trans (Nat.le_of_eq size) (mapped_count (applyMapping_resources hm)))
    ((Limits.check_eq_ok_iff ..).mp area)
  refine ⟨hc,hb,?_⟩
  intro over
  rw [← suffix_eq hd]
  simp only [suffix,hi,hm,area,conv,bind,Except.bind]
  by_cases hw : L.maxWorkSamples < cells (Assemble.reduceRect (imageRect d.header.siz) opts.reduce) ch
  · simp [Limits.check,Limits.checkLe,Limits.bound,hw,Nat.not_le.mpr hw]
  · have bad := over.resolve_left hw
    simp [Limits.check,Limits.checkLe,Limits.bound,hw,Nat.le_of_not_gt hw,Nat.not_le.mpr bad]

private noncomputable def suffixStage {L data opts d} (hd : decodeCodestream L data opts.reduce = .ok d) :
    Stage L (imageCap L data.size) (fun _ => True) (suffix L data opts d) := by
  unfold suffix
  apply chain (resolveStage (opts := opts) hd)
  intro info hi _
  let layout := (MappingPrefix.choice opts info d).2
  let r := Assemble.reduceRect (imageRect d.header.siz) opts.reduce
  have raw := raw_sides hd
  apply chain (mappingStage (chosenBounds hd hi) raw)
  intro cs hm _
  have cert := applyMapping_resources hm
  have count := mapped_count cert
  have wh := reduce_sides (imageRect d.header.siz) opts.reduce
  have geo := (NativeResources.decodeCodestream_resources hd).header.2.2.1
  have sides : r.width*r.height ≤ L.maxImageSide*L.maxImageSide :=
    Nat.mul_le_mul (Nat.le_trans wh.1 geo.1) (Nat.le_trans wh.2 geo.2.1)
  apply chain (checked (show r.width*r.height ≤ imageCap L data.size by unfold imageCap; omega))
  intro u area admitted
  apply chain (chosenConversion r layout.colours hd hi hm)
  intro q hq hsize
  have ⟨hc,hb⟩ := displayCounts (Nat.le_trans (Nat.le_of_eq hsize) count) admitted
  apply chain (checked (show cells r q.2 ≤ imageCap L data.size by unfold imageCap; omega))
  intro _ work _
  apply chain (checked (show byteCount r q.2 ≤ imageCap L data.size by unfold imageCap; omega))
  intro _ bytes _
  apply chain (upsampleStage L _ r.x0 r.y0 r.width r.height q.2)
  intro full up _
  have reached : pickInputs L data opts = .ok (layout,full) := by
    unfold pickInputs
    simp only [hd,hi,hm,bind,Except.bind]
    change (do
      L.check Image.loc .imageArea (r.width*r.height)
      let q ← convert L opts info d r layout.colours cs
      L.check Image.loc .workSamples (cells r q.2)
      L.check Image.loc .decodedBytes (byteCount r q.2)
      let fs ← q.2.mapM (Resources.upsampleChannel r.x0 r.y0 r.width r.height)
      pure (layout,fs) : Except Error _) = _
    simp only [area,hq,work,bytes,up,bind,Except.bind,pure,Except.pure]
  apply chain (P := fun _ => True)
  · cases h : pickChannels layout full with
    | ok => exact ⟨True.intro⟩
    | error e =>
      let i := (public_pick reached h).2.choose
      have hi := (public_pick reached h).2.choose_spec.1
      have he : e = .malformed Image.loc s!"channel {i} missing" := (public_pick reached h).2.choose_spec.2.1
      rw [he]
      have hi' : i ≤ imageCap L data.size := by unfold imageCap; omega
      exact .malformed (closeExpr (catExpr (catExpr (litExpr _ "channel ") (decExpr hi'))
        (litExpr _ " missing")) (by decide) (by decide))
  · intros; exact ⟨True.intro⟩

/-! ## Public traces and resource bounds -/

private noncomputable def imageStage {L data opts d}
    (hd : decodeCodestream L data opts.reduce = .ok d) :
    Stage L (imageCap L data.size) (fun _ => True) (JPEG2000.decode L data opts) :=
  suffix_eq hd ▸ suffixStage hd

private def stageTrace {α : Type} {L : Limits} {cap : Nat} {run : Except Error α}
    (stage : Stage L cap (fun _ => True) run) : Trace cap run 1 := by
  cases run with
  | ok x => exact doneTrace x
  | error e =>
    change Refusal L cap e at stage
    cases stage with
    | limit hv _ => exact ⟨[],by simp,by intro e h; cases h; exact ⟨Nat.zero_le _,hv⟩⟩
    | malformed text | unsupported text =>
      exact ⟨[⟨_,text⟩],by simp,by intro e h; cases h; exact ⟨Nat.zero_le _,⟨_,text⟩,by simp,rfl⟩⟩

/-- Message expressions constructed by the public decoder strictly after its
successful native call. The certificate can be raised to the cap of an earlier
trace and appended without changing the expression trees. -/
noncomputable def imageTrace {L data opts d} (hd : decodeCodestream L data opts.reduce = .ok d) :
    Trace (imageCap L data.size) (JPEG2000.decode L data opts) 1 :=
  stageTrace (imageStage hd)

/-- Strings of the strictly propagating image suffix, in construction order. -/
def messageTexts {α : Type} : Except Error α → List String
  | .error (.malformed _ s) | .error (.unsupported _ s) | .error (.truncated _ s) => [s]
  | .error (.limitExceeded ..) | .ok _ => []

private theorem stage_texts {α : Type} {L cap} {run : Except Error α}
    (s : Stage L cap (fun _ => True) run) :
    (stageTrace s).messages.map Sigma.fst = messageTexts run := by
  cases run with
  | ok => rfl
  | error e =>
    change Refusal L cap e at s
    cases s <;> rfl

/-- Internally owned fields of the eventual refusal, zero on success. -/
def recordBytes {α : Type} : Except Error α → Nat
  | .ok _ => 0
  | .error e => storedPayload false e

private theorem record_bound {α : Type} {cap n} {run : Except Error α} (t : Trace cap run n) :
    recordBytes run ≤ 6 + Text.byteBound cap 128 24 + 2*bits cap := by
  cases run with
  | ok => exact Nat.zero_le _
  | error => exact trace_retained t rfl

/-- Exact emitted strings, the complete charge from native success through display
(including construction of numeric arguments of successful checks), cumulative
diagnostic storage, and the location and binary value of every retained refusal. -/
theorem image_diagnostics {L data opts d} (hd : decodeCodestream L data opts.reduce = .ok d) :
    let cap := imageCap L data.size
    let run := JPEG2000.decode L data opts
    let t := imageTrace hd
    let record := 6 + Text.byteBound cap 128 24 + 2*bits cap
    t.messages.map Sigma.fst = messageTexts run ∧
    (MappingPrefix.measuredNative L data opts d).2 + (DisplayPrefix.measuredDisplay L data opts).2 +
        (t.messages.map (fun m => m.2.tree.work)).sum + recordBytes run ≤
      MappingPrefix.metadataBudget L data.size + DisplayPrefix.displayBudget L data.size +
        Text.workBound cap 128 24 + record ∧
    (t.messages.map (fun m => m.2.tree.storage)).sum + recordBytes run ≤
      Text.workBound cap 128 24 + record ∧
    ∀ e, run = .error e → e.loc = Image.loc ∧ (match e with
      | .limitExceeded _ k v ceiling => L.bound k < v ∧ v ≤ cap ∧ ceiling = L.bound k
      | _ => retainedBytes e ≤ Text.byteBound cap 128 24) := by
  dsimp only
  let t := imageTrace (opts := opts) hd
  have mapping := (MappingPrefix.native_mapping_work (opts := opts) hd).2.1
  have disp := (DisplayPrefix.display_work L data opts).2
  have work := (trace_cost t).1
  have storage := trace_storage t
  have record := record_bound t
  simp only [Nat.one_mul] at work storage
  refine ⟨stage_texts (imageStage hd),Nat.add_le_add (Nat.add_le_add (Nat.add_le_add mapping disp) work)
    record,Nat.add_le_add storage record,?_⟩
  intro e he
  have s := imageStage hd
  rw [he] at s
  change Refusal L _ e at s
  cases s with
  | limit hv over => exact ⟨rfl,over,hv,rfl⟩
  | malformed _ | unsupported _ => exact ⟨rfl,(trace_cost t).2 _ he⟩

/-- Extend an ordered native diagnostic trace to the public image result. A native
refusal keeps its complete trace. On native success the display stage appends its
own construction trees, including when an earlier compact attempt produced a
message and a wide retry recovered. -/
theorem compose_native {L data opts cap events}
    (native : Trace cap (decodeCodestream L data opts.reduce) events)
    (fits : imageCap L data.size ≤ cap) :
    ∃ whole : Trace cap (JPEG2000.decode L data opts) (events+1),
      (∀ e, decodeCodestream L data opts.reduce = .error e →
        JPEG2000.decode L data opts = .error e ∧ whole.messages = native.messages) ∧
      (∀ d (ok : decodeCodestream L data opts.reduce = .ok d),
        whole.messages = native.messages ++ ((imageTrace ok).raiseCap fits).messages) := by
  have paths : (∃ d, decodeCodestream L data opts.reduce = .ok d) ∨
      (∃ e, decodeCodestream L data opts.reduce = .error e) := by
    cases decodeCodestream L data opts.reduce with
    | ok d => exact .inl ⟨d, rfl⟩
    | error e => exact .inr ⟨e, rfl⟩
  rcases paths with ⟨d, hn⟩ | ⟨e, hn⟩
  · let suffix := (imageTrace (opts := opts) hn).raiseCap fits
    refine ⟨includeTrace native suffix, ?_, ?_⟩
    · intro e he
      cases hn.symm.trans he
    · intro d' he
      cases hn.symm.trans he
      rfl
  · have refused : JPEG2000.decode L data opts = .error e := by
      simp only [JPEG2000.decode, hn, bind, Except.bind]
    let t : Trace cap (JPEG2000.decode L data opts) (events + 1) :=
      ⟨native.messages, Nat.le_trans native.countBound (Nat.le_add_right ..), by
        intro e' he
        rw [refused] at he
        cases he
        exact native.origin _ hn⟩
    refine ⟨t, ?_, ?_⟩
    · intro e' he
      cases hn.symm.trans he
      exact ⟨refused, rfl⟩
    · intro d he
      cases hn.symm.trans he

/-- Independent 8/16-bit conversion on an actual output. Either the buffer is
admitted or its computed size is retained with the external display ceiling.
The first pass over channel sizes also completes on a byte-budget refusal. -/
theorem interleaver_diagnostics {L data opts img} (ok : JPEG2000.decode L data opts = .ok img)
    (budget : Limits) (alpha wide : Bool) (mode : Scaling) :
    let run := if wide then img.interleaved16 budget alpha mode else img.interleaved8 budget alpha mode
    let count := img.width * img.height * (img.outChannels alpha).size * (if wide then 2 else 1)
    let cap := L.maxImageArea * (L.maxComponents + 2) * (if wide then 2 else 1)
    ∃ t : Trace cap run 0, t.messages = [] ∧
      DisplayPrefix.interleavingCharge img budget alpha wide ≤ DisplayPrefix.interleavingBudget L budget ∧
      DisplayWithin budget count run ∧
      (∀ e, run = .error e → e = .limitExceeded Image.loc .decodedBytes count budget.maxDecodedBytes ∧
        count ≤ cap ∧ storedPayload false e = 7 + bits count) := by
  dsimp only
  obtain ⟨charge,display,_⟩ := DisplayPrefix.interleaving_work ok budget alpha wide mode
  let run := if wide then img.interleaved16 budget alpha mode else img.interleaved8 budget alpha mode
  have refusal := fun {e} (h : run = .error e) => public_interleavers ok budget alpha mode wide h
  let t : Trace (L.maxImageArea * (L.maxComponents + 2) * (if wide then 2 else 1)) run 0 :=
    ⟨[],by simp,by
      intro e h
      obtain ⟨rfl,hc,_⟩ := refusal h
      exact ⟨Nat.zero_le _,hc⟩⟩
  refine ⟨t,rfl,charge,display,?_⟩
  intro e h
  obtain ⟨rfl,hc,_⟩ := refusal h
  exact ⟨rfl,hc,rfl⟩

end JPEG2000.Spec.ColorResources.DiagnosticImage
