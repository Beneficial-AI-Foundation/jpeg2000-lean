import Spec.ColorResources.MappingTables
import Spec.ColorResources.ResolveWork

/-!
# Resolver prefix charges (Plan.md §§3–5, 7, S3; T.800 I.5.3.3–6)

The outer search for a missing palette column starts a fresh, short-circuiting
CMAP scan for each column. The source array reserves its capacity before the
first entry conversion and the meter accounts for earlier conversions on error.
-/

namespace JPEG2000.Spec.ColorResources.MappingPrefix

open JPEG2000 JPEG2000.Color JPEG2000.Box

/-- Predicate visits up to and including the first hit, with a per-visit tariff. -/
def scan {α : Type} (hit : α → Bool) (price : α → Nat) : List α → Nat
  | [] => 0
  | a::as => price a + if hit a then 0 else scan hit price as

/-- Prefix cost is bounded by the length times the largest per-entry tariff. -/
theorem scan_le {α : Type} (hit : α → Bool) (price : α → Nat) (k : Nat)
    (cap : ∀ a, price a ≤ k) (xs : List α) : scan hit price xs ≤ xs.length*k := by
  induction xs with
  | nil => simp [scan]
  | cons a as ih =>
    have := cap a
    simp only [scan,List.length_cons,Nat.succ_mul]
    split <;> omega

private def visits {α : Type} (p : α → Bool) (xs : Array α) := scan p (fun _ => 1) xs.toList

private theorem visits_le {α : Type} (p : α → Bool) (xs : Array α) : visits p xs ≤ xs.size := by
  simpa [visits] using scan_le p (fun _ => 1) 1 (fun _ => Nat.le_refl _) xs.toList

private def repairCharge (n : Nat) (p : Palette) (cm : ComponentMapping) :=
  if n == 1 && cm.size == p.npc then
    let missing := fun c => !cm.any (fun e => e.pcol.toNat == c)
    let cols := List.range p.npc
    p.npc + scan missing (fun c => 1 + visits (fun e => e.pcol.toNat == c) cm) cols +
      (if cols.any missing then 2*cm.size else 0)
  else 0

private theorem repair_le (n : Nat) (p : Palette) (cm : ComponentMapping) :
    repairCharge n p cm ≤ p.npc + p.npc * (1+p.npc) + 2*cm.size := by
  unfold repairCharge
  split
  · rename_i eligible
    have same : cm.size = p.npc := by
      exact (show n = 1 ∧ cm.size = p.npc from by simpa using eligible).2
    dsimp only
    have h := scan_le (fun c => !cm.any (fun e => e.pcol.toNat == c))
      (fun c => 1 + visits (fun e => e.pcol.toNat == c) cm) (1+cm.size)
      (fun c => Nat.add_le_add_left (visits_le _ _) _) (List.range p.npc)
    simp only [List.length_range] at h
    have product := congrArg (fun k => p.npc*(1+k)) same
    split <;> omega
  · exact Nat.zero_le _

private def validation (p : Palette) :=
  if p.ne == 0 || p.npc == 0 || p.bits.size != p.npc || p.entries.size != p.ne*p.npc then 1
  else 1 + visits (fun b => (bitsDepth b).1 > 38) p.bits

private theorem validation_le (p : Palette) : validation p ≤ 1+p.bits.size := by
  unfold validation
  have := visits_le (fun b => (bitsDepth b).1 > 38) p.bits
  split <;> omega

private def paletteSelection (L : Limits) (p : Palette) (cm : ComponentMapping) (n : Nat) :=
  if cm.size > L.maxComponents || cm.isEmpty then 1
  else 1 + validation p + match checkPalette p with
    | .error _ => 0
    | .ok _ =>
      let fixed := fixWeirdCmap n p cm
      repairCharge n p cm + fixed.size +
        2 * visits (fun e => !(entrySource n p e).isOk) fixed

private theorem fixed_size (n : Nat) (p : Palette) (cm : ComponentMapping) :
    (fixWeirdCmap n p cm).size = cm.size := by unfold fixWeirdCmap; split <;> simp

private def paletteBudget (w : Nat) := 1+256+255+255*(1+255)+5*w

private theorem paletteSelection_le {L : Limits} {p : Palette} (hp : PaletteWithin L p)
    (cm : ComponentMapping) (n w : Nat) (hw : cm.size ≤ w) :
    paletteSelection L p cm n ≤ paletteBudget (min w L.maxComponents) := by
  have hv := validation_le p
  have hr := repair_le n p cm
  have hn := hp.2.1
  have hb := hp.2.2.1
  have hm := Nat.mul_le_mul hn (Nat.add_le_add_left hn 1)
  have hs := visits_le (fun e => !(entrySource n p e).isOk) (fixWeirdCmap n p cm)
  rw [fixed_size] at hs
  unfold paletteSelection paletteBudget
  split
  · omega
  · rename_i admitted
    have lim : cm.size ≤ L.maxComponents := by
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at admitted
      omega
    have size := Nat.le_min.mpr ⟨hw,lim⟩
    split
    · omega
    · simp only [fixed_size]
      change 1 + validation p + (repairCharge n p cm + cm.size + 2 * visits _ _) ≤ _
      omega

private def identityCharge (L : Limits) (n : Nat) :=
  1 + if n ≤ L.maxComponents then 3*n else 0

private def select (L : Limits) (hdr : Option Jp2Header) (n : Nat) : Except Error Mapping :=
  match hdr with
  | some h => resolveMapping L h n
  | none => do
    L.check (.at .color) .components n
    return identityMapping n

private def selectionCharge (L : Limits) (hdr : Option Jp2Header) (n : Nat) :=
  match hdr.bind Jp2Header.pclr, hdr.bind Jp2Header.cmap with
  | some p, some cm => paletteSelection L p cm n
  | _, _ => identityCharge L n

private theorem selection_le {L : Limits} {hdr : Option Jp2Header} {b n : Nat}
    (hc : Retained L b hdr)
    (hp : ∀ p, hdr.bind Jp2Header.pclr = some p → PaletteWithin L p) :
    selectionCharge L hdr n ≤ paletteBudget (min (b / 4) L.maxComponents) + 1+3*L.maxComponents := by
  unfold selectionCharge
  split
  · rename_i p cm h₁ h₂
    have hm := hc.2
    rw [h₂] at hm
    have := paletteSelection_le (hp p h₁) cm n (b/4) hm
    omega
  · unfold identityCharge
    split
    · exact Nat.add_le_add (by omega) (Nat.mul_le_mul_left 3 (by assumption))
    · exact Nat.le_trans (by decide : 1+0 ≤ 1) (by omega)

private theorem selected_size {L : Limits} {hdr : Option Jp2Header} {n : Nat} {m : Mapping}
    (ok : select L hdr n = .ok m) : m.sources.size ≤ L.maxComponents := by
  cases hdr with
  | none =>
    obtain ⟨_,hc,h⟩ := Tier2Equiv.bind_ok ok
    cases h
    simpa [identityMapping, Limits.bound] using (Limits.check_eq_ok_iff ..).mp hc
  | some h =>
    change resolveMapping L h n = .ok m at ok
    unfold resolveMapping at ok
    split at ok
    · unfold mappingOf at ok
      obtain ⟨_,hc,ok⟩ := Tier2Equiv.bind_ok ok
      split at ok <;> try contradiction
      obtain ⟨_,_,ok⟩ := Tier2Equiv.bind_ok ok
      obtain ⟨src,hs,ok⟩ := Tier2Equiv.bind_ok ok
      cases ok
      have sz := channel_map_size hs
      rw [fixed_size] at sz
      exact sz ▸ (Limits.check_eq_ok_iff ..).mp hc
    · obtain ⟨_,hc,h⟩ := Tier2Equiv.bind_ok ok
      cases h
      simpa [identityMapping, Limits.bound] using (Limits.check_eq_ok_iff ..).mp hc

private def signature (data : ByteArray) : ColourSpace → Nat
  | .icc r => if r.len < 20 || r.start+r.len > data.size then 1 else 5
  | _ => 1

private theorem signature_le (data : ByteArray) (s : ColourSpace) : signature data s ≤ 5 := by
  cases s <;> simp [signature] <;> split <;> decide

private def spaceCharge (data : ByteArray) : Option Jp2Header → Nat
  | none => 1
  | some h => visits (fun c => c.meth == 1 || c.meth == 2) h.colr +
      signature data (resolveColourSpace h)

private theorem space_le {L : Limits} {b : Nat} {hdr : Option Jp2Header}
    (h : Retained L b hdr) (data : ByteArray) : spaceCharge data hdr ≤ L.maxBoxes+5 := by
  cases hdr with
  | none => simp [spaceCharge]
  | some hdr =>
    have hc : hdr.colr.size ≤ L.maxBoxes := h.1
    have := visits_le (fun (c : ColourSpec) => c.meth == 1 || c.meth == 2) hdr.colr
    have := signature_le data (resolveColourSpace hdr)
    simp only [spaceCharge]; omega

/-- All resolver charges other than channel layout. Both format arrays are
priced when mapping succeeds, including when the subsequent CDEF rejects. -/
def resolverCharge (L : Limits) (data : ByteArray) (hdr : Option Jp2Header)
    (comps : Array Marker.Component) :=
  selectionCharge L hdr comps.size + match select L hdr comps.size with
    | .error _ => 0
    | .ok m => spaceCharge data hdr + 2*comps.size + 3*m.sources.size

/-- Uniform metadata tariff before adding the reusable CDEF layout charge. -/
def resolverBudget (L : Limits) (b : Nat) :=
  paletteBudget (min (b / 4) L.maxComponents) + 1+3*L.maxComponents + (L.maxBoxes+5) + 5*L.maxComponents

/-- Resolver work depends on the public limits and input length even if CMAP
or CDEF rejects. The retained palette supplies the bound on validation tags. -/
theorem resolver_work {L : Limits} {data : ByteArray} {hdr : Option Jp2Header}
    {comps : Array Marker.Component} (hc : Retained L data.size hdr)
    (hp : ∀ p, hdr.bind Jp2Header.pclr = some p → PaletteWithin L p)
    (hn : comps.size ≤ L.maxComponents) :
    resolverCharge L data hdr comps ≤ resolverBudget L data.size := by
  have hs := selection_le (n := comps.size) hc hp
  have hb := space_le hc data
  unfold resolverCharge resolverBudget
  split
  · omega
  · have := selected_size (by assumption : select L hdr comps.size = .ok _)
    rename_i m _
    change selectionCharge L hdr comps.size + (spaceCharge data hdr + 2*comps.size + 3*m.sources.size) ≤ _
    omega

/-- Run the original resolver with the full charge through its first error. -/
def measuredResolver (L : Limits) (data : ByteArray) (hdr : Option Jp2Header)
    (comps : Array Marker.Component) : Except Error Info × Nat :=
  let layout := measuredResolveLayout L data hdr comps
  (layout.1, resolverCharge L data hdr comps + layout.2)

/-- Full resolver erasure and charge on parsed metadata. The actual retained
CDEF length controls the layout bound even if there are zero output samples. -/
theorem resolve_prefix_work {L : Limits} {data : ByteArray} {hdr : Option Jp2Header}
    {comps : Array Marker.Component} (hc : Retained L data.size hdr)
    (hp : ∀ p, hdr.bind Jp2Header.pclr = some p → PaletteWithin L p)
    (hn : comps.size ≤ L.maxComponents) :
    let d := ((hdr.bind Jp2Header.cdef).getD #[]).size
    (measuredResolver L data hdr comps).1 = resolve L data hdr comps ∧
    (measuredResolver L data hdr comps).2 ≤ resolverBudget L data.size +
      layoutBudget L.maxComponents d (max 15 d) := by
  have hl := resolve_layout_work L data hdr comps
  exact ⟨hl.1, Nat.add_le_add (resolver_work hc hp hn) hl.2⟩

end JPEG2000.Spec.ColorResources.MappingPrefix
