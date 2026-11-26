import Spec.RoundTrip.PacketBlocks

/-!
# Image and codestream budgets for the reversible round trip

Plan.md §§4 (C10, S3), 5.3 and 7 (M7). T.800 A.4–A.6, B.5–B.7 and B.10.6.
The encoder checks the area of one component. Together with its side bound this
admits the default precinct count even at the largest allowed component count.
The remaining header budgets measure the entire codestream and the code-blocks
across all components. The Tier-2 pass budget counts the actual encoder records.
-/

namespace JPEG2000.Spec.RoundTrip

open JPEG2000.Encode (Params Image Encoded encodeDetailed BlockInfo)
open JPEG2000.Header (bandBlocks1 cdiv cdivPow)
open JPEG2000.Spec.Progression (packets)

variable {p : Params} {img : Image} {e : Encoded}

/-- The area check in the encoder's argument validation applies to the reference grid. -/
theorem imageArea_of_check {L : Limits} (h : Encode.check L p img = .ok ()) :
    img.width * img.height ≤ L.maxImageArea := by
  unfold Encode.check at h
  dsimp only at h
  by_cases hz : img.width = 0 ∨ img.height = 0
  · rw [ite_eq_left hz] at h
    cases h
  · rw [ite_eq_right hz] at h
    obtain ⟨_, _, h⟩ := Spec.Tier2Equiv.bind_ok h
    obtain ⟨_, _, h⟩ := Spec.Tier2Equiv.bind_ok h
    obtain ⟨_, ha, _⟩ := Spec.Tier2Equiv.bind_ok h
    exact (Limits.check_eq_ok_iff ..).mp ha

/-- Total code-blocks across all components and resolutions, computed from the image
dimensions, the decomposition depth and the two code-block exponents (B.5–B.7). -/
def imageCodeBlocks (p : Params) (img : Image) : Nat :=
  img.comps.size * ((List.range (p.levels + 1)).map fun r =>
    let x n o := bandBlocks1 0 img.width n o p.cbWidthExp
    let y n o := bandBlocks1 0 img.height n o p.cbHeightExp
    if r = 0 then x p.levels 0 * y p.levels 0 else
      let n := p.levels - r + 1
      x n 1 * y n 0 + x n 0 * y n 1 + x n 1 * y n 1).sum

private theorem fold_blocks (blocks precincts : Nat → Nat) (rs : List Nat) (a : Nat × Nat) :
    (rs.foldl (fun (b, q) r => (b + blocks r, q + precincts r)) a).1 =
      a.1 + (rs.map blocks).sum := by
  induction rs generalizing a with
  | nil => simp
  | cons r rs ih => cases a; simp [ih, Nat.add_assoc]

/-- Default precinct exponents leave the checked code-block exponents unchanged. Thus
the decoder's header count equals the image grid count for every guard/exponent table. -/
theorem imageCodeBlocks_eq_encCounts (hc : EncCheckFacts p img) (guard : Nat) (exps : Array Nat) :
    imageCodeBlocks p img = img.comps.size * (encCounts p img guard exps).1 := by
  unfold encCounts Header.tileCompCounts imageCodeBlocks
  rw [fold_blocks, Nat.zero_add]
  congr 2
  apply List.map_congr_left
  intro r _
  have hpp : (encParams p guard exps).precincts.getD r Marker.Precinct.default =
      Marker.Precinct.default := by
    simp only [encParams, Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
    split <;> rfl
  have hw := hc.cbw_le
  have hh := hc.cbh_le
  simp only [Header.numCodeBlocks, Header.CompParams.effCbWidthExp,
    Header.CompParams.effCbHeightExp, hpp]
  by_cases hr : r = 0 <;>
    simp (disch := omega) [hr, encRect, encParams, Marker.Precinct.default]

private theorem precinct_axis_bound (w d k : Nat) (hw : w ≤ k * 2^15) :
    cdivPow w (d + 15) ≤ k := by
  have hpow : 2^15 ≤ 2^(d+15) := Nat.pow_le_pow_right (by decide) (by omega)
  have h := Nat.le_trans hw (Nat.mul_le_mul_left k hpow)
  unfold cdivPow cdiv
  rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), Nat.succ_mul]
  omega

/-- The default image area forces at least one axis to fit in one default precinct.
The other axis spans at most four, so even 16384 components at 33 resolutions fit. -/
theorem precincts_le_default_of_check (h : Encode.check Limits.default p img = .ok ())
    (guard : Nat) (exps : Array Nat) :
    img.comps.size * (encCounts p img guard exps).2 ≤ Limits.default.maxPrecincts := by
  have hc := checkFacts_of_ok h
  have ha : img.width * img.height ≤ 2^28 := imageArea_of_check h
  have hside : img.width ≤ 2^15 ∨ img.height ≤ 2^15 := by
    by_cases hw : img.width ≤ 2^15
    · exact Or.inl hw
    · right
      by_cases hn : img.height ≤ 2^15
      · exact hn
      have hh : 32769 ≤ img.height := by omega
      have hprod := Nat.mul_le_mul (show 32769 ≤ img.width by omega) hh
      omega
  have four (r : Nat) : encResolutionPrecincts p.levels img.width img.height r ≤ 4 := by
    unfold encResolutionPrecincts
    rcases hside with h | h
    · exact Nat.mul_le_mul (precinct_axis_bound _ _ 1 (by simpa using h))
        (precinct_axis_bound _ _ 4 hc.height_le)
    · exact Nat.mul_le_mul (precinct_axis_bound _ _ 4 hc.width_le)
        (precinct_axis_bound _ _ 1 (by simpa using h))
  have bound (rs : List Nat) :
      (rs.map (encResolutionPrecincts p.levels img.width img.height)).sum ≤ rs.length * 4 := by
    induction rs with
    | nil => simp
    | cons r rs ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
      have := four r
      omega
  rw [encCounts_precincts]
  have hsum := bound (List.range (p.levels + 1))
  rw [List.length_range] at hsum
  have hr := Nat.mul_le_mul_right 4 (Nat.succ_le_succ hc.levels_le)
  exact Nat.le_trans (Nat.mul_le_mul hc.comps_le (Nat.le_trans hsum hr)) (by decide)

/-- For a successful encoding, only the physical codestream size and the aggregate
code-block grid remain to be checked for default header admission. -/
theorem headerFits_default_iff (he : encodeDetailed p img = .ok e) :
    HeaderFits Limits.default p img e.guardBits e.exponents e.codestream.size ↔
      e.codestream.size ≤ Limits.default.maxInputBytes ∧
      imageCodeBlocks p img ≤ Limits.default.maxCodeBlocks := by
  have h := (encodeDetailed_shape he).check
  have hc := checkFacts_of_ok h
  rw [imageCodeBlocks_eq_encCounts hc e.guardBits e.exponents]
  constructor
  · intro fits
    exact ⟨fits.inputBytes, fits.codeBlocks⟩
  · rintro ⟨hbytes, hblocks⟩
    have hp := precincts_le_default_of_check h e.guardBits e.exponents
    exact ⟨hbytes, hc.comps_le, hc.levels_le, by decide, hc.width_le, hc.height_le,
      imageArea_of_check h, by decide, by decide, by decide, Nat.le_trans hc.comps_le (by decide),
      hblocks, hp, Nat.le_trans hp (by decide)⟩

/-- The three physical inequalities for default header and aggregate Tier-2 pass admission.
`passesBefore` is zero at the start of an image. -/
structure ImageBudget (p : Params) (img : Image) (e : Encoded) (passesBefore : Nat := 0) : Prop where
  bytes : e.codestream.size ≤ Limits.default.maxInputBytes
  blocks : imageCodeBlocks p img ≤ Limits.default.maxCodeBlocks
  passes : passesBefore + (e.blocks.toList.map BlockInfo.numPasses).sum ≤ Limits.default.maxCodingPasses

instance {passesBefore : Nat} : Decidable (ImageBudget p img e passesBefore) :=
  decidable_of_iff (_ ∧ _ ∧ _) ⟨fun ⟨b, c, n⟩ => ⟨b, c, n⟩, fun h => ⟨h.bytes, h.blocks, h.passes⟩⟩

/-- The image budgets admit the encoded header under the decoder defaults. -/
theorem ImageBudget.headerFits {passesBefore : Nat} (budget : ImageBudget p img e passesBefore)
    (he : encodeDetailed p img = .ok e) :
    HeaderFits Limits.default p img e.guardBits e.exponents e.codestream.size :=
  (headerFits_default_iff he).2 ⟨budget.bytes, budget.blocks⟩

/-- LRCP charges exactly the budgeted pass sum, including any passes already charged. -/
theorem ImageBudget.packetPasses {passesBefore : Nat} (budget : ImageBudget p img e passesBefore)
    {prec infos} (hp : ReversibleTilePackets p img e prec infos) :
    passesBefore + ((packets (encLayout p img e.guardBits e.exponents) .lrcp #[]).map
      fun q => passesOf (encBands prec q)).sum ≤ Limits.default.maxCodingPasses := by
  rw [hp.packetPasses]
  exact budget.passes

/-- For every successful reversible encoding, the three image budgets are necessary
and sufficient for `HeaderFits` and the pass premise of the LRCP tile round trip. -/
theorem imageBudget_iff {passesBefore : Nat} (he : encodeDetailed p img = .ok e)
    (hrev : p.reversible = true) :
    ImageBudget p img e passesBefore ↔
      HeaderFits Limits.default p img e.guardBits e.exponents e.codestream.size ∧
        ∀ {prec infos}, ReversibleTilePackets p img e prec infos →
        passesBefore + ((packets (encLayout p img e.guardBits e.exponents) .lrcp #[]).map
          fun q => passesOf (encBands prec q)).sum ≤ Limits.default.maxCodingPasses := by
  constructor
  · exact fun budget => ⟨budget.headerFits he, fun hp => budget.packetPasses hp⟩
  · rintro ⟨fits, hpasses⟩
    obtain ⟨prec, infos, hp⟩ := encodeDetailed_tilePackets he hrev
    obtain ⟨hbytes, hblocks⟩ := (headerFits_default_iff he).1 fits
    exact ⟨hbytes, hblocks, hp.packetPasses ▸ hpasses hp⟩

end JPEG2000.Spec.RoundTrip
