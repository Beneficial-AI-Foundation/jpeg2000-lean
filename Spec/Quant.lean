import JPEG2000.Header
import JPEG2000.Tier2.Geometry
import Spec.Tier1.Decode

/-!
# Spec: dequantisation (T.800 Annex E) and ROI max-shift (T.800 Annex H)

Plan.md §4 (C8, C9), §5.1 (spec first), §5.4 (numbers). Task 5.1.

Exact definitions over `Nat`/`Int`/`Rat` of what happens to a code-block coefficient between
Tier-1 (`Spec.Tier1.Coeff`) and the inverse wavelet transform:

* **E.1, Equation E-2** — `magBits`: `Mb = G + εb − 1` magnitude bit-planes of a sub-band
  (`G` guard bits, `εb` the band's exponent).
* **E.1.1, Equation E-3** — `stepSize`: `Δb = 2^(Rb − εb) · (1 + μb / 2^11)`, as an exact
  rational, with **E-4** `Rb = bit depth + log2 gain_b` (`nominalRange`, gains of Table E-1:
  `log2Gain` = 0 for LL, 1 for HL/LH, 2 for HH).
* **E-5** — `derivedExponent`: derived quantisation `εb = εo − NL + nb`, `μb = μo`.
  `JPEG2000.Header.bandSteps` already expands it (band `i > 0` gets `εo − (i − 1)/3`);
  `bandSteps_derived_exponent` proves that this is E-5 with `nb = bandLevel NL r`.
* **E.1.1.2, Equation E-6** — `reconstructE6`: `Rqb = (qb + r·2^(Mb − Nb))·Δb` for
  `qb > 0`, `(qb − r·2^(Mb − Nb))·Δb` for `qb < 0`, `0` for `qb = 0`, with the
  reconstruction parameter `r` (we use `r = 1/2`, as OpenJPEG).
* **Annex H (max-shift)** — `roiUnshift`: with `s = SPrgn > 0` the code-block carries
  `Mb + s` bit-planes; a decoded magnitude `≥ 2^s` belongs to the ROI and is shifted down by
  `s`, a magnitude `< 2^s` is background and is kept (H.1/H.2; OpenJPEG
  `opj_t1_clbl_decode_processor`, see below for its doubled-scale threshold).

## Our Tier-1 convention and `Nb`

`Spec.Tier1.Coeff.mag` holds the decoded magnitude bits at their place value (bit-plane `p`
adds `2^p`; no reconstruction offset) and `lsbPlane` is the plane of the last decoded bit,
so in E.1.1.2's notation `Nb(u, v) = Mb − lsbPlane` and `2^(Mb − Nb) = 2^lsbPlane`. Hence
E-6 with `r = 1/2` reads, for a non-zero magnitude `q = mag`,

  `Rq = ±(mag + 2^lsbPlane / 2) · Δb`                                  (`reconstructIrrev`)

(`reconstructIrrev_eq_E6` proves the correspondence). With ROI the block's planes are
counted with the extra `s` (Tier-2 passes `Mb + s`): `roiUnshift` divides a ROI magnitude by
`2^s` and lowers its `lsbPlane` by `s` (to 0 if the last bit decoded lay below plane `s`,
where a ROI coefficient has only zero bits).

## Reversible path (5/3)

No quantisation (`Δb = 1`); OpenJPEG computes `(2·mag + 2^lsbPlane) / 2` with C truncation,
i.e. `mag + ⌊2^lsbPlane / 2⌋` on the magnitude: the exact index when every bit-plane was
decoded (`lsbPlane = 0`, `reconstructRev_full`), the midpoint `r = 1/2` when the block was
truncated (`lsbPlane ≥ 1`, `reconstructRev_eq_irrev`). `reconstructRev` is this rule.
The transform decides the path (as OpenJPEG `qmfbid`): 5/3 → `reconstructRev` whatever the
quantisation style; 9/7 → `reconstructIrrev` with `Δb` of E-3 (style 0 = mantissa 0).

## Gain convention (coordination with the 9/7 of task 5.3)

`Δb` here is T.800's (E-4 with the Table E-1 gains), which matches T.800's 9/7 synthesis
normalisation (F.3.8.2: low-pass samples scaled by `K`, high-pass by `1/K`). OpenJPEG instead
uses gain 0 for every band in its decoder (`opj_tcd_init_tile`, "BUG_WEIRD_TWO_INVK") and
compensates by scaling high-pass samples by `2/K` in its 9/7; both give the same samples.
A 9/7 implementation consuming these coefficients must use T.800's `1/K`.

## OpenJPEG ROI threshold (documented deviation)

OpenJPEG stores Tier-1 magnitudes doubled plus the midpoint (`2·mag + 2^lsbPlane`) and
compares *that* with `2^s`; a background magnitude `≥ 2^(s−1)` is then treated as ROI.
We follow T.800 (compare `mag` with `2^s`); the two agree whenever background magnitudes
stay below `2^(s−1)`. `Tests/Quant.lean` transcribes OpenJPEG's rule and checks both.
-/

namespace JPEG2000.Spec.Quant

open JPEG2000 JPEG2000.Header JPEG2000.Marker
open JPEG2000.Tier2.Geometry (Band bandLevel)
open JPEG2000.Spec.Tier1 (Coeff)

/-! ## E.1: bit-planes, step sizes -/

/-- `log2` of the sub-band gain (T.800 Table E-1): LL 0, HL and LH 1, HH 2. -/
def log2Gain : Band → Nat
  | .LL => 0
  | .HL => 1
  | .LH => 1
  | .HH => 2

/-- Equation E-4: the nominal dynamic range `Rb` of a sub-band, component bit depth plus
`log2 gain_b`. -/
def nominalRange (depth : Nat) (b : Band) : Nat := depth + log2Gain b

/-- Equation E-2: `Mb = G + εb − 1` magnitude bit-planes (`G` guard bits, exponent `εb`). -/
def magBits (guard exponent : Nat) : Nat := guard + exponent - 1

/-- Equation E-5 (derived quantisation): `εb = εo − NL + nb` for a band at decomposition
level `nb` (the mantissa is `μo` unchanged). -/
def derivedExponent (eo nl nb : Nat) : Nat := eo + nb - nl

/-- Equation E-3: `Δb = 2^(Rb − εb) · (1 + μb / 2^11)` with `Rb = depth + gain` (E-4, `gain`
the `log2` band gain), as an exact rational `2^Rb · (2^11 + μb) / 2^(εb + 11)`. -/
def stepSize (depth gain exponent mantissa : Nat) : Rat :=
  ((2 ^ (depth + gain) * (2048 + mantissa) : Nat) : Rat) / ((2 ^ (exponent + 11) : Nat) : Rat)

/-- The index of a sub-band in `CompParams.steps` (band order LL, then HL, LH, HH per
resolution 1…NL; T.800 A.6.4). -/
def bandIndex (r : Nat) (b : Band) : Nat := if r = 0 then 0 else 3 * (r - 1) + b.index

/-- The dequantisation parameters of one sub-band. -/
structure BandQuant where
  /-- The 5/3 reversible transform is used (no quantisation, `reconstructRev`). -/
  reversible : Bool
  /-- ROI max-shift `s` (`SPrgn`, 0 without RGN). -/
  roiShift : Nat
  /-- Guard bits `G`. -/
  guard : Nat
  /-- Nominal dynamic range `Rb` (E-4). -/
  range : Nat
  /-- Exponent `εb`. -/
  exponent : Nat
  /-- Mantissa `μb` (< 2^11). -/
  mantissa : Nat
  deriving Repr, DecidableEq, Inhabited

/-- `Mb` (E-2) of the band. -/
def BandQuant.Mb (q : BandQuant) : Nat := magBits q.guard q.exponent

/-- `Δb` (E-3) of the band. -/
def BandQuant.delta (q : BandQuant) : Rat := stepSize q.range 0 q.exponent q.mantissa

/-- The parameters of band `b` of resolution `r` of a tile-component of bit depth `depth`
(merged parameters `p`; step sizes already expanded by E-5). -/
def bandQuant (p : CompParams) (depth r : Nat) (b : Band) : BandQuant :=
  let st := p.steps.getD (bandIndex r b) default
  { reversible := p.transform == .reversible53, roiShift := p.roiShift, guard := p.guardBits,
    range := nominalRange depth b, exponent := st.exponent.toNat,
    mantissa := st.mantissa.toNat }

/-! ## Annex H: ROI max-shift -/

/-- Annex H (max-shift) at the decoder: a magnitude `≥ 2^s` is an ROI coefficient, divided
by `2^s` (its last decoded plane moves down by `s`, saturating at 0); a smaller one is
background and is kept. -/
def roiUnshift (s : Nat) (c : Coeff) : Coeff :=
  if 2 ^ s ≤ c.mag then { c with mag := c.mag / 2 ^ s, lsbPlane := c.lsbPlane - s } else c

/-! ## E.1.1.2: reconstruction -/

/-- Equation E-6, literally: `(q + r·2^(Mb − Nb))·Δ` for `q > 0`, `(q − r·2^(Mb − Nb))·Δ`
for `q < 0`, `0` for `q = 0`. -/
def reconstructE6 (r : Rat) (Mb Nb : Nat) (q : Int) (delta : Rat) : Rat :=
  if 0 < q then ((q : Rat) + r * ((2 ^ (Mb - Nb) : Nat) : Rat)) * delta
  else if q < 0 then ((q : Rat) - r * ((2 ^ (Mb - Nb) : Nat) : Rat)) * delta
  else 0

/-- Irreversible reconstruction (E-6 with `r = 1/2`, `2^(Mb − Nb) = 2^lsbPlane`):
`±(mag + 2^lsbPlane / 2)·Δ`, `0` for a zero magnitude. -/
def reconstructIrrev (delta : Rat) (c : Coeff) : Rat :=
  if c.mag = 0 then 0
  else
    let m : Rat := ((c.mag : Rat) + ((2 ^ c.lsbPlane : Nat) : Rat) / 2) * delta
    if c.sign then -m else m

/-- Reversible reconstruction: `±(mag + ⌊2^lsbPlane / 2⌋)` (the index itself when all
bit-planes were decoded, the midpoint otherwise; OpenJPEG's `(2·mag + 2^lsb) / 2`). -/
def reconstructRev (c : Coeff) : Int :=
  if c.mag = 0 then 0
  else
    let m : Int := (c.mag : Int) + ((2 ^ c.lsbPlane / 2 : Nat) : Int)
    if c.sign then -m else m

/-- One coefficient, reversible path: ROI unshift, then `reconstructRev`. -/
def dequantRev (s : Nat) (c : Coeff) : Int := reconstructRev (roiUnshift s c)

/-- One coefficient, irreversible path: ROI unshift, then `reconstructIrrev Δ`. -/
def dequantIrrev (s : Nat) (delta : Rat) (c : Coeff) : Rat :=
  reconstructIrrev delta (roiUnshift s c)

/-- A decoded code-block (raster order), reversible path. -/
def dequantBlockRev (s : Nat) (cs : Array Coeff) : Array Int := cs.map (dequantRev s)

/-- A decoded code-block (raster order), irreversible path. -/
def dequantBlockIrrev (s : Nat) (delta : Rat) (cs : Array Coeff) : Array Rat :=
  cs.map (dequantIrrev s delta)

/-- The irreversible result in fixed point with `F` fractional bits, as an exact rational:
`dequantIrrev s Δ c · 2^F` (the quantity the fast path rounds). -/
def dequantIrrevScaled (s : Nat) (delta : Rat) (F : Nat) (c : Coeff) : Rat :=
  dequantIrrev s delta c * ((2 ^ F : Nat) : Rat)

/-! ## Lemmas -/

/-- E-3 in its literal form: `Δb · 2^εb = 2^Rb · (1 + μb / 2^11)`. -/
theorem stepSize_mul_pow (depth gain e m : Nat) :
    stepSize depth gain e m * ((2 ^ e : Nat) : Rat) =
      ((2 ^ (depth + gain) : Nat) : Rat) * (1 + (m : Rat) / 2048) := by
  have h2 : ((2 ^ (e + 11) : Nat) : Rat) = ((2 ^ e : Nat) : Rat) * 2048 := by
    rw [Nat.pow_add]; push_cast; rfl
  have hp : ((2 ^ e : Nat) : Rat) ≠ 0 := by
    have : 0 < 2 ^ e := Nat.two_pow_pos e
    exact_mod_cast Nat.ne_of_gt this
  unfold stepSize
  rw [h2]
  push_cast
  grind

/-- No quantisation (mantissa 0, `εb = Rb`) gives `Δb = 1`. -/
theorem stepSize_unit (depth gain : Nat) : stepSize depth gain (depth + gain) 0 = 1 := by
  have hp : ((2 ^ (depth + gain + 11) : Nat) : Rat) ≠ 0 := by
    have : 0 < 2 ^ (depth + gain + 11) := Nat.two_pow_pos _
    exact_mod_cast Nat.ne_of_gt this
  unfold stepSize
  rw [Nat.add_zero, show 2 ^ (depth + gain) * 2048 = 2 ^ (depth + gain + 11) by
    rw [Nat.pow_add 2 (depth + gain) 11]]
  grind

/-- E-5 as `bandSteps` expands it: for derived quantisation with `εo ≥ NL − 1`, the exponent
stored for band `b ≠ LL` of resolution `1 ≤ r ≤ NL` is `εo − NL + nb` with
`nb = bandLevel NL r`, and the LL band keeps `εo` (`nb = NL`). -/
theorem bandSteps_derived_exponent (pos nl : Nat) (s : StepSize) (steps : Array StepSize)
    (h : bandSteps pos nl (.derived s) = .ok steps) (r : Nat) (b : Band)
    (hr : r ≤ nl) (hb : (r = 0 ∧ b = .LL) ∨ (0 < r ∧ b ≠ .LL)) :
    (steps.getD (bandIndex r b) default).exponent.toNat =
      derivedExponent s.exponent.toNat nl (bandLevel nl r) ∧
    (steps.getD (bandIndex r b) default).mantissa = s.mantissa := by
  unfold bandSteps at h
  simp only at h
  split at h
  · exact absurd h (by simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw])
  · rename_i hle
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    have hi : bandIndex r b < 3 * nl + 1 := by
      rcases hb with ⟨h0, hb⟩ | ⟨h0, hb⟩
      · subst h0; subst hb; simp [bandIndex]
      · have hr0 : r ≠ 0 := by omega
        cases b <;> simp_all [bandIndex, Band.index] <;> omega
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range]
    simp only [hi, ↓reduceIte, Option.map_some, Option.getD_some]
    unfold bandIndex derivedExponent bandLevel
    rcases hb with ⟨h0, hb⟩ | ⟨h0, hb⟩
    · subst h0; subst hb
      simp only [↓reduceIte]
      exact ⟨by omega, trivial⟩
    · have hr0 : r ≠ 0 := by omega
      have hidx : 3 * (r - 1) + b.index ≠ 0 := by cases b <;> simp_all [Band.index]
      have hq : (3 * (r - 1) + b.index - 1) / 3 = r - 1 := by
        cases b <;> simp_all [Band.index] <;> omega
      simp only [hr0, ↓reduceIte, hidx, hq]
      refine ⟨?_, trivial⟩
      have hlt : (r - 1) < 256 := by have := s.exponent.toNat_lt; omega
      have hle' : (r - 1).toUInt8 ≤ s.exponent := by
        rw [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat', Nat.mod_eq_of_lt hlt]; omega
      rw [UInt8.toNat_sub_of_le _ _ hle', UInt8.toNat_ofNat', Nat.mod_eq_of_lt hlt]
      omega

/-- ROI unshift with `s = 0` changes nothing. -/
theorem roiUnshift_zero (c : Coeff) : roiUnshift 0 c = c := by
  unfold roiUnshift
  split <;> simp

/-- ROI unshift keeps a background coefficient (magnitude `< 2^s`) unchanged. -/
theorem roiUnshift_background (s : Nat) (c : Coeff) (h : c.mag < 2 ^ s) :
    roiUnshift s c = c := by
  unfold roiUnshift
  simp [Nat.not_le.mpr h]

/-- ROI unshift recovers the index of an ROI coefficient shifted up by `s` at the encoder
(`mag = q·2^s`, `q ≥ 1`), and lowers its last decoded plane by `s`. -/
theorem roiUnshift_roi (s q : Nat) (c : Coeff) (hq : 0 < q) (h : c.mag = q * 2 ^ s) :
    (roiUnshift s c).mag = q ∧ (roiUnshift s c).lsbPlane = c.lsbPlane - s := by
  have hp : 0 < 2 ^ s := Nat.two_pow_pos s
  have hle : 2 ^ s ≤ q * 2 ^ s := Nat.le_mul_of_pos_left _ hq
  unfold roiUnshift
  simp only [h, hle, ↓reduceIte]
  exact ⟨Nat.mul_div_cancel _ hp, trivial⟩

/-- Reversible reconstruction with every bit-plane decoded (`lsbPlane = 0`, i.e.
`Nb = Mb`) is the identity on sign · magnitude. -/
theorem reconstructRev_full (c : Coeff) (h : c.lsbPlane = 0) : reconstructRev c = c.value := by
  unfold reconstructRev Spec.Tier1.Coeff.value
  rw [h]
  split
  · rename_i hm; simp [hm]
  · simp

/-- On a truncated coefficient (`lsbPlane ≥ 1`) the reversible reconstruction is E-6 with
`r = 1/2` and `Δ = 1`. -/
theorem reconstructRev_eq_irrev (c : Coeff) (h : 1 ≤ c.lsbPlane) :
    ((reconstructRev c : Int) : Rat) = reconstructIrrev 1 c := by
  have hp : 2 ^ c.lsbPlane / 2 = 2 ^ (c.lsbPlane - 1) := by
    obtain ⟨k, hk⟩ : ∃ k, c.lsbPlane = k + 1 := ⟨c.lsbPlane - 1, by omega⟩
    rw [hk, Nat.pow_succ, Nat.mul_div_cancel _ (by decide)]; rfl
  have hq : ((2 ^ c.lsbPlane : Nat) : Rat) / 2 = ((2 ^ (c.lsbPlane - 1) : Nat) : Rat) := by
    obtain ⟨k, hk⟩ : ∃ k, c.lsbPlane = k + 1 := ⟨c.lsbPlane - 1, by omega⟩
    rw [hk, Nat.pow_succ]; push_cast; grind
  unfold reconstructRev reconstructIrrev
  rw [hp, hq]
  split
  · simp
  · split <;> push_cast <;> grind

/-- The irreversible reconstruction is E-6 with `r = 1/2` and `Nb = Mb − lsbPlane` (needs
`lsbPlane ≤ Mb`), on the signed index `q = ±mag`. -/
theorem reconstructIrrev_eq_E6 (Mb : Nat) (delta : Rat) (c : Coeff) (h : c.lsbPlane ≤ Mb) :
    reconstructIrrev delta c = reconstructE6 (1 / 2) Mb (Mb - c.lsbPlane) c.value delta := by
  have hN : Mb - (Mb - c.lsbPlane) = c.lsbPlane := by omega
  unfold reconstructIrrev reconstructE6 Spec.Tier1.Coeff.value
  rw [hN]
  by_cases hm : c.mag = 0
  · simp [hm]
  · have hpos : (0 : Int) < c.mag := by omega
    simp only [hm, ↓reduceIte]
    cases c.sign
    · simp only [Bool.false_eq_true, ↓reduceIte, hpos, Rat.intCast_natCast]; grind
    · have hneg : -(c.mag : Int) < 0 := by omega
      have hnp : ¬ (0 < -(c.mag : Int)) := by omega
      simp only [↓reduceIte, hnp, hneg]; push_cast; grind

/-- The reversible reconstruction depends only on the signed value `±mag` and `lsbPlane`
(the sign of a zero magnitude is irrelevant). -/
theorem reconstructRev_congr (c d : Coeff) (hv : c.value = d.value)
    (hl : c.lsbPlane = d.lsbPlane) : reconstructRev c = reconstructRev d := by
  unfold reconstructRev
  unfold Spec.Tier1.Coeff.value at hv
  rw [hl]
  have hm : c.mag = d.mag := by
    revert hv; cases c.sign <;> cases d.sign <;> simp <;> omega
  rw [hm]
  split
  · rfl
  · rename_i h0
    have hs : c.sign = d.sign := by
      revert hv; cases c.sign <;> cases d.sign <;> simp <;> omega
    rw [hs]

/-- ROI unshift followed by either reconstruction depends only on `±mag` and `lsbPlane`. -/
theorem roiUnshift_congr (s : Nat) (c d : Coeff) (hv : c.value = d.value)
    (hl : c.lsbPlane = d.lsbPlane) :
    (roiUnshift s c).value = (roiUnshift s d).value ∧
      (roiUnshift s c).lsbPlane = (roiUnshift s d).lsbPlane := by
  unfold Spec.Tier1.Coeff.value at hv
  have hm : c.mag = d.mag := by
    revert hv; cases c.sign <;> cases d.sign <;> simp <;> omega
  unfold roiUnshift Spec.Tier1.Coeff.value
  rw [hm, hl]
  by_cases h : 2 ^ s ≤ d.mag
  · simp only [h, ↓reduceIte]
    refine ⟨?_, trivial⟩
    by_cases h0 : d.mag = 0
    · simp [h0]
    · have hs : c.sign = d.sign := by
        revert hv; cases c.sign <;> cases d.sign <;> simp <;> omega
      rw [hs]
  · simp only [h, ↓reduceIte]
    exact ⟨by simp only [hm] at hv ⊢; exact hv, hl⟩

/-- `dequantRev` depends only on `±mag` and `lsbPlane`. -/
theorem dequantRev_congr (s : Nat) (c d : Coeff) (hv : c.value = d.value)
    (hl : c.lsbPlane = d.lsbPlane) : dequantRev s c = dequantRev s d := by
  obtain ⟨h1, h2⟩ := roiUnshift_congr s c d hv hl
  exact reconstructRev_congr _ _ h1 h2

/-- `dequantIrrev` depends only on `±mag` and `lsbPlane`. -/
theorem dequantIrrev_congr (s : Nat) (delta : Rat) (c d : Coeff) (hv : c.value = d.value)
    (hl : c.lsbPlane = d.lsbPlane) : dequantIrrev s delta c = dequantIrrev s delta d := by
  obtain ⟨h1, h2⟩ := roiUnshift_congr s c d hv hl
  unfold dequantIrrev
  generalize roiUnshift s c = c' at h1 h2
  generalize roiUnshift s d = d' at h1 h2
  unfold reconstructIrrev
  unfold Spec.Tier1.Coeff.value at h1
  have hm : c'.mag = d'.mag := by
    revert h1; cases c'.sign <;> cases d'.sign <;> simp <;> omega
  rw [hm, h2]
  split
  · rfl
  · rename_i h0
    have hs : c'.sign = d'.sign := by
      revert h1; cases c'.sign <;> cases d'.sign <;> simp <;> omega
    rw [hs]

end JPEG2000.Spec.Quant
