import Spec.Tier1Equiv.Modes.Strict

/-!
# C3 with passes below bit-plane 0 dropped (task 5.8)

Plan.md §4 (C3), §5.1; T.800 D.2 (a block of `K` coded bit-planes has `3K − 2` coding
passes: the cleanup pass of bit-plane `K − 1`, then three passes per lower bit-plane), B.10.6
(Tier-2 signals the number of included passes).

Some encoders signal more passes than `3K − 2` (`kodak_2layers_lrcp.j2c`, `test_lossless.j2k`
of the OpenJPEG test data). Such passes would lie below bit-plane 0: they code no coefficient
bit, and OpenJPEG ignores them (`opj_t1_decode_cblk` stops once `bpno_plus_one` reaches 0).
Both Tier-1 decoders therefore drop them first and decode the rest **exactly** — the spec
`Spec.Tier1.decodeCodeBlock = decodeCodeBlockExact ∘ CodeBlock.clampPasses`, the fast
`JPEG2000.Tier1.decodeCodeBlock` (plain, `min n (3K − 2)` passes) and
`JPEG2000.Tier1.decodeCodeBlockSegs` (every style; after checking every byte range,
`decodeCodeBlockSegsExact ∘ clampSegs`).

The C3 theorems keep their names and statements (now about the clamping decoders) and follow
from the `…_exact` theorems about the exact decoders:

* `Spec.Tier1Equiv.c3_plain` from `c3_plain_exact` (`specBlock_clamp`: clamping the one-segment
  spec block is the spec block of `min n (3K − 2)` passes);
* `Spec.Tier1EquivM.c3_all`, `c3_all_unsup`, `c3_all_strict` from their `…_exact` versions
  (`specBlockM_clamp`: clamping the spec block of `segs` is the spec block of `clampSegs segs`;
  `clampSegs` keeps byte ranges and does not add passes).
-/

namespace JPEG2000.Spec.Tier1Equiv

open JPEG2000
open JPEG2000.Tier2.Geometry (Band)
open JPEG2000.Spec.Tier1 (CodeBlock)

/-- Clamping the one-segment spec block of `n` passes gives the spec block of
`min n (3K − 2)` passes. -/
theorem specBlock_clamp (data : ByteArray) (start stop w h : Nat) (band : Band)
    (Mb zbp n : Nat) :
    (specBlock data start stop w h band Mb zbp n).clampPasses =
      specBlock data start stop w h band Mb zbp (min n (3 * (Mb - zbp) - 2)) := by
  have hn := specBlock_numPasses data start stop w h band Mb zbp n
  unfold CodeBlock.clampPasses
  rw [hn]
  have hK : (specBlock data start stop w h band Mb zbp n).codedPlanes = Mb - zbp := rfl
  rw [hK]
  by_cases hle : n ≤ 3 * (Mb - zbp) - 2
  · simp only [hle, ↓reduceIte, Nat.min_eq_left hle]
  · simp only [hle, ↓reduceIte]
    rw [Nat.min_eq_right (by omega)]
    simp only [specBlock, CodeBlock.ofData, Spec.Tier1.Segment.single]
    have hn0 : n ≠ 0 := by omega
    simp only [hn0, ↓reduceIte]
    by_cases hB : 3 * (Mb - zbp) - 2 = 0
    · rw [hB]; simp [Spec.Tier1.truncSegments]
    · simp only [hB, ↓reduceIte, Spec.Tier1.truncSegments,
        Nat.le_of_lt (by omega : 3 * (Mb - zbp) - 2 < n)]

/-- **C3 for plain mode** (Plan.md §4): the fast Tier-1 decoder equals the Annex D reference
decoder on every plain-mode code-block with one codeword segment `data[start, stop)` — both
fail with the same error, or both succeed and agree, coefficient by coefficient, on the value,
the significance and `lsbPlane` (the decoded bit count `Nb = Mb − lsbPlane` of E.1.1.2).
Both decode `min n (3K − 2)` passes (passes below bit-plane 0 are dropped, task 5.8).
Side conditions: the segment lies in the buffer and at most 31 bit-planes are coded when a
pass is decoded (the fast decoder's two extra checks). -/
theorem c3_plain (data : ByteArray) (start stop w h : Nat) (band : Band) (Mb zbp n : Nat)
    (hrange : start ≤ stop ∧ stop ≤ data.size) (hK : 0 < n → Mb - zbp ≤ 31) :
    match JPEG2000.Tier1.decodeCodeBlock data start stop w h band Mb zbp n,
      Spec.Tier1.decodeCodeBlock (specBlock data start stop w h band Mb zbp n) with
    | .error e1, .error e2 => e1 = e2
    | .ok o, .ok cs =>
      cs.size = w * h ∧ o.plane.width = w ∧ o.plane.height = h ∧
      ∀ x y, x < w → y < h →
        (o.plane.get? (y * w + x)).map Int32.toInt = some (cs.getD (y * w + x) {}).value ∧
        o.sig x y = (cs.getD (y * w + x) {}).sig ∧
        o.lsbPlane x y = (cs.getD (y * w + x) {}).lsbPlane
    | _, _ => False := by
  have C := c3_plain_exact data start stop w h band Mb zbp (min n (3 * (Mb - zbp) - 2)) hrange
    (fun h0 => hK (by omega))
  rw [← specBlock_clamp] at C
  exact C

end JPEG2000.Spec.Tier1Equiv

namespace JPEG2000.Spec.Tier1EquivM

open JPEG2000
open JPEG2000.Tier2.Geometry (Band)
open JPEG2000.Spec.Tier1 (CodeBlock Segment)
open JPEG2000.Spec.Tier1Equiv

/-- The spec segment of a fast segment (as `specBlockM` builds it). -/
abbrev segOf (data : ByteArray) (sg : JPEG2000.Tier1.Seg) : Segment :=
  ⟨MQEquiv.segment data sg.start sg.stop, sg.passes⟩

/-- Truncation commutes with reading fast segments as spec segments. -/
theorem truncSegments_map (data : ByteArray) :
    ∀ (l : List JPEG2000.Tier1.Seg) (m : Nat),
      Spec.Tier1.truncSegments (l.map (segOf data)) m =
        (JPEG2000.Tier1.truncSegs l m).map (segOf data)
  | [], m => by simp [Spec.Tier1.truncSegments, JPEG2000.Tier1.truncSegs]
  | s :: ss, m => by
    simp only [List.map_cons, Spec.Tier1.truncSegments, JPEG2000.Tier1.truncSegs]
    by_cases h0 : m = 0
    · simp [h0]
    · by_cases h1 : m ≤ s.passes
      · simp [h0, h1]
      · simp [h0, h1, truncSegments_map data ss]

/-- A truncated segment keeps the byte range of a segment of the list. -/
theorem mem_truncSegs :
    ∀ (l : List JPEG2000.Tier1.Seg) (m : Nat) (sg : JPEG2000.Tier1.Seg),
      sg ∈ JPEG2000.Tier1.truncSegs l m → ∃ s ∈ l, sg.start = s.start ∧ sg.stop = s.stop
  | [], m, sg, h => by simp [JPEG2000.Tier1.truncSegs] at h
  | s :: ss, m, sg, h => by
    simp only [JPEG2000.Tier1.truncSegs] at h
    by_cases h0 : m = 0
    · simp [h0] at h
    · by_cases h1 : m ≤ s.passes
      · simp only [h0, h1, ↓reduceIte, List.mem_singleton] at h
        subst h
        exact ⟨s, List.mem_cons_self .., rfl, rfl⟩
      · simp only [h0, h1, ↓reduceIte, List.mem_cons] at h
        rcases h with h | h
        · subst h; exact ⟨sg, List.mem_cons_self .., rfl, rfl⟩
        · obtain ⟨s', hs', e1, e2⟩ := mem_truncSegs ss _ sg h
          exact ⟨s', List.mem_cons_of_mem _ hs', e1, e2⟩

/-- Truncation adds no pass. -/
theorem truncSegs_sum_le :
    ∀ (l : List JPEG2000.Tier1.Seg) (m : Nat),
      ((JPEG2000.Tier1.truncSegs l m).map (·.passes)).sum ≤ (l.map (·.passes)).sum
  | [], m => by simp [JPEG2000.Tier1.truncSegs]
  | s :: ss, m => by
    simp only [JPEG2000.Tier1.truncSegs]
    by_cases h0 : m = 0
    · simp [h0]
    · by_cases h1 : m ≤ s.passes
      · simp only [h0, h1, ↓reduceIte, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil, List.sum_cons]
        omega
      · simp only [h0, h1, ↓reduceIte, List.map_cons, List.sum_cons]
        have := truncSegs_sum_le ss (m - s.passes)
        omega

/-- **Clamping the spec block of `segs` is the spec block of `clampSegs segs`.** -/
theorem specBlockM_clamp (data : ByteArray) (segs : Array JPEG2000.Tier1.Seg) (w h : Nat)
    (band : Band) (style : UInt8) (Mb zbp : Nat) :
    (specBlockM data segs w h band style Mb zbp).clampPasses =
      specBlockM data (JPEG2000.Tier1.clampSegs segs (Mb - zbp)) w h band style Mb zbp := by
  unfold CodeBlock.clampPasses JPEG2000.Tier1.clampSegs
  rw [specBlockM_numPasses, segsPasses_eq]
  have hK : (specBlockM data segs w h band style Mb zbp).codedPlanes = Mb - zbp := rfl
  rw [hK]
  by_cases hle : (segs.toList.map (·.passes)).sum ≤ 3 * (Mb - zbp) - 2
  · simp only [hle, ↓reduceIte]
  · simp only [hle, ↓reduceIte, specBlockM]
    rw [← truncSegments_map]

/-- The clamped segments still lie in the buffer. -/
theorem clampSegs_range (data : ByteArray) (segs : Array JPEG2000.Tier1.Seg) (K : Nat)
    (hrange : ∀ sg ∈ segs.toList, sg.start ≤ sg.stop ∧ sg.stop ≤ data.size) :
    ∀ sg ∈ (JPEG2000.Tier1.clampSegs segs K).toList, sg.start ≤ sg.stop ∧ sg.stop ≤ data.size := by
  intro sg hsg
  unfold JPEG2000.Tier1.clampSegs at hsg
  split at hsg
  · exact hrange sg hsg
  · obtain ⟨s, hs, e1, e2⟩ := mem_truncSegs _ _ sg hsg
    rw [e1, e2]
    exact hrange s hs

/-- The clamped segments have no more passes. -/
theorem clampSegs_sum_le (segs : Array JPEG2000.Tier1.Seg) (K : Nat) :
    ((JPEG2000.Tier1.clampSegs segs K).toList.map (·.passes)).sum ≤
      (segs.toList.map (·.passes)).sum := by
  unfold JPEG2000.Tier1.clampSegs
  split
  · exact Nat.le_refl _
  · exact truncSegs_sum_le _ _

/-- No range check fails when every range lies in the buffer. -/
theorem badRange_false (data : ByteArray) (segs : Array JPEG2000.Tier1.Seg)
    (hrange : ∀ sg ∈ segs.toList, sg.start ≤ sg.stop ∧ sg.stop ≤ data.size) :
    JPEG2000.Tier1.badRange data segs = false := by
  unfold JPEG2000.Tier1.badRange
  rw [Bool.eq_false_iff]
  intro hc
  rw [Array.any_eq_true'] at hc
  obtain ⟨sg, hm, hb⟩ := hc
  have := hrange sg (by simpa using hm)
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hb
  omega

/-- The fast lenient decoder on in-buffer ranges: the exact decoder on the clamped segments. -/
theorem decodeCodeBlockSegs_clamp (data : ByteArray) (segs : Array JPEG2000.Tier1.Seg) (w h : Nat)
    (band : Band) (style : UInt8) (Mb zbp : Nat)
    (hrange : ∀ sg ∈ segs.toList, sg.start ≤ sg.stop ∧ sg.stop ≤ data.size) :
    JPEG2000.Tier1.decodeCodeBlockSegs data segs w h band style Mb zbp =
      JPEG2000.Tier1.decodeCodeBlockSegsExact data (JPEG2000.Tier1.clampSegs segs (Mb - zbp))
        w h band style Mb zbp := by
  unfold JPEG2000.Tier1.decodeCodeBlockSegs
  rw [badRange_false data segs hrange]
  rfl

/-- The fast strict decoder on in-buffer ranges: the exact one on the clamped segments. -/
theorem decodeCodeBlockSegsStrict_clamp (data : ByteArray) (segs : Array JPEG2000.Tier1.Seg)
    (w h : Nat) (band : Band) (style : UInt8) (Mb zbp : Nat)
    (hrange : ∀ sg ∈ segs.toList, sg.start ≤ sg.stop ∧ sg.stop ≤ data.size) :
    JPEG2000.Tier1.decodeCodeBlockSegsStrict data segs w h band style Mb zbp =
      JPEG2000.Tier1.decodeCodeBlockSegsStrictExact data
        (JPEG2000.Tier1.clampSegs segs (Mb - zbp)) w h band style Mb zbp := by
  unfold JPEG2000.Tier1.decodeCodeBlockSegsStrict
  rw [badRange_false data segs hrange]
  rfl

/-- **C3 for every code-block style** (Plan.md §4; T.800 Annex D, Table A.19): with every
segment range inside the buffer and `K = Mb − zbp ≤ 31` whenever a pass is included, the fast
`decodeCodeBlockSegs` and the spec `Spec.Tier1.decodeCodeBlock` of `specBlockM` both fail with
the same error or both succeed and agree on every coefficient (`Agree`). Both drop the passes
beyond `3K − 2` first (task 5.8). -/
theorem c3_all (data : ByteArray) (segs : Array JPEG2000.Tier1.Seg) (w h : Nat) (band : Band)
    (style : UInt8) (Mb zbp : Nat)
    (hrange : ∀ sg ∈ segs.toList, sg.start ≤ sg.stop ∧ sg.stop ≤ data.size)
    (hK : 0 < (segs.toList.map (·.passes)).sum → Mb - zbp ≤ 31) :
    match JPEG2000.Tier1.decodeCodeBlockSegs data segs w h band style Mb zbp,
      Spec.Tier1.decodeCodeBlock (specBlockM data segs w h band style Mb zbp) with
    | .error e1, .error e2 => e1 = e2
    | .ok o, .ok cs => Agree w h o cs
    | _, _ => False := by
  have C := c3_all_exact data (JPEG2000.Tier1.clampSegs segs (Mb - zbp)) w h band style Mb zbp
    (clampSegs_range data segs _ hrange)
    (fun h0 => hK (Nat.lt_of_lt_of_le h0 (clampSegs_sum_le segs _)))
  rw [← specBlockM_clamp, ← decodeCodeBlockSegs_clamp data segs w h band style Mb zbp hrange] at C
  exact C

/-- **C3 for every code-block style, without the bit-plane bound**: as `c3_all`, but when more
than 31 bit-planes would be decoded the fast decoder may refuse with `unsupported` where the
spec succeeds. -/
theorem c3_all_unsup (data : ByteArray) (segs : Array JPEG2000.Tier1.Seg) (w h : Nat)
    (band : Band) (style : UInt8) (Mb zbp : Nat)
    (hrange : ∀ sg ∈ segs.toList, sg.start ≤ sg.stop ∧ sg.stop ≤ data.size) :
    match JPEG2000.Tier1.decodeCodeBlockSegs data segs w h band style Mb zbp,
      Spec.Tier1.decodeCodeBlock (specBlockM data segs w h band style Mb zbp) with
    | .error e1, .error e2 => e1 = e2
    | .ok o, .ok cs => Agree w h o cs
    | .error e, .ok _ => e = .unsupported JPEG2000.Tier1.tier1Loc "more than 31 coded bit-planes"
    | _, _ => False := by
  have C := c3_all_unsup_exact data (JPEG2000.Tier1.clampSegs segs (Mb - zbp)) w h band style
    Mb zbp (clampSegs_range data segs _ hrange)
  rw [← specBlockM_clamp, ← decodeCodeBlockSegs_clamp data segs w h band style Mb zbp hrange] at C
  exact C

/-- **C3 for every code-block style, strict segmentation symbols**: as `c3_all` for
`decodeCodeBlockSegsStrict` and `Spec.Tier1.decodeCodeBlockStrict` (a segmentation symbol other
than `1010` is the same `malformed` error on both sides). -/
theorem c3_all_strict (data : ByteArray) (segs : Array JPEG2000.Tier1.Seg) (w h : Nat)
    (band : Band) (style : UInt8) (Mb zbp : Nat)
    (hrange : ∀ sg ∈ segs.toList, sg.start ≤ sg.stop ∧ sg.stop ≤ data.size)
    (hK : 0 < (segs.toList.map (·.passes)).sum → Mb - zbp ≤ 31) :
    match JPEG2000.Tier1.decodeCodeBlockSegsStrict data segs w h band style Mb zbp,
      Spec.Tier1.decodeCodeBlockStrict (specBlockM data segs w h band style Mb zbp) with
    | .error e1, .error e2 => e1 = e2
    | .ok o, .ok cs => Agree w h o cs
    | _, _ => False := by
  have C := c3_all_strict_exact data (JPEG2000.Tier1.clampSegs segs (Mb - zbp)) w h band style
    Mb zbp (clampSegs_range data segs _ hrange)
    (fun h0 => hK (Nat.lt_of_lt_of_le h0 (clampSegs_sum_le segs _)))
  rw [← specBlockM_clamp,
    ← decodeCodeBlockSegsStrict_clamp data segs w h band style Mb zbp hrange] at C
  exact C

end JPEG2000.Spec.Tier1EquivM
