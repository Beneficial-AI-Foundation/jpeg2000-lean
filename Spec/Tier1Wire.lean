import Spec.Tier2Wire
import Spec.Tier1Equiv.Clamp

/-!
# The Tier-1 equivalence wired into C9

Plan.md §4 (C3: fast Tier-1 = the Annex D spec, every code-block style; C9), §5.1 (one
equivalence per stage, composed into C9); T.800 Annex D (D.3–D.7, codeword segments D.4.1),
B.10.7 (segments of a code-block across packets). Task 7.1h.

`Spec.Equiv.Tier1Equiv` relates, for every code-block, the fast `Assemble.decodeBlock` (the
buffer and ranges of `Assemble.tier1Input` fed to `Tier1.decodeCodeBlockSegs`) and the spec
`Spec.Decode.decodeBlock` (the same buffer and ranges, read as byte lists by
`Spec.Decode.specCodeBlock`, decoded by `Spec.Tier1.decodeCodeBlock`). Both sides read the
same `tier1Input` buffer, so no byte-level argument is needed here (that the buffer holds the
segments of the spec Tier-2 result is `Spec.Equiv.decodeBlock_eq_st`, used by C9 itself):

* a range outside the buffer: the spec fails (`specCodeBlock`) and so does the fast decoder
  (it checks every range before anything else, `badRange`, `fast_error_of_bad` — also the
  ranges of segments it would drop as lying below bit-plane 0, task 5.8);
* otherwise `specCodeBlock` is `Spec.Tier1EquivM.specBlockM` of the buffer and ranges
  (`specCodeBlock_ok`), and C3 for every style (`Spec.Tier1EquivM.c3_all_unsup`) gives
  `Agree`, both failing, or the fast one refusing with `unsupported` (K > 31); `Agree` implies
  `BlockAgree` (`agree_blockAgree`).

`tier1Equiv` discharges the hypothesis; `c9_of_header` is C9 with only `Tier2WF` and
`HeaderWF` left open.
-/

namespace JPEG2000.Spec.Tier1Wire

open JPEG2000 JPEG2000.Header JPEG2000.Tier2.Packet JPEG2000.Tier2.Geometry
open JPEG2000.Spec.Equiv
open JPEG2000.Spec.Tier1 (Coeff)

/-- The fast argument check fails when some segment range lies outside the buffer. -/
theorem validateSegs_error (data : ByteArray) (segs : Array Tier1.Seg) (w h : Nat)
    (m : Tier1.Style) (K : Nat)
    (hbad : (segs.any fun sg => decide (sg.start > sg.stop) || decide (sg.stop > data.size)) = true) :
    ∃ e, Tier1.validateSegs data segs w h m K = .error e := by
  unfold Tier1.validateSegs
  simp only [hbad]
  split
  · exact ⟨_, rfl⟩
  · split
    · exact ⟨_, rfl⟩
    · split
      · exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩

/-- **The fast Tier-1 decoder fails** when some segment range lies outside its buffer. -/
theorem fast_error_of_bad (data : ByteArray) (segs : Array Tier1.Seg) (w h : Nat) (band : Band)
    (style : UInt8) (Mb zbp : Nat)
    (hbad : (segs.any fun sg => decide (sg.start > sg.stop) || decide (sg.stop > data.size)) = true) :
    ∃ e, Tier1.decodeCodeBlockSegs data segs w h band style Mb zbp = .error e := by
  refine ⟨.malformed JPEG2000.Tier1.tier1Loc "code-block data range outside the buffer", ?_⟩
  unfold Tier1.decodeCodeBlockSegs Tier1.badRange
  simp only [hbad, ↓reduceIte]

/-- With every range in its buffer, the spec code-block of a fast code-block is `specBlockM` of
the `tier1Input` buffer and ranges. -/
theorem specCodeBlock_ok (data : ByteArray) (p : CompParams) (r : Nat) (b : Band) (cb : CodeBlock)
    (buf : ByteArray) (segs : Array Tier1.Seg) (hx : Assemble.tier1Input data cb = (buf, segs))
    (hgood : (segs.any fun sg => decide (sg.start > sg.stop) || decide (sg.stop > buf.size)) = false) :
    Spec.Decode.specCodeBlock data p r b cb =
      .ok (Spec.Tier1EquivM.specBlockM buf segs cb.geom.rect.width cb.geom.rect.height b p.cbStyle
        (bandMb p r b + p.roiShift) (if cb.included then cb.zeroBitPlanes else 0)) := by
  unfold Spec.Decode.specCodeBlock Spec.Decode.Tier2Spec.segments
  rw [hx]
  simp only [hgood, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- C3's `Agree` (with `sig`) implies the `BlockAgree` C9 uses. -/
theorem agree_blockAgree (cb : CodeBlock) (o : Tier1.CodeBlockOut) (cs : Array Coeff)
    (h : Spec.Tier1EquivM.Agree cb.geom.rect.width cb.geom.rect.height o cs) : BlockAgree cb o cs := by
  obtain ⟨hs, hw, hh, hxy⟩ := h
  exact ⟨hw, hh, hs, fun x y hx hy => ⟨(hxy x y hx hy).1, (hxy x y hx hy).2.2⟩⟩

/-- **Stage hypothesis `Tier1Equiv` discharged** (C3 for every code-block style, through the
segment gathering of `Assemble.tier1Input`). -/
theorem tier1Equiv : Tier1Equiv := by
  intro data p r b cb
  unfold Assemble.decodeBlock Spec.Decode.decodeBlock
  rcases hx : Assemble.tier1Input data cb with ⟨buf, segs⟩
  dsimp only
  cases hg : (segs.any fun sg => decide (sg.start > sg.stop) || decide (sg.stop > buf.size)) with
  | true =>
    obtain ⟨e, he⟩ := fast_error_of_bad buf segs cb.geom.rect.width cb.geom.rect.height b p.cbStyle
      (bandMb p r b + p.roiShift) (if cb.included then cb.zeroBitPlanes else 0) hg
    have hs : ∃ e', Spec.Decode.specCodeBlock data p r b cb = .error e' := by
      unfold Spec.Decode.specCodeBlock Spec.Decode.Tier2Spec.segments
      rw [hx]
      simp only [hg, ↓reduceIte]
      exact ⟨_, rfl⟩
    obtain ⟨e', he'⟩ := hs
    rw [he, he']
    trivial
  | false =>
    rw [specCodeBlock_ok data p r b cb buf segs hx hg]
    have hrange : ∀ sg ∈ segs.toList, sg.start ≤ sg.stop ∧ sg.stop ≤ buf.size := by
      intro sg hsg
      rw [Bool.eq_false_iff] at hg
      refine Classical.byContradiction fun hc => hg ?_
      rw [Array.any_eq_true']
      refine ⟨sg, by simpa using hsg, ?_⟩
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      omega
    have C := Spec.Tier1EquivM.c3_all_unsup buf segs cb.geom.rect.width cb.geom.rect.height b
      p.cbStyle (bandMb p r b + p.roiShift) (if cb.included then cb.zeroBitPlanes else 0)
      hrange
    show ERel (BlockAgree cb) _ (Spec.Tier1.decodeCodeBlock _)
    revert C
    generalize Tier1.decodeCodeBlockSegs _ _ _ _ _ _ _ _ = r1
    generalize Spec.Tier1.decodeCodeBlock _ = r2
    intro C
    cases r1 <;> cases r2
    · trivial
    · simp only at C
      subst C
      trivial
    · exact C.elim
    · exact agree_blockAgree cb _ _ C

/-- **C9 with Tier-1 discharged**: only `Tier2WF` (task 7.1g) and `HeaderWF` (task 7.1e) remain. -/
theorem c9_of_header (hT2w : Tier2WF) (hHd : HeaderWF) :
    ∀ (L : Limits) (data : ByteArray) (reduce : Nat),
      ERel C9Rel (decodeCodestream L data reduce) (Spec.Decode.decode L data reduce) :=
  Spec.Tier2Wire.c9_of_open hT2w tier1Equiv hHd

end JPEG2000.Spec.Tier1Wire
