import Spec.TileDispatch
import Spec.NativeComposition

/-!
# Public codestream equivalence (Plan.md §4 C9 and §5.1, T.800 Annexes A–H)

Both decoders reject together or return the same component layout and related samples.
Checked reconstruction gives exact reversible samples and the C8 bound after irreversible
lifting, colour transformation and final rounding. The compact-only decoder remains available
through its original numerical relation.
-/

namespace JPEG2000.Spec.C9

open JPEG2000.NativeOutput JPEG2000.Header NativeComposition

/-- Transport a checked read of a post-MCT component into the native placement contract. -/
private theorem plane_dc {siz : Marker.SIZ} {i F : Nat} {rev : Bool} {fmt : Marker.Component}
    {src : Source} {p : Decode.CellPlane} (plane : TileDispatch.PlaneRel F rev src p)
    (scale : ∀ j (hj : j < p.cells.size), rev = true ∨ Assemble.fracBitsOf siz p.cells[j].mct i = F) :
    NativePlacement.SourceRel siz i F rev fmt src (Decode.dcSpec (fmt.signed,fmt.depth.toNat) rev p) := by
  obtain ⟨hw,hh,hs,all⟩ := plane
  apply NativePlacement.source_dcSpec _ _ _ _ _ _ _ hw.symm hh.symm hs
  intro x y hx hy
  have inside : y * src.width + x < src.width * src.height := DWT53.idx_lt hx hy
  have hj : y * src.width + x < p.cells.size := by simpa [hs, ← hw, ← hh] using inside
  obtain ⟨v,val,related⟩ := all _ hj
  simp only [Source.get?, inside, ↓reduceDIte, Option.some.injEq] at val
  exact ⟨val ▸ related, scale _ hj⟩
/-- The common traversal passes the precise packet evidence required by the checked tile. -/
private theorem packet_origin {L : Limits} {h : Header} {data : ByteArray} {t j n : Nat} {d s}
    (origin : NativeTraversal.PacketOrigin L h data t j n d s) :
    TileDispatch.Packets L h data t d s := by
  cases origin with
  | absent => exact .absent
  | present chunks selected index stream packets reference precincts count => exact .present index packets reference

/-- The reconstructed tile's independent G.1 cells supply the native writer's full contract. -/
private theorem placement_input {h : Header} {t red : Nat} {out : JPEG2000.Decode.CenteredTile} {s : Decode.TileOut}
    (rel : TileDispatch.TileRel h t red out s) : TileAgrees h red t out s := by
  obtain ⟨ps,⟨ns,np,rows⟩,cs,tiles⟩ := rel.cells
  refine ⟨rel.layout,ns,cs,?_⟩
  intro i hi
  have ih : i < out.sources.size := ns.symm ▸ hi
  have is : i < s.comps.size := cs.symm ▸ hi
  obtain ⟨plane,⟨reduced, width, height⟩, scale⟩ := rows i ih
  dsimp only
  rw [tiles i is]
  exact ⟨reduced,plane.1.trans width,plane.2.1.trans height,rfl,plane_dc plane scale⟩

/-- C9 for the public decoder on every input, limit policy and reduction. The success
relation covers complete metadata, exact lookup domains and every native sample. -/
theorem c9 (L : Limits) (data : ByteArray) (red : Nat) : NativeEquiv.Agrees L data red := by
  apply of_tiles
  intro h parsed t ht j n a b origin
  exact (TileDispatch.parsed_tile parsed (packet_origin origin)).mono (fun _ _ => placement_input)

/-- **Conditional sample bounds for the legacy Int32 decoder**, for every
`Limits`, input and reduction, with no hypotheses. `ERel C9Rel (decodeCodestreamNarrow L data reduce)
(Spec.Decode.decode L data reduce)` means:

* **failures**: both decoders fail (any errors); or the fast one fails with an `unsupported`
  error (an implementation limit: a code-block with more than 31 coded bit-planes, components
  wider than the `Int32` pipeline) where the spec succeeds. A fast success where the spec fails
  never happens.
* **successes**: same header, same number of components, and per component the same origin,
  size, depth, signedness and sub-sampling; and **if the fast decoder reports no saturated
  code-block (`saturatedBlocks = 0`)**, every sample satisfies `SampleRel`: under C8's
  no-overflow precondition `InRangeT` (vacuous for a reversible component without MCT; otherwise
  the exact inverse-transform values the sample depends on, scaled by `2^F`, fit in `Int32`),
  * a reversible (5/3) sample **equals** the spec sample;
  * an irreversible (9/7) sample is within `cellErr F mct levels + 1` of the exact (rational)
    spec sample (C8's bound plus the two final roundings).

See `docs/c9.md` for when the side conditions can fail. -/
theorem c9_narrow : ∀ (L : Limits) (data : ByteArray) (reduce : Nat),
    Spec.Equiv.ERel Spec.Equiv.C9Rel (JPEG2000.decodeCodestreamNarrow L data reduce)
      (Spec.Decode.decode L data reduce) :=
  Spec.Tier2WF.c9_of_hdr Spec.HeaderWF.headerWF

end JPEG2000.Spec.C9
