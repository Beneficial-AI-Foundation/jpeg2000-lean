import Spec.Equiv
import Spec.NativeOutput

/-!
# Native output samples and C9

Plan.md §§4, 5.1, 7, T.800 Annex G. The centred reconstruction of a reversible
cell is an exact integer. On irreversible cells the upstream error is measured in
physical sample units. Native G.1 and tile placement carry these claims to the
sample returned by the component accessor at the translated output coordinate.
-/

namespace JPEG2000.Spec.NativeSample

open JPEG2000.NativeOutput JPEG2000.Spec.Decode
open JPEG2000.Spec.Equiv (cellErr pw)
open JPEG2000.Header (Rect)

/-- Required accuracy of a post-MCT source cell at its actual binary scale. -/
def CenteredAgrees (F : Nat) (rev : Bool) (z : Int) (c : SpecCell) : Prop :=
  if rev then z = c.ival
  else ((z : Rat) / pw F - c.rval).abs ≤ cellErr F c.mct c.levels

/-- Full native sample claim at scale `F`, including G.1 rounding on irreversible cells. -/
def Agrees (F : Nat) (v : Int) (s : SpecSample) : Prop :=
  if s.reversible then v = s.value
  else ((v : Rat) - s.value).abs ≤ cellErr F s.mct s.levels + 1

/-- At a written location, exact or C8-bounded centred reconstruction gives the native
sample claim. The input and stored integers may have any magnitude. -/
theorem placed_sample {d q : OutputComponent} {r : Rect} {src : Source} (F : Nat)
    (rev : Bool) (placed : NativeOutput.Placed d q r (if rev then 0 else F) src)
    (x y : Nat) (hx : x < src.width) (hy : y < src.height) (c : SpecCell)
    (hc : CenteredAgrees F rev (src.read ⟨y * src.width + x, DWT53.idx_lt hx hy⟩) c) :
    ∃ v, q.get? ((r.y0 - d.rect.y0 + y) * d.rect.width + (r.x0 - d.rect.x0 + x)) = some v ∧
      Agrees F v (c.toSample d.format.signed d.format.depth.toNat rev) := by
  have hit := placed.2.2.1 x y hx hy
  simp only [Source.get?, DWT53.idx_lt hx hy, ↓reduceDIte, Option.map_some] at hit
  refine ⟨_, hit, ?_⟩
  cases rev with
  | false => exact Equiv.irrev_sample _ _ F d.precision.1 _ _ _ hc
  | true =>
    simp only [CenteredAgrees, ↓reduceIte] at hc
    simp [Agrees, SpecCell.toSample, MCT.reconIrrev, MCT.roundFix, hc]

/-- The indexed public tile writer delivers the native sample claim for every component
and tile-local coordinate whenever the corresponding post-MCT source cell meets its
reconstruction bound. The effective transform and scale are the writer's actual ones. -/
theorem writeTile_sample {L : Limits} {s : Marker.SIZ} {reduce : Nat} {g : Progression.Layout}
    {coding : Header.Coding} {ds out : Array OutputComponent} {src : Array Source}
    {irrevBits : Nat → Nat} (ok : writeTile L s reduce g coding ds src irrevBits = .ok out)
    (i : Nat) (hi : i < ds.size) :
    ∃ q t, out[i]? = some q ∧ src[i]? = some t ∧
      ∀ x y (hx : x < t.width) (hy : y < t.height) (c : SpecCell),
        let r := Assemble.reduceRect (g.comp i).rect reduce
        let rev := (g.comp i).params.transform == .reversible53
        CenteredAgrees (irrevBits i) rev (t.read ⟨y * t.width + x, DWT53.idx_lt hx hy⟩) c →
          ∃ v, q.get? ((r.y0 - ds[i].rect.y0 + y) * ds[i].rect.width +
              (r.x0 - ds[i].rect.x0 + x)) = some v ∧
            Agrees (irrevBits i) v (c.toSample ds[i].format.signed ds[i].format.depth.toNat rev) := by
  obtain ⟨q, t, hq, ht, placed⟩ := (NativeOutput.writeTile_spec ok).2.2.2.2 i hi
  exact ⟨q, t, hq, ht, fun x y hx hy c hc =>
    placed_sample (irrevBits i) _ placed x y hx hy c hc⟩

end JPEG2000.Spec.NativeSample
