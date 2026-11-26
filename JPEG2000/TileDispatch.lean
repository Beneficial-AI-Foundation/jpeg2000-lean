import JPEG2000.ReversibleDispatch
import JPEG2000.IrreversibleDispatch

/-!
# Centred tile reconstruction (Plan.md §§3–5, 7; T.800 Annexes B, D, E, F and G)

The effective tile-component coding determines the wavelet and the precision required
for lifting. Keep the irreversible component's scale until the optional colour transform.
-/

namespace JPEG2000.TileDispatch

open Header NativeOutput Tier2.Packet

/-- One reconstructed component before the optional inverse colour transform. -/
inductive Spatial where
  /-- Integer samples after inverse 5/3. -/
  | rev (s : Source)
  /-- Fixed-point samples after inverse 9/7. -/
  | irrev (s : IrreversibleDispatch.Spatial)

/-- Borrow the packed or exact raster for placement. -/
def Spatial.source : Spatial → Source
  | .rev s => s
  | .irrev s => s.source

/-- Reconstruct the retained resolutions of the selected tile component. -/
def component (L : Limits) (h : Header) (data : ByteArray) (g : Progression.Layout)
    (coding : Coding) (store : Option TileCodeBlocks) (c : Fin g.numComps) (reduce : Nat) :
    Except Error Spatial :=
  match (g.comp c).params.transform with
  | .reversible53 => Spatial.rev <$> ReversibleDispatch.component L data h.siz g coding store c reduce
  | .irreversible97 => Spatial.irrev <$> IrreversibleDispatch.component L data (g.comp c)
      (h.siz.components.getD c default).depth.toNat (Assemble.fracBitsOf h.siz (coding.mctApplies h.siz) c)
      reduce ((store.map (·.comps.getD c #[])).getD #[])

/-- G.2 or G.3 on the first three components. Additional components keep their
own transforms, geometry and scales. -/
def sources (L : Limits) (mct : Bool) (ps : Array Spatial) : Except Error (Array Source) := do
  if !mct then return ps.map Spatial.source
  let rgb ← match ps[0]?, ps[1]?, ps[2]? with
    | some (Spatial.rev y), some (Spatial.rev cb), some (Spatial.rev cr) => ReversibleDispatch.colour L y cb cr
    | some (Spatial.irrev y), some (Spatial.irrev cb), some (Spatial.irrev cr) => do
      let (r,g,b) ← IrreversibleDispatch.ict L y cb cr
      pure (r.source,g.source,b.source)
    | _, _, _ => throw (.malformed (.at .mct) "inconsistent colour transform components")
  return (((ps.map Spatial.source).setIfInBounds 0 rgb.1).setIfInBounds 1 rgb.2.1).setIfInBounds 2 rgb.2.2

/-- Check the combined tile work before allocating the first spatial component. -/
def tile (L : Limits) (h : Header) (data : ByteArray) (g : Progression.Layout) (coding : Coding)
    (store : Option TileCodeBlocks) (reduce : Nat) : Except Error (Array Source) := do
  L.check Assemble.loc .workSamples (g.comps.foldl (fun n tc =>
    n + Tier2.Geometry.rectArea (Assemble.reduceRect tc.rect reduce)) 0)
  let ps ← g.comps.mapFinIdxM fun i _ hi => component L h data g coding store ⟨i, hi⟩ reduce
  sources L (coding.mctApplies h.siz) ps

end JPEG2000.TileDispatch
