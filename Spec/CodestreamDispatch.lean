import Spec.C9
import Spec.NativeOutput

/-!
# Public codestream dispatch and native tile observations
(Plan.md §§4, 5.1, 5.4, 7; T.800 B.2, B-12, B-14, G.1)

The explicit legacy compact decoder retains its numerical C9 theorem. A successful public
decode starts with checked zero grids and writes the actual centred reconstructions in tile
order. The pointwise specification of each write includes translated and untouched cells.
-/

namespace JPEG2000.Spec.CodestreamDispatch

open JPEG2000.Decode JPEG2000.NativeOutput Header TilePart

private theorem bind_ok {α β : Type} {x : Except Error α} {f : α → Except Error β} {y : β} :
    (x >>= f) = .ok y ↔ ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x <;> simp [bind, Except.bind]

/-- The public accessor returns the compact kernel's exact signed integer at every index. -/
theorem compact_read (img : DecodedImage) (c i : Nat) :
    (img.toCodestream.comps[c]?).bind (·.get? i) =
      (img.comps[c]?).bind (fun d => (d.plane.get? i).map Int32.toInt) := by
  simp only [DecodedImage.toCodestream, Array.getElem?_map]
  cases img.comps[c]? <;> rfl

/-- Dispatch on any parsed header agrees with the checked native pipeline,
including all allocation and reconstruction errors and the outer reduction check. -/
theorem native_dispatch {L : Limits} {data : ByteArray} {reduce : Nat} {h : Header}
    (hp : Header.parse L data = .ok h) :
    decodeCodestream L data reduce = nativeFromHeader L h data reduce := by
  unfold decodeCodestream
  cases hr : L.check JPEG2000.Decode.loc .decompLevels reduce with
  | ok u => simp [hp, bind, Except.bind]
  | error e =>
    unfold nativeFromHeader JPEG2000.NativeOutput.allocOutput
    change L.check (.at .decode) .decompLevels reduce = .error e at hr
    simp [hr, bind, Except.bind]

/-- Observe one reconstructed source at an image-relative coordinate. Inside its absolute
tile rectangle, apply G.1 at the post-MCT scale; elsewhere keep the preceding observation. -/
def observeTile (s : Marker.SIZ) (reduce i : Nat) (grid : Rect) (c : Marker.Component)
    (x y : Nat) (old : Option Int) (tile : CenteredTile) (src : Source) : Option Int :=
  let r := Assemble.reduceRect (tile.layout.comp i).rect reduce
  let ox := r.x0 - grid.x0
  let oy := r.y0 - grid.y0
  if ox ≤ x ∧ x < ox + src.width ∧ oy ≤ y ∧ y < oy + src.height then
    let F := if (tile.layout.comp i).params.transform == .reversible53 then 0
             else Assemble.fracBitsOf s (tile.coding.mctApplies s) i
    (src.get? ((y - oy) * src.width + (x - ox))).map (Spec.MCT.reconIrrev c.signed c.depth.toNat F)
  else old

-- The observer inspects a single component and coordinate. Its work is needed only on
-- successful image decodes, which have already checked all components and placements.
private def Sim {α β : Type} (R : α → β → Prop) : Except Error α → Except Error β → Prop
  | .error _, _ => True
  | .ok a, .ok b => R a b
  | .ok _, .error _ => False

private theorem sim_bind {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop}
    {a : Except Error α} {b : Except Error β} {f : α → Except Error γ} {g : β → Except Error δ}
    (ab : Sim R a b) (fg : ∀ x y, R x y → Sim S (f x) (g y)) : Sim S (a >>= f) (b >>= g) := by
  cases a <;> cases b <;> first | trivial | contradiction | exact fg _ _ ab

private theorem sim_same {α γ δ : Type} {S : γ → δ → Prop} (a : Except Error α)
    {f : α → Except Error γ} {g : α → Except Error δ} (same : ∀ x, Sim S (f x) (g x)) :
    Sim S (a >>= f) (a >>= g) := by
  cases a <;> first | trivial | exact same _

private theorem sim_loop {α β : Type} (R : α → β → Prop) (f : Nat → α → Except Error (ForInStep α))
    (g : Nat → β → Except Error (ForInStep β))
    (step : ∀ t a b, R a b → Sim (Equiv.StepRel R) (f t a) (g t b)) :
    ∀ (ts : List Nat) a b, R a b → Sim R (forIn ts a f) (forIn ts b g)
  | [], _, _, rel => by simpa only [List.forIn_nil, pure, Except.pure, Sim] using rel
  | t :: rest, a, b, rel => by
    simp only [List.forIn_cons]
    apply sim_bind (step t a b rel)
    intro x y matched
    cases x <;> cases y <;> simp only [Equiv.StepRel] at matched
    · exact matched
    · exact sim_loop R f g step rest _ _ matched

private theorem tiles_sim {A B T α : Type} {L : Limits} {h : Header} {data : ByteArray}
    {a : A} {b : B} {tile : Nat → Option Tier2.Packet.TileCodeBlocks → Except Error T}
    {sat : T → Nat} {write : A → T → Except Error A} {observe : B → T → B} {finish : A → Nat → α}
    (R : A → B → Prop) (S : α → B → Prop) (init : R a b)
    (step : ∀ ds v t q, R ds v → write ds t = .ok q → R q (observe v t))
    (done : ∀ ds v n, R ds v → S (finish ds n) v) :
    Sim S (withTiles L h data a tile sat write finish)
      (withTiles L h data b tile sat (fun v t => .ok (observe v t)) (fun v _ => v)) := by
  let inv := fun (a : A × Nat × Nat × Nat) (b : B × Nat × Nat × Nat) => a.2 = b.2 ∧ R a.1 b.1
  unfold withTiles
  split <;> apply sim_same <;> intro idx
  all_goals
    refine sim_bind (R := inv) ?_ ?_
    · simp only [Std.Legacy.Range.forIn_eq_forIn_range']
      apply sim_loop
      · rintro t ⟨ds, passes, n, j⟩ ⟨v, stat⟩ ⟨rfl, rel⟩
        dsimp only
        have tail (cb : Option Tier2.Packet.TileCodeBlocks) (nextPass nextJ : Nat) :
            Sim (Equiv.StepRel inv) (do
              let obj ← tile t cb
              let q ← write ds obj
              pure (.yield (q, nextPass, n + sat obj, nextJ))) (do
              let obj ← tile t cb
              pure (.yield (observe v obj, nextPass, n + sat obj, nextJ))) := by
          apply sim_same
          intro obj
          cases hw : write ds obj with
          | error => trivial
          | ok q => exact ⟨rfl, step ds v obj q rel hw⟩
        cases it : h.tiles[j]? with
        | none =>
          simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, pure_bind]
          exact tail none _ _
        | some tp =>
          by_cases hit : tp.index = t <;>
            simp only [hit, ↓reduceIte, Option.isSome_some, Option.isSome_none,
              Bool.false_eq_true, pure_bind]
          · apply sim_same; intro hs
            apply sim_same; intro block
            exact tail (some block) _ _
          · exact tail none _ _
      · exact ⟨rfl, init⟩
    · rintro ⟨ds, passes, n, j⟩ ⟨v, stat⟩ ⟨rfl, rel⟩
      exact done ds v n rel

/-- A successful native decode retains the parsed header, reduction and every SIZ descriptor
and reduced rectangle in order. The combined area and declared bytes satisfy the limits. -/
theorem native_geometry {L : Limits} {data : ByteArray} {reduce : Nat} {h : Header}
    {img : CodestreamImage} (hp : Header.parse L data = .ok h)
    (ok : decodeCodestream L data reduce = .ok img) :
    img.header = h ∧ img.reduce = reduce ∧
      (∃ ds : Array OutputComponent, img.comps = ds.map .native ∧
        ds.map (fun d => (d.rect, d.format)) = layout h.siz reduce) ∧
      cells (layout h.siz reduce) ≤ L.maxWorkSamples ∧
      decodedBytes (layout h.siz reduce) ≤ L.maxDecodedBytes := by
  rw [native_dispatch hp, nativeFromHeader, bind_ok] at ok
  obtain ⟨ds, ha, decoded⟩ := ok
  obtain ⟨work, bytes, _, _⟩ := Spec.NativeOutput.allocOutput_spec ha
  let shape := fun (ps : Array OutputComponent) => ps.map fun d => (d.rect, d.format)
  let R := fun ps (_ : Unit) => shape ps = layout h.siz reduce
  let S := fun (out : CodestreamImage) (_ : Unit) => out.header = h ∧ out.reduce = reduce ∧
    ∃ ps, out.comps = ps.map .native ∧ shape ps = layout h.siz reduce
  have sim := tiles_sim (L := L) (a := ds) (b := ()) (h := h) (data := data)
    (tile := centeredTile L h data reduce) (sat := CenteredTile.saturated)
    (write := fun ps t => writeTile L h.siz reduce t.layout t.coding ps t.sources)
    (finish := fun ps n => ⟨h, reduce, ps.map .native, n⟩) (observe := fun _ _ => ())
    R S (Spec.NativeOutput.allocOutput_bounds ha).1 (by
      intro ps _ t out prev hw
      obtain ⟨sz, _, _, _, place⟩ := Spec.NativeOutput.writeTile_spec hw
      change shape out = _
      rw [← prev]
      apply Array.ext
      · simpa [shape] using sz.symm
      · intro i _ hi
        have h := Array.size_map .. ▸ hi
        obtain ⟨q, _, hq, _, hr, hf, _, _⟩ := place i h
        simp only [Array.getElem?_eq_getElem (sz ▸ h), Option.some.injEq] at hq
        simp [shape, hq, hr, hf]) (fun ps _ n prev => ⟨rfl, rfl, ps, rfl, prev⟩)
  rw [decoded] at sim
  cases run : withTiles L h data () (centeredTile L h data reduce) CenteredTile.saturated
      (fun _ _ => .ok ()) (fun v _ => v) <;> rw [run] at sim
  · contradiction
  · exact ⟨sim.1, sim.2.1, sim.2.2, work, bytes⟩

/-- Replay the same Tier-2 packet traversal and centred reconstruction as production, observing
just one image-relative coordinate with the mathematical G.1 rule. The reference retains
one integer observation across tiles, initially zero. -/
def replaySample (L : Limits) (h : Header) (data : ByteArray) (reduce i x y : Nat)
    (r : Rect) (c : Marker.Component) : Except Error (Option Int) :=
  withTiles L h data (some (0 : Int)) (centeredTile L h data reduce) (·.saturated)
    (fun old t => .ok (t.sources[i]?.bind fun src =>
      observeTile h.siz reduce i r c x y old t src)) (fun v _ => v)

/-- The ordinary native decoder's exact public sample equals an independent observation
of G.1 at that coordinate through the same packet and post-MCT tile traversal. The
comparison uses no externally supplied tiles, packet data or numerical range hypotheses. -/
theorem native_read {L : Limits} {data : ByteArray} {reduce : Nat} {h : Header}
    {img : CodestreamImage} (hp : Header.parse L data = .ok h)
    (ok : decodeCodestream L data reduce = .ok img)
    (i : Nat) (hi : i < (layout h.siz reduce).size) (x y : Nat)
    (hx : x < (layout h.siz reduce)[i].1.width) (hy : y < (layout h.siz reduce)[i].1.height) :
    let (r, c) := (layout h.siz reduce)[i]
    replaySample L h data reduce i x y r c = .ok ((img.comps[i]?).bind (·.get? (y * r.width + x))) := by
  rw [native_dispatch hp, nativeFromHeader, bind_ok] at ok
  obtain ⟨ds, ha, decoded⟩ := ok
  let r := (layout h.siz reduce)[i].1
  let c := (layout h.siz reduce)[i].2
  let idx := y * r.width + x
  let R := fun (ps : Array OutputComponent) (v : Option Int) =>
    ∃ d, ps[i]? = some d ∧ d.rect = r ∧ d.format = c ∧ d.get? idx = v
  let S := fun (img : CodestreamImage) (v : Option Int) => (img.comps[i]?).bind (·.get? idx) = v
  have init : R ds (some 0) := by
    obtain ⟨_, _, _, atIdx⟩ := Spec.NativeOutput.allocOutput_spec ha
    obtain ⟨d, hd, hr, hf, zero⟩ := atIdx i hi
    refine ⟨d, hd, hr, hf, zero _ ?_⟩
    rw [hr]
    change x < r.width at hx
    change y < r.height at hy
    have bound := Nat.mul_le_mul_right r.width hy
    rw [Nat.succ_mul] at bound
    change y * r.width + x < r.width * r.height
    rw [Nat.mul_comm r.width r.height]
    omega
  have sim := tiles_sim (L := L) (a := ds) (h := h) (data := data) (tile := centeredTile L h data reduce)
    (write := fun ps t => writeTile L h.siz reduce t.layout t.coding ps t.sources)
    (sat := CenteredTile.saturated) (finish := fun ps n => ⟨h, reduce, ps.map .native, n⟩)
    (observe := fun old t => t.sources[i]?.bind fun src => observeTile h.siz reduce i r c x y old t src)
    R S init (by
      rintro ps v tile out ⟨d, hd, hr, hf, read⟩ hw
      obtain ⟨hi, he⟩ := Array.getElem?_eq_some_iff.mp hd
      obtain ⟨_, _, _, _, place⟩ := Spec.NativeOutput.writeTile_spec hw
      obtain ⟨q, src, hq, hs, placed⟩ := place i hi
      rw [he] at placed
      obtain ⟨qr, qf, inside, outside⟩ := placed
      refine ⟨q, hq, qr.trans hr, qf.trans hf, ?_⟩
      rw [hr, hf] at inside
      rw [hr] at outside
      simp only [hs, Option.bind_some, observeTile]
      split
      · rename_i hit
        let tr := Assemble.reduceRect (tile.layout.comp i).rect reduce
        let ox := tr.x0 - r.x0
        let oy := tr.y0 - r.y0
        change ox ≤ x ∧ x < ox + src.width ∧ oy ≤ y ∧ y < oy + src.height at hit
        have cell := inside (x - ox) (y - oy) (by omega) (by omega)
        change q.get? ((oy + (y - oy)) * r.width + (ox + (x - ox))) = _ at cell
        rwa [show oy + (y - oy) = y by omega, show ox + (x - ox) = x by omega] at cell
      · exact (outside x y hx hy (by assumption)).trans read) (by
      rintro ps v n ⟨d, hd, _, _, read⟩
      simpa [S, hd, CodestreamComponent.get?] using read)
  rw [decoded] at sim
  change Sim S (.ok img) (replaySample L h data reduce i x y r c) at sim
  change replaySample L h data reduce i x y r c = .ok _
  cases replay : replaySample L h data reduce i x y r c <;> rw [replay] at sim
  · contradiction
  · exact congrArg Except.ok sim.symm

end JPEG2000.Spec.CodestreamDispatch
