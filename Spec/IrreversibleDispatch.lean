import JPEG2000.IrreversibleDispatch
import Spec.HeaderWF
import Spec.Tier1Wire
import Spec.WideAssembly
import Spec.WideDWT97
import Spec.WideICT
import Spec.NativeSample

/-!
# Irreversible dispatch and C8 (Plan.md §§4, 5.1, 5.4, 7; T.800 B-15, E, F.3, G.3)

Compare each selected spatial source with the independent rational inverse of the parsed
packet entries. The ICT uses those unclamped estimates, their actual fractional bits and
the individual reduced level counts. All error bounds are in physical sample units.
-/

namespace JPEG2000.Spec.IrreversibleDispatch

open JPEG2000.IrreversibleDispatch
open JPEG2000.Bytes JPEG2000.Header JPEG2000.Tier2.Geometry JPEG2000.Tier2.Packet
open Equiv (ERel ReadBand InBand BandsClose pw cellErr errOf posU posV)
open JPEG2000.Spec.Decode (Entry dec97)
open JPEG2000.DWT53 (specRect halfRect halfN)
open JPEG2000.DWT97 (En)
open JPEG2000.Tier2.Geometry (rectArea)

/-- The compact coefficient loop stops at saturation. Every success supplies all B-15
band errors at the requested scale against the entries of the independent packet image. -/
theorem compactBands_ok {L : Limits} {data : ByteArray} {tc : TileCompGeom} {depth F red : Nat}
    {ps : Array (Array PrecinctOut)} {p : Plane} (reduction : red ≤ tc.params.levels)
    (params : Equiv.ParamsWF tc) (wf : Equiv.PrecsWF tc ps) (ranges : Equiv.BlocksIn data ps)
    (ok : compactBands L data tc depth F red ps = .ok p) :
    ∃ es, WideAssembly.entries L tc depth F red (Equiv.imagePrecs data ps) = .ok (es, 0) ∧
      Equiv.LoopRel F (tc.params.transform == .reversible53) p (Assemble.reduceRect tc.rect red)
        (tc.params.levels - red) 0 es := by
  have checked : L.check Assemble.loc .decompLevels (max red tc.params.levels) = .ok () := by
    cases h : L.check Assemble.loc .decompLevels (max red tc.params.levels) with
    | ok u => cases u; rfl
    | error e => simp [compactBands, h, bind, Except.bind] at ok
  let rect := Assemble.reduceRect tc.rect red
  let nl := tc.params.levels - red
  let R := fun (p : Plane) (s : List Entry × Nat) =>
    Equiv.LoopRel F (tc.params.transform == .reversible53) p rect nl 0 s.1 ∧ s.2 = 0
  suffices sim : ERel R (compactBands L data tc depth F red ps)
      (WideAssembly.entries L tc depth F red (Equiv.imagePrecs data ps)) by
    rw [ok] at sim
    cases h : WideAssembly.entries L tc depth F red (Equiv.imagePrecs data ps) with
    | error e => rw [h] at sim; exact False.elim sim
    | ok s =>
      rw [h] at sim
      obtain ⟨es, sat⟩ := s
      obtain ⟨rel, rfl⟩ := sim
      exact ⟨es, rfl, rel⟩
  unfold compactBands WideAssembly.entries
  dsimp only
  simp only [checked, Equiv.ok_bind, Nat.not_lt_of_ge reduction, ↓reduceIte, Plane.zeroChecked, Decode.initSpec, bind_assoc]
  apply Equiv.ERel.bind_same
  intro _
  simp only [pure_bind, JPEG2000.WideAssembly.visitBlocks, Equiv.imagePrecs_getD, List.forIn_map,
    Array.forIn_toList]
  simp only [Equiv.imagePrecs, List.length_map, Array.length_toList, Tier2Equiv.imageBand,
    List.forIn_map, Array.forIn_toList]
  -- The spec accumulates a (zero) saturation counter; the checked loop exits instead.
  refine Equiv.ERel.bind (R := R) ?_ (by intro a b h; exact h)
  apply QuantBlock.ERel.forIn_range_mem _ _ _ _ _ _ (show R _ ([], 0) from ⟨QuantBlock.init_rel .., rfl⟩)
  intro r hr a s inv
  have hr' : r ≤ nl := by dsimp [nl]; omega
  have hrs : r < ps.size := by omega
  refine Equiv.ERel.bind (R := R) ?_ (by intro a s h; exact h)
  apply QuantBlock.ERel.forIn_arr_mem _ _ _ _ _ _ inv
  intro prec hprec a s inv
  refine Equiv.ERel.bind (R := R) ?_ (by intro a s h; exact h)
  apply QuantBlock.ERel.forIn_arr_mem _ _ _ _ _ _ inv
  intro bo hbo a s inv
  obtain ⟨hb, bound⟩ := wf r hrs prec hprec bo hbo
  refine Equiv.ERel.bind (R := R) ?_ (by intro a s h; exact h)
  apply QuantBlock.ERel.forIn_arr_mem _ _ _ _ _ _ inv
  intro cb hcb a s inv
  simp only [show (Tier2Equiv.blockOf data cb).passes = cb.numPasses from rfl,
    show (Tier2Equiv.blockOf data cb).geom = cb.geom from rfl]
  by_cases active : (cb.numPasses != 0 && !rectEmpty cb.geom.rect) = true
  · simp only [active, ↓reduceIte]
    have inside := ranges r prec hprec bo hbo cb hcb
    change cb.segments.all (fun seg => seg.ranges.all (fun rg => decide (rg.offset + rg.length ≤ data.size))) = true at inside
    simp only [inside, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind_assoc]
    have coeff := Tier1Wire.tier1Equiv data tc.params r bo.band cb
    rw [Equiv.decodeBlock_eq_st _ _ _ _ _ inside] at coeff
    apply Equiv.ERel.bind coeff
    intro o cs hag
    have br := WideQuant.reduced_band tc.rect tc.params.levels red r bo.band reduction hr' hb
    obtain ⟨bx, by0, ex, ey⟩ := br ▸ bound cb hcb
    have ne : cb.geom.rect.x0 < cb.geom.rect.x1 ∧ cb.geom.rect.y0 < cb.geom.rect.y1 := by
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at active
      simpa [rectEmpty] using active.2
    have mu : (Spec.Quant.bandQuant tc.params depth r bo.band).mantissa < 2048 := by
      simp only [Spec.Quant.bandQuant, Array.getD_eq_getD_getElem?]
      cases h : tc.params.steps[Spec.Quant.bandIndex r bo.band]? with
      | none => decide
      | some st => exact params st (Array.mem_of_getElem? h)
    obtain ⟨old, sat⟩ := inv
    have rel := QuantBlock.step_rel F _ a rect nl 0 s.1 old r bo.band cb o cs
      (Spec.Quant.bandQuant tc.params depth r bo.band) rfl mu hr' hb hag bx by0 ex ey ne.1 ne.2
    rw [QuantBlock.dequantBlock_ok _ _ _ _ _ _ _ _ _ old.1 old.2.1 hr' hag.1 hag.2.1 bx by0 ex ey]
    simp only [Equiv.ok_bind, Decode.collect, pure_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    generalize JPEG2000.Quant.blockRows _ o _ _ o.plane.height 0 a true = result at rel ⊢
    cases hv : result.2
    · trivial
    · exact ⟨by simpa [hv] using rel, sat⟩
  · simp only [active]
    exact inv

private theorem ll_at (a : Array Int) (w : Nat) (r : Rect) (n k : Nat) (u v : Int) :
    (WideReversible.mallat a w (halfN r k) n).ll.get u v =
      a.getD ((v.toNat - (halfN r (k + n)).y0) * w + (u.toNat - (halfN r (k + n)).x0)) 0 := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    change (WideReversible.mallat a w (halfN r (k+1)) n).ll.get u v = _
    rw [ih, Nat.add_right_comm k 1 n]
    rfl

private theorem detail_at (a : Array Int) (w : Nat) (r : Rect) (n k i : Nat) (hi : i < n) :
    (WideReversible.mallat a w (halfN r k) n).details[i]? =
      some (WideReversible.details a w (halfN r (k + i))) := by
  induction n generalizing k i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => rfl
    | succ i =>
      change (WideReversible.mallat a w (halfN r (k+1)) n).details[i]? = _
      rw [ih _ _ (by omega), Nat.add_right_comm k 1 i]
      rfl

private theorem wide_bands {r : Rect} {nl F : Nat} {p : JPEG2000.WideQuant.Plane}
    {es : List Entry} (h : WideAssembly.LoopRel r nl false F p es) :
    BandsClose (1/2) F r nl (WideReversible.mallat p.samples.toArray r.width r nl) (dec97 es nl) := by
  intro lvl b u v read inside
  obtain ⟨z, hit, bound⟩ := WideAssembly.bandGrid97_close h lvl b u v read inside
  rw [QuantBlock.band97_dec97 _ _ _ _ read, Rat.mul_comm]
  suffices idx : (Equiv.band53 (WideReversible.mallat p.samples.toArray r.width r nl) lvl b).get u v =
      p.samples.toArray.getD ((QuantBlock.my r lvl b v).toNat * r.width + (QuantBlock.mx r lvl b u).toNat) 0 by
    rwa [idx, Array.getD_eq_getD_getElem?, hit]
  rcases read with ⟨rfl, rfl⟩ | ⟨nb, hl, hn⟩
  · change (WideReversible.mallat _ _ (halfN r 0) lvl).ll.get u v = _
    rw [ll_at]
    simp only [Nat.zero_add, QuantBlock.mx, QuantBlock.my, Band.xob, Band.yob]
    congr 3 <;> omega
  · obtain ⟨k, rfl⟩ : ∃ k, lvl = k+1 := ⟨lvl-1, by omega⟩
    have det := detail_at p.samples.toArray r.width r nl 0 k (by omega)
    simp only [halfN, Nat.zero_add] at det
    obtain ⟨x0,y0,x1,y1⟩ := DWTPlane.halfN_coords r k
    obtain ⟨lx0,ly0,lx1,ly1⟩ := DWTPlane.halfN_coords r (k+1)
    cases b with
    | LL => exact absurd rfl nb
    | _ =>
      simp only [Equiv.band53, Nat.add_sub_cancel, det]
      simp only [WideReversible.details,
        QuantBlock.mx, QuantBlock.my, Band.xob, Band.yob, Rect.width, Rect.height,
        ← show halfRect (halfN r k) = halfN r (k+1) from rfl]
      simp only [InBand, bandRect, Band.xob, Band.yob, DWTPlane.bandCoord_low,
        DWTPlane.bandCoord_high, ← x0, ← y0, ← x1, ← y1, ← lx0, ← ly0, ← lx1, ← ly1] at inside
      simp (config := { decide := true }) only [↓reduceIte, Nat.add_sub_cancel]
      have low := DWTPlane.halfN_mono r k
      simp only [halfN, halfRect] at inside ⊢
      congr 3 <;> omega

private theorem source_shape (s : Spatial) :
    s.source.width = s.rect.width ∧ s.source.height = s.rect.height := by
  cases s with
  | compact r f q hw hh => exact ⟨hw, hh⟩
  | wide p => exact ⟨rfl, rfl⟩

/-- Every local fixed-point value used in the C8 bounds is the value observed by the
native source accessor on the corresponding component rectangle. -/
theorem source_fixed (s : Spatial) (i : Nat) (hi : i < rectArea s.rect) :
    s.source.get? i = some (s.fixed i) := by
  have h : i < s.source.width * s.source.height := by rw [(source_shape s).1, (source_shape s).2]; exact hi
  simp [Spatial.fixed, NativeOutput.Source.get?, h]

private theorem physical_bound {F n : Nat} {z x : Rat} (h : (z - pw F * x).abs ≤ En n (1/2)) :
    (z / pw F - x).abs ≤ errOf F n := by
  have hp : 0 < pw F := by exact_mod_cast Nat.two_pow_pos F
  have hp' : pw F ≠ 0 := by grind
  have e : z / pw F - x = (z - pw F * x) * (pw F)⁻¹ := by grind
  rw [e]
  have m := Spec.DWT97.abs_mul_le _ (pw F)⁻¹ _ h
  have pos := Rat.le_of_lt (Rat.inv_pos.mpr hp)
  rw [Rat.abs_of_nonneg pos] at m
  unfold errOf
  rw [Rat.div_def]
  exact Rat.le_trans m (Rat.mul_le_mul_of_nonneg_right (by grind) pos)

/-- One independent rational Annex F sample at a local row-major index. -/
def target (r : Rect) (nl : Nat) (d : Spec.DWT97.Dec) (j : Nat) : Rat :=
  (Spec.DWT97.srMulti (specRect r) nl d).get (posU r j) (posV r j)

/-- Shape, actual binary scale and physical error on the whole reduced plane. This is
also the post-colour claim for a component outside the ICT. -/
def SpatialAgrees (s : Spatial) (r : Rect) (F nl : Nat) (d : Spec.DWT97.Dec) : Prop :=
  s.rect = r ∧ s.bits = F ∧ ∀ j, j < rectArea r →
    (((s.fixed j : Int) : Rat) / pw s.bits - target r nl d j).abs ≤ cellErr s.bits false [nl]

private theorem compact_fixed (r : Rect) (F : Nat) (q : Plane) (hw : q.width = r.width)
    (hh : q.height = r.height) (j : Nat) (hj : j < rectArea r) {v : Int32}
    (hit : q.get? j = some v) : (Spatial.compact r F q hw hh).fixed j = v.toInt := by
  have h : j < q.width * q.height := by rw [hw,hh]; exact hj
  simp only [Plane.get?, h, ↓reduceDIte, Option.some.injEq] at hit
  simp [Spatial.fixed, Spatial.source, NativeOutput.Source.get?, NativeOutput.Source.width,
    NativeOutput.Source.height, NativeOutput.Source.read, h, hit]

private theorem compact_lift {p q : Plane} {r : Rect} {nl F : Nat}
    (d : Spec.DWT97.Dec) (len : d.details.length = nl)
    (hw : p.width = r.width) (hh : p.height = r.height)
    (bands : BandsClose (1/2) F r nl (JPEG2000.DWT53.toDec p r nl) d)
    (fast : JPEG2000.DWT97.idwt97Fast p r nl = some q) (qw : q.width = r.width)
    (qh : q.height = r.height) : SpatialAgrees (.compact r F q qw qh) r F nl d := by
  refine ⟨rfl, rfl, fun j hj => ?_⟩
  obtain ⟨v, hit, err⟩ := (DWTPlane.idwt97Fast_err p r nl F d _ q hw hh len fast).2.2 bands j hj
  rw [compact_fixed r F q qw qh j hj hit]
  exact physical_bound (F := F) (n := nl) err

private theorem compact_spatial {p : Plane} {r : Rect} {nl F : Nat} {s : Spatial}
    (ok : compactSpatial p r nl F = some s) (d : Spec.DWT97.Dec) (len : d.details.length = nl)
    (hw : p.width = r.width) (hh : p.height = r.height)
    (bands : BandsClose (1/2) F r nl (JPEG2000.DWT53.toDec p r nl) d) :
    SpatialAgrees s r F nl d := by
  unfold compactSpatial at ok
  generalize fast : JPEG2000.DWT97.idwt97Fast p r nl = result at ok
  cases result with
  | none => cases ok
  | some q =>
    simp only [bind, Option.bind] at ok
    split at ok
    · rename_i shape
      cases ok
      exact compact_lift d len hw hh bands fast shape.1 shape.2
    · cases ok

private theorem wide_spatial {L : Limits} {p q : JPEG2000.WideQuant.Plane} {nl F : Nat}
    (ok : JPEG2000.WideDWT97.idwt97 L p nl = .ok q) (d : Spec.DWT97.Dec)
    (len : d.details.length = nl)
    (bands : BandsClose (1/2) F p.rect nl (WideReversible.mallat p.samples.toArray p.rect.width p.rect nl) d) :
    SpatialAgrees (.wide ⟨q,F⟩) p.rect F nl d := by
  obtain ⟨shape, cells⟩ := WideDWT97.idwt97_of_bandsClose ok d len _ bands
  refine ⟨shape, rfl, fun j hj => ?_⟩
  let w := p.rect.width
  have area : j < w * p.rect.height := hj
  have wp : 0 < w := Nat.pos_of_mul_pos_right (Nat.zero_lt_of_lt area)
  have hx := Nat.mod_lt j wp
  have hy := (Nat.div_lt_iff_lt_mul wp).mpr (Nat.mul_comm w p.rect.height ▸ area)
  obtain ⟨z, get, err⟩ := cells (j % w) (j / w) hx hy
  have index : j / w * p.rect.width + j % w = j := by
    rw [Nat.mul_comm, Nat.add_comm]; exact Nat.mod_add_div ..
  rw [index] at get
  have hq : j < rectArea q.rect := shape ▸ hj
  have hq' : j < q.samples.toArray.size := by simpa only [Vector.size_toArray] using hq
  simp only [Array.getElem?_eq_getElem hq', Option.some.injEq] at get
  subst z
  have fixed : (Spatial.wide ⟨q,F⟩).fixed j = q.samples.toArray[j] := by
    change ((if h : j < q.rect.width * q.rect.height then some (q.samples.get ⟨j,h⟩) else none).getD 0) = _
    rw [dite_eq_left (show j < q.rect.width * q.rect.height from hq)]
    rfl
  rw [fixed]
  exact physical_bound (F := F) (n := nl) err

private theorem bind_ok {α β : Type} {x : Except Error α} {f : α → Except Error β} {b : β}
    (h : x >>= f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- Samplewise C8 for the actual component dispatcher and the spec entries collected from
its packet image. No premise about an intermediate or final sample magnitude is needed. -/
theorem component_c8 {L : Limits} {data : ByteArray} {tc : TileCompGeom} {depth F red : Nat}
    {ps : Array (Array PrecinctOut)} {allow : Bool} {s : Spatial} (params : Equiv.ParamsWF tc)
    (wf : Equiv.PrecsWF tc ps) (ranges : Equiv.BlocksIn data ps)
    (ok : component L data tc depth F red ps allow = .ok s) :
    ∃ es, WideAssembly.entries L tc depth F red (Equiv.imagePrecs data ps) = .ok (es, 0) ∧
      SpatialAgrees s (Assemble.reduceRect tc.rect red) F (tc.params.levels-red)
        (dec97 es (tc.params.levels-red)) := by
  unfold component at ok
  dsimp only at ok
  split at ok
  · cases ok
  rename_i transform
  have irr : (tc.params.transform == .reversible53) = false := by
    cases ht : tc.params.transform <;> simp [ht] at transform ⊢
  split at ok
  · cases ok
  rename_i reduction
  obtain ⟨_, _, ok⟩ := bind_ok ok
  split at ok
  · cases ok
  obtain ⟨attempt, attempted, ok⟩ := bind_ok ok
  cases attempt with
  | some q =>
    cases ok
    cases allow <;> simp only [Bool.false_eq_true, ↓reduceIte] at attempted
    · cases attempted
    unfold tryCompact at attempted
    cases bands : compactBands L data tc depth F red ps with
    | error e => cases e <;> simp [bands] at attempted
    | ok p =>
      simp only [bands, Except.ok.injEq] at attempted
      obtain ⟨es, entries, rel⟩ := compactBands_ok (Nat.le_of_not_lt reduction) params wf ranges bands
      obtain ⟨hw, hh, close⟩ := rel
      refine ⟨es, entries, compact_spatial attempted _ (by simp [dec97]) hw hh ?_⟩
      simpa [irr] using close rfl
  | none =>
    obtain ⟨p, bands, ok⟩ := bind_ok ok
    obtain ⟨q, lifted, ok⟩ := bind_ok ok
    cases ok
    obtain ⟨es, entries, rel⟩ := WideAssembly.tileComp_sound wf ranges bands
    rw [irr] at rel
    have close := wide_bands rel
    rw [← rel.1] at close ⊢
    exact ⟨es, entries, wide_spatial lifted _ (by simp [dec97]) close⟩

private theorem packRows_ok {N : Nat} (f : Nat → Int) (n : Nat) (hn : n ≤ N)
    (p q : JPEG2000.DWT53.Buf N) (ok : packRows f n hn p = some q) (j : Nat) (hj : j < N) :
    (q.get j hj).toInt = if j < n then f j else (p.get j hj).toInt := by
  induction n generalizing p with
  | zero => cases ok; simp
  | succ k ih =>
    unfold packRows at ok
    dsimp only at ok
    split at ok
    · rename_i fit
      rw [ih _ _ ok, JPEG2000.DWT53.Buf.get_set]
      by_cases e : j = k
      · subst j; simp [fit]
      · by_cases h : j < k <;> simp [h, Ne.symm e, show (j < k+1) ↔ j < k by omega]
    · cases ok

private theorem pack_ok {r : Rect} {F : Nat} {f : Nat → Int} {s : Spatial}
    (ok : pack r F f = some s) :
    s.rect = r ∧ s.bits = F ∧ ∀ i, i < rectArea r → s.fixed i = f i := by
  unfold pack at ok
  generalize filled : packRows f (rectArea r) _ _ = result at ok
  cases result with
  | none => cases ok
  | some q =>
    dsimp only [bind, Option.bind] at ok
    split at ok
    · rename_i shape
      cases ok
      refine ⟨rfl, rfl, fun i hi => ?_⟩
      have hq : i < q.val.width * q.val.height := by rw [q.2]; exact hi
      rw [compact_fixed _ _ _ _ _ _ hi (show q.val.get? i = some (q.get i hi) by
        simp only [Plane.get?, hq, ↓reduceDIte]; rfl)]
      simpa only [hi, ↓reduceIte] using packRows_ok _ _ _ _ _ filled i hi
    · cases ok

private abbrev Row (q : Spatial) (r : Rect) (F : Nat) (f : Nat → Int) :=
  q.rect = r ∧ q.bits = F ∧ ∀ i, i < rectArea r → q.fixed i = f i

private theorem compact_rows {y cb cr : Spatial} {out : Spatial × Spatial × Spatial}
    (ok : compactICT y cb cr = some out) :
    Row out.1 y.rect y.bits (fun i => JPEG2000.WideICT.red (y.fixed i) (cr.fixed i)) ∧
    Row out.2.1 cb.rect y.bits (fun i => JPEG2000.WideICT.green (y.fixed i) (cb.fixed i) (cr.fixed i)) ∧
    Row out.2.2 cr.rect y.bits (fun i => JPEG2000.WideICT.blue (y.fixed i) (cb.fixed i)) := by
  cases y <;> cases cb <;> cases cr <;> try cases ok
  unfold compactICT at ok
  simp only [bind, Option.bind_eq_some_iff] at ok
  obtain ⟨r, hr, g, hg, b, hb, eq⟩ := ok
  cases eq
  exact ⟨pack_ok hr, pack_ok hg, pack_ok hb⟩

private theorem wide_meta (s : Spatial) : s.toWide.rect = s.rect ∧ s.toWide.fracBits = s.bits := by
  cases s <;> exact ⟨rfl, rfl⟩

private theorem fixed_ofFn (r : Rect) (F : Nat) (f : Fin (rectArea r) → Int) (i : Nat) (hi : i < rectArea r) :
    WideICT.fixed ⟨⟨r,Vector.ofFn f⟩,F⟩ i = f ⟨i,hi⟩ := by
  simp [WideICT.fixed, Array.getD_eq_getD_getElem?, hi]

private theorem promote_fixed (s : Spatial) (i : Nat) (hi : i < rectArea s.rect) :
    WideICT.fixed s.toWide i = s.fixed i := by
  cases s with
  | compact r F p hw hh =>
    change i < rectArea r at hi
    have hp : i < p.width * p.height := by rw [hw,hh]; exact hi
    exact (fixed_ofFn r F _ i hi).trans (compact_fixed r F p hw hh i hi
      (show p.get? i = some (p.get i hp) by simp only [Plane.get?, hp, ↓reduceDIte])).symm
  | wide p =>
    have h : i < p.rect.width * p.rect.height := hi
    have hs : i < p.samples.toArray.size := by rw [Vector.size_toArray]; exact hi
    change p.samples.toArray.getD i 0 = (if h : i < p.rect.width * p.rect.height then
      some (p.samples.get ⟨i,h⟩) else none).getD 0
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hs, dite_eq_left h]
    rfl

private theorem model_rows (y cb cr : JPEG2000.WideICT.Component)
    (shape : JPEG2000.WideReversible.SameShape y.rect cb.rect cr.rect) (i : Nat) (hi : i < rectArea y.rect) :
    let out := JPEG2000.WideICT.colour y cb cr shape
    WideICT.fixed out.1 i = JPEG2000.WideICT.red (WideICT.fixed y i) (WideICT.fixed cr i) ∧
    WideICT.fixed out.2.1 i = JPEG2000.WideICT.green (WideICT.fixed y i) (WideICT.fixed cb i) (WideICT.fixed cr i) ∧
    WideICT.fixed out.2.2 i = JPEG2000.WideICT.blue (WideICT.fixed y i) (WideICT.fixed cb i) := by
  obtain ⟨bw,bh,rw,rh⟩ := shape
  have hb : i < rectArea cb.rect := by simpa only [rectArea,bw,bh] using hi
  have hr : i < rectArea cr.rect := by simpa only [rectArea,rw,rh] using hi
  simp [WideICT.fixed, JPEG2000.WideICT.colour, Array.getD_eq_getD_getElem?, hi, hb, hr]

/-- Physical sample value observed on a selected spatial or colour source. -/
abbrev physical (p : Spatial) (i : Nat) : Rat := (p.fixed i : Rat) / pw p.bits

private theorem promote_physical (s : Spatial) (i : Nat) (hi : i < rectArea s.rect) :
    WideICT.physical s.toWide i = physical s i := by
  simp only [WideICT.physical, promote_fixed s i hi, (wide_meta s).2, physical]

private theorem max_errors (F a b c : Nat) :
    errOf F a ≤ Equiv.maxErr F [a,b,c] ∧ errOf F b ≤ Equiv.maxErr F [a,b,c] ∧
    errOf F c ≤ Equiv.maxErr F [a,b,c] := by
  have l (x y : Rat) : x ≤ Equiv.rmax x y := by unfold Equiv.rmax; split <;> grind
  have r (x y : Rat) : y ≤ Equiv.rmax x y := by unfold Equiv.rmax; split <;> grind
  exact ⟨l .., Rat.le_trans (l ..) (r ..), Rat.le_trans (l ..) (Rat.le_trans (r ..) (r ..))⟩

/-- Physical C8 error of the selected post-ICT source at every local index. Each reference
peer has its own reduced level count. The three inputs must meet their individual 9/7
bounds; the dispatcher itself establishes their common scale and geometry. -/
theorem ict_c8 {L : Limits} {y cb cr : Spatial} {out : Spatial × Spatial × Spatial}
    (ok : ict L y cb cr = .ok out) :
    JPEG2000.WideReversible.SameShape y.rect cb.rect cr.rect ∧
    cb.bits = y.bits ∧ cr.bits = y.bits ∧
    out.1.rect = y.rect ∧ out.2.1.rect = cb.rect ∧ out.2.2.rect = cr.rect ∧
    out.1.bits = y.bits ∧ out.2.1.bits = y.bits ∧ out.2.2.bits = y.bits ∧
    ∀ i, i < rectArea y.rect → ∀ (ref : MCT.Triple Rat) (a b c : Nat),
      WideICT.Close (physical y i, physical cb i, physical cr i) ref
        (errOf y.bits a, errOf cb.bits b, errOf cr.bits c) →
      let E := cellErr y.bits true [a,b,c]
      WideICT.Close (physical out.1 i, physical out.2.1 i, physical out.2.2 i)
        (MCT.ictInv ref) (E,E,E) := by
  unfold ict at ok
  obtain ⟨u, budget, ok⟩ := bind_ok ok
  split at ok
  case isFalse => cases ok
  rename_i compat
  let shape := compat.1
  refine ⟨shape, compat.2.2.2.2.1, compat.2.2.2.2.2, ?_⟩
  have H : JPEG2000.WideICT.Compatible y.toWide cb.toWide cr.toWide := by
    simpa only [JPEG2000.WideICT.Compatible, (wide_meta y).1, (wide_meta cb).1, (wide_meta cr).1,
      (wide_meta y).2, (wide_meta cb).2, (wide_meta cr).2] using compat
  let model := JPEG2000.WideICT.colour y.toWide cb.toWide cr.toWide H.1
  have modelOk : JPEG2000.WideICT.ictInverse L y.toWide cb.toWide cr.toWide = .ok model := by
    apply (WideICT.ictInverse_ok ..).2
    cases u
    refine ⟨?_, H, rfl⟩
    rw [(wide_meta y).1, (wide_meta cb).1, (wide_meta cr).1]
    exact (Limits.check_eq_ok_iff ..).1 budget
  have peerBounds (i : Nat) (hi : i < rectArea y.rect) :
      i < rectArea cb.rect ∧ i < rectArea cr.rect := by
    obtain ⟨w,h,w',h'⟩ := shape
    exact ⟨by simpa only [rectArea,w,h] using hi, by simpa only [rectArea,w',h'] using hi⟩
  have measured (i : Nat) (hi : i < rectArea y.rect) (ref : MCT.Triple Rat) (a b c : Nat)
      (bounds : WideICT.Close (physical y i, physical cb i, physical cr i) ref
        (errOf y.bits a, errOf cb.bits b, errOf cr.bits c)) :
      let E := cellErr y.bits true [a,b,c]
      WideICT.Close (WideICT.physical model.1 i, WideICT.physical model.2.1 i, WideICT.physical model.2.2 i)
        (MCT.ictInv ref) (E,E,E) := by
    let e := Equiv.maxErr y.bits [a,b,c]
    obtain ⟨ea,eb,ec⟩ := max_errors y.bits a b c
    obtain ⟨hb,hr⟩ := peerBounds i hi
    rw [compat.2.2.2.2.1, compat.2.2.2.2.2] at bounds
    have h : WideICT.Close (WideICT.physical y.toWide i, WideICT.physical cb.toWide i,
        WideICT.physical cr.toWide i) ref (e,e,e) := by
      rw [promote_physical _ _ hi, promote_physical _ _ hb, promote_physical _ _ hr]
      exact ⟨Rat.le_trans bounds.1 ea, Rat.le_trans bounds.2.1 eb, Rat.le_trans bounds.2.2 ec⟩
    have := WideICT.ictInverse_c8 modelOk i (by rw [(wide_meta y).1]; exact hi) ref (e,e,e) h
    have same : max e e = e := by grind
    simpa only [same, (wide_meta y).2, cellErr, ↓reduceIte, e] using this
  cases fast : compactICT y cb cr with
  | none =>
    rw [fast] at ok
    simp only [modelOk, Equiv.ok_bind, pure] at ok
    cases ok
    refine ⟨(wide_meta y).1, (wide_meta cb).1, (wide_meta cr).1,
      (wide_meta y).2, (wide_meta y).2, (wide_meta y).2, fun i hi ref a b c h => ?_⟩
    obtain ⟨hb,hr⟩ := peerBounds i hi
    have conv (p : JPEG2000.WideICT.Component) (hp : i < rectArea p.rect) :
        physical (.wide p) i = WideICT.physical p i := (promote_physical (.wide p) i hp).symm
    rw [conv model.1 (by change i < rectArea y.toWide.rect; rwa [(wide_meta y).1]),
      conv model.2.1 (by change i < rectArea cb.toWide.rect; rwa [(wide_meta cb).1]),
      conv model.2.2 (by change i < rectArea cr.toWide.rect; rwa [(wide_meta cr).1])]
    exact measured i hi ref a b c h
  | some result =>
    rw [fast] at ok
    cases ok
    obtain ⟨red,green,blue⟩ := compact_rows fast
    refine ⟨red.1, green.1, blue.1, red.2.1, green.2.1, blue.2.1, fun i hi ref a b c h => ?_⟩
    obtain ⟨hb,hr⟩ := peerBounds i hi
    have modelAt := model_rows y.toWide cb.toWide cr.toWide H.1 i (by rwa [(wide_meta y).1])
    change WideICT.fixed model.1 i = _ ∧ WideICT.fixed model.2.1 i = _ ∧ WideICT.fixed model.2.2 i = _ at modelAt
    rw [promote_fixed _ _ hi, promote_fixed _ _ hb, promote_fixed _ _ hr] at modelAt
    have := measured i hi ref a b c h
    simp only [physical, red.2.1, green.2.1, blue.2.1, red.2.2 i hi, green.2.2 i hb, blue.2.2 i hr]
    simpa only [WideICT.physical, modelAt.1, modelAt.2.1, modelAt.2.2,
      show model.1.fracBits = y.bits from (wide_meta y).2,
      show model.2.1.fracBits = y.bits from (wide_meta y).2,
      show model.2.2.fracBits = y.bits from (wide_meta y).2] using this

/-- The independent Annex F input and metadata for one retained component. -/
structure Reference where
  /-- Reduced component-grid rectangle. -/
  rect : Rect
  /-- Working fractional precision. -/
  bits : Nat
  /-- Retained inverse wavelet levels. -/
  levels : Nat
  /-- Physical, rational sub-bands. -/
  bands : Spec.DWT97.Dec

/-- Independent pre-colour spec cell, including the component's own level count. -/
def Reference.cell (r : Reference) (j : Nat) : Decode.SpecCell :=
  .ofIrrev (target r.rect r.levels r.bands j) r.levels

/-- Post-MCT cell in the native writer's component order. ICT combines the first three
local indices even when the component rectangles have different origins. -/
def postCell (mct : Bool) (ref : Nat → Reference) (c j : Nat) : Decode.SpecCell :=
  if mct ∧ c < 3 then
    let rgb := Decode.ictCells ((ref 0).cell j) ((ref 1).cell j) ((ref 2).cell j)
    if c = 0 then rgb.1 else if c = 1 then rgb.2.1 else rgb.2.2
  else (ref c).cell j

/-- The numerical precondition of native G.1, stated on the actual selected source. -/
def SourceAgrees (src : NativeOutput.Source) (r : Reference) (cell : Nat → Decode.SpecCell) : Prop :=
  src.width = r.rect.width ∧ src.height = r.rect.height ∧
    ∀ j, j < rectArea r.rect → ∃ z, src.get? j = some z ∧ NativeSample.CenteredAgrees r.bits false z (cell j)

private theorem single_source {ref : Nat → Reference} {c : Nat} {p : Spatial} {mct : Bool}
    (pre : SpatialAgrees p (ref c).rect (ref c).bits (ref c).levels (ref c).bands)
    (single : ¬ (mct ∧ c < 3)) : SourceAgrees p.source (ref c) (postCell mct ref c) := by
  obtain ⟨shape, bits, all⟩ := pre
  refine ⟨(source_shape p).1.trans (congrArg Rect.width shape),
    (source_shape p).2.trans (congrArg Rect.height shape), fun j hj => ?_⟩
  refine ⟨_, source_fixed _ _ (shape ▸ hj), ?_⟩
  simpa only [NativeSample.CenteredAgrees, Bool.false_eq_true, ↓reduceIte, postCell, ite_eq_right single, Reference.cell,
    Decode.SpecCell.ofIrrev, bits] using all j hj

/-- The three actual ICT sources meet the native writer's bounds against independent
component references, including each peer's own resolution level count. -/
theorem ict_sources {L : Limits} {y cb cr : Spatial} {out : Spatial × Spatial × Spatial}
    {ref : Nat → Reference} (ok : ict L y cb cr = .ok out)
    (p0 : SpatialAgrees y (ref 0).rect (ref 0).bits (ref 0).levels (ref 0).bands)
    (p1 : SpatialAgrees cb (ref 1).rect (ref 1).bits (ref 1).levels (ref 1).bands)
    (p2 : SpatialAgrees cr (ref 2).rect (ref 2).bits (ref 2).levels (ref 2).bands) :
    SourceAgrees out.1.source (ref 0) (postCell true ref 0) ∧
    SourceAgrees out.2.1.source (ref 1) (postCell true ref 1) ∧
    SourceAgrees out.2.2.source (ref 2) (postCell true ref 2) := by
  obtain ⟨shape, fb, fr, r0,r1,r2,f0,f1,f2,measure⟩ := ict_c8 ok
  obtain ⟨bw,bh,rw,rh⟩ := shape
  have area1 : rectArea cb.rect = rectArea y.rect := by simp only [rectArea,bw,bh]
  have area2 : rectArea cr.rect = rectArea y.rect := by simp only [rectArea,rw,rh]
  have ar0 := congrArg rectArea p0.1
  have ar1 := congrArg rectArea p1.1
  have ar2 := congrArg rectArea p2.1
  let x := fun c j => target (ref c).rect (ref c).levels (ref c).bands j
  have atIndex (i : Nat) (hi : i < rectArea y.rect) :=
    measure i hi (x 0 i, x 1 i, x 2 i) (ref 0).levels (ref 1).levels (ref 2).levels
      ⟨p0.2.2 i (ar0 ▸ hi), p1.2.2 i ((area1.symm.trans ar1) ▸ hi),
        p2.2.2 i ((area2.symm.trans ar2) ▸ hi)⟩
  have toSrc (c : Nat) (p : Spatial) (hr : p.rect = (ref c).rect)
      (hf : p.bits = (ref c).bits) (hcell : ∀ j, j < rectArea (ref c).rect →
        (physical p j - (postCell true ref c j).rval).abs ≤ cellErr p.bits
          (postCell true ref c j).mct (postCell true ref c j).levels) :
      SourceAgrees p.source (ref c) (postCell true ref c) := by
    refine ⟨(source_shape p).1.trans (congrArg Rect.width hr),
      (source_shape p).2.trans (congrArg Rect.height hr), fun j hj => ?_⟩
    exact ⟨_, source_fixed _ _ (hr ▸ hj), hf ▸ hcell j hj⟩
  refine ⟨toSrc 0 _ (r0.trans p0.1) (f0.trans p0.2.1) ?_,
    toSrc 1 _ (r1.trans p1.1) ((f1.trans fb.symm).trans p1.2.1) ?_,
    toSrc 2 _ (r2.trans p2.1) ((f2.trans fr.symm).trans p2.2.1) ?_⟩
  · intro j hj
    rw [f0]
    exact (atIndex j (ar0 ▸ hj)).1
  · intro j hj
    rw [f1]
    exact (atIndex j ((area1.symm.trans ar1) ▸ hj)).2.1
  · intro j hj
    rw [f2]
    exact (atIndex j ((area2.symm.trans ar2) ▸ hj)).2.2

/-- Every post-MCT source in the returned array meets native G.1's per-cell precondition.
This includes independently reconstructed extra components and tiles without an MCT. -/
theorem sources_c8 {L : Limits} {mct : Bool} {ps : Array Spatial} {out : Array JPEG2000.NativeOutput.Source}
    (ok : sources L mct ps = .ok out) (ref : Nat → Reference)
    (pre : ∀ c p, ps[c]? = some p → SpatialAgrees p (ref c).rect (ref c).bits (ref c).levels (ref c).bands) :
    out.size = ps.size ∧ ∀ c, c < ps.size → ∃ src, out[c]? = some src ∧
      SourceAgrees src (ref c) (postCell mct ref c) := by
  unfold sources at ok
  cases mct with
  | false =>
    simp only [Bool.not_false, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at ok
    subst out
    refine ⟨Array.size_map .., fun c hc => ?_⟩
    have hp := Array.getElem?_eq_getElem (xs := ps) hc
    exact ⟨_, by rw [Array.getElem?_map, hp]; rfl, single_source (pre c _ hp) (by simp)⟩
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at ok
    split at ok <;> try contradiction
    rename_i y hy
    split at ok <;> try contradiction
    rename_i cb hcb
    split at ok <;> try contradiction
    rename_i cr hcr
    obtain ⟨rgb, converted, eq⟩ := bind_ok ok
    cases eq
    obtain ⟨red,green,blue⟩ := ict_sources converted (pre 0 _ hy) (pre 1 _ hcb) (pre 2 _ hcr)
    refine ⟨by simp, fun c hc => ?_⟩
    have s0 := (Array.getElem?_eq_some_iff.mp hy).1
    have s1 := (Array.getElem?_eq_some_iff.mp hcb).1
    have s2 := (Array.getElem?_eq_some_iff.mp hcr).1
    simp only [Array.getElem?_setIfInBounds, Array.size_setIfInBounds, Array.size_map]
    by_cases a : c = 0
    · subst c; simp [s0, red]
    by_cases b : c = 1
    · subst c; simp [s1, green]
    by_cases d : c = 2
    · subst c; simp [s2, blue]
    have hp := Array.getElem?_eq_getElem (xs := ps) hc
    simp [Ne.symm a, Ne.symm b, Ne.symm d, Array.getElem?_map,hp,
      single_source (mct := true) (pre c _ hp) (by omega)]

/-- Reference geometry, precision and rational bands of each spec packet component. -/
def reference (siz : Marker.SIZ) (g : Progression.Layout) (coding : Coding) (red : Nat)
    (es : Nat → List Entry) (c : Nat) : Reference :=
  let tc := g.comp c
  let n := tc.params.levels - red
  ⟨Assemble.reduceRect tc.rect red, Assemble.fracBitsOf siz (coding.mctApplies siz) c, n, dec97 (es c) n⟩

/-- A complete stage claim on the actual array consumed by native G.1. The entries are
collected by the independent decoder from its packet bodies, with no clipped-band premise. -/
def TileAgrees (L : Limits) (siz : Marker.SIZ) (g : Progression.Layout) (coding : Coding)
    (red : Nat) (ps : Nat → Decode.SpecPrecs) (out : Array JPEG2000.NativeOutput.Source) : Prop :=
  ∃ es : Nat → List Entry,
    (∀ c, c < g.numComps → WideAssembly.entries L (g.comp c) (siz.components.getD c default).depth.toNat
      (Assemble.fracBitsOf siz (coding.mctApplies siz) c) red (ps c) = .ok (es c, 0)) ∧
    out.size = g.numComps ∧ ∀ c, c < g.numComps → ∃ src, out[c]? = some src ∧
      SourceAgrees src (reference siz g coding red es c) (postCell (coding.mctApplies siz) (reference siz g coding red es) c)

private theorem map_ok {α β : Type} (xs : Array α) (f : (i : Nat) → α → i < xs.size → Except Error β)
    {out : Array β} (ok : xs.mapFinIdxM f = .ok out) :
    xs.size = out.size ∧ ∀ i (hi : i < xs.size), ∃ b, out[i]? = some b ∧ f i xs[i] hi = .ok b := by
  have loop (k j : Nat) (inv : k + j = xs.size) (acc : Array β) (sz : acc.size = j)
      (hk : Array.mapFinIdxM.map xs f k j inv acc = .ok out) :
      xs.size = out.size ∧ (∀ i < j, out[i]? = acc[i]?) ∧
      ∀ i (hi : i < xs.size), j ≤ i → ∃ b, out[i]? = some b ∧ f i xs[i] hi = .ok b := by
    induction k generalizing j acc with
    | zero =>
      simp [Array.mapFinIdxM.map, pure, Except.pure] at hk
      subst out
      exact ⟨by omega, fun _ _ => rfl, fun _ _ _ => by omega⟩
    | succ k ih =>
      rw [Array.mapFinIdxM.map] at hk
      obtain ⟨b, hb, hk⟩ := bind_ok hk
      obtain ⟨hout, earlier, suffix⟩ := ih (j + 1) (by omega) (acc.push b) (by simp [sz]) hk
      refine ⟨hout, fun i hi => ?_, fun i hi hji => ?_⟩
      · rw [earlier i (by omega), Array.getElem?_push, ite_eq_right (by omega)]
      · by_cases e : i = j
        · subst i
          exact ⟨b, by rw [earlier j (by omega), Array.getElem?_push, sz, ite_eq_left rfl], hb⟩
        · exact suffix i hi (by omega)
  obtain ⟨sz, _, h⟩ := loop xs.size 0 (by omega) #[] rfl ok
  exact ⟨sz, fun i hi => h i hi (Nat.zero_le _)⟩

/-- Irreversible reconstruction up to the native writer, for any well-formed packet store,
including an absent tile. Each output component and every local sample is covered. -/
theorem tile_c8 {L : Limits} {data : ByteArray} {siz : Marker.SIZ} {g : Progression.Layout}
    {coding : Coding} {store : Option TileCodeBlocks} {red : Nat} {allow : Bool}
    {out : Array JPEG2000.NativeOutput.Source}
    (ok : tile L data siz g coding store red allow = .ok out)
    (params : ∀ c, Equiv.ParamsWF (g.comp c))
    (wf : ∀ c, Equiv.PrecsWF (g.comp c) ((store.map (·.comps.getD c #[])).getD #[]))
    (ranges : ∀ c, Equiv.BlocksIn data ((store.map (·.comps.getD c #[])).getD #[])) :
    TileAgrees L siz g coding red (fun c => Equiv.imagePrecs data ((store.map (·.comps.getD c #[])).getD #[])) out := by
  let prec := fun c => ((store.map (·.comps.getD c #[])).getD #[])
  let gather := fun c => WideAssembly.entries L (g.comp c) (siz.components.getD c default).depth.toNat
    (Assemble.fracBitsOf siz (coding.mctApplies siz) c) red (Equiv.imagePrecs data (prec c))
  let es := fun c => ((gather c).toOption.map Prod.fst).getD []
  let ref := reference siz g coding red es
  unfold tile at ok
  obtain ⟨_, _, ok⟩ := bind_ok ok
  obtain ⟨_, _, ok⟩ := bind_ok ok
  obtain ⟨spatial, comps, colour⟩ := bind_ok ok
  obtain ⟨size, each⟩ := map_ok _ _ comps
  have pre (c : Nat) (hc : c < g.comps.size) : ∃ p, spatial[c]? = some p ∧
      gather c = .ok (es c, 0) ∧ SpatialAgrees p (ref c).rect (ref c).bits (ref c).levels (ref c).bands := by
    obtain ⟨p, got, decoded⟩ := each c hc
    have tc : g.comp c = g.comps[c] := by simp [Progression.Layout.comp, Array.getD, hc]
    obtain ⟨entries, collected, rel⟩ := component_c8 (params c) (wf c) (ranges c) (tc ▸ decoded)
    change gather c = .ok (entries, 0) at collected
    have chosen : es c = entries := by simp [es, collected, Except.toOption]
    refine ⟨p, got, chosen ▸ collected, ?_⟩
    change SpatialAgrees p _ _ _ (dec97 (es c) _)
    rwa [chosen]
  obtain ⟨sz, all⟩ := sources_c8 colour ref (by
    intro c p hp
    have hc := (Array.getElem?_eq_some_iff.mp hp).1
    obtain ⟨p', hp', _, rel⟩ := pre c (size ▸ hc)
    rw [hp] at hp'
    cases hp'
    exact rel)
  refine ⟨es, fun c hc => ?_, sz.trans size.symm, fun c hc => all c (size ▸ hc)⟩
  obtain ⟨_, _, entries, _⟩ := pre c hc
  exact entries

/-- End of the parsed-packet irreversible stage. The header parser and packet decoder
supply every band, containment and range fact used by `tile_c8`. The resulting native
source claim uses the spec's actual tile packet store. -/
theorem parsed_tile_c8 {L : Limits} {data : ByteArray} {h : Header} {g : Progression.Layout}
    {coding : Coding} {tp : TileParams} {hs : Option JPEG2000.Tier2.Headers.HeaderStream}
    {n red : Nat} {store : TileCodeBlocks} {allow : Bool} {out : Array JPEG2000.NativeOutput.Source}
    (parsed : Header.parse L data = .ok h) (layout : Progression.Layout.ofHeader h tp.index = .ok (g,coding))
    (packets : JPEG2000.Tier2.Headers.decodeWithStream L h data tp hs n = .ok store)
    (ok : tile L data h.siz g coding (some store) red allow = .ok out) :
    ∃ st, Spec.Tier2.decodeWithStream L h data tp hs n = .ok st ∧
      TileAgrees L h.siz g coding red (fun c => st.comps.getD c []) out := by
  have wf := Tier2WF.tier2WF _ _ _ _ _ _ _ packets
  have proved := tile_c8 ok ((HeaderWF.headerWF _ _ _ parsed _ _ _ layout).1) (wf.1 _ _ layout) wf.2
  have sim := Tier2Equiv.tier2_equiv_of_siz L h data tp hs n (Equiv.parse_dxdy parsed)
  rw [packets] at sim
  cases spec : Spec.Tier2.decodeWithStream L h data tp hs n with
  | error e => rw [spec] at sim; exact False.elim sim
  | ok st =>
    rw [spec] at sim
    refine ⟨st, rfl, ?_⟩
    simpa only [sim.1, Equiv.image_getD, Option.map_some, Option.getD_some] using proved

end JPEG2000.Spec.IrreversibleDispatch
