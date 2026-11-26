import JPEG2000.ReversibleDispatch
import Spec.WideAssembly
import Spec.WideReversible
import Spec.HeaderWF
import Spec.Tier1Wire

/-!
# Exact reversible reconstruction dispatch (Plan.md §§4, 5.1, 5.4, 7; T.800 B-15, D, E, F, G)

Compare both reconstruction branches with the specification on the packet store's
independent entries. Colour combines the centred component values before G.1.
-/

namespace JPEG2000.Spec.ReversibleDispatch

open JPEG2000.ReversibleDispatch JPEG2000.NativeOutput Bytes Header
open JPEG2000.Tier2.Geometry JPEG2000.Tier2.Packet
open JPEG2000.DWT53 (halfRect halfN specRect)
open JPEG2000.Spec.Decode (Entry dec53 tileCompWith)
open JPEG2000.Spec.WideReversible (mallat details)

private theorem half_step (r : Rect) (k : Nat) : halfN (halfRect r) k = halfN r (k+1) := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg halfRect ih

private theorem ll_read (p : Array Int) (s : Nat) (r : Rect) (nl : Nat) (u v : Int) :
    (mallat p s r nl).ll.get u v =
      p.getD ((v.toNat - (halfN r nl).y0) * s + (u.toNat - (halfN r nl).x0)) 0 := by
  induction nl generalizing r with
  | zero => rfl
  | succ n ih => simp only [mallat, ih, half_step]

private theorem detail_read (p : Array Int) (s : Nat) (r : Rect) (nl k : Nat) (hk : k < nl) :
    (mallat p s r nl).details[k]? = some (details p s (halfN r k)) := by
  induction nl generalizing r k with
  | zero => omega
  | succ n ih =>
    cases k with
    | zero => rfl
    | succ k =>
      simpa only [mallat, List.getElem?_cons_succ, half_step] using
        ih (halfRect r) k (by omega)

/-- Read the unbounded inverse DWT's own Mallat decomposition at the B-15 address
used by the wide packet assembler. Both offsets use the original full row stride. -/
theorem mallat_read (p : Array Int) (s : Nat) (r : Rect) (nl lvl : Nat)
    (b : Band) (u v : Int) (read : Equiv.ReadBand nl lvl b) (inside : Equiv.InBand r lvl b u v) :
    (Equiv.band53 (mallat p s r nl) lvl b).get u v =
      p.getD ((QuantBlock.my r lvl b v).toNat * s + (QuantBlock.mx r lvl b u).toNat) 0 := by
  rcases read with ⟨rfl, rfl⟩ | ⟨detail, hl, hn⟩
  · simp only [Equiv.band53, ll_read, QuantBlock.mx, QuantBlock.my, Band.xob, Band.yob,
      Nat.zero_ne_one, ↓reduceIte]
    congr 2 <;> first | omega | congr 1 <;> omega
  · obtain ⟨k, rfl⟩ : ∃ k, lvl = k+1 := ⟨lvl-1, by omega⟩
    have hd := detail_read p s r nl k (by omega)
    obtain ⟨x0, y0, x1, y1⟩ := DWTPlane.halfN_coords r k
    cases b <;> first | contradiction | skip
    all_goals
      simp only [Equiv.InBand, bandRect, Band.xob, Band.yob, DWTPlane.bandCoord_high,
        DWTPlane.bandCoord_low, DWTPlane.cdivPow_succ, ← x0, ← x1, ← y0, ← y1] at inside
      simp (config := { decide := true }) only [Equiv.band53, Nat.add_sub_cancel, hd, details,
        QuantBlock.mx, QuantBlock.my, ↓reduceIte, halfN, halfRect,
        Rect.width, Rect.height]
      congr 2 <;> first | omega | congr 1 <;> omega

/-- Wide coefficient assembly gives the independent Annex F decomposition required by lifting. -/
theorem wideBands {r : Rect} {nl F : Nat} {p : JPEG2000.WideQuant.Plane} {es : List Entry}
    (rel : WideAssembly.LoopRel r nl true F p es) :
    Equiv.BandsEq r nl (mallat p.samples.toArray r.width r nl) (dec53 es nl) := by
  intro lvl b u v read inside
  rw [mallat_read _ _ _ _ _ _ _ _ read inside, QuantBlock.band53_dec53 _ _ _ _ read,
    Array.getD_eq_getD_getElem?, WideAssembly.bandGrid53_eq rel _ _ _ _ read inside]
  rfl

/-- A centred source has exactly the reversible specification's cell at each raster index. -/
def Exact (s : Source) (p : Decode.CellPlane) : Prop :=
  s.width = p.width ∧ s.height = p.height ∧ p.cells.size = p.width * p.height ∧
    ∀ j, j < p.width * p.height → s.get? j = (p.cells[j]?).map (·.ival)

private theorem plane_read (p : Plane) (j : Nat) :
    (Source.plane p).get? j = (p.get? j).map Int32.toInt := by
  simp only [Source.get?, Source.width, Source.height, Source.read, Plane.get?]
  by_cases h : j < p.width * p.height <;> simp [h]

private def finN (_ : Bool) (p : Plane) (rect : Rect) (nl sat : Nat) :
    Except Error (Option Plane × Nat) :=
  .ok (if sat = 0 then JPEG2000.DWT53.idwt53Fast p rect nl else none, sat)

private theorem narrow_rel (L : Limits) (data : ByteArray) (tc : TileCompGeom) (depth F red : Nat)
    (ps : Array (Array PrecinctOut)) (rev : tc.params.transform = .reversible53)
    (params : Equiv.ParamsWF tc) (wf : Equiv.PrecsWF tc ps) (ranges : Equiv.BlocksIn data ps) :
    Equiv.ERel (fun a b => ∀ p, a.1 = some p → Exact (.plane p) b.1)
      (narrow L data tc depth F red ps) (Decode.tileComp L tc depth F red (Equiv.imagePrecs data ps)) := by
  have count (pl : Plane) (ok : Bool) (sat : Nat) :
      (pure (ForInStep.yield (pl, if ok then sat else sat + 1)) : Except Error _) =
        (if !ok then pure (ForInStep.yield (pl, sat + 1)) else pure (.yield (pl, sat))) := by
    cases ok <;> rfl
  have stages : narrow L data tc depth F red ps =
      tileCompWith (Plane.zeroChecked L Assemble.loc) (checkedBlock data) JPEG2000.Quant.dequantBlock
        finN tc depth F red ps := by
    simp only [narrow, JPEG2000.WideAssembly.visitBlocks, tileCompWith, finN, count, bind_assoc, pure_bind]
    rfl
  rw [stages]
  rw [Equiv.tileComp_image,
    Equiv.tileCompWith_congr _ (checkedBlock data) (Assemble.decodeBlock data) _ _ _ _ _ _ _
      (fun r prec hp bo hb cb hc _ _ => ite_eq_left (ranges r prec hp bo hb cb hc)),
    Equiv.tileCompWith_congr _ _ (Decode.decodeBlock data) _ _ _ _ _ _ _
      (fun r prec hp bo hb cb hc p b => (Equiv.decodeBlock_eq_st data p r b cb
        (ranges r prec hp bo hb cb hc)).symm)]
  apply QuantBlock.dequantLoopEquiv L _ _ _ _ (Tier1Wire.tier1Equiv data) _ _ _ _ _ _ _ _ params wf
  intro pl es r nl sat m loop
  rw [rev] at loop ⊢
  simp only [BEq.rfl, Equiv.LoopRel, ↓reduceIte] at loop
  obtain ⟨hw, hh, hb⟩ := loop
  change ∀ p, (if sat = 0 then JPEG2000.DWT53.idwt53Fast pl r nl else none) = some p →
    Exact (.plane p) (Decode.idwt true es r nl)
  intro p ok
  split at ok <;> try contradiction
  rename_i zero
  obtain ⟨qw, qh, sample⟩ := DWTPlane.idwt53Fast_bandsEq pl r nl (dec53 es nl) p hw hh
    (by simp [dec53]) ok
  refine ⟨qw, qh, by simp [Decode.idwt], fun j hj => ?_⟩
  change j < r.width * r.height at hj
  obtain ⟨v, hv, eq⟩ := sample (hb zero) j hj
  simp [plane_read, hv, Decode.idwt, hj, Spec.DWT53.memo_eq, Decode.SpecCell.ofRev,
    Equiv.posU, Equiv.posV, eq]

private theorem wide_sound {L : Limits} {r : Rect} {nl F : Nat} {p : JPEG2000.WideQuant.Plane}
    {es : List Entry} {s : Source} (rel : WideAssembly.LoopRel r nl true F p es)
    (ok : wideSource L p nl = .ok s) : Exact s (Decode.idwt true es r nl) := by
  obtain ⟨q, lifting, ok⟩ := Tier2Equiv.bind_ok ok
  split at ok <;> try contradiction
  rename_i size
  cases ok
  have bands := wideBands rel
  rw [← rel.1] at bands ⊢
  refine ⟨rfl, rfl, by simp [Decode.idwt], fun j hj => ?_⟩
  change j < p.rect.width * p.rect.height at hj
  have hw : 0 < p.rect.width := Nat.pos_of_mul_pos_right (Nat.lt_of_le_of_lt (Nat.zero_le _) hj)
  have hx := Nat.mod_lt j hw
  have hy := (Nat.div_lt_iff_lt_mul hw).2 (Nat.mul_comm _ _ ▸ hj)
  have cell := WideReversible.idwt53_of_bandsEq lifting (dec53 es nl) (by simp [dec53])
    bands _ _ hx hy
  rw [Nat.mul_comm (j / _) _, Nat.add_comm, Nat.mod_add_div] at cell
  have hq : j < q.size := size ▸ hj
  simpa [Source.get?, Source.width, Source.height, Source.read, Decode.idwt, hj,
    Spec.DWT53.memo_eq, Decode.SpecCell.ofRev, Array.getD_eq_getD_getElem?, hq] using
    congrArg some cell

private theorem wide_success {L : Limits} {p : JPEG2000.WideQuant.Plane} {nl : Nat}
    (hl : nl ≤ L.maxDecompLevels) (hw : rectArea p.rect ≤ L.maxWorkSamples)
    (ord : p.rect.x0 ≤ p.rect.x1 ∧ p.rect.y0 ≤ p.rect.y1) :
    ∃ s, wideSource L p nl = .ok s := by
  let q := WideReversible.spatial p.rect nl p.samples.toArray
  have lift : JPEG2000.WideReversible.idwt53 L p.rect nl p.samples.toArray = .ok q :=
    (WideReversible.idwt53_spec ..).2 ⟨hl, hw, ⟨ord.1, ord.2, p.samples.size_toArray⟩, rfl⟩
  have size : q.size = p.rect.width * p.rect.height := by
    simp [q, WideReversible.spatial, JPEG2000.WideReversible.raster]
  simp [wideSource, lift, size, bind, Except.bind, pure, Except.pure]

private theorem select_eq {L : Limits} {data : ByteArray} {tc : TileCompGeom} {depth F red : Nat}
    {ps : Array (Array PrecinctOut)} (rev : tc.params.transform = .reversible53) :
    tileComp L data tc depth F red ps =
      match compactPlane? L data tc depth F red ps with
      | some p => .ok (.plane p)
      | none => JPEG2000.WideAssembly.tileComp L data tc depth F red ps >>= fun p =>
          wideSource L p (tc.params.levels - red) := by
  simp only [JPEG2000.ReversibleDispatch.tileComp, rev, bne_self_eq_false, Bool.false_eq_true,
    ↓reduceIte]
  cases compactPlane? L data tc depth F red ps <;> rfl

private theorem compact_hit {L : Limits} {data : ByteArray} {tc : TileCompGeom} {depth F red : Nat}
    {ps : Array (Array PrecinctOut)} {p : Plane}
    (hit : compactPlane? L data tc depth F red ps = some p) :
    ∃ n, narrow L data tc depth F red ps = .ok (some p, n) := by
  unfold compactPlane? at hit
  simp only [guard, bind, Option.bind] at hit
  split at hit <;> try contradiction
  split at hit <;> try contradiction
  cases eq : narrow L data tc depth F red ps with
  | error e => simp [eq, Except.toOption] at hit
  | ok a =>
    obtain ⟨v, n⟩ := a
    simp [eq, Except.toOption] at hit
    exact ⟨n, by rw [hit]⟩

private theorem narrow_ok {L : Limits} {data : ByteArray} {tc : TileCompGeom} {depth F red n : Nat}
    {ps : Array (Array PrecinctOut)} {p : Plane} (rev : tc.params.transform = .reversible53)
    (params : Equiv.ParamsWF tc) (wf : Equiv.PrecsWF tc ps) (ranges : Equiv.BlocksIn data ps)
    (ok : narrow L data tc depth F red ps = .ok (some p, n)) :
    ∃ v, Decode.tileComp L tc depth F red (Equiv.imagePrecs data ps) = .ok v ∧ Exact (.plane p) v.1 := by
  have h := narrow_rel L data tc depth F red ps rev params wf ranges
  rw [ok] at h
  cases ref : Decode.tileComp L tc depth F red (Equiv.imagePrecs data ps) with
  | error e => rw [ref] at h; exact False.elim h
  | ok v => rw [ref] at h; exact ⟨_, rfl, h p rfl⟩

/-- Successful reconstruction agrees with the actual specification component, including
its reduced dimensions and each unbounded centred sample, without a coded-plane bound. -/
theorem tileComp_sound {L : Limits} {data : ByteArray} {tc : TileCompGeom} {depth F red : Nat}
    {ps : Array (Array PrecinctOut)} {s : Source} (rev : tc.params.transform = .reversible53)
    (params : Equiv.ParamsWF tc) (wf : Equiv.PrecsWF tc ps) (ranges : Equiv.BlocksIn data ps)
    (ok : tileComp L data tc depth F red ps = .ok s) :
    ∃ v, Decode.tileComp L tc depth F red (Equiv.imagePrecs data ps) = .ok v ∧ Exact s v.1 := by
  rw [select_eq rev] at ok
  split at ok
  · rename_i p hit
    obtain ⟨_, hit⟩ := compact_hit hit
    cases ok
    exact narrow_ok rev params wf ranges hit
  · obtain ⟨p, assembled, spatial⟩ := Tier2Equiv.bind_ok ok
    obtain ⟨es, collected, rel⟩ := WideAssembly.tileComp_sound wf ranges assembled
    rw [WideAssembly.tileComp_eq_finish, collected, Equiv.ok_bind]
    simp only [rev, BEq.rfl] at rel ⊢
    exact ⟨_, rfl, wide_sound rel spatial⟩

private theorem entries_work {L : Limits} {tc : TileCompGeom} {depth F red : Nat}
    {rs : Decode.SpecPrecs} {v : List Entry × Nat}
    (ok : WideAssembly.entries L tc depth F red rs = .ok v) :
    rectArea (Assemble.reduceRect tc.rect red) ≤ L.maxWorkSamples := by
  unfold WideAssembly.entries at ok
  dsimp only at ok
  split at ok <;> try contradiction
  obtain ⟨_, init, _⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨u, check, _⟩ := Tier2Equiv.bind_ok init
  cases u
  exact (Limits.check_eq_ok_iff ..).1 check

/-- Agreement on success and errors, including the reduced work budget. The plane bound
concerns the retained packet bands' header fields. -/
theorem tileComp_equiv (L : Limits) (data : ByteArray) (tc : TileCompGeom) (depth F red : Nat)
    (ps : Array (Array PrecinctOut)) (rev : tc.params.transform = .reversible53)
    (params : Equiv.ParamsWF tc) (wf : Equiv.PrecsWF tc ps) (ranges : Equiv.BlocksIn data ps)
    (levels : tc.params.levels ≤ L.maxDecompLevels)
    (ordered : let r := Assemble.reduceRect tc.rect red; r.x0 ≤ r.x1 ∧ r.y0 ≤ r.y1)
    (planes : ∀ r b, r ≤ tc.params.levels - red → b ∈ bandsOf r →
      bandMb tc.params r b + tc.params.roiShift ≤ JPEG2000.Tier1.WidePlain.maxCodedPlanes) :
    WideAssembly.ResultRel (fun s v => Exact s v.1) (tileComp L data tc depth F red ps)
      (Decode.tileComp L tc depth F red (Equiv.imagePrecs data ps)) := by
  rw [select_eq rev]
  split
  · rename_i p hit
    obtain ⟨_, hit⟩ := compact_hit hit
    obtain ⟨v, ref, h⟩ := narrow_ok rev params wf ranges hit
    rw [ref]
    exact h
  · have rel := WideAssembly.tileComp_equiv L data tc depth F red ps levels ordered planes wf ranges
    rw [WideAssembly.tileComp_eq_finish]
    cases assembled : JPEG2000.WideAssembly.tileComp L data tc depth F red ps <;>
      cases collected : WideAssembly.entries L tc depth F red (Equiv.imagePrecs data ps) <;>
      rw [assembled, collected] at rel
    · exact rel
    · exact False.elim rel
    · exact False.elim rel
    · obtain ⟨loop, _⟩ := rel
      obtain ⟨s, hs⟩ := wide_success (Nat.le_trans (Nat.sub_le ..) levels)
        (loop.1 ▸ entries_work collected) (loop.1 ▸ ordered)
      rw [Equiv.ok_bind, hs, Equiv.ok_bind]
      simp only [rev, BEq.rfl] at loop ⊢
      exact wide_sound loop hs

private theorem packets_image {L : Limits} {data : ByteArray} {h : Header} {tp : TileParams}
    {hs : Option JPEG2000.Tier2.Headers.HeaderStream} {n : Nat} {store : TileCodeBlocks}
    (parsed : Header.parse L data = .ok h)
    (packets : JPEG2000.Tier2.Headers.decodeWithStream L h data tp hs n = .ok store) (c : Nat) :
    ∃ st, Spec.Tier2.decodeWithStream L h data tp hs n = .ok st ∧
      st.comps.getD c [] = Equiv.imagePrecs data (store.comps.getD c #[]) := by
  have sim := Tier2Equiv.tier2_equiv_of_siz L h data tp hs n (Equiv.parse_dxdy parsed)
  rw [packets] at sim
  cases ref : Spec.Tier2.decodeWithStream L h data tp hs n with
  | error e => rw [ref] at sim; exact False.elim sim
  | ok st => rw [ref] at sim; exact ⟨_, rfl, by rw [sim.1, Equiv.image_getD]⟩

/-- A successful native component equals every centred cell produced by the real spec
packet decoder and its Annex F continuation. Parsing supplies parameter and range validity. -/
theorem parsed_component_ok {L : Limits} {data : ByteArray} {h : Header} {tp : TileParams}
    {hs : Option JPEG2000.Tier2.Headers.HeaderStream} {n : Nat} {store : TileCodeBlocks}
    {g : Progression.Layout} {coding : Coding} {s : Source}
    (parsed : Header.parse L data = .ok h)
    (layout : Progression.Layout.ofHeader h tp.index = .ok (g, coding))
    (packets : JPEG2000.Tier2.Headers.decodeWithStream L h data tp hs n = .ok store)
    (c : Fin g.numComps) (red : Nat) (rev : (g.comp c).params.transform = .reversible53)
    (ok : component L data h.siz g coding (some store) c red = .ok s) :
    ∃ st v, Spec.Tier2.decodeWithStream L h data tp hs n = .ok st ∧
      Decode.tileComp L (g.comp c) (h.siz.components.getD c default).depth.toNat
        (Assemble.fracBitsOf h.siz (coding.mctApplies h.siz) c) red (st.comps.getD c []) = .ok v ∧
      Exact s v.1 := by
  obtain ⟨st, ref, image⟩ := packets_image parsed packets c
  have wf := Tier2WF.tier2WF L h data tp hs n store packets
  have params := (HeaderWF.headerWF L data h parsed tp.index g coding layout).1 c
  obtain ⟨v, ok', exactCells⟩ := tileComp_sound rev params (wf.1 _ _ layout c) (wf.2 c) ok
  exact ⟨st, v, ref, image ▸ ok', exactCells⟩

/-- Two-sided agreement on a parsed tile. The external header bounds are the signalled
guard, ROI shift and step exponents, independent of the magnitudes actually reconstructed. -/
theorem parsed_component {L : Limits} {data : ByteArray} {h : Header} {tp : TileParams}
    {hs : Option JPEG2000.Tier2.Headers.HeaderStream} {n : Nat} {store : TileCodeBlocks}
    {g : Progression.Layout} {coding : Coding}
    (parsed : Header.parse L data = .ok h)
    (layout : Progression.Layout.ofHeader h tp.index = .ok (g, coding))
    (packets : JPEG2000.Tier2.Headers.decodeWithStream L h data tp hs n = .ok store)
    (c : Fin g.numComps) (red : Nat) (rev : (g.comp c).params.transform = .reversible53)
    (levels : (g.comp c).params.levels ≤ L.maxDecompLevels)
    (ordered : let r := Assemble.reduceRect (g.comp c).rect red; r.x0 ≤ r.x1 ∧ r.y0 ≤ r.y1)
    (guard : (g.comp c).params.guardBits ≤ 7) (roi : (g.comp c).params.roiShift ≤ 255)
    (exponents : ∀ s ∈ (g.comp c).params.steps, s.exponent.toNat ≤ 31) :
    ∃ st, Spec.Tier2.decodeWithStream L h data tp hs n = .ok st ∧
      WideAssembly.ResultRel (fun s v => Exact s v.1)
        (component L data h.siz g coding (some store) c red)
        (Decode.tileComp L (g.comp c) (h.siz.components.getD c default).depth.toNat
          (Assemble.fracBitsOf h.siz (coding.mctApplies h.siz) c) red (st.comps.getD c [])) := by
  obtain ⟨st, ref, image⟩ := packets_image parsed packets c
  refine ⟨st, ref, ?_⟩
  rw [image]
  have wf := Tier2WF.tier2WF L h data tp hs n store packets
  apply tileComp_equiv _ _ _ _ _ _ _ rev
    ((HeaderWF.headerWF L data h parsed tp.index g coding layout).1 c)
    (wf.1 _ _ layout c) (wf.2 c) levels ordered
  intro r b _ _
  unfold bandMb
  apply Tier1Wide.codedPlanes_le_of_header _ _ _ 0 guard _ roi
  simp only [Array.getD_eq_getD_getElem?]
  cases step : (g.comp c).params.steps[if r = 0 then 0 else 3 * (r-1) + b.index]? with
  | none => decide
  | some t => exact exponents _ (Array.mem_of_getElem? step)

/-- The three native sources retain their shapes and carry exactly G-6/G-7 at each
common raster index. The integers in the comparison have no machine-range premise. -/
def ColourRel (y cb cr : Source) (q : Source × Source × Source) : Prop :=
  q.1.width = y.width ∧ q.1.height = y.height ∧
  q.2.1.width = cb.width ∧ q.2.1.height = cb.height ∧
  q.2.2.width = cr.width ∧ q.2.2.height = cr.height ∧
  ∀ j, j < y.width * y.height →
    let t := rgbAt y cb cr j
    q.1.get? j = some t.1 ∧ q.2.1.get? j = some t.2.1 ∧ q.2.2.get? j = some t.2.2

private theorem views_rel {y cb cr : Source}
    (h : cb.width = y.width ∧ cb.height = y.height ∧ cr.width = y.width ∧ cr.height = y.height) :
    ColourRel y cb cr (views y cb cr) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun j hj => ?_⟩
  have read (w h : Nat) (f : Fin (w*h) → Int) (hi : j < w*h) :
      (Source.exact w h f).get? j = some (f ⟨j,hi⟩) := dite_eq_left hi
  exact ⟨read _ _ _ hj, read _ _ _ (by rwa [h.1,h.2.1]), read _ _ _ (by rwa [h.2.2.1,h.2.2.2])⟩

private theorem fits_at {y cb cr : Source} {n : Nat} (ok : colourFits y cb cr n = true)
    {j : Nat} (hj : j < n) : fitsRGB (rgbAt y cb cr j) = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    obtain ⟨last, rest⟩ := Bool.and_eq_true_iff.mp ok
    by_cases eq : j = n
    · exact eq ▸ last
    · exact ih rest (by omega)

private theorem map_dims {N : Nat} (a b c : JPEG2000.DWT53.Buf N) (i : Nat) :
    let q := JPEG2000.MCT.map3 JPEG2000.MCT.rctSample a b c i
    q.1.1.width = a.1.width ∧ q.1.1.height = a.1.height ∧
    q.2.1.1.width = b.1.width ∧ q.2.1.1.height = b.1.height ∧
    q.2.2.1.width = c.1.width ∧ q.2.2.1.height = c.1.height := by
  unfold JPEG2000.MCT.map3
  split
  · exact map_dims _ _ _ (i+1)
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
termination_by N - i

private theorem raw_read (p : Plane) (j : Nat) (hj : j < p.width * p.height) :
    p.get? j = some (p.get j hj) := by simp [Plane.get?, hj]

private theorem rct_ok (p0 p1 p2 : Plane)
    (hd : p1.width = p0.width ∧ p1.height = p0.height ∧ p2.width = p0.width ∧ p2.height = p0.height) :
    ∃ q0 q1 q2, JPEG2000.MCT.rctInverse p0 p1 p2 = .ok (q0, q1, q2) ∧
      q0.width = p0.width ∧ q0.height = p0.height ∧ q1.width = p1.width ∧ q1.height = p1.height ∧
      q2.width = p2.width ∧ q2.height = p2.height ∧
      ∀ j, j < p0.width * p0.height → ∃ a b c, p0.get? j = some a ∧ p1.get? j = some b ∧
        p2.get? j = some c ∧ q0.get? j = some (JPEG2000.MCT.rctSample a b c).1 ∧ q1.get? j = some (JPEG2000.MCT.rctSample a b c).2.1 ∧
        q2.get? j = some (JPEG2000.MCT.rctSample a b c).2.2 := by
  unfold JPEG2000.MCT.rctInverse JPEG2000.MCT.apply3
  simp only [hd, and_self, ↓reduceDIte]
  refine ⟨_, _, _, rfl, ?_⟩
  have hdm := map_dims (N := p0.width * p0.height) ⟨p0, rfl⟩ ⟨p1, by rw [hd.1, hd.2.1]⟩
    ⟨p2, by rw [hd.2.2.1, hd.2.2.2]⟩ 0
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := hdm
  refine ⟨d1, d2, d3.trans hd.1, d4.trans hd.2.1, d5.trans hd.2.2.1, d6.trans hd.2.2.2, fun j hj => ?_⟩
  have hg := JPEG2000.MCT.map3_get JPEG2000.MCT.rctSample (N := p0.width * p0.height) ⟨p0, rfl⟩ ⟨p1, by rw [hd.1, hd.2.1]⟩
    ⟨p2, by rw [hd.2.2.1, hd.2.2.2]⟩ 0 j hj
  simp only [Nat.not_lt_zero, ↓reduceIte] at hg
  obtain ⟨g0, g1, g2⟩ := hg
  have hj1 : j < p1.width * p1.height := by rw [hd.1, hd.2.1]; exact hj
  have hj2 : j < p2.width * p2.height := by rw [hd.2.2.1, hd.2.2.2]; exact hj
  refine ⟨_, _, _, raw_read p0 j hj, raw_read p1 j hj1, raw_read p2 j hj2, ?_, ?_, ?_⟩
  · rw [raw_read _ j (by rw [d1, d2]; exact hj)]; exact congrArg some g0
  · rw [raw_read _ j (by rw [d3, d4]; exact hj1)]; exact congrArg some g1
  · rw [raw_read _ j (by rw [d5, d6]; exact hj2)]; exact congrArg some g2

private theorem compact_colour (a b c : Plane)
    (shape : b.width = a.width ∧ b.height = a.height ∧ c.width = a.width ∧ c.height = a.height)
    (fits : colourFits (.plane a) (.plane b) (.plane c) (a.width * a.height) = true) :
    ∃ r g blue, JPEG2000.MCT.rctInverse a b c = .ok (r,g,blue) ∧
      ColourRel (.plane a) (.plane b) (.plane c) (.plane r,.plane g,.plane blue) := by
  obtain ⟨r, g, blue, done_, w0, h0, w1, h1, w2, h2, reads⟩ := rct_ok a b c shape
  refine ⟨r, g, blue, done_, w0, h0, w1, h1, w2, h2, fun j hj => ?_⟩
  obtain ⟨x, y, z, hx, hy, hz, hr, hg, hb⟩ := reads j hj
  let rgb := MCT.rctInv (x.toInt, y.toInt, z.toInt)
  have exactRGB : rgbAt (.plane a) (.plane b) (.plane c) j = rgb := by
    simp [rgbAt, rgb, plane_read, hx, hy, hz]
  have bounds := fits_at fits hj
  rw [exactRGB] at bounds
  simp only [fitsRGB, Bool.and_eq_true, decide_eq_true_eq] at bounds
  obtain ⟨⟨rb, gb⟩, bl⟩ := bounds
  have kernels := JPEG2000.MCT.rctSample_eq x y z
  change _ = JPEG2000.MCT.clamp32 rgb.1 ∧ _ = JPEG2000.MCT.clamp32 rgb.2.1 ∧
    _ = JPEG2000.MCT.clamp32 rgb.2.2 at kernels
  simp only [JPEG2000.MCT.clamp32, MCT.clamp_of_mem _ _ _ rb.1 rb.2,
    MCT.clamp_of_mem _ _ _ gb.1 gb.2, MCT.clamp_of_mem _ _ _ bl.1 bl.2] at kernels
  dsimp only
  simp only [exactRGB, plane_read, hr, hg, hb, Option.map_some, Option.some.injEq]
  exact kernels

/-- The inverse RCT succeeds precisely on equal-sized sources within their aggregate
work limit. Every success retains the full integer triple, including compact-input overflow. -/
theorem colour_spec (L : Limits) (y cb cr : Source) :
    let shape := cb.width = y.width ∧ cb.height = y.height ∧ cr.width = y.width ∧ cr.height = y.height
    let work := y.width * y.height + cb.width * cb.height + cr.width * cr.height ≤ L.maxWorkSamples
    match colour L y cb cr with
    | .error _ => ¬(work ∧ shape)
    | .ok q => work ∧ shape ∧ ColourRel y cb cr q := by
  dsimp only
  unfold colour
  cases budget : L.check (.at .mct) .workSamples _ with
  | error e =>
    intro ⟨hw, _⟩
    rw [(Limits.check_eq_ok_iff ..).2 hw] at budget
    contradiction
  | ok u =>
    cases u
    have hw := (Limits.check_eq_ok_iff ..).1 budget
    simp only [Equiv.ok_bind]
    by_cases shape : cb.width = y.width ∧ cb.height = y.height ∧ cr.width = y.width ∧ cr.height = y.height
    · rw [ite_eq_left shape]
      cases y <;> cases cb <;> cases cr <;> try exact ⟨hw, shape, views_rel shape⟩
      rename_i a b c
      by_cases hf : colourFits (.plane a) (.plane b) (.plane c) (a.width*a.height) = true
      · obtain ⟨r, g, blue, ok, rel⟩ := compact_colour a b c shape hf
        simp only [hf, ↓reduceIte, ok, Equiv.ok_bind]
        exact ⟨hw, shape, rel⟩
      · simp only [hf]
        exact ⟨hw, shape, views_rel shape⟩
    · rw [ite_eq_right shape]
      exact fun h => shape h.2

/-- At a local tile index, inverse colour on three exact component results equals the
spec tile decoder's G.2 cells, including the three actual Annex F inputs. -/
theorem colour_cells {L : Limits} {y cb cr : Source} {q : Source × Source × Source}
    {py pb pr : Decode.CellPlane} (ey : Exact y py) (eb : Exact cb pb) (er : Exact cr pr)
    (ok : colour L y cb cr = .ok q) (j : Nat) (hj : j < py.width * py.height) :
    let t := Decode.rctCells (py.cells.getD j default) (pb.cells.getD j default) (pr.cells.getD j default)
    q.1.get? j = some t.1.ival ∧ q.2.1.get? j = some t.2.1.ival ∧ q.2.2.get? j = some t.2.2.ival := by
  have hc := colour_spec L y cb cr
  rw [ok] at hc
  obtain ⟨_, sh, hc⟩ := hc
  have hy : j < y.width * y.height := by rwa [ey.1, ey.2.1]
  have sample := hc.2.2.2.2.2.2 j hy
  have read {s : Source} {p : Decode.CellPlane} (h : Exact s p) (hi : j < s.width * s.height) :
      (s.get? j).getD 0 = (p.cells.getD j default).ival := by
    rw [h.1, h.2.1] at hi
    rw [h.2.2.2 j hi]
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (h.2.2.1 ▸ hi)]
  simpa only [rgbAt, Decode.rctCells, MCT.rctInv, read ey hy, read eb (by rwa [sh.1, sh.2.1]),
    read er (by rwa [sh.2.2.1, sh.2.2.2])] using sample

/-- The common tile loop may substitute the three centred sources in the specification's
component array. Its actual inverse MCT continuation succeeds and updates exactly those
slots with planes related at every cell. -/
theorem colour_mctSpec {L : Limits} {y cb cr : Source} {q : Source × Source × Source}
    (ps : Array Decode.CellPlane) (ey : Exact y (ps.getD 0 Decode.CellPlane.empty))
    (eb : Exact cb (ps.getD 1 Decode.CellPlane.empty)) (er : Exact cr (ps.getD 2 Decode.CellPlane.empty))
    (ok : colour L y cb cr = .ok q) :
    ∃ r g b, Decode.mctSpec true ps =
      .ok (((ps.setIfInBounds 0 r).setIfInBounds 1 g).setIfInBounds 2 b) ∧
      Exact q.1 r ∧ Exact q.2.1 g ∧ Exact q.2.2 b := by
  let py := ps.getD 0 Decode.CellPlane.empty
  let pb := ps.getD 1 Decode.CellPlane.empty
  let pr := ps.getD 2 Decode.CellPlane.empty
  have checked := colour_spec L y cb cr
  rw [ok] at checked
  obtain ⟨_, shape, rel⟩ := checked
  have dims : pb.width = py.width ∧ pb.height = py.height ∧ pr.width = py.width ∧
      pr.height = py.height := ⟨eb.1.symm.trans (shape.1.trans ey.1),
    eb.2.1.symm.trans (shape.2.1.trans ey.2.1), er.1.symm.trans (shape.2.2.1.trans ey.1),
    er.2.1.symm.trans (shape.2.2.2.trans ey.2.1)⟩
  let triples := Array.ofFn (n := py.width * py.height) fun i =>
    Decode.rctCells (py.cells.getD i default) (pb.cells.getD i default) (pr.cells.getD i default)
  refine ⟨{py with cells := triples.map (·.1)}, {pb with cells := triples.map (·.2.1)},
    {pr with cells := triples.map (·.2.2)}, ?_, ?_, ?_, ?_⟩
  · unfold Decode.mctSpec
    exact ite_eq_left dims
  · refine ⟨rel.1.trans ey.1, rel.2.1.trans ey.2.1, by simp [triples], fun j hj => ?_⟩
    simpa only [triples, Array.getElem?_map, Array.getElem?_ofFn, hj, ↓reduceDIte, Option.map_some] using (colour_cells ey eb er ok j hj).1
  · refine ⟨rel.2.2.1.trans eb.1, rel.2.2.2.1.trans eb.2.1,
      by simp [triples, dims.1, dims.2.1], fun j hj => ?_⟩
    have hi : j < py.width * py.height := by rwa [← dims.1, ← dims.2.1]
    simpa only [triples, Array.getElem?_map, Array.getElem?_ofFn, hi, ↓reduceDIte, Option.map_some] using (colour_cells ey eb er ok j hi).2.1
  · refine ⟨rel.2.2.2.2.1.trans er.1, rel.2.2.2.2.2.1.trans er.2.1,
      by simp [triples, dims.2.2.1, dims.2.2.2], fun j hj => ?_⟩
    have hi : j < py.width * py.height := by rwa [← dims.2.2.1, ← dims.2.2.2]
    simpa only [triples, Array.getElem?_map, Array.getElem?_ofFn, hi, ↓reduceDIte, Option.map_some] using (colour_cells ey eb er ok j hi).2.2

end JPEG2000.Spec.ReversibleDispatch
