import Spec.HeaderWF
import Spec.WideAssembly

/-!
# Effective header bounds for wide packet assembly
Plan.md §§4, 5.1, 5.4, 7. T.800 A.5.1, A.6.1–A.6.6, B.3, B.5 and E.1.

Trace the selected style and quantisation through both levels of marker overrides.
The block bound applies before zero-bit-plane subtraction, including at resolutions
omitted by reduction. The SIZ checks order both axes even for empty component grids.
-/

namespace JPEG2000.Spec.WideHeaderBounds

open JPEG2000.Header JPEG2000.Marker JPEG2000.TilePart JPEG2000.Bytes
open JPEG2000.Tier2.Geometry JPEG2000.Tier2.Packet
open HeaderWF (FieldsRead SegmentRead)
open Tier2Equiv (bind_ok)

/-- Numerical fields of an effective tile-component after COD/COC, QCD/QCC and RGN merge. -/
structure ComponentBounds (L : Limits) (p : CompParams) : Prop where
  /-- The selected coding style passed the caller's decomposition limit. -/
  levels : p.levels ≤ L.maxDecompLevels
  /-- The quantisation guard occupies three bits. -/
  guard : p.guardBits ≤ 7
  /-- The ROI shift was read as one byte, or defaulted to zero. -/
  roi : p.roiShift ≤ 255
  /-- The exponents of the effective sub-band steps fit five bits. -/
  exponents : ∀ st ∈ p.steps, st.exponent.toNat ≤ 31

private theorem style_levels {L : Limits} {defined : Bool} {r r' : Reader} {s : CodingStyle}
    (h : readCodingStyle L defined r = .ok (s, r')) : s.levels.toNat ≤ L.maxDecompLevels := by
  unfold readCodingStyle at h
  obtain ⟨⟨levels, _⟩, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨u, check, h⟩ := bind_ok h
  have bound := (Limits.check_eq_ok_iff L _ .decompLevels levels.toNat).1 check
  obtain ⟨⟨_, _⟩, _, h⟩ := bind_ok h
  obtain ⟨⟨_, _⟩, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨⟨_, _⟩, _, h⟩ := bind_ok h
  dsimp only at h
  split at h
  · contradiction
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨⟨_, _⟩, _, h⟩ := bind_ok h
  dsimp only at h
  split at h <;> try contradiction
  all_goals
    simp only [pure_bind] at h
    cases defined <;> try dsimp only at h
    · cases h; exact bound
    · obtain ⟨⟨_, _⟩, _, h⟩ := bind_ok h
      obtain ⟨_, _, h⟩ := bind_ok h
      cases h; exact bound

private theorem cod_levels {L : Limits} {d : COD} (hd : SegmentRead L (.cod d)) :
    d.style.levels.toNat ≤ L.maxDecompLevels := by
  obtain ⟨_, h⟩ := hd
  unfold parseCOD at h
  obtain ⟨⟨_, _⟩, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨⟨_, _⟩, _, h⟩ := bind_ok h
  dsimp only at h
  split at h <;> try contradiction
  simp only [pure_bind] at h
  obtain ⟨⟨_, _⟩, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨⟨_, _⟩, _, h⟩ := bind_ok h
  try dsimp only at h
  split at h <;> try contradiction
  obtain ⟨⟨_, _⟩, hs, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  cases h; exact style_levels hs

private theorem coc_levels {L : Limits} {d : COC} (hd : SegmentRead L (.coc d)) :
    d.style.levels.toNat ≤ L.maxDecompLevels := by
  obtain ⟨_, _, h⟩ := hd
  unfold parseCOC at h
  obtain ⟨⟨_, _⟩, _, h⟩ := bind_ok h
  obtain ⟨⟨_, _⟩, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨⟨_, _⟩, hs, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  cases h; exact style_levels hs

private def Exponents : Quantization → Prop
  | .none es => ∀ e ∈ es, e.toNat ≤ 31
  | .expounded ss => ∀ s ∈ ss, s.exponent.toNat ≤ 31
  | .derived s => s.exponent.toNat ≤ 31

private def QuantBounds (q : QCD) := q.guardBits.toNat ≤ 7 ∧ Exponents q.quant

private theorem read_exponent {r r' : Reader} {e : UInt8}
    (h : readExponent r = .ok (e, r')) : e.toNat ≤ 31 := by
  unfold readExponent at h
  obtain ⟨⟨b, _⟩, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  cases h
  have := b.toNat_lt
  simp [UInt8.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  omega

private theorem read_step {r r' : Reader} {s : StepSize}
    (h : readStepSize r = .ok (s, r')) : s.exponent.toNat ≤ 31 := by
  unfold readStepSize at h
  obtain ⟨⟨v, _⟩, _, h⟩ := bind_ok h
  cases h
  have := v.toNat_lt
  simp [UInt16.toNat_toUInt8, UInt16.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  omega

private theorem read_quant {r : Reader} {q : QCD} (h : readQuant r = .ok q) : QuantBounds q := by
  unfold readQuant at h
  obtain ⟨⟨s, r1⟩, _, h⟩ := bind_ok h
  have hg : (s >>> 5).toNat ≤ 7 := by
    have := s.toNat_lt
    simp [UInt8.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    omega
  dsimp only at h
  generalize s &&& 0x1F = k at h
  split at h
  · obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨⟨es, _⟩, hes, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    cases h
    exact ⟨hg, HeaderWF.readArray_inv _ _ (fun _ _ _ => read_exponent) _ _ _ _ _ (by simp) hes⟩
  · obtain ⟨⟨_, _⟩, hs, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    cases h; exact ⟨hg, read_step hs⟩
  · obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨⟨ss, _⟩, hss, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    cases h
    exact ⟨hg, HeaderWF.readArray_inv _ _ (fun _ _ _ => read_step) _ _ _ _ _ (by simp) hss⟩
  · cases h

private theorem qcd_bounds {L : Limits} {q : QCD} (hq : SegmentRead L (.qcd q)) : QuantBounds q := by
  obtain ⟨_, h⟩ := hq
  exact read_quant h

private theorem qcc_bounds {L : Limits} {q : QCC} (hq : SegmentRead L (.qcc q)) :
    QuantBounds q.params := by
  obtain ⟨_, _, h⟩ := hq
  unfold parseQCC at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, hq, h⟩ := bind_ok h
  cases h; exact read_quant hq

private theorem band_exponents {pos nl : Nat} {q : Quantization} {ss : Array StepSize}
    (hq : Exponents q) (h : bandSteps pos nl q = .ok ss) : ∀ st ∈ ss, st.exponent.toNat ≤ 31 := by
  unfold bandSteps at h
  dsimp only at h
  split at h <;> split at h <;> try contradiction
  · cases h
    intro st hst
    obtain ⟨e, he, rfl⟩ := Array.mem_map.1 hst
    exact hq e (HeaderWF.mem_extract he)
  · cases h
    intro st hst
    exact hq st (HeaderWF.mem_extract hst)
  · rename_i base admitted
    cases h
    intro st hst
    obtain ⟨i, hi, rfl⟩ := Array.mem_map.1 hst
    have hi' := Array.mem_range.1 hi
    split
    · exact hq
    · have hk : (i - 1) / 3 ≤ base.exponent.toNat := by omega
      have bound : base.exponent.toNat ≤ 31 := hq
      have he : ((i - 1) / 3).toUInt8 ≤ base.exponent := by
        rw [UInt8.le_iff_toNat_le]
        simp [Nat.toUInt8, UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega : (i - 1) / 3 < 256)]
        exact hk
      simp only [UInt8.toNat_sub_of_le _ _ he]
      omega

private theorem mkComp_bounds {L : Limits} {pos roi : Nat} {s : CodingStyle} {q : QCD}
    {p : CompParams} (hs : s.levels.toNat ≤ L.maxDecompLevels) (hq : QuantBounds q)
    (hr : roi ≤ 255) (h : mkComp pos s q roi = .ok p) : ComponentBounds L p := by
  unfold mkComp at h
  obtain ⟨_, steps, h⟩ := bind_ok h
  cases h
  exact ⟨hs, hq.1, hr, band_exponents hq.2 steps⟩

private abbrev AllSome {α : Type} (P : α → Prop) (xs : Array (Option α)) :=
  ∀ o ∈ xs, ∀ v, o = some v → P v

private structure OverrideBounds (L : Limits) (ov : Overrides) : Prop where
  style : AllSome (fun s => s.levels.toNat ≤ L.maxDecompLevels) ov.coc
  quant : AllSome QuantBounds ov.qcc
  roi : AllSome (· ≤ 255) ov.rgn

private theorem overrides_bounds {L : Limits} {pos n : Nat} {ds : Array COC} {qs : Array QCC}
    {rs : Array RGN} {d : Option COD} {q : Option QCD} {ov : Overrides}
    (hf : FieldsRead L d ds q qs) (h : mkOverrides pos n ds qs rs = .ok ov) : OverrideBounds L ov := by
  unfold mkOverrides at h
  obtain ⟨_, hd, h⟩ := bind_ok h
  obtain ⟨_, hq, h⟩ := bind_ok h
  obtain ⟨_, hr, h⟩ := bind_ok h
  cases h
  constructor
  · refine HeaderWF.overrides_inv (fun s : CodingStyle => s.levels.toNat ≤ L.maxDecompLevels) ?_ hd
    intro x hx
    obtain ⟨v, hv, rfl⟩ := Array.mem_map.1 hx
    exact coc_levels (hf.coc v hv)
  · refine HeaderWF.overrides_inv QuantBounds ?_ hq
    intro x hx
    obtain ⟨v, hv, rfl⟩ := Array.mem_map.1 hx
    exact qcc_bounds (hf.qcc v hv)
  · refine HeaderWF.overrides_inv (· ≤ 255) ?_ hr
    intro x hx
    obtain ⟨v, _, rfl⟩ := Array.mem_map.1 hx
    exact Nat.le_of_lt_succ v.shift.toNat_lt

private abbrev MainFields (L : Limits) (mh : MainHeader) :=
  FieldsRead L (some mh.cod) mh.coc (some mh.qcd) mh.qcc

private abbrev CodingBounds (L : Limits) (c : Coding) := ∀ p ∈ c.comps, ComponentBounds L p

private theorem main_bounds {L : Limits} {mh : MainHeader} {c : Coding}
    (hf : MainFields L mh) (h : mainCoding mh = .ok c) : CodingBounds L c := by
  unfold mainCoding at h
  obtain ⟨_, hov, h⟩ := bind_ok h
  obtain ⟨comps, hc, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  cases h
  have ov := overrides_bounds hf hov
  refine HeaderWF.arrayMapM_mem _ _ _ ?_ comps hc
  intro i _ p hp
  exact mkComp_bounds (HeaderWF.getD_getD _ ov.style (cod_levels (hf.cod _ rfl)))
    (HeaderWF.getD_getD _ ov.quant (qcd_bounds (hf.qcd _ rfl)))
    (HeaderWF.getD_getD _ ov.roi (Nat.zero_le _)) hp

private abbrev TileFields (L : Limits) (ts : TileSegs) := FieldsRead L ts.cod ts.coc ts.qcd ts.qcc

private theorem tile_fields {L : Limits} {t : Tile}
    (ht : ∀ p ∈ t.parts, ∀ s ∈ p.segments, SegmentRead L s) : TileFields L (tileSegs t) := by
  unfold tileSegs
  rw [← Array.foldl_toList]
  refine HeaderWF.list_foldl_inv (TileFields L) _ _ ?_ _ (by constructor <;> simp)
  intro p hp acc ha
  rw [← Array.foldl_toList]
  refine HeaderWF.list_foldl_inv (TileFields L) _ _ ?_ _ ha
  intro s hs acc ha
  have read := ht p (Array.mem_def.2 hp) s (Array.mem_def.2 hs)
  cases s with
  | cod d => exact { ha with cod := fun _ e => by cases e; exact read }
  | coc d =>
    refine { ha with coc := ?_ }
    intro x hx
    rcases Array.mem_push.1 hx with hx | rfl
    · exact ha.coc _ hx
    · exact read
  | qcd q => exact { ha with qcd := fun _ e => by cases e; exact read }
  | qcc q =>
    refine { ha with qcc := ?_ }
    intro x hx
    rcases Array.mem_push.1 hx with hx | rfl
    · exact ha.qcc _ hx
    · exact read
  | _ => exact ha

private theorem tile_bounds {L : Limits} {mh : MainHeader} {mainOv : Overrides} {defaults c : Coding}
    {t : Tile} (hm : MainFields L mh) (main : OverrideBounds L mainOv)
    (hd : CodingBounds L defaults) (ht : TileFields L (tileSegs t))
    (h : tileCoding mh mainOv defaults t = .ok c) : CodingBounds L c := by
  unfold tileCoding at h
  dsimp only at h
  obtain ⟨_, _, h⟩ := bind_ok h
  split at h
  · obtain ⟨_, hs, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    cases h; cases hs; exact hd
  · obtain ⟨_, hov, h⟩ := bind_ok h
    obtain ⟨comps, hc, h⟩ := bind_ok h
    obtain ⟨_, hs, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    cases h; cases hs
    have ov := overrides_bounds ht hov
    refine HeaderWF.arrayMapM_mem _ _ _ ?_ comps hc
    intro i _ p hp
    apply mkComp_bounds _ _ _ hp
    · split
      · exact HeaderWF.getD_none (fun s : CodingStyle => s.levels.toNat ≤ L.maxDecompLevels) ov.style (by assumption)
      · exact cod_levels (ht.cod _ (by assumption))
      · exact HeaderWF.getD_getD _ main.style (cod_levels (hm.cod _ rfl))
    · split
      · exact HeaderWF.getD_none _ ov.quant (by assumption)
      · exact qcd_bounds (ht.qcd _ (by assumption))
      · exact HeaderWF.getD_getD _ main.quant (qcd_bounds (hm.qcd _ rfl))
    · split
      · exact HeaderWF.getD_none (· ≤ 255) ov.roi (by assumption)
      · exact HeaderWF.getD_getD _ main.roi (Nat.zero_le _)

private def AxisValid (start offset step stop : Nat) : Prop :=
  start ≤ offset ∧ offset < stop ∧ 0 < step ∧ offset < start + step

private def GridValid (s : SIZ) : Prop :=
  AxisValid s.xtosiz.toNat s.xosiz.toNat s.xtsiz.toNat s.xsiz.toNat ∧
  AxisValid s.ytosiz.toNat s.yosiz.toNat s.ytsiz.toNat s.ysiz.toNat

private theorem required {r : Reader} {test : Bool} {msg : String} {u : Unit}
    (h : Marker.require r test msg = .ok u) : test = true := by
  unfold Marker.require at h
  split at h <;> first | assumption | contradiction

private theorem siz_grid {L : Limits} {r : Reader} {s : SIZ}
    (h : parseSIZ L r = .ok s) : GridValid s := by
  unfold parseSIZ at h
  iterate 10 obtain ⟨⟨_, _⟩, _, h⟩ := bind_ok h
  iterate 3 obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, image, h⟩ := bind_ok h
  obtain ⟨_, size, h⟩ := bind_ok h
  obtain ⟨_, offset, h⟩ := bind_ok h
  obtain ⟨_, first, h⟩ := bind_ok h
  obtain ⟨⟨_, _⟩, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  cases h
  have hi := required image
  have hs := required size
  have ho := required offset
  have hf := required first
  simp only [decide_eq_true_eq, UInt32.lt_iff_toNat_lt,
    UInt32.le_iff_toNat_le, ne_eq, ← UInt32.toNat_inj, UInt32.toNat_zero] at hi hs ho hf
  exact ⟨⟨ho.1, hi.1, Nat.pos_of_ne_zero hs.1, hf.1⟩, ⟨ho.2, hi.2, Nat.pos_of_ne_zero hs.2, hf.2⟩⟩

private theorem axis_order {start offset step stop i : Nat} (valid : AxisValid start offset step stop)
    (hi : i < TilePart.ceilDiv (stop - start) step) :
    max (start + i * step) offset ≤ min (start + (i + 1) * step) stop := by
  obtain ⟨origin, extent, pos, first⟩ := valid
  have whole := (Nat.le_div_iff_mul_le pos).mp (show i + 1 ≤ (stop - start + step - 1) / step from hi)
  rw [Nat.succ_mul] at whole ⊢
  omega

private theorem tile_order {s : SIZ} {t : Nat} (grid : GridValid s) (ht : t < numTiles s) :
    (tileRect s t).x0 ≤ (tileRect s t).x1 ∧ (tileRect s t).y0 ≤ (tileRect s t).y1 := by
  unfold numTiles at ht
  have pos : 0 < numTilesX s := by
    apply Nat.pos_of_ne_zero
    intro hz
    simp [hz] at ht
  simp only [tileRect, ite_eq_right (Nat.ne_of_gt pos)]
  exact ⟨axis_order grid.1 (Nat.mod_lt t pos),
    axis_order grid.2 ((Nat.div_lt_iff_lt_mul pos).2 ((Nat.mul_comm (numTilesX s) (numTilesY s)) ▸ ht))⟩

private theorem parsed_codings {L : Limits} {data : ByteArray} {h : Header}
    (parsed : Header.parse L data = .ok h) :
    GridValid h.siz ∧ CodingBounds L h.defaults ∧ ∀ tp ∈ h.tiles, CodingBounds L tp.coding := by
  unfold Header.parse at parsed
  obtain ⟨_, _, parsed⟩ := bind_ok parsed
  unfold parseCodestreamIn at parsed
  obtain ⟨_, _, parsed⟩ := bind_ok parsed
  obtain ⟨⟨mh, _⟩, hmh, parsed⟩ := bind_ok parsed
  obtain ⟨_, _, parsed⟩ := bind_ok parsed
  obtain ⟨_, hdef, parsed⟩ := bind_ok parsed
  obtain ⟨_, _, parsed⟩ := bind_ok parsed
  obtain ⟨tiles, htiles, parsed⟩ := bind_ok parsed
  obtain ⟨_, hov, parsed⟩ := bind_ok parsed
  obtain ⟨tps, htps, parsed⟩ := bind_ok parsed
  obtain ⟨_, _, parsed⟩ := bind_ok parsed
  cases parsed
  obtain ⟨⟨_, hs⟩, fields⟩ := HeaderWF.parseMainHeader_fields hmh
  have hd := main_bounds fields hdef
  refine ⟨siz_grid hs, hd, HeaderWF.arrayMapM_mem (fun tp => CodingBounds L tp.coding) _ _ ?_ tps htps⟩
  intro t ht tp htp
  obtain ⟨_, hc, htp⟩ := bind_ok htp
  cases htp
  exact tile_bounds fields (overrides_bounds fields hov) hd
    (tile_fields (HeaderWF.parseTileParts_fields htiles t ht)) hc

private theorem cdiv_mono {a b : Nat} (h : a ≤ b) (d : Nat) : cdiv a d ≤ cdiv b d :=
  Nat.div_le_div_right (Nat.sub_le_sub_right (Nat.add_le_add_right h d) 1)

private theorem reduced_order {h : Header} {t c : Nat} {tc : TileCompGeom} (red : Nat)
    (ordered : (tileRect h.siz t).x0 ≤ (tileRect h.siz t).x1 ∧
      (tileRect h.siz t).y0 ≤ (tileRect h.siz t).y1)
    (hg : JPEG2000.Tier2.Geometry.ofHeader h t c = .ok tc) :
    let z := Assemble.reduceRect tc.rect red
    z.x0 ≤ z.x1 ∧ z.y0 ≤ z.y1 := by
  unfold JPEG2000.Tier2.Geometry.ofHeader at hg
  dsimp only at hg
  repeat' split at hg
  all_goals first
    | contradiction
    | (cases hg; exact ⟨cdiv_mono (cdiv_mono ordered.1 _) _, cdiv_mono (cdiv_mono ordered.2 _) _⟩)

/-- Every actual layout component inherits the selected marker bounds. Its B-14 grid
has ordered endpoints at every reduction, including reductions that the decoder rejects. -/
theorem parsed_component_bounds {L : Limits} {data : ByteArray} {h : Header} {t : Nat}
    {g : Progression.Layout} {coding : Coding} (parsed : Header.parse L data = .ok h)
    (layout : Progression.Layout.ofHeader h t = .ok (g, coding)) (c : Fin g.numComps) (red : Nat) :
    ComponentBounds L (g.comp c).params ∧
      let z := Assemble.reduceRect (g.comp c).rect red
      z.x0 ≤ z.x1 ∧ z.y0 ≤ z.y1 := by
  obtain ⟨grid, defaults, tiles⟩ := parsed_codings parsed
  have selected : CodingBounds L (HeaderWF.codingOf h t) := by
    unfold HeaderWF.codingOf
    split
    · exact tiles _ (Array.mem_of_find?_eq_some (by assumption))
    · exact defaults
  unfold Progression.Layout.ofHeader at layout
  dsimp only at layout
  split at layout <;> try contradiction
  rename_i ht
  obtain ⟨comps, hc, layout⟩ := bind_ok layout
  cases layout
  have good := HeaderWF.arrayMapM_mem (fun tc : TileCompGeom =>
    ComponentBounds L tc.params ∧
      let z := Assemble.reduceRect tc.rect red
      z.x0 ≤ z.x1 ∧ z.y0 ≤ z.y1) _ _ (fun _ _ _ hg =>
        ⟨selected _ (Array.mem_of_getElem? (HeaderWF.geom_params hg)),
         reduced_order red (tile_order grid (Nat.lt_of_not_ge ht)) hg⟩) comps hc
  have bound : c.val < comps.size := c.isLt
  simpa only [Progression.Layout.comp, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem bound,
    Option.getD_some] using good _ (Array.getElem_mem bound)

/-- The entire sub-band magnitude budget fits 292 planes before subtracting any
zero bit-planes. This includes scalar-derived quantisation and the full Maxshift byte. -/
theorem ComponentBounds.block_planes {L : Limits} {p : CompParams} (h : ComponentBounds L p)
    (r : Nat) (b : Band) : bandMb p r b + p.roiShift ≤ 292 := by
  unfold bandMb
  let idx := if r = 0 then 0 else 3 * (r - 1) + b.index
  have exp : (p.steps.getD idx default).exponent.toNat ≤ 31 := by
    rw [Array.getD_eq_getD_getElem?]
    cases he : p.steps[idx]? with
    | none => decide
    | some s => exact h.exponents _ (Array.mem_of_getElem? he)
  exact Tier1Wide.codedPlanes_le_of_header _ _ _ 0 h.guard exp h.roi

/-- Wide packet assembly and reference entry collection return the same error, or
both succeed with related band grids and zero saturated blocks. -/
def AssemblyRel (L : Limits) (data : ByteArray) (siz : SIZ) (g : Progression.Layout) (coding : Coding)
    (store : Option TileCodeBlocks) (c : Fin g.numComps) (red : Nat) (precs : Decode.SpecPrecs) : Prop :=
  let tc := g.comp c
  let F := Assemble.fracBitsOf siz (coding.mctApplies siz) c
  WideAssembly.ResultRel (fun pl s => WideAssembly.LoopRel (Assemble.reduceRect tc.rect red)
      (tc.params.levels - red) (tc.params.transform == .reversible53) F pl s.1 ∧ s.2 = 0)
    (JPEG2000.WideAssembly.component L data siz g coding store c red)
    (WideAssembly.entries L tc (siz.components.getD c default).depth.toNat F red precs)

/-- Error and success correspondence for the store actually returned by Tier-2.
Parsing discharges every effective-header premise under the original limits. -/
theorem parsed_component {L : Limits} {data : ByteArray} {h : Header} {tp : TileParams}
    {hs : Option JPEG2000.Tier2.Headers.HeaderStream} {n : Nat} {store : TileCodeBlocks}
    {g : Progression.Layout} {coding : Coding}
    (parsed : Header.parse L data = .ok h)
    (layout : Progression.Layout.ofHeader h tp.index = .ok (g, coding))
    (packets : JPEG2000.Tier2.Headers.decodeWithStream L h data tp hs n = .ok store)
    (c : Fin g.numComps) (red : Nat) :
    ∃ st, Spec.Tier2.decodeWithStream L h data tp hs n = .ok st ∧
      AssemblyRel L data h.siz g coding (some store) c red (st.comps.getD c []) := by
  obtain ⟨bounds, ordered⟩ := parsed_component_bounds parsed layout c red
  exact WideAssembly.parsed_component parsed layout packets c red bounds.levels ordered
    bounds.guard bounds.roi bounds.exponents

/-- An omitted tile contributes empty precincts on both sides. This includes the
reduction and allocation error branches before either traversal reaches a packet. -/
theorem absent_component {L : Limits} {data : ByteArray} {h : Header} {t : Nat}
    {g : Progression.Layout} {coding : Coding} (parsed : Header.parse L data = .ok h)
    (layout : Progression.Layout.ofHeader h t = .ok (g, coding)) (c : Fin g.numComps) (red : Nat) :
    AssemblyRel L data h.siz g coding none c red [] := by
  obtain ⟨bounds, ordered⟩ := parsed_component_bounds parsed layout c red
  apply WideAssembly.tileComp_equiv _ _ _ _ _ _ #[] bounds.levels ordered
    (fun r b _ _ => bounds.block_planes r b)
  · intro r hr
    simp at hr
  · intro r prec hp
    simp [Array.getD_eq_getD_getElem?] at hp

end JPEG2000.Spec.WideHeaderBounds
