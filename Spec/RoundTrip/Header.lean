import Encode.Encode
import Spec.MarkerRoundTrip
import Spec.TilePartRoundTrip

/-!
# C10 layer 3: the encoder's headers parse back (Plan.md §4 C10, §5.3; T.800 A.2–A.6, A.4, I)

Task 7.3c. The reference encoder (`Encode.encodeDetailed`, task 7.2) writes `SOC`, `SIZ`
(A.5.1), `COD` (A.6.1), `QCD` (A.6.4), one tile-part (`SOT`, A.4.2; `SOD`), its packet bytes
and `EOC`. This file proves that the decoder's header parser `Header.parse` (raw codestream
detection of `Box.parseFile`, T.800 Annex I; `Marker.parseMainHeader`; geometry checks;
`mainCoding`; `TilePart.parsePointers`; `TilePart.parseTileParts`; `tileCoding`; `checkWork`)
returns **exactly** the header the encoder intended, stated as functions of the parameters,
the image, the guard bits/exponents the encoder chose and the packet bytes:

* `encodeDetailed_shape`: a successful `encodeDetailed` produces `encCodestream p img G ε data`
  (guard bits `G ≤ 7`, `3·NL + 1` exponents ≤ 31, `Psot < 2^32`);
* `parse_encCodestream` / `parse_encodeDetailed` / `parse_encode`: under `HeaderFits L …`
  (the decoder's `Limits` admit the stream), `Header.parse L bytes = .ok (encHeader …)`:
  `siz = encSIZ img`, `defaults = encCoding` (LRCP, one layer, `encParams` per component), one
  tile (index 0, the whole image, coding `encCoding`) with one tile-part whose data range
  holds exactly the packet bytes (`data_bytes`). The WF facts later layers need follow from
  this equation and the existing theorems about `Header.parse` (e.g. `Spec.HeaderWF`).

Method: the segment round trips of `Spec.MarkerRoundTrip` / `Spec.TilePartRoundTrip`
(`parseSIZ_rd`, `parseCOD_rd`, `parseQCD_rd`, `parseSOT_rd`, `segment_rd`) on the reader
predicate `Rd`, one step lemma per loop iteration (`segmentLoop`, `headerLoop`,
`tilePartLoop`), positions tracked through `Reader.u16be_pos`/`readSegment` and byte-list
lengths; the encoder's do-block is peeled with `bind`/`if … throw` inversion lemmas.
-/

namespace JPEG2000.Spec.RoundTrip

open JPEG2000 JPEG2000.Encode JPEG2000.Marker JPEG2000.Header JPEG2000.Tier2.Geometry
open JPEG2000.Bytes JPEG2000.TilePart JPEG2000.Spec.MarkerRoundTrip JPEG2000.Spec.TilePartRoundTrip
open JPEG2000.Encode.Marker JPEG2000.Encode.TilePart
private theorem bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩
private theorem ite_throw_ok {ε α β : Type} {c : Prop} [Decidable c] {err : ε} {f : α → Except ε β}
    {y : Except ε β} {b : β} (h : (if c then (throw err >>= f) else y) = .ok b) : ¬c ∧ y = .ok b := by
  by_cases hc : c
  · rw [ite_eq_left hc] at h; cases h
  · rw [ite_eq_right hc] at h; exact ⟨hc, h⟩
private theorem ite_ok_throw {ε α β : Type} {c : Prop} [Decidable c] {err : ε} {f : α → Except ε β}
    {y : Except ε β} {b : β} (h : (if c then y else (throw err >>= f)) = .ok b) : c ∧ y = .ok b := by
  by_cases hc : c
  · rw [ite_eq_left hc] at h; exact ⟨hc, h⟩
  · rw [ite_eq_right hc] at h; cases h
private theorem check_ok {β : Type} {L : Limits} {loc k v} {f : Unit → Except Error β} {b : β}
    (h : (L.check loc k v >>= f) = .ok b) : v ≤ L.bound k ∧ f () = .ok b := by
  obtain ⟨u, hu, h⟩ := bind_ok h
  exact ⟨(Limits.checkLe_eq_ok_iff _ _ _ _).mp hu, h⟩

/-- What `Encode.check` guarantees about a successfully encoded image and its parameters (sizes
within `Limits.default`, `NL ≤ 32`, code-block exponents 2…10 summing to ≤ 12, bit depths 1…38). -/
structure EncCheckFacts (p : Params) (img : Image) : Prop where
  width_pos : 0 < img.width
  height_pos : 0 < img.height
  width_le : img.width ≤ 2 ^ 17
  height_le : img.height ≤ 2 ^ 17
  comps_pos : 0 < img.comps.size
  comps_le : img.comps.size ≤ 16384
  levels_le : p.levels ≤ 32
  cbw_ge : 2 ≤ p.cbWidthExp
  cbw_le : p.cbWidthExp ≤ 10
  cbh_ge : 2 ≤ p.cbHeightExp
  cbh_le : p.cbHeightExp ≤ 10
  cb_sum : p.cbWidthExp + p.cbHeightExp ≤ 12
  depth : ∀ c ∈ img.comps.toList, 1 ≤ c.depth ∧ c.depth ≤ 38

private theorem forIn_depth : ∀ (l : List Encode.Component) (f : Encode.Component → Unit → Except Error (ForInStep Unit)),
    (∀ c u r, f c u = .ok r → 1 ≤ c.depth ∧ c.depth ≤ 38 ∧ r = .yield ()) →
    forIn l () f = .ok () → ∀ c ∈ l, 1 ≤ c.depth ∧ c.depth ≤ 38
  | [], _, _, _ => by simp
  | c :: l, f, hf, h => by
    rw [List.forIn_cons] at h
    obtain ⟨r, hr, h⟩ := bind_ok h
    obtain ⟨d1, d2, rfl⟩ := hf c _ r hr
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨d1, d2⟩
    · exact forIn_depth l f hf h x hx

/-- The encoder's argument check passing gives `EncCheckFacts`. -/
theorem checkFacts_of_ok {p : Params} {img : Image} (h : check Limits.default p img = .ok ()) :
    EncCheckFacts p img := by
  unfold check at h
  dsimp only at h
  obtain ⟨h1, h⟩ := ite_throw_ok h
  obtain ⟨h2, h⟩ := check_ok h
  obtain ⟨h3, h⟩ := check_ok h
  obtain ⟨_, h⟩ := check_ok h
  obtain ⟨h5, h⟩ := ite_throw_ok h
  obtain ⟨h6, h⟩ := check_ok h
  obtain ⟨h7, h⟩ := ite_throw_ok h
  obtain ⟨h8, h⟩ := ite_ok_throw h
  obtain ⟨u, hu, _⟩ := bind_ok h
  rw [← Array.forIn_toList] at hu
  have hd := forIn_depth img.comps.toList _ (fun c u r hr => by
    by_cases hc : 1 ≤ c.depth ∧ c.depth ≤ 38
    · refine ⟨hc.1, hc.2, ?_⟩
      rw [ite_eq_left hc] at hr
      split at hr
      · obtain ⟨_, h, _⟩ := bind_ok hr; cases h
      · split at hr
        · cases hr; rfl
        · obtain ⟨_, h, _⟩ := bind_ok hr; cases h
    · rw [ite_eq_right hc] at hr
      obtain ⟨_, h, _⟩ := bind_ok hr; cases h) hu
  simp only [Limits.bound, Limits.default] at h2 h3 h6
  exact ⟨by omega, by omega, by simpa using h2, by simpa using h3, by omega, by simpa using h6,
    by omega, h8.1, h8.2.1, h8.2.2.1, h8.2.2.2.1, h8.2.2.2.2, hd⟩
private theorem flat_size {β : Type} (n : Nat) (f : Nat → Array β) (hf : ∀ r, (f r).size = (bandsOf r).size) :
    ((Array.range (n + 1)).flatMap f).size = 3 * n + 1 := by
  induction n with
  | zero => rw [show Array.range 1 = #[0] from rfl, Array.size_flatMap]; simp [hf, bandsOf]
  | succ n ih => 
    rw [Array.range_succ, Array.flatMap_append, Array.size_append, ih]
    rw [Array.size_flatMap]; simp [hf, bandsOf]; omega
/-- The encoder's band ranges `Rb`: one per sub-band, `3·NL + 1`. -/
theorem ranges_size (p : Params) (img : Image) : (ranges p img).size = 3 * p.levels + 1 :=
  flat_size _ _ (fun r => by simp)
/-- The encoder's per-band magnitudes: one per sub-band, `3·NL + 1`. -/
theorem bandMaxMags_size (bs : Array (Array (Array BandData))) (n : Nat) : (bandMaxMags bs n).size = 3 * n + 1 := flat_size _ _ (fun r => by simp)
private theorem mapM_size {α β ε : Type} (f : α → Except ε β) : ∀ (l : List α) (ys : List β), l.mapM f = .ok ys → ys.length = l.length
  | [], ys, h => by simp [List.mapM_nil] at h; cases h; rfl
  | a :: l, ys, h => by
    rw [List.mapM_cons] at h
    cases hfa : f a with
    | error e => rw [hfa] at h; cases h
    | ok b =>
      rw [hfa] at h
      cases hl : l.mapM f with
      | error e => rw [hl] at h; cases h
      | ok bs => rw [hl] at h; cases h; simp [mapM_size f l bs hl]

/-- The SIZ segment the encoder writes (T.800 A.5.1): one tile covering the image at the origin, no
sub-sampling. -/
def encSIZ (img : Image) : SIZ :=
  { rsiz := 0, xsiz := img.width.toUInt32, ysiz := img.height.toUInt32, xosiz := 0, yosiz := 0,
    xtsiz := img.width.toUInt32, ytsiz := img.height.toUInt32, xtosiz := 0, ytosiz := 0,
    components := img.comps.map fun c =>
      { signed := c.signed, depth := c.depth.toUInt8, dx := 1, dy := 1 } }
/-- The `SPcod` the encoder writes (T.800 A.6.1): `NL` levels, its code-block exponents, plain
code-block style, the 5/3 or 9/7 wavelet, default precincts. -/
def encStyle (p : Params) : CodingStyle :=
  { levels := p.levels.toUInt8, xcb := (p.cbWidthExp - 2).toUInt8,
    ycb := (p.cbHeightExp - 2).toUInt8, cbStyle := 0,
    transform := if p.reversible then .reversible53 else .irreversible97, precincts := none }
/-- Whether the encoder sets the multiple component transform (`SGcod`, G.2): asked for and `Csiz ≥
3`. -/
def encMct (p : Params) (img : Image) : Bool := p.mct && img.comps.size ≥ 3
/-- The COD segment the encoder writes (T.800 A.6.1): no SOP/EPH, LRCP, one layer. -/
def encCOD (p : Params) (img : Image) : COD :=
  { sop := false, eph := false, progression := .lrcp, layers := 1, mct := encMct p img,
    style := encStyle p }
/-- The QCD segment the encoder writes (T.800 A.6.4) for guard bits `guard` and band exponents
`exps`: style 0 (reversible) or style 2 with mantissa 0 (irreversible). -/
def encQCD (p : Params) (guard : Nat) (exps : Array Nat) : QCD :=
  { guardBits := guard.toUInt8,
    quant := if p.reversible then .none (exps.map (·.toUInt8))
             else .expounded (exps.map fun e => { exponent := e.toUInt8, mantissa := 0 }) }
/-- The SOT segment the encoder writes for `n` bytes of packet data (T.800 A.4.2): tile 0, tile-part
0 of 1, `Psot = 14 + n`. -/
def encSOT (n : Nat) : TilePart.SOT := { isot := 0, psot := (12 + 2 + n).toUInt32, tpsot := 0, tnsot := 1 }
/-- The codestream the encoder assembles from its header choices and the packet bytes `data`
(exactly the expression of `Encode.encodeDetailed`): SOC, SIZ, COD, QCD, SOT, SOD, data, EOC. -/
def encCodestream (p : Params) (img : Image) (guard : Nat) (exps : Array Nat) (data : ByteArray) :
    ByteArray :=
  Encode.Marker.pack (Encode.Marker.be16 Code.SOC) ++
    Encode.Marker.segment Code.SIZ (Encode.Marker.serializeSIZ (encSIZ img)) ++
    Encode.Marker.segment Code.COD (Encode.Marker.serializeCOD (encCOD p img)) ++
    Encode.Marker.segment Code.QCD (Encode.Marker.serializeQCD (encQCD p guard exps)) ++
    Encode.Marker.segment Code.SOT (Encode.TilePart.serializeSOT (encSOT data.size)) ++
    Encode.Marker.pack (Encode.Marker.be16 Code.SOD) ++ data ++
    Encode.Marker.pack (Encode.Marker.be16 Code.EOC)

/-- The shape of a successful `encodeDetailed` result: the argument check passed, guard bits ≤ 7 (2
when reversible), `3·NL + 1` band exponents each ≤ 31, `mkComp` accepts the written COD/QCD, and
the codestream is `encCodestream` of some packet bytes `data` with `Psot` representable. -/
structure EncShape (p : Params) (img : Image) (e : Encoded) : Prop where
  check : check Limits.default p img = .ok ()
  guard_le : e.guardBits ≤ 7
  guard_rev : p.reversible = true → e.guardBits = 2
  exps_le : ∀ x ∈ e.exponents.toList, x ≤ 31
  exps_size : e.exponents.size = 3 * p.levels + 1
  mkComp_ok : ∃ params, mkComp 0 (encStyle p) (encQCD p e.guardBits e.exponents) 0 = .ok params
  data : ∃ data : ByteArray, 12 + 2 + data.size < 2 ^ 32 ∧
    e.codestream = encCodestream p img e.guardBits e.exponents data

private theorem map_ok {ε α β : Type} {x : Except ε α} {f : α → β} {b : β}
    (h : (f <$> x) = .ok b) : ∃ a, x = .ok a ∧ f a = b := by
  cases x with
  | error e => cases h
  | ok a => injection h with h; exact ⟨a, rfl, h⟩

/-- **Encoder shape**: every successful `encodeDetailed` has `EncShape`. -/
theorem encodeDetailed_shape {p : Params} {img : Image} {e : Encoded}
    (h : encodeDetailed p img = .ok e) : EncShape p img e := by
  unfold encodeDetailed at h
  dsimp only at h
  obtain ⟨u, hc, h⟩ := bind_ok h
  cases u
  -- both branches reduce to the same tail applied to `(bands, guard, exps)`
  cases hrev : p.reversible
  · rw [hrev, ite_eq_right (by simp)] at h
    obtain ⟨exps, hx, h⟩ := bind_ok h
    rw [pure_bind] at h
    obtain ⟨h31, h⟩ := ite_throw_ok h
    obtain ⟨h7, h⟩ := ite_throw_ok h
    obtain ⟨params, hp, h⟩ := bind_ok h
    obtain ⟨st, hst, h⟩ := bind_ok h
    obtain ⟨hps, h⟩ := ite_throw_ok h
    injection h with h
    subst h
    have hsz : exps.size = 3 * p.levels + 1 := by
      rw [Array.mapM_eq_mapM_toList] at hx
      obtain ⟨ys, hl, hx⟩ := map_ok hx
      subst hx
      simp [mapM_size _ _ _ hl, ranges_size]
    refine ⟨hc, Nat.le_of_not_gt h7, fun h => by simp [hrev] at h, ?_, by simp [hsz], ⟨params, ?_⟩,
      ⟨_, by simp at hps ⊢; omega, ?_⟩⟩
    · intro x hx
      refine Nat.le_of_not_gt fun hgt => h31 ?_
      exact Array.any_eq_true'.mpr ⟨x, Array.mem_toList_iff.mp hx, by simpa using hgt⟩
    · simpa [encStyle, encQCD, hrev] using hp
    · simp [encCodestream, encSIZ, encCOD, encStyle, encQCD, encSOT, encMct, hrev]
  · rw [hrev, ite_eq_left rfl, pure_bind] at h
    obtain ⟨h31, h⟩ := ite_throw_ok h
    obtain ⟨h7, h⟩ := ite_throw_ok h
    obtain ⟨params, hp, h⟩ := bind_ok h
    obtain ⟨st, hst, h⟩ := bind_ok h
    obtain ⟨hps, h⟩ := ite_throw_ok h
    injection h with h
    subst h
    refine ⟨hc, by simp, by simp, ?_, ?_, ⟨params, ?_⟩,
      ⟨_, by simp at hps ⊢; omega, ?_⟩⟩
    · intro x hx
      refine Nat.le_of_not_gt fun hgt => h31 ?_
      exact Array.any_eq_true'.mpr ⟨x, Array.mem_toList_iff.mp hx, by simpa using hgt⟩
    · simp [ranges_size, bandMaxMags_size]
    · simpa [encStyle, encQCD, hrev] using hp
    · simp [encCodestream, encSIZ, encCOD, encStyle, encQCD, encSOT, encMct, hrev]

/-- A whole marker segment as a byte list (T.800 A.1.4): marker, `Lxxx = body + 2`, body. -/
def encSegBytes (code : UInt16) (body : List UInt8) : List UInt8 :=
  be16 code ++ be16 (body.length + 2).toUInt16 ++ body

/-- The main header the encoder writes, as a byte list: SOC, SIZ, COD, QCD. -/
def encMainBytes (p : Params) (img : Image) (guard : Nat) (exps : Array Nat) : List UInt8 :=
  be16 Code.SOC ++ encSegBytes Code.SIZ (sizBytes (encSIZ img)) ++
    encSegBytes Code.COD (codBytes (encCOD p img)) ++ encSegBytes Code.QCD (qcdBytes (encQCD p guard exps))

/-- The rest of the codestream after the main header: SOT segment, SOD, the packet bytes, EOC. -/
def encTailBytes (data : ByteArray) : List UInt8 :=
  encSegBytes Code.SOT (sotBytes (encSOT data.size)) ++ be16 Code.SOD ++ data.data.toList ++ be16 Code.EOC

private theorem segment_pack (code : UInt16) (l : List UInt8) :
    segment code (pack l) = pack (encSegBytes code l) := by
  have : (pack l).size = l.length := by simp [pack, ByteArray.size]
  simp [segment, encSegBytes, this, pack_append]

/-- `encCodestream` is the packed byte list `encMainBytes ++ encTailBytes`. -/
theorem encCodestream_eq (p : Params) (img : Image) (guard : Nat) (exps : Array Nat) (data : ByteArray) :
    encCodestream p img guard exps data = pack (encMainBytes p img guard exps ++ encTailBytes data) := by
  have hd : data = pack data.data.toList := by apply ByteArray.ext; simp [pack]
  rw [encCodestream, serializeSIZ, serializeCOD, serializeQCD, serializeSOT, segment_pack,
    segment_pack, segment_pack, segment_pack, hd]
  simp only [pack_append, encMainBytes, encTailBytes, List.append_assoc]
  rw [← hd]


private theorem readSegment_pos {r sub r2 : Reader} {n : Nat} (h : readSegment r = .ok (sub, n, r2)) :
    r2.pos = r.pos + n ∧ r2.stop = r.stop ∧ r2.data = r.data ∧ r2.stage = r.stage ∧
      sub.pos = r.pos + 2 ∧ sub.data = r.data ∧ sub.stage = r.stage ∧ 2 ≤ n := by
  unfold readSegment at h
  obtain ⟨⟨len, r1⟩, h1, h⟩ := bind_ok h
  obtain ⟨u, hu, h⟩ := bind_ok h
  obtain ⟨⟨s, r3⟩, h3, h⟩ := map_ok h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  have p1 := Reader.u16be_pos h1
  have hl : 2 ≤ len.toNat := by
    simp only [require] at hu; split at hu
    · rename_i hc; simpa [UInt16.le_iff_toNat_le] using hc
    · cases hu
  unfold Reader.take at h3; split at h3
  · cases h3; simp only; refine ⟨by omega, by omega, by simp_all, by simp_all, by omega, by simp_all, by simp_all, hl⟩
  · cases h3

private theorem segLoop_seg (L : Limits) (csiz fuel : Nat) (acc acc' : Acc) (m : UInt16)
    (body rest : List UInt8) (r : Reader) (hb : body.length + 2 < 65536)
    (hm1 : (m == Code.SOT) = false) (hm2 : ¬ m < 0xFF01) (hm3 : ¬(0xFF30 ≤ m ∧ m ≤ 0xFF3F))
    (hm4 : forbiddenInMain m = false) (h : Rd r (encSegBytes m body ++ rest))
    (hadd : ∀ sub : Reader, Rd sub body →
      addSegment L csiz
        { acc with markers := acc.markers.push (⟨m, r.pos, body.length + 4⟩ : MarkerPos) } m sub =
        .ok acc') :
    ∃ r2, segmentLoop L csiz (fuel + 1) acc r = segmentLoop L csiz fuel acc' r2 ∧ Rd r2 rest ∧
      r2.pos = r.pos + (body.length + 4) ∧ r2.stop = r.stop ∧ r2.data = r.data ∧ r2.stage = r.stage := by
  obtain ⟨r1, sub, r2, h1, h2, hs, hr2⟩ := segment_rd m body rest hb r (by simpa [encSegBytes] using h)
  have p1 := Reader.u16be_pos h1
  have p2 := readSegment_pos h2
  refine ⟨r2, ?_, hr2, by omega, by simp_all, by simp_all, by simp_all⟩
  simp only [segmentLoop, h1, h2, hm1, hm2, hm3, hm4, Bool.false_eq_true, ite_false,
    show body.length + 2 + 2 = body.length + 4 by omega, hadd sub hs]

/-- The `MainHeader` the decoder must read from `encMainBytes` placed at offset `base` (marker index
and end position included). -/
def encMain (p : Params) (img : Image) (guard : Nat) (exps : Array Nat) (base : Nat) : MainHeader :=
  let a := (Encode.Marker.sizBytes (encSIZ img)).length + 4
  let b := (Encode.Marker.codBytes (encCOD p img)).length + 4
  let c := (Encode.Marker.qcdBytes (encQCD p guard exps)).length + 4
  { siz := encSIZ img, cod := encCOD p img, coc := #[], qcd := encQCD p guard exps, qcc := #[],
    rgn := #[], poc := #[], com := #[], cap := none, crg := none, pointers := #[], unknown := #[],
    markers := #[⟨Code.SOC, base, 2⟩, ⟨Code.SIZ, base + 2, a⟩, ⟨Code.COD, base + 2 + a, b⟩,
      ⟨Code.QCD, base + 2 + a + b, c⟩],
    endPos := base + 2 + a + b + c }

private theorem segLoop_sot (L : Limits) (csiz fuel : Nat) (acc : Acc) (rest : List UInt8) (r : Reader)
    (h : Rd r (Encode.Marker.be16 Code.SOT ++ rest)) :
    segmentLoop L csiz (fuel + 1) acc r = .ok (acc, r) := by
  obtain ⟨r1, e1, _⟩ := rd_u16 h
  simp [segmentLoop, e1]

/-- **Main-header round trip**: on a reader holding the encoder's main header followed by an SOT
marker, `parseMainHeader` returns exactly `encMain` and stops at the SOT, having consumed
exactly `encMainBytes`. -/
theorem parseMainHeader_enc (L : Limits) (p : Params) (img : Image) (guard : Nat)
    (exps : Array Nat) (hS : WFSIZ L (encSIZ img)) (hC : WFCOD L (encCOD p img))
    (hQ : WFQCD (encQCD p guard exps))
    (h1 : (Encode.Marker.sizBytes (encSIZ img)).length + 2 < 65536)
    (h2 : (Encode.Marker.codBytes (encCOD p img)).length + 2 < 65536)
    (h3 : (Encode.Marker.qcdBytes (encQCD p guard exps)).length + 2 < 65536)
    (r : Reader) (rest : List UInt8)
    (h : Rd r (encMainBytes p img guard exps ++ (Encode.Marker.be16 Code.SOT ++ rest))) :
    ∃ r', parseMainHeader L r = .ok (encMain p img guard exps r.pos, r') ∧
      Rd r' (Encode.Marker.be16 Code.SOT ++ rest) ∧
      r'.pos = r.pos + (encMainBytes p img guard exps).length ∧ r'.stop = r.stop ∧
      r'.data = r.data ∧ r'.stage = r.stage := by
  simp only [encMainBytes, List.append_assoc] at h
  obtain ⟨r1, e1, hr1⟩ := rd_u16 h
  have q1 := Reader.u16be_pos e1
  obtain ⟨r2, sub, r3, e2, e3, hsub, hr3⟩ := segment_rd Code.SIZ _
    (encSegBytes Code.COD (Encode.Marker.codBytes (encCOD p img)) ++
      (encSegBytes Code.QCD (Encode.Marker.qcdBytes (encQCD p guard exps)) ++
        (Encode.Marker.be16 Code.SOT ++ rest))) h1 r1
    (by simpa only [encSegBytes, List.append_assoc] using hr1)
  have q2 := Reader.u16be_pos e2
  have q3 := readSegment_pos e3
  have hsiz := parseSIZ_rd L _ hS sub hsub
  have hrem : ∃ k, r3.remaining = k + 3 := by
    rw [rd_len hr3]; simp [encSegBytes, Encode.Marker.be16]
  obtain ⟨k, hk⟩ := hrem
  let acc0 : Acc := { markers := #[⟨Code.SOC, r.pos, 2⟩,
      ⟨Code.SIZ, r1.pos, (Encode.Marker.sizBytes (encSIZ img)).length + 2 + 2⟩] }
  let mCOD : MarkerPos := ⟨Code.COD, r3.pos, (Encode.Marker.codBytes (encCOD p img)).length + 4⟩
  let acc1 : Acc := { acc0 with cod := some (encCOD p img), markers := acc0.markers.push mCOD }
  obtain ⟨r4, e4, hr4, q4⟩ := segLoop_seg L (encSIZ img).csiz (k + 2) acc0 acc1
    Code.COD _ _ r3 h2 (by decide) (by decide) (by decide) (by decide) hr3
    (fun sub hs => by
      simp [addSegment, parseCOD_rd L _ hC sub hs, require, bind, Except.bind, pure, Except.pure,
        acc0, acc1, mCOD])
  let mQCD : MarkerPos := ⟨Code.QCD, r4.pos, (Encode.Marker.qcdBytes (encQCD p guard exps)).length + 4⟩
  let acc2 : Acc := { acc1 with qcd := some (encQCD p guard exps), markers := acc1.markers.push mQCD }
  obtain ⟨r5, e5, hr5, q5⟩ := segLoop_seg L (encSIZ img).csiz (k + 1) acc1 acc2
    Code.QCD _ _ r4 h3 (by decide) (by decide) (by decide) (by decide) hr4
    (fun sub hs => by
      simp [addSegment, parseQCD_rd _ hQ sub hs, require, bind, Except.bind, pure, Except.pure,
        acc0, acc1, acc2, mQCD, Code.COD, Code.COC, Code.QCD])
  have e6 := segLoop_sot L (encSIZ img).csiz k acc2 rest r5 hr5
  refine ⟨r5, ?_, hr5, ?_, by simp_all, by simp_all, by simp_all⟩
  · simp only [parseMainHeader, e1, e2, e3, hsiz, hk, require, bind, Except.bind, pure, Except.pure,
      beq_self_eq_true, ite_true]
    rw [show k + 3 = k + 2 + 1 from rfl]
    erw [e4]
    rw [show k + 2 = k + 1 + 1 from rfl]
    erw [e5, e6]
    have hp1 : r1.pos = r.pos + 2 := q1.1
    have hp3 : r3.pos = r.pos + 2 + ((Encode.Marker.sizBytes (encSIZ img)).length + 4) := by omega
    have hp4 : r4.pos = r.pos + 2 + ((Encode.Marker.sizBytes (encSIZ img)).length + 4) +
      ((Encode.Marker.codBytes (encCOD p img)).length + 4) := by omega
    have hp5 : r5.pos = r.pos + 2 + ((Encode.Marker.sizBytes (encSIZ img)).length + 4) +
      ((Encode.Marker.codBytes (encCOD p img)).length + 4) +
      ((Encode.Marker.qcdBytes (encQCD p guard exps)).length + 4) := by omega
    simp only [acc2, acc1, acc0, mQCD, mCOD, encMain, hp1, hp3, hp4, hp5]
    rfl
  · simp only [encMainBytes, encSegBytes, List.length_append, Encode.Marker.be16, List.length_cons, List.length_nil]
    omega


/-- The tile-part header the decoder must read for the encoder's single tile-part at offset `base`
with `n` bytes of packet data: no header segments, data range `[base + 14, base + 14 + n)`. -/
def encPart (base n : Nat) : TilePartHeader :=
  { sot := encSOT n, pos := base, segments := #[],
    markers := #[⟨Code.SOT, base, 12⟩, ⟨Code.SOD, base + 12, 2⟩],
    data := { offset := base + 14, length := n } }

/-- The single tile the decoder must assemble from `encPart`. -/
def encTile (base n : Nat) : Tile :=
  { index := 0, parts := #[encPart base n], tnsot := 1, ppt := #[], plt := #[] }

private theorem headerLoop_sod (L : Limits) (csiz : Nat) (first ppm : Bool) (fuel : Nat) (acc : TPAcc)
    (l : List UInt8) (r : Reader) (h : Rd r (Encode.Marker.be16 Code.SOD ++ l)) :
    ∃ r1, headerLoop L csiz first ppm (fuel + 1) acc r =
      .ok ({ acc with markers := acc.markers.push ⟨Code.SOD, r.pos, 2⟩ }, r1) ∧ Rd r1 l ∧
      r1.pos = r.pos + 2 ∧ r1.stop = r.stop ∧ r1.data = r.data := by
  obtain ⟨r1, e1, hr1⟩ := rd_u16 h
  have q1 := Reader.u16be_pos e1
  exact ⟨r1, by simp [headerLoop, e1], hr1, q1.1, q1.2.1, q1.2.2.1⟩

/-- The tile-part loop reads the encoder's single tile-part (SOT, SOD, `n` data bytes) and stops at
EOC. -/
theorem tilePartLoop_enc (c : Ctx) (n fuel : Nat) (st : State) (r : Reader)
    (hn : 12 + 2 + n < 2 ^ 32) (ht : c.numTiles = 1)
    (hst : st.parts = #[#[]]) (htot : st.total = 0) (hfd : st.firstDone = none)
    (hL1 : 1 ≤ c.limits.maxTileParts) (hL2 : 1 ≤ c.limits.maxTilePartsPerTile)
    (l : List UInt8) (hl : l.length = n)
    (h : Rd r (encSegBytes Code.SOT (Encode.TilePart.sotBytes (encSOT n)) ++
      (Encode.Marker.be16 Code.SOD ++ (l ++ Encode.Marker.be16 Code.EOC)))) :
    tilePartLoop c (fuel + 2) st r =
      .ok { parts := #[#[encPart r.pos n]], total := 1, pocEntries := st.pocEntries,
            firstDone := some (0, 1) } := by
  have hpsot : (encSOT n).psot.toNat = 14 + n := by
    simp [encSOT]; omega
  have hwf : WFSOT (encSOT n) := by
    refine ⟨by simp [encSOT], Or.inr ?_, by simp [encSOT], Or.inr (by simp [encSOT])⟩
    exact UInt32.le_iff_toNat_le.mpr (by rw [hpsot]; simp)
  have hlen8 : (Encode.TilePart.sotBytes (encSOT n)).length = 8 := by
    simp [Encode.TilePart.sotBytes, Encode.Marker.be16, Encode.Marker.be32]
  obtain ⟨r1, sub, r2, e1, e2, hsub, hr2⟩ := segment_rd Code.SOT
    (Encode.TilePart.sotBytes (encSOT n)) _ (by rw [hlen8]; decide) r
    (by simpa only [encSegBytes] using h)
  have q1 := Reader.u16be_pos e1
  have q2 := readSegment_pos e2
  have hsot := parseSOT_rd _ hwf sub hsub
  have hstop : r.stop = r.pos + (16 + n) := by
    have := h.1; simp [encSegBytes, hlen8, Encode.Marker.be16, hl] at this; omega
  have hr2' : Rd r2 ((Encode.Marker.be16 Code.SOD ++ l) ++ Encode.Marker.be16 Code.EOC) := by
    simpa only [List.append_assoc] using hr2
  obtain ⟨tp, rN, e3, htp, hrN⟩ := rd_take hr2'
  have q3 := Reader.take_spec e3
  have htl : (Encode.Marker.be16 Code.SOD ++ l).length = 2 + n := by
    simp [Encode.Marker.be16, hl]; omega
  rw [htl] at e3
  have htr : tp.remaining = (1 + n) + 1 := by rw [rd_len htp, htl]; omega
  obtain ⟨rD, e4, hrD, q4⟩ := headerLoop_sod c.limits c.csiz true c.ppm (1 + n)
    { markers := #[⟨Code.SOT, r.pos, 12⟩], pocEntries := st.pocEntries } l tp
    (by simpa only [List.append_assoc] using htp)
  let st' : State := { parts := #[#[encPart r.pos n]], total := 1, pocEntries := st.pocEntries, firstDone := some (0, 1) }
  have eR : readTilePart c st r = .ok (st', rN) := by
    have hi : (encSOT n).isot = 0 := rfl
    have hn1 : (encSOT n).tnsot = 1 := rfl
    have hp0 : (encSOT n).tpsot = 0 := rfl
    have hps0 : (encSOT n).psot ≠ 0 := by
      intro e; have := congrArg UInt32.toNat e; rw [hpsot] at this; simp at this
    have hr2p : r2.pos = r.pos + 12 := by rw [hlen8] at q2; omega
    have hsub2 : r.pos + (14 + n) - r2.pos = 2 + n := by omega
    have hle : r.pos + (14 + n) ≤ r.stop := by omega
    simp [readTilePart, e1, e2, hsot, bind, Except.bind, pure, Except.pure, hi, hn1, hp0,
      hps0, hpsot, ht, hst, htot, require, Limits.check, Limits.checkLe, Limits.bound, hL1, hL2,
      hsub2, hle, e3, htr, hfd, hlen8]
    have hDp : rD.pos = r.pos + 14 := by have := q3.1; have := q4.1; omega
    have hDr : rD.remaining = n := by rw [rd_len hrD, hl]
    have htpp : tp.pos = r.pos + 12 := by have := q3.1; omega
    simp [e4, hDp, hDr, htpp, st', encPart]
  obtain ⟨rE, eE, _⟩ := rd_u16 hrN
  simp [tilePartLoop, e1, eR, eE, Code.SOT, Code.EOC, st']

private theorem insertionSort_empty {α : Type} (f : α → α → Bool) :
    (#[] : Array α).insertionSort f = #[] := rfl

/-- **Tile-part round trip**: `parseTileParts` reads the encoder's tile-part data back as the single
tile `encTile`. -/
theorem parseTileParts_enc (L : Limits) (mh : MainHeader) (n : Nat) (r : Reader)
    (hn : 12 + 2 + n < 2 ^ 32) (ht : numTiles mh.siz = 1)
    (hL0 : 1 ≤ L.maxTiles) (hL1 : 1 ≤ L.maxTileParts) (hL2 : 1 ≤ L.maxTilePartsPerTile)
    (l : List UInt8) (hl : l.length = n)
    (h : Rd r (encSegBytes Code.SOT (Encode.TilePart.sotBytes (encSOT n)) ++
      (Encode.Marker.be16 Code.SOD ++ (l ++ Encode.Marker.be16 Code.EOC)))) :
    parseTileParts L mh r = .ok #[encTile r.pos n] := by
  have hrem : r.remaining = (n + 14) + 2 := by
    rw [rd_len h]; simp [encSegBytes, Encode.TilePart.sotBytes, Encode.Marker.be16, Encode.Marker.be32, hl]
  let c : Ctx := { limits := L, csiz := mh.siz.csiz, numTiles := numTiles mh.siz, ppm := mh.pointers.any (·.code == Code.PPM) }
  let st0 : State := { parts := Array.replicate (numTiles mh.siz) #[], total := 0, pocEntries := mh.poc.foldl (fun a p => a + p.entries.size) 0 }
  have e := tilePartLoop_enc c n (n + 14) st0 r hn ht (by simp [st0, ht]) rfl rfl hL1 hL2 l hl h
  simp only [c, st0, ht, show Array.replicate 1 (#[] : Array TilePartHeader) = #[#[]] from rfl] at e
  simp only [parseTileParts, hrem, bind, Except.bind, Limits.check,
    Limits.checkLe, Limits.bound, ht, hL0]
  simp [e, insertionSort_empty, assembleTiles, tnsotCorrection, assembleTile, sortUnique, firstDup, partPlt, encPart,
    encTile, encSOT, Limits.check, Limits.checkLe, Limits.bound, bind, Except.bind, pure, Except.pure]

/-- The merged `CompParams` the decoder derives from the encoder's COD and QCD (every component). -/
def encParams (p : Params) (guard : Nat) (exps : Array Nat) : CompParams :=
  { levels := p.levels, cbWidthExp := p.cbWidthExp, cbHeightExp := p.cbHeightExp, cbStyle := 0,
    transform := if p.reversible then .reversible53 else .irreversible97,
    precinctsDefined := false, precincts := Array.replicate (p.levels + 1) Precinct.default,
    quantStyle := if p.reversible then 0 else 2, guardBits := guard,
    steps := exps.map fun e => { exponent := e.toUInt8, mantissa := 0 }, roiShift := 0 }

/-- `mkComp` on the encoder's COD style and QCD gives `encParams` (within the encoder's ranges,
`3·NL + 1` exponents). -/
theorem mkComp_enc (pos : Nat) (p : Params) (guard : Nat) (exps : Array Nat)
    (hl : p.levels ≤ 32) (hw1 : 2 ≤ p.cbWidthExp) (hw2 : p.cbWidthExp ≤ 10)
    (hh1 : 2 ≤ p.cbHeightExp) (hh2 : p.cbHeightExp ≤ 10) (hg : guard ≤ 7)
    (hs : exps.size = 3 * p.levels + 1) :
    mkComp pos (encStyle p) (encQCD p guard exps) 0 = .ok (encParams p guard exps) := by
  have e1 : p.levels.toUInt8.toNat = p.levels := by simp; omega
  have e2 : (p.cbWidthExp - 2).toUInt8.toNat + 2 = p.cbWidthExp := by simp; omega
  have e3 : (p.cbHeightExp - 2).toUInt8.toNat + 2 = p.cbHeightExp := by simp; omega
  have e4 : guard.toUInt8.toNat = guard := by simp; omega
  have hpr : ∀ s : CodingStyle, s.precincts = none → (Array.range (p.levels + 1)).map s.precinct =
      Array.replicate (p.levels + 1) Precinct.default := by
    intro s hs
    apply Array.ext
    · simp
    · intro i h1 h2; simp [CodingStyle.precinct, hs]
  cases hr : p.reversible
  · simp [mkComp, bandSteps, encStyle, encQCD, encParams, hr, e1, e4, hs,
      CodingStyle.cbWidthExp, CodingStyle.cbHeightExp, bind, Except.bind, pure, Except.pure]
    refine ⟨by omega, by omega, hpr _ rfl⟩
  · simp [mkComp, bandSteps, encStyle, encQCD, encParams, hr, e1, e4, hs,
      CodingStyle.cbWidthExp, CodingStyle.cbHeightExp, bind, Except.bind, pure, Except.pure]
    refine ⟨by omega, by omega, hpr _ rfl, ?_⟩
    rw [Array.extract_eq_self_of_le (by simp [hs])]
    simp

/-- The encoder's SIZ is well formed for the marker round trip (`MarkerRoundTrip.WFSIZ`). -/
theorem wfSIZ_enc (L : Limits) (p : Params) (img : Image) (hc : EncCheckFacts p img)
    (hL : img.comps.size ≤ L.maxComponents) : WFSIZ L (encSIZ img) := by
  have hw : img.width.toUInt32.toNat = img.width := by
    have := hc.width_le; simp; omega
  have hh : img.height.toUInt32.toNat = img.height := by
    have := hc.height_le; simp; omega
  have := hc.width_pos; have := hc.height_pos; have := hc.comps_le; have := hc.comps_pos
  refine ⟨by simp [SIZ.csiz, encSIZ]; omega, by simp [SIZ.csiz, encSIZ]; omega,
    by simp [SIZ.csiz, encSIZ]; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [encSIZ, UInt32.lt_iff_toNat_lt, hw]; simp; omega
  · simp only [encSIZ, UInt32.lt_iff_toNat_lt, hh]; simp; omega
  · intro e; have := congrArg UInt32.toNat e; simp only [encSIZ, hw] at this; simp at this; omega
  · intro e; have := congrArg UInt32.toNat e; simp only [encSIZ, hh] at this; simp at this; omega
  · simp [encSIZ]
  · simp [encSIZ]
  · simp only [encSIZ, hw]; simp; omega
  · simp only [encSIZ, hh]; simp; omega
  · intro c hcm
    simp only [encSIZ, Array.toList_map, List.mem_map] at hcm
    obtain ⟨c0, hc0, rfl⟩ := hcm
    obtain ⟨d1, d2⟩ := hc.depth c0 hc0
    have e : c0.depth.toUInt8.toNat = c0.depth := by simp; omega
    refine ⟨?_, ?_, by simp, by simp⟩
    · rw [UInt8.le_iff_toNat_le, e]; simpa using d1
    · rw [UInt8.le_iff_toNat_le, e]; simpa using d2

/-- The encoder's COD is well formed for the marker round trip (`MarkerRoundTrip.WFCOD`). -/
theorem wfCOD_enc (L : Limits) (p : Params) (img : Image) (hc : EncCheckFacts p img)
    (hL1 : p.levels ≤ L.maxDecompLevels) (hL2 : 1 ≤ L.maxLayers) : WFCOD L (encCOD p img) := by
  have := hc.levels_le; have := hc.cbw_ge; have := hc.cbw_le; have := hc.cbh_ge
  have := hc.cbh_le; have := hc.cb_sum
  have e1 : p.levels.toUInt8.toNat = p.levels := by simp; omega
  have e2 : (p.cbWidthExp - 2).toUInt8.toNat = p.cbWidthExp - 2 := by simp; omega
  have e3 : (p.cbHeightExp - 2).toUInt8.toNat = p.cbHeightExp - 2 := by simp; omega
  refine ⟨by simp [encCOD], by simpa [encCOD] using hL2, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, by simp [encCOD, encStyle], by simp [encCOD, encStyle], ?_⟩
  · simp only [encCOD, encStyle, UInt8.le_iff_toNat_le, e1]; simp; omega
  · simp only [encCOD, encStyle, e1]; omega
  · simp only [encCOD, encStyle, UInt8.le_iff_toNat_le, e2]; simp; omega
  · simp only [encCOD, encStyle, UInt8.le_iff_toNat_le, e3]; simp; omega
  · simp only [encCOD, encStyle, e2, e3]; omega
  · intro ps h; simp [encCOD, encStyle] at h

/-- The encoder's QCD is well formed for the marker round trip (`MarkerRoundTrip.WFQCD`). -/
theorem wfQCD_enc (p : Params) (guard : Nat) (exps : Array Nat) (hg : guard ≤ 7)
    (hx : ∀ x ∈ exps.toList, x ≤ 31) (hs1 : 1 ≤ exps.size) (hs2 : exps.size ≤ 97) :
    WFQCD (encQCD p guard exps) := by
  have hg' : guard.toUInt8.toNat = guard := by simp; omega
  refine ⟨?_, ?_⟩
  · simp only [encQCD, UInt8.lt_iff_toNat_lt, hg']; simp; omega
  · cases hr : p.reversible
    · simp only [encQCD, hr]
      refine ⟨by simpa using hs1, by simpa [maxBands] using hs2, ?_⟩
      intro s hs
      simp only [Array.toList_map, List.mem_map] at hs
      obtain ⟨e, he, rfl⟩ := hs
      have := hx e he
      refine ⟨?_, by simp⟩
      rw [UInt8.lt_iff_toNat_lt]; simp; omega
    · simp only [encQCD, hr]
      refine ⟨by simpa using hs1, by simpa [maxBands] using hs2, ?_⟩
      intro s hs
      simp only [Array.toList_map, List.mem_map] at hs
      obtain ⟨e, he, rfl⟩ := hs
      have := hx e he
      rw [UInt8.lt_iff_toNat_lt]; simp; omega

/-- The image rectangle `[0, w) × [0, h)`: the tile and every tile-component. -/
def encRect (img : Image) : Rect := { x0 := 0, y0 := 0, x1 := img.width, y1 := img.height }

/-- The decoder's merged coding parameters for the encoder's stream (defaults and the tile's): LRCP,
one layer, `encMct`, no SOP/EPH/POC, `encParams` for every component. -/
def encCoding (p : Params) (img : Image) (guard : Nat) (exps : Array Nat) : Coding :=
  { progression := .lrcp, layers := 1, mct := encMct p img, sop := false, eph := false, poc := #[],
    comps := Array.replicate img.comps.size (encParams p guard exps) }

private theorem mapM_const {α β ε : Type} (f : α → Except ε β) (b : β) (hf : ∀ a, f a = .ok b) :
    ∀ (xs : List α), xs.mapM f = .ok (xs.map fun _ => b)
  | [] => rfl
  | a :: xs => by simp [List.mapM_cons, hf a, mapM_const f b hf xs, bind, Except.bind, pure, Except.pure]

private theorem arrayMapM_const {α β ε : Type} (f : α → Except ε β) (b : β) (hf : ∀ a, f a = .ok b)
    (n : Nat) (xs : Array α) (hn : xs.size = n) : xs.mapM f = .ok (Array.replicate n b) := by
  rw [Array.mapM_eq_mapM_toList, mapM_const f b hf]
  subst hn
  simp only [Functor.map, Except.map]
  congr 1
  apply Array.ext <;> simp

private theorem overrides_empty {α : Type} (pos csiz : Nat) (what : String) :
    overrides (α := α) pos what csiz #[] = .ok (Array.replicate csiz none) := rfl

private theorem encSIZ_csiz (img : Image) : (encSIZ img).csiz = img.comps.size := by
  simp [encSIZ, SIZ.csiz]

private theorem getD_replicate_none {α : Type} (n c : Nat) :
    (Array.replicate n (none : Option α)).getD c none = none := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]; split <;> rfl

private theorem checkPoc_empty (pos csiz : Nat) : checkPoc pos csiz #[] = .ok () := rfl

private theorem checkMct_enc (pos : Nat) (img : Image) (c : Coding) (q : CompParams) (n : Nat)
    (hc : c.comps = Array.replicate n q) : checkMct pos (encSIZ img) c = .ok () := by
  unfold checkMct
  cases c.mct
  · rfl
  · simp only [encSIZ, Array.getElem?_map, hc]
    cases img.comps[0]? <;> cases img.comps[1]? <;> cases img.comps[2]? <;>
      simp [pure, Except.pure]
    generalize hm : min 3 n = m
    have hs : (Array.replicate m q.transform).size = m := by simp
    conv => lhs; arg 4; rw [← hs]
    rw [Array.all_eq_true]
    intro i hi
    have h0 : 0 < m := by simp at hi; omega
    simp [h0]

/-- `mainCoding` of the encoder's main header is `encCoding`. -/
theorem mainCoding_enc (p : Params) (img : Image) (guard : Nat) (exps : Array Nat) (base : Nat)
    (hk : ∀ pos, mkComp pos (encStyle p) (encQCD p guard exps) 0 = .ok (encParams p guard exps)) :
    mainCoding (encMain p img guard exps base) = .ok (encCoding p img guard exps) := by
  simp only [mainCoding, encMain, mkOverrides, overrides_empty, encSIZ_csiz, bind, Except.bind,
    pure, Except.pure, Array.map_empty, getD_replicate_none, Option.getD_none]
  rw [arrayMapM_const _ (encParams p guard exps) (fun _ => by simpa [encCOD] using hk _)
    img.comps.size _ (by simp)]
  simp only [Array.foldl_empty, checkPoc_empty]
  rw [checkMct_enc _ _ _ (encParams p guard exps) img.comps.size rfl]
  simp [encCoding, encCOD]

/-- `tileCoding` of the encoder's tile (no tile-part overrides) is `encCoding`. -/
theorem tileCoding_enc (p : Params) (img : Image) (guard : Nat) (exps : Array Nat) (base base' n : Nat)
    (ov : Overrides) :
    tileCoding (encMain p img guard exps base) ov (encCoding p img guard exps) (encTile base' n) =
      .ok (encCoding p img guard exps) := by
  have hs : tileSegs (encTile base' n) = {} := rfl
  have hz : (encMain p img guard exps base).siz = encSIZ img := rfl
  simp only [tileCoding, hs, hz]
  simp [checkPoc_empty, encCoding, bind, Except.bind, pure, Except.pure]
  rw [checkMct_enc _ _ _ (encParams p guard exps) img.comps.size rfl]
  simp [encMain, encCOD]

private theorem ceilDiv_self (w : Nat) (h : 0 < w) : ceilDiv w w = 1 := by
  unfold ceilDiv
  exact Nat.div_eq_of_lt_le (by omega) (by omega)

/-- The encoder's SIZ declares a single tile. -/
theorem numTiles_enc (img : Image) (hw : img.width ≤ 2 ^ 17) (hh : img.height ≤ 2 ^ 17)
    (hw0 : 0 < img.width) (hh0 : 0 < img.height) :
    numTilesX (encSIZ img) = 1 ∧ numTilesY (encSIZ img) = 1 ∧ numTiles (encSIZ img) = 1 := by
  have e1 : img.width.toUInt32.toNat = img.width := by simp; omega
  have e2 : img.height.toUInt32.toNat = img.height := by simp; omega
  have hx : numTilesX (encSIZ img) = 1 := by
    simp only [numTilesX, encSIZ, e1]; simpa using ceilDiv_self _ hw0
  have hy : numTilesY (encSIZ img) = 1 := by
    simp only [numTilesY, encSIZ, e2]; simpa using ceilDiv_self _ hh0
  exact ⟨hx, hy, by simp [numTiles, hx, hy]⟩

/-- The encoder's single tile covers the image. -/
theorem tileRect_enc (img : Image) (hw : img.width ≤ 2 ^ 17) (hh : img.height ≤ 2 ^ 17)
    (hw0 : 0 < img.width) (hh0 : 0 < img.height) :
    tileRect (encSIZ img) 0 = encRect img := by
  have e1 : img.width.toUInt32.toNat = img.width := by simp; omega
  have e2 : img.height.toUInt32.toNat = img.height := by simp; omega
  have hn := (numTiles_enc img hw hh hw0 hh0).1
  simp only [tileRect, hn]
  simp [encSIZ, encRect, e1, e2]

/-- Code-blocks and precincts of one tile-component of the encoder's stream (`tileCompCounts`). -/
def encCounts (p : Params) (img : Image) (guard : Nat) (exps : Array Nat) : Nat × Nat :=
  tileCompCounts (encRect img) (encParams p guard exps)

private def totK (cb pr k : Nat) : Totals := { codeBlocks := k * cb, precincts := k * pr, packets := k * pr }

private theorem forIn_totK (cb pr N : Nat) (f : Nat → Totals → Except Error (ForInStep Totals))
    (hf : ∀ k, k < N → f k (totK cb pr k) = .ok (.yield (totK cb pr (k + 1)))) :
    ∀ m s, s + m ≤ N → forIn (List.range' s m) (totK cb pr s) f = .ok (totK cb pr (s + m))
  | 0, s, _ => by simp; rfl
  | m + 1, s, h => by
    rw [List.range'_succ, List.forIn_cons, hf s (by omega)]
    simp only [bind, Except.bind]
    rw [forIn_totK cb pr N f hf m (s + 1) (by omega)]
    congr 2; omega

private theorem addTile_enc (L : Limits) (p : Params) (img : Image) (guard : Nat) (exps : Array Nat)
    (hw : img.width ≤ 2 ^ 17) (hh : img.height ≤ 2 ^ 17) (hw0 : 0 < img.width) (hh0 : 0 < img.height)
    (hcb : img.comps.size * (encCounts p img guard exps).1 ≤ L.maxCodeBlocks)
    (hpr : img.comps.size * (encCounts p img guard exps).2 ≤ L.maxPrecincts)
    (hpk : img.comps.size * (encCounts p img guard exps).2 ≤ L.maxPackets) :
    addTile L (encSIZ img) 0 (encCoding p img guard exps) {} =
      .ok (totK (encCounts p img guard exps).1 (encCounts p img guard exps).2 img.comps.size) := by
  unfold addTile
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', tileRect_enc img hw hh hw0 hh0]
  have h0 : ({} : Totals) = totK (encCounts p img guard exps).1 (encCounts p img guard exps).2 0 := by
    simp [totK]
  rw [h0]
  simp only [bind, Except.bind]
  rw [forIn_totK _ _ img.comps.size _ ?_ _ 0 (by simp [Std.Legacy.Range.size, encSIZ_csiz])]
  · simp [Std.Legacy.Range.size, encSIZ_csiz, pure, Except.pure]
  · intro k hk
    have hc1 : compRect (encRect img) ((encSIZ img).components.getD k default) = encRect img := by
      simp [encSIZ, Array.getD_eq_getD_getElem?, hk, compRect, encRect, cdiv]
    have hc2 : (encCoding p img guard exps).comps.getD k default = encParams p guard exps := by
      simp [encCoding, Array.getD_eq_getD_getElem?, hk]
    have hl : (encCoding p img guard exps).layers = 1 := rfl
    have hq : tileCompCounts (encRect img) (encParams p guard exps) = encCounts p img guard exps := rfl
    simp only [hc1, hc2, hl, hq]
    generalize encCounts p img guard exps = q at hcb hpr hpk ⊢
    obtain ⟨cb, pr⟩ := q
    simp only at hcb hpr hpk ⊢
    have m1 : (k + 1) * cb ≤ img.comps.size * cb := Nat.mul_le_mul_right _ hk
    have m2 : (k + 1) * pr ≤ img.comps.size * pr := Nat.mul_le_mul_right _ hk
    simp only [totK, Nat.succ_mul] at m1 m2 ⊢
    have a1 : k * cb + cb ≤ L.maxCodeBlocks := by omega
    have a2 : k * pr + pr ≤ L.maxPrecincts := by omega
    have a3 : k * pr + pr ≤ L.maxPackets := by omega
    simp [Limits.check, Limits.checkLe, Limits.bound, pure, Except.pure, a1, a2, a3]

/-- The work check passes for the encoder's stream within the stated limits. -/
theorem checkWork_enc (L : Limits) (p : Params) (img : Image) (guard : Nat) (exps : Array Nat)
    (hw : img.width ≤ 2 ^ 17) (hh : img.height ≤ 2 ^ 17) (hw0 : 0 < img.width) (hh0 : 0 < img.height)
    (hcb : img.comps.size * (encCounts p img guard exps).1 ≤ L.maxCodeBlocks)
    (hpr : img.comps.size * (encCounts p img guard exps).2 ≤ L.maxPrecincts)
    (hpk : img.comps.size * (encCounts p img guard exps).2 ≤ L.maxPackets)
    (tp : TileParams) (hi : tp.index = 0) (hc : tp.coding = encCoding p img guard exps) :
    ∃ tot, checkWork L (encSIZ img) (encCoding p img guard exps) #[tp] = .ok tot := by
  have hn := (numTiles_enc img hw hh hw0 hh0).2.2
  unfold checkWork
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', hn]
  simp [Std.Legacy.Range.size, hi, hc, addTile_enc L p img guard exps hw hh hw0 hh0 hcb hpr hpk,
    bind, Except.bind, pure, Except.pure]

/-- The `Header` the decoder must return for the encoder's codestream with packet bytes `data`: SIZ,
defaults `encCoding`, one tile (index 0, whole image, `encCoding`, `encTile` at the end of the
main header), no TLM/PPM, main header `encMain`, the whole input as raw codestream. -/
def encHeader (p : Params) (img : Image) (guard : Nat) (exps : Array Nat) (data : ByteArray) :
    Header :=
  { siz := encSIZ img, numTilesX := 1, numTilesY := 1, defaults := encCoding p img guard exps,
    tiles := #[{ index := 0, rect := encRect img, compRects := img.comps.map (fun _ => encRect img),
                 coding := encCoding p img guard exps,
                 tile := encTile (encMainBytes p img guard exps).length data.size }],
    tlm := #[], ppm := {}, main := encMain p img guard exps 0,
    codestream := ⟨0, (encCodestream p img guard exps data).size⟩, container := none }

/-- The decoder's `Limits` admit the encoder's stream of `size` bytes: input size, components,
levels, one layer, image side and area, one tile and tile-part, and the tile-component,
code-block, precinct and packet totals. -/
structure HeaderFits (L : Limits) (p : Params) (img : Image) (guard : Nat) (exps : Array Nat)
    (size : Nat) : Prop where
  inputBytes : size ≤ L.maxInputBytes
  components : img.comps.size ≤ L.maxComponents
  decompLevels : p.levels ≤ L.maxDecompLevels
  layers : 1 ≤ L.maxLayers
  width : img.width ≤ L.maxImageSide
  height : img.height ≤ L.maxImageSide
  area : img.width * img.height ≤ L.maxImageArea
  tiles : 1 ≤ L.maxTiles
  tileParts : 1 ≤ L.maxTileParts
  tilePartsPerTile : 1 ≤ L.maxTilePartsPerTile
  tileComponents : img.comps.size ≤ L.maxCodeBlocks
  codeBlocks : img.comps.size * (encCounts p img guard exps).1 ≤ L.maxCodeBlocks
  precincts : img.comps.size * (encCounts p img guard exps).2 ≤ L.maxPrecincts
  packets : img.comps.size * (encCounts p img guard exps).2 ≤ L.maxPackets

private theorem rd_of {r : JPEG2000.Bytes.Reader} {l : List UInt8} (hd : r.data = Encode.Marker.pack l)
    (hp : r.pos = 0) (hs : r.stop = l.length) : Rd r l := by
  refine ⟨by omega, fun i h => ?_⟩
  simp [hd, hp, Encode.Marker.pack, h]

private theorem rangeReader_all (d : ByteArray) :
    ∃ r, rangeReader d ⟨0, d.size⟩ = .ok r ∧ r.pos = 0 ∧ r.stop = d.size ∧ r.data = d ∧
      r.stage = .marker := by
  simp [rangeReader, JPEG2000.Bytes.Reader.skip, JPEG2000.Bytes.Reader.take,
    JPEG2000.Bytes.Reader.ofByteArray, bind, Except.bind, pure, Except.pure]

/-- `Box.parseFile` recognises a buffer starting with SOC, SIZ as a raw codestream spanning the
whole input. -/
theorem parseFile_raw (L : Limits) (d : ByteArray) (rest : List UInt8)
    (hd : d = Encode.Marker.pack (Encode.Marker.be16 Code.SOC ++ (Encode.Marker.be16 Code.SIZ ++ rest)))
    (hL : d.size ≤ L.maxInputBytes) : Box.parseFile L d = .ok { codestream := ⟨0, d.size⟩ } := by
  have hr : Rd (JPEG2000.Bytes.Reader.ofByteArray d .box) (Encode.Marker.be32 0xFF4FFF51 ++ rest) := by
    rw [hd]
    exact rd_ofByteArray _ _
  obtain ⟨r', e, _⟩ := rd_u32 hr
  have hraw : Box.isRawCodestream d = true := by
    simp [Box.isRawCodestream, e]
  simp [Box.parseFile, Box.parseFileAux, hraw, Limits.check, Limits.checkLe, Limits.bound, hL,
    bind, Except.bind, pure, Except.pure]

/-- **Header round trip for `encCodestream`**: within the encoder's ranges and the decoder's limits,
`Header.parse` returns exactly `encHeader`. -/
theorem parse_encCodestream (L : Limits) (p : Params) (img : Image) (guard : Nat)
    (exps : Array Nat) (data : ByteArray) (hc : EncCheckFacts p img) (hg : guard ≤ 7)
    (hx : ∀ x ∈ exps.toList, x ≤ 31) (hs : exps.size = 3 * p.levels + 1)
    (hn : 12 + 2 + data.size < 2 ^ 32)
    (hL : HeaderFits L p img guard exps (encCodestream p img guard exps data).size) :
    Header.parse L (encCodestream p img guard exps data) = .ok (encHeader p img guard exps data) := by
  have hS := wfSIZ_enc L p img hc hL.components
  have hC := wfCOD_enc L p img hc hL.decompLevels hL.layers
  have hQ := wfQCD_enc p guard exps hg hx (by omega) (by have := hc.levels_le; omega)
  have hk : ∀ pos, mkComp pos (encStyle p) (encQCD p guard exps) 0 = .ok (encParams p guard exps) :=
    fun pos => mkComp_enc pos p guard exps hc.levels_le hc.cbw_ge hc.cbw_le hc.cbh_ge hc.cbh_le hg hs
  have hw := hc.width_le; have hh := hc.height_le; have hw0 := hc.width_pos
  have hh0 := hc.height_pos
  obtain ⟨hnx, hny, hnt⟩ := numTiles_enc img hw hh hw0 hh0
  -- segment lengths
  have l1 : (Encode.Marker.sizBytes (encSIZ img)).length + 2 < 65536 := by
    have := hc.comps_le
    simp [Encode.Marker.sizBytes, Encode.Marker.be16, Encode.Marker.be32, encSIZ,
      Encode.Marker.componentBytes, List.length_flatMap, Function.comp_def, List.map_const',
      List.sum_replicate_nat]
    omega
  have l2 : (Encode.Marker.codBytes (encCOD p img)).length + 2 < 65536 := by
    simp [Encode.Marker.codBytes, Encode.Marker.be16, Encode.Marker.codingStyleBytes, encCOD, encStyle,
      Encode.Marker.precinctBytes]
  have l3 : (Encode.Marker.qcdBytes (encQCD p guard exps)).length + 2 < 65536 := by
    have := hc.levels_le
    cases hr : p.reversible <;>
    simp [Encode.Marker.qcdBytes, Encode.Marker.quantBytes, Encode.Marker.be16, encQCD, hr, hs,
      List.length_flatMap, Function.comp_def, List.map_const', List.sum_replicate_nat] <;> omega
  -- the byte list
  have hb := encCodestream_eq p img guard exps data
  generalize hB : encCodestream p img guard exps data = bytes at hb hL ⊢
  have hlist : encMainBytes p img guard exps ++ encTailBytes data =
      Encode.Marker.be16 Code.SOC ++ (Encode.Marker.be16 Code.SIZ ++
        ((Encode.Marker.be16 (((Encode.Marker.sizBytes (encSIZ img)).length + 2).toUInt16) ++
          Encode.Marker.sizBytes (encSIZ img)) ++
        encSegBytes Code.COD (Encode.Marker.codBytes (encCOD p img)) ++
        encSegBytes Code.QCD (Encode.Marker.qcdBytes (encQCD p guard exps)) ++ encTailBytes data)) := by
    simp only [encMainBytes, encSegBytes, List.append_assoc]
  have hF := parseFile_raw L bytes _ (by rw [hb, hlist]) hL.inputBytes
  obtain ⟨r, er, rp, rs, rd, rst⟩ := rangeReader_all bytes
  have hsz : bytes.size = (encMainBytes p img guard exps ++ encTailBytes data).length := by
    rw [hb]; simp [Encode.Marker.pack, ByteArray.size]
  have hRd : Rd r (encMainBytes p img guard exps ++ (Encode.Marker.be16 Code.SOT ++
      (Encode.Marker.be16 ((Encode.TilePart.sotBytes (encSOT data.size)).length + 2).toUInt16 ++
        Encode.TilePart.sotBytes (encSOT data.size) ++
        (Encode.Marker.be16 Code.SOD ++ (data.data.toList ++ Encode.Marker.be16 Code.EOC))))) := by
    have := rd_of (l := encMainBytes p img guard exps ++ encTailBytes data) (by rw [rd, hb]) rp
      (by rw [rs, hsz])
    simpa only [encTailBytes, encSegBytes, List.append_assoc] using this
  obtain ⟨r', em, hr', rp', rs', rd', rst'⟩ :=
    parseMainHeader_enc L p img guard exps hS hC hQ l1 l2 l3 r _ hRd
  rw [rp] at em rp'
  have hT := parseTileParts_enc L (encMain p img guard exps 0) data.size r' hn hnt
    hL.tiles hL.tileParts hL.tilePartsPerTile data.data.toList (by rw [Array.length_toList]; rfl)
    (by simpa only [encSegBytes, List.append_assoc] using hr')
  rw [rp'] at hT
  simp only [Header.parse, hF, bind, Except.bind]
  have hG : checkGeometry L (encMain p img guard exps 0) = .ok () := by
    have e1 : img.width.toUInt32.toNat = img.width := by simp; omega
    have e2 : img.height.toUInt32.toNat = img.height := by simp; omega
    have hz : (encMain p img guard exps 0).siz = encSIZ img := rfl
    simp only [checkGeometry, hz, hnt, imageRect]
    simp [Rect.width, Rect.height, encSIZ, e1, e2, SIZ.csiz,
      Limits.check, Limits.checkLe, Limits.bound, hL.width, hL.height, hL.area, hL.tiles,
      hL.tileComponents, bind, Except.bind]
  have hP : parsePointers L (encMain p img guard exps 0) bytes = .ok (#[], {}) := by
    simp [parsePointers, encMain, sortUnique, insertionSort_empty, firstDup, ppmChunks, bind,
      Except.bind, pure, Except.pure]
  simp only [parseCodestreamIn, er, em, hG, mainCoding_enc p img guard exps 0 hk, hP, hT,
    bind, Except.bind, pure, Except.pure]
  have hz : (encMain p img guard exps 0).siz = encSIZ img := rfl
  obtain ⟨ov, hov⟩ : ∃ ov, mkOverrides (encMain p img guard exps 0).endPos
      (encMain p img guard exps 0).siz.csiz (encMain p img guard exps 0).coc
      (encMain p img guard exps 0).qcc (encMain p img guard exps 0).rgn = .ok ov := by
    simp [mkOverrides, encMain, overrides_empty, bind, Except.bind, pure, Except.pure]
  have hR := tileRect_enc img hw hh hw0 hh0
  let tp : TileParams := { index := 0, rect := encRect img, compRects := img.comps.map (fun _ => encRect img), coding := encCoding p img guard exps, tile := encTile (encMainBytes p img guard exps).length data.size }
  obtain ⟨tot, hW⟩ := checkWork_enc L p img guard exps hw hh hw0 hh0 hL.codeBlocks hL.precincts
    hL.packets tp rfl rfl
  have hcr : (encSIZ img).components.map (compRect (encRect img)) = img.comps.map (fun _ => encRect img) := by
    simp [encSIZ, compRect, encRect, cdiv]
  rw [hov]
  simp only [hz, Nat.zero_add, Array.mapM_eq_mapM_toList, List.mapM_cons, List.mapM_nil,
    tileCoding_enc, bind, Except.bind, pure, Except.pure]
  have hti : (encTile (encMainBytes p img guard exps).length data.size).index = 0 := rfl
  simp only [tp] at hW
  simp only [hti, hR, hcr, Functor.map, Except.map]
  rw [hW]
  simp [hnx, hny, encHeader, ← hB]

private theorem extract_mid (A D E : List UInt8) :
    (Encode.Marker.pack (A ++ (D ++ E))).extract A.length (A.length + D.length) =
      Encode.Marker.pack D := by
  apply ByteArray.ext
  simp [Encode.Marker.pack, ByteArray.data_extract]

/-- The tile-part data range of `encHeader` holds exactly the packet bytes `data`. -/
theorem data_bytes (p : Params) (img : Image) (guard : Nat) (exps : Array Nat) (data : ByteArray) :
    ({ offset := (encMainBytes p img guard exps).length + 14, length := data.size } : ByteRange).bytes
      (encCodestream p img guard exps data) = data := by
  rw [encCodestream_eq]
  let A := encMainBytes p img guard exps ++ (Encode.Marker.be16 Code.SOT ++ Encode.Marker.be16
      ((Encode.TilePart.sotBytes (encSOT data.size)).length + 2).toUInt16 ++
      Encode.TilePart.sotBytes (encSOT data.size) ++ Encode.Marker.be16 Code.SOD)
  have hA : A.length = (encMainBytes p img guard exps).length + 14 := by
    simp [A, Encode.Marker.be16, Encode.TilePart.sotBytes, Encode.Marker.be32]
  have hD : data.data.toList.length = data.size := by rw [Array.length_toList]; rfl
  have hl : encMainBytes p img guard exps ++ encTailBytes data =
      A ++ (data.data.toList ++ Encode.Marker.be16 Code.EOC) := by
    simp [A, encTailBytes, encSegBytes]
  have hp : Encode.Marker.pack data.data.toList = data := by
    apply ByteArray.ext; simp [Encode.Marker.pack]
  simp only [ByteRange.bytes, ByteRange.stop]
  rw [hl, ← hA, ← hD, extract_mid, hp]

/-- **C10 layer 3** (Plan.md §4 C10): the codestream of a successful `encodeDetailed` parses back
(`Header.parse`, within `HeaderFits`) to exactly `encHeader` — SIZ, default coding/quantisation,
one tile with one tile-part whose data range holds exactly the encoder's packet bytes. -/
theorem parse_encodeDetailed (L : Limits) (p : Params) (img : Image) (e : Encoded)
    (he : encodeDetailed p img = .ok e)
    (hL : HeaderFits L p img e.guardBits e.exponents e.codestream.size) :
    ∃ data : ByteArray,
      e.codestream = encCodestream p img e.guardBits e.exponents data ∧
      Header.parse L e.codestream = .ok (encHeader p img e.guardBits e.exponents data) ∧
      ({ offset := (encMainBytes p img e.guardBits e.exponents).length + 14, length := data.size } :
        ByteRange).bytes e.codestream = data := by
  have hs := encodeDetailed_shape he
  have hc := checkFacts_of_ok hs.check
  obtain ⟨data, hn, hcs⟩ := hs.data
  refine ⟨data, hcs, ?_, by rw [hcs]; exact data_bytes _ _ _ _ _⟩
  rw [hcs] at hL ⊢
  exact parse_encCodestream L p img _ _ data hc hs.guard_le hs.exps_le hs.exps_size hn hL

/-- **C10 layer 3 for `encode`**: the bytes of a successful `encode` are the codestream of some
`encodeDetailed` result `e`, and within `HeaderFits` they parse back to `encHeader` of `e`'s
guard bits and exponents, the tile-part data range holding exactly the packet bytes. -/
theorem parse_encode (L : Limits) (p : Params) (img : Image) (bytes : ByteArray)
    (he : encode p img = .ok bytes) :
    ∃ e : Encoded, encodeDetailed p img = .ok e ∧ bytes = e.codestream ∧
      (HeaderFits L p img e.guardBits e.exponents bytes.size →
        ∃ data : ByteArray,
          bytes = encCodestream p img e.guardBits e.exponents data ∧
          Header.parse L bytes = .ok (encHeader p img e.guardBits e.exponents data) ∧
          ({ offset := (encMainBytes p img e.guardBits e.exponents).length + 14, length := data.size } :
            ByteRange).bytes bytes = data) := by
  obtain ⟨e, he', rfl⟩ := map_ok he
  exact ⟨e, he', rfl, fun hL => parse_encodeDetailed L p img e he' hL⟩

end JPEG2000.Spec.RoundTrip
