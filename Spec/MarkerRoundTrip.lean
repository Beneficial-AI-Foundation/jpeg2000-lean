import JPEG2000.Bytes
import JPEG2000.Marker
import Encode.Marker

/-!
# Marker-segment round trip: `parse (serialise m) = m` (Plan.md §4 M1, §5.1, §5.3; T.800 Annex A)

Task 1.6, the proof half of milestone M1. For every main-header marker segment type of
`JPEG2000.Marker` — SIZ (T.800 A.5.1), COD (A.6.1), COC (A.6.2), RGN (A.6.3), QCD (A.6.4),
QCC (A.6.5), POC (A.6.6), CRG (A.9.1), COM (A.9.2) — a well-formedness predicate `WFX`
capturing what the parser accepts, and the round-trip theorem against the reference
serialiser of `Encode.Marker`:

* `parseX_roundTrip : WFX … m → parseX … (Reader.ofByteArray (serializeX … m) st) = .ok m`
  for every error stage `st`. The parsers consume the whole body and check for trailing
  bytes, so the theorem also says the serialised body is exactly as long as the parser needs.
* `parseX_rd` is the same statement over any reader `r` with `Rd r (xBytes m)` (the reader
  has exactly the body's bytes left), e.g. the sub-reader `readSegment` splits off; with
  `segment_roundTrip` (marker + `Lxxx` framing, T.800 A.1.4) this composes into
  whole-segment round trips (`parseCOD_segment` shows the pattern).

Proof method: the predicate `Rd r l` ("`r` has exactly the bytes `l` left") and one lemma per
reader primitive (`rd_u8`, `rd_u16`, `rd_u32`, `rd_take`, `rd_rest`, `rd_readArray`,
`rd_expectEnd`), then one lemma per field reader. Byte arithmetic goes through `toNat`:
masks `x &&& (2^k − 1)` become `% 2^k`, shifts become division, disjoint `|||` becomes `+`
(`Nat.shiftLeft_add_eq_or_of_lt`), and `omega` closes.
-/

namespace JPEG2000.Spec.MarkerRoundTrip

open JPEG2000 JPEG2000.Bytes JPEG2000.Marker JPEG2000.Encode.Marker

/-! ## Readers holding a known byte list -/

/-- `Rd r l`: the reader `r` has exactly the bytes `l` left (`[pos, stop)` holds `l`). -/
def Rd (r : Reader) (l : List UInt8) : Prop :=
  r.stop = r.pos + l.length ∧ ∀ i (h : i < l.length), r.data.data[r.pos + i]? = some l[i]


private theorem or_shl {a b k : Nat} (hb : b < 2^k) : (a <<< k) ||| b = a * 2^k + b := by
  rw [← Nat.shiftLeft_add_eq_or_of_lt hb, Nat.shiftLeft_eq]

private theorem or_shl2 {a b k j : Nat} (hb : b < 2^k) :
    (a <<< (k+j)) ||| (b <<< j) = (a*2^k + b) <<< j := by
  rw [Nat.shiftLeft_add, ← Nat.shiftLeft_or_distrib, or_shl hb]

/-- Reading back the two bytes of `be16 v` as `Reader.u16be` does gives `v`. -/
theorem be16_val (v : UInt16) :
    ((v >>> 8).toUInt8.toUInt16 <<< 8) ||| v.toUInt8.toUInt16 = v := by
  apply UInt16.toNat_inj.mp
  have h1 : v.toNat < 65536 := v.toNat_lt
  simp only [UInt16.toNat_or, UInt16.toNat_shiftLeft, UInt8.toNat_toUInt16, UInt16.toNat_toUInt8,
    UInt16.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  simp only [show (8 : UInt16).toNat % 16 = 8 from rfl]
  rw [Nat.mod_eq_of_lt (a := _ <<< 8) (by rw [Nat.shiftLeft_eq]; omega), or_shl (by omega)]
  omega

/-- Reading back the four bytes of `be32 v` as `Reader.u32be` does gives `v`. -/
theorem be32_val (v : UInt32) :
    (((v >>> 24).toUInt8.toUInt32 <<< 24) ||| ((v >>> 16).toUInt8.toUInt32 <<< 16)
      ||| ((v >>> 8).toUInt8.toUInt32 <<< 8) ||| v.toUInt8.toUInt32) = v := by
  apply UInt32.toNat_inj.mp
  have h1 : v.toNat < 2^32 := v.toNat_lt
  simp only [UInt32.toNat_or, UInt32.toNat_shiftLeft, UInt8.toNat_toUInt32, UInt32.toNat_toUInt8,
    UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  simp only [show (8 : UInt32).toNat % 32 = 8 from rfl, show (16 : UInt32).toNat % 32 = 16 from rfl,
    show (24 : UInt32).toNat % 32 = 24 from rfl]
  rw [Nat.mod_eq_of_lt (a := _ <<< 8) (by rw [Nat.shiftLeft_eq]; omega),
    Nat.mod_eq_of_lt (a := _ <<< 16) (by rw [Nat.shiftLeft_eq]; omega),
    Nat.mod_eq_of_lt (a := _ <<< 24) (by rw [Nat.shiftLeft_eq]; omega)]
  rw [show (24 : Nat) = 8 + 16 from rfl, or_shl2 (by omega), show (16 : Nat) = 8 + 8 from rfl,
    or_shl2 (by omega), or_shl (by omega)]
  omega

/-- A reader over a packed byte list has exactly that list left. -/
theorem rd_ofByteArray (l : List UInt8) (st : Stage) : Rd (Reader.ofByteArray (pack l) st) l := by
  refine ⟨?_, ?_⟩
  · simp [Reader.ofByteArray, pack, ByteArray.size]
  · intro i h; simp [Reader.ofByteArray, pack, h]

/-- Under `Rd r l`, the byte at `r.pos + k` is `l[k]`. -/
theorem rd_get {r : Reader} {l : List UInt8} (h : Rd r l) (k : Nat) (hk' : k < l.length) (hk) :
    r.data.get (r.pos + k) hk = l[k] := by
  have := h.2 k hk'
  rw [Array.getElem?_eq_some_iff] at this
  obtain ⟨_, h3⟩ := this
  simpa [ByteArray.get] using h3

/-- Advancing a reader by `n` bytes leaves `l.drop n`. -/
theorem rd_adv {r : Reader} {l : List UInt8} (h : Rd r l) (n : Nat) (hn : r.pos + n ≤ r.stop) :
    Rd { r with pos := r.pos + n, pos_le := hn } (l.drop n) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · simp; omega
  · intro i hi
    have := h2 (n + i) (by simp at hi; omega)
    simpa [Nat.add_assoc] using this

/-- Under `Rd r l`, `r.remaining` is the length of `l`. -/
theorem rd_len {r : Reader} {l : List UInt8} (h : Rd r l) : r.remaining = l.length := by
  simp [Reader.remaining, h.1]

/-- `Reader.u8` reads back the first byte. -/
theorem rd_u8 {r : Reader} {b : UInt8} {l : List UInt8} (h : Rd r (b :: l)) :
    ∃ r', r.u8 = .ok (b, r') ∧ Rd r' l := by
  unfold Reader.u8; split
  · rename_i hn
    refine ⟨_, ?_, rd_adv h 1 hn⟩
    have := rd_get h 0 (by simp) (by have := r.stop_le; omega)
    simp only [Nat.add_zero] at this
    simp [this]
  · have := h.1; simp at this; omega

/-- `Reader.u16be` reads back a `be16` value. -/
theorem rd_u16 {r : Reader} {v : UInt16} {l : List UInt8} (h : Rd r (be16 v ++ l)) :
    ∃ r', r.u16be = .ok (v, r') ∧ Rd r' l := by
  unfold Reader.u16be; split
  · rename_i hn
    refine ⟨_, ?_, by simpa [be16] using rd_adv h 2 hn⟩
    have g0 := rd_get h 0 (by simp [be16]) (by have := r.stop_le; omega)
    have g1 := rd_get h 1 (by simp [be16]) (by have := r.stop_le; omega)
    simp only [Nat.add_zero] at g0
    simp only [g0, g1, be16, List.cons_append, List.getElem_cons_zero, List.getElem_cons_succ]
    rw [be16_val]
  · have := h.1; simp [be16] at this; omega

/-- `Reader.u32be` reads back a `be32` value. -/
theorem rd_u32 {r : Reader} {v : UInt32} {l : List UInt8} (h : Rd r (be32 v ++ l)) :
    ∃ r', r.u32be = .ok (v, r') ∧ Rd r' l := by
  unfold Reader.u32be; split
  · rename_i hn
    refine ⟨_, ?_, by simpa [be32] using rd_adv h 4 hn⟩
    have g0 := rd_get h 0 (by simp [be32]) (by have := r.stop_le; omega)
    have g1 := rd_get h 1 (by simp [be32]) (by have := r.stop_le; omega)
    have g2 := rd_get h 2 (by simp [be32]) (by have := r.stop_le; omega)
    have g3 := rd_get h 3 (by simp [be32]) (by have := r.stop_le; omega)
    simp only [Nat.add_zero] at g0
    simp only [g0, g1, g2, g3, be32, List.cons_append, List.getElem_cons_zero,
      List.getElem_cons_succ]
    rw [be32_val]
  · have := h.1; simp [be32] at this; omega

/-- `readArray f` reads back a list of items, each encoded by `enc` and read back by `f`. -/
theorem rd_readArray {α : Type} (f : Reader → Except Error (α × Reader)) (enc : α → List UInt8)
    (P : α → Prop)
    (hf : ∀ x, P x → ∀ r rest, Rd r (enc x ++ rest) → ∃ r', f r = .ok (x, r') ∧ Rd r' rest) :
    ∀ (xs : List α) (acc : Array α) (r : Reader) (rest : List UInt8), (∀ x ∈ xs, P x) →
      Rd r (xs.flatMap enc ++ rest) →
      ∃ r', readArray f acc xs.length r = .ok (acc ++ xs.toArray, r') ∧ Rd r' rest
  | [], acc, r, rest, _, h => ⟨r, by simp [readArray], by simpa using h⟩
  | x :: xs, acc, r, rest, hP, h => by
    obtain ⟨r1, h1, hr1⟩ := hf x (hP x (by simp)) r _ (by simpa [List.append_assoc] using h)
    obtain ⟨r2, h2, hr2⟩ := rd_readArray f enc P hf xs (acc.push x) r1 rest
      (fun y hy => hP y (by simp [hy])) hr1
    exact ⟨r2, by simp [readArray, h1, h2], hr2⟩

/-- `readArray f #[] a.size` reads back an array whose items are encoded by `enc` (the form the parsers use, `Array.mkEmpty n` simplifying to `#[]`). -/
theorem rd_readArray' {α : Type} (f : Reader → Except Error (α × Reader)) (enc : α → List UInt8)
    (P : α → Prop)
    (hf : ∀ x, P x → ∀ r rest, Rd r (enc x ++ rest) → ∃ r', f r = .ok (x, r') ∧ Rd r' rest)
    (a : Array α) (r : Reader) (rest : List UInt8) (hP : ∀ x ∈ a.toList, P x)
    (h : Rd r (a.toList.flatMap enc ++ rest)) :
    ∃ r', readArray f #[] a.size r = .ok (a, r') ∧ Rd r' rest := by
  obtain ⟨r', h1, h2⟩ := rd_readArray f enc P hf a.toList #[] r rest hP h
  refine ⟨r', ?_, h2⟩
  simpa using h1

/-- `expectEnd` succeeds on a reader with nothing left. -/
theorem rd_expectEnd {r : Reader} (h : Rd r []) (w : String) : expectEnd r w = .ok () := by
  have := h.1
  simp [expectEnd, Reader.atEnd, this]

private theorem ssiz_spec (c : Component) (h1 : 1 ≤ c.depth) (h2 : c.depth ≤ 38) :
    c.ssiz &&& 0x7F = c.depth - 1 ∧ decide (c.ssiz ≥ 0x80) = c.signed := by
  have a1 : 1 ≤ c.depth.toNat := h1
  have a2 : c.depth.toNat ≤ 38 := h2
  cases hs : c.signed
  · simp only [Component.ssiz, hs]
    constructor
    · apply UInt8.toNat_inj.mp
      simp only [UInt8.toNat_and, show (0x7F : UInt8).toNat = 2^7 - 1 from rfl,
        Nat.and_two_pow_sub_one_eq_mod, UInt8.toNat_add, UInt8.toNat_sub_of_le _ _ h1]
      simp; omega
    · simp [UInt8.le_iff_toNat_le, UInt8.toNat_sub_of_le _ _ h1]; omega
  · simp only [Component.ssiz, hs]
    constructor
    · apply UInt8.toNat_inj.mp
      simp only [UInt8.toNat_and, show (0x7F : UInt8).toNat = 2^7 - 1 from rfl,
        Nat.and_two_pow_sub_one_eq_mod, UInt8.toNat_add, UInt8.toNat_sub_of_le _ _ h1]
      simp; omega
    · simp [UInt8.le_iff_toNat_le, UInt8.toNat_add, UInt8.toNat_sub_of_le _ _ h1]; omega

/-- A SIZ component the parser accepts: bit depth 1…38 and nonzero sub-sampling. -/
structure WFComponent (c : Component) : Prop where
  depth_pos : 1 ≤ c.depth
  depth_le : c.depth ≤ 38
  dx_ne : c.dx ≠ 0
  dy_ne : c.dy ≠ 0

/-- A SIZ record `parseSIZ L` accepts (T.800 A.5.1): `1 ≤ Csiz ≤ 16384`, `Csiz ≤ L.maxComponents`, the image/tile geometry checks, and well-formed components. -/
structure WFSIZ (L : Limits) (s : SIZ) : Prop where
  csiz_pos : 1 ≤ s.csiz
  csiz_le : s.csiz ≤ 16384
  csiz_limit : s.csiz ≤ L.maxComponents
  xo_lt : s.xosiz < s.xsiz
  yo_lt : s.yosiz < s.ysiz
  xt_ne : s.xtsiz ≠ 0
  yt_ne : s.ytsiz ≠ 0
  xto_le : s.xtosiz ≤ s.xosiz
  yto_le : s.ytosiz ≤ s.yosiz
  x_meet : s.xtosiz.toNat + s.xtsiz.toNat > s.xosiz.toNat
  y_meet : s.ytosiz.toNat + s.ytsiz.toNat > s.yosiz.toNat
  comps : ∀ c ∈ s.components.toList, WFComponent c

private theorem readSizComponent_rd (c : Component) (hc : WFComponent c) (r : Reader) (rest : List UInt8)
    (h : Rd r (componentBytes c ++ rest)) :
    ∃ r', readSizComponent r = .ok (c, r') ∧ Rd r' rest := by
  obtain ⟨r1, h1, hr1⟩ := rd_u8 h
  obtain ⟨r2, h2, hr2⟩ := rd_u8 hr1
  obtain ⟨r3, h3, hr3⟩ := rd_u8 hr2
  obtain ⟨s1, s2⟩ := ssiz_spec c hc.depth_pos hc.depth_le
  have d1 : c.depth - 1 < 38 := by
    have a1 : 1 ≤ c.depth.toNat := hc.depth_pos
    have a2 : c.depth.toNat ≤ 38 := hc.depth_le
    rw [UInt8.lt_iff_toNat_lt, UInt8.toNat_sub_of_le _ _ hc.depth_pos]; simp; omega
  have d2 : c.depth - 1 + 1 = c.depth := by simp
  refine ⟨r3, ?_, hr3⟩
  simp [readSizComponent, h1, h2, h3, require, bind, Except.bind, pure, Except.pure, s1, s2, d1, d2,
    hc.dx_ne, hc.dy_ne]

/-- SIZ round trip on any reader holding exactly the serialised body. -/
theorem parseSIZ_rd (L : Limits) (s : SIZ) (hs : WFSIZ L s) (r : Reader) (h : Rd r (sizBytes s)) :
    parseSIZ L r = .ok s := by
  simp only [sizBytes, List.append_assoc] at h
  obtain ⟨r1, h1, hr1⟩ := rd_u16 h
  obtain ⟨r2, h2, hr2⟩ := rd_u32 hr1
  obtain ⟨r3, h3, hr3⟩ := rd_u32 hr2
  obtain ⟨r4, h4, hr4⟩ := rd_u32 hr3
  obtain ⟨r5, h5, hr5⟩ := rd_u32 hr4
  obtain ⟨r6, h6, hr6⟩ := rd_u32 hr5
  obtain ⟨r7, h7, hr7⟩ := rd_u32 hr6
  obtain ⟨r8, h8, hr8⟩ := rd_u32 hr7
  obtain ⟨r9, h9, hr9⟩ := rd_u32 hr8
  obtain ⟨r10, h10, hr10⟩ := rd_u16 hr9
  obtain ⟨r11, h11, hr11⟩ := rd_readArray' readSizComponent componentBytes WFComponent
    readSizComponent_rd s.components r10 []
    hs.comps (by simpa using hr10)
  have hn : s.components.size.toUInt16.toNat = s.components.size := by
    have := hs.csiz_le; simp [SIZ.csiz] at this; simp; omega
  have hrem : r10.remaining = 3 * s.components.size := by
    rw [rd_len hr10]; simp [List.length_flatMap, componentBytes, List.map_const', List.sum_replicate_nat, Nat.mul_comm]
  have e := rd_expectEnd hr11 "SIZ"
  obtain ⟨c1, c2, c3, x1, y1, x2, y2, x3, y3, x4, y4, _⟩ := hs
  simp only [SIZ.csiz] at c1 c2 c3
  simp [parseSIZ, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, e, hn, hrem, c1, c2, c3, x1, y1, x2, y2, x3, y3, x4, y4, require, bind, Except.bind,
    pure, Except.pure, Limits.check, Limits.checkLe, Limits.bound]

/-- **SIZ round trip** (T.800 A.5.1): `parseSIZ L (serializeSIZ s) = .ok s` for every well-formed `s`. -/
theorem parseSIZ_roundTrip (L : Limits) (s : SIZ) (hs : WFSIZ L s) (st : Stage) :
    parseSIZ L (Reader.ofByteArray (serializeSIZ s) st) = .ok s :=
  parseSIZ_rd L s hs _ (rd_ofByteArray _ _)

/-- A precinct size whose exponents fit in 4 bits. -/
structure WFPrecinct (p : Precinct) : Prop where
  ppx_lt : p.ppx < 16
  ppy_lt : p.ppy < 16

private theorem readPrecinct_rd (p : Precinct) (hp : WFPrecinct p) (r : Reader) (rest : List UInt8)
    (h : Rd r ([p.toUInt8] ++ rest)) :
    ∃ r', readPrecinct r = .ok (p, r') ∧ Rd r' rest := by
  obtain ⟨r1, h1, hr1⟩ := rd_u8 h
  refine ⟨r1, ?_, hr1⟩
  have a1 : p.ppx.toNat < 16 := hp.ppx_lt
  have a2 : p.ppy.toNat < 16 := hp.ppy_lt
  have e1 : p.toUInt8 &&& 0x0F = p.ppx := by
    apply UInt8.toNat_inj.mp
    simp only [UInt8.toNat_and, show (0x0F : UInt8).toNat = 2^4 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, Precinct.toUInt8, UInt8.toNat_add, UInt8.toNat_mul]
    simp; omega
  have e2 : p.toUInt8 >>> 4 = p.ppy := by
    apply UInt8.toNat_inj.mp
    simp only [UInt8.toNat_shiftRight, Nat.shiftRight_eq_div_pow, Precinct.toUInt8,
      UInt8.toNat_add, UInt8.toNat_mul]
    simp; omega
  simp [readPrecinct, h1, e1, e2, bind, Except.bind, pure, Except.pure]

/-- `SPcod`/`SPcoc` values `readCodingStyle L` accepts: levels ≤ 32 and ≤ `L.maxDecompLevels`, `xcb, ycb ≤ 8`, `xcb + ycb ≤ 8`, code-block style bits 6–7 clear, and when precincts are defined, `levels + 1` well-formed sizes, nonzero above resolution 0. -/
structure WFCodingStyle (L : Limits) (s : CodingStyle) : Prop where
  levels_le : s.levels ≤ 32
  levels_limit : s.levels.toNat ≤ L.maxDecompLevels
  xcb_le : s.xcb ≤ 8
  ycb_le : s.ycb ≤ 8
  cb_sum : s.xcb.toNat + s.ycb.toNat ≤ 8
  no_ht : s.cbStyle &&& 0x40 = 0
  no_reserved : s.cbStyle &&& 0x80 = 0
  precincts : ∀ ps, s.precincts = some ps → ps.size = s.levels.toNat + 1 ∧
    (∀ p ∈ ps.toList, WFPrecinct p) ∧ (∀ p ∈ ps.toList.drop 1, p.ppx ≠ 0 ∧ p.ppy ≠ 0)

/-- `readCodingStyle` reads back `SPcod`/`SPcoc`, given the `Scod`/`Scoc` precinct flag. -/
theorem readCodingStyle_rd (L : Limits) (s : CodingStyle) (hs : WFCodingStyle L s) (r : Reader)
    (rest : List UInt8) (h : Rd r (codingStyleBytes s ++ rest)) :
    ∃ r', readCodingStyle L s.precincts.isSome r = .ok (s, r') ∧ Rd r' rest := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := hs
  obtain ⟨levels, xcb, ycb, cbStyle, transform, precincts⟩ := s
  simp only [codingStyleBytes, List.cons_append, List.nil_append] at h
  obtain ⟨r1, h1, hr1⟩ := rd_u8 h
  obtain ⟨r2, h2, hr2⟩ := rd_u8 hr1
  obtain ⟨r3, h3, hr3⟩ := rd_u8 hr2
  obtain ⟨r4, h4, hr4⟩ := rd_u8 hr3
  obtain ⟨r5, h5, hr5⟩ := rd_u8 hr4
  simp only at c1 c2 c3 c4 c5 c6 c7 c8
  have ht : transform.toUInt8 = 0 ∨ transform.toUInt8 = 1 := by cases transform <;> simp [Transform.toUInt8]
  cases precincts with
  | none =>
    refine ⟨r5, ?_, by simpa [precinctBytes] using hr5⟩
    cases transform <;>
    simp [readCodingStyle, h1, h2, h3, h4, h5, c1, c2, c3, c4, c5, c6, c7, require, bind,
      Except.bind, pure, Except.pure, Limits.check, Limits.checkLe, Limits.bound, Transform.toUInt8]
  | some ps =>
    obtain ⟨p1, p2, p3⟩ := c8 ps rfl
    obtain ⟨r6, h6, hr6⟩ := rd_readArray' readPrecinct (fun p => [p.toUInt8]) WFPrecinct
      readPrecinct_rd ps r5 rest p2 (by simpa [precinctBytes] using hr5)
    refine ⟨r6, ?_, hr6⟩
    have p3' : ∀ x ∈ ps.toList.tail, ¬x.ppx = 0 ∧ ¬x.ppy = 0 := by simpa using p3
    have hsz : levels.toNat + 1 = ps.size := p1.symm
    cases transform <;>
    simp [readCodingStyle, h1, h2, h3, h4, h5, hsz, h6, c1, c2, c3, c4, c5, c6, c7, require,
      bind, Except.bind, pure, Except.pure, Limits.check, Limits.checkLe, Limits.bound,
      Transform.toUInt8] <;>
    rw [ite_eq_left_of_eq_true _ _ (eq_true p3')]

/-- `Progression.ofUInt8?` inverts `Progression.toUInt8`. -/
theorem progression_roundTrip (p : Progression) : Progression.ofUInt8? p.toUInt8 = some p := by
  cases p <;> rfl

private theorem scod_spec (c : COD) :
    c.scod &&& 0xF8 = 0 ∧ decide (c.scod &&& 1 ≠ 0) = c.style.precincts.isSome ∧
      decide (c.scod &&& 2 ≠ 0) = c.sop ∧ decide (c.scod &&& 4 ≠ 0) = c.eph := by
  unfold COD.scod
  cases c.sop <;> cases c.eph <;> cases c.style.precincts.isSome <;> decide

/-- A COD record `parseCOD L` accepts (T.800 A.6.1): layers 1…`L.maxLayers` and a well-formed coding style. -/
structure WFCOD (L : Limits) (c : COD) : Prop where
  layers_ne : c.layers ≠ 0
  layers_limit : c.layers.toNat ≤ L.maxLayers
  style : WFCodingStyle L c.style

/-- COD round trip on any reader holding exactly the serialised body. -/
theorem parseCOD_rd (L : Limits) (c : COD) (hc : WFCOD L c) (r : Reader) (h : Rd r (codBytes c)) :
    parseCOD L r = .ok c := by
  rw [← List.append_nil (codBytes c)] at h
  simp only [codBytes, List.cons_append, List.nil_append, List.append_assoc] at h
  obtain ⟨r1, h1, hr1⟩ := rd_u8 h
  obtain ⟨r2, h2, hr2⟩ := rd_u8 hr1
  obtain ⟨r3, h3, hr3⟩ := rd_u16 hr2
  obtain ⟨r4, h4, hr4⟩ := rd_u8 hr3
  obtain ⟨r5, h5, hr5⟩ := readCodingStyle_rd L c.style hc.style r4 [] hr4
  have e := rd_expectEnd hr5 "COD"
  obtain ⟨s1, s2, s3, s4⟩ := scod_spec c
  obtain ⟨l1, l2, _⟩ := hc
  obtain ⟨sop, eph, progression, layers, mct, style⟩ := c
  simp only at s1 s2 s3 s4 l1 l2 h1 h2 h3 h4 h5
  cases mct <;>
  simp [parseCOD, h1, h2, h3, h4, h5, e, s1, s2, s3, s4, l1, l2, progression_roundTrip, require,
    bind, Except.bind, pure, Except.pure, Limits.check, Limits.checkLe, Limits.bound]

/-- `readCompIndex` reads back a component index of the width `csiz` selects. -/
theorem readCompIndex_rd (csiz : Nat) (c : UInt16) (hw : csiz < 257 → c.toNat < 256) (r : Reader)
    (rest : List UInt8) (h : Rd r (compIndex csiz c ++ rest)) :
    ∃ r', readCompIndex csiz r = .ok (c, r') ∧ Rd r' rest := by
  unfold compIndex at h; unfold readCompIndex
  split
  · rename_i hc
    simp only [hc, ↓reduceIte, List.cons_append, List.nil_append] at h
    obtain ⟨r1, h1, hr1⟩ := rd_u8 h
    refine ⟨r1, ?_, hr1⟩
    have : c.toUInt8.toUInt16 = c := by
      apply UInt16.toNat_inj.mp; simp; have := hw hc; omega
    simp [h1, this]
  · rename_i hc
    simp only [hc, ↓reduceIte] at h
    exact rd_u16 h

/-- `readComponent` reads back a component index `< csiz`. -/
theorem readComponent_rd (csiz : Nat) (c : UInt16) (hc : c.toNat < csiz) (r : Reader)
    (rest : List UInt8) (h : Rd r (compIndex csiz c ++ rest)) :
    ∃ r', readComponent csiz r = .ok (c, r') ∧ Rd r' rest := by
  obtain ⟨r1, h1, hr1⟩ := readCompIndex_rd csiz c (fun h => by omega) r rest h
  refine ⟨r1, ?_, hr1⟩
  simp [readComponent, h1, hc, require, bind, Except.bind, pure, Except.pure]

/-- A COC record `parseCOC L csiz` accepts (T.800 A.6.2): component `< csiz`, well-formed coding style. -/
structure WFCOC (L : Limits) (csiz : Nat) (c : COC) : Prop where
  comp_lt : c.component.toNat < csiz
  style : WFCodingStyle L c.style

/-- COC round trip on any reader holding exactly the serialised body. -/
theorem parseCOC_rd (L : Limits) (csiz : Nat) (c : COC) (hc : WFCOC L csiz c) (r : Reader) (h : Rd r (cocBytes csiz c)) :
    parseCOC L csiz r = .ok c := by
  rw [← List.append_nil (cocBytes csiz c)] at h
  simp only [cocBytes, List.cons_append, List.nil_append, List.append_assoc] at h
  obtain ⟨r1, h1, hr1⟩ := readComponent_rd csiz c.component hc.comp_lt r _ h
  obtain ⟨r2, h2, hr2⟩ := rd_u8 hr1
  obtain ⟨r3, h3, hr3⟩ := readCodingStyle_rd L c.style hc.style r2 [] hr2
  have e := rd_expectEnd hr3 "COC"
  obtain ⟨component, style⟩ := c
  simp only at h1 h2 h3
  cases hs : style.precincts.isSome <;> rw [hs] at h3 <;>
  simp [parseCOC, h1, h2, h3, hs, e, require, bind, Except.bind, pure, Except.pure]

/-- **COD round trip** (T.800 A.6.1): `parseCOD L (serializeCOD c) = .ok c` for every well-formed `c`. -/
theorem parseCOD_roundTrip (L : Limits) (c : COD) (hc : WFCOD L c) (st : Stage) :
    parseCOD L (Reader.ofByteArray (serializeCOD c) st) = .ok c :=
  parseCOD_rd L c hc _ (rd_ofByteArray _ _)

/-- **COC round trip** (T.800 A.6.2): `parseCOC L csiz (serializeCOC csiz c) = .ok c` for every well-formed `c`. -/
theorem parseCOC_roundTrip (L : Limits) (csiz : Nat) (c : COC) (hc : WFCOC L csiz c) (st : Stage) :
    parseCOC L csiz (Reader.ofByteArray (serializeCOC csiz c) st) = .ok c :=
  parseCOC_rd L csiz c hc _ (rd_ofByteArray _ _)

/-- A step size whose exponent fits 5 bits and mantissa 11 bits. -/
structure WFStepSize (s : StepSize) : Prop where
  exponent_lt : s.exponent < 32
  mantissa_lt : s.mantissa < 2048

/-- Quantisation values `readQuant` accepts: 1…97 exponents (< 32) or step sizes, or one derived step size. -/
def WFQuant : Quantization → Prop
  | .none es => 1 ≤ es.size ∧ es.size ≤ maxBands ∧ ∀ e ∈ es.toList, e < 32
  | .derived b => WFStepSize b
  | .expounded ss => 1 ≤ ss.size ∧ ss.size ≤ maxBands ∧ ∀ s ∈ ss.toList, WFStepSize s

/-- A QCD record `parseQCD` accepts (T.800 A.6.4): guard bits < 8 and well-formed values. -/
structure WFQCD (q : QCD) : Prop where
  guard_lt : q.guardBits < 8
  quant : WFQuant q.quant

private theorem readExponent_rd (e : UInt8) (he : e < 32) (r : Reader) (rest : List UInt8)
    (h : Rd r ([e * 8] ++ rest)) : ∃ r', readExponent r = .ok (e, r') ∧ Rd r' rest := by
  obtain ⟨r1, h1, hr1⟩ := rd_u8 h
  refine ⟨r1, ?_, hr1⟩
  have a : e.toNat < 32 := he
  have e1 : e * 8 &&& 7 = 0 := by
    apply UInt8.toNat_inj.mp
    simp only [UInt8.toNat_and, show (7 : UInt8).toNat = 2^3 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, UInt8.toNat_mul]
    simp
    all_goals omega
  have e2 : (e * 8) >>> 3 = e := by
    apply UInt8.toNat_inj.mp
    simp only [UInt8.toNat_shiftRight, Nat.shiftRight_eq_div_pow, UInt8.toNat_mul]
    simp; omega
  simp [readExponent, h1, e1, e2, require, bind, Except.bind, pure, Except.pure]

private theorem readStepSize_rd (s : StepSize) (hs : WFStepSize s) (r : Reader) (rest : List UInt8)
    (h : Rd r (be16 s.toUInt16 ++ rest)) : ∃ r', readStepSize r = .ok (s, r') ∧ Rd r' rest := by
  obtain ⟨r1, h1, hr1⟩ := rd_u16 h
  refine ⟨r1, ?_, hr1⟩
  have a1 : s.exponent.toNat < 32 := hs.exponent_lt
  have a2 : s.mantissa.toNat < 2048 := hs.mantissa_lt
  have e1 : (s.toUInt16 >>> 11).toUInt8 = s.exponent := by
    apply UInt8.toNat_inj.mp
    simp only [UInt16.toNat_toUInt8, UInt16.toNat_shiftRight, Nat.shiftRight_eq_div_pow,
      StepSize.toUInt16, UInt16.toNat_add, UInt16.toNat_mul, UInt8.toNat_toUInt16]
    simp; omega
  have e2 : s.toUInt16 &&& 0x7FF = s.mantissa := by
    apply UInt16.toNat_inj.mp
    simp only [UInt16.toNat_and, show (0x7FF : UInt16).toNat = 2^11 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, StepSize.toUInt16, UInt16.toNat_add, UInt16.toNat_mul,
      UInt8.toNat_toUInt16]
    simp; omega
  simp [readStepSize, h1, e1, e2, bind, Except.bind, pure, Except.pure]

/-- `readQuant` reads back `Sqcd`/`SPqcd` for every quantisation style. -/
theorem readQuant_rd (q : QCD) (hq : WFQCD q) (r : Reader) (h : Rd r (qcdBytes q)) :
    readQuant r = .ok q := by
  obtain ⟨g, hw⟩ := hq
  obtain ⟨guardBits, quant⟩ := q
  simp only at g hw
  have a : guardBits.toNat < 8 := g
  have sh : ∀ k : UInt8, k < 3 → (guardBits * 32 + k) >>> 5 = guardBits ∧
      (guardBits * 32 + k) &&& 0x1F = k := by
    intro k hk
    have : k.toNat < 3 := hk
    constructor
    · apply UInt8.toNat_inj.mp
      simp only [UInt8.toNat_shiftRight, Nat.shiftRight_eq_div_pow, UInt8.toNat_add,
        UInt8.toNat_mul]
      simp; omega
    · apply UInt8.toNat_inj.mp
      simp only [UInt8.toNat_and, show (0x1F : UInt8).toNat = 2^5 - 1 from rfl,
        Nat.and_two_pow_sub_one_eq_mod, UInt8.toNat_add, UInt8.toNat_mul]
      simp; omega
  cases quant with
  | none es =>
    obtain ⟨w1, w2, w3⟩ := hw
    rw [← List.append_nil (qcdBytes _)] at h
    simp only [qcdBytes, quantBytes, QCD.sqcd, List.cons_append, List.nil_append] at h
    obtain ⟨r1, h1, hr1⟩ := rd_u8 h
    have hm : List.map (fun x => x * 8) es.toList = es.toList.flatMap fun e => [e * 8] := by
      generalize es.toList = l; induction l <;> simp_all
    rw [hm] at hr1
    have hl := rd_len hr1
    obtain ⟨r2, h2, hr2⟩ := rd_readArray' readExponent (fun e => [e * 8]) (· < 32)
      readExponent_rd es r1 [] w3 hr1
    have e := rd_expectEnd hr2 "QCD/QCC"
    obtain ⟨s1, s2⟩ := sh 0 (by decide)
    simp only [List.length_append, List.length_flatMap, List.length_singleton, List.map_const',
      List.sum_replicate_nat, List.length_nil] at hl
    simp_all [readQuant, require, bind, Except.bind, pure, Except.pure]
  | derived b =>
    rw [← List.append_nil (qcdBytes _)] at h
    simp only [qcdBytes, quantBytes, QCD.sqcd, List.cons_append, List.nil_append] at h
    obtain ⟨r1, h1, hr1⟩ := rd_u8 h
    obtain ⟨r2, h2, hr2⟩ := readStepSize_rd b hw r1 [] hr1
    have e := rd_expectEnd hr2 "QCD/QCC"
    obtain ⟨s1, s2⟩ := sh 1 (by decide)
    simp [readQuant, h1, h2, e, s1, s2, bind, Except.bind, pure, Except.pure]
  | expounded ss =>
    obtain ⟨w1, w2, w3⟩ := hw
    rw [← List.append_nil (qcdBytes _)] at h
    simp only [qcdBytes, quantBytes, QCD.sqcd, List.cons_append, List.nil_append] at h
    obtain ⟨r1, h1, hr1⟩ := rd_u8 h
    have hl := rd_len hr1
    obtain ⟨r2, h2, hr2⟩ := rd_readArray' readStepSize (fun s => be16 s.toUInt16) WFStepSize
      readStepSize_rd ss r1 [] w3 hr1
    have e := rd_expectEnd hr2 "QCD/QCC"
    obtain ⟨s1, s2⟩ := sh 2 (by decide)
    have hl' : r1.remaining = 2 * ss.size := by
      rw [hl]; simp [be16, List.length_flatMap, List.map_const', List.sum_replicate_nat, Nat.mul_comm]
    have d1 : 2 * ss.size % 2 = 0 := by omega
    have d2 : 2 * ss.size / 2 = ss.size := by omega
    simp [readQuant, h1, h2, e, s1, s2, hl', d1, d2, w1, w2, require, bind, Except.bind, pure,
      Except.pure]

/-- QCD round trip on any reader holding exactly the serialised body. -/
theorem parseQCD_rd (q : QCD) (hq : WFQCD q) (r : Reader) (h : Rd r (qcdBytes q)) :
    parseQCD r = .ok q :=
  readQuant_rd q hq r h

/-- **QCD round trip** (T.800 A.6.4): `parseQCD (serializeQCD q) = .ok q` for every well-formed `q`. -/
theorem parseQCD_roundTrip (q : QCD) (hq : WFQCD q) (st : Stage) :
    parseQCD (Reader.ofByteArray (serializeQCD q) st) = .ok q :=
  readQuant_rd q hq _ (rd_ofByteArray _ _)

/-- A QCC record `parseQCC csiz` accepts (T.800 A.6.5): component `< csiz` and well-formed parameters. -/
structure WFQCC (csiz : Nat) (q : QCC) : Prop where
  comp_lt : q.component.toNat < csiz
  params : WFQCD q.params

/-- QCC round trip on any reader holding exactly the serialised body. -/
theorem parseQCC_rd (csiz : Nat) (q : QCC) (hq : WFQCC csiz q) (r : Reader)
    (h : Rd r (qccBytes csiz q)) : parseQCC csiz r = .ok q := by
  obtain ⟨r1, h1, hr1⟩ := readComponent_rd csiz q.component hq.comp_lt r _ h
  have h2 := readQuant_rd q.params hq.params r1 hr1
  simp [parseQCC, h1, h2, bind, Except.bind, pure, Except.pure]

/-- **QCC round trip** (T.800 A.6.5): `parseQCC csiz (serializeQCC csiz q) = .ok q` for every well-formed `q`. -/
theorem parseQCC_roundTrip (csiz : Nat) (q : QCC) (hq : WFQCC csiz q) (st : Stage) :
    parseQCC csiz (Reader.ofByteArray (serializeQCC csiz q) st) = .ok q :=
  parseQCC_rd csiz q hq _ (rd_ofByteArray _ _)

/-- An RGN record `parseRGN csiz` accepts (T.800 A.6.3): component `< csiz` (`Srgn = 0` is implicit in the record). -/
structure WFRGN (csiz : Nat) (g : RGN) : Prop where
  comp_lt : g.component.toNat < csiz

/-- RGN round trip on any reader holding exactly the serialised body. -/
theorem parseRGN_rd (csiz : Nat) (g : RGN) (hg : WFRGN csiz g) (r : Reader) (h : Rd r (rgnBytes csiz g)) :
    parseRGN csiz r = .ok g := by
  obtain ⟨r1, h1, hr1⟩ := readComponent_rd csiz g.component hg.comp_lt r _ h
  obtain ⟨r2, h2, hr2⟩ := rd_u8 hr1
  obtain ⟨r3, h3, hr3⟩ := rd_u8 hr2
  have e := rd_expectEnd hr3 "RGN"
  simp [parseRGN, h1, h2, h3, e, bind, Except.bind, pure, Except.pure]

/-- A POC entry `readPocEntry csiz` accepts (T.800 Table A.32), including that both component fields fit one byte when `Csiz < 257`. -/
structure WFPocEntry (csiz : Nat) (e : PocEntry) : Prop where
  res_start_le : e.resStart ≤ 32
  res_lt : e.resStart < e.resEnd
  res_end_le : e.resEnd ≤ 33
  layer_ne : e.layerEnd ≠ 0
  comp_lt : e.compStart.toNat < e.compEnd csiz
  width : csiz < 257 → e.compStart.toNat < 256 ∧ e.compEndRaw.toNat < 256

/-- A POC record `parsePOC L csiz` accepts (T.800 A.6.6): 1…`L.maxPocEntries` well-formed entries. -/
structure WFPOC (L : Limits) (csiz : Nat) (p : POC) : Prop where
  size_pos : 1 ≤ p.entries.size
  size_limit : p.entries.size ≤ L.maxPocEntries
  entries : ∀ e ∈ p.entries.toList, WFPocEntry csiz e

private theorem readPocEntry_rd (csiz : Nat) (e : PocEntry) (he : WFPocEntry csiz e) (r : Reader)
    (rest : List UInt8) (h : Rd r (pocEntryBytes csiz e ++ rest)) :
    ∃ r', readPocEntry csiz r = .ok (e, r') ∧ Rd r' rest := by
  simp only [pocEntryBytes, List.cons_append, List.nil_append, List.append_assoc] at h
  obtain ⟨r1, h1, hr1⟩ := rd_u8 h
  obtain ⟨r2, h2, hr2⟩ := readCompIndex_rd csiz e.compStart (fun h => (he.width h).1) r1 _ hr1
  obtain ⟨r3, h3, hr3⟩ := rd_u16 hr2
  obtain ⟨r4, h4, hr4⟩ := rd_u8 hr3
  obtain ⟨r5, h5, hr5⟩ := readCompIndex_rd csiz e.compEndRaw (fun h => (he.width h).2) r4 _ hr4
  obtain ⟨r6, h6, hr6⟩ := rd_u8 hr5
  refine ⟨r6, ?_, hr6⟩
  obtain ⟨w1, w2, w3, w4, w5, _⟩ := he
  obtain ⟨resStart, compStart, layerEnd, resEnd, compEndRaw, order⟩ := e
  simp only at h1 h2 h3 h4 h5 h6 w1 w2 w3 w4 w5
  simp [readPocEntry, h1, h2, h3, h4, h5, h6, w1, w2, w3, w4, w5, progression_roundTrip, require,
    bind, Except.bind, pure, Except.pure]

private theorem pocEntryBytes_length (csiz : Nat) (e : PocEntry) :
    (pocEntryBytes csiz e).length = pocEntrySize csiz := by
  unfold pocEntryBytes compIndex pocEntrySize
  split <;> simp [be16]

/-- POC round trip on any reader holding exactly the serialised body. -/
theorem parsePOC_rd (L : Limits) (csiz : Nat) (p : POC) (hp : WFPOC L csiz p) (r : Reader) (h : Rd r (pocBytes csiz p)) :
    parsePOC L csiz r = .ok p := by
  have hl := rd_len h
  rw [← List.append_nil (pocBytes csiz p)] at h
  obtain ⟨r1, h1, hr1⟩ := rd_readArray' (readPocEntry csiz) (pocEntryBytes csiz) (WFPocEntry csiz)
    (readPocEntry_rd csiz) p.entries r [] hp.entries h
  have e := rd_expectEnd hr1 "POC"
  have hl' : r.remaining = p.entries.size * pocEntrySize csiz := by
    rw [hl]; simp [pocBytes, List.length_flatMap, pocEntryBytes_length, List.map_const',
      List.sum_replicate_nat]
  have hsz : 0 < pocEntrySize csiz := by unfold pocEntrySize; split <;> omega
  have d1 : p.entries.size * pocEntrySize csiz % pocEntrySize csiz = 0 := Nat.mul_mod_left _ _
  have d2 : p.entries.size * pocEntrySize csiz / pocEntrySize csiz = p.entries.size :=
    Nat.mul_div_cancel _ hsz
  obtain ⟨w1, w2, _⟩ := hp
  simp [parsePOC, h1, e, hl', d1, d2, w1, w2, require, bind, Except.bind, pure, Except.pure,
    Limits.check, Limits.checkLe, Limits.bound]

/-- `Reader.rest` copies out exactly the bytes left. -/
theorem rd_rest {r : Reader} {l : List UInt8} (h : Rd r l) : r.rest = pack l := by
  obtain ⟨h1, h2⟩ := h
  apply ByteArray.ext
  simp only [Reader.rest, ByteArray.data_extract, pack]
  have hs := r.stop_le
  apply Array.ext
  · have hs' : r.stop ≤ r.data.data.size := hs
    rw [Array.size_extract, Nat.min_eq_left hs', List.size_toArray]
    omega
  · intro i hi1 hi2
    simp only [Array.getElem_extract, List.getElem_toArray]
    have := h2 i (by simpa using hi2)
    rw [Array.getElem?_eq_some_iff] at this
    obtain ⟨_, h3⟩ := this
    exact h3

/-- Every COM is well formed (`Rcom` is kept raw, `Ccom` is any byte string). -/
def WFCOM (_c : COM) : Prop := True

/-- COM round trip on any reader holding exactly the serialised body. -/
theorem parseCOM_rd (c : COM) (r : Reader) (h : Rd r (comBytes c)) :
    parseCOM r = .ok c := by
  obtain ⟨r1, h1, hr1⟩ := rd_u16 h
  have e := rd_rest hr1
  have hp : pack c.data.data.toList = c.data := by apply ByteArray.ext; simp [pack]
  simp [parseCOM, h1, e, hp, bind, Except.bind, pure, Except.pure]

/-- A CRG record `parseCRG csiz` accepts (T.800 A.9.1): exactly `csiz` pairs. -/
structure WFCRG (csiz : Nat) (c : CRG) : Prop where
  size_eq : c.offsets.size = csiz

private theorem readCrgPair_rd (p : UInt16 × UInt16) (_hp : True) (r : Reader) (rest : List UInt8)
    (h : Rd r (crgPairBytes p ++ rest)) : ∃ r', readCrgPair r = .ok (p, r') ∧ Rd r' rest := by
  simp only [crgPairBytes, List.append_assoc] at h
  obtain ⟨r1, h1, hr1⟩ := rd_u16 h
  obtain ⟨r2, h2, hr2⟩ := rd_u16 hr1
  exact ⟨r2, by simp [readCrgPair, h1, h2, bind, Except.bind, pure, Except.pure], hr2⟩

/-- CRG round trip on any reader holding exactly the serialised body. -/
theorem parseCRG_rd (csiz : Nat) (c : CRG) (hc : WFCRG csiz c) (r : Reader) (h : Rd r (crgBytes c)) :
    parseCRG csiz r = .ok c := by
  have hl := rd_len h
  rw [← List.append_nil (crgBytes c)] at h
  obtain ⟨r1, h1, hr1⟩ := rd_readArray' readCrgPair crgPairBytes (fun _ => True)
    readCrgPair_rd c.offsets r [] (fun _ _ => trivial) h
  have e := rd_expectEnd hr1 "CRG"
  have hl' : r.remaining = 4 * csiz := by
    rw [hl, ← hc.size_eq]
    simp [crgBytes, crgPairBytes, be16, List.length_flatMap, List.map_const',
      List.sum_replicate_nat, Nat.mul_comm]
  obtain ⟨w⟩ := hc
  subst w
  simp [parseCRG, h1, e, hl', require, bind, Except.bind, pure, Except.pure]

/-- **RGN round trip** (T.800 A.6.3): `parseRGN csiz (serializeRGN csiz g) = .ok g` for every well-formed `g`. -/
theorem parseRGN_roundTrip (csiz : Nat) (g : RGN) (hg : WFRGN csiz g) (st : Stage) :
    parseRGN csiz (Reader.ofByteArray (serializeRGN csiz g) st) = .ok g :=
  parseRGN_rd csiz g hg _ (rd_ofByteArray _ _)

/-- **POC round trip** (T.800 A.6.6): `parsePOC L csiz (serializePOC csiz p) = .ok p` for every well-formed `p`. -/
theorem parsePOC_roundTrip (L : Limits) (csiz : Nat) (p : POC) (hp : WFPOC L csiz p) (st : Stage) :
    parsePOC L csiz (Reader.ofByteArray (serializePOC csiz p) st) = .ok p :=
  parsePOC_rd L csiz p hp _ (rd_ofByteArray _ _)

/-- **COM round trip** (T.800 A.9.2): `parseCOM (serializeCOM c) = .ok c` for every `c` (no side condition). -/
theorem parseCOM_roundTrip (c : COM) (st : Stage) :
    parseCOM (Reader.ofByteArray (serializeCOM c) st) = .ok c :=
  parseCOM_rd c _ (rd_ofByteArray _ _)

/-- **CRG round trip** (T.800 A.9.1): `parseCRG csiz (serializeCRG c) = .ok c` when `c` has `csiz` pairs. -/
theorem parseCRG_roundTrip (csiz : Nat) (c : CRG) (hc : WFCRG csiz c) (st : Stage) :
    parseCRG csiz (Reader.ofByteArray (serializeCRG c) st) = .ok c :=
  parseCRG_rd csiz c hc _ (rd_ofByteArray _ _)

/-- `Reader.take` splits off exactly the next `l.length` bytes as a sub-reader holding `l`. -/
theorem rd_take {r : Reader} {l rest : List UInt8} (h : Rd r (l ++ rest)) :
    ∃ sub r', r.take l.length = .ok (sub, r') ∧ Rd sub l ∧ Rd r' rest := by
  unfold Reader.take; split
  · rename_i hn
    refine ⟨_, _, rfl, ⟨rfl, fun i hi => ?_⟩, by simpa using rd_adv h l.length hn⟩
    have := h.2 i (by simp; omega)
    simpa [List.getElem_append_left hi] using this
  · have := h.1; simp at this; omega

/-- Reading a marker and `readSegment` on `marker ++ Lxxx ++ body ++ rest` yields the marker, a body reader holding exactly `body`, `Lxxx = body.length + 2`, and a reader holding `rest`. -/
theorem segment_rd (code : UInt16) (body rest : List UInt8) (hb : body.length + 2 < 65536)
    (r : Reader) (h : Rd r (be16 code ++ be16 (body.length + 2).toUInt16 ++ body ++ rest)) :
    ∃ r1 sub r2, r.u16be = .ok (code, r1) ∧ readSegment r1 = .ok (sub, body.length + 2, r2) ∧
      Rd sub body ∧ Rd r2 rest := by
  simp only [List.append_assoc] at h
  obtain ⟨r1, h1, hr1⟩ := rd_u16 h
  obtain ⟨r2, h2, hr2⟩ := rd_u16 hr1
  obtain ⟨sub, r3, h3, hs, hr3⟩ := rd_take hr2
  have e : (body.length + 2).toUInt16.toNat = body.length + 2 := by simp; omega
  have g : (2 : UInt16) ≤ (body.length + 2).toUInt16 := by
    rw [UInt16.le_iff_toNat_le, e]; simp
  refine ⟨r1, sub, r3, h1, ?_, hs, hr3⟩
  generalize (body.length + 2).toUInt16 = v at h2 e g
  simp [readSegment, h2, h3, g, e, require, bind, Except.bind, pure, Except.pure]

/-- `pack` turns list append into `ByteArray` append. -/
theorem pack_append (a b : List UInt8) : pack a ++ pack b = pack (a ++ b) := by
  apply ByteArray.ext; simp [pack]

/-- **Segment framing round trip** (T.800 A.1.4): on `segment code (pack body)`, `u16be` reads `code` and `readSegment` returns a sub-reader holding exactly `body`, `Lxxx = body.length + 2`, and nothing is left. -/
theorem segment_roundTrip (code : UInt16) (body : List UInt8) (hb : body.length + 2 < 65536)
    (st : Stage) :
    ∃ r1 sub r2, (Reader.ofByteArray (segment code (pack body)) st).u16be = .ok (code, r1) ∧
      readSegment r1 = .ok (sub, body.length + 2, r2) ∧ Rd sub body ∧ r2.atEnd := by
  have hsz : (pack body).size = body.length := by simp [pack, ByteArray.size]
  have h := rd_ofByteArray (be16 code ++ be16 (body.length + 2).toUInt16 ++ body ++ []) st
  simp only [List.append_nil] at h
  rw [← pack_append] at h
  obtain ⟨r1, sub, r2, h1, h2, h3, h4⟩ := segment_rd code body [] hb _ (by simpa using h)
  refine ⟨r1, sub, r2, ?_, h2, h3, ?_⟩
  · simpa [segment, hsz] using h1
  · have := h4.1; simp [Reader.atEnd, this]

/-- Composition example: a whole serialised COD segment reads back as the marker, the length and the record. -/
theorem parseCOD_segment (L : Limits) (c : COD) (hc : WFCOD L c)
    (hb : (codBytes c).length + 2 < 65536) (st : Stage) :
    ∃ r1 sub r2, (Reader.ofByteArray (segment Code.COD (serializeCOD c)) st).u16be =
        .ok (Code.COD, r1) ∧
      readSegment r1 = .ok (sub, (codBytes c).length + 2, r2) ∧ parseCOD L sub = .ok c ∧
      r2.atEnd := by
  obtain ⟨r1, sub, r2, h1, h2, h3, h4⟩ := segment_roundTrip Code.COD (codBytes c) hb st
  exact ⟨r1, sub, r2, h1, h2, parseCOD_rd L c hc sub h3, h4⟩

end JPEG2000.Spec.MarkerRoundTrip
