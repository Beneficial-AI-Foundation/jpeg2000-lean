import JPEG2000.Bytes
import JPEG2000.TilePart
import Encode.TilePart
import Spec.MarkerRoundTrip

/-!
# Tile-part marker-segment round trip (Plan.md §4 M1, §5.1, §5.3; T.800 A.4.2, A.7)

Task 1.10 completes the M1 round trip for marker segments: the tile-part and pointer
segments `SOT` (T.800 A.4.2), `TLM` (A.7.1), `PLT` (A.7.3), `PPM` (A.7.4) and `PPT` (A.7.5)
of `JPEG2000.TilePart`, against the serialisers of `Encode.TilePart`. Same shape as
`Spec.MarkerRoundTrip` (whose reader lemmas `Rd`, `rd_u8`, `rd_u16`, `rd_u32`, `rd_readArray'`,
`rd_expectEnd`, `rd_rest` are reused):

* `WFX` states exactly the parser's checks; `parseX_rd` is the round trip on any reader with
  `Rd r (xBytes m)`; `parseX_roundTrip` on `Reader.ofByteArray (serializeX m) st`.
* `PLT`: the packet lengths are written in the canonical 7-bit continuation code;
  `readVarints_encodeVarint` is the varint lemma (decoding `encodeVarint n ++ rest` yields
  `n` and leaves `rest`), proved by well-founded induction on `n` along `varintHigh`.
  `WFPLT` = every length `< 2^32` (the parser rejects larger ones).
* `PPM`/`PPT`: the parsed record holds its data as an absolute byte range of the input, not
  a copy. The serialiser takes the buffer `src` the range refers to; parsing the serialised
  body gives the same `Zppm`/`Zppt` and the range `[1, 1 + length)` of the new buffer, whose
  bytes are exactly the original range's bytes of `src` (`parsePPM_roundTrip`). On an
  arbitrary reader (`parsePPM_rd`) the range is `[r.pos + 1, r.stop)` and holds the data.
-/

namespace JPEG2000.Spec.TilePartRoundTrip

open JPEG2000 JPEG2000.Bytes JPEG2000.Marker JPEG2000.TilePart JPEG2000.Encode.Marker
  JPEG2000.Encode.TilePart JPEG2000.Spec.MarkerRoundTrip

/-! ## SOT -/

/-- A SOT record `parseSOT` accepts (T.800 A.4.2): `Isot ≤ 65534`, `Psot = 0 ∨ Psot ≥ 14`,
`TPsot ≤ 254`, `TPsot ≤ TNsot` when `TNsot ≠ 0`. -/
structure WFSOT (s : SOT) : Prop where
  isot_ne : s.isot ≠ 0xFFFF
  psot_ok : s.psot = 0 ∨ s.psot ≥ 14
  tpsot_ne : s.tpsot ≠ 255
  tnsot_ok : s.tnsot = 0 ∨ s.tpsot ≤ s.tnsot

/-- SOT round trip on any reader holding exactly the serialised body. -/
theorem parseSOT_rd (s : SOT) (hs : WFSOT s) (r : Reader) (h : Rd r (sotBytes s)) :
    parseSOT r = .ok s := by
  have hl := rd_len h
  simp only [sotBytes, List.append_assoc] at h
  obtain ⟨r1, h1, hr1⟩ := rd_u16 h
  obtain ⟨r2, h2, hr2⟩ := rd_u32 hr1
  obtain ⟨r3, h3, hr3⟩ := rd_u8 hr2
  obtain ⟨r4, h4, hr4⟩ := rd_u8 hr3
  have e := rd_expectEnd hr4 "SOT"
  obtain ⟨c1, c2, c3, c4⟩ := hs
  have hl' : r.remaining = 8 := by rw [hl]; simp [sotBytes, be16, be32]
  simp [parseSOT, hl', h1, h2, h3, h4, e, c1, c2, c3, c4, require, bind, Except.bind, pure,
    Except.pure]

/-- **SOT round trip** (T.800 A.4.2). -/
theorem parseSOT_roundTrip (s : SOT) (hs : WFSOT s) (st : Stage) :
    parseSOT (Reader.ofByteArray (serializeSOT s) st) = .ok s :=
  parseSOT_rd s hs _ (rd_ofByteArray _ _)

/-! ## TLM -/

/-- A TLM entry that fits the widths `ST`/`SP` (T.800 Table A.34): no tile index when
`ST = 0`, one below 256 when `ST = 1`, one present when `ST = 2`, and `Ptlm < 2^16` when
`SP = 0`. -/
structure WFTlmEntry (st : UInt8) (sp : Bool) (e : TlmEntry) : Prop where
  tile_none : st = 0 → e.tile = none
  tile_byte : st = 1 → ∃ v, e.tile = some v ∧ v.toNat < 256
  tile_some : st = 2 → e.tile.isSome
  len16 : sp = false → e.length.toNat < 65536

/-- A TLM record `parseTLM L` accepts (T.800 A.7.1): `ST ≤ 2`, at most `L.maxTileParts`
entries, each fitting the widths. -/
structure WFTLM (L : Limits) (t : TLM) : Prop where
  st_le : t.st ≤ 2
  count : t.entries.size ≤ L.maxTileParts
  entries : ∀ e ∈ t.entries.toList, WFTlmEntry t.st t.sp e

private theorem st_cases : ∀ s : UInt8, s ≤ 2 → s = 0 ∨ s = 1 ∨ s = 2 := by decide +kernel

private theorem stlm_bits : ∀ s : UInt8, s ≤ 2 → ∀ b : Bool,
    (s * 16 + (if b then 64 else 0)) &&& 0x8F = 0 ∧
    ((s * 16 + (if b then 64 else 0)) >>> 4) &&& 3 = s ∧
    ((s * 16 + (if b then 64 else 0)) &&& 0x40 != 0) = b := by decide +kernel

private theorem u16_of_u8 (v : UInt16) (h : v.toNat < 256) : v.toUInt8.toUInt16 = v := by
  apply UInt16.toNat_inj.mp; simp; omega

private theorem u32_of_u16 (v : UInt32) (h : v.toNat < 65536) : v.toUInt16.toUInt32 = v := by
  apply UInt32.toNat_inj.mp; simp; omega

private theorem readTlmEntry_rd (st : UInt8) (sp : Bool) (hst : st ≤ 2) (e : TlmEntry)
    (he : WFTlmEntry st sp e) (r : Reader) (rest : List UInt8)
    (h : Rd r (tlmEntryBytes st sp e ++ rest)) :
    ∃ r', readTlmEntry st sp r = .ok (e, r') ∧ Rd r' rest := by
  obtain ⟨tile, len⟩ := e
  obtain ⟨w0, w1, w2, w3⟩ := he
  simp only at w0 w1 w2 w3
  rcases st_cases st hst with rfl | rfl | rfl
  · have ht := w0 rfl; subst ht
    cases sp
    · simp only [tlmEntryBytes, tlmTileBytes, List.nil_append, Bool.false_eq_true,
        ↓reduceIte] at h
      obtain ⟨r1, h1, hr1⟩ := rd_u16 h
      exact ⟨r1, by simp [readTlmEntry, h1, u32_of_u16 len (w3 rfl), bind, Except.bind, pure,
        Except.pure], hr1⟩
    · simp only [tlmEntryBytes, tlmTileBytes, List.nil_append, ↓reduceIte] at h
      obtain ⟨r1, h1, hr1⟩ := rd_u32 h
      exact ⟨r1, by simp [readTlmEntry, h1, bind, Except.bind, pure, Except.pure], hr1⟩
  · obtain ⟨v, hv, hv'⟩ := w1 rfl; subst hv
    cases sp
    · simp only [tlmEntryBytes, tlmTileBytes, Option.getD_some, Bool.false_eq_true,
        ↓reduceIte, List.cons_append, List.nil_append] at h
      obtain ⟨r1, h1, hr1⟩ := rd_u8 h
      obtain ⟨r2, h2, hr2⟩ := rd_u16 hr1
      exact ⟨r2, by simp [readTlmEntry, h1, h2, u32_of_u16 len (w3 rfl), u16_of_u8 v hv', bind,
        Except.bind, pure, Except.pure], hr2⟩
    · simp only [tlmEntryBytes, tlmTileBytes, Option.getD_some, ↓reduceIte, List.cons_append,
        List.nil_append] at h
      obtain ⟨r1, h1, hr1⟩ := rd_u8 h
      obtain ⟨r2, h2, hr2⟩ := rd_u32 hr1
      exact ⟨r2, by simp [readTlmEntry, h1, h2, u16_of_u8 v hv', bind, Except.bind, pure,
        Except.pure], hr2⟩
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (w2 rfl); subst hv
    cases sp
    · simp only [tlmEntryBytes, tlmTileBytes, Option.getD_some, Bool.false_eq_true,
        ↓reduceIte, List.append_assoc] at h
      obtain ⟨r1, h1, hr1⟩ := rd_u16 h
      obtain ⟨r2, h2, hr2⟩ := rd_u16 hr1
      exact ⟨r2, by simp [readTlmEntry, h1, h2, u32_of_u16 len (w3 rfl), bind,
        Except.bind, pure, Except.pure], hr2⟩
    · simp only [tlmEntryBytes, tlmTileBytes, Option.getD_some, ↓reduceIte,
        List.append_assoc] at h
      obtain ⟨r1, h1, hr1⟩ := rd_u16 h
      obtain ⟨r2, h2, hr2⟩ := rd_u32 hr1
      exact ⟨r2, by simp [readTlmEntry, h1, h2, bind, Except.bind, pure, Except.pure], hr2⟩

private theorem tlmEntryBytes_length (st : UInt8) (sp : Bool) (hst : st ≤ 2) (e : TlmEntry)
    (he : WFTlmEntry st sp e) :
    (tlmEntryBytes st sp e).length = st.toNat + (if sp then 4 else 2) := by
  rcases st_cases st hst with rfl | rfl | rfl <;> cases sp <;>
    simp [tlmEntryBytes, tlmTileBytes, be16, be32]

private theorem flatMap_length_const {α : Type} (f : α → List UInt8) (k : Nat) :
    ∀ l : List α, (∀ x ∈ l, (f x).length = k) → (l.flatMap f).length = l.length * k
  | [], _ => by simp
  | x :: xs, h => by
    have := flatMap_length_const f k xs (fun y hy => h y (by simp [hy]))
    simp only [List.flatMap_cons, List.length_append, h x (by simp), this, List.length_cons]
    rw [Nat.succ_mul]; omega

/-- TLM round trip on any reader holding exactly the serialised body. -/
theorem parseTLM_rd (L : Limits) (t : TLM) (ht : WFTLM L t) (r : Reader)
    (h : Rd r (tlmBytes t)) : parseTLM L r = .ok t := by
  obtain ⟨c1, c2, c3⟩ := ht
  simp only [tlmBytes, List.cons_append, List.nil_append] at h
  obtain ⟨r1, h1, hr1⟩ := rd_u8 h
  obtain ⟨r2, h2, hr2⟩ := rd_u8 hr1
  obtain ⟨r3, h3, hr3⟩ := rd_readArray' (readTlmEntry t.st t.sp) (tlmEntryBytes t.st t.sp)
    (WFTlmEntry t.st t.sp) (readTlmEntry_rd t.st t.sp c1) t.entries r2 [] c3
    (by simpa using hr2)
  have e := rd_expectEnd hr3 "TLM"
  obtain ⟨b1, b2, b3⟩ := stlm_bits t.st c1 t.sp
  have hesz : 0 < t.st.toNat + (if t.sp then 4 else 2) := by cases t.sp <;> simp
  have hrem : r2.remaining = t.entries.size * (t.st.toNat + (if t.sp then 4 else 2)) := by
    rw [rd_len hr2, flatMap_length_const _ _ _
      (fun e he => tlmEntryBytes_length t.st t.sp c1 e (c3 e he))]
    simp
  have hmod : t.entries.size * (t.st.toNat + (if t.sp then 4 else 2)) %
      (t.st.toNat + (if t.sp then 4 else 2)) = 0 := Nat.mul_mod_left _ _
  have hdiv : t.entries.size * (t.st.toNat + (if t.sp then 4 else 2)) /
      (t.st.toNat + (if t.sp then 4 else 2)) = t.entries.size := Nat.mul_div_cancel _ hesz
  simp only [TLM.stlm] at h2
  simp [parseTLM, h1, h2, b1, b2, b3, c1, hrem, hmod, hdiv, c2, h3, e, require, bind,
    Except.bind, pure, Except.pure, Limits.check, Limits.checkLe, Limits.bound]

/-- **TLM round trip** (T.800 A.7.1). -/
theorem parseTLM_roundTrip (L : Limits) (t : TLM) (ht : WFTLM L t) (st : Stage) :
    parseTLM L (Reader.ofByteArray (serializeTLM t) st) = .ok t :=
  parseTLM_rd L t ht _ (rd_ofByteArray _ _)

/-! ## PLT -/

private theorem and7F (b : UInt8) : (b &&& 0x7F).toNat = b.toNat % 128 := by
  simp only [UInt8.toNat_and, show (0x7F : UInt8).toNat = 2^7 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

private theorem and80 : ∀ b : UInt8, (b &&& 0x80 != 0) = decide (128 ≤ b.toNat) := by
  decide +kernel

/-- The pending flag only matters once the fuel is exhausted. -/
private theorem readVarints_pending (f c : Nat) (p q : Bool) (acc : Array Nat) (r : Reader) :
    readVarints (f + 1) c p acc r = readVarints (f + 1) c q acc r := rfl

/-- One unfolding of `varintHigh` for a nonzero argument. -/
theorem varintHigh_succ (m : Nat) (h : m ≠ 0) :
    varintHigh m = varintHigh (m / 128) ++ [(m % 128 + 128).toUInt8] := by
  rw [varintHigh]; simp [h]

/-- Decoding the leading bytes `varintHigh m` from `cur = 0` leaves `cur = m`. -/
theorem readVarints_high (m : Nat) (hm : m < 2^32) (fuel : Nat) (p q : Bool)
    (acc : Array Nat) (r : Reader) (rest : List UInt8) (h : Rd r (varintHigh m ++ rest)) :
    ∃ r', Rd r' rest ∧
      readVarints (fuel + 1 + (varintHigh m).length) 0 p acc r =
        readVarints (fuel + 1) m q acc r' := by
  by_cases h0 : m = 0
  · subst h0
    have e : varintHigh 0 = [] := by rw [varintHigh]; simp
    rw [e] at h ⊢
    exact ⟨r, by simpa using h, readVarints_pending _ _ _ _ _ _⟩
  · rw [varintHigh_succ m h0] at h ⊢
    rw [List.append_assoc] at h
    obtain ⟨r1, hr1, e1⟩ := readVarints_high (m / 128) (by omega) (fuel + 1) p true acc r _ h
    obtain ⟨r2, h2, hr2⟩ := rd_u8 hr1
    refine ⟨r2, hr2, ?_⟩
    have hb : ((m % 128 + 128).toUInt8).toNat = m % 128 + 128 := by
      simp only [Nat.toUInt8, UInt8.toNat_ofNat']; omega
    have hv : m / 128 * 128 + (((m % 128 + 128).toUInt8) &&& 0x7F).toNat = m := by
      rw [and7F, hb]; omega
    rw [show fuel + 1 + (varintHigh (m / 128) ++ [(m % 128 + 128).toUInt8]).length =
      fuel + 1 + 1 + (varintHigh (m / 128)).length by simp; omega, e1]
    simp only [readVarints, h2, hv, and80, hb]
    simp (disch := omega) [show ¬ (m ≥ 4294967296) by omega]

/-- **Varint lemma** (T.800 A.7.3): decoding `encodeVarint n ++ rest` (the canonical code of
`n < 2^32`) yields `n` and leaves exactly `rest`, whatever follows. -/
theorem readVarints_encodeVarint (n : Nat) (hn : n < 2^32) (fuel : Nat) (p : Bool)
    (acc : Array Nat) (r : Reader) (rest : List UInt8) (h : Rd r (encodeVarint n ++ rest)) :
    ∃ r', Rd r' rest ∧
      readVarints (fuel + (encodeVarint n).length) 0 p acc r =
        readVarints fuel 0 false (acc.push n) r' := by
  simp only [encodeVarint, List.append_assoc] at h ⊢
  obtain ⟨r1, hr1, e1⟩ := readVarints_high (n / 128) (by omega) fuel p true acc r _ h
  obtain ⟨r2, h2, hr2⟩ := rd_u8 hr1
  refine ⟨r2, hr2, ?_⟩
  have hb : ((n % 128).toUInt8).toNat = n % 128 := by
    simp only [Nat.toUInt8, UInt8.toNat_ofNat']; omega
  have hv : n / 128 * 128 + (((n % 128).toUInt8) &&& 0x7F).toNat = n := by
    rw [and7F, hb]; omega
  rw [show fuel + (varintHigh (n / 128) ++ [(n % 128).toUInt8]).length =
    fuel + 1 + (varintHigh (n / 128)).length by simp; omega, e1]
  simp only [readVarints, h2, hv, and80, hb]
  simp (disch := omega) [show ¬ (n ≥ 4294967296) by omega, show ¬ 128 ≤ n % 128 by omega]

/-- Decoding the concatenated canonical codes of a list of lengths `< 2^32` yields the list. -/
theorem readVarints_list : ∀ (ls : List Nat) (acc : Array Nat) (r : Reader),
    (∀ x ∈ ls, x < 2^32) → Rd r (ls.flatMap encodeVarint) →
    readVarints (ls.flatMap encodeVarint).length 0 false acc r = .ok (acc ++ ls.toArray)
  | [], acc, r, _, _ => by simp [readVarints]
  | x :: xs, acc, r, hx, h => by
    simp only [List.flatMap_cons] at h ⊢
    obtain ⟨r1, hr1, e1⟩ := readVarints_encodeVarint x (hx x (by simp))
      (xs.flatMap encodeVarint).length false acc r _ h
    rw [List.length_append, Nat.add_comm, e1,
      readVarints_list xs (acc.push x) r1 (fun y hy => hx y (by simp [hy])) hr1]
    simp

/-- A PLT record `parsePLT` accepts (T.800 A.7.3): every packet length below `2^32`. -/
structure WFPLT (p : PLT) : Prop where
  lengths_lt : ∀ x ∈ p.lengths.toList, x < 2^32

/-- PLT round trip on any reader holding exactly the serialised body. -/
theorem parsePLT_rd (p : PLT) (hp : WFPLT p) (r : Reader) (h : Rd r (pltBytes p)) :
    parsePLT r = .ok p := by
  simp only [pltBytes, List.cons_append, List.nil_append] at h
  obtain ⟨r1, h1, hr1⟩ := rd_u8 h
  have e := readVarints_list p.lengths.toList #[] r1 hp.lengths_lt hr1
  rw [← rd_len hr1] at e
  simp [parsePLT, h1, e, bind, Except.bind, pure, Except.pure]

/-- **PLT round trip** (T.800 A.7.3), with the canonical packet-length code. -/
theorem parsePLT_roundTrip (p : PLT) (hp : WFPLT p) (st : Stage) :
    parsePLT (Reader.ofByteArray (serializePLT p) st) = .ok p :=
  parsePLT_rd p hp _ (rd_ofByteArray _ _)

/-! ## PPM and PPT -/

/-- The reader after its first byte, as `Reader.u8` leaves it. -/
private theorem rd_u8_pos {r : Reader} {b : UInt8} {l : List UInt8} (h : Rd r (b :: l)) :
    ∃ hp : r.pos + 1 ≤ r.stop,
      r.u8 = .ok (b, { r with pos := r.pos + 1, pos_le := hp }) ∧
      Rd { r with pos := r.pos + 1, pos_le := hp } l := by
  have hp : r.pos + 1 ≤ r.stop := by have := h.1; simp at this; omega
  obtain ⟨r', h1, _⟩ := rd_u8 h
  refine ⟨hp, ?_, by simpa using rd_adv h 1 hp⟩
  have e : r.u8 = .ok (r.data.get r.pos (by have := r.stop_le; omega),
      { r with pos := r.pos + 1, pos_le := hp }) := by
    unfold Reader.u8; simp [hp]
  rw [e] at h1 ⊢
  simp only [Except.ok.injEq, Prod.mk.injEq] at h1
  rw [h1.1]

/-- Under `Rd r l`, the range `[r.pos, r.pos + l.length)` of the buffer holds `l`. -/
theorem rd_range {r : Reader} {l : List UInt8} (h : Rd r l) :
    ({ offset := r.pos, length := l.length } : ByteRange).bytes r.data = pack l := by
  have e := rd_rest h
  have hs := h.1
  simp only [Reader.rest] at e
  simp only [ByteRange.bytes, ByteRange.stop, ← hs, e]

/-- PPM round trip on any reader holding `Zppm` followed by nonempty data `l`: the record has
`Zppm = z` and the range `[r.pos + 1, r.stop)` of the buffer, which holds `l`. -/
theorem parsePPM_rd (z : UInt8) (l : List UInt8) (hl : l ≠ []) (r : Reader)
    (h : Rd r (z :: l)) :
    parsePPM r = .ok { zppm := z, body := { offset := r.pos + 1, length := l.length } } ∧
      ({ offset := r.pos + 1, length := l.length } : ByteRange).bytes r.data = pack l := by
  obtain ⟨hp, h1, hr1⟩ := rd_u8_pos h
  have hlen := rd_len hr1
  have hne : 1 ≤ l.length := by cases l <;> simp_all
  refine ⟨?_, rd_range hr1⟩
  simp only [Reader.remaining] at hlen
  simp [parsePPM, h1, Reader.remaining, hlen, hne, require, bind, Except.bind, pure,
    Except.pure]

/-- PPT round trip on any reader holding `Zppt` followed by nonempty data `l`: the record has
`Zppt = z` and the range `[r.pos + 1, r.stop)` of the buffer, which holds `l`. -/
theorem parsePPT_rd (z : UInt8) (l : List UInt8) (hl : l ≠ []) (r : Reader)
    (h : Rd r (z :: l)) :
    parsePPT r = .ok { zppt := z, body := { offset := r.pos + 1, length := l.length } } ∧
      ({ offset := r.pos + 1, length := l.length } : ByteRange).bytes r.data = pack l := by
  obtain ⟨hp, h1, hr1⟩ := rd_u8_pos h
  have hlen := rd_len hr1
  have hne : 1 ≤ l.length := by cases l <;> simp_all
  refine ⟨?_, rd_range hr1⟩
  simp only [Reader.remaining] at hlen
  simp [parsePPT, h1, Reader.remaining, hlen, hne, require, bind, Except.bind, pure,
    Except.pure]

/-- A byte range lying inside `src` with at least one byte (the parsers reject an empty
`Ippm`/`Ippt`). -/
structure WFRange (src : ByteArray) (b : ByteRange) : Prop where
  inside : b.stop ≤ src.size
  nonempty : 1 ≤ b.length

private theorem range_bytes_list (src : ByteArray) (b : ByteRange) (hb : WFRange src b) :
    (b.bytes src).data.toList.length = b.length ∧ (b.bytes src).data.toList ≠ [] ∧
      pack (b.bytes src).data.toList = b.bytes src := by
  have hsz : (b.bytes src).size = b.length := by
    have := hb.inside
    simp only [ByteRange.bytes, ByteArray.size_extract, ByteRange.stop] at this ⊢
    omega
  have hl : (b.bytes src).data.toList.length = b.length := by
    rw [Array.length_toList]; exact hsz
  refine ⟨hl, ?_, by apply ByteArray.ext; simp [pack]⟩
  intro e; rw [e] at hl; have := hb.nonempty; simp at hl; omega

/-- A PPM record whose data range lies inside its source buffer `src` (T.800 A.7.4). -/
def WFPPM (src : ByteArray) (p : PPM) : Prop := WFRange src p.body

/-- A PPT record whose data range lies inside its source buffer `src` (T.800 A.7.5). -/
def WFPPT (src : ByteArray) (p : PPT) : Prop := WFRange src p.body

/-- **PPM round trip** (T.800 A.7.4). The record keeps its data as a range of the input, so
the round trip is up to relocation: parsing `serializePPM p src` gives the same `Zppm` and
the range `[1, 1 + length)` of the serialised body, holding exactly the bytes of `p.body`
in `src`. -/
theorem parsePPM_roundTrip (src : ByteArray) (p : PPM) (hp : WFPPM src p) (st : Stage) :
    parsePPM (Reader.ofByteArray (serializePPM p src) st) =
        .ok { zppm := p.zppm, body := { offset := 1, length := p.body.length } } ∧
      ({ offset := 1, length := p.body.length } : ByteRange).bytes (serializePPM p src) =
        p.body.bytes src := by
  obtain ⟨hl, hne, hpk⟩ := range_bytes_list src p.body hp
  have := parsePPM_rd p.zppm _ hne _ (rd_ofByteArray (ppmBytes p src) st)
  simp only [hl, hpk] at this
  exact this

/-- **PPT round trip** (T.800 A.7.5), up to relocation as `parsePPM_roundTrip`. -/
theorem parsePPT_roundTrip (src : ByteArray) (p : PPT) (hp : WFPPT src p) (st : Stage) :
    parsePPT (Reader.ofByteArray (serializePPT p src) st) =
        .ok { zppt := p.zppt, body := { offset := 1, length := p.body.length } } ∧
      ({ offset := 1, length := p.body.length } : ByteRange).bytes (serializePPT p src) =
        p.body.bytes src := by
  obtain ⟨hl, hne, hpk⟩ := range_bytes_list src p.body hp
  have := parsePPT_rd p.zppt _ hne _ (rd_ofByteArray (pptBytes p src) st)
  simp only [hl, hpk] at this
  exact this

end JPEG2000.Spec.TilePartRoundTrip
