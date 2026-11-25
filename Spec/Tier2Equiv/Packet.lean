import Spec.Tier2Equiv.Body

/-!
# Tier-2 equivalence: one packet
(Plan.md §4 C9, §5.1, §5.2 "Tier-2"; T.800 B.9, B.10, A.8.1, A.8.2)

Task 7.1b. Big-endian reads take two bytes of the reader's list (`u16be_rbytes`); the
optional `SOP` and the `EPH` marker follow the spec (`readSop_sim`, `readEph_sim`); and a whole
packet — `SOP`, header bits from the un-stuffed header stream (layers (a)–(c)), the header's
byte length by `alignedLength` (`align_sim`), `EPH`, body (layer (e)) — follows the spec
`packet` (`decodePacket_sim`), with the header and body streams shared (`same`) or separate
(packed packet headers).
-/

namespace JPEG2000.Spec.Tier2Equiv

open JPEG2000 JPEG2000.Bytes JPEG2000.TilePart JPEG2000.Spec.Tier2 JPEG2000.Tier2.Packet

/-- The value of two big-endian bytes. -/
theorem u16_toNat (a b : UInt8) :
    ((a.toUInt16 <<< 8) ||| b.toUInt16).toNat = a.toNat * 256 + b.toNat := by
  rw [UInt16.toNat_or, UInt16.toNat_shiftLeft]
  have h8 : (8 : UInt16).toNat % 16 = 8 := rfl
  rw [h8, UInt8.toNat_toUInt16, UInt8.toNat_toUInt16]
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  rw [Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
  rw [← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt (by simpa using hb), Nat.shiftLeft_eq]

/-- A big-endian 16-bit read takes two bytes of the list (or fails with fewer than two). -/
theorem u16be_rbytes (r : Reader) :
    match r.u16be with
    | .ok (v, r') => ∃ a b, rbytes r = a :: b :: rbytes r' ∧ v.toNat = a.toNat * 256 + b.toNat ∧
        r'.data = r.data ∧ r'.stop = r.stop
    | .error _ => (rbytes r).length < 2 := by
  have hs := r.stop_le
  by_cases h : r.pos + 2 ≤ r.stop
  · have e : r.u16be = .ok (((r.data.get r.pos (by omega)).toUInt16 <<< 8) |||
        (r.data.get (r.pos + 1) (by omega)).toUInt16, { r with pos := r.pos + 2, pos_le := h }) := by
      simp only [Reader.u16be, h, ↓reduceDIte]
    rw [e]
    refine ⟨r.data.get r.pos (by omega), r.data.get (r.pos + 1) (by omega), ?_, u16_toNat _ _, rfl, rfl⟩
    simp only [rbytes]
    rw [bytesFrom_cons (by omega) hs, bytesFrom_cons (by omega) hs, get_eq_data, get_eq_data]
  · have e : ∃ er, r.u16be = .error er := by simp only [Reader.u16be, h, ↓reduceDIte]; exact ⟨_, rfl⟩
    obtain ⟨er, e⟩ := e
    rw [e]
    show (rbytes r).length < 2
    rw [length_rbytes]; have := r.pos_le; omega

/-- A 16-bit value read from bytes `a b` equals `c` exactly when `a, b` are the bytes of `c`. -/
theorem marker_eq (m : UInt16) (a b : UInt8) (hv : m.toNat = a.toNat * 256 + b.toNat) (c : Nat)
    (hc : c < 65536) : (m == UInt16.ofNat c) = decide (a.toNat = c / 256 ∧ b.toNat = c % 256) := by
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  have : (m == UInt16.ofNat c) = decide (m.toNat = c) := by
    by_cases h : m.toNat = c
    · have : m = UInt16.ofNat c := UInt16.toNat_inj.mp (by rw [h]; simp; omega)
      rw [this]; simp; omega
    · have : m ≠ UInt16.ofNat c := fun e => h (by rw [e]; simp; omega)
      simp [this, h]
  rw [this, hv]
  by_cases h : a.toNat = c / 256 ∧ b.toNat = c % 256 <;> simp only [h, decide_false] <;>
    simp <;> omega

/-- **A.8.1**: the optional `SOP` follows the spec. -/
theorem readSop_sim (seq : Nat) (r : Reader) :
    Res (fun (x : Bool × Reader) (y : List UInt8) => y = rbytes x.2 ∧ x.2.data = r.data ∧ x.2.stop = r.stop)
      (JPEG2000.Tier2.Packet.readSop seq r) (Spec.Tier2.readSop seq (rbytes r)) := by
  have h1 := u16be_rbytes r
  unfold JPEG2000.Tier2.Packet.readSop
  revert h1
  cases r.u16be with
  | error e =>
    intro hl
    show Res _ (.ok (false, r)) _
    rcases hr : rbytes r with _ | ⟨x, _ | ⟨y, t⟩⟩
    · exact ⟨hr.symm, rfl, rfl⟩
    · exact ⟨hr.symm, rfl, rfl⟩
    · rw [hr] at hl; simp at hl; omega
  | ok p =>
    obtain ⟨m, r1⟩ := p
    intro ⟨a, b, hl, hv, hd, hs⟩
    dsimp only
    rw [hl]
    have hm := marker_eq m a b hv 0xFF91 (by decide)
    have hab : (a = 0xFF ∧ b = 0x91) ↔ (a.toNat = 0xFF91 / 256 ∧ b.toNat = 0xFF91 % 256) := by
      constructor
      · rintro ⟨rfl, rfl⟩; decide
      · rintro ⟨h1, h2⟩; exact ⟨UInt8.toNat_inj.mp (by rw [h1]; rfl), UInt8.toNat_inj.mp (by rw [h2]; rfl)⟩
    by_cases hc : a = 0xFF ∧ b = 0x91
    · have hm' : (m == 0xFF91) = true := by
        rw [show (0xFF91 : UInt16) = UInt16.ofNat 0xFF91 from rfl, hm]; simpa using hab.mp hc
      simp only [hm', ↓reduceIte, Spec.Tier2.readSop, hc, and_self]
      have h2 := u16be_rbytes r1
      revert h2
      cases r1.u16be with
      | error e =>
        intro hl1
        rcases hr : rbytes r1 with _ | ⟨x, _ | ⟨y, t⟩⟩
        · exact Res.error _ _
        · exact Res.error _ _
        · rw [hr] at hl1; simp at hl1; omega
      | ok p2 =>
        obtain ⟨lsop, r2⟩ := p2
        intro ⟨c1, c2, hl2, hv2, hd2, hs2⟩
        rw [hl2]
        simp only [ok_bind]
        have h3 := u16be_rbytes r2
        by_cases h4 : lsop != 4
        · have h4' : (c1.toNat * 256 + c2.toNat != 4) = true := by
            rw [← hv2]; simp only [bne_iff_ne, ne_eq] at h4 ⊢
            intro e; exact h4 (UInt16.toNat_inj.mp (by rw [e]; rfl))
          simp only [h4, ↓reduceIte]
          rcases hr : rbytes r2 with _ | ⟨x, _ | ⟨y, t⟩⟩ <;> simp only [h4', ↓reduceIte] <;>
            exact Res.error _ _
        · have h4' : (c1.toNat * 256 + c2.toNat != 4) = false := by
            have e4 : lsop = 4 := by simpa using h4
            rw [← hv2, e4]; rfl
          simp only [h4, Bool.false_eq_true, ↓reduceIte]
          revert h3
          cases r2.u16be with
          | error e =>
            intro hl3
            rcases hr : rbytes r2 with _ | ⟨x, _ | ⟨y, t⟩⟩
            · exact Res.error _ _
            · exact Res.error _ _
            · rw [hr] at hl3; simp at hl3; omega
          | ok p3 =>
            obtain ⟨nsop, r3⟩ := p3
            intro ⟨d1, d2, hl3, hv3, hd3, hs3⟩
            rw [hl3]
            simp only [ok_bind, h4', Bool.false_eq_true, ↓reduceIte]
            by_cases h5 : nsop.toNat != seq % 65536
            · have h5' : (d1.toNat * 256 + d2.toNat != seq % 65536) = true := by rw [← hv3]; exact h5
              simp only [h5, h5', ↓reduceIte]; exact Res.error _ _
            · have h5' : (d1.toNat * 256 + d2.toNat != seq % 65536) = false := by
                rw [← hv3]; simpa using h5
              simp only [h5, h5', Bool.false_eq_true, ↓reduceIte]
              exact ⟨rfl, hd3.trans (hd2.trans hd), hs3.trans (hs2.trans hs)⟩
    · have hm' : (m == 0xFF91) = false := by
        rw [show (0xFF91 : UInt16) = UInt16.ofNat 0xFF91 from rfl, hm]
        simp only [decide_eq_false_iff_not]; exact fun h => hc (hab.mpr h)
      simp only [hm', Bool.false_eq_true, ↓reduceIte, Spec.Tier2.readSop, hc]
      exact ⟨hl.symm, rfl, rfl⟩

/-- **A.8.2**: the `EPH` marker follows the spec. -/
theorem readEph_sim (r : Reader) :
    Res (fun (x : Reader) (y : List UInt8) => y = rbytes x ∧ x.data = r.data ∧ x.stop = r.stop)
      (JPEG2000.Tier2.Packet.readEph r) (Spec.Tier2.readEph (rbytes r)) := by
  have h1 := u16be_rbytes r
  unfold JPEG2000.Tier2.Packet.readEph
  revert h1
  cases r.u16be with
  | error e =>
    intro hl
    rcases hr : rbytes r with _ | ⟨x, _ | ⟨y, t⟩⟩
    · exact Res.error _ _
    · exact Res.error _ _
    · rw [hr] at hl; simp at hl; omega
  | ok p =>
    obtain ⟨m, r1⟩ := p
    intro ⟨a, b, hl, hv, hd, hs⟩
    rw [hl]
    simp only [ok_bind, Spec.Tier2.readEph]
    have hm := marker_eq m a b hv 0xFF92 (by decide)
    have hab : (a = 0xFF ∧ b = 0x92) ↔ (a.toNat = 0xFF92 / 256 ∧ b.toNat = 0xFF92 % 256) := by
      constructor
      · rintro ⟨rfl, rfl⟩; decide
      · rintro ⟨h1, h2⟩; exact ⟨UInt8.toNat_inj.mp (by rw [h1]; rfl), UInt8.toNat_inj.mp (by rw [h2]; rfl)⟩
    by_cases hc : a = 0xFF ∧ b = 0x92
    · have hm' : (m != 0xFF92) = false := by
        rw [show (0xFF92 : UInt16) = UInt16.ofNat 0xFF92 from rfl, bne, hm]; simpa using hab.mp hc
      simp only [hm', Bool.false_eq_true, ↓reduceIte, hc, and_self]
      exact ⟨rfl, hd, hs⟩
    · have hm' : (m != 0xFF92) = true := by
        rw [show (0xFF92 : UInt16) = UInt16.ofNat 0xFF92 from rfl, bne, hm]
        simp only [Bool.not_eq_true', decide_eq_false_iff_not]; exact fun h => hc (hab.mpr h)
      simp only [hm', ↓reduceIte, hc]
      exact Res.error _ _

/-- Merging a bind out of both branches of an `if`. -/
theorem ite_bind' {α β : Type} (c : Prop) [Decidable c] (x y : Except Error α) (f : α → Except Error β) :
    (if c then x >>= f else y >>= f) = (if c then x else y) >>= f := by
  split <;> rfl

/-- The result relation of one packet. -/
def PRel (buf : ByteArray) (same : Bool) (hdr body : Reader) (x : PrecState × PacketInfo × Reader × Reader)
    (y : PrecSt × Nat × List UInt8 × List UInt8) : Prop :=
  PrecRel buf x.1 y.1 ∧ x.2.1.newPasses = y.2.1 ∧ y.2.2.1 = rbytes x.2.2.1 ∧ y.2.2.2 = rbytes x.2.2.2 ∧
  x.2.2.2.data = buf ∧ x.2.2.2.stop = body.stop ∧
  (same = false → x.2.2.1.data = hdr.data ∧ x.2.2.1.stop = hdr.stop) ∧
  (same = true → x.2.2.1 = x.2.2.2)

/-- The optional `SOP` step of a packet (A.8.1). -/
theorem sop_step (sop : Bool) (seq : Nat) (body : Reader) :
    Res (fun (x : Bool × Reader) (y : List UInt8) => y = rbytes x.2 ∧ x.2.data = body.data ∧ x.2.stop = body.stop)
      (if sop then JPEG2000.Tier2.Packet.readSop seq body else pure (false, body))
      (if sop then Spec.Tier2.readSop seq (rbytes body) else pure (rbytes body)) := by
  cases sop
  · exact ⟨rfl, rfl, rfl⟩
  · exact readSop_sim seq body

/-- The optional `EPH` step of a packet (A.8.2). -/
theorem eph_step (eph : Bool) (hdr : Reader) :
    Res (fun (x : Reader) (y : List UInt8) => y = rbytes x ∧ x.data = hdr.data ∧ x.stop = hdr.stop)
      (if eph then JPEG2000.Tier2.Packet.readEph hdr else pure hdr)
      (if eph then Spec.Tier2.readEph (rbytes hdr) else pure (rbytes hdr)) := by
  cases eph
  · exact ⟨rfl, rfl, rfl⟩
  · exact readEph_sim hdr

/-- The header step of a packet: the bands when the "non-empty" bit is set (B.10.3). -/
theorem hdr_step {I : BitReader → Prop} (hI : BitSim I) (buf : ByteArray) (L : Limits) (layer : Nat)
    (ne : Bool) (fp : PrecState) (sp : PrecSt) (hR : PrecRel buf fp sp) (br : BitReader) (hb : I br) :
    Res (fun (x : PrecState × Array Contribution × BitReader) (y : List BandSt × List Contribution × List Bool) =>
        PrecRel buf x.1 { sp with bands := y.1 } ∧ x.2.1.toList = y.2.1 ∧ y.2.2 = rem x.2.2 ∧ I x.2.2)
      (if ne = true then headerBands L layer fp br else pure (fp, #[], br))
      (if ne = true then bandsHeader L sp.style layer 0 sp.bands (rem br) else pure (sp.bands, [], rem br)) := by
  cases ne
  · exact ⟨hR, rfl, rfl, hb⟩
  · exact headerBands_sim hI buf L layer fp sp hR br hb

/-- **One packet** (B.9, B.10, A.8): `decodePacket` follows the spec `packet`. -/
theorem decodePacket_sim (buf : ByteArray) (L : Limits) (sop eph : Bool) (seq layer : Nat)
    (fp : PrecState) (sp : PrecSt) (hR : PrecRel buf fp sp) (same : Bool) (hdr body : Reader)
    (hd : body.data = buf) :
    Res (PRel buf same hdr body) (decodePacket L sop eph seq layer fp same hdr body)
      (packet L sop eph seq layer sp same (rbytes hdr) (rbytes body)) := by
  unfold decodePacket packet
  dsimp only
  simp only [ite_bind']
  refine Res.bind (sop_step sop seq body) fun ⟨hs, body1⟩ l1 ⟨hl1, hd1, hs1⟩ => ?_
  dsimp only at hl1 hd1 hs1 ⊢
  subst hl1
  have hrb : (if same = true then rbytes body1 else rbytes hdr) = rbytes (if same = true then body1 else hdr) := by
    split <;> rfl
  have hHd : (if same = true then body1 else hdr).data = (if same = true then body.data else hdr.data) := by
    split
    · exact hd1
    · rfl
  have hHs : (if same = true then body1 else hdr).stop = (if same = true then body.stop else hdr.stop) := by
    split
    · exact hs1
    · rfl
  rw [hrb]
  generalize (if same = true then body1 else hdr) = H at hHd hHs ⊢
  obtain ⟨hInv, hrem⟩ := ofReader_inv H
  have hrem' : rem (BitReader.ofReader H) = unstuff (rbytes H) := hrem
  rw [← hrem']
  have hsim := inv_sim H.pos H.data H.stop
  refine Res.bind (Res.ofFol (readBit_sim hsim _ hInv)) fun ⟨ne, br⟩ ⟨ne', rest⟩ ⟨hne, hrest, hbr⟩ => ?_
  dsimp only at hne hrest hbr ⊢
  subst hne hrest
  refine Res.bind (hdr_step hsim buf L layer ne fp sp hR br hbr)
    fun ⟨st1, cs, br1⟩ ⟨bands, cs', rest⟩ ⟨hP, hcs, hrest, hI1⟩ => ?_
  dsimp only at hP hcs hrest hI1 ⊢
  subst hrest hcs
  rw [hrem']
  have hal := align_sim hI1
  revert hal
  cases br1.align with
  | error e =>
    intro hal
    rw [show bytesFrom H.data H.pos H.stop = rbytes H from rfl] at hal
    rw [hal]; exact Res.error _ _
  | ok b' =>
    intro ⟨hal, hbd, hbs, hbp⟩
    rw [show bytesFrom H.data H.pos H.stop = rbytes H from rfl] at hal
    rw [hal]
    simp only [ok_bind]
    have hdrop : (rbytes H).drop (b'.pos - H.pos) = rbytes (b'.toReader .tier2) := by
      simp only [rbytes, BitReader.toReader, ← bytesFrom_add, hbd, hbs]
      congr 1; omega
    rw [hdrop]
    refine Res.bind (eph_step eph (b'.toReader .tier2)) fun hdr3 l3 ⟨hl3, hd3, hs3⟩ => ?_
    subst hl3
    have hrb2 : (if same = true then rbytes hdr3 else rbytes body1) =
        rbytes (if same = true then hdr3 else body1) := by split <;> rfl
    rw [hrb2]
    have hd2 : (if same = true then hdr3 else body1).data = buf := by
      split
      · rename_i hsm
        simp only [hsm, ↓reduceIte] at hHd
        rw [hd3]; show b'.data = buf
        rw [hbd, hHd, hd]
      · rw [hd1, hd]
    refine Res.bind (readBody_sim buf st1 { style := sp.style, bands := bands } hP cs _ hd2)
      fun ⟨st2, body3⟩ ⟨sst, l4⟩ ⟨hP2, hl4, hd4, hs4⟩ => ?_
    dsimp only at hP2 hl4 hd4 hs4 ⊢
    subst hl4
    refine ⟨hP2, ?_, ?_, rfl, hd4, ?_, ?_, ?_⟩
    · simp only [newPasses, Array.foldl_toList]
    · split <;> rfl
    · rw [hs4]
      split
      · rename_i hsm
        simp only [hsm, ↓reduceIte] at hHs
        rw [hs3]; show b'.stop = body.stop
        rw [hbs, hHs]
      · exact hs1
    · intro hsm
      simp only [hsm, Bool.false_eq_true, ↓reduceIte] at hHd hHs ⊢
      exact ⟨by rw [hd3]; show b'.data = hdr.data; rw [hbd, hHd],
        by rw [hs3]; show b'.stop = hdr.stop; rw [hbs, hHs]⟩
    · intro hsm
      simp only [hsm, ↓reduceIte]

end JPEG2000.Spec.Tier2Equiv
