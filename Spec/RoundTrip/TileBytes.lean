import Spec.RoundTrip.Header
import Spec.Tier2WF

/-!
# Packet bytes of the reversible encoder (Plan.md §§4, 5.3, 7, C10; T.800 A.4 and Annex B)

The encoder accumulates one Tier-2 input array per component. Its LRCP serialization is the
payload of the single tile-part. The decoder recovers it with one span mapping tile-buffer offset
zero to the first byte after SOD in the input.
-/

namespace JPEG2000.Spec.RoundTrip

open JPEG2000.Encode JPEG2000.Header JPEG2000.Tier2.Geometry

private abbrev PrecInputs := Array (Array (Array Encode.Tier2.BandIn))

/-- The LRCP input for each component and its block records, in encoder traversal order. -/
structure ReversibleTilePackets (p : Params) (img : Image) (e : Encoded)
    (prec : Array (Array (Array (Array Encode.Tier2.BandIn))))
    (infos : Array (Array BlockInfo)) : Prop where
  prec_size : prec.size = img.comps.size
  infos_size : infos.size = img.comps.size
  component : ∀ c, c < img.comps.size →
    encodeComp Limits.default
      (tileComp (encRect img) ((encSIZ img).components.getD c default)
        (encParams p e.guardBits e.exponents)) c
      ((bands53 p img (encMct p img)).getD c #[]) = .ok (prec.getD c #[], infos.getD c #[])
  blocks : e.blocks = infos.flatten
  psot : 14 + (Encode.Tier2.encodeTileLRCP prec).size < 2 ^ 32
  codestream : e.codestream =
    encCodestream p img e.guardBits e.exponents (Encode.Tier2.encodeTileLRCP prec)

private theorem componentLoop {n : Nat}
    (call : Nat → Except Error (PrecInputs × Array BlockInfo))
    {prec : Array PrecInputs} {blocks : Array BlockInfo}
    (h : forIn [0:n] ((#[] : Array PrecInputs), (#[] : Array BlockInfo)) (fun c st => do
        let result ← call c
        pure (.yield (st.1.push result.1, st.2 ++ result.2))) = .ok (prec, blocks)) :
    ∃ infos : Array (Array BlockInfo), prec.size = n ∧ infos.size = n ∧
      (∀ c, c < n → call c = .ok (prec.getD c #[], infos.getD c #[])) ∧
      blocks = infos.flatten := by
  let P (i : Nat) (st : Array PrecInputs × Array BlockInfo) :=
    ∃ infos : Array (Array BlockInfo), st.1.size = i ∧ infos.size = i ∧
      (∀ c, c < i → call c = .ok (st.1.getD c #[], infos.getD c #[])) ∧
      st.2 = infos.flatten
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at h
  have hn : [0:n].size = n := by simp [Std.Legacy.Range.size]
  rw [hn] at h
  suffices hinv : P (0 + n) (prec, blocks) by simpa [P] using hinv
  refine Spec.Tier2WF.forIn_range'_inv P _ ?_ n 0 _ _ ?_ h
  · intro i st r hi hr
    obtain ⟨infos, hp, hs, hc, hb⟩ := hi
    obtain ⟨⟨pc, ic⟩, hcall, hr⟩ := Spec.Tier2Equiv.bind_ok hr
    cases hr
    refine ⟨_, rfl, infos.push ic, by simpa using hp, by simpa using hs, ?_, ?_⟩
    · intro c hci
      by_cases he : c = i
      · subst c
        simpa only [Array.getD_eq_getD_getElem?, Array.getElem?_push, hp, hs, ite_true,
          Option.getD_some] using hcall
      · have hlt : c < i := by omega
        simpa only [Array.getD_eq_getD_getElem?, Array.getElem?_push, hp, hs, ite_eq_right he]
          using hc c hlt
    · simp [Array.flatten_push, hb]
  · exact ⟨#[], rfl, rfl, by simp, rfl⟩

/-- The reversible encoder serializes exactly the arrays returned by its successful component
calls, and retains their block records in the same order. -/
theorem encodeDetailed_tilePackets {p : Params} {img : Image} {e : Encoded}
    (he : encodeDetailed p img = .ok e) (hrev : p.reversible = true) :
    ∃ prec infos, ReversibleTilePackets p img e prec infos := by
  have hs := encodeDetailed_shape he
  have hc := checkFacts_of_ok hs.check
  have hm := mkComp_enc 0 p e.guardBits e.exponents hc.levels_le hc.cbw_ge hc.cbw_le
    hc.cbh_ge hc.cbh_le hs.guard_le hs.exps_size
  unfold encodeDetailed at he
  dsimp only at he
  obtain ⟨u, _, he⟩ := Spec.Tier2Equiv.bind_ok he
  cases u
  rw [hrev, ite_eq_left rfl, pure_bind] at he
  split at he
  · cases he
  split at he
  · cases he
  obtain ⟨params, hparams, he⟩ := Spec.Tier2Equiv.bind_ok he
  obtain ⟨st, hst, he⟩ := Spec.Tier2Equiv.bind_ok he
  split at he
  · cases he
  rename_i hps
  injection he with he
  subst e
  have hp : _ = params := Except.ok.inj (hm.symm.trans (by
    simpa [encStyle, encQCD, hrev] using hparams))
  subst params
  obtain ⟨infos, hp, hi, hcomp, hblocks⟩ := componentLoop _ hst
  exact ⟨_, infos, hp, hi, hcomp, hblocks, Nat.lt_of_not_ge hps, by
    simp [encCodestream, encSIZ, encCOD, encStyle, encQCD, encSOT, encMct, hrev]⟩

/-- The single tile-part contributes its entire payload and one span starting after SOD. -/
theorem tileData_encCodestream (p : Params) (img : Image) (guard : Nat) (exps : Array Nat)
    (data : ByteArray) :
    Tier2.Packet.tileData (encCodestream p img guard exps data)
        (encTile (encMainBytes p img guard exps).length data.size) =
      .ok (data, [(0, (encMainBytes p img guard exps).length + 14, data.size)]) := by
  have hstop : ¬ (encMainBytes p img guard exps).length + 14 + data.size >
      (encCodestream p img guard exps data).size := by
    rw [encCodestream_eq]
    change ¬ _ > (Encode.Marker.pack _).data.size
    simp [Encode.Marker.pack, encTailBytes, encSegBytes, Encode.Marker.be16,
      Encode.TilePart.sotBytes, Encode.Marker.be32]
    omega
  unfold Tier2.Packet.tileData
  dsimp only
  rw [← Array.forIn_toList]
  simp [encTile, encPart, JPEG2000.TilePart.ByteRange.stop, hstop, data_bytes, List.forIn_cons,
    bind, Except.bind, pure, Except.pure]

/-- Under the decoder's header limits, parsing a reversible stream and collecting its only
tile's data recovers the LRCP bytes of the successful component calls and their input span. -/
theorem parse_encodeDetailed_tileData (L : Limits) {p : Params} {img : Image} {e : Encoded}
    (he : encodeDetailed p img = .ok e) (hrev : p.reversible = true)
    (hL : HeaderFits L p img e.guardBits e.exponents e.codestream.size) :
    ∃ prec infos, ReversibleTilePackets p img e prec infos ∧
      let data := Encode.Tier2.encodeTileLRCP prec
      let hdr := encHeader p img e.guardBits e.exponents data
      Header.parse L e.codestream = .ok hdr ∧
        Tier2.Packet.tileData e.codestream (hdr.tiles[0]'(by simp [hdr, encHeader])).tile =
          .ok (data, [(0, (encMainBytes p img e.guardBits e.exponents).length + 14, data.size)]) := by
  obtain ⟨prec, infos, hp⟩ := encodeDetailed_tilePackets he hrev
  have hs := encodeDetailed_shape he
  refine ⟨prec, infos, hp, ?_⟩
  dsimp only
  rw [hp.codestream] at hL ⊢
  exact ⟨parse_encCodestream L p img _ _ _ (checkFacts_of_ok hs.check) hs.guard_le hs.exps_le
    hs.exps_size hp.psot hL, tileData_encCodestream _ _ _ _ _⟩

end JPEG2000.Spec.RoundTrip
