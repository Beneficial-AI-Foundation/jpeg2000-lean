import Spec.RoundTrip.PacketBlocks

/-!
# Codeword bounds for the reversible encoder

Plan.md §§4, 5.3, 7 (C10, M7). T.800 A.4.2, B.10.5–B.10.8 and E.1.
An included block's bytes occur in the body of its LRCP packet. The containing
tile-part passes the encoder's Psot check, and its QCD fields bound the number
of coded planes admitted by Tier-1.
-/

namespace JPEG2000.Spec.RoundTrip

open JPEG2000.Encode (Params Image Encoded encodeDetailed)
open JPEG2000.Encode.Tier2 (BandIn encodePacket packetBody encodeTileLRCP)
open JPEG2000.Encode.Tier1 (numBits maxMag)
open JPEG2000.Progression (PacketId)
open JPEG2000.Spec.Progression (packets)
open JPEG2000.Tier2.Packet (bandMb)

private theorem length_le_flatMap {α β : Type} {xs : List α} {x : α} (hx : x ∈ xs)
    (f : α → List β) : (f x).length ≤ (xs.flatMap f).length :=
  (List.sublist_flatten_of_mem (List.mem_map.mpr ⟨x, hx, rfl⟩)).length_le

/-- An included codeword fits in its packet, including when another band has no blocks. -/
theorem included_size_le_packet {bands : Array BandIn} {b : BandIn} (hb : b ∈ bands)
    {k : Nat} (hk : k < b.blocks.size) (hinc : (b.blocks.getD k default).numPasses ≠ 0) :
    (b.blocks.getD k default).data.size ≤ (encodePacket bands).size := by
  have hblock := length_le_flatMap (List.mem_range.mpr hk) (blockBody b)
  have hband := length_le_flatMap (Array.mem_toList_iff.mpr hb)
    (fun a => (List.range a.blocks.size).flatMap (blockBody a))
  have hbody : (b.blocks.getD k default).data.size ≤ (packetBody bands).size := by
    change _ ≤ (packetBody bands).data.toList.length
    rw [packetBody_toList]
    simpa only [bodyAll, blockBody, ite_eq_right hinc, Array.length_toList, ByteArray.size_data]
      using Nat.le_trans hblock hband
  rw [encodePacket, ByteArray.size_append]
  omega

/-- Each packet in the encoder layout contributes its bytes to the serialized tile. -/
theorem ReversibleTilePackets.packet_size_le_tile {p : Params} {img : Image} {e : Encoded}
    {prec infos} (hp : ReversibleTilePackets p img e prec infos) {q : PacketId}
    (hq : (encLayout p img e.guardBits e.exponents).InPacketSet q) :
    (encodePacket (encBands prec q)).size ≤ (encodeTileLRCP prec).size := by
  let g := encLayout p img e.guardBits e.exponents
  have hwf := encLayout_wf p img e.guardBits e.exponents
  have hm : q ∈ packets g .lrcp #[] := by
    rw [Spec.Progression.packets_noPoc hwf]
    exact ((Spec.Progression.c5 hwf _).2 q).mpr hq
  change _ ≤ (encodeTileLRCP prec).data.toList.length
  rw [encodeTileLRCP_eq g hwf rfl prec hp.tileShape]
  exact length_le_flatMap hm (fun t => (encodePacket (encBands prec t)).data.toList)

/-- The reversible encoder writes two guard bits and band exponents at most 31.
A successful Tier-1 call therefore fits the 37-plane plain-segment budget. -/
theorem PacketBlockCall.planes_le_37 {p : Params} {img : Image} {e : Encoded}
    (he : encodeDetailed p img = .ok e) (hrev : p.reversible = true)
    {L bands r pr bi k pb cb o}
    (call : PacketBlockCall L (encGeom p img e.guardBits e.exponents) bands r pr bi k pb cb o) :
    numBits (maxMag (packetBlockCoeffs bands r bi cb)) ≤ 37 := by
  have hs := encodeDetailed_shape he
  let params := encParams p e.guardBits e.exponents
  have hstep (i : Nat) : (params.steps.getD i default).exponent.toNat ≤ 31 := by
    cases hi : e.exponents[i]? with
    | none => simp [params, encParams, Array.getD_eq_getD_getElem?, hi]; decide
    | some exp =>
      have hle := hs.exps_le exp (Array.mem_toList_iff.mpr (Array.mem_iff_getElem?.mpr ⟨i, hi⟩))
      simp [params, encParams, Array.getD_eq_getD_getElem?, hi,
        Nat.mod_eq_of_lt (show exp < 256 by omega), hle]
  obtain ⟨hc, hz, _⟩ := encodeCodeBlock_counts call.encoded
  change o.zeroBitPlanes + o.codedPlanes = bandMb params r pb.band at hz
  unfold bandMb at hz
  have hg : params.guardBits = 2 := hs.guard_rev hrev
  rw [hg] at hz
  dsimp only at hz
  have := hstep (if r = 0 then 0 else 3 * (r - 1) + pb.band.index)
  omega

/-- The per-packet block premise of `decodeTile_encodeDetailed` follows from
successful reversible encoding and the decoder's per-block pass allowance. -/
theorem encodeDetailed_packetBlockOK {p : Params} {img : Image} {e : Encoded}
    (he : encodeDetailed p img = .ok e) (hrev : p.reversible = true)
    {L : Limits} (hlim : 109 ≤ L.maxPassesPerCodeBlock)
    {prec infos} (hp : ReversibleTilePackets p img e prec infos) (q : PacketId)
    (hq : (encLayout p img e.guardBits e.exponents).InPacketSet q) :
    ∀ b ∈ encBands prec q, ∀ k < b.blocks.size, BlockOK L b.maxZero (b.blocks.getD k default) := by
  intro b hb k hk
  obtain ⟨bi, hbi⟩ := Array.mem_iff_getElem?.mp hb
  have hx : b.blocks[k]? = some (b.blocks.getD k default) := by simp [Array.getD, hk]
  obtain ⟨pb, cb, o, call, hz, hblk⟩ := hp.packetBlock hq hbi hx
  rw [hz, hblk]
  apply blockOK_encodeCodeBlock call.encoded (call.planes_le_37 he hrev) hlim
  intro hinc
  have hsize := included_size_le_packet hb hk (hblk ▸ hinc)
  rw [hblk] at hsize
  change o.bytes.length ≤ _ at hsize
  have ht := hp.packet_size_le_tile hq
  have hpsot := hp.psot
  omega

end JPEG2000.Spec.RoundTrip
