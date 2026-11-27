import Spec.Tier2Equiv.Tile
import Spec.Equiv

/-!
# Tier-2: the fast packet decoder equals the B.10 specification
(Plan.md §4 C9, §5.1, §5.2 "Tier-2"; T.800 B.9–B.12, B.10.1–B.10.8, A.7.4–A.7.5, A.8)

Task 7.1b. The equivalence of `JPEG2000.Tier2.Headers.decodeWithStream` (fast: bit reader
over a `ByteArray`, flat-array tag trees, segments as range lists) and
`Spec.Tier2.decodeWithStream` (spec: header bits as the un-stuffed bit list, tag trees
`Spec.TagTree`, segments as byte lists), built in layers:

| layer | file | key results |
|---|---|---|
| (a) bit reader = un-stuffed bit list | `Spec/Tier2Equiv/Bits.lean` | `bit_rem`, `bits_sim`, `align_sim`, `ofReader_inv` |
| (b) tag trees over the bit reader | `Spec/Tier2Equiv/TagTree.lean` | `decode_spec`, `decodeValue_spec` |
| (c) packet header | `Spec/Tier2Equiv/Header.lean` | `headerBlock_sim`, `headerBands_sim`, `segmentPasses_eq` |
| (e) packet body | `Spec/Tier2Equiv/Body.lean` | `addPieces_eq`, `takePieces_sim`, `readBody_sim` |
| one packet (SOP/EPH) | `Spec/Tier2Equiv/Packet.lean` | `decodePacket_sim` |
| (d) a tile | `Spec/Tier2Equiv/Tile.lean` | `decodeTile_sim`, `decodeWithStream_sim` |

**`tier2_equiv`**: for a tile whose layout is well formed (`Layout.WF`: sub-sampling ≥ 1 and
B-12 tile-component rectangles, the hypothesis of `Spec.Progression.forPackets_eq_spec`), the
fast decoder and the spec both fail, or both succeed and the spec result is the image of the
fast one (`image`): per component, resolution, precinct and band the same labels, and per
code-block the same geometry, inclusion, `Lblock`, zero bit-planes and passes, each segment's
byte list being the bytes of the fast segment's ranges (`segOf`: `Segment.bytes` of the
input), and the same pass totals. The fast decoder never fails where the spec succeeds (no
`unsupported` case is needed).
-/

namespace JPEG2000.Spec.Tier2Equiv

open JPEG2000 JPEG2000.Header JPEG2000.Progression JPEG2000.Tier2.Packet

/-- `Res` (both fail, or both succeed related) implies the C9 relation `Spec.Equiv.ERel`. -/
theorem Res.toERel {X Y : Type} {P : X → Y → Prop} {x : Except Error X} {y : Except Error Y}
    (h : Res P x y) : Spec.Equiv.ERel P x y := by
  match x, y, h with
  | .error _, .error _, _ => trivial
  | .ok _, .ok _, hp => exact hp

/-- **Tier-2 fast = spec** (B.9–B.12, B.10, A.7.4–A.7.5, A.8): for a tile with a well-formed
layout, `Tier2.Headers.decodeWithStream` and `Spec.Tier2.decodeWithStream` both fail or both
succeed, the spec result being the image of the fast one with the same pass count. -/
theorem tier2_equiv (L : Limits) (h : Header) (data : ByteArray) (tp : TileParams)
    (hs : Option Tier2.Headers.HeaderStream) (n : Nat)
    (hwf : ∀ g c, Layout.ofHeader h tp.index = .ok (g, c) → g.WF) :
    Spec.Equiv.ERel (fun (t : TileCodeBlocks) (s : Spec.Tier2.TileOut) =>
        s.comps = image data t ∧ s.passes = t.passes)
      (Tier2.Headers.decodeWithStream L h data tp hs n) (Spec.Tier2.decodeWithStream L h data tp hs n) :=
  (decodeWithStream_sim L h data tp hs n hwf).toERel

/-- **Tier-2 fast = spec** for every header whose `SIZ` components have non-zero sub-sampling
(`XRsiz`, `YRsiz` ≥ 1, which `Marker` parsing of `SIZ` requires, A.5.1): `tier2_equiv` with
`Layout.WF` discharged by `ofHeader_wf`. -/
theorem tier2_equiv_of_siz (L : Limits) (h : Header) (data : ByteArray) (tp : TileParams)
    (hs : Option Tier2.Headers.HeaderStream) (n : Nat)
    (hd : ∀ comp ∈ h.siz.components.toList, comp.dx ≠ 0 ∧ comp.dy ≠ 0) :
    Spec.Equiv.ERel (fun (t : TileCodeBlocks) (s : Spec.Tier2.TileOut) =>
        s.comps = image data t ∧ s.passes = t.passes)
      (Tier2.Headers.decodeWithStream L h data tp hs n) (Spec.Tier2.decodeWithStream L h data tp hs n) :=
  tier2_equiv L h data tp hs n fun _ _ he => ofHeader_wf hd he

/-- The spec image of a fast code-block: its segments are the bytes of the fast segments'
ranges in the input (`Segment.bytes`), with their pass counts. -/
theorem blockOf_segs (data : ByteArray) (cb : CodeBlock) :
    (blockOf data cb).segs =
      cb.segments.toList.map fun s => { data := (s.bytes data).data.toList, passes := s.passes } :=
  rfl

end JPEG2000.Spec.Tier2Equiv
