import Spec.Resources
import Spec.Resources.HeaderSort
import Spec.WideHeaderBounds
import Spec.Tier2WF

/-!
# Header traversal and gathering (Plan.md §4 S3, §7 M7)

T.800 A.3–A.7 (main header, tile-parts and packed headers), B.5–B.10
(resolutions, precincts and packet contributions), I.4–I.5 (JP2 boxes).
Fuel equivalences preserve the complete result, including the error on a rejecting
prefix. A unit of fuel counts one outer loop body. The cost of a segment parser,
sorting and arithmetic inside these bodies is separate.

The public parse theorems relate the checked geometry, main marker tables,
tile-part ranges and PPM/PPT selectors to input size and Limits. The charged
byte folds erase to the decoder operations, including the rejecting tile-data
case. Their unit is a byte written by extraction or append under full copying.
Geometry and tag-tree arrays are counted in entries. Descriptor gathering for a
Tier-1 block is parameterized by the number of ranges supplied by Tier-2.

The component-visit counter includes the check which first rejects. The module
does not bound the whole decoder, runtime allocation overhead, the inner work of
every segment parser or the aggregate cost of all geometry initialization on a
rejecting input.
-/

namespace JPEG2000.Spec.Resources.HeaderWork

open JPEG2000 JPEG2000.Bytes JPEG2000.Marker JPEG2000.TilePart JPEG2000.Header
open JPEG2000.Tier2.Packet

open JPEG2000.Spec.Tier2Equiv (bind_ok)

private theorem checked {L : Limits} {loc k n} {u : Unit} (h : L.check loc k n = .ok u) :
    n ≤ L.bound k := (Limits.check_eq_ok_iff L loc k n).1 h

/-- The length-bearing marker reader partitions the same buffer. Its body starts
after the length field and ends exactly where the next reader begins. -/
theorem readSegment_extent {r body next : Reader} {n : Nat}
    (h : readSegment r = .ok (body, n, next)) :
    body.data = r.data ∧ next.data = r.data ∧ body.pos = r.pos + 2 ∧
    body.stop = next.pos ∧ next.stop = r.stop ∧ next.pos = r.pos + n ∧ 2 ≤ n := by
  unfold readSegment at h
  obtain ⟨⟨len, mid⟩, hmid, h⟩ := bind_ok h
  obtain ⟨_, hlen, h⟩ := bind_ok h
  obtain ⟨⟨sub, tail⟩, ht, h⟩ := bind_ok h
  cases h
  have hm := Reader.u16be_pos hmid
  have hs := Reader.take_spec ht
  unfold require at hlen
  split at hlen
  · rename_i hl
    have hn : 2 ≤ len.toNat := by simpa [UInt16.le_iff_toNat_le] using hl
    exact ⟨hs.2.2.1.trans hm.2.2.1, hs.2.2.2.2.2.2.trans hm.2.2.1, by omega,
      by omega, by omega, by omega, hn⟩
  · cases hlen

private theorem more16 {r t : Reader} {m : UInt16} (e : r.u16be = .ok (m,t)) :
    t.remaining + 2 ≤ r.remaining := by
  have := Reader.u16be_pos e
  have := t.pos_le
  simp only [Reader.remaining]
  omega

private theorem moreSeg {r b t : Reader} {n : Nat} (e : readSegment r = .ok (b,n,t)) :
    t.remaining + 2 ≤ r.remaining := by
  have := readSegment_extent e
  have := t.pos_le
  simp only [Reader.remaining]
  omega

/-- Two fuels above the byte budget give identical main-header results, including
rejection. The extra visit may peek SOT, reject a marker or encounter truncation. -/
theorem segmentLoop_fuel (L : Limits) (csiz f g : Nat) (a : Acc) (r : Reader)
    (hf : r.remaining / 2 < f) (hg : r.remaining / 2 < g) :
    segmentLoop L csiz f a r = segmentLoop L csiz g a r := by
  induction f generalizing g a r with
  | zero => omega
  | succ f ih =>
    cases g with
    | zero => omega
    | succ g =>
      simp only [segmentLoop]
      split
      · rfl
      · rename_i m r1 e
        have h1 := more16 e
        split <;> first | rfl | skip
        split <;> first | rfl | skip
        split
        · apply ih <;> omega
        · split <;> first | rfl | skip
          split
          · rfl
          · rename_i body len r2 es
            have := moreSeg es
            split
            · rfl
            · apply ih <;> omega

/-- Tile-part header marker visits have the same byte budget. The SOD marker is
consumed by the terminal visit. -/
theorem tileHeaderLoop_fuel (L : Limits) (csiz : Nat) (first ppm : Bool) (f g : Nat)
    (a : TPAcc) (r : Reader) (hf : r.remaining / 2 < f) (hg : r.remaining / 2 < g) :
    TilePart.headerLoop L csiz first ppm f a r = TilePart.headerLoop L csiz first ppm g a r := by
  induction f generalizing g a r with
  | zero => omega
  | succ f ih =>
    cases g with
    | zero => omega
    | succ g =>
      simp only [TilePart.headerLoop]
      split
      · rfl
      · rename_i m r1 e
        have h1 := more16 e
        split <;> first | rfl | skip
        split <;> first | rfl | skip
        split
        · apply ih <;> omega
        · split <;> first | rfl | skip
          split
          · rfl
          · rename_i body len r2 es
            have := moreSeg es
            split
            · rfl
            · apply ih <;> omega

/-- Every admitted tile-part grows the checked total by one, checks its own tile's
part count, and advances the outer reader in the same buffer. -/
theorem readTilePart_step {c : Ctx} {st st' : State} {r t : Reader}
    (ok : readTilePart c st r = .ok (st', t)) :
    st'.total = st.total + 1 ∧ st'.total ≤ c.limits.maxTileParts ∧
    t.remaining + 4 ≤ r.remaining ∧ t.data = r.data ∧
    ∃ i : Nat, (st.parts[i]?.getD #[]).size + 1 ≤ c.limits.maxTilePartsPerTile := by
  unfold readTilePart at ok
  obtain ⟨⟨m,r1⟩, h1, ok⟩ := bind_ok ok
  obtain ⟨⟨body,n,r2⟩, h2, ok⟩ := bind_ok ok
  obtain ⟨sot, _, ok⟩ := bind_ok ok
  obtain ⟨_, _, ok⟩ := bind_ok ok
  obtain ⟨_, htot, ok⟩ := bind_ok ok
  obtain ⟨_, hpart, ok⟩ := bind_ok ok
  obtain ⟨_, _, ok⟩ := bind_ok ok
  obtain ⟨_, _, ok⟩ := bind_ok ok
  obtain ⟨_, _, ok⟩ := bind_ok ok
  dsimp only at ok
  split at ok <;> split at ok <;> try contradiction
  all_goals
    simp only [pure_bind] at ok
    obtain ⟨⟨tp, next⟩, ht, ok⟩ := bind_ok ok
    obtain ⟨⟨acc,rd⟩, _, ok⟩ := bind_ok ok
    cases ok
    have h := Reader.take_spec ht
    have h12 := Reader.u16be_pos h1
    have h23 := readSegment_extent h2
    have := next.pos_le
    exact ⟨rfl, checked htot, by dsimp only [Reader.remaining]; omega,
      h.2.2.2.2.2.2.trans (h23.2.1.trans h12.2.2.1), _, checked hpart⟩

/-- The outer tile-part traversal admits both an input-byte and a checked-count fuel
cap. One further iteration can report excess, malformed data, truncation or EOC. -/
theorem tilePartLoop_fuel (c : Ctx) (f g : Nat) (a : State) (r : Reader)
    (hf : min (r.remaining / 4) (c.limits.maxTileParts - a.total) < f)
    (hg : min (r.remaining / 4) (c.limits.maxTileParts - a.total) < g) :
    tilePartLoop c f a r = tilePartLoop c g a r := by
  induction f generalizing g a r with
  | zero => omega
  | succ f ih =>
    cases g with
    | zero => omega
    | succ g =>
      simp only [tilePartLoop]
      split <;> first | rfl | skip
      split <;> first | rfl | skip
      split <;> first | rfl | skip
      split
      · rfl
      · rename_i a' t e
        obtain ⟨hs,hl,hr,-⟩ := readTilePart_step e
        apply ih <;> omega

/-- The JP2 length field, including its extended and to-end encodings, describes
a borrowed subreader. Sibling boxes advance by at least eight bytes. -/
theorem readBox_extent {r t : Reader} {b : Box.BoxHdr} (ok : Box.readBox r = .ok (b,t)) :
    b.start = r.pos ∧ b.body.data = r.data ∧ t.data = r.data ∧
    r.pos + 8 ≤ b.body.pos ∧ b.body.stop = t.pos ∧ t.stop = r.stop := by
  unfold Box.readBox at ok
  obtain ⟨⟨l,r1⟩,h1,ok⟩ := bind_ok ok
  obtain ⟨⟨ty,r2⟩,h2,ok⟩ := bind_ok ok
  have p1 := Reader.u32be_pos h1
  have p2 := Reader.u32be_pos h2
  dsimp only at ok
  have finish {a : Reader} {n : Nat} (pa : r.pos + 8 ≤ a.pos)
      (sa : a.stop = r.stop) (da : a.data = r.data)
      (ok : (match a.take n with
        | .ok (sub,t') => Except.ok ((⟨ty, r.pos, sub⟩ : Box.BoxHdr), t')
        | .error _ => Except.error (Error.truncated (.atOffset .box r.pos)
            s!"box '{Box.typeName ty}' body of {n} bytes, {a.remaining} left")) = .ok (b,t)) :
      b.start = r.pos ∧ b.body.data = r.data ∧ t.data = r.data ∧
        r.pos + 8 ≤ b.body.pos ∧ b.body.stop = t.pos ∧ t.stop = r.stop := by
    split at ok
    · rename_i sub next ht
      cases ok
      have hs := Reader.take_spec ht
      dsimp only
      exact ⟨rfl, hs.2.2.1.trans da, hs.2.2.2.2.2.2.trans da, by omega, by omega, by omega⟩
    · cases ok
  split at ok
  · exact finish (by omega) (by omega) (p2.2.2.1.trans p1.2.2.1) ok
  · split at ok
    · obtain ⟨⟨xl,r3⟩,h3,ok⟩ := bind_ok ok
      have p3 := Reader.u64be_pos h3
      dsimp only at ok
      split at ok
      · cases ok
      · exact finish (by omega) (by omega) (p3.2.2.1.trans (p2.2.2.1.trans p1.2.2.1)) ok
    · split at ok
      · cases ok
      · exact finish (by omega) (by omega) (p2.2.2.1.trans p1.2.2.1) ok

private theorem box_consumes {r t : Reader} {b : Box.BoxHdr} (ok : Box.readBox r = .ok (b,t)) :
    t.remaining + 8 ≤ r.remaining := by
  have := readBox_extent ok
  have := b.body.pos_le
  have := t.pos_le
  unfold Reader.remaining
  omega

private theorem box_count {L : Limits} {r : Reader} {a b : Box.HdrAcc} {i j f : Nat}
    (h : Box.headerLoop L r a i f = .ok (b,j)) : i ≤ j := by
  induction f generalizing r a i with
  | zero => simp only [Box.headerLoop] at h; split at h <;> cases h; exact Nat.le_refl _
  | succ f ih =>
    simp only [Box.headerLoop] at h
    split at h
    · cases h; exact Nat.le_refl _
    · obtain ⟨_,_,h⟩ := bind_ok h
      obtain ⟨⟨_,_⟩,_,h⟩ := bind_ok h
      obtain ⟨_,_,h⟩ := bind_ok h
      have := ih h
      omega

private theorem jp2h_count {L : Limits} {b : Box.BoxHdr} {h : Box.Jp2Header} {i j : Nat}
    (ok : Box.parseJp2h L b i = .ok (h,j)) : i ≤ j ∧ 1 ≤ L.maxBoxDepth := by
  unfold Box.parseJp2h at ok
  obtain ⟨_,depth,ok⟩ := bind_ok ok
  obtain ⟨⟨acc,k⟩,hk,ok⟩ := bind_ok ok
  have := box_count hk
  dsimp only at ok
  repeat' first | (split at ok <;> try contradiction) | (obtain ⟨_, _, ok⟩ := bind_ok ok)
  all_goals cases ok; exact ⟨this, checked depth⟩

/-- Each box loop has both a sibling-byte budget and a shared file-count budget.
One extra visit detects the end or a rejection. The two signature/file-type
reads before the outer loop are charged separately even when maxBoxes is tiny. -/
theorem boxLoops_fuel (L : Limits) (r : Reader) (count f g : Nat)
    (hf : min (r.remaining / 8) (L.maxBoxes - count) < f)
    (hg : min (r.remaining / 8) (L.maxBoxes - count) < g) :
    (∀ a, Box.headerLoop L r a count f = Box.headerLoop L r a count g) ∧
    (∀ h, Box.topLoop L r h count f = Box.topLoop L r h count g) := by
  induction f generalizing r g count with
  | zero => omega
  | succ f ih =>
    cases g with
    | zero => omega
    | succ g =>
      constructor <;> intro a
      · simp only [Box.headerLoop]
        split <;> first | rfl | skip
        simp only [bind, Except.bind]
        split <;> first | rfl | skip
        rename_i u hc
        have hl : count + 1 ≤ L.maxBoxes := checked hc
        split <;> first | rfl | skip
        rename_i p hp
        rcases p with ⟨b,t⟩
        have ht := box_consumes hp
        split <;> first | rfl | skip
        apply (ih t (count + 1) g (by omega) (by omega)).1
      · simp only [Box.topLoop]
        split <;> first | rfl | skip
        simp only [bind, Except.bind]
        split <;> first | rfl | skip
        rename_i u hc
        have hl : count + 1 ≤ L.maxBoxes := checked hc
        split <;> first | rfl | skip
        rename_i p hp
        rcases p with ⟨b,t⟩
        have ht := box_consumes hp
        split <;> first | rfl | skip
        split
        · split <;> first | rfl | skip
          rename_i p hj
          rcases p with ⟨h,k⟩
          have := (jp2h_count hj).1
          apply (ih t k g (by omega) (by omega)).2
        · apply (ih t (count + 1) g (by omega) (by omega)).2

/-- The public byte parser rejects an oversize buffer at its first check, including
malformed inputs with no complete box or marker. -/
theorem parse_input_excess {L : Limits} {data : ByteArray} (over : L.maxInputBytes < data.size) :
    Header.parse L data = .error (.limitExceeded (.atOffset .box 0) .inputBytes data.size
      L.maxInputBytes) := by
  simp [Header.parse, Box.parseFile, Box.parseFileAux, Limits.check, Limits.checkLe,
    Limits.bound, Nat.not_le.mpr over, bind, Except.bind]

/-- Length actually copied by extracting one range, including clamping by ByteArray.extract. -/
def copied (data : ByteArray) (r : ByteRange) : Nat := min r.stop data.size - r.offset

private theorem sum_bound {α : Type} (xs : List α) (f : α → Nat) (n : Nat)
    (h : ∀ x ∈ xs, f x ≤ n) : (xs.map f).sum ≤ xs.length * n := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    omega

private theorem gather_fold (data : ByteArray) (xs : List ByteRange) (acc : ByteArray) :
    (xs.foldl (fun a r => a ++ r.bytes data) acc).size =
      acc.size + (xs.map (copied data)).sum := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, ih, ByteArray.size_append]
    simp [ByteRange.bytes, copied, Nat.add_assoc]

/-- Exact fresh bytes and a multiplicity-sensitive upper bound, also for any prefix
passed to the range fold. Overlapping and repeated ranges are counted every time. -/
theorem gatherBytes_size (data : ByteArray) (rs : Array ByteRange) :
    (gatherBytes data rs).size = (rs.toList.map (copied data)).sum ∧
    (gatherBytes data rs).size ≤ rs.size * data.size := by
  have he : (gatherBytes data rs).size = (rs.toList.map (copied data)).sum := by
    rw [gatherBytes, ← Array.foldl_toList, gather_fold]
    simp
  refine ⟨he, ?_⟩
  rw [he]
  simpa using sum_bound rs.toList (copied data) data.size (fun x _ => by dsimp [copied]; omega)

/-- Number of source range descriptors traversed when the fragmented path gathers
every segment of one block. -/
def blockRanges (ss : List Segment) : Nat := (ss.map (fun s => s.ranges.size)).sum

private theorem block_sum_bound (data : ByteArray) (ss : List Segment) :
    (ss.map (fun s => (s.bytes data).size)).sum ≤ blockRanges ss * data.size := by
  induction ss with
  | nil => simp [blockRanges]
  | cons s ss ih =>
    have h : (s.bytes data).size ≤ s.ranges.size * data.size := (gatherBytes_size data _).2
    change (s.bytes data).size + _ ≤ (s.ranges.size + blockRanges ss) * data.size
    rw [Nat.add_mul]
    exact Nat.add_le_add h ih

private theorem concat_sizes (data : ByteArray) (ss : List Segment) (acc : ByteArray × Array Tier1.Seg) :
    let out := ss.foldl (Equiv.concatStep data) acc
    out.1.size = acc.1.size + (ss.map (fun s => (s.bytes data).size)).sum ∧
    out.2.size = acc.2.size + ss.length := by
  induction ss generalizing acc with
  | nil => simp
  | cons s ss ih =>
    simp only [List.foldl_cons]
    obtain ⟨h1,h2⟩ := ih (Equiv.concatStep data acc s)
    simp only [Equiv.concatStep, ByteArray.size_append, Array.size_push] at h1 h2
    exact ⟨by simpa [Equiv.concatStep, Nat.add_assoc] using h1,
      by simpa [Equiv.concatStep, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h2⟩

/-- The direct branch passes the original input with one descriptor per segment.
The fragmented branch emits one descriptor per segment and exactly the sum of the
extracted bytes, bounded by source range count times input size. -/
theorem tier1Input_storage (data : ByteArray) (cb : CodeBlock) :
    let out := Assemble.tier1Input data cb
    out.2.size = cb.segments.size ∧
    if cb.segments.all (·.ranges.size ≤ 1) then
      out = (data, cb.segments.map Assemble.directSeg)
    else
      out.1.size = (cb.segments.toList.map fun s => (s.bytes data).size).sum ∧
      out.1.size ≤ blockRanges cb.segments.toList * data.size := by
  dsimp only
  unfold Assemble.tier1Input
  split
  · simp
  · rw [← Array.foldl_toList]
    obtain ⟨hb,hs⟩ := concat_sizes data cb.segments.toList (ByteArray.empty, #[])
    simp only [ByteArray.size_empty, Array.size_empty, Nat.zero_add, Array.length_toList] at hb hs
    exact ⟨hs, hb, hb ▸ block_sum_bound data _⟩

private theorem pushRange_count (rs : Array ByteRange) (r : ByteRange) :
    (pushRange rs r).size ≤ rs.size + 1 := by
  unfold pushRange
  (repeat' split) <;> simp [Array.size_pop]

private theorem gather_checked (data : ByteArray) (xs : List ByteRange) (acc out : Array ByteRange)
    (inside : Tier2WF.RangesIn data.size acc)
    (h : forIn xs acc (fun r a =>
      if r.stop > data.size then throw (Error.truncated (.atOffset .tier2 r.offset)
        "packed packet headers past the end of the input")
      else pure (.yield (pushRange a r))) = Except.ok out) :
    out.size ≤ acc.size + xs.length ∧ Tier2WF.RangesIn data.size out := by
  induction xs generalizing acc with
  | nil => simp only [List.forIn_nil] at h; cases h; exact ⟨by simp, inside⟩
  | cons r rs ih =>
    rw [List.forIn_cons] at h
    split at h
    · cases h
    · rename_i hr
      obtain ⟨hs,hi⟩ := ih (pushRange acc r) (Tier2WF.pushRange_in inside (Nat.le_of_not_gt hr)) h
      have := pushRange_count acc r
      exact ⟨by simp only [List.length_cons]; omega, hi⟩

open JPEG2000.Tier2.Headers

/-- The actual PPM/PPT gather validates and coalesces before copying. A returned
stream retains at most the supplied descriptor count, each merged range is in the
input, and the new byte buffer counts each merged range with its multiplicity. -/
theorem headerGather_storage {data : ByteArray} {ppm : Bool} {rs : Array ByteRange}
    {stream : HeaderStream} (h : gather ppm data rs = .ok stream) :
    stream.fromPpm = ppm ∧ stream.ranges.size ≤ rs.size ∧
    Tier2WF.RangesIn data.size stream.ranges ∧
    stream.bytes.size = (stream.ranges.toList.map ByteRange.length).sum ∧
    stream.bytes.size ≤ rs.size * data.size := by
  unfold gather at h
  obtain ⟨merged,hm,h⟩ := bind_ok h
  cases h
  rw [← Array.forIn_toList] at hm
  obtain ⟨hs,hi⟩ := gather_checked data rs.toList #[] merged (by intro x hx; simp at hx) hm
  simp only [Array.size_empty, Nat.zero_add, Array.length_toList] at hs
  obtain ⟨he,hl⟩ := gatherBytes_size data merged
  refine ⟨rfl, hs, hi, he.trans ?_, Nat.le_trans hl (Nat.mul_le_mul_right _ hs)⟩
  congr 1
  apply List.map_congr_left
  intro r hr
  have hin := hi r (by simpa using hr)
  simp only [copied, ByteRange.stop, Nat.min_eq_left hin, Nat.add_sub_cancel_left]

/-- The main header's variable-length top-level collections, counting each marker
index and each segment reference. This count excludes arrays nested within each segment. -/
def mainSlots (a : Acc) : Nat :=
  a.markers.size + a.coc.size + a.qcc.size + a.rgn.size + a.poc.size + a.com.size +
    a.pointers.size + a.unknown.size

private theorem main_add {L : Limits} {c : Nat} {a z : Acc} {m : UInt16} {b : Reader}
    (h : addSegment L c a m b = .ok z) : mainSlots z ≤ mainSlots a + 1 := by
  unfold addSegment at h
  generalize (m == Code.COD) = k0 at h
  generalize (m == Code.COC) = k1 at h
  generalize (m == Code.QCD) = k2 at h
  generalize (m == Code.QCC) = k3 at h
  generalize (m == Code.RGN) = k4 at h
  generalize (m == Code.POC) = k5 at h
  generalize (m == Code.COM) = k6 at h
  generalize (m == Code.CRG) = k7 at h
  generalize (m == Code.CAP) = k8 at h
  generalize (m == Code.TLM || m == Code.PLM || m == Code.PPM) = k9 at h
  cases k0 <;> simp only [Bool.false_eq_true, ↓reduceIte] at h
  case true => repeat' obtain ⟨_,_,h⟩ := bind_ok h
               cases h; simp [mainSlots] <;> omega
  cases k1 <;> simp only [Bool.false_eq_true, ↓reduceIte] at h
  case true => repeat' obtain ⟨_,_,h⟩ := bind_ok h
               cases h; simp [mainSlots] <;> omega
  cases k2 <;> simp only [Bool.false_eq_true, ↓reduceIte] at h
  case true => repeat' obtain ⟨_,_,h⟩ := bind_ok h
               cases h; simp [mainSlots] <;> omega
  cases k3 <;> simp only [Bool.false_eq_true, ↓reduceIte] at h
  case true => repeat' obtain ⟨_,_,h⟩ := bind_ok h
               cases h; simp [mainSlots] <;> omega
  cases k4 <;> simp only [Bool.false_eq_true, ↓reduceIte] at h
  case true => repeat' obtain ⟨_,_,h⟩ := bind_ok h
               cases h; simp [mainSlots] <;> omega
  cases k5 <;> simp only [Bool.false_eq_true, ↓reduceIte] at h
  case true => repeat' obtain ⟨_,_,h⟩ := bind_ok h
               cases h; simp [mainSlots] <;> omega
  cases k6 <;> simp only [Bool.false_eq_true, ↓reduceIte] at h
  case true => repeat' obtain ⟨_,_,h⟩ := bind_ok h
               cases h; simp [mainSlots] <;> omega
  cases k7 <;> simp only [Bool.false_eq_true, ↓reduceIte] at h
  case true => repeat' obtain ⟨_,_,h⟩ := bind_ok h
               cases h; simp [mainSlots] <;> omega
  cases k8 <;> simp only [Bool.false_eq_true, ↓reduceIte] at h
  case true => repeat' obtain ⟨_,_,h⟩ := bind_ok h
               cases h; simp [mainSlots] <;> omega
  cases k9 <;> simp only [Bool.false_eq_true, ↓reduceIte] at h
  all_goals repeat' obtain ⟨_,_,h⟩ := bind_ok h
  all_goals cases h; simp [mainSlots] <;> omega

/-- At most two top-level collection slots per recursive step, paid from the input
cursor. The result includes the unread tail; the same accounting applies when a
later stage rejects the codestream. -/
theorem segmentLoop_storage {L : Limits} {c f : Nat} {a z : Acc} {r t : Reader}
    (h : segmentLoop L c f a r = .ok (z,t)) :
    mainSlots z + t.remaining ≤ mainSlots a + r.remaining ∧ t.data = r.data ∧ t.stop = r.stop := by
  induction f generalizing a r with
  | zero => cases h
  | succ f ih =>
    simp only [segmentLoop] at h
    split at h <;> try contradiction
    rename_i m r1 e
    have h1 := more16 e
    have p1 := Reader.u16be_pos e
    split at h
    · cases h; exact ⟨Nat.le_refl _,rfl,rfl⟩
    split at h <;> try contradiction
    split at h
    · obtain ⟨sz,dt,st⟩ := ih h
      simp only [mainSlots, Array.size_push] at sz ⊢
      exact ⟨by omega, dt.trans p1.2.2.1, st.trans p1.2.1⟩
    split at h <;> try contradiction
    split at h <;> try contradiction
    rename_i body n r2 e2
    have p2 := readSegment_extent e2
    split at h <;> try contradiction
    rename_i a2 ha
    have ha' := main_add ha
    have h2 := moreSeg e2
    obtain ⟨sz,dt,st⟩ := ih h
    simp only [mainSlots, Array.size_push] at ha' sz ⊢
    exact ⟨by omega, dt.trans (p2.2.1.trans p1.2.2.1), st.trans (p2.2.2.2.2.1.trans p1.2.1)⟩

private theorem tile_add {L : Limits} {c : Nat} {first ppm : Bool} {a z : TPAcc}
    {m : UInt16} {b : Reader} (h : addTileSegment L c first ppm a m b = .ok z) :
    z.segments.size = a.segments.size + 1 ∧ z.markers = a.markers := by
  unfold addTileSegment at h
  repeat' first | (split at h <;> try contradiction) | (obtain ⟨_,_,h⟩ := bind_ok h)
  all_goals cases h; simp

/-- The tile-part's marker index and segment array share a byte budget even for a
tile-part whose packet data or a later tile-part subsequently fails. -/
theorem tileHeaderLoop_storage {L : Limits} {c f : Nat} {first ppm : Bool} {a z : TPAcc}
    {r t : Reader} (h : TilePart.headerLoop L c first ppm f a r = .ok (z,t)) :
    z.markers.size + z.segments.size + t.remaining ≤
      a.markers.size + a.segments.size + r.remaining ∧ t.data = r.data ∧ t.stop = r.stop := by
  induction f generalizing a r with
  | zero => cases h
  | succ f ih =>
    simp only [TilePart.headerLoop] at h
    split at h <;> try contradiction
    rename_i m r1 e
    have h1 := more16 e
    have p1 := Reader.u16be_pos e
    split at h
    · cases h; simp only [Array.size_push]; exact ⟨by omega, p1.2.2.1, p1.2.1⟩
    split at h <;> try contradiction
    split at h
    · obtain ⟨sz,dt,st⟩ := ih h
      simp only [Array.size_push] at sz
      exact ⟨by omega,dt.trans p1.2.2.1,st.trans p1.2.1⟩
    split at h <;> try contradiction
    split at h <;> try contradiction
    rename_i body n r2 e2
    have p2 := readSegment_extent e2
    split at h <;> try contradiction
    rename_i a2 ha
    obtain ⟨seg,mark⟩ := tile_add ha
    obtain ⟨sz,dt,st⟩ := ih h
    have h2 := moreSeg e2
    simp only [seg,mark,Array.size_push] at sz
    exact ⟨by omega, dt.trans (p2.2.1.trans p1.2.2.1), st.trans (p2.2.2.2.2.1.trans p1.2.1)⟩

open JPEG2000.Tier2.Geometry

private theorem map_size {α β : Type} {xs : Array α} {ys : Array β}
    {f : α → Except Error β} (ok : xs.mapM f = .ok ys) : ys.size = xs.size := by
  have len (l : List α) (out : List β) (ok : l.mapM f = .ok out) : out.length = l.length := by
    induction l generalizing out with
    | nil => cases ok; rfl
    | cons a l ih =>
      rw [List.mapM_cons] at ok
      obtain ⟨_,_,ok⟩ := bind_ok ok
      obtain ⟨ys,hy,ok⟩ := bind_ok ok
      cases ok; simp [ih ys hy]
  rw [Array.mapM_eq_mapM_toList] at ok
  cases hm : xs.toList.mapM f with
  | error e => rw [hm] at ok; cases ok
  | ok l => rw [hm] at ok; cases ok; simpa using len _ _ hm

private theorem tree_slots {L : Limits} {w h : Nat} {tr : TagTree.Tree}
    (ok : TagTree.create L w h = .ok tr) :
    tr.low.size + tr.val.size ≤ 8 * L.maxCodeBlocks := by
  unfold TagTree.create at ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  obtain ⟨_,hc,ok⟩ := bind_ok ok
  have := (Limits.checkLe_eq_ok_iff ..).1 hc
  cases ok
  simp only [Array.size_replicate]
  omega

/-- Number of array entries for the two tag trees and the code-block states of
one freshly initialized band. These are entries of different Lean types. -/
def bandSlots (b : BandState) : Nat :=
  b.blocks.size + b.incl.low.size + b.incl.val.size + b.zbp.low.size + b.zbp.val.size

/-- Geometry allocated before the aggregate block check and before either tag
tree is created. A completely constructed precinct may itself trigger rejection
by the subsequent aggregate check in initPrecincts. -/
theorem precinct_geometry {L : Limits} {tc : TileCompGeom} {r p : Nat}
    {res : ResolutionGeom} {pg : PrecinctGeom} (hr : resolution L tc r = .ok res)
    (hp : precinct L res p = .ok pg) :
    res.numPrecincts ≤ L.maxPrecincts ∧ pg.bands.size ≤ 3 ∧
    ∀ b ∈ pg.bands, b.codeBlocks.size ≤ L.maxCodeBlocks := by
  have resSize : res.numPrecincts ≤ L.maxPrecincts ∧ res.bands.size ≤ 3 := by
    unfold resolution at hr
    dsimp only at hr
    split at hr <;> try contradiction
    obtain ⟨_,hc,hr⟩ := bind_ok hr
    obtain ⟨_,_,hr⟩ := bind_ok hr
    cases hr
    exact ⟨checked hc, by simp only [Array.size_map, bandsOf]; split <;> decide⟩
  unfold precinct at hp
  dsimp only at hp
  split at hp <;> try contradiction
  obtain ⟨bands,hb,hp⟩ := bind_ok hp
  cases hp
  have count := map_size hb
  have each : ∀ b ∈ bands, b.codeBlocks.size ≤ L.maxCodeBlocks := by
    refine Tier2WF.arrayMapM_mem _ _ _ ?_ _ hb
    intro b _ pb ok
    obtain ⟨_,hc,ok⟩ := bind_ok ok
    cases ok
    simp only [codeBlocksOf, Array.size_map, List.size_toArray, List.length_range]
    exact (Limits.check_eq_ok_iff ..).1 hc
  exact ⟨resSize.1, by dsimp only; omega, each⟩

/-- Actual per-resolution and per-precinct initialization. Each successful
prefix has at most three bands; allocation in one band takes at most one checked
code-block array and four checked tag-tree arrays. -/
theorem precinct_storage {L : Limits} {tc : TileCompGeom} {r p : Nat} {res : ResolutionGeom}
    {pg : PrecinctGeom} {st : PrecState} (hr : resolution L tc r = .ok res)
    (hp : precinct L res p = .ok pg) (hs : PrecState.init L tc.params r pg = .ok st) :
    res.numPrecincts ≤ L.maxPrecincts ∧ pg.bands.size ≤ 3 ∧
    (∀ b ∈ pg.bands, b.codeBlocks.size ≤ L.maxCodeBlocks) ∧
    (st.bands.toList.map bandSlots).sum ≤ 3 * (17 * L.maxCodeBlocks) := by
  obtain ⟨nr,nb,each⟩ := precinct_geometry hr hp
  unfold PrecState.init at hs
  obtain ⟨bs,hbs,hs⟩ := bind_ok hs
  cases hs
  have states : ∀ b ∈ bs, bandSlots b ≤ 17 * L.maxCodeBlocks := by
    refine Tier2WF.arrayMapM_mem _ _ _ ?_ _ hbs
    intro pb hm b ok
    obtain ⟨inc,hi,ok⟩ := bind_ok ok
    obtain ⟨zbp,hz,ok⟩ := bind_ok ok
    cases ok
    have := tree_slots hi
    have := tree_slots hz
    have := each pb hm
    simp only [bandSlots, Array.size_map]
    omega
  have hsum := sum_bound bs.toList bandSlots _ (fun b hm => states b (by simpa using hm))
  have hlen := map_size hbs
  refine ⟨nr, nb, each, ?_⟩
  refine Nat.le_trans hsum (Nat.mul_le_mul_right _ ?_)
  simp only [Array.length_toList]
  omega

/-- Byte lengths in descriptor order, counting multiplicity. -/
def rangeBytes (xs : List ByteRange) : Nat := (xs.map ByteRange.length).sum

/-- Splitting an Nppm or Ippm prefix conserves bytes exactly. A partial final
range adds at most one descriptor; neither output can have more source ranges
than it visited (apart from the pre-existing accumulator). -/
theorem takeRanges_account (xs : List ByteRange) (n : Nat) (a taken : Array ByteRange)
    (rest : List ByteRange) (ok : takeRanges xs n a = some (taken,rest)) :
    rangeBytes taken.toList = rangeBytes a.toList + n ∧
    rangeBytes rest + n = rangeBytes xs ∧
    taken.size ≤ a.size + xs.length ∧ rest.length ≤ xs.length := by
  induction xs generalizing n a with
  | nil =>
    cases n <;> cases ok
    simp [rangeBytes]
  | cons x xs ih =>
    cases n with
    | zero => cases ok; simp
    | succ n =>
      simp only [takeRanges] at ok
      split at ok
      · cases ok
        simp [rangeBytes, Nat.add_assoc] <;> omega
      · obtain ⟨h1,h2,h3,h4⟩ := ih _ _ ok
        simp only [rangeBytes, Array.toList_push, List.map_append, List.map_singleton,
          List.sum_append, List.sum_singleton] at h1
        simp only [rangeBytes, List.map_cons, List.sum_cons] at h2 ⊢
        simp only [Array.size_push] at h3
        simp only [List.length_cons]
        exact ⟨by omega, by omega, by omega, by omega⟩

/-- At most four fresh bytes for reading Nppm, even if these bytes straddle
segments or a range refers past the buffer and u32be then rejects the prefix. -/
theorem ppmLength_copy {data : ByteArray} {xs rest : List ByteRange} {nb : Array ByteRange}
    (h : takeRanges xs 4 #[] = some (nb,rest)) : (gatherBytes data nb).size ≤ 4 := by
  have he := (takeRanges_account _ _ _ _ _ h).1
  have bounds (ys : List ByteRange) : (ys.map (copied data)).sum ≤ rangeBytes ys := by
    induction ys with
    | nil => simp [rangeBytes]
    | cons x ys ih =>
      have hx : copied data x ≤ x.length := by dsimp [copied,ByteRange.stop]; omega
      exact Nat.add_le_add hx ih
  rw [(gatherBytes_size data nb).1]
  have := bounds nb.toList
  simpa [rangeBytes] using Nat.le_trans this (Nat.le_of_eq he)

/-- Total payload bytes described by the PPM chunk table, counting every range. -/
def chunkBytes (a : Array (Array ByteRange)) : Nat :=
  (a.toList.map (fun xs => rangeBytes xs.toList)).sum

/-- Chunk splitting consumes four length bytes per chunk in addition to its
payload, and checks the growing table before pushing. Applies at each admitted
prefix, independent of any later tile or packet decode. -/
theorem ppmChunks_account (L : Limits) (data : ByteArray) (loc : Location)
    (f : Nat) (xs : List ByteRange) (a out : Array (Array ByteRange))
    (ha : a.size ≤ L.maxTileParts) (ok : ppmChunks L data loc f xs a = .ok out) :
    out.size ≤ L.maxTileParts ∧ a.size ≤ out.size ∧
    chunkBytes out + 4 * (out.size - a.size) = chunkBytes a + rangeBytes xs := by
  induction f generalizing xs a with
  | zero => cases xs <;> cases ok; simp [ha, rangeBytes]
  | succ f ih =>
    cases xs with
    | nil => cases ok; simp [ha, rangeBytes]
    | cons x xs =>
      simp only [ppmChunks] at ok
      obtain ⟨_,hc,ok⟩ := bind_ok ok
      split at ok <;> try contradiction
      rename_i nb rest hn
      obtain ⟨⟨n,_⟩,_,ok⟩ := bind_ok ok
      dsimp only at ok
      split at ok <;> try contradiction
      rename_i chunk tail ht
      have hcount : a.size + 1 ≤ L.maxTileParts := checked hc
      obtain ⟨h1,h2,h3⟩ := ih tail (a.push chunk) (by simpa using hcount) ok
      have v1 := (takeRanges_account _ _ _ _ _ hn).2.1
      obtain ⟨v2,v3,-⟩ := takeRanges_account _ _ _ _ _ ht
      simp only [Array.size_push] at h2 h3
      have vp : chunkBytes (a.push chunk) = chunkBytes a + rangeBytes chunk.toList := by
        simp [chunkBytes]
      rw [vp] at h3
      change rangeBytes chunk.toList = 0 + n.toNat at v2
      exact ⟨h1, by omega, by omega⟩

private theorem ppm_select (data : ByteArray) (h : Header) (tp : TileParams)
    (ranks : Array Nat) (stream : HeaderStream)
    (ok : headerStreamAt h data tp ranks = .ok (some stream)) :
    ∃ rs, gather stream.fromPpm data rs = .ok stream ∧
      (if stream.fromPpm then rs.size ≤ tp.tile.parts.size *
        (h.ppm.chunks.toList.map Array.size).sum else rs = tp.tile.ppt) := by
  unfold headerStreamAt at ok
  dsimp only at ok
  split at ok
  · split at ok <;> try contradiction
    obtain ⟨rs,hr,ok⟩ := bind_ok ok
    obtain ⟨s,hs,ok⟩ := bind_ok ok
    cases ok
    have src := (headerGather_storage hs).1
    refine ⟨rs, src ▸ hs, ?_⟩
    simp only [src, ↓reduceIte]
    simp only [Std.Legacy.Range.forIn_eq_forIn_range'] at hr
    let n := (h.ppm.chunks.toList.map Array.size).sum
    have bound (ys : List (Array ByteRange)) (y : Array ByteRange) (hy : y ∈ ys) :
        y.size ≤ (ys.map Array.size).sum := by
      induction ys with
      | nil => simp at hy
      | cons x xs ih =>
        simp only [List.mem_cons] at hy
        rcases hy with rfl | hy
        · simp
        · have := ih hy; simp only [List.map_cons,List.sum_cons]; omega
    have step := Tier2WF.forIn_range'_inv (fun i (b : Array ByteRange) => b.size ≤ i*n)
      _ ?_ _ 0 _ _ (by simp) hr
    · simpa [Std.Legacy.Range.size] using step
    intro i b v hb hv
    split at hv <;> try contradiction
    split at hv <;> try contradiction
    rename_i chunk hc
    cases hv
    have hsize := bound h.ppm.chunks.toList chunk (by simpa using Array.mem_of_getElem? hc)
    refine ⟨_,rfl,?_⟩
    simp only [Array.size_append, Nat.add_mul, Nat.one_mul]
    exact Nat.add_le_add hb hsize
  · split at ok <;> try (solve | cases ok)
    obtain ⟨s,hs,ok⟩ := bind_ok ok
    cases ok
    have src := (headerGather_storage hs).1
    exact ⟨_, src ▸ hs, by simp [src]⟩

/-- The input-specific descriptor and byte budget at the actual header-stream
selection. PPM charges selected chunks per tile-part even for repeated ranks;
PPT uses the tile's supplied ranges. -/
theorem headerStreamAt_storage {h : Header} {data : ByteArray} {tp : TileParams}
    {ranks : Array Nat} {stream : HeaderStream}
    (ok : headerStreamAt h data tp ranks = .ok (some stream)) :
    let budget := if stream.fromPpm then tp.tile.parts.size * (h.ppm.chunks.toList.map Array.size).sum
                  else tp.tile.ppt.size
    stream.ranges.size ≤ budget ∧ stream.bytes.size ≤ budget * data.size ∧
    Tier2WF.RangesIn data.size stream.ranges := by
  obtain ⟨rs,hg,hb⟩ := ppm_select data h tp ranks stream ok
  obtain ⟨_,hs,hi,_,hl⟩ := headerGather_storage hg
  dsimp only
  split at hb
  · rename_i ht
    simp only [ht, ↓reduceIte]
    exact ⟨Nat.le_trans hs hb,Nat.le_trans hl (Nat.mul_le_mul_right _ hb),hi⟩
  · rename_i ht
    simp only [ht]
    exact hb ▸ ⟨hs,hl,hi⟩


private def statesBound (L : Limits) (xs : Array PrecState) : Prop :=
  ∀ st ∈ xs, (st.bands.toList.map bandSlots).sum ≤ 3 * (17 * L.maxCodeBlocks)

/-- The actual initialization loops return at most the checked precinct count and
one pair of index rows per component. The bound on the nested arrays charges every
code-block state and every low/value entry in both tag trees of all retained bands. -/
theorem initPrecincts_storage {L : Limits} {g : Progression.Layout} {ps : Array PrecState}
    {base : Array (Array Nat)} {spans : Array (Array (Nat × Nat))}
    (ok : initPrecincts L g = .ok (ps,base,spans)) :
    ps.size ≤ L.maxPrecincts ∧ base.size = g.numComps ∧ spans.size = g.numComps ∧
    (ps.toList.map (fun st => (st.bands.toList.map bandSlots).sum)).sum ≤
      L.maxPrecincts * (3 * (17 * L.maxCodeBlocks)) := by
  unfold initPrecincts at ok
  simp only [Std.Legacy.Range.forIn_eq_forIn_range'] at ok
  obtain ⟨out,loop,ok⟩ := bind_ok ok
  cases ok
  have size_range (n : Nat) : [:n].size = n := by simp [Std.Legacy.Range.size]
  simp only [size_range] at loop
  have outer := Tier2WF.forIn_range'_inv
    (fun i (s : Array PrecState × Array (Array Nat) × Array (Array (Nat × Nat)) × Nat) =>
      s.1.size ≤ L.maxPrecincts ∧ s.2.1.size = i ∧ s.2.2.1.size = i ∧ statesBound L s.1)
    _ ?_ _ 0 _ _ (by simp [statesBound]) loop
  · obtain ⟨hn,hb,hs,ha⟩ := outer
    have hsum := sum_bound out.1.toList (fun st => (st.bands.toList.map bandSlots).sum) _
      (fun x hx => ha x (by simpa using hx))
    exact ⟨hn,by simpa using hb,by simpa using hs,Nat.le_trans hsum (Nat.mul_le_mul_right _ (by simpa using hn))⟩
  intro i b v hb hv
  obtain ⟨out2,loop2,hv⟩ := bind_ok hv
  cases hv
  have middle := Tier2WF.forIn_range'_inv
    (fun _ (s : Array PrecState × Nat × Array Nat × Array (Nat × Nat)) =>
      s.1.size ≤ L.maxPrecincts ∧ statesBound L s.1)
    _ ?_ _ 0 _ _ ⟨hb.1,hb.2.2.2⟩ loop2
  · exact ⟨_, rfl, middle.1, by simp [hb.2.1], by simp [hb.2.2.1], middle.2⟩
  intro rr b2 v2 hb2 hv2
  obtain ⟨res,hr,hv2⟩ := bind_ok hv2
  obtain ⟨_,hc,hv2⟩ := bind_ok hv2
  obtain ⟨out3,loop3,hv2⟩ := bind_ok hv2
  cases hv2
  have inner := Tier2WF.forIn_range'_inv
    (fun p (s : Array PrecState × Nat) => s.1.size = b2.1.size + p ∧ statesBound L s.1)
    _ ?_ _ 0 _ _ ⟨rfl,hb2.2⟩ loop3
  · have limit : b2.1.size + res.numPrecincts ≤ L.maxPrecincts := checked hc
    obtain ⟨hs,ha⟩ := inner
    exact ⟨_,rfl, by dsimp only; omega, ha⟩
  intro p b3 v3 hb3 hv3
  obtain ⟨pg,hp,hv3⟩ := bind_ok hv3
  obtain ⟨_,_,hv3⟩ := bind_ok hv3
  obtain ⟨st,hs,hv3⟩ := bind_ok hv3
  cases hv3
  refine ⟨_,rfl, by simp [hb3.1,Nat.add_assoc], ?_⟩
  intro x hx
  rw [Array.mem_push] at hx
  rcases hx with hx | rfl
  · exact hb3.2 _ hx
  · exact (precinct_storage hr hp hs).2.2.2

private theorem readArray_size {α : Type} (f : Reader → Except Error (α × Reader))
    (n : Nat) (a z : Array α) (r t : Reader) (ok : readArray f a n r = .ok (z,t)) :
    z.size = a.size + n := by
  induction n generalizing a r with
  | zero => cases ok; rfl
  | succ n ih =>
    simp only [readArray] at ok
    split at ok <;> try contradiction
    rw [ih _ _ ok, Array.size_push]
    omega

private theorem siz_count {L : Limits} {r : Reader} {s : SIZ} (ok : parseSIZ L r = .ok s) :
    s.csiz ≤ L.maxComponents := by
  unfold parseSIZ at ok
  iterate 10 obtain ⟨⟨_,_⟩,_,ok⟩ := bind_ok ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  obtain ⟨_,hc,ok⟩ := bind_ok ok
  iterate 5 obtain ⟨_,_,ok⟩ := bind_ok ok
  obtain ⟨⟨cs,tail⟩,ha,ok⟩ := bind_ok ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  cases ok
  have sz := readArray_size _ _ _ _ _ _ ha
  simp at sz
  change cs.size ≤ L.maxComponents
  exact sz ▸ checked hc

private theorem main_reader {L : Limits} {r t : Reader} {mh : MainHeader}
    (ok : parseMainHeader L r = .ok (mh,t)) :
    mh.markers.size + mh.coc.size + mh.qcc.size + mh.rgn.size + mh.poc.size + mh.com.size +
      mh.pointers.size + mh.unknown.size + t.remaining ≤ r.remaining ∧ t.data = r.data := by
  unfold parseMainHeader at ok
  obtain ⟨⟨_,r1⟩,h1,ok⟩ := bind_ok ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  obtain ⟨⟨_,r2⟩,h2,ok⟩ := bind_ok ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  obtain ⟨⟨body,n,r3⟩,h3,ok⟩ := bind_ok ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  obtain ⟨⟨a,t'⟩,loop,ok⟩ := bind_ok ok
  cases hc : a.cod <;> simp only [hc] at ok
  · cases ok
  cases hq : a.qcd <;> simp only [hq] at ok
  · cases ok
  cases ok
  obtain ⟨hs,hd,_⟩ := segmentLoop_storage loop
  have b1 := more16 h1
  have b2 := more16 h2
  have b3 := moreSeg h3
  have d1 := (Reader.u16be_pos h1).2.2.1
  have d2 := (Reader.u16be_pos h2).2.2.1
  have d3 := (readSegment_extent h3).2.1
  dsimp only
  simp [mainSlots] at hs
  exact ⟨by omega,hd.trans (d3.trans (d2.trans d1))⟩

/-- Resources of a parsed public header, including the physically traversed main-header
collections and their enclosing codestream range. HeaderWithin supplies checked
image sides, area, tile grid and the code-block, packet and precinct totals. -/
theorem parse_storage {L : Limits} {data : ByteArray} {h : Header} (ok : Header.parse L data = .ok h) :
    Resources.HeaderWithin L data h ∧ h.siz.csiz ≤ L.maxComponents ∧
    h.codestream.start + h.codestream.len ≤ data.size ∧
    h.main.markers.size + h.main.coc.size + h.main.qcc.size + h.main.rgn.size +
      h.main.poc.size + h.main.com.size + h.main.pointers.size + h.main.unknown.size ≤
        h.codestream.len := by
  refine ⟨Resources.parse_within ok,?_⟩
  unfold Header.parse at ok
  obtain ⟨c,hc,ok⟩ := bind_ok ok
  unfold parseCodestreamIn at ok
  obtain ⟨r,hr,ok⟩ := bind_ok ok
  obtain ⟨⟨mh,t⟩,hm,ok⟩ := bind_ok ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  obtain ⟨⟨_,_⟩,_,ok⟩ := bind_ok ok
  repeat' obtain ⟨_,_,ok⟩ := bind_ok ok
  cases ok
  obtain ⟨⟨_,hs⟩,_⟩ := Spec.HeaderWF.parseMainHeader_fields hm
  have work := (main_reader hm).1
  unfold rangeReader at hr
  obtain ⟨mid,_,hr⟩ := bind_ok hr
  obtain ⟨⟨sub,_⟩,ht,hr⟩ := bind_ok hr
  cases hr
  have ht := Reader.take_spec ht
  dsimp only [Reader.remaining] at work
  refine ⟨siz_count hs, Box.parseFile_range hc, ?_⟩
  dsimp only
  dsimp only at ht
  omega

/-- Iteration dimensions of the geometry initialization for a parsed tile. Applies
before entering any resolution/precinct loops, including when one of them rejects. -/
theorem layout_budget {L : Limits} {data : ByteArray} {h : Header} {t : Nat}
    {g : Progression.Layout} {c : Coding} (ok : Header.parse L data = .ok h)
    (layout : Progression.Layout.ofHeader h t = .ok (g,c)) :
    g.numComps ≤ L.maxComponents ∧ ∀ i : Fin g.numComps,
      (g.comp i).numResolutions ≤ L.maxDecompLevels + 1 := by
  refine ⟨?_,fun i => Nat.add_le_add_right (WideHeaderBounds.parsed_component_bounds ok layout i 0).1.levels 1⟩
  unfold Progression.Layout.ofHeader at layout
  dsimp only at layout
  split at layout <;> try contradiction
  obtain ⟨xs,hm,layout⟩ := bind_ok layout
  cases layout
  have count := map_size hm
  simpa [Progression.Layout.numComps, count] using (parse_storage ok).2.1


private theorem unique_perm {α : Type} {xs ys : Array α} {key : α → UInt8} {loc w}
    (ok : sortUnique key loc w xs = .ok ys) : ys.Perm xs := by
  unfold sortUnique at ok
  dsimp only at ok
  split at ok <;> cases ok
  exact insertionSort_perm ..

private theorem chunks_width (L : Limits) (data : ByteArray) (loc : Location) (n m : Nat)
    (xs : List ByteRange) (a out : Array (Array ByteRange)) (hx : xs.length ≤ m)
    (ha : ∀ chunk ∈ a, chunk.size ≤ m) (ok : ppmChunks L data loc n xs a = .ok out) :
    ∀ chunk ∈ out, chunk.size ≤ m := by
  induction n generalizing xs a with
  | zero => cases xs <;> cases ok; exact ha
  | succ n ih =>
    cases xs with
    | nil => cases ok; exact ha
    | cons x xs =>
      simp only [ppmChunks] at ok
      obtain ⟨_,_,ok⟩ := bind_ok ok
      split at ok <;> try contradiction
      rename_i nb rest hn
      obtain ⟨⟨_,_⟩,_,ok⟩ := bind_ok ok
      dsimp only at ok
      split at ok <;> try contradiction
      rename_i chunk tail ht
      have h1 := (takeRanges_account _ _ _ _ _ hn).2.2.2
      obtain ⟨h2,h3⟩ := (takeRanges_account _ _ _ _ _ ht).2.2
      apply ih tail (a.push chunk) (by omega) _ ok
      intro v hv
      rcases Array.mem_push.1 hv with hv | rfl
      · exact ha v hv
      · simp only [Array.size_empty,Nat.zero_add] at h2
        omega

private theorem forIn_growth {α β : Type} (weight : β → Nat)
    (f : α → β → Except Error (ForInStep β))
    (step : ∀ x b v, f x b = .ok v → weight v.value ≤ weight b + 1)
    (l : List α) (b z : β) (ok : forIn l b f = .ok z) :
    weight z ≤ weight b + l.length := by
  induction l generalizing b with
  | nil => cases ok; simp
  | cons x xs ih =>
    rw [List.forIn_cons] at ok
    obtain ⟨v,hv,ok⟩ := bind_ok ok
    have hs := step _ _ _ hv
    cases v with
    | done b' => cases ok; change weight z ≤ weight b + 1 at hs; simp only [List.length_cons]; omega
    | yield b' =>
      have := ih b' ok
      change weight b' ≤ weight b + 1 at hs
      simp only [List.length_cons]; omega

private theorem pointers_count {L : Limits} {mh : MainHeader} {data : ByteArray}
    {tlm : Array TLM} {ppm : PPMData} (ok : parsePointers L mh data = .ok (tlm,ppm)) :
    ppm.chunks.size ≤ L.maxTileParts ∧ ppm.segments.size ≤ mh.pointers.size ∧
    (∀ chunk ∈ ppm.chunks, chunk.size ≤ mh.pointers.size) := by
  unfold parsePointers at ok
  obtain ⟨a,loop,ok⟩ := bind_ok ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  obtain ⟨ps,sorted,ok⟩ := bind_ok ok
  obtain ⟨chunks,hc,ok⟩ := bind_ok ok
  cases ok
  have eq := (unique_perm sorted).size_eq
  rw [← Array.forIn_toList] at loop
  have count := forIn_growth (fun b : Array TLM × Array PPM × Nat => b.2.1.size)
    _ ?_ _ _ _ loop
  · simp only [Array.size_empty,Nat.zero_add,Array.length_toList] at count
    refine ⟨(ppmChunks_account _ _ _ _ _ _ _ (by simp) hc).1, ?_, ?_⟩
    · dsimp only; omega
    · exact chunks_width _ _ _ _ _ _ _ _ (by simp; omega) (by simp) hc
  intro s acc v hv
  obtain ⟨_,_,hv⟩ := bind_ok hv
  (repeat' first | (split at hv <;> try contradiction) | (obtain ⟨_,_,hv⟩ := bind_ok hv))
  all_goals cases hv; simp

/-- The parsed PPM descriptor tables are bounded by input bytes and the tile-part
limit before any tile selects its chunks. A split range is charged again in the next
chunk. -/
theorem parse_ppm {L : Limits} {data : ByteArray} {h : Header} (ok : Header.parse L data = .ok h) :
    h.ppm.chunks.size ≤ L.maxTileParts ∧ h.ppm.segments.size ≤ data.size ∧
    (h.ppm.chunks.toList.map Array.size).sum ≤ L.maxTileParts * data.size := by
  obtain ⟨_,_,range,main⟩ := parse_storage ok
  have ptr : h.main.pointers.size ≤ data.size := by omega
  unfold Header.parse at ok
  obtain ⟨c,_,ok⟩ := bind_ok ok
  unfold parseCodestreamIn at ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  obtain ⟨⟨mh,_⟩,_,ok⟩ := bind_ok ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  obtain ⟨⟨tlm,ppm⟩,hp,ok⟩ := bind_ok ok
  repeat' obtain ⟨_,_,ok⟩ := bind_ok ok
  cases ok
  obtain ⟨hc,hs,hw⟩ := pointers_count hp
  dsimp only at ptr ⊢
  refine ⟨hc,Nat.le_trans hs ptr,?_⟩
  have bound := sum_bound ppm.chunks.toList Array.size data.size
    (fun x hx => Nat.le_trans (hw x (by simpa using hx)) ptr)
  simp only [Array.length_toList] at bound
  exact Nat.le_trans bound (Nat.mul_le_mul_right _ hc)


private def partTable (L : Limits) (n : Nat) (ps : Array TilePartHeader) : Prop :=
  ps.size ≤ L.maxTilePartsPerTile ∧ ∀ p ∈ ps, p.data.stop ≤ n ∧
    p.markers.size + p.segments.size ≤ n + 1

private theorem modify_all {α : Type} (P : α → Prop) {a : Array α} {i : Nat} {f : α → α}
    (old : ∀ x ∈ a, P x) (step : ∀ x, a[i]? = some x → P (f x)) :
    ∀ x ∈ a.modify i f, P x := by
  intro x hx
  obtain ⟨j,hj,rfl⟩ := Array.mem_iff_getElem.1 hx
  have inb : j < a.size := by simpa using hj
  rw [Array.getElem_modify]
  split
  · rename_i eq
    subst j
    exact step _ (Array.getElem?_eq_getElem inb)
  · exact old _ (Array.getElem_mem inb)

private theorem part_step_table {c : Ctx} {r t : Reader} {a z : State}
    (ha : ∀ ps ∈ a.parts, partTable c.limits r.data.size ps)
    (ok : readTilePart c a r = .ok (z,t)) : ∀ ps ∈ z.parts, partTable c.limits r.data.size ps := by
  unfold readTilePart at ok
  obtain ⟨⟨_,r1⟩,h1,ok⟩ := bind_ok ok
  obtain ⟨⟨_,_,r2⟩,h2,ok⟩ := bind_ok ok
  obtain ⟨sot,_,ok⟩ := bind_ok ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  obtain ⟨_,hc,ok⟩ := bind_ok ok
  iterate 3 obtain ⟨_,_,ok⟩ := bind_ok ok
  dsimp only at ok
  split at ok <;> split at ok <;> try contradiction
  all_goals
    simp only [pure_bind] at ok
    obtain ⟨⟨tp,next⟩,ht,ok⟩ := bind_ok ok
    obtain ⟨⟨acc,rd⟩,hl,ok⟩ := bind_ok ok
    cases ok
    have htp := Reader.take_spec ht
    have hrd := tileHeaderLoop_storage hl
    have data_eq := htp.2.2.1.trans ((readSegment_extent h2).2.1.trans (Reader.u16be_pos h1).2.2.1)
    have pn : tp.stop ≤ r.data.size := data_eq ▸ tp.stop_le
    have slot := hrd.1
    change acc.markers.size + acc.segments.size + rd.remaining ≤ 1 + 0 + tp.remaining at slot
    intro ys hy
    dsimp only at hy
    refine modify_all _ ha ?_ ys hy
    intro xs hxs
    have lim := checked hc
    rw [hxs] at lim
    refine ⟨by simpa [Limits.bound] using lim,?_⟩
    intro p hp
    rcases Array.mem_push.1 hp with hp | rfl
    · exact (ha xs (Array.mem_of_getElem? hxs)).2 _ hp
    · have end_le : rd.stop ≤ r.data.size := (hrd.2.1.trans data_eq) ▸ rd.stop_le
      have := rd.pos_le
      dsimp only [ByteRange.stop,Reader.remaining] at slot ⊢
      exact ⟨by omega,by omega⟩

private theorem tile_loop_table {c : Ctx} {r : Reader} {a z : State} {f : Nat}
    (ha : ∀ ps ∈ a.parts, partTable c.limits r.data.size ps)
    (ok : tilePartLoop c f a r = .ok z) : ∀ ps ∈ z.parts, partTable c.limits r.data.size ps := by
  induction f generalizing r a with
  | zero => cases ok
  | succ f ih =>
    simp only [tilePartLoop] at ok
    split at ok <;> try contradiction
    split at ok
    · cases ok; exact ha
    split at ok <;> try contradiction
    split at ok <;> try contradiction
    rename_i a' r' hs
    have hdata := (readTilePart_step hs).2.2.2.1
    rw [← hdata]
    apply ih _ ok
    rw [hdata]
    exact part_step_table ha hs

private def tileTable (L : Limits) (n : Nat) (t : Tile) : Prop :=
  partTable L n t.parts ∧ t.ppt.size ≤ t.parts.size * (n+1)

private theorem assemble_table {L : Limits} {n i : Nat} {corr : Bool} {ps : Array TilePartHeader}
    {t : Tile} (ht : partTable L n ps) (ok : assembleTile corr i ps = .ok t) : tileTable L n t := by
  have step (l : List TilePartHeader) (a : Array PPT)
      (hl : ∀ p ∈ l, p.segments.size ≤ n + 1) :
      (l.foldl (fun acc p => acc ++ p.segments.filterMap (fun | .ppt x => some x | _ => none)) a).size ≤
        a.size + l.length * (n + 1) := by
    induction l generalizing a with
    | nil => simp
    | cons p l ih =>
      rw [List.foldl_cons]
      have h := ih (a ++ p.segments.filterMap (fun | .ppt x => some x | _ => none))
        (fun q hq => hl q (by simp [hq]))
      have hb := hl p (by simp)
      have hf := Array.size_filterMap_le (xs := p.segments) (f := fun | .ppt x => some x | _ => none)
      simp only [Array.size_append] at h
      rw [List.length_cons,Nat.succ_mul]
      omega
  unfold assembleTile at ok
  dsimp only at ok
  split at ok <;> split at ok <;> try (obtain ⟨_,hbad,_⟩ := bind_ok ok; cases hbad)
  all_goals
    obtain ⟨ppts,hp,ok⟩ := bind_ok ok
    obtain ⟨_,_,ok⟩ := bind_ok ok
    cases ok
    refine ⟨ht,?_⟩
    dsimp only
    rw [Array.size_map,(unique_perm hp).size_eq, ← Array.foldl_toList]
    apply Nat.le_trans (step ps.toList #[] ?_) (by simp)
    intro p hp
    have := (ht.2 p (by simpa using hp)).2
    omega

private theorem assembled_tables {L : Limits} {n f i packets : Nat} {corr : Bool}
    {parts : Array (Array TilePartHeader)} {a z : Array Tile}
    (table : ∀ ps ∈ parts, partTable L n ps) (acc : ∀ t ∈ a, tileTable L n t)
    (ok : assembleTiles L corr parts f i packets a = .ok z) : ∀ t ∈ z, tileTable L n t := by
  induction f generalizing i packets a with
  | zero => cases ok; exact acc
  | succ f ih =>
    simp only [assembleTiles] at ok
    split at ok
    · exact ih acc ok
    split at ok <;> try contradiction
    rename_i t ht
    split at ok <;> try contradiction
    apply ih _ ok
    intro v hv
    rcases Array.mem_push.1 hv with hv | rfl
    · exact acc v hv
    · apply assemble_table _ ht
      cases he : parts[i]? with
      | none => simp [partTable]
      | some ps => exact table _ (Array.mem_of_getElem? he)

private theorem tileParts_table {L : Limits} {mh : MainHeader} {r : Reader} {ts : Array Tile}
    (ok : parseTileParts L mh r = .ok ts) : ∀ t ∈ ts, tileTable L r.data.size t := by
  unfold parseTileParts at ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  obtain ⟨_,hl,ok⟩ := bind_ok ok
  apply assembled_tables (tile_loop_table (z := _) (r := r) ?_ hl) (by simp) ok
  intro ps hp
  simp only [Array.mem_replicate] at hp
  obtain ⟨_,rfl⟩ := hp
  simp [partTable]

/-- Each tile in the public parse result retains checked part counts, borrowed data
ranges inside the actual input and a bounded number of PPT source descriptors. -/
theorem parse_tile_storage {L : Limits} {data : ByteArray} {h : Header} (ok : Header.parse L data = .ok h) :
    ∀ tp ∈ h.tiles, tp.tile.parts.size ≤ L.maxTilePartsPerTile ∧
      tp.tile.ppt.size ≤ L.maxTilePartsPerTile * (data.size + 1) ∧
      ∀ p ∈ tp.tile.parts, p.data.stop ≤ data.size ∧
        p.markers.size + p.segments.size ≤ data.size + 1 := by
  unfold Header.parse at ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  unfold parseCodestreamIn at ok
  obtain ⟨r,hr,ok⟩ := bind_ok ok
  obtain ⟨⟨mh,t⟩,hm,ok⟩ := bind_ok ok
  iterate 2 obtain ⟨_,_,ok⟩ := bind_ok ok
  obtain ⟨⟨_,_⟩,_,ok⟩ := bind_ok ok
  obtain ⟨ts,hts,ok⟩ := bind_ok ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  obtain ⟨tps,hmap,ok⟩ := bind_ok ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  cases ok
  have td := (main_reader hm).2
  unfold rangeReader at hr
  obtain ⟨mid,hs,hr⟩ := bind_ok hr
  obtain ⟨⟨sub,_⟩,hn,hr⟩ := bind_ok hr
  cases hr
  have de : t.data = data := td.trans ((Reader.take_spec hn).2.2.1.trans (Reader.skip_pos hs).2.2.1)
  refine Tier2WF.arrayMapM_mem _ _ _ ?_ _ hmap
  intro tile ht tp ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  cases ok
  obtain ⟨⟨hp,hw⟩,hs⟩ := tileParts_table hts tile ht
  rw [de] at hw hs
  exact ⟨hp, Nat.le_trans hs (Nat.mul_le_mul_right _ hp), hw⟩

/-- Explicit input/limit bound on the fresh buffer and descriptors selected for a
parsed tile. PPM counts repetitions of chunk indexes; PPT counts the checked tile's
header records. Inline packet headers allocate no separate stream. -/
theorem parsed_headerStream {L : Limits} {data : ByteArray} {h : Header} {tp : TileParams}
    {ranks : Array Nat} {stream : HeaderStream} (parsed : Header.parse L data = .ok h)
    (member : tp ∈ h.tiles) (ok : headerStreamAt h data tp ranks = .ok (some stream)) :
    let k := if stream.fromPpm then L.maxTilePartsPerTile * (L.maxTileParts * data.size)
             else L.maxTilePartsPerTile * (data.size + 1)
    stream.ranges.size ≤ k ∧ stream.bytes.size ≤ k * data.size := by
  obtain ⟨parts,ppt,_⟩ := parse_tile_storage parsed tp member
  have ppm := (parse_ppm parsed).2.2
  obtain ⟨hs,hb,_⟩ := headerStreamAt_storage ok
  dsimp only
  split <;> rename_i hm <;> simp only [hm, ↓reduceIte] at hs hb
  · have mul := Nat.mul_le_mul parts ppm
    exact ⟨Nat.le_trans hs mul,Nat.le_trans hb (Nat.mul_le_mul_right _ mul)⟩
  · exact ⟨Nat.le_trans hs ppt,Nat.le_trans hb (Nat.mul_le_mul_right _ ppt)⟩

/-- Source-level copy accounting for the append fold. Each step charges its
extracted piece and a full copy of the new accumulator, allowing every append to
reallocate. This counts byte writes, independent of a runtime's capacity policy. -/
def chargedGather (data : ByteArray) : List ByteRange → ByteArray → ByteArray × Nat
  | [], acc => (acc,0)
  | r :: rs, acc =>
    let piece := r.bytes data
    let next := acc ++ piece
    let tail := chargedGather data rs next
    (tail.1, piece.size + next.size + tail.2)

private theorem charged_prefix (data : ByteArray) (rs : List ByteRange) (a : ByteArray) :
    (chargedGather data rs a).1 = rs.foldl (fun acc r => acc ++ r.bytes data) a ∧
    (chargedGather data rs a).2 ≤ rs.length * (2 * (a.size + (rs.map (copied data)).sum)) := by
  induction rs generalizing a with
  | nil => simp [chargedGather]
  | cons r rs ih =>
    obtain ⟨eq,hb⟩ := ih (a ++ r.bytes data)
    have bytes : (r.bytes data).size = copied data r := by simp [ByteRange.bytes,copied]
    simp only [ByteArray.size_append,bytes] at hb
    simp only [chargedGather,List.foldl_cons,List.length_cons,List.map_cons,
      List.sum_cons,ByteArray.size_append,bytes]
    rw [Nat.add_assoc] at hb
    refine ⟨eq,?_⟩
    rw [Nat.succ_mul]
    omega

/-- Erasing the copy counter recovers the real gather. For k source ranges and B
output bytes, including overlapping ranges, even full reallocation at every append
charges at most 2 k B bytes. The theorem can be applied to any visited prefix. -/
theorem gather_copy_charge (data : ByteArray) (rs : Array ByteRange) :
    let run := chargedGather data rs.toList ByteArray.empty
    run.1 = gatherBytes data rs ∧ run.2 ≤ rs.size * (2 * (gatherBytes data rs).size) := by
  obtain ⟨he,hc⟩ := charged_prefix data rs.toList ByteArray.empty
  exact ⟨by rwa [gatherBytes, ← Array.foldl_toList],
    by simpa only [Array.length_toList,ByteArray.size_empty,Nat.zero_add,(gatherBytes_size ..).1] using hc⟩

/-- Copy accounting for the fragmented branch of tier1Input: first gather each
segment, then append that segment to the accumulating block buffer. The second
charge allows a full copy of that larger buffer. -/
def chargedBlock (data : ByteArray) : List Segment → ByteArray × Array Tier1.Seg →
    (ByteArray × Array Tier1.Seg) × Nat
  | [], acc => (acc,0)
  | s :: ss, acc =>
    let (piece, inner) := chargedGather data s.ranges.toList ByteArray.empty
    let next := acc.1 ++ piece
    let tail := chargedBlock data ss (next, acc.2.push
      { start := acc.1.size, stop := acc.1.size + piece.size, passes := s.passes })
    (tail.1, inner + next.size + tail.2)

private theorem charged_segments (data : ByteArray) (ss : List Segment) (a : ByteArray × Array Tier1.Seg)
    (cap : Nat) (fits : a.1.size + (ss.map (fun s => (s.bytes data).size)).sum ≤ cap) :
    (chargedBlock data ss a).1 = ss.foldl (Equiv.concatStep data) a ∧
    (chargedBlock data ss a).2 ≤ (2 * blockRanges ss + ss.length) * cap := by
  induction ss generalizing a with
  | nil => simp [chargedBlock,blockRanges]
  | cons s ss ih =>
    have charge := gather_copy_charge data s.ranges
    change (chargedGather data s.ranges.toList ByteArray.empty).1 = s.bytes data ∧
      (chargedGather data s.ranges.toList ByteArray.empty).2 ≤ s.ranges.size * (2 * (s.bytes data).size) at charge
    simp only [List.map_cons,List.sum_cons] at fits
    have next : (Equiv.concatStep data a s).1.size = a.1.size + (s.bytes data).size := by
      simp [Equiv.concatStep]
    obtain ⟨eq,hb⟩ := ih (Equiv.concatStep data a s) (by rw [next]; omega)
    have inner := Nat.le_trans charge.2 (Nat.mul_le_mul_left s.ranges.size
      (Nat.mul_le_mul_left 2 (show (s.bytes data).size ≤ cap by omega)))
    rw [← Nat.mul_assoc, Nat.mul_comm s.ranges.size 2] at inner
    simp only [chargedBlock,charge.1,List.foldl_cons]
    refine ⟨eq,?_⟩
    change _ + (a.1 ++ s.bytes data).size + (chargedBlock data ss (Equiv.concatStep data a s)).2 ≤
      (2 * (s.ranges.size + blockRanges ss) + (ss.length + 1)) * cap
    rw [ByteArray.size_append, Nat.mul_add]
    rw [show 2*s.ranges.size + 2*blockRanges ss + (ss.length + 1) =
      (2*s.ranges.size + 1) + (2*blockRanges ss + ss.length) by omega, Nat.add_mul, Nat.add_mul,
      Nat.one_mul]
    omega

/-- Exact erasure and conservative cumulative byte-write budget for the full
fragmented Tier-1 input, charging every byte extraction and both levels of append.
The cap is explicit in source range count K, segment count S and input length N. -/
theorem tier1Input_copy_charge (data : ByteArray) (cb : CodeBlock)
    (fragmented : cb.segments.all (·.ranges.size ≤ 1) = false) :
    let run := chargedBlock data cb.segments.toList (ByteArray.empty,#[])
    run.1 = Assemble.tier1Input data cb ∧ run.2 ≤
      (2 * blockRanges cb.segments.toList + cb.segments.size) * (blockRanges cb.segments.toList * data.size) := by
  have h := charged_segments data cb.segments.toList (ByteArray.empty,#[]) _
    (by simpa using block_sum_bound data cb.segments.toList)
  refine ⟨?_, by simpa using h.2⟩
  simp only [Assemble.tier1Input, fragmented, Bool.false_eq_true, ↓reduceIte, ← Array.foldl_toList]
  exact h.1

/-- Count extracted bytes plus the full resulting buffer on each successful tile
append. A truncated part returns immediately and preserves the charge incurred
by earlier parts. The offset table uses one triple per appended part. -/
def chargedTile (data : ByteArray) : List TilePartHeader → ByteArray × Array (Nat × Nat × Nat) →
    Except Error (ByteArray × Array (Nat × Nat × Nat)) × Nat
  | [], a => (.ok a,0)
  | p :: ps, a =>
    if p.data.stop > data.size then
      (.error (.truncated (locAt p.data.offset) "tile-part data past the end of the input"),0)
    else
      let piece := p.data.bytes data
      let next := a.1 ++ piece
      let tail := chargedTile data ps (next, a.2.push (a.1.size,p.data.offset,p.data.length))
      (tail.1, piece.size + next.size + tail.2)

private theorem chargedTile_erase (data : ByteArray) (ps : List TilePartHeader)
    (a : ByteArray × Array (Nat × Nat × Nat)) :
    (chargedTile data ps a).1 = forIn ps a (fun p s =>
      if p.data.stop > data.size then throw (Error.truncated (locAt p.data.offset)
        "tile-part data past the end of the input")
      else pure (.yield (s.1 ++ p.data.bytes data,s.2.push (s.1.size,p.data.offset,p.data.length)))) := by
  induction ps generalizing a with
  | nil => rfl
  | cons p ps ih =>
    rw [List.forIn_cons,chargedTile]
    split
    · rfl
    · exact ih _

private theorem chargedTile_bounds (data : ByteArray) (ps : List TilePartHeader)
    (a : ByteArray × Array (Nat × Nat × Nat)) (cap : Nat)
    (hc : a.1.size + ps.length * data.size ≤ cap) :
    let run := chargedTile data ps a
    run.2 ≤ ps.length * (data.size + cap) ∧
    ∀ z, run.1 = .ok z → z.1.size ≤ cap ∧ z.2.size = a.2.size + ps.length := by
  induction ps generalizing a with
  | nil =>
    simp only [chargedTile,List.length_nil,Nat.zero_mul,Nat.add_zero,Except.ok.injEq] at hc ⊢
    exact ⟨Nat.le_refl _, fun _ eq => eq ▸ ⟨hc,rfl⟩⟩
  | cons p ps ih =>
    simp only [chargedTile]
    split
    · exact ⟨Nat.zero_le _,fun _ eq => by cases eq⟩
    · simp only [List.length_cons,Nat.succ_mul] at hc
      have piece : (p.data.bytes data).size ≤ data.size := by simp [ByteRange.bytes]; omega
      have hn : (a.1 ++ p.data.bytes data).size + ps.length * data.size ≤ cap := by
        rw [ByteArray.size_append]; omega
      obtain ⟨cost,ret⟩ := ih (a.1 ++ p.data.bytes data, a.2.push (a.1.size,p.data.offset,p.data.length)) hn
      simp only [List.length_cons,Nat.succ_mul]
      refine ⟨by omega,fun z eq => ?_⟩
      obtain ⟨sz,cnt⟩ := ret z eq
      exact ⟨sz,by simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using cnt⟩

/-- Byte writes of tile data assembly, with exact error erasure. A parsed tile has
at most maxTilePartsPerTile parts; the bound also covers a failing assembly call
with an arbitrary list of overlapping or invalid ranges. -/
theorem tileData_copy_charge (data : ByteArray) (t : Tile) :
    let run := chargedTile data t.parts.toList (ByteArray.empty,#[])
    (do let a ← run.1; pure (a.1,a.2.toList)) = tileData data t ∧
    run.2 ≤ t.parts.size * (data.size + t.parts.size * data.size) ∧
    ∀ buf parts, tileData data t = .ok (buf,parts) →
      buf.size ≤ t.parts.size * data.size ∧ parts.length = t.parts.size := by
  dsimp only
  have erase : (do let a ← (chargedTile data t.parts.toList (ByteArray.empty,#[])).1
                   pure (a.1,a.2.toList)) = tileData data t := by
    rw [chargedTile_erase, tileData, ← Array.forIn_toList]
    rfl
  obtain ⟨hc,hr⟩ := chargedTile_bounds data t.parts.toList (ByteArray.empty,#[])
    (t.parts.size * data.size) (by simp)
  refine ⟨erase, by simpa using hc,?_⟩
  intro buf parts ok
  rw [← erase] at ok
  obtain ⟨a,ha,ok⟩ := bind_ok ok
  cases ok
  simpa using hr a ha

/-- On reaching the JP2 palette table, the actual row reader reserves NE × NPC
UInt64 slots and traverses one field per column and row. This equation includes
errors from the row reader. A rejected header can have performed this allocation. -/
theorem palette_table {L : Limits} {b : Box.BoxHdr} {ne : UInt16} {npc : UInt8}
    {r1 r2 r3 : Reader} {bits : Array UInt8}
    (h1 : b.body.u16be = .ok (ne,r1)) (h2 : r1.u8 = .ok (npc,r2))
    (rows : 1 ≤ ne.toNat ∧ ne.toNat ≤ 1024)
    (limit : L.check (.atOffset .box b.start) .paletteEntries ne.toNat = .ok ())
    (cols : 0 < npc.toNat) (tags : npc.toNat ≤ r2.remaining)
    (hb : Box.readMany Reader.u8 r2 (Array.emptyWithCapacity npc.toNat) npc.toNat = .ok (bits,r3))
    (depth : bits.any (fun x => (x &&& 0x7F) + 1 > 38) = false)
    (bytes : ne.toNat * bits.foldl (fun s x => s + Box.entryBytes x) 0 ≤ r3.remaining) :
    bits.size = npc.toNat ∧
    ne.toNat * bits.size ≤ min L.maxPaletteEntries 1024 * 255 ∧
    Box.parsePclr L b = (do
      let (entries,_) ← Box.parsePclr.rows (fun r a =>
        bits.foldlM (fun (a,r) bi => do
          let (v,r) ← Box.readBE r 0 (Box.entryBytes bi)
          pure (a.push v,r)) (a,r)) r3 (Array.emptyWithCapacity (ne.toNat * npc.toNat)) ne.toNat
      return { ne := ne.toNat, npc := npc.toNat, bits, entries }) := by
  have many (n : Nat) (r : Reader) (a : Array UInt8) (out : Array UInt8 × Reader)
      (ok : Box.readMany Reader.u8 r a n = .ok out) : out.1.size = a.size + n := by
    induction n generalizing r a with
    | zero => cases ok; rfl
    | succ n ih =>
      rw [Box.readMany] at ok
      obtain ⟨⟨x,t⟩,_,ok⟩ := bind_ok ok
      rw [ih t (a.push x) ok, Array.size_push]
      omega
  have count : bits.size = npc.toNat := by simpa using many _ _ _ _ hb
  have hlim : ne.toNat ≤ L.maxPaletteEntries := checked limit
  have colmax := npc.toNat_lt
  refine ⟨count, Nat.mul_le_mul (by omega) (by omega), ?_⟩
  have nz : (ne.toNat == 0) = false := by simp; omega
  have nc : (npc.toNat == 0) = false := by simp; omega
  have upper := Nat.not_lt.mpr rows.2
  have enough := Nat.not_lt.mpr tags
  have fits := Nat.not_lt.mpr bytes
  simp only [Box.parsePclr, h1,h2,bind,Except.bind,nz,nc,upper,decide_false,
    Bool.false_or, Bool.false_eq_true, ↓reduceIte,limit,enough,hb,depth,fits]

/-- The actual JP2 superbox depth guard runs before the child loop. -/
theorem jp2h_depth_excess (L : Limits) (b : Box.BoxHdr) (count : Nat) (h : L.maxBoxDepth < 1) :
    Box.parseJp2h L b count = .error (.limitExceeded (.atOffset .box b.start) .boxDepth 1
      L.maxBoxDepth) := by
  simp [Box.parseJp2h,Limits.check,Limits.checkLe,Limits.bound,Nat.not_le.mpr h,bind,Except.bind]


private def countedFor {α β : Type} (f : α → β → Except Error (ForInStep β) × Nat) :
    List α → β → Except Error β × Nat
  | [], a => (.ok a,0)
  | x :: xs, a =>
    let step := f x a
    match step.1 with
    | .error e => (.error e, step.2)
    | .ok (.done z) => (.ok z, step.2)
    | .ok (.yield b) =>
      let tail := countedFor f xs b
      (tail.1,step.2 + tail.2)

private theorem countedFor_spec {α β : Type} (f : α → β → Except Error (ForInStep β) × Nat)
    (xs : List α) (a : β) (bound : Nat) (hf : ∀ x b, (f x b).2 ≤ bound) :
    (countedFor f xs a).1 = forIn xs a (fun x b => (f x b).1) ∧
    (countedFor f xs a).2 ≤ xs.length * bound := by
  induction xs generalizing a with
  | nil => exact ⟨rfl,by simp [countedFor]⟩
  | cons x xs ih =>
    simp only [countedFor,List.length_cons,Nat.succ_mul,List.forIn_cons]
    have step := hf x a
    cases he : (f x a).1 with
    | error e => exact ⟨rfl,by dsimp; omega⟩
    | ok v =>
      cases v with
      | done b => exact ⟨rfl,by dsimp; omega⟩
      | yield b =>
        obtain ⟨eq,hb⟩ := ih b
        exact ⟨eq,by dsimp; omega⟩

private def countedTile (L : Limits) (s : SIZ) (t : Nat) (c : Coding) (tot : Totals) :
    Except Error Totals × Nat :=
  countedFor (fun i a => (do
    let (cb,pr) := tileCompCounts (compRect (tileRect s t) (s.components.getD i default))
      (c.comps.getD i default)
    let z : Totals := ⟨a.codeBlocks + cb,a.precincts + pr,a.packets + c.layers*pr⟩
    L.check (.atOffset .marker 2) .codeBlocks z.codeBlocks
    L.check (.atOffset .marker 2) .precincts z.precincts
    L.check (.atOffset .marker 2) .packets z.packets
    pure (.yield z), 1)) (List.range' 0 s.csiz) tot

private theorem countedTile_spec (L : Limits) (s : SIZ) (t : Nat) (c : Coding) (tot : Totals) :
    (countedTile L s t c tot).1 = addTile L s t c tot ∧ (countedTile L s t c tot).2 ≤ s.csiz := by
  unfold countedTile addTile
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', bind_pure]
  have hs (n : Nat) : [:n].size = n := by simp [Std.Legacy.Range.size]
  simp only [hs]
  constructor
  · rw [(countedFor_spec _ _ _ 1 (by intros; exact Nat.le_refl _)).1]
  · calc
      _ ≤ (List.range' 0 s.csiz).length * 1 := (countedFor_spec _ _ _ 1 (fun _ _ => Nat.le_refl 1)).2
      _ = s.csiz := by simp

/-- Evaluations of tileCompCounts in the actual checkWork traversal, counting the
component whose check first fails. Each evaluation folds its component's NL+1
resolution indices. -/
def chargedCheckWork (L : Limits) (s : SIZ) (defaults : Coding) (tiles : Array TileParams) :
    Except Error Totals × Nat :=
  let run := countedFor (fun t (a : Totals × Nat) =>
    let here := match tiles[a.2]? with
      | some tp => if tp.index = t then some tp.coding else none
      | none => none
    let run := countedTile L s t (here.getD defaults) a.1
    (run.1.map (fun tot => .yield (tot,if here.isSome then a.2+1 else a.2)),run.2))
    (List.range' 0 (numTiles s)) ({},0)
  (run.1.map Prod.fst,run.2)

/-- After the early SIZ grid check, both successful and rejecting checkWork
calls evaluate the per-component geometry fold at most maxCodeBlocks times. -/
theorem checkWork_visits {L : Limits} {mh : MainHeader} (d : Coding) (tiles : Array TileParams)
    (grid : checkGeometry L mh = .ok ()) :
    (chargedCheckWork L mh.siz d tiles).1 = checkWork L mh.siz d tiles ∧
    (chargedCheckWork L mh.siz d tiles).2 ≤ L.maxCodeBlocks := by
  have hlim := ((Resources.checkGeometry_ok_iff L mh).1 grid).2.2.2.2
  unfold chargedCheckWork checkWork
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  have hs (n : Nat) : [:n].size = n := by simp [Std.Legacy.Range.size]
  simp only [hs]
  constructor
  · rw [(countedFor_spec _ _ _ mh.siz.csiz (fun _ _ => (countedTile_spec ..).2)).1]
    apply congrArg (fun x : Except Error (Totals × Nat) => x.map Prod.fst)
    congr 1
    funext t a
    dsimp only
    rw [(countedTile_spec ..).1]
    cases ht : tiles[a.2]? with
    | none =>
      simp only [Option.isSome_none,Bool.false_eq_true,↓reduceIte,Option.getD_none]
      cases addTile L mh.siz t d a.1 <;> rfl
    | some tp =>
      by_cases hi : tp.index = t
      · simp only [hi,↓reduceIte,Option.isSome_some,Option.getD_some]
        cases addTile L mh.siz t tp.coding a.1 <;> rfl
      · simp only [hi,↓reduceIte,Option.isSome_none,Bool.false_eq_true,Option.getD_none]
        cases addTile L mh.siz t d a.1 <;> rfl
  · calc
      _ ≤ (List.range' 0 (numTiles mh.siz)).length * mh.siz.csiz :=
        (countedFor_spec _ _ _ _ (fun _ _ => (countedTile_spec ..).2)).2
      _ ≤ L.maxCodeBlocks := by simpa using hlim

/-- The real PPM splitter has a fuel cap on rejecting inputs too. Each recursive
edge spent four Nppm bytes and passed the chunk-count check. The terminal visit
includes a possible truncated length, missing payload or excess chunk. -/
theorem ppmChunks_fuel (L : Limits) (data : ByteArray) (loc : Location) (f g : Nat)
    (xs : List ByteRange) (a : Array (Array ByteRange))
    (hf : min (rangeBytes xs / 4) (L.maxTileParts - a.size) < f)
    (hg : min (rangeBytes xs / 4) (L.maxTileParts - a.size) < g) :
    ppmChunks L data loc f xs a = ppmChunks L data loc g xs a := by
  induction f generalizing g xs a with
  | zero => omega
  | succ f ih =>
    cases g with
    | zero => omega
    | succ g =>
      cases xs with
      | nil => rfl
      | cons x xs =>
        simp only [ppmChunks,bind,Except.bind]
        split <;> first | rfl | skip
        rename_i u hc
        have hl : a.size + 1 ≤ L.maxTileParts := checked hc
        split <;> first | rfl | skip
        rename_i nb rest hn
        have h4 := (takeRanges_account _ _ _ _ _ hn).2.1
        split <;> first | rfl | skip
        split <;> first | rfl | skip
        rename_i chunk tail ht
        have hb := (takeRanges_account _ _ _ _ _ ht).2.1
        apply ih <;> simp only [Array.size_push] <;> omega

private def measuredDup : List UInt8 → Option UInt8 × Nat
  | [] | [_] => (none, 0)
  | a :: b :: rest =>
    if a == b then (some a, 1)
    else
      let next := measuredDup (b :: rest)
      (next.1, next.2+1)

private theorem duplicate_checks (xs : List UInt8) :
    (measuredDup xs).1 = TilePart.firstDup xs ∧ (measuredDup xs).2 ≤ xs.length := by
  induction xs with
  | nil => exact ⟨rfl, Nat.zero_le _⟩
  | cons a xs ih =>
    cases xs with
    | nil => exact ⟨rfl, Nat.zero_le _⟩
    | cons b rest =>
      simp only [measuredDup, TilePart.firstDup]
      split
      · exact ⟨rfl, by simp⟩
      · exact ⟨ih.1, Nat.succ_le_succ ih.2⟩

/-- Charge sorting comparisons, one key-list entry per pointer, and each adjacent
key test up to and including the first duplicate. -/
def measuredSortUnique {α : Type} (key : α → UInt8) (loc : Location)
    (what : String) (xs : Array α) : Except Error (Array α) × Nat :=
  let sorted := measuredSort (fun a b => key a < key b) xs
  let keys := sorted.1.toList.map key
  let duplicates := measuredDup keys
  let result := match duplicates.1 with
    | some z => .error (.malformed loc s!"duplicate {what} = {z}")
    | none => .ok sorted.1
  (result, sorted.2 + keys.length + duplicates.2)

/-- The TLM, PPM, PPT and PLT sort uses at most `n*n + 2*n` charged operations
for `n` entries and preserves the exact result or duplicate-key diagnostic. -/
theorem sortUnique_work {α : Type} (key : α → UInt8) (loc : Location)
    (what : String) (xs : Array α) :
    let m := measuredSortUnique key loc what xs
    m.1 = TilePart.sortUnique key loc what xs ∧ m.2 ≤ xs.size * xs.size + 2*xs.size := by
  let lt := fun a b => decide (key a < key b)
  obtain ⟨sortEq, sortCost⟩ := measuredSort_work lt xs
  have len : (measuredSort lt xs).1.size = xs.size :=
    sortEq ▸ (insertionSort_perm lt xs).size_eq
  obtain ⟨dupEq, dupCost⟩ := duplicate_checks ((measuredSort lt xs).1.toList.map key)
  simp only [List.length_map, Array.length_toList, len] at dupCost
  unfold measuredSortUnique TilePart.sortUnique
  change _ ∧ (measuredSort lt xs).2 + (((measuredSort lt xs).1.toList.map key).length) +
    (measuredDup ((measuredSort lt xs).1.toList.map key)).2 ≤ _
  constructor
  · simp only [lt] at sortEq dupEq
    dsimp only
    rw [dupEq, sortEq]
    cases TilePart.firstDup ((xs.insertionSort fun a b => key a < key b).toList.map key) <;> rfl
  · simp only [List.length_map, Array.length_toList, len]
    omega


end JPEG2000.Spec.Resources.HeaderWork
