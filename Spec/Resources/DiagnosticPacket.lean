import Spec.Resources.NativeCost
import Spec.Resources.DiagnosticPacketRanges
import Spec.Resources.DiagnosticCost
import Spec.RoundTrip.InitAdmission

/-!
# Tier-2 diagnostic construction (Plan.md §§3–5, 7, S3; T.800 A.7–A.8, B.5–B.12)

The public SOP and PPM results in `DiagnosticCost.public_sop` and
`DiagnosticCost.public_ppm_mismatch` bound those calls in isolation.
Here the packet walk records the failed optional SOP peek before the callback's
final result. The shared rank check precedes all tile visits. After selection,
bounded successful reader and code-block states feed the next attempted read.

`records` follows the public grid through packed validation and the geometry lookup
at entry to centred-tile reconstruction. `decode_work` adds its diagnostic charge
to the native meter, which already accounts for raw-store translation and placement.
-/

namespace JPEG2000.Spec.Resources.DiagnosticPacket

open JPEG2000.Bytes JPEG2000.Header JPEG2000.Progression JPEG2000.Tier2.Packet
open JPEG2000.Tier2.Headers PacketTraversal DiagnosticCost

/-- The actual construction at a single refusing operation. Limit ceilings are borrowed. -/
structure Fault (cap : Nat) (e : Error) where
  /-- Location stored in the new error record. -/
  offset : e.offset?.getD 0 ≤ cap
  /-- Tree of the emitted text, or the binary value supplied to a refusing check. -/
  payload : match e with
    | .malformed _ s | .truncated _ s | .unsupported _ s => Built cap s
    | .limitExceeded _ _ v _ => PLift (v ≤ cap)

/-- A strict subcomputation, which constructs a single diagnosis on its first error.
The successful postcondition threads the actual reader and code-block facts forward. -/
def Scan {α : Type} (cap : Nat) (P : α → Prop) : Except Error α → Type
  | .error e => Fault cap e
  | .ok a => PLift (P a)

private def chain {α β : Type} {cap : Nat} {P : α → Prop} {Q : β → Prop}
    {x : Except Error α} {f : α → Except Error β} (first : Scan cap P x)
    (next : ∀ a, P a → Scan cap Q (f a)) : Scan cap Q (x >>= f) := by
  cases x with
  | error => exact first
  | ok a => exact next a first.down

private def walkList {α β : Type} {cap : Nat} (P : β → Prop)
    (f : α → β → Except Error (ForInStep β)) (xs : List α) (s : β) (start : P s)
    (each : ∀ x ∈ xs, ∀ b, P b → Scan cap (fun y : ForInStep β => P y.value) (f x b)) :
    Scan cap P (forIn xs s f) := by
  match xs with
  | [] => exact ⟨start⟩
  | x :: xs =>
    rw [List.forIn_cons]
    apply chain (each x (.head _) s start)
    intro y good
    cases y with
    | done => exact ⟨good⟩
    | yield => exact walkList P f xs _ good (fun z hz => each z (.tail _ hz))

private def bitScan (cap : Nat) (b : BitReader) (h : b.data.size ≤ cap) :
    Scan cap (fun z : UInt32 × BitReader => z.2.data.size ≤ cap) b.bit := by
  unfold BitReader.bit
  split
  · unfold BitReader.load
    split
    · exact ⟨h⟩
    · exact ⟨Nat.le_trans b.pos_le (Nat.le_trans b.stop_le h),oneFixed _ (by decide)⟩
  · exact ⟨h⟩

private def nextBit (cap : Nat) (b : BitReader) (h : b.data.size ≤ cap) :
    Scan cap (fun z : Bool × BitReader => z.2.data.size ≤ cap) (readBit b) := by
  let seen := bitScan cap b h
  unfold readBit TagTree.bitNext
  cases eq : b.bit with
  | error e => rw [eq] at seen; exact seen
  | ok pair =>
    obtain ⟨_,t⟩ := pair
    rw [eq] at seen
    exact ⟨seen.down⟩

private def fieldAux (cap : Nat) (b : BitReader) (h : b.data.size ≤ cap) (a : UInt32) (k : Nat) :
    Scan cap (fun z : UInt32 × BitReader => z.2.data.size ≤ cap) (b.bitsAux a k) := by
  match k with
  | 0 => exact ⟨h⟩
  | k+1 =>
    unfold BitReader.bitsAux
    apply chain (bitScan cap b h)
    rintro ⟨x,t⟩ ht
    exact fieldAux cap t ht _ k

/-- The field guard formats its actual requested width before reading any bits.
A truncated shorter field reports the position of its first failed refill. -/
def field (cap : Nat) (b : BitReader) (n : Nat) (hb : b.data.size ≤ cap) (hn : n ≤ cap) :
    Scan cap (fun z : UInt32 × BitReader => z.2.data.size ≤ cap) (b.bits n) := by
  unfold BitReader.bits
  split
  · exact fieldAux cap b hb 0 n
  · exact ⟨Nat.le_trans b.pos_le (Nat.le_trans b.stop_le hb),closeExpr
      (catExpr (catExpr (litExpr _ "bit field of ") (decExpr hn)) (litExpr _ " > 32 bits"))
      (by decide) (by decide)⟩

private def alignScan (cap : Nat) (b : BitReader) (h : b.data.size ≤ cap) :
    Scan cap (fun t : BitReader => t.data.size ≤ cap) b.align := by
  unfold BitReader.align
  split
  · split
    · exact ⟨h⟩
    · exact ⟨Nat.le_trans b.pos_le (Nat.le_trans b.stop_le h),oneFixed _ (by decide)⟩
  · exact ⟨h⟩

private def ephScan (cap : Nat) (r : Reader) (hr : r.data.size ≤ cap) :
    Scan cap (fun t : Reader => t.data.size ≤ cap) (readEph r) := by
  unfold readEph Reader.u16be
  split
  · simp only [bind,Except.bind]
    split
    · exact ⟨Nat.le_trans r.pos_le_size hr,oneFixed _ (by decide)⟩
    · exact ⟨hr⟩
  · exact ⟨Nat.le_trans r.pos_le_size hr,oneFixed _ (by decide)⟩

private def treeBits (cap : Nat) (n low : Nat) (b : BitReader) (hb : b.data.size ≤ cap) :
    Scan cap (fun z : Nat × Bool × BitReader => z.2.2.data.size ≤ cap)
      (JPEG2000.TagTree.readLoop TagTree.bitNext n low b) := by
  match n with
  | 0 => exact ⟨hb⟩
  | k+1 =>
    unfold JPEG2000.TagTree.readLoop
    let seen := nextBit cap b hb
    change Scan cap _ (TagTree.bitNext b) at seen
    cases eq : TagTree.bitNext b with
    | error => rw [eq] at seen; exact seen
    | ok z =>
      obtain ⟨flag,t⟩ := z
      rw [eq] at seen
      cases flag
      · exact treeBits cap k _ t seen.down
      · exact ⟨seen.down⟩

private abbrev NodeOut := Nat × Nat × Array Nat × Array Nat × BitReader

private def nodeScan (cap t i l : Nat) (lo va : Array Nat) (b : BitReader) (hb : b.data.size ≤ cap) :
    Scan cap (fun z : NodeOut => z.2.2.2.2.data.size ≤ cap)
      (TagTree.nodeStep TagTree.bitNext t i l lo va b) := by
  unfold TagTree.nodeStep
  dsimp only
  split
  · exact ⟨hb⟩
  · let seen := treeBits cap (t - max l (lo.getD i 0)) (max l (lo.getD i 0)) b hb
    split
    · rename_i eq
      rw [eq] at seen
      exact seen
    · rename_i eq
      rw [eq] at seen
      split <;> exact ⟨seen.down⟩

private def pathScan (cap t n off w h x y : Nat) (lo va : Array Nat) (b : BitReader)
    (hb : b.data.size ≤ cap) :
    Scan cap (fun z : NodeOut => z.2.2.2.2.data.size ≤ cap)
      (JPEG2000.TagTree.walk TagTree.bitNext t n off w h x y lo va b) := by
  match n with
  | 0 => exact ⟨Nat.zero_le _,oneFixed _ (by decide)⟩
  | 1 => exact nodeScan cap t _ _ lo va b hb
  | k+2 =>
    unfold JPEG2000.TagTree.walk
    let seen := pathScan cap t (k+1) (off+w*h) ((w+1)/2) ((h+1)/2) (x/2) (y/2) lo va b hb
    split
    · rename_i eq; rw [eq] at seen; exact seen
    · rename_i eq; rw [eq] at seen; exact nodeScan cap t _ _ _ _ _ seen.down

private def inclusionScan (cap : Nat) (tr : TagTree.Tree) (b : BitReader) (k t : Nat)
    (hb : b.data.size ≤ cap) :
    Scan cap (fun z : Bool × TagTree.Tree × BitReader => z.2.2.data.size ≤ cap)
      (TagTree.decode tr b k t) := by
  unfold TagTree.decode TagTree.decodeWith
  split
  · let seen := pathScan cap t tr.numLevels 0 tr.w tr.h (k%tr.w) (k/tr.w) tr.low tr.val b hb
    split
    · rename_i eq; rw [eq] at seen; exact seen
    · rename_i eq; rw [eq] at seen; exact ⟨seen.down⟩
  · exact ⟨Nat.zero_le _,oneFixed _ (by decide)⟩

private def valueScan (cap k n t : Nat) (tr : TagTree.Tree) (b : BitReader) (hb : b.data.size ≤ cap) :
    Scan cap (fun z : Nat × TagTree.Tree × BitReader => z.2.2.data.size ≤ cap)
      (TagTree.valueLoop TagTree.bitNext k n t tr b) := by
  match n with
  | 0 => exact ⟨Nat.zero_le _,oneFixed _ (by decide)⟩
  | f+1 =>
    unfold TagTree.valueLoop
    let seen := inclusionScan cap tr b k t hb
    change Scan cap _ (TagTree.decodeWith TagTree.bitNext tr b k t) at seen
    split
    · rename_i eq; rw [eq] at seen; exact seen
    · rename_i eq; rw [eq] at seen
      split
      · exact ⟨seen.down⟩
      · exact valueScan cap k f (t+1) _ _ seen.down

private def passesScan (cap : Nat) (b : BitReader) (hb : b.data.size ≤ cap) (wire : 7 ≤ cap) :
    Scan cap (fun z : Nat × BitReader => 0 < z.1 ∧ z.1 ≤ 2^32+37 ∧ z.2.data.size ≤ cap)
      (readNumPasses b) := by
  unfold readNumPasses
  apply chain (nextBit cap b hb)
  rintro ⟨f,t⟩ ht
  cases f
  · exact ⟨by dsimp; decide, by dsimp; decide, ht⟩
  · apply chain (nextBit cap t ht)
    rintro ⟨f,t⟩ ht
    cases f
    · exact ⟨by dsimp; decide, by dsimp; decide, ht⟩
    · apply chain (field cap t 2 ht (by omega))
      rintro ⟨v,t⟩ ht
      dsimp only
      split
      · exact ⟨by omega, by dsimp; have := v.toNat_lt; omega, ht⟩
      · apply chain (field cap t 5 ht (by omega))
        rintro ⟨v,t⟩ ht
        dsimp only
        split
        · exact ⟨by omega, by dsimp; have := v.toNat_lt; omega, ht⟩
        · apply chain (field cap t 7 ht wire)
          rintro ⟨v,t⟩ ht
          exact ⟨by omega, by dsimp; have := v.toNat_lt; omega, ht⟩

private def commaScan (cap n a : Nat) (b : BitReader) (hb : b.data.size ≤ cap) :
    Scan cap (fun z : Nat × BitReader => z.1 < a+n ∧ z.2.data.size ≤ cap) (commaCode n a b) := by
  match n with
  | 0 => exact ⟨Nat.le_trans b.pos_le (Nat.le_trans b.stop_le hb),oneFixed _ (by decide)⟩
  | k+1 =>
    unfold commaCode
    apply chain (nextBit cap b hb)
    rintro ⟨f,t⟩ ht
    cases f
    · exact ⟨by omega,ht⟩
    · simpa only [↓reduceIte,Nat.add_assoc,Nat.add_comm 1 k] using commaScan cap k (a+1) t ht

private def post {α : Type} {cap : Nat} {P Q : α → Prop} {x : Except Error α}
    (scan : Scan cap P x) (f : ∀ a, x = .ok a → P a → Q a) : Scan cap Q x := by
  cases x with
  | error => exact scan
  | ok a => exact ⟨f a rfl scan.down⟩

private def check (cap : Nat) (L : Limits) (l : Location) (k : LimitKind) (n : Nat)
    (off : l.offset.getD 0 ≤ cap) (hn : n ≤ cap) :
    Scan cap (fun _ => n ≤ L.bound k) (L.check l k n) := by
  unfold Limits.check Limits.checkLe
  split
  · exact ⟨by assumption⟩
  · exact ⟨off,⟨hn⟩⟩

private abbrev WirePieces (ps : List (Nat × Nat)) := ∀ x ∈ ps, x.2 ≤ 2^32

private def lengthsScan (cap lb : Nat) (ps : List Nat) (b : BitReader) (hb : b.data.size ≤ cap)
    (width : ∀ p ∈ ps, lb + p.log2 ≤ cap) :
    Scan cap (fun z : List (Nat × Nat) × BitReader =>
      z.2.data.size ≤ cap ∧ WirePieces z.1 ∧ (z.1.map Prod.fst) = ps ∧ (ps ≠ [] → lb ≤ 32))
      (readLengths lb ps b) := by
  match ps with
  | [] => exact ⟨hb,by simp [WirePieces],rfl,by simp⟩
  | p::rest =>
    unfold readLengths
    let step := post (field cap b (lb+p.log2) hb (width p (.head _))) (Q :=
      fun z : UInt32 × BitReader => z.2.data.size ≤ cap ∧ lb ≤ 32) (by
        intro z ok bound
        refine ⟨bound,?_⟩
        unfold BitReader.bits at ok
        split at ok <;> first | contradiction | omega)
    apply chain step
    rintro ⟨len,t⟩ ⟨ht,hl⟩
    apply chain (lengthsScan cap lb rest t ht (fun x hx => width x (.tail _ hx)))
    rintro ⟨rs,t⟩ ⟨ht,wire,eq,_⟩
    refine ⟨ht,?_,congrArg (p :: ·) eq,fun _ => hl⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | mem
    · exact Nat.le_of_lt len.toNat_lt
    · exact wire _ mem

/-- Header values retained by each block for the next packet. -/
def BandOK (L : Limits) (bs : BandState) :=
  ∀ cb ∈ bs.blocks, cb.lblock ≤ 32 ∧ cb.numPasses ≤ L.maxPassesPerCodeBlock

private abbrev COK (L : Limits) (c : Contribution) :=
  WirePieces c.pieces ∧ (c.pieces.map Prod.fst).sum ≤ L.maxPassesPerCodeBlock

private abbrev TablesOK (L : Limits) (cs : Array Contribution) := ∀ c ∈ cs, COK L c

private def blockTail (cap : Nat) (L : Limits) (style bi k : Nat) (bs : BandState)
    (cb : CodeBlock) (b : BitReader) (hb : b.data.size ≤ cap)
    (old : BandOK L bs) (good : cb.lblock ≤ 32 ∧ cb.numPasses ≤ L.maxPassesPerCodeBlock)
    (room : L.maxPassesPerCodeBlock + 2^32 + 101 ≤ cap) :
    Scan cap (fun z : BandState × Option Contribution × BitReader =>
      BandOK L z.1 ∧ (∀ c, z.2.1 = some c → COK L c) ∧ z.2.2.data.size ≤ cap)
      (do
        let n' ← readNumPasses b
        let n := n'.1
        let inc ← commaCode 33 0 n'.2
        let lb := cb.lblock + inc.1
        L.check (locAt inc.2.pos) .passesPerCodeBlock (cb.numPasses+n)
        let fields ← readLengths lb (segmentPasses style n cb.numPasses) inc.2
        let ps := fields.1
        let b := fields.2
        let cb' := {cb with lblock := lb, numPasses := cb.numPasses+n}
        return ({bs with blocks := bs.blocks.setIfInBounds k cb'},
          some { band := bi, block := k, pieces := ps,
                 cont := cb.numPasses > 0 && !passEndsSegment style (cb.numPasses-1)}, b)) := by
  apply chain (passesScan cap b hb (by omega))
  rintro ⟨n,b⟩ ⟨pos,bound,hb⟩
  apply chain (commaScan cap 33 0 b hb)
  rintro ⟨i,b⟩ ⟨inc,hb⟩
  dsimp only at inc pos bound hb ⊢
  apply chain (check cap L (locAt b.pos) .passesPerCodeBlock (cb.numPasses+n)
    (Nat.le_trans b.pos_le (Nat.le_trans b.stop_le hb)) (by omega))
  intro _ accepted
  change cb.numPasses+n ≤ L.maxPassesPerCodeBlock at accepted
  have sum : (segmentPasses style n cb.numPasses).sum = n := by
    rw [Tier2Equiv.segmentPasses_eq,Spec.Tier1.segmentPasses_sum]
  apply chain (lengthsScan cap _ _ b hb (by
    intro p hp
    obtain ⟨a,z,eq⟩ := List.mem_iff_append.mp hp
    rw [eq,List.sum_append_nat,List.sum_cons] at sum
    have := Nat.log2_le_self p
    omega))
  rintro ⟨ps,t⟩ ⟨ht,wire,eq,lb⟩
  have small := lb (by intro empty; rw [empty] at sum; simp at sum; omega)
  refine ⟨?_,?_,ht⟩
  · intro cb' hit
    rcases Array.mem_or_eq_of_mem_setIfInBounds hit with h | rfl
    · exact old _ h
    · exact ⟨small,accepted⟩
  · rintro c eqC; cases eqC
    exact ⟨wire,by dsimp only; rw [eq,sum]; omega⟩

private def blockScan (cap : Nat) (L : Limits) (style layer bi k : Nat) (bs : BandState)
    (b : BitReader) (hb : b.data.size ≤ cap) (old : BandOK L bs)
    (room : L.maxPassesPerCodeBlock+2^32+101 ≤ cap) :
    Scan cap (fun z : BandState × Option Contribution × BitReader =>
      BandOK L z.1 ∧ (∀ c, z.2.1 = some c → COK L c) ∧ z.2.2.data.size ≤ cap)
      (headerBlock L style layer bi k bs b) := by
  unfold headerBlock
  cases look : bs.blocks[k]? with
  | none => exact ⟨Nat.zero_le _,oneFixed _ (by decide)⟩
  | some cb =>
    have good := old _ (Array.mem_of_getElem? look)
    cases prev : cb.included
    · simp only [prev,Bool.false_eq_true,↓reduceIte,pure_bind]
      apply chain (inclusionScan cap bs.incl b k (layer+1) hb)
      rintro ⟨inc,tr,b⟩ hb
      cases inc
      · exact PLift.up ⟨old,(fun _ eq => nomatch eq),hb⟩
      · dsimp only
        apply chain (valueScan cap k (bs.maxZero+2) 0 bs.zbp b hb)
        rintro ⟨z,tr',t⟩ ht
        exact blockTail cap L style bi k {bs with incl := tr, zbp := tr'}
          {cb with included := true, firstLayer := layer, zeroBitPlanes := z} t ht old good room
    · simp only [prev,↓reduceIte,pure_bind]
      apply chain (nextBit cap b hb)
      rintro ⟨inc,t⟩ ht
      cases inc
      · exact PLift.up ⟨old,(fun _ eq => nomatch eq),ht⟩
      · dsimp only
        simp only [Bool.not_true,Bool.false_eq_true,↓reduceIte]
        simpa only [prev] using blockTail cap L style bi k bs cb t ht old good room

private def rangeBound {β : Type} {cap : Nat} (P : Nat → β → Prop)
    (f : Nat → β → Except Error (ForInStep β)) (i n : Nat) (s : β) (start : P i s)
    (each : ∀ j < i+n, ∀ b, P j b → Scan cap (fun y => ∃ t, y = .yield t ∧ P (j+1) t) (f j b)) :
    Scan cap (P (i+n)) (forIn (List.range' i n) s f) := by
  match n with
  | 0 => exact ⟨start⟩
  | n+1 =>
    rw [List.range'_succ,List.forIn_cons]
    apply chain (each i (by omega) s start)
    intro y h
    cases y with
    | done => exact False.elim (by obtain ⟨_,eq,_⟩ := h; cases eq)
    | yield t =>
      have ht : P (i+1) t := by obtain ⟨_,eq,ht⟩ := h; cases eq; exact ht
      simpa only [Nat.add_assoc,Nat.add_comm 1 n] using
        rangeBound P f (i+1) n t ht (fun j hj => each j (by omega))

private def rangeScan {β : Type} {cap : Nat} (P : Nat → β → Prop)
    (f : Nat → β → Except Error (ForInStep β)) (i n : Nat) (b : β) (start : P i b)
    (each : ∀ j s, P j s → Scan cap (fun y => ∃ t, y = .yield t ∧ P (j+1) t) (f j s)) :
    Scan cap (P (i+n)) (forIn (List.range' i n) b f) :=
  rangeBound P f i n b start (fun j _ => each j)

private def bandScan (cap : Nat) (L : Limits) (style layer bi : Nat) (bs : BandState)
    (b : BitReader) (hb : b.data.size ≤ cap) (old : BandOK L bs)
    (room : L.maxPassesPerCodeBlock+2^32+101 ≤ cap) :
    Scan cap (fun z : BandState × Array Contribution × BitReader =>
      BandOK L z.1 ∧ TablesOK L z.2.1 ∧ z.2.1.size ≤ bs.blocks.size ∧ z.2.2.data.size ≤ cap)
      (headerBand L style layer bi bs b) := by
  rw [Tier2Equiv.headerBand_eq]
  let P := fun k (s : BandState × BitReader × Array Contribution) =>
    BandOK L s.1 ∧ s.2.1.data.size ≤ cap ∧ TablesOK L s.2.2 ∧ s.2.2.size ≤ k
  apply chain (rangeScan P _ 0 bs.blocks.size (bs,b,#[]) ⟨old,hb,by simp [TablesOK],by simp⟩ ?_)
  · intro z h
    exact ⟨⟨h.1,h.2.2.1,by simpa using h.2.2.2,h.2.1⟩⟩
  · intro k s h
    unfold Tier2Equiv.bandBody
    apply chain (blockScan cap L style layer bi k s.1 s.2.1 h.2.1 h.1 room)
    rintro ⟨bs',opt,t⟩ ⟨hb',hc,ht⟩
    cases opt with
    | none => exact ⟨_,rfl,hb',ht,h.2.2.1,Nat.le_succ_of_le h.2.2.2⟩
    | some c =>
      refine ⟨_,rfl,hb',ht,?_,?_⟩
      · intro x hx
        exact (Array.mem_push.mp hx).elim (h.2.2.1 _) (fun e => e ▸ hc c rfl)
      · simpa only [Array.size_push] using Nat.succ_le_succ h.2.2.2

/-- Every band in the current precinct table satisfies its block-state bound. -/
def BandsOK (L : Limits) (bs : Array BandState) :=
  ∀ b ∈ bs, BandOK L b ∧ b.blocks.size ≤ L.maxCodeBlocks

private def headersScan (cap : Nat) (L : Limits) (layer : Nat) (st : PrecState)
    (b : BitReader) (hb : b.data.size ≤ cap) (old : BandsOK L st.bands)
    (room : L.maxPassesPerCodeBlock+2^32+101 ≤ cap) :
    Scan cap (fun z : PrecState × Array Contribution × BitReader =>
      BandsOK L z.1.bands ∧ TablesOK L z.2.1 ∧ z.2.1.size ≤ st.bands.size*L.maxCodeBlocks ∧
        z.2.2.data.size ≤ cap) (headerBands L layer st b) := by
  rw [Tier2Equiv.headerBands_eq]
  let P := fun k (s : Array BandState × BitReader × Array Contribution) =>
    BandsOK L s.1 ∧ s.2.1.data.size ≤ cap ∧ TablesOK L s.2.2 ∧ s.2.2.size ≤ k*L.maxCodeBlocks
  apply chain (rangeScan P _ 0 st.bands.size (st.bands,b,#[]) ⟨old,hb,by simp [TablesOK],by simp⟩ ?_)
  · intro z h; exact ⟨⟨h.1,h.2.2.1,by simpa using h.2.2.2,h.2.1⟩⟩
  · intro k s h
    unfold Tier2Equiv.bandsBody
    split
    · rename_i bs lookup
      have bsok := h.1 _ (Array.mem_of_getElem? lookup)
      let one := bandScan cap L st.style layer k bs s.2.1 h.2.1 bsok.1 room
      refine chain (post one (Q := fun z => _ ∧ z.1.blocks.size = bs.blocks.size)
        (fun z ok facts => ⟨facts,?_⟩)) ?_
      · have shape := congrArg (fun v => v.2.size) (Tier2WF.headerBand_shape ok)
        simpa only [Tier2WF.bshape,Array.size_map] using shape
      · rintro ⟨bs',cs,t⟩ ⟨⟨good,table,count,ht⟩,size⟩
        refine ⟨_,rfl,?_,ht,?_,?_⟩
        · intro z mem
          exact (Array.mem_or_eq_of_mem_setIfInBounds mem).elim (h.1 _)
            (fun e => e ▸ ⟨good,size ▸ bsok.2⟩)
        · intro x hx
          exact (Array.mem_append.mp hx).elim (h.2.2.1 _) (table _)
        · exact (Array.size_append ..) ▸ (Nat.succ_mul ..) ▸
            Nat.add_le_add h.2.2.2 (Nat.le_trans count bsok.2)
    · exact ⟨Nat.zero_le _,oneFixed _ (by decide)⟩

private def pieceScan (cap : Nat) (ps : List (Nat × Nat)) (r : Reader)
    (hr : r.data.size ≤ cap) (wire : 2^32 ≤ cap) (lens : WirePieces ps) :
    Scan cap (fun z : List (Nat × TilePart.ByteRange) × Reader => z.2.data.size ≤ cap)
      (takePieces r ps) := by
  match ps with
  | [] => exact ⟨hr⟩
  | (p,n)::xs =>
    unfold takePieces
    split
    · exact ⟨Nat.le_trans r.pos_le_size hr,closeExpr
        (catExpr (catExpr (litExpr _ "packet body: segment of ")
          (decExpr (Nat.le_trans (lens (p,n) (.head _)) wire))) (litExpr _ " bytes"))
        (by decide) (by decide)⟩
    · rename_i fits
      simp only [Reader.skip,show r.pos+n ≤ r.stop by omega,↓reduceDIte,bind,Except.bind]
      let t : Reader := {r with pos := r.pos+n, pos_le := by omega}
      let seen := pieceScan cap xs t hr wire (fun x hx => lens x (.tail _ hx))
      cases eq : takePieces t xs with
      | error => rw [eq] at seen; exact seen
      | ok z => rw [eq] at seen; exact ⟨seen.down⟩

/-- The exact first piece past the reader's end, after a successfully read prefix
of the same code-block contribution. Its declared length supplies the decimal leaf. -/
def PieceFailure (r : Reader) (ps : List (Nat × Nat)) (e : Error) : Prop :=
  ∃ done passes n tail rs t, ps = done ++ (passes,n)::tail ∧ takePieces r done = .ok (rs,t) ∧
    t.stop < t.pos+n ∧ e = .truncated (locAt t.pos) s!"packet body: segment of {n} bytes"

private theorem rejectedPiece {ps : List (Nat × Nat)} {r : Reader} {e : Error}
    (bad : takePieces r ps = .error e) : PieceFailure r ps e := by
  induction ps generalizing r with
  | nil => cases bad
  | cons pair ps ih =>
    obtain ⟨p,n⟩ := pair
    unfold takePieces at bad
    split at bad
    · rename_i over
      cases bad; exact ⟨[],p,n,ps,[],r,rfl,rfl,over,rfl⟩
    · rename_i fits
      have ok : r.pos+n ≤ r.stop := by omega
      let t : Reader := {r with pos := r.pos+n, pos_le := ok}
      have skip : r.skip n = .ok t := by simp [Reader.skip,ok,t]
      simp only [skip,bind,Except.bind] at bad
      cases next : takePieces t ps with
      | ok z => rw [next] at bad; cases bad
      | error err =>
        rw [next] at bad
        cases bad
        obtain ⟨done,q,m,tail,rs,u,cut,read,over,diagnosis⟩ := ih next
        refine ⟨(p,n)::done,q,m,tail,(p,⟨r.pos,n⟩)::rs,u,by simp [cut],?_,over,diagnosis⟩
        simp only [takePieces,fits,ite_false,skip,bind,Except.bind,read]
        rfl

private theorem refusedIteration {α β : Type} (step : α → β → Except Error (ForInStep β))
    (xs : List α) (s : β) {e} (bad : forIn xs s step = .error e) :
    ∃ before x tail t, xs = before ++ x::tail ∧ forIn before s step = .ok t ∧ step x t = .error e := by
  induction xs generalizing s with
  | nil => cases bad
  | cons x xs ih =>
    rw [List.forIn_cons] at bad
    cases get : step x s with
    | error err => rw [get] at bad; cases bad; exact ⟨[],x,xs,s,rfl,rfl,get⟩
    | ok y =>
      rw [get] at bad
      cases y with
      | done => cases bad
      | yield t =>
        obtain ⟨pre,z,tail,u,cut,read,fail⟩ := ih t bad
        exact ⟨x::pre,z,tail,u,by simp [cut],by simpa only [List.forIn_cons,get,bind,Except.bind] using read,fail⟩

/-- A body rejection identifies its preceding complete contributions and the actual
reader at the failing contribution. The failure is either inside its piece list
or in one of the two destination lookups after its pieces were read. -/
def BodyFailure (st : PrecState) (cs : Array Contribution) (r : Reader) (e : Error) : Prop :=
  ∃ before c tail z, cs.toList = before ++ c::tail ∧ forIn before (st.bands,r) Tier2Equiv.bodyBody = .ok z ∧
    (PieceFailure z.2 c.pieces e ∨ ∃ rs t, takePieces z.2 c.pieces = .ok (rs,t) ∧
      ((z.1[c.band]? = none ∧ e = .malformed JPEG2000.Tier2.Packet.loc "band index out of range") ∨
       ∃ b, z.1[c.band]? = some b ∧ b.blocks[c.block]? = none ∧
         e = .malformed JPEG2000.Tier2.Packet.loc "code-block index out of range"))

private theorem rejectedBody {st cs r e} (bad : readBody st cs r = .error e) : BodyFailure st cs r e := by
  rw [Tier2Equiv.readBody_eq] at bad
  cases loop : forIn cs.toList (st.bands,r) Tier2Equiv.bodyBody with
  | ok => rw [loop] at bad; cases bad
  | error err =>
    rw [loop] at bad
    cases bad
    obtain ⟨pre,c,tail,z,cut,before,last⟩ := refusedIteration _ _ _ loop
    refine ⟨pre,c,tail,z,cut,before,?_⟩
    unfold Tier2Equiv.bodyBody at last
    cases read : takePieces z.2 c.pieces with
    | error e => rw [read] at last; cases last; exact .inl (rejectedPiece read)
    | ok pair =>
      obtain ⟨rs,t⟩ := pair
      simp only [read,bind,Except.bind] at last
      cases band : z.1[c.band]? with
      | none => rw [band] at last; cases last; exact .inr ⟨rs,t,rfl,.inl ⟨rfl,rfl⟩⟩
      | some b =>
        simp only [band] at last
        cases block : b.blocks[c.block]? <;> rw [block] at last <;> cases last
        exact .inr ⟨rs,t,rfl,.inr ⟨b,rfl,block,rfl⟩⟩

private theorem add_fields (cb : CodeBlock) (cont : Bool) (rs : List (Nat × TilePart.ByteRange)) :
    (addPieces cb cont rs).lblock = cb.lblock ∧ (addPieces cb cont rs).numPasses = cb.numPasses := by
  induction rs generalizing cb cont with
  | nil => exact ⟨rfl,rfl⟩
  | cons x xs ih => obtain ⟨n,rg⟩ := x; exact ih _ false

private def bodyScan (cap : Nat) (L : Limits) (st : PrecState) (cs : Array Contribution) (r : Reader)
    (hr : r.data.size ≤ cap) (wire : 2^32 ≤ cap) (old : BandsOK L st.bands) (table : TablesOK L cs) :
    Scan cap (fun z : PrecState × Reader => BandsOK L z.1.bands ∧ z.2.data.size ≤ cap)
      (readBody st cs r) := by
  rw [Tier2Equiv.readBody_eq]
  let P := fun s : Array BandState × Reader => BandsOK L s.1 ∧ s.2.data.size ≤ cap
  apply chain (walkList P _ cs.toList (st.bands,r) ⟨old,hr⟩ ?_)
  · intro z h; exact ⟨h⟩
  · intro c hc s h
    unfold Tier2Equiv.bodyBody
    apply chain (pieceScan cap c.pieces s.2 h.2 wire (table _ (by simpa using hc)).1)
    rintro ⟨rs,t⟩ ht
    dsimp only
    split
    · rename_i bs lookup
      split
      · rename_i cb block
        have good := h.1 bs (Array.mem_of_getElem? lookup)
        have hh := good.1 _ (Array.mem_of_getElem? block)
        refine PLift.up ⟨?_,ht⟩
        intro z hz
        rcases Array.mem_or_eq_of_mem_setIfInBounds hz with mem | rfl
        · exact h.1 _ mem
        · refine ⟨?_,by simpa using good.2⟩
          intro y hy
          rcases Array.mem_or_eq_of_mem_setIfInBounds hy with mem | rfl
          · exact good.1 _ mem
          · simpa only [(add_fields cb c.cont rs).1,(add_fields cb c.cont rs).2] using hh
      · exact ⟨Nat.zero_le _,oneFixed _ (by decide)⟩
    · exact ⟨Nat.zero_le _,oneFixed _ (by decide)⟩

private def u16 (cap : Nat) (r : Reader) (hr : r.data.size ≤ cap) :
    Scan cap (fun z : UInt16 × Reader => z.2.data.size ≤ cap) r.u16be := by
  unfold Reader.u16be
  split
  · exact ⟨hr⟩
  · exact ⟨Nat.le_trans r.pos_le_size hr,oneFixed _ (by decide)⟩

private def sopResult (cap seq : Nat) (r : Reader) (hr : r.data.size ≤ cap) (wire : 65535 ≤ cap) :
    Scan cap (fun z : Bool × Reader => z.2.data.size ≤ cap) (readSop seq r) := by
  unfold readSop
  cases peek : r.u16be with
  | error => exact ⟨hr⟩
  | ok z =>
    obtain ⟨m,t⟩ := z
    have ht : t.data.size ≤ cap := by rw [(Reader.u16be_pos peek).2.2.1]; exact hr
    dsimp only
    split
    · apply chain (u16 cap t ht)
      rintro ⟨len,t⟩ ht
      dsimp only
      split
      · exact ⟨Nat.le_trans r.pos_le_size hr,closeExpr (catExpr
          (catExpr (litExpr _ "SOP: Lsop = ") (decExpr (show len.toNat ≤ cap by have := len.toNat_lt; omega)))
          (litExpr _ ", expected 4")) (by decide) (by decide)⟩
      · apply chain (u16 cap t ht)
        rintro ⟨num,t⟩ ht
        dsimp only
        split
        · exact ⟨Nat.le_trans r.pos_le_size hr,closeExpr (catExpr (catExpr
            (catExpr (litExpr _ "SOP: Nsop = ") (decExpr (show num.toNat ≤ cap by have := num.toNat_lt; omega)))
            (litExpr _ ", expected ")) (decExpr (show seq%65536 ≤ cap by omega))) (by decide) (by decide)⟩
        · exact ⟨ht⟩
    · exact ⟨hr⟩

private theorem branch_bind {α β : Type} (b : Prop) [Decidable b] (x y : Except Error α)
    (f : α → Except Error β) :
    (if b then x >>= f else y >>= f) = (if b then x else y) >>= f := by split <;> rfl

private theorem foldPasses (ps : List (Nat × Nat)) (a : Nat) :
    ps.foldl (fun a p => a+p.1) a = a+(ps.map Prod.fst).sum := by
  induction ps generalizing a with
  | nil => simp
  | cons x xs ih => simp [ih,Nat.add_assoc]

private theorem tablePasses (L : Limits) (cs : List Contribution) (a : Nat)
    (good : ∀ c ∈ cs, COK L c) :
    cs.foldl (fun a c => c.pieces.foldl (fun a p => a+p.1) a) a ≤ a + cs.length*L.maxPassesPerCodeBlock := by
  induction cs generalizing a with
  | nil => simp
  | cons c cs ih =>
    have h := (good c (.head _)).2
    have t := ih (a+(c.pieces.map Prod.fst).sum) (fun x hx => good x (.tail _ hx))
    simp only [foldPasses] at t
    simp only [List.foldl_cons,foldPasses,List.length_cons,Nat.succ_mul]
    omega

/-- Block counts, accumulated passes and Lblock values in the reached precinct bands. -/
def PrecOK (L : Limits) (st : PrecState) := BandsOK L st.bands ∧ st.bands.size ≤ 3
/-- Maximum new passes proposed by a single decoded packet before cumulative admission. -/
def passProposal (L : Limits) := 3*L.maxCodeBlocks*L.maxPassesPerCodeBlock

private def packetScan (cap : Nat) (L : Limits) (sop eph : Bool) (seq layer : Nat) (st : PrecState)
    (same : Bool) (hdr body : Reader) (hh : same = false → hdr.data.size ≤ cap) (hb : body.data.size ≤ cap)
    (good : PrecOK L st) (room : L.maxPassesPerCodeBlock+2^32+101 ≤ cap) :
    Scan cap (fun z : PrecState × PacketInfo × Reader × Reader =>
      PrecOK L z.1 ∧ z.2.1.newPasses ≤ passProposal L ∧
      z.2.2.1.data.size ≤ cap ∧ z.2.2.2.data.size ≤ cap)
      (decodePacket L sop eph seq layer st same hdr body) := by
  unfold decodePacket
  simp only [branch_bind]
  apply chain (P := fun z : Bool × Reader => z.2.data.size ≤ cap) (by
    split
    · exact sopResult cap seq body hb (by omega)
    · exact ⟨hb⟩)
  rintro ⟨_,body1⟩ hb1
  let r := if same then body1 else hdr
  have bound : r.data.size ≤ cap := by cases same <;> first | exact hh rfl | exact hb1
  apply chain (nextBit cap (BitReader.ofReader r) bound)
  rintro ⟨present,b⟩ hb
  apply chain (P := fun z : PrecState × Array Contribution × BitReader =>
    PrecOK L z.1 ∧ TablesOK L z.2.1 ∧ z.2.1.size ≤ 3*L.maxCodeBlocks ∧ z.2.2.data.size ≤ cap) (by
    cases present
    · exact PLift.up ⟨good,by simp [TablesOK],Nat.zero_le _,hb⟩
    · refine post (headersScan cap L layer st b hb good.1 room) ?_
      rintro ⟨pre,cs,b⟩ eq ⟨good',table,size,hb⟩
      have shape := Tier2WF.headerBands_shape eq
      have bands := congrArg Array.size shape
      simp only [Array.size_map] at bands
      exact ⟨⟨good',bands ▸ good.2⟩,table,Nat.le_trans size (Nat.mul_le_mul_right _ good.2),hb⟩)
  rintro ⟨pre,cs,b⟩ ⟨preOK,table,size,hb⟩
  apply chain (alignScan cap b hb)
  intro aligned ha
  apply chain (P := fun r : Reader => r.data.size ≤ cap) (by
    split
    · exact ephScan cap _ ha
    · exact ⟨ha⟩)
  intro head hh
  apply chain (bodyScan cap L pre cs (if same then head else body1)
    (by cases same <;> assumption) (by omega) preOK.1 table |> fun scan =>
    post scan (Q := fun z => PrecOK L z.1 ∧ z.2.data.size ≤ cap) (by
      rintro ⟨out,t⟩ eq ⟨ok,ht⟩
      have shape := congrArg Array.size (Tier2WF.readBody_shape eq)
      simp only [Array.size_map] at shape
      exact ⟨⟨ok,shape ▸ preOK.2⟩,ht⟩))
  rintro ⟨out,t⟩ ⟨outOK,ht⟩
  have count := tablePasses L cs.toList 0 (fun c hc => table c (by simpa using hc))
  simp only [Array.foldl_toList,Array.length_toList,Nat.zero_add] at count
  exact PLift.up ⟨outOK,Nat.le_trans count (Nat.mul_le_mul_right _ size),by cases same <;> assumption,ht⟩

/-- State of a reached packet reader, including the admitted cumulative pass count,
block tables and input extents for inline and packed operation. -/
def StateOK (cap : Nat) (L : Limits) (same : Bool) (pb : Nat) (s : LoopState) :=
  (∀ st ∈ s.precs, PrecOK L st) ∧ pb+s.passes ≤ L.maxCodingPasses ∧
  s.body.data.size ≤ cap ∧ (same = false → s.hdr.data.size ≤ cap)

private def stepScan (cap : Nat) (L : Limits) (c : Coding) (base : Array (Array Nat))
    (same : Bool) (pb : Nat) (s : LoopState) (p : PacketId) (good : StateOK cap L same pb s)
    (room : L.maxPassesPerCodeBlock+2^32+101 ≤ cap) (quota : L.maxCodingPasses+passProposal L ≤ cap) :
    Scan cap (StateOK cap L same pb) (packetStep L c base same pb s p) := by
  unfold packetStep
  dsimp only
  split
  · rename_i st get
    apply chain (packetScan cap L c.sop c.eph s.seq p.layer st same s.hdr s.body good.2.2.2
      good.2.2.1 (good.1 _ (Array.mem_of_getElem? get)) room)
    rintro ⟨next,info,hdr,body⟩ ⟨hn,count,hh,hb⟩
    dsimp only at count ⊢
    apply chain (check cap L JPEG2000.Tier2.Packet.loc .codingPasses _ (Nat.zero_le _)
      (by have := good.2.1; omega))
    intro _ accepted
    refine PLift.up ⟨?_,accepted,hb,fun _ => hh⟩
    intro x hx
    rw [Array.setIfInBounds_setIfInBounds] at hx
    exact (Array.mem_or_eq_of_mem_setIfInBounds hx).elim (good.1 _) (fun e => e ▸ hn)
  · exact ⟨Nat.zero_le _,oneFixed _ (by decide)⟩

open JPEG2000.Tier2.Geometry

private theorem startPrec {L : Limits} {tc : TileCompGeom} {r k res pg st}
    (hr : resolution L tc r = .ok res) (hp : precinct L res k = .ok pg)
    (hi : PrecState.init L tc.params r pg = .ok st) : PrecOK L st := by
  obtain ⟨_,nb,blocks⟩ := HeaderWork.precinct_geometry hr hp
  unfold PrecState.init at hi
  obtain ⟨bs,hm,hi⟩ := Tier2Equiv.bind_ok hi
  cases hi
  refine ⟨Tier2WF.arrayMapM_mem _ _ _ ?_ _ hm,Nat.le_trans (Nat.le_of_eq
    (ColorResources.channel_map_size hm)) nb⟩
  intro g hg b eq
  obtain ⟨_,_,eq⟩ := Tier2Equiv.bind_ok eq
  obtain ⟨_,_,eq⟩ := Tier2Equiv.bind_ok eq
  cases eq
  refine ⟨?_,by simpa using blocks g hg⟩
  intro cb mem
  obtain ⟨a,_,rfl⟩ := Array.mem_map.mp mem
  exact ⟨by change 3 ≤ 32; decide,Nat.zero_le _⟩

private theorem startStates {L : Limits} {g ps base spans}
    (init : initPrecincts L g = .ok (ps,base,spans)) : ∀ st ∈ ps, PrecOK L st := by
  unfold initPrecincts at init
  simp only [Std.Legacy.Range.forIn_eq_forIn_range'] at init
  obtain ⟨s,loop,init⟩ := Tier2Equiv.bind_ok init
  cases init
  refine Tier2Equiv.forIn_inv (fun (a : Array PrecState × Array (Array Nat) × Array (Array (Nat × Nat)) × Nat) =>
    ∀ st ∈ a.1, PrecOK L st) _ ?_ _ _ _ (by simp) loop
  intro _ a _ inv run
  obtain ⟨_,middle,run⟩ := Tier2Equiv.bind_ok run
  cases run
  refine Tier2Equiv.forIn_inv (fun (a : Array PrecState × Nat × Array Nat × Array (Nat × Nat)) =>
    ∀ st ∈ a.1, PrecOK L st) _ ?_ _ _ _ inv middle
  intro _ a _ inv run
  obtain ⟨res,hr,run⟩ := Tier2Equiv.bind_ok run
  obtain ⟨_,_,run⟩ := Tier2Equiv.bind_ok run
  obtain ⟨_,inner,run⟩ := Tier2Equiv.bind_ok run
  cases run
  refine Tier2Equiv.forIn_inv (fun (a : Array PrecState × Nat) => ∀ st ∈ a.1, PrecOK L st)
    _ ?_ _ _ _ inv inner
  intro _ a _ inv run
  obtain ⟨pg,hp,run⟩ := Tier2Equiv.bind_ok run
  obtain ⟨_,_,run⟩ := Tier2Equiv.bind_ok run
  obtain ⟨st,hi,run⟩ := Tier2Equiv.bind_ok run
  cases run
  intro x hx
  exact (Array.mem_push.mp hx).elim (inv x) (fun e => e ▸ startPrec hr hp hi)

private theorem prefixOK {L : Limits} {cap : Nat} {c : Coding} {base same pb}
    (ps : List Position) {s t : LoopState} (good : StateOK cap L same pb s)
    (room : L.maxPassesPerCodeBlock+2^32+101 ≤ cap) (quota : L.maxCodingPasses+passProposal L ≤ cap)
    (run : ps.foldlM (dispatch (packetStep L c base same pb)) s = .ok t) : StateOK cap L same pb t := by
  induction ps generalizing s with
  | nil => cases run; exact good
  | cons p ps ih =>
    rw [List.foldlM_cons] at run
    obtain ⟨z,step,tail⟩ := Tier2Equiv.bind_ok run
    apply ih _ tail
    unfold dispatch at step
    split at step
    · cases step; exact good
    · let scan := stepScan cap L c base same pb s p.packet good room quota
      rw [step] at scan
      exact scan.down

/-- Text and numeric construction charged to an emitted error. The record includes its
offset and checked value even when the stream rejects at the admission test. -/
def Fault.work {cap : Nat} {e : Error} (f : Fault cap e) : Nat := by
  cases e with
  | limitExceeded l k n b => exact storedPayload false (.limitExceeded l k n b)
  | truncated l s => exact storedPayload false (.truncated l s) + f.payload.tree.work
  | malformed l s => exact storedPayload false (.malformed l s) + f.payload.tree.work
  | unsupported l s => exact storedPayload false (.unsupported l s) + f.payload.tree.work

/-- Cumulative logical payload of the error record, numeric temporaries and string
copies constructed at this site. -/
def Fault.storage {cap : Nat} {e : Error} (f : Fault cap e) : Nat := by
  cases e with
  | limitExceeded l k n b => exact storedPayload false (.limitExceeded l k n b)
  | truncated l s => exact storedPayload false (.truncated l s) + f.payload.tree.storage
  | malformed l s => exact storedPayload false (.malformed l s) + f.payload.tree.storage
  | unsupported l s => exact storedPayload false (.unsupported l s) + f.payload.tree.storage

private theorem fault_storage {cap : Nat} {e : Error} (f : Fault cap e) : f.storage ≤ f.work := by
  cases e with
  | limitExceeded => exact Nat.le_refl _
  | _ => exact Nat.add_le_add_left f.payload.tree.storage_le_work _

private def singleTrace {cap : Nat} {e : Error} (f : Fault cap e) :
    DiagnosticCost.Trace cap (Except.error e : Except Error Unit) 1 := by
  cases e with
  | limitExceeded =>
    exact ⟨[],by simp,by intro e eq; cases eq; exact ⟨f.offset,f.payload.down⟩⟩
  | _ =>
    exact ⟨[⟨_,f.payload⟩],by simp,by intro e eq; cases eq; exact ⟨f.offset,⟨_,f.payload⟩,by simp,rfl⟩⟩

/-- A single construction allowance in logical operations and cumulative payload. -/
def eventBudget (cap : Nat) :=
  6 + Text.byteBound cap 128 24 + 2*bits cap + Text.workBound cap 128 24

private theorem fault_bound {cap : Nat} {e : Error} (f : Fault cap e) : f.work ≤ eventBudget cap := by
  have record := trace_retained (singleTrace f) rfl
  cases e with
  | limitExceeded => exact Nat.le_trans record (Nat.le_add_right ..)
  | _ => exact Nat.add_le_add record (built_cost f.payload).2

private def refused {α : Type} {cap : Nat} {P : α → Prop} (x : Except Error α) (scan : Scan cap P x) :
    List (Σ e, Fault cap e) := match x,scan with
  | .ok _,_ => []
  | .error e,f => [⟨e,f⟩]

private theorem refused_count {α : Type} {cap : Nat} {P : α → Prop} (x : Except Error α)
    (s : Scan cap P x) : (refused x s).length = (!x.isOk).toNat := by cases x <;> rfl

private theorem refused_mem {α : Type} {cap : Nat} {P : α → Prop} {x : Except Error α}
    (s : Scan cap P x) {e} (bad : x = .error e) : ∃ f : Fault cap e, ⟨e,f⟩ ∈ refused x s := by
  cases bad; exact ⟨s,.head _⟩

private theorem refused_single {α : Type} {cap : Nat} {P : α → Prop} {x : Except Error α}
    (s : Scan cap P x) {e} (bad : x = .error e) : ∃ f : Fault cap e, refused x s = [⟨e,f⟩] := by
  cases bad; exact ⟨s,rfl⟩

/-- A discarded SOP diagnosis occurs exactly when the selected precinct probes two
body bytes and the read fails. The record precedes any later header/body refusal. -/
def discarded (c : Coding) (base : Array (Array Nat)) (s : LoopState) (p : PacketId) : Bool :=
  (s.precs[((base.getD p.comp #[]).getD p.res 0)+p.prec]?).isSome && c.sop &&
    !(s.body.u16be).isOk

/-- Both constructions of an attempted packet, in production order. -/
def stepEvents (cap : Nat) (L : Limits) (c : Coding) (base : Array (Array Nat))
    (same : Bool) (pb : Nat) (s : LoopState) (p : PacketId) (good : StateOK cap L same pb s)
    (room : L.maxPassesPerCodeBlock+2^32+101 ≤ cap) (quota : L.maxCodingPasses+passProposal L ≤ cap) :
    List (Σ e, Fault cap e) :=
  let peek := if (s.precs[((base.getD p.comp #[]).getD p.res 0)+p.prec]?).isSome && c.sop then
    refused s.body.u16be (u16 cap _ good.2.2.1) else []
  peek ++ refused (packetStep L c base same pb s p) (stepScan cap L c base same pb s p good room quota)

private theorem stepEvents_count {cap L c base same pb s p good room quota} :
    (stepEvents cap L c base same pb s p good room quota).length =
      (discarded c base s p).toNat + (!(packetStep L c base same pb s p).isOk).toNat := by
  unfold stepEvents discarded
  split <;> rename_i peeking
  · simp only [List.length_append,refused_count,peeking,Bool.true_and]
  · have no := Bool.eq_false_iff.mpr peeking
    rw [no]; simp only [Bool.false_and,Bool.toNat_false,Nat.zero_add,List.nil_append,refused_count]

/-- Scalar envelope of public packet reads, including gathered offsets, a refused local
pass count, a refused cumulative pass proposal, and the declared piece lengths. -/
def callbackCap (L : Limits) (n : Nat) :=
  L.maxPassesPerCodeBlock + 2^32 + 101 + (L.maxCodingPasses + passProposal L) +
  L.maxTilePartsPerTile*n +
    (L.maxTilePartsPerTile*(L.maxTileParts*n) + L.maxTilePartsPerTile*(n+1))*n

private theorem packed_le (L : Limits) (n : Nat) (s : HeaderStream) :
    PacketLocalWork.packedCap L n s ≤ callbackCap L n := by
  unfold PacketLocalWork.packedCap callbackCap
  rw [Nat.add_mul]
  split <;> omega

private theorem event_sum {cap : Nat} (xs : List (Σ e, Fault cap e)) :
    (xs.map (fun x => x.2.work)).sum ≤ xs.length * eventBudget cap := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.succ_mul]
    rw [Nat.add_comm (_ * _)]
    exact Nat.add_le_add (fault_bound x.2) ih

/-- Payloads built by the callback at the exact public packet position, including
the failed optional peek followed by a replacement diagnostic. Replaying the
successful predecessor packets establishes the bounds on existing Lblock and passes. -/
theorem public_callback (L : Limits) (d : ByteArray) (red : Nat) {v p a}
    (hit : v ∈ (PublicPacketWork.measure L d red).1) (member : (p,a) ∈ v.packets)
    (called : a.attempted = true) :
    let cap := callbackCap L d.size
    ∃ h dst idx tp hs g c ps base spans buf parts pre tail s,
      PublicPacketWork.prepareTiles L d red = .ok (h,dst) ∧ NativeCost.ranks L h = .ok idx ∧
      Header.parse L d = .ok h ∧ presentAt h v.tile v.cursor = some tp ∧
      headerStreamAt h d tp (idx.getD v.cursor #[]) = .ok hs ∧
      Layout.ofHeader h tp.index = .ok (g,c) ∧ initPrecincts L g = .ok (ps,base,spans) ∧
      tileData d tp.tile = .ok (buf,parts) ∧ schedule g [] (volumes g c.progression c.poc) = pre ++ p::tail ∧
      let same := (hs.map HeaderStream.bytes).isNone
      let f := packetStep L c base same v.passesBefore
      pre.foldlM (dispatch f) (firstState ps buf hs) = .ok s ∧ PacketLocalWork.agrees s a (f s p.packet) ∧
      ∃ good room quota, let events := stepEvents cap L c base same v.passesBefore s p.packet good room quota
        events.length = (discarded c base s p.packet).toNat + (!(f s p.packet).isOk).toNat ∧
        (events.map (fun x => x.2.work)).sum ≤ 2*eventBudget cap ∧
        (∀ e, discarded c base s p.packet = true → s.body.u16be = .error e →
          ∃ witness : Fault cap e, events.head? = some ⟨e,witness⟩) ∧
        (∀ st pre cs r e,
          s.precs[((base.getD p.packet.comp #[]).getD p.packet.res 0)+p.packet.prec]? = some st →
          SegmentHistory.packetBody L c same s p.packet st = .ok (pre,cs,r) →
          readBody pre cs r = .error e → BodyFailure pre cs r e ∧ f s p.packet = .error e) ∧
        ∀ e, f s p.packet = .error e → ∃ witness : Fault cap e, ⟨e,witness⟩ ∈ events := by
  obtain ⟨h,dst,entry,parsed,_,prior,idx,rank,_,_,source⟩ := NativeCost.visited_storage L d red v hit
  cases sel : presentAt h v.tile v.cursor with
  | none => rw [sel] at source; rw [source] at member; cases member
  | some tp =>
    rw [sel] at source
    obtain ⟨mem,_,source⟩ := source
    cases selected : headerStreamAt h d tp (idx.getD v.cursor #[]) with
    | error => rw [selected] at source; rw [source] at member; cases member
    | ok hs =>
      rw [selected] at source
      have logged := (SegmentHistory.packet_prefix_counts parsed tp hs v.passesBefore prior).1.symm.trans source.2.1
      obtain ⟨g,c,ps,base,spans,buf,parts,pre,tail,s,layout,init,input,_,order,run,_,_,_,_,_,_,_,_,action,erase,_⟩ :=
        PacketLocalWork.stream_attempt parsed called (logged ▸ member)
      have size : buf.size ≤ L.maxTilePartsPerTile*d.size := by
        obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,hp,sel',_,_,input',nb,_⟩ :=
          NativeCost.attempted_storage L d red hit member called
        rw [parsed] at hp; cases hp
        rw [sel] at sel'; cases sel'
        rw [input] at input'; cases input'; exact nb
      have packed (b : HeaderStream) (eq : hs = some b) :
          b.bytes.size ≤ PacketLocalWork.packedCap L d.size b :=
        (HeaderWork.parsed_headerStream parsed mem (selected.trans (congrArg Except.ok eq))).2
      let cap := callbackCap L d.size
      have room : L.maxPassesPerCodeBlock+2^32+101 ≤ cap := by unfold cap callbackCap; omega
      have quota : L.maxCodingPasses+passProposal L ≤ cap := by unfold cap callbackCap; omega
      have body : buf.size ≤ cap := by unfold cap callbackCap; omega
      have initial : StateOK cap L (hs.map HeaderStream.bytes).isNone v.passesBefore (firstState ps buf hs) := by
        refine ⟨startStates init,prior,body,?_⟩
        cases hs with
        | none => intro eq; cases eq
        | some b => exact fun _ => Nat.le_trans (packed b rfl) (packed_le ..)
      have good := prefixOK pre initial room quota run
      refine ⟨h,dst,idx,tp,hs,g,c,ps,base,spans,buf,parts,pre,tail,s,entry,rank,parsed,sel,selected,layout,init,input,order,run,
        erase ▸ action,good,room,quota,stepEvents_count,?_,?_,?_,?_⟩
      · apply Nat.le_trans (event_sum _) (Nat.mul_le_mul_right _ ?_)
        rw [stepEvents_count]
        generalize discarded c base s p.packet = peek
        generalize (!(packetStep L c base (hs.map HeaderStream.bytes).isNone v.passesBefore s p.packet).isOk) = bad
        cases peek <;> cases bad <;> decide
      · intro e peek bad
        have entered := (Bool.and_eq_true_iff.mp peek).1
        unfold stepEvents
        rw [ite_eq_left entered]
        obtain ⟨w,eq⟩ := refused_single (u16 cap _ good.2.2.1) bad
        exact ⟨w,by dsimp only; rw [eq]; rfl⟩
      · intro st pre cs r e get header bad
        refine ⟨rejectedBody bad,?_⟩
        let same := (hs.map HeaderStream.bytes).isNone
        change SegmentHistory.packetBody L c same s p.packet st = .ok (pre,cs,r) at header
        have er := SegmentHistory.packet_body_erase L c same s p.packet st
        simp only [header,bind,Except.bind,bad] at er
        unfold packetStep
        simp only [get]
        cases read : decodePacket L c.sop c.eph s.seq p.packet.layer st same s.hdr s.body with
        | error err => rw [read] at er; cases er; rfl
        | ok z => rw [read] at er; cases er
      · intro e bad
        unfold stepEvents
        obtain ⟨f,mem⟩ := refused_mem (stepScan cap L c base _ _ s p.packet good room quota) bad
        exact ⟨f,List.mem_append_right _ mem⟩

private def listScan {α β : Type} {cap : Nat} (P : β → Prop) (xs : List α) (f : α → Except Error β)
    (each : ∀ x ∈ xs, Scan cap P (f x)) : Scan cap (fun ys : List β => ∀ y ∈ ys, P y) (xs.mapM f) := by
  match xs with
  | [] => exact ⟨by simp⟩
  | x::xs =>
    rw [List.mapM_cons]
    apply chain (each x (.head _))
    intro y hy
    apply chain (listScan P xs f (fun z hz => each z (.tail _ hz)))
    intro ys hys
    exact ⟨fun z hz => (List.mem_cons.mp hz).elim (fun e => e ▸ hy) (hys z)⟩

private def mapScan {α β : Type} {cap : Nat} (P : β → Prop) (xs : Array α) (f : α → Except Error β)
    (each : ∀ x ∈ xs, Scan cap P (f x)) : Scan cap (fun ys : Array β => ∀ y ∈ ys, P y) (xs.mapM f) := by
  rw [Array.mapM_eq_mapM_toList]
  apply chain (listScan P xs.toList f (fun x hx => each x (by simpa using hx)))
  intro ys hy
  exact ⟨fun z hz => hy z (by simpa using hz)⟩

private def compLayout (cap : Nat) (h : Header) (t c : Nat) (ht : t ≤ cap) (hc : c ≤ cap) :
    Scan cap (fun _ => True) (JPEG2000.Tier2.Geometry.ofHeader h t c) := by
  unfold JPEG2000.Tier2.Geometry.ofHeader
  dsimp only
  by_cases tbad : t ≥ TilePart.numTiles h.siz <;> simp only [tbad,↓reduceIte]

  · exact ⟨Nat.zero_le _,closeExpr (catExpr (catExpr (litExpr _ "tile index ") (decExpr ht))
      (litExpr _ " out of range")) (by decide) (by decide)⟩
  · split
    · split
      · exact ⟨trivial⟩
      · exact ⟨Nat.zero_le _,closeExpr (catExpr (litExpr _ "no parameters for component ") (decExpr hc))
          (by decide) (by decide)⟩
    · exact ⟨Nat.zero_le _,closeExpr (catExpr (catExpr (litExpr _ "component ") (decExpr hc))
        (litExpr _ " out of range")) (by decide) (by decide)⟩

private def layoutScan (cap : Nat) (h : Header) (t : Nat) (ht : t ≤ cap) (hc : h.siz.csiz ≤ cap) :
    Scan cap (fun _ => True) (Layout.ofHeader h t) := by
  unfold Layout.ofHeader
  dsimp only
  split
  · exact ⟨Nat.zero_le _,closeExpr (catExpr (catExpr (litExpr _ "tile index ") (decExpr ht))
      (litExpr _ " out of range")) (by decide) (by decide)⟩
  · refine chain (mapScan (fun _ => True) _ _ (fun i hi => compLayout cap h t i ht ?_))
      (fun _ _ => ⟨trivial⟩)
    have lt := Array.mem_range.mp hi
    omega

private theorem ceil_le (a b : Nat) : cdiv a b ≤ a := by
  cases b with
  | zero => simp [cdiv]
  | succ d =>
    apply Nat.le_of_lt_succ
    apply (Nat.div_lt_iff_lt_mul (Nat.succ_pos d)).2
    rw [Nat.succ_mul,Nat.mul_succ]
    omega

private abbrev SmallRect (rc : Rect) := rc.x1 ≤ 2^32 ∧ rc.y1 ≤ 2^32

private theorem compRect_bound {L : Limits} {d : ByteArray} {h : Header} {t g c}
    (hp : Header.parse L d = .ok h) (hg : Layout.ofHeader h t = .ok (g,c)) {i : Nat}
    (hi : i < g.numComps) : SmallRect (g.comp i).rect := by
  have wf := Tier2Equiv.ofHeader_wf (Equiv.parse_dxdy hp) hg
  have tile : g.tile = tileRect h.siz t := by
    unfold Layout.ofHeader at hg
    dsimp only at hg
    split at hg <;> try contradiction
    obtain ⟨_,_,last⟩ := Tier2Equiv.bind_ok hg
    cases last; rfl
  rw [(wf i hi).2.2,tile]
  exact ⟨Nat.le_trans (ceil_le ..) (Nat.le_trans (Nat.min_le_right ..) (Nat.le_of_lt h.siz.xsiz.toNat_lt)),
    Nat.le_trans (ceil_le ..) (Nat.le_trans (Nat.min_le_right ..) (Nat.le_of_lt h.siz.ysiz.toNat_lt))⟩

private theorem grid_le (lo hi e : Nat) : gridCount lo hi e ≤ hi := by
  unfold gridCount
  split
  · exact Nat.zero_le _
  · exact Nat.le_trans (Nat.sub_le ..) (ceil_le ..)

private theorem res_small {tc : TileCompGeom} (h : SmallRect tc.rect) (r : Nat) :
    SmallRect (resRect tc.rect tc.params.levels r) :=
  ⟨Nat.le_trans (ceil_le ..) h.1,Nat.le_trans (ceil_le ..) h.2⟩

private theorem band_small {tc : TileCompGeom} (h : SmallRect tc.rect) (r : Nat) (b : Band) :
    SmallRect (bandGeom tc r b).rect := by
  constructor <;> apply Nat.le_trans (ceil_le ..) <;> apply Nat.le_trans (Nat.sub_le ..)
  · exact h.1
  · exact h.2

private theorem res_product {rc : Rect} (sm : SmallRect rc) (x y : Nat) :
    gridCount rc.x0 rc.x1 x * gridCount rc.y0 rc.y1 y ≤ 2^64 :=
  show _ ≤ (2^32)*(2^32) from
    Nat.mul_le_mul (Nat.le_trans (grid_le ..) sm.1) (Nat.le_trans (grid_le ..) sm.2)

private theorem fold_limit {α : Type} (xs : List α) (f : α → Nat) (k a : Nat)
    (each : ∀ x ∈ xs, f x ≤ k) : xs.foldl (fun n x => n+f x) a ≤ a+xs.length*k := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
    have h := each x (.head _)
    have tail := ih (a+f x) (fun z hz => each z (.tail _ hz))
    simp only [List.foldl_cons,List.length_cons,Nat.succ_mul]
    omega

private theorem fold_sum {α : Type} (xs : List α) (f : α → Nat) (a : Nat) :
    xs.foldl (fun n x => n+f x) a = a+(xs.map f).sum := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih => simp [ih,Nat.add_assoc]

/-- Upper bound on the packet proposal at the POC preflight, including a proposal refused
before the iterator is entered. Each pair of grid counts is bounded by SIZ. -/
def preflightValue (L : Limits) :=
  (L.maxPocEntries+1)*((L.maxPocEntries+1)*L.maxLayers*
    (L.maxComponents*((L.maxDecompLevels+1)*2^64)))

private theorem preflight_bound {L : Limits} {d : ByteArray} {h : Header} {t g c}
    (hp : Header.parse L d = .ok h) (hg : Layout.ofHeader h t = .ok (g,c)) :
    iterationWork g c.progression c.poc ≤ preflightValue L := by
  let vs := volumes g c.progression c.poc
  obtain ⟨layers,entries⟩ := ProgressionFields.parsed_limits hp hg
  obtain ⟨nc,levels⟩ := HeaderWork.layout_budget hp hg
  have nr : g.maxLevels ≤ L.maxDecompLevels := by
    unfold Layout.maxLevels
    have fold (xs : List Nat) (le : ∀ n ∈ xs, n ≤ L.maxDecompLevels) :
        xs.foldr max 0 ≤ L.maxDecompLevels := by
      induction xs with
      | nil => exact Nat.zero_le _
      | cons x xs ih => exact Nat.max_le.mpr ⟨le _ (.head _),ih (fun n hn => le n (.tail _ hn))⟩
    apply fold
    intro a ha
    obtain ⟨tc,mem,rfl⟩ := List.mem_map.mp ha
    obtain ⟨i,hi,eq⟩ := Array.mem_iff_getElem.mp (by simpa using mem : tc ∈ g.comps)
    have hh := levels ⟨i,hi⟩
    have get : g.comp i = tc := by simpa [Layout.comp,hi] using eq
    rw [get] at hh
    change tc.params.levels+1 ≤ _ at hh; omega
  have nv : vs.length ≤ L.maxPocEntries+1 := by unfold vs volumes; split <;> simp <;> omega
  let term := fun (q : Volume × Nat) =>
    let v := q.1
    (q.2+1)*v.le g*((List.range' v.compStart (v.ce g-v.compStart)).foldl (fun a i =>
      (List.range' v.resStart (v.re g-v.resStart)).foldl (fun a r => a+g.numPrecincts i r) a) 0)
  have each (q : Volume × Nat) (hit : q ∈ vs.zipIdx) :
      term q ≤ (L.maxPocEntries+1)*L.maxLayers*(L.maxComponents*((L.maxDecompLevels+1)*2^64)) := by
    let v := q.1
    have index : q.2 < vs.length := by
      simpa using List.snd_lt_add_of_mem_zipIdx hit
    have layer : v.le g ≤ L.maxLayers := Nat.le_trans (Nat.min_le_right ..) layers
    have cr : v.ce g - v.compStart ≤ L.maxComponents := by unfold Volume.ce; omega
    have rr : v.re g - v.resStart ≤ L.maxDecompLevels+1 := by unfold Volume.re; omega
    apply Nat.mul_le_mul (Nat.mul_le_mul (by omega) layer)
    let cs := List.range' v.compStart (v.ce g-v.compStart)
    let rs := List.range' v.resStart (v.re g-v.resStart)
    have bound (i : Nat) (mem : i ∈ cs) : (rs.map (g.numPrecincts i)).sum ≤ (L.maxDecompLevels+1)*2^64 := by
      have hi := List.mem_range'.mp mem
      have cc : v.ce g ≤ g.numComps := Nat.min_le_right ..
      have sm := compRect_bound hp hg (i := i) (by omega)
      have bz := fold_limit rs (g.numPrecincts i) (2^64) 0 (by
        intro r _
        unfold Layout.numPrecincts
        split
        · exact res_product (res_small sm r) _ _
        · exact Nat.zero_le _)
      simp only [fold_sum,Nat.zero_add] at bz
      exact Nat.le_trans bz (Nat.mul_le_mul_right _ (by simpa only [rs,List.length_range'] using rr))
    simp only [fold_sum,Nat.zero_add]
    have bz := fold_limit cs (fun i => (rs.map (g.numPrecincts i)).sum) _ 0 bound
    simp only [fold_sum,Nat.zero_add] at bz
    exact Nat.le_trans bz (Nat.mul_le_mul_right _ (by simpa only [cs,List.length_range'] using cr))
  have all := fold_limit vs.zipIdx term _ 0 each
  simp only [fold_sum,Nat.zero_add,List.length_zipIdx] at all
  unfold iterationWork
  rw [← List.sum_eq_foldl_nat]
  exact Nat.le_trans all (Nat.mul_le_mul_right _ (by simpa using nv))

private def mapWithResult {α : Type} {cap : Nat} {P : α → Prop} {x : Except Error α}
    (scan : Scan cap P x) : Scan cap (fun a => P a ∧ x = .ok a) x :=
  post scan (fun _ ok p => ⟨p,ok⟩)

private def resolveGeom (cap : Nat) (L : Limits) (tc : TileCompGeom) (r : Nat)
    (hr : r ≤ tc.params.levels) (sm : SmallRect tc.rect) (room : 2^64 ≤ cap) :
    Scan cap (fun res : ResolutionGeom => res.numPrecincts ≤ L.maxPrecincts ∧
      (∀ b ∈ res.bands, SmallRect b.rect)) (resolution L tc r) := by
  unfold resolution
  dsimp only
  rw [ite_eq_right (by omega : ¬r > tc.params.levels)]
  apply chain (check cap L _ .precincts _ (Nat.zero_le _)
    (Nat.le_trans (res_product (res_small sm r) ..) room))
  intro _ prec
  rw [← Array.forIn_toList]
  refine chain (walkList (fun _ => True) _ _ _ trivial ?_) ?_
  · intro b mem _
    have val : b.numCodeBlocks ≤ cap := by
      obtain ⟨orient,_,rfl⟩ := Array.mem_map.mp (Array.mem_def.mpr mem)
      exact Nat.le_trans (res_product (band_small sm r orient) ..) room
    intro _
    exact chain (check cap L _ .codeBlocks _ (Nat.zero_le _) val) (fun _ _ => ⟨trivial⟩)
  · intro _ _
    refine PLift.up ⟨prec,?_⟩
    intro b mem
    obtain ⟨o,_,rfl⟩ := Array.mem_map.mp mem
    exact band_small sm r o

private theorem clip_grid (a b x y e : Nat) :
    gridCount (max a x) (max (max a x) (min b y)) e ≤ b := by
  by_cases h : min b y ≤ max a x
  · rw [Nat.max_eq_left h]; simp [gridCount]
  · rw [Nat.max_eq_right (show max a x ≤ min b y by omega)]
    exact Nat.le_trans (grid_le ..) (Nat.min_le_left ..)

private def precinctScan (cap : Nat) (L : Limits) (res : ResolutionGeom) (k : Nat)
    (inside : k < res.numPrecincts) (small : ∀ b ∈ res.bands, SmallRect b.rect) (room : 2^64 ≤ cap) :
    Scan cap (fun pg : PrecinctGeom => ∀ b ∈ pg.bands, b.cw*b.ch ≤ L.maxCodeBlocks)
      (precinct L res k) := by
  unfold precinct
  dsimp only
  rw [ite_eq_right (by omega : ¬ k ≥ res.numPrecincts)]
  apply chain (mapScan (fun b : PrecinctBandGeom => b.cw*b.ch ≤ L.maxCodeBlocks) _ _ ?_)
  · intro _ h; exact ⟨h⟩
  · intro b mem
    have sm := small b mem
    let rect := precinctBandRect res b (k%res.pw) (k/res.pw)
    have wx : gridCount rect.x0 rect.x1 b.cbWidthExp ≤ 2^32 := Nat.le_trans (clip_grid ..) sm.1
    have wy : gridCount rect.y0 rect.y1 b.cbHeightExp ≤ 2^32 := Nat.le_trans (clip_grid ..) sm.2
    have wh := Nat.mul_le_mul wx wy
    split
    · exact chain (check cap L _ .codeBlocks 0 (Nat.zero_le _) (Nat.zero_le _)) (fun _ h => ⟨h⟩)
    · exact chain (check cap L _ .codeBlocks _ (Nat.zero_le _) (Nat.le_trans wh room)) (fun _ h => ⟨h⟩)

private def fromSuccess {α : Type} {cap : Nat} (x : Except Error α) (ok : ∃ a, x = .ok a) :
    Scan cap (fun _ => True) x := by
  cases x with
  | ok => exact ⟨trivial⟩
  | error => exact False.elim (by obtain ⟨_,h⟩ := ok; cases h)

private def stateScan (cap : Nat) (L : Limits) (tc : TileCompGeom) (r : Nat) (pg : PrecinctGeom)
    (leaves : ∀ b ∈ pg.bands, b.cw*b.ch ≤ L.maxCodeBlocks) :
    Scan cap (fun _ => True) (PrecState.init L tc.params r pg) := by
  unfold PrecState.init
  refine chain (mapScan (fun _ => True) _ _ ?_) (fun _ _ => ⟨trivial⟩)
  intro b mem
  let tr := fromSuccess (cap := cap) _ (RoundTrip.tagTree_create_of_le (leaves b mem))
  exact chain tr (fun _ _ => chain tr (fun _ _ => ⟨trivial⟩))

private abbrev SetupState := Array PrecState × Array (Array Nat) × Array (Array (Nat × Nat)) × Nat
private abbrev ResState := Array PrecState × Nat × Array Nat × Array (Nat × Nat)

/-- Scalar cap for tile layout, POC preflight, initialization and packed-header checks. -/
def tileCap (L : Limits) (n : Nat) :=
  2^64 + preflightValue L + 2*L.maxPrecincts + 4*L.maxCodeBlocks + L.maxTiles +
    L.maxComponents + L.maxTiles*L.maxTilePartsPerTile + L.maxTileParts + callbackCap L n + n

private def initScan {L : Limits} {d : ByteArray} {h : Header} {t g c}
    (hp : Header.parse L d = .ok h) (layout : Layout.ofHeader h t = .ok (g,c)) :
    Scan (tileCap L d.size) (fun _ => True) (initPrecincts L g) := by
  let cap := tileCap L d.size
  have room : 2^64 ≤ cap := by unfold cap tileCap; omega
  have prCap : 2*L.maxPrecincts ≤ cap := by unfold cap tileCap; omega
  have cbCap : 4*L.maxCodeBlocks ≤ cap := by unfold cap tileCap; omega
  unfold initPrecincts
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,Nat.sub_zero,Nat.div_one,Nat.add_one_sub_one]
  let outer := fun (_ : Nat) (s : SetupState) => s.1.size ≤ L.maxPrecincts ∧ s.2.2.2 ≤ L.maxCodeBlocks
  refine chain (rangeBound outer _ 0 g.numComps _ ⟨Nat.zero_le _,Nat.zero_le _⟩ ?_) (fun _ _ => ⟨trivial⟩)
  intro i hi s hs
  have sm := compRect_bound hp layout (i := i) (by omega)
  let mid := fun (_ : Nat) (z : ResState) => z.1.size ≤ L.maxPrecincts ∧ z.2.1 ≤ L.maxCodeBlocks
  apply chain (rangeBound mid _ 0 ((g.comp i).params.levels+1) _ hs ?_)
  · intro z hz; exact PLift.up ⟨_,rfl,hz⟩
  · intro r hr z hz
    apply chain (mapWithResult (resolveGeom cap L (g.comp i) r (by omega) sm room))
    rintro res ⟨⟨num,small⟩,re⟩
    apply chain (check cap L _ .precincts (z.1.size+res.numPrecincts) (Nat.zero_le _) (by have := hz.1; omega))
    intro _ admitted
    change z.1.size+res.numPrecincts ≤ L.maxPrecincts at admitted
    let inner := fun j (a : Array PrecState × Nat) => a.1.size = z.1.size+j ∧ a.2 ≤ L.maxCodeBlocks
    apply chain (rangeBound inner _ 0 res.numPrecincts _ ⟨rfl,hz.2⟩ ?_)
    · intro a ha
      exact PLift.up ⟨_,rfl,Nat.le_trans (Nat.le_of_eq (by simpa [inner] using ha.1)) admitted,ha.2⟩
    · intro k hk a ha
      apply chain (mapWithResult (precinctScan cap L res k (by omega) small room))
      rintro pg ⟨leaf,get⟩
      obtain ⟨_,three,blocks⟩ := HeaderWork.precinct_geometry re get
      have sum := fold_limit pg.bands.toList (fun b => b.codeBlocks.size) L.maxCodeBlocks 0
        (fun b hb => blocks b (by simpa using hb))
      simp only [Array.foldl_toList,Array.length_toList,Nat.zero_add] at sum
      have bound := Nat.le_trans sum (Nat.mul_le_mul_right _ three)
      apply chain (check cap L _ .codeBlocks _ (Nat.zero_le _) (by have := ha.2; omega))
      intro _ total
      apply chain (stateScan cap L (g.comp i) r pg leaf)
      intro st _
      exact PLift.up ⟨_,rfl,by simp [ha.1,Nat.add_assoc],total⟩

open JPEG2000.TilePart

private theorem parsedRows {L : Limits} {d : ByteArray} {h : Header} (hp : Header.parse L d = .ok h) :
    h.tiles.size ≤ L.maxTiles := by
  have count {corr ps i n} (f : Nat) (a : Array Tile) {z}
      (ok : assembleTiles L corr ps f i n a = .ok z) : z.size ≤ a.size+f := by
    induction f generalizing i n a with
    | zero => cases ok; omega
    | succ f ih =>
      simp only [assembleTiles] at ok
      split at ok
      · have := ih _ ok; omega
      split at ok <;> try contradiction
      split at ok <;> try contradiction
      have := ih _ ok; simp only [Array.size_push] at this; omega
  unfold Header.parse at hp
  obtain ⟨_,_,hp⟩ := Tier2Equiv.bind_ok hp
  unfold parseCodestreamIn at hp
  iterate 5 obtain ⟨_,_,hp⟩ := Tier2Equiv.bind_ok hp
  obtain ⟨ts,parts,hp⟩ := Tier2Equiv.bind_ok hp
  obtain ⟨_,_,hp⟩ := Tier2Equiv.bind_ok hp
  obtain ⟨_,mapped,hp⟩ := Tier2Equiv.bind_ok hp
  obtain ⟨_,_,hp⟩ := Tier2Equiv.bind_ok hp
  cases hp
  unfold parseTileParts at parts
  obtain ⟨_,checked,parts⟩ := Tier2Equiv.bind_ok parts
  obtain ⟨_,_,parts⟩ := Tier2Equiv.bind_ok parts
  exact (ColorResources.channel_map_size mapped) ▸ Nat.le_trans (by simpa using count _ _ parts)
    ((Limits.check_eq_ok_iff ..).1 checked)

private def rankScan {L : Limits} {d : ByteArray} {h : Header} (hp : Header.parse L d = .ok h) :
    Scan (tileCap L d.size) (fun _ => True) (NativeCost.ranks L h) := by
  let cap := tileCap L d.size
  have count := fold_limit h.tiles.toList (fun t => t.tile.parts.size) L.maxTilePartsPerTile 0
    (fun t ht => (HeaderWork.parse_tile_storage hp t (by simpa using ht)).1)
  simp only [Array.foldl_toList, Array.length_toList, Nat.zero_add] at count
  have total : numTileParts h ≤ L.maxTiles*L.maxTilePartsPerTile :=
    Nat.le_trans count (Nat.mul_le_mul_right _ (parsedRows hp))
  unfold NativeCost.ranks
  split
  · exact ⟨trivial⟩
  unfold ppmChunkIndex
  apply chain (check cap L _ .tileParts _ (Nat.zero_le _) (by unfold cap tileCap; omega))
  intro _ checked
  split
  · have chunks := (HeaderWork.parse_ppm hp).1
    have ha : h.ppm.chunks.size ≤ cap := by unfold cap tileCap; omega
    have hb : numTileParts h ≤ cap := by unfold cap tileCap; omega
    exact ⟨Nat.zero_le _,closeExpr (catExpr (catExpr (catExpr (catExpr (litExpr _ "PPM: ") (decExpr ha))
      (litExpr _ " Nppm/Ippm chunks for ")) (decExpr hb)) (litExpr _ " tile-parts")) (by decide) (by decide)⟩
  · exact ⟨trivial⟩

private def gatherScan (cap : Nat) (ppm : Bool) (d : ByteArray) (rs : Array ByteRange)
    (inside : ∀ r ∈ rs, r.stop ≤ d.size) : Scan cap (fun _ => True) (gather ppm d rs) := by
  unfold gather
  dsimp only
  rw [← Array.forIn_toList]
  refine chain (walkList (fun _ => True) _ _ _ trivial ?_) (fun _ _ => ⟨trivial⟩)
  intro r hr _ _
  have valid := inside r (by simpa using hr)
  rw [ite_eq_right (Nat.not_lt.mpr valid)]
  exact ⟨trivial⟩

private def selectScan {L : Limits} {d : ByteArray} {h : Header} {tp : TileParams}
    (hp : Header.parse L d = .ok h) (mem : tp ∈ h.tiles) (idx : Array Nat) :
    Scan (tileCap L d.size) (fun _ => True) (headerStreamAt h d tp idx) := by
  let cap := tileCap L d.size
  have inside := DiagnosticPacketRanges.parsed_ranges hp
  unfold headerStreamAt
  split
  · split
    · exact ⟨Nat.zero_le _,oneFixed _ (by decide)⟩
    · simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,Nat.sub_zero,
        Nat.div_one,Nat.add_one_sub_one]
      let P := fun (_ : Nat) (rs : Array ByteRange) => ∀ r ∈ rs, r.stop ≤ d.size
      apply chain (rangeScan P _ 0 tp.tile.parts.size #[] (by simp [P]) ?_)
      · intro rs good
        exact chain (gatherScan cap true d rs good) (fun _ _ => ⟨trivial⟩)
      · intro k rs old
        split
        · split
          · rename_i chunk found
            refine PLift.up ⟨_,rfl,?_⟩
            intro r hr
            exact (Array.mem_append.mp hr).elim (old r) (inside.1 _ (Array.mem_of_getElem? found) _)
          · exact ⟨Nat.zero_le _,oneFixed _ (by decide)⟩
        · exact ⟨Nat.zero_le _,oneFixed _ (by decide)⟩
  · split
    · exact chain (gatherScan cap false d _ (inside.2 tp mem)) (fun _ _ => ⟨trivial⟩)
    · exact ⟨trivial⟩

private def inputScan {L : Limits} {d : ByteArray} {h : Header} {tp : TileParams}
    (hp : Header.parse L d = .ok h) (mem : tp ∈ h.tiles) :
    Scan (tileCap L d.size) (fun _ => True) (tileData d tp.tile) := by
  unfold tileData
  dsimp only
  rw [← Array.forIn_toList]
  refine chain (walkList (fun _ => True) _ _ _ trivial ?_) (fun _ _ => ⟨trivial⟩)
  intro p hm s _
  have valid := ((HeaderWork.parse_tile_storage hp tp mem).2.2 p (by simpa using hm)).1
  rw [ite_eq_right (Nat.not_lt.mpr valid)]
  exact ⟨trivial⟩

/-- Diagnostics in construction order for a computation, with an allowance on its
number of records, origin of a returned refusal and an invariant on success. -/
structure Audit {α : Type} (cap : Nat) (P : α → Prop) (run : Except Error α) (allowance : Nat) where
  /-- Includes discarded records. -/
  events : List (Σ e, Fault cap e)
  /-- Each entered strict stage or packet is charged before an error can exit the loop. -/
  count : events.length ≤ allowance
  /-- The result keeps the fault built at its failing stage. -/
  origin : ∀ e, run = .error e → ∃ f : Fault cap e, ⟨e,f⟩ ∈ events
  /-- Only successful states are used to enter a later stage. -/
  success : ∀ a, run = .ok a → P a

private def walkAudit (cap : Nat) (L : Limits) (c : Coding) (base : Array (Array Nat))
    (same : Bool) (pb : Nat) (room : L.maxPassesPerCodeBlock+2^32+101 ≤ cap)
    (quota : L.maxCodingPasses+passProposal L ≤ cap) (ps : List Position) (s : LoopState)
    (good : StateOK cap L same pb s) :
    let m := walk (packetStep L c base same pb) ps s
    Audit cap (StateOK cap L same pb) m.2 (2*attempts m.1) := by
  match ps with
  | [] => exact ⟨[],Nat.zero_le _,(by intro _ eq; cases eq),fun _ eq => by cases eq; exact good⟩
  | p :: ps =>
    dsimp only
    rw [walk]
    split
    · let rest := walkAudit cap L c base same pb room quota ps s good
      refine ⟨rest.events,?_,rest.origin,rest.success⟩
      change rest.events.length ≤ 2*attempts ((p,.skip)::(walk (packetStep L c base same pb) ps s).1)
      simpa only [attempts,List.countP_cons,PacketAction.attempted,Bool.false_eq_true,ite_false,Nat.add_zero] using rest.count
    · let events := stepEvents cap L c base same pb s p.packet good room quota
      have count := @stepEvents_count cap L c base same pb s p.packet good room quota
      have size : events.length ≤ 2 := by
        unfold events
        rw [count]
        generalize discarded c base s p.packet = b
        generalize (!(packetStep L c base same pb s p.packet).isOk) = b'
        cases b <;> cases b' <;> decide
      cases step : packetStep L c base same pb s p.packet with
      | error e =>
        refine ⟨events,size,?_,by intro _ eq; cases eq⟩
        intro err eq
        cases eq
        obtain ⟨f,mem⟩ := refused_mem (stepScan cap L c base same pb s p.packet good room quota) step
        exact ⟨f,List.mem_append_right _ mem⟩
      | ok t =>
        have inv := stepScan cap L c base same pb s p.packet good room quota
        rw [step] at inv
        let rest := walkAudit cap L c base same pb room quota ps t inv.down
        let m := walk (packetStep L c base same pb) ps t
        refine ⟨events ++ rest.events,?_,?_,rest.success⟩
        · change (events ++ rest.events).length ≤ 2*attempts ((p,.accepted (t.passes-s.passes))::m.1)
          rw [List.length_append]
          have bound : rest.events.length ≤ 2*attempts m.1 := rest.count
          simp only [attempts,List.countP_cons,PacketAction.attempted,ite_true] at *
          omega
        · intro e bad
          obtain ⟨f,mem⟩ := rest.origin e bad
          exact ⟨f,List.mem_append_right _ mem⟩

private def beforeAudit {α β : Type} {cap : Nat} {P : α → Prop} {x : Except Error α}
    {next : α → PacketLog × Except Error β} (scan : Scan cap P x)
    (k : ∀ a, P a → x = .ok a → let m := next a; Audit cap (fun _ => True) m.2 (1+2*attempts m.1)) :
    let m := before x next; Audit cap (fun _ => True) m.2 (1+2*attempts m.1) := by
  cases x with
  | error e =>
    exact ⟨[⟨e,scan⟩],Nat.le_refl _,(by intro _ eq; cases eq; exact ⟨scan,.head _⟩),fun _ _ => trivial⟩
  | ok a => exact k a scan.down rfl

/-- The production exhaustion check after the raw result has been materialized. -/
def packedEnd (tp : TileParams) (hs : Option HeaderStream) (t : TileCodeBlocks) :
    Except Error TileCodeBlocks := do
  if let some s := hs then
    if t.headerStreamConsumed != s.bytes.size then
      throw (.malformed (.atOffset .tier2 t.headerStreamConsumed)
        s!"tile {tp.index}: {s.bytes.size - t.headerStreamConsumed} bytes of packed packet headers left over")
  return t

private def endScan (cap : Nat) (tp : TileParams) (hs : Option HeaderStream) (t : TileCodeBlocks)
    (tile : tp.index ≤ cap)
    (sizes : ∀ b, hs = some b → b.bytes.size ≤ cap ∧ t.headerStreamConsumed ≤ cap) :
    Scan cap (fun _ => True) (packedEnd tp hs t) := by
  cases hs with
  | none => exact ⟨trivial⟩
  | some b =>
    obtain ⟨total,offset⟩ := sizes b rfl
    unfold packedEnd
    dsimp only
    split
    · exact ⟨offset,closeExpr (catExpr (catExpr (catExpr (catExpr (litExpr _ "tile ") (decExpr tile))
        (litExpr _ ": ")) (decExpr (show b.bytes.size-t.headerStreamConsumed ≤ cap by omega)))
        (litExpr _ " bytes of packed packet headers left over")) (by decide) (by decide)⟩
    · exact ⟨trivial⟩

private def finishAudit {α β : Type} {cap : Nat} {P : α → Prop} (m : PacketLog × Except Error α)
    (k : α → Except Error β) (a : Audit cap P m.2 (2*attempts m.1))
    (postRun : ∀ z, P z → Scan cap (fun _ => True) (k z)) :
    Audit cap (fun _ => True) (afterRun m k).2 (1+2*attempts m.1) := by
  cases eq : m.2 with
  | error e =>
    refine ⟨a.events,by have := a.count; omega,?_,fun _ _ => trivial⟩
    intro err bad
    simp only [afterRun,eq,bind,Except.bind,Except.error.injEq] at bad
    exact a.origin _ (bad ▸ eq)
  | ok z =>
    let scan := postRun z (a.success z eq)
    let tail := refused (k z) scan
    have size : tail.length ≤ 1 := by
      unfold tail; rw [refused_count]; cases (!(k z).isOk) <;> decide
    refine ⟨a.events ++ tail,by rw [List.length_append]; have := a.count; omega,?_,fun _ _ => trivial⟩
    intro err bad
    simp only [afterRun,eq,bind,Except.bind] at bad
    obtain ⟨f,hf⟩ := refused_mem scan bad
    exact ⟨f,List.mem_append_right _ hf⟩

private def streamAudit {L : Limits} {d : ByteArray} {h : Header} {tp : TileParams} {idx hs pb}
    (hp : Header.parse L d = .ok h) (mem : tp ∈ h.tiles) (tile : tp.index ≤ L.maxTiles)
    (selected : headerStreamAt h d tp idx = .ok hs) (prior : pb ≤ L.maxCodingPasses) :
    let m := measureStream L h d tp hs pb
    Audit (tileCap L d.size) (fun _ => True) m.2 (1+2*attempts m.1) := by
  let cap := tileCap L d.size
  have ht : tp.index ≤ cap := by unfold cap tileCap; omega
  have hc : h.siz.csiz ≤ cap := by have := (HeaderWork.parse_storage hp).2.1; unfold cap tileCap; omega
  have cb : callbackCap L d.size ≤ cap := by unfold cap tileCap; omega
  have room : L.maxPassesPerCodeBlock+2^32+101 ≤ cap := by unfold callbackCap at cb; omega
  have quota : L.maxCodingPasses+passProposal L ≤ cap := by unfold callbackCap at cb; omega
  have stream : ∀ b, hs = some b → b.bytes.size ≤ cap := by
    rintro b rfl
    exact Nat.le_trans (HeaderWork.parsed_headerStream hp mem selected).2 (Nat.le_trans (packed_le ..) cb)
  unfold measureStream
  apply beforeAudit (layoutScan cap h tp.index ht hc)
  rintro ⟨g,c⟩ _ layout
  have pf := preflight_bound hp layout
  apply beforeAudit (check cap L _ .packets _ (Nat.zero_le _) (by unfold cap tileCap; omega))
  intro _ _ _
  apply beforeAudit (initScan hp layout)
  rintro ⟨ps,base,spans⟩ _ init
  apply beforeAudit (inputScan hp mem)
  rintro ⟨buf,parts⟩ _ input
  let same := (hs.map HeaderStream.bytes).isNone
  have size := (HeaderWork.tileData_copy_charge d tp.tile).2.2 buf parts input
  have small := Nat.le_trans size.1 (Nat.mul_le_mul_right d.size (HeaderWork.parse_tile_storage hp tp mem).1)
  have initial : StateOK cap L same pb (firstState ps buf hs) := by
    refine ⟨startStates init,prior,by unfold callbackCap at cb; exact show buf.size ≤ cap by omega,?_⟩
    cases hs with
    | none => intro eq; simp [same] at eq
    | some b => exact fun _ => stream b rfl
  apply finishAudit _ (fun s => packedEnd tp hs (outputTile tp same buf parts spans s))
    (walkAudit cap L c base same pb room quota _ _ initial)
  intro s inv
  apply endScan _ _ _ _ ht
  rintro b eq
  refine ⟨stream b eq,?_⟩
  have separate : same = false := by simp [same,eq]
  simpa only [outputTile,separate,Bool.false_eq_true,ite_false] using
    Nat.le_trans s.hdr.pos_le_size (inv.2.2.2 separate)

/-- The present tile's shared rank lookup, packet iteration and final packed-length
check, or the empty tile's immediate return to native reconstruction. -/
def tileResult (L : Limits) (h : Header) (d : ByteArray) (idx : Array (Array Nat)) (v : TileVisit) :
    Except Error (Option TileCodeBlocks) := do
  let some tp := presentAt h v.tile v.cursor | return none
  let hs ← headerStreamAt h d tp (idx.getD v.cursor #[])
  return some (← decodeWithStream L h d tp hs v.passesBefore)

private theorem prepared {L : Limits} {d : ByteArray} {red h dst}
    (ok : PublicPacketWork.prepareTiles L d red = .ok (h,dst)) : Header.parse L d = .ok h := by
  unfold PublicPacketWork.prepareTiles at ok
  obtain ⟨_,_,ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨_,hp,ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨_,_,ok⟩ := Tier2Equiv.bind_ok ok
  cases ok; exact hp

private theorem tileNumber {L : Limits} {d : ByteArray} {red v}
    (member : v ∈ (PublicPacketWork.measure L d red).1) : v.tile ≤ L.maxTiles := by
  obtain ⟨pre,tail,split⟩ := List.append_of_mem member
  obtain ⟨_,_,_,_,_,_,_,_,ix,_,_⟩ := NativeCost.destination_storage L d red split
  have len := (PublicPacketWork.decode_packet_work L d red).2.1
  rw [split,List.length_append,List.length_cons] at len
  omega

private theorem presentIndex {h : Header} {t j : Nat} {tp : TileParams}
    (eq : presentAt h t j = some tp) : tp.index = t := by
  unfold presentAt at eq
  split at eq <;> try contradiction
  split at eq <;> cases eq; assumption

/-- The deterministic construction record for a tile in the public trace. The
successful prepare and rank equations identify the actual header and shared table.
The count includes a possible terminal setup, selection or exhaustion refusal. -/
def visitAudit {L : Limits} {d : ByteArray} {red h dst idx v}
    (entry : PublicPacketWork.prepareTiles L d red = .ok (h,dst)) (rank : NativeCost.ranks L h = .ok idx)
    (hit : v ∈ (PublicPacketWork.measure L d red).1) :
    Audit (tileCap L d.size) (fun _ => True) (tileResult L h d idx v) (1+2*attempts v.packets) := by
  have facts := NativeCost.visited_storage L d red v hit
  have prior : v.passesBefore ≤ L.maxCodingPasses := by obtain ⟨_,_,_,_,_,prior,_⟩ := facts; exact prior
  have source : NativeCost.VisitStorage L h d v := by
    obtain ⟨_,_,entry',_,_,_,src⟩ := facts
    rw [entry] at entry'; cases entry'; exact src
  have src : match presentAt h v.tile v.cursor with
      | none => v.packets = []
      | some tp => match headerStreamAt h d tp (idx.getD v.cursor #[]) with
        | .error _ => v.packets = []
        | .ok hs => (measureStream L h d tp hs v.passesBefore).1 = v.packets := by
    obtain ⟨idx',rank',_,_,src⟩ := source
    rw [rank] at rank'; cases rank'
    split <;> rename_i sel
    · simpa only [sel] using src
    · simp only [sel] at src
      split <;> rename_i got
      · simpa only [got] using src.2.2
      · have eq := src.2.2
        rw [got] at eq
        exact (SegmentHistory.packet_prefix_counts (prepared entry) _ _ _ prior).1.symm.trans eq.2.1
  unfold tileResult
  cases sel : presentAt h v.tile v.cursor with
  | none =>
    exact ⟨[],Nat.zero_le _,(by intro _ eq; cases eq),fun _ _ => trivial⟩
  | some tp =>
    have hp := prepared entry
    have mem := SegmentHistory.present_mem sel
    have tile := (presentIndex sel) ▸ tileNumber hit
    dsimp only
    let scan := selectScan hp mem (idx.getD v.cursor #[])
    cases selected : headerStreamAt h d tp (idx.getD v.cursor #[]) with
    | error e =>
      rw [selected] at scan
      refine ⟨[⟨e,scan⟩],by simp,?_,fun _ _ => trivial⟩
      intro err eq; cases eq; exact ⟨scan,.head _⟩
    | ok hs =>
      let a := streamAudit hp mem tile selected prior
      simp only [sel,selected] at src
      have er := measureStream_erase hp tp hs v.passesBefore
      refine ⟨a.events,src ▸ a.count,?_,fun _ _ => trivial⟩
      intro err bad
      apply a.origin
      rw [er]
      cases run : decodeWithStream L h d tp hs v.passesBefore <;> simp [run,bind,Except.bind,pure,Except.pure] at bad
      exact congrArg Except.error bad

/-- Store selection and iteration followed by the geometry lookup used by native reconstruction. -/
def reachedLayout (L : Limits) (h : Header) (d : ByteArray) (idx : Array (Array Nat))
    (v : TileVisit) : Except Error (Layout × Coding) := do
  let _ ← tileResult L h d idx v
  Layout.ofHeader h v.tile

/-- The geometry call at entry to the public centred-tile callback also runs on
absent tiles. It runs only after the store and its packed check return successfully.
Subsequent native coefficient, transform and placement stages have separate meters. -/
def geometryAudit {L : Limits} {d : ByteArray} {red h dst idx v}
    (entry : PublicPacketWork.prepareTiles L d red = .ok (h,dst)) (rank : NativeCost.ranks L h = .ok idx)
    (hit : v ∈ (PublicPacketWork.measure L d red).1) :
    Audit (tileCap L d.size) (fun _ => True) (reachedLayout L h d idx v) (2+2*attempts v.packets) := by
  let old := visitAudit entry rank hit
  let cap := tileCap L d.size
  have ht : v.tile ≤ cap := by have := tileNumber hit; unfold cap tileCap; omega
  have hc : h.siz.csiz ≤ cap := by have := (HeaderWork.parse_storage (prepared entry)).2.1; unfold cap tileCap; omega
  let scan := layoutScan cap h v.tile ht hc
  let next := fun (x : Except Error (Option TileCodeBlocks)) =>
    match x with
    | .error _ => []
    | .ok _ => refused (Layout.ofHeader h v.tile) scan
  let events := old.events ++ next (tileResult L h d idx v)
  refine ⟨events,?_,?_,fun _ _ => trivial⟩
  · have count := old.count
    unfold events
    rw [List.length_append]
    have small (x) : (next x).length ≤ 1 := by
      cases x with
      | error => exact Nat.zero_le _
      | ok =>
        simp only [next,refused_count]
        cases (!(Layout.ofHeader h v.tile).isOk) <;> decide
    have := small (tileResult L h d idx v)
    omega
  · intro e bad
    unfold reachedLayout at bad
    cases store : tileResult L h d idx v with
    | error err =>
      rw [store] at bad
      cases bad
      obtain ⟨f,mem⟩ := old.origin _ store
      exact ⟨f,List.mem_append_left _ mem⟩
    | ok cb =>
      rw [store] at bad
      obtain ⟨f,mem⟩ := refused_mem scan bad
      refine ⟨f,List.mem_append_right _ ?_⟩
      simpa only [store,next] using mem

/-- All construction records for an executed prefix, with their aggregate cardinality. -/
structure RecordList (cap slots : Nat) where
  /-- The constructors actually entered, in order. -/
  events : List (Σ e, Fault cap e)
  /-- The allowance is charged on first entry to each contributing stage. -/
  count : events.length ≤ slots

private def collectVisits {cap : Nat} (vs : List TileVisit)
    (per : ∀ v ∈ vs, RecordList cap (2+2*attempts v.packets)) :
    RecordList cap (2*vs.length + 2*imageAttempts vs) := by
  match vs with
  | [] => exact ⟨[],Nat.zero_le _⟩
  | v::vs =>
    let head := per v (.head _)
    let tail := collectVisits vs (fun t ht => per t (.tail _ ht))
    refine ⟨head.events ++ tail.events,?_⟩
    have h := head.count
    have t := tail.count
    simp only [imageAttempts,List.length_cons,List.map_cons,List.sum_cons,List.length_append] at *
    omega

/-- Diagnostic records constructed in the public Tier-2 stage. A failed earlier
admission emits no Tier-2 record. A refused rank preflight suppresses the grid.
Every reached tile gets the rank table at its real cursor and its incoming pass count. -/
def records (L : Limits) (d : ByteArray) (red : Nat) :
    let vs := (PublicPacketWork.measure L d red).1
    RecordList (tileCap L d.size) (1+2*vs.length+2*imageAttempts vs) := by
  dsimp only
  match entry : PublicPacketWork.prepareTiles L d red with
  | .error _ => exact ⟨[],Nat.zero_le _⟩
  | .ok (h,dst) =>
    let scan := rankScan (prepared entry)
    match rank : NativeCost.ranks L h with
    | .error e =>
      rw [rank] at scan
      exact ⟨[⟨e,scan⟩],by simp; omega⟩
    | .ok idx =>
      let vs := (PublicPacketWork.measure L d red).1
      let all := collectVisits vs fun _ hit =>
        let a := geometryAudit entry rank hit
        ⟨a.events,a.count⟩
      exact ⟨all.events,by have := all.count; dsimp only [vs] at *; omega⟩

/-- New string construction, its retained payload and newly built numeric fields,
summed over the observed calls. Borrowed ceilings and caller rendering cost zero. -/
def charge (L : Limits) (d : ByteArray) (red : Nat) :=
  ((records L d red).events.map (fun x => x.2.work)).sum

/-- A refusal during reduction, parsing or output allocation precedes the shared
rank check and constructs no Tier-2 diagnostics. -/
theorem admission_free {L : Limits} {d : ByteArray} {red e}
    (first : PublicPacketWork.prepareTiles L d red = .error e) : charge L d red = 0 := by
  unfold charge records
  split <;> rename_i eq <;> rw [first] at eq <;> cases eq
  rfl

/-- The work charge bounds cumulative logical payload even when an operation
replaces its first diagnostic and only the second record escapes to the caller. -/
theorem storage_le_charge (L : Limits) (d : ByteArray) (red : Nat) :
    ((records L d red).events.map (fun x => x.2.storage)).sum ≤ charge L d red := by
  unfold charge
  generalize (records L d red).events = xs
  induction xs with
  | nil => exact Nat.le_refl _
  | cons f xs ih => exact Nat.add_le_add (fault_storage f.2) ih

/-- Closed upper bound for public Tier-2 diagnostic construction. -/
def budget (L : Limits) (n : Nat) :=
  (1+2*L.maxTiles+2*(L.maxTiles*L.maxPackets))*eventBudget (tileCap L n)

/-- Measured Tier-2 charges compose with the public native meter. Shared placement
is already in the native meter and is charged once. The sharper bound uses the
actual visited and attempted prefixes, including a final refused packet. -/
theorem decode_work (L : Limits) (d : ByteArray) (red : Nat) :
    let m := NativeCost.measure L d red
    let vs := (PublicPacketWork.measure L d red).1
    m.1 = decodeCodestream L d red ∧
      charge L d red ≤ (1+2*vs.length+2*imageAttempts vs)*eventBudget (tileCap L d.size) ∧
      charge L d red ≤ budget L d.size ∧
      m.2 + charge L d red ≤ NativeCost.budget L d.size + budget L d.size := by
  obtain ⟨result,_,_,native,_⟩ := NativeCost.decode_work L d red
  obtain ⟨_,nt,calls,positions,cost,_⟩ := PublicPacketWork.decode_packet_work L d red
  have prefixBound := Nat.le_trans (event_sum (records L d red).events)
    (Nat.mul_le_mul_right _ (records L d red).count)
  have closed : charge L d red ≤ budget L d.size := by
    apply Nat.le_trans prefixBound (Nat.mul_le_mul_right _ ?_)
    omega
  exact ⟨result,prefixBound,closed,Nat.add_le_add native closed⟩

/-- Header work, placement at the caller's byte price, and Tier-2 diagnostic work
on the same public prefix. This form can be used independently of native reconstruction. -/
theorem header_work (B : Nat) (L : Limits) (d : ByteArray) (red : Nat) :
    let vs := (PublicPacketWork.measure L d red).1
    HeaderPayload.publicHeaderCharge L d red + (PublicPacketWork.measurePlacement B L d red).2 +
        charge L d red ≤ HeaderPayload.headerBudget L d.size + HeaderPayload.rankBudget L +
        vs.length*(HeaderPayload.selectionBudget L d.size + placementBudget B L) +
        (1+2*vs.length+2*imageAttempts vs)*eventBudget (tileCap L d.size) :=
  Nat.add_le_add (HeaderPayload.decode_header_work B L d red).2.1 (decode_work L d red).2.1

private abbrev GridState (P : Type) := P × Nat × Nat × Nat

private def observedTile (L : Limits) (h : Header) (d : ByteArray) (idx : Array (Array Nat)) (j pb : Nat) :
    Option TileParams → PacketLog × Except Error (Option TileCodeBlocks)
  | none => ([],.ok none)
  | some tp => before (headerStreamAt h d tp (idx.getD j #[])) fun hs =>
      afterRun (measureStream L h d tp hs pb) (fun t => pure (some t))

private def observedVisit {P T : Type} (L : Limits) (h : Header) (d : ByteArray)
    (tile : Nat → Option TileCodeBlocks → Except Error T) (sat : T → Nat)
    (write : P → T → Except Error P) (idx : Array (Array Nat)) (t : Nat) (s : GridState P) :
    TileVisit × Except Error (GridState P) :=
  let (dst,pb,total,j) := s
  let selected := presentAt h t j
  let r := observedTile L h d idx j pb selected
  (⟨t,j,pb,selected.isSome,r.1⟩,do
    let cb ← r.2
    let out ← tile t cb
    let next ← write dst out
    return (next,pb+(cb.map (·.passes)).getD 0,total+sat out,j+selected.isSome.toNat))

private def walkGrid {P : Type} (f : Nat → GridState P → TileVisit × Except Error (GridState P)) :
    Nat → Nat → GridState P → Measured TileVisit (GridState P)
  | 0,_,s => ([],.ok s)
  | n+1,t,s =>
    let (v,r) := f t s
    match r with
    | .error e => ([v],.error e)
    | .ok z =>
      let rest := walkGrid f n (t+1) z
      (v::rest.1,rest.2)

private theorem observeGrid {P T : Type} (L : Limits) (h : Header) (d : ByteArray)
    (dst : P) (tile : Nat → Option TileCodeBlocks → Except Error T) (sat : T → Nat)
    (write : P → T → Except Error P) :
    measureGrid L h d dst tile sat write = before (NativeCost.ranks L h) (fun idx =>
      walkGrid (observedVisit L h d tile sat write idx) (numTiles h.siz) 0 (dst,0,0,0)) := by
  unfold measureGrid
  congr 1
  funext idx
  generalize numTiles h.siz = n
  generalize (dst,(0:Nat),(0:Nat),(0:Nat)) = s
  generalize (0:Nat) = t
  induction n generalizing t s with
  | zero => rfl
  | succ n ih =>
    rw [walkGrid]
    conv => lhs; whnf
    simp only [ih]
    rfl

private theorem walkStops {P : Type} (f : Nat → GridState P → TileVisit × Except Error (GridState P))
    {v : TileVisit} {e : Error} (bad : ∀ t s, (f t s).1 = v → (f t s).2 = .error e)
    (n t : Nat) (s : GridState P) (hit : v ∈ (walkGrid f n t s).1) :
    (walkGrid f n t s).2 = .error e ∧ ∃ pre, (walkGrid f n t s).1 = pre ++ [v] := by
  induction n generalizing t s with
  | zero => cases hit
  | succ n ih =>
    rw [walkGrid] at hit ⊢
    cases step : f t s with
    | mk w r =>
      rw [step] at hit
      cases r with
      | error err =>
        have eq : v = w := by simpa using hit
        have stop := bad t s (by rw [step,eq])
        rw [step] at stop
        exact ⟨stop,[],by simp [eq]⟩
      | ok z =>
        change v ∈ w :: (walkGrid f n (t+1) z).1 at hit
        rcases List.mem_cons.mp hit with eq | mem
        · have stop := bad t s (by rw [step,eq])
          rw [step] at stop; contradiction
        · obtain ⟨endRun,pre,last⟩ := ih _ _ mem
          exact ⟨endRun,w::pre,by simp [last]⟩

private theorem visitStops {P : Type} {L : Limits} {h : Header} {d : ByteArray} {idx red}
    (hp : Header.parse L d = .ok h) (sat : JPEG2000.Decode.CenteredTile → Nat)
    (write : P → JPEG2000.Decode.CenteredTile → Except Error P) {v e} (bad : reachedLayout L h d idx v = .error e)
    (t : Nat) (s : GridState P)
    (atVisit : (observedVisit L h d (JPEG2000.Decode.centeredTile L h d red) sat write idx t s).1 = v) :
    (observedVisit L h d (JPEG2000.Decode.centeredTile L h d red) sat write idx t s).2 = .error e := by
  subst v
  obtain ⟨dst,pb,total,j⟩ := s
  let run := observedTile L h d idx j pb (presentAt h t j)
  have erased : run.2 = tileResult L h d idx ⟨t,j,pb,(presentAt h t j).isSome,run.1⟩ := by
    unfold tileResult run
    cases selected : presentAt h t j with
    | none => rfl
    | some tp =>
      dsimp only [observedTile]
      cases get : headerStreamAt h d tp (idx.getD j #[]) with
      | error => rfl
      | ok hs => simp only [before,afterRun,measureStream_erase hp,bind,Except.bind]
  change (run.2 >>= fun cb => JPEG2000.Decode.centeredTile L h d red t cb >>= _) = _
  unfold reachedLayout at bad
  change (tileResult L h d idx ⟨t,j,pb,(presentAt h t j).isSome,run.1⟩ >>= fun _ => Layout.ofHeader h t) = _ at bad
  rw [← erased] at bad
  cases result : run.2 with
  | error err => rw [result] at bad; cases bad; rfl
  | ok cb =>
    rw [result] at bad
    change Layout.ofHeader h t = .error e at bad
    simp only [bind,Except.bind,JPEG2000.Decode.centeredTile,bad]

/-- Every refusal charged at a visited tile terminates both public APIs there,
even when its raw iteration had already succeeded. No subsequent tile is entered. -/
theorem public_tile_refusal {L : Limits} {d : ByteArray} {opts : DecodeOptions} {h dst idx v e}
    (entry : PublicPacketWork.prepareTiles L d opts.reduce = .ok (h,dst))
    (rank : NativeCost.ranks L h = .ok idx) (hit : v ∈ (PublicPacketWork.measure L d opts.reduce).1)
    (bad : reachedLayout L h d idx v = .error e) :
    decodeCodestream L d opts.reduce = .error e ∧ JPEG2000.decode L d opts = .error e ∧
    (∃ pre, (PublicPacketWork.measure L d opts.reduce).1 = pre ++ [v]) ∧
    ∃ f : Fault (tileCap L d.size) e, ⟨e,f⟩ ∈ (geometryAudit entry rank hit).events := by
  have origin := (geometryAudit entry rank hit).origin e bad
  have trace := (PublicPacketWork.decode_packet_work L d opts.reduce).1
  simp only [PublicPacketWork.measure,entry,before,measureTiles_finish,afterRun,observeGrid,rank,before] at hit trace ⊢
  obtain ⟨stop,last⟩ := walkStops _ (visitStops (prepared entry) _ _ bad) _ _ _ hit
  rw [stop] at trace
  have raw := trace.symm
  change decodeCodestream L d opts.reduce = .error e at raw
  exact ⟨raw,by simp [JPEG2000.decode,raw,bind,Except.bind],last,origin⟩

private theorem collect_mem {cap : Nat} (vs : List TileVisit)
    (per : ∀ v ∈ vs, RecordList cap (2+2*attempts v.packets))
    (v : TileVisit) (hit : v ∈ vs) {f} (mem : f ∈ (per v hit).events) :
    f ∈ (collectVisits vs per).events := by
  induction vs with
  | nil => cases hit
  | cons w vs ih =>
    rw [collectVisits]
    rcases List.mem_cons.mp hit with rfl | tail
    · exact List.mem_append_left _ mem
    · exact List.mem_append_right _ (ih _ tail mem)

/-- A tile's records are retained by the whole-input diagnostic measure, including
a successful packet's discarded SOP read and errors in the last tile visited. -/
theorem visit_records {L : Limits} {d : ByteArray} {red h dst idx v}
    (entry : PublicPacketWork.prepareTiles L d red = .ok (h,dst)) (rank : NativeCost.ranks L h = .ok idx)
    (hit : v ∈ (PublicPacketWork.measure L d red).1) {f}
    (mem : f ∈ (geometryAudit entry rank hit).events) : f ∈ (records L d red).events := by
  unfold records
  split <;> rename_i eq <;> rw [entry] at eq <;> cases eq
  split <;> rename_i eq <;> rw [rank] at eq <;> cases eq
  apply collect_mem _ (fun _ hv => ⟨(geometryAudit entry rank hv).events,(geometryAudit entry rank hv).count⟩) v hit
  exact mem

/-- A refusing shared rank preflight is the sole Tier-2 construction on that
input. Its typed count is bounded before admission, including when the caller
sets the tile-part limit below the count already collected. -/
theorem public_rank_refusal {L : Limits} {d : ByteArray} {opts : DecodeOptions} {h dst e}
    (entry : PublicPacketWork.prepareTiles L d opts.reduce = .ok (h,dst)) (bad : NativeCost.ranks L h = .error e) :
    decodeCodestream L d opts.reduce = .error e ∧ JPEG2000.decode L d opts = .error e ∧
      ∃ f : Fault (tileCap L d.size) e, (records L d opts.reduce).events = [⟨e,f⟩] := by
  have trace := (PublicPacketWork.decode_packet_work L d opts.reduce).1
  simp only [PublicPacketWork.measure,entry,before,measureTiles_finish,afterRun,observeGrid,bad,
    bind,Except.bind] at trace
  have raw : decodeCodestream L d opts.reduce = .error e := trace.symm
  refine ⟨raw,by simp [JPEG2000.decode,raw,bind,Except.bind],?_⟩
  unfold records
  split <;> rename_i eq <;> rw [entry] at eq <;> cases eq
  split <;> rename_i eq <;> rw [bad] at eq <;> cases eq
  exact ⟨_,rfl⟩

/-- The existing sharp PPM decimal bounds apply to the singleton actually
constructed at the shared rank stage, before any packet or tile is entered. -/
theorem ppm_mismatch {L : Limits} {d : ByteArray} {opts : DecodeOptions} {h dst}
    (entry : PublicPacketWork.prepareTiles L d opts.reduce = .ok (h,dst))
    (present : h.ppm.segments.isEmpty = false) (parts : numTileParts h ≤ L.maxTileParts)
    (mismatch : h.ppm.chunks.size ≠ numTileParts h) :
    let msg := s!"PPM: {h.ppm.chunks.size} Nppm/Ippm chunks for {numTileParts h} tile-parts"
    let e := Error.malformed JPEG2000.Tier2.Headers.loc msg
    decodeCodestream L d opts.reduce = .error e ∧ JPEG2000.decode L d opts = .error e ∧
      retainedBytes e ≤ Text.byteBound L.maxTileParts 128 24 ∧
      ∃ f : Fault (tileCap L d.size) e, (records L d opts.reduce).events = [⟨e,f⟩] := by
  have admission := entry
  unfold PublicPacketWork.prepareTiles at admission
  obtain ⟨_,reduce,admission⟩ := Tier2Equiv.bind_ok admission
  obtain ⟨_,parse,admission⟩ := Tier2Equiv.bind_ok admission
  obtain ⟨_,alloc,admission⟩ := Tier2Equiv.bind_ok admission
  cases admission
  obtain ⟨_,_,raw,pub,bytes,_⟩ :=
    DiagnosticCost.public_ppm_mismatch ((Limits.check_eq_ok_iff ..).1 reduce) parse alloc present parts mismatch
  refine ⟨raw,pub,bytes,(public_rank_refusal entry ?_).2.2⟩
  have guard := (Limits.check_eq_ok_iff L JPEG2000.Tier2.Headers.loc .tileParts (numTileParts h)).2 parts
  simp [NativeCost.ranks,present,ppmChunkIndex,guard,mismatch,bind,Except.bind]
  rfl

/-- In a selected tile the post-iteration check consumes exactly the successful
raw result whose per-range translation has already been charged by the native
meter. A mismatch preserves that work and the audit charges the later diagnosis. -/
theorem packed_refusal {L : Limits} {d : ByteArray} {opts : DecodeOptions} {h dst idx v tp stream t}
    (entry : PublicPacketWork.prepareTiles L d opts.reduce = .ok (h,dst)) (rank : NativeCost.ranks L h = .ok idx)
    (hit : v ∈ (PublicPacketWork.measure L d opts.reduce).1) (sel : presentAt h v.tile v.cursor = some tp)
    (get : headerStreamAt h d tp (idx.getD v.cursor #[]) = .ok (some stream))
    (raw : (NativeCost.packetMeter L h d tp (some stream) v.passesBefore).1 = .ok t)
    (leftover : t.headerStreamConsumed ≠ stream.bytes.size) :
    let e := Error.malformed (.atOffset .tier2 t.headerStreamConsumed)
      s!"tile {tp.index}: {stream.bytes.size - t.headerStreamConsumed} bytes of packed packet headers left over"
    decodeCodestream L d opts.reduce = .error e ∧ JPEG2000.decode L d opts = .error e ∧
      ∃ f : Fault (tileCap L d.size) e, ⟨e,f⟩ ∈ (records L d opts.reduce).events := by
  intro e
  let hs := some stream
  have bad : packedEnd tp hs t = .error e := by simp [packedEnd,hs,leftover]; rfl
  rw [NativeCost.packetMeter_result (prepared entry)] at raw
  have postRun : decodeWithStream L h d tp hs v.passesBefore = .error e := by
    change (decodeTilePacketsWith L h d tp (hs.map HeaderStream.bytes) v.passesBefore >>= packedEnd tp hs) = _
    rw [raw]; exact bad
  change decodeWithStream L h d tp (some stream) v.passesBefore = .error e at postRun
  have rejected : tileResult L h d idx v = .error e := by simp only [tileResult,sel,get,postRun,bind,Except.bind]
  have stopped : reachedLayout L h d idx v = .error e := by simp [reachedLayout,rejected,bind,Except.bind]
  obtain ⟨native,decoded,_,f,mem⟩ := public_tile_refusal entry rank hit stopped
  exact ⟨native,decoded,f,visit_records entry rank hit mem⟩

end JPEG2000.Spec.Resources.DiagnosticPacket
