import Spec.Resources.PacketSortWork
import Spec.Resources.PublicPacketWork
import Spec.Resources.ProgressionFields

/-!
# Structural work inside a Tier-2 packet attempt

Plan.md §§3–5, 7 (S3), T.800 B.9, B.10.1–8 and B.12. A counted computation
carries the production result, including its diagnostic. Sequential composition
keeps the count of the failing operation. Counts are structural operations on
the Lean data structures, independent of runtime array uniqueness.
-/

namespace JPEG2000.Spec.Resources.PacketLocalWork

open JPEG2000.Bytes JPEG2000.TagTree JPEG2000.Tier2.Packet JPEG2000.Progression
open JPEG2000.Header JPEG2000.TilePart JPEG2000.Tier2.Headers PacketTraversal

/-- A computation instrumented against a particular production expression and
a budget measured in the units specified by the caller. -/
structure Counted {α : Type} (production : Except Error α) (budget : Nat) where
  /-- Measured outcome, including the original diagnostic on failure. -/
  result : Except Error α
  /-- Number of charged operations, including those before an error. -/
  work : Nat
  /-- Erasing the instrumentation recovers the production result. -/
  erase : result = production
  /-- The bound holds for both outcomes. -/
  within : work ≤ budget

private def pay {α : Type} (x : Except Error α) (n : Nat) : Counted x n :=
  ⟨x, n, rfl, Nat.le_refl _⟩

private def widen {α : Type} {x : Except Error α} {n m : Nat} (a : Counted x n) (h : n ≤ m) :
    Counted x m := ⟨a.result, a.work, a.erase, Nat.le_trans a.within h⟩

private def chain {α β : Type} {x : Except Error α} {f : α → Except Error β} {n m : Nat}
    (a : Counted x n) (k : ∀ z, x = .ok z → Counted (f z) m) : Counted (x >>= f) (n + m) :=
  match h : a.result with
  | .error e => ⟨.error e, a.work, by rw [← a.erase, h]; rfl, by have := a.within; omega⟩
  | .ok z =>
    let b := k z (a.erase.symm.trans h)
    ⟨b.result, a.work + b.work, by rw [← a.erase, h]; exact b.erase, Nat.add_le_add a.within b.within⟩

private def afterMap {α β : Type} {x : Except Error α} {n : Nat}
    (a : Counted x n) (f : α → β) : Counted (x >>= fun z => pure (f z)) n :=
  widen (chain a (fun z _ => pay (.ok (f z)) 0)) (by omega)

private def tick {α : Type} {x : Except Error α} {n : Nat} (a : Counted x n) :
    Counted x (1 + n) := ⟨a.result, 1 + a.work, a.erase, Nat.add_le_add_left a.within 1⟩

private def nodeBits (next : BitReader → Except Error (Bool × BitReader)) :
    (n low : Nat) → (s : BitReader) → Counted (readLoop next n low s) n
  | 0, _, _ => pay _ 0
  | n+1, low, s => by
    unfold readLoop
    cases h : next s with
    | error => exact widen (pay _ 1) (by omega)
    | ok z =>
      obtain ⟨b,s'⟩ := z
      cases b
      · exact widen (tick (nodeBits next n (low+1) s')) (by omega)
      · exact widen (pay _ 1) (by omega)

private def node (t i low : Nat) (lo va : Array Nat) (s : BitReader) :
    Counted (nodeStep bitNext t i low lo va s) (1 + t) := by
  unfold nodeStep
  dsimp only
  split
  · exact widen (pay _ 1) (by omega)
  · let a := nodeBits bitNext (t - max low (lo.getD i 0)) (max low (lo.getD i 0)) s
    exact ⟨_, 1 + a.work, rfl, by have := a.within; omega⟩

private def path (t : Nat) : (n off w h x y : Nat) → (lo va : Array Nat) → (s : BitReader) →
    Counted (JPEG2000.TagTree.walk bitNext t n off w h x y lo va s) (n * (1 + t))
  | 0, _, _, _, _, _, _, _, _ => widen (pay _ 0) (by simp)
  | 1, off, w, _, x, y, lo, va, s => widen (node t (off+y*w+x) 0 lo va s) (by simp)
  | n+2, off, w, h, x, y, lo, va, s => by
    let parent := path t (n+1) (off+w*h) ((w+1)/2) ((h+1)/2) (x/2) (y/2) lo va s
    let child := fun (z : Nat × Nat × Array Nat × Array Nat × BitReader) =>
      node t (off+y*w+x) z.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2
    cases parent.result with
    | error e => exact ⟨_, parent.work, rfl, by have := parent.within; simp only [Nat.succ_mul] at *; omega⟩
    | ok p => exact ⟨_, parent.work + (child p).work, rfl, by
        have := parent.within; have := (child p).within
        simp only [Nat.succ_mul] at *; omega⟩

/-- Node visits plus attempted bit reads for one actual inclusion query. -/
def inclusion (tr : Tree) (br : BitReader) (leaf t : Nat) :
    Counted (TagTree.decode tr br leaf t) (1 + tr.numLevels * (1 + t)) := by
  unfold TagTree.decode decodeWith
  split
  · let a := path t tr.numLevels 0 tr.w tr.h (leaf%tr.w) (leaf/tr.w) tr.low tr.val br
    exact ⟨_, 1 + a.work, rfl, Nat.add_le_add_left a.within 1⟩
  · exact widen (pay _ 1) (by omega)

private theorem depth_after {tr : Tree} {br : BitReader} {leaf t z}
    (ok : decodeWith bitNext tr br leaf t = .ok z) : z.2.1.numLevels = tr.numLevels := by
  unfold decodeWith at ok
  split at ok <;> try contradiction
  split at ok <;> cases ok
  rfl

private def values (leaf : Nat) : (n t : Nat) → (tr : Tree) → (br : BitReader) →
    Counted (valueLoop bitNext leaf n t tr br) (n * (1 + tr.numLevels * (1 + (t+n))))
  | 0, _, _, _ => widen (pay _ 0) (by simp)
  | n+1, t, tr, br => by
    let a := inclusion tr br leaf t
    let k := fun (z : Bool × Tree × BitReader) (hz : decodeWith bitNext tr br leaf t = .ok z) =>
      (show Counted (if z.1 then .ok (t-1,z.2) else valueLoop bitNext leaf n (t+1) z.2.1 z.2.2)
        (n * (1 + tr.numLevels * (1 + (t+(n+1))))) from by
          split
          · exact widen (pay _ 0) (Nat.zero_le _)
          · exact widen (values leaf n (t+1) z.2.1 z.2.2) (by rw [depth_after hz]; simp [Nat.add_comm,Nat.add_left_comm]))
    have inc := Nat.mul_le_mul_left tr.numLevels (show 1+t ≤ 1+(t+(n+1)) by omega)
    cases hz : a.result with
    | error e => exact ⟨_, a.work, rfl, by have := a.within; rw [Nat.succ_mul]; omega⟩
    | ok z =>
      let b := k z (a.erase.symm.trans hz)
      exact ⟨_, a.work + b.work, rfl, by have := a.within; have := b.within; rw [Nat.succ_mul]; omega⟩

/-- Zero-bit-plane queries include the initial threshold zero and the last
unsuccessful threshold when the signalled value exceeds the band bound. -/
def zeroPlanes (tr : Tree) (br : BitReader) (leaf maxZero : Nat) :
    Counted (TagTree.decodeValue tr br leaf maxZero)
      ((maxZero+2) * (1 + tr.numLevels * (1+(maxZero+2)))) :=
  by simpa only [JPEG2000.TagTree.decodeValue, decodeValueWith, Nat.zero_add] using values leaf (maxZero+2) 0 tr br


private theorem ok_bind {α β : Type} {x : Except Error α} {f : α → Except Error β} {z} :
    (x >>= f) = .ok z ↔ ∃ y, x = .ok y ∧ f y = .ok z := by
  cases x <;> simp [bind, Except.bind]

private def commas : (n acc : Nat) → (br : BitReader) → Counted (commaCode n acc br) n
  | 0, _, _ => pay _ 0
  | n+1, acc, br => by
    unfold commaCode
    refine widen (chain (pay (readBit br) 1) (m := n) ?_) (by omega)
    rintro ⟨b,s⟩ _
    cases b
    · exact widen (pay _ 0) (by omega)
    · exact commas n (acc+1) s

private def bitFieldAux (b : BitReader) (acc : UInt32) : (n : Nat) →
    Counted (b.bitsAux acc n) n
  | 0 => pay _ 0
  | n+1 => by
    unfold BitReader.bitsAux
    exact widen (chain (pay b.bit 1) (fun ⟨v,s⟩ _ => bitFieldAux s ((acc <<< 1) ||| v) n)) (by omega)

private def field (b : BitReader) (n : Nat) : Counted (b.bits n) (min n 32) := by
  unfold BitReader.bits
  split
  · exact widen (bitFieldAux b 0 n) (by omega)
  · exact widen (pay _ 0) (by omega)

private def passes (br : BitReader) : Counted (readNumPasses br) 16 := by
  unfold readNumPasses
  refine chain (pay (readBit br) 1) (m := 15) ?_
  rintro ⟨b,s⟩ _
  cases b
  · exact widen (pay _ 0) (by decide)
  · refine chain (pay (readBit s) 1) (m := 14) ?_
    rintro ⟨b,s⟩ _
    cases b
    · exact widen (pay _ 0) (by decide)
    · refine chain (field s 2) (m := 12) ?_
      rintro ⟨v,s⟩ _
      dsimp only
      split
      · exact widen (pay _ 0) (by decide)
      · refine chain (field s 5) (m := 7) ?_
        rintro ⟨v,s⟩ _
        dsimp only
        split
        · exact widen (pay _ 0) (by decide)
        · exact afterMap (field s 7) _

private theorem runs_size (style n first cur : Nat) :
    (segmentRuns style n first cur).length ≤ n + (if cur = 0 then 0 else 1) := by
  induction n generalizing first cur with
  | zero => simp only [segmentRuns]; split <;> simp
  | succ n ih =>
    simp only [segmentRuns]
    split
    · have := ih (first+1) 0
      simp at this
      simp only [List.length_cons]; split <;> omega
    · have := ih (first+1) (cur+1)
      simp at this
      split <;> omega

private theorem pieces_size (style n first : Nat) :
    (segmentPasses style n first).length ≤ n := by simpa [segmentPasses] using runs_size style n first 0

private def lengths (lb : Nat) : (ps : List Nat) → (s : BitReader) →
    Counted (readLengths lb ps s) (ps.length * 33)
  | [], _ => pay _ 0
  | p::ps, s => by
    unfold readLengths
    refine widen (tick (chain (field s (lb + Nat.log2 p)) (m := ps.length*33) ?_)) ?_
    · exact fun ⟨_,b⟩ _ => afterMap (lengths lb ps b) _
    · simp only [List.length_cons, Nat.succ_mul]; omega

private theorem lengths_size (lb : Nat) (ps : List Nat) (s : BitReader) {out}
    (ok : readLengths lb ps s = .ok out) : out.1.length = ps.length := by
  induction ps generalizing s out with
  | nil => cases ok; rfl
  | cons p ps ih =>
    simp only [readLengths, ok_bind] at ok
    obtain ⟨⟨v,b⟩,_,⟨r,b'⟩,hr,ok⟩ := ok
    cases ok
    exact congrArg Nat.succ (ih _ hr)

/-- Per-block header budget. Each length has one piece visit and at most 32
bit attempts. Run classification visits each new pass once. The local passes
check precedes splitting even when the later cumulative check refuses. -/
def blockBudget (L : Limits) (layer depth maxZero : Nat) : Nat :=
  1 + (1 + depth*(1+(layer+1))) + ((maxZero+2)*(1+depth*(1+(maxZero+2)))) +
    (16 + 33 + L.maxPassesPerCodeBlock*34)

private def tailHeader (L : Limits) (style bi k : Nat) (cb : CodeBlock) (bs : BandState) (br : BitReader) :
    Counted (do
      let (n,br) ← readNumPasses br
      let (inc,br) ← commaCode 33 0 br
      let lb := cb.lblock + inc
      L.check (locAt br.pos) .passesPerCodeBlock (cb.numPasses+n)
      let (ps,br) ← readLengths lb (segmentPasses style n cb.numPasses) br
      let cont := cb.numPasses > 0 && !passEndsSegment style (cb.numPasses-1)
      let cb := { cb with lblock := lb, numPasses := cb.numPasses+n }
      pure ({ bs with blocks := bs.blocks.setIfInBounds k cb },
        some ({ band := bi, block := k, pieces := ps, cont } : Contribution), br))
      (16 + 33 + L.maxPassesPerCodeBlock*34) := by
  refine widen (chain (passes br) (m := 33 + L.maxPassesPerCodeBlock*34) ?_) (by omega)
  rintro ⟨n,b⟩ _
  refine chain (commas 33 0 b) ?_
  rintro ⟨i,b'⟩ _
  refine widen (chain (pay (L.check (locAt b'.pos) .passesPerCodeBlock (cb.numPasses+n)) 0)
    (m := L.maxPassesPerCodeBlock*34) ?_) (by omega)
  intro u ok
  have cap : cb.numPasses + n ≤ L.maxPassesPerCodeBlock := (Limits.check_eq_ok_iff ..).1 ok
  let rs := segmentPasses style n cb.numPasses
  have sz := pieces_size style n cb.numPasses
  let a := lengths (cb.lblock+i) rs b'
  exact ⟨_, n+a.work, rfl, by have := a.within; dsimp only [rs] at *; omega⟩

/-- The actual block's inclusion path, value queries, pass classification and length
reads. The failed operation is included. Each visited length contributes one piece slot. -/
def blockHeader (L : Limits) (style layer bi k : Nat) (bs : BandState) (br : BitReader)
    (d z : Nat) (hi : bs.incl.numLevels ≤ d) (hz : bs.zbp.numLevels ≤ d) (hm : bs.maxZero ≤ z) :
    Counted (headerBlock L style layer bi k bs br) (blockBudget L layer d z) := by
  unfold headerBlock
  cases hx : bs.blocks[k]? with
  | none => exact widen (pay _ 1) (by unfold blockBudget; omega)
  | some cb =>
    let ib := 1+d*(1+(layer+1))
    let zb := (z+2)*(1+d*(1+(z+2)))
    let tb := 16+33+L.maxPassesPerCodeBlock*34
    have iz : 1 + bs.incl.numLevels*(1+(layer+1)) ≤ ib :=
      Nat.add_le_add_left (Nat.mul_le_mul_right _ hi) 1
    have zz : (bs.maxZero+2)*(1+bs.zbp.numLevels*(1+(bs.maxZero+2))) ≤ zb :=
      Nat.mul_le_mul (by omega) (Nat.add_le_add_left (Nat.mul_le_mul hz (by omega)) 1)
    by_cases prev : cb.included = true
    · simp only [prev, ↓reduceIte]
      refine widen (tick (chain (pay (readBit br) 1) (m := tb) ?_)) (by
        dsimp [tb,blockBudget]; omega)
      rintro ⟨inc,br'⟩ _
      cases inc
      · exact widen (pay _ 0) (Nat.zero_le _)
      · exact tailHeader L style bi k cb bs br'
    · simp only [prev, Bool.false_eq_true, ↓reduceIte]
      refine widen (tick (chain (inclusion bs.incl br k (layer+1)) (m := zb+tb) ?_))
        (by change 1 + (1 + bs.incl.numLevels * (1 + (layer+1)) + (zb+tb)) ≤ 1+ib+zb+tb; omega)
      rintro ⟨inc,bs',br'⟩ he
      cases inc
      · exact widen (pay _ 0) (Nat.zero_le _)
      · simp only [pure_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        refine widen (chain (zeroPlanes bs.zbp br' k bs.maxZero) (m := tb) ?_) (by omega)
        rintro ⟨v,tr,b'⟩ _
        exact tailHeader L style bi k { cb with included := true, firstLayer := layer, zeroBitPlanes := v }
          { bs with incl := bs', zbp := tr } b'


/-- Per-precinct geometry used to price the header loops. -/
structure GeometryBudget where
  /-- Maximum blocks in any of its bands. -/
  blocks : Nat
  /-- Maximum number of levels in either tag tree. -/
  depth : Nat
  /-- Maximum admissible number of zero bit-planes. -/
  planes : Nat

private def fits (g : GeometryBudget) (b : BandState) : Prop :=
  b.blocks.size ≤ g.blocks ∧ b.incl.numLevels ≤ g.depth ∧ b.zbp.numLevels ≤ g.depth ∧ b.maxZero ≤ g.planes

/-- Every band of this precinct meets the supplied per-band bounds. -/
def Fits (g : GeometryBudget) (s : PrecState) : Prop := ∀ b ∈ s.bands, fits g b

private theorem value_depth (leaf : Nat) : ∀ n t tr br z,
    valueLoop bitNext leaf n t tr br = .ok z → z.2.1.numLevels = tr.numLevels
  | 0, _, _, _, _, h => by cases h
  | n+1, t, tr, br, _, h => by
    simp only [valueLoop] at h
    split at h <;> try contradiction
    rename_i b tree src eq
    have depth := depth_after eq
    split at h
    · cases h; exact depth
    · exact (value_depth leaf n (t+1) tree src _ h).trans depth

private def optionWeight : Option Contribution → Nat
  | none => 0
  | some c => 1 + c.pieces.length

private theorem tail_size {L : Limits} {cb : CodeBlock} {n b m s ps style}
    (checked : L.check (locAt b.pos) .passesPerCodeBlock (cb.numPasses + n) = .ok ())
    (fields : readLengths m (segmentPasses style n cb.numPasses) b = .ok (ps,s)) :
    ps.length ≤ L.maxPassesPerCodeBlock := by
  have cap : cb.numPasses+n ≤ L.maxPassesPerCodeBlock := (Limits.check_eq_ok_iff ..).1 checked
  rw [lengths_size _ _ _ fields]
  exact Nat.le_trans (pieces_size ..) (by omega)

private theorem block_post {g : GeometryBudget} {L : Limits} {style layer bi k bs br out}
    (h : fits g bs) (ok : headerBlock L style layer bi k bs br = .ok out) :
    fits g out.1 ∧ optionWeight out.2.1 ≤ 1 + L.maxPassesPerCodeBlock := by
  obtain ⟨hblocks,hi,hz,hm⟩ := h
  unfold headerBlock at ok
  cases hx : bs.blocks[k]? with
  | none => simp [hx] at ok
  | some cb =>
    cases prev : cb.included <;>
      simp only [hx, prev, Bool.false_eq_true, ↓reduceIte, ok_bind, pure, Except.pure, Except.ok.injEq] at ok
    all_goals
      obtain ⟨⟨inc,src⟩,read,_,rfl,ok⟩ := ok
      cases inc
      · cases ok
        first
        | exact ⟨⟨hblocks,hi,hz,hm⟩, Nat.zero_le _⟩
        | exact ⟨⟨hblocks,Nat.le_trans (Nat.le_of_eq (depth_after read)) hi,hz,hm⟩,Nat.zero_le _⟩
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, ok_bind, Except.ok.injEq] at ok
        first
        | obtain ⟨⟨_,tr,b⟩,v,_,rfl,⟨n,b1⟩,_,⟨i,b2⟩,_,u,hc,⟨ps,b3⟩,fields,ok⟩ := ok
        | obtain ⟨_,rfl,⟨n,b1⟩,_,⟨i,b2⟩,_,u,hc,⟨ps,b3⟩,fields,ok⟩ := ok
        cases ok
        refine ⟨⟨by simpa using hblocks, ?_, ?_, hm⟩, Nat.add_le_add_left (tail_size hc fields) 1⟩
        all_goals first
          | exact hi
          | exact hz
          | exact Nat.le_trans (Nat.le_of_eq (depth_after read)) hi
          | exact Nat.le_trans (Nat.le_of_eq (value_depth _ _ _ _ _ _ v)) hz

/-- Number of contribution descriptors plus their length/pass pairs. -/
def weight (a : Array Contribution) : Nat :=
  (a.toList.map (fun c => 1+c.pieces.length)).sum

private abbrev Iter {α β : Type} (f : α → β → Except Error (ForInStep β)) (xs : List α) (s : β) :=
  forIn xs s f

private def countFor {α β : Type} {P : β → Prop} {f : α → β → Except Error (ForInStep β)}
    (price : α → Nat) (each : ∀ x s, P s → Counted (f x s) (price x))
    (pres : ∀ x s y, P s → f x s = .ok y → P y.value) :
    (xs : List α) → (s : β) → P s → Counted (Iter f xs s) ((xs.map price).sum)
  | [], _, _ => pay _ 0
  | x::xs, s, hs => by
    simp only [Iter,List.forIn_cons,List.map_cons,List.sum_cons]
    refine chain (each x s hs) ?_
    intro step eq
    cases step with
    | done => exact widen (pay _ 0) (Nat.zero_le _)
    | yield t => exact countFor price each pres xs t (pres x s _ hs eq)

private theorem for_post {α β : Type} {P : β → Prop} {f : α → β → Except Error (ForInStep β)}
    (w : β → Nat) (step : Nat) (each : ∀ x s y, P s → f x s = .ok y →
      P y.value ∧ w y.value ≤ w s + step) (xs : List α) (s : β) (hs : P s) (t : β)
    (ok : Iter f xs s = .ok t) : P t ∧ w t ≤ w s + xs.length*step := by
  induction xs generalizing s t with
  | nil => cases ok; simp [hs]
  | cons x xs ih =>
    rw [Iter,List.forIn_cons] at ok
    obtain ⟨y,hy,ok⟩ := ok_bind.mp ok
    obtain ⟨hp,hw⟩ := each x s y hs hy
    cases y with
    | done s' => cases ok; dsimp only [ForInStep.value] at hw; exact ⟨hp, by simp only [List.length_cons,Nat.succ_mul]; omega⟩
    | yield s' =>
      obtain ⟨p,w'⟩ := ih s' hp t ok
      exact ⟨p, by simp only [List.length_cons,Nat.succ_mul]; dsimp only [ForInStep.value] at hw; omega⟩

open Tier2Equiv in
private theorem bandStep_post {L : Limits} {g : GeometryBudget} {style layer bi k s y}
    (h : fits g s.1) (ok : bandBody L style layer bi k s = .ok y) :
    fits g y.value.1 ∧ weight y.value.2.2 ≤ weight s.2.2 + (1+L.maxPassesPerCodeBlock) := by
  unfold bandBody at ok
  obtain ⟨⟨bs,c,b⟩,hr,ok⟩ := ok_bind.mp ok
  obtain ⟨hb,hp⟩ := block_post h hr
  cases c with
  | none => cases ok; exact ⟨hb, by dsimp; omega⟩
  | some c => cases ok; exact ⟨hb, by simpa [weight,optionWeight,Nat.add_assoc] using Nat.add_le_add_left hp (weight s.2.2)⟩

private theorem sum_const {α : Type} (xs : List α) (n : Nat) :
    (xs.map (fun _ => n)).sum = xs.length*n := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih,Nat.succ_mul,Nat.add_comm]

open Tier2Equiv in
private def bandHeader (L : Limits) (g : GeometryBudget) (style layer bi : Nat) (bs : BandState)
    (br : BitReader) (h : fits g bs) :
    Counted (headerBand L style layer bi bs br) (g.blocks * blockBudget L layer g.depth g.planes) := by
  rw [headerBand_eq]
  let each := fun k (s : BandState × BitReader × Array Contribution) (hs : fits g s.1) =>
    (show Counted (bandBody L style layer bi k s) (blockBudget L layer g.depth g.planes) from by
      let a := blockHeader L style layer bi k s.1 s.2.1 g.depth g.planes hs.2.1 hs.2.2.1 hs.2.2.2
      exact ⟨_, a.work, rfl, a.within⟩)
  let a := countFor _ each (fun _ _ _ hs eq => (bandStep_post hs eq).1) (List.range' 0 bs.blocks.size)
    (bs,br,#[]) h
  exact widen (afterMap a _) (by rw [sum_const,List.length_range']; exact Nat.mul_le_mul_right _ h.1)

open Tier2Equiv in
private theorem band_post {L : Limits} {g : GeometryBudget} {style layer bi bs br z}
    (h : fits g bs) (ok : headerBand L style layer bi bs br = .ok z) :
    fits g z.1 ∧ weight z.2.1 ≤ g.blocks*(1+L.maxPassesPerCodeBlock) := by
  rw [headerBand_eq] at ok
  obtain ⟨s,loop,ok⟩ := ok_bind.mp ok
  cases ok
  obtain ⟨hp,hw⟩ := for_post (P := fun s => fits g s.1) (fun s => weight s.2.2) _
    (fun _ _ _ hs eq => bandStep_post hs eq) _ _ h _ loop
  refine ⟨hp, Nat.le_trans ?_ (Nat.mul_le_mul_right _ h.1)⟩
  simpa [weight] using hw


private abbrev bandsFit (g : GeometryBudget) (a : Array BandState) := ∀ b ∈ a, fits g b

private theorem set_pres {α : Type} {a : Array α} {P : α → Prop} {i x}
    (h : ∀ y ∈ a, P y) (hx : P x) : ∀ y ∈ a.setIfInBounds i x, P y := by
  intro y hy
  rcases Array.mem_or_eq_of_mem_setIfInBounds hy with mem | eq
  · exact h _ mem
  · cases eq; exact hx

open Tier2Equiv in
private theorem bandsStep_post {L : Limits} {g : GeometryBudget} {style layer bi s y}
    (h : bandsFit g s.1) (ok : bandsBody L style layer bi s = .ok y) :
    bandsFit g y.value.1 ∧ weight y.value.2.2 ≤ weight s.2.2 + g.blocks*(1+L.maxPassesPerCodeBlock) := by
  unfold bandsBody at ok
  split at ok <;> try contradiction
  rename_i bs hb
  obtain ⟨⟨bs',cs,b⟩,hr,ok⟩ := ok_bind.mp ok
  cases ok
  obtain ⟨hp,hw⟩ := band_post (h _ (Array.mem_of_getElem? hb)) hr
  refine ⟨set_pres h hp, ?_⟩
  simpa [weight] using Nat.add_le_add_left hw (weight s.2.2)

open Tier2Equiv in
private def headers (L : Limits) (g : GeometryBudget) (layer : Nat) (st : PrecState) (br : BitReader)
    (hs : Fits g st) : Counted (headerBands L layer st br)
      (st.bands.size * (1 + g.blocks * blockBudget L layer g.depth g.planes)) := by
  rw [headerBands_eq]
  let each := fun bi (s : Array BandState × BitReader × Array Contribution) (hs : bandsFit g s.1) =>
    (show Counted (bandsBody L st.style layer bi s) (1+g.blocks*blockBudget L layer g.depth g.planes) from by
      unfold bandsBody
      split
      · rename_i b hb
        exact tick (afterMap (bandHeader L g st.style layer bi b s.2.1 (hs _ (Array.mem_of_getElem? hb))) _)
      · exact widen (pay _ 1) (by omega))
  let a := countFor _ each (fun _ _ _ hs eq => (bandsStep_post hs eq).1) (List.range' 0 st.bands.size)
    (st.bands,br,#[]) hs
  exact widen (afterMap a _) (by rw [sum_const,List.length_range']; exact Nat.le_refl _)

open Tier2Equiv in
private theorem headers_post {L : Limits} {g : GeometryBudget} {layer st br z}
    (hs : Fits g st) (ok : headerBands L layer st br = .ok z) :
    Fits g z.1 ∧ weight z.2.1 ≤ st.bands.size * (g.blocks*(1+L.maxPassesPerCodeBlock)) := by
  rw [headerBands_eq] at ok
  obtain ⟨s,loop,ok⟩ := ok_bind.mp ok
  cases ok
  obtain ⟨hp,hw⟩ := for_post (f := Tier2Equiv.bandsBody L st.style layer) (P := fun (s : Array BandState × BitReader × Array Contribution) => bandsFit g s.1) (fun s => weight s.2.2) _
    (fun _ _ _ hs eq => bandsStep_post hs eq) _ (st.bands,br,#[]) hs _ loop
  exact ⟨hp,by simpa [weight] using hw⟩

private def takeRanges (r : Reader) : (ps : List (Nat × Nat)) →
    Counted (takePieces r ps) ps.length
  | [] => pay _ 0
  | (p,n)::ps => by
    unfold takePieces
    split
    · exact widen (pay _ 1) (by simp)
    · refine widen (tick (chain (pay (r.skip n) 0) (m := ps.length) ?_)) (by simp [Nat.add_comm])
      exact fun r' _ => afterMap (takeRanges r' ps) _

/-- A successful contribution produces one direct range per length. The ranges
partition exactly the skipped interval, so their total cannot exceed the unread
body bytes. The body reader never copies a fragment. -/
theorem takePieces_extent (r : Reader) (ps : List (Nat × Nat)) {rs r'}
    (ok : takePieces r ps = .ok (rs,r')) :
    rs.length = ps.length ∧ r'.data = r.data ∧ r'.stop = r.stop ∧
    r'.pos = r.pos + (rs.map (fun p => p.2.length)).sum ∧
    (rs.map (fun p => p.2.length)).sum ≤ r.stop-r.pos ∧
    ∀ z ∈ rs, r.pos ≤ z.2.offset ∧ z.2.stop ≤ r'.pos := by
  induction ps generalizing r rs r' with
  | nil => cases ok; simp
  | cons x xs ih =>
    obtain ⟨p,n⟩ := x
    simp only [takePieces] at ok
    split at ok <;> try contradiction
    simp only [ok_bind] at ok
    obtain ⟨b,skip,⟨rest,t⟩,tail,ok⟩ := ok
    cases ok
    obtain ⟨pos,stop,data,_⟩ := Reader.skip_pos skip
    obtain ⟨hs,hd,ht,hp,hl,all⟩ := ih b tail
    simp only [List.length_cons,List.map_cons,List.sum_cons,List.mem_cons,ByteRange.stop] at *
    refine ⟨by omega, hd.trans data, ht.trans stop, by omega, by have := t.pos_le; omega, ?_⟩
    intro z h
    rcases h with rfl | mem
    · exact ⟨Nat.le_refl _, by dsimp; omega⟩
    · obtain ⟨a,c⟩ := all z mem
      exact ⟨by omega,c⟩


private theorem push_count (xs : Array ByteRange) (r : ByteRange) :
    (pushRange xs r).size ≤ xs.size + 1 := by
  unfold pushRange
  (repeat' split) <;> simp [Array.size_pop]

/-- Logical segment and range records retained in the code-block, before translating
the tile buffer's offsets back to the original tile-part ranges. -/
def segmentSlots (ss : Array Segment) : Nat :=
  ss.size + (ss.toList.map (fun s => s.ranges.size)).sum

/-- Each piece adds at most one segment record and one range record, including
empty pieces, continuation across layers and merging adjacent nonempty ranges. -/
theorem addPieces_storage (cb : CodeBlock) (cont : Bool) (rs : List (Nat × ByteRange)) :
    segmentSlots (addPieces cb cont rs).segments ≤ segmentSlots cb.segments + 2*rs.length := by
  induction rs generalizing cb cont with
  | nil => simp [addPieces]
  | cons x xs ih =>
    obtain ⟨p,r⟩ := x
    unfold addPieces
    apply Nat.le_trans (ih _ false)
    simp only [List.length_cons,Nat.mul_succ]
    generalize cb.segments = ss
    by_cases he : ss = #[]
    · subst ss
      cases cont <;> simp [segmentSlots]
      all_goals have hx := push_count #[] r; simp at hx; omega
    · obtain ⟨a,s,rfl⟩ := Array.exists_push_of_ne_empty he
      cases cont <;> simp [segmentSlots]
      · have hx := push_count #[] r; simp at hx; omega
      · have hx := push_count s.ranges r; omega

open Tier2Equiv in
private def bodies (st : PrecState) (cs : Array Contribution) (body : Reader) :
    Counted (readBody st cs body) (4*weight cs) := by
  rw [readBody_eq]
  let each := fun (c : Contribution) (s : Array BandState × Reader) (_ : True) =>
    (show Counted (bodyBody c s) (4*(1+c.pieces.length)) from by
      unfold bodyBody
      refine widen (tick (chain (takeRanges s.2 c.pieces) (m := 3*c.pieces.length) ?_)) (by omega)
      rintro ⟨rs,b⟩ hr
      dsimp only
      split
      · split
        · exact widen (pay _ (3*rs.length)) (by rw [(takePieces_extent _ _ hr).1]; exact Nat.le_refl _)
        · exact widen (pay _ 0) (Nat.zero_le _)
      · exact widen (pay _ 0) (Nat.zero_le _))
  let a := countFor _ each (fun _ _ _ _ _ => True.intro) cs.toList (st.bands,body) True.intro
  refine widen (afterMap a _) ?_
  have sum (xs : List Contribution) :
      (xs.map (fun c => 4*(1+c.pieces.length))).sum = 4*(xs.map (fun c => 1+c.pieces.length)).sum := by
    induction xs with
    | nil => rfl
    | cons c xs ih => simp only [List.map_cons,List.sum_cons,ih]; omega
  rw [sum]; exact Nat.le_refl _

private structure ByteRun {α : Type} (x : Except Error α) (start : Reader) (reader : α → Reader)
    extends Counted x start.remaining where
  balance : ∀ z, x = .ok z → work + (reader z).remaining = start.remaining

private def pieceBytes (r : Reader) : (ps : List (Nat × Nat)) →
    ByteRun (takePieces r ps) r Prod.snd
  | [] => ⟨⟨_,0,rfl,Nat.zero_le _⟩,by intro z hz; cases hz; simp⟩
  | (p,n)::ps => by
    unfold takePieces
    split
    · exact ⟨widen (pay _ 0) (Nat.zero_le _),by intro _ eq; cases eq⟩
    · cases skip : r.skip n with
      | error e => exact ⟨widen (pay _ 0) (Nat.zero_le _),by intro _ eq; cases eq⟩
      | ok b =>
        let tail := pieceBytes b ps
        obtain ⟨pos,stop,_,_⟩ := Reader.skip_pos skip
        have delta : n+b.remaining = r.remaining := by
          have := b.pos_le; unfold Reader.remaining; omega
        refine ⟨⟨_,n+tail.work,rfl,by have := tail.within; omega⟩,?_⟩
        intro z ok
        change (takePieces b ps >>= _) = .ok z at ok
        obtain ⟨⟨xs,t⟩,ht,ok⟩ := ok_bind.mp ok
        cases ok
        have bal := tail.balance _ ht
        change n+tail.work+t.remaining = r.remaining
        dsimp only at bal; omega

open Tier2Equiv in
private def contributionBytes (c : Contribution) (s : Array BandState × Reader) :
    ByteRun (bodyBody c s) s.2 (fun step => step.value.2) := by
  let a := pieceBytes s.2 c.pieces
  refine ⟨⟨_,a.work,rfl,a.within⟩,?_⟩
  intro step ok
  unfold bodyBody at ok
  obtain ⟨⟨rs,b⟩,read,ok⟩ := ok_bind.mp ok
  dsimp only at ok
  split at ok <;> try contradiction
  split at ok <;> cases ok
  exact a.balance _ read

open Tier2Equiv in
private def bodyByteLoop : (xs : List Contribution) → (s : Array BandState × Reader) →
    ByteRun (forIn xs s bodyBody) s.2 Prod.snd
  | [], s => ⟨⟨_,0,rfl,Nat.zero_le _⟩,by intro z eq; cases eq; simp⟩
  | c::cs, s => by
    rw [List.forIn_cons]
    let a := contributionBytes c s
    cases here : bodyBody c s with
    | error e => exact ⟨⟨_,a.work,rfl,a.within⟩,by intro _ eq; cases eq⟩
    | ok step =>
      have first := a.balance _ here
      cases step with
      | done z => exact ⟨⟨_,a.work,rfl,a.within⟩,by intro _ eq; cases eq; exact first⟩
      | yield z =>
        let tail := bodyByteLoop cs z
        refine ⟨⟨_,a.work+tail.work,rfl,by have := tail.within; dsimp only [ForInStep.value] at first; omega⟩,?_⟩
        intro t ok
        have last := tail.balance t ok
        dsimp only [ForInStep.value] at first last ⊢
        omega

/-- Total length of direct packet-body ranges actually skipped, including the prefix
inside the contribution whose later length or block lookup fails. -/
def bodyRangeBytes (st : PrecState) (cs : Array Contribution) (r : Reader) : Nat :=
  (bodyByteLoop cs.toList (st.bands,r)).work

/-- The entire contribution loop uses at most the available body range. A successful
read accounts for the exact decrease in remaining bytes. The bound applies to an
arbitrary declared contribution table, independently of the cumulative pass decision. -/
theorem body_range_bytes (st : PrecState) (cs : Array Contribution) (r : Reader) :
    bodyRangeBytes st cs r ≤ r.remaining ∧
    ∀ st' t, readBody st cs r = .ok (st',t) → bodyRangeBytes st cs r + t.remaining = r.remaining := by
  let a := bodyByteLoop cs.toList (st.bands,r)
  refine ⟨a.within,?_⟩
  intro st' t ok
  rw [Tier2Equiv.readBody_eq] at ok
  obtain ⟨⟨bs,b⟩,hr,ok⟩ := ok_bind.mp ok
  cases ok
  exact a.balance _ hr


private def slots {α : Type} (f : α → Nat) (xs : Array α) := (xs.toList.map f).sum

private def blockSlots (cb : CodeBlock) := segmentSlots cb.segments
private def bandRecords (bs : BandState) := slots blockSlots bs.blocks

/-- Retained pre-translation segment/range records across every band and block. -/
def retained (bands : Array BandState) : Nat := slots bandRecords bands

private theorem slots_set {α : Type} (f : α → Nat) {xs : Array α} {i old new cost}
    (get : xs[i]? = some old) (h : f new ≤ f old + cost) :
    slots f (xs.setIfInBounds i new) ≤ slots f xs + cost := by
  have aux (ys : List α) (j : Nat) (ok : ys[j]? = some old) :
      ((ys.set j new).map f).sum ≤ (ys.map f).sum + cost := by
    induction ys generalizing j with
    | nil => simp at ok
    | cons y ys ih =>
      cases j with
      | zero => simp at ok; subst y; simp; omega
      | succ j => have := ih j (by simpa using ok); simp only [List.set,List.map_cons,List.sum_cons]; omega
  simpa [slots] using aux xs.toList i (by simpa using get)

private theorem block_records {L : Limits} {style layer bi k bs br out}
    (ok : headerBlock L style layer bi k bs br = .ok out) : bandRecords out.1 = bandRecords bs := by
  unfold headerBlock at ok
  cases hx : bs.blocks[k]? with
  | none => simp [hx] at ok
  | some cb =>
    cases prev : cb.included <;>
      simp only [hx,prev,Bool.false_eq_true,↓reduceIte,ok_bind,pure,Except.pure,Except.ok.injEq] at ok
    all_goals
      obtain ⟨⟨inc,src⟩,_,_,rfl,ok⟩ := ok
      cases inc
      · cases ok; rfl
      · simp only [Bool.not_true,Bool.false_eq_true,↓reduceIte,ok_bind,Except.ok.injEq] at ok
        first
        | obtain ⟨⟨_,_,_⟩,_,_,rfl,⟨_,_⟩,_,⟨_,_⟩,_,_,_,⟨_,_⟩,_,ok⟩ := ok
        | obtain ⟨_,rfl,⟨_,_⟩,_,⟨_,_⟩,_,_,_,⟨_,_⟩,_,ok⟩ := ok
        cases ok
        unfold bandRecords slots
        rw [← Array.toList_map,← Array.toList_map]
        exact congrArg (fun (a : Array Nat) => a.toList.sum) (Tier2WF.map_set_eq _ _ _ _ (by
          intro y hy
          rw [hx] at hy
          cases hy
          rfl))

open Tier2Equiv in
private theorem header_records {L : Limits} {layer st br out} (ok : headerBands L layer st br = .ok out) :
    retained out.1.bands = retained st.bands := by
  have band {style bi bs b z} (ok : headerBand L style layer bi bs b = .ok z) :
      bandRecords z.1 = bandRecords bs := by
    rw [headerBand_eq] at ok
    obtain ⟨s,hr,ok⟩ := ok_bind.mp ok
    cases ok
    refine forIn_inv (fun (s : BandState × BitReader × Array Contribution) => bandRecords s.1 = bandRecords bs)
      _ ?_ _ _ _ rfl hr
    intro k s step hs ht
    unfold bandBody at ht
    obtain ⟨⟨b,c,r⟩,hb,ht⟩ := ok_bind.mp ht
    cases c <;> cases ht <;> exact (block_records hb).trans hs
  rw [headerBands_eq] at ok
  obtain ⟨s,hr,ok⟩ := ok_bind.mp ok
  cases ok
  refine forIn_inv (fun (s : Array BandState × BitReader × Array Contribution) => retained s.1 = retained st.bands)
    _ ?_ _ _ _ rfl hr
  intro k s step hs ht
  unfold bandsBody at ht
  split at ht <;> try contradiction
  rename_i b get
  obtain ⟨⟨b',c,r⟩,hb,ht⟩ := ok_bind.mp ht
  cases ht
  refine Eq.trans ?_ hs
  unfold retained slots
  rw [← Array.toList_map,← Array.toList_map]
  exact congrArg (fun (a : Array Nat) => a.toList.sum) (Tier2WF.map_set_eq _ _ _ _ (by
    intro y hy
    rw [get] at hy
    cases hy
    exact band hb))

open Tier2Equiv in
private theorem bodyRecords (xs : List Contribution) (s t : Array BandState × Reader)
    (ok : forIn xs s bodyBody = .ok t) :
    retained t.1 ≤ retained s.1 + 2*(xs.map (fun c => 1+c.pieces.length)).sum := by
  induction xs generalizing s with
  | nil => cases ok; simp
  | cons c xs ih =>
    rw [List.forIn_cons] at ok
    obtain ⟨y,hy,ok⟩ := ok_bind.mp ok
    unfold bodyBody at hy
    obtain ⟨⟨rs,b⟩,ht,hy⟩ := ok_bind.mp hy
    dsimp only at hy
    split at hy <;> try contradiction
    rename_i bs bsGet
    split at hy <;> try contradiction
    rename_i cb cbGet
    cases hy
    have cbGrowth := addPieces_storage cb c.cont rs
    have bandGrowth := slots_set blockSlots cbGet cbGrowth
    have delta : retained (s.1.setIfInBounds c.band {bs with blocks := bs.blocks.setIfInBounds c.block (addPieces cb c.cont rs)}) ≤ retained s.1 + 2*rs.length :=
      slots_set bandRecords bsGet (new := {bs with blocks := _}) bandGrowth
    have tail := ih _ ok
    have len := (takePieces_extent _ _ ht).1
    simp only [List.map_cons,List.sum_cons]
    dsimp only at tail
    omega

/-- Storage of every completed body-contribution prefix, even when the next one
fails, or when the cumulative pass check discards the completed packet. Uses the
incoming precinct's retained records and the geometry of this attempted packet. -/
theorem packet_prefix_storage {L : Limits} {g : GeometryBudget} {st : PrecState} {layer}
    {nonEmpty : Bool} {br pre cs bits} (h : Fits g st)
    (header : (if nonEmpty then headerBands L layer st br else pure (st,#[],br)) = .ok (pre,cs,bits))
    {xs : List Contribution} (prefixOk : xs <+: cs.toList) (body : Reader) {z}
    (prefixRead : forIn xs (pre.bands,body) Tier2Equiv.bodyBody = .ok z) :
    retained z.1 ≤ retained st.bands + 2*(st.bands.size*(g.blocks*(1+L.maxPassesPerCodeBlock))) := by
  have same : retained pre.bands = retained st.bands := by
    cases nonEmpty
    · cases header; rfl
    · exact header_records header
  have hw : weight cs ≤ st.bands.size*(g.blocks*(1+L.maxPassesPerCodeBlock)) := by
    cases nonEmpty
    · cases header; exact Nat.zero_le _
    · exact (headers_post h header).2
  have hr := bodyRecords xs _ _ prefixRead
  obtain ⟨suffix,eq⟩ := prefixOk
  unfold weight at hw
  rw [← eq,List.map_append,List.sum_append] at hw
  dsimp only at hr
  omega

/-- Structural charge per packet. Includes SOP/EPH and stuffing-byte probes, the
packet-present bit, band/block visits, tag queries, bit attempts, one classification
per new pass, length visits, body range visits, segment/range updates and the final
contribution/pass fold. Counts logical operations and newly introduced records.
Array backing-store copies under sharing and arbitrary-precision arithmetic are
outside these units. -/
def packetBudget (L : Limits) (g : GeometryBudget) (bands layer : Nat) : Nat :=
  10 + bands * (1 + g.blocks*blockBudget L layer g.depth g.planes) +
    5*(bands*(g.blocks*(1+L.maxPassesPerCodeBlock)))

/-- Replays one production packet, preserving the cost of partial reads on a malformed
packet. A successful result can still be refused by the outer cumulative pass test. -/
def packet (L : Limits) (g : GeometryBudget) (sop eph : Bool) (seq layer : Nat)
    (st : PrecState) (same : Bool) (hdr body : Reader) (hs : Fits g st) :
    Counted (decodePacket L sop eph seq layer st same hdr body) (packetBudget L g st.bands.size layer) := by
  let H := st.bands.size*(1+g.blocks*blockBudget L layer g.depth g.planes)
  let W := st.bands.size*(g.blocks*(1+L.maxPassesPerCodeBlock))
  have branch {α β : Type} (p : Prop) [Decidable p] (x y : Except Error α) (f : α → Except Error β) :
      (if p then x >>= f else y >>= f) = (if p then x else y) >>= f := by split <;> rfl
  simp only [decodePacket,branch]
  -- SOP reads at most three big-endian 16-bit words.
  let s := if sop then readSop seq body else pure (false,body)
  refine widen (chain (pay s (if sop then 6 else 0)) (m := 1+H+(3+5*W)) ?_) (by
    unfold packetBudget; split <;> omega)
  rintro ⟨found,b⟩ _
  refine widen (chain (pay (readBit (BitReader.ofReader (if same then b else hdr))) 1)
    (m := H+(3+5*W)) ?_) (by omega)
  rintro ⟨present,br⟩ _
  let head : Counted (if present then headerBands L layer st br else pure (st,#[],br)) H := by
    cases present
    · exact widen (pay _ 0) (Nat.zero_le _)
    · exact headers L g layer st br hs
  refine chain head ?_
  rintro ⟨pre,cs,bits⟩ hh
  have hw : weight cs ≤ W := by
    cases present
    · cases hh; exact Nat.zero_le _
    · exact (headers_post hs hh).2
  refine widen (chain (pay bits.align 1) (m := 2+5*W) ?_) (by omega)
  intro aligned _
  let e := if eph then readEph (aligned.toReader .tier2) else pure (aligned.toReader .tier2)
  refine widen (chain (pay e (if eph then 2 else 0)) (m := 5*W) ?_) (by split <;> omega)
  intro h _
  refine widen (chain (bodies pre cs (if same then h else b)) (m := weight cs) ?_) (by omega)
  exact fun _ _ => pay _ (weight cs)

/-- Erasure and the unconditional local bound use the same attempted computation. -/
theorem packet_work (L : Limits) (g : GeometryBudget) (sop eph : Bool) (seq layer : Nat)
    (st : PrecState) (same : Bool) (hdr body : Reader) (hs : Fits g st) :
    let m := packet L g sop eph seq layer st same hdr body hs
    m.result = decodePacket L sop eph seq layer st same hdr body ∧
      m.work ≤ packetBudget L g st.bands.size layer :=
  ⟨(packet ..).erase,(packet ..).within⟩


/-- Header-derived uniform geometry. Each nonempty block grid has both axes at
most the checked product. The tag tree halves at most once per unit of its initial width-plus-height fuel. -/
def checkedGeometry (L : Limits) : GeometryBudget :=
  ⟨L.maxCodeBlocks, 2*L.maxCodeBlocks+1, 292⟩

/-- At most three bands, each within the geometry established during parsing and initialization. -/
def valid (L : Limits) (st : PrecState) : Prop :=
  st.bands.size ≤ 3 ∧ Fits (checkedGeometry L) st

private theorem level_fuel (f w h : Nat) : JPEG2000.TagTree.levelsAux f w h ≤ f+1 := by
  induction f generalizing w h with
  | zero => exact Nat.le_refl _
  | succ f ih =>
    simp only [JPEG2000.TagTree.levelsAux]
    split
    · omega
    · have := ih ((w+1)/2) ((h+1)/2); omega

private theorem new_depth {L : Limits} {w h : Nat} {tr : Tree}
    (empty : w = 0 ↔ h = 0) (ok : create L w h = .ok tr) :
    tr.numLevels ≤ (checkedGeometry L).depth := by
  unfold create at ok
  obtain ⟨_,hc,ok⟩ := ok_bind.mp ok
  obtain ⟨_,_,ok⟩ := ok_bind.mp ok
  cases ok
  have prod : w*h ≤ L.maxCodeBlocks := (Limits.check_eq_ok_iff ..).1 hc
  apply Nat.le_trans (level_fuel ..)
  change w+h+1 ≤ 2*L.maxCodeBlocks+1
  by_cases hw : w = 0
  · simp [hw,empty.mp hw]
  · have hh := mt empty.mpr hw
    have := Nat.mul_le_mul_left w (show 1 ≤ h by omega)
    have := Nat.mul_le_mul_right h (show 1 ≤ w by omega)
    simp only [Nat.mul_one,Nat.one_mul] at *; omega

open JPEG2000.Tier2.Geometry in
private theorem empty_axes {L : Limits} {res : ResolutionGeom} {p pg}
    (hp : precinct L res p = .ok pg) : ∀ b ∈ pg.bands, b.cw = 0 ↔ b.ch = 0 := by
  unfold precinct at hp
  dsimp only at hp
  split at hp <;> try contradiction
  obtain ⟨bands,hm,hp⟩ := ok_bind.mp hp
  cases hp
  refine Tier2WF.arrayMapM_mem _ _ _ ?_ _ hm
  intro b _ pb ok
  obtain ⟨u,hc,ok⟩ := ok_bind.mp ok
  cases ok
  dsimp only
  split <;> simp_all

private theorem map_size {α β : Type} {xs : Array α} {ys : Array β} {f : α → Except Error β}
    (ok : xs.mapM f = .ok ys) : ys.size = xs.size := by
  have len (l : List α) (out : List β) (ok : l.mapM f = .ok out) : out.length = l.length := by
    induction l generalizing out with
    | nil => cases ok; rfl
    | cons a l ih =>
      rw [List.mapM_cons] at ok
      obtain ⟨_,_,ok⟩ := ok_bind.mp ok
      obtain ⟨l',hl,ok⟩ := ok_bind.mp ok
      cases ok
      exact congrArg Nat.succ (ih l' hl)
  rw [Array.mapM_eq_mapM_toList] at ok
  cases hm : xs.toList.mapM f with
  | error e => rw [hm] at ok; cases ok
  | ok l => rw [hm] at ok; cases ok; simpa using len _ _ hm

open JPEG2000.Tier2.Geometry in
private theorem fresh_valid {L : Limits} {tc : TileCompGeom} {r p res pg st}
    (hc : WideHeaderBounds.ComponentBounds L tc.params) (hr : resolution L tc r = .ok res)
    (hp : precinct L res p = .ok pg) (hs : PrecState.init L tc.params r pg = .ok st) : valid L st := by
  obtain ⟨_,three,blocks⟩ := HeaderWork.precinct_geometry hr hp
  unfold PrecState.init at hs
  obtain ⟨bands,hm,hs⟩ := ok_bind.mp hs
  cases hs
  refine ⟨Nat.le_trans (Nat.le_of_eq (map_size hm)) three,Tier2WF.arrayMapM_mem _ _ _ ?_ _ hm⟩
  intro pb mem b ok
  obtain ⟨incl,hi,ok⟩ := ok_bind.mp ok
  obtain ⟨zbp,hz,ok⟩ := ok_bind.mp ok
  cases ok
  exact ⟨by simpa [checkedGeometry] using blocks pb mem, new_depth (empty_axes hp pb mem) hi,
    new_depth (empty_axes hp pb mem) hz, hc.block_planes r pb.band⟩

private theorem for_mem {α β : Type} (P : β → Prop) (f : α → β → Except Error (ForInStep β))
    (xs : List α) (each : ∀ x ∈ xs, ∀ s y, P s → f x s = .ok y → P y.value)
    (s y : β) (hs : P s) (ok : forIn xs s f = .ok y) : P y := by
  induction xs generalizing s y with
  | nil => cases ok; exact hs
  | cons x xs ih =>
    rw [List.forIn_cons] at ok
    obtain ⟨step,he,ok⟩ := ok_bind.mp ok
    have h := each x (by simp) s step hs he
    cases step with
    | done => cases ok; exact h
    | yield => exact ih (fun a ha => each a (by simp [ha])) _ _ h ok

private theorem initial_valid {L : Limits} {h : Header} {data : ByteArray} {t g c ps base spans}
    (parsed : Header.parse L data = .ok h) (layout : Layout.ofHeader h t = .ok (g,c))
    (init : initPrecincts L g = .ok (ps,base,spans)) : ∀ st ∈ ps, valid L st := by
  unfold initPrecincts at init
  simp only [Std.Legacy.Range.forIn_eq_forIn_range'] at init
  obtain ⟨s,loop,ok⟩ := ok_bind.mp init
  cases ok
  refine for_mem (fun (s : Array PrecState × Array (Array Nat) × Array (Array (Nat × Nat)) × Nat) =>
    ∀ st ∈ s.1, valid L st) _ _ ?_ _ _ (by simp) loop
  intro i mem b r hb hr
  have hi : i < g.numComps := by simpa [Std.Legacy.Range.size] using mem
  have bounds := (WideHeaderBounds.parsed_component_bounds parsed layout ⟨i,hi⟩ 0).1
  obtain ⟨s2,loop2,hr⟩ := ok_bind.mp hr
  cases hr
  refine Tier2Equiv.forIn_inv (fun (s : Array PrecState × Nat × Array Nat × Array (Nat × Nat)) =>
    ∀ st ∈ s.1, valid L st) _ ?_ _ _ _ hb loop2
  intro rr b2 r2 hb2 hr2
  obtain ⟨res,hs,hr2⟩ := ok_bind.mp hr2
  obtain ⟨_,_,hr2⟩ := ok_bind.mp hr2
  obtain ⟨s3,loop3,hr2⟩ := ok_bind.mp hr2
  cases hr2
  refine Tier2Equiv.forIn_inv (fun (s : Array PrecState × Nat) => ∀ st ∈ s.1, valid L st)
    _ ?_ _ _ _ hb2 loop3
  intro pp b3 r3 hb3 hr3
  obtain ⟨pg,hp,hr3⟩ := ok_bind.mp hr3
  obtain ⟨_,_,hr3⟩ := ok_bind.mp hr3
  obtain ⟨st,hst,hr3⟩ := ok_bind.mp hr3
  cases hr3
  intro x hx
  rcases Array.mem_push.mp hx with mem | rfl
  · exact hb3 x mem
  · exact fresh_valid bounds hs hp hst

open Tier2Equiv in
private theorem body_pres {g : GeometryBudget} {st cs body z} (h : Fits g st)
    (ok : readBody st cs body = .ok z) : Fits g z.1 := by
  rw [readBody_eq] at ok
  obtain ⟨a,hr,ok⟩ := ok_bind.mp ok
  cases ok
  refine forIn_inv (fun (s : Array BandState × Reader) => bandsFit g s.1) bodyBody ?_ _ (st.bands,body) _ h hr
  intro c s v hs hv
  unfold bodyBody at hv
  obtain ⟨⟨rs,b⟩,_,hv⟩ := ok_bind.mp hv
  dsimp only at hv
  split at hv <;> try contradiction
  rename_i bs hb
  split at hv <;> try contradiction
  cases hv
  apply set_pres hs
  have hb := hs _ (Array.mem_of_getElem? hb)
  simpa [fits] using hb

private theorem packet_pres {L : Limits} {sop eph seq layer st same hdr body z}
    (hs : valid L st) (ok : decodePacket L sop eph seq layer st same hdr body = .ok z) : valid L z.1 := by
  obtain ⟨st',info,h',b'⟩ := z
  have sz := congrArg Array.size (Tier2WF.decodePacket_shape ok)
  simp only [Array.size_map] at sz
  obtain ⟨_,_,nonEmpty,_,pre,cs,bits,_,_,_,_,bands,_,_,bodyOk,_⟩ := decodePacket_contributions ok
  refine ⟨by exact Nat.le_trans (Nat.le_of_eq sz) hs.1,body_pres (st := pre) ?_ bodyOk⟩
  cases nonEmpty
  · cases bands; exact hs.2
  · exact (headers_post hs.2 bands).1

/-- All precinct states retained by the packet iterator satisfy the checked geometry. -/
def StatesValid (L : Limits) (s : LoopState) := ∀ st ∈ s.precs, valid L st

private theorem step_pres {L : Limits} {c base same pb s p z}
    (hs : StatesValid L s) (ok : packetStep L c base same pb s p = .ok z) : StatesValid L z := by
  simp only [packetStep] at ok
  split at ok <;> try contradiction
  rename_i st sel
  simp only [ok_bind] at ok
  obtain ⟨⟨st',info,h',b'⟩,rd,_,_,ok⟩ := ok
  cases ok
  apply set_pres _ (packet_pres (hs _ (Array.mem_of_getElem? sel)) rd)
  apply set_pres hs
  exact ⟨by decide,by intro b hb; change b ∈ (#[] : Array BandState) at hb; simp at hb⟩


/-- Total pre-translation segment and range records retained by a tile's current precincts. -/
def tileRecords (s : LoopState) : Nat := slots (fun st => retained st.bands) s.precs

/-- Maximum additional retained records constructed in a single packet attempt. -/
def recordGrowth (L : Limits) : Nat := 2*(3*(L.maxCodeBlocks*(1+L.maxPassesPerCodeBlock)))

private theorem packet_records {L : Limits} {sop eph seq layer st same hdr body st' info hdr' body'}
    (hs : valid L st) (ok : decodePacket L sop eph seq layer st same hdr body = .ok (st',info,hdr',body')) :
    retained st'.bands ≤ retained st.bands + recordGrowth L := by
  obtain ⟨_,_,ne,_,pre,cs,_,_,_,_,_,head,_,_,bdy,_⟩ := decodePacket_contributions ok
  rw [Tier2Equiv.readBody_eq] at bdy
  obtain ⟨⟨bs,rd⟩,read,bdy⟩ := ok_bind.mp bdy
  cases bdy
  have bound := packet_prefix_storage hs.2 head (List.prefix_refl _) _ read
  exact Nat.le_trans bound (Nat.add_le_add_left (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right _ hs.1)) _)

private theorem step_records {L : Limits} {c base same pb s p z}
    (hs : StatesValid L s) (ok : packetStep L c base same pb s p = .ok z) :
    tileRecords z ≤ tileRecords s + recordGrowth L ∧ z.seq = s.seq+1 := by
  simp only [packetStep] at ok
  split at ok <;> try contradiction
  rename_i st sel
  simp only [ok_bind] at ok
  obtain ⟨⟨st',info,h',b'⟩,rd,_,_,ok⟩ := ok
  cases ok
  refine ⟨?_,rfl⟩
  unfold tileRecords
  dsimp only
  rw [Array.setIfInBounds_setIfInBounds]
  exact slots_set (fun st => retained st.bands) sel (packet_records (hs _ (Array.mem_of_getElem? sel)) rd)

private theorem initial_records {L : Limits} {g ps base spans} (init : initPrecincts L g = .ok (ps,base,spans))
    (buf : ByteArray) (hs : Option HeaderStream) : tileRecords (firstState ps buf hs) = 0 := by
  have zero {α : Type} (xs : Array α) (f : α → Nat) (h : ∀ x ∈ xs.toList, f x = 0) : slots f xs = 0 := by
    unfold slots
    have aux (ys : List α) (h : ∀ x ∈ ys, f x = 0) : (ys.map f).sum = 0 := by
      induction ys with
      | nil => rfl
      | cons y ys ih => simp [h y (by simp),ih (fun x hx => h x (by simp [hx]))]
    exact aux _ h
  apply zero ps
  intro p hp
  apply zero p.bands
  intro b hb
  apply zero b.blocks
  intro cb hc
  have fresh := (Tier2Equiv.initPrecincts_fresh init p hp b hb).2.2.2.2 cb hc
  have empty := congrArg CodeBlock.segments fresh
  simp [blockSlots,empty,segmentSlots]

private theorem prefix_records (L : Limits) (c base same pb) (pre : List Position) (s : LoopState)
    (hs : StatesValid L s) (start : tileRecords s ≤ s.seq * recordGrowth L) {t}
    (ok : pre.foldlM (dispatch (packetStep L c base same pb)) s = .ok t) :
    tileRecords t ≤ t.seq * recordGrowth L ∧ t.seq ≤ s.seq + pre.length := by
  induction pre generalizing s with
  | nil => cases ok; exact ⟨start,by simp⟩
  | cons x xs ih =>
    rw [List.foldlM_cons] at ok
    obtain ⟨z,hz,ok⟩ := ok_bind.mp ok
    unfold dispatch at hz
    split at hz
    · cases hz
      obtain ⟨rec,sz⟩ := ih _ hs start ok
      exact ⟨rec,by simp; omega⟩
    · obtain ⟨grow,step⟩ := step_records hs hz
      have new : tileRecords z ≤ z.seq * recordGrowth L := by rw [step,Nat.succ_mul]; omega
      obtain ⟨rec,sz⟩ := ih _ (step_pres hs hz) new ok
      exact ⟨rec,by simp; omega⟩

private theorem price_mono (L : Limits) (g : GeometryBudget) {n N l m : Nat}
    (hn : n ≤ N) (hl : l ≤ m) : packetBudget L g n l ≤ packetBudget L g N m := by
  have incl := Nat.mul_le_mul_left g.depth (show 1+(l+1) ≤ 1+(m+1) by omega)
  have block : blockBudget L l g.depth g.planes ≤ blockBudget L m g.depth g.planes := by
    unfold blockBudget; omega
  have bands := Nat.mul_le_mul hn (Nat.add_le_add_left (Nat.mul_le_mul_left g.blocks block) 1)
  have body := Nat.mul_le_mul_left 5 (Nat.mul_le_mul_right (g.blocks*(1+L.maxPassesPerCodeBlock)) hn)
  unfold packetBudget; omega

/-- Uniform per-attempt charge on a public packet prefix. Two units cover precinct
selection and the cumulative check. The check runs after all packet construction. -/
def attemptBudget (L : Limits) : Nat := 1 + (packetBudget L (checkedGeometry L) 3 L.maxPackets + 1)

/-- Measure the complete callback, including an index failure or a refused pass proposal. -/
def attempt (L : Limits) (c : Coding) (base : Array (Array Nat)) (same : Bool)
    (pb : Nat) (s : LoopState) (p : PacketId) (hs : StatesValid L s) (hl : p.layer ≤ L.maxPackets) :
    Counted (packetStep L c base same pb s p) (attemptBudget L) := by
  simp only [packetStep]
  split
  · rename_i st sel
    have valid := hs _ (Array.mem_of_getElem? sel)
    refine tick (chain (widen (packet L (checkedGeometry L) c.sop c.eph s.seq p.layer st same
      s.hdr s.body valid.2) (price_mono _ _ valid.1 hl)) (m := 1) ?_)
    exact fun _ _ => pay _ 1
  · exact widen (pay _ 1) (by unfold attemptBudget; omega)

private theorem layer_schedule (g : Layout) (wf : g.WF) (prev vs : List Volume) (p : Position)
    (mem : p ∈ schedule g prev vs) : p.packet.layer ≤ (schedule g prev vs).length := by
  induction vs generalizing prev with
  | nil => cases mem
  | cons v vs ih =>
    simp only [schedule,List.mem_append,List.mem_map] at mem
    simp only [schedule,List.length_append,List.length_map]
    rcases mem with ⟨q,hq,rfl⟩ | tail
    · let seq := Spec.Progression.volume g v
      have h := ((Spec.Progression.c5_volume wf v).2 q).1 hq
      have sub : List.range q.layer ⊆ seq.map PacketId.layer := by
        intro i hi
        have lt := List.mem_range.mp hi
        refine List.mem_map.mpr ⟨{q with layer := i}, ((Spec.Progression.c5_volume wf v).2 _).2
          ⟨⟨by exact Nat.lt_trans lt h.1.1,h.1.2⟩,by exact ⟨Nat.lt_trans lt h.2.1,h.2.2⟩⟩, rfl⟩
      have sz := List.nodup_range.length_le_of_subset sub
      simp only [List.length_range,List.length_map] at sz
      dsimp only [seq] at sz; exact Nat.le_trans sz (by omega)
    · exact Nat.le_trans (ih _ tail) (by omega)

/-- Decoding a particular observed callback has the indicated outcome. -/
def agrees (s : LoopState) (a : PacketAction) (r : Except Error LoopState) : Prop :=
  match a,r with
  | .rejected,.error _ => True
  | .accepted n,.ok t => t.passes - s.passes = n
  | _,_ => False

private theorem walk_hit (f : LoopState → PacketId → Except Error LoopState) (ps : List Position)
    (s : LoopState) {p a} (attempted : a.attempted = true) (hit : (p,a) ∈ (PacketTraversal.walk f ps s).1) :
    ∃ pre tail reached, ps = pre ++ p :: tail ∧ pre.foldlM (dispatch f) s = .ok reached ∧
      p.previous.any (·.contains p.packet) = false ∧ agrees reached a (f reached p.packet) := by
  induction ps generalizing s with
  | nil => cases hit
  | cons q qs ih =>
    simp only [PacketTraversal.walk] at hit
    split at hit
    · rename_i skipped
      change (p,a) ∈ (q,.skip)::(PacketTraversal.walk f qs s).1 at hit
      rcases List.mem_cons.mp hit with eq | mem
      · cases eq; cases attempted
      · obtain ⟨pre,tail,t,ids,run,fresh,ok⟩ := ih s mem
        exact ⟨q::pre,tail,t,by simp [ids],by simpa [dispatch,skipped] using run,fresh,ok⟩
    · rename_i fresh
      cases step : f s q.packet with
      | error e =>
        simp only [step,List.mem_singleton,Prod.mk.injEq] at hit
        obtain ⟨rfl,rfl⟩ := hit
        exact ⟨[],qs,s,rfl,rfl,by simpa using fresh,by simp [agrees,step]⟩
      | ok t =>
        rw [step] at hit
        change (p,a) ∈ (q,.accepted (t.passes-s.passes))::(PacketTraversal.walk f qs t).1 at hit
        rcases List.mem_cons.mp hit with eq | mem
        · cases eq; exact ⟨[],qs,s,rfl,rfl,by simpa using fresh,by simp [agrees,step]⟩
        · obtain ⟨pre,tail,z,ids,run,first,ok⟩ := ih t mem
          exact ⟨q::pre,tail,z,by simp [ids],by simpa [dispatch,fresh,step,bind,Except.bind] using run,first,ok⟩

private theorem prefix_valid (L : Limits) (c base same pb) (pre : List Position) (s : LoopState)
    (hs : StatesValid L s) {t} (ok : pre.foldlM (dispatch (packetStep L c base same pb)) s = .ok t) :
    StatesValid L t := by
  induction pre generalizing s with
  | nil => cases ok; exact hs
  | cons x xs ih =>
    rw [List.foldlM_cons] at ok
    obtain ⟨z,hz,ok⟩ := ok_bind.mp ok
    refine ih z ?_ ok
    unfold dispatch at hz
    split at hz
    · cases hz; exact hs
    · exact step_pres hs hz

open Tier2Equiv in
private theorem prefix_buffers (L : Limits) (c : Coding) (base : Array (Array Nat)) (pb : Nat)
    (buf : ByteArray) (hs : Option ByteArray) (pre : List Position) (s t : LoopState)
    (start : ∃ l, LRel buf hs s l)
    (run : pre.foldlM (dispatch (packetStep L c base hs.isNone pb)) s = .ok t) :
    t.body.data = buf ∧ t.body.stop = buf.size ∧
      ∀ hb, hs = some hb → t.hdr.data = hb ∧ t.hdr.stop = hb.size := by
  induction pre generalizing s with
  | nil => cases run; obtain ⟨l,_,_,_,hd,hb,_,_,hh⟩ := start; exact ⟨hd,hb,hh⟩
  | cons p ps ih =>
    rw [List.foldlM_cons] at run
    obtain ⟨a,step,run⟩ := ok_bind.mp run
    apply ih a _ run
    unfold dispatch at step
    split at step
    · cases step; exact start
    · obtain ⟨l,rel⟩ := start
      have sim := step_sim buf hs L c.sop c.eph base pb s l rel p.packet
      change fastStep L c.sop c.eph hs.isNone base pb s p.packet = .ok a at step
      rw [step] at sim
      cases out : Spec.Tier2.step L c.sop c.eph hs.isNone base pb l p.packet with
      | error => rw [out] at sim; contradiction
      | ok z => rw [out] at sim; exact ⟨z,sim⟩

open Tier2Equiv in
private theorem first_buffers {L : Limits} {g ps base spans} (init : initPrecincts L g = .ok (ps,base,spans))
    (buf : ByteArray) (hs : Option HeaderStream) : ∃ l, LRel buf (hs.map (·.bytes)) (firstState ps buf hs) l := by
  let br := Reader.ofByteArray buf .tier2
  let s := firstState ps buf hs
  refine ⟨{precs := ps.toList.map Spec.Tier2.PrecSt.ofFast, hdr := rbytes s.hdr, body := rbytes br},
    fun j => ?_,rfl,rfl,rfl,rfl,rfl,rfl,?_⟩
  · rw [List.getElem?_map,Array.getElem?_toList]
    change ORel _ ps[j]? _
    cases h : ps[j]? with
    | none => trivial
    | some p => exact fresh_rel buf p (initPrecincts_fresh init p (by simpa using Array.mem_of_getElem? h))
  · intro hb eq
    cases hs with
    | none => cases eq
    | some b => cases eq; exact ⟨rfl,rfl⟩

/-- The production layout, readers, initial state and physical prefix that reached
this callback. The bound is attached to the measured callback at that precise
state. Both a failed local read and a refused cumulative proposal are included. -/
def Observed (L : Limits) (h : Header) (data : ByteArray) (tp : TileParams)
    (hs : Option HeaderStream) (pb : Nat) (p : Position) (a : PacketAction) : Prop :=
  ∃ g c precs base spans buf parts pre tail reached,
    Layout.ofHeader h tp.index = .ok (g,c) ∧ initPrecincts L g = .ok (precs,base,spans) ∧
    tileData data tp.tile = .ok (buf,parts) ∧ buf.size ≤ tp.tile.parts.size * data.size ∧
    schedule g [] (volumes g c.progression c.poc) = pre ++ p :: tail ∧
    let f := packetStep L c base (hs.map (·.bytes)).isNone pb
    pre.foldlM (dispatch f) (firstState precs buf hs) = .ok reached ∧
    p.previous.any (·.contains p.packet) = false ∧
    tileRecords reached ≤ reached.seq * recordGrowth L ∧ reached.seq < L.maxPackets ∧
    reached.body.data = buf ∧ reached.body.stop = buf.size ∧
    (∀ b, hs = some b → reached.hdr.data = b.bytes ∧ reached.hdr.stop = b.bytes.size) ∧
    ∃ hv : StatesValid L reached, ∃ hl : p.packet.layer ≤ L.maxPackets,
      let m := attempt L c base (hs.map (·.bytes)).isNone pb reached p.packet hv hl
      agrees reached a m.result ∧ m.result = f reached p.packet ∧ m.work ≤ attemptBudget L

/-- Every actual attempted callback in a parsed tile's prefix carries its local bound,
including the last callback on error. A duplicate physical visit has no callback. -/
theorem stream_attempt {L : Limits} {h : Header} {data : ByteArray} {tp : TileParams}
    {hs : Option HeaderStream} {pb p a} (parsed : Header.parse L data = .ok h)
    (entered : a.attempted = true) (hit : (p,a) ∈ (measureStream L h data tp hs pb).1) :
    Observed L h data tp hs pb p a := by
  unfold measureStream at hit
  cases layout : Layout.ofHeader h tp.index with
  | error => simp [layout,before] at hit
  | ok pair =>
    obtain ⟨g,c⟩ := pair
    simp only [layout,before] at hit
    cases quota : L.check JPEG2000.Tier2.Packet.loc .packets (iterationWork g c.progression c.poc) with
    | error => simp [quota] at hit
    | ok u =>
      simp only [quota] at hit
      cases init : initPrecincts L g with
      | error => simp [init] at hit
      | ok pair =>
        obtain ⟨ps,base,spans⟩ := pair
        simp only [init] at hit
        cases input : tileData data tp.tile with
        | error => simp [input] at hit
        | ok pair =>
          obtain ⟨buf,parts⟩ := pair
          simp only [input,afterRun] at hit
          obtain ⟨pre,tail,t,ids,run,fresh,ok⟩ := walk_hit _ _ _ entered hit
          have wf := Tier2Equiv.ofHeader_wf (Equiv.parse_dxdy parsed) layout
          let sched := schedule g [] (volumes g c.progression c.poc)
          have mem : p ∈ sched := by simp [sched,ids]
          have ly := layer_schedule g wf [] _ p mem
          have cap : iterationWork g c.progression c.poc ≤ L.maxPackets := (Limits.check_eq_ok_iff ..).1 quota
          have charged := visits_tests_le_charge sched
          rw [show charge sched = iterationWork g c.progression c.poc from schedule_charge g wf ..] at charged
          have hl : p.packet.layer ≤ L.maxPackets := by change p.packet.layer ≤ sched.length at ly; omega
          have hv := prefix_valid L _ _ _ _ pre _ (initial_valid parsed layout init) run
          have initial : tileRecords (firstState ps buf hs) ≤ (firstState ps buf hs).seq * recordGrowth L := by
            rw [initial_records init]; exact Nat.zero_le _
          obtain ⟨records,count⟩ := prefix_records L _ _ _ _ pre _ (initial_valid parsed layout init) initial run
          have beforeCap : t.seq < L.maxPackets := by
            change t.seq ≤ 0+pre.length at count
            change sched.length + _ ≤ _ at charged
            have len : sched.length = pre.length+1+tail.length := by simp [sched,ids]; omega
            omega
          obtain ⟨dataEq,stopEq,packed⟩ := prefix_buffers L c base pb buf _ pre _ t (first_buffers init buf hs) run
          exact ⟨g,c,ps,base,spans,buf,parts,pre,tail,t,layout,init,input,
            ((HeaderWork.tileData_copy_charge data tp.tile).2.2 buf parts input).1,ids,run,fresh,records,beforeCap,dataEq,stopEq,(fun b eq => packed b.bytes (by rw [eq]; rfl)),hv,hl,
            by rwa [(attempt ..).erase],(attempt ..).erase,(attempt ..).within⟩


/-- Initial buffer extents at a public callback. The tile and packed-header buffers
are produced by the separate gather operations measured by HeaderWork. -/
def packedCap (L : Limits) (n : Nat) (hs : HeaderStream) : Nat :=
  (if hs.fromPpm then L.maxTilePartsPerTile * (L.maxTileParts * n)
   else L.maxTilePartsPerTile * (n+1)) * n

private theorem sourced_attempt {L : Limits} {data : ByteArray} {h : Header} {v : TileVisit} {p a}
    (parsed : Header.parse L data = .ok h) (source : Sourced L h data v)
    (entered : a.attempted = true) (hit : (p,a) ∈ v.packets) :
    ∃ tp hs, presentAt h v.tile v.cursor = some tp ∧ tp.tile.parts.size ≤ L.maxTilePartsPerTile ∧
      (∀ b, hs = some b → b.bytes.size ≤ packedCap L data.size b) ∧
      Observed L h data tp hs v.passesBefore p a := by
  obtain ⟨idx,_,src⟩ := source
  rw [src] at hit
  cases sel : presentAt h v.tile v.cursor with
  | none => simp [sel] at hit
  | some tp =>
    have member : tp ∈ h.tiles := by
      unfold presentAt at sel
      split at sel <;> try contradiction
      split at sel <;> cases sel
      exact Array.mem_of_getElem? (by assumption)
    simp only [sel] at hit
    cases got : headerStreamAt h data tp (idx.getD v.cursor #[]) with
    | error => rw [got] at hit; cases hit
    | ok hs =>
      simp only [got] at hit
      refine ⟨tp,hs,rfl,(HeaderWork.parse_tile_storage parsed tp member).1,?_,stream_attempt parsed entered hit⟩
      rintro b rfl
      exact (HeaderWork.parsed_headerStream parsed member got).2

private theorem trace_source {L : Limits} {h : Header} {data : ByteArray} {t j pb vs v}
    (tr : Trace L h data t j pb vs) (mem : v ∈ vs) : Sourced L h data v := by
  induction tr with
  | stop => cases mem
  | next hv _ ih =>
    rcases List.mem_cons.mp mem with rfl | tail
    · exact hv.source
    · exact ih tail

/-- The ordinary byte API, including rejected prefixes. Every attempted event has a
certified local execution on its actual incoming readers and precinct state. Multiplying
the per-call reservation by actual attempts charges no skipped position. -/
theorem decode_attempts (L : Limits) (data : ByteArray) (reduce : Nat) :
    let m := PublicPacketWork.measure L data reduce
    m.2 = decodeCodestream L data reduce ∧
    imageAttempts m.1 * attemptBudget L ≤ L.maxTiles*L.maxPackets*attemptBudget L ∧
    ∀ v ∈ m.1, ∀ p a, (p,a) ∈ v.packets → a.attempted = true →
      ∃ h tp hs, Header.parse L data = .ok h ∧ presentAt h v.tile v.cursor = some tp ∧
        tp.tile.parts.size ≤ L.maxTilePartsPerTile ∧
        (∀ b, hs = some b → b.bytes.size ≤ packedCap L data.size b) ∧
        Observed L h data tp hs v.passesBefore p a := by
  obtain ⟨er,_,calls,positions,charge,_⟩ := PublicPacketWork.decode_packet_work L data reduce
  refine ⟨er,Nat.mul_le_mul_right _ (by omega),?_⟩
  unfold PublicPacketWork.measure
  cases admission : PublicPacketWork.prepareTiles L data reduce with
  | error => simp [before]
  | ok pair =>
    unfold PublicPacketWork.prepareTiles at admission
    obtain ⟨_,_,tail⟩ := Tier2Equiv.bind_ok admission
    obtain ⟨h,parsed,tail⟩ := Tier2Equiv.bind_ok tail
    obtain ⟨initial,_,ret⟩ := Tier2Equiv.bind_ok tail
    cases ret
    simp only [before,measureTiles_finish,afterRun]
    intro v mem p a hit entered
    have trace := (measureGrid_trace parsed initial (JPEG2000.Decode.centeredTile L h data reduce)
      (·.saturated) (fun dst t => JPEG2000.NativeOutput.writeTile L h.siz reduce t.layout t.coding dst t.sources)).1
    obtain ⟨tp,hs,sel,parts,packed,obs⟩ := sourced_attempt parsed (trace_source trace mem) entered hit
    exact ⟨h,tp,hs,parsed,sel,parts,packed,obs⟩


/-! ## Position-driven progression preparation (B.12.1.3–5)

Lean's pinned compiler rewrites List.mergeSort to mergeSortTR₂. The two
mutually recursive directions split at different halves and swap the reversed
half. The counter below follows those branches and the real merge comparator.
-/

/-- Component/resolution loop visits plus the component scans needed to clamp each
resolution range when preparing precinct references, including empty volumes. -/
def gridSetup (g : Layout) (v : Volume) : Nat :=
  1 + (v.ce g-v.compStart)*(1+3*g.numComps+(v.re g-v.resStart))

/-- Count position-table setup. The linear terms charge the precinct range, reference,
five key cells, key pair, tagging and final projection. Sorting counts split-list
visits, comparisons, accumulator reversal and calls of the pinned runtime sorter. -/
def positionTable (g : Layout) (v : Volume) : List PrecRef × Nat :=
  let refs := precRefs g v
  let tagged := refs.map fun p => (posKey g v.order p,p)
  let s := PacketSortWork.measured (fun (a b : List Nat × PrecRef) => decide (a.1 ≤ b.1)) tagged
  (s.1.map (·.2), gridSetup g v + 10*refs.length + tagged.length + s.2)

/-- The key of every prepared precinct has five entries and the observed table is
exactly the one used by production, even at zero layers. The quadratic bound on
the halving recurrence is conservative. A comparison of keys sees at most five
pairs of coordinates. -/
theorem positionTable_work (g : Layout) (v : Volume) :
    let n := (precRefs g v).length
    let m := positionTable g v
    m.1 = sortedPrecincts g v ∧ m.1.length = n ∧
      (∀ p, (posKey g v.order p).length = 5) ∧ m.2 ≤ gridSetup g v + 11*n + 8*(n*n)+1 := by
  let tagged := (precRefs g v).map fun p => (posKey g v.order p,p)
  let s := PacketSortWork.measured (fun (a b : List Nat × PrecRef) => decide (a.1 ≤ b.1)) tagged
  have hlen : tagged.length = (precRefs g v).length := List.length_map _
  have he : s.1 = tagged.mergeSort (fun a b => decide (a.1 ≤ b.1)) := by
    exact (PacketSortWork.sort_work _ _).1
  refine ⟨congrArg (List.map Prod.snd) he,?_,fun p => ?_,?_⟩
  · change (s.1.map Prod.snd).length = _
    rw [List.length_map,he,List.length_mergeSort,hlen]
  · cases v.order <;> rfl
  · change gridSetup g v + 10*(precRefs g v).length + tagged.length + s.2 ≤ _
    have bound : tagged.length + s.2 ≤ tagged.length + 8*(tagged.length*tagged.length)+1 := (PacketSortWork.sort_work _ _).2
    rw [hlen] at *
    omega


private def rangeSetup {α : Type} (f : α → Nat → Except Error α) (cap : Nat)
    (step : ∀ b i, Counted (f b i) cap) (i n : Nat) (b : α) :
    Counted (forRange i n f b) (n*(1+cap)) := by
  induction n generalizing i b with
  | zero => exact widen (pay _ 0) (by simp)
  | succ n ih =>
    unfold forRange
    exact widen (chain (tick (step b i)) (fun a _ => ih (i+1) a)) (by rw [Nat.succ_mul]; omega)

private def reserve {α : Type} {x : Except Error α} {n : Nat} (over : Nat) (a : Counted x n) :
    Counted x (over+n) := ⟨a.result,over+a.work,a.erase,Nat.add_le_add_left a.within over⟩

/-- Setup budget for a single progression volume, independent of its emitted packets.
A maxLevels evaluation scans the component table (toList, map and fold).
Layer/resolution orders launch an innermost iterator even when the precinct count is zero.
Position orders build their entire sorted table even when the layer count is zero. -/
def volumeBudget (g : Layout) (v : Volume) : Nat :=
  let l := v.le g
  let r := v.re g - v.resStart
  let c := v.ce g - v.compStart
  let scan := 3*g.numComps
  match v.order with
  | .lrcp => 1+l*(1+(scan+r*(1+c*(1+0))))
  | .rlcp => 1+scan+r*(1+l*(1+c*(1+0)))
  | _ =>
    let n := (precRefs g v).length
    gridSetup g v + 11*n + 8*(n*n)+1 + n

private def listSetup {α β : Type} (f : β → α → Except Error β) : (xs : List α) → (b : β) → Counted (xs.foldlM f b) xs.length
  | [], _ => pay _ 0
  | x::xs, b => by
    rw [List.foldlM_cons]
    exact widen (chain (pay (f b x) 1) (fun y _ => listSetup f xs y)) (by simp [Nat.add_comm])

/-- Replays progression-specific setup of the actual monadic iteration. Every
innermost range is delegated to the original callback loop. Its physical visits
and membership tests are already charged by PacketTraversal. -/
def volumeSetup {α : Type} (g : Layout) (v : Volume) (f : α → PacketId → Except Error α) (b : α) :
    Counted (forVolume g v f b) (volumeBudget g v) := by
  simp only [forVolume, volumeBudget]
  cases v.order with
  | lrcp =>
    unfold forLRCP
    refine tick (rangeSetup _ _ (fun a l => reserve (3*g.numComps) (rangeSetup _ _ (fun a r =>
      rangeSetup _ _ (fun _ _ => pay _ 0) _ _ a) _ _ a)) _ _ b)
  | rlcp =>
    unfold forRLCP
    refine reserve (1+3*g.numComps) (rangeSetup _ _ (fun a r => rangeSetup _ _
      (fun a l => rangeSetup _ _ (fun _ _ => pay _ 0) _ _ a) _ _ a) _ _ b)
  | rpcl | pcrl | cprl =>
    unfold forPosition
    rw [← (positionTable_work g v).1]
    let table := positionTable g v
    refine widen (reserve table.2 (listSetup _ table.1 b)) ?_
    obtain ⟨_,sz,_,cap⟩ := positionTable_work g v
    change table.1.length = _ at sz
    change table.2 ≤ _ at cap
    exact Nat.add_le_add cap (Nat.le_of_eq sz)

/-- Sum of setup reservations, including the cost of appending each visited volume to the previous list. -/
def setupRest (g : Layout) (previous : Nat) : List Volume → Nat
  | [] => 0
  | v::vs => 1+volumeBudget g v + (previous+1) + setupRest g (previous+1) vs

private def volumesSetup {α : Type} (g : Layout) (prev : List Volume) : (vs : List Volume) →
    (f : α → PacketId → Except Error α) → (b : α) →
    Counted (forVolumes g prev vs f b) (setupRest g prev.length vs)
  | [], _, _ => pay _ 0
  | v::vs, f, b => by
    simp only [forVolumes,setupRest]
    let run := volumeSetup g v (fun a p => if prev.any (·.contains p) then pure a else f a p) b
    refine widen (chain (tick run) (m := (prev.length+1)+setupRest g (prev.length+1) vs) ?_) (by omega)
    intro b' _
    refine reserve (prev.length+1) ?_
    simpa using volumesSetup g (prev++[v]) vs f b'

/-- Setup across all five orders and all POC volumes, with the real failure prefix.
In particular even an empty earlier volume costs a visit and a previous-list append.
The initial conversion of POC records, or maxLevels on the default full volume, is
charged separately from physical packet visits. -/
def progressionSetup {α : Type} (g : Layout) (o : Marker.Progression) (poc : Array Marker.PocEntry)
    (f : α → PacketId → Except Error α) (b : α) :
    Counted (forPackets g o poc f b)
      ((1+2*poc.size+3*g.numComps)+setupRest g 0 (volumes g o poc)) :=
  reserve _ (volumesSetup g [] _ f b)

/-- Equality at the streaming entry point and a structural setup price independent
of callback success. The full-volume sum reserves every possible attempted volume. -/
theorem progression_work {α : Type} (g : Layout) (o : Marker.Progression) (poc : Array Marker.PocEntry)
    (f : α → PacketId → Except Error α) (b : α) :
    let s := progressionSetup g o poc f b
    s.result = forPackets g o poc f b ∧
    s.work ≤ (1+2*poc.size+3*g.numComps)+setupRest g 0 (volumes g o poc) :=
  ⟨(progressionSetup ..).erase,(progressionSetup ..).within⟩


private theorem for_visited {α β : Type} (f : α → β → Except Error (ForInStep β))
    (yielding : ∀ x s y, f x s ≠ .ok (.done y)) (xs : List α) (s t : β)
    (ok : forIn xs s f = .ok t) {x} (mem : x ∈ xs) : ∃ s' t', f x s' = .ok (.yield t') := by
  induction xs generalizing s with
  | nil => cases mem
  | cons y ys ih =>
    rw [List.forIn_cons] at ok
    obtain ⟨step,here,ok⟩ := ok_bind.mp ok
    cases step with
    | done => exact False.elim (yielding _ _ _ here)
    | yield z =>
      rcases List.mem_cons.mp mem with rfl | tail
      · exact ⟨s,z,here⟩
      · exact ih z ok tail

open JPEG2000.Tier2.Geometry in
private theorem prec_limit {L : Limits} {g : Layout} {ps base spans}
    (init : initPrecincts L g = .ok (ps,base,spans)) {i : Nat} (hi : i < g.numComps) (r : Nat) :
    g.numPrecincts i r ≤ L.maxPrecincts := by
  unfold Layout.numPrecincts
  split <;> try exact Nat.zero_le _
  rename_i hr
  unfold initPrecincts at init
  simp only [Std.Legacy.Range.forIn_eq_forIn_range'] at init
  obtain ⟨s,loop,_⟩ := ok_bind.mp init
  have sizeRange (n : Nat) : [:n].size = n := by simp [Std.Legacy.Range.size]
  simp only [sizeRange] at loop
  obtain ⟨_,_,hit⟩ := for_visited _ (by
    intro x s y bad
    obtain ⟨_,_,bad⟩ := ok_bind.mp bad
    cases bad) _ _ _ loop (by simpa using hi)
  obtain ⟨_,inner,_⟩ := ok_bind.mp hit
  obtain ⟨_,_,hit⟩ := for_visited _ (by
    intro x s y bad
    simp only [ok_bind] at bad
    obtain ⟨_,_,_,_,_,_,bad⟩ := bad
    cases bad) _ _ _ inner (x := r) (by simpa [Layout.levels] using Nat.lt_succ_of_le hr)
  obtain ⟨res,read,_⟩ := ok_bind.mp hit
  unfold resolution at read
  dsimp only at read
  split at read <;> try contradiction
  obtain ⟨_,check,_⟩ := ok_bind.mp read
  exact (Limits.check_eq_ok_iff ..).1 check

private theorem sum_le {α : Type} (xs : List α) (f : α → Nat) (cap : Nat)
    (h : ∀ x ∈ xs, f x ≤ cap) : (xs.map f).sum ≤ xs.length*cap := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.succ_mul]; omega

private theorem parsed_levels {L : Limits} {data : ByteArray} {h : Header} {t g c}
    (parsed : Header.parse L data = .ok h) (layout : Layout.ofHeader h t = .ok (g,c)) :
    g.maxLevels ≤ L.maxDecompLevels := by
  obtain ⟨_,levels⟩ := HeaderWork.layout_budget parsed layout
  unfold Layout.maxLevels
  have fold (xs : List Nat) (h : ∀ n ∈ xs, n ≤ L.maxDecompLevels) : xs.foldr max 0 ≤ L.maxDecompLevels := by
    induction xs with
    | nil => exact Nat.zero_le _
    | cons x xs ih => exact Nat.max_le.mpr ⟨h _ (by simp),ih (fun y hy => h y (by simp [hy]))⟩
  apply fold
  intro n mem
  obtain ⟨tc,htc,rfl⟩ := List.mem_map.mp mem
  have hm : tc ∈ g.comps := by simpa using htc
  obtain ⟨i,hi,eq⟩ := Array.mem_iff_getElem.mp hm
  subst tc
  have cap := levels ⟨i,hi⟩
  simpa [Layout.comp,Array.getD_eq_getD_getElem?,Array.getElem?_eq_getElem hi,Tier2.Geometry.TileCompGeom.numResolutions]
    using cap

/-- Number of precincts in a prepared position table, independently of packet count.
Zero-layer volumes still build a table. Initialization checked each resolution's
count and parsing checked both outer dimensions. -/
theorem table_limit {L : Limits} {data : ByteArray} {h : Header} {t g c ps base spans}
    (parsed : Header.parse L data = .ok h) (layout : Layout.ofHeader h t = .ok (g,c))
    (init : initPrecincts L g = .ok (ps,base,spans)) (v : Volume) :
    (precRefs g v).length ≤ L.maxComponents*((L.maxDecompLevels+1)*L.maxPrecincts) := by
  have hc : v.ce g - v.compStart ≤ L.maxComponents := by
    have := (HeaderWork.layout_budget parsed layout).1; unfold Volume.ce; omega
  have hr : v.re g - v.resStart ≤ L.maxDecompLevels+1 := by
    have := parsed_levels parsed layout; unfold Volume.re; omega
  simp only [precRefs,List.length_flatMap,List.length_map,List.length_range]
  apply Nat.le_trans (sum_le _ _ ((L.maxDecompLevels+1)*L.maxPrecincts) ?_)
  · exact Nat.mul_le_mul_right _ (by simpa using hc)
  intro i hi
  apply Nat.le_trans (sum_le _ _ L.maxPrecincts ?_)
  · exact Nat.mul_le_mul_right _ (by simpa using hr)
  intro r _
  apply prec_limit init _ r
  simp only [List.mem_range'_1,Volume.ce] at hi
  omega

private theorem sum_volumes (g : Layout) (vs : List Volume) (j cap : Nat)
    (bounded : ∀ v ∈ vs, volumeBudget g v ≤ cap) :
    setupRest g j vs ≤ vs.length*(2+cap+(j+vs.length)) := by
  induction vs generalizing j with
  | nil => simp [setupRest]
  | cons v vs ih =>
    have hv := bounded v (by simp)
    have ht := ih (j+1) (fun x hx => bounded x (by simp [hx]))
    simp only [setupRest,List.length_cons,Nat.succ_mul]
    rw [show j+1+vs.length = j+(vs.length+1) by omega] at ht
    omega

/-- A single layout-wide price for all orders (including empty volumes).
The remaining parameters are the effective layer count and number of POC entries.
The precinct table term is independent of both. -/
def setupLimit (L : Limits) (layers entries : Nat) : Nat :=
  let c := L.maxComponents
  let r := L.maxDecompLevels+1
  let n := c*(r*L.maxPrecincts)
  let v := 1+layers*(1+(3*c+r*(1+c))) + (1+3*c+r*(1+layers*(1+c))) +
    (1+c*(1+3*c+r) + 12*n + 8*(n*n)+1)
  let m := entries+1
  (1+2*entries+3*c) + m*(2+v+m)

/-- Uniform progression setup bound after the actual initialization, even if the
callback fails at the first position or no volume emits any positions. -/
theorem parsed_setup {α : Type} {L : Limits} {h : Header} {data : ByteArray} {t g c ps base spans}
    (parsed : Header.parse L data = .ok h) (layout : Layout.ofHeader h t = .ok (g,c))
    (init : initPrecincts L g = .ok (ps,base,spans))
    (f : α → PacketId → Except Error α) (b : α) :
    (progressionSetup g c.progression c.poc f b).work ≤ setupLimit L L.maxLayers L.maxPocEntries := by
  let C := L.maxComponents
  let R := L.maxDecompLevels+1
  let N := C*(R*L.maxPrecincts)
  let top := 1+L.maxLayers*(1+(3*C+R*(1+C))) + (1+3*C+R*(1+L.maxLayers*(1+C))) +
    (1+C*(1+3*C+R) + 12*N + 8*(N*N)+1)
  let vs := volumes g c.progression c.poc
  have hc : g.numComps ≤ C := (HeaderWork.layout_budget parsed layout).1
  obtain ⟨layers,entries⟩ := ProgressionFields.parsed_limits parsed layout
  have size : vs.length ≤ L.maxPocEntries+1 := by
    unfold vs volumes; split <;> simp <;> omega
  have per (v : Volume) : volumeBudget g v ≤ top := by
    have cc : v.ce g - v.compStart ≤ C := by unfold Volume.ce; omega
    have rr : v.re g - v.resStart ≤ R := by
      have cap := parsed_levels parsed layout; unfold Volume.re R; omega
    have ll : v.le g ≤ L.maxLayers := Nat.le_trans (Nat.min_le_right ..) layers
    have nn : (precRefs g v).length ≤ N := table_limit parsed layout init v
    have scan := Nat.mul_le_mul_left 3 hc
    have gr := Nat.mul_le_mul cc (show 1+3*g.numComps+(v.re g-v.resStart) ≤ 1+3*C+R by omega)
    have cr := Nat.mul_le_mul rr (show 1+(v.ce g-v.compStart) ≤ 1+C by omega)
    have lr := Nat.mul_le_mul ll (show 1+(v.ce g-v.compStart) ≤ 1+C by omega)
    have left := Nat.mul_le_mul ll (Nat.add_le_add_left (Nat.add_le_add scan cr) 1)
    have right := Nat.mul_le_mul rr (Nat.add_le_add_left lr 1)
    have sq := Nat.mul_le_mul nn nn
    unfold volumeBudget gridSetup top
    cases v.order <;> simp only [Nat.add_zero,Nat.mul_one] <;> omega
  have sum := sum_volumes g vs 0 top (fun v _ => per v)
  have product := Nat.mul_le_mul size (show 2+top+(0+vs.length) ≤ 2+top+(L.maxPocEntries+1) by omega)
  apply Nat.le_trans (progressionSetup g c.progression c.poc f b).within
  change 1+2*c.poc.size+3*g.numComps+setupRest g 0 vs ≤ (1+2*L.maxPocEntries+3*C)+(L.maxPocEntries+1)*(2+top+(L.maxPocEntries+1))
  omega


/-- Preparation of iterationWork precedes the packet-budget check and precinct
initialization. Each component/resolution pair evaluates numPrecincts once. The
remaining terms cover conversion, construction and traversal of the finite lists
and rescanning the layout to clamp resolution ends. -/
def preflight (g : Layout) (o : Marker.Progression) (poc : Array Marker.PocEntry) : Nat × Nat :=
  let vs := volumes g o poc
  let counts := vs.zipIdx.map fun (v,j) =>
    let cs := List.range' v.compStart (v.ce g - v.compStart)
    let rs := List.range' v.resStart (v.re g - v.resStart)
    let n := cs.foldl (fun a i => rs.foldl (fun a r => a + g.numPrecincts i r) a) 0
    ((j+1) * v.le g * n, 4 + cs.length * (3 + 3*g.numComps + 2*rs.length))
  ((counts.map Prod.fst).foldl (·+·) 0, 1+2*poc.size+3*g.numComps+(counts.map Prod.snd).sum)

/-- The actual preflight price does not depend on any later successful check.
This applies to parsed layouts that are rejected before a single callback runs. -/
theorem preflight_work {L : Limits} {h : Header} {data : ByteArray} {t g c}
    (parsed : Header.parse L data = .ok h) (layout : Layout.ofHeader h t = .ok (g,c)) :
    (preflight g c.progression c.poc).1 = iterationWork g c.progression c.poc ∧
    (preflight g c.progression c.poc).2 ≤
      1+2*L.maxPocEntries+3*L.maxComponents + (L.maxPocEntries+1)*
        (4+L.maxComponents*(3+3*L.maxComponents+2*(L.maxDecompLevels+1))) := by
  constructor
  · simp [preflight,iterationWork,List.map_map,Function.comp_def]
  · let vs := volumes g c.progression c.poc
    have hc := (HeaderWork.layout_budget parsed layout).1
    have hr := parsed_levels parsed layout
    have entries := (ProgressionFields.parsed_limits parsed layout).2
    have size : vs.length ≤ L.maxPocEntries+1 := by unfold vs volumes; split <;> simp <;> omega
    let w := fun (p : Volume × Nat) =>
      4+(p.1.ce g-p.1.compStart)*(3+3*g.numComps+2*(p.1.re g-p.1.resStart))
    let cap := 4+L.maxComponents*(3+3*L.maxComponents+2*(L.maxDecompLevels+1))
    have each (p : Volume × Nat) : w p ≤ cap := by
      have C : p.1.ce g - p.1.compStart ≤ L.maxComponents := by unfold Volume.ce; omega
      have R : p.1.re g - p.1.resStart ≤ L.maxDecompLevels+1 := by unfold Volume.re; omega
      exact Nat.add_le_add_left (Nat.mul_le_mul C (by omega)) 4
    have total := sum_le vs.zipIdx w cap (fun p _ => each p)
    rw [List.length_zipIdx] at total
    have count := Nat.le_trans total (Nat.mul_le_mul_right cap size)
    simp only [preflight,List.map_map,Function.comp_def,List.length_range']
    change 1+2*c.poc.size+3*g.numComps+(vs.zipIdx.map w).sum ≤ 1+2*L.maxPocEntries+3*L.maxComponents+(L.maxPocEntries+1)*cap
    omega



/-- Shape and pre-translation history of a completed packet store. The part
table used by every output block has one entry per source tile-part. -/
def CompletedStore (L : Limits) (tp : TileParams) (out : TileCodeBlocks) : Prop :=
  ∃ (s : LoopState) (parts : List (Nat × Nat × Nat)) (spans : Array (Array (Nat × Nat))),
    parts.length = tp.tile.parts.size ∧ s.seq = out.packets ∧ s.seq ≤ L.maxPackets ∧
    tileRecords s ≤ s.seq * recordGrowth L ∧
    out.comps = spans.map (fun si => si.map fun (start,n) =>
      (Array.range n).map fun k => (s.precs.getD (start+k) default).out parts k)

/-- Logical segment/range count of the whole updated tile at any completed
body prefix, together with the contribution table still live during that
prefix. The next piece skip or the cumulative pass check can still fail. -/
theorem partial_body_store {L : Limits} {s : LoopState} {j st}
    (shape : StatesValid L s) (records : tileRecords s ≤ s.seq*recordGrowth L)
    (seq : s.seq < L.maxPackets) (get : s.precs[j]? = some st)
    {layer : Nat} {nonEmpty : Bool} {br pre cs bits}
    (header : (if nonEmpty then headerBands L layer st br else pure (st,#[],br)) = .ok (pre,cs,bits))
    {xs : List Contribution} (sub : xs <+: cs.toList) {body : Reader} {z}
    (read : forIn xs (pre.bands,body) Tier2Equiv.bodyBody = .ok z) :
    weight cs ≤ 3*(L.maxCodeBlocks*(1+L.maxPassesPerCodeBlock)) ∧
    tileRecords {s with precs := s.precs.setIfInBounds j {pre with bands := z.1}} ≤
      L.maxPackets*recordGrowth L := by
  obtain ⟨bands,geom⟩ := shape _ (Array.mem_of_getElem? get)
  have blockCap := Nat.mul_le_mul_right (L.maxCodeBlocks*(1+L.maxPassesPerCodeBlock)) bands
  have h := packet_prefix_storage geom header sub body read
  have step : retained z.1 ≤ retained st.bands + recordGrowth L :=
    Nat.le_trans h (Nat.add_le_add_left (Nat.mul_le_mul_left 2 blockCap) _)
  have stored := slots_set (fun p => retained p.bands) get (new := {pre with bands := z.1}) step
  have next := Nat.mul_le_mul_right (recordGrowth L) (Nat.succ_le_of_lt seq)
  rw [Nat.succ_mul] at next
  refine ⟨?_,Nat.le_trans stored (Nat.le_trans (Nat.add_le_add_right records _) next)⟩
  cases nonEmpty
  · cases header; exact Nat.zero_le _
  · exact Nat.le_trans (headers_post geom header).2 blockCap

/-- The final iterator state before range translation, including a tile whose
packed-header consumption check subsequently fails. -/
theorem completed_iteration {L : Limits} {h : Header} {data : ByteArray} {t g c ps base spans}
    {hs : Option HeaderStream} {pb : Nat} {buf : ByteArray} {s : LoopState}
    (parsed : Header.parse L data = .ok h) (layout : Layout.ofHeader h t = .ok (g,c))
    (quota : L.check JPEG2000.Tier2.Packet.loc .packets (iterationWork g c.progression c.poc) = .ok ())
    (init : initPrecincts L g = .ok (ps,base,spans))
    (run : forPackets g c.progression c.poc (packetStep L c base (hs.map (·.bytes)).isNone pb)
      (firstState ps buf hs) = .ok s) :
    StatesValid L s ∧ tileRecords s ≤ s.seq * recordGrowth L ∧ s.seq ≤ L.maxPackets := by
  have wf := Tier2Equiv.ofHeader_wf (Equiv.parse_dxdy parsed) layout
  rw [forPackets_schedule g wf] at run
  have initial : tileRecords (firstState ps buf hs) ≤ (firstState ps buf hs).seq * recordGrowth L := by
    rw [initial_records init]; exact Nat.zero_le _
  obtain ⟨records,count⟩ := prefix_records L _ _ _ _ _ _ (initial_valid parsed layout init) initial run
  have charged := visits_tests_le_charge (schedule g [] (volumes g c.progression c.poc))
  rw [schedule_charge g wf] at charged
  have allowed := (Limits.check_eq_ok_iff ..).1 quota
  change iterationWork g c.progression c.poc ≤ L.maxPackets at allowed
  change s.seq ≤ 0+(schedule g [] (volumes g c.progression c.poc)).length at count
  exact ⟨prefix_valid L _ _ _ _ _ _ (initial_valid parsed layout init) run, records, by omega⟩

private theorem raw_completed {L : Limits} {h : Header} {data : ByteArray} {tp : TileParams}
    {hs : Option HeaderStream} {pb : Nat} {out : TileCodeBlocks}
    (parsed : Header.parse L data = .ok h)
    (ok : decodeTilePacketsWith L h data tp (hs.map (·.bytes)) pb = .ok out) :
    CompletedStore L tp out := by
  unfold decodeTilePacketsWith at ok
  obtain ⟨⟨g,c⟩,layout,tail⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨_,quota,tail⟩ := Tier2Equiv.bind_ok tail
  obtain ⟨⟨ps,base,spans⟩,init,tail⟩ := Tier2Equiv.bind_ok tail
  obtain ⟨⟨buf,parts⟩,input,tail⟩ := Tier2Equiv.bind_ok tail
  obtain ⟨s,run,ret⟩ := Tier2Equiv.bind_ok tail
  cases ret
  obtain ⟨_,records,count⟩ := completed_iteration parsed layout quota init (hs := hs) run
  exact ⟨s,parts,spans,((HeaderWork.tileData_copy_charge data tp.tile).2.2 buf parts input).2,
    rfl,count,records,rfl⟩

/-- A successful tile at the public header-stream callback exposes the actual
pre-translation states, a packet-count limit and the retained history bound. -/
theorem completed_store {L : Limits} {h : Header} {data : ByteArray} {tp : TileParams}
    {hs : Option HeaderStream} {pb : Nat} {out : TileCodeBlocks}
    (parsed : Header.parse L data = .ok h)
    (ok : JPEG2000.Tier2.Headers.decodeWithStream L h data tp hs pb = .ok out) :
    CompletedStore L tp out := by
  unfold JPEG2000.Tier2.Headers.decodeWithStream at ok
  obtain ⟨tile,decoded,tail⟩ := Tier2Equiv.bind_ok ok
  cases hs with
  | none => cases tail; exact raw_completed (hs := none) parsed decoded
  | some stream =>
    simp only at tail
    split at tail <;> first | contradiction | (cases tail; exact raw_completed (hs := some stream) parsed decoded)

end JPEG2000.Spec.Resources.PacketLocalWork
