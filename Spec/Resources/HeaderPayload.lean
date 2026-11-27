import Spec.Resources.HeaderWork
import Spec.Resources.PacketSortWork
import Spec.Resources.PublicPacketWork

/-!
# Header payload and pointer work (Plan.md §§3–5, 7, S3)

T.800 A.3–A.7 and I.4–I.5. Work is measured in source-level callback visits,
sort operations and logical descriptor slots. In particular the failing callback
is visited even when its result never enters the output array. Rank sorting uses
the pinned list merge sort. The four byte-key sorts use insertion sort.

The account pairs an execution with its bound. A bind pays for its left side
even on error, then pays for the continuation only if reached. The counters
combine array capacity reservations, visits and copies. Some tariffs reserve
the maximum for a reached fold. Explicit concatenations allow full copies of
their growing accumulators. Descriptor units count logical slots and exclude
allocator headers, machine-specific capacity growth and diagnostic formatting.

The public codestream path builds the PPM rank index once. The standalone
single-tile `headerStreamOf` convenience API additionally searches for the tile
with `findIdx?`. `Color.checkCdef`, the per-colour `colourChannel` filters,
channel ordering and alpha selection occur after codestream decoding (7.4c4).
The `tileCompCounts` resolution arithmetic inside each charged admission visit
belongs to the geometry account (7.4c3c).
-/

namespace JPEG2000.Spec.Resources.HeaderPayload

open JPEG2000 JPEG2000.Bytes JPEG2000.Marker JPEG2000.TilePart JPEG2000.Header
open JPEG2000.Tier2.Headers
open JPEG2000.Spec.Tier2Equiv (bind_ok)

/-! ## Array reads and rejecting callback prefixes -/

private abbrev Run (α : Type) := Except Error α × Nat

private def next {α β : Type} (a : Run α) (f : α → Run β) : Run β :=
  match a.1 with
  | .error e => (.error e, a.2)
  | .ok x => let b := f x; (b.1, a.2 + b.2)

private theorem next_result {α β : Type} (a : Run α) (f : α → Run β) :
    (next a f).1 = (a.1 >>= fun x => (f x).1) := by
  cases a with | mk x n => cases x <;> rfl

private theorem next_bound {α β : Type} {a : Run α} {f : α → Run β} {i j : Nat}
    (ha : a.2 ≤ i) (hf : ∀ x, a.1 = .ok x → (f x).2 ≤ j) : (next a f).2 ≤ i+j := by
  cases a with | mk v c =>
    cases v with
    | error => exact Nat.le_trans ha (Nat.le_add_right ..)
    | ok x => exact Nat.add_le_add ha (hf x rfl)

/-- Meter the callback actually reached by either fixed-count array reader.
A failed read adds one visit and creates no entry. -/
def arrayReads {α : Type} (f : Reader → Except Error (α × Reader)) :
    Nat → Array α → Reader → Except Error (Array α × Reader) × Nat
  | 0, a, r => (.ok (a,r), 0)
  | n+1, a, r => next (f r, 1) fun (x,t) => arrayReads f n (a.push x) t

/-- Both array readers execute the same prefix, even on a callback error. Each
successful visit pushes one entry. The calling tariff separately charges the
initial capacity reservation. -/
theorem arrayReads_work {α : Type} (f : Reader → Except Error (α × Reader))
    (n : Nat) (a : Array α) (r : Reader) :
    (arrayReads f n a r).1 = Marker.readArray f a n r ∧
    (arrayReads f n a r).1 = Box.readMany f r a n ∧ (arrayReads f n a r).2 ≤ n := by
  induction n generalizing a r with
  | zero => exact ⟨rfl,rfl,Nat.zero_le _⟩
  | succ n ih =>
    cases h : f r with
    | error e => simp [arrayReads, next, Marker.readArray, Box.readMany, h, bind, Except.bind]
    | ok p =>
      obtain ⟨x,t⟩ := p
      obtain ⟨e₁,e₂,c⟩ := ih (a.push x) t
      simp [arrayReads, next, Marker.readArray, Box.readMany, h, bind, Except.bind, ← e₁, ← e₂]
      omega

/-- Charge one visit for each attempted varint byte, including the byte that
overflows a 32-bit packet length. -/
def varintReads : Nat → Nat → Bool → Array Nat → Reader → Except Error (Array Nat) × Nat
  | 0, c, p, a, r => (readVarints 0 c p a r,0)
  | n+1, c, _, a, r => next (r.u8,1) fun (b,t) =>
    let v := c*128 + (b &&& 0x7F).toNat
    if v ≥ 4294967296 then (.error (Marker.malformedAt r "PLT packet length ≥ 2^32"),0)
    else if b &&& 0x80 != 0 then varintReads n v true a t
    else varintReads n 0 false (a.push v) t

/-- PLT never attempts more byte reads or length pushes than the remaining
input fuel. A pending unterminated length still returns its original error. -/
theorem varintReads_work (n c : Nat) (p : Bool) (a : Array Nat) (r : Reader) :
    (varintReads n c p a r).1 = readVarints n c p a r ∧
    (varintReads n c p a r).2 ≤ n := by
  induction n generalizing c p a r with
  | zero => exact ⟨rfl,Nat.zero_le _⟩
  | succ n ih =>
    cases h : r.u8 with
    | error => simp [varintReads, next, readVarints, h]
    | ok pair =>
      obtain ⟨b,t⟩ := pair
      simp only [varintReads, next, h, readVarints]
      split
      · simp
      · split <;> (refine ⟨(ih ..).1,?_⟩; rw [Nat.add_comm 1]; exact Nat.succ_le_succ (ih ..).2)

private def countedFold {α β : Type} (f : β → α → Run β) : List α → β → Run β
  | [], a => (.ok a,0)
  | x::xs, a => next (f a x) (countedFold f xs)

private theorem fold_result {α β : Type} (f : β → α → Run β) (xs : List α) (a : β) :
    (countedFold f xs a).1 = xs.foldlM (m := Except Error) (fun a x => (f a x).1) a := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih => simp [countedFold,next_result,ih,List.foldlM_cons,bind,Except.bind]

private theorem fold_bound {α β : Type} (f : β → α → Run β) (P : β → Prop)
    (xs : List α) (a : β) (ha : P a) (k : Nat)
    (step : ∀ x ∈ xs, ∀ b, P b → (f b x).2 ≤ k ∧ ∀ z, (f b x).1 = .ok z → P z) :
    (countedFold f xs a).2 ≤ xs.length*k := by
  induction xs generalizing a with
  | nil => simp [countedFold]
  | cons x xs ih =>
    rw [countedFold,List.length_cons,Nat.succ_mul,Nat.add_comm]
    have s := step x (by simp) a ha
    exact next_bound s.1 fun z hz => ih z (s.2 z hz) fun y hy => step y (by simp [hy])

/-! ## Rank-sort inputs and pointer-sort call sites -/

/-- SOT position, owning tile row and part index supplied to the PPM rank sorter. -/
def rankTriples (h : Header) :=
  h.tiles.toList.zipIdx.flatMap fun (tp, j) =>
    tp.tile.parts.toList.zipIdx.map fun (p,k) => (p.pos,j,k)

private theorem triple_count (h : Header) : (rankTriples h).length = numTileParts h := by
  unfold rankTriples numTileParts
  rw [← Array.foldl_toList]
  generalize h.tiles.toList = l
  suffices aux : ∀ (a j : Nat), a + (l.zipIdx j |>.flatMap fun (tp,i) =>
      tp.tile.parts.toList.zipIdx.map fun (p,k) => (p.pos,i,k)).length =
    l.foldl (fun a tp => a + tp.tile.parts.size) a by simpa using aux 0 0
  induction l with
  | nil => simp
  | cons x xs ih =>
    intro a j
    simp only [List.zipIdx_cons,List.flatMap_cons,List.length_append,List.length_map,
      List.length_zipIdx,Array.length_toList,List.foldl_cons]
    rw [← ih (a + x.tile.parts.size) (j+1)]
    exact Nat.add_assoc .. |>.symm

/-- The exact rank sort in the public PPM index. Its input has one triple per
part across all tiles. `ppmChunkIndex` checks this length before sorting. -/
theorem rank_work (h : Header) :
    let xs := rankTriples h
    let s := PacketSortWork.measured (fun a b => a.1 ≤ b.1) xs
    xs.length = numTileParts h ∧ s.1 = xs.mergeSort (fun a b => a.1 ≤ b.1) ∧
    xs.length + s.2 ≤ numTileParts h + 8*(numTileParts h * numTileParts h)+1 ∧
    streamRanks h = s.1.zipIdx.foldl (fun acc ((_,j,k),rank) =>
      acc.modify j (·.setIfInBounds k rank)) (h.tiles.map fun tp => Array.replicate tp.tile.parts.size 0) := by
  have hs := PacketSortWork.sort_work (fun a b => a.1 ≤ b.1) (rankTriples h)
  exact ⟨triple_count h,hs.1,triple_count h ▸ hs.2, by rw [hs.1]; rfl⟩

/-- Charge a sort by a caller-supplied tariff of its input length and actual
checked operations. Unit tariff counts calls. The sort executes even on an
empty input and returns the original duplicate diagnostic. -/
def sortCall {α : Type} (price : Nat → Nat → Nat) (key : α → UInt8) (loc : Location)
    (what : String) (xs : Array α) : Except Error (Array α) × Nat :=
  let s := HeaderWork.measuredSortUnique key loc what xs
  (s.1, price xs.size s.2)

private theorem sort_result {α : Type} (price : Nat → Nat → Nat) (key : α → UInt8)
    (loc : Location) (what : String) (xs : Array α) :
    (sortCall price key loc what xs).1 = sortUnique key loc what xs :=
  (HeaderWork.sortUnique_work ..).1

/-- A cap for a tariff on any byte-key sort no longer than `n`. -/
def priceBound (price : Nat → Nat → Nat) (n k : Nat) :=
  ∀ i ≤ n, ∀ w ≤ i*i+2*i, price i w ≤ k

private theorem sort_bound {α : Type} (price : Nat → Nat → Nat) (key : α → UInt8)
    (loc : Location) (what : String) (xs : Array α) {n k : Nat}
    (hn : xs.size ≤ n) (hp : priceBound price n k) :
    (sortCall price key loc what xs).2 ≤ k :=
  hp _ hn _ (HeaderWork.sortUnique_work ..).2

private def pointerTables (L : Limits) (mh : MainHeader) (data : ByteArray) :
    Except Error (Array TLM × Array PPM × Nat) := do
  let mut tlms : Array TLM := #[]
  let mut ppms : Array PPM := #[]
  let mut tlmEntries := 0
  for s in mh.pointers do
    let body ← rangeReader data { offset := s.offset, length := s.length }
    if s.code == Code.TLM then
      let t ← parseTLM L body
      tlmEntries := tlmEntries + t.entries.size
      L.check (.atOffset .marker s.offset) .tileParts tlmEntries
      tlms := tlms.push t
    else if s.code == Code.PPM then
      ppms := ppms.push (← parsePPM body)
  return (tlms,ppms,tlmEntries)

private def finishPointers (L : Limits) (data : ByteArray) (loc : Location)
    (ts : Array TLM) (ps : Array PPM) : Except Error (Array TLM × PPMData) := do
  let ranges := ps.toList.map PPM.body
  let total := ranges.foldl (fun a rg => a + rg.length) 0
  let chunks ← ppmChunks L data loc total ranges #[]
  return (ts,{ segments := ps, chunks })

/-- Trace the two main-header sort sites. A bad TLM prefix prevents both sorts,
and a duplicate Ztlm prevents the Zppm sort. -/
def pointerSorts (price : Nat → Nat → Nat) (L : Limits) (mh : MainHeader) (data : ByteArray) :
    Except Error (Array TLM × PPMData) × Nat :=
  let loc := Location.atOffset .marker mh.endPos
  next (pointerTables L mh data,0) fun (ts,ps,_) =>
  next (sortCall price TLM.ztlm loc "Ztlm" ts) fun ts =>
  next (sortCall price PPM.zppm loc "Zppm" ps) fun ps =>
    (finishPointers L data loc ts ps,0)

private theorem growth {α β : Type} (w : β → Nat)
    (f : α → β → Except Error (ForInStep β))
    (add : ∀ x b v, f x b = .ok v → w v.value ≤ w b + 1)
    (xs : List α) (a z : β) (ok : forIn xs a f = .ok z) : w z ≤ w a + xs.length := by
  induction xs generalizing a with
  | nil => cases ok; simp
  | cons x xs ih =>
    rw [List.forIn_cons] at ok
    obtain ⟨v,hv,ok⟩ := bind_ok ok
    have hs := add _ _ _ hv
    cases v with
    | done y => cases ok; exact Nat.le_trans hs (by simp)
    | yield y =>
      have := ih y ok
      change w y ≤ w a + 1 at hs
      simp only [List.length_cons]; omega

private theorem table_sizes {L : Limits} {mh : MainHeader} {d : ByteArray} {z}
    (ok : pointerTables L mh d = .ok z) : z.1.size + z.2.1.size ≤ mh.pointers.size := by
  unfold pointerTables at ok
  obtain ⟨a,loop,ok⟩ := bind_ok ok
  cases ok
  rw [← Array.forIn_toList] at loop
  apply Nat.le_trans (growth (fun b : Array TLM × Array PPM × Nat => b.1.size + b.2.1.size)
    _ ?_ _ _ _ loop) (by simp)
  intro s b v hv
  obtain ⟨_,_,hv⟩ := bind_ok hv
  (repeat' first | (split at hv <;> try contradiction) | (obtain ⟨_,_,hv⟩ := bind_ok hv))
  all_goals cases hv; simp <;> omega

private theorem pointer_erases (price : Nat → Nat → Nat) (L : Limits) (mh : MainHeader)
    (d : ByteArray) : (pointerSorts price L mh d).1 = parsePointers L mh d := by
  simp only [pointerSorts,next_result,sort_result]
  unfold pointerTables parsePointers
  simp only [bind_assoc,pure_bind]
  rfl

/-- The two arrays together contain at most one descriptor per raw pointer
visited. Multiplying the per-call tariff by two covers the rejecting prefix. -/
theorem pointerSorts_work (price : Nat → Nat → Nat) (L : Limits) (mh : MainHeader)
    (d : ByteArray) (k : Nat) (hp : priceBound price mh.pointers.size k) :
    (pointerSorts price L mh d).1 = parsePointers L mh d ∧ (pointerSorts price L mh d).2 ≤ 2*k := by
  refine ⟨pointer_erases ..,?_⟩
  unfold pointerSorts
  rw [Nat.two_mul,← Nat.zero_add (k+k)]
  apply next_bound (Nat.le_refl 0)
  rintro ⟨ts,ps,n⟩ hz
  have sizes := table_sizes hz
  apply next_bound (sort_bound _ _ _ _ _ (by dsimp at sizes; omega) hp)
  intro _ _
  apply Nat.le_trans (next_bound (sort_bound _ _ _ _ _ (by dsimp at sizes; omega) hp)
    (j := 0) (by intros; exact Nat.le_refl 0)) (by simp)

private def plts (p : TilePartHeader) := p.segments.filterMap fun | .plt x => some x | _ => none
private def ppts (ps : Array TilePartHeader) :=
  ps.foldl (fun acc p => acc ++ p.segments.filterMap fun | .ppt x => some x | _ => none) #[]

private def partSort (price : Nat → Nat → Nat) (p : TilePartHeader) : Run (Array Nat) :=
  next (sortCall price PLT.zplt (.atOffset .marker p.pos) "Zplt" (plts p))
    fun xs => (.ok (xs.foldl (fun a x => a ++ x.lengths) #[]),0)

private theorem part_result (price : Nat → Nat → Nat) (p : TilePartHeader) :
    (partSort price p).1 = partPlt p := by
  simp only [partSort,next_result,sort_result]; rfl

private theorem ppt_size (ps : Array TilePartHeader) (n : Nat)
    (hp : ∀ p ∈ ps, p.segments.size ≤ n) : (ppts ps).size ≤ ps.size*n := by
  unfold ppts
  rw [← Array.foldl_toList]
  suffices ∀ a : Array PPT, (ps.toList.foldl (fun acc p => acc ++ p.segments.filterMap
      fun | .ppt x => some x | _ => none) a).size ≤ a.size + ps.toList.length*n by
    simpa using this #[]
  replace hp : ∀ p ∈ ps.toList, p.segments.size ≤ n := by simpa using hp
  generalize ps.toList = xs at *
  induction xs with
  | nil => simp
  | cons x xs ih =>
    intro a
    rw [List.foldl_cons]
    have h := ih (fun y hy => hp y (by simp [hy])) (a ++ x.segments.filterMap fun | .ppt p => some p | _ => none)
    have sz := Array.size_filterMap_le (xs := x.segments) (f := fun | .ppt p => some p | _ => none)
    have hx := hp x (by simp)
    simp only [Array.size_append,List.length_cons,Nat.succ_mul] at *
    omega

private def declaredParts (corr : Bool) (ps : Array TilePartHeader) :=
  let d := ps.foldl (fun a p => if p.sot.tnsot ≠ 0 then p.sot.tnsot.toNat else a) 0
  if d ≠ 0 ∧ corr then d + 1 else d

/-- Trace the single tile-wide PPT sort and the tile-part-local PLT sorts in
their actual execution order. The TNsot check precedes even the first sort. -/
def tileSorts (price : Nat → Nat → Nat) (corr : Bool) (i : Nat) (ps : Array TilePartHeader) :
    Except Error Tile × Nat :=
  let loc := Location.atOffset .marker ((ps[0]?.map (·.pos)).getD 0)
  let tn := declaredParts corr ps
  if tn ≠ 0 ∧ tn ≠ ps.size then (assembleTile corr i ps,0)
  else next (sortCall price PPT.zppt loc "Zppt" (ppts ps)) fun ppt =>
    next (countedFold (fun a p => next (partSort price p) fun xs => (.ok (a ++ xs),0))
      ps.toList #[]) fun plt =>
      (.ok { index := i, parts := ps, tnsot := tn, ppt := ppt.map PPT.body, plt },0)

private theorem tile_erases (price : Nat → Nat → Nat) (corr : Bool) (i : Nat) (ps : Array TilePartHeader) :
    (tileSorts price corr i ps).1 = assembleTile corr i ps := by
  unfold tileSorts
  dsimp only
  split
  · rfl
  · rename_i h
    simp only [next_result,sort_result,fold_result,part_result,Array.foldlM_toList]
    unfold declaredParts at h
    simp only [assembleTile, h, ↓reduceIte]
    rfl

/-- One sort can see PPT markers across all parts. Each reached PLT sort sees
only its own part. Unit tariffs bound calls by `1 + ps.size`. -/
theorem tileSorts_work (price : Nat → Nat → Nat) (corr : Bool) (i n : Nat)
    (ps : Array TilePartHeader) (hn : ∀ p ∈ ps, p.segments.size ≤ n) (ppt plt : Nat)
    (ht : priceBound price (ps.size*n) ppt) (hl : priceBound price n plt) :
    (tileSorts price corr i ps).1 = assembleTile corr i ps ∧
    (tileSorts price corr i ps).2 ≤ ppt + ps.size*plt := by
  refine ⟨tile_erases ..,?_⟩
  unfold tileSorts
  dsimp only
  split
  · exact Nat.zero_le _
  · apply next_bound (sort_bound _ _ _ _ _ (ppt_size _ _ hn) ht)
    intro _ _
    apply Nat.le_trans (next_bound (i := ps.toList.length*plt) (j := 0) ?_ (by intros; exact Nat.le_refl 0)) (by simp)
    apply fold_bound _ (fun _ => True) _ _ trivial
    intro p hp a _
    have h : (plts p).size ≤ n := Nat.le_trans Array.size_filterMap_le (hn p (by simpa using hp))
    refine ⟨?_, by simp⟩
    apply Nat.le_trans (next_bound (i := plt) (j := 0) ?_ (by intros; exact Nat.le_refl 0)) (by simp)
    apply Nat.le_trans (next_bound (sort_bound _ _ _ _ _ h hl) (j := 0) (by intros; exact Nat.le_refl 0)) (by simp)

/-! ## Composing bounded executions -/

/-- A metered execution of a specific decoder expression with a proved budget.
The result component includes decoder errors. -/
structure Account {α : Type} (source : Except Error α) (budget : Nat) where
  /-- Metered result and source-level charge. -/
  run : Except Error α × Nat
  /-- Erasure preserves the complete result. -/
  erase : run.1 = source
  /-- Upper bound, independent of success. -/
  bound : run.2 ≤ budget

private def billed {α : Type} (s : Except Error α) {n cap : Nat} (h : n ≤ cap) :
    Account s cap := ⟨(s,n),rfl,h⟩

private def free {α : Type} (s : Except Error α) (n : Nat) : Account s n :=
  billed s (Nat.zero_le n)

private def widen {α : Type} {s : Except Error α} {i j : Nat} (a : Account s i) (h : i ≤ j) :
    Account s j := ⟨a.run,a.erase,Nat.le_trans a.bound h⟩

private def seqAct {α β : Type} {s : Except Error α} {f : α → Except Error β} {i j : Nat}
    (a : Account s i) (b : ∀ x, s = .ok x → Account (f x) j) : Account (s >>= f) (i+j) :=
  match h : a.run.1 with
  | .error e => ⟨(.error e,a.run.2), by exact (congrArg (· >>= f) (a.erase.symm.trans h)).symm,
      Nat.le_trans a.bound (Nat.le_add_right ..)⟩
  | .ok x =>
    let tail := b x (a.erase.symm.trans h)
    ⟨(tail.run.1,a.run.2+tail.run.2), by exact tail.erase.trans (congrArg (· >>= f) (a.erase.symm.trans h)).symm,
      Nat.add_le_add a.bound tail.bound⟩

private def after {α β : Type} {s : Except Error α} {f : α → Except Error β} {n : Nat}
    (b : ∀ x, s = .ok x → Account (f x) n) : Account (s >>= f) n :=
  widen (seqAct (free s 0) b) (by omega)

private def before {α β : Type} {s : Except Error α} {f : α → Except Error β} {n : Nat}
    (a : Account s n) : Account (s >>= f) n := seqAct a (fun x _ => free (f x) 0)

private theorem check_limit {L : Limits} {loc k n u} (h : L.check loc k n = .ok u) :
    n ≤ L.bound k := (Limits.check_eq_ok_iff ..).1 h

private theorem required {r : Reader} {P : Prop} [Decidable P] {s u}
    (h : require r P s = .ok u) : P := by
  unfold require at h; split at h <;> first | exact of_decide_eq_true (by assumption) | contradiction

private def fixedRead {α : Type} (f : Reader → Except Error (α × Reader)) (r : Reader) (n : Nat)
    (a : Array α) : Account (readArray f a n r) (2*n) :=
  let m := arrayReads_work f n a r
  ⟨((arrayReads f n a r).1,n+(arrayReads f n a r).2),m.1,by have := m.2.2; omega⟩

private theorem array_size {α : Type} (f : Reader → Except Error (α × Reader)) (n : Nat)
    (a : Array α) (r : Reader) {out : Array α × Reader}
    (ok : readArray f a n r = .ok out) : out.1.size = a.size+n := by
  induction n generalizing a r with
  | zero => cases ok; rfl
  | succ n ih =>
    rw [readArray] at ok
    split at ok <;> try contradiction
    rw [ih _ _ ok, Array.size_push]; omega

/-! ## Main and tile-part marker payloads -/

private def quantAccount (r : Reader) : Account (readQuant r) (2*maxBands) := by
  unfold readQuant
  apply after
  rintro ⟨s,t⟩ _
  dsimp only
  split
  · apply after
    intro u hu
    exact before (widen (fixedRead ..) (Nat.mul_le_mul_left 2 (required hu).2))
  · exact free _ _
  · apply after
    intro u hu
    exact before (widen (fixedRead ..) (Nat.mul_le_mul_left 2 (required hu).2.2))
  · exact free _ _

private def pocAccount (L : Limits) (c : Nat) (r : Reader) :
    Account (parsePOC L c r) (2*L.maxPocEntries) := by
  unfold parsePOC
  apply after
  intro _ _
  apply after
  intro _ hc
  exact before (widen (fixedRead ..) (Nat.mul_le_mul_left 2 (check_limit hc)))

private def tlmAccount (L : Limits) (r : Reader) :
    Account (parseTLM L r) (2*L.maxTileParts) := by
  unfold parseTLM
  iterate 2 (apply after; rintro ⟨_,_⟩ _)
  iterate 3 (apply after; intro _ _)
  apply after
  intro _ hc
  exact before (widen (fixedRead ..) (Nat.mul_le_mul_left 2 (check_limit hc)))

/-- The SIZ component array charges its reserved slots even if the first
component reader fails. -/
def sizPayload (L : Limits) (r : Reader) : Account (parseSIZ L r) (2*L.maxComponents) := by
  unfold parseSIZ
  iterate 10 (apply after; rintro ⟨_,_⟩ _)
  apply after
  intro _ _
  apply after
  intro _ hc
  iterate 5 (apply after; intro _ _)
  exact before (widen (fixedRead ..) (Nat.mul_le_mul_left 2 (check_limit hc)))

private def styleAccount (L : Limits) (defined : Bool) (r : Reader) :
    Account (readCodingStyle L defined r) (4*(L.maxDecompLevels+1)) := by
  unfold readCodingStyle
  apply after
  rintro ⟨levels,r⟩ _
  apply after
  intro _ _
  apply after
  intro _ hc
  have maxLevel : levels.toNat ≤ L.maxDecompLevels := check_limit hc
  iterate 2 (apply after; rintro ⟨_,_⟩ _)
  apply after
  intro _ _
  apply after
  rintro ⟨_,_⟩ _
  dsimp only
  split
  · exact free _ _
  apply after
  intro _ _
  apply after
  rintro ⟨_,_⟩ _
  dsimp only
  split <;> apply after <;> intro _ _ <;> split
  all_goals first
    | apply widen (seqAct (fixedRead ..) (j := 2*(levels.toNat+1)) ?_) (by omega)
      rintro ⟨ps,t⟩ hp
      have hsize := array_size _ _ _ _ hp
      exact billed _ (n := 2*ps.size) (by simpa using Nat.mul_le_mul_left 2 (Nat.le_of_eq hsize))
    | exact free (pure _) _

private def codAccount (L : Limits) (r : Reader) :
    Account (parseCOD L r) (4*(L.maxDecompLevels+1)) := by
  unfold parseCOD
  apply after
  rintro ⟨_,_⟩ _
  apply after
  intro _ _
  apply after
  rintro ⟨_,_⟩ _
  dsimp only
  split <;> apply after <;> intro _ _ <;> apply after <;> rintro ⟨_,_⟩ _
  all_goals
    iterate 2 (apply after; intro _ _)
    apply after
    rintro ⟨_,_⟩ _
    dsimp only
    split
    · exact free _ _
    exact before (styleAccount ..)

private def cocAccount (L : Limits) (c : Nat) (r : Reader) :
    Account (parseCOC L c r) (4*(L.maxDecompLevels+1)) := by
  unfold parseCOC
  iterate 2 (apply after; rintro ⟨_,_⟩ _)
  apply after
  intro _ _
  exact before (styleAccount ..)

private def comAccount (r : Reader) : Account (parseCOM r) r.data.size := by
  unfold parseCOM
  apply after
  rintro ⟨_,t⟩ ht
  apply billed _ (n := t.remaining)
  rw [← (Reader.u16be_pos ht).2.2.1]; exact Nat.le_trans (Nat.sub_le ..) t.stop_le

private def pltAccount (r : Reader) : Account (parsePLT r) (2*r.data.size) := by
  unfold parsePLT
  apply after
  rintro ⟨_,t⟩ ht
  have hd := (Reader.u8_pos ht).2.2.1
  have h := varintReads_work t.remaining 0 false #[] t
  have := t.stop_le
  apply before
  refine ⟨((varintReads t.remaining 0 false #[] t).1,2*(varintReads t.remaining 0 false #[] t).2),h.1,?_⟩
  apply Nat.mul_le_mul_left 2
  exact Nat.le_trans h.2 (by rw [← hd]; unfold Reader.remaining; omega)

/-- Inner marker tariff, including reserved array slots, callback visits and
the subsequent COD/COC precinct validation traversal. TLM pointers are parsed
later in the main pointer pass. -/
def markerBudget (L : Limits) (c bytes : Nat) :=
  4*(L.maxDecompLevels+1) + 2*maxBands + 2*L.maxPocEntries + 2*c + 2*bytes

private def mainCallback (L : Limits) (c : Nat) (a : Acc) (m : UInt16) (r : Reader) :
    Account (addSegment L c a m r) (markerBudget L c r.data.size) := by
  unfold addSegment
  by_cases hm : m == Code.COD
  · rw [ite_eq_left hm]
    apply after; intro _ _; apply before; apply widen (codAccount ..); unfold markerBudget; omega
  rw [ite_eq_right hm]
  split
  · apply before; apply widen (cocAccount ..); unfold markerBudget; omega
  split
  · apply after; intro _ _; apply before; apply widen (quantAccount ..); unfold markerBudget; omega
  split
  · apply before; unfold parseQCC; apply after; rintro ⟨_,_⟩ _
    apply before; apply widen (quantAccount ..); unfold markerBudget; omega
  split
  · exact free _ _
  split
  · apply before; apply widen (pocAccount ..); unfold markerBudget; omega
  split
  · apply before; apply widen (comAccount ..); unfold markerBudget; omega
  split
  · apply after; intro _ _; apply before; unfold parseCRG; apply after; intro _ _
    apply before; apply widen (fixedRead ..); unfold markerBudget; omega
  exact free _ _

private def tileCallback (L : Limits) (c : Nat) (first ppm : Bool) (a : TPAcc) (m : UInt16) (r : Reader) :
    Account (addTileSegment L c first ppm a m r) (markerBudget L c r.data.size) := by
  unfold addTileSegment
  by_cases hg : (firstPartOnly m && !first) = true
  · simp only [hg, ↓reduceIte]; exact free _ _
  simp only [hg, Bool.false_eq_true, ↓reduceIte]
  by_cases hm : m == Code.COD
  · rw [ite_eq_left hm]
    apply after; intro _ _; apply before; apply widen (codAccount ..); unfold markerBudget; omega
  rw [ite_eq_right hm]
  split
  · apply before; apply widen (cocAccount ..); unfold markerBudget; omega
  split
  · apply after; intro _ _; apply before; apply widen (quantAccount ..); unfold markerBudget; omega
  split
  · apply before; unfold parseQCC; apply after; rintro ⟨_,_⟩ _
    apply before; apply widen (quantAccount ..); unfold markerBudget; omega
  split
  · exact free _ _
  split
  · apply before; apply widen (pocAccount ..); unfold markerBudget; omega
  split
  · exact free _ _
  split
  · apply before; apply widen (pltAccount ..); unfold markerBudget; omega
  split
  · apply before; apply widen (comAccount ..); unfold markerBudget; omega
  exact free _ _

private def charge {α : Type} {s : Except Error α} {i : Nat} (j : Nat) (a : Account s i) :
    Account s (j+i) := ⟨(a.run.1,j+a.run.2),a.erase,Nat.add_le_add_left a.bound j⟩

private def pay {α β : Type} {s : Except Error α} {t : Except Error β} {i j : Nat}
    (a : Account s i) (b : Account t j) : Account t (i+j) :=
  ⟨(b.run.1,a.run.2+b.run.2),b.erase,Nat.add_le_add a.bound b.bound⟩

private theorem rem_le (r : Reader) : r.remaining ≤ r.data.size :=
  Nat.le_trans (Nat.sub_le ..) r.stop_le

/-- Every reached main marker charges its visit and index/segment slots,
including the marker whose payload rejects. The caller supplies remaining bytes as fuel. -/
def mainHeaderPayload (L : Limits) (c : Nat) :
    (f : Nat) → (a : Acc) → (r : Reader) →
    Account (segmentLoop L c f a r) (f*(3+markerBudget L c r.data.size))
  | 0, _, _ => free _ _
  | f+1, a, r => by
    rw [Nat.succ_mul,Nat.add_comm (f*_ : Nat), Nat.add_assoc]
    apply charge 3
    rw [segmentLoop]
    split
    · exact free _ _
    · rename_i m r1 hr
      have hd := (Reader.u16be_pos hr).2.2.1
      split
      · exact free _ _
      split
      · exact free _ _
      split
      · apply widen (mainHeaderPayload L c f _ _)
        rw [hd]; omega
      split
      · exact free _ _
      split
      · exact free _ _
      · rename_i body len r2 hs
        have h := HeaderWork.readSegment_extent hs
        have hb := h.1.trans hd
        have ht := h.2.1.trans hd
        let inner := mainCallback L c { a with markers := a.markers.push { code := m, pos := r.pos, len := len+2 } } m body
        dsimp only
        split
        · apply pay (widen inner (by simp only [hb, Nat.le_refl]))
          exact free _ _
        · apply pay (widen inner (by simp only [hb, Nat.le_refl]))
          exact widen (mainHeaderPayload L c f _ _) (by simp only [ht, Nat.le_refl])

/-- Every reached tile-part marker charges its visit and index/segment slots,
including the marker whose payload rejects. The caller supplies remaining bytes as fuel. -/
def tileHeaderPayload (L : Limits) (c : Nat) (first ppm : Bool) :
    (f : Nat) → (a : TPAcc) → (r : Reader) →
    Account (TilePart.headerLoop L c first ppm f a r) (f*(3+markerBudget L c r.data.size))
  | 0, _, _ => free _ _
  | f+1, a, r => by
    rw [Nat.succ_mul,Nat.add_comm (f*_ : Nat), Nat.add_assoc]
    apply charge 3
    rw [TilePart.headerLoop]
    split
    · exact free _ _
    · rename_i m r1 hr
      have hd := (Reader.u16be_pos hr).2.2.1
      split
      · exact free _ _
      split
      · exact free _ _
      split
      · apply widen (tileHeaderPayload L c first ppm f _ _)
        rw [hd]; omega
      split
      · exact free _ _
      split
      · exact free _ _
      · rename_i body len r2 hs
        have h := HeaderWork.readSegment_extent hs
        have hb := h.1.trans hd
        have ht := h.2.1.trans hd
        let inner := tileCallback L c first ppm { a with markers := a.markers.push { code := m, pos := r.pos, len := len+2 } } m body
        dsimp only
        split
        · apply pay (widen inner (by simp only [hb, Nat.le_refl]))
          exact free _ _
        · apply pay (widen inner (by simp only [hb, Nat.le_refl]))
          exact widen (tileHeaderPayload L c first ppm f _ _) (by simp only [ht, Nat.le_refl])


/-! ## JP2 box payloads and the single descent into jp2h -/

private def many {α : Type} (f : Reader → Except Error (α × Reader)) (r : Reader)
    (a : Array α) (n : Nat) : Account (Box.readMany f r a n) (2*n) :=
  let h := arrayReads_work f n a r
  ⟨((arrayReads f n a r).1,n+(arrayReads f n a r).2),h.2.1,by have := h.2.2; omega⟩

private def beReads (r : Reader) (a : UInt64) : (n : Nat) → Account (Box.readBE r a n) n
  | 0 => free _ _
  | n+1 => by
    rw [Box.readBE,Nat.add_comm n]
    apply seqAct (billed _ (Nat.le_refl 1))
    rintro ⟨_,t⟩ _
    exact beReads t _ n

private def readRow (bits : Array UInt8) (r : Reader) (a : Array UInt64) :=
  bits.foldlM (fun (a,r) bi => do
    let (v,r) ← Box.readBE r 0 (Box.entryBytes bi)
    pure (a.push v,r)) (a,r)

private def rowCell (s : Array UInt64 × Reader) (bi : UInt8) :=
  next ((beReads s.2 0 (Box.entryBytes bi)).run) fun (v,t) => (.ok (s.1.push v,t),1)

private def rowAccount (bits : Array UInt8) (r : Reader) (a : Array UInt64) :
    Account (readRow bits r a) (bits.size*33) := by
  refine ⟨countedFold rowCell bits.toList (a,r),?_,?_⟩
  · simp only [fold_result,rowCell,next_result,Account.erase,Array.foldlM_toList]; rfl
  · rw [← Array.length_toList (xs := bits)]
    apply fold_bound _ (fun _ => True) _ _ trivial
    intro b _ s _
    refine ⟨?_,by simp⟩
    have hb := (b &&& 0x7F).toNat_lt
    have bound : Box.entryBytes b ≤ 32 := by unfold Box.entryBytes; omega
    exact next_bound (Nat.le_trans (beReads ..).bound bound) (j := 1) (by rintro ⟨_,_⟩ _; exact Nat.le_refl _)

private def rowsAccount (bits : Array UInt8) (r : Reader) (a : Array UInt64) :
    (n : Nat) → Account (Box.parsePclr.rows (readRow bits) r a n) (n*(1+bits.size*33))
  | 0 => free _ _
  | n+1 => by
    rw [Box.parsePclr.rows,Nat.succ_mul,Nat.add_comm (n*_),Nat.add_assoc]
    apply charge 1
    apply seqAct (rowAccount ..)
    rintro ⟨a,t⟩ _
    exact rowsAccount bits t a n

/-- Per-box capacity and callback budget. Palette dimensions are bounded before
reserving the row-major result. Tag scans may run even if no row is reached. -/
def boxBudget (L : Limits) (bytes : Nat) :=
  4*bytes + 4*255 + min L.maxPaletteEntries 1024 * (1+255*34)

private def paletteAccount (L : Limits) (b : Box.BoxHdr) :
    Account (Box.parsePclr L b) (boxBudget L b.body.data.size) := by
  unfold Box.parsePclr
  apply after
  rintro ⟨ne,r1⟩ h1
  apply after
  rintro ⟨npc,r2⟩ h2
  dsimp only
  by_cases hr : (ne.toNat == 0 || decide (ne.toNat > 1024)) = true
  · rw [ite_eq_left hr]; exact free _ _
  rw [ite_eq_right hr]
  apply after
  intro _ hc
  split
  · exact free _ _
  rename_i hn
  split
  · exact free _ _
  rename_i ht
  have maxrows : ne.toNat ≤ min L.maxPaletteEntries 1024 := by
    have hlim : ne.toNat ≤ L.maxPaletteEntries := check_limit hc
    simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hr
    omega
  have maxcols : npc.toNat ≤ 255 := by have := npc.toNat_lt; omega
  let cells := min L.maxPaletteEntries 1024 * (1+255*34)
  apply widen (seqAct (many ..) (j := 2*255+cells) ?_) (by unfold boxBudget; dsimp [cells]; omega)
  rintro ⟨bits,r3⟩ hb
  have hb' := (arrayReads_work Reader.u8 npc.toNat (Array.emptyWithCapacity npc.toNat) r2)
  have sz := array_size _ _ _ _ (hb'.1 ▸ hb'.2.1 ▸ hb)
  change bits.size = 0+npc.toNat at sz
  apply widen (charge (2*bits.size) (i := cells) ?_) (by omega)
  dsimp only
  split
  · exact free _ _
  rename_i hd
  split
  · exact free _ _
  rename_i fit
  have rr : 1 ≤ ne.toNat ∧ ne.toNat ≤ 1024 := by
    simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hr
    omega
  have ht' := HeaderWork.palette_table h1 h2 rr (by simpa using hc)
    (by simp only [beq_iff_eq] at hn; omega) (by omega) hb (by simpa using hd) (by omega)
  have rowcost := Nat.mul_le_mul maxrows (Nat.add_le_add_left (Nat.mul_le_mul_right 34 maxcols) 1)
  apply widen (charge (ne.toNat*npc.toNat) (before (rowsAccount ..))) ?_
  dsimp [cells]
  rw [ht'.1,← Nat.mul_add]
  exact Nat.le_trans (Nat.mul_le_mul_left _ (by omega)) rowcost

private def boxCallback (L : Limits) (a : Box.HdrAcc) (b : Box.BoxHdr) :
    Account (Box.addHeaderBox L a b) (boxBudget L b.body.data.size) := by
  unfold Box.addHeaderBox
  dsimp only
  split
  · exact free _ _
  split
  · split
    · exact free _ _
    apply before
    unfold Box.parseBpcc
    apply widen (seqAct (many ..) (j := b.body.remaining) ?_) ?_
    · rintro ⟨bs,t⟩ hb
      have p := arrayReads_work Reader.u8 b.body.remaining (Array.emptyWithCapacity b.body.remaining) b.body
      have sz := array_size _ _ _ _ (p.1 ▸ p.2.1 ▸ hb)
      exact billed _ (n := bs.size) (by simpa using Nat.le_of_eq sz)
    · have := rem_le b.body; unfold boxBudget; omega
  split
  · exact free _ _
  split
  · split
    · exact free _ _
    exact before (paletteAccount ..)
  split
  · split
    · exact free _ _
    apply before
    unfold Box.parseCmap
    dsimp only
    split
    · exact free _ _
    apply before; apply widen (many ..)
    have := rem_le b.body; unfold boxBudget; omega
  split
  · split
    · exact free _ _
    apply before
    unfold Box.parseCdef
    apply after
    rintro ⟨n,t⟩ h
    dsimp only
    split
    · exact free _ _
    split
    · exact free _ _
    apply before; apply widen (many ..)
    have hd := (Reader.u16be_pos h).2.2.1
    have hh := rem_le t; rw [hd] at hh
    unfold boxBudget; omega
  exact free _ _

/-- Every child of jp2h, including a rejecting payload, uses the same checked
backing data as its enclosing box. -/
def boxChildren (L : Limits) (r : Reader) (a : Box.HdrAcc) (count : Nat) :
    (f : Nat) → Account (Box.headerLoop L r a count f) (f*(3+boxBudget L r.data.size))
  | 0 => free _ _
  | f+1 => by
    rw [Nat.succ_mul,Nat.add_comm (f*_),Nat.add_assoc]
    apply charge 3
    rw [Box.headerLoop]
    split
    · exact free _ _
    apply after
    intro _ _
    apply after
    rintro ⟨b,t⟩ hb
    have e := HeaderWork.readBox_extent hb
    apply seqAct (widen (boxCallback L a b) (by simp [e.2.1]))
    intro z _
    exact widen (boxChildren L t z _ f) (by simp [e.2.2.1])

private def jp2hAccount (L : Limits) (b : Box.BoxHdr) (i : Nat) :
    Account (Box.parseJp2h L b i) ((L.maxBoxes+1)*(3+boxBudget L b.body.data.size)) := by
  unfold Box.parseJp2h
  apply after
  intro _ _
  exact before (boxChildren ..)

/-- The top loop descends into at most one jp2h. A failed descent spends its
own budget, while a successful descent removes that budget from the tail. -/
def topBoxes (L : Limits) (r : Reader) (hdr : Option Box.Jp2Header) (count : Nat) :
    (f : Nat) → Account (Box.topLoop L r hdr count f)
      (f*3 + if hdr.isNone then (L.maxBoxes+1)*(3+boxBudget L r.data.size) else 0)
  | 0 => free _ _
  | f+1 => by
    rw [Nat.succ_mul,Nat.add_comm (f*3),Nat.add_assoc]
    apply charge 3
    rw [Box.topLoop]
    split
    · exact free _ _
    apply after
    intro _ _
    apply after
    rintro ⟨b,t⟩ hb
    have e := HeaderWork.readBox_extent hb
    dsimp only
    split
    · exact free _ _
    split
    · rename_i hy
      have hn := (Bool.and_eq_true_iff.mp hy).2
      rw [hn,ite_eq_left rfl,Nat.add_comm (f*3)]
      apply seqAct (widen (jp2hAccount L b _) (by simp only [e.2.1,Nat.le_refl]))
      rintro ⟨h,j⟩ _
      exact widen (topBoxes L t (some h) j f) (by simp)
    · exact widen (topBoxes L t hdr _ f) (by simp [e.2.2.1])

/-- Header signature plus ftyp and JP2 boxes at the real container entry point.
Raw codestream recognition, ICC ranges and skipped superboxes take fixed work. -/
def filePayload (L : Limits) (d : ByteArray) :
    Account (Box.parseFileAux L d)
      (2*d.size + (L.maxBoxes+1)*3 + (L.maxBoxes+1)*(3+boxBudget L d.size)) := by
  unfold Box.parseFileAux
  apply after
  intro _ _
  split
  · exact free _ _
  dsimp only
  cases hs : Box.readBox (Reader.ofByteArray d .box)
  · exact free _ _
  rename_i p
  obtain ⟨sig,r⟩ := p
  simp only [pure_bind]
  split
  · exact free _ _
  apply after
  rintro ⟨_,_⟩ hv
  dsimp only
  split
  · exact free _ _
  apply after
  rintro ⟨b,t⟩ hb
  dsimp only
  split
  · exact free _ _
  have h0 : r.data = d := by
    exact (HeaderWork.readBox_extent hs).2.2.1
  have e := HeaderWork.readBox_extent hb
  have hd := e.2.1.trans h0
  rw [Nat.add_assoc]
  apply seqAct (i := 2*d.size)
  · unfold Box.parseFtyp
    dsimp only
    split
    · exact free _ _
    iterate 2 (apply after; rintro ⟨_,_⟩ _)
    apply before; apply widen (many ..)
    have h := rem_le b.body; rw [hd] at h; omega
  · intro _ _
    apply before; apply widen (topBoxes ..)
    simp [e.2.2.1,h0]

/-! ## Pointer tables, range splitting and tile assembly -/

/-- For each reached loop body `j` is the number of preceding successes.
The invariant is required only for states that continue the decoder loop. -/
private def forBudget {α β : Type} (P : Nat → β → Prop) (f : α → β → Except Error (ForInStep β))
    (k : Nat) (xs : List α) (j : Nat) (b : β) (hb : P j b)
    (step : ∀ x ∈ xs, ∀ i a, i < j+xs.length → P i a →
      Account (f x a) k)
    (inv : ∀ x ∈ xs, ∀ i a z, P i a → f x a = .ok (.yield z) → P (i+1) z) :
    Account (forIn xs b f) (xs.length*k) := by
  cases xs with
  | nil => exact free _ _
  | cons x xs =>
    rw [List.forIn_cons,List.length_cons,Nat.succ_mul,Nat.add_comm (xs.length*k)]
    apply seqAct (step x (by simp) j b (by simp) hb)
    intro v hv
    cases v with
    | done => exact free _ _
    | yield z =>
      apply forBudget P f k xs (j+1) z (inv x (by simp) j b z hb hv)
      · intro y hy i a hi ha
        apply step y (by simp [hy]) i a (by simp; omega) ha
      · intro y hy
        exact inv y (by simp [hy])
termination_by xs.length

private theorem growth_by {α β : Type} (w : β → Nat) (k : Nat)
    (f : α → β → Except Error (ForInStep β))
    (l : List α) (add : ∀ x ∈ l, ∀ b v, f x b = .ok v → w v.value ≤ w b + k)
    (a z : β) (ok : forIn l a f = .ok z) : w z ≤ w a + l.length*k := by
  induction l generalizing a with
  | nil => cases ok; simp
  | cons x xs ih =>
    rw [List.forIn_cons] at ok
    obtain ⟨v,hv,ok⟩ := bind_ok ok
    have hs := add x (by simp) _ _ hv
    cases v with
    | done y => cases ok; change w z ≤ w a + k at hs; simp [Nat.succ_mul]; omega
    | yield y =>
      have := ih (fun x hx => add x (by simp [hx])) y ok
      change w y ≤ w a + k at hs
      simp only [List.length_cons,Nat.succ_mul]; omega

private def ptrPayload (L : Limits) (mh : MainHeader) (d : ByteArray) :
    Account (pointerTables L mh d) (mh.pointers.size*(2+2*L.maxTileParts)) := by
  unfold pointerTables
  apply before
  rw [← Array.forIn_toList,← Array.length_toList (xs := mh.pointers)]
  apply forBudget (fun _ _ => True) _ _ _ 0 _ trivial
  · intro s _ i a _ _
    apply charge 2
    apply after
    intro body _
    split
    · exact before (tlmAccount ..)
    · exact free _ _
  · simp

/-- Sort checks and copied descriptor slots, allowing a full array copy per swap. -/
def sortBudget (n : Nat) := 4*n + (n+1)*(n*n+2*n)

private def sortAccount {α : Type} (key : α → UInt8) (loc : Location) (what : String)
    (xs : Array α) {n : Nat} (h : xs.size ≤ n) : Account (sortUnique key loc what xs) (sortBudget n) :=
  let m := HeaderWork.sortUnique_work key loc what xs
  ⟨((HeaderWork.measuredSortUnique key loc what xs).1,4*xs.size+(xs.size+1)*(HeaderWork.measuredSortUnique key loc what xs).2),
    m.1, Nat.add_le_add (Nat.mul_le_mul_left 4 h) (Nat.mul_le_mul (by omega)
      (Nat.le_trans m.2 (Nat.add_le_add (Nat.mul_le_mul h h) (Nat.mul_le_mul_left 2 h))))⟩

private theorem sorted_size {α : Type} {key : α → UInt8} {loc what} {xs ys : Array α}
    (h : sortUnique key loc what xs = .ok ys) : ys.Perm xs := by
  unfold sortUnique at h
  dsimp only at h
  split at h <;> cases h
  exact HeaderWork.insertionSort_perm ..

private def takeVisits : (xs : List ByteRange) → (n : Nat) → (a : Array ByteRange) →
    Option (Array ByteRange × List ByteRange) × Nat
  | [], n, a => (takeRanges [] n a,0)
  | x::xs, 0, a => (some (a,x::xs),0)
  | x::xs, n+1, a =>
    if n+1 < x.length then (takeRanges (x::xs) (n+1) a,3)
    else let t := takeVisits xs (n+1-x.length) (a.push x); (t.1,2+t.2)

private theorem take_work (xs : List ByteRange) (n : Nat) (a : Array ByteRange) :
    (takeVisits xs n a).1 = takeRanges xs n a ∧ (takeVisits xs n a).2 ≤ 3*xs.length := by
  induction xs generalizing n a with
  | nil => simp [takeVisits]
  | cons x xs ih =>
    cases n with
    | zero => simp [takeVisits,takeRanges]
    | succ n =>
      simp only [takeVisits,List.length_cons]
      split
      · exact ⟨rfl,by omega⟩
      · rename_i hn
        rw [takeRanges,ite_eq_right hn]
        refine ⟨(ih ..).1,?_⟩
        have := (ih (n+1-x.length) (a.push x)).2; omega

/-- Each PPM chunk attempt pays for *both* range walks, the four-byte length
gather and the temporary split descriptors. Failure in the second walk retains
the charge for the first. The limit guard precedes both walks. -/
def chunkPayload (L : Limits) (d : ByteArray) (loc : Location) (maxRanges : Nat) :
    (f : Nat) → (xs : List ByteRange) → (a : Array (Array ByteRange)) →
    xs.length ≤ maxRanges → Account (ppmChunks L d loc f xs a)
      ((L.maxTileParts-a.size+1)*(3+14*maxRanges))
  | _, [], _, _ => free _ _
  | 0, _::_, _, _ => free _ _
  | f+1, x::xs, a, hx => by
    rw [ppmChunks,Nat.succ_mul,Nat.add_comm (_*_)]
    apply widen (charge 1 (i := 2+14*maxRanges+(L.maxTileParts-a.size)*(3+14*maxRanges)) ?_) (by omega)
    apply after
    intro _ hc
    have lim : a.size+1 ≤ L.maxTileParts := check_limit hc
    let w := 3+14*maxRanges
    have room : L.maxTileParts-a.size = L.maxTileParts-(a.push #[]).size+1 := by
      rw [Array.size_push]; omega
    rw [room]
    have hfirst := take_work (x::xs) 4 #[]
    cases hn : takeRanges (x::xs) 4 #[]
    · apply billed _ (n := 1+(takeVisits (x::xs) 4 #[]).2)
      have := hfirst.2; omega
    rename_i pr
    obtain ⟨nb,rest⟩ := pr
    have ht := HeaderWork.takeRanges_account _ _ _ _ _ hn
    have nsize : nb.size ≤ maxRanges := Nat.le_trans (by simpa using ht.2.2.1) hx
    have remain := Nat.le_trans ht.2.2.2 hx
    have g := (HeaderWork.gather_copy_charge d nb).2
    have bytes := HeaderWork.ppmLength_copy hn (data := d)
    have gc := Nat.le_trans g (Nat.mul_le_mul nsize (Nat.mul_le_mul_left 2 bytes))
    let firstCost := 1+(takeVisits (x::xs) 4 #[]).2+(HeaderWork.chargedGather d nb.toList ByteArray.empty).2
    have hf : firstCost ≤ 1+11*maxRanges := by dsimp [firstCost]; have := hfirst.2; omega
    apply widen (seqAct (billed _ hf) (j := 1+3*maxRanges + (L.maxTileParts-(a.push #[]).size+1)*w) ?_)
      (by dsimp [w]; omega)
    rintro ⟨n,t⟩ _
    dsimp only
    have hs := (take_work rest n.toNat #[]).2
    let second := 1+(takeVisits rest n.toNat #[]).2
    have hsecond : second ≤ 1+3*maxRanges := by dsimp [second]; omega
    cases ht2 : takeRanges rest n.toNat #[]
    · exact billed _ (Nat.le_trans hsecond (Nat.le_add_right ..))
    · rename_i pr
      obtain ⟨chunk,tail⟩ := pr
      apply widen (charge second (chunkPayload L d loc maxRanges f tail (a.push chunk)
        (Nat.le_trans (HeaderWork.takeRanges_account _ _ _ _ _ ht2).2.2.2 remain))) ?_
      simp only [Array.size_push]; exact Nat.add_le_add_right hsecond _


/-- All main pointer stages, including the nested TLM array read, duplicate
sorts, the temporary PPM range list and failed Nppm/Ippm walks. -/
def pointerPayload (L : Limits) (mh : MainHeader) (d : ByteArray) :
    let n := mh.pointers.size
    Account (parsePointers L mh d) (n*(2+2*L.maxTileParts) + (sortBudget n +
      (sortBudget n + (3*n + (L.maxTileParts+1)*(3+14*n))))) := by
  let n := mh.pointers.size
  let loc := Location.atOffset .marker mh.endPos
  have eq : parsePointers L mh d = (do
    let (ts,ps,_) ← pointerTables L mh d
    let ts ← sortUnique TLM.ztlm loc "Ztlm" ts
    let ps ← sortUnique PPM.zppm loc "Zppm" ps
    finishPointers L d loc ts ps) := by
    unfold parsePointers pointerTables; simp only [bind_assoc,pure_bind]; rfl
  rw [eq]
  apply seqAct (ptrPayload ..)
  rintro ⟨ts,ps,z⟩ hz
  have hs := table_sizes hz
  change ts.size + ps.size ≤ n at hs
  apply seqAct (sortAccount _ _ _ ts (n := n) (by omega))
  intro ts' _
  apply seqAct (sortAccount _ _ _ ps (n := n) (by omega))
  intro ps' hsort
  have hn := (sorted_size hsort).size_eq
  unfold finishPointers
  apply widen (charge (3*ps'.size) (before (chunkPayload L d loc n _ _ #[] (by simp; omega)))) ?_
  simp only [Array.size_empty,Nat.sub_zero]
  dsimp [n] at hs ⊢
  omega

private def concatData {α β : Type} (f : α → Array β) : List α → Array β → Array β × Nat
  | [], a => (a,0)
  | x::xs, a =>
    let z := a ++ f x
    let t := concatData f xs z
    (t.1,1+z.size+t.2)

private theorem concat_data {α β : Type} (f : α → Array β) (xs : List α) (a : Array β)
    (k : Nat) (hk : ∀ x ∈ xs, (f x).size ≤ k) :
    let t := concatData f xs a
    t.1 = xs.foldl (fun a x => a ++ f x) a ∧ t.1.size ≤ a.size+xs.length*k ∧
    t.2 ≤ xs.length*(1+a.size+xs.length*k) := by
  induction xs generalizing a with
  | nil => simp [concatData]
  | cons x xs ih =>
    obtain ⟨e,sz,w⟩ := ih (a ++ f x) (fun y hy => hk y (by simp [hy]))
    have hx := hk x (by simp)
    have hd : (a ++ f x).size + xs.length*k ≤ a.size+(xs.length+1)*k := by
      simp only [Array.size_append,Nat.succ_mul]; omega
    have hstep : 1+(a ++ f x).size ≤ 1+a.size+(xs.length+1)*k := by
      simp only [Array.size_append,Nat.succ_mul]; omega
    have hcost := Nat.mul_le_mul_left xs.length (Nat.add_le_add_left hd 1)
    simp only [concatData,List.length_cons,List.foldl_cons]
    refine ⟨e,Nat.le_trans sz hd,?_⟩
    rw [Nat.succ_mul xs.length (1+_+_),Nat.add_comm (xs.length*_)]
    apply Nat.add_le_add hstep
    apply Nat.le_trans w
    simpa only [Nat.add_assoc] using hcost

private def pltShapes (n : Nat) (p : TilePartHeader) : Prop :=
  p.segments.size ≤ n ∧ ∀ q ∈ plts p, q.lengths.size ≤ n

/-- PLT extraction, per-part sorting and cumulative length-array copying. -/
def partBudget (n : Nat) := 2*n + (sortBudget n + n*(1+n*n))

private def partPayload (p : TilePartHeader) (n : Nat) (hp : pltShapes n p) :
    Account (partPlt p) (partBudget n) := by
  unfold partPlt partBudget
  have len : (plts p).size ≤ n := Nat.le_trans Array.size_filterMap_le hp.1
  apply widen (charge (2*p.segments.size) (i := sortBudget n+n*(1+n*n)) ?_) (by have := hp.1; omega)
  apply seqAct (sortAccount _ _ _ (plts p) len)
  intro sorted hs
  have perm := sorted_size hs
  have hl := Nat.le_trans (Nat.le_of_eq perm.size_eq) len
  have hq : ∀ q ∈ sorted.toList, q.lengths.size ≤ n := by
    intro q hq
    exact hp.2 q ((Array.Perm.mem_iff perm).1 (by simpa using hq))
  let m := concatData PLT.lengths sorted.toList #[]
  have ⟨er,_,cost⟩ := concat_data PLT.lengths sorted.toList #[] n hq
  exact ⟨(.ok m.1,m.2),by simp only [Array.foldl_toList] at er; rw [show m.1 = _ from er]; rfl,
    by simpa using Nat.le_trans cost (Nat.mul_le_mul (by simpa using hl) (Nat.add_le_add_left
      (Nat.mul_le_mul_right n (by simpa using hl)) 1))⟩

private theorem part_width {p : TilePartHeader} {n : Nat} (hp : pltShapes n p) {a : Array Nat}
    (ok : partPlt p = .ok a) : a.size ≤ n*n := by
  unfold partPlt at ok
  obtain ⟨s,hs,ok⟩ := bind_ok ok
  cases ok
  have perm := sorted_size hs
  have len : s.size ≤ n := Nat.le_trans (Nat.le_of_eq perm.size_eq) (Nat.le_trans Array.size_filterMap_le hp.1)
  have ⟨er,sz,_⟩ := concat_data PLT.lengths s.toList #[] n (fun q hq =>
    hp.2 q (perm.mem_iff.1 (by simpa using hq)))
  rw [er,Array.foldl_toList] at sz
  exact Nat.le_trans (by simpa using sz) (Nat.mul_le_mul_right _ len)

private def joinParts (ps : List TilePartHeader) (a : Array Nat) (n : Nat)
    (hp : ∀ p ∈ ps, pltShapes n p) :
    Account (ps.foldlM (fun a p => do return a ++ (← partPlt p)) a)
      (ps.length*(partBudget n+1+a.size+ps.length*(n*n))) := by
  cases ps with
  | nil => exact free _ _
  | cons p ps =>
    rw [List.foldlM_cons]
    have head := hp p (by simp)
    have tail : ∀ q ∈ ps, pltShapes n q := fun q hq => hp q (by simp [hq])
    simp only [bind_assoc,pure_bind]
    apply widen (seqAct (partPayload p n head)
      (j := 1+a.size+n*n+ps.length*(partBudget n+1+a.size+(ps.length+1)*(n*n))) ?_) ?_
    · intro z hz
      have sz := part_width head hz
      apply widen (charge (1+(a++z).size) (joinParts ps (a++z) n tail)) ?_
      simp only [Array.size_append]
      apply Nat.add_le_add (by omega)
      apply Nat.mul_le_mul_left
      rw [Nat.succ_mul]; omega
    · rw [List.length_cons,Nat.succ_mul ps.length (_+_)]
      have h := Nat.le_add_left (ps.length*(n*n)) (n*n)
      simp only [Nat.succ_mul] at *; omega
termination_by ps.length

/-- Tile-wide PPT and per-part PLT work for at most `p` parts with widths at most `n`. -/
def tileBudget (p n : Nat) := p + p*(2*n) + p*(1+p*n) + sortBudget (p*n) +
  (p*(partBudget n+1+p*(n*n)) + p*n)

private def segmentCount (ps : Array TilePartHeader) := ps.foldl (fun n p => n+p.segments.size) 0

private theorem segment_count (ps : Array TilePartHeader) (n : Nat)
    (hn : ∀ p ∈ ps, p.segments.size ≤ n) : segmentCount ps ≤ ps.size*n := by
  unfold segmentCount
  rw [← Array.foldl_toList,← Array.length_toList (xs := ps)]
  replace hn : ∀ p ∈ ps.toList, p.segments.size ≤ n := by simpa using hn
  generalize ps.toList = l at *
  suffices ∀ a, l.foldl (fun b p => b+p.segments.size) a ≤ a+l.length*n by simpa using this 0
  induction l with
  | nil => simp
  | cons p l ih =>
    intro a
    rw [List.foldl_cons,List.length_cons,Nat.succ_mul]
    have := ih (fun x hx => hn x (by simp [hx])) (a+p.segments.size)
    have := hn p (by simp); omega

private def tilePayload (corr : Bool) (i : Nat) (ps : Array TilePartHeader) (n : Nat)
    (hp : ∀ p ∈ ps, pltShapes n p) : Account (assembleTile corr i ps) (tileBudget ps.size n) := by
  unfold assembleTile
  change Account (if declaredParts corr ps ≠ 0 ∧ declaredParts corr ps ≠ ps.size then _ else _) _
  split
  · exact billed _ (n := ps.size) (by unfold tileBudget; omega)
  let choose := fun p : TilePartHeader => p.segments.filterMap (fun | .ppt x => some x | _ => none)
  let m := concatData choose ps.toList #[]
  have ⟨_,_,wc⟩ := concat_data choose ps.toList #[] n (fun p hm =>
    Nat.le_trans Array.size_filterMap_le (hp p (by simpa using hm)).1)
  have hsum : m.2 ≤ ps.size*(1+ps.size*n) := by simpa using wc
  have hlen := ppt_size ps n (fun p hm => (hp p hm).1)
  have scans := segment_count ps n (fun p hm => (hp p hm).1)
  have twice : 2*segmentCount ps ≤ ps.size*(2*n) := by
    rw [← Nat.mul_assoc, Nat.mul_comm ps.size 2, Nat.mul_assoc]
    exact Nat.mul_le_mul_left 2 scans
  apply widen (charge (ps.size+2*segmentCount ps+m.2) (i := sortBudget (ps.size*n)+
    (ps.size*(partBudget n+1+ps.size*(n*n)) + ps.size*n)) ?_) (by unfold tileBudget; omega)
  apply seqAct (sortAccount _ _ _ (ppts ps) hlen)
  intro s hs
  rw [← Array.foldlM_toList]
  apply seqAct (widen (joinParts ps.toList #[] n (by simpa using hp)) (by simp))
  intro _ _
  exact billed _ (n := s.size) (Nat.le_trans (Nat.le_of_eq (sorted_size hs).size_eq) hlen)

private theorem varint_size (f c : Nat) (p : Bool) (a z : Array Nat) (r : Reader)
    (ok : readVarints f c p a r = .ok z) : z.size ≤ a.size+f := by
  induction f generalizing c a r p with
  | zero => simp only [readVarints] at ok; split at ok <;> cases ok; omega
  | succ f ih =>
    rw [readVarints] at ok
    split at ok <;> try contradiction
    dsimp only at ok
    split at ok <;> try contradiction
    split at ok
    · exact Nat.le_trans (ih _ _ _ _ ok) (by omega)
    · exact Nat.le_trans (ih _ _ _ _ ok) (by simp; omega)

private theorem parsed_plt {r : Reader} {p : PLT} (ok : parsePLT r = .ok p) :
    p.lengths.size ≤ r.data.size := by
  unfold parsePLT at ok
  obtain ⟨⟨_,t⟩,ht,ok⟩ := bind_ok ok
  obtain ⟨a,ha,ok⟩ := bind_ok ok
  cases ok
  have h := varint_size _ _ _ _ _ _ ha
  have h' := rem_le t
  rw [(Reader.u8_pos ht).2.2.1] at h'
  simpa using Nat.le_trans h (by simpa using h')

private theorem poc_width {L : Limits} {c : Nat} {b : Reader} {p : POC}
    (ok : parsePOC L c b = .ok p) : p.entries.size ≤ b.data.size := by
  unfold parsePOC at ok
  iterate 2 obtain ⟨_,_,ok⟩ := bind_ok ok
  obtain ⟨⟨a,t⟩,ha,ok⟩ := bind_ok ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  cases ok
  have sz := array_size _ _ _ _ ha
  have hn := Nat.le_trans (Nat.div_le_self b.remaining (pocEntrySize c)) (rem_le b)
  simpa using Nat.le_trans (Nat.le_of_eq sz) (by simpa using hn)

private def segmentEntries : TileSegment → Nat
  | .poc p => p.entries.size
  | .plt p => p.lengths.size
  | _ => 0

private def lengthsFit (n : Nat) (ss : Array TileSegment) := ∀ s ∈ ss, segmentEntries s ≤ n

private theorem lengths_add {L : Limits} {c : Nat} {first ppm : Bool} {a z : TPAcc}
    {m : UInt16} {b : Reader} (ha : lengthsFit b.data.size a.segments)
    (h : addTileSegment L c first ppm a m b = .ok z) : lengthsFit b.data.size z.segments := by
  unfold addTileSegment at h
  repeat' first | (split at h <;> try contradiction) | (obtain ⟨_,_,h⟩ := bind_ok h)
  all_goals cases h; intro p hp; rcases Array.mem_push.1 hp with old | rfl
  all_goals first | exact ha _ old | exact Nat.zero_le _ | exact parsed_plt (by assumption) | exact poc_width (by assumption)

private theorem lengths_loop {L : Limits} {c f : Nat} {first ppm : Bool} {a z : TPAcc} {r t : Reader}
    (ha : lengthsFit r.data.size a.segments)
    (h : TilePart.headerLoop L c first ppm f a r = .ok (z,t)) : lengthsFit r.data.size z.segments := by
  induction f generalizing a r with
  | zero => cases h
  | succ f ih =>
    rw [TilePart.headerLoop] at h
    split at h <;> try contradiction
    rename_i m r1 hr
    have hd := (Reader.u16be_pos hr).2.2.1
    split at h
    · cases h; exact ha
    split at h <;> try contradiction
    split at h
    · rw [← hd]; apply ih _ h; simpa only [hd] using ha
    split at h <;> try contradiction
    split at h <;> try contradiction
    rename_i b len r2 hs
    have he := HeaderWork.readSegment_extent hs
    dsimp only at h
    split at h <;> try contradiction
    rename_i a' haz
    rw [← he.2.1.trans hd]
    apply ih _ h
    rw [he.2.1,← he.1]
    apply lengths_add _ haz
    simpa only [he.1,hd] using ha

private def tableFits (L : Limits) (bytes : Nat) (ps : Array TilePartHeader) :=
  ps.size ≤ L.maxTilePartsPerTile ∧ ∀ p ∈ ps, pltShapes (bytes+1) p ∧ lengthsFit bytes p.segments

private theorem modify_mem {α : Type} {P : α → Prop} {a : Array α} {i : Nat} {f : α → α}
    (ha : ∀ x ∈ a, P x) (hf : ∀ x, a[i]? = some x → P (f x)) : ∀ x ∈ a.modify i f, P x := by
  intro x hx
  obtain ⟨j,hj,rfl⟩ := Array.mem_iff_getElem.1 hx
  have hj' : j < a.size := by simpa using hj
  rw [Array.getElem_modify]
  split
  · rename_i h; subst j; exact hf _ (Array.getElem?_eq_getElem hj')
  · exact ha _ (Array.getElem_mem hj')

private theorem table_step {c : Ctx} {r t : Reader} {a z : State}
    (ha : ∀ ps ∈ a.parts, tableFits c.limits r.data.size ps)
    (ok : readTilePart c a r = .ok (z,t)) : ∀ ps ∈ z.parts, tableFits c.limits r.data.size ps := by
  unfold readTilePart at ok
  obtain ⟨⟨_,r1⟩,h1,ok⟩ := bind_ok ok
  obtain ⟨⟨_,_,r2⟩,h2,ok⟩ := bind_ok ok
  obtain ⟨sot,_,ok⟩ := bind_ok ok
  iterate 2 obtain ⟨_,_,ok⟩ := bind_ok ok
  obtain ⟨_,hc,ok⟩ := bind_ok ok
  iterate 3 obtain ⟨_,_,ok⟩ := bind_ok ok
  dsimp only at ok
  split at ok <;> split at ok <;> try contradiction
  all_goals
    simp only [pure_bind] at ok
    obtain ⟨⟨tp,_⟩,ht,ok⟩ := bind_ok ok
    obtain ⟨⟨acc,rd⟩,hl,ok⟩ := bind_ok ok
    cases ok
    have de := (Reader.take_spec ht).2.2.1.trans
      ((HeaderWork.readSegment_extent h2).2.1.trans (Reader.u16be_pos h1).2.2.1)
    have len := lengths_loop (a := _) (by intro _ h; simp at h) hl
    have slots := (HeaderWork.tileHeaderLoop_storage hl).1
    change acc.markers.size + acc.segments.size + rd.remaining ≤ 1+0+tp.remaining at slots
    have rem := rem_le tp
    rw [de] at rem len
    intro ps hp
    dsimp only at hp
    refine modify_mem ha ?_ ps hp
    intro ys hy
    have checked := check_limit hc
    rw [hy] at checked
    refine ⟨by simpa [Limits.bound] using checked,?_⟩
    intro p hp
    rcases Array.mem_push.1 hp with old | rfl
    · exact (ha ys (Array.mem_of_getElem? hy)).2 _ old
    · refine ⟨⟨by dsimp only; omega,?_⟩,len⟩
      intro q hq
      obtain ⟨s,hs,he⟩ := Array.mem_filterMap.1 hq
      cases s <;> cases he
      exact Nat.le_trans (len _ hs) (Nat.le_succ _)

private theorem loop_tables {c : Ctx} {r : Reader} {a z : State} {f : Nat}
    (ha : ∀ ps ∈ a.parts, tableFits c.limits r.data.size ps)
    (ok : tilePartLoop c f a r = .ok z) : ∀ ps ∈ z.parts, tableFits c.limits r.data.size ps := by
  induction f generalizing a r with
  | zero => cases ok
  | succ f ih =>
    rw [tilePartLoop] at ok
    split at ok <;> try contradiction
    split at ok
    · cases ok; exact ha
    split at ok <;> try contradiction
    split at ok <;> try contradiction
    rename_i a' r' hs
    have hd := (HeaderWork.readTilePart_step hs).2.2.2.1
    rw [← hd]; apply ih _ ok; rw [hd]; exact table_step ha hs

/-- TNsot scans and one tile-part header inside a buffer of `b` bytes. -/
def readPartBudget (c : Ctx) (b : Nat) :=
  4+3*c.limits.maxTilePartsPerTile + b*(3+markerBudget c.limits c.csiz b)

private def readPartPayload (c : Ctx) (a : State) (r : Reader) :
    Account (readTilePart c a r) (readPartBudget c r.data.size+a.parts.size) := by
  unfold readTilePart
  apply after; rintro ⟨_,r1⟩ h1
  apply after; rintro ⟨_,_,r2⟩ h2
  apply after; intro sot _
  iterate 2 (apply after; intro _ _)
  apply after
  intro _ hprev
  have sz : (a.parts[sot.isot.toNat]?.getD #[]).size+1 ≤ c.limits.maxTilePartsPerTile := check_limit hprev
  iterate 2 (apply after; intro _ _)
  let p := (a.parts[sot.isot.toNat]?.getD #[]).size
  let n := r.data.size
  apply widen (charge (4+p) (i := n*(3+markerBudget c.limits c.csiz n)+(2*p+a.parts.size)) ?_)
    (by unfold readPartBudget; dsimp [p,n]; omega)
  apply after
  intro _ _
  dsimp only
  split <;> split
  all_goals try simp only [pure_bind]
  all_goals try (apply after (s := throw _); intro _ h; cases h)
  all_goals
      apply after (s := Reader.take _ _)
      rintro ⟨tp,_⟩ ht
      have de := (Reader.take_spec ht).2.2.1.trans
        ((HeaderWork.readSegment_extent h2).2.1.trans (Reader.u16be_pos h1).2.2.1)
      apply seqAct (widen (tileHeaderPayload ..) ?_)
      · intro _ _
        exact billed _ (n := (if sot.tnsot ≠ 0 then 0 else p)+p+a.parts.size) (by split <;> omega)
      · dsimp only [n]; rw [de]; exact Nat.mul_le_mul_right _ (by simpa only [de] using rem_le tp)


private theorem row_count {c : Ctx} {a z : State} {r t : Reader} (h : readTilePart c a r = .ok (z,t)) :
    z.parts.size = a.parts.size := by
  unfold readTilePart at h
  iterate 3 obtain ⟨_,_,h⟩ := bind_ok h
  iterate 6 obtain ⟨_,_,h⟩ := bind_ok h
  dsimp only at h
  split at h <;> split at h <;> try contradiction
  all_goals simp only [pure_bind] at h
  all_goals repeat' obtain ⟨_,_,h⟩ := bind_ok h
  all_goals cases h; simp

private def partsPayload (c : Ctx) : (f : Nat) → (a : State) → (r : Reader) →
    Account (tilePartLoop c f a r) ((c.limits.maxTileParts-a.total+1)*(1+(readPartBudget c r.data.size+a.parts.size)))
  | 0, _, _ => free _ _
  | f+1, a, r => by
    rw [Nat.succ_mul,Nat.add_comm (_*_)]
    apply widen (charge 1 (i := readPartBudget c r.data.size+a.parts.size +
      (c.limits.maxTileParts-a.total)*(1+(readPartBudget c r.data.size+a.parts.size))) ?_) (by omega)
    rw [tilePartLoop]
    split
    · exact free _ _
    split
    · exact free _ _
    split
    · exact free _ _
    apply pay (readPartPayload c a r)
    split
    · exact free _ _
    rename_i a' t hs
    have h := HeaderWork.readTilePart_step hs
    apply widen (partsPayload c f a' t)
    rw [h.2.2.2.1,row_count hs]
    exact Nat.mul_le_mul_right _ (by omega)

private theorem tileBudget_mono {p q n : Nat} (hp : p ≤ q) : tileBudget p n ≤ tileBudget q n := by
  unfold tileBudget sortBudget
  repeat' first | assumption | exact Nat.le_refl _ | apply Nat.add_le_add | apply Nat.mul_le_mul

private def assemblyWalk (L : Limits) (corr : Bool) (ps : Array (Array TilePartHeader)) (b : Nat)
    (hp : ∀ a ∈ ps, tableFits L b a) (visit cap : Nat)
    (each : ∀ i row, tableFits L b row → Account (assembleTile corr i row) cap) : (f i packets : Nat) → (out : Array Tile) →
    Account (assembleTiles L corr ps f i packets out) (f*(visit+cap))
  | 0, _, _, _ => free _ _
  | f+1, i, packets, out => by
    rw [Nat.succ_mul,Nat.add_comm (f*_),Nat.add_assoc]
    apply charge visit
    rw [assembleTiles]
    dsimp only
    split
    · apply widen (assemblyWalk L corr ps b hp visit cap each f _ _ _)
      exact Nat.le_add_left ..
    · rename_i nonempty
      have hrow : tableFits L b (ps[i]?.getD #[]) := by
        cases h : ps[i]? with
        | none => simp [h] at nonempty
        | some row => exact hp _ (Array.mem_of_getElem? h)
      apply pay (each i _ hrow)
      split
      · exact free _ _
      split
      · exact free _ _
      · exact assemblyWalk L corr ps b hp visit cap each f _ _ _

private def assemblyPayload (L : Limits) (corr : Bool) (ps : Array (Array TilePartHeader)) (b : Nat)
    (hp : ∀ a ∈ ps, tableFits L b a) :=
  assemblyWalk L corr ps b hp 2 (tileBudget L.maxTilePartsPerTile (b+1))
    fun i row h => widen (tilePayload corr i row _ (fun p hm => (h.2 p hm).1)) (tileBudget_mono h.1)

/-- The complete tile-part driver. Every attempted SOT can rescan the previous
parts for TNsot consistency and scan them again for inherited TNsot. Assembly
charges a full copy at each PPT/PLT append, including the tile whose packet
limit rejects *after* the length arrays have been concatenated. -/
def tilePartsPayload (L : Limits) (mh : MainHeader) (r : Reader) :
    let b := r.data.size
    let c : Ctx := { limits := L, csiz := mh.siz.csiz, numTiles := numTiles mh.siz,
                     ppm := mh.pointers.any (·.code == Code.PPM) }
    Account (parseTileParts L mh r) (L.maxTiles+mh.pointers.size+mh.poc.size +
      ((L.maxTileParts+1)*(1+(readPartBudget c b+L.maxTiles)) + L.maxTiles*(2+tileBudget L.maxTilePartsPerTile (b+1)))) := by
  unfold parseTileParts
  apply after
  intro _ h
  have bound : numTiles mh.siz ≤ L.maxTiles := check_limit h
  apply widen (charge (numTiles mh.siz+mh.pointers.size+mh.poc.size) (i := _) ?_) (Nat.add_le_add_right (by omega) _)
  apply seqAct (widen (partsPayload ..) (by
    simp only [Nat.sub_zero,Array.size_replicate]; apply Nat.mul_le_mul_left
    exact Nat.add_le_add_left (Nat.add_le_add_left bound _) 1))
  intro st hl
  apply widen (assemblyPayload _ _ _ _ ?_ _ _ _ _) (Nat.mul_le_mul_right _ bound)
  apply loop_tables _ hl
  intro ps hp
  obtain ⟨_,rfl⟩ := Array.mem_replicate.1 hp
  simp [tableFits]

/-! ## Packed-header selection and PPM rank tables -/

private theorem push_size (a : Array ByteRange) (r : ByteRange) :
    (Tier2.Packet.pushRange a r).size ≤ a.size+1 := by
  unfold Tier2.Packet.pushRange
  split
  · omega
  split
  · split <;> simp
  · simp

/-- Range validation, coalescing and full-copy byte gathering. -/
def gatherBudget (k bytes : Nat) := k*(2+k) + k*(2*(k*bytes))

private def gatherPayload (ppm : Bool) (d : ByteArray) (rs : Array ByteRange)
    (k : Nat) (h : rs.size ≤ k) : Account (gather ppm d rs) (gatherBudget k d.size) := by
  unfold gather gatherBudget
  apply seqAct
  · rw [← Array.forIn_toList]
    apply widen (forBudget (fun i a => a.size ≤ i) _ (2+k) _ 0 _ (by simp) ?_ ?_)
      (Nat.mul_le_mul_right _ (by simpa using h))
    · intro r _ i a hi ha
      split
      · exact billed _ (n := 1) (by omega)
      · exact billed _ (n := 1+(Tier2.Packet.pushRange a r).size) (by
          have := push_size a r; simp at hi; omega)
    · intro r _ i a z ha hz
      split at hz <;> cases hz
      exact Nat.le_trans (push_size ..) (by omega)
  · intro merged hm
    rw [← Array.forIn_toList] at hm
    have hg := growth Array.size _ (fun r a v hv => by
      split at hv <;> cases hv
      exact push_size ..) _ _ _ hm
    simp only [Array.size_empty,Nat.zero_add,Array.length_toList] at hg
    have hw := HeaderWork.gather_copy_charge d merged
    have sz := (HeaderWork.gatherBytes_size d merged).2
    exact ⟨(.ok { fromPpm := ppm, ranges := merged, bytes := (HeaderWork.chargedGather d merged.toList ByteArray.empty).1 },
      (HeaderWork.chargedGather d merged.toList ByteArray.empty).2), by rw [hw.1]; rfl,
      Nat.le_trans hw.2 (Nat.mul_le_mul (Nat.le_trans hg h) (Nat.mul_le_mul_left 2
        (Nat.le_trans sz (Nat.mul_le_mul_right _ (Nat.le_trans hg h)))))⟩

private theorem mem_sum {α : Type} (xs : List (Array α)) (x : Array α) (hx : x ∈ xs) :
    x.size ≤ (xs.map Array.size).sum := by
  induction xs with
  | nil => cases hx
  | cons y ys ih =>
    rcases List.mem_cons.1 hx with rfl | h <;> simp only [List.map_cons,List.sum_cons]
    · omega
    · have := ih h; omega

/-- Packed-header selection budget. Repeated ranks are charged independently.
The selector may copy the entire accumulated descriptor array on every append. -/
def selectionBudget (L : Limits) (bytes : Nat) :=
  let k := L.maxTilePartsPerTile*(L.maxTileParts*bytes) + L.maxTilePartsPerTile*(bytes+1)
  L.maxTilePartsPerTile*(2+k) + gatherBudget k bytes

/-- Cost of headerStreamAt on any parsed tile, including missing ranks, missing
chunks, a bad range in the middle of the gather and inline headers. -/
def selectPayload {L : Limits} {h : Header} {d : ByteArray} {tp : TileParams}
    (parsed : Header.parse L d = .ok h) (member : tp ∈ h.tiles) (ranks : Array Nat) :
    Account (headerStreamAt h d tp ranks) (selectionBudget L d.size) := by
  obtain ⟨parts,ppt,_⟩ := HeaderWork.parse_tile_storage parsed tp member
  have widths := (HeaderWork.parse_ppm parsed).2.2
  let w := L.maxTileParts*d.size
  let k := L.maxTilePartsPerTile*w+L.maxTilePartsPerTile*(d.size+1)
  have cw : ∀ x ∈ h.ppm.chunks, x.size ≤ w := fun x hx =>
    Nat.le_trans (mem_sum _ x (by simpa using hx)) widths
  unfold headerStreamAt
  dsimp only
  split
  · split
    · exact free _ _
    unfold selectionBudget
    apply seqAct
    · rw [Std.Legacy.Range.forIn_eq_forIn_range']
      apply widen (forBudget (fun i (a : Array ByteRange) => a.size ≤ i*w) _ (2+k) _ 0 _ (by simp) ?_ ?_) ?_
      · intro index _ i a hi ha
        have hn : i+1 ≤ L.maxTilePartsPerTile := by
          simp [Std.Legacy.Range.size] at hi; omega
        split
        · split
          · rename_i chunk hc
            have hw := cw chunk (Array.mem_of_getElem? hc)
            apply billed _ (n := 2+a.size+chunk.size)
            have := Nat.mul_le_mul_right w hn
            rw [Nat.succ_mul] at this; dsimp [k]; omega
          · exact billed _ (n := 2) (by omega)
        · exact billed _ (n := 1) (by omega)
      · intro _ _ i a z ha hz
        split at hz <;> try contradiction
        split at hz <;> try contradiction
        rename_i chunk hc
        cases hz
        have hh := cw chunk (Array.mem_of_getElem? hc)
        simp only [Array.size_append,Nat.succ_mul]; omega
      · apply Nat.mul_le_mul_right; simpa [Std.Legacy.Range.size] using parts
    · intro rs hrs
      rw [Std.Legacy.Range.forIn_eq_forIn_range'] at hrs
      have hg := growth_by Array.size w _ _ (fun _ _ a v hv => by
        split at hv <;> try contradiction
        split at hv <;> try contradiction
        rename_i chunk hc
        cases hv
        simpa only [ForInStep.value,Array.size_append] using Nat.add_le_add_left (cw chunk (Array.mem_of_getElem? hc)) a.size) _ _ hrs
      simp [Std.Legacy.Range.size] at hg
      apply before; apply gatherPayload
      have := Nat.mul_le_mul_right w parts
      change rs.size ≤ k; dsimp [k]; omega
  · split
    · apply before; apply widen (gatherPayload _ _ _ k (by dsimp [k]; omega))
      exact Nat.le_add_left ..
    · exact free _ _

private theorem row_shape (a : Array (Array Nat)) (j k v : Nat) :
    (a.modify j (·.setIfInBounds k v)).map Array.size = a.map Array.size := by
  apply Array.ext
  · simp
  · intro i hi hj
    simp only [Array.getElem_map,Array.getElem_modify]
    split <;> simp

private theorem rank_fold (xs : List ((Nat × Nat × Nat) × Nat)) (a : Array (Array Nat)) :
    (xs.foldl (fun acc ((_,j,k),rank) => acc.modify j (·.setIfInBounds k rank)) a).map Array.size =
      a.map Array.size := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨⟨_,j,k⟩,v⟩ := x
    rw [List.foldl_cons,ih,row_shape]

/-- Every index row has exactly one slot per part of its tile. The same shape
holds at every intermediate prefix of the rank-writing fold. -/
theorem rank_table (h : Header) : (streamRanks h).map Array.size =
    h.tiles.map (fun tp => tp.tile.parts.size) := by
  unfold streamRanks
  rw [rank_fold]
  simp [Function.comp_def]

private theorem assembled_count {L : Limits} {corr : Bool} {ps : Array (Array TilePartHeader)}
    {f i packets : Nat} {a z : Array Tile} (ok : assembleTiles L corr ps f i packets a = .ok z) :
    z.size ≤ a.size+f := by
  induction f generalizing i packets a with
  | zero => cases ok; simp
  | succ f ih =>
    rw [assembleTiles] at ok
    dsimp only at ok
    split at ok
    · have := ih ok; omega
    · split at ok <;> try contradiction
      split at ok <;> try contradiction
      have := ih ok
      simp only [Array.size_push] at this
      omega

private theorem map_count {α β : Type} (f : α → Except Error β) {xs : Array α} {ys : Array β}
    (ok : xs.mapM f = .ok ys) : ys.size = xs.size := by
  have len (l : List α) (out : List β) (ok : l.mapM f = .ok out) : out.length = l.length := by
    induction l generalizing out with
    | nil => cases ok; rfl
    | cons x l ih =>
      rw [List.mapM_cons] at ok
      obtain ⟨_,_,ok⟩ := bind_ok ok
      obtain ⟨a,ha,ok⟩ := bind_ok ok
      cases ok; simp [ih a ha]
  rw [Array.mapM_eq_mapM_toList] at ok
  cases hm : xs.toList.mapM f with
  | error => rw [hm] at ok; cases ok
  | ok l => rw [hm] at ok; cases ok; simpa using len _ _ hm

private theorem parsed_tiles {L : Limits} {d : ByteArray} {h : Header} (ok : Header.parse L d = .ok h) :
    h.tiles.size ≤ L.maxTiles := by
  unfold Header.parse at ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  unfold parseCodestreamIn at ok
  iterate 5 obtain ⟨_,_,ok⟩ := bind_ok ok
  obtain ⟨ts,tiles,ok⟩ := bind_ok ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  obtain ⟨tps,hm,ok⟩ := bind_ok ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  cases ok
  unfold parseTileParts at tiles
  obtain ⟨_,hc,tiles⟩ := bind_ok tiles
  obtain ⟨_,_,tiles⟩ := bind_ok tiles
  have ct := assembled_count tiles
  have ht := map_count _ hm
  exact Nat.le_trans (Nat.le_of_eq ht) (Nat.le_trans (by simpa using ct) (check_limit hc))

/-- PPM rank construction is reached once before the public grid. The preflight
scans tile headers even if the chunk count rejects. Triple lists, indexed lists,
rank rows and a full outer/inner array copy per update are included. -/
def rankBudget (L : Limits) :=
  L.maxTiles + (8*(L.maxTiles+L.maxTileParts) +
    (L.maxTileParts+8*(L.maxTileParts*L.maxTileParts)+1) +
    L.maxTileParts*(1+L.maxTiles+L.maxTileParts))

private theorem parts_sum (h : Header) : (h.tiles.toList.map (fun t => t.tile.parts.size)).sum = numTileParts h := by
  unfold numTileParts
  rw [← Array.foldl_toList]
  generalize h.tiles.toList = l
  suffices aux : ∀ a, a+(l.map (fun t => t.tile.parts.size)).sum =
      l.foldl (fun a t => a+t.tile.parts.size) a by simpa using aux 0
  induction l with
  | nil => simp
  | cons x xs ih => intro a; simp only [List.map_cons,List.sum_cons,List.foldl_cons,← ih,Nat.add_assoc]

/-- Row and rank slots retained by the actual public PPM preflight. An empty
PPM directory retains an empty rank table even when the header has tiles. -/
theorem rank_storage {L : Limits} {h : Header} {d : ByteArray} {idx : Array (Array Nat)}
    (hp : Header.parse L d = .ok h)
    (ok : (if h.ppm.segments.isEmpty then pure #[] else ppmChunkIndex L h) = .ok idx) :
    idx.size ≤ L.maxTiles ∧ (idx.map Array.size).toList.sum ≤ L.maxTileParts := by
  split at ok
  · cases ok
    simp
  unfold ppmChunkIndex at ok
  obtain ⟨_,quota,ok⟩ := bind_ok ok
  split at ok <;> try contradiction
  cases ok
  have outer := congrArg Array.size (rank_table h)
  have inner := parts_sum h
  rw [rank_table]
  refine ⟨Nat.le_trans (by simpa only [Array.size_map] using Nat.le_of_eq outer) (parsed_tiles hp),?_⟩
  exact Nat.le_trans (Nat.le_of_eq (by simpa using inner)) (check_limit quota)

private def rankWrites (xs : List ((Nat × Nat × Nat) × Nat)) (a : Array (Array Nat)) :
    Array (Array Nat) × Nat :=
  match xs with
  | [] => (a,0)
  | ((_,j,k),v)::ys =>
    let z := a.modify j (·.setIfInBounds k v)
    let tail := rankWrites ys z
    (tail.1,1+a.size+(a[j]?.getD #[]).size+tail.2)

private theorem rank_writes (xs : List ((Nat × Nat × Nat) × Nat)) (a : Array (Array Nat)) (r c : Nat)
    (rows : a.size ≤ r) (cells : (a.map Array.size).toList.sum ≤ c) :
    (rankWrites xs a).1 = xs.foldl (fun a ((_,j,k),v) => a.modify j (·.setIfInBounds k v)) a ∧
    (rankWrites xs a).2 ≤ xs.length*(1+r+c) := by
  induction xs generalizing a with
  | nil => simp [rankWrites]
  | cons x xs ih =>
    obtain ⟨⟨_,j,k⟩,v⟩ := x
    have sz : (a[j]?.getD #[]).size ≤ c := by
      cases h : a[j]? with
      | none => simp
      | some row =>
        apply Nat.le_trans _ cells
        simpa using mem_sum a.toList row (by simpa using Array.mem_of_getElem? h)
    have ⟨er,hc⟩ := ih (a.modify j (·.setIfInBounds k v)) (by simpa using rows)
      (by rw [row_shape]; exact cells)
    refine ⟨er,?_⟩
    change 1+a.size+(a[j]?.getD #[]).size+_ ≤ (xs.length+1)*(1+r+c)
    rw [Nat.succ_mul,Nat.add_comm (xs.length*_)]; exact Nat.add_le_add (by omega) hc

private def rankPayload {L : Limits} {h : Header} {d : ByteArray} (hp : Header.parse L d = .ok h) :
    Account (if h.ppm.segments.isEmpty then pure #[] else ppmChunkIndex L h) (rankBudget L) := by
  split
  · exact free _ _
  unfold ppmChunkIndex rankBudget
  apply widen (charge h.tiles.size (i := _) ?_) (Nat.add_le_add_right (parsed_tiles hp) _)
  apply after
  intro _ hc
  have n : numTileParts h ≤ L.maxTileParts := check_limit hc
  split
  · exact free _ _
  let xs := rankTriples h
  let m := PacketSortWork.measured (fun a b => a.1 ≤ b.1) xs
  obtain ⟨tr,_,sortBound,eq⟩ := rank_work h
  let ct := numTileParts h
  let rows := h.tiles.size
  let init := h.tiles.map fun tp => Array.replicate tp.tile.parts.size 0
  let writes := rankWrites m.1.zipIdx init
  have he := (rank_work h).2.1
  have sortedLength : m.1.zipIdx.length = ct := by
    change ((PacketSortWork.measured _ (rankTriples h)).1.zipIdx).length = _
    rw [he]; simp [ct,tr]
  have hshape : (init.map Array.size).toList.sum = ct := by
    simpa [init,Function.comp_def,ct] using parts_sum h
  obtain ⟨writeEr,writeBound⟩ := rank_writes m.1.zipIdx init rows ct (by simp [init,rows]) (Nat.le_of_eq hshape)
  rw [sortedLength] at writeBound
  let work := 8*(rows+ct)+(xs.length+m.2)+writes.2
  refine ⟨(.ok writes.1,work),by dsimp only [writes]; rw [writeEr,eq]; rfl,?_⟩
  have rt := parsed_tiles hp
  have sq := Nat.mul_le_mul n n
  have updates := Nat.mul_le_mul n (Nat.add_le_add (Nat.add_le_add_left rt 1) n)
  dsimp only [work,rows,ct,xs,m,writes] at *; omega

/-! ## Header validation and component override tables -/

private theorem main_entries {L : Limits} {c f : Nat} {a z : Acc} {r t : Reader}
    (ha : ∀ p ∈ a.poc, p.entries.size ≤ r.data.size)
    (ok : segmentLoop L c f a r = .ok (z,t)) : ∀ p ∈ z.poc, p.entries.size ≤ r.data.size := by
  induction f generalizing a r with
  | zero => cases ok
  | succ f ih =>
    rw [segmentLoop] at ok
    split at ok <;> try contradiction
    rename_i m r1 h1
    have hd := (Reader.u16be_pos h1).2.2.1
    split at ok
    · cases ok; exact ha
    split at ok <;> try contradiction
    split at ok
    · rw [← hd]; apply ih _ ok; simpa only [hd] using ha
    split at ok <;> try contradiction
    split at ok <;> try contradiction
    rename_i b len r2 hs
    have he := HeaderWork.readSegment_extent hs
    dsimp only at ok
    split at ok <;> try contradiction
    rename_i acc hac
    rw [← he.2.1.trans hd]
    apply ih _ ok
    rw [he.2.1,hd]
    unfold addSegment at hac
    by_cases hcod : m == Code.COD
    · rw [ite_eq_left hcod] at hac
      repeat' obtain ⟨_,_,hac⟩ := bind_ok hac
      cases hac; exact ha
    rw [ite_eq_right hcod] at hac
    dsimp only at hac
    repeat' first | (split at hac <;> try contradiction) | (obtain ⟨_,_,hac⟩ := bind_ok hac)
    all_goals cases hac <;> first | exact ha | skip
    intro p hp
    rcases Array.mem_push.1 hp with old | rfl
    · exact ha _ old
    · have width := poc_width (by assumption : parsePOC L c b = .ok p)
      simpa only [he.1,hd] using width

private theorem siz_components {L : Limits} {r : Reader} {s : SIZ} (ok : parseSIZ L r = .ok s) :
    s.csiz ≤ L.maxComponents := by
  unfold parseSIZ at ok
  iterate 10 obtain ⟨⟨_,_⟩,_,ok⟩ := bind_ok ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  obtain ⟨_,hc,ok⟩ := bind_ok ok
  iterate 5 obtain ⟨_,_,ok⟩ := bind_ok ok
  obtain ⟨⟨cs,_⟩,ha,ok⟩ := bind_ok ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  cases ok
  have h := array_size _ _ _ _ ha
  have cap := check_limit hc
  simpa [SIZ.csiz] using Nat.le_trans (Nat.le_of_eq h) (by simpa [Limits.bound] using cap)

private def mainWidth (h : MainHeader) := h.pointers.size+h.poc.size+h.coc.size+h.qcc.size+h.rgn.size

private theorem main_fields {L : Limits} {r t : Reader} {h : MainHeader}
    (ok : parseMainHeader L r = .ok (h,t)) : t.data = r.data ∧ h.siz.csiz ≤ L.maxComponents ∧
    mainWidth h ≤ r.data.size+2 ∧ ∀ p ∈ h.poc, p.entries.size ≤ r.data.size := by
  unfold parseMainHeader at ok
  obtain ⟨⟨_,r1⟩,h1,ok⟩ := bind_ok ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  obtain ⟨⟨_,r2⟩,h2,ok⟩ := bind_ok ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  obtain ⟨⟨b,_,r3⟩,h3,ok⟩ := bind_ok ok
  obtain ⟨s,hs,ok⟩ := bind_ok ok
  obtain ⟨⟨a,_⟩,hl,ok⟩ := bind_ok ok
  cases hc : a.cod <;> simp only [hc] at ok <;> try contradiction
  cases hq : a.qcd <;> simp only [hq] at ok <;> try contradiction
  cases ok
  have hd := (HeaderWork.readSegment_extent h3).2.1.trans
    ((Reader.u16be_pos h2).2.2.1.trans (Reader.u16be_pos h1).2.2.1)
  obtain ⟨sz,dt,_⟩ := HeaderWork.segmentLoop_storage hl
  have hp := main_entries (by simp) hl
  have bytes := rem_le r3
  rw [hd] at bytes hp
  simp [HeaderWork.mainSlots] at sz
  exact ⟨dt.trans hd,siz_components hs,by dsimp [mainWidth]; omega,hp⟩

/-- One SIZ followed by the main-header marker loop. -/
def mainBudget (L : Limits) (b : Nat) :=
  2*L.maxComponents + b*(3+markerBudget L L.maxComponents b)

private def mainPayload (L : Limits) (r : Reader) : Account (parseMainHeader L r) (mainBudget L r.data.size) := by
  unfold parseMainHeader
  apply after; rintro ⟨_,r1⟩ h1
  apply after; intro _ _
  apply after; rintro ⟨_,r2⟩ h2
  apply after; intro _ _
  apply after; rintro ⟨b,_,r3⟩ h3
  apply seqAct (sizPayload L b)
  intro s hs
  have h := (HeaderWork.readSegment_extent h3).2.1.trans
    ((Reader.u16be_pos h2).2.2.1.trans (Reader.u16be_pos h1).2.2.1)
  apply before; apply widen (mainHeaderPayload ..)
  rw [h]
  exact Nat.mul_le_mul (by simpa only [h] using rem_le r3) (by
    have := siz_components hs; unfold markerBudget; omega)

/-- Three indexed duplicate tables and their projected marker arrays. -/
def overrideBudget (csiz n : Nat) := 3*csiz+n*(4+csiz)

private def overrideScan {α : Type} (pos : Nat) (what : String) (c : Nat) (xs : Array (UInt16 × α)) :
    Account (overrides pos what c xs) (c+xs.size*(2+c)) := by
  let f (a : Array (Option α)) (p : UInt16 × α) : Run (Array (Option α)) :=
    match a[p.1.toNat]? with
    | some none => (.ok (a.setIfInBounds p.1.toNat (some p.2)),2+a.size)
    | some (some _) => (.error (Header.malformed pos s!"second {what} for component {p.1}"),1)
    | none => (.error (Header.malformed pos s!"{what} component {p.1} ≥ Csiz {c}"),1)
  apply charge c
  refine ⟨countedFold f xs.toList (Array.replicate c none),?_,?_⟩
  · rw [fold_result,Array.foldlM_toList]
    unfold overrides
    congr 1; funext a x; obtain ⟨i,v⟩ := x
    dsimp [f]
    cases hx : a[i.toNat]? with
    | none => rfl
    | some v => cases v <;> rfl
  · rw [← Array.length_toList (xs := xs)]
    apply fold_bound _ (fun a => a.size = c) _ _ (by simp)
    intro x _ a ha
    dsimp [f]
    split <;> simp [ha] <;> omega

private def overrideTables (pos c : Nat) (cs : Array COC) (qs : Array QCC) (gs : Array RGN) :
    Account (mkOverrides pos c cs qs gs) (overrideBudget c (cs.size+qs.size+gs.size)) := by
  unfold mkOverrides
  apply widen (seqAct (charge cs.size (overrideScan ..)) (fun _ _ =>
    seqAct (charge qs.size (overrideScan ..)) (fun _ _ => before (charge gs.size (overrideScan ..))))) ?_
  simp only [Array.size_map]
  unfold overrideBudget
  simp only [Nat.add_mul,Nat.mul_add]
  omega

private theorem assembly_parts {corr i ps t} (ok : assembleTile corr i ps = .ok t) : t.parts = ps := by
  unfold assembleTile at ok
  dsimp only at ok
  split at ok <;> split at ok <;> try contradiction
  all_goals repeat' obtain ⟨_,_,ok⟩ := bind_ok ok
  all_goals cases ok; rfl

private theorem assembled_shapes {L : Limits} {b f i pk : Nat} {corr : Bool} {ps : Array (Array TilePartHeader)}
    {a z : Array Tile} (hp : ∀ row ∈ ps, tableFits L b row) (ha : ∀ t ∈ a, tableFits L b t.parts)
    (ok : assembleTiles L corr ps f i pk a = .ok z) : ∀ t ∈ z, tableFits L b t.parts := by
  induction f generalizing i pk a with
  | zero => cases ok; exact ha
  | succ f ih =>
    simp only [assembleTiles] at ok
    split at ok
    · exact ih ha ok
    split at ok <;> try contradiction
    rename_i t ht
    split at ok <;> try contradiction
    apply ih _ ok
    intro v hv
    rcases Array.mem_push.1 hv with old | rfl
    · exact ha _ old
    rw [assembly_parts ht]
    cases h : ps[i]? with
    | none => simp [tableFits]
    | some row => exact hp row (Array.mem_of_getElem? h)

private theorem tile_shapes {L : Limits} {mh : MainHeader} {r : Reader} {ts : Array Tile}
    (ht : parseTileParts L mh r = .ok ts) :
    ts.size ≤ L.maxTiles ∧ ∀ t ∈ ts, tableFits L r.data.size t.parts := by
  unfold parseTileParts at ht
  obtain ⟨_,hc,ht⟩ := bind_ok ht
  obtain ⟨_,hl,ht⟩ := bind_ok ht
  refine ⟨Nat.le_trans (by simpa using assembled_count ht) (check_limit hc),?_⟩
  apply assembled_shapes (loop_tables ?_ hl) (by simp) ht
  intro ps hp
  obtain ⟨_,rfl⟩ := Array.mem_replicate.1 hp
  simp [tableFits]

private theorem fold_increase {α β : Type} (weight : β → Nat) (f : β → α → β)
    (xs : Array α) (a : β) (k : Nat) (step : ∀ x ∈ xs, ∀ v, weight (f v x) ≤ weight v+k) :
    weight (xs.foldl f a) ≤ weight a + xs.size*k := by
  rw [← Array.foldl_toList,← Array.length_toList (xs := xs)]
  replace step : ∀ x ∈ xs.toList, ∀ v, weight (f v x) ≤ weight v+k := by simpa using step
  generalize xs.toList = l at *
  induction l generalizing a with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons,List.length_cons,Nat.succ_mul]
    have := ih (f a x) (fun y hy => step y (by simp [hy]))
    have := step x (by simp) a
    omega

private def segWeight (v : TileSegs) := v.coc.size+v.qcc.size+v.rgn.size+v.poc.size

private theorem seg_weight {L : Limits} {b : Nat} {t : Tile} (ht : tableFits L b t.parts) :
    segWeight (tileSegs t) ≤ L.maxTilePartsPerTile*((b+1)*(b+1)) := by
  unfold tileSegs
  apply Nat.le_trans (fold_increase segWeight _ _ _ ((b+1)*(b+1)) ?_) ?_
  · intro p hm v
    apply Nat.le_trans (fold_increase segWeight _ _ _ (b+1) ?_) ?_
    · intro s hs a
      have h := (ht.2 p hm).2 s hs
      cases s <;> simp only [segmentEntries,segWeight,Array.size_push,Array.size_append] at * <;> omega
    · exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (ht.2 p hm).1.1) _
  · simpa [segWeight] using Nat.mul_le_mul_right ((b+1)*(b+1)) ht.1

private def mapItems {α β : Type} (f : α → Except Error β) (k : Nat) (xs : List α)
    (each : ∀ x ∈ xs, Account (f x) k) : Account (xs.mapM f) (xs.length*k) := by
  cases xs with
  | nil => exact free _ _
  | cons x xs =>
    rw [List.mapM_cons,List.length_cons,Nat.succ_mul,Nat.add_comm (xs.length*k)]
    apply seqAct (each _ (by simp))
    intro _ _
    exact before (mapItems f k xs (fun y hy => each y (by simp [hy])))
termination_by xs.length

private def mapArray {α β : Type} (f : α → Except Error β) (k : Nat) (xs : Array α)
    (each : ∀ x ∈ xs, Account (f x) k) : Account (xs.mapM f) (xs.size*k) := by
  rw [Array.mapM_eq_mapM_toList,← Array.length_toList (xs := xs)]
  exact before (mapItems f k xs.toList (fun x hx => each x (by simpa using hx)))

/-- The header component builder makes at most 766 band records and 256
precincts for any UInt8 level, before exploiting the tighter parsed level guard.
The tariff includes the extract/map or range/map pair and component descriptor. -/
def componentBudget := 2*(3*255+1)+2*(255+1)+3

private def compPayload (pos : Nat) (s : CodingStyle) (q : QCD) (roi : Nat) :
    Account (mkComp pos s q roi) componentBudget := by
  unfold mkComp
  let nl := s.levels.toNat
  have nh := s.levels.toNat_lt
  apply widen (seqAct (billed _ (Nat.le_refl (2*(3*nl+1)+1)))
    (j := 2*(nl+1)+2) (fun _ _ => billed _ (Nat.le_refl _))) ?_
  dsimp [componentBudget,nl]; omega

/-- Header-wide component setup, override validation and progression-change copies. -/
def mainCodingBudget (L : Limits) (b : Nat) :=
  overrideBudget L.maxComponents (b+2) + L.maxComponents*(2+componentBudget) +
    ((b+2)*(1+(b+2)*b)+(b+2)*b+12)

private theorem override_mono {i j n m : Nat} (hi : i ≤ j) (hn : n ≤ m) :
    overrideBudget i n ≤ overrideBudget j m :=
  Nat.add_le_add (Nat.mul_le_mul_left _ hi) (Nat.mul_le_mul hn (Nat.add_le_add_left hi 4))

private def components {α : Type} (c : Nat) (f : Nat → Except Error α)
    (each : ∀ i ∈ Array.range c, Account (f i) componentBudget) :
    Account ((Array.range c).mapM f) (c*(2+componentBudget)) :=
  widen (charge (2*c) (mapArray _ _ _ each)) (by simp only [Array.size_range,Nat.mul_add]; omega)

private def mainCodingPayload {L : Limits} {mh : MainHeader} {r t : Reader}
    (ok : parseMainHeader L r = .ok (mh,t)) : Account (mainCoding mh) (mainCodingBudget L r.data.size) := by
  obtain ⟨_,hc,slots,entries⟩ := main_fields ok
  unfold mainWidth at slots
  unfold mainCoding mainCodingBudget
  rw [Nat.add_assoc]
  apply seqAct (widen (overrideTables ..) (override_mono hc (by omega)))
  intro _ _
  apply seqAct (widen (components _ _ (fun _ _ => compPayload ..)) (Nat.mul_le_mul_right _ hc))
  intro _ _
  let m := concatData POC.entries mh.poc.toList #[]
  have ⟨_,sz,work⟩ := concat_data POC.entries mh.poc.toList #[] r.data.size (by simpa using entries)
  simp only [Array.size_empty,Array.length_toList,Nat.zero_add,Nat.add_zero] at sz work
  have hps : mh.poc.size ≤ r.data.size+2 := by omega
  have w := Nat.mul_le_mul_right r.data.size hps
  apply billed _ (n := m.2 + m.1.size + 12)
  have w' := Nat.mul_le_mul hps (Nat.add_le_add_left w 1)
  dsimp only [m]; omega

private theorem default_poc {mh : MainHeader} {d : Coding} (ok : mainCoding mh = .ok d) :
    d.poc = mh.poc.foldl (fun a p => a++p.entries) #[] := by
  unfold mainCoding at ok
  repeat' obtain ⟨_,_,ok⟩ := bind_ok ok
  cases ok; rfl

/-- Segment collection, override tables and component setup for one assembled tile. -/
def tileCodingBudget (L : Limits) (b : Nat) :=
  let p := L.maxTilePartsPerTile
  let segments := p*(b+1)
  let width := p*((b+1)*(b+1))
  p + segments*(2+width) + (width+(b+2)*b+12) +
    (overrideBudget L.maxComponents width + L.maxComponents*(2+componentBudget))

private def tileCodingPayload {L : Limits} {mh : MainHeader} {r tail : Reader} {d : Coding}
    (main : parseMainHeader L r = .ok (mh,tail)) (defaults : mainCoding mh = .ok d)
    (ov : Overrides) (t : Tile) (ht : tableFits L r.data.size t.parts) :
    Account (tileCoding mh ov d t) (tileCodingBudget L r.data.size) := by
  obtain ⟨_,hc,slots,entries⟩ := main_fields main
  unfold mainWidth at slots
  let b := r.data.size
  let p := L.maxTilePartsPerTile
  let width := p*((b+1)*(b+1))
  have sw := seg_weight ht
  change segWeight (tileSegs t) ≤ width at sw
  unfold segWeight at sw
  have ⟨er,sz,_⟩ := concat_data POC.entries mh.poc.toList #[] b (by simpa using entries)
  rw [er,Array.foldl_toList,← default_poc defaults] at sz
  simp only [Array.size_empty,Nat.zero_add,Array.length_toList] at sz
  have hw := Nat.mul_le_mul_right b (show mh.poc.size ≤ b+2 by dsimp [b]; omega)
  unfold tileCoding tileCodingBudget
  dsimp only
  let ts := tileSegs t
  let scans := t.parts.size + segmentCount t.parts*(2+segWeight ts)
  let pc := (if ts.poc.isEmpty then d.poc else ts.poc).size
  apply widen (charge (scans+pc+12) (i := overrideBudget L.maxComponents width + L.maxComponents*(2+componentBudget)) ?_) ?_
  · apply after
    intro _ _
    split
    · exact free _ _
    · apply seqAct (widen (overrideTables ..) (override_mono hc (by omega)))
      intro _ _
      apply before; apply widen (components _ _ (fun _ _ => compPayload ..))
      exact Nat.mul_le_mul_right _ hc
  · have hp := ht.1
    change t.parts.size ≤ p at hp
    have hpoc : pc ≤ width+(b+2)*b := by dsimp only [pc,ts]; split <;> omega
    change scans + pc + 12 + _ ≤ p+(p*(b+1))*(2+width)+(width+(b+2)*b+12)+_
    apply Nat.add_le_add_right
    have count := Nat.le_trans (segment_count t.parts (b+1) (fun q hq => (ht.2 q hq).1.1))
      (Nat.mul_le_mul_right _ hp)
    have cw := Nat.mul_le_mul count (Nat.add_le_add_left (show segWeight ts ≤ width from sw) 2)
    dsimp only [scans]; omega

/-! ## Public parser and tile-prefix bounds -/

/-- Raw pointer descriptors and PPM chunk construction for at most `m` main
pointer markers. Includes the rejected TLM table built before the cumulative guard. -/
def pointersBudget (L : Limits) (m : Nat) :=
  m*(2+2*L.maxTileParts) + (sortBudget m + (sortBudget m + (3*m+(L.maxTileParts+1)*(3+14*m))))

/-- Byte- and limit-only budget for tile-part payloads, grouping and assembly. -/
def partsBudget (L : Limits) (b : Nat) :=
  L.maxTiles + (b+2) + ((L.maxTileParts+1)*(1+(4+3*L.maxTilePartsPerTile +
    b*(3+markerBudget L L.maxComponents b)+L.maxTiles)) +
    L.maxTiles*(2+tileBudget L.maxTilePartsPerTile (b+1)))

/-- Public container and codestream header tariffs. The final charge counts
geometry admission visits. The arithmetic inside a visit is a separate stage. -/
def headerBudget (L : Limits) (b : Nat) :=
  let boxes := 2*b+(L.maxBoxes+1)*3+(L.maxBoxes+1)*(3+boxBudget L b)
  boxes + (mainBudget L b + (mainCodingBudget L b + (pointersBudget L (b+2) +
    (partsBudget L b + (overrideBudget L.maxComponents (b+2) +
    (L.maxTiles*(tileCodingBudget L b+2*L.maxComponents+2) + (L.maxTiles+L.maxCodeBlocks)))))))

private theorem ptr_mono {L : Limits} {i j : Nat} (h : i ≤ j) : pointersBudget L i ≤ pointersBudget L j := by
  unfold pointersBudget sortBudget
  repeat' first | assumption | exact Nat.le_refl _ | apply Nat.add_le_add | apply Nat.mul_le_mul

private theorem range_data {d : ByteArray} {rg : ByteRange} {r : Reader} (ok : rangeReader d rg = .ok r) :
    r.data = d := by
  unfold rangeReader at ok
  obtain ⟨mid,hm,ok⟩ := bind_ok ok
  obtain ⟨⟨_,_⟩,ht,ok⟩ := bind_ok ok
  cases ok
  exact (Reader.take_spec ht).2.2.1.trans (Reader.skip_pos hm).2.2.1

/-- Meter the real parser from its public byte entry point. Every composition
retains the original error and charges work before the first rejection. -/
def headerPayload (L : Limits) (data : ByteArray) : Account (Header.parse L data) (headerBudget L data.size) := by
  unfold Header.parse headerBudget
  apply seqAct
  · unfold Box.parseFile; exact before (filePayload ..)
  intro ct _
  unfold parseCodestreamIn
  apply after
  intro r hr
  have hd := range_data hr
  apply seqAct (widen (mainPayload ..) (by simp only [hd,Nat.le_refl]))
  rintro ⟨mh,t⟩ hm
  obtain ⟨ht,hc,width,_⟩ := main_fields hm
  rw [hd] at width ht
  unfold mainWidth at width
  apply after
  intro _ grid
  apply seqAct (widen (mainCodingPayload hm) (by simp only [hd,Nat.le_refl]))
  intro d defaults
  apply seqAct (widen (pointerPayload ..) (ptr_mono (by omega)))
  rintro ⟨_,_⟩ _
  apply seqAct (widen (tilePartsPayload ..) ?_)
  · intro ts hts
    obtain ⟨tc,shapes⟩ := tile_shapes hts
    apply seqAct (widen (overrideTables ..) (override_mono hc (by omega)))
    intro ov _
    apply seqAct (widen (mapArray _ (tileCodingBudget L data.size+2*L.maxComponents+2) ts ?_) (Nat.mul_le_mul_right _ tc))
    · intro tps _
      apply before
      obtain ⟨e,b⟩ := HeaderWork.checkWork_visits d tps (by simpa using grid)
      have nt := ((Resources.checkGeometry_ok_iff L mh).1 (by simpa using grid)).2.2.2.1
      exact widen (charge (numTiles mh.siz) ⟨_,e,b⟩) (Nat.add_le_add_right nt L.maxCodeBlocks)
    · intro tile member
      have fit := shapes tile member
      rw [ht,← hd] at fit
      rw [Nat.add_assoc]
      apply seqAct (widen (tileCodingPayload hm defaults ov tile fit) (by simp only [hd,Nat.le_refl]))
      intro _ _
      exact billed _ (n := 2*mh.siz.csiz+2) (by omega)
  · dsimp only [partsBudget,readPartBudget]
    rw [ht]
    apply Nat.add_le_add (by omega)
    apply Nat.add_le_add_right
    apply Nat.mul_le_mul_left
    apply Nat.add_le_add_left
    apply Nat.add_le_add_right
    apply Nat.add_le_add_left
    apply Nat.mul_le_mul_left
    unfold markerBudget; omega

/-- Exact public parser result and the combined bound on the named visits,
sort checks, temporary logical descriptors and copies, on all byte strings. -/
theorem parse_work (L : Limits) (data : ByteArray) :
    (headerPayload L data).run.1 = Header.parse L data ∧
    (headerPayload L data).run.2 ≤ headerBudget L data.size :=
  ⟨(headerPayload ..).erase,(headerPayload ..).bound⟩

private def tilePartSortMeter (L : Limits) (mh : MainHeader) (r : Reader) (price : Nat → Nat → Nat)
    (ppt plt : Nat) (hp : priceBound price (L.maxTilePartsPerTile*(r.data.size+1)) ppt)
    (hl : priceBound price (r.data.size+1) plt) :
    Account (parseTileParts L mh r) (L.maxTiles*(ppt+L.maxTilePartsPerTile*plt)) := by
  unfold parseTileParts
  apply after; intro _ hc
  apply after; intro st hs
  have rows := loop_tables (by intro ps h; obtain ⟨_,rfl⟩ := Array.mem_replicate.1 h; simp [tableFits]) hs
  apply widen (assemblyWalk L _ _ _ rows 0 (ppt+L.maxTilePartsPerTile*plt) ?_ _ _ _ _) ?_
  · intro i row hr
    have small : priceBound price (row.size*(r.data.size+1)) ppt :=
      fun n hn => hp n (Nat.le_trans hn (Nat.mul_le_mul_right _ hr.1))
    have th := tileSorts_work price (tnsotCorrection st.parts st.firstDone) i _ row (fun p hm => (hr.2 p hm).1.1) ppt plt small hl
    exact ⟨_,th.1,Nat.le_trans th.2 (Nat.add_le_add_left (Nat.mul_le_mul_right _ hr.1) ppt)⟩
  · simpa [Limits.bound] using Nat.mul_le_mul_right (ppt+L.maxTilePartsPerTile*plt) (check_limit hc)

/-- Trace all four sort sites on the public parser path. `price n w` can count
calls, select particular widths, or charge their comparisons and checks. No
sort is scheduled after a preceding error. -/
def sortSchedule (L : Limits) (data : ByteArray) (price : Nat → Nat → Nat)
    (pointer ppt plt : Nat) (hp : priceBound price (data.size+2) pointer)
    (ht : priceBound price (L.maxTilePartsPerTile*(data.size+1)) ppt)
    (hl : priceBound price (data.size+1) plt) :
    Account (Header.parse L data) (2*pointer + L.maxTiles*(ppt+L.maxTilePartsPerTile*plt)) := by
  unfold Header.parse
  apply after; intro _ _
  unfold parseCodestreamIn
  apply after; intro r hr
  apply after; rintro ⟨mh,t⟩ hm
  have hd := range_data hr
  obtain ⟨hdata,_,width,_⟩ := main_fields hm
  rw [hd] at width hdata
  unfold mainWidth at width
  iterate 2 (apply after; intro _ _)
  have ptr := pointerSorts_work price L mh data pointer (fun i hi => hp i (by omega))
  apply seqAct ⟨_,ptr.1,ptr.2⟩
  rintro ⟨_,_⟩ _
  exact before (tilePartSortMeter L mh t price ppt plt (by simpa only [hdata] using ht)
    (by simpa only [hdata] using hl))

/-- Unit tariff counts the calls actually made, including the first duplicate
sort. The PPM SOT-rank merge sort is a separate, once-per-grid operation. -/
theorem sort_calls (L : Limits) (data : ByteArray) :
    let m := (sortSchedule L data (fun _ _ => 1) 1 1 1
      (by intro _ _ _ _; exact Nat.le_refl 1) (by intro _ _ _ _; exact Nat.le_refl 1) (by intro _ _ _ _; exact Nat.le_refl 1)).run
    m.1 = Header.parse L data ∧ m.2 ≤ 2+L.maxTiles*(1+L.maxTilePartsPerTile) := by
  exact ⟨(sortSchedule ..).erase,by simpa using (sortSchedule L data (fun _ _ => 1) 1 1 1 _ _ _).bound⟩

/-- Pair prefix charging with the exact descriptor partition on success. -/
theorem chunks_work (L : Limits) (d : ByteArray) (loc : Location) (f : Nat)
    (xs : List ByteRange) (a : Array (Array ByteRange)) (ha : a.size ≤ L.maxTileParts) :
    let m := (chunkPayload L d loc xs.length f xs a (Nat.le_refl _)).run
    m.1 = ppmChunks L d loc f xs a ∧ m.2 ≤ (L.maxTileParts-a.size+1)*(3+14*xs.length) ∧
    ∀ out, m.1 = .ok out → out.size ≤ L.maxTileParts ∧ HeaderWork.chunkBytes out +
      4*(out.size-a.size) = HeaderWork.chunkBytes a + HeaderWork.rangeBytes xs := by
  let a' := chunkPayload L d loc xs.length f xs a (Nat.le_refl _)
  refine ⟨a'.erase,a'.bound,?_⟩
  intro out h
  have z := HeaderWork.ppmChunks_account L d loc f xs a out ha (a'.erase.symm.trans h)
  exact ⟨z.1,z.2.2⟩

/-- Rejection-prefix selector cost and retained stream storage on success. -/
theorem selection_work {L : Limits} {h : Header} {d : ByteArray} {tp : TileParams}
    (parsed : Header.parse L d = .ok h) (member : tp ∈ h.tiles) (ranks : Array Nat) :
    let m := (selectPayload parsed member ranks).run
    m.1 = headerStreamAt h d tp ranks ∧ m.2 ≤ selectionBudget L d.size ∧
    ∀ s, m.1 = .ok (some s) → let k := if s.fromPpm then L.maxTilePartsPerTile*(L.maxTileParts*d.size)
      else L.maxTilePartsPerTile*(d.size+1)
    s.ranges.size ≤ k ∧ s.bytes.size ≤ k*d.size ∧ Tier2WF.RangesIn d.size s.ranges := by
  let a := selectPayload parsed member ranks
  refine ⟨a.erase,a.bound,?_⟩
  intro s hs
  have ok := a.erase.symm.trans hs
  have storage := HeaderWork.parsed_headerStream parsed member ok
  exact ⟨storage.1,storage.2,(HeaderWork.headerStreamAt_storage ok).2.2⟩

private theorem prepared {L : Limits} {d : ByteArray} {red : Nat} {h dst}
    (hp : PublicPacketWork.prepareTiles L d red = .ok (h,dst)) : Header.parse L d = .ok h := by
  unfold PublicPacketWork.prepareTiles at hp
  obtain ⟨_,_,hp⟩ := bind_ok hp
  obtain ⟨_,h,hp⟩ := bind_ok hp
  obtain ⟨_,_,hp⟩ := bind_ok hp
  cases hp; exact h

private def visitSelection {L : Limits} {h : Header} {d : ByteArray} (hp : Header.parse L d = .ok h)
    (idx : Array (Array Nat)) (v : PacketTraversal.TileVisit) : Nat :=
  match hit : h.tiles[v.cursor]? with
  | none => 0
  | some tp => if tp.index = v.tile then
      (selectPayload hp (Array.mem_of_getElem? hit) (idx.getD v.cursor #[])).run.2
    else 0

private theorem visits_bound {L : Limits} {h : Header} {d : ByteArray} (hp : Header.parse L d = .ok h)
    (idx : Array (Array Nat)) (vs : List PacketTraversal.TileVisit) :
    (vs.map (visitSelection hp idx)).sum ≤ vs.length*selectionBudget L d.size := by
  induction vs with
  | nil => simp
  | cons v vs ih =>
    simp only [List.map_cons,List.length_cons,List.sum_cons,Nat.succ_mul]
    rw [Nat.add_comm (vs.length*_)]
    apply Nat.add_le_add _ ih
    unfold visitSelection
    split
    · exact Nat.zero_le _
    split
    · exact (selectPayload ..).bound
    · exact Nat.zero_le _

private def publicSelection (L : Limits) (d : ByteArray) (red : Nat) : Nat :=
  match pr : PublicPacketWork.prepareTiles L d red with
  | .error _ => 0
  | .ok (_,_) =>
    let hp := prepared pr
    let ranks := rankPayload hp
    ranks.run.2 + match ranks.run.1 with
      | .error _ => 0
      | .ok rows => ((PublicPacketWork.measure L d red).1.map (visitSelection hp rows)).sum

/-- Parser work is reached after reduction admission. Rank construction is
reached after allocation of the native destinations. Selected streams are
priced at the actual cursor for each tile on the public packet trace. -/
def publicHeaderCharge (L : Limits) (d : ByteArray) (red : Nat) : Nat :=
  (match L.check JPEG2000.Decode.loc .decompLevels red with
   | .error _ => 0
   | .ok _ => (headerPayload L d).run.2) + publicSelection L d red

/-- Source-level header, packed selection, colour and placement charges on the
ordinary public byte path. The grid contributes one rank preflight and at most
one selector per visited tile, including the first failing tile. -/
theorem decode_header_work (B : Nat) (L : Limits) (d : ByteArray) (red : Nat) :
    let m := PublicPacketWork.measurePlacement B L d red
    let vs := (PublicPacketWork.measure L d red).1
    m.1 = decodeCodestream L d red ∧
    publicHeaderCharge L d red + m.2 ≤ headerBudget L d.size + rankBudget L +
      vs.length*(selectionBudget L d.size + PacketTraversal.placementBudget B L) ∧
    publicHeaderCharge L d red + m.2 ≤ headerBudget L d.size + rankBudget L +
      L.maxTiles*(selectionBudget L d.size + PacketTraversal.placementBudget B L) := by
  obtain ⟨erase,place,_⟩ := PublicPacketWork.decode_placement_work B L d red
  have count := (PublicPacketWork.decode_packet_work L d red).2.1
  let vs := (PublicPacketWork.measure L d red).1
  have sel : publicSelection L d red ≤ rankBudget L + vs.length*selectionBudget L d.size := by
    unfold publicSelection
    split
    · exact Nat.zero_le _
    · rename_i h _ hp
      apply Nat.add_le_add (rankPayload (prepared hp)).bound
      split
      · exact Nat.zero_le _
      · exact visits_bound ..
  have cost : publicHeaderCharge L d red ≤ headerBudget L d.size +
      (rankBudget L+vs.length*selectionBudget L d.size) := by
    unfold publicHeaderCharge
    apply Nat.add_le_add _ sel
    split
    · exact Nat.zero_le _
    · exact (headerPayload ..).bound
  have total := Nat.add_le_add cost place
  have sum : publicHeaderCharge L d red + (PublicPacketWork.measurePlacement B L d red).2 ≤
      headerBudget L d.size + rankBudget L + vs.length*(selectionBudget L d.size+PacketTraversal.placementBudget B L) := by
    rw [Nat.mul_add]
    dsimp only [vs] at *; omega
  exact ⟨erase,sum,Nat.le_trans sum (Nat.add_le_add_left (Nat.mul_le_mul_right _ count) _)⟩

end JPEG2000.Spec.Resources.HeaderPayload
