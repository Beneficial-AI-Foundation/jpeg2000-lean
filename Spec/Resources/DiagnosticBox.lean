import Spec.Resources.DiagnosticCost
import Spec.Resources.HeaderWork

/-!
# Container diagnostic construction (Plan.md §§3–5, 7, S3; T.800 A.4.1, A.5.1, I.4–I.5)

The field readers and payload parsers propagate their first failure. Their successful
paths build no diagnostic text. The surrounding parser also constructs the duplicate-box
argument, masks later colour errors, probes for a raw codestream, and replaces a failed
signature read. Those operations need separate events, including on successful prefixes.
-/

namespace JPEG2000.Spec.Resources.DiagnosticBox

open Bytes Box DiagnosticCost

private structure Walk {α : Type} (cap : Nat) (r : Except Error α) (k : Nat) (P : α → Prop) where
  trace : Trace cap r k
  post : ∀ a, r = .ok a → P a

private def pass {α : Type} {cap k : Nat} {P : α → Prop} (a : α) (h : P a) :
    Walk cap (.ok a) k P :=
  ⟨doneTrace a, fun _ e => by cases e; exact h⟩

private def chain {α β : Type} {cap i j : Nat} {r : Except Error α} {f : α → Except Error β}
    {P : α → Prop} {Q : β → Prop} (x : Walk cap r i P)
    (y : ∀ a, P a → Walk cap (f a) j Q) : Walk cap (r >>= f) (j+i) Q := by
  refine ⟨bindTrace x.trace (fun a h => (y a (x.post a h)).trace), ?_⟩
  cases h : r with
  | error => intro a he; cases he
  | ok a => exact (y a (x.post a h)).post

private def enlarge {α : Type} {cap i j : Nat} {r : Except Error α} {P : α → Prop}
    (x : Walk cap r i P) (h : i ≤ j) : Walk cap r j P :=
  ⟨widen x.trace h,x.post⟩

private def earlier {α β : Type} {cap i j : Nat} {r : Except Error α} {s : Except Error β}
    {P : β → Prop} (x : Trace cap r i) (y : Walk cap s j P) : Walk cap s (i+j) P :=
  ⟨includeTrace x y.trace,y.post⟩

-- At a leaf the first error terminates every enclosing bind. This stronger certificate
-- allows arbitrary many array/row reads to spend a single message between them.
private inductive Leaf {α : Type} (cap : Nat) (P : α → Prop) : Except Error α → Type where
  | ok (a : α) (h : P a) : Leaf cap P (.ok a)
  | error (e : Error) (t : Trace cap (Except.error e : Except Error Unit) 1) :
      Leaf cap P (.error e)

private def leafBind {α β : Type} {cap : Nat} {r : Except Error α} {f : α → Except Error β}
    {P : α → Prop} {Q : β → Prop} (x : Leaf cap P r)
    (y : ∀ a, P a → Leaf cap Q (f a)) : Leaf cap Q (r >>= f) :=
  match x with
  | .ok a h => y a h
  | .error e t => .error e t

private def leafWalk {α : Type} {cap : Nat} {r : Except Error α} {P : α → Prop}
    (x : Leaf cap P r) : Walk cap r 1 P :=
  match x with
  | .ok a h => pass a h
  | .error e t => ⟨⟨t.messages,t.countBound,fun _ h => by cases h; exact t.origin e rfl⟩,
      fun _ h => by cases h⟩

private def mal {α : Type} {cap p : Nat} {P : α → Prop} {s : String}
    (hp : p ≤ cap) (b : Built cap s) : Leaf cap P (.error (malformedAt p s)) :=
  .error _ ⟨[⟨s,b⟩],by simp,by intro e h; cases h; exact ⟨hp,⟨s,b⟩,by simp,rfl⟩⟩

private def trunc {α : Type} {cap p : Nat} {P : α → Prop} {s : String}
    (hp : p ≤ cap) (b : Built cap s) (stage : Stage := .box) :
    Leaf cap P (.error (.truncated (.atOffset stage p) s)) :=
  .error _ ⟨[⟨s,b⟩],by simp,by intro e h; cases h; exact ⟨hp,⟨s,b⟩,by simp,rfl⟩⟩

private def limit {α : Type} {cap v p : Nat} {P : α → Prop} {k : LimitKind} {bound : Nat}
    (hp : p ≤ cap) (hv : v ≤ cap) : Leaf cap P (.error (.limitExceeded (.atOffset .box p) k v bound)) :=
  .error _ ⟨[],by simp,by intro e h; cases h; exact ⟨hp,hv⟩⟩

private def check (L : Limits) (k : LimitKind) {cap p v : Nat} (hp : p ≤ cap) (hv : v ≤ cap) :
    Leaf cap (fun _ => v ≤ L.bound k) (L.check (.atOffset .box p) k v) := by
  unfold Limits.check Limits.checkLe
  split
  · exact .ok () ‹_›
  · exact limit hp hv

private theorem pos {cap : Nat} {r : Reader} (h : r.data.size ≤ cap) : r.pos ≤ cap := Nat.le_trans r.pos_le_size h

private theorem rem {cap : Nat} {r : Reader} (h : r.data.size ≤ cap) : r.remaining ≤ cap :=
  Nat.le_trans (Nat.sub_le ..) (Nat.le_trans r.stop_le h)

private def u8 {cap : Nat} (r : Reader) (h : r.data.size ≤ cap) :
    Leaf cap (fun z => z.2.data.size ≤ cap) (r.u8) := by
  unfold Reader.u8
  split
  · exact .ok _ h
  · exact trunc (pos h) (oneFixed "u8" (by decide)) r.stage

private def u16be {cap : Nat} (r : Reader) (h : r.data.size ≤ cap) :
    Leaf cap (fun z => z.2.data.size ≤ cap) (r.u16be) := by
  unfold Reader.u16be
  split
  · exact .ok _ h
  · exact trunc (pos h) (oneFixed "u16" (by decide)) r.stage

private def u32be {cap : Nat} (r : Reader) (h : r.data.size ≤ cap) :
    Leaf cap (fun z => z.2.data.size ≤ cap) (r.u32be) := by
  unfold Reader.u32be
  split
  · exact .ok _ h
  · exact trunc (pos h) (oneFixed "u32" (by decide)) r.stage

private def many {α : Type} {cap : Nat} {f : Reader → Except Error (α × Reader)}
    (one : ∀ r : Reader, r.data.size ≤ cap → Leaf cap (fun z => z.2.data.size ≤ cap) (f r))
    (a : Array α) (r : Reader) (hr : r.data.size ≤ cap) (n : Nat) :
    Leaf cap (fun z => z.1.size = a.size+n ∧ z.2.data.size ≤ cap) (readMany f r a n) := by
  induction n generalizing r a with
  | zero => exact .ok _ ⟨rfl,hr⟩
  | succ n ih =>
    rw [readMany]
    apply leafBind (one r hr)
    rintro ⟨v,t⟩ ht
    simpa only [Array.size_push,Nat.add_assoc,Nat.add_comm 1 n] using ih (a.push v) t ht

private def ihdrLeaf {cap : Nat} (L : Limits) (b : BoxHdr) (hp : b.start ≤ cap)
    (hb : b.body.data.size ≤ cap) (wire : 2^64 ≤ cap) :
    Leaf cap (fun _ => True) (parseIhdr L b) := by
  unfold parseIhdr
  dsimp only
  split
  · exact mal hp (closeExpr (catExpr (catExpr (litExpr _ "ihdr of ") (decExpr (rem hb)))
      (litExpr _ " bytes, expected 14")) (by decide) (by decide))
  apply leafBind (u32be b.body hb)
  rintro ⟨height,r1⟩ h1
  apply leafBind (u32be r1 h1)
  rintro ⟨width,r2⟩ h2
  apply leafBind (u16be r2 h2)
  rintro ⟨nc,r3⟩ h3
  apply leafBind (u8 r3 h3)
  rintro ⟨bpc,r4⟩ h4
  apply leafBind (u8 r4 h4)
  rintro ⟨c,r5⟩ h5
  apply leafBind (u8 r5 h5)
  rintro ⟨unk,r6⟩ h6
  apply leafBind (u8 r6 h6)
  rintro ⟨ipr,r7⟩ h7
  dsimp only
  split
  · exact mal hp (oneFixed _ (by decide))
  apply leafBind (check L .components hp (v := nc.toNat) (by have := nc.toNat_lt; omega))
  intro _ _
  split
  · exact mal hp (closeExpr (catExpr (catExpr (litExpr _ "ihdr: BPC ")
      (decExpr (n := bpc.toNat) (by have := bpc.toNat_lt; omega))) (litExpr _ " depth > 38"))
      (by decide) (by decide))
  · exact .ok _ trivial

private def bpccLeaf {cap : Nat} (b : BoxHdr) (hp : b.start ≤ cap) (hb : b.body.data.size ≤ cap) :
    Leaf cap (fun a => a.size ≤ cap) (parseBpcc b) := by
  unfold parseBpcc
  apply leafBind (many u8 _ _ hb _)
  rintro ⟨bs,t⟩ ⟨hs,_⟩
  dsimp only
  split
  · exact mal hp (oneFixed _ (by decide))
  · exact .ok _ (by change bs.size = _ at hs; rw [hs]; exact Nat.le_trans (by simp) (rem hb))

private def colrLeaf {cap : Nat} (b : BoxHdr) (hp : b.start ≤ cap) (hb : b.body.data.size ≤ cap) :
    Leaf cap (fun _ => True) (parseColr b) := by
  unfold parseColr
  dsimp only
  split
  · exact mal hp (oneFixed _ (by decide))
  apply leafBind (u8 b.body hb)
  rintro ⟨meth,r1⟩ h1
  apply leafBind (u8 r1 h1)
  rintro ⟨prec,r2⟩ h2
  apply leafBind (u8 r2 h2)
  rintro ⟨approx,r3⟩ h3
  dsimp only
  split
  · split
    · exact mal hp (oneFixed _ (by decide))
    · apply leafBind (u32be r3 h3)
      rintro ⟨_,_⟩ _
      exact .ok _ trivial
  all_goals exact .ok _ trivial

private def cmapEntry {cap : Nat} (r : Reader) (h : r.data.size ≤ cap) :
    Leaf cap (fun z => z.2.data.size ≤ cap) (readCmapEntry r) := by
  unfold readCmapEntry
  apply leafBind (u16be r h)
  rintro ⟨cmp,r1⟩ h1
  apply leafBind (u8 r1 h1)
  rintro ⟨mtyp,r2⟩ h2
  apply leafBind (u8 r2 h2)
  rintro ⟨pcol,r3⟩ h3
  exact .ok _ h3

private def cdefEntry {cap : Nat} (r : Reader) (h : r.data.size ≤ cap) :
    Leaf cap (fun z => z.2.data.size ≤ cap) (readCdefEntry r) := by
  unfold readCdefEntry
  apply leafBind (u16be r h)
  rintro ⟨cn,r1⟩ h1
  apply leafBind (u16be r1 h1)
  rintro ⟨typ,r2⟩ h2
  apply leafBind (u16be r2 h2)
  rintro ⟨asc,r3⟩ h3
  exact .ok _ h3

private def cmapLeaf {cap : Nat} (b : BoxHdr) (hp : b.start ≤ cap) (hb : b.body.data.size ≤ cap) :
    Leaf cap (fun _ => True) (parseCmap b) := by
  unfold parseCmap
  dsimp only
  split
  · exact mal hp (closeExpr (catExpr (catExpr (litExpr _ "cmap of ") (decExpr (rem hb)))
      (litExpr _ " bytes, not a multiple of 4")) (by decide) (by decide))
  apply leafBind (many cmapEntry _ _ hb _)
  rintro ⟨_,_⟩ _
  exact .ok _ trivial

private def cdefLeaf {cap : Nat} (b : BoxHdr) (hp : b.start ≤ cap) (hb : b.body.data.size ≤ cap) :
    Leaf cap (fun _ => True) (parseCdef b) := by
  unfold parseCdef
  apply leafBind (u16be _ hb)
  rintro ⟨n,t⟩ ht
  dsimp only
  split
  · exact mal hp (oneFixed _ (by decide))
  split
  · exact trunc hp (oneFixed _ (by decide))
  apply leafBind (many cdefEntry _ _ ht _)
  rintro ⟨_,_⟩ _
  exact .ok _ trivial

private def ftypLeaf {cap : Nat} (b : BoxHdr) (hp : b.start ≤ cap) (hb : b.body.data.size ≤ cap) :
    Leaf cap (fun _ => True) (parseFtyp b) := by
  unfold parseFtyp
  dsimp only
  split
  · exact mal hp (closeExpr (catExpr (catExpr (litExpr _ "ftyp of ") (decExpr (rem hb)))
      (litExpr _ " bytes")) (by decide) (by decide))
  apply leafBind (u32be b.body hb)
  rintro ⟨brand,r1⟩ h1
  apply leafBind (u32be r1 h1)
  rintro ⟨minor,r2⟩ h2
  apply leafBind (many u32be _ _ h2 _)
  rintro ⟨_,_⟩ _
  exact .ok _ trivial

private def bigEndian {cap : Nat} (r : Reader) (h : r.data.size ≤ cap) (a : UInt64) (n : Nat) :
    Leaf cap (fun z => z.2.data.size ≤ cap) (readBE r a n) := by
  induction n generalizing a r with
  | zero => exact .ok _ h
  | succ n ih =>
    rw [readBE]
    apply leafBind (u8 r h)
    rintro ⟨_,t⟩ ht
    exact ih t ht _

private def paletteCell (s : Array UInt64 × Reader) (bi : UInt8) :
    Except Error (Array UInt64 × Reader) := do
  let (v,t) ← readBE s.2 0 (entryBytes bi)
  pure (s.1.push v,t)

private def cellFold {cap : Nat} (s : Array UInt64 × Reader) (hs : s.2.data.size ≤ cap)
    (cols : List UInt8) : Leaf cap (fun z => z.2.data.size ≤ cap) (cols.foldlM paletteCell s) := by
  match cols with
  | [] => exact .ok _ hs
  | bi :: cols =>
    rw [List.foldlM_cons]
    apply leafBind (P := fun z => z.2.data.size ≤ cap)
    · unfold paletteCell
      apply leafBind (bigEndian s.2 hs 0 _)
      rintro ⟨_,_⟩ ht
      exact .ok _ ht
    exact fun t ht => cellFold t ht cols

private def paletteRows {cap : Nat} (bits : Array UInt8) (r : Reader) (hr : r.data.size ≤ cap)
    (a : Array UInt64) (n : Nat) :
    Leaf cap (fun z => z.2.data.size ≤ cap)
      (parsePclr.rows (fun t acc => bits.foldlM paletteCell (acc,t)) r a n) := by
  induction n generalizing r a with
  | zero => exact .ok _ hr
  | succ n ih =>
    rw [parsePclr.rows, ← Array.foldlM_toList]
    apply leafBind (cellFold (a,r) hr bits.toList)
    rintro ⟨acc,t⟩ ht
    exact ih t ht acc

private def pclrLeaf {cap : Nat} (L : Limits) (b : BoxHdr) (hp : b.start ≤ cap)
    (hb : b.body.data.size ≤ cap) (wire : 2^64 ≤ cap) :
    Leaf cap (fun _ => True) (parsePclr L b) := by
  unfold parsePclr
  apply leafBind (u16be b.body hb)
  rintro ⟨ne,r1⟩ h1
  apply leafBind (u8 r1 h1)
  rintro ⟨npc,r2⟩ h2
  dsimp only
  have hn : ne.toNat ≤ cap := by have := ne.toNat_lt; omega
  by_cases bad : (ne.toNat == 0 || decide (ne.toNat > 1024)) = true
  · rw [ite_eq_left bad]
    exact mal hp (closeExpr (catExpr (catExpr (litExpr _ "pclr: NE ") (decExpr hn))
      (litExpr _ " not in 1..1024")) (by decide) (by decide))
  rw [ite_eq_right bad]
  apply leafBind (check L .paletteEntries hp hn)
  intro _ _
  split
  · exact mal hp (oneFixed _ (by decide))
  split
  · exact trunc hp (oneFixed _ (by decide))
  apply leafBind (many u8 _ _ h2 _)
  rintro ⟨bits,r3⟩ ⟨_,h3⟩
  dsimp only
  split
  · exact mal hp (oneFixed _ (by decide))
  split
  · exact trunc hp (oneFixed _ (by decide))
  apply leafBind (paletteRows bits r3 h3 _ _)
  rintro ⟨_,_⟩ _
  exact .ok _ trivial

-- The deferred BPCC comparison needs both fields retained when the first BPCC was read.
private def Saved (cap : Nat) (a : HdrAcc) : Prop :=
  ∀ bs p, a.bpcc = some (bs,p) → bs.size ≤ cap ∧ p ≤ cap

private def child {cap : Nat} (L : Limits) (b : BoxHdr) (a : HdrAcc) (ha : Saved cap a)
    (hp : b.start ≤ cap) (hb : b.body.data.size ≤ cap) (wire : 2^64 ≤ cap) :
    Walk cap (addHeaderBox L a b) 2 (Saved cap) := by
  let msg := s!"duplicate '{typeName b.tbox}' box"
  let tree : Built cap msg := closeExpr (catExpr (catExpr (litExpr _ "duplicate '")
    ⟨_,rfl,.boxName b.tbox⟩) (litExpr _ "' box")) (by decide) (by decide)
  let dup := leafWalk (P := Saved cap) (mal hp tree)
  unfold addHeaderBox
  dsimp only
  split
  · apply earlier (j := 1) dup.trace
    split
    · exact pass _ ha
    · apply chain (leafWalk (ihdrLeaf L b hp hb wire))
      intro _ _
      exact pass _ ha
  split
  · apply earlier (j := 1) dup.trace
    split
    · exact pass _ ha
    · apply chain (leafWalk (bpccLeaf b hp hb))
      intro bs hs
      exact pass _ (by rintro _ _ h; cases h; exact ⟨hs,hp⟩)
  split
  · apply earlier (j := 1) dup.trace
    split
    · apply chain (leafWalk (colrLeaf b hp hb))
      intro c _
      cases c <;> exact pass _ ha
    · let ct := leafWalk (colrLeaf b hp hb)
      apply earlier (j := 0) ct.trace
      cases parseColr b with
      | error => exact pass _ ha
      | ok c => cases c <;> exact pass _ ha
  split
  · split
    · exact enlarge dup (by decide)
    · apply earlier (j := 1) dup.trace
      apply chain (leafWalk (pclrLeaf L b hp hb wire))
      intro _ _
      exact pass _ ha
  split
  · split
    · exact enlarge dup (by decide)
    · apply earlier (j := 1) dup.trace
      apply chain (leafWalk (cmapLeaf b hp hb))
      intro _ _
      exact pass _ ha
  split
  · split
    · exact enlarge dup (by decide)
    · apply earlier (j := 1) dup.trace
      apply chain (leafWalk (cdefLeaf b hp hb))
      intro _ _
      exact pass _ ha
  · exact earlier (j := 1) dup.trace (pass _ ha)

private def checked (L : Limits) (k : LimitKind) {cap p v : Nat} (hp : p ≤ cap) (hv : v ≤ cap) :
    Walk cap (L.check (.atOffset .box p) k v) 0 (fun _ => v ≤ L.bound k) := by
  refine ⟨checkedTrace _ _ _ _ hp hv, ?_⟩
  rintro ⟨⟩ h
  exact (Limits.check_eq_ok_iff ..).1 h

private def readHeader {cap : Nat} (r : Reader) (hr : r.data.size ≤ cap) (wire : 2^64 ≤ cap) :
    Walk cap (readBox r) 5 (fun z =>
      z.1.start ≤ cap ∧ z.1.body.data.size ≤ cap ∧ z.2.data.size ≤ cap) := by
  refine ⟨boxTrace r hr wire, ?_⟩
  rintro ⟨b,t⟩ ok
  obtain ⟨offset,body,tail,_⟩ := HeaderWork.readBox_extent ok
  exact ⟨offset ▸ pos hr,body ▸ hr,tail ▸ hr⟩

-- The initial two boxes are read before the loop's box-count check. After that
-- each iteration checks the new count before passing it to either loop.
private def inner {cap : Nat} (L : Limits) (r : Reader) (a : HdrAcc) (i f : Nat)
    (hr : r.data.size ≤ cap) (ha : Saved cap a) (hi : i ≤ max 2 L.maxBoxes)
    (ceiling : max 2 L.maxBoxes + 1 ≤ cap) (wire : 2^64 ≤ cap) :
    Walk cap (Box.headerLoop L r a i f) (7*f)
      (fun z => Saved cap z.1 ∧ z.2 ≤ max 2 L.maxBoxes) := by
  match f with
  | 0 =>
    rw [Box.headerLoop]
    split
    · exact pass _ ⟨ha,hi⟩
    · exact ⟨⟨[],by simp,by intro e h; cases h; exact ⟨pos hr,by omega⟩⟩,fun _ h => by cases h⟩
  | f+1 =>
    rw [Box.headerLoop]
    split
    · exact pass _ ⟨ha,hi⟩
    rw [Nat.mul_succ,show 7*f+7 = ((7*f+2)+5)+0 by omega]
    apply chain (checked L .boxes (pos hr) (v := i+1) (by omega))
    intro _ hc
    change i+1 ≤ L.maxBoxes at hc
    apply chain (readHeader r hr wire)
    rintro ⟨b,t⟩ ⟨hp,hb,ht⟩
    apply chain (child L b a ha hp hb wire)
    intro next hn
    exact inner L t next (i+1) f ht hn (by omega) ceiling wire

private def superbox {cap : Nat} (L : Limits) (b : BoxHdr) (i : Nat) (hp : b.start ≤ cap)
    (hb : b.body.data.size ≤ cap) (hi : i ≤ max 2 L.maxBoxes)
    (ceiling : max 2 L.maxBoxes + 1 ≤ cap) (wire : 2^64 ≤ cap) :
    Walk cap (parseJp2h L b i) (1+7*(L.maxBoxes+1)) (fun z => z.2 ≤ max 2 L.maxBoxes) := by
  unfold parseJp2h
  apply chain (checked L .boxDepth hp (v := 1) (by omega))
  intro _ _
  apply chain (inner L b.body {} i _ hb (by intro _ _ h; cases h) hi ceiling wire)
  rintro ⟨a,j⟩ ⟨ha,hj⟩
  dsimp only
  cases a.ihdr with
  | none => exact leafWalk (mal hp (oneFixed _ (by decide)))
  | some ih =>
    apply leafWalk
    cases h : a.bpcc with
    | none =>
      dsimp only
      split
      · exact mal hp (oneFixed _ (by decide))
      · exact .ok _ hj
    | some pair =>
      obtain ⟨bs,p⟩ := pair
      obtain ⟨hs,hp'⟩ := ha bs p h
      dsimp only
      split
      · exact mal hp' (closeExpr (catExpr (catExpr (catExpr (litExpr _ "bpcc of ") (decExpr hs))
          (litExpr _ " entries, NC = ")) (decExpr (n := ih.nc.toNat) (by have := ih.nc.toNat_lt; omega)))
          (by decide) (by decide))
      split
      · exact mal hp (oneFixed _ (by decide))
      · exact .ok _ hj

private def topBudget (L : Limits) (hdr : Option Jp2Header) (fuel : Nat) :=
  1 + 5*fuel + if hdr.isNone then 1 + 7*(L.maxBoxes+1) else 0

private def outer {cap : Nat} (L : Limits) (r : Reader) (hdr : Option Jp2Header) (i f : Nat)
    (hr : r.data.size ≤ cap) (hi : i ≤ max 2 L.maxBoxes)
    (ceiling : max 2 L.maxBoxes + 1 ≤ cap) (wire : 2^64 ≤ cap) :
    Walk cap (topLoop L r hdr i f) (topBudget L hdr f) (fun z => z.2.start ≤ cap) := by
  match f with
  | 0 =>
    rw [topLoop]
    split
    · exact enlarge (leafWalk (mal (pos hr) (oneFixed _ (by decide)))) (by unfold topBudget; omega)
    · exact enlarge (leafWalk (limit (pos hr) (by omega))) (by unfold topBudget; omega)
  | f+1 =>
    rw [topLoop]
    split
    · exact enlarge (leafWalk (mal (pos hr) (oneFixed _ (by decide)))) (by unfold topBudget; omega)
    apply chain (checked L .boxes (pos hr) (v := i+1) (by omega))
    intro _ hc
    change i+1 ≤ L.maxBoxes at hc
    change Walk cap _ (topBudget L hdr (f+1)) _
    rw [show topBudget L hdr (f+1) = topBudget L hdr f + 5 by unfold topBudget; omega]
    apply chain (readHeader r hr wire)
    rintro ⟨b,t⟩ ⟨hp,hb,ht⟩
    dsimp only
    split
    · cases hdr with
      | none =>
        exact enlarge (leafWalk (mal hp (oneFixed _ (by decide)))) (by unfold topBudget; omega)
      | some h => exact pass _ (pos hb)
    split
    · rename_i descent
      have hn := (Bool.and_eq_true_iff.mp descent).2
      rw [show topBudget L hdr f = topBudget L (some (default : Jp2Header)) f + (1+7*(L.maxBoxes+1))
        by simp [topBudget,hn]]
      apply chain (superbox L b (i+1) hp hb (by omega) ceiling wire)
      rintro ⟨h,j⟩ hj
      exact outer L t (some h) j f ht hj ceiling wire
    · exact outer L t hdr (i+1) f ht (by omega) ceiling wire

/-- Cap on offsets, requested box count before admission, file size and unsigned XLBox.
The public admission lemmas separately account for borrowing an oversized input size. -/
def scalarCap (L : Limits) (bytes : Nat) :=
  max (2^64) (max (max 2 L.maxBoxes + 1) bytes)

/-- Uniform message allowance. The top-level loop descends into at most one JP2 header.
Each reached child has a box-header allowance and two payload events. -/
def eventBound (L : Limits) := 15 + (1 + 5*(L.maxBoxes+1)) + (1 + 7*(L.maxBoxes+1))

private def wrappedTail {cap : Nat} (L : Limits) (r : Reader) (hr : r.data.size ≤ cap)
    (ceiling : max 2 L.maxBoxes + 1 ≤ cap) (wire : 2^64 ≤ cap) :
    Walk cap (do
      let (fb,t) ← readBox r
      if fb.tbox != tFtyp then throw (malformedAt fb.start "ftyp must be the second box")
      let ft ← parseFtyp fb
      let (h,cs) ← topLoop L t none 2 (L.maxBoxes+1)
      return { codestream := cs, fileType := some ft, header := some h : Container })
      ((topBudget L none (L.maxBoxes+1) + 1) + 5) (fun c => c.codestream.start ≤ cap) := by
  apply chain (readHeader r hr wire)
  rintro ⟨b,t⟩ ⟨hp,hb,ht⟩
  dsimp only
  split
  · exact enlarge (leafWalk (mal hp (oneFixed _ (by decide)))) (by omega)
  apply chain (leafWalk (ftypLeaf b hp hb))
  intro ft _
  rw [← Nat.zero_add (topBudget L none (L.maxBoxes+1))]
  apply chain (outer L t none 2 _ ht (Nat.le_max_left ..) ceiling wire)
  rintro ⟨_,cs⟩ hs
  exact pass _ hs

private def signatureMessage := "neither a JP2 signature box nor a raw codestream (FF4F FF51)"

private def signatureError (cap : Nat) : Walk cap (.error (malformedAt 0 signatureMessage)) 1
    (fun c : Container => c.codestream.start ≤ cap) :=
  leafWalk (mal (Nat.zero_le cap) (oneFixed signatureMessage (by decide)))

private def replaced {cap : Nat} (r : Reader) (hr : r.data.size ≤ cap) (wire : 2^64 ≤ cap) :=
  earlier (readHeader r hr wire).trace (signatureError cap)

private def wrappedFile (L : Limits) (d : ByteArray) {cap : Nat} (fits : scalarCap L d.size ≤ cap)
    (input : d.size ≤ L.maxInputBytes) (wrapped : isRawCodestream d = false)
    {sig : BoxHdr} {t : Reader} (hs : readBox (Reader.ofByteArray d .box) = .ok (sig,t)) :
    Walk cap (parseFileAux L d) (eventBound L - 1) (fun c => c.codestream.start ≤ cap) := by
  let r := Reader.ofByteArray d .box
  have wire : 2^64 ≤ cap := Nat.le_trans (Nat.le_max_left ..) fits
  have outerCap : max (max 2 L.maxBoxes + 1) d.size ≤ cap := Nat.le_trans (Nat.le_max_right ..) fits
  have ceiling : max 2 L.maxBoxes + 1 ≤ cap := Nat.le_trans (Nat.le_max_left ..) outerCap
  have hd : d.size ≤ cap := Nat.le_trans (Nat.le_max_right ..) outerCap
  let budget := topBudget L none (L.maxBoxes+1)
  have budgetEq : eventBound L - 1 = 1 + (5 + ((budget + 1 + 5 + 1) + 1)) := by
    simp [budget,eventBound,topBudget]
    omega
  unfold parseFileAux
  rw [(Limits.check_eq_ok_iff L (.atOffset .box 0) .inputBytes d.size).2 input]
  change Walk cap _ (eventBound L - 1) _
  rw [budgetEq]
  -- The recognition probe drops its u32 truncation and then tries the JP2 signature.
  apply earlier (j := 5 + ((budget + 1 + 5 + 1) + 1)) (u32beTrace r (Nat.zero_le cap))
  rw [wrapped,ite_eq_right (by decide)]
  dsimp only
  let badSig := signatureError cap
  let sigBox := readHeader r hd wire
  rw [hs]
  apply earlier (j := (budget + 1 + 5 + 1) + 1) sigBox.trace
  obtain ⟨_,hb,ht⟩ := sigBox.post _ hs
  simp only [pure_bind]
  split
  · exact enlarge badSig (by omega)
  cases hv : sig.body.u32be with
  | error e =>
    have err := (leafWalk (u32be sig.body hb)).trace
    rw [hv] at err
    exact enlarge (earlier badSig.trace
      ⟨⟨err.messages,err.countBound,fun _ h => by cases h; exact err.origin e rfl⟩,
       fun _ h => by cases h⟩) (by omega)
  | ok pair =>
    obtain ⟨v,_⟩ := pair
    simp only [bind,Except.bind]
    split
    · exact enlarge badSig (by omega)
    · exact enlarge (earlier badSig.trace (wrappedTail L t ht ceiling wire)) (by omega)

/-- Events produced through the final range check of the actual container parser.
A larger common scalar cap permits direct composition with a subsequent parser. -/
def fileTrace (L : Limits) (d : ByteArray) (cap : Nat := scalarCap L d.size)
    (fits : scalarCap L d.size ≤ cap := by exact Nat.le_refl _) :
    Trace cap (Box.parseFile L d) (eventBound L) := by
  let capOK : 2^64 ≤ cap := Nat.le_trans (Nat.le_max_left ..) fits
  let hd : (Reader.ofByteArray d .box).data.size ≤ cap :=
    Nat.le_trans (Nat.le_max_right ..) (Nat.le_trans (Nat.le_max_right ..) fits)
  by_cases input : d.size ≤ L.maxInputBytes
  · have ci := (Limits.check_eq_ok_iff L (.atOffset .box 0) .inputBytes d.size).2 input
    by_cases raw : isRawCodestream d = true
    · let probe := u32beTrace (Reader.ofByteArray d .box) (Nat.zero_le cap)
      refine ⟨probe.messages,Nat.le_trans probe.countBound (by unfold eventBound; omega),?_⟩
      intro e h
      simp [Box.parseFile,parseFileAux,ci,raw,bind,Except.bind,pure,Except.pure] at h
    have wrapped := Bool.eq_false_iff.mpr raw
    by_cases good : (readBox (Reader.ofByteArray d .box)).isOk
    · cases hs : readBox (Reader.ofByteArray d .box) with
      | error e => simp [hs,Except.isOk,Except.toBool] at good
      | ok pair =>
        obtain ⟨sig,t⟩ := pair
        unfold Box.parseFile
        rw [show eventBound L = 1 + (eventBound L - 1) by unfold eventBound; omega]
        apply bindTrace (wrappedFile L d fits input wrapped hs).trace
        intro c ok
        split
        · exact doneTrace _
        · exact (leafWalk (P := fun _ : Container => True)
            (mal ((wrappedFile L d fits input wrapped hs).post c ok) (oneFixed _ (by decide)))).trace
    · let events := includeTrace (u32beTrace (Reader.ofByteArray d .box) (Nat.zero_le cap))
        (replaced _ hd capOK).trace
      refine ⟨events.messages,Nat.le_trans events.countBound (by unfold eventBound; omega),?_⟩
      intro e h
      cases hs : readBox (Reader.ofByteArray d .box) with
      | ok pair => simp [hs,Except.isOk,Except.toBool] at good
      | error _ =>
        simp only [Box.parseFile,parseFileAux,ci,wrapped,Bool.false_eq_true,↓reduceIte,
          bind,Except.bind,hs] at h
        exact events.origin e h
  · refine ⟨[],Nat.zero_le _,?_⟩
    intro e h
    simp only [Box.parseFile,parseFileAux,Limits.check,Limits.checkLe,Limits.bound,input,↓reduceIte,
      bind,Except.bind,Except.error.injEq] at h
    subst e
    exact ⟨Nat.zero_le _,Nat.le_trans (Nat.le_max_right ..) (Nat.le_trans (Nat.le_max_right ..) fits)⟩

/-- Measured conversion/copy work and temporary storage on an arbitrary container
run. The returned record carries the exact location and original error payload. -/
theorem file_bounds (L : Limits) (d : ByteArray) :
    let cap := scalarCap L d.size
    let t := fileTrace L d
    (t.messages.map (fun m => m.2.tree.work)).sum ≤ eventBound L * Text.workBound cap 128 24 ∧
    (t.messages.map (fun m => m.2.tree.storage)).sum ≤ eventBound L * Text.workBound cap 128 24 ∧
    ∀ e, Box.parseFile L d = .error e →
      storedPayload false e ≤ 6 + Text.byteBound cap 128 24 + 2*bits cap := by
  exact ⟨(trace_cost (fileTrace L d)).1,trace_storage (fileTrace L d),fun _ h => trace_retained (fileTrace L d) h⟩

/-- The decoder continuation reached by a successful container parse. -/
def afterContainer (L : Limits) (d : ByteArray) (red : Nat) (c : Container) :
    Except Error CodestreamImage := do
  let h ← Header.parseCodestreamIn L d c.codestream (if c.fileType.isSome then some c else none)
  Decode.nativeFromHeader L h d red

/-- Erasing the split at the container boundary yields the raw API on all inputs
and options, including both possible admission errors. -/
theorem raw_eq (L : Limits) (d : ByteArray) (red : Nat) :
    decodeCodestream L d red = (do
      L.check Decode.loc .decompLevels red
      let c ← Box.parseFile L d
      afterContainer L d red c) := by
  simp only [decodeCodestream,Header.parse,afterContainer,bind_assoc]

/-- A bounded suffix trace is needed only for the container actually returned.
The passed reduction check contributes zero message constructions. -/
def composeRaw (L : Limits) (d : ByteArray) (red cap k : Nat) (fits : scalarCap L d.size ≤ cap)
    (admitted : red ≤ L.maxDecompLevels)
    (tail : ∀ c, Box.parseFile L d = .ok c → Trace cap (afterContainer L d red c) k) :
    Trace cap (decodeCodestream L d red) (k + eventBound L) := by
  rw [raw_eq, (Limits.check_eq_ok_iff L Decode.loc .decompLevels red).2 admitted]
  exact (bindTrace (fileTrace L d cap fits) tail : Trace cap (Box.parseFile L d >>= afterContainer L d red) _)

/-- The public prefix reaches the container only after reduction admission.
An oversized input size is borrowed alongside the caller's limit. -/
def publicMessages (L : Limits) (d : ByteArray) (red : Nat) :
    List (Σ s, Built (scalarCap L d.size) s) :=
  if red ≤ L.maxDecompLevels then (fileTrace L d).messages else []

/-- Construction at both public entry points, including successful container paths
whose codestream or image continuation may still reject. When the container rejects,
both entry points preserve its exact error. -/
theorem public_box (L : Limits) (d : ByteArray) (opts : DecodeOptions) :
    let cap := scalarCap L d.size
    let ms := publicMessages L d opts.reduce
    (ms.map (fun m => m.2.tree.work)).sum ≤ eventBound L * Text.workBound cap 128 24 ∧
    (ms.map (fun m => m.2.tree.storage)).sum ≤ eventBound L * Text.workBound cap 128 24 ∧
    (∀ e, opts.reduce ≤ L.maxDecompLevels → Box.parseFile L d = .error e →
      decodeCodestream L d opts.reduce = .error e ∧ JPEG2000.decode L d opts = .error e ∧
      e.offset?.getD 0 ≤ cap ∧ (match e with
        | .truncated _ s | .malformed _ s | .unsupported _ s => ∃ m ∈ ms, m.1 = s
        | .limitExceeded _ _ v _ => v ≤ cap)) := by
  dsimp only
  unfold publicMessages
  split
  · rename_i red
    refine ⟨(file_bounds L d).1,(file_bounds L d).2.1,?_⟩
    intro e _ h
    have raw : decodeCodestream L d opts.reduce = .error e := by
      rw [raw_eq,(Limits.check_eq_ok_iff L Decode.loc .decompLevels opts.reduce).2 red,h]
      rfl
    exact ⟨raw,by simp only [JPEG2000.decode,raw,bind,Except.bind],(fileTrace L d).origin e h⟩
  · rename_i red
    exact ⟨Nat.zero_le _,Nat.zero_le _,fun _ h => False.elim (red h)⟩

/-- Reduction and input admission happen in order. Either refusal constructs zero
messages and retains the supplied value and limit by reference. -/
theorem public_admission_excess {L : Limits} {d : ByteArray} {opts : DecodeOptions}
    (excess : L.maxDecompLevels < opts.reduce ∨ L.maxInputBytes < d.size) :
    let e := if L.maxDecompLevels < opts.reduce then
        Error.limitExceeded Decode.loc .decompLevels opts.reduce L.maxDecompLevels
      else Error.limitExceeded (.atOffset .box 0) .inputBytes d.size L.maxInputBytes
    publicMessages L d opts.reduce = [] ∧ decodeCodestream L d opts.reduce = .error e ∧
      JPEG2000.decode L d opts = .error e ∧ storedPayload true e = 7 := by
  obtain ⟨raw,img,_⟩ := public_admission excess
  refine ⟨?_,raw,img,by split <;> rfl⟩
  by_cases over : L.maxDecompLevels < opts.reduce
  · simp [publicMessages,Nat.not_le_of_lt over]
  · have bytes := excess.resolve_left over
    simp only [publicMessages,Nat.le_of_not_gt over,↓reduceIte,fileTrace,Nat.not_le_of_lt bytes,↓reduceDIte]

private theorem castMessages {α : Type} {cap k : Nat} {r s : Except Error α} (h : r = s)
    (eq : Trace cap s k = Trace cap r k) (t : Trace cap r k) :
    (eq.mpr t).messages = t.messages := by cases h; rfl

/-- Admitted raw bytes incur no container diagnostic at all and pass their entire
extent to the actual native continuation. -/
theorem public_raw {L : Limits} {d : ByteArray} {opts : DecodeOptions}
    (red : opts.reduce ≤ L.maxDecompLevels) (input : d.size ≤ L.maxInputBytes)
    (raw : isRawCodestream d = true) :
    let c : Container := { codestream := ⟨0,d.size⟩ }
    publicMessages L d opts.reduce = [] ∧ Box.parseFile L d = .ok c ∧
      decodeCodestream L d opts.reduce = afterContainer L d opts.reduce c := by
  have ci := (Limits.check_eq_ok_iff L (.atOffset .box 0) .inputBytes d.size).2 input
  have fit : 4 ≤ d.size := by
    by_cases short : 4 ≤ d.size
    · exact short
    · simp [Box.isRawCodestream,Reader.u32be,Reader.ofByteArray,short] at raw
  have container : Box.parseFile L d = .ok { codestream := ⟨0,d.size⟩ } := by
    simp [Box.parseFile,parseFileAux,ci,raw,bind,Except.bind,pure,Except.pure]
  refine ⟨?_,container,?_⟩
  · simp [publicMessages,red,fileTrace,input,raw,u32beTrace,Reader.ofByteArray,fit,doneTrace]
    apply castMessages
    simp [Reader.u32be,Reader.ofByteArray,fit]
  · rw [raw_eq,(Limits.check_eq_ok_iff L Decode.loc .decompLevels opts.reduce).2 red,container]
    rfl

/-- On a discarded first-box failure, the measured public prefix includes the raw
recognition probe, the box read (including a failed body split), and the replacement.
Every discarded textual error occurs in this prefix as well as the returned signature. -/
theorem signature_replacement {L : Limits} {d : ByteArray} {opts : DecodeOptions} {discarded : Error}
    (red : opts.reduce ≤ L.maxDecompLevels) (input : d.size ≤ L.maxInputBytes)
    (wrapped : isRawCodestream d = false)
    (bad : readBox (Reader.ofByteArray d .box) = .error discarded) :
    let cap := scalarCap L d.size
    let r := Reader.ofByteArray d .box
    let msg := "neither a JP2 signature box nor a raw codestream (FF4F FF51)"
    let e := malformedAt 0 msg
    let box := boxTrace (cap := cap) r (by
      exact Nat.le_trans (Nat.le_max_right ..) (Nat.le_max_right ..)) (Nat.le_max_left ..)
    let emitted := (u32beTrace r (Nat.zero_le cap)).messages ++ box.messages ++
      [⟨msg,oneFixed (cap := cap) msg (by decide)⟩]
    publicMessages L d opts.reduce = emitted ∧
      decodeCodestream L d opts.reduce = .error e ∧ JPEG2000.decode L d opts = .error e ∧
      emitted.length ≤ 7 ∧ (match discarded with
        | .truncated _ s | .malformed _ s | .unsupported _ s => ∃ m ∈ emitted, m.1 = s
        | .limitExceeded _ _ v _ => v ≤ cap) := by
  obtain ⟨_,raw,img,_,_⟩ := public_signature red input wrapped bad
  let cap := scalarCap L d.size
  let r := Reader.ofByteArray d .box
  have hd : r.data.size ≤ cap := Nat.le_trans (Nat.le_max_right ..) (Nat.le_max_right ..)
  let probe := u32beTrace r (Nat.zero_le cap)
  let box := boxTrace r hd (show 2^64 ≤ cap from Nat.le_max_left ..)
  refine ⟨?_,raw,img,?_,?_⟩
  · simp only [publicMessages,red,↓reduceIte,fileTrace,input,↓reduceDIte,wrapped,bad,Bool.false_eq_true,Except.isOk]
    change probe.messages ++ (box.messages ++ [_]) = (probe.messages ++ box.messages) ++ [_]
    exact (List.append_assoc ..).symm
  · change (probe.messages ++ box.messages ++ [_]).length ≤ 7
    simp only [List.length_append,List.length_cons,List.length_nil]
    have := probe.countBound
    have := box.countBound
    omega
  · have h := (box.origin discarded bad).2
    cases discarded with
    | limitExceeded => exact h
    | _ =>
      obtain ⟨m,hm,eq⟩ := h
      exact ⟨m,List.mem_append_left _ (List.mem_append_right probe.messages hm),eq⟩

end JPEG2000.Spec.Resources.DiagnosticBox
