import Spec.Tier1Wide.Segments

/-!
# Structural cost of a Tier-1 pass (Plan.md §§3–5, 7, S3; T.800 D.1–D.7)

A reader trace carries the actual starting and ending registers in its type. Each leaf
is an MQ decision, bypass decision or context reset. Composing traces adds their budgets.
The proofs construct traces along the branches and folds of the production kernels.
-/

namespace JPEG2000.Spec.Resources.Tier1Work

open JPEG2000 JPEG2000.Tier1 JPEG2000.Tier2.Geometry

/-- A bounded derivation of the reader operations within a pass. Segment initialisation
is counted separately by the segment driver. -/
inductive Reads : Nat → JPEG2000.MQ.Dec → JPEG2000.MQ.Dec → Type where
  | idle (s : JPEG2000.MQ.Dec) (n : Nat) : Reads n s s
  | mq (s : JPEG2000.MQ.Dec) (cx : Nat) : Reads 1 s (s.decode cx).2
  | raw (s : JPEG2000.MQ.Dec) : Reads 1 s (rawBit s).2
  | reset (s : JPEG2000.MQ.Dec) : Reads 1 s { s with cx := JPEG2000.MQ.tier1Contexts }
  | append {a b c : JPEG2000.MQ.Dec} {n m : Nat} :
      Reads n a b → Reads m b c → Reads (n + m) a c
  | visit {a b : JPEG2000.MQ.Dec} {n : Nat} (slots : Nat) : Reads n a b → Reads (n + slots) a b
  | weaken {a b : JPEG2000.MQ.Dec} {n m : Nat} : Reads n a b → n ≤ m → Reads m a b

/-- Number of D.3/D.5/D.6 reader calls and D.7 resets in the constructed trace. -/
def Reads.operations {n : Nat} {a b : JPEG2000.MQ.Dec} : Reads n a b → Nat
  | .idle .. => 0
  | .mq .. | .raw .. | .reset .. => 1
  | .append l r => l.operations + r.operations
  | .visit _ t | .weaken t _ => t.operations

/-- Number of raw decisions when `raw` is true, or MQ decisions otherwise. A D.7 reset
is an administrative reader operation and consumes no coded bit. -/
def Reads.decisions {n : Nat} {a b : JPEG2000.MQ.Dec} (raw : Bool) : Reads n a b → Nat
  | .idle .. | .reset .. => 0
  | .mq .. => (!raw).toNat
  | .raw .. => raw.toNat
  | .append l r => l.decisions raw + r.decisions raw
  | .visit _ t | .weaken t _ => t.decisions raw

/-- The two decision counts together fit the reader-operation charge. -/
theorem Reads.decisions_le {n : Nat} {a b : JPEG2000.MQ.Dec} (t : Reads n a b) :
    t.decisions true + t.decisions false ≤ t.operations := by
  induction t <;> simp_all only [Reads.decisions, Reads.operations, Bool.not_true, Bool.not_false,
    Bool.toNat_true, Bool.toNat_false] <;> omega

/-- Structural scan slots charged on the executed control path. The charge at a cleanup
column includes room for its eligibility and prefix traversals, even on a short circuit. -/
def Reads.slots {n : Nat} {a b : JPEG2000.MQ.Dec} : Reads n a b → Nat
  | .idle .. | .mq .. | .raw .. | .reset .. => 0
  | .append l r => l.slots + r.slots
  | .visit k t => t.slots + k
  | .weaken t _ => t.slots

/-- The trace budget covers both reader operations and cell/column traversal. -/
theorem Reads.work_le {n : Nat} {a b : JPEG2000.MQ.Dec} (t : Reads n a b) :
    t.operations + t.slots ≤ n := by
  induction t <;> simp_all only [Reads.operations, Reads.slots] <;> omega

/-- Charging unused budget never adds a reader operation. -/
theorem Reads.operations_le {n : Nat} {a b : JPEG2000.MQ.Dec} (t : Reads n a b) :
    t.operations ≤ n := by
  have := t.work_le; omega

attribute [local irreducible] JPEG2000.MQ.Dec.decode rawBit WidePlain.signCoding

private def foldReads {α σ : Type} (reader : σ → JPEG2000.MQ.Dec)
    (cost : α → Nat) (step : σ → α → σ)
    (visit : ∀ s x, Reads (cost x) (reader s) (reader (step s x))) :
    (xs : List α) → (s : σ) → Reads (xs.map cost).sum (reader s) (reader (xs.foldl step s))
  | [], s => .idle (reader s) 0
  | x :: xs, s => .append (visit s x) (foldReads reader cost step visit xs (step s x))

private def foldUniform {α σ : Type} (reader : σ → JPEG2000.MQ.Dec)
    (n : Nat) (step : σ → α → σ)
    (visit : ∀ s x, Reads n (reader s) (reader (step s x))) (xs : List α) (s : σ) :
    Reads (xs.length * n) (reader s) (reader (xs.foldl step s)) :=
  (foldReads reader (fun _ => n) step visit xs s).weaken
    (by change (xs.map (fun _ => n)).sum ≤ xs.length * n; simp [List.map_const', List.sum_replicate_nat])

private def foldCells {α : Type} (step : WidePlain.State → α → WidePlain.State)
    (act : ∀ s x, Reads 2 s.mq (step s x).mq) (xs : List α) (s : WidePlain.State) :
    Reads (xs.length * 3) s.mq (xs.foldl step s).mq :=
  foldUniform _ 3 step (fun t x => .visit 1 (act t x)) xs s

private def wideZero (w h : Nat) (b : Band) (p : Nat) (v : Bool) (s : WidePlain.State)
    (pos : Nat × Nat) : Reads 2 s.mq (WidePlain.zeroCode w h b p v s pos).mq := by
  unfold WidePlain.zeroCode
  dsimp only
  split
  · exact .append (.mq _ _) (.mq _ _)
  · exact .weaken (.mq _ _) (by decide)

private def wideProp (w h : Nat) (b : Band) (p : Nat) (s : WidePlain.State)
    (pos : Nat × Nat) : Reads 2 s.mq (WidePlain.propagate w h b p s pos).mq := by
  unfold WidePlain.propagate
  split
  · exact wideZero ..
  · exact .idle _ _

private def wideRef (w h p : Nat) (s : WidePlain.State) (pos : Nat × Nat) :
    Reads 2 s.mq (WidePlain.refineCell w h p s pos).mq := by
  unfold WidePlain.refineCell
  dsimp only
  split
  · exact .weaken (.mq _ _) (by decide)
  · exact .idle _ _

private def wideRawProp (w h p : Nat) (s : WidePlain.State) (pos : Nat × Nat) :
    Reads 2 s.mq (WideModes.rawPropagate w h p s pos).mq := by
  unfold WideModes.rawPropagate
  dsimp only
  split
  · split
    · exact .append (.raw _) (.raw _)
    · exact .weaken (.raw _) (by decide)
  · exact .idle _ _

private def wideRawRef (w h p : Nat) (s : WidePlain.State) (pos : Nat × Nat) :
    Reads 2 s.mq (WideModes.rawRefine w h p s pos).mq := by
  unfold WideModes.rawRefine
  dsimp only
  split
  · exact .weaken (.raw _) (by decide)
  · exact .idle _ _

private def wideCu (w h : Nat) (b : Band) (p : Nat) (s : WidePlain.State)
    (pos : Nat × Nat) : Reads 2 s.mq (WidePlain.cleanupCell w h b p s pos).mq := by
  unfold WidePlain.cleanupCell
  dsimp only
  split
  · exact wideZero ..
  · exact .idle _ _

private opaque tailReads (w h : Nat) (b : Band) (p : Nat) (s : WidePlain.State)
    (tail : List (Nat × Nat)) : Reads (tail.length * 3) s.mq
      (match tail with
       | [] => s
       | pos :: rest => rest.foldl (WidePlain.cleanupCell w h b p)
           (WidePlain.become w h p false s pos)).mq := by
  cases tail with
  | nil => exact .idle _ _
  | cons pos rest =>
    let sign : Reads 1 s.mq (WidePlain.become w h p false s pos).mq := .mq _ _
    exact .weaken (.append (.visit 1 sign) (foldCells _ (wideCu w h b p) rest
      (WidePlain.become w h p false s pos))) (by simp; omega)

private opaque wideColumn (w h : Nat) (b : Band) (p : Nat) (s : WidePlain.State)
    (col : List (Nat × Nat)) :
    Reads (col.length * 6 + 8) s.mq (WidePlain.cleanupColumn w h b p s col).mq := by
  apply Reads.weaken (m := col.length * 6 + 8) (n := (col.length * 3 + 3) + (col.length * 3 + 1)) _ (by omega)
  apply Reads.visit (col.length * 3 + 1)
  unfold WidePlain.cleanupColumn
  dsimp only
  split
  · generalize e : WidePlain.bit s 17 = v
    let a : Reads 1 s.mq v.2.mq := e ▸ Reads.mq s.mq 17
    split
    · exact a.weaken (by omega)
    · generalize f : WidePlain.bit v.2 18 = hi
      generalize g : WidePlain.bit hi.2 18 = lo
      let b1 : Reads 1 v.2.mq hi.2.mq := f ▸ Reads.mq v.2.mq 18
      let b0 : Reads 1 hi.2.mq lo.2.mq := g ▸ Reads.mq hi.2.mq 18
      let r := (if hi.1 then 2 else 0) + (if lo.1 then 1 else 0)
      exact ((a.append (b1.append b0)).append (tailReads w h b p lo.2 (col.drop r))).weaken
        (by simp only [List.length_drop]; omega)
  · exact .weaken (foldCells _ (wideCu w h b p) col s) (by omega)

/-- Uniform scan budget for the compact and wide kernels. It covers cell visits, sign
and magnitude decisions, column checks and the three MQ decisions of an interrupted run. -/
def columnBudget (cols : List (List (Nat × Nat))) : Nat :=
  (cols.map fun col => col.length * 6 + 8).sum

/-- The plain production pass has a reader trace bounded by its actual stripe columns. -/
def plainPassReads (w h : Nat) (b : Band) (K : Nat) (cols : List (List (Nat × Nat)))
    (s : WidePlain.State) (i : Nat) :
    Reads (columnBudget cols) s.mq (WidePlain.runPass w h b K cols s i).mq := by
  unfold WidePlain.runPass
  split
  · exact foldReads _ _ _ (fun t col =>
      (Reads.visit 1 (foldCells _ (wideProp w h b _) col t)).weaken (by omega)) cols s
  · exact foldReads _ _ _ (fun t col =>
      (Reads.visit 1 (foldCells _ (wideRef w h _) col t)).weaken (by omega)) cols s
  · exact foldReads _ _ _ (wideColumn w h b _) cols s

private def bodyReads (vc raw : Bool) (w h : Nat) (b : Band) (K : Nat)
    (cols : List (List (Nat × Nat))) (s : WidePlain.State) (i : Nat) :
    Reads (columnBudget cols) s.mq (WideModes.passBody vc raw w h b K cols s i).mq := by
  unfold WideModes.passBody
  split
  · cases raw
    · exact foldReads _ _ _ (fun t col =>
        (Reads.visit 1 (foldCells _ (wideProp w _ b _) col t)).weaken (by omega)) cols s
    · exact foldReads _ _ _ (fun t col =>
        (Reads.visit 1 (foldCells _ (wideRawProp w _ _) col t)).weaken (by omega)) cols s
  · cases raw
    · exact foldReads _ _ _ (fun t col =>
        (Reads.visit 1 (foldCells _ (wideRef w _ _) col t)).weaken (by omega)) cols s
    · exact foldReads _ _ _ (fun t col =>
        (Reads.visit 1 (foldCells _ (wideRawRef w _ _) col t)).weaken (by omega)) cols s
  · exact foldReads _ _ _ (fun t col => wideColumn w _ b _ t col) cols s

private def symbolReads (s : WideModes.State) :
    Reads 4 s.block.mq (WideModes.segSymbol s).block.mq :=
  .append (.append (.mq _ 18) (.mq _ 18)) (.append (.mq _ 18) (.mq _ 18))

/-- A pass in every style adds at most four D.5 decisions and one D.7 context reset. -/
def widePassReads (m : Style) (w h : Nat) (b : Band) (K : Nat)
    (cols : List (List (Nat × Nat))) (s : WideModes.State) (i : Nat) :
    Reads (columnBudget cols + 5) s.block.mq (WideModes.runPass m w h b K cols s i).block.mq := by
  let t : WideModes.State := { s with
    block := WideModes.passBody m.vertCausal (isRawPass m i) w h b K cols s.block i }
  let a : Reads (columnBudget cols) s.block.mq t.block.mq :=
    bodyReads _ _ _ _ _ _ _ _ _
  let u := if m.segSymbols && passKind i == 2 then WideModes.segSymbol t else t
  let z : Reads 4 t.block.mq u.block.mq := by
    dsimp only [u]; split
    · exact symbolReads t
    · exact .idle _ _
  let r : Reads 1 u.block.mq (WideModes.runPass m w h b K cols s i).block.mq := by
    unfold WideModes.runPass
    dsimp only
    split
    · exact .reset _
    · exact .idle _ _
  exact .append a (.append z r)

end JPEG2000.Spec.Resources.Tier1Work
