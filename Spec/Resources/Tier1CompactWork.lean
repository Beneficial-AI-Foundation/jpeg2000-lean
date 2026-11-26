import Spec.Resources.Tier1Reader

/-!
# Reader traces for the compact Tier-1 loops (Plan.md §§3–5, 7, S3; T.800 D.1–D.7)

The compact decoder skips entire stripe columns when the bordered flag words allow it.
The trace follows each skip test and counts only the decisions of the chosen branch.
-/

namespace JPEG2000.Spec.Resources.Tier1Work

open JPEG2000 JPEG2000.Tier1 JPEG2000.Tier2.Geometry

attribute [local irreducible] JPEG2000.MQ.Dec.decode rawBit

private abbrev CellStep (step : St → Nat → St) :=
  ∀ s i, Reads 2 s.mq (step s i).mq

private abbrev ColStep (col : St → Nat → Nat → St) :=
  ∀ s i rows, Reads (rows * 6 + 8) s.mq (col s i rows).mq

private def rowReads (step : St → Nat → St) (act : CellStep step) (st : Nat) :
    (k : Nat) → (s : St) → (i : Nat) → Reads (k * 3) s.mq (colRows step st k s i).mq
  | 0, s, _ => .idle s.mq 0
  | k + 1, s, i => by
    let pre := Reads.visit 1 (act s i)
    let post := rowReads step act st k (step s i) (i + st)
    exact .weaken (.append pre post) (by omega)

private def compactZero (g : Geo) (one : UInt32) (v : Bool) (s : St) (i : Nat) :
    Reads 2 s.mq (zeroCode g one v s i).mq := by
  unfold zeroCode
  dsimp only
  split
  · exact .append (.mq _ _) (.mq _ _)
  · split <;> exact .weaken (.mq _ _) (by decide)

private def compactZeroM (g : Geo) (vc : Bool) (one : UInt32) (v : Bool) (s : St) (i : Nat) :
    Reads 2 s.mq (zeroCodeM g vc one v s i).mq := by
  unfold zeroCodeM
  dsimp only
  split
  · exact .append (.mq _ _) (.mq _ _)
  · split <;> exact .weaken (.mq _ _) (by decide)

private def sp (g : Geo) (one : UInt32) : CellStep (spStep g one) := by
  intro s i; unfold spStep; dsimp only; split
  · exact compactZero ..
  · exact .idle _ _

private def spM (g : Geo) (vc : Bool) (one : UInt32) : CellStep (spStepM g vc one) := by
  intro s i; unfold spStepM; dsimp only; split
  · exact compactZeroM ..
  · exact .idle _ _

private def cu (g : Geo) (one : UInt32) : CellStep (cuStep g one) := by
  intro s i; unfold cuStep; dsimp only; split
  · exact compactZero ..
  · exact .idle _ _

private def cuM (g : Geo) (vc : Bool) (one : UInt32) : CellStep (cuStepM g vc one) := by
  intro s i; unfold cuStepM; dsimp only; split
  · exact compactZeroM ..
  · exact .idle _ _

private def mr (one : UInt32) : CellStep (mrStep one) := by
  intro s i; unfold mrStep; dsimp only; split
  · exact .weaken (.mq _ _) (by decide)
  · exact .idle _ _

private def rawSp (g : Geo) (vc : Bool) (one : UInt32) : CellStep (rawSpStep g vc one) := by
  intro s i; unfold rawSpStep; dsimp only; split
  · split
    · exact .append (.raw _) (.raw _)
    · exact .weaken (.raw _) (by decide)
  · exact .idle _ _

private def rawMr (one : UInt32) : CellStep (rawMrStep one) := by
  intro s i; unfold rawMrStep; dsimp only; split
  · exact .weaken (.raw _) (by decide)
  · exact .idle _ _

private def skipReads (skip : St → Nat → Nat → Bool) (g : Geo) (step : St → Nat → St)
    (act : CellStep step) : ColStep (fun s i rows => if skip s i rows then s
      else colRows step g.st rows s i) := by
  intro s i rows
  apply Reads.weaken (n := rows * 3 + 5) _ (by omega)
  apply Reads.visit 5
  dsimp only; split
  · exact .idle _ _
  · exact (rowReads step act g.st rows s i).weaken (by omega)

private opaque cleanupReads (g : Geo) (step : St → Nat → St)
    (sign : St → Nat → St) (act : CellStep step)
    (signAct : ∀ s i, Reads 1 s.mq (sign s i).mq) :
    ColStep (fun s i rows =>
      if rlCond g s i rows then
        let (v, mq) := s.mq.decode 17
        if !v then { s with mq } else
          let (hi, mq) := mq.decode 18
          let (lo, mq) := mq.decode 18
          let r := (if hi then 2 else 0) + (if lo then 1 else 0)
          colRows step g.st (3 - r) (sign {s with mq} (i + r * g.st)) (i + (r + 1) * g.st)
      else colRows step g.st rows s i) := by
  intro s i rows
  apply Reads.weaken (n := (rows * 3 + 3) + 5) _ (by omega)
  apply Reads.visit 5
  dsimp only
  split
  · rename_i hr
    have hrows : rows = 4 := by
      simp only [rlCond, Bool.and_eq_true, beq_iff_eq] at hr
      exact hr.1
    generalize e : s.mq.decode 17 = v
    let a : Reads 1 s.mq v.2 := e ▸ Reads.mq s.mq 17
    split
    · exact a.weaken (by omega)
    · generalize f : v.2.decode 18 = hi
      generalize l : hi.2.decode 18 = lo
      let b1 : Reads 1 v.2 hi.2 := f ▸ Reads.mq v.2 18
      let b0 : Reads 1 hi.2 lo.2 := l ▸ Reads.mq hi.2 18
      let r := (if hi.1 then 2 else 0) + (if lo.1 then 1 else 0)
      let t := { s with mq := lo.2 }
      let a' := Reads.visit 1 (signAct t (i + r * g.st))
      let tail := rowReads step act g.st (3 - r) (sign t (i + r * g.st)) (i + (r + 1) * g.st)
      exact ((a.append (b1.append b0)).append (a'.append tail)).weaken (by omega)
  · exact (rowReads step act g.st rows s i).weaken (by omega)

private def colsReads (col : St → Nat → Nat → St) (act : ColStep col) (rows : Nat) :
    (k : Nat) → (s : St) → (i : Nat) →
      Reads (k * (rows * 6 + 8)) s.mq (scanCols col rows k s i).mq
  | 0, s, _ => .idle _ _
  | k + 1, s, i => (act s i rows |>.append
      (colsReads col act rows k (col s i rows) (i + 1))).weaken (by rw [Nat.succ_mul]; omega)

private def stripeReads (g : Geo) (col : St → Nat → Nat → St) (act : ColStep col) :
    (k : Nat) → (s : St) → (y : Nat) →
      Reads (g.w * (min (4 * k) (g.h - y) * 6 + k * 8)) s.mq
        (scanStripes col g k s y).mq
  | 0, s, _ => .idle _ _
  | k + 1, s, y => by
    let rows := min 4 (g.h - y)
    let i := (y + 1) * g.st + 1
    let a := colsReads col act rows g.w s i
    let b := stripeReads g col act k (scanCols col rows g.w s i) (y + 4)
    apply (a.append b).weaken
    rw [← Nat.mul_add]
    apply Nat.mul_le_mul_left
    dsimp only [rows]
    omega

/-- Per-pass decision and scan budget for either representation, before a segmentation symbol or
context reset. There are exactly `w*h` available cell positions and `w*ceil(h/4)` columns. -/
def passBudget (w h : Nat) : Nat := w * (h * 6 + ((h + 3) / 4) * 8)

private def scanReads (g : Geo) (col : St → Nat → Nat → St) (act : ColStep col) (s : St) :
    Reads (passBudget g.w g.h) s.mq (scanBlock col g s).mq :=
  (stripeReads g col act _ s 0).weaken (by
    apply Nat.mul_le_mul_left
    omega)

private def compactCleanup (g : Geo) (one : UInt32) : ColStep (cuCol g one) :=
  cleanupReads g _ (becomeSig g one false) (cu g one) (fun _ _ => .mq _ _)

private def compactCleanupM (g : Geo) (vc : Bool) (one : UInt32) : ColStep (cuColM g vc one) :=
  cleanupReads g _ (becomeSigM g vc one false) (cuM g vc one) (fun _ _ => .mq _ _)

/-- Read trace of the compact single-codeword pass, including run interruption and skips. -/
def compactPlainReads (g : Geo) (K : Nat) (s : St) (i : Nat) :
    Reads (passBudget g.w g.h) s.mq (JPEG2000.Tier1.runPass g K s i).mq := by
  unfold JPEG2000.Tier1.runPass
  split
  · exact scanReads g _ (skipReads _ g _ (sp g _)) s
  · exact scanReads g _ (skipReads _ g _ (mr _)) s
  · exact scanReads g _ (compactCleanup g _) s

/-- Read trace of the compact mode-aware pass. Reset and the four D.5 decisions share
the five-operation allowance with the wide pass. -/
opaque compactModeReads (m : Style) (g : Geo) (K : Nat) (s : St) (bad i : Nat) :
    Reads (passBudget g.w g.h + 5) s.mq (runPassM m g K s bad i).1.mq := by
  let one := (1 : UInt32) <<< (passPlane K i).toUInt32
  let t := if isRawPass m i then
      (match passKind i with
       | 0 => rawSigPropPass g m.vertCausal one s
       | 1 => rawMagRefPass g one s
       | _ => cleanupPassM g m.vertCausal one s)
    else
      (match passKind i with
       | 0 => sigPropPassM g m.vertCausal one s
       | 1 => magRefPass g one s
       | _ => cleanupPassM g m.vertCausal one s)
  let a : Reads (passBudget g.w g.h) s.mq t.mq := by
    dsimp only [t]; split <;> split
    · exact scanReads g _ (skipReads _ g _ (rawSp g _ _)) s
    · exact scanReads g _ (skipReads _ g _ (rawMr _)) s
    · exact scanReads g _ (compactCleanupM g _ _) s
    · exact scanReads g _ (skipReads _ g _ (spM g _ _)) s
    · exact scanReads g _ (skipReads _ g _ (mr _)) s
    · exact scanReads g _ (compactCleanupM g _ _) s
  let u := if m.segSymbols && passKind i == 2 then segSymbol t bad else (t, bad)
  let b : Reads 4 t.mq u.1.mq := by
    dsimp only [u]; split
    · exact .append (.append (.mq _ 18) (.mq _ 18)) (.append (.mq _ 18) (.mq _ 18))
    · exact .idle _ _
  let r : Reads 1 u.1.mq (runPassM m g K s bad i).1.mq := by
    unfold runPassM; dsimp only; split
    · exact .reset _
    · exact .idle _ _
  exact .append a (.append b r)

end JPEG2000.Spec.Resources.Tier1Work
