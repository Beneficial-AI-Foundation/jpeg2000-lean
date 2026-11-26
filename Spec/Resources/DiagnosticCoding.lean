import Spec.Resources.DiagnosticPointers

/-!
# Coding merge diagnostics (Plan.md §§3–5, 7, S3; T.800 A.6, B.12, E.1, G.2)

All message expressions in the coding merges occur inside rejecting branches. Each
successful prefix therefore builds no text. A failed prefix builds exactly the
message of its first refusal, at the main-header tail or first tile-part offset.
-/

namespace JPEG2000.Spec.Resources.DiagnosticCoding

open Bytes Marker TilePart Header Tier2Equiv DiagnosticCost

/-- Decimal operands include wire component indices, the admitted Csiz, and up to
766 bands for a byte-sized level. A short quantization table prints its actual size,
which is strictly less than the required band count on that branch. -/
def scalarCap (L : Limits) (bytes : Nat) := max bytes (max 65535 L.maxComponents)

private inductive Log (cap pos : Nat) {α : Type} : Except Error α → Type where
  | ok (a : α) : Log cap pos (.ok a)
  | bad {s : String} (built : Built cap s) : Log cap pos (.error (Header.malformed pos s))

private def Log.seq {α β : Type} {cap pos : Nat} {r : Except Error α} {f : α → Except Error β}
    (log : Log cap pos r) (next : ∀ a, Log cap pos (f a)) : Log cap pos (r >>= f) := by
  cases log with
  | ok a => exact next a
  | bad b => exact .bad b

private def Log.trace {α : Type} {cap pos : Nat} {r : Except Error α}
    (log : Log cap pos r) (h : pos ≤ cap) : Trace cap r 1 := by
  cases log with
  | ok a => exact doneTrace a
  | @bad s b =>
    exact ⟨[⟨s,b⟩],by simp,by intro e he; cases he; exact ⟨h,⟨s,b⟩,by simp,rfl⟩⟩

private def foldLog {α β : Type} {cap pos : Nat} (f : β → α → Except Error β)
    (step : ∀ a x, Log cap pos (f a x)) (xs : List α) (a : β) :
    Log cap pos (xs.foldlM f a) := by
  cases xs with
  | nil => exact .ok _
  | cons x xs => exact (step a x).seq (foldLog f step xs)

private def mapListLog {α β : Type} {cap pos : Nat} (f : α → Except Error β)
    (step : ∀ x, Log cap pos (f x)) (xs : List α) : Log cap pos (xs.mapM f) := by
  cases xs with
  | nil => exact .ok _
  | cons x xs =>
    rw [List.mapM_cons]
    exact (step x).seq fun _ => (mapListLog f step xs).seq fun _ => .ok _

private def mapLog {α β : Type} {cap pos : Nat} (f : α → Except Error β)
    (step : ∀ x, Log cap pos (f x)) (xs : Array α) : Log cap pos (xs.mapM f) := by
  rw [Array.mapM_eq_mapM_toList]
  exact (mapListLog f step xs.toList).seq fun _ => .ok _

private def overrideLog {α : Type} {cap pos c : Nat} (wire : 65535 ≤ cap) (hc : c ≤ cap)
    (name : String) (hn : name.utf8ByteSize ≤ 3) (xs : Array (UInt16 × α)) :
    Log cap pos (overrides pos name c xs) := by
  unfold overrides
  rw [← Array.foldlM_toList]
  apply foldLog
  rintro a ⟨i,v⟩
  have hi : i.toNat ≤ cap := by have := i.toNat_lt; omega
  dsimp only
  split
  · exact .ok _
  · apply Log.bad
    apply closeExpr (catExpr (catExpr (catExpr (litExpr _ "second ") (litExpr _ name))
      (litExpr _ " for component ")) (decExpr hi))
    · change 7+name.utf8ByteSize+15+0 ≤ 128; omega
    · decide
  · apply Log.bad
    apply closeExpr (catExpr (catExpr (catExpr (catExpr (litExpr _ name) (litExpr _ " component "))
      (decExpr hi)) (litExpr _ " ≥ Csiz ")) (decExpr hc))
    · change name.utf8ByteSize+11+0+10+0 ≤ 128; omega
    · decide

private def tablesLog {cap pos c : Nat} (wire : 65535 ≤ cap) (hc : c ≤ cap)
    (cs : Array COC) (qs : Array QCC) (gs : Array RGN) :
    Log cap pos (mkOverrides pos c cs qs gs) := by
  unfold mkOverrides
  apply Log.seq (overrideLog wire hc _ (by decide) _)
  intro _
  apply Log.seq (overrideLog wire hc _ (by decide) _)
  intro _
  apply Log.seq (overrideLog wire hc _ (by decide) _)
  exact fun _ => .ok _

private def bandsLog {cap pos : Nat} (wire : 65535 ≤ cap) (level : UInt8) (q : Quantization) :
    Log cap pos (bandSteps pos level.toNat q) := by
  have ln := level.toNat_lt
  have nl : level.toNat ≤ cap := by omega
  have nb : 3 * level.toNat + 1 ≤ cap := by omega
  cases q <;> simp only [bandSteps]
  case none es =>
    split
    · rename_i short
      apply Log.bad
      exact closeExpr (catExpr (catExpr (catExpr (catExpr (catExpr (decExpr (n := es.size) (by omega))
        (litExpr _ " exponents for ")) (decExpr nb)) (litExpr _ " sub-bands (NL = "))
        (decExpr nl)) (litExpr _ ")")) (by decide) (by decide)
    · exact .ok _
  case expounded ss =>
    split
    · rename_i short
      apply Log.bad
      exact closeExpr (catExpr (catExpr (catExpr (catExpr (catExpr (decExpr (n := ss.size) (by omega))
        (litExpr _ " step sizes for ")) (decExpr nb)) (litExpr _ " sub-bands (NL = "))
        (decExpr nl)) (litExpr _ ")")) (by decide) (by decide)
    · exact .ok _
  case derived b =>
    split
    · apply Log.bad
      have := b.exponent.toNat_lt
      exact closeExpr (catExpr (catExpr (catExpr (litExpr _ "derived exponent ")
        (decExpr (n := b.exponent.toNat) (by omega))) (litExpr _ " < NL − 1 = "))
        (decExpr (n := level.toNat-1) (by omega))) (by decide) (by decide)
    · exact .ok _

private def compLog {cap pos : Nat} (wire : 65535 ≤ cap) (s : CodingStyle) (q : QCD) (roi : Nat) :
    Log cap pos (mkComp pos s q roi) :=
  (bandsLog wire s.levels q.quant).seq fun _ => .ok _

private def pocLog {cap pos c : Nat} (wire : 65535 ≤ cap) (hc : c ≤ cap) (xs : Array PocEntry) :
    Log cap pos (checkPoc pos c xs) := by
  unfold checkPoc Array.forM
  rw [← Array.foldlM_toList]
  apply foldLog
  intro _ e
  split
  · exact .ok _
  · apply Log.bad
    have := e.compStart.toNat_lt
    exact closeExpr (catExpr (catExpr (catExpr (litExpr _ "POC CSpoc ")
      (decExpr (n := e.compStart.toNat) (by omega))) (litExpr _ " ≥ Csiz "))
      (decExpr hc)) (by decide) (by decide)

private def mctLog {cap pos : Nat} (s : SIZ) (c : Coding) :
    Log cap pos (checkMct pos s c) := by
  unfold checkMct
  dsimp only
  repeat' first | exact .ok _ | exact .bad (oneFixed _ (by decide)) | split

private def mainLog {cap : Nat} (wire : 65535 ≤ cap) (mh : MainHeader) (hc : mh.siz.csiz ≤ cap) :
    Log cap mh.endPos (mainCoding mh) := by
  unfold mainCoding
  apply Log.seq (tablesLog wire hc ..)
  intro _
  apply Log.seq (mapLog _ (fun _ => compLog wire ..) _)
  intro _
  apply Log.seq (pocLog wire hc _)
  intro _
  apply Log.seq (mctLog ..)
  exact fun _ => .ok _

private def tileLog {cap : Nat} (wire : 65535 ≤ cap) (mh : MainHeader) (hc : mh.siz.csiz ≤ cap)
    (mainOv : Overrides) (defaults : Coding) (t : Tile) :
    Log cap ((t.parts[0]?.map (·.pos)).getD mh.endPos) (tileCoding mh mainOv defaults t) := by
  unfold tileCoding
  apply Log.seq (pocLog wire hc _)
  intro _
  dsimp only
  split
  · exact (mctLog ..).seq fun _ => .ok _
  · apply Log.seq (tablesLog wire hc ..)
    intro _
    apply Log.seq (mapLog _ (fun _ => compLog wire ..) _)
    intro _
    exact (mctLog ..).seq fun _ => .ok _

private abbrev Positions (n : Nat) (ps : Array TilePartHeader) := ∀ p ∈ ps, p.pos ≤ n

private theorem read_positions {c : Ctx} {r t : Reader} {a z : State} {n : Nat}
    (size : r.data.size ≤ n) (old : ∀ ps ∈ a.parts, Positions n ps)
    (ok : readTilePart c a r = .ok (z,t)) : ∀ ps ∈ z.parts, Positions n ps := by
  unfold readTilePart at ok
  obtain ⟨⟨_,_⟩,_,ok⟩ := bind_ok ok
  obtain ⟨⟨_,_,_⟩,_,ok⟩ := bind_ok ok
  iterate 7 obtain ⟨_,_,ok⟩ := bind_ok ok
  dsimp only at ok
  split at ok <;> split at ok <;> try contradiction
  all_goals
    simp only [pure_bind] at ok
    obtain ⟨⟨_,_⟩,_,ok⟩ := bind_ok ok
    obtain ⟨⟨_,_⟩,_,ok⟩ := bind_ok ok
    cases ok
    intro ps hps
    obtain ⟨j,hj,rfl⟩ := Array.mem_iff_getElem.mp hps
    dsimp only
    rw [Array.getElem_modify]
    split
    · intro p hp
      rcases Array.mem_push.mp hp with mem | rfl
      · exact old _ (Array.getElem_mem _) _ mem
      · exact Nat.le_trans r.pos_le_size size
    · exact old _ (Array.getElem_mem _)

private theorem loop_positions {c : Ctx} {n : Nat} (fuel : Nat) {s z : State} {r : Reader}
    (size : r.data.size ≤ n) (old : ∀ ps ∈ s.parts, Positions n ps)
    (ok : tilePartLoop c fuel s r = .ok z) : ∀ ps ∈ z.parts, Positions n ps := by
  induction fuel generalizing s r with
  | zero => cases ok
  | succ f ih =>
    simp only [tilePartLoop] at ok
    split at ok <;> try contradiction
    split at ok
    · cases ok; exact old
    split at ok <;> try contradiction
    split at ok <;> try contradiction
    rename_i s' r' step
    exact ih ((HeaderWork.readTilePart_step step).2.2.2.1 ▸ size) (read_positions size old step) ok

private theorem assembled_parts {corr i ps t} (ok : assembleTile corr i ps = .ok t) : t.parts = ps := by
  unfold assembleTile at ok
  dsimp only at ok
  split at ok <;> split at ok <;> try contradiction
  all_goals repeat' obtain ⟨_,_,ok⟩ := bind_ok ok
  all_goals cases ok; rfl

private theorem assemble_positions {L : Limits} {n : Nat} {corr : Bool} {parts : Array (Array TilePartHeader)}
    (all : ∀ ps ∈ parts, Positions n ps) (fuel i count : Nat) (a : Array Tile)
    (old : ∀ t ∈ a, Positions n t.parts) {out} (ok : assembleTiles L corr parts fuel i count a = .ok out) :
    ∀ t ∈ out, Positions n t.parts := by
  induction fuel generalizing a i count with
  | zero => cases ok; exact old
  | succ f ih =>
    simp only [assembleTiles] at ok
    split at ok
    · exact ih _ _ _ old ok
    split at ok <;> try contradiction
    rename_i t ht
    split at ok <;> try contradiction
    apply ih _ _ _ _ ok
    intro x mem
    rcases Array.mem_push.mp mem with mem | rfl
    · exact old _ mem
    · rw [assembled_parts ht]
      cases get : parts[i]? with
      | none => simp [Positions]
      | some z => exact all _ (Array.mem_of_getElem? get)

/-- Every assembled part retains the absolute position of its source SOT reader.
This holds immediately after tile-part assembly, even if the subsequent merge fails. -/
theorem tile_positions {L : Limits} {mh : MainHeader} {r : Reader} {out : Array Tile}
    (ok : parseTileParts L mh r = .ok out) :
    ∀ t ∈ out, ∀ p ∈ t.parts, p.pos ≤ r.data.size := by
  unfold parseTileParts at ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  obtain ⟨_,loop,ok⟩ := bind_ok ok
  apply assemble_positions (loop_positions _ (Nat.le_refl _) _ loop) _ _ _ _ (by simp) ok
  intro ps hp
  obtain ⟨_,rfl⟩ := Array.mem_replicate.mp hp
  simp [Positions]

/-- The trace of a coding call together with its absolute marker location and the
exact list of constructions on both return paths. -/
structure MergeTrace {α : Type} (cap bytes pos : Nat) (run : Except Error α) extends Trace cap run 1 where
  /-- The diagnostic position is in the source buffer. -/
  position : pos ≤ bytes
  /-- Success constructs nothing. A refusal constructs precisely its one returned
  malformed payload with the computed position. -/
  events : match run with
    | .ok _ => toTrace.messages = []
    | .error e => ∃ m, toTrace.messages = [m] ∧ e = Header.malformed pos m.1

private theorem success_events {α : Type} {cap n pos : Nat} {run : Except Error α}
    (tr : MergeTrace cap n pos run) {a : α} (ok : run = .ok a) : tr.messages = [] := by
  cases ok
  exact tr.events

/-- A refusing merge retains exactly its one construction, the marker offset and
the bounded stored record. This applies to a rejected tile before header validation. -/
theorem merge_refusal {α : Type} {cap bytes pos : Nat} {run : Except Error α}
    (t : MergeTrace cap bytes pos run) {e : Error} (err : run = .error e) :
    e.offset? = some pos ∧ pos ≤ bytes ∧
    storedPayload false e ≤ 6 + Text.byteBound cap 128 24 + 2*bits cap ∧
    ∃ m, t.messages = [m] ∧ e = Header.malformed pos m.1 := by
  cases err
  obtain ⟨m,hm,rfl⟩ := t.events
  exact ⟨rfl,t.position,trace_retained t.toTrace rfl,m,hm,rfl⟩

private def certify {α : Type} {L : Limits} {n pos : Nat} {run : Except Error α}
    (log : Log (scalarCap L n) pos run) (loc : pos ≤ n) : MergeTrace (scalarCap L n) n pos run := by
  refine ⟨log.trace (Nat.le_trans loc (Nat.le_max_left ..)),loc,?_⟩
  cases log with
  | ok => rfl
  | bad b => exact ⟨⟨_,b⟩,rfl,rfl⟩

private theorem parsed_count {L : Limits} {r t : Reader} {mh : MainHeader}
    (ok : parseMainHeader L r = .ok (mh,t)) (n : Nat) : mh.siz.csiz ≤ scalarCap L n := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,limit⟩ := DiagnosticMarker.main_source ok
  exact Nat.le_trans limit (Nat.le_trans (Nat.le_max_right ..) (Nat.le_max_right ..))

private theorem end_pos {L : Limits} {d : ByteArray} {rg : ByteRange} {r t : Reader} {mh : MainHeader}
    (range : rangeReader d rg = .ok r) (main : parseMainHeader L r = .ok (mh,t)) : mh.endPos ≤ d.size :=
  (DiagnosticMarker.range_source range).1 ▸ (DiagnosticPointers.main_ranges main).2.2

/-- The main merge in the range parser, including a refusal before pointer inspection. -/
def mainTrace {L : Limits} {d : ByteArray} {rg : ByteRange} {r tail : Reader} {mh : MainHeader}
    (range : rangeReader d rg = .ok r) (main : parseMainHeader L r = .ok (mh,tail)) :
    MergeTrace (scalarCap L d.size) d.size mh.endPos (mainCoding mh) :=
  certify (mainLog (by unfold scalarCap; omega) mh (parsed_count main _)) (end_pos range main)

/-- The second collection uses the same main marker arrays and the main tail offset. -/
def overridesTrace {L : Limits} {d : ByteArray} {rg : ByteRange} {r tail : Reader} {mh : MainHeader}
    (range : rangeReader d rg = .ok r) (main : parseMainHeader L r = .ok (mh,tail)) :
    MergeTrace (scalarCap L d.size) d.size mh.endPos
      (mkOverrides mh.endPos mh.siz.csiz mh.coc mh.qcc mh.rgn) :=
  certify (tablesLog (by unfold scalarCap; omega) (parsed_count main _) ..) (end_pos range main)

/-- Successful default coding proves that repeating the collection after tile assembly
succeeds and constructs no text, although the override tables are rebuilt. -/
theorem repeated_overrides {L : Limits} {d : ByteArray} {rg : ByteRange} {r tail : Reader}
    {mh : MainHeader} {defaults : Coding}
    (range : rangeReader d rg = .ok r) (main : parseMainHeader L r = .ok (mh,tail))
    (ok : mainCoding mh = .ok defaults) :
    ∃ ov, mkOverrides mh.endPos mh.siz.csiz mh.coc mh.qcc mh.rgn = .ok ov ∧
      (overridesTrace range main).messages = [] := by
  unfold mainCoding at ok
  obtain ⟨ov,success,_⟩ := bind_ok ok
  exact ⟨ov,success,success_events (overridesTrace range main) success⟩

/-- A tile callback of the actual assembled array. The trace follows tile POC
replacement, shared default components, and the production COD/COC, QCD/QCC and
RGN precedence. The result may be the first tile refusal. -/
def tileTrace {L : Limits} {d : ByteArray} {rg : ByteRange} {r tail : Reader} {mh : MainHeader}
    (range : rangeReader d rg = .ok r) (main : parseMainHeader L r = .ok (mh,tail))
    {tiles : Array Tile} (parsed : parseTileParts L mh tail = .ok tiles) {t : Tile} (member : t ∈ tiles)
    (mainOv : Overrides) (defaults : Coding) :
    MergeTrace (scalarCap L d.size) d.size ((t.parts[0]?.map (·.pos)).getD mh.endPos)
      (tileCoding mh mainOv defaults t) := by
  apply certify (tileLog (by unfold scalarCap; omega) mh (parsed_count main _) ..)
  cases hit : t.parts[0]? with
  | none => exact end_pos range main
  | some p =>
    have src := (DiagnosticMarker.main_source main).1.trans (DiagnosticMarker.range_source range).1
    exact src ▸ tile_positions parsed t member p (Array.mem_of_getElem? hit)

private abbrev Events (cap : Nat) := { xs : List (Σ s, Built cap s) // xs.length ≤ 1 }

private def silent (cap : Nat) : Events cap := ⟨[],Nat.zero_le _⟩

-- A successful coding call has an empty prefix (MergeTrace.events). Only a refusal
-- can contribute an event, and its continuation is never visited.
private def continueMerge {α : Type} {cap n pos : Nat} {run : Except Error α}
    (tr : MergeTrace cap n pos run) (next : α → Events cap) : Events cap :=
  match run with
  | .error _ => ⟨tr.messages,tr.countBound⟩
  | .ok a => next a

private def tileEvents {L : Limits} {d : ByteArray} {rg : ByteRange} {r tail : Reader}
    {mh : MainHeader} (range : rangeReader d rg = .ok r) (main : parseMainHeader L r = .ok (mh,tail))
    {tiles : Array Tile} (parsed : parseTileParts L mh tail = .ok tiles) (ov : Overrides) (defaults : Coding)
    (remaining : List Tile) (member : ∀ t ∈ remaining, t ∈ tiles) : Events (scalarCap L d.size) :=
  match remaining with
  | [] => silent _
  | t :: ts => continueMerge (tileTrace range main parsed (member t (.head _)) ov defaults) fun _ =>
    tileEvents range main parsed ov defaults ts (fun x hx => member x (.tail _ hx))

/-- Construction events of just the coding merges on public bytes. Non-coding calls
gate the visits. Tiles are traversed in array order with the actual admitted
defaults and the result of the repeated override collection. -/
def publicEvents (L : Limits) (d : ByteArray) (red : Nat) :
    { xs : List (Σ s, Built (scalarCap L d.size) s) // xs.length ≤ 1 } :=
  match L.check Decode.loc .decompLevels red with
  | .error _ => silent _
  | .ok () =>
    match Box.parseFile L d with
    | .error _ => silent _
    | .ok c =>
      match range : rangeReader d ⟨c.codestream.start,c.codestream.len⟩ with
      | .error _ => silent _
      | .ok r =>
        match main : parseMainHeader L r with
        | .error _ => silent _
        | .ok (mh,tail) =>
          match checkGeometry L mh with
          | .error _ => silent _
          | .ok () => continueMerge (mainTrace range main) fun defaults =>
            match parsePointers L mh d with
            | .error _ => silent _
            | .ok _ =>
              match parsed : parseTileParts L mh tail with
              | .error _ => silent _
              | .ok tiles => continueMerge (overridesTrace range main) fun ov =>
                tileEvents range main parsed ov defaults tiles.toList (by simp)

/-- The decimal values actually interpolated, in append order. -/
def decimalOperands : Text → List Nat
  | .dec n => [n]
  | .cat l r => decimalOperands l ++ decimalOperands r
  | _ => []

private theorem operand_bound {cap lit nodes : Nat} {t : Text} (shape : t.Within cap lit nodes) :
    ∀ n ∈ decimalOperands t, n ≤ cap := by
  induction shape with
  | fixed | boxName | hex => simp [decimalOperands]
  | dec h => simpa [decimalOperands] using h
  | cat _ _ left right =>
    intro n hn
    rcases List.mem_append.mp hn with hl | hr
    · exact left _ hl
    · exact right _ hr

/-- Each reached decimal conversion uses its actual numeric operand, with digit
length and conversion work bounded in the caller's limits and source byte count. -/
theorem public_digits (L : Limits) (d : ByteArray) (red : Nat) :
    let cap := scalarCap L d.size
    ∀ m ∈ (publicEvents L d red).val, ∀ n ∈ decimalOperands m.2.tree,
      n ≤ cap ∧ (Nat.toDigits 10 n).length ≤ bits cap ∧
      digitWork 10 (n+1) n ≤ bits cap * (32+16*bits (cap+1)) := by
  intro cap m _ n hn
  have h := operand_bound m.2.shape n hn
  exact ⟨h,(radix_cost (base := 10) (by decide) h).2⟩

/-- Add coding diagnostics to the existing parser work account, which already prices
the first merge at `HeaderPayload.mainCodingBudget`, each reached tile merge at
`HeaderPayload.tileCodingBudget`, and the repeated tables at `HeaderPayload.overrideBudget`.
Even across all tiles, at most one coding interpolation is built. The allocation
bound includes decimal conversion and intermediate appends. -/
theorem public_cost (L : Limits) (d : ByteArray) (red : Nat) :
    let xs := (publicEvents L d red).val
    let bound := Text.workBound (scalarCap L d.size) 128 24
    let payload := if red ≤ L.maxDecompLevels then (HeaderPayload.headerPayload L d).run.2 else 0
    payload + (xs.map (fun m => m.2.tree.work)).sum ≤ HeaderPayload.headerBudget L d.size + bound ∧
      (xs.map (fun m => m.2.tree.storage)).sum ≤ bound := by
  dsimp only
  let xs := publicEvents L d red
  have costs {cap : Nat} (xs : List (Σ s, Built cap s)) (length : xs.length ≤ 1) :
      (xs.map (fun m => m.2.tree.work)).sum ≤ Text.workBound cap 128 24 ∧
      (xs.map (fun m => m.2.tree.storage)).sum ≤ Text.workBound cap 128 24 := by
    cases xs with
    | nil => exact ⟨Nat.zero_le _,Nat.zero_le _⟩
    | cons m rest =>
      cases rest with
      | nil =>
        have cost := (built_cost m.2).2
        simpa using And.intro cost (Nat.le_trans m.2.tree.storage_le_work cost)
      | cons => simp at length
  obtain ⟨work,storage⟩ := costs xs.val xs.property
  refine ⟨Nat.add_le_add ?_ work,storage⟩
  split
  · exact (HeaderPayload.headerPayload L d).bound
  · exact Nat.zero_le _

/-- A reached early refusal is returned by the public decoder before the pointer
parser runs. Its byte position is exactly the parsed main tail, and the recorded
singleton retains the complete interpolation. -/
theorem main_refusal {L : Limits} {d : ByteArray} {opts : DecodeOptions} {c : Box.Container}
    {r tail : Reader} {mh : MainHeader} {e : Error}
    (red : L.check Decode.loc .decompLevels opts.reduce = .ok ()) (box : Box.parseFile L d = .ok c)
    (range : rangeReader d ⟨c.codestream.start,c.codestream.len⟩ = .ok r)
    (main : parseMainHeader L r = .ok (mh,tail)) (geom : checkGeometry L mh = .ok ())
    (bad : mainCoding mh = .error e) :
    DiagnosticPointers.pointerInput L d opts.reduce = .error e ∧
      Header.parse L d = .error e ∧ decodeCodestream L d opts.reduce = .error e ∧ JPEG2000.decode L d opts = .error e ∧
      e.offset? = some mh.endPos ∧ mh.endPos ≤ d.size ∧
      ∃ m, (publicEvents L d opts.reduce).val = [m] ∧ e = Header.malformed mh.endPos m.1 := by
  let tr := mainTrace range main
  obtain ⟨off,loc,_,m,events,err⟩ := merge_refusal tr bad
  have hp : Header.parse L d = .error e := by
    simp only [Header.parse,box,parseCodestreamIn,range,main,geom,bad,bind,Except.bind]
  have raw : decodeCodestream L d opts.reduce = .error e := by
    simp only [decodeCodestream,red,hp,bind,Except.bind]
  refine ⟨by simp only [DiagnosticPointers.pointerInput,red,box,range,main,geom,bad,bind,Except.bind],
    hp,raw,by simp only [JPEG2000.decode,raw,bind,Except.bind],off,loc,m,?_,err⟩
  simp only [publicEvents,red,box]
  split <;> rename_i h <;> rw [range] at h <;> cases h
  split <;> rename_i h <;> rw [main] at h <;> cases h
  rw [geom]
  have refused {α : Type} {cap n pos : Nat} {run : Except Error α} (t : MergeTrace cap n pos run)
      (next : α → Events cap) (err : run = .error e) : (continueMerge t next).val = t.messages := by
    cases err
    rfl
  exact (refused tr _ bad).trans events

-- One-component SIZ, default COD with the supplied level, and one QCD exponent.
private def oneExponent (level : UInt8) : Array UInt8 := #[
    0xFF,0x4F, 0xFF,0x51,0,41, 0,0,
    0,0,0,1, 0,0,0,1, 0,0,0,0, 0,0,0,0,
    0,0,0,1, 0,0,0,1, 0,0,0,0, 0,0,0,0, 0,1,7,1,1,
    0xFF,0x52,0,12, 0,0,0,1,0,level,2,2,0,1,
    0xFF,0x5C,0,4, 0x40,0x40]

/-- One level needs four exponents. The main header also retains an empty PPM
segment and ends at its SOT marker at byte 69. -/
def shortQuantization : ByteArray := ⟨oneExponent 1 ++ #[0xFF,0x60,0,2, 0xFF,0x90]⟩

/-- A rejected public merge retains the available count, required count and level.
The malformed PPM is never inspected and incurs no pointer work or diagnostic. -/
theorem short_quantization_refusal :
    let e := Header.malformed 69 "1 exponents for 4 sub-bands (NL = 1)"
    Header.parse Limits.default shortQuantization = .error e ∧
      DiagnosticPointers.pointerInput Limits.default shortQuantization 0 = .error e ∧
      DiagnosticPointers.publicCharge Limits.default shortQuantization 0 = (0,[]) ∧
      ((publicEvents Limits.default shortQuantization 0).val.map fun m => m.2.tree) =
        [.cat (.cat (.cat (.cat (.cat (.dec 1) (.fixed " exponents for ")) (.dec 4))
          (.fixed " sub-bands (NL = ")) (.dec 1)) (.fixed ")")] := by
  have rejected : DiagnosticPointers.pointerInput Limits.default shortQuantization 0 =
      .error (Header.malformed 69 "1 exponents for 4 sub-bands (NL = 1)") := by rfl'
  refine ⟨?_,rejected,?_,?_⟩
  · rfl'
  · unfold DiagnosticPointers.publicCharge
    split <;> rename_i h <;> rw [rejected] at h <;> cases h
  · rfl'

/-- The main's one exponent covers level zero. The tile COD selects two levels
and inherits that main QCD, producing a short table at the tile's SOT offset. -/
def shortTileQuantization : ByteArray := ⟨oneExponent 0 ++ #[
    0xFF,0x90,0,10,0,0,0,0,0,28,0,1,
    0xFF,0x52,0,12,0,0,0,1,0,2,2,2,0,1,
    0xFF,0x93,0xFF,0xD9]⟩

/-- The inherited QCD is refused on the actual tile path after the successful
default merge and repeated override collection. Only the tile's three operands
are rendered, in available-count, required-count and level order. -/
theorem inherited_quantization_refusal :
    Header.parse Limits.default shortTileQuantization =
      .error (Header.malformed 65 "1 exponents for 7 sub-bands (NL = 2)") ∧
      ((publicEvents Limits.default shortTileQuantization 0).val.map fun m =>
        decimalOperands m.2.tree) = [[1,7,2]] := by
  constructor <;> rfl'

end JPEG2000.Spec.Resources.DiagnosticCoding
