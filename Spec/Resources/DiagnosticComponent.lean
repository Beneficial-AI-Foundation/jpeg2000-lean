import Spec.Resources.DiagnosticCodeBlock

/-!
# Tile-component diagnostics (Plan.md §§3–5, 7, S3)

T.800 B.10.7 and Annex D supply the code-block inputs, E.1 and H.2 reconstruct
coefficients, and F.3 synthesises the spatial raster. Each assembly attempt
stops at its first error. A packed precision miss can restart the traversal at
its first block, including when the final spatial raster is returned successfully.
-/

namespace JPEG2000.Spec.Resources.DiagnosticComponent

open JPEG2000.Header JPEG2000.Tier2.Geometry JPEG2000.Tier2.Packet JPEG2000.Bytes
open DiagnosticCost

noncomputable section

/-- A reader entered by assembly, with the data needed to recover its source
range prefix, gathered input and metered Tier-1 calls. -/
structure ReaderVisit (L : Limits) (data : ByteArray) where
  /-- Zero-based tile-component index. -/
  component : Nat
  /-- Whether this visit decoded arbitrary-magnitude coefficient cells. -/
  wide : Bool
  /-- Effective coding parameters of this component. -/
  params : CompParams
  /-- Resolution index in the retained packet store. -/
  resolution : Nat
  /-- Orientation selected by the enclosing band record. -/
  band : Band
  /-- The packet record handed to this reader. -/
  block : CodeBlock
  /-- Bounds on its original scan, gathering, validation, passes and reads. -/
  bounded : DiagnosticCodeBlock.ReaderBounds L data params resolution band block

/-- Text constructed by a terminal error. A typed limit check emits an empty list. -/
def errorText : Error → List String
  | .malformed _ s | .unsupported _ s | .truncated _ s => [s]
  | .limitExceeded .. => []

/-- The terminal error of a stage, if it failed. -/
def errors {α : Type} : Except Error α → List Error
  | .ok _ => []
  | .error e => [e]

/-- Actual reader callbacks and ordered message expressions through this result. -/
structure Report (V : Type) {α : Type} (cap : Nat) (run : Except Error α) (count : Nat) where
  /-- One entry per invoked reader, including a failing reader and retries. -/
  visits : List V
  /-- The diagnostic constructions in production order. -/
  trace : Trace cap run count
  /-- Errors discarded by the compact-to-wide conversion, in invocation order. -/
  discarded : List Error
  /-- Every message is accounted for even on eventual success. -/
  sequence : trace.messages.map Sigma.fst = (discarded ++ errors run).flatMap errorText

-- A single attempt cannot recover from a throw. Consequently all successful
-- iterations have empty message lists and the entire attempt needs just one slot.
private structure Attempt (V : Type) {α : Type} (cap : Nat) (P : α → Prop)
    (run : Except Error α) where
  visits : List V
  trace : Trace cap run 1
  sequence : trace.messages.map Sigma.fst = (errors run).flatMap errorText
  post : ∀ a, run = .ok a → P a

variable {V α β : Type} {cap : Nat} {P : α → Prop} {S : β → Prop}

private def Attempt.report {x : Except Error α} (u : Attempt V cap P x) : Report V cap x 1 :=
  ⟨u.visits,u.trace,[],u.sequence⟩

private def success (a : α) (h : P a) : Attempt V cap P (.ok a) :=
  ⟨[],doneTrace a,rfl,fun _ eq => Except.ok.inj eq ▸ h⟩

private def chain {x : Except Error α} {f : α → Except Error β} (u : Attempt V cap P x)
    (k : ∀ a, P a → Attempt V cap S (f a)) : Attempt V cap S (x >>= f) := by
  cases x with
  | error e =>
    exact ⟨u.visits,⟨u.trace.messages,u.trace.countBound,by intro _ eq; cases eq; exact u.trace.origin _ rfl⟩,
      u.sequence,by intros; contradiction⟩
  | ok a =>
    let z := k a (u.post a rfl)
    let t := includeTrace u.trace z.trace
    have empty : u.trace.messages = [] := List.map_eq_nil_iff.mp u.sequence
    refine ⟨u.visits ++ z.visits,⟨t.messages,?_,t.origin⟩,?_,z.post⟩
    · simpa only [t,includeTrace,empty,List.nil_append] using z.trace.countBound
    · change t.messages.map Sigma.fst = (errors (f a)).flatMap errorText
      simpa only [t,includeTrace,empty,List.nil_append] using z.sequence

private theorem checked_sequence (L : Limits) (stage : Stage) (kind : LimitKind) (n : Nat)
    (bound : n ≤ cap) :
    (checkedTrace L (.at stage) kind n (Nat.zero_le _) bound).messages.map Sigma.fst =
      (errors (L.check (.at stage) kind n)).flatMap errorText := by
  have empty := (checkedTrace L (.at stage) kind n (Nat.zero_le _) bound).countBound
  rw [List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero empty)]
  unfold Limits.check Limits.checkLe
  split <;> rfl

private def failed {x : Except Error α} {e : Error} (u : Attempt V cap P x) (hx : x = .error e) :
    Attempt V cap S (.error e) := by
  cases hx
  exact ⟨u.visits,⟨u.trace.messages,u.trace.countBound,by intro _ eq; cases eq; exact u.trace.origin _ rfl⟩,
    u.sequence,by intros; contradiction⟩

private def checked (L : Limits) (stage : Stage) (kind : LimitKind) (v : Nat) (hv : v ≤ cap) :
    Attempt V cap (fun _ => True) (L.check (.at stage) kind v) := by
  let t := checkedTrace L (.at stage) kind v (Nat.zero_le _) hv
  exact ⟨[],widen t (by decide),checked_sequence L stage kind v hv,fun _ _ => trivial⟩

private def malformed (stage : Stage) {s : String} (b : Built cap s) :
    Attempt V cap P (.error (.malformed (.at stage) s)) :=
  ⟨[],⟨[⟨s,b⟩],by simp,by intro e eq; cases eq; exact ⟨Nat.zero_le _,⟨s,b⟩,by simp,rfl⟩⟩,
    rfl,by intros; contradiction⟩

private def unsupported (stage : Stage) {s : String} (b : Built cap s) :
    Attempt V cap P (.error (.unsupported (.at stage) s)) :=
  ⟨[],⟨[⟨s,b⟩],by simp,by intro e eq; cases eq; exact ⟨Nat.zero_le _,⟨s,b⟩,by simp,rfl⟩⟩,
    rfl,by intros; contradiction⟩

private def reductionText {red nl : Nat} (hr : red ≤ cap) (hl : nl ≤ cap) :
    Built cap s!"resolution reduction {red} exceeds the {nl} decomposition levels of a tile-component" :=
  closeExpr (catExpr (catExpr (catExpr (catExpr (litExpr _ "resolution reduction ") (decExpr hr))
    (litExpr _ " exceeds the ")) (decExpr hl)) (litExpr _ " decomposition levels of a tile-component"))
    (by decide) (by decide)

private def resolutionText {r nl : Nat} (hr : r ≤ cap) (hl : nl ≤ cap) :
    Built cap s!"dequantisation: resolution {r} > NL = {nl}" :=
  closeExpr (catExpr (catExpr (catExpr (litExpr _ "dequantisation: resolution ") (decExpr hr))
    (litExpr _ " > NL = ")) (decExpr hl)) (by decide) (by decide)

private def packedQuant (dst : Plane) (rc : Rect) (nl r : Nat) (b : Band) (cb : Rect)
    (q : Spec.Quant.BandQuant) (F : Nat) (o : Tier1.CodeBlockOut) (hr : r ≤ cap) (hl : nl ≤ cap) :
    Attempt V cap (fun _ => True) (JPEG2000.Quant.dequantBlock dst rc nl r b cb q F o) := by
  unfold JPEG2000.Quant.dequantBlock
  dsimp only
  repeat' first | exact malformed _ (oneFixed _ (by decide)) | exact malformed _ (resolutionText hr hl) |
    exact success _ trivial | split

private def wideQuant (L : Limits) (dst : JPEG2000.WideQuant.Plane) (p : CompParams) (d red r : Nat)
    (b : Band) (cb : Rect) (F : Nat) (cs : Array Tier1.WidePlain.Cell)
    (ha : rectArea dst.rect ≤ cap) (hl : p.levels ≤ cap) :
    Attempt V cap (fun out => out.rect = dst.rect) (JPEG2000.WideQuant.dequantBlock L dst p d red r b cb F cs) := by
  unfold JPEG2000.WideQuant.dequantBlock
  apply chain (checked L .quant _ _ ha)
  intro _ _
  apply chain (checked L .quant _ _ hl)
  intro _ _
  dsimp only
  repeat' first | exact malformed _ (oneFixed _ (by decide)) | exact success _ rfl | split

private def packedZero (L : Limits) (rc : Rect) (h : rectArea rc ≤ cap) :
    Attempt V cap (fun _ => True) (Plane.zeroChecked L Assemble.loc rc.width rc.height) := by
  unfold Plane.zeroChecked
  exact chain (checked L .assemble _ _ h) (fun _ _ => success _ trivial)

private def wideZero (L : Limits) (rc : Rect) (h : rectArea rc ≤ cap) :
    Attempt V cap (fun p => p.rect = rc) (JPEG2000.WideQuant.zeroChecked L rc) := by
  unfold JPEG2000.WideQuant.zeroChecked
  apply chain (checked L .quant _ _ h)
  intro _ _
  split
  · exact malformed _ (oneFixed _ (by decide))
  · exact success _ rfl

private def reader {x : Except Error α} (v : V) (t : Trace 0 x 1)
    (trees : (t.messages.map fun m => m.2.tree) = DiagnosticCodeBlock.literalMessages x) :
    Attempt V cap (fun _ => True) x := by
  refine ⟨[v],t.raiseCap (Nat.zero_le cap),?_,fun _ _ => trivial⟩
  have fst := congrArg (List.map Prod.fst) (t.raiseCap_events (Nat.zero_le cap))
  simp only [List.map_map,Function.comp_def] at fst
  rw [fst]
  have rendered := congrArg (List.map Text.render) trees
  simp only [List.map_map,Function.comp_def,Built.erase] at rendered
  cases x with
  | ok => exact rendered
  | error e =>
    cases e with
    | truncated loc msg =>
      -- The native reader produces only malformed and unsupported text.
      have empty : t.messages = [] := List.map_eq_nil_iff.mp trees
      obtain ⟨_,m,hm,_⟩ := t.origin _ rfl
      simp [empty] at hm
    | _ => exact rendered

private def forList (xs : List α) (f : α → β → Except Error (ForInStep β))
    (each : ∀ a ∈ xs, ∀ b, S b → Attempt V cap (fun y => S (ForInStep.value y)) (f a b))
    (z : β) (hz : S z) : Attempt V cap S (forIn xs z f) := by
  match xs with
  | [] => exact success z hz
  | a :: tail =>
    rw [List.forIn_cons]
    apply chain (each a (by simp) z hz)
    intro step h
    cases step with
    | done b => exact success b h
    | yield b => exact forList tail f (fun x hx => each x (List.mem_cons_of_mem _ hx)) b h

private def visit {nl : Nat} {ps : AssemblyCost.Store} (a : α) (ha : P a)
    (step : α → Nat → Band → CodeBlock → Except Error α)
    (each : ∀ r ≤ nl, ∀ pr ∈ ps.getD r #[], ∀ bo ∈ pr.bands, ∀ cb ∈ bo.blocks,
      ∀ z, P z → Attempt V cap P (step z r bo.band cb)) :
    Attempt V cap P (JPEG2000.WideAssembly.visitBlocks nl ps a step) := by
  unfold JPEG2000.WideAssembly.visitBlocks
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,Nat.sub_zero,
    Nat.add_one_sub_one,Nat.div_one,← Array.forIn_toList,bind_pure]
  apply forList _ _ _ a ha
  intro r hr z hz
  have bound : r ≤ nl := by
    obtain ⟨j,hj,eq⟩ := List.mem_range'.mp hr
    simp only [Nat.one_mul,Nat.zero_add] at eq
    omega
  refine chain (forList _ _ ?_ z hz) (fun _ h => success _ h)
  intro pr hp z hz
  refine chain (forList _ _ ?_ z hz) (fun _ h => success _ h)
  intro bo hb z hz
  refine chain (forList _ _ ?_ z hz) (fun _ h => success _ h)
  intro cb hc z hz
  split
  · exact chain (each r bound pr (Array.mem_toList_iff.mp hp) bo
      (Array.mem_toList_iff.mp hb) cb (Array.mem_toList_iff.mp hc) z hz) (fun _ h => success _ h)
  · exact success _ hz

private structure Inputs (L : Limits) (data : ByteArray) (tc : TileCompGeom)
    (ps : AssemblyCost.Store) (red cap : Nat) where
  component : Nat
  reduction : red ≤ cap
  levels : tc.params.levels ≤ cap
  area : rectArea (Assemble.reduceRect tc.rect red) ≤ cap
  readers : ∀ r, ∀ pr ∈ ps.getD r #[], ∀ bo ∈ pr.bands, ∀ cb ∈ bo.blocks,
    DiagnosticCodeBlock.ReaderBounds L data tc.params r bo.band cb

section
variable {L : Limits} {data : ByteArray} {tc : TileCompGeom} {ps : AssemblyCost.Store} {red : Nat}
variable (ctx : Inputs L data tc ps red cap) (d F : Nat)

private abbrev A {α : Type} := @Attempt (ReaderVisit L data) α cap

private def visitReader (wide : Bool) (r : Nat) (pr : PrecinctOut) (hp : pr ∈ ps.getD r #[])
    (bo : BandOut) (hb : bo ∈ pr.bands) (cb : CodeBlock) (hc : cb ∈ bo.blocks) : ReaderVisit L data :=
  ⟨ctx.component,wide,tc.params,r,bo.band,cb,ctx.readers r pr hp bo hb cb hc⟩

private def narrow : A (L := L) (data := data) (cap := cap) (fun _ => True)
    (JPEG2000.ReversibleDispatch.narrow L data tc d F red ps) := by
  unfold JPEG2000.ReversibleDispatch.narrow
  dsimp only
  split
  · exact unsupported _ (reductionText ctx.reduction ctx.levels)
  apply chain (packedZero L _ ctx.area)
  intro pl _
  refine chain (visit (pl,0) (P := fun _ => True) trivial _ ?_) (fun _ _ => success _ trivial)
  intro r hr pr hp bo hb cb hc z _
  apply chain (reader (visitReader ctx false r pr hp bo hb cb hc) (DiagnosticCodeBlock.compactTrace ..)
    (DiagnosticCodeBlock.reader_messages data tc.params r bo.band cb).1)
  intro o _
  exact chain (packedQuant _ _ _ _ _ _ _ _ o (Nat.le_trans hr (Nat.le_trans (Nat.sub_le ..) ctx.levels))
    (Nat.le_trans (Nat.sub_le ..) ctx.levels)) (fun _ _ => success _ trivial)

private def compactBands : A (L := L) (data := data) (cap := cap) (fun _ => True)
    (JPEG2000.IrreversibleDispatch.compactBands L data tc d F red ps) := by
  unfold JPEG2000.IrreversibleDispatch.compactBands
  apply chain (checked L .assemble _ _ (Nat.max_le.mpr ⟨ctx.reduction,ctx.levels⟩))
  intro _ _
  apply chain (packedZero L _ ctx.area)
  intro pl _
  apply visit pl trivial
  intro r hr pr hp bo hb cb hc dst _
  let u := reader (cap := cap) (visitReader ctx false r pr hp bo hb cb hc)
    (DiagnosticCodeBlock.compactTrace ..) (DiagnosticCodeBlock.reader_messages data tc.params r bo.band cb).1
  -- The irreversible caller inlines the same range guard as checkedBlock.
  unfold JPEG2000.ReversibleDispatch.checkedBlock at u
  cases h : cb.segments.all (fun s => s.ranges.all (fun rg => rg.offset + rg.length ≤ data.size)) <;>
    simp only [h,Bool.not_true,Bool.not_false,Bool.false_eq_true,↓reduceIte] at u ⊢
  · exact failed u rfl
  · apply chain u
    intro o _
    apply chain (packedQuant _ _ _ _ _ _ _ _ o (Nat.le_trans hr (Nat.le_trans (Nat.sub_le ..) ctx.levels))
      (Nat.le_trans (Nat.sub_le ..) ctx.levels))
    intro pair _
    split
    · exact success _ trivial
    · exact unsupported _ (oneFixed _ (by decide))

private def wideBands : A (L := L) (data := data) (cap := cap)
    (fun p => p.rect = Assemble.reduceRect tc.rect red) (JPEG2000.WideAssembly.tileComp L data tc d F red ps) := by
  unfold JPEG2000.WideAssembly.tileComp
  dsimp only
  split
  · exact unsupported _ (reductionText ctx.reduction ctx.levels)
  apply chain (checked L .assemble _ _ ctx.levels)
  intro _ _
  apply chain (checked L .assemble _ _ ctx.area)
  intro _ _
  apply chain (wideZero L _ ctx.area)
  intro pl rect
  apply visit pl rect
  intro r _ pr hp bo hb cb hc dst same
  apply chain (reader (visitReader ctx true r pr hp bo hb cb hc) (DiagnosticCodeBlock.wideTrace ..)
    (DiagnosticCodeBlock.reader_messages data tc.params r bo.band cb).2)
  intro cs _
  let q := wideQuant (V := ReaderVisit L data) L dst tc.params d red r bo.band cb.geom.rect F cs (same ▸ ctx.area) ctx.levels
  exact { q with post := fun out ok => (q.post out ok).trans same }

end

private def spatial53 (L : Limits) (p : JPEG2000.WideQuant.Plane) (nl : Nat)
    (hl : nl ≤ cap) (ha : rectArea p.rect ≤ cap) :
    Attempt V cap (fun _ => True) (JPEG2000.ReversibleDispatch.wideSource L p nl) := by
  unfold JPEG2000.ReversibleDispatch.wideSource
  refine chain (P := fun _ => True) ?_ ?_
  · unfold JPEG2000.WideReversible.idwt53
    apply chain (checked L .dwt _ _ hl)
    intro _ _
    apply chain (checked L .dwt _ _ ha)
    intro _ _
    split
    · exact success _ trivial
    · exact malformed _ (oneFixed _ (by decide))
  · intro q _
    split
    · exact success _ trivial
    · exact malformed _ (oneFixed _ (by decide))

private def spatial97 (L : Limits) (p : JPEG2000.WideQuant.Plane) (nl : Nat)
    (hl : nl ≤ cap) (ha : rectArea p.rect ≤ cap) :
    Attempt V cap (fun _ => True) (JPEG2000.WideDWT97.idwt97 L p nl) := by
  unfold JPEG2000.WideDWT97.idwt97
  apply chain (checked L .dwt _ _ hl)
  intro _ _
  apply chain (checked L .dwt _ _ ha)
  intro _ _
  repeat' first | exact malformed _ (oneFixed _ (by decide)) | exact success _ trivial | split

private def pureReport {k : Nat} (a : α) : Report V cap (.ok a) k := ⟨[],doneTrace a,[],rfl⟩

private def mapReport {k : Nat} {x : Except Error α} (f : α → β) (u : Report V cap x k) :
    Report V cap (f <$> x) k := by
  cases x with
  | ok a => exact ⟨u.visits,⟨u.trace.messages,u.trace.countBound,by intros; contradiction⟩,u.discarded,u.sequence⟩
  | error e => exact ⟨u.visits,⟨u.trace.messages,u.trace.countBound,
      by intro e' eq; cases eq; exact u.trace.origin _ rfl⟩,u.discarded,u.sequence⟩

private def appendReport {i j : Nat} {a : α} {y : Except Error β}
    (u : Report V cap (.ok a) i) (z : Report V cap y j) : Report V cap y (i+j) := by
  refine ⟨u.visits ++ z.visits,includeTrace u.trace z.trace,u.discarded ++ z.discarded,?_⟩
  simp only [includeTrace,List.map_append,u.sequence,z.sequence,errors,List.append_nil,
    List.flatMap_append,List.append_assoc]

private def bindReport {i j : Nat} {x : Except Error α} {f : α → Except Error β}
    (u : Report V cap x i) (k : ∀ a, x = .ok a → Report V cap (f a) j) :
    Report V cap (x >>= f) (j+i) := by
  cases x with
  | error e => exact ⟨u.visits,bindTrace u.trace fun a h => (k a h).trace,u.discarded,u.sequence⟩
  | ok a =>
    let z := appendReport u (k a rfl)
    exact ⟨z.visits,⟨z.trace.messages,Nat.add_comm i j ▸ z.trace.countBound,z.trace.origin⟩,z.discarded,z.sequence⟩

private def widenReport {i j : Nat} {x : Except Error α} (u : Report V cap x i) (h : i ≤ j) :
    Report V cap x j := ⟨u.visits,widen u.trace h,u.discarded,u.sequence⟩

-- Conversion to Option drops the error value while preserving the entire
-- attempt's callback and construction lists.
private def masked {x : Except Error α} (u : Attempt V cap P x) (result : β) :
    Report V cap (.ok result) 1 := by
  exact ⟨u.visits,⟨u.trace.messages,u.trace.countBound,by intros; contradiction⟩,errors x,
    by simpa only [errors,List.append_nil] using u.sequence⟩

private def checkReport (L : Limits) (stage : Stage) (kind : LimitKind) (n : Nat) (bound : n ≤ cap) :
    Report V cap (L.check (.at stage) kind n) 0 :=
  ⟨[],checkedTrace L (.at stage) kind n (Nat.zero_le _) bound,[],checked_sequence ..⟩

/-- The error masked at the packed attempt. Both public kernels admit the
same level and rectangle checks before entering their first reader. -/
def packedErrors (L : Limits) (data : ByteArray) (tc : TileCompGeom) (d F red : Nat)
    (ps : AssemblyCost.Store) : List Error :=
  let r := Assemble.reduceRect tc.rect red
  if red ≤ tc.params.levels ∧ tc.params.levels ≤ L.maxDecompLevels ∧ r.x0 ≤ r.x1 ∧ r.y0 ≤ r.y1 then
    match tc.params.transform with
    | .reversible53 => errors (JPEG2000.ReversibleDispatch.narrow L data tc d F red ps)
    | .irreversible97 => errors (JPEG2000.IrreversibleDispatch.compactBands L data tc d F red ps)
  else []

private abbrev WithDiscard {α : Type} (V : Type) (cap : Nat) (x : Except Error α) (k : Nat)
    (es : List Error) := { z : Report V cap x k // z.discarded = es }

private def afterOk (x : Except Error α) (rest : α → List Error) : List Error :=
  match x with
  | .error _ => []
  | .ok a => rest a

private def join {i j : Nat} {x : Except Error α} {f : α → Except Error β} {es : List Error}
    {rest : α → List Error} (u : WithDiscard V cap x i es)
    (k : ∀ a, x = .ok a → WithDiscard V cap (f a) j (rest a)) :
    WithDiscard V cap (x >>= f) (j+i) (es ++ afterOk x rest) := by
  refine ⟨bindReport u.val (fun a h => (k a h).val),?_⟩
  cases x with
  | error => exact u.property.trans (List.append_nil _).symm
  | ok a =>
    change u.val.discarded ++ (k a rfl).val.discarded = es ++ rest a
    rw [u.property,(k a rfl).property]

private def mapped {k : Nat} {x : Except Error α} {es : List Error} (f : α → β)
    (u : WithDiscard V cap x k es) : WithDiscard V cap (f <$> x) k es := by
  exact ⟨mapReport f u.val,by cases x <;> exact u.property⟩

section
variable {L : Limits} {data : ByteArray} {tc : TileCompGeom} {ps : AssemblyCost.Store} {red : Nat}
variable (ctx : Inputs L data tc ps red cap) (d F : Nat)

private def compact53 (hw : tc.params.transform = .reversible53) :
    WithDiscard (ReaderVisit L data) cap (.ok (JPEG2000.ReversibleDispatch.compactPlane? L data tc d F red ps))
      1 (packedErrors L data tc d F red ps) := by
  unfold JPEG2000.ReversibleDispatch.compactPlane? packedErrors
  dsimp only
  cases allowed : (decide (red ≤ tc.params.levels) && decide (tc.params.levels ≤ L.maxDecompLevels)) with
  | false =>
    refine ⟨pureReport none,?_⟩
    rw [ite_eq_right (fun h => by simp [h.1,h.2.1] at allowed)]
    rfl
  | true =>
    let r := Assemble.reduceRect tc.rect red
    cases ordered : (decide (r.x0 ≤ r.x1) && decide (r.y0 ≤ r.y1)) with
    | false =>
      refine ⟨pureReport none,?_⟩
      rw [ite_eq_right (fun h => by
        have : r.x0 ≤ r.x1 ∧ r.y0 ≤ r.y1 := h.2.2
        simp [this.1,this.2] at ordered)]
      rfl
    | true =>
      let run := JPEG2000.ReversibleDispatch.narrow L data tc d F red ps
      refine ⟨masked (narrow ctx d F) (run.toOption.bind Prod.fst),?_⟩
      simp only [Bool.and_eq_true,decide_eq_true_eq] at allowed ordered
      rw [ite_eq_left ⟨allowed.1,allowed.2,ordered⟩,hw]
      rfl

private def reversible (hw : tc.params.transform = .reversible53) :
    WithDiscard (ReaderVisit L data) cap (JPEG2000.ReversibleDispatch.tileComp L data tc d F red ps)
      2 (packedErrors L data tc d F red ps) := by
  unfold JPEG2000.ReversibleDispatch.tileComp
  dsimp only
  rw [ite_eq_right (by simp [hw])]
  let first := compact53 ctx d F hw
  split
  · exact ⟨appendReport first.val (pureReport (k := 1) _),(List.append_nil _).trans first.property⟩
  · refine ⟨appendReport first.val (chain (S := fun _ => True) (wideBands ctx d F) ?_).report,
      (List.append_nil _).trans first.property⟩
    intro p same
    exact spatial53 L p _ (Nat.le_trans (Nat.sub_le ..) ctx.levels) (same ▸ ctx.area)

private def compact97 : WithDiscard (ReaderVisit L data) cap
    (JPEG2000.IrreversibleDispatch.tryCompact L data tc d F red ps) 1
    (errors (JPEG2000.IrreversibleDispatch.compactBands L data tc d F red ps)) := by
  let first := compactBands ctx d F
  unfold JPEG2000.IrreversibleDispatch.tryCompact
  split <;> exact ⟨masked first _,rfl⟩

private def irreversible (hw : tc.params.transform = .irreversible97) :
    WithDiscard (ReaderVisit L data) cap (JPEG2000.IrreversibleDispatch.component L data tc d F red ps)
      2 (packedErrors L data tc d F red ps) := by
  unfold JPEG2000.IrreversibleDispatch.component
  dsimp only [↓reduceIte]
  rw [ite_eq_right (by simp [hw])]
  unfold packedErrors
  dsimp only
  let r := Assemble.reduceRect tc.rect red
  let ready := red ≤ tc.params.levels ∧ tc.params.levels ≤ L.maxDecompLevels ∧ r.x0 ≤ r.x1 ∧ r.y0 ≤ r.y1
  by_cases reduction : red > tc.params.levels
  · have no : ¬ ready := fun h => Nat.not_le_of_lt reduction h.1
    rw [ite_eq_left reduction,ite_eq_right no]
    refine ⟨widenReport (i := 1) ?_ (by decide),?_⟩
    · apply Attempt.report (P := fun _ => True)
      exact unsupported _ (oneFixed _ (by decide))
    · rfl
  rw [ite_eq_right reduction]
  cases budget : L.check Assemble.loc .decompLevels tc.params.levels with
  | error e =>
    have no : ¬ ready := by
      intro good
      have ok := (Limits.check_eq_ok_iff L Assemble.loc .decompLevels tc.params.levels).2 good.2.1
      rw [budget] at ok
      contradiction
    rw [ite_eq_right no]
    let err := failed (S := fun _ : JPEG2000.IrreversibleDispatch.Spatial => True)
      (checked (V := ReaderVisit L data) L .assemble _ _ ctx.levels) budget
    exact ⟨widenReport err.report (by decide),rfl⟩
  | ok u =>
    cases u
    have levels := (Limits.check_eq_ok_iff ..).1 budget
    change tc.params.levels ≤ L.maxDecompLevels at levels
    simp only [Equiv.ok_bind]
    by_cases inverted : r.x1 < r.x0 ∨ r.y1 < r.y0
    · have no : ¬ ready := by
        intro h
        have ordered := h.2.2
        omega
      rw [ite_eq_left inverted,ite_eq_right no]
      refine ⟨widenReport (i := 1) ?_ (by decide),?_⟩
      · apply Attempt.report (P := fun _ => True)
        exact malformed _ (oneFixed _ (by decide))
      · rfl
    · have yes : ready := ⟨by omega,levels,by omega,by omega⟩
      rw [ite_eq_right inverted,ite_eq_left yes,hw]
      let result := JPEG2000.IrreversibleDispatch.tryCompact L data tc d F red ps
      have empty (x : Except Error (Option JPEG2000.IrreversibleDispatch.Spatial)) :
          afterOk x (fun _ => []) = [] := by cases x <;> rfl
      rw [← List.append_nil (errors (JPEG2000.IrreversibleDispatch.compactBands L data tc d F red ps)),← empty result]
      apply join (j := 1) (compact97 ctx d F)
      intro attempt _
      cases attempt with
      | some q => exact ⟨pureReport q,rfl⟩
      | none =>
        refine ⟨(chain (S := fun _ => True) (wideBands ctx d F) ?_).report,rfl⟩
        intro p same
        exact chain (spatial97 L p _ (Nat.le_trans (Nat.sub_le ..) ctx.levels) (same ▸ ctx.area))
          (fun _ _ => success _ trivial)

end

private def component {L : Limits} {data : ByteArray} (h : Header) (g : Progression.Layout)
    (coding : Coding) (store : Option TileCodeBlocks) (i : Fin g.numComps) (red : Nat)
    (ctx : Inputs L data (g.comp i) (AssemblyCost.selected store i) red cap) :
    WithDiscard (ReaderVisit L data) cap (JPEG2000.TileDispatch.component L h data g coding store i red) 2
      (packedErrors L data (g.comp i) (h.siz.components.getD i default).depth.toNat
        (Assemble.fracBitsOf h.siz (coding.mctApplies h.siz) i) red (AssemblyCost.selected store i)) := by
  unfold JPEG2000.TileDispatch.component
  split
  · apply mapped
    cases store <;> exact reversible ctx _ _ (by assumption)
  · exact mapped _ (irreversible ctx _ _ (by assumption))

/-- The scalar budget covers the proposed aggregate before the tile workspace
check as well as the checked reduction, component levels and admitted planes. -/
def scalarCap (L : Limits) :=
  max L.maxDecompLevels (max L.maxWorkSamples (L.maxComponents * 2^64))

private theorem ceilBound (a b : Nat) : cdiv a b ≤ a := by
  cases b with
  | zero => simp [cdiv]
  | succ d =>
    apply Nat.le_of_lt_succ
    apply (Nat.div_lt_iff_lt_mul (Nat.succ_pos d)).2
    rw [Nat.succ_mul,Nat.mul_succ]
    omega

private theorem geometry {L : Limits} {data : ByteArray} {h : Header} {t g c}
    (parsed : Header.parse L data = .ok h) (layout : Progression.Layout.ofHeader h t = .ok (g,c))
    (red : Nat) (i : Fin g.numComps) :
    let r := Assemble.reduceRect (g.comp i).rect red
    r.x0 ≤ r.x1 ∧ r.x1 ≤ 2^32 ∧ r.y0 ≤ r.y1 ∧ r.y1 ≤ 2^32 := by
  obtain ⟨count, bounds⟩ := NativePlacement.tile_grid (red := red) parsed layout
  obtain ⟨_,x,x',_,y,y'⟩ := bounds i i.isLt
  refine ⟨x,Nat.le_trans x' ?_,y,Nat.le_trans y' ?_⟩
  · exact Nat.le_trans (ceilBound ..) (Nat.le_trans (ceilBound ..) (Nat.le_of_lt h.siz.xsiz.toNat_lt))
  · exact Nat.le_trans (ceilBound ..) (Nat.le_trans (ceilBound ..) (Nat.le_of_lt h.siz.ysiz.toNat_lt))

private theorem proposed {L : Limits} {data : ByteArray} {h : Header} {t g c}
    (parsed : Header.parse L data = .ok h) (layout : Progression.Layout.ofHeader h t = .ok (g,c))
    (red : Nat) : tileCells g red ≤ L.maxComponents * 2^64 := by
  have sum (xs : List Nat) (all : ∀ a ∈ xs, a ≤ 2^64) : xs.sum ≤ xs.length * 2^64 := by
    induction xs with
    | nil => simp
    | cons a xs ih =>
      simp only [List.sum_cons,List.length_cons,Nat.succ_mul]
      have head := all a (.head _)
      have tail := ih (fun b hb => all b (.tail _ hb))
      omega
  apply Nat.le_trans (sum _ ?_)
  · simp only [List.length_map,Array.length_toList]
    exact Nat.mul_le_mul_right _ (HeaderWork.layout_budget parsed layout).1
  · intro n hn
    obtain ⟨tc,ht,rfl⟩ := List.mem_map.mp hn
    obtain ⟨i,hi,eq⟩ := Array.getElem_of_mem (Array.mem_toList_iff.mp ht)
    have same : g.comp i = tc := by
      simpa only [Progression.Layout.comp,Array.getD_eq_getD_getElem?,Array.getElem?_eq_getElem hi,
        Option.getD_some] using eq
    obtain ⟨_,x,_,y⟩ := geometry parsed layout red ⟨i,hi⟩
    simp only [same] at x y
    change _ ≤ (2^32)*(2^32)
    exact Nat.mul_le_mul (Nat.le_trans (Nat.sub_le ..) x) (Nat.le_trans (Nat.sub_le ..) y)

private theorem prepared {L : Limits} {data : ByteArray} {red : Nat} {h dst}
    (entry : PublicPacketWork.prepareTiles L data red = .ok (h,dst)) :
    red ≤ L.maxDecompLevels ∧ Header.parse L data = .ok h := by
  unfold PublicPacketWork.prepareTiles at entry
  obtain ⟨u,checked,tail⟩ := Tier2Equiv.bind_ok entry
  obtain ⟨_,parsed,tail⟩ := Tier2Equiv.bind_ok tail
  obtain ⟨_,_,ret⟩ := Tier2Equiv.bind_ok tail
  cases ret
  cases u
  exact ⟨(Limits.check_eq_ok_iff ..).1 checked,parsed⟩

section
variable {L : Limits} {data : ByteArray} {red : Nat} {v : PacketTraversal.TileVisit}
variable (hit : v ∈ (PublicPacketWork.measure L data red).1) {h dst idx a g coding}
variable (entry : PublicPacketWork.prepareTiles L data red = .ok (h,dst))
variable (ranks : NativeCost.ranks L h = .ok idx)
variable (store : SegmentHistory.packetStore L h data idx v.tile v.cursor v.passesBefore = .ok a)
variable (layout : Progression.Layout.ofHeader h v.tile = .ok (g,coding))

private def publicInputs (admitted : tileCells g red ≤ L.maxWorkSamples) (i : Fin g.numComps) :
    Inputs L data (g.comp i) (AssemblyCost.selected a i) red (scalarCap L) := by
  have pars := (prepared entry).2
  have area := AssemblyCost.native_budget pars layout a i red
  simp only [admitted,↓reduceIte] at area
  have levels := (WideHeaderBounds.parsed_component_bounds pars layout i red).1.levels
  refine ⟨i,?_,?_,?_,?_⟩
  · exact Nat.le_trans (prepared entry).1 (Nat.le_max_left ..)
  · exact Nat.le_trans levels (Nat.le_max_left ..)
  · exact Nat.le_trans area.1 (Nat.le_trans (Nat.le_max_left ..) (Nat.le_max_right ..))
  · intro r pr hp bo hb cb hc
    exact (DiagnosticCodeBlock.public_readers hit entry ranks store layout admitted i r hp hb hc).1

/-- Trace one production component callback on the actual packet store. Each
attempt contributes at most one message and carries precisely the readers it
entered. An omitted tile supplies the empty store to both attempts. -/
def componentTrace (admitted : tileCells g red ≤ L.maxWorkSamples) (i : Fin g.numComps) :
    Report (ReaderVisit L data) (scalarCap L) (JPEG2000.TileDispatch.component L h data g coding a i red) 2 :=
  (component h g coding a i red (publicInputs hit entry ranks store layout admitted i)).val

end

/-- The packed error for the actual component parameters and selected packet store. -/
def componentErrors (L : Limits) (h : Header) (data : ByteArray) (g : Progression.Layout)
    (coding : Coding) (store : Option TileCodeBlocks) (red : Nat) (i : Fin g.numComps) : List Error :=
  packedErrors L data (g.comp i) (h.siz.components.getD i default).depth.toNat
    (Assemble.fracBitsOf h.siz (coding.mctApplies h.siz) i) red (AssemblyCost.selected store i)

/-- Collect the masked errors of each entered component in map order, including
the component that returns a definitive error. -/
def prefixErrors {n : Nat} (run : Fin n → Except Error β) (packed : Fin n → List Error) :
    (k j : Nat) → k+j = n → List Error
  | 0, _, _ => []
  | k+1, j, _ =>
    let i : Fin n := ⟨j,by omega⟩
    packed i ++ afterOk (run i) (fun _ => prefixErrors run packed k (j+1) (by omega))

private def componentMap (xs : Array α) (f : Fin xs.size → Except Error β) (packed : Fin xs.size → List Error)
    (each : ∀ i, WithDiscard V cap (f i) 2 (packed i)) (k j : Nat) (len : k+j = xs.size) (acc : Array β) :
    WithDiscard V cap (Array.mapFinIdxM.map xs (fun i _ hi => f ⟨i,hi⟩) k j len acc) (2*k)
      (prefixErrors f packed k j len) := by
  match k with
  | 0 => exact ⟨pureReport acc,rfl⟩
  | k+1 =>
    rw [Array.mapFinIdxM.map,Nat.mul_succ,prefixErrors]
    exact join (rest := fun _ => prefixErrors f packed k (j+1) (by omega)) (each ⟨j,by omega⟩)
      fun b _ => componentMap xs f packed each k (j+1) (by omega) (acc.push b)

/-- The production tile prefix ending just before colour dispatch. The work
check evaluates all reduced component rectangles before the first callback. -/
def beforeColour (L : Limits) (h : Header) (data : ByteArray) (g : Progression.Layout)
    (coding : Coding) (store : Option TileCodeBlocks) (red : Nat) := do
  L.check Assemble.loc .workSamples (tileCells g red)
  g.comps.mapFinIdxM fun i _ hi => JPEG2000.TileDispatch.component L h data g coding store ⟨i,hi⟩ red

/-- The next production continuation consumes exactly the accumulated spatial rasters. -/
theorem tile_eq (L : Limits) (h : Header) (data : ByteArray) (g : Progression.Layout)
    (coding : Coding) (store : Option TileCodeBlocks) (red : Nat) :
    JPEG2000.TileDispatch.tile L h data g coding store red =
    (beforeColour L h data g coding store red >>= JPEG2000.TileDispatch.sources L (coding.mctApplies h.siz)) := by
  unfold JPEG2000.TileDispatch.tile beforeColour
  rw [array_foldl_sum _ _ (fun _ _ => rfl)]
  simp only [bind_assoc]
  rfl

section
variable {L : Limits} {data : ByteArray} {red : Nat} {v : PacketTraversal.TileVisit}
variable (hit : v ∈ (PublicPacketWork.measure L data red).1) {h dst idx a g coding}
variable (entry : PublicPacketWork.prepareTiles L data red = .ok (h,dst))
variable (ranks : NativeCost.ranks L h = .ok idx)
variable (store : SegmentHistory.packetStore L h data idx v.tile v.cursor v.passesBefore = .ok a)
variable (layout : Progression.Layout.ofHeader h v.tile = .ok (g,coding))

/-- The independent ordered list of compact errors discarded before colour.
It is empty if the aggregate workspace check rejects. -/
def tileErrors (L : Limits) (h : Header) (data : ByteArray) (g : Progression.Layout)
    (coding : Coding) (store : Option TileCodeBlocks) (red : Nat) : List Error :=
  afterOk (L.check Assemble.loc .workSamples (tileCells g red)) fun _ =>
    prefixErrors (fun i => JPEG2000.TileDispatch.component L h data g coding store i red)
      (componentErrors L h data g coding store red) g.numComps 0 rfl

private def tileReport : WithDiscard (ReaderVisit L data) (scalarCap L)
    (beforeColour L h data g coding a red) (2*L.maxComponents) (tileErrors L h data g coding a red) := by
  have pars := (prepared entry).2
  have value := proposed pars layout red
  unfold beforeColour tileErrors
  let guardReport := checkReport (V := ReaderVisit L data) L .assemble .workSamples (tileCells g red)
    (Nat.le_trans value (show L.maxComponents * 2^64 ≤ scalarCap L from
      Nat.le_trans (Nat.le_max_right ..) (Nat.le_max_right ..)))
  let f := fun i => JPEG2000.TileDispatch.component L h data g coding a i red
  let packed := componentErrors L h data g coding a red
  let collect := g.comps.mapFinIdxM fun i _ hi => f ⟨i,hi⟩
  have next (u : Unit) (ok : L.check Assemble.loc .workSamples (tileCells g red) = .ok u) :
      WithDiscard (ReaderVisit L data) (scalarCap L) collect (2*L.maxComponents)
        (prefixErrors f packed g.numComps 0 rfl) := by
    cases u
    have admitted := (Limits.check_eq_ok_iff ..).1 ok
    let each (i : Fin g.numComps) := component h g coding a i red (publicInputs hit entry ranks store layout admitted i)
    let z := componentMap g.comps f packed each g.numComps 0 rfl (Array.emptyWithCapacity g.numComps)
    exact ⟨widenReport z.val (Nat.mul_le_mul_left 2 (HeaderWork.layout_budget pars layout).1),z.property⟩
  simpa only [List.nil_append,f,packed,collect,Assemble.loc,Nat.add_zero] using
    (join (f := fun _ => collect) (es := []) (rest := fun _ => prefixErrors f packed g.numComps 0 rfl)
      (i := 0) (j := 2*L.maxComponents) ⟨guardReport,rfl⟩ next)

/-- The complete workspace check and map prefix, stopping on the first failed
component. Previous successful components retain their discarded messages. -/
def tileTrace : Report (ReaderVisit L data) (scalarCap L)
    (beforeColour L h data g coding a red) (2*L.maxComponents) :=
  (tileReport hit entry ranks store layout).val

/-- Exact diagnostics of every reached prefix. A component emits its packed error
first and then its terminal textual error, if present. At tile scope the same order
extends across earlier successful components through the first rejection. -/
theorem messages :
    (∀ (admitted : tileCells g red ≤ L.maxWorkSamples) (i : Fin g.numComps),
      (componentTrace hit entry ranks store layout admitted i).trace.messages.map Sigma.fst =
        (componentErrors L h data g coding a red i ++
          errors (JPEG2000.TileDispatch.component L h data g coding a i red)).flatMap errorText) ∧
    (tileTrace hit entry ranks store layout).trace.messages.map Sigma.fst =
      (tileErrors L h data g coding a red ++ errors (beforeColour L h data g coding a red)).flatMap errorText := by
  constructor
  · intro admitted i
    let z := component h g coding a i red (publicInputs hit entry ranks store layout admitted i)
    exact z.val.sequence.trans (by rw [z.property]; rfl)
  · let z := tileReport hit entry ranks store layout
    exact z.val.sequence.trans (by rw [z.property])

/-- Work and logical storage of all component messages at an entered tile,
including the aggregate refusal and earlier compact errors. The source rows for
each entered reader include empty segments and stop at the first invalid range. -/
theorem public_components :
    ∃ h dst idx, ∃ (entry : PublicPacketWork.prepareTiles L data red = .ok (h,dst))
      (ranks : NativeCost.ranks L h = .ok idx),
    ∀ a g coding, ∀ (store : SegmentHistory.packetStore L h data idx v.tile v.cursor v.passesBefore = .ok a)
      (layout : Progression.Layout.ofHeader h v.tile = .ok (g,coding)),
    let z := tileTrace hit entry ranks store layout
    let cap := scalarCap L
    red ≤ L.maxDecompLevels ∧ 2^red ≤ 2^L.maxDecompLevels ∧
    tileCells g red ≤ L.maxComponents * 2^64 ∧
    (∀ i : Fin g.numComps, let rc := Assemble.reduceRect (g.comp i).rect red
      rc.x0 ≤ rc.x1 ∧ rc.x1 ≤ 2^32 ∧ rc.y0 ≤ rc.y1 ∧ rc.y1 ≤ 2^32) ∧
    (z.trace.messages.map (fun m => m.2.tree.work)).sum ≤ 2*L.maxComponents*Text.workBound cap 128 24 ∧
    (z.trace.messages.map (fun m => m.2.tree.storage)).sum ≤ 2*L.maxComponents*Text.workBound cap 128 24 ∧
    (∀ e, beforeColour L h data g coding a red = .error e →
      storedPayload false e ≤ 6 + Text.byteBound cap 128 24 + 2*bits cap) ∧
    ∀ visit ∈ z.visits, let rows := DiagnosticCodeBlock.testedRanges data visit.block
      rows.length ≤ SegmentHistory.segmentLimit L ∧ rows.flatten.length ≤ SegmentHistory.rangeLimit L := by
  obtain ⟨h,dst,idx,entry,ranks,_⟩ := NativeCost.reconstruction_storage L data red v hit
  refine ⟨h,dst,idx,entry,ranks,?_⟩
  intro a g coding store layout
  let z := tileTrace hit entry ranks store layout
  obtain ⟨hr,parsed⟩ := prepared entry
  refine ⟨hr,Nat.pow_le_pow_right (by decide) hr,proposed parsed layout red,geometry parsed layout red,
    (trace_cost z.trace).1,trace_storage z.trace,fun _ bad => trace_retained z.trace bad,?_⟩
  intro v _
  have calls := DiagnosticCodeBlock.reader_calls data v.params v.resolution v.band v.block
  exact ⟨Nat.le_trans calls.1 v.bounded.1,Nat.le_trans calls.2.1 v.bounded.2.1⟩

end

end

end JPEG2000.Spec.Resources.DiagnosticComponent
