import JPEG2000.Marker

/-!
# Absolute positions in marker diagnostics (Plan.md §§3–5, 7, S3; T.800 Annex A)

A bounded codestream reader can start in the middle of a JP2 file. Track its stage
and both absolute endpoints through reads, segment splits and nested payload loops.
-/

namespace JPEG2000.Spec.Resources.DiagnosticMarkerOrigin

open JPEG2000.Bytes JPEG2000.Marker

private structure Inside (src r : Reader) : Prop where
  start : src.pos ≤ r.pos
  stop : r.stop ≤ src.stop
  stage : r.stage = src.stage

private def Located {α : Type} (src : Reader) (x : Except Error α) (post : α → Prop) : Prop :=
  match x with
  | .ok a => post a
  | .error e => ∃ off, e.loc = .atOffset src.stage off ∧ src.pos ≤ off ∧ off ≤ src.stop

private theorem here {src r : Reader} (hr : Inside src r) :
    ∃ off, Location.atOffset r.stage r.pos = .atOffset src.stage off ∧ src.pos ≤ off ∧ off ≤ src.stop :=
  ⟨r.pos, hr.stage ▸ rfl, hr.start, Nat.le_trans r.pos_le hr.stop⟩

private theorem seqAt {α β : Type} {src : Reader} {x : Except Error α} {f : α → Except Error β}
    {P : α → Prop} {Q : β → Prop} (hx : Located src x P)
    (hf : ∀ v, P v → Located src (f v) Q) : Located src (x >>= f) Q := by
  cases x with
  | error => exact hx
  | ok a => exact hf a hx

private abbrev Field {α : Type} (src : Reader) (x : Except Error (α × Reader)) :=
  Located src x fun v => Inside src v.2

private theorem byteAt {src r : Reader} (hr : Inside src r) : Field src r.u8 := by
  unfold Reader.u8
  split
  · exact ⟨by have := hr.start; dsimp; omega, hr.stop, hr.stage⟩
  · exact here hr

private theorem wordAt {src r : Reader} (hr : Inside src r) : Field src r.u16be := by
  unfold Reader.u16be
  split
  · exact ⟨by have := hr.start; dsimp; omega, hr.stop, hr.stage⟩
  · exact here hr

private theorem longAt {src r : Reader} (hr : Inside src r) : Field src r.u32be := by
  unfold Reader.u32be
  split
  · exact ⟨by have := hr.start; dsimp; omega, hr.stop, hr.stage⟩
  · exact here hr

private theorem requireAt {src r : Reader} (hr : Inside src r) (c : Bool) (s : String) :
    Located src (require r c s) (fun _ => True) := by
  unfold require
  split <;> first | trivial | exact here hr

private theorem endAt {src r : Reader} (hr : Inside src r) (s : String) :
    Located src (expectEnd r s) (fun _ => True) := by
  unfold expectEnd
  split <;> first | trivial | exact here hr

private theorem checkAt {src r : Reader} (hr : Inside src r) (L : Limits) (k : LimitKind) (n : Nat) :
    Located src (L.check (.atOffset r.stage r.pos) k n) (fun _ => True) := by
  unfold Limits.check Limits.checkLe
  split <;> first | trivial | exact here hr

private theorem arrayAt {α : Type} {src : Reader} {f : Reader → Except Error (α × Reader)}
    (one : ∀ {r}, Inside src r → Field src (f r)) (a : Array α) (n : Nat) {r : Reader} (hr : Inside src r) :
    Field src (readArray f a n r) := by
  induction n generalizing a r with
  | zero => exact hr
  | succ n ih =>
    have p := one hr
    rw [readArray]
    split
    · rename_i e h
      simpa only [h,Field,Located] using p
    · rename_i x t h
      exact ih _ (show Inside src t by simpa only [h,Field,Located] using p)

-- The substitution below also reduces projections of the bound pair, keeping the
-- source reader visible for each later check that reports a saved position.
local macro "fieldsAt" : tactic => `(tactic|
  repeat' first
    | apply seqAt (byteAt (by assumption)); rintro ⟨_,_⟩ h; dsimp only at h ⊢
    | apply seqAt (wordAt (by assumption)); rintro ⟨_,_⟩ h; dsimp only at h ⊢
    | apply seqAt (longAt (by assumption)); rintro ⟨_,_⟩ h; dsimp only at h ⊢
    | apply seqAt (requireAt (by assumption) _ _); intro _ _
    | apply seqAt (checkAt (by assumption) _ _ _); intro _ _
    | apply seqAt (endAt (by assumption) _); intro _ _)

private theorem segmentAt {src r : Reader} (hr : Inside src r) :
    Located src (readSegment r) (fun (b,_,t) => Inside src b ∧ Inside src t) := by
  unfold readSegment
  apply seqAt (wordAt hr)
  rintro ⟨len,mid⟩ hm
  change Inside src mid at hm
  fieldsAt
  unfold Reader.take
  split
  · rename_i fits
    exact ⟨⟨hm.start, Nat.le_trans fits hm.stop, hm.stage⟩,
      ⟨by have := hm.start; dsimp; omega, hm.stop, hm.stage⟩⟩
  · exact here hm

private theorem indexAt {src r : Reader} (hr : Inside src r) (c : Nat) : Field src (readCompIndex c r) := by
  unfold readCompIndex
  split
  · have h := byteAt hr
    split <;> rename_i eq <;> simpa only [eq,Field,Located] using h
  · exact wordAt hr

private theorem componentAt {src r : Reader} (hr : Inside src r) (c : Nat) : Field src (readComponent c r) := by
  unfold readComponent
  apply seqAt (indexAt hr c)
  rintro ⟨_,_⟩ h
  fieldsAt
  exact h

private theorem sizComponentAt {src r : Reader} (hr : Inside src r) : Field src (readSizComponent r) := by
  unfold readSizComponent
  fieldsAt
  assumption

private theorem sizAt {src r : Reader} (hr : Inside src r) (L : Limits) :
    Located src (parseSIZ L r) (fun _ => True) := by
  unfold parseSIZ
  fieldsAt
  apply seqAt (arrayAt (fun h => sizComponentAt h) _ _ (by assumption))
  rintro ⟨_,_⟩ h
  fieldsAt
  trivial

private theorem precinctAt {src r : Reader} (hr : Inside src r) : Field src (readPrecinct r) := by
  unfold readPrecinct
  fieldsAt
  assumption

private theorem styleAt {src r : Reader} (hr : Inside src r) (L : Limits) (d : Bool) :
    Field src (readCodingStyle L d r) := by
  unfold readCodingStyle
  fieldsAt
  split
  · exact here (by assumption)
  fieldsAt
  split
  case h_3 => exact here (by assumption)
  all_goals
    simp only [pure, Except.pure, bind, Except.bind]
    split
    · apply seqAt (arrayAt (fun h => precinctAt h) _ _ (by assumption))
      rintro ⟨_,_⟩ h
      fieldsAt
      exact h
    · assumption

private theorem codAt {src r : Reader} (hr : Inside src r) (L : Limits) :
    Located src (parseCOD L r) (fun _ => True) := by
  unfold parseCOD
  fieldsAt
  split
  case h_2 => exact here (by assumption)
  apply seqAt (P := fun _ => True) (show Located _ (pure _) _ from True.intro)
  intro _ _
  fieldsAt
  split
  · exact here (by assumption)
  apply seqAt (styleAt (by assumption) _ _)
  rintro ⟨_,_⟩ h
  fieldsAt
  trivial

private theorem cocAt {src r : Reader} (hr : Inside src r) (L : Limits) (c : Nat) :
    Located src (parseCOC L c r) (fun _ => True) := by
  unfold parseCOC
  apply seqAt (componentAt hr c)
  rintro ⟨_,_⟩ h
  fieldsAt
  apply seqAt (styleAt (by assumption) _ _)
  rintro ⟨_,_⟩ h
  fieldsAt
  trivial

private theorem exponentAt {src r : Reader} (hr : Inside src r) : Field src (readExponent r) := by
  unfold readExponent
  fieldsAt
  assumption

private theorem stepAt {src r : Reader} (hr : Inside src r) : Field src (readStepSize r) := by
  unfold readStepSize
  fieldsAt
  assumption

private theorem quantAt {src r : Reader} (hr : Inside src r) : Located src (readQuant r) (fun _ => True) := by
  unfold readQuant
  fieldsAt
  split
  · fieldsAt
    apply seqAt (arrayAt (fun h => exponentAt h) _ _ (by assumption))
    rintro ⟨_,_⟩ h
    fieldsAt
    trivial
  · apply seqAt (stepAt (by assumption))
    rintro ⟨_,_⟩ h
    fieldsAt
    trivial
  · fieldsAt
    apply seqAt (arrayAt (fun h => stepAt h) _ _ (by assumption))
    rintro ⟨_,_⟩ h
    fieldsAt
    trivial
  · exact here hr

private theorem qccAt {src r : Reader} (hr : Inside src r) (c : Nat) :
    Located src (parseQCC c r) (fun _ => True) := by
  unfold parseQCC
  apply seqAt (componentAt hr c)
  rintro ⟨_,t⟩ ht
  apply seqAt (quantAt ht)
  intros
  trivial

private theorem rgnAt {src r : Reader} (hr : Inside src r) (c : Nat) :
    Located src (parseRGN c r) (fun _ => True) := by
  unfold parseRGN
  apply seqAt (componentAt hr c)
  rintro ⟨_,t⟩ ht
  fieldsAt
  split
  · exact here ht
  fieldsAt
  trivial

private theorem entryAt {src r : Reader} (hr : Inside src r) (c : Nat) : Field src (readPocEntry c r) := by
  unfold readPocEntry
  fieldsAt
  apply seqAt (indexAt (by assumption) c)
  rintro ⟨_,_⟩ h
  fieldsAt
  apply seqAt (indexAt (by assumption) c)
  rintro ⟨_,_⟩ h
  fieldsAt
  split
  case h_2 => exact here (by assumption)
  apply seqAt (P := fun _ => True) (show Located _ (pure _) _ from True.intro)
  intro _ _
  fieldsAt
  assumption

private theorem pocAt {src r : Reader} (hr : Inside src r) (L : Limits) (c : Nat) :
    Located src (parsePOC L c r) (fun _ => True) := by
  unfold parsePOC
  fieldsAt
  apply seqAt (arrayAt (fun h => entryAt h c) _ _ hr)
  rintro ⟨_,_⟩ h
  fieldsAt
  trivial

private theorem comAt {src r : Reader} (hr : Inside src r) : Located src (parseCOM r) (fun _ => True) := by
  unfold parseCOM
  fieldsAt
  trivial

private theorem pairAt {src r : Reader} (hr : Inside src r) : Field src (readCrgPair r) := by
  unfold readCrgPair
  fieldsAt
  assumption

private theorem crgAt {src r : Reader} (hr : Inside src r) (c : Nat) :
    Located src (parseCRG c r) (fun _ => True) := by
  unfold parseCRG
  fieldsAt
  apply seqAt (arrayAt (fun h => pairAt h) _ _ hr)
  rintro ⟨_,_⟩ h
  fieldsAt
  trivial

private theorem addAt {src r : Reader} (hr : Inside src r) (L : Limits) (c : Nat) (a : Acc) (m : UInt16) :
    Located src (addSegment L c a m r) (fun _ => True) := by
  unfold addSegment
  by_cases hm : m == Code.COD
  · rw [ite_eq_left hm]
    fieldsAt
    apply seqAt (codAt hr L)
    intros
    trivial
  rw [ite_eq_right hm]
  repeat' split
  all_goals
    fieldsAt
    first
    | apply seqAt (cocAt hr L c)
    | apply seqAt (quantAt hr)
    | apply seqAt (qccAt hr c)
    | apply seqAt (rgnAt hr c)
    | apply seqAt (pocAt hr L c)
    | apply seqAt (comAt hr)
    | apply seqAt (crgAt hr c)
    | trivial
  all_goals intros _ _; fieldsAt; trivial

private theorem loopAt {src r : Reader} (hr : Inside src r) (L : Limits) (c f : Nat) (a : Acc) :
    Field src (segmentLoop L c f a r) := by
  induction f generalizing a r with
  | zero => exact here hr
  | succ f ih =>
    rw [segmentLoop]
    have read := wordAt hr
    split
    · rename_i e h
      simpa only [h,Field,Located] using read
    · rename_i m mid h
      have hm : Inside src mid := by simpa only [h,Field,Located] using read
      split
      · exact hr
      split
      · exact here hr
      split
      · exact ih hm _
      split
      · exact here hr
      have frame := segmentAt hm
      split
      · rename_i e hs
        simpa only [hs,Located] using frame
      · rename_i b len t hs
        have ⟨hb,ht⟩ : Inside src b ∧ Inside src t := by simpa only [hs,Located] using frame
        dsimp only
        split
        · rename_i e he
          have p := addAt hb L c {a with markers := a.markers.push ⟨m,r.pos,len+2⟩} m
          simpa only [he,Located] using p
        · exact ih ht _

/-- A successful header's tail stays in the original interval. Every rejection stores
the actual reader stage and an absolute byte position in that same closed interval,
including truncation exactly at its upper endpoint. -/
theorem main_location (L : Limits) (r : Reader) :
    match parseMainHeader L r with
    | .ok (mh,t) => r.pos ≤ t.pos ∧ t.stop ≤ r.stop ∧ t.stage = r.stage ∧ mh.endPos = t.pos
    | .error e => ∃ off, e.loc = .atOffset r.stage off ∧ r.pos ≤ off ∧ off ≤ r.stop := by
  let P := fun (v : MainHeader × Reader) =>
    r.pos ≤ v.2.pos ∧ v.2.stop ≤ r.stop ∧ v.2.stage = r.stage ∧ v.1.endPos = v.2.pos
  suffices h : Located r (parseMainHeader L r) P by
    cases hrun : parseMainHeader L r with
    | error => simpa only [hrun,Located] using h
    | ok v => cases v; simpa only [hrun,Located,P] using h
  have start : Inside r r := ⟨Nat.le_refl _, Nat.le_refl _, rfl⟩
  unfold parseMainHeader
  fieldsAt
  apply seqAt (segmentAt (by assumption))
  rintro ⟨b,_,t⟩ ⟨hb,ht⟩
  apply seqAt (sizAt hb L)
  intro _ _
  apply seqAt (loopAt ht L _ _ _)
  rintro ⟨a,last⟩ hl
  dsimp only
  split
  · split
    · exact ⟨hl.start,hl.stop,hl.stage,rfl⟩
    · exact here hl
  · exact here hl

end JPEG2000.Spec.Resources.DiagnosticMarkerOrigin
