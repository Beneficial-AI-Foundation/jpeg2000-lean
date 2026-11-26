import Spec.Resources.DiagnosticCost
import Spec.Resources.DiagnosticMarkerOrigin

/-!
# Main-header diagnostic construction (Plan.md §§3–5, 7, S3; T.800 Annex A)

Each trace follows the binds and branches of the corresponding marker reader. For
length-bearing segments, the body and the following reader share the original byte
array. The bounds on decimal and hexadecimal operands therefore apply before admission,
including on truncated bodies. Successful requirements retain their construction event.
-/

namespace JPEG2000.Spec.Resources.DiagnosticMarker

open JPEG2000.Bytes JPEG2000.Marker DiagnosticCost

private theorem pos {cap : Nat} {r : Reader} (h : r.data.size ≤ cap) : r.pos ≤ cap :=
  Nat.le_trans r.pos_le_size h

private theorem rem {cap : Nat} {r : Reader} (h : r.data.size ≤ cap) : r.remaining ≤ cap :=
  Nat.le_trans (Nat.sub_le ..) (Nat.le_trans r.stop_le h)

private theorem byte {cap : Nat} (wire : 65535 ≤ cap) (x : UInt8) : x.toNat ≤ cap := by
  have := x.toNat_lt
  omega

private theorem word {cap : Nat} (wire : 65535 ≤ cap) (x : UInt16) : x.toNat ≤ cap := by
  have := x.toNat_lt
  omega

private def hexExpr {cap n : Nat} (h : n ≤ cap) : ExprFor cap (hex n) 2 3 :=
  catExpr (litExpr _ "0x") (⟨_, rfl, .hex h⟩ : ExprFor cap _ 0 1)

private def bad {α : Type} {cap : Nat} {s : String} (r : Reader) (hr : r.data.size ≤ cap)
    (b : Built cap s) : Trace cap (Except.error (malformedAt r s) : Except Error α) 1 :=
  ⟨[⟨s,b⟩], by simp, by intro e h; cases h; exact ⟨pos hr, ⟨s,b⟩, by simp, rfl⟩⟩

private def unsupported {α : Type} {cap : Nat} {s : String} (r : Reader) (hr : r.data.size ≤ cap)
    (b : Built cap s) : Trace cap (Except.error (unsupportedAt r s) : Except Error α) 1 :=
  ⟨[⟨s,b⟩], by simp, by intro e h; cases h; exact ⟨pos hr, ⟨s,b⟩, by simp, rfl⟩⟩

private def fieldBind {α β : Type} {cap k j : Nat} {r : Reader}
    {read : Except Error (α × Reader)} {f : α × Reader → Except Error β}
    (hr : r.data.size ≤ cap) (first : Trace cap read k)
    (same : ∀ {a t}, read = .ok (a,t) → t.data = r.data)
    (rest : ∀ a t, t.data.size ≤ cap → Trace cap (f (a,t)) j) :
    Trace cap (read >>= f) (j+k) :=
  bindTrace first fun (a,t) h => rest a t (same h ▸ hr)

private def byteBind {α : Type} {cap j : Nat} {r : Reader} (hr : r.data.size ≤ cap)
    {f : UInt8 × Reader → Except Error α}
    (rest : ∀ a t, t.data.size ≤ cap → Trace cap (f (a,t)) j) :
    Trace cap (r.u8 >>= f) (j+1) :=
  fieldBind hr (u8Trace r (pos hr)) (fun h => (Reader.u8_pos h).2.2.1) rest

private def wordBind {α : Type} {cap j : Nat} {r : Reader} (hr : r.data.size ≤ cap)
    {f : UInt16 × Reader → Except Error α}
    (rest : ∀ a t, t.data.size ≤ cap → Trace cap (f (a,t)) j) :
    Trace cap (r.u16be >>= f) (j+1) :=
  fieldBind hr (u16beTrace r (pos hr)) (fun h => (Reader.u16be_pos h).2.2.1) rest

private theorem arraySource {α : Type} {f : Reader → Except Error (α × Reader)}
    (same : ∀ r t a, f r = .ok (a,t) → t.data = r.data)
    {n : Nat} {a z : Array α} {r t : Reader} (ok : readArray f a n r = .ok (z,t)) :
    t.data = r.data := by
  induction n generalizing a r with
  | zero => cases ok; rfl
  | succ n ih =>
    rw [readArray] at ok
    split at ok
    · contradiction
    · rename_i x s hs
      exact (ih ok).trans (same r s x hs)

private def arrayBind {α β : Type} {cap k j : Nat} {f : Reader → Except Error (α × Reader)}
    (one : ∀ r : Reader, r.data.size ≤ cap → Trace cap (f r) k)
    (same : ∀ r t a, f r = .ok (a,t) → t.data = r.data)
    (a : Array α) (n : Nat) (r : Reader) (hr : r.data.size ≤ cap)
    {g : Array α × Reader → Except Error β}
    (rest : ∀ z t, t.data.size ≤ cap → Trace cap (g (z,t)) j) :
    Trace cap (readArray f a n r >>= g) (j+n*k) :=
  fieldBind hr (arrayTrace one same a n r hr) (fun h => arraySource same h) rest

private def indexTrace {cap : Nat} (c : Nat) (r : Reader) (hr : r.data.size ≤ cap) :
    Trace cap (readCompIndex c r) 1 := by
  unfold readCompIndex
  split
  · let first := u8Trace r (pos hr)
    cases h : r.u8 with
    | error e => exact ⟨first.messages, first.countBound, by intro _ he; cases he; exact first.origin e h⟩
    | ok v => cases v; exact doneTrace _
  · exact u16beTrace r (pos hr)

private theorem indexSource {c : Nat} {r t : Reader} {v : UInt16}
    (ok : readCompIndex c r = .ok (v,t)) : t.data = r.data := by
  unfold readCompIndex at ok
  split at ok
  · split at ok <;> first | contradiction | cases ok; exact (Reader.u8_pos (by assumption)).2.2.1
  · exact (Reader.u16be_pos ok).2.2.1

private def componentTrace {cap : Nat} (wire : 65535 ≤ cap) (c : Nat) (hc : c ≤ cap)
    (r : Reader) (hr : r.data.size ≤ cap) : Trace cap (readComponent c r) 2 := by
  unfold readComponent
  apply bindTrace (indexTrace c r hr)
  rintro ⟨v,t⟩ _
  apply bindTrace (requireTrace r (pos hr) _ _ (closeExpr
    (catExpr (catExpr (catExpr (litExpr _ "component index ") (decExpr (word wire v)))
      (litExpr _ " ≥ Csiz ")) (decExpr hc)) (by decide) (by decide)))
  intro _ _
  exact doneTrace _

private theorem componentSource {c : Nat} {r t : Reader} {v : UInt16}
    (ok : readComponent c r = .ok (v,t)) : t.data = r.data := by
  unfold readComponent at ok
  obtain ⟨⟨_,_⟩,hv,ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨_,_,ok⟩ := Tier2Equiv.bind_ok ok
  cases ok
  exact indexSource hv

private def precinctTrace {cap : Nat} (r : Reader) (hr : r.data.size ≤ cap) :
    Trace cap (readPrecinct r) 1 := by
  unfold readPrecinct
  apply byteBind hr
  intros
  exact doneTrace _

private theorem precinctSource (r t : Reader) (v : Precinct) (ok : readPrecinct r = .ok (v,t)) :
    t.data = r.data := by
  unfold readPrecinct at ok
  obtain ⟨⟨_,_⟩,hv,ok⟩ := Tier2Equiv.bind_ok ok
  cases ok
  exact (Reader.u8_pos hv).2.2.1

private def styleTrace {cap : Nat} (wire : 65535 ≤ cap) (L : Limits) (defined : Bool)
    (r : Reader) (hr : r.data.size ≤ cap) : Trace cap (readCodingStyle L defined r) 270 := by
  unfold readCodingStyle
  apply byteBind hr
  intro levels r1 h1
  apply bindTrace (requireTrace r (pos hr) _ _ (closeExpr
    (catExpr (catExpr (litExpr _ "decomposition levels ") (decExpr (byte wire levels)))
      (litExpr _ " > 32")) (by decide) (by decide)))
  intro _ _
  apply bindTrace (checkedTrace L _ _ _ (pos hr) (byte wire levels))
  intro _ _
  apply byteBind h1
  intro xcb r2 h2
  apply byteBind h2
  intro ycb r3 h3
  have hx : xcb.toNat + 2 ≤ cap := by have := xcb.toNat_lt; omega
  have hy : ycb.toNat + 2 ≤ cap := by have := ycb.toNat_lt; omega
  apply bindTrace (requireTrace r1 (pos h1) _ _ (closeExpr
    (catExpr (catExpr (catExpr (catExpr (litExpr _ "code-block size exponents ") (decExpr hx))
      (litExpr _ ", ")) (decExpr hy)) (litExpr _ " (each ≤ 10, sum ≤ 12)")) (by decide) (by decide)))
  intro _ _
  apply byteBind h3
  intro style r4 h4
  dsimp only
  split
  · exact widen (unsupported r3 h3 (oneFixed _ (by decide))) (by decide)
  apply bindTrace (requireTrace r3 (pos h3) _ _ (closeExpr
    (catExpr (catExpr (litExpr _ "reserved code-block style bit (") (hexExpr (byte wire style)))
      (litExpr _ ")")) (by decide) (by decide)))
  intro _ _
  apply byteBind h4
  intro tb r5 h5
  dsimp only
  split
  case h_3 =>
    exact widen (unsupported r4 h4 (closeExpr (catExpr (catExpr (litExpr _ "wavelet transform ")
      (decExpr (byte wire tb))) (litExpr _ " (Part 2)")) (by decide) (by decide))) (by decide)
  all_goals
    simp only [pure, Except.pure, bind, Except.bind]
    split
    · apply widen (arrayBind precinctTrace precinctSource _ _ r5 h5 (j := 1) ?_)
        (by have := levels.toNat_lt; omega)
      intro _ _ _
      apply bindTrace (requireTrace r5 (pos h5) _ _ (oneFixed _ (by decide)))
      intro _ _
      exact doneTrace _
    · exact doneTrace _

private theorem styleSource {L : Limits} {d : Bool} {r t : Reader} {v : CodingStyle}
    (ok : readCodingStyle L d r = .ok (v,t)) : t.data = r.data := by
  unfold readCodingStyle at ok
  obtain ⟨⟨_,_⟩,a,ok⟩ := Tier2Equiv.bind_ok ok
  iterate 2 obtain ⟨_,_,ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨⟨_,_⟩,b,ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨⟨_,_⟩,c,ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨_,_,ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨⟨_,_⟩,e,ok⟩ := Tier2Equiv.bind_ok ok
  dsimp only at ok
  split at ok
  · contradiction
  obtain ⟨_,_,ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨⟨_,_⟩,f,ok⟩ := Tier2Equiv.bind_ok ok
  have back := (Reader.u8_pos f).2.2.1.trans ((Reader.u8_pos e).2.2.1.trans
    ((Reader.u8_pos c).2.2.1.trans ((Reader.u8_pos b).2.2.1.trans (Reader.u8_pos a).2.2.1)))
  dsimp only at ok
  split at ok <;> try contradiction
  all_goals
    obtain ⟨_,_,ok⟩ := Tier2Equiv.bind_ok ok
    split at ok
    · obtain ⟨⟨_,_⟩,arr,ok⟩ := Tier2Equiv.bind_ok ok
      obtain ⟨_,_,ok⟩ := Tier2Equiv.bind_ok ok
      cases ok
      exact (arraySource precinctSource arr).trans back
    · cases ok
      exact back

/-- COD charges every reached fixed field, the optional precinct array and the final
trailing-byte check. Layer and decomposition limit errors retain the raw wire value. -/
def codTrace {cap : Nat} (wire : 65535 ≤ cap) (L : Limits) (r : Reader) (hr : r.data.size ≤ cap) :
    Trace cap (parseCOD L r) 280 := by
  unfold parseCOD
  apply byteBind hr
  intro scod r1 h1
  apply bindTrace (requireTrace r (pos hr) _ _ (closeExpr
    (catExpr (catExpr (litExpr _ "reserved Scod bits (") (hexExpr (byte wire scod))) (litExpr _ ")"))
    (by decide) (by decide)))
  intro _ _
  apply byteBind h1
  intro pb r2 h2
  dsimp only
  split
  case h_2 =>
    exact widen (bad r1 h1 (closeExpr (catExpr (litExpr _ "progression order ") (decExpr (byte wire pb)))
      (by decide) (by decide))) (by decide)
  apply bindTrace (i := 0) (doneTrace _)
  intro _ _
  apply wordBind h2
  intro layers r3 h3
  apply bindTrace (requireTrace r2 (pos h2) _ _ (oneFixed _ (by decide)))
  intro _ _
  apply bindTrace (checkedTrace L _ _ _ (pos h2) (word wire layers))
  intro _ _
  apply byteBind h3
  intro mb r4 h4
  dsimp only
  split
  · exact widen (unsupported r3 h3 (closeExpr
      (catExpr (catExpr (litExpr _ "multiple component transform ") (decExpr (byte wire mb)))
        (litExpr _ " (Part 2)")) (by decide) (by decide))) (by decide)
  apply fieldBind h4 (styleTrace wire L _ r4 h4) (fun h => styleSource h)
  intro _ t ht
  apply bindTrace (endTrace t ht "COD" (by decide))
  intro _ _
  exact doneTrace _

/-- COC uses the SIZ component count both to select the wire width and to price
the eagerly constructed component-index diagnostic. -/
def cocTrace {cap : Nat} (wire : 65535 ≤ cap) (L : Limits) (c : Nat) (hc : c ≤ cap)
    (r : Reader) (hr : r.data.size ≤ cap) : Trace cap (parseCOC L c r) 275 := by
  unfold parseCOC
  apply fieldBind hr (componentTrace wire c hc r hr) (fun h => componentSource h)
  intro _ r1 h1
  apply byteBind h1
  intro scoc r2 h2
  apply bindTrace (requireTrace r1 (pos h1) _ _ (closeExpr
    (catExpr (catExpr (litExpr _ "reserved Scoc bits (") (hexExpr (byte wire scoc))) (litExpr _ ")"))
    (by decide) (by decide)))
  intro _ _
  apply fieldBind h2 (styleTrace wire L _ r2 h2) (fun h => styleSource h)
  intro _ t ht
  apply bindTrace (endTrace t ht "COC" (by decide))
  intro _ _
  exact doneTrace _

private def exponentTrace {cap : Nat} (wire : 65535 ≤ cap) (r : Reader) (hr : r.data.size ≤ cap) :
    Trace cap (readExponent r) 2 := by
  unfold readExponent
  apply byteBind hr
  intro v _ _
  apply bindTrace (requireTrace r (pos hr) _ _ (closeExpr
    (catExpr (litExpr _ "reserved bits in exponent byte ") (hexExpr (byte wire v))) (by decide) (by decide)))
  intro _ _
  exact doneTrace _

private theorem exponentSource (r t : Reader) (v : UInt8) (ok : readExponent r = .ok (v,t)) :
    t.data = r.data := by
  unfold readExponent at ok
  obtain ⟨⟨_,_⟩,hv,ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨_,_,ok⟩ := Tier2Equiv.bind_ok ok
  cases ok
  exact (Reader.u8_pos hv).2.2.1

private def stepTrace {cap : Nat} (r : Reader) (hr : r.data.size ≤ cap) :
    Trace cap (readStepSize r) 1 := by
  unfold readStepSize
  apply wordBind hr
  intros
  exact doneTrace _

private theorem stepSource (r t : Reader) (v : StepSize) (ok : readStepSize r = .ok (v,t)) :
    t.data = r.data := by
  unfold readStepSize at ok
  obtain ⟨⟨_,_⟩,hv,ok⟩ := Tier2Equiv.bind_ok ok
  cases ok
  exact (Reader.u16be_pos hv).2.2.1

private theorem required {r : Reader} {p : Prop} [Decidable p] {s : String} {u : Unit}
    (h : require r p s = .ok u) : p := by
  unfold require at h
  split at h <;> first | exact of_decide_eq_true (by assumption) | contradiction

/-- QCD accounts for each exponent's eager hex check, each step-size read, and the
remaining-byte count before checking the band limit. QCC reuses this trace. -/
def qcdTrace {cap : Nat} (wire : 65535 ≤ cap) (r : Reader) (hr : r.data.size ≤ cap) :
    Trace cap (parseQCD r) 200 := by
  unfold parseQCD readQuant
  apply byteBind hr
  intro s t ht
  dsimp only
  split
  · apply bindTrace (requireTrace r (pos hr) _ _ (closeExpr
      (catExpr (decExpr (rem ht)) (litExpr _ " sub-band exponents (1…97)")) (by decide) (by decide)))
    intro _ ok
    have hn : t.remaining ≤ 97 := (required ok).2
    apply widen (arrayBind (exponentTrace wire) exponentSource _ _ t ht (j := 1) ?_) (by omega)
    intro _ u hu
    apply bindTrace (endTrace u hu "QCD/QCC" (by decide))
    intro _ _
    exact doneTrace _
  · apply fieldBind ht (stepTrace t ht) (fun h => stepSource _ _ _ h)
    intro _ u hu
    apply bindTrace (endTrace u hu "QCD/QCC" (by decide))
    intro _ _
    exact doneTrace _
  · apply bindTrace (requireTrace r (pos hr) _ _ (closeExpr
      (catExpr (decExpr (rem ht)) (litExpr _ " bytes of expounded step sizes (even, 2…194)"))
      (by decide) (by decide)))
    intro _ ok
    have hn : t.remaining / 2 ≤ 97 := (required ok).2.2
    apply widen (arrayBind stepTrace stepSource _ _ t ht (j := 1) ?_) (by omega)
    intro _ u hu
    apply bindTrace (endTrace u hu "QCD/QCC" (by decide))
    intro _ _
    exact doneTrace _
  · exact widen (bad r hr (closeExpr (catExpr (litExpr _ "quantisation style ")
      (decExpr (byte wire (s &&& 0x1F)))) (by decide) (by decide))) (by decide)

/-- QCC reads and checks its component before running the quantisation-body trace. -/
def qccTrace {cap : Nat} (wire : 65535 ≤ cap) (c : Nat) (hc : c ≤ cap)
    (r : Reader) (hr : r.data.size ≤ cap) : Trace cap (parseQCC c r) 202 := by
  unfold parseQCC
  apply fieldBind hr (componentTrace wire c hc r hr) (fun h => componentSource h)
  intro _ t ht
  apply bindTrace (qcdTrace wire t ht)
  intro _ _
  exact doneTrace _

/-- RGN charges its component, unsupported ROI style and final payload-length check. -/
def rgnTrace {cap : Nat} (wire : 65535 ≤ cap) (c : Nat) (hc : c ≤ cap)
    (r : Reader) (hr : r.data.size ≤ cap) : Trace cap (parseRGN c r) 5 := by
  unfold parseRGN
  apply fieldBind hr (componentTrace wire c hc r hr) (fun h => componentSource h)
  intro _ r1 h1
  apply byteBind h1
  intro style r2 h2
  dsimp only
  split
  · exact widen (unsupported r1 h1 (closeExpr
      (catExpr (catExpr (litExpr _ "ROI style ") (decExpr (byte wire style))) (litExpr _ " (Part 2)"))
      (by decide) (by decide))) (by decide)
  apply byteBind h2
  intro _ r3 h3
  apply bindTrace (endTrace r3 h3 "RGN" (by decide))
  intro _ _
  exact doneTrace _

private theorem compEndBound {cap : Nat} (wire : 65535 ≤ cap) (c : Nat) (e : PocEntry) :
    e.compEnd c ≤ cap := by
  unfold PocEntry.compEnd
  split
  · split <;> omega
  · exact word wire _

private def entryTrace {cap : Nat} (wire : 65535 ≤ cap) (c : Nat) (r : Reader) (hr : r.data.size ≤ cap) :
    Trace cap (readPocEntry c r) 10 := by
  unfold readPocEntry
  apply byteBind hr
  intro rs r1 h1
  apply fieldBind h1 (indexTrace c r1 h1) (fun h => indexSource h)
  intro cs r2 h2
  apply wordBind h2
  intro le r3 h3
  apply byteBind h3
  intro re r4 h4
  apply fieldBind h4 (indexTrace c r4 h4) (fun h => indexSource h)
  intro ce r5 h5
  apply byteBind h5
  intro pb _ _
  dsimp only
  split
  case h_2 =>
    exact widen (bad r5 h5 (closeExpr (catExpr (litExpr _ "POC progression order ") (decExpr (byte wire pb)))
      (by decide) (by decide))) (by decide)
  apply bindTrace (i := 0) (doneTrace _)
  intro order _
  apply bindTrace (requireTrace r (pos hr) _ _ (closeExpr
    (catExpr (catExpr (catExpr (litExpr _ "POC resolutions ") (decExpr (byte wire rs)))
      (litExpr _ "…")) (decExpr (byte wire re))) (by decide) (by decide)))
  intro _ _
  apply bindTrace (requireTrace r (pos hr) _ _ (oneFixed _ (by decide)))
  intro _ _
  apply bindTrace (requireTrace r (pos hr) _ _ (closeExpr
    (catExpr (catExpr (catExpr (litExpr _ "POC components ") (decExpr (word wire cs)))
      (litExpr _ "…")) (decExpr (compEndBound wire c ⟨rs,cs,le,re,ce,order⟩))) (by decide) (by decide)))
  intro _ _
  exact doneTrace _

private theorem entrySource (c : Nat) (r t : Reader) (v : PocEntry) (ok : readPocEntry c r = .ok (v,t)) :
    t.data = r.data := by
  unfold readPocEntry at ok
  obtain ⟨⟨_,_⟩,a,ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨⟨_,_⟩,b,ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨⟨_,_⟩,d,ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨⟨_,_⟩,e,ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨⟨_,_⟩,f,ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨⟨_,_⟩,g,ok⟩ := Tier2Equiv.bind_ok ok
  dsimp only at ok
  split at ok <;> try contradiction
  iterate 4 obtain ⟨_,_,ok⟩ := Tier2Equiv.bind_ok ok
  cases ok
  exact (Reader.u8_pos g).2.2.1.trans ((indexSource f).trans ((Reader.u8_pos e).2.2.1.trans
    ((Reader.u16be_pos d).2.2.1.trans ((indexSource b).trans (Reader.u8_pos a).2.2.1))))

/-- POC prices the body size and the 7- or 9-byte entry width before division and
admission. Only an admitted entry count starts the repeated field reader. -/
def pocTrace {cap : Nat} (wire : 65535 ≤ cap) (L : Limits) (c : Nat) (r : Reader)
    (hr : r.data.size ≤ cap) : Trace cap (parsePOC L c r) (L.maxPocEntries*10+2) := by
  unfold parsePOC
  have sz : pocEntrySize c ≤ cap := by unfold pocEntrySize; split <;> omega
  have hn := Nat.le_trans (Nat.div_le_self r.remaining (pocEntrySize c)) (rem hr)
  apply bindTrace (requireTrace r (pos hr) _ _ (closeExpr
    (catExpr (catExpr (catExpr (catExpr (litExpr _ "POC body of ") (decExpr (rem hr)))
      (litExpr _ " bytes (entries of ")) (decExpr sz)) (litExpr _ ")")) (by decide) (by decide)))
  intro _ _
  apply bindTrace (checkedTrace L _ _ _ (pos hr) hn)
  intro _ ok
  have count : r.remaining / pocEntrySize c ≤ L.maxPocEntries := (Limits.check_eq_ok_iff ..).1 ok
  apply widen (arrayBind (entryTrace wire c) (entrySource c) _ _ r hr (j := 1) ?_) (by omega)
  intro _ t ht
  apply bindTrace (endTrace t ht "POC" (by decide))
  intro _ _
  exact doneTrace _

/-- COM's body reader can construct a truncation diagnostic for its registration field. -/
def comTrace {cap : Nat} (r : Reader) (hr : r.data.size ≤ cap) : Trace cap (parseCOM r) 1 := by
  unfold parseCOM
  apply wordBind hr
  intros
  exact doneTrace _

private def pairTrace {cap : Nat} (r : Reader) (hr : r.data.size ≤ cap) : Trace cap (readCrgPair r) 2 := by
  unfold readCrgPair
  apply wordBind hr
  intro _ t ht
  apply wordBind ht
  intros
  exact doneTrace _

private theorem pairSource (r t : Reader) (v : UInt16 × UInt16) (ok : readCrgPair r = .ok (v,t)) :
    t.data = r.data := by
  unfold readCrgPair at ok
  obtain ⟨⟨_,_⟩,a,ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨⟨_,_⟩,b,ok⟩ := Tier2Equiv.bind_ok ok
  cases ok
  exact (Reader.u16be_pos b).2.2.1.trans (Reader.u16be_pos a).2.2.1

/-- CRG charges the eager length check and both reads per SIZ component. -/
def crgTrace {cap : Nat} (c : Nat) (r : Reader) (hr : r.data.size ≤ cap) :
    Trace cap (parseCRG c r) (c*2+2) := by
  unfold parseCRG
  apply bindTrace (requireTrace r (pos hr) _ _ (closeExpr
    (catExpr (catExpr (litExpr _ "CRG body of ") (decExpr (rem hr))) (litExpr _ " bytes, expected 4·Csiz"))
    (by decide) (by decide)))
  intro _ _
  apply widen (arrayBind pairTrace pairSource _ c r hr (j := 1) ?_) (by omega)
  intro _ t ht
  apply bindTrace (endTrace t ht "CRG" (by decide))
  intro _ _
  exact doneTrace _

private theorem arrayCount {α : Type} {f : Reader → Except Error (α × Reader)} {n : Nat}
    {a z : Array α} {r t : Reader} (ok : readArray f a n r = .ok (z,t)) : z.size = a.size+n := by
  induction n generalizing a r with
  | zero => cases ok; rfl
  | succ n ih =>
    rw [readArray] at ok
    split at ok <;> try contradiction
    rw [ih ok, Array.size_push]
    omega

private theorem pocCount {L : Limits} {c : Nat} {r : Reader} {p : POC} (ok : parsePOC L c r = .ok p) :
    p.entries.size ≤ L.maxPocEntries := by
  unfold parsePOC at ok
  obtain ⟨_,_,ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨_,h,ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨⟨_,_⟩,a,ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨_,_,ok⟩ := Tier2Equiv.bind_ok ok
  cases ok
  have sz := arrayCount a
  simp at sz
  exact sz ▸ (Limits.check_eq_ok_iff ..).1 h

private theorem sizWire {L : Limits} {r : Reader} {s : SIZ} (ok : parseSIZ L r = .ok s) :
    ∃ (field next : Reader) (v : UInt16), field.u16be = .ok (v,next) ∧ field.data = r.data ∧
      field.pos = r.pos+34 ∧ s.csiz = v.toNat ∧ 1 ≤ s.csiz ∧ s.csiz ≤ 16384 ∧ s.csiz ≤ L.maxComponents := by
  unfold parseSIZ at ok
  obtain ⟨⟨_,r1⟩,h1,ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨p1,_,d1,_⟩ := Reader.u16be_pos h1
  have back : r1.data = r.data ∧ r1.pos = r.pos+2 := ⟨d1,p1⟩
  iterate 8
    obtain ⟨⟨_,t⟩,h,ok⟩ := Tier2Equiv.bind_ok ok
    obtain ⟨hp,_,hd,_⟩ := Reader.u32be_pos h
    have back := And.intro (hd.trans back.1) (hp.trans (congrArg (·+4) back.2))
  obtain ⟨⟨v,next⟩,read,ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨_,h,ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨_,l,ok⟩ := Tier2Equiv.bind_ok ok
  iterate 5 obtain ⟨_,_,ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨⟨cs,_⟩,a,ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨_,_,ok⟩ := Tier2Equiv.bind_ok ok
  cases ok
  have sz := arrayCount a
  simp at sz
  refine ⟨_,next,v,read,back.1,?_,sz,?_⟩
  · have := back.2; omega
  · change 1 ≤ cs.size ∧ cs.size ≤ 16384 ∧ cs.size ≤ L.maxComponents
    rw [sz]
    exact ⟨(required h).1,(required h).2,(Limits.check_eq_ok_iff ..).1 l⟩

/-- One main-header iteration can run one marker body, including both typed POC
checks and a duplicate-marker check. CRG visits at most the admitted component count. -/
def segmentBudget (L : Limits) := L.maxPocEntries*10 + L.maxComponents*2 + 300

private def collected {α β : Type} {cap k : Nat} {x : Except Error α}
    (t : Trace cap x k) (f : α → β) : Trace cap (x >>= fun v => pure (f v)) k :=
  widen (bindTrace (j := 0) t (fun _ _ => doneTrace _)) (by omega)

private def addTrace {cap : Nat} (wire : 65535 ≤ cap) (L : Limits) (total : 2*L.maxPocEntries ≤ cap)
    (c : Nat) (hc : c ≤ cap) (cl : c ≤ L.maxComponents) (a : Acc) (ha : a.pocEntries ≤ L.maxPocEntries)
    (m : UInt16) (r : Reader) (hr : r.data.size ≤ cap) :
    Trace cap (addSegment L c a m r) (segmentBudget L) := by
  unfold addSegment segmentBudget
  by_cases hm : m == Code.COD
  · rw [ite_eq_left hm]
    apply widen (bindTrace (j := 280) (requireTrace r (pos hr) _ _ (oneFixed _ (by decide))) ?_) (by omega)
    intro _ _
    exact collected (codTrace wire L r hr) _
  rw [ite_eq_right hm]
  split
  · exact widen (collected (cocTrace wire L c hc r hr) _) (by omega)
  split
  · apply widen (bindTrace (j := 200) (requireTrace r (pos hr) _ _ (oneFixed _ (by decide))) ?_) (by omega)
    intro _ _
    exact collected (qcdTrace wire r hr) _
  split
  · exact widen (collected (qccTrace wire c hc r hr) _) (by omega)
  split
  · exact widen (collected (rgnTrace wire c hc r hr) _) (by omega)
  split
  · apply widen (bindTrace (j := 0) (pocTrace wire L c r hr) ?_) (by omega)
    intro p hp
    have width := pocCount hp
    apply bindTrace (checkedTrace L _ _ (a.pocEntries + p.entries.size) (pos hr) (by omega))
    intro _ _
    exact doneTrace _
  split
  · exact widen (collected (comTrace r hr) _) (by omega)
  split
  · apply widen (bindTrace (j := c*2+2) (requireTrace r (pos hr) _ _ (oneFixed _ (by decide))) ?_) (by omega)
    intro _ _
    exact collected (crgTrace c r hr) _
  split
  · exact widen (collected (requireTrace r (pos hr) _ _ (oneFixed _ (by decide))) _) (by omega)
  split <;> exact doneTrace _

private theorem addCount {L : Limits} {c : Nat} {a z : Acc} {m : UInt16} {r : Reader}
    (ha : a.pocEntries ≤ L.maxPocEntries) (ok : addSegment L c a m r = .ok z) :
    z.pocEntries ≤ L.maxPocEntries := by
  unfold addSegment at ok
  by_cases hm : m == Code.COD
  · rw [ite_eq_left hm] at ok
    iterate 2 obtain ⟨_,_,ok⟩ := Tier2Equiv.bind_ok ok
    cases ok
    exact ha
  rw [ite_eq_right hm] at ok
  repeat' first | (split at ok <;> try contradiction) | (obtain ⟨_,_,ok⟩ := Tier2Equiv.bind_ok ok)
  all_goals cases ok
  all_goals first | exact ha | exact (Limits.check_eq_ok_iff ..).1 (by assumption)

private def propagated {α β : Type} {cap k : Nat} {x : Except Error α} {e : Error}
    (t : Trace cap x k) (h : x = .error e) : Trace cap (Except.error e : Except Error β) k :=
  ⟨t.messages, t.countBound, by intro _ he; cases he; exact t.origin _ h⟩

private def loopTrace {cap : Nat} (wire : 65535 ≤ cap) (L : Limits) (total : 2*L.maxPocEntries ≤ cap)
    (c : Nat) (hc : c ≤ cap) (cl : c ≤ L.maxComponents) (fuel : Nat) (a : Acc)
    (ha : a.pocEntries ≤ L.maxPocEntries) (r : Reader) (hr : r.data.size ≤ cap) :
    Trace cap (segmentLoop L c fuel a r) (fuel*(segmentBudget L+4)+1) := by
  induction fuel generalizing a r with
  | zero =>
    exact ⟨[⟨_,oneFixed "main header: no SOT" (by decide)⟩], by simp,
      by intro e h; cases h; exact ⟨pos hr, ⟨_,oneFixed _ (by decide)⟩, by simp, rfl⟩⟩
  | succ f ih =>
    rw [segmentLoop, Nat.succ_mul]
    let read := u16beTrace r (pos hr)
    split
    · rename_i e h
      exact widen (propagated read h) (by omega)
    · rename_i m t h
      have ht : t.data.size ≤ cap := (Reader.u16be_pos h).2.2.1 ▸ hr
      split
      · exact doneTrace _
      split
      · exact widen (bad r hr (closeExpr (catExpr (litExpr _ "expected a marker, found ")
          (hexExpr (word wire m))) (by decide) (by decide))) (by omega)
      split
      · exact widen (ih {a with markers := a.markers.push ⟨m,r.pos,2⟩} ha t ht) (by omega)
      split
      · exact widen (bad r hr (closeExpr
          (catExpr (catExpr (litExpr _ "marker ") (hexExpr (word wire m)))
            (litExpr _ " not allowed in the main header")) (by decide) (by decide))) (by omega)
      let frame := segmentTrace t ht wire
      split
      · rename_i e hs
        exact widen (propagated frame hs) (by omega)
      · rename_i body len next hs
        have ext := HeaderWork.readSegment_extent hs
        have hb : body.data.size ≤ cap := ext.1 ▸ ht
        have hn : next.data.size ≤ cap := ext.2.1 ▸ ht
        let indexed : Acc := {a with markers := a.markers.push ⟨m,r.pos,len+2⟩}
        dsimp only
        split
        · rename_i e he
          exact widen (includeTrace frame (propagated (addTrace wire L total c hc cl indexed ha m body hb) he))
            (by omega)
        · rename_i z hz
          let payload := addTrace wire L total c hc cl indexed ha m body hb
          exact widen (includeTrace frame (includeTrace payload (ih z (addCount (a := indexed) ha hz) next hn))) (by omega)

/-- Hex operands are the original 16-bit fields. Every word in the marker range has
four digits; an invalid short word uses just the digits that `Marker.hex` renders. -/
theorem marker_digits (m : UInt16) :
    (Nat.toDigits 16 m.toNat).length ≤ 4 ∧
    (0xFF01 ≤ m → (Nat.toDigits 16 m.toNat).length = 4) := by
  have upper := (Nat.length_toDigits_le_iff (b := 16) (n := m.toNat) (k := 4) (by decide) (by decide)).2
    m.toNat_lt
  refine ⟨upper, fun h => ?_⟩
  have h' : 65281 ≤ m.toNat := UInt16.le_iff_toNat_le.mp h
  have iff := Nat.length_toDigits_le_iff (b := 16) (n := m.toNat) (k := 3) (by decide) (by decide)
  change ((Nat.toDigits 16 m.toNat).length ≤ 3 ↔ m.toNat < 4096) at iff
  omega

/-- The event count includes SOC/SIZ, one visit per unit of initial segment-loop fuel,
and the final required COD and QCD. The fuel is bounded by the backing byte count. -/
def mainBudget (L : Limits) (bytes : Nat) :=
  bytes*(segmentBudget L+4) + 2 + (L.maxComponents*6+17) + 7

/-- Trace the production main-header reader on arbitrary input, including a reader
starting at a nonzero offset. Segment framing and payload traces share the same
buffer. A rejected cumulative POC limit can contain two individually admitted counts. -/
def mainTrace {cap bytes : Nat} (wire : 65535 ≤ cap) (L : Limits) (total : 2*L.maxPocEntries ≤ cap)
    (r : Reader) (source : r.data.size ≤ bytes) (bound : bytes ≤ cap) :
    Trace cap (parseMainHeader L r) (mainBudget L bytes) := by
  have hr := Nat.le_trans source bound
  unfold parseMainHeader mainBudget
  apply bindTrace (u16beTrace r (pos hr))
  rintro ⟨_,r1⟩ h1
  have b1 := (Reader.u16be_pos h1).2.2.1
  apply bindTrace (requireTrace r (pos hr) _ _ (oneFixed _ (by decide)))
  intro _ _
  apply bindTrace (u16beTrace r1 (pos (b1 ▸ hr)))
  rintro ⟨_,r2⟩ h2
  have b2 := (Reader.u16be_pos h2).2.2.1.trans b1
  apply bindTrace (requireTrace r1 (pos (b1 ▸ hr)) _ _ (oneFixed _ (by decide)))
  intro _ _
  apply bindTrace (segmentTrace r2 (b2 ▸ hr) wire)
  rintro ⟨body,len,r3⟩ hs
  have ext := HeaderWork.readSegment_extent hs
  have b3 := ext.2.1.trans b2
  apply bindTrace (sizTrace L body (ext.1.trans b2 ▸ hr) wire)
  intro siz parsed
  have counts : siz.csiz ≤ 16384 ∧ siz.csiz ≤ L.maxComponents := by
    obtain ⟨_,_,_,_,_,_,_,_,h⟩ := sizWire parsed
    exact h
  let initial : Acc := { markers := #[⟨Code.SOC,r.pos,2⟩, ⟨Code.SIZ,r1.pos,len+2⟩] }
  let loop := loopTrace wire L total siz.csiz (by have := counts.1; omega) counts.2 r3.remaining initial
    (Nat.zero_le _) r3 (b3 ▸ hr)
  have fuel := Nat.mul_le_mul_right (segmentBudget L+4) (rem (b3 ▸ source))
  apply widen (bindTrace (j := 1) loop ?_) (by omega)
  rintro ⟨a,t⟩ hl
  have ht : t.data.size ≤ cap := (HeaderWork.segmentLoop_storage hl).2.1.trans b3 ▸ hr
  dsimp only
  split
  · split
    · exact doneTrace _
    · exact bad t ht (oneFixed _ (by decide))
  · exact bad t ht (oneFixed _ (by decide))

/-- On success the tail still reads the caller's buffer. The component count used by
all callbacks is the unsigned word read exactly forty bytes after the initial SOC. -/
theorem main_source {L : Limits} {r t : Reader} {mh : MainHeader} (ok : parseMainHeader L r = .ok (mh,t)) :
    t.data = r.data ∧ t.stop = r.stop ∧
    ∃ (field next : Reader) (v : UInt16), field.u16be = .ok (v,next) ∧ field.data = r.data ∧
      field.pos = r.pos+40 ∧ mh.siz.csiz = v.toNat ∧
      1 ≤ mh.siz.csiz ∧ mh.siz.csiz ≤ 16384 ∧ mh.siz.csiz ≤ L.maxComponents := by
  unfold parseMainHeader at ok
  obtain ⟨⟨_,_⟩,h1,ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨_,_,ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨⟨_,_⟩,h2,ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨_,_,ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨⟨_,_,_⟩,seg,ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨_,hs,ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨⟨a,_⟩,hl,ok⟩ := Tier2Equiv.bind_ok ok
  cases hc : a.cod <;> simp only [hc] at ok
  · cases ok
  cases hq : a.qcd <;> simp only [hq] at ok
  · cases ok
  cases ok
  obtain ⟨field,next,v,read,fd,fp,counts⟩ := sizWire hs
  have a1 := Reader.u16be_pos h1
  have a2 := Reader.u16be_pos h2
  have same := a2.2.2.1.trans a1.2.2.1
  have extent := HeaderWork.readSegment_extent seg
  have tail := HeaderWork.segmentLoop_storage hl
  exact ⟨tail.2.1.trans (extent.2.1.trans same), by omega, field,next,v,read,
    fd.trans (extent.1.trans same), by omega, counts⟩

private def skipTrace {cap : Nat} (r : Reader) (hr : r.data.size ≤ cap) (n : Nat) (hn : n ≤ cap) :
    Trace cap (r.skip n) 1 := by
  unfold Reader.skip
  split
  · exact doneTrace _
  · let b := closeExpr (catExpr (litExpr _ "skip ") (decExpr hn)) (by decide) (by decide)
    exact ⟨[⟨_,b⟩], by simp, by intro e h; cases h; exact ⟨pos hr, ⟨_,b⟩, by simp, rfl⟩⟩

/-- The range reader may format a rejected offset or length. Separate bounds on the
arguments also allow callers with ranges that extend beyond the backing array. -/
def rangeTrace {cap : Nat} (data : ByteArray) (hd : data.size ≤ cap) (rg : TilePart.ByteRange)
    (ho : rg.offset ≤ cap) (hn : rg.length ≤ cap) : Trace cap (TilePart.rangeReader data rg) 2 := by
  unfold TilePart.rangeReader
  apply bindTrace (skipTrace _ hd rg.offset ho)
  intro r hs
  have hr : r.data.size ≤ cap := (Reader.skip_pos hs).2.2.1 ▸ hd
  apply bindTrace (takeTrace r (pos hr) rg.length hn)
  rintro ⟨_,_⟩ _
  exact doneTrace _

/-- A returned range reader retains the input buffer and both absolute endpoints. -/
theorem range_source {data : ByteArray} {rg : TilePart.ByteRange} {r : Reader}
    (ok : TilePart.rangeReader data rg = .ok r) :
    r.data = data ∧ r.pos = rg.offset ∧ r.stop = rg.offset + rg.length ∧ r.stage = .marker := by
  unfold TilePart.rangeReader at ok
  obtain ⟨t,hs,ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨⟨_,_⟩,ht,ok⟩ := Tier2Equiv.bind_ok ok
  cases ok
  have a := Reader.skip_pos hs
  have b := Reader.take_spec ht
  have stage := a.2.2.2
  unfold Reader.take at ht
  split at ht <;> try contradiction
  cases ht
  refine ⟨b.2.2.1.trans a.2.2.1, ?_, ?_, stage⟩ <;> simp only [Reader.ofByteArray, Nat.zero_add] at a <;> omega

/-- Main-header prefix after the actual container result has supplied its range. -/
def inRange (L : Limits) (data : ByteArray) (c : Box.Container) : Except Error (MainHeader × Reader) := do
  let r ← TilePart.rangeReader data ⟨c.codestream.start,c.codestream.len⟩
  parseMainHeader L r

/-- Scalar capacity includes the largest rejected aggregate POC value, all 16-bit
fields and absolute input offsets. The caller's limit ceilings are borrowed fields. -/
def scalarCap (L : Limits) (bytes : Nat) := max 65535 (max bytes (2*L.maxPocEntries))

/-- Range selection and the main-header continuation for a container admitted by
the production parser on this input. -/
def inRangeTrace {L : Limits} {data : ByteArray} {c : Box.Container} (hc : Box.parseFile L data = .ok c) :
    Trace (scalarCap L data.size) (inRange L data c) (mainBudget L data.size+2) := by
  have extent := Box.parseFile_range hc
  have hd : data.size ≤ scalarCap L data.size := by unfold scalarCap; omega
  unfold inRange
  apply bindTrace (rangeTrace data hd _ (by dsimp; omega) (by dsimp; omega))
  intro r hr
  apply mainTrace (by unfold scalarCap; omega) L (by unfold scalarCap; omega) r _ hd
  exact (range_source hr).1 ▸ Nat.le_refl _

private theorem rangeReady (data : ByteArray) (rg : TilePart.ByteRange) (fits : rg.offset+rg.length ≤ data.size) :
    ∃ r, TilePart.rangeReader data rg = .ok r := by
  have off : rg.offset ≤ data.size := by omega
  simp [TilePart.rangeReader,Reader.ofByteArray,Reader.skip,Reader.take,off,fits,bind,Except.bind,pure,Except.pure]

/-- A public container has already validated its codestream range. Every refusal by
the header prefix carries the marker stage and an absolute position inside that range. -/
theorem inRange_location {L : Limits} {data : ByteArray} {c : Box.Container} (hc : Box.parseFile L data = .ok c)
    {e : Error} (bad : inRange L data c = .error e) :
    ∃ off, e.loc = .atOffset .marker off ∧ c.codestream.start ≤ off ∧
      off ≤ c.codestream.start+c.codestream.len ∧ off ≤ data.size := by
  have extent := Box.parseFile_range hc
  obtain ⟨r,hr⟩ := rangeReady data ⟨c.codestream.start,c.codestream.len⟩ extent
  have ⟨_,p,s,stage⟩ := range_source hr
  change r.pos = c.codestream.start at p
  change r.stop = c.codestream.start + c.codestream.len at s
  simp only [inRange,hr,bind,Except.bind] at bad
  have loc := DiagnosticMarkerOrigin.main_location L r
  rw [bad] at loc
  obtain ⟨off,he,hlo,hhi⟩ := loc
  exact ⟨off,stage ▸ he,p ▸ hlo,s ▸ hhi,Nat.le_trans (s ▸ hhi) extent⟩

private theorem rangeFailure {L : Limits} {data : ByteArray} {opts : DecodeOptions} {c : Box.Container}
    (red : L.check Decode.loc .decompLevels opts.reduce = .ok ()) (box : Box.parseFile L data = .ok c)
    {e : Error} (bad : inRange L data c = .error e) :
    decodeCodestream L data opts.reduce = .error e ∧ JPEG2000.decode L data opts = .error e := by
  suffices raw : decodeCodestream L data opts.reduce = .error e from
    ⟨raw, by simp only [JPEG2000.decode,raw,bind,Except.bind]⟩
  unfold inRange at bad
  simp only [decodeCodestream, red, Header.parse, box, Header.parseCodestreamIn, bind, Except.bind]
  cases hr : TilePart.rangeReader data ⟨c.codestream.start,c.codestream.len⟩ with
  | error => simpa [hr,bind,Except.bind] using bad
  | ok r =>
    simp only [hr,bind,Except.bind] at bad ⊢
    rw [bad]

/-- Work and cumulative temporary storage for the reached range/main-header prefix,
including all earlier successful requirements. On refusal both public APIs propagate
the actual error; its offset, retained payload and internally computed value are bounded. -/
theorem public_main {L : Limits} {data : ByteArray} {opts : DecodeOptions} {c : Box.Container}
    (red : L.check Decode.loc .decompLevels opts.reduce = .ok ()) (box : Box.parseFile L data = .ok c) :
    let cap := scalarCap L data.size
    let t := inRangeTrace box
    let cost := (mainBudget L data.size+2)*Text.workBound cap 128 24
    (t.messages.map (fun m => m.2.tree.work)).sum ≤ cost ∧
    (t.messages.map (fun m => m.2.tree.storage)).sum ≤ cost ∧
    ∀ e, inRange L data c = .error e →
      decodeCodestream L data opts.reduce = .error e ∧ JPEG2000.decode L data opts = .error e ∧
      e.offset?.getD 0 ≤ data.size ∧ storedPayload false e ≤ 6+Text.byteBound cap 128 24+2*bits cap ∧
      (∀ loc k v b, e = .limitExceeded loc k v b → v ≤ cap) := by
  let t := inRangeTrace box
  refine ⟨(trace_cost t).1, trace_storage t, ?_⟩
  intro e bad
  have ⟨raw,image⟩ := rangeFailure red box bad
  obtain ⟨off,he,_,_,within⟩ := inRange_location box bad
  refine ⟨raw,image,by simpa only [Error.offset?,he,Location.atOffset,Option.getD_some] using within,
    trace_retained t bad,?_⟩
  rintro loc k v b rfl
  exact (t.origin _ bad).2

/-- Range/main-header events on arbitrary public input. The reduction and container
checks select whether this stage is reached; their diagnostics belong to their stages. -/
def publicEvents (L : Limits) (data : ByteArray) (opts : DecodeOptions) :
    List (Σ s, Built (scalarCap L data.size) s) :=
  match L.check Decode.loc .decompLevels opts.reduce with
  | .error _ => []
  | .ok _ =>
    match h : Box.parseFile L data with
    | .error _ => []
    | .ok _ => (inRangeTrace h).messages

/-- Uniform work and cumulative allocation for this stage on every public input,
including successful headers followed by failures in later decode stages. -/
theorem public_cost (L : Limits) (data : ByteArray) (opts : DecodeOptions) :
    let events := publicEvents L data opts
    let cost := (mainBudget L data.size+2)*Text.workBound (scalarCap L data.size) 128 24
    (events.map (fun m => m.2.tree.work)).sum ≤ cost ∧ (events.map (fun m => m.2.tree.storage)).sum ≤ cost := by
  unfold publicEvents
  split
  · exact ⟨Nat.zero_le _, Nat.zero_le _⟩
  · split
    · exact ⟨Nat.zero_le _, Nat.zero_le _⟩
    · rename_i box
      exact ⟨(trace_cost (inRangeTrace box)).1, trace_storage (inRangeTrace box)⟩

end JPEG2000.Spec.Resources.DiagnosticMarker
