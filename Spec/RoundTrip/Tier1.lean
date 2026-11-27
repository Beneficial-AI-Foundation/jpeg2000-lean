import Encode.Tier1
import Spec.MQRoundTrip
import Spec.Tier1Equiv.Basic

/-!
# C10, layer 1: the Tier-1 round trip `decode ∘ encode = id` (plain mode)

Plan.md §4 (C10; C1 and C3's spec decoder), §5.3 (reference encoder). Task 7.3, layer 1.
T.800 Annex D (D.1 scan, D.2 passes, D.3.1–D.3.4 the three coding passes, D.4 one MQ
codeword per code-block in plain mode) and Annex C (the MQ coder, through C1).

**`decodeValues_encodeCodeBlock`**: if the reference Tier-1 encoder
`Encode.Tier1.encodeCodeBlock w h orient Mb src` succeeds with output `o`, then the spec
Tier-1 decoder, given the block as Tier-2 would hand it over (`CodeBlock.ofData` with the
encoder's zero bit-planes, pass count and codeword), returns exactly `src`.

## Proof structure

* **MQ / Tier-1 simulation** (`decodePasses_encode`). The encoder (`Encode/Tier1.lean`) is
  the decoder with "decode a decision" replaced by "emit the decision". `Good D cxs R` says
  that the MQ decoder in state `D` decodes the decisions of `R` when asked for their contexts
  (`decodeMany`); it propagates one decision at a time (`good_cons`) and holds initially for
  the whole trace by C1 (`Spec.MQRoundTrip.roundTrip`), so no private MQ lemma is needed.
  `Rel T d e` (equal coefficient arrays; the encoder's emitted decisions followed by what the
  decoder still has to decode make up the whole trace `T`) is preserved by every pair of
  steps (`Sim`), given that the encoder's output after the step is a prefix of `T` (every
  step only appends, `Mono`). Folds, composition and the run-length branch of the cleanup
  pass (`r_bits`: the two UNIFORM decisions give back the row `r < 4`) are handled
  generically. The per-pass split of the encoder (`encodePassesSplit`) is covered by
  `SplitInv`.
* **Encoder correctness** (`enc_final`). Per position, the encoder's coefficient model goes
  through `Done (p+1)` → `S1 p` (significance propagation) → `M p` (refinement) → `AtP p`
  (cleanup) → `Done p` (visited marks cleared), where `AtP k` = "magnitude = the source's
  bit-planes `≥ k`, significance = (that ≠ 0), sign = the source's sign when significant".
  A step only touches its own position (`cat_set`), and the scan order visits every position
  of the block exactly once (`scanOrder_nodup`, `mem_scanOrder_of`), so a generic fold
  lemma with footprints (`fold_fp`; footprint = one position, or one stripe column for the
  cleanup pass) lifts the per-position facts to passes. The block starts as `Done K` with
  `K = numBits (maxMag src)` (every magnitude is `< 2^K`), and `3K − 2` passes reach
  `Done 0`, i.e. every coefficient value equals the source (`value_of_atp`, `values_eq`).
-/

namespace JPEG2000.Spec.RoundTrip

open JPEG2000
open JPEG2000.Spec.Tier1

/-- The MQ decoder in state `D`, `cxs` decodes the decisions of `R` when asked for its
contexts. -/
private def Good (D : Spec.MQ.State) (cxs : Spec.MQ.Contexts) (R : List (Nat × Bool)) : Prop :=
  (Spec.MQ.decodeMany D cxs (R.map (·.1))).1 = R.map (·.2)

private theorem good_cons {D : Spec.MQ.State} {cxs : Spec.MQ.Contexts} {cx : Nat} {b : Bool}
    {R : List (Nat × Bool)} (h : Good D cxs ((cx, b) :: R)) :
    (Spec.MQ.decode D cxs cx).1 = b ∧
      Good (Spec.MQ.decode D cxs cx).2.1 (Spec.MQ.decode D cxs cx).2.2 R := by
  unfold Good at *
  simp only [List.map_cons, Spec.MQ.decodeMany] at h
  generalize Spec.MQ.decode D cxs cx = r at h ⊢
  obtain ⟨d, s, c⟩ := r
  generalize Spec.MQ.decodeMany s c (List.map (·.1) R) = q at h ⊢
  obtain ⟨ds, s', c'⟩ := q
  simp only [List.cons.injEq] at h
  exact h

/-- Simulation relation. -/
private structure Rel (T : List (Nat × Bool)) (d : DecState) (e : Encode.Tier1.EncState) : Prop where
  coeffs : d.coeffs = e.coeffs
  good : ∃ R, e.out.toList ++ R = T ∧ Good d.mq d.cxs R

private theorem rel_emit {T : List (Nat × Bool)} {d : DecState} {e : Encode.Tier1.EncState}
    {cx : Nat} {b : Bool} (h : Rel T d e) (hp : (e.emit cx b).out.toList <+: T) :
    (d.decodeBit cx).1 = b ∧ Rel T (d.decodeBit cx).2 (e.emit cx b) := by
  obtain ⟨hc, R, hR, hg⟩ := h
  obtain ⟨t, ht⟩ := hp
  simp only [Encode.Tier1.EncState.emit, Array.toList_push, List.append_assoc,
    List.singleton_append] at ht
  rw [← hR] at ht
  have hR' : R = (cx, b) :: t := (List.append_cancel_left ht).symm
  subst hR'
  have hg' := good_cons hg
  unfold DecState.decodeBit
  generalize Spec.MQ.decode d.mq d.cxs cx = r at hg' ⊢
  obtain ⟨b', mq, cxs⟩ := r
  refine ⟨hg'.1, ⟨hc, t, ?_, hg'.2⟩⟩
  simpa [Encode.Tier1.EncState.emit] using hR


/-- `f` only appends to the trace. -/
private def Mono (f : Encode.Tier1.EncState → Encode.Tier1.EncState) : Prop :=
  ∀ e, e.out.toList <+: (f e).out.toList

/-- `fd` simulates `f`. -/
private def Sim (f : Encode.Tier1.EncState → Encode.Tier1.EncState) (fd : DecState → DecState) : Prop :=
  ∀ T d e, Rel T d e → (f e).out.toList <+: T → Rel T (fd d) (f e)

private theorem mono_id : Mono id := fun _ => List.prefix_refl _

private theorem mono_comp {f g : Encode.Tier1.EncState → Encode.Tier1.EncState} (hf : Mono f)
    (hg : Mono g) : Mono (fun e => g (f e)) := fun e => (hf e).trans (hg (f e))

private theorem sim_comp {f g : Encode.Tier1.EncState → Encode.Tier1.EncState}
    {fd gd : DecState → DecState} (hf : Sim f fd) (hg : Sim g gd) (hgm : Mono g) :
    Sim (fun e => g (f e)) (fun d => gd (fd d)) :=
  fun T d e h hp => hg T _ _ (hf T d e h ((hgm (f e)).trans hp)) hp

private theorem sim_foldl {α : Type} (f : Encode.Tier1.EncState → α → Encode.Tier1.EncState)
    (fd : DecState → α → DecState) (hs : ∀ a, Sim (f · a) (fd · a))
    (hm : ∀ a, Mono (f · a)) :
    ∀ l : List α, Sim (fun e => l.foldl f e) (fun d => l.foldl fd d) ∧
      Mono (fun e => l.foldl f e)
  | [] => ⟨fun _ _ _ h _ => h, fun _ => List.prefix_refl _⟩
  | a :: l => by
    obtain ⟨ih1, ih2⟩ := sim_foldl f fd hs hm l
    exact ⟨sim_comp (hs a) ih1 ih2, mono_comp (hm a) ih2⟩

private theorem mono_emit (e : Encode.Tier1.EncState) (cx : Nat) (b : Bool) :
    e.out.toList <+: (e.emit cx b).out.toList := by
  simp [Encode.Tier1.EncState.emit]

private theorem rel_coeffs {T : List (Nat × Bool)} {d : DecState} {e : Encode.Tier1.EncState}
    (h : Rel T d e) (cs : Array Coeff) : Rel T { d with coeffs := cs } { e with coeffs := cs } :=
  ⟨rfl, h.good⟩

/-! ## Steps -/

private theorem mono_becomeSignificant (g : Geom) (src : Array Int) (p : Nat) (vis : Bool) (x y : Nat) :
    Mono (fun e => Encode.Tier1.becomeSignificant g src p vis e x y) := by
  intro e
  simp [Encode.Tier1.becomeSignificant, Encode.Tier1.encodeSign, Encode.Tier1.EncState.emit]

private theorem sim_becomeSignificant (g : Geom) (src : Array Int) (p : Nat) (vis : Bool) (x y : Nat) :
    Sim (fun e => Encode.Tier1.becomeSignificant g src p vis e x y)
      (fun d => Spec.Tier1.becomeSignificant g p vis d x y) := by
  intro T d e h hp
  simp only [Encode.Tier1.becomeSignificant, Encode.Tier1.encodeSign,
    Spec.Tier1.becomeSignificant, decodeSign] at hp ⊢
  rw [h.coeffs]
  generalize g.signContext e.coeffs x y = sc at hp ⊢
  obtain ⟨cx, xb⟩ := sc
  simp only at hp ⊢
  have hp' : (e.emit cx (Encode.Tier1.srcNeg g src x y != xb)).out.toList <+: T := hp
  obtain ⟨h1, h2⟩ := rel_emit h hp'
  generalize d.decodeBit cx = r at h1 h2 ⊢
  obtain ⟨b, d'⟩ := r
  simp only at h1 h2 ⊢
  subst h1
  have hx : ((Encode.Tier1.srcNeg g src x y != xb) != xb) = Encode.Tier1.srcNeg g src x y := by
    cases Encode.Tier1.srcNeg g src x y <;> cases xb <;> rfl
  rw [hx, h2.coeffs]
  exact rel_coeffs h2 _


private theorem mono_zeroCode (g : Geom) (src : Array Int) (p : Nat) (vis : Bool) (x y : Nat) :
    Mono (fun e => Encode.Tier1.zeroCode g src p vis e x y) := by
  intro e
  simp only [Encode.Tier1.zeroCode]
  split
  · exact (mono_emit _ _ _).trans (mono_becomeSignificant g src p vis x y _)
  · exact mono_emit _ _ _

private theorem sim_zeroCode (g : Geom) (src : Array Int) (p : Nat) (vis : Bool) (x y : Nat) :
    Sim (fun e => Encode.Tier1.zeroCode g src p vis e x y)
      (fun d => Spec.Tier1.zeroCode g p vis d x y) := by
  intro T d e h hp
  simp only [Encode.Tier1.zeroCode, Spec.Tier1.zeroCode] at hp ⊢
  rw [h.coeffs]
  have hp1 : (e.emit (g.zcCtx e.coeffs x y) (Encode.Tier1.srcBit g src p x y)).out.toList
      <+: T := by
    split at hp
    · exact (mono_becomeSignificant g src p vis x y _).trans hp
    · exact hp
  obtain ⟨h1, h2⟩ := rel_emit h hp1
  generalize d.decodeBit (g.zcCtx e.coeffs x y) = r at h1 h2 ⊢
  obtain ⟨b, d'⟩ := r
  simp only at h1 h2 ⊢
  subst h1
  split
  · exact sim_becomeSignificant g src p vis x y T _ _ h2 (by simpa [*] using hp)
  · rw [h2.coeffs]
    exact rel_coeffs h2 _

private theorem mono_sigPropStep (g : Geom) (src : Array Int) (p : Nat) (pos : Nat × Nat) :
    Mono (fun e => Encode.Tier1.sigPropStep g src p e pos) := by
  intro e
  simp only [Encode.Tier1.sigPropStep]
  split
  · exact mono_zeroCode g src p true _ _ e
  · exact List.prefix_refl _

private theorem sim_sigPropStep (g : Geom) (src : Array Int) (p : Nat) (pos : Nat × Nat) :
    Sim (fun e => Encode.Tier1.sigPropStep g src p e pos)
      (fun d => Spec.Tier1.sigPropStep g p d pos) := by
  intro T d e h hp
  simp only [Encode.Tier1.sigPropStep, Spec.Tier1.sigPropStep] at hp ⊢
  rw [h.coeffs]
  split
  · simp only [*] at hp
    exact sim_zeroCode g src p true _ _ T d e h hp
  · exact h

private theorem mono_magRefStep (g : Geom) (src : Array Int) (p : Nat) (pos : Nat × Nat) :
    Mono (fun e => Encode.Tier1.magRefStep g src p e pos) := by
  intro e
  simp only [Encode.Tier1.magRefStep]
  split
  · exact mono_emit _ _ _
  · exact List.prefix_refl _

private theorem sim_magRefStep (g : Geom) (src : Array Int) (p : Nat) (pos : Nat × Nat) :
    Sim (fun e => Encode.Tier1.magRefStep g src p e pos)
      (fun d => Spec.Tier1.magRefStep g p d pos) := by
  intro T d e h hp
  simp only [Encode.Tier1.magRefStep, Spec.Tier1.magRefStep] at hp ⊢
  rw [h.coeffs]
  split
  · simp only [*] at hp
    obtain ⟨h1, h2⟩ := rel_emit h hp
    generalize d.decodeBit (g.mrCtx e.coeffs pos.1 pos.2) = r at h1 h2 ⊢
    obtain ⟨b, d'⟩ := r
    simp only at h1 h2 ⊢
    subst h1
    rw [h2.coeffs]
    exact rel_coeffs h2 _
  · exact h

private theorem mono_cleanupStep (g : Geom) (src : Array Int) (p : Nat) (pos : Nat × Nat) :
    Mono (fun e => Encode.Tier1.cleanupStep g src p e pos) := by
  intro e
  simp only [Encode.Tier1.cleanupStep]
  split
  · exact mono_zeroCode g src p false _ _ e
  · exact List.prefix_refl _

private theorem sim_cleanupStep (g : Geom) (src : Array Int) (p : Nat) (pos : Nat × Nat) :
    Sim (fun e => Encode.Tier1.cleanupStep g src p e pos)
      (fun d => Spec.Tier1.cleanupStep g p d pos) := by
  intro T d e h hp
  simp only [Encode.Tier1.cleanupStep, Spec.Tier1.cleanupStep] at hp ⊢
  rw [h.coeffs]
  split
  · simp only [*] at hp
    exact sim_zeroCode g src p false _ _ T d e h hp
  · exact h


private theorem firstOne_lt {g : Geom} {src : Array Int} {p : Nat} {col : List (Nat × Nat)} {r : Nat}
    (h : Encode.Tier1.firstOne g src p col = some r) : r < col.length :=
  (List.findIdx?_eq_some_iff_findIdx_eq.1 h).1

private theorem runLength_len {g : Geom} {cs : Array Coeff} {col : List (Nat × Nat)}
    (h : runLengthColumn g cs col = true) : col.length = 4 := by
  simp only [runLengthColumn, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

private theorem r_bits (r : Nat) (hr : r < 4) :
    ((if (r / 2 % 2 == 1) = true then 2 else 0) + (if (r % 2 == 1) = true then 1 else 0)) = r := by
  have : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl <;> rfl

private theorem mono_emit3 (e : Encode.Tier1.EncState) (c1 c2 c3 : Nat) (b1 b2 b3 : Bool) :
    e.out.toList <+: (((e.emit c1 b1).emit c2 b2).emit c3 b3).out.toList :=
  (mono_emit _ _ _).trans ((mono_emit _ _ _).trans (mono_emit _ _ _))

/-- The tail of a run-length column after the run-length decisions. -/
private def encTail (g : Geom) (src : Array Int) (p : Nat) (dl : List (Nat × Nat))
    (e : Encode.Tier1.EncState) : Encode.Tier1.EncState :=
  match dl with
  | [] => e
  | (x, y) :: rest =>
    rest.foldl (Encode.Tier1.cleanupStep g src p) (Encode.Tier1.becomeSignificant g src p false e x y)

/-- Decoder mirror of `encTail`. -/
private def decTail (g : Geom) (p : Nat) (dl : List (Nat × Nat)) (d : DecState) : DecState :=
  match dl with
  | [] => d
  | (x, y) :: rest => rest.foldl (cleanupStep g p) (becomeSignificant g p false d x y)

private theorem tail_sim (g : Geom) (src : Array Int) (p : Nat) (dl : List (Nat × Nat)) :
    Sim (encTail g src p dl) (decTail g p dl) ∧ Mono (encTail g src p dl) := by
  have hcs := (sim_foldl _ _ (fun a => sim_cleanupStep g src p a)
    (fun a => mono_cleanupStep g src p a))
  rcases dl with _ | ⟨⟨x, y⟩, rest⟩
  · exact ⟨fun _ _ _ h _ => h, fun _ => List.prefix_refl _⟩
  · constructor
    · intro T d e h hp
      exact sim_comp (sim_becomeSignificant g src p false x y) (hcs rest).1 (hcs rest).2
        T d e h hp
    · intro e
      exact mono_comp (mono_becomeSignificant g src p false x y) (hcs rest).2 e

private theorem enc_cleanupColumn_rl (g : Geom) (src : Array Int) (p : Nat) (e : Encode.Tier1.EncState)
    (col : List (Nat × Nat)) (hrl : runLengthColumn g e.coeffs col = true) (r : Nat)
    (hfo : Encode.Tier1.firstOne g src p col = some r) :
    Encode.Tier1.cleanupColumn g src p e col = encTail g src p (col.drop r)
      (((e.emit ctxRunLength true).emit ctxUniform (r / 2 % 2 == 1)).emit ctxUniform
        (r % 2 == 1)) := by
  simp only [Encode.Tier1.cleanupColumn, hrl, hfo, ite_true]
  generalize List.drop r col = dl
  rcases dl with _ | ⟨⟨x, y⟩, rest⟩ <;> rfl

private theorem dec_cleanupColumn_rl (g : Geom) (p : Nat) (d : DecState)
    (col : List (Nat × Nat)) (hrl : runLengthColumn g d.coeffs col = true) :
    Spec.Tier1.cleanupColumn g p d col =
      if !(d.decodeBit ctxRunLength).1 then (d.decodeBit ctxRunLength).2
      else
        let d1 := (d.decodeBit ctxRunLength).2
        let q1 := d1.decodeBit ctxUniform
        let q0 := q1.2.decodeBit ctxUniform
        decTail g p (col.drop ((if q1.1 then 2 else 0) + (if q0.1 then 1 else 0))) q0.2 := by
  simp only [Spec.Tier1.cleanupColumn, hrl, ite_true]
  split
  · rfl
  · generalize List.drop _ col = dl
    rcases dl with _ | ⟨⟨x, y⟩, rest⟩ <;> rfl

private theorem mono_cleanupColumn (g : Geom) (src : Array Int) (p : Nat) (col : List (Nat × Nat)) :
    Mono (fun e => Encode.Tier1.cleanupColumn g src p e col) := by
  intro e
  have hcs := (sim_foldl _ _ (fun a => sim_cleanupStep g src p a)
    (fun a => mono_cleanupStep g src p a))
  by_cases hrl : runLengthColumn g e.coeffs col = true
  · cases hfo : Encode.Tier1.firstOne g src p col with
    | none =>
      simp only [Encode.Tier1.cleanupColumn, hrl, hfo, ite_true]
      exact mono_emit _ _ _
    | some r =>
      simp only
      rw [enc_cleanupColumn_rl g src p e col hrl r hfo]
      exact (mono_emit3 _ _ _ _ _ _ _).trans ((tail_sim g src p _).2 _)
  · simp only [Encode.Tier1.cleanupColumn, hrl]
    exact (hcs col).2 e

private theorem sim_cleanupColumn (g : Geom) (src : Array Int) (p : Nat) (col : List (Nat × Nat)) :
    Sim (fun e => Encode.Tier1.cleanupColumn g src p e col)
      (fun d => Spec.Tier1.cleanupColumn g p d col) := by
  have hcs := (sim_foldl _ _ (fun a => sim_cleanupStep g src p a)
    (fun a => mono_cleanupStep g src p a))
  intro T d e h hp
  simp only at hp ⊢
  by_cases hrl : runLengthColumn g e.coeffs col = true
  · have hrl' : runLengthColumn g d.coeffs col = true := h.coeffs ▸ hrl
    rw [dec_cleanupColumn_rl g p d col hrl']
    cases hfo : Encode.Tier1.firstOne g src p col with
    | none =>
      simp only [Encode.Tier1.cleanupColumn, hrl, hfo, ite_true] at hp ⊢
      obtain ⟨h1, h2⟩ := rel_emit h hp
      rw [h1]
      exact h2
    | some r =>
      have hr : r < 4 := runLength_len hrl ▸ firstOne_lt hfo
      rw [enc_cleanupColumn_rl g src p e col hrl r hfo] at hp ⊢
      have hp3 := ((tail_sim g src p (col.drop r)).2 _).trans hp
      have hp2 := (mono_emit _ _ _).trans hp3
      have hp1 := (mono_emit _ _ _).trans hp2
      obtain ⟨h1, h2⟩ := rel_emit h hp1
      obtain ⟨h3, h4⟩ := rel_emit h2 hp2
      obtain ⟨h5, h6⟩ := rel_emit h4 hp3
      simp only [h1, h3, h5, Bool.not_true, Bool.false_eq_true, ite_false]
      rw [r_bits r hr]
      exact (tail_sim g src p (col.drop r)).1 T _ _ h6 hp
  · have hrl' : ¬ runLengthColumn g d.coeffs col = true := h.coeffs ▸ hrl
    simp only [Encode.Tier1.cleanupColumn, hrl, Spec.Tier1.cleanupColumn, hrl'] at hp ⊢
    exact (hcs col).1 T d e h hp


/-! ## Passes -/

private theorem sim_sigPropPass (g : Geom) (src : Array Int) (p : Nat) :
    Sim (Encode.Tier1.sigPropPass g src p) (Spec.Tier1.sigPropPass g p) ∧
      Mono (Encode.Tier1.sigPropPass g src p) :=
  sim_foldl _ _ (fun a => sim_sigPropStep g src p a) (fun a => mono_sigPropStep g src p a) _

private theorem sim_magRefPass (g : Geom) (src : Array Int) (p : Nat) :
    Sim (Encode.Tier1.magRefPass g src p) (Spec.Tier1.magRefPass g p) ∧
      Mono (Encode.Tier1.magRefPass g src p) :=
  sim_foldl _ _ (fun a => sim_magRefStep g src p a) (fun a => mono_magRefStep g src p a) _

private theorem sim_cleanupPass (g : Geom) (src : Array Int) (p : Nat) :
    Sim (Encode.Tier1.cleanupPass g src p) (Spec.Tier1.cleanupPass g p) ∧
      Mono (Encode.Tier1.cleanupPass g src p) := by
  have hf := sim_foldl _ _ (fun a => sim_cleanupColumn g src p a)
    (fun a => mono_cleanupColumn g src p a) (stripeColumns g.width g.height)
  constructor
  · intro T d e h hp
    have := hf.1 T d e h hp
    exact ⟨by simp [Encode.Tier1.cleanupPass, Spec.Tier1.cleanupPass, this.coeffs], this.good⟩
  · intro e
    exact hf.2 e

private theorem sim_runPass (g : Geom) (src : Array Int) (K i : Nat) :
    Sim (Encode.Tier1.runPass g src K · i) (Spec.Tier1.runPass g K · i) ∧
      Mono (Encode.Tier1.runPass g src K · i) := by
  simp only [Encode.Tier1.runPass, Spec.Tier1.runPass]
  cases passKind i
  · exact sim_sigPropPass g src _
  · exact sim_magRefPass g src _
  · exact sim_cleanupPass g src _

/-- Invariant of the per-pass split encoder. -/
private def SplitInv (T : List (Nat × Bool)) (d : DecState)
    (st : Encode.Tier1.EncState × Array (List (Nat × Bool))) : Prop :=
  d.coeffs = st.1.coeffs ∧ ∃ R, st.2.toList.flatten ++ R = T ∧ Good d.mq d.cxs R

/-- The step function of `encodePassesSplit`. -/
private def splitStep (g : Geom) (src : Array Int) (K : Nat)
    (st : Encode.Tier1.EncState × Array (List (Nat × Bool))) (i : Nat) :
    Encode.Tier1.EncState × Array (List (Nat × Bool)) :=
  let e := Encode.Tier1.runPass g src K { st.1 with out := #[] } i
  (e, st.2.push e.out.toList)

private theorem splitStep_mono (g : Geom) (src : Array Int) (K : Nat) :
    ∀ (l : List Nat) (st : Encode.Tier1.EncState × Array (List (Nat × Bool))),
      st.2.toList.flatten <+: (l.foldl (splitStep g src K) st).2.toList.flatten
  | [], _ => List.prefix_refl _
  | i :: l, st => by
    refine List.IsPrefix.trans ?_ (splitStep_mono g src K l _)
    simp [splitStep]

private theorem split_sim (g : Geom) (src : Array Int) (K : Nat) (T : List (Nat × Bool)) :
    ∀ (l : List Nat) (st : Encode.Tier1.EncState × Array (List (Nat × Bool))) (d : DecState),
      SplitInv T d st → (l.foldl (splitStep g src K) st).2.toList.flatten <+: T →
      SplitInv T (l.foldl (Spec.Tier1.runPass g K) d) (l.foldl (splitStep g src K) st)
  | [], _, _, h, _ => h
  | i :: l, st, d, h, hp => by
    simp only [List.foldl_cons] at hp ⊢
    apply split_sim g src K T l _ _ _ hp
    have hp1 := (splitStep_mono g src K l (splitStep g src K st i)).trans hp
    obtain ⟨hc, R, hR, hg⟩ := h
    have h0 : Rel R d { st.1 with out := #[] } := ⟨hc, R, by simp, hg⟩
    obtain ⟨t, ht⟩ := hp1
    simp only [splitStep, Array.toList_push, List.flatten_append, List.flatten_cons,
      List.flatten_nil, List.append_nil, List.append_assoc] at ht
    rw [← hR] at ht
    have hRt := List.append_cancel_left ht
    have hpR : (Encode.Tier1.runPass g src K { st.1 with out := #[] } i).out.toList <+: R :=
      ⟨t, hRt⟩
    obtain ⟨hc', R', hR', hg'⟩ := (sim_runPass g src K i).1 R d _ h0 hpR
    refine ⟨hc', R', ?_, hg'⟩
    simp only [splitStep, Array.toList_push, List.flatten_append, List.flatten_cons,
      List.flatten_nil, List.append_nil, List.append_assoc, hR', hR]

/-- **Tier-1 simulation**: decoding the MQ codeword of the encoder's decision trace with
the spec decoder reproduces the encoder's model of the coefficient states. -/
theorem decodePasses_encode (g : Geom) (src : Array Int) (K n : Nat) :
    (Spec.Tier1.decodePasses g K n (DecState.init g (Encode.MQ.encodeAll initialStates
        (Encode.Tier1.encodePassesSplit g src K n (Encode.Tier1.EncState.init g)).2.flatten))).coeffs =
      (Encode.Tier1.encodePassesSplit g src K n (Encode.Tier1.EncState.init g)).1.coeffs := by
  have hfold : Encode.Tier1.encodePassesSplit g src K n (Encode.Tier1.EncState.init g) =
      (((List.range n).foldl (splitStep g src K) (Encode.Tier1.EncState.init g, #[])).1,
       ((List.range n).foldl (splitStep g src K) (Encode.Tier1.EncState.init g, #[])).2.toList) :=
    rfl
  rw [hfold]
  generalize hT : ((List.range n).foldl (splitStep g src K)
    (Encode.Tier1.EncState.init g, #[])).2.toList.flatten = T
  have h0 : SplitInv T (DecState.init g (Encode.MQ.encodeAll initialStates T))
      (Encode.Tier1.EncState.init g, #[]) := by
    refine ⟨rfl, T, by simp, ?_⟩
    have := Spec.MQRoundTrip.roundTrip initialStates T
    exact this
  exact (split_sim g src K T (List.range n) _ _ h0 (hT ▸ List.prefix_refl _)).1

end JPEG2000.Spec.RoundTrip

namespace JPEG2000.Spec.RoundTrip

open JPEG2000.Spec.Tier1

private theorem nodup_flatMap_proj {α β : Type} (proj : β → α) {l : List α} {f : α → List β}
    (hl : l.Nodup) (hf : ∀ a ∈ l, (f a).Nodup) (hp : ∀ a ∈ l, ∀ x ∈ f a, proj x = a) :
    (l.flatMap f).Nodup := by
  rw [List.nodup_iff_pairwise_ne] at hl ⊢
  rw [List.pairwise_flatMap]
  refine ⟨fun a ha => List.nodup_iff_pairwise_ne.1 (hf a ha), ?_⟩
  refine hl.imp_of_mem (fun ha hb hne x hx y hy hxy => hne ?_)
  rw [← hp _ ha x hx, ← hp _ hb y hy, hxy]

private theorem flatten_flatMap {α β : Type} (f : α → List (List β)) :
    ∀ l : List α, (l.flatMap f).flatten = l.flatMap (fun a => (f a).flatten)
  | [] => rfl
  | a :: l => by simp [List.flatMap_cons, List.flatten_append, flatten_flatMap f l]

private theorem scanOrder_eq (w h : Nat) : scanOrder w h =
    (List.range ((h + 3) / 4)).flatMap fun s =>
      (List.range w).flatMap fun x => stripeColumn h x (4 * s) := by
  unfold scanOrder stripeColumns
  rw [flatten_flatMap]
  simp only [List.flatMap_def]

private theorem mem_stripeColumn {h x y0 : Nat} {q : Nat × Nat} (hq : q ∈ stripeColumn h x y0) :
    q.1 = x ∧ y0 ≤ q.2 ∧ q.2 < y0 + 4 ∧ q.2 < h := by
  simp only [stripeColumn, List.mem_map, List.mem_filter, List.mem_range,
    decide_eq_true_eq] at hq
  obtain ⟨r, ⟨h1, h2⟩, rfl⟩ := hq
  exact ⟨rfl, by simp only; omega, by simp only; omega, h2⟩

private theorem stripeColumn_nodup (h x y0 : Nat) : (stripeColumn h x y0).Nodup := by
  unfold stripeColumn
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
  have := (List.nodup_iff_pairwise_ne.1 (@List.nodup_range 4)).filter
    (fun r => decide (y0 + r < h))
  exact this.imp fun hne heq => hne (by simp only [Prod.mk.injEq] at heq; omega)

/-- The scan order visits each position once. -/
theorem scanOrder_nodup (w h : Nat) : (scanOrder w h).Nodup := by
  rw [scanOrder_eq]
  refine nodup_flatMap_proj (fun q => q.2 / 4) List.nodup_range ?_ ?_
  · intro s _
    refine nodup_flatMap_proj (fun q => q.1) List.nodup_range ?_ ?_
    · intro x _; exact stripeColumn_nodup _ _ _
    · intro x _ q hq; exact (mem_stripeColumn hq).1
  · intro s _ q hq
    simp only [List.mem_flatMap, List.mem_range] at hq
    obtain ⟨x, _, hq⟩ := hq
    have := mem_stripeColumn hq
    omega

/-- The scan order visits every position of the block. -/
theorem mem_scanOrder_of {w h x y : Nat} (hx : x < w) (hy : y < h) : (x, y) ∈ scanOrder w h := by
  rw [scanOrder_eq]
  simp only [List.mem_flatMap, List.mem_range, stripeColumn, List.mem_map, List.mem_filter,
    decide_eq_true_eq, Prod.mk.injEq]
  exact ⟨y / 4, by omega, x, hx, y % 4, ⟨by omega, by omega⟩, rfl, by omega⟩

private theorem mem_scanOrder_iff {w h : Nat} {q : Nat × Nat} : q ∈ scanOrder w h ↔ q.1 < w ∧ q.2 < h :=
  ⟨fun hm => mem_scanOrder hm, fun ⟨a, b⟩ => mem_scanOrder_of a b⟩

private theorem stripeColumns_flatten (w h : Nat) : (stripeColumns w h).flatMap id = scanOrder w h := by
  rw [List.flatMap_id]; rfl

end JPEG2000.Spec.RoundTrip

namespace JPEG2000.Spec.RoundTrip

open JPEG2000
open JPEG2000.Spec.Tier1

/-- The encoder's model of the coefficient at position `q`. -/
private def cat (g : Geom) (e : Encode.Tier1.EncState) (q : Nat × Nat) : Coeff := g.coeffAt e.coeffs q.1 q.2

/-- The coefficient array has the block's size. -/
private def SizeOK (g : Geom) (e : Encode.Tier1.EncState) : Prop := e.coeffs.size = g.width * g.height

/-- `q` lies in the block. -/
private def InB (g : Geom) (q : Nat × Nat) : Prop := q.1 < g.width ∧ q.2 < g.height

private theorem cat_set (g : Geom) (e : Encode.Tier1.EncState) (hs : SizeOK g e) (x y : Nat) (hb : InB g (x, y))
    (c : Coeff) (out : Array (Nat × Bool)) (q : Nat × Nat) :
    cat g { coeffs := g.setCoeff e.coeffs x y c, out := out } q =
      if q = (x, y) then c else cat g e q := by
  unfold cat
  rw [Spec.Tier1Equiv.coeffAt_setCoeff g e.coeffs hs x y hb.1 hb.2]
  by_cases h : q = (x, y)
  · subst h; simp
  · have : ¬ ((q.1 : Int) = x ∧ (q.2 : Int) = y) := by
      intro ⟨a, b⟩; apply h; ext <;> simp only <;> omega
    simp [h, this]

private theorem cat_emit (g : Geom) (e : Encode.Tier1.EncState) (cx : Nat) (b : Bool) (q : Nat × Nat) :
    cat g (e.emit cx b) q = cat g e q := rfl

private theorem coeffAt_map' (g : Geom) (cs : Array Coeff) (f : Coeff → Coeff) (hf : f {} = {})
    (X Y : Int) : g.coeffAt (cs.map f) X Y = f (g.coeffAt cs X Y) := by
  unfold Geom.coeffAt
  split
  · rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_map]
    cases cs[g.idx X.toNat Y.toNat]? <;> simp [hf]
  · exact hf.symm

/-! ## Generic fold with footprints -/

private theorem fold_fp {α : Type} (g : Geom) (f : Encode.Tier1.EncState → α → Encode.Tier1.EncState) (fp : α → List (Nat × Nat))
    (Pre Post : (Nat × Nat) → Coeff → Prop)
    (hsize : ∀ e a, SizeOK g e → SizeOK g (f e a))
    (hframe : ∀ e a, SizeOK g e → (∀ q ∈ fp a, InB g q) → (fp a).Nodup → ∀ q, q ∉ fp a →
      cat g (f e a) q = cat g e q)
    (hact : ∀ e a, SizeOK g e → (∀ q ∈ fp a, InB g q) → (fp a).Nodup →
      (∀ q ∈ fp a, Pre q (cat g e q)) →
      ∀ q ∈ fp a, Post q (cat g (f e a) q)) :
    ∀ (l : List α) (e : Encode.Tier1.EncState), SizeOK g e → (l.flatMap fp).Nodup →
      (∀ a ∈ l, ∀ q ∈ fp a, InB g q) → (∀ a ∈ l, ∀ q ∈ fp a, Pre q (cat g e q)) →
      SizeOK g (l.foldl f e) ∧ (∀ a ∈ l, ∀ q ∈ fp a, Post q (cat g (l.foldl f e) q)) ∧
        (∀ q, q ∉ l.flatMap fp → cat g (l.foldl f e) q = cat g e q)
  | [], e, hs, _, _, _ => ⟨hs, by simp, fun _ _ => rfl⟩
  | a :: l, e, hs, hnd, hb, hpre => by
    simp only [List.flatMap_cons, List.nodup_append] at hnd
    obtain ⟨hnd1, hnd2, hdis⟩ := hnd
    have hba : ∀ q ∈ fp a, InB g q := hb a (List.mem_cons_self ..)
    have hs1 := hsize e a hs
    have hpre' : ∀ b ∈ l, ∀ q ∈ fp b, Pre q (cat g (f e a) q) := by
      intro b hbm q hq
      have hq' : q ∉ fp a := fun hm =>
        hdis q hm q (List.mem_flatMap.2 ⟨b, hbm, hq⟩) rfl
      rw [hframe e a hs hba hnd1 q hq']
      exact hpre b (List.mem_cons_of_mem _ hbm) q hq
    obtain ⟨r1, r2, r3⟩ := fold_fp g f fp Pre Post hsize hframe hact l (f e a) hs1 hnd2
      (fun b hbm => hb b (List.mem_cons_of_mem _ hbm)) hpre'
    refine ⟨r1, ?_, ?_⟩
    · intro b hbm q hq
      simp only [List.foldl_cons]
      rcases List.mem_cons.1 hbm with rfl | hbm
      · have hq' : q ∉ l.flatMap fp := fun hm => hdis q hq q hm rfl
        rw [r3 q hq']
        exact hact e b hs hba hnd1 (hpre b (List.mem_cons_self ..)) q hq
      · exact r2 b hbm q hq
    · intro q hq
      simp only [List.foldl_cons, List.flatMap_cons, List.mem_append, not_or] at hq ⊢
      rw [r3 q hq.2, hframe e a hs hba hnd1 q hq.1]


/-! ## Effects of the encoder steps -/

section Effects
variable (g : Geom) (src : Array Int) (p : Nat)

/-- The new state of a coefficient that becomes significant. -/
private def sigC (c : Coeff) (neg : Bool) (p : Nat) (vis : Bool) : Coeff :=
  { c with sig := true, sign := neg, mag := c.mag + 2 ^ p, visited := vis, lsbPlane := p }

private theorem bs_eff (vis : Bool) (e : Encode.Tier1.EncState) (x y : Nat) (hs : SizeOK g e)
    (hb : InB g (x, y)) :
    SizeOK g (Encode.Tier1.becomeSignificant g src p vis e x y) ∧
    ∀ q, cat g (Encode.Tier1.becomeSignificant g src p vis e x y) q =
      if q = (x, y) then sigC (cat g e (x, y)) (Encode.Tier1.srcNeg g src x y) p vis
      else cat g e q := by
  refine ⟨?_, fun q => ?_⟩
  · simp only [SizeOK, Encode.Tier1.becomeSignificant, Encode.Tier1.encodeSign,
      Encode.Tier1.EncState.emit, Spec.Tier1Equiv.setCoeff_size]
    exact hs
  · exact cat_set g (e.emit _ _) hs x y hb _ _ q

private theorem zc_eff (vis : Bool) (e : Encode.Tier1.EncState) (x y : Nat) (hs : SizeOK g e)
    (hb : InB g (x, y)) :
    SizeOK g (Encode.Tier1.zeroCode g src p vis e x y) ∧
    ∀ q, cat g (Encode.Tier1.zeroCode g src p vis e x y) q =
      if q = (x, y) then
        (if Encode.Tier1.srcBit g src p x y then
          sigC (cat g e (x, y)) (Encode.Tier1.srcNeg g src x y) p vis
        else { cat g e (x, y) with visited := vis })
      else cat g e q := by
  simp only [Encode.Tier1.zeroCode]
  split
  · rename_i hb1
    obtain ⟨a, b⟩ := bs_eff g src p vis (e.emit _ _) x y hs hb
    refine ⟨a, fun q => ?_⟩
    rw [b q]
    simp only [hb1]
    rfl
  · rename_i hb1
    refine ⟨?_, fun q => ?_⟩
    · simp only [SizeOK, Encode.Tier1.EncState.emit, Spec.Tier1Equiv.setCoeff_size]; exact hs
    · rw [cat_set g (e.emit _ _) hs x y hb _ _ q]
      simp only [hb1]
      rfl

end Effects

end JPEG2000.Spec.RoundTrip

namespace JPEG2000.Spec.RoundTrip

open JPEG2000
open JPEG2000.Spec.Tier1

section Planes
variable (g : Geom) (src : Array Int)

/-- Magnitude of the source coefficient at `q`. -/
private def mg (q : Nat × Nat) : Nat := (Encode.Tier1.srcAt g src q.1 q.2).natAbs

/-- The magnitude bits of planes `≥ k`. -/
private def hi (k : Nat) (q : Nat × Nat) : Nat := mg g src q / 2 ^ k * 2 ^ k

private theorem hi_succ (k : Nat) (q : Nat × Nat) :
    hi g src k q = hi g src (k + 1) q +
      (if Encode.Tier1.srcBit g src k q.1 q.2 then 2 ^ k else 0) := by
  unfold hi Encode.Tier1.srcBit
  rw [show (Encode.Tier1.srcAt g src q.1 q.2).natAbs = mg g src q from rfl]
  generalize mg g src q = n
  have h1 : n / 2 ^ (k + 1) = n / 2 ^ k / 2 := by
    rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
  have h2 := Nat.div_add_mod (n / 2 ^ k) 2
  rw [h1, Nat.pow_succ]
  generalize n / 2 ^ k = a at h2 ⊢
  have : a % 2 = 0 ∨ a % 2 = 1 := by omega
  rcases this with h | h <;> simp [h]
  · rw [Nat.mul_comm (2 ^ k) 2, ← Nat.mul_assoc, show a / 2 * 2 = a by omega]
  · conv => lhs; rw [show a = a / 2 * 2 + 1 by omega]
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (2 ^ k) 2, ← Nat.mul_assoc]

end Planes

end JPEG2000.Spec.RoundTrip

namespace JPEG2000.Spec.RoundTrip

open JPEG2000
open JPEG2000.Spec.Tier1

section Preds
variable (g : Geom) (src : Array Int)

/-- The coefficient holds exactly the bit-planes `≥ k` of the source. -/
private def AtP (k : Nat) (q : Nat × Nat) (c : Coeff) : Prop :=
  c.mag = hi g src k q ∧ c.sig = decide (hi g src k q ≠ 0) ∧
    (c.sig = true → c.sign = Encode.Tier1.srcNeg g src q.1 q.2)

/-- Start of a bit-plane: planes `≥ k` coded, not visited. -/
private def Done (k : Nat) (q : Nat × Nat) (c : Coeff) : Prop := AtP g src k q c ∧ c.visited = false

/-- After the significance propagation pass of plane `p`. -/
private def S1 (p : Nat) (q : Nat × Nat) (c : Coeff) : Prop :=
  (c.visited = false ∧ AtP g src (p + 1) q c) ∨
    (c.visited = true ∧ hi g src (p + 1) q = 0 ∧ AtP g src p q c)

/-- After the magnitude refinement pass of plane `p`. -/
private def M (p : Nat) (q : Nat × Nat) (c : Coeff) : Prop :=
  (c.visited = true ∧ hi g src (p + 1) q = 0 ∧ AtP g src p q c) ∨
    (c.visited = false ∧ hi g src (p + 1) q ≠ 0 ∧ AtP g src p q c) ∨
    (c.visited = false ∧ hi g src (p + 1) q = 0 ∧ c.sig = false ∧ c.mag = 0)

private theorem fold_single (f : Encode.Tier1.EncState → (Nat × Nat) → Encode.Tier1.EncState)
    (Pre Post : (Nat × Nat) → Coeff → Prop)
    (hsize : ∀ e pos, SizeOK g e → SizeOK g (f e pos))
    (hstep : ∀ e pos, SizeOK g e → InB g pos →
      (∀ q, q ≠ pos → cat g (f e pos) q = cat g e q) ∧
      (Pre pos (cat g e pos) → Post pos (cat g (f e pos) pos)))
    (l : List (Nat × Nat)) (e : Encode.Tier1.EncState) (hs : SizeOK g e) (hnd : l.Nodup)
    (hb : ∀ q ∈ l, InB g q) :
    SizeOK g (l.foldl f e) ∧ (∀ q, q ∉ l → cat g (l.foldl f e) q = cat g e q) ∧
      ((∀ q ∈ l, Pre q (cat g e q)) → ∀ q ∈ l, Post q (cat g (l.foldl f e) q)) := by
  have hfl : l.flatMap (fun a => [a]) = l := by simp
  have gen := fun (Pre Post : (Nat × Nat) → Coeff → Prop)
      (hstep : ∀ e pos, SizeOK g e → InB g pos →
        (∀ q, q ≠ pos → cat g (f e pos) q = cat g e q) ∧
        (Pre pos (cat g e pos) → Post pos (cat g (f e pos) pos)))
      (hpre : ∀ q ∈ l, Pre q (cat g e q)) =>
    fold_fp g f (fun a => [a]) Pre Post hsize
    (fun e a hs hb _ q hq => (hstep e a hs (hb a (List.mem_singleton_self _))).1 q
      (by simpa using hq))
    (fun e a hs hb _ hp q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact (hstep e q hs (hb q (List.mem_singleton_self _))).2 (hp q (List.mem_singleton_self _)))
    l e hs (by rw [hfl]; exact hnd) (fun a ha q hq => by simp at hq; subst hq; exact hb _ ha)
    (fun a ha q hq => by simp at hq; subst hq; exact hpre _ ha)
  obtain ⟨r1, _, r3⟩ := gen (fun _ _ => True) (fun _ _ => True)
    (fun e pos hs hb => ⟨(hstep e pos hs hb).1, fun _ => trivial⟩) (fun _ _ => trivial)
  refine ⟨r1, fun q hq => r3 q (by rw [hfl]; exact hq), fun hpre q hq => ?_⟩
  exact (gen Pre Post hstep hpre).2.1 q hq q (List.mem_singleton_self _)

variable (p : Nat)

private theorem size_zeroCode (vis : Bool) (e : Encode.Tier1.EncState) (x y : Nat) :
    (Encode.Tier1.zeroCode g src p vis e x y).coeffs.size = e.coeffs.size := by
  simp only [Encode.Tier1.zeroCode]
  split <;> simp [Encode.Tier1.becomeSignificant, Encode.Tier1.encodeSign,
    Encode.Tier1.EncState.emit]

private theorem size_becomeSignificant (vis : Bool) (e : Encode.Tier1.EncState) (x y : Nat) :
    (Encode.Tier1.becomeSignificant g src p vis e x y).coeffs.size = e.coeffs.size := by
  simp [Encode.Tier1.becomeSignificant, Encode.Tier1.encodeSign, Encode.Tier1.EncState.emit]

/-- Zero coding of an insignificant coefficient whose higher planes are zero. -/
private theorem zc_correct (q : Nat × Nat) (c : Coeff) (vis : Bool) (h1 : c.sig = false) (h2 : c.mag = 0)
    (h3 : hi g src (p + 1) q = 0) :
    AtP g src p q (if Encode.Tier1.srcBit g src p q.1 q.2 then
      sigC c (Encode.Tier1.srcNeg g src q.1 q.2) p vis else { c with visited := vis }) ∧
    (if Encode.Tier1.srcBit g src p q.1 q.2 then
      sigC c (Encode.Tier1.srcNeg g src q.1 q.2) p vis else { c with visited := vis }).visited
      = vis := by
  have hh := hi_succ g src p q
  rw [h3, Nat.zero_add] at hh
  cases hb : Encode.Tier1.srcBit g src p q.1 q.2
  · simp only [hb, Bool.false_eq_true, ite_false] at hh ⊢
    refine ⟨⟨by simp [h2, hh], by simp [h1, hh], by simp [h1]⟩, trivial⟩
  · simp only [hb, ite_true] at hh ⊢
    have : 2 ^ p ≠ 0 := Nat.pos_iff_ne_zero.1 (Nat.two_pow_pos p)
    refine ⟨⟨by simp [sigC, h2, hh], by simp [sigC, hh], by simp [sigC]⟩, rfl⟩

private theorem sp_step (e : Encode.Tier1.EncState) (pos : Nat × Nat) (hs : SizeOK g e)
    (hb : InB g pos) :
    (∀ q, q ≠ pos → cat g (Encode.Tier1.sigPropStep g src p e pos) q = cat g e q) ∧
    (Done g src (p + 1) pos (cat g e pos) →
      S1 g src p pos (cat g (Encode.Tier1.sigPropStep g src p e pos) pos)) := by
  obtain ⟨x, y⟩ := pos
  simp only [Encode.Tier1.sigPropStep]
  split
  · rename_i hc
    obtain ⟨_, hz⟩ := zc_eff g src p true e x y hs hb
    refine ⟨fun q hq => by rw [hz q]; simp [hq], fun hd => ?_⟩
    rw [hz (x, y)]; simp only [↓reduceIte]
    have hsig : (cat g e (x, y)).sig = false := by
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc; exact hc.1
    obtain ⟨⟨hm, hsg, _⟩, _⟩ := hd
    have h3 : hi g src (p + 1) (x, y) = 0 := by
      rw [hsig] at hsg; simpa using hsg
    have := zc_correct g src p (x, y) (cat g e (x, y)) true hsig (by rw [hm, h3]) h3
    exact Or.inr ⟨this.2, h3, this.1⟩
  · exact ⟨fun _ _ => rfl, fun hd => Or.inl ⟨hd.2, hd.1⟩⟩

private theorem mr_step (e : Encode.Tier1.EncState) (pos : Nat × Nat) (hs : SizeOK g e)
    (hb : InB g pos) :
    (∀ q, q ≠ pos → cat g (Encode.Tier1.magRefStep g src p e pos) q = cat g e q) ∧
    (S1 g src p pos (cat g e pos) →
      M g src p pos (cat g (Encode.Tier1.magRefStep g src p e pos) pos)) := by
  obtain ⟨x, y⟩ := pos
  have hh := hi_succ g src p (x, y)
  simp only [Encode.Tier1.magRefStep, Encode.Tier1.EncState.emit]
  split
  · rename_i hc
    refine ⟨fun q hq => ?_, fun hd => ?_⟩
    · rw [cat_set g e hs x y hb]; simp [hq]
    · rw [cat_set g e hs x y hb]; simp only [↓reduceIte]
      change S1 g src p (x, y) (g.coeffAt e.coeffs x y) at hd
      generalize g.coeffAt e.coeffs ↑x ↑y = c at hc hd ⊢
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
      obtain ⟨hsig, hvis⟩ := hc
      rcases hd with ⟨_, hm, hsg, hsn⟩ | ⟨hv, _⟩
      · have h1 : hi g src (p + 1) (x, y) ≠ 0 := by
          rw [hsig] at hsg; simpa using hsg.symm
        refine Or.inr (Or.inl ⟨hvis, h1, ?_, ?_, ?_⟩)
        · simp only; rw [hm, hh]
        · simp only [hsig]; simp; omega
        · exact hsn
      · rw [hv] at hvis; cases hvis
  · rename_i hc
    refine ⟨fun _ _ => rfl, fun hd => ?_⟩
    change S1 g src p (x, y) (g.coeffAt e.coeffs x y) at hd
    change M g src p (x, y) (g.coeffAt e.coeffs x y)
    generalize g.coeffAt e.coeffs ↑x ↑y = c at hc hd ⊢
    simp only [Bool.and_eq_true, Bool.not_eq_true', not_and, Bool.not_eq_false] at hc
    rcases hd with ⟨hv, hm, hsg, hsn⟩ | ⟨hv, h3, hat⟩
    · have hsig : c.sig = false := by
        cases h : c.sig
        · rfl
        · exact absurd (hc h) (by rw [hv]; decide)
      have h3 : hi g src (p + 1) (x, y) = 0 := by rw [hsig] at hsg; simpa using hsg
      exact Or.inr (Or.inr ⟨hv, h3, hsig, by rw [hm, h3]⟩)
    · exact Or.inl ⟨hv, h3, hat⟩

private theorem cl_step (e : Encode.Tier1.EncState) (pos : Nat × Nat) (hs : SizeOK g e)
    (hb : InB g pos) :
    (∀ q, q ≠ pos → cat g (Encode.Tier1.cleanupStep g src p e pos) q = cat g e q) ∧
    (M g src p pos (cat g e pos) →
      AtP g src p pos (cat g (Encode.Tier1.cleanupStep g src p e pos) pos)) := by
  obtain ⟨x, y⟩ := pos
  simp only [Encode.Tier1.cleanupStep]
  split
  · rename_i hc
    obtain ⟨_, hz⟩ := zc_eff g src p false e x y hs hb
    refine ⟨fun q hq => by rw [hz q]; simp [hq], fun hd => ?_⟩
    rw [hz (x, y)]; simp only [↓reduceIte]
    change M g src p (x, y) (g.coeffAt e.coeffs x y) at hd
    change AtP g src p (x, y) (if Encode.Tier1.srcBit g src p x y = true then
      sigC (g.coeffAt e.coeffs x y) (Encode.Tier1.srcNeg g src x y) p false
      else { g.coeffAt e.coeffs x y with visited := false })
    generalize g.coeffAt e.coeffs ↑x ↑y = c at hc hd ⊢
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
    obtain ⟨hsig, hvis⟩ := hc
    rcases hd with ⟨hv, _⟩ | ⟨_, h1, _, hsg, _⟩ | ⟨_, h3, _, hm⟩
    · rw [hv] at hvis; cases hvis
    · have := hi_succ g src p (x, y)
      rw [hsig] at hsg
      have : hi g src p (x, y) = 0 := by simpa using hsg.symm
      omega
    · exact (zc_correct g src p (x, y) c false hsig hm h3).1
  · rename_i hc
    refine ⟨fun _ _ => rfl, fun hd => ?_⟩
    change M g src p (x, y) (g.coeffAt e.coeffs x y) at hd
    change AtP g src p (x, y) (g.coeffAt e.coeffs x y)
    generalize g.coeffAt e.coeffs ↑x ↑y = c at hc hd ⊢
    rcases hd with ⟨_, _, ha⟩ | ⟨_, _, ha⟩ | ⟨hv, _, hsg, _⟩
    · exact ha
    · exact ha
    · simp [hv, hsg] at hc

private theorem size_cleanupStep (e : Encode.Tier1.EncState) (pos : Nat × Nat) :
    (Encode.Tier1.cleanupStep g src p e pos).coeffs.size = e.coeffs.size := by
  simp only [Encode.Tier1.cleanupStep]
  split
  · exact size_zeroCode g src p _ _ _ _
  · rfl

private theorem foldl_inv {α β : Type} (P : β → Prop) (f : β → α → β) (h : ∀ b a, P b → P (f b a)) :
    ∀ (l : List α) (b : β), P b → P (l.foldl f b)
  | [], _, hb => hb
  | a :: l, b, hb => foldl_inv P f h l (f b a) (h b a hb)

private theorem size_cleanupColumn (e : Encode.Tier1.EncState) (col : List (Nat × Nat)) :
    (Encode.Tier1.cleanupColumn g src p e col).coeffs.size = e.coeffs.size := by
  have hf : ∀ (l : List (Nat × Nat)) (e' : Encode.Tier1.EncState),
      (l.foldl (Encode.Tier1.cleanupStep g src p) e').coeffs.size = e'.coeffs.size := by
    intro l e'
    exact foldl_inv (fun b : Encode.Tier1.EncState => b.coeffs.size = e'.coeffs.size) _
      (fun b a hb => (size_cleanupStep g src p b a).trans hb) l e' rfl
  by_cases hrl : runLengthColumn g e.coeffs col = true
  · cases hfo : Encode.Tier1.firstOne g src p col with
    | none => simp [Encode.Tier1.cleanupColumn, hrl, hfo, Encode.Tier1.EncState.emit]
    | some r =>
      rw [enc_cleanupColumn_rl g src p e col hrl r hfo]
      generalize List.drop r col = dl
      rcases dl with _ | ⟨⟨x, y⟩, rest⟩
      · rfl
      · simp only [encTail]
        rw [hf, size_becomeSignificant]; rfl
  · simp only [Encode.Tier1.cleanupColumn, hrl]
    exact hf col e

private theorem atp_zero (q : Nat × Nat) (c : Coeff) (h1 : c.sig = false) (h2 : c.mag = 0)
    (h3 : hi g src (p + 1) q = 0) (h4 : Encode.Tier1.srcBit g src p q.1 q.2 = false) :
    AtP g src p q c := by
  have hh := hi_succ g src p q
  rw [h3, h4] at hh
  simp only [Bool.false_eq_true, ite_false, Nat.add_zero] at hh
  exact ⟨by rw [h2, hh], by simp [h1, hh], by simp [h1]⟩

private theorem m_rl (q : Nat × Nat) (c : Coeff) (hm : M g src p q c) (hsig : c.sig = false)
    (hvis : c.visited = false) : c.mag = 0 ∧ hi g src (p + 1) q = 0 := by
  rcases hm with ⟨hv, _⟩ | ⟨_, h1, _, hsg, _⟩ | ⟨_, h3, _, hm⟩
  · rw [hv] at hvis; cases hvis
  · have := hi_succ g src p q
    rw [hsig] at hsg
    have : hi g src p q = 0 := by simpa using hsg.symm
    omega
  · exact ⟨hm, h3⟩

private theorem rl_facts {e : Encode.Tier1.EncState} {col : List (Nat × Nat)}
    (hrl : runLengthColumn g e.coeffs col = true) (q : Nat × Nat) (hq : q ∈ col) :
    (cat g e q).sig = false ∧ (cat g e q).visited = false := by
  simp only [runLengthColumn, Bool.and_eq_true, List.all_eq_true] at hrl
  have := hrl.2 q hq
  obtain ⟨x, y⟩ := q
  simp only [Bool.not_eq_true'] at this
  exact ⟨this.1.1, this.1.2⟩

private theorem cc_col (e : Encode.Tier1.EncState) (col : List (Nat × Nat)) (hs : SizeOK g e)
    (hnd : col.Nodup) (hb : ∀ q ∈ col, InB g q) :
    (∀ q, q ∉ col → cat g (Encode.Tier1.cleanupColumn g src p e col) q = cat g e q) ∧
    ((∀ q ∈ col, M g src p q (cat g e q)) →
      ∀ q ∈ col, AtP g src p q (cat g (Encode.Tier1.cleanupColumn g src p e col) q)) := by
  have hsz : ∀ e' pos, SizeOK g e' → SizeOK g (Encode.Tier1.cleanupStep g src p e' pos) :=
    fun e' pos h => (size_cleanupStep g src p e' pos).trans h
  by_cases hrl : runLengthColumn g e.coeffs col = true
  · cases hfo : Encode.Tier1.firstOne g src p col with
    | none =>
      have he : Encode.Tier1.cleanupColumn g src p e col = e.emit ctxRunLength false := by
        simp [Encode.Tier1.cleanupColumn, hrl, hfo]
      rw [he]
      refine ⟨fun _ _ => rfl, fun hm q hq => ?_⟩
      have hbit := List.findIdx?_eq_none_iff.1 hfo q hq
      obtain ⟨h1, h2⟩ := rl_facts g hrl q hq
      obtain ⟨h3, h4⟩ := m_rl g src p q _ (hm q hq) h1 h2
      obtain ⟨x, y⟩ := q
      exact atp_zero g src p (x, y) _ h1 h3 h4 hbit
    | some r =>
      rw [enc_cleanupColumn_rl g src p e col hrl r hfo]
      obtain ⟨hr, hbr, hbj⟩ := List.findIdx?_eq_some_iff_getElem.1 hfo
      have hcol := List.take_append_drop r col
      rw [List.drop_eq_getElem_cons hr] at hcol ⊢
      have hnd' := hnd
      rw [← hcol, List.nodup_append, List.nodup_cons] at hnd'
      obtain ⟨_, ⟨hxr, hndr⟩, hdis⟩ := hnd'
      generalize hxy : col[r] = xy at hbr hcol hxr hdis ⊢
      obtain ⟨x, y⟩ := xy
      generalize hrest : List.drop (r + 1) col = rest at hcol hxr hndr hdis ⊢
      have hmem : ∀ q, q ∈ col ↔ q ∈ List.take r col ∨ q = (x, y) ∨ q ∈ rest := by
        intro q; conv => lhs; rw [← hcol]
        simp
      have hbxy : InB g (x, y) := hb _ ((hmem _).2 (Or.inr (Or.inl rfl)))
      generalize he3 : ((e.emit ctxRunLength true).emit ctxUniform (r / 2 % 2 == 1)).emit
        ctxUniform (r % 2 == 1) = e3
      have hc3 : ∀ q, cat g e3 q = cat g e q := fun q => by rw [← he3]; rfl
      have hs3 : SizeOK g e3 := by rw [← he3]; exact hs
      obtain ⟨hs4, hz4⟩ := bs_eff g src p false e3 x y hs3 hbxy
      simp only [encTail]
      obtain ⟨_, hfr, hpost⟩ := fold_single g (Encode.Tier1.cleanupStep g src p) (M g src p)
        (AtP g src p) hsz (fun e' pos hs' hb' => cl_step g src p e' pos hs' hb') rest _ hs4 hndr
        (fun q hq => hb q ((hmem q).2 (Or.inr (Or.inr hq))))
      have hfr' : ∀ q, q ∉ col → cat g (List.foldl (Encode.Tier1.cleanupStep g src p)
          (Encode.Tier1.becomeSignificant g src p false e3 x y) rest) q = cat g e q := by
        intro q hq
        have h1 : q ∉ rest := fun h => hq ((hmem q).2 (Or.inr (Or.inr h)))
        have h2 : q ≠ (x, y) := fun h => hq ((hmem q).2 (Or.inr (Or.inl h)))
        rw [hfr q h1, hz4 q]; simp [h2, hc3]
      refine ⟨hfr', fun hm q hq => ?_⟩
      have hmq := hm q hq
      have hmxy := hm (x, y) ((hmem _).2 (Or.inr (Or.inl rfl)))
      rcases (hmem q).1 hq with ht | rfl | hr'
      · have h1 : q ∉ rest := fun h => hdis q ht q (List.mem_cons_of_mem _ h) rfl
        have h2 : q ≠ (x, y) := fun h => hdis q ht q (h ▸ List.mem_cons_self ..) rfl
        rw [hfr q h1, hz4 q]; simp only [h2, ↓reduceIte, hc3]
        obtain ⟨j, hj, hjq⟩ := List.mem_take_iff_getElem.1 ht
        have hbit := hbj j (by omega)
        rw [hjq] at hbit
        obtain ⟨h1', h2'⟩ := rl_facts g hrl q hq
        obtain ⟨h3, h4⟩ := m_rl g src p q _ hmq h1' h2'
        obtain ⟨qx, qy⟩ := q
        exact atp_zero g src p (qx, qy) _ h1' h3 h4 (by simpa using hbit)
      · rw [hfr _ hxr, hz4]; simp only [↓reduceIte, hc3]
        obtain ⟨h1', h2'⟩ := rl_facts g hrl (x, y) hq
        obtain ⟨h3, h4⟩ := m_rl g src p (x, y) _ hmq h1' h2'
        have hh := hi_succ g src p (x, y)
        simp only at hbr hh
        rw [h4, hbr] at hh
        simp only [ite_true, Nat.zero_add] at hh
        have : 2 ^ p ≠ 0 := Nat.pos_iff_ne_zero.1 (Nat.two_pow_pos p)
        refine ⟨by simp [sigC, h3, hh], by simp [sigC, hh], fun _ => rfl⟩
      · refine hpost (fun q' hq' => ?_) q hr'
        have h2 : q' ≠ (x, y) := fun h => hxr (h ▸ hq')
        rw [hz4 q']; simp only [h2, ↓reduceIte, hc3]
        exact hm q' ((hmem q').2 (Or.inr (Or.inr hq')))
  · simp only [Encode.Tier1.cleanupColumn, hrl]
    obtain ⟨_, r2, r3⟩ := fold_single g (Encode.Tier1.cleanupStep g src p) (M g src p)
      (AtP g src p) hsz (fun e' pos hs' hb' => cl_step g src p e' pos hs' hb') col e hs hnd hb
    exact ⟨r2, r3⟩

end Preds

end JPEG2000.Spec.RoundTrip

namespace JPEG2000.Spec.RoundTrip

open JPEG2000
open JPEG2000.Spec.Tier1

section Passes
variable (g : Geom) (src : Array Int) (p : Nat)

private theorem size_sigPropStep (e : Encode.Tier1.EncState) (pos : Nat × Nat) :
    (Encode.Tier1.sigPropStep g src p e pos).coeffs.size = e.coeffs.size := by
  simp only [Encode.Tier1.sigPropStep]
  split
  · exact size_zeroCode g src p _ _ _ _
  · rfl

private theorem size_magRefStep (e : Encode.Tier1.EncState) (pos : Nat × Nat) :
    (Encode.Tier1.magRefStep g src p e pos).coeffs.size = e.coeffs.size := by
  simp only [Encode.Tier1.magRefStep]
  split
  · simp [Encode.Tier1.EncState.emit]
  · rfl

private theorem scan_inB : ∀ q ∈ scanOrder g.width g.height, InB g q :=
  fun _ hq => mem_scanOrder hq

private theorem sp_pass (e : Encode.Tier1.EncState) (hs : SizeOK g e)
    (h : ∀ q ∈ scanOrder g.width g.height, Done g src (p + 1) q (cat g e q)) :
    SizeOK g (Encode.Tier1.sigPropPass g src p e) ∧
      ∀ q ∈ scanOrder g.width g.height, S1 g src p q (cat g (Encode.Tier1.sigPropPass g src p e) q) := by
  obtain ⟨r1, _, r3⟩ := fold_single g (Encode.Tier1.sigPropStep g src p) (Done g src (p + 1))
    (S1 g src p) (fun e pos h => (size_sigPropStep g src p e pos).trans h)
    (fun e pos hs hb => sp_step g src p e pos hs hb) _ e hs (scanOrder_nodup _ _) (scan_inB g)
  exact ⟨r1, r3 h⟩

private theorem mr_pass (e : Encode.Tier1.EncState) (hs : SizeOK g e)
    (h : ∀ q ∈ scanOrder g.width g.height, S1 g src p q (cat g e q)) :
    SizeOK g (Encode.Tier1.magRefPass g src p e) ∧
      ∀ q ∈ scanOrder g.width g.height, M g src p q (cat g (Encode.Tier1.magRefPass g src p e) q) := by
  obtain ⟨r1, _, r3⟩ := fold_single g (Encode.Tier1.magRefStep g src p) (S1 g src p)
    (M g src p) (fun e pos h => (size_magRefStep g src p e pos).trans h)
    (fun e pos hs hb => mr_step g src p e pos hs hb) _ e hs (scanOrder_nodup _ _) (scan_inB g)
  exact ⟨r1, r3 h⟩

private theorem cl_pass (e : Encode.Tier1.EncState) (hs : SizeOK g e)
    (h : ∀ q ∈ scanOrder g.width g.height, M g src p q (cat g e q)) :
    SizeOK g (Encode.Tier1.cleanupPass g src p e) ∧
      ∀ q ∈ scanOrder g.width g.height, Done g src p q (cat g (Encode.Tier1.cleanupPass g src p e) q) := by
  have hfl := stripeColumns_flatten g.width g.height
  have hmem : ∀ a ∈ stripeColumns g.width g.height, ∀ q ∈ id a, q ∈ scanOrder g.width g.height :=
    fun a ha q hq => hfl ▸ List.mem_flatMap.2 ⟨a, ha, hq⟩
  obtain ⟨r1, r2, _⟩ := fold_fp g (Encode.Tier1.cleanupColumn g src p) id (M g src p) (AtP g src p)
    (fun e a h => (size_cleanupColumn g src p e a).trans h)
    (fun e a hs hb hnd => (cc_col g src p e a hs hnd hb).1)
    (fun e a hs hb hnd => (cc_col g src p e a hs hnd hb).2)
    (stripeColumns g.width g.height) e hs (hfl ▸ scanOrder_nodup _ _)
    (fun a ha q hq => scan_inB g q (hmem a ha q hq)) (fun a ha q hq => h q (hmem a ha q hq))
  refine ⟨by simpa [SizeOK, Encode.Tier1.cleanupPass, clearVisited] using r1, fun q hq => ?_⟩
  rw [← hfl, List.mem_flatMap] at hq
  obtain ⟨a, ha, hq⟩ := hq
  have := r2 a ha q hq
  simp only [cat, Encode.Tier1.cleanupPass, clearVisited] at this ⊢
  rw [coeffAt_map' g _ _ rfl]
  exact ⟨this, rfl⟩

end Passes

end JPEG2000.Spec.RoundTrip

namespace JPEG2000.Spec.RoundTrip

open JPEG2000
open JPEG2000.Spec.Tier1

private theorem passKind_0 : passKind 0 = .cleanup := rfl
private theorem passKind_1 (m : Nat) : passKind (3 * m + 1) = .sigProp := by
  simp [passKind, Nat.mul_mod_right]
private theorem passKind_2 (m : Nat) : passKind (3 * m + 2) = .magRef := by
  simp only [passKind, show 3 * m + 2 ≠ 0 by omega, ↓reduceIte,
    show 3 * m + 2 - 1 = 3 * m + 1 by omega, Nat.mul_add_mod]
private theorem passKind_3 (m : Nat) : passKind (3 * m + 3) = .cleanup := by
  simp only [passKind, show 3 * m + 3 ≠ 0 by omega, ↓reduceIte,
    show 3 * m + 3 - 1 = 3 * m + 2 by omega, Nat.mul_add_mod]

section Planes2
variable (g : Geom) (src : Array Int)

/-- The invariant at the start of a bit-plane. -/
private def PInv (k : Nat) (e : Encode.Tier1.EncState) : Prop :=
  SizeOK g e ∧ ∀ q ∈ scanOrder g.width g.height, Done g src k q (cat g e q)

private theorem done_M (k : Nat) (q : Nat × Nat) (c : Coeff) (hd : Done g src (k + 1) q c)
    (h0 : hi g src (k + 1) q = 0) : M g src k q c := by
  obtain ⟨⟨hm, hsg, _⟩, hv⟩ := hd
  rw [h0] at hm hsg
  exact Or.inr (Or.inr ⟨hv, h0, by simpa using hsg, hm⟩)

private theorem done_S1 (k : Nat) (q : Nat × Nat) (c : Coeff) (hd : Done g src (k + 1) q c) :
    S1 g src k q c := Or.inl ⟨hd.2, hd.1⟩

private theorem plane_step (K m : Nat) (hm : m + 1 < K) (st : Encode.Tier1.EncState × Array (List (Nat × Bool)))
    (h : PInv g src (K - 1 - m) st.1) :
    PInv g src (K - 1 - (m + 1))
      ([3 * m + 1, 3 * m + 2, 3 * m + 3].foldl (splitStep g src K) st).1 := by
  have hp : K - 1 - m = (K - 1 - (m + 1)) + 1 := by omega
  rw [hp] at h
  have h1 : passPlane K (3 * m + 1) = K - 1 - (m + 1) := by simp only [passPlane]; omega
  have h2 : passPlane K (3 * m + 2) = K - 1 - (m + 1) := by simp only [passPlane]; omega
  have h3 : passPlane K (3 * m + 3) = K - 1 - (m + 1) := by simp only [passPlane]; omega
  simp only [List.foldl_cons, List.foldl_nil, splitStep, Encode.Tier1.runPass, passKind_1,
    passKind_2, passKind_3, h1, h2, h3]
  generalize K - 1 - (m + 1) = p at h ⊢
  obtain ⟨hs, hd⟩ := h
  obtain ⟨s1, d1⟩ := sp_pass g src p { st.1 with out := #[] } hs hd
  obtain ⟨s2, d2⟩ := mr_pass g src p { (Encode.Tier1.sigPropPass g src p { st.1 with out := #[] })
    with out := #[] } s1 d1
  exact cl_pass g src p _ s2 d2

private theorem planes (K : Nat) (hK : ∀ q ∈ scanOrder g.width g.height, hi g src K q = 0) :
    ∀ m, m < K → ∀ st : Encode.Tier1.EncState × Array (List (Nat × Bool)),
      PInv g src K st.1 →
      PInv g src (K - 1 - m) ((List.range (3 * m + 1)).foldl (splitStep g src K) st).1
  | 0, hm, st, h => by
    have hp : K = (K - 1) + 1 := by omega
    have hpp : passPlane K 0 = K - 1 := by simp [passPlane]
    simp only [Nat.mul_zero, Nat.zero_add, List.range_one, List.foldl_cons, List.foldl_nil,
      splitStep, Encode.Tier1.runPass, passKind_0, hpp, Nat.sub_zero]
    obtain ⟨hs, hd⟩ := h
    rw [hp] at hd hK
    exact cl_pass g src (K - 1) _ hs
      (fun q hq => done_M g src (K - 1) q _ (hd q hq) (hK q hq))
  | m + 1, hm, st, h => by
    have ih := planes K hK m (by omega) st h
    have : List.range (3 * (m + 1) + 1) = List.range (3 * m + 1) ++ [3 * m + 1, 3 * m + 2, 3 * m + 3] := by
      rw [show 3 * (m + 1) + 1 = 3 * m + 1 + 1 + 1 + 1 by omega, List.range_succ, List.range_succ,
        List.range_succ]
      simp
    rw [this, List.foldl_append]
    exact plane_step g src K m hm _ ih

end Planes2

end JPEG2000.Spec.RoundTrip

namespace JPEG2000.Spec.RoundTrip

open JPEG2000
open JPEG2000.Spec.Tier1

private theorem foldl_max_bound : ∀ (l : List Int) (a : Nat),
    a ≤ l.foldl (fun m v => max m v.natAbs) a ∧
      ∀ v ∈ l, v.natAbs ≤ l.foldl (fun m v => max m v.natAbs) a
  | [], a => ⟨Nat.le_refl _, by simp⟩
  | v :: l, a => by
    obtain ⟨i1, i2⟩ := foldl_max_bound l (max a v.natAbs)
    refine ⟨Nat.le_trans (Nat.le_max_left _ _) i1, fun u hu => ?_⟩
    rcases List.mem_cons.1 hu with rfl | hu
    · exact Nat.le_trans (Nat.le_max_right _ _) i1
    · exact i2 u hu

private theorem mg_le_maxMag (g : Geom) (src : Array Int) (q : Nat × Nat) :
    mg g src q ≤ Encode.Tier1.maxMag src := by
  unfold mg Encode.Tier1.srcAt Encode.Tier1.maxMag
  rw [← Array.foldl_toList, Array.getD_eq_getD_getElem?]
  cases hq : src[g.idx q.1 q.2]? with
  | none => simp
  | some v =>
    simp only [Option.getD_some]
    obtain ⟨hi', hv⟩ := Array.getElem?_eq_some_iff.1 hq
    exact (foldl_max_bound src.toList 0).2 v (hv ▸ Array.getElem_mem_toList hi')

private theorem hi_numBits (g : Geom) (src : Array Int) (q : Nat × Nat) :
    hi g src (Encode.Tier1.numBits (Encode.Tier1.maxMag src)) q = 0 := by
  unfold hi
  have := Nat.lt_of_le_of_lt (mg_le_maxMag g src q)
    (Encode.Tier1.lt_two_pow_numBits (Encode.Tier1.maxMag src))
  rw [Nat.div_eq_of_lt this, Nat.zero_mul]

private theorem cat_init (g : Geom) (q : Nat × Nat) : cat g (Encode.Tier1.EncState.init g) q = {} := by
  simp only [cat, Encode.Tier1.EncState.init, Geom.coeffAt]
  split
  · rw [Array.getD_eq_getD_getElem?]
    cases h : (Array.replicate (g.width * g.height) ({} : Coeff))[g.idx (q.1 : Int).toNat (q.2 : Int).toNat]? with
    | none => rfl
    | some c =>
      obtain ⟨_, hc⟩ := Array.getElem?_eq_some_iff.1 h
      rw [← hc, Array.getElem_replicate]; rfl
  · rfl

private theorem pinv_init (g : Geom) (src : Array Int) :
    PInv g src (Encode.Tier1.numBits (Encode.Tier1.maxMag src)) (Encode.Tier1.EncState.init g) := by
  refine ⟨by simp [SizeOK, Encode.Tier1.EncState.init], fun q _ => ?_⟩
  rw [cat_init]
  have := hi_numBits g src q
  exact ⟨⟨by rw [this], by rw [this]; rfl, by simp⟩, rfl⟩

private theorem value_of_atp (g : Geom) (src : Array Int) (q : Nat × Nat) (c : Coeff)
    (h : AtP g src 0 q c) : c.value = Encode.Tier1.srcAt g src q.1 q.2 := by
  obtain ⟨hm, hsg, hsn⟩ := h
  simp only [hi, mg, Nat.pow_zero, Nat.div_one, Nat.mul_one] at hm hsg
  unfold Coeff.value
  simp only [Encode.Tier1.srcNeg] at hsn
  generalize Encode.Tier1.srcAt g src q.1 q.2 = v at hm hsg hsn
  by_cases hv : v = 0
  · subst hv; simp at hm; simp [hm]
  · have hs : c.sig = true := by rw [hsg]; simp; omega
    have := hsn hs
    rw [this, hm]
    by_cases hneg : v < 0
    · simp [hneg]; omega
    · simp [hneg]; omega

end JPEG2000.Spec.RoundTrip

namespace JPEG2000.Spec.RoundTrip

open JPEG2000
open JPEG2000.Spec.Tier1

private theorem values_eq (g : Geom) (src : Array Int) (cs : Array Coeff)
    (hcs : cs.size = g.width * g.height) (hsrc : src.size = g.width * g.height)
    (hd : ∀ q ∈ scanOrder g.width g.height, AtP g src 0 q (g.coeffAt cs q.1 q.2)) :
    cs.map Coeff.value = src := by
  apply Array.ext
  · simp [hcs, hsrc]
  · intro i h1 _
    rw [Array.getElem_map]
    simp only [Array.size_map, hcs] at h1
    have hw : 0 < g.width := Nat.pos_of_ne_zero (fun h0 => by simp [h0] at h1)
    have hx : i % g.width < g.width := Nat.mod_lt _ hw
    have hy : i / g.width < g.height := by
      rw [Nat.div_lt_iff_lt_mul hw, Nat.mul_comm]; exact h1
    have hidx : g.idx (i % g.width) (i / g.width) = i := by
      unfold Geom.idx
      have := Nat.div_add_mod i g.width
      rw [Nat.mul_comm] at this; exact this
    have := value_of_atp g src _ _ (hd _ (mem_scanOrder_of hx hy))
    simp only [Encode.Tier1.srcAt, hidx, Geom.coeffAt] at this
    simp only [Int.natCast_nonneg, Int.ofNat_lt, hx, hy, and_self, ↓reduceIte,
      Int.toNat_natCast, hidx] at this
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega)] at this
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega)] at this
    exact this


/-- The encoder's final coefficient states hold the source. -/
private theorem enc_final (g : Geom) (src : Array Int) :
    let K := Encode.Tier1.numBits (Encode.Tier1.maxMag src)
    let n := if K = 0 then 0 else 3 * K - 2
    PInv g src 0 (Encode.Tier1.encodePassesSplit g src K n (Encode.Tier1.EncState.init g)).1 := by
  intro K n
  have h0 := pinv_init g src
  by_cases hK : K = 0
  · have hn : n = 0 := by simp [n, hK]
    rw [hn]
    show PInv g src 0 (Encode.Tier1.EncState.init g)
    rw [← hK]; exact h0
  · have hn : n = 3 * (K - 1) + 1 := by simp only [n, hK, ↓reduceIte]; omega
    rw [hn]
    have := planes g src K (fun q _ => hi_numBits g src q) (K - 1) (by omega)
      (Encode.Tier1.EncState.init g, #[]) h0
    rw [show K - 1 - (K - 1) = 0 by omega] at this
    exact this

/-- **C10, layer 1 — the Tier-1 round trip (plain mode).** If the reference Tier-1 encoder
accepts a `w × h` block of signed quantisation indices `src` (orientation `orient`, `Mb`
magnitude bit-planes), the spec Tier-1 decoder, given the block as Tier-2 delivers it (the
encoder's zero bit-planes, pass count and codeword, one segment), returns exactly `src`.
Side condition: at most 37 coded bit-planes (`numBits (maxMag src) ≤ 37`), i.e. at most
3·37 − 2 = 109 passes, so the decoder's OpenJPEG-compatible 109-pass segment cap (task 4.9)
leaves the encoder's single codeword segment intact. -/
theorem decodeValues_encodeCodeBlock {w h : Nat} {orient : Orientation} {Mb : Nat}
    {src : Array Int} {o : Encode.Tier1.EncOut}
    (henc : Encode.Tier1.encodeCodeBlock w h orient Mb src = .ok o)
    (hK : Encode.Tier1.numBits (Encode.Tier1.maxMag src) ≤ 37) :
    decodeValues (CodeBlock.ofData w h orient Mb o.zeroBitPlanes o.numPasses o.bytes) = .ok src := by
  have hfin := enc_final { width := w, height := h, orient := orient } src
  unfold Encode.Tier1.encodeCodeBlock at henc
  by_cases h1 : w > 1024 ∨ h > 1024 ∨ w * h > 4096
  · simp [h1] at henc; cases henc
  by_cases h2 : src.size ≠ w * h
  · simp [h1, h2] at henc; cases henc
  by_cases h3 : Encode.Tier1.numBits (Encode.Tier1.maxMag src) > Mb
  · simp [h1, h2, h3] at henc; cases henc
  simp only [h1, h2, h3, ↓reduceIte] at henc
  generalize Encode.Tier1.numBits (Encode.Tier1.maxMag src) = K at henc h3 hfin hK
  generalize hg : ({ width := w, height := h, orient := orient } : Geom) = g at henc hfin
  generalize hn : (if K = 0 then 0 else 3 * K - 2) = n at henc hfin
  simp only [pure, Except.pure, Except.ok.injEq] at henc
  subst henc
  simp only
  -- the decoder's block
  generalize hcb : CodeBlock.ofData w h orient Mb (Mb - K) n
    (if n = 0 then [] else Encode.MQ.encodeAll initialStates
      (Encode.Tier1.encodePassesSplit g src K n (Encode.Tier1.EncState.init g)).2.flatten) = cb
  have hgeom : cb.geom = g := by rw [← hcb, ← hg]; rfl
  have hcp : cb.codedPlanes = K := by
    rw [← hcb]; simp only [CodeBlock.codedPlanes, CodeBlock.ofData]; omega
  have hnp : cb.numPasses = n := by
    rw [← hcb]; simp only [CodeBlock.numPasses, CodeBlock.ofData, Segment.single]
    split <;> simp [*]
  have hle : n ≤ 3 * K - 2 := by rw [← hn]; split <;> omega
  have hclamp : cb.clampPasses = cb := by
    simp only [CodeBlock.clampPasses, hnp, hcp, hle, ↓reduceIte]
  have hval : cb.validate = .ok () := by
    have hw : ¬ (cb.width > 1024 ∨ cb.height > 1024 ∨ cb.width * cb.height > 4096) := by
      rw [← hcb]; exact h1
    have hseg : cb.segments.map (·.passes) = segmentPasses cb.mode n 0 := by
      rw [segmentPasses_plain _ (by rw [← hcb]; rfl) (by rw [← hcb]; rfl) _ _ (by omega)]
      rw [← hcb]; simp only [CodeBlock.ofData, Segment.single]
      split <;> simp
    simp only [CodeBlock.validate, hw, ↓reduceIte, hnp, hcp, hseg]
    have : ¬ (0 < n ∧ n > 3 * K - 2) := by omega
    simp [this]
    rfl
  have hstate : (decodeState cb).coeffs =
      (Encode.Tier1.encodePassesSplit g src K n (Encode.Tier1.EncState.init g)).1.coeffs := by
    by_cases hn0 : n = 0
    · subst hn0 hg
      rw [← hcb]
      rfl
    · have hs : cb.segments = [⟨Encode.MQ.encodeAll initialStates
          (Encode.Tier1.encodePassesSplit g src K n (Encode.Tier1.EncState.init g)).2.flatten, n⟩] := by
        rw [← hcb]; simp only [CodeBlock.ofData, Segment.single, hn0, ↓reduceIte]
      rw [decodeState_plain cb (by rw [← hcb]; rfl) _ n hs, hgeom, hcp]
      exact decodePasses_encode g src K n
  unfold decodeValues decodeCodeBlock
  rw [hclamp]
  unfold decodeCodeBlockExact
  rw [hval]
  simp only [bind, Except.bind, pure, Except.pure, Except.map, Except.ok.injEq]
  rw [hstate]
  obtain ⟨hs, hd⟩ := hfin
  rw [hn] at hs hd
  have hsz : g.width * g.height = w * h := by rw [← hg]
  apply values_eq g src _ hs (by rw [hsz]; exact Classical.not_not.1 h2)
  intro q hq
  exact (hd q hq).1

end JPEG2000.Spec.RoundTrip

