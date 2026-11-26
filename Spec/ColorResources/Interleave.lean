import Spec.NativeResources

/-!
# Interleaved display buffers (Plan.md §§3–5, 7, S3; T.800 Annex I)

The format changes the number of byte writes, while both kernels visit one sample per
pixel and selected channel. Refusal uses the caller's display budget.
-/

namespace JPEG2000.Spec.ColorResources

open JPEG2000

private theorem unit_loop {α β : Type} (xs : Array α) (z : β)
    (f : α → β → Except Error (ForInStep β))
    (hf : ∀ a ∈ xs, f a z = .ok (.yield z)) : forIn xs z f = .ok z := by
  rw [← Array.forIn_toList]
  have hl : ∀ a ∈ xs.toList, f a z = .ok (.yield z) := fun a h => hf a (Array.mem_def.mpr h)
  generalize xs.toList = l at hl ⊢
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.forIn_cons, hl a (by simp)]
    exact ih (fun b hb => hl b (by simp [hb]))

/-- Exact outcome for a dimension-checked display buffer, including zero-size reads and
the precise limit error on excess. The budget may differ from the one used to decode. -/
def DisplayWithin (L : Limits) (n : Nat) (run : Except Error ByteArray) : Prop :=
  (n ≤ L.maxDecodedBytes → ∃ buf, run = .ok buf ∧ buf.size = n ∧
    (∀ i, (buf[i]?).isSome ↔ i < n) ∧ (∀ i, n ≤ i → (buf[i]?).getD 0 = 0)) ∧
  (L.maxDecodedBytes < n → run = .error (.limitExceeded Image.loc .decodedBytes n L.maxDecodedBytes))

/-- Both display kernels terminate with the exact size or refuse the checked byte count. -/
theorem interleave_resources {w h : Nat} {cs : Array Channel}
    (dims : ∀ c ∈ cs, c.plane.width = w ∧ c.plane.height = h)
    (L : Limits) (wide : Bool) (mode : Scaling) :
    DisplayWithin L (w*h*cs.size*(if wide then 2 else 1)) (interleave L w h cs wide mode) := by
  let n := w*h*cs.size*(if wide then 2 else 1)
  have run : (n ≤ L.maxDecodedBytes → ∃ buf, interleave L w h cs wide mode = .ok buf) ∧
      (L.maxDecodedBytes < n → interleave L w h cs wide mode =
        .error (.limitExceeded Image.loc .decodedBytes n L.maxDecodedBytes)) := by
    unfold interleave
    rw [unit_loop _ _ _ (by
      intro c hc
      obtain ⟨hw, hh⟩ := dims c hc
      simp [hw, hh, pure, Except.pure])]
    constructor
    · intro hn
      have ck : L.check Image.loc .decodedBytes n = .ok () := (Limits.check_eq_ok_iff ..).2 hn
      dsimp [n] at ck
      simp only [bind, Except.bind, ck]
      cases wide <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> split <;> exact ⟨_, rfl⟩
    · intro hn
      have ck : L.check Image.loc .decodedBytes n =
          .error (.limitExceeded Image.loc .decodedBytes n L.maxDecodedBytes) := by
        simp [Limits.check, Limits.checkLe, Limits.bound, Nat.not_le.mpr hn]
      dsimp [n] at ck
      simp only [bind, Except.bind, ck, n]
  refine ⟨fun hn => ?_, run.2⟩
  obtain ⟨buf, ok⟩ := run.1 hn
  have size := (Resources.interleave_size ok).1
  exact ⟨buf, ok, size, by intro i; simp [← size], by
    intro i hi
    rw [getElem?_neg buf i (by omega)]
    rfl⟩

/-- Exact outer fuel and per-pixel work list of the selected display kernel. The compact
kernel borrows each original four-byte plane. The native kernel retains the selected views. -/
def DisplayLoop (w h : Nat) (channels : Array Channel) (wide : Bool) (mode : Scaling)
    (buf : ByteArray) : Prop :=
  let cs := channels.toList.map fun c => (c.plane, Scaler.make mode c.depth c.signed (if wide then 16 else 8))
  let out := ByteArray.emptyWithCapacity (w*h*channels.size*(if wide then 2 else 1))
  if allCompact : cs.all (fun c => c.1.compact?.isSome) then
    let planes := cs.attach.map fun ⟨c,hc⟩ => (c.1.compact?.get (List.all_eq_true.mp allCompact c hc), c.2)
    planes.length = channels.size ∧
      buf = interleaveLoop (fun p s i => s.apply ((p.get? i).getD 0)) wide planes out 0 (w*h)
  else cs.length = channels.size ∧
    buf = interleaveLoop (fun p s i => s.applyNative ((p.get? i).getD 0)) wide cs out 0 (w*h)

/-- The actual successful interleaver uses image-area fuel even when there are zero
selected channels. Its inner loop has exactly one scaler per selected channel. -/
theorem interleave_loop {L w h channels wide mode buf}
    (ok : interleave L w h channels wide mode = .ok buf) : DisplayLoop w h channels wide mode buf := by
  unfold interleave at ok
  obtain ⟨_, _, ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨_, _, ok⟩ := Tier2Equiv.bind_ok ok
  unfold DisplayLoop
  cases wide <;> simp only [Bool.false_eq_true, ↓reduceIte] at ok ⊢
  all_goals split at ok <;> rename_i hc <;> simp only [hc, ↓reduceDIte] <;> cases ok <;> simp

end JPEG2000.Spec.ColorResources
