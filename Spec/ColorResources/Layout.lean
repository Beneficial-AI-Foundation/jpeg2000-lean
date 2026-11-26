import Spec.NativeResources
import Spec.ColorResources.ChannelSort

/-!
# Output channel-record counts (Plan.md §§3–5, 7, S3; T.800 I.5.3.6)

Dimension and byte checks alone do not bound channel selection or scaler preparation
when the image area is zero. These bounds come from the CDEF association checks.
-/

namespace JPEG2000.Spec.ColorResources

open JPEG2000 JPEG2000.Color JPEG2000.Box

private theorem map_runs {α β : Type} (f : α → Except Error β) (xs : List α) (ys : List β)
    (ok : xs.mapM f = .ok ys) : ys.length = xs.length ∧ ∀ a ∈ xs, ∃ b, f a = .ok b := by
  induction xs generalizing ys with
  | nil => cases ok; simp
  | cons a as ih =>
    rw [List.mapM_cons] at ok
    obtain ⟨b,hb,ok⟩ := Tier2Equiv.bind_ok ok
    obtain ⟨bs,hbs,ok⟩ := Tier2Equiv.bind_ok ok
    cases ok
    obtain ⟨len, all⟩ := ih _ hbs
    exact ⟨by simp [len], fun x hx => (List.mem_cons.mp hx).elim (fun e => e ▸ ⟨b,hb⟩) (all x)⟩

/-- The successful channel-array traversals perform one call for every input record. -/
theorem channel_map_size {α β : Type} {f : α → Except Error β} {xs : Array α} {ys : Array β}
    (ok : xs.mapM f = .ok ys) : ys.size = xs.size := by
  rw [Array.mapM_eq_mapM_toList] at ok
  cases hl : xs.toList.mapM f with
  | error e => rw [hl] at ok; cases ok
  | ok bs => rw [hl] at ok; cases ok; simpa using (map_runs _ _ _ hl).1

private theorem for_all {α : Type} (f : α → Unit → Except Error (ForInStep Unit))
    (P : α → Prop) (step : ∀ a s, f a () = .ok s → s = .yield () ∧ P a) :
    ∀ xs, forIn xs () f = .ok () → ∀ a ∈ (xs : List α), P a
  | [], _, _, h => by cases h
  | a :: as, ok, x, hx => by
    rw [List.forIn_cons] at ok
    obtain ⟨s,hs,ok⟩ := Tier2Equiv.bind_ok ok
    obtain ⟨rfl, ha⟩ := step a s hs
    exact (List.mem_cons.mp hx).elim (fun e => e ▸ ha) (for_all f P step as ok x)

private theorem valid_assoc {n : Nat} {ds : Array ChannelDef} (ok : checkCdef n ds = .ok ()) :
    ∀ d ∈ ds, d.asoc.toNat ≤ n ∨ d.asoc.toNat = 65535 := by
  unfold checkCdef at ok
  obtain ⟨u,loop,_⟩ := Tier2Equiv.bind_ok ok
  cases u
  rw [← Array.forIn_toList] at loop
  intro d hd
  apply for_all _ _ _ ds.toList loop d (Array.mem_def.mp hd)
  intro a s h
  dsimp only at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  rename_i good
  cases h
  refine ⟨rfl, ?_⟩
  by_cases zero : a.asoc = 0
  · simp [zero]
  by_cases max : a.asoc = 65535
  · simp [max]
  simp [zero, max] at good
  omega

private theorem colour_assoc {n k i : Nat} {ds : Array ChannelDef}
    (valid : checkCdef n ds = .ok ()) (ok : colourChannel ds k = .ok i) :
    k ≤ n ∨ k = 65535 := by
  unfold colourChannel at ok
  split at ok <;> try contradiction
  rename_i d hd
  have mem : d ∈ ds.filter (fun a => a.typ == 0 && a.asoc.toNat == k) :=
    Array.mem_def.mpr (hd ▸ (by simp))
  obtain ⟨h, hk⟩ := Array.mem_filter.mp mem
  simp only [Bool.and_eq_true, beq_iff_eq] at hk
  exact hk.2 ▸ valid_assoc valid d h

private theorem range_count {n m : Nat} {ds : Array ChannelDef} {cs : Array Nat}
    (valid : checkCdef n ds = .ok ())
    (map : (List.range m).toArray.mapM (fun k => colourChannel ds (k+1)) = .ok cs) :
    cs.size ≤ n+1 := by
  rw [Array.mapM_eq_mapM_toList] at map
  cases hh : (List.range m).mapM (fun k => colourChannel ds (k+1)) with
  | error e => rw [hh] at map; cases map
  | ok vals =>
    rw [hh] at map; cases map
    obtain ⟨len, run⟩ := map_runs _ _ _ hh
    have bound (k : Nat) (hk : k < m) : k+1 ≤ n ∨ k+1 = 65535 := by
      obtain ⟨v, hv⟩ := run _ (List.mem_range.mpr hk)
      exact colour_assoc valid hv
    change vals.toArray.size ≤ n+1
    simp [len]
    by_cases above : n+1 < m
    · have h1 := bound n (by omega)
      have h2 := bound (n+1) (by omega)
      omega
    · omega

private theorem layout_count {n : Nat} {nc : Option Nat} {defs : Option (Array ChannelDef)}
    {layout : ChannelLayout} (ok : channelLayout nc n defs = .ok layout) :
    layout.colours.size ≤ n+1 ∧ layout.other.size ≤ n := by
  cases defs with
  | none =>
    cases ok
    simp; omega
  | some ds =>
    obtain ⟨_, valid, ok⟩ := Tier2Equiv.bind_ok ok
    obtain ⟨cs, map, ok⟩ := Tier2Equiv.bind_ok ok
    cases ok
    exact ⟨range_count valid map, Nat.le_trans Array.size_filter_le (by simp)⟩

/-- Size of the colour and other index arrays from the actual resolved JP2 layout. -/
theorem resolved_layout_size {L data hdr comps info} (ok : resolve L data hdr comps = .ok info) :
    info.layout.colours.size ≤ info.mapping.sources.size+1 ∧
      info.layout.other.size ≤ info.mapping.sources.size := by
  unfold resolve at ok
  cases hdr <;> simp only at ok
  all_goals
    obtain ⟨_, _, ok⟩ := Tier2Equiv.bind_ok ok
    obtain ⟨⟨_,_,_⟩, _, ok⟩ := Tier2Equiv.bind_ok ok
    obtain ⟨layout, hl, ok⟩ := Tier2Equiv.bind_ok ok
    cases ok
    exact layout_count hl


private def opacity (d : ChannelDef) := (d.typ == 1 || d.typ == 2) && d.asoc == 0

private def firstMatch {α : Type} (pred : α → Bool) : List α → Option α × Nat
  | [] => (none,0)
  | x::xs => if pred x then (some x,1) else
    let tail := firstMatch pred xs
    (tail.1,tail.2+1)

private theorem firstMatch_work {α : Type} (pred : α → Bool) (xs : List α) :
    (firstMatch pred xs).1 = xs.find? pred ∧ (firstMatch pred xs).2 ≤ xs.length := by
  induction xs with
  | nil => exact ⟨rfl,Nat.zero_le _⟩
  | cons x xs ih =>
    simp only [firstMatch,List.find?_cons,List.length_cons]
    cases pred x with
    | true => exact ⟨rfl,by simp⟩
    | false => exact ⟨ih.1,Nat.succ_le_succ ih.2⟩

/-- Sort CDEF records by channel index and scan through the first opacity
record. Count comparator calls and evaluated opacity predicates. -/
def measuredAlpha (defs : Array ChannelDef) : Option ChannelDef × Nat :=
  let sorted := channelSort (fun a b => a.cn < b.cn) defs
  let found := firstMatch opacity sorted.1.toList
  (found.1,sorted.2+found.2)

/-- The JP2 alpha selector retains exactly the sorted search result, including
its premultiplication flag. With `d` CDEF records it costs at most
`(d-1)*(d+3) + d` comparisons and predicate calls. -/
theorem alpha_work (defs : Array ChannelDef) :
    let r := measuredAlpha defs
    r.1 = (defs.qsort (fun a b => a.cn < b.cn)).find?
      (fun d => (d.typ == 1 || d.typ == 2) && d.asoc == 0) ∧
      r.2 ≤ (defs.size-1)*(defs.size+3)+defs.size := by
  let lt := fun a b : ChannelDef => decide (a.cn < b.cn)
  obtain ⟨sort,size,cap⟩ := channelSort_work lt defs
  obtain ⟨found,visits⟩ := firstMatch_work opacity (channelSort lt defs).1.toList
  change (firstMatch opacity _).1 = (defs.qsort lt).find? opacity ∧ (channelSort lt defs).2 + _ ≤ _
  exact ⟨found.trans (by rw [Array.find?_toList,sort]),
    Nat.add_le_add cap (by simpa only [Array.length_toList,size] using visits)⟩

end JPEG2000.Spec.ColorResources
