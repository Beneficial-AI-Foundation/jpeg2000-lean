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


private def validateOne (n : Nat) (d : ChannelDef) (_ : Unit) : Except Error (ForInStep Unit) := do
  if d.cn.toNat ≥ n then throw (malformed s!"cdef: channel {d.cn} ≥ {n} channels")
  if d.asoc != 0 && d.asoc != 65535 && d.asoc.toNat - 1 ≥ n then
    throw (malformed s!"cdef: association {d.asoc} > {n} channels")
  return .yield ()

private def validateDefs (n : Nat) : List ChannelDef → Except Error Unit × Nat
  | [] => (.ok (),0)
  | d::ds => match validateOne n d () with
    | .error e => (.error e,1)
    | .ok (.done _) => (.ok (),1)
    | .ok (.yield _) =>
      let tail := validateDefs n ds
      (tail.1,1+tail.2)

private theorem validateDefs_work (n : Nat) (ds : List ChannelDef) :
    (validateDefs n ds).1 = forIn ds () (validateOne n) ∧ (validateDefs n ds).2 ≤ ds.length := by
  induction ds with
  | nil => exact ⟨rfl,Nat.zero_le _⟩
  | cons d ds ih =>
    rw [validateDefs,List.forIn_cons]
    cases validateOne n d () with
    | error => exact ⟨rfl,by simp⟩
    | ok step =>
      cases step with
      | done => exact ⟨rfl,by simp⟩
      | yield => exact ⟨ih.1,by simp only [List.length_cons]; omega⟩

private def markSeen (xs : Array Nat) (d : ChannelDef) :=
  xs.setIfInBounds d.cn.toNat (xs.getD d.cn.toNat 0 + 1)

private theorem marks_size (ds : List ChannelDef) (xs : Array Nat) :
    (ds.foldl markSeen xs).size = xs.size := by
  induction ds generalizing xs with
  | nil => rfl
  | cons d ds ih => exact (ih _).trans (Array.size_setIfInBounds ..)

/-- Meter the initial reference check up to the first error. Once it passes,
charge one slot per initial count, a read and update per definition, and each
tested count through the first missing or duplicated channel. -/
def measuredCdef (n : Nat) (ds : Array ChannelDef) : Except Error Unit × Nat :=
  let refs := validateDefs n ds.toList
  match refs.1 with
  | .error e => (.error e,refs.2)
  | .ok () =>
    let seen := ds.foldl markSeen (Array.replicate n 0)
    let bad := firstMatch (· != 1) seen.toList
    let result := if bad.1.isSome then .error (malformed "cdef: channels not each defined exactly once")
                  else .ok ()
    (result,refs.2+n+2*ds.size+bad.2)

/-- Checking `d` CDEF records against `n` channels costs at most `3*d+2*n`
record visits and count-slot operations. Both failure stages preserve the exact error. -/
theorem cdef_work (n : Nat) (ds : Array ChannelDef) :
    (measuredCdef n ds).1 = checkCdef n ds ∧ (measuredCdef n ds).2 ≤ 3*ds.size+2*n := by
  obtain ⟨value,visits⟩ := validateDefs_work n ds.toList
  simp only [Array.forIn_toList,Array.length_toList] at value visits
  let seen := ds.foldl markSeen (Array.replicate n 0)
  have size : seen.size = n := by
    unfold seen
    rw [← Array.foldl_toList,marks_size,Array.size_replicate]
  obtain ⟨find,checked⟩ := firstMatch_work (· != 1) seen.toList
  have found : (firstMatch (· != 1) seen.toList).1.isSome = seen.any (· != 1) := by
    rw [find,List.isSome_find?,Array.any_toList]
  simp only [Array.length_toList,size] at checked
  unfold measuredCdef checkCdef
  change _ = (forIn ds () (validateOne n) >>= fun _ =>
    if seen.any (· != 1) then .error (malformed "cdef: channels not each defined exactly once") else .ok ()) ∧ _
  rw [← value]
  dsimp only
  cases (validateDefs n ds.toList).1 with
  | error => exact ⟨rfl,by dsimp only; omega⟩
  | ok u =>
    cases u
    refine ⟨?_,?_⟩
    · dsimp only
      rw [found]
      rfl
    · change _+n+2*ds.size+(firstMatch (· != 1) seen.toList).2 ≤ _
      omega

/-- Charge the full CDEF filter and its two materialisations when looking up a
colour association. The original selector distinguishes absent and ambiguous keys. -/
def measuredChannel (ds : Array ChannelDef) (k : Nat) : Except Error Nat × Nat :=
  let hits := ds.filter fun d => d.typ == 0 && d.asoc.toNat == k
  let result := match hits.toList with
    | [d] => .ok d.cn.toNat
    | [] => .error (malformed s!"cdef: no channel for colour {k}")
    | _ => .error (malformed s!"cdef: several channels for colour {k}")
  (result,ds.size+2*hits.size)

private theorem channel_cost (ds : Array ChannelDef) (k : Nat) :
    (measuredChannel ds k).1 = colourChannel ds k ∧ (measuredChannel ds k).2 ≤ 3*ds.size := by
  refine ⟨rfl,?_⟩
  have := @Array.size_filter_le _ (fun d : ChannelDef => d.typ == 0 && d.asoc.toNat == k) ds
  dsimp only [measuredChannel]
  omega


private def assocList (ds : Array ChannelDef) : List Nat → Except Error (List Nat) × Nat
  | [] => (.ok [],0)
  | k::ks =>
    let one := measuredChannel ds (k+1)
    match one.1 with
    | .error e => (.error e,1+one.2)
    | .ok value =>
      let rest := assocList ds ks
      (rest.1.map (value :: ·),1+one.2+rest.2)

private theorem assocList_work (ds : Array ChannelDef) (ks : List Nat) :
    (assocList ds ks).1 = ks.mapM (fun k => colourChannel ds (k+1)) ∧
    (assocList ds ks).2 ≤ ks.length*(1+3*ds.size) := by
  induction ks with
  | nil => exact ⟨rfl,Nat.zero_le _⟩
  | cons k ks ih =>
    obtain ⟨value,cost⟩ := channel_cost ds (k+1)
    rw [assocList,List.mapM_cons,← value]
    dsimp only
    cases (measuredChannel ds (k+1)).1 with
    | error e => exact ⟨rfl,by simp only [List.length_cons,Nat.succ_mul]; omega⟩
    | ok v =>
      constructor
      · dsimp only
        rw [ih.1]
        cases ks.mapM (fun k => colourChannel ds (k+1)) <;> rfl
      · change 1+(measuredChannel ds (k+1)).2+(assocList ds ks).2 ≤ (ks.length+1)*(1+3*ds.size)
        rw [Nat.add_mul,Nat.one_mul]
        omega

/-- Look up successive colour associations, including the full reserved
range and the lookup that returns a missing or ambiguous association. -/
def measuredAssociations (ds : Array ChannelDef) (m : Nat) : Except Error (Array Nat) × Nat :=
  let run := assocList ds (List.range m)
  (run.1.map List.toArray,2*m+run.2)

/-- Each attempted colour lookup inspects all definitions. A failure returns
the same association error and stops before later lookups and opacity sorting. -/
theorem associations_work (ds : Array ChannelDef) (m : Nat) :
    (measuredAssociations ds m).1 = (List.range m).toArray.mapM (fun k => colourChannel ds (k+1)) ∧
    (measuredAssociations ds m).2 ≤ 2*m+m*(1+3*ds.size) := by
  obtain ⟨out,cap⟩ := assocList_work ds (List.range m)
  simp only [List.length_range] at cap
  unfold measuredAssociations
  constructor
  · simp only [out,Array.mapM_eq_mapM_toList]
    cases (List.range m).mapM (fun k => colourChannel ds (k+1)) <;> rfl
  · exact Nat.add_le_add_left cap _

private def remaining (cs : Array Nat) (alpha : Option Nat) : List Nat → List Nat × Nat
  | [] => ([],0)
  | i::is =>
    let found := firstMatch (i == ·) cs.toList
    let rest := remaining cs alpha is
    (if !found.1.isSome && alpha != some i then i::rest.1 else rest.1,1+found.2+rest.2)

private theorem remaining_work (cs : Array Nat) (a : Option Nat) (is : List Nat) :
    (remaining cs a is).1 = is.filter (fun i => !cs.contains i && a != some i) ∧
    (remaining cs a is).2 ≤ is.length*(1+cs.size) := by
  induction is with
  | nil => exact ⟨rfl,Nat.zero_le _⟩
  | cons i is ih =>
    obtain ⟨out,cost⟩ := firstMatch_work (i == ·) cs.toList
    have eq : (firstMatch (i == ·) cs.toList).1.isSome = cs.contains i := by
      rw [out,List.isSome_find?,Array.any_toList,Array.contains_eq_any_beq]
    simp only [Array.length_toList] at cost
    simp only [remaining,eq,ih.1,List.filter_cons,List.length_cons,Nat.succ_mul]
    exact ⟨trivial,by omega⟩


private def colourCount (nc : Option Nat) (ds : Array ChannelDef) : Nat × Nat :=
  match nc with
  | some k => (k,0)
  | none =>
    let named := ds.filter fun d => d.typ == 0 && d.asoc != 0 && d.asoc != 65535
    (named.size,ds.size+named.size)

private theorem count_work (nc : Option Nat) (ds : Array ChannelDef) :
    (colourCount nc ds).1 ≤ nc.getD ds.size ∧ (colourCount nc ds).2 ≤ 2*ds.size := by
  cases nc with
  | some k => exact ⟨Nat.le_refl _,Nat.zero_le _⟩
  | none =>
    have h := @Array.size_filter_le _ (fun d : ChannelDef => d.typ == 0 && d.asoc != 0 && d.asoc != 65535) ds
    exact ⟨h,by dsimp only [colourCount]; omega⟩

private def finishLayout (ds : Array ChannelDef) (n : Nat) (cs : Array Nat) :
    ChannelLayout × Nat :=
  let alpha := measuredAlpha ds
  let index := alpha.1.map (·.cn.toNat)
  let other := remaining cs index (List.range n)
  (⟨cs,index,alpha.1.any (·.typ == 2),other.1.toArray⟩,alpha.2+3*n+other.2)

private theorem finish_work (ds : Array ChannelDef) (n : Nat) (cs : Array Nat) :
    let alpha := (ds.qsort (fun a b => a.cn < b.cn)).find? opacity
    let index := alpha.map (·.cn.toNat)
    let other := (List.range n).toArray.filter fun i => !cs.contains i && index != some i
    let f := finishLayout ds n cs
    f.1 = ⟨cs,index,alpha.any (·.typ == 2),other⟩ ∧
    f.2 ≤ (ds.size-1)*(ds.size+3)+ds.size+3*n+n*(1+cs.size) := by
  obtain ⟨alpha,price⟩ := alpha_work ds
  let index := (measuredAlpha ds).1.map (·.cn.toNat)
  obtain ⟨vals,checks⟩ := remaining_work cs index (List.range n)
  simp only [List.length_range] at checks
  have arr : (remaining cs index (List.range n)).1.toArray =
      (List.range n).toArray.filter (fun i => !cs.contains i && index != some i) := by
    apply Array.toList_inj.mp
    simp only [Array.toList_filter,vals]
  unfold finishLayout
  constructor
  · dsimp only
    change (measuredAlpha ds).1 = (ds.qsort (fun a b => a.cn < b.cn)).find? opacity at alpha
    rw [arr, ← alpha]
  · exact Nat.add_le_add (Nat.add_le_add_right price _) checks

/-- Count validation, association lookups, sorted alpha selection and the
remaining-channel filter at their actual entry points, stopping at the first
layout error. Range creation and conversion count by index slots. -/
def measuredLayout (nc : Option Nat) (n : Nat) (cdef : Option (Array ChannelDef)) :
    Except Error ChannelLayout × Nat :=
  match cdef with
  | none =>
    let k := min (nc.getD n) n
    (.ok { colours := (List.range k).toArray, other := ((List.range n).drop k).toArray },2*k+3*n)
  | some ds =>
    let validation := measuredCdef n ds
    match validation.1 with
    | .error e => (.error e,validation.2)
    | .ok () =>
      let count := colourCount nc ds
      let cs := measuredAssociations ds count.1
      let spent := validation.2+count.2+cs.2
      match cs.1 with
      | .error e => (.error e,spent)
      | .ok a =>
        let tail := finishLayout ds n a
        (.ok tail.1,spent+tail.2)

/-- Layout charge in terms of the channel count `n`, the CDEF record count `d`
and the upper bound `m` on associations requested from those records. -/
def layoutBudget (n d m : Nat) :=
  5*n + 5*d + 2*m + m*(1+3*d) + (d-1)*(d+3) + d + n*(1+m)

/-- The complete channel-layout meter preserves the original result and first
error, including rejection before sorting. Its work and temporary index
materialisations have a numeric bound even when the image has no samples. -/
theorem layout_work (nc : Option Nat) (n : Nat) (cdef : Option (Array ChannelDef)) :
    let d := (cdef.getD #[]).size
    let m := nc.getD d
    let r := measuredLayout nc n cdef
    r.1 = channelLayout nc n cdef ∧ r.2 ≤ layoutBudget n d m := by
  cases cdef with
  | none =>
    refine ⟨rfl,?_⟩
    change 2 * min (nc.getD n) n + 3*n ≤ layoutBudget n 0 (nc.getD 0)
    unfold layoutBudget
    omega
  | some ds =>
    obtain ⟨val,vc⟩ := cdef_work n ds
    obtain ⟨lim,cc⟩ := count_work nc ds
    let count := colourCount nc ds
    obtain ⟨found,fc⟩ := associations_work ds count.1
    let m := nc.getD ds.size
    have mc : count.1 ≤ m := lim
    have search := Nat.mul_le_mul_right (1+3*ds.size) mc
    have original : channelLayout nc n (some ds) = (do
        checkCdef n ds
        let cs ← (List.range count.1).toArray.mapM (fun k => colourChannel ds (k+1))
        let alpha := (ds.qsort (fun a b => a.cn < b.cn)).find? opacity
        let index := alpha.map (·.cn.toNat)
        let other := (List.range n).toArray.filter fun i => !cs.contains i && index != some i
        pure ⟨cs,index,alpha.any (·.typ == 2),other⟩) := by cases nc <;> rfl
    rw [original,← val,← found]
    unfold measuredLayout
    dsimp only
    cases hv : (measuredCdef n ds).1 with
    | error e => exact ⟨rfl,by change (measuredCdef n ds).2 ≤ layoutBudget n ds.size m; unfold layoutBudget; omega⟩
    | ok u =>
      cases u
      simp only [bind,Except.bind,count]
      cases ha : (measuredAssociations ds (colourCount nc ds).1).1 with
      | error e =>
        refine ⟨rfl,?_⟩
        change (measuredCdef n ds).2+count.2+(measuredAssociations ds count.1).2 ≤ layoutBudget n ds.size m
        unfold layoutBudget
        change count.2 ≤ 2*ds.size at cc
        omega
      | ok cs =>
        have success := ha
        rw [found] at success
        have size : cs.size = count.1 := by simpa using channel_map_size success
        obtain ⟨tail,tc⟩ := finish_work ds n cs
        have other := Nat.mul_le_mul_left n (Nat.add_le_add_left (size ▸ mc : cs.size ≤ m) 1)
        refine ⟨congrArg Except.ok tail,?_⟩
        change (measuredCdef n ds).2+count.2+(measuredAssociations ds count.1).2+(finishLayout ds n cs).2 ≤ layoutBudget n ds.size m
        unfold layoutBudget
        change count.2 ≤ 2*ds.size at cc
        omega

end JPEG2000.Spec.ColorResources
