import Spec.RoundTrip.Layout

/-!
# Admission of the encoder's precinct geometry

Plan.md §§4 (C10, S3), 5.3 and 7 (M7), task 7.3f5c. T.800 B.5–B.7 and B.10.2.
The decoder checks precinct and code-block counts as it traverses the tile in raster
order. Each of the two fresh tag trees in a precinct-band fits the block budget.
-/

namespace JPEG2000.Spec.RoundTrip

open JPEG2000.Header JPEG2000.Progression JPEG2000.Tier2.Geometry
open JPEG2000.Tier2.Packet (PrecState initPrecincts)

private theorem tree_nodes (fuel w h : Nat) :
    JPEG2000.TagTree.totalAux (JPEG2000.TagTree.levelsAux fuel w h) w h ≤ 3 * (w * h) := by
  induction fuel generalizing w h with
  | zero => simp [JPEG2000.TagTree.levelsAux, JPEG2000.TagTree.totalAux]; omega
  | succ n ih =>
    simp only [JPEG2000.TagTree.levelsAux]
    split
    · simp [JPEG2000.TagTree.totalAux]; omega
    · rename_i hlarge
      let x := (w + 1) / 2
      let y := (h + 1) / 2
      have hxy : 3 * (x * y) ≤ 2 * (w * h) := by
        by_cases hw : 1 < w
        · have a : 3*x ≤ 2*w := by dsimp [x]; omega
          have b : y ≤ h := by dsimp [y]; omega
          simpa only [Nat.mul_assoc] using Nat.mul_le_mul a b
        · have a : x ≤ w := by dsimp [x]; omega
          have b : 3*y ≤ 2*h := by dsimp [y]; omega
          simpa only [Nat.mul_left_comm] using Nat.mul_le_mul a b
      have ht := ih x y
      change w * h + JPEG2000.TagTree.totalAux (JPEG2000.TagTree.levelsAux n x y) x y ≤ _
      omega

/-- Both tag-tree allocation checks follow from the leaf count, even for empty or narrow
grids. The levels together contain at most three nodes per leaf. -/
theorem tagTree_create_of_le {L : Limits} {w h : Nat} (hle : w * h ≤ L.maxCodeBlocks) :
    ∃ t, JPEG2000.TagTree.create L w h = .ok t := by
  have hn := tree_nodes (w + h) w h
  have ht : JPEG2000.TagTree.totalAux (JPEG2000.TagTree.levels w h) w h ≤ 4 * L.maxCodeBlocks :=
    by unfold JPEG2000.TagTree.levels; omega
  unfold JPEG2000.TagTree.create
  dsimp only
  rw [(Limits.check_eq_ok_iff ..).2 hle, (Limits.checkLe_eq_ok_iff ..).2 ht]
  exact ⟨_, rfl⟩

private def sumTo (f : Nat → Nat) (n : Nat) : Nat :=
  ((List.range n).map f).sum

private theorem sumTo_succ (f : Nat → Nat) (n : Nat) :
    sumTo f (n+1) = sumTo f n + f n := by simp [sumTo, List.range_succ]

private theorem sumTo_mono (f : Nat → Nat) {i j : Nat} (h : i ≤ j) : sumTo f i ≤ sumTo f j := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => rw [sumTo_succ]; omega

private theorem range_ok {β : Type} (P : Nat → β → Prop) {n : Nat} {b : β}
    {f : Nat → β → Except Error (ForInStep β)} (hb : P 0 b)
    (hs : ∀ i < n, ∀ a, P i a → ∃ a', f i a = .ok (.yield a') ∧ P (i+1) a') :
    ∃ v, forIn [0:n] b f = .ok v ∧ P n v := by
  have go (m : Nat) : ∀ i a, i+m ≤ n → P i a →
      ∃ v, forIn (List.range' i m) a f = .ok v ∧ P (i+m) v := by
    induction m with
    | zero => intro i a _ ha; exact ⟨a, rfl, ha⟩
    | succ m ih =>
      intro i a hi ha
      obtain ⟨a', hf, ha'⟩ := hs i (by omega) a ha
      obtain ⟨v, hv, hp⟩ := ih (i+1) a' (by omega) ha'
      rw [List.range'_succ, List.forIn_cons, hf]
      exact ⟨v, hv, by rwa [show i+(m+1) = i+1+m by omega]⟩
  simpa [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size] using go n 0 b (by simp) hb

private theorem array_map_ok {α β : Type} (xs : Array α) (f : α → Except Error β) (g : α → β)
    (hf : ∀ x ∈ xs, f x = .ok (g x)) : xs.mapM f = .ok (xs.map g) := by
  have aux (l : List α) (hl : ∀ x ∈ l, f x = .ok (g x)) : l.mapM f = .ok (l.map g) := by
    induction l with
    | nil => rfl
    | cons a l ih =>
      simp [List.mapM_cons, hl a (by simp), ih (fun x hx => hl x (by simp [hx])),
        bind, Except.bind, pure, Except.pure]
  rw [Array.mapM_eq_mapM_toList, aux xs.toList (fun x hx => hf x (Array.mem_def.mpr hx))]
  simp only [Functor.map, Except.map, ← Array.toList_map, Array.toArray_toList]

private theorem band_checks {L : Limits} (bs : Array BandGeom)
    (h : ∀ b ∈ bs, b.numCodeBlocks ≤ L.maxCodeBlocks) :
    (forIn bs PUnit.unit (fun (b : BandGeom) _ => do
      L.check JPEG2000.Tier2.Geometry.loc .codeBlocks b.numCodeBlocks
      pure (.yield PUnit.unit))) = .ok PUnit.unit := by
  rw [← Array.forIn_toList]
  generalize hl : bs.toList = xs
  have h' : ∀ x ∈ xs, x.numCodeBlocks ≤ L.maxCodeBlocks := fun x hx =>
    h x (Array.mem_def.mpr (hl ▸ hx))
  clear hl h
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.forIn_cons, (Limits.check_eq_ok_iff ..).2 (h' x (by simp))]
    exact ih (fun y hy => h' y (by simp [hy]))

private def summary (tc : TileCompGeom) (r : Nat) : ResolutionGeom :=
  let rect := resRect tc.rect tc.params.levels r
  let pp := tc.params.precincts.getD r Marker.Precinct.default
  let x := pp.ppx.toNat
  let y := pp.ppy.toNat
  { tc, r, rect, ppx := x, ppy := y, bandPpx := if r = 0 then x else x-1,
    bandPpy := if r = 0 then y else y-1, k0x := rect.x0 / 2^x, k0y := rect.y0 / 2^y,
    pw := gridCount rect.x0 rect.x1 x, ph := gridCount rect.y0 rect.y1 y,
    bands := (bandsOf r).map (bandGeom tc r) }

private theorem resolution_ok {L : Limits} {tc : TileCompGeom} {r : Nat}
    (hr : r ≤ tc.params.levels) (hn : (summary tc r).numPrecincts ≤ L.maxPrecincts)
    (hb : ∀ b ∈ (summary tc r).bands, b.numCodeBlocks ≤ L.maxCodeBlocks) :
    resolution L tc r = .ok (summary tc r) := by
  unfold resolution
  dsimp only
  rw [ite_eq_right (by omega : ¬ r > tc.params.levels), (Limits.check_eq_ok_iff ..).2 hn]
  change (forIn (summary tc r).bands PUnit.unit (fun (b : BandGeom) _ => do
    L.check JPEG2000.Tier2.Geometry.loc .codeBlocks b.numCodeBlocks
    pure (.yield PUnit.unit)) >>= fun _ => pure (summary tc r)) = _
  rw [band_checks _ hb]
  rfl


private def grid (res : ResolutionGeom) (k : Nat) (b : BandGeom) : Nat × Nat :=
  let pb := precinctBandRect res b (k % res.pw) (k / res.pw)
  let w := gridCount pb.x0 pb.x1 b.cbWidthExp
  let h := gridCount pb.y0 pb.y1 b.cbHeightExp
  if w = 0 ∨ h = 0 then (0, 0) else (w, h)

private def leaves (res : ResolutionGeom) (k : Nat) (b : BandGeom) : Nat :=
  (grid res k b).1 * (grid res k b).2

private def blocksAt (res : ResolutionGeom) (k : Nat) : Nat :=
  (res.bands.toList.map (leaves res k)).sum

private theorem member_le_sum {l : List Nat} {a : Nat} (h : a ∈ l) : a ≤ l.sum := by
  induction l with
  | nil => cases h
  | cons x l ih =>
    simp only [List.sum_cons, List.mem_cons] at *
    rcases h with rfl | h
    · exact Nat.le_add_right ..
    · exact Nat.le_trans (ih h) (Nat.le_add_left ..)

private theorem leaves_le {res : ResolutionGeom} {k : Nat} {b : BandGeom} (hb : b ∈ res.bands) :
    leaves res k b ≤ blocksAt res k :=
  member_le_sum (List.mem_map.mpr ⟨b, Array.mem_def.mp hb, rfl⟩)

private def precinctBand (res : ResolutionGeom) (k : Nat) (b : BandGeom) : PrecinctBandGeom :=
  let rect := precinctBandRect res b (k % res.pw) (k / res.pw)
  let wh := grid res k b
  { band := b.band, rect, cw := wh.1, ch := wh.2,
    codeBlocks := codeBlocksOf rect b.cbWidthExp b.cbHeightExp wh.1 wh.2 }

private theorem fold_count {α : Type} (xs : List α) (f : α → Nat) (a : Nat) :
    xs.foldl (fun a x => a + f x) a = a + (xs.map f).sum := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.add_assoc]

private theorem array_map_pure {α β γ : Type} (xs : Array α) (f : α → Except Error β) (g : Array β → γ)
    (hf : ∀ x ∈ xs, ∃ y, f x = .ok y) :
    ∃ v, (xs.mapM f >>= fun ys => pure (g ys)) = .ok v := by
  have aux (l : List α) (hl : ∀ x ∈ l, ∃ y, f x = .ok y) : ∃ ys, l.mapM f = .ok ys := by
    induction l with
    | nil => exact ⟨[], rfl⟩
    | cons x l ih =>
      obtain ⟨y, hy⟩ := hl x (by simp)
      obtain ⟨ys, hys⟩ := ih (fun z hz => hl z (by simp [hz]))
      rw [List.mapM_cons, hy, hys]
      exact ⟨_, rfl⟩
  obtain ⟨ys, hys⟩ := aux xs.toList (fun x hx => hf x (Array.mem_def.mpr hx))
  rw [Array.mapM_eq_mapM_toList, hys]
  exact ⟨_, rfl⟩

private theorem state_ok {L : Limits} (params : CompParams) (r : Nat) (pg : PrecinctGeom)
    (hb : ∀ b ∈ pg.bands, b.cw * b.ch ≤ L.maxCodeBlocks) :
    ∃ st, PrecState.init L params r pg = .ok st := by
  unfold PrecState.init
  apply array_map_pure
  intro pb h
  obtain ⟨tree, ht⟩ := tagTree_create_of_le (hb pb h)
  dsimp only
  rw [ht]
  exact ⟨_, rfl⟩

private theorem precinct_ok {L : Limits} (res : ResolutionGeom) (k : Nat) (hk : k < res.numPrecincts)
    (hn : blocksAt res k ≤ L.maxCodeBlocks) :
    ∃ pg, precinct L res k = .ok pg ∧
      pg.bands.foldl (fun a b => a + b.codeBlocks.size) 0 = blocksAt res k ∧
      ∀ b ∈ pg.bands, b.cw * b.ch ≤ L.maxCodeBlocks := by
  unfold precinct
  dsimp only
  rw [ite_eq_right (by omega : ¬ k ≥ res.numPrecincts), array_map_ok _ _ (precinctBand res k)]
  · refine ⟨_, rfl, ?_, ?_⟩
    · dsimp only
      rw [← Array.foldl_toList, fold_count]
      simp [precinctBand, codeBlocksOf, blocksAt, List.map_map, Function.comp_def]
      rfl
    · intro b hb
      obtain ⟨b', hb', rfl⟩ := Array.mem_map.mp hb
      exact Nat.le_trans (leaves_le hb') hn
  · intro b hb
    have he := (Limits.check_eq_ok_iff L JPEG2000.Tier2.Geometry.loc .codeBlocks (leaves res k b)).2
      (Nat.le_trans (leaves_le hb) hn)
    simp only [leaves, grid] at he
    split at he <;> simp_all only [precinctBand, grid, ite_true, ite_false, bind, Except.bind,
      pure, Except.pure]

private theorem range_bind {β γ δ : Type} (P : Nat → β → Prop) {n : Nat} {b : β}
    {f : Nat → β → Except Error (ForInStep β)} {cont : β → Except Error δ}
    {result : γ → δ} {Q : γ → Prop}
    (hb : P 0 b)
    (hs : ∀ i < n, ∀ a, P i a → ∃ a', f i a = .ok (.yield a') ∧ P (i+1) a')
    (hc : ∀ b', P n b' → ∃ v, cont b' = .ok (result v) ∧ Q v) :
    ∃ v, (forIn [0:n] b f >>= cont) = .ok (result v) ∧ Q v := by
  obtain ⟨b', he, hp⟩ := range_ok P hb hs
  rw [he]
  exact hc _ hp

private def blockTotal (tc : TileCompGeom) (r : Nat) : Nat :=
  let res := summary tc r
  sumTo (blocksAt res) res.numPrecincts

private theorem prefix_budget (f : Nat → Nat) {c C i n : Nat} (hc : c < C) (hi : i ≤ n) :
    c * sumTo f n + sumTo f i ≤ C * sumTo f n := by
  have h := Nat.mul_le_mul_right (sumTo f n) (Nat.succ_le_of_lt hc)
  rw [Nat.succ_mul] at h
  exact Nat.le_trans (Nat.add_le_add_left (sumTo_mono _ hi) _) h

private theorem init_uniform {L : Limits} (g : Layout) (tc : TileCompGeom)
    (hcomp : ∀ c < g.numComps, g.comp c = tc)
    (hp : g.numComps * sumTo (fun r => (summary tc r).numPrecincts) (tc.params.levels+1) ≤ L.maxPrecincts)
    (hb : g.numComps * sumTo (blockTotal tc) (tc.params.levels+1) ≤ L.maxCodeBlocks)
    (hband : ∀ c < g.numComps, ∀ r ≤ tc.params.levels, ∀ b ∈ (summary tc r).bands, b.numCodeBlocks ≤ L.maxCodeBlocks) :
    ∃ precs base spans, initPrecincts L g = .ok (precs, base, spans) := by
  let n := tc.params.levels+1
  let ps := fun r => (summary tc r).numPrecincts
  let bs := blockTotal tc
  let pc := sumTo ps n
  let bc := sumTo bs n
  suffices h : ∃ v, initPrecincts L g = .ok v ∧ True by
    obtain ⟨⟨precs, base, spans⟩, he, _⟩ := h
    exact ⟨precs, base, spans, he⟩
  unfold initPrecincts
  dsimp only
  apply range_bind (result := id) (fun c (s : Array PrecState × Array (Array Nat) ×
      Array (Array (Nat × Nat)) × Nat) => s.1.size = c*pc ∧ s.2.2.2 = c*bc)
  · simp
  · intro c hc s hs
    rw [hcomp c hc]
    apply range_bind (fun r (t : Array PrecState × Nat × Array Nat × Array (Nat × Nat)) =>
      t.1.size = c*pc + sumTo ps r ∧ t.2.1 = c*bc + sumTo bs r)
    · exact ⟨by simpa [sumTo] using hs.1, by simpa [sumTo] using hs.2⟩
    · intro r hr t ht
      let res := summary tc r
      have hpr := Nat.le_trans (prefix_budget ps hc hr) hp
      have hbr := Nat.le_trans (prefix_budget bs hc hr) hb
      change c*pc + sumTo ps (r+1) ≤ _ at hpr
      change c*bc + sumTo bs (r+1) ≤ _ at hbr
      rw [sumTo_succ] at hpr hbr
      have hp' : t.1.size + res.numPrecincts ≤ L.maxPrecincts := by
        change t.1.size + ps r ≤ _; omega
      have hres := resolution_ok (L := L) (tc := tc) (r := r) (by omega)
        (Nat.le_trans (Nat.le_add_left ..) hp') (hband c hc r (by omega))
      rw [hres]
      dsimp only [bind, Except.bind]
      rw [(Limits.check_eq_ok_iff ..).2 hp']
      dsimp only [bind, Except.bind]
      apply range_bind (fun k (a : Array PrecState × Nat) =>
        a.1.size = t.1.size + k ∧ a.2 = t.2.1 + sumTo (blocksAt res) k)
      · simp [sumTo]
      · intro k hk a ha
        have hkp := sumTo_mono (blocksAt res) (Nat.succ_le_of_lt hk)
        change sumTo (blocksAt res) (k+1) ≤ bs r at hkp
        rw [sumTo_succ] at hkp
        have hab : a.2 + blocksAt res k ≤ L.maxCodeBlocks := by omega
        obtain ⟨pg, hpg, hnum, hle⟩ := precinct_ok res k hk (Nat.le_trans (Nat.le_add_left ..) hab)
        obtain ⟨st, hst⟩ := state_ok tc.params r pg hle
        rw [hpg]
        dsimp only [bind, Except.bind]
        rw [hnum, (Limits.check_eq_ok_iff ..).2 hab, hst]
        refine ⟨_, rfl, ?_, ?_⟩
        · simp only [Array.size_push]; omega
        · dsimp only; rw [sumTo_succ]; omega
      · intro a ha
        change a.1.size = t.1.size + ps r ∧ a.2 = t.2.1 + bs r at ha
        refine ⟨_, rfl, ?_, ?_⟩
        · dsimp only; rw [sumTo_succ]; change a.1.size = _; omega
        · dsimp only; rw [sumTo_succ]; change a.2 = _; omega
    · intro t ht
      refine ⟨_, rfl, ?_, ?_⟩ <;> dsimp only <;> rw [Nat.succ_mul]
      · exact ht.1
      · exact ht.2
  · intro s _
    exact ⟨_, rfl, trivial⟩

-- Along one axis a precinct boundary is also a code-block boundary. Clipping successive
-- precinct cells to an origin-zero band therefore telescopes, including its last cell.
private theorem cdiv_zero (e : Nat) : cdivPow 0 e = 0 := by
  have h := Nat.two_pow_pos e
  simp [cdivPow, cdiv, Nat.div_eq_of_lt (show 2^e-1 < 2^e by omega)]

private theorem cdiv_mono {w v : Nat} (e : Nat) (hle : w ≤ v) : cdivPow w e ≤ cdivPow v e := by
  unfold cdivPow cdiv
  exact Nat.div_le_div_right (by omega)

private def boundary (w d e i : Nat) := cdivPow (min w (i * 2^d)) e

private def delta (w d e i : Nat) := boundary w d e (i+1) - boundary w d e i

private theorem axis_cells (w d e i : Nat) (he : e ≤ d) :
    gridCount (i*2^d) (max (i*2^d) (min w (i*2^d + 2^d))) e = delta w d e i := by
  have hle := Nat.mul_le_mul_right (2^d) (Nat.le_succ i)
  unfold gridCount delta boundary
  rw [← Nat.succ_mul]
  by_cases h : w ≤ i*2^d
  · rw [Nat.min_eq_left (Nat.le_trans h hle), Nat.min_eq_left h, Nat.max_eq_left h]
    simp
  · have hnext : i*2^d < min w ((i+1)*2^d) := by
      apply Nat.lt_min.mpr
      exact ⟨by omega, by rw [Nat.succ_mul]; have := Nat.two_pow_pos d; omega⟩
    rw [Nat.max_eq_right (Nat.le_of_lt hnext), ite_eq_right (by omega),
      Nat.min_eq_right (by omega : i*2^d ≤ w)]
    have hmul : i*2^d = (i*2^(d-e))*2^e := by
      rw [Nat.mul_assoc, ← Nat.pow_add, Nat.sub_add_cancel he]
    have hm := Nat.two_pow_pos e
    rw [hmul, Nat.mul_div_cancel _ hm]
    congr 1
    unfold cdivPow cdiv
    rw [show i*2^(d-e)*2^e + 2^e - 1 = (2^e-1) + (i*2^(d-e))*2^e by omega,
      Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt (by omega)]
    simp

private theorem sum_delta (w d e n : Nat) : sumTo (delta w d e) n = boundary w d e n := by
  induction n with
  | zero => simp [sumTo, boundary, cdiv_zero]
  | succ n ih =>
    rw [sumTo_succ, ih]
    have h : boundary w d e n ≤ boundary w d e (n+1) := by
      apply cdiv_mono
      have hle : n*2^d ≤ (n+1)*2^d := Nat.mul_le_mul_right _ (Nat.le_succ _)
      omega
    unfold delta
    omega

private theorem sumTo_add (f : Nat → Nat) (a b : Nat) :
    sumTo f (a+b) = sumTo f a + sumTo (fun i => f (a+i)) b := by
  induction b with
  | zero => simp [sumTo]
  | succ b ih => rw [← Nat.add_assoc, sumTo_succ, ih, sumTo_succ, Nat.add_assoc]

private theorem sum_rect (x y : Nat → Nat) (w h : Nat) :
    sumTo (fun k => x (k%w) * y (k/w)) (w*h) = sumTo x w * sumTo y h := by
  induction h with
  | zero => simp [sumTo]
  | succ h ih =>
    rw [Nat.mul_succ, sumTo_add, ih, sumTo_succ, Nat.mul_add]
    congr 1
    cases w with
    | zero => simp [sumTo]
    | succ w =>
      have row (n : Nat) (hn : n ≤ w+1) :
          sumTo (fun i => x (((w+1)*h+i) % (w+1)) * y (((w+1)*h+i) / (w+1))) n =
            sumTo x n * y h := by
        induction n with
        | zero => simp [sumTo]
        | succ n ih =>
          rw [sumTo_succ, ih (by omega), sumTo_succ, Nat.add_mul (sumTo x n), Nat.mul_add_mod,
            Nat.mul_add_div (by omega), Nat.mod_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega),
            Nat.add_zero]
      exact row _ (Nat.le_refl _)

private theorem sum_band_le (res : ResolutionGeom) (b : BandGeom)
    (hkx : res.k0x = 0) (hky : res.k0y = 0) (hbx : b.rect.x0 = 0) (hby : b.rect.y0 = 0)
    (hx : b.cbWidthExp ≤ res.bandPpx) (hy : b.cbHeightExp ≤ res.bandPpy)
    (hcount : b.numCodeBlocks = cdivPow b.rect.x1 b.cbWidthExp * cdivPow b.rect.y1 b.cbHeightExp) :
    sumTo (fun k => leaves res k b) res.numPrecincts ≤ b.numCodeBlocks := by
  let x := delta b.rect.x1 res.bandPpx b.cbWidthExp
  let y := delta b.rect.y1 res.bandPpy b.cbHeightExp
  have heq (k : Nat) : leaves res k b = x (k%res.pw) * y (k/res.pw) := by
    unfold leaves grid
    simp only [precinctBandRect, clip, hkx, hky, hbx, hby, Nat.zero_add, Nat.zero_max,
      axis_cells _ _ _ _ hx, axis_cells _ _ _ _ hy]
    split
    · rename_i h
      rcases h with h | h
      · change x _ = 0 at h; simp [h]
      · change y _ = 0 at h; simp [h]
    · rfl
  rw [show (fun k => leaves res k b) = _ from funext heq, ResolutionGeom.numPrecincts,
    sum_rect, hcount]
  unfold x y
  rw [sum_delta, sum_delta]
  exact Nat.mul_le_mul (cdiv_mono _ (Nat.min_le_left ..)) (cdiv_mono _ (Nat.min_le_left ..))

private theorem cdiv_cast (w e : Nat) : cdivPowI (w : Int) e = (cdivPow w e : Nat) := by
  let d := 2^e
  have hd : 0 < d := Nat.two_pow_pos e
  have hd' : (0 : Int) < d := by omega
  have hpow : (2 : Int)^e = (d : Int) := by simp [d]
  unfold cdivPowI cdivPow cdiv
  rw [hpow]
  change -(-(w : Int) / d) = (((w+d-1)/d : Nat) : Int)
  let q := ((w+d-1 : Nat) : Int) / (d : Int)
  have hq := (Int.ediv_eq_iff_of_pos (x := ((w+d-1 : Nat) : Int)) (y := q) hd').1 rfl
  change _ = q
  suffices hh : -(w : Int) / (d : Int) = -q by omega
  rw [Int.ediv_eq_iff_of_pos hd', Int.neg_mul]
  omega

private theorem band_coord_cast (w n o : Nat) :
    cdivPowI ((w : Int) - (if o = 0 ∨ n = 0 then 0 else (2 : Int)^(n-1))) n =
      (bandCoord w n o : Int) := by
  unfold bandCoord
  split
  · simp [cdiv_cast]
  · rename_i h
    have hn : 0 < n := by omega
    let off := 2^(n-1)
    have hoff : off < 2^n := Nat.pow_lt_pow_right (by decide) (by omega)
    have hoff' : (2 : Int)^(n-1) = (off : Int) := by simp [off]
    rw [hoff']
    by_cases hle : off ≤ w
    · rw [← Int.natCast_sub hle, cdiv_cast]
    · have hsub : w - off = 0 := by omega
      change _ = (cdivPow (w-off) n : Int)
      rw [hsub, cdiv_zero]
      unfold cdivPowI
      rw [show (2 : Int)^n = ((2^n : Nat) : Int) by simp,
        Int.ediv_eq_zero_of_lt (by omega) (by omega)]
      rfl

private theorem band_origin (n o : Nat) : bandCoord 0 n o = 0 := by
  simp [bandCoord, cdiv_zero]

private theorem header_axis (w n o e : Nat) :
    bandBlocks1 0 w n o e = cdivPow (bandCoord w n o) e := by
  unfold bandBlocks1
  dsimp only
  rw [band_coord_cast, band_coord_cast, band_origin]
  split
  · rename_i h
    have : bandCoord w n o = 0 := by omega
    simp [this, cdiv_zero]
  · simp [cdiv_cast]

private theorem grid_origin (w e : Nat) : gridCount 0 w e = cdivPow w e := by
  cases w <;> simp [gridCount, cdiv_zero]

private theorem counted_band (tc : TileCompGeom) (r : Nat) (b : Band)
    (hx : tc.rect.x0 = 0) (hy : tc.rect.y0 = 0) :
    sumTo (fun k => leaves (summary tc r) k (bandGeom tc r b)) (summary tc r).numPrecincts ≤
      (bandGeom tc r b).numCodeBlocks := by
  apply sum_band_le
  · simp [summary, resRect, hx, cdiv_zero]
  · simp [summary, resRect, hy, cdiv_zero]
  · simp [bandGeom, bandRect, hx, band_origin]
  · simp [bandGeom, bandRect, hy, band_origin]
  · simp only [bandGeom, CompParams.effCbWidthExp, summary]; split <;> exact Nat.min_le_right ..
  · simp only [bandGeom, CompParams.effCbHeightExp, summary]; split <;> exact Nat.min_le_right ..
  · simp [bandGeom, bandRect, hx, hy, band_origin, grid_origin]

private theorem sumTo_plus (f g : Nat → Nat) (n : Nat) :
    sumTo (fun i => f i + g i) n = sumTo f n + sumTo g n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sumTo_succ, ih]; omega

private theorem sum_bands (tc : TileCompGeom) (r : Nat) (hx : tc.rect.x0 = 0)
    (hy : tc.rect.y0 = 0) :
    blockTotal tc r ≤ ((summary tc r).bands.toList.map BandGeom.numCodeBlocks).sum := by
  let res := summary tc r
  have aux (xs : List BandGeom) (hs : ∀ b ∈ xs, b ∈ res.bands) :
      sumTo (fun k => (xs.map (leaves res k)).sum) res.numPrecincts ≤
        (xs.map BandGeom.numCodeBlocks).sum := by
    induction xs with
    | nil => simp [sumTo, List.map_const', List.sum_replicate_nat]
    | cons b xs ih =>
      obtain ⟨orient, _, rfl⟩ := Array.mem_map.mp (hs b (by simp))
      simp only [List.map_cons, List.sum_cons, sumTo_plus]
      exact Nat.add_le_add (counted_band tc r orient hx hy) (ih (fun b hb => hs b (by simp [hb])))
  exact aux res.bands.toList (fun _ => Array.mem_def.mpr)

private theorem header_bands (tc : TileCompGeom) (r : Nat) (hx : tc.rect.x0 = 0)
    (hy : tc.rect.y0 = 0) :
    ((summary tc r).bands.toList.map BandGeom.numCodeBlocks).sum = numCodeBlocks tc.rect tc.params r := by
  by_cases hr : r = 0 <;>
    simp [summary, bandsOf, bandGeom, bandLevel, hr, bandRect, Band.xob, Band.yob, hx, hy,
      band_origin, grid_origin, numCodeBlocks, header_axis, Nat.add_assoc]

private theorem tile_counts (tc : TileCompGeom) :
    tileCompCounts tc.rect tc.params =
      (sumTo (numCodeBlocks tc.rect tc.params) (tc.params.levels+1),
       sumTo (fun r => (summary tc r).numPrecincts) (tc.params.levels+1)) := by
  have prec (r : Nat) : numPrecincts (resRect tc.rect tc.params.levels r)
      (tc.params.precincts.getD r Marker.Precinct.default) = (summary tc r).numPrecincts := by
    simp only [numPrecincts, summary, ResolutionGeom.numPrecincts, gridCount]
    split <;> rename_i h
    · rcases h with h | h <;> simp [h]
    · simp only [not_or] at h
      simp [h.1, h.2]
  have counts (xs : List Nat) (a : Nat × Nat) :
      xs.foldl (fun (cb, pr) r =>
        (cb + numCodeBlocks tc.rect tc.params r, pr + (summary tc r).numPrecincts)) a =
      (a.1 + (xs.map (numCodeBlocks tc.rect tc.params)).sum,
       a.2 + (xs.map (fun r => (summary tc r).numPrecincts)).sum) := by
    induction xs generalizing a with
    | nil => simp
    | cons r xs ih => simp [ih, Nat.add_assoc]
  simp only [tileCompCounts, prec, counts, Nat.zero_add, sumTo]

private theorem sumTo_le_sumTo (f g : Nat → Nat) (h : ∀ r, f r ≤ g r) (n : Nat) :
    sumTo f n ≤ sumTo g n := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih => rw [sumTo_succ, sumTo_succ]; exact Nat.add_le_add ih (h n)

/-- The header's total precinct and code-block inequalities suffice for all decoder
initialization loops on the encoder layout. Each precinct-band grid partitions a band
along aligned code-block boundaries, so its running block total fits the header count. -/
theorem initPrecincts_of_encCounts {L : Limits} {p : Encode.Params} {img : Encode.Image}
    {guard : Nat} {exps : Array Nat}
    (hpr : img.comps.size * (encCounts p img guard exps).2 ≤ L.maxPrecincts)
    (hcb : img.comps.size * (encCounts p img guard exps).1 ≤ L.maxCodeBlocks) :
    ∃ precs base spans, initPrecincts L (encLayout p img guard exps) = .ok (precs, base, spans) := by
  let tc := encGeom p img guard exps
  let g := encLayout p img guard exps
  have hc : g.numComps = img.comps.size := (encLayout_coding p img guard exps).1
  have hx : tc.rect.x0 = 0 := rfl
  have hy : tc.rect.y0 = 0 := rfl
  change img.comps.size * (tileCompCounts tc.rect tc.params).2 ≤ _ at hpr
  change img.comps.size * (tileCompCounts tc.rect tc.params).1 ≤ _ at hcb
  rw [tile_counts] at hpr hcb
  apply init_uniform g tc (fun c h => encLayout_comp p img guard exps c (hc ▸ h))
  · rwa [hc]
  · rw [hc]
    apply Nat.le_trans (Nat.mul_le_mul_left _ (sumTo_le_sumTo _ _ _ _)) hcb
    intro r
    rw [← header_bands tc r hx hy]
    exact sum_bands tc r hx hy
  · intro c hci r hr b hb
    have h1 : b.numCodeBlocks ≤ ((summary tc r).bands.toList.map BandGeom.numCodeBlocks).sum :=
      member_le_sum (List.mem_map.mpr ⟨b, Array.mem_def.mp hb, rfl⟩)
    rw [header_bands tc r hx hy] at h1
    have h2 : numCodeBlocks tc.rect tc.params r ≤
        sumTo (numCodeBlocks tc.rect tc.params) (tc.params.levels+1) :=
      member_le_sum (List.mem_map.mpr ⟨r, List.mem_range.mpr (by omega), rfl⟩)
    have h3 := Nat.mul_le_mul_right (sumTo (numCodeBlocks tc.rect tc.params) (tc.params.levels+1))
      (show 1 ≤ img.comps.size by omega)
    rw [Nat.one_mul] at h3
    exact Nat.le_trans h1 (Nat.le_trans h2 (Nat.le_trans h3 hcb))

/-- A decoder which admits the encoded header can initialize its precincts with the
same limits. The two tag trees per band impose no additional numerical premise. -/
theorem initPrecincts_of_headerFits {L : Limits} {p : Encode.Params} {img : Encode.Image}
    {guard size : Nat} {exps : Array Nat} (fits : HeaderFits L p img guard exps size) :
    ∃ precs base spans, initPrecincts L (encLayout p img guard exps) = .ok (precs, base, spans) :=
  initPrecincts_of_encCounts fits.precincts fits.codeBlocks

end JPEG2000.Spec.RoundTrip
