import Spec.WideOutput
import JPEG2000.NativeOutput

/-!
# Native component allocation and placement (Plan.md §§4, 5.1, 5.4, 7; T.800 B.2, B-14, G.1)

A component keeps its reduced image rectangle and SIZ descriptor. At a translated
tile coordinate the observed integer is the G.1 reconstruction of the centred
post-MCT cell. At every other coordinate the previous observation survives.
-/

namespace JPEG2000.Spec.NativeOutput

open JPEG2000.NativeOutput Bytes Header

/-- Pointwise specification for writing one post-MCT tile-component. Coordinates
are relative to the component image; the tile rectangle uses absolute grid coordinates. -/
def Placed (dst q : OutputComponent) (r : Rect) (F : Nat) (src : Source) : Prop :=
  let ox := r.x0 - dst.rect.x0
  let oy := r.y0 - dst.rect.y0
  q.rect = dst.rect ∧ q.format = dst.format ∧
  (∀ x y, x < src.width → y < src.height →
    q.get? ((oy + y) * dst.rect.width + (ox + x)) =
      (src.get? (y * src.width + x)).map (MCT.reconIrrev dst.format.signed dst.format.depth.toNat F)) ∧
  (∀ x y, x < dst.rect.width → y < dst.rect.height →
    ¬WideOutput.Inside src.width src.height ox oy x y →
    q.get? (y * dst.rect.width + x) = dst.get? (y * dst.rect.width + x))

private theorem bind_ok {α β : Type} {x : Except Error α} {f : α → Except Error β} {q : β} :
    (x >>= f) = .ok q ↔ ∃ a, x = .ok a ∧ f a = .ok q := by
  cases x <;> simp [bind, Except.bind]

private theorem mapFin_ok {α β : Type} (xs : Array α)
    (f : (i : Nat) → α → i < xs.size → Except Error β) {out : Array β}
    (ok : xs.mapFinIdxM f = .ok out) :
    xs.size = out.size ∧ ∀ i (hi : i < xs.size), ∃ b, out[i]? = some b ∧ f i xs[i] hi = .ok b := by
  have loop (k j : Nat) (inv : k + j = xs.size) (acc : Array β) (sz : acc.size = j)
      (hk : Array.mapFinIdxM.map xs f k j inv acc = .ok out) :
      xs.size = out.size ∧ (∀ i < j, out[i]? = acc[i]?) ∧
      ∀ i (hi : i < xs.size), j ≤ i → ∃ b, out[i]? = some b ∧ f i xs[i] hi = .ok b := by
    induction k generalizing j acc with
    | zero =>
      simp [Array.mapFinIdxM.map, pure, Except.pure] at hk
      subst out
      exact ⟨by omega, fun _ _ => rfl, fun _ _ _ => by omega⟩
    | succ k ih =>
      simp only [Array.mapFinIdxM.map, bind_ok] at hk
      obtain ⟨b, hb, hk⟩ := hk
      obtain ⟨hout, earlier, suffix⟩ := ih (j + 1) (by omega) (acc.push b) (by simp [sz]) hk
      refine ⟨hout, fun i hi => ?_, fun i hi hji => ?_⟩
      · rw [earlier i (by omega), Array.getElem?_push, ite_eq_right (by omega)]
      · by_cases e : i = j
        · subst i
          exact ⟨b, by rw [earlier j (by omega), Array.getElem?_push, sz, ite_eq_left rfl], hb⟩
        · exact suffix i hi (by omega)
  obtain ⟨sz, _, h⟩ := loop xs.size 0 (by omega) #[] rfl ok
  exact ⟨sz, fun i hi => h i hi (Nat.zero_le _)⟩

private theorem allocOne_spec (r : Rect) (c : Marker.Component) (d : OutputComponent)
    (ok : allocOne r c = .ok d) :
    d.rect = r ∧ d.format = c ∧
    ∀ i (_hi : i < r.width * r.height), d.get? i = some 0 := by
  unfold allocOne at ok
  split at ok
  · split at ok <;> cases ok
    · refine ⟨rfl, rfl, fun i hi => ?_⟩
      simp [OutputComponent.get?, Plane.get?, show i < (Plane.zero r.width r.height).width *
          (Plane.zero r.width r.height).height from hi, Plane.get_zero]
    · refine ⟨rfl, rfl, fun i hi => ?_⟩
      simp only [OutputComponent.get?, Bytes.WidePlane.get?]
      split
      · exact congrArg some (Bytes.WidePlane.get_zero _ _ _ _ _ i hi)
      · exact False.elim (by contradiction)
  · cases ok

/-- Allocation checks the total reduced work and declared bytes. The result contains
one zeroed component per SIZ entry with its complete geometry and original format. -/
theorem allocOutput_spec {L : Limits} {s : Marker.SIZ} {reduce : Nat} {out : Array OutputComponent}
    (ok : allocOutput L s reduce = .ok out) :
    let rs := layout s reduce
    cells rs ≤ L.maxWorkSamples ∧ decodedBytes rs ≤ L.maxDecodedBytes ∧ rs.size = out.size ∧
    ∀ i (hi : i < rs.size), ∃ d, out[i]? = some d ∧ d.rect = rs[i].1 ∧ d.format = rs[i].2 ∧
      ∀ j (_hj : j < d.rect.width * d.rect.height), d.get? j = some 0 := by
  simp only [allocOutput, bind_ok] at ok
  obtain ⟨_, _, _, hw, _, hb, hm⟩ := ok
  have le {v bound : Nat} {loc : Location} {k : LimitKind} {u : Unit}
      (h : Limits.checkLe loc k v bound = .ok u) : v ≤ bound := by
    unfold Limits.checkLe at h
    split at h <;> first | assumption | contradiction
  obtain ⟨sz, atIdx⟩ := mapFin_ok _ _ hm
  refine ⟨le hw, le hb, sz, fun i hi => ?_⟩
  obtain ⟨d, hd, ha⟩ := atIdx i hi
  obtain ⟨hr, hc, hz⟩ := allocOne_spec _ _ _ ha
  exact ⟨d, hd, hr, hc, fun j hj => hz j (hr ▸ hj)⟩

private theorem fill_spec {N : Nat} (f : Fin N → Int32) (n : Nat) (hn : n ≤ N)
    (b : DWT53.Buf N) :
    let q := fill f n hn b
    q.1.width = b.1.width ∧ q.1.height = b.1.height ∧
    ∀ i (hi : i < N), q.get i hi = if i < n then f ⟨i, hi⟩ else b.get i hi := by
  induction n generalizing b with
  | zero => exact ⟨rfl, rfl, fun i _ => by simp [fill]⟩
  | succ n ih =>
    obtain ⟨hw, hh, hg⟩ := ih (Nat.le_of_lt hn) (b.set n (f ⟨n, hn⟩) hn)
    refine ⟨hw, hh, fun i hi => ?_⟩
    rw [fill, hg, DWT53.Buf.get_set]
    by_cases h : i = n
    · subst i; simp
    · by_cases hs : i < n <;> simp [hs, Ne.symm h, show (i < n + 1) ↔ i < n by omega]

private def TileValues (q : Plane) (s : Source) (r : NativeSampleRange) (F : Nat) : Prop :=
  q.width = s.width ∧ q.height = s.height ∧
  ∀ i (hi : i < s.width * s.height), (q.get? i).map Int32.toInt =
    some (MCT.reconIrrev r.signed r.depth F (s.read ⟨i, hi⟩))

private theorem exact_values (s : Source) (r : NativeSampleRange)
    (fits : -2147483648 ≤ r.lo ∧ r.hi ≤ 2147483647) (F : Nat) :
    TileValues (exactTile s r fits F) s r F := by
  let kernel := JPEG2000.WideOutput.prepare r F
  let f := fun i => Int32.ofInt (kernel.sample (s.read i)).val
  let b : DWT53.Buf (s.width * s.height) := ⟨Plane.zero s.width s.height, rfl⟩
  let q := fill f _ (Nat.le_refl _) b
  obtain ⟨hw, hh, hv⟩ := fill_spec f _ (Nat.le_refl _) b
  refine ⟨hw, hh, fun i hi => ?_⟩
  have hi' : i < q.1.width * q.1.height := Nat.lt_of_lt_of_eq hi q.2.symm
  let v := kernel.sample (s.read ⟨i, hi⟩)
  have hval := v.property
  have he : (Int32.ofInt v.val).toInt = v.val :=
    Int32.toInt_ofInt_of_le (by have := fits.1; omega) (by have := fits.2; omega)
  change (q.1.get? i).map Int32.toInt = _
  simp only [Plane.get?, hi', ↓reduceDIte, Option.map_some, Option.some.injEq]
  change (q.get i hi).toInt = _
  rw [hv, ite_eq_left hi]
  exact he.trans (WideOutput.sample_irrev r F (s.read ⟨i, hi⟩))

private theorem map_dims {N : Nat} (f : Int32 → Int32) (b : DWT53.Buf N) (i : Nat) :
    (JPEG2000.MCT.map1 f b i).1.width = b.1.width ∧
    (JPEG2000.MCT.map1 f b i).1.height = b.1.height := by
  unfold JPEG2000.MCT.map1
  split
  · exact map_dims f _ (i + 1)
  · exact ⟨rfl, rfl⟩
termination_by N - i

private theorem mapped_values (p : Plane) (r : NativeSampleRange) (F : Nat)
    (f : Int32 → Int32) (hf : ∀ v, (f v).toInt = MCT.reconIrrev r.signed r.depth F v.toInt) :
    TileValues (JPEG2000.MCT.map1 f (N := p.width * p.height) ⟨p, rfl⟩ 0).1 (.plane p) r F := by
  let b : DWT53.Buf (p.width * p.height) := ⟨p, rfl⟩
  let q := JPEG2000.MCT.map1 f b 0
  obtain ⟨hw, hh⟩ := map_dims f b 0
  refine ⟨hw, hh, fun i hi => ?_⟩
  have hi' : i < q.1.width * q.1.height := Nat.lt_of_lt_of_eq hi q.2.symm
  change (q.1.get? i).map Int32.toInt = _
  simp only [Plane.get?, hi', ↓reduceDIte, Option.map_some, Option.some.injEq]
  change (q.get i hi).toInt = _
  have hg := JPEG2000.MCT.map1_get f b 0 i hi
  rw [ite_eq_right (Nat.not_lt_zero _)] at hg
  rw [show q.get i hi = _ from hg]
  exact hf _

private theorem narrow_values (s : Source) (r : NativeSampleRange)
    (fits : -2147483648 ≤ r.lo ∧ r.hi ≤ 2147483647) (F : Nat) :
    TileValues (narrowTile s r fits F) s r F := by
  cases s with
  | exact => exact exact_values _ r fits F
  | plane p =>
    simp only [narrowTile]
    split
    · rename_i dc hdc
      have wf := JPEG2000.MCT.DcShift.make_wf _ _ _ dc hdc
      have fields : dc.signed = r.signed ∧ dc.depth = r.depth ∧ dc.F = F := by
        simp only [JPEG2000.MCT.DcShift.make] at hdc
        split at hdc <;> cases hdc
        exact ⟨rfl, rfl, rfl⟩
      split
      · rename_i hF
        apply mapped_values
        intro v
        rw [JPEG2000.MCT.DcShift.rev_eq _ wf, fields.1, fields.2.1, hF]
        simp [MCT.reconIrrev, MCT.roundFix]
      · apply mapped_values
        intro v
        rw [JPEG2000.MCT.DcShift.irrev_eq _ wf, fields.1, fields.2.1, fields.2.2]
    · exact exact_values _ r fits F

private theorem set_get? (p : Plane) (i : Nat) (v : Int32) (hi : i < p.width * p.height)
    (j : Nat) : (p.set i v hi).get? j = if i = j then some v else p.get? j := by
  by_cases hj : j < p.width * p.height
  · have hj' : j < (p.set i v hi).width * (p.set i v hi).height := hj
    simp only [Plane.get?, hj, hj', ↓reduceDIte]
    split
    · subst j; exact congrArg some (Plane.get_set_self ..)
    · exact congrArg some (Plane.get_set_ne p i j v hi hj (by assumption))
  · have hj' : ¬j < (p.set i v hi).width * (p.set i v hi).height := hj
    simp [Plane.get?, hj, hj', show i ≠ j by omega]

private theorem row_spec (p : Plane) (k si di : Nat) (d : Plane)
    (hs : si + k ≤ p.width * p.height) (hd : di + k ≤ d.width * d.height) :
    let q := Assemble.blitRow p k si di d
    q.width = d.width ∧ q.height = d.height ∧ ∀ j, q.get? j =
      if di ≤ j ∧ j < di + k then p.get? (si + (j - di)) else d.get? j := by
  induction k generalizing si di d with
  | zero => exact ⟨rfl, rfl, fun j => by simp [Assemble.blitRow]; omega⟩
  | succ k ih =>
    have h1 : si < p.width * p.height := by omega
    have h2 : di < d.width * d.height := by omega
    let next := d.set di (p.get si h1) h2
    have hn : di + 1 + k ≤ next.width * next.height := by change di + 1 + k ≤ d.width * d.height; omega
    simp only [Assemble.blitRow, h1, h2, ↓reduceDIte]
    obtain ⟨hw, hh, hv⟩ := ih (si + 1) (di + 1) next (by omega) hn
    refine ⟨hw, hh, fun j => ?_⟩
    rw [hv, show next.get? j = _ from set_get? ..]
    split
    · rename_i hj
      rw [ite_eq_left (by omega), show si + 1 + (j - (di + 1)) = si + (j - di) by omega]
    · by_cases e : di = j
      · subst j; simp [Plane.get?, h1]
      · simp [e, show ¬(di ≤ j ∧ j < di + (k + 1)) by omega]

private theorem rows_spec (p : Plane) (ox oy k start : Nat) (d : Plane)
    (hx : ox + p.width ≤ d.width) (hy : oy + p.height ≤ d.height) (hk : start + k ≤ p.height) :
    let q := Assemble.blitRows p ox oy k start d
    q.width = d.width ∧ q.height = d.height ∧ ∀ x y, x < d.width →
      q.get? (y * d.width + x) =
        if oy + start ≤ y ∧ y < oy + start + k ∧ ox ≤ x ∧ x < ox + p.width
        then p.get? ((y - oy) * p.width + (x - ox)) else d.get? (y * d.width + x) := by
  induction k generalizing start d with
  | zero => exact ⟨rfl, rfl, fun _ _ _ => by simp [Assemble.blitRows]; omega⟩
  | succ k ih =>
    let dw := d.width
    let base := (oy + start) * dw + ox
    let next := Assemble.blitRow p p.width (start * p.width) base d
    have srcBound := Nat.mul_le_mul_right p.width (show start + 1 ≤ p.height by omega)
    have dstBound := Nat.mul_le_mul_right dw (show oy + start + 1 ≤ d.height by omega)
    rw [Nat.succ_mul, Nat.mul_comm p.height] at srcBound
    rw [Nat.succ_mul, Nat.mul_comm d.height] at dstBound
    have row := row_spec p p.width (start * p.width) base d srcBound (by dsimp [base, dw] at *; omega)
    obtain ⟨hw, hh, hr⟩ := row
    have hw' : next.width = dw := hw
    obtain ⟨hw2, hh2, hv⟩ := ih (start + 1) next (hw ▸ hx) (hh ▸ hy) (by omega)
    refine ⟨hw2.trans hw, hh2.trans hh, fun x y hcol => ?_⟩
    have step := hv x y (hw ▸ hcol)
    rw [hw'] at step
    change (Assemble.blitRows p ox oy k (start + 1) next).get? (y * dw + x) = _
    rw [step, hr]
    change x < dw at hcol
    change ox + p.width ≤ dw at hx
    by_cases eq : y = oy + start
    · subst y
      simp only [show ¬oy + (start + 1) ≤ oy + start by omega, false_and, ↓reduceIte,
        Nat.le_refl, true_and, show oy + start < oy + start + (k + 1) by omega,
        show oy + start - oy = start by omega]
      dsimp only [base]
      split <;> split <;> first | rfl | congr 2 <;> omega | omega
    · have miss : ¬(base ≤ y * dw + x ∧ y * dw + x < base + p.width) := by
        dsimp [base]
        rcases Nat.lt_or_gt_of_ne eq with lt | gt
        · have := Nat.mul_le_mul_right dw lt; rw [Nat.succ_mul] at this; omega
        · have := Nat.mul_le_mul_right dw gt; rw [Nat.succ_mul] at this; omega
      rw [ite_eq_right miss]
      congr 1
      apply propext
      omega

private theorem narrow_blit {p d q : Plane} {ox oy : Nat} (ok : Assemble.blit d p ox oy = .ok q) :
    (∀ x y, x < p.width → y < p.height →
      q.get? ((oy + y) * d.width + (ox + x)) = p.get? (y * p.width + x)) ∧
    (∀ x y, x < d.width → ¬WideOutput.Inside p.width p.height ox oy x y →
      q.get? (y * d.width + x) = d.get? (y * d.width + x)) := by
  unfold Assemble.blit at ok
  split at ok
  · rename_i fit
    cases ok
    obtain ⟨_, _, hv⟩ := rows_spec p ox oy p.height 0 d fit.1 fit.2 (by omega)
    constructor
    · intro x y hx hy
      have h := hv (ox + x) (oy + y) (by have := fit.1; omega)
      simpa [hx, hy] using h
    · intro x y hx miss
      have h := hv x y hx
      simp only [Nat.add_zero] at h
      rwa [ite_eq_right (by unfold WideOutput.Inside at miss; omega)] at h
  · cases ok

private theorem finish_eq {r : Rect} {c : Marker.Component}
    {hd : 1 ≤ c.depth.toNat ∧ c.depth.toNat ≤ 38} {b : Storage} {q : OutputComponent}
    (ok : finish r c hd b = .ok q) : ∃ hv, q = ⟨r, c, hd, b, hv⟩ := by
  unfold finish at ok
  split at ok <;> cases ok
  exact ⟨_, rfl⟩

/-- Malformed absolute offsets and inconsistent source dimensions are rejected
before DC reconstruction. Empty tiles still undergo both origin checks. -/
theorem writeComponent_badGeometry (L : Limits) (dst : OutputComponent) (r : Rect)
    (F : Nat) (src : Source) (bad : fitsTile dst.rect r src = false) :
    writeComponent L dst r F src = .error
      (.malformed (.at .decode) "tile-component shape or offset outside the reduced image") := by
  simp only [writeComponent, bad, Bool.not_false, ↓reduceIte]
  rfl

/-- Every successful component write implements exact G.1 and preserves every
outside observation, independent of the destination backing or centred source format. -/
theorem writeComponent_spec {L : Limits} {dst q : OutputComponent} {r : Rect}
    {F : Nat} {src : Source} (ok : writeComponent L dst r F src = .ok q) : Placed dst q r F src := by
  cases geom : fitsTile dst.rect r src with
  | false => rw [writeComponent_badGeometry _ _ _ _ _ geom] at ok; contradiction
  | true =>
    cases dst with
    | mk d c hd b valid =>
      cases b with
      | wide p =>
        simp only [Storage.matches, Bool.and_eq_true, beq_iff_eq] at valid
        obtain ⟨⟨⟨⟨hw, hh⟩, hs⟩, hd⟩, _⟩ := valid
        simp only [writeComponent, geom, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          bind, Except.bind] at ok
        cases hbl : JPEG2000.WideOutput.blit L (.at .decode) p src.width src.height
            (r.x0 - d.x0) (r.y0 - d.y0) F src.read with
        | error e => rw [hbl] at ok; contradiction
        | ok bp =>
          rw [hbl] at ok
          obtain ⟨_, rfl⟩ := finish_eq ok
          obtain ⟨_, _, _, inside, frame⟩ := WideOutput.blit_spec hbl
          refine ⟨rfl, rfl, fun x y hx hy => ?_, fun x y hx hy ho => ?_⟩
          · have inner := inside x y hx hy
            rw [hw, hs, hd] at inner
            simpa only [OutputComponent.get?, Source.get?, DWT53.idx_lt hx hy,
              ↓reduceDIte, Option.map_some] using inner
          · rw [hw, hh] at frame
            exact frame x y hx hy ho
      | narrow p =>
        simp only [Storage.matches, Bool.and_eq_true, beq_iff_eq] at valid
        obtain ⟨⟨hw, hh⟩, hc⟩ := valid
        simp only [writeComponent, geom, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          bind_ok] at ok
        obtain ⟨_, _, _, _, bp, hbl, hfin⟩ := ok
        obtain ⟨_, rfl⟩ := finish_eq hfin
        let rng : NativeSampleRange := ⟨_, c.signed, hd, _, _, rfl, rfl⟩
        have fits : -2147483648 ≤ rng.lo ∧ rng.hi ≤ 2147483647 := by simpa [compact] using hc
        obtain ⟨sw, sh, values⟩ := narrow_values src rng fits F
        change Assemble.blit p (narrowTile src rng fits F) _ _ = .ok bp at hbl
        obtain ⟨inside, frame⟩ := narrow_blit hbl
        simp only [sw, sh, hw] at inside frame
        refine ⟨rfl, rfl, fun x y hx hy => ?_, fun x y hx _ ho => ?_⟩
        · have h := congrArg (Option.map Int32.toInt) (inside x y hx hy)
          rw [values _ (DWT53.idx_lt hx hy)] at h
          simpa only [OutputComponent.get?, Source.get?, DWT53.idx_lt hx hy,
            ↓reduceDIte, Option.map_some] using h
        · exact congrArg (Option.map Int32.toInt) (frame x y hx ho)

private theorem fitOffsets (d r : Rect) (s : Source) (h : fitsTile d r s) :
    r.x0 - d.x0 + s.width ≤ d.width ∧ r.y0 - d.y0 + s.height ≤ d.height := by
  simp only [fitsTile, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  unfold Rect.width Rect.height at *
  omega

/-- A contained, correctly shaped tile can be placed on any admitted native component
within the two inclusive output limits, for every centred input and binary scale. -/
theorem writeComponent_succeeds (L : Limits) (dst : OutputComponent) (r : Rect)
    (F : Nat) (src : Source) (geom : fitsTile dst.rect r src)
    (work : dst.rect.width * dst.rect.height ≤ L.maxWorkSamples)
    (bytes : dst.rect.width * dst.rect.height * bytesPerSample dst.format.depth.toNat ≤ L.maxDecodedBytes) :
    ∃ q, writeComponent L dst r F src = .ok q := by
  obtain ⟨ox, oy⟩ := fitOffsets _ _ _ geom
  cases dst with
  | mk d c hd b valid =>
    cases b with
    | wide p =>
      simp only [Storage.matches, Bool.and_eq_true, beq_iff_eq] at valid
      obtain ⟨⟨⟨⟨hw, hh⟩, hs⟩, hdepth⟩, hc⟩ := valid
      have h := (WideOutput.blit_succeeds L (.at .decode) p src.width src.height
        (r.x0 - d.x0) (r.y0 - d.y0) F src.read).mpr
          (by rw [hw, hh, hdepth]; exact ⟨work, bytes, ox, oy⟩)
      obtain ⟨bp, hb⟩ := h
      obtain ⟨hw', hh', hr, _⟩ := WideOutput.blit_spec hb
      have hv : (Storage.wide bp).matches d c := by
        simp only [Storage.matches, Bool.and_eq_true, beq_iff_eq]
        rw [hw', hh', hr]; exact ⟨⟨⟨⟨hw, hh⟩, hs⟩, hdepth⟩, hc⟩
      exact ⟨⟨d, c, hd, _, hv⟩, by simp [writeComponent, geom, hb, finish, hv, bind, Except.bind]⟩
    | narrow p =>
      obtain ⟨⟨hw, hh⟩, hc⟩ : (p.width = d.width ∧ p.height = d.height) ∧ compact c := by
        simpa only [Storage.matches, Bool.and_eq_true, beq_iff_eq] using valid
      let rng : NativeSampleRange := ⟨_, c.signed, hd, _, _, rfl, rfl⟩
      have fits : -2147483648 ≤ rng.lo ∧ rng.hi ≤ 2147483647 := by simpa [compact] using hc
      let pl := narrowTile src rng fits F
      obtain ⟨sw, sh, _⟩ := narrow_values src rng fits F
      have fit : r.x0 - d.x0 + pl.width ≤ p.width ∧ r.y0 - d.y0 + pl.height ≤ p.height := by
        dsimp only [pl]; rw [sw, sh, hw, hh]; exact ⟨ox, oy⟩
      let bp := Assemble.blitRows pl (r.x0 - d.x0) (r.y0 - d.y0) pl.height 0 p
      obtain ⟨hw', hh', _⟩ := rows_spec pl _ _ pl.height 0 p fit.1 fit.2 (by omega)
      have hv : (Storage.narrow bp).matches d c := by
        simp only [Storage.matches, Bool.and_eq_true, beq_iff_eq]
        exact ⟨⟨hw'.trans hw, hh'.trans hh⟩, hc⟩
      have hb : Assemble.blit p pl (r.x0 - d.x0) (r.y0 - d.y0) = .ok bp := by
        simp [Assemble.blit, fit, bp]
      have wc : L.check (.at .decode) .workSamples (d.width * d.height) = .ok () :=
        by apply ite_eq_left; exact work
      have bc : L.check (.at .decode) .decodedBytes (d.width * d.height * bytesPerSample c.depth.toNat)
          = .ok () := by apply ite_eq_left; exact bytes
      refine ⟨⟨d, c, hd, _, hv⟩, ?_⟩
      simp only [writeComponent, geom, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        wc, bc, bind, Except.bind]
      dsimp only [pl, rng] at hb
      rw [hb]
      simp [finish, hv]

/-- A second placement retains the exact reconstructed value of every site written
by the first tile that lies outside the second rectangle. -/
theorem disjoint_writes {L : Limits} {d q z : OutputComponent} {a b : Rect} {F G : Nat}
    {s t : Source} (first : writeComponent L d a F s = .ok q)
    (second : writeComponent L q b G t = .ok z)
    (x y : Nat) (hx : x < s.width) (hy : y < s.height)
    (outside : ¬WideOutput.Inside t.width t.height (b.x0 - d.rect.x0) (b.y0 - d.rect.y0)
      (a.x0 - d.rect.x0 + x) (a.y0 - d.rect.y0 + y)) :
    z.get? ((a.y0 - d.rect.y0 + y) * d.rect.width + (a.x0 - d.rect.x0 + x)) =
      (s.get? (y * s.width + x)).map (MCT.reconIrrev d.format.signed d.format.depth.toNat F) := by
  have hgeom : fitsTile d.rect a s := by
    cases h : fitsTile d.rect a s
    · rw [writeComponent_badGeometry _ _ _ _ _ h] at first; contradiction
    · rfl
  obtain ⟨gx, gy⟩ := fitOffsets _ _ _ hgeom
  obtain ⟨hr, _, hit, _⟩ := writeComponent_spec first
  obtain ⟨_, _, _, frame⟩ := writeComponent_spec second
  rw [hr] at frame
  rw [frame _ _ (by omega) (by omega) outside, hit _ _ hx hy]

/-- The indexed tile traversal pairs every output with exactly one source. Its
rectangle comes from the tile layout, its scale from the effective transform and
post-MCT precision supplied by reconstruction. Every pair satisfies the pointwise
native placement specification. -/
theorem writeTile_spec {L : Limits} {s : Marker.SIZ} {reduce : Nat} {g : Progression.Layout}
    {coding : Coding} {ds out : Array OutputComponent} {src : Array Source}
    {irrevBits : Nat → Nat} (ok : writeTile L s reduce g coding ds src irrevBits = .ok out) :
    ds.size = out.size ∧ ds.size = s.components.size ∧ ds.size = g.numComps ∧ ds.size = src.size ∧
    ∀ i (hi : i < ds.size), ∃ q t, out[i]? = some q ∧ src[i]? = some t ∧
      Placed ds[i] q (Assemble.reduceRect (g.comp i).rect reduce)
        (if (g.comp i).params.transform == .reversible53 then 0
         else irrevBits i) t := by
  simp only [writeTile, bind_ok] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · rename_i counts
    obtain ⟨sz, atIdx⟩ := mapFin_ok _ _ ok
    refine ⟨sz, counts.1, counts.2.1, counts.2.2, fun i hi => ?_⟩
    obtain ⟨q, hq, hw⟩ := atIdx i hi
    split at hw
    · cases hw
    · split at hw
      · cases hw
      · refine ⟨q, src[i]'(counts.2.2 ▸ hi), hq, Array.getElem?_eq_getElem _, ?_⟩
        exact writeComponent_spec hw
  · cases ok

private theorem mapFin_succeeds {α β : Type} (xs : Array α)
    (f : (i : Nat) → α → i < xs.size → Except Error β)
    (hf : ∀ i (hi : i < xs.size), ∃ b, f i xs[i] hi = .ok b) :
    ∃ out, xs.mapFinIdxM f = .ok out := by
  have loop (k j : Nat) (inv : k + j = xs.size) (acc : Array β) :
      ∃ out, Array.mapFinIdxM.map xs f k j inv acc = .ok out := by
    induction k generalizing j acc with
    | zero => exact ⟨acc, rfl⟩
    | succ k ih =>
      obtain ⟨b, hb⟩ := hf j (by omega)
      obtain ⟨out, hout⟩ := ih (j + 1) (by omega) (acc.push b)
      exact ⟨out, by simp only [Array.mapFinIdxM.map, bind_ok]; exact ⟨b, hb, hout⟩⟩
  exact loop _ 0 rfl #[]

/-- At legal SIZ precisions the reduction and both aggregate budgets suffice for allocation. -/
theorem allocOutput_succeeds (L : Limits) (s : Marker.SIZ) (reduce : Nat)
    (hr : reduce ≤ L.maxDecompLevels) (work : cells (layout s reduce) ≤ L.maxWorkSamples)
    (bytes : decodedBytes (layout s reduce) ≤ L.maxDecodedBytes)
    (depth : ∀ c ∈ s.components, 1 ≤ c.depth.toNat ∧ c.depth.toNat ≤ 38) :
    ∃ out, allocOutput L s reduce = .ok out := by
  obtain ⟨out, ho⟩ := mapFin_succeeds (layout s reduce) (fun _ (r, c) _ => allocOne r c) (by
    intro i hi
    unfold layout at hi ⊢
    simp only [Array.getElem_map]
    have hd := depth _ (Array.getElem_mem (by simpa using hi))
    simp only [allocOne, dite_eq_left hd]
    split <;> exact ⟨_, rfl⟩)
  refine ⟨out, ?_⟩
  simpa only [allocOutput, Limits.check, Limits.checkLe, Limits.bound,
    hr, work, bytes, ↓reduceIte, bind, Except.bind] using ho

/-- Number of bytes in the component's physical sample buffer. -/
def backingBytes (d : OutputComponent) : Nat :=
  match d.storage with
  | .narrow p => p.data.size
  | .wide p => p.words.data.size

/-- Each output owns exactly four or eight backing bytes per cell according to its
declared interval. This also counts partially filled and repeatedly placed images. -/
theorem backing_size (d : OutputComponent) :
    backingBytes d =
      (if compact d.format then 4 else 8) * (d.rect.width * d.rect.height) := by
  unfold backingBytes
  cases d with
  | mk r c hd b hv =>
    cases b with
    | narrow p =>
      obtain ⟨⟨hw, hh⟩, hc⟩ : (p.width = r.width ∧ p.height = r.height) ∧ compact c := by
        simpa only [Storage.matches, Bool.and_eq_true, beq_iff_eq] using hv
      simpa only [hc, ↓reduceIte, ← hw, ← hh] using p.size_eq
    | wide p =>
      simp only [Storage.matches, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hv
      obtain ⟨⟨⟨⟨hw, hh⟩, _⟩, _⟩, hc⟩ := hv
      simpa only [hc, Bool.false_eq_true, ↓reduceIte, ← hw, ← hh] using p.size_eq

/-- The sum of the actual allocated buffers is bounded by eight physical bytes per
permitted work sample. The allocated grids also satisfy the declared output-byte budget. -/
theorem allocOutput_bounds {L : Limits} {s : Marker.SIZ} {reduce : Nat} {out : Array OutputComponent}
    (ok : allocOutput L s reduce = .ok out) :
    let actual := out.map fun d => (d.rect, d.format)
    actual = layout s reduce ∧ decodedBytes actual ≤ L.maxDecodedBytes ∧
      (out.toList.map backingBytes).sum ≤ 8 * L.maxWorkSamples := by
  obtain ⟨hw, hb, hs, hv⟩ := allocOutput_spec ok
  have shape : (out.map fun d => (d.rect, d.format)) = layout s reduce := by
    apply Array.ext
    · simpa using hs.symm
    · intro i _ hi
      obtain ⟨d, hd, hr, hc, _⟩ := hv i hi
      have ho : out[i]'(hs ▸ hi) = d := by simpa only [Array.getElem?_eq_getElem (hs ▸ hi),
        Option.some.injEq] using hd
      simp [ho, hr, hc]
  refine ⟨shape, shape ▸ hb, ?_⟩
  have bound (ds : List OutputComponent) (a : Nat) :
      (ds.map backingBytes).sum + 8 * a ≤
        8 * ((ds.map fun d => (d.rect, d.format)).foldl (fun j p => j + p.1.width * p.1.height) a) := by
    induction ds generalizing a with
    | nil => simp
    | cons d ds ih =>
      simp only [List.map_cons, List.sum_cons, List.foldl_cons]
      have tail := ih (a + d.rect.width * d.rect.height)
      have single : backingBytes d ≤ 8 * (d.rect.width * d.rect.height) := by
        rw [backing_size]; split <;> omega
      omega
  have ha := bound out.toList 0
  simp only [Nat.mul_zero, Nat.add_zero, ← Array.toList_map, Array.foldl_toList] at ha
  have hcells : cells (out.map fun d => (d.rect, d.format)) ≤ L.maxWorkSamples := shape ▸ hw
  apply Nat.le_trans _ (Nat.mul_le_mul_left 8 hcells)
  simpa only [cells, Array.toList_map] using ha

/-- After final rounding, the stored sample is the exact rational decoder's half-up
result shifted by G.1 and clamped to the SIZ interval. This includes negative ties. -/
theorem writeComponent_roundHalf {L : Limits} {d q : OutputComponent} {r : Rect}
    {F : Nat} {src : Source} (ok : writeComponent L d r F src = .ok q)
    (x y : Nat) (hx : x < src.width) (hy : y < src.height) :
    let z := src.read ⟨y * src.width + x, DWT53.idx_lt hx hy⟩
    q.get? ((r.y0 - d.rect.y0 + y) * d.rect.width + (r.x0 - d.rect.x0 + x)) =
      some (MCT.reconRev d.format.signed d.format.depth.toNat
        (Decode.roundHalf ((z : Rat) / ((2^F : Int) : Rat)))) := by
  have hit := (writeComponent_spec ok).2.2.1 x y hx hy
  simpa only [Source.get?, DWT53.idx_lt hx hy, ↓reduceDIte, Option.map_some,
    MCT.reconIrrev, WideOutput.roundFix_eq_roundHalf] using hit

/-- Legal native values survive centred reconstruction at every binary scale, with
no restriction that the centred value or its DC shift fit a machine word. -/
theorem writeComponent_recovers {L : Limits} {d q : OutputComponent} {r : Rect}
    {F : Nat} {src : Source} (ok : writeComponent L d r F src = .ok q)
    (x y : Nat) (hx : x < src.width) (hy : y < src.height) (v : Int)
    (hv : MCT.sampleMin d.format.signed d.format.depth.toNat ≤ v ∧
      v ≤ MCT.sampleMax d.format.signed d.format.depth.toNat)
    (centered : src.read ⟨y * src.width + x, DWT53.idx_lt hx hy⟩ =
      (v - MCT.dcOffset d.format.signed d.format.depth.toNat) * 2^F) :
    q.get? ((r.y0 - d.rect.y0 + y) * d.rect.width + (r.x0 - d.rect.x0 + x)) = some v := by
  let rng : NativeSampleRange := ⟨_, d.format.signed, d.precision, _, _, rfl, rfl⟩
  have recover := WideOutput.sample_recovers rng F v hv
  rw [WideOutput.sample_irrev] at recover
  have hit := (writeComponent_spec ok).2.2.1 x y hx hy
  rw [hit]
  simp only [Source.get?, DWT53.idx_lt hx hy, ↓reduceDIte, Option.map_some, centered]
  exact congrArg some recover

/-- A tile with matching component metadata, admissible reduction, contained sources
and sufficient destination budgets is written in its entirety. -/
theorem writeTile_succeeds (L : Limits) (s : Marker.SIZ) (reduce : Nat) (g : Progression.Layout)
    (coding : Coding) (ds : Array OutputComponent) (src : Array Source)
    (hr : reduce ≤ L.maxDecompLevels)
    (counts : ds.size = s.components.size ∧ ds.size = g.numComps ∧ ds.size = src.size)
    (ready : ∀ i (hi : i < ds.size),
      let d := ds[i]
      let c := s.components[i]'(counts.1 ▸ hi)
      let t := src[i]'(counts.2.2 ▸ hi)
      d.format = c ∧ d.rect = Assemble.reduceRect (compRect (imageRect s) c) reduce ∧
      reduce ≤ (g.comp i).params.levels ∧ fitsTile d.rect (Assemble.reduceRect (g.comp i).rect reduce) t ∧
      d.rect.width * d.rect.height ≤ L.maxWorkSamples ∧
      d.rect.width * d.rect.height * bytesPerSample d.format.depth.toNat ≤ L.maxDecodedBytes)
    (irrevBits : Nat → Nat := Assemble.fracBitsOf s (coding.mctApplies s)) :
    ∃ out, writeTile L s reduce g coding ds src irrevBits = .ok out := by
  have hcheck : L.check (.at .decode) .decompLevels reduce = .ok () := by
    apply ite_eq_left; exact hr
  simp only [writeTile, hcheck, bind, Except.bind, dite_eq_left counts]
  apply mapFin_succeeds
  intro i hi
  obtain ⟨hc, hd, hl, hg, work, bytes⟩ := ready i hi
  simp only [hc, hd, bne_self_eq_false, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
    Nat.not_lt.mpr hl]
  exact writeComponent_succeeds L ds[i] _ _ _ hg work bytes

private def mixedSiz : Marker.SIZ :=
  { rsiz := 0, xsiz := 13, ysiz := 5, xosiz := 1, yosiz := 1, xtsiz := 8, ytsiz := 5,
    xtosiz := 0, ytosiz := 0, components := #[⟨true, 8, 1, 1⟩, ⟨false, 38, 2, 2⟩] }

private def mixedLayout (i : Nat) : Progression.Layout :=
  let tile := tileRect mixedSiz i
  { tile, layers := 1, comps := mixedSiz.components.map fun c =>
      { tile, rect := compRect tile c, dx := c.dx.toNat, dy := c.dy.toNat
        params := { (default : CompParams) with levels := 1, transform := .reversible53 } } }

/-- Observe both reduced images after writing tile 1 before tile 0. -/
private def mixedImage (L : Limits) : Option (List (Rect × Marker.Component × List Int)) := do
  let ds ← (allocOutput L mixedSiz 1).toOption
  let g1 := mixedLayout 1
  let g0 := mixedLayout 0
  let ds ← (writeTile L mixedSiz 1 g1 default ds
    #[.exact 3 2 (fun i => i.val + 10), .exact 2 1 (fun i => if i.val = 0 then -(2^37) else 2^37 - 1)]).toOption
  let ds ← (writeTile L mixedSiz 1 g0 default ds
    #[.plane (Plane.zero 3 2), .plane (Plane.zero 1 1)]).toOption
  ds.toList.mapM fun d => do
    let samples ← (List.range (d.rect.width * d.rect.height)).mapM d.get?
    return (d.rect, d.format, samples)

-- Inclusive aggregate limits: 12 ordinary cells + 3 wide cells cost 36 declared bytes.
set_option maxRecDepth 8192 in
example : mixedImage { Limits.default with maxWorkSamples := 15, maxDecodedBytes := 36 } =
    some [(⟨1, 1, 7, 3⟩, ⟨true, 8, 1, 1⟩, [0, 0, 0, 10, 11, 12, 0, 0, 0, 13, 14, 15]),
          (⟨1, 1, 4, 2⟩, ⟨false, 38, 2, 2⟩, [137438953472, 0, 274877906943])] := by decide +kernel

example : mixedImage { Limits.default with maxWorkSamples := 14 } = none := by decide +kernel
example : mixedImage { Limits.default with maxDecodedBytes := 35 } = none := by decide +kernel

private def ictSamples (overrideBits : Option Nat := none) : Option (List Int) := do
  let s := { mixedSiz with
    xsiz := 2, ysiz := 1, xosiz := 0, yosiz := 0
    components := #[⟨true, 8, 1, 1⟩, ⟨true, 24, 1, 1⟩, ⟨false, 12, 1, 1⟩] }
  let r := imageRect s
  let params := { (default : CompParams) with transform := .irreversible97 }
  let g : Progression.Layout := { tile := r, layers := 1, comps := Array.replicate 3 ⟨r, r, 1, 1, params⟩ }
  let p ← (Plane.zero 2 1).set? 0 (-6)
  let p ← p.set? 1 2
  let ds ← (allocOutput Limits.default s 0).toOption
  let coding := { (default : Coding) with mct := true }
  let src : Array Source := #[.plane p, .exact 2 1 (fun i => if i.val = 0 then -6 else 2), .plane p]
  let qs ← (match overrideBits with
    | none => writeTile Limits.default s 0 g coding ds src
    | some F => writeTile Limits.default s 0 g coding ds src (fun _ => F)).toOption
  let pairs ← qs.toList.mapM fun q => do return [← q.get? 0, ← q.get? 1]
  return pairs.flatten

-- The 24-bit component sets F=2 for all three ICT outputs: -1.5 rounds to -1,
-- +0.5 to +1, including the 12-bit unsigned channel's DC shift.
example : ictSamples none = some [-1, 1, -1, 1, 2047, 2049] := by decide +kernel
example : ictSamples (some 4) = some [0, 0, 0, 0, 2048, 2048] := by decide +kernel

-- The dispatch boundary differs by one precision bit for signed and unsigned samples.
example : [compact ⟨false, 31, 1, 1⟩, compact ⟨false, 32, 1, 1⟩,
           compact ⟨true, 32, 1, 1⟩, compact ⟨true, 33, 1, 1⟩] = [true, false, true, false] := by decide

private def atRect (signed : Bool) (depth : UInt8) (r : Rect) : Option (Option Int) := do
  let d ← (allocOne ⟨3, 4, 5, 6⟩ ⟨signed, depth, 1, 1⟩).toOption
  let q ← (writeComponent Limits.default d r 1 (.exact 2 1 (fun _ => -3))).toOption
  return q.get? 0

-- The same negative tie crosses both physical backings. Shape errors include an
-- equal-area transposition and starts before either absolute origin.
example : atRect true 38 ⟨3, 4, 5, 5⟩ = some (some (-1)) := by decide +kernel
example : atRect false 32 ⟨3, 4, 5, 5⟩ = some (some 2147483647) := by decide +kernel
example : atRect true 32 ⟨2, 4, 4, 5⟩ = none := by decide +kernel
example : atRect false 38 ⟨3, 3, 5, 4⟩ = none := by decide +kernel
example : atRect true 8 ⟨3, 4, 4, 6⟩ = none := by decide +kernel

end JPEG2000.Spec.NativeOutput
