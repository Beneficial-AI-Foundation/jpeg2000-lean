import Spec.Resources.HeaderWork

/-!
# Source ranges of packed packet headers (Plan.md §§3–5, 7, S3; T.800 A.7.4–5)

PPM chunk splitting preserves input extent, including a split within a marker.
PPT sorting preserves the descriptors read within each tile-part. These facts
apply before the shared selector validates or copies any ranges.
-/
namespace JPEG2000.Spec.Resources.DiagnosticPacketRanges

open JPEG2000.Bytes JPEG2000.Header JPEG2000.Marker JPEG2000.TilePart Tier2Equiv

private abbrev Inside (n : Nat) (xs : Array ByteRange) := ∀ r ∈ xs, r.stop ≤ n

private theorem take_ranges {n : Nat} (rs : List ByteRange) (k : Nat) (a : Array ByteRange)
    (ha : Inside n a) (hr : ∀ r ∈ rs, r.stop ≤ n) {out tail}
    (ok : takeRanges rs k a = some (out,tail)) : Inside n out ∧ ∀ r ∈ tail, r.stop ≤ n := by
  induction rs generalizing a k with
  | nil => cases k <;> cases ok; exact ⟨ha,hr⟩
  | cons r rs ih =>
    have head := hr r (.head _)
    have rest := fun x hx => hr x (.tail _ hx)
    cases k with
    | zero => cases ok; exact ⟨ha,hr⟩
    | succ k =>
      simp only [takeRanges] at ok
      split at ok
      · rename_i fits; cases ok
        unfold ByteRange.stop at head
        constructor
        · intro x hx
          rcases Array.mem_push.mp hx with mem | rfl
          · exact ha x mem
          · simp only [ByteRange.stop]; omega
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | mem
          · simp only [ByteRange.stop]; omega
          · exact rest x mem
      · exact ih _ _ (fun x hx => (Array.mem_push.mp hx).elim (ha x) (fun e => e ▸ head)) rest ok

private theorem chunks {L : Limits} {d : ByteArray} {loc : Location} (fuel : Nat)
    (rs : List ByteRange) (a : Array (Array ByteRange)) (ha : ∀ xs ∈ a, Inside d.size xs)
    (hr : ∀ r ∈ rs, r.stop ≤ d.size) {out} (ok : ppmChunks L d loc fuel rs a = .ok out) :
    ∀ xs ∈ out, Inside d.size xs := by
  induction fuel generalizing rs a with
  | zero => cases rs <;> cases ok; exact ha
  | succ f ih =>
    cases rs with
    | nil => cases ok; exact ha
    | cons r rs =>
      unfold ppmChunks at ok
      obtain ⟨_,_,ok⟩ := bind_ok ok
      split at ok <;> try contradiction
      rename_i nb tail ht
      obtain ⟨⟨v,b⟩,_,ok⟩ := bind_ok ok
      dsimp only at ok
      split at ok <;> try contradiction
      rename_i part rest hpart
      have one := take_ranges _ _ _ (by simp [Inside]) hr ht
      have two := take_ranges _ _ _ (by simp [Inside]) one.2 hpart
      exact ih rest _ (fun xs hx => (Array.mem_push.mp hx).elim (ha xs) (fun e => e ▸ two.1)) two.2 ok

private theorem sorted_perm {α : Type} {xs ys : Array α} {key : α → UInt8} {loc name}
    (ok : sortUnique key loc name xs = .ok ys) : ys.Perm xs := by
  unfold sortUnique at ok
  dsimp only at ok
  split at ok <;> cases ok
  exact HeaderWork.insertionSort_perm ..

private theorem range_data {d : ByteArray} {rg : ByteRange} {r : Reader}
    (ok : rangeReader d rg = .ok r) : r.data = d := by
  unfold rangeReader at ok
  obtain ⟨t,skip,ok⟩ := bind_ok ok
  obtain ⟨⟨b,_⟩,take,ok⟩ := bind_ok ok
  cases ok
  exact (Reader.take_spec take).2.2.1.trans (Reader.skip_pos skip).2.2.1

private theorem pointers {L : Limits} {mh : MainHeader} {d : ByteArray} {ts ppm}
    (ok : parsePointers L mh d = .ok (ts,ppm)) : ∀ xs ∈ ppm.chunks, Inside d.size xs := by
  unfold parsePointers at ok
  obtain ⟨s,loop,ok⟩ := bind_ok ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  obtain ⟨ppms,sort,ok⟩ := bind_ok ok
  obtain ⟨out,hc,ok⟩ := bind_ok ok
  cases ok
  rw [← Array.forIn_toList] at loop
  have inv := forIn_inv (fun s : Array TLM × Array PPM × Nat => ∀ p ∈ s.2.1, p.body.stop ≤ d.size)
    _ ?_ _ _ _ (by simp) loop
  · apply chunks _ _ _ (by simp) _ hc
    intro r mem
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp mem
    exact inv p ((sorted_perm sort).mem_iff.mp (by simpa using hp))
  · intro seg s y old step
    obtain ⟨r,range,step⟩ := bind_ok step
    split at step
    · obtain ⟨_,_,step⟩ := bind_ok step
      obtain ⟨_,_,step⟩ := bind_ok step
      cases step; exact old
    · split at step
      · obtain ⟨p,read,step⟩ := bind_ok step
        cases step
        unfold parsePPM at read
        obtain ⟨⟨_,t⟩,u,read⟩ := bind_ok read
        obtain ⟨_,_,read⟩ := bind_ok read
        cases read
        intro x hx
        rcases Array.mem_push.mp hx with mem | rfl
        · exact old _ mem
        · change t.pos+(t.stop-t.pos) ≤ _
          have := t.pos_le
          have le := (Reader.u8_pos u).2.2.1.trans (range_data range)
          have := le ▸ t.stop_le; omega
      · cases step; exact old

private abbrev Segs (n : Nat) (a : Array TileSegment) := ∀ p, .ppt p ∈ a → p.body.stop ≤ n

private theorem add_ppt {L : Limits} {r : Reader} {n c first ppm a m z}
    (size : r.data.size ≤ n) (old : Segs n a.segments)
    (ok : addTileSegment L c first ppm a m r = .ok z) : Segs n z.segments := by
  unfold addTileSegment at ok
  repeat' first | (split at ok <;> try contradiction) | obtain ⟨_,_,ok⟩ := bind_ok ok
  all_goals cases ok; intro p hp; rcases Array.mem_push.mp hp with mem | eq
  all_goals try first | exact old p mem | contradiction
  have read : parsePPT r = .ok p := by cases eq; assumption
  unfold parsePPT at read
  obtain ⟨⟨_,t⟩,u,read⟩ := bind_ok read
  obtain ⟨_,_,read⟩ := bind_ok read
  cases read
  change t.pos+(t.stop-t.pos) ≤ _
  have := t.pos_le
  have le := Nat.le_trans t.stop_le ((Reader.u8_pos u).2.2.1 ▸ size)
  omega

private theorem tile_header {L : Limits} {c first ppm n} (fuel : Nat) {r t : Reader} {a z}
    (bound : r.data.size ≤ n) (old : Segs n a.segments)
    (ok : headerLoop L c first ppm fuel a r = .ok (z,t)) : Segs n z.segments := by
  induction fuel generalizing a r with
  | zero => cases ok
  | succ f ih =>
    simp only [headerLoop] at ok
    split at ok <;> try contradiction
    rename_i m r1 read
    have hb : r1.data.size ≤ n := by rw [(Reader.u16be_pos read).2.2.1]; exact bound
    split at ok
    · cases ok; exact old
    split at ok <;> try contradiction
    split at ok
    · apply ih hb _ ok; exact old
    split at ok <;> try contradiction
    split at ok <;> try contradiction
    rename_i body len next seg
    split at ok <;> try contradiction
    rename_i z' step
    obtain ⟨db,dn,_⟩ := HeaderWork.readSegment_extent seg
    exact ih (dn ▸ hb) (add_ppt (r := body) (db ▸ hb) (by exact old) step) ok

private abbrev Parts (n : Nat) (ps : Array TilePartHeader) := ∀ p ∈ ps, Segs n p.segments

private theorem part {c : Ctx} {r t : Reader} {a z : State} {n}
    (size : r.data.size ≤ n) (old : ∀ ps ∈ a.parts, Parts n ps)
    (ok : readTilePart c a r = .ok (z,t)) : ∀ ps ∈ z.parts, Parts n ps := by
  unfold readTilePart at ok
  obtain ⟨⟨_,_⟩,u,ok⟩ := bind_ok ok
  obtain ⟨⟨_,_,r2⟩,seg,ok⟩ := bind_ok ok
  iterate 7 obtain ⟨_,_,ok⟩ := bind_ok ok
  dsimp only at ok
  split at ok <;> split at ok <;> try contradiction
  all_goals
    simp only [pure_bind] at ok
    obtain ⟨⟨tp,_⟩,take,ok⟩ := bind_ok ok
    obtain ⟨⟨_,_⟩,loop,ok⟩ := bind_ok ok
    cases ok
    have db := (Reader.take_spec take).2.2.1.trans
      ((HeaderWork.readSegment_extent seg).2.1.trans (Reader.u16be_pos u).2.2.1)
    have hd := tile_header _ (db ▸ size) (by simp [Segs]) loop
    intro ps hps
    obtain ⟨j,hj,rfl⟩ := Array.mem_iff_getElem.mp hps
    dsimp only
    rw [Array.getElem_modify]
    split
    · intro p hp
      rcases Array.mem_push.mp hp with mem | rfl
      · exact old _ (Array.getElem_mem _) _ mem
      · exact hd
    · exact old _ (Array.getElem_mem _)

private theorem loop_parts {c : Ctx} {n} (fuel : Nat) {s z : State} {r : Reader}
    (size : r.data.size ≤ n) (old : ∀ ps ∈ s.parts, Parts n ps)
    (ok : tilePartLoop c fuel s r = .ok z) : ∀ ps ∈ z.parts, Parts n ps := by
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
    exact ih ((HeaderWork.readTilePart_step step).2.2.2.1 ▸ size) (part size old step) ok

private theorem assembled {n : Nat} {corr i ps t} (inside : Parts n ps) (ok : assembleTile corr i ps = .ok t) :
    Inside n t.ppt := by
  let collect := fun (acc : Array PPT) (p : TilePartHeader) =>
    acc ++ p.segments.filterMap fun | .ppt x => some x | _ => none
  have collect_ok (xs : List TilePartHeader) (a : Array PPT) (ha : ∀ p ∈ a, p.body.stop ≤ n)
      (hx : ∀ p ∈ xs, Segs n p.segments) : ∀ p ∈ xs.foldl collect a, p.body.stop ≤ n := by
    induction xs generalizing a with
    | nil => exact ha
    | cons p ps ih =>
      apply ih _ _ (fun z hz => hx z (.tail _ hz))
      intro x hit
      rcases Array.mem_append.mp hit with mem | mem
      · exact ha _ mem
      · obtain ⟨s,hs,eq⟩ := Array.mem_filterMap.mp mem
        cases s <;> cases eq
        exact hx p (.head _) _ hs
  unfold assembleTile at ok
  dsimp only at ok
  split at ok <;> split at ok <;> try (obtain ⟨_,bad,_⟩ := bind_ok ok; cases bad)
  all_goals
    obtain ⟨ppts,sort,ok⟩ := bind_ok ok
    obtain ⟨_,_,ok⟩ := bind_ok ok
    cases ok
    intro r hr
    obtain ⟨p,mem,rfl⟩ := Array.mem_map.mp hr
    have src := (sorted_perm sort).mem_iff.mp mem
    rw [← Array.foldl_toList] at src
    exact collect_ok ps.toList #[] (by simp) (fun x hx => inside x (by simpa using hx)) p src

private theorem tiles {L : Limits} {n : Nat} {corr : Bool} {parts : Array (Array TilePartHeader)}
    (all : ∀ ps ∈ parts, Parts n ps) (fuel i count : Nat) (a : Array Tile)
    (old : ∀ t ∈ a, Inside n t.ppt) {out} (ok : assembleTiles L corr parts fuel i count a = .ok out) :
    ∀ t ∈ out, Inside n t.ppt := by
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
    · apply assembled _ ht
      cases get : parts[i]? with
      | none => simp [Parts]
      | some z => exact all _ (Array.mem_of_getElem? get)

private theorem tilePPT {L : Limits} {mh : MainHeader} {r : Reader} {out}
    (ok : parseTileParts L mh r = .ok out) : ∀ t ∈ out, Inside r.data.size t.ppt := by
  unfold parseTileParts at ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  obtain ⟨_,loop,ok⟩ := bind_ok ok
  apply tiles (loop_parts _ (Nat.le_refl _) _ loop) _ _ _ _ (by simp) ok
  intro ps hp
  obtain ⟨_,rfl⟩ := Array.mem_replicate.mp hp
  simp [Parts]

private theorem main_data {L : Limits} {r t : Reader} {mh : MainHeader}
    (ok : parseMainHeader L r = .ok (mh,t)) : t.data = r.data := by
  unfold parseMainHeader at ok
  obtain ⟨⟨_,_⟩,h1,ok⟩ := bind_ok ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  obtain ⟨⟨_,_⟩,h2,ok⟩ := bind_ok ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  obtain ⟨⟨_,_,_⟩,seg,ok⟩ := bind_ok ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  obtain ⟨⟨a,last⟩,loop,ok⟩ := bind_ok ok
  cases hc : a.cod <;> simp only [hc] at ok <;> try contradiction
  cases hq : a.qcd <;> simp only [hq] at ok <;> try contradiction
  cases ok
  exact (HeaderWork.segmentLoop_storage loop).2.1.trans ((HeaderWork.readSegment_extent seg).2.1.trans
    ((Reader.u16be_pos h2).2.2.1.trans (Reader.u16be_pos h1).2.2.1))

/-- Every range passed from a successful public header parse to the shared PPM/PPT
selector ends within the original input. The validation loop can fail at a rank
lookup, but its range-overrun diagnostic is unreachable for these descriptors. -/
theorem parsed_ranges {L : Limits} {d : ByteArray} {h : Header} (ok : Header.parse L d = .ok h) :
    (∀ xs ∈ h.ppm.chunks, ∀ r ∈ xs, r.stop ≤ d.size) ∧
    (∀ tp ∈ h.tiles, ∀ r ∈ tp.tile.ppt, r.stop ≤ d.size) := by
  unfold Header.parse at ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  unfold parseCodestreamIn at ok
  obtain ⟨r,range,ok⟩ := bind_ok ok
  obtain ⟨⟨mh,t⟩,main,ok⟩ := bind_ok ok
  iterate 2 obtain ⟨_,_,ok⟩ := bind_ok ok
  obtain ⟨⟨_,ppm⟩,ptr,ok⟩ := bind_ok ok
  obtain ⟨ts,parts,ok⟩ := bind_ok ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  obtain ⟨_,mapped,ok⟩ := bind_ok ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  cases ok
  have eq := (main_data main).trans (range_data range)
  refine ⟨pointers ptr,Tier2WF.arrayMapM_mem _ _ _ ?_ _ mapped⟩
  intro tile mem tp ok
  obtain ⟨_,_,ok⟩ := bind_ok ok; cases ok
  exact eq ▸ tilePPT parts tile mem

end JPEG2000.Spec.Resources.DiagnosticPacketRanges
