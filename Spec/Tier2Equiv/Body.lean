import Spec.Tier2Equiv.Header

/-!
# Tier-2 equivalence, layer (e): packet bodies
(Plan.md §4 C9, §5.1, §5.2 "Tier-2"; T.800 B.10.8, D.4)

Task 7.1b. A fast segment (a list of byte ranges of the body buffer) has the bytes
`segOf buf`; appending a range (`pushRange`, merging adjacent ranges) appends its bytes
(`pushRange_bytes`), so the fast `addPieces` is the spec `addPieces` of the image
(`addPieces_eq`); `takePieces` over the body reader slices the reader's byte list as the
spec does (`takePieces_sim`), and the whole body loop follows the spec `readBody`
(`readBody_sim`).
-/

namespace JPEG2000.Spec.Tier2Equiv

open JPEG2000 JPEG2000.Bytes JPEG2000.TilePart JPEG2000.Spec.Tier2 JPEG2000.Tier2.Packet

/-- The bytes of a range of `buf` as a list. -/
def rb (buf : ByteArray) (r : ByteRange) : List UInt8 := (r.bytes buf).data.toList

/-- The bytes of `extract` as a list are `bytesFrom`. -/
theorem extract_toList (d : ByteArray) (a b : Nat) :
    (d.extract a b).data.toList = bytesFrom d a b := by
  simp only [ByteArray.data_extract, Array.toList_extract, List.extract, bytesFrom]
  rw [List.drop_take]

/-- The bytes of a range are `bytesFrom` of its bounds (clamped to the buffer). -/
theorem rb_eq (buf : ByteArray) (r : ByteRange) : rb buf r = bytesFrom buf r.offset r.stop :=
  extract_toList buf _ _

/-- Concatenating range bytes onto an accumulator. -/
theorem foldl_bytes (d : ByteArray) : ∀ (rs : List ByteRange) (acc : ByteArray),
    (rs.foldl (fun acc r => acc ++ r.bytes d) acc).data.toList = acc.data.toList ++ rs.flatMap (rb d)
  | [], acc => by simp
  | r :: rs, acc => by
    simp only [List.foldl_cons, foldl_bytes d rs, ByteArray.data_append, Array.toList_append,
      List.flatMap_cons, List.append_assoc, rb]

/-- The bytes of a fast segment: its ranges' bytes concatenated. -/
theorem segment_bytes (d : ByteArray) (s : Segment) :
    (s.bytes d).data.toList = s.ranges.toList.flatMap (rb d) := by
  unfold Segment.bytes
  rw [← Array.foldl_toList, foldl_bytes]
  simp [ByteArray.empty, ByteArray.emptyWithCapacity]; rfl

/-- `back?` is the last element of the list. -/
theorem back?_toList {α : Type} (xs : Array α) : xs.back? = xs.toList.getLast? := by
  rw [Array.back?_eq_getElem?, List.getLast?_eq_getElem?, Array.getElem?_toList]; simp

/-- `pushRange` appends the range's bytes (empty ranges dropped, adjacent ones merged). -/
theorem pushRange_bytes (d : ByteArray) (rs : Array ByteRange) (rg : ByteRange) :
    (pushRange rs rg).toList.flatMap (rb d) = rs.toList.flatMap (rb d) ++ rb d rg := by
  unfold pushRange
  by_cases h0 : rg.length = 0
  · simp only [h0, ↓reduceIte]
    have : rb d rg = [] := by
      rw [rb_eq, bytesFrom_of_le (by simp [ByteRange.stop, h0])]
    rw [this, List.append_nil]
  · simp only [h0, ↓reduceIte]
    rw [back?_toList]
    cases hb : rs.toList.getLast? with
    | none =>
      have : rs.toList = [] := List.getLast?_eq_none_iff.mp hb
      simp [this]
    | some l =>
      have hsplit : rs.toList = rs.toList.dropLast ++ [l] := by
        obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hb
        rw [hys, List.dropLast_concat]
      dsimp only
      split
      · rename_i hst
        rw [Array.toList_push, Array.toList_pop]
        conv => rhs; rw [hsplit]
        simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
          List.append_assoc]
        congr 1
        simp only [rb, ByteRange.bytes, ByteRange.stop] at hst ⊢
        rw [← hst]
        have : d.extract l.offset (l.offset + l.length) ++
            d.extract (l.offset + l.length) (l.offset + l.length + rg.length) =
            d.extract l.offset (l.offset + (l.length + rg.length)) := by
          rw [ByteArray.extract_append_extract, Nat.min_eq_left (by omega), Nat.max_eq_right (by omega),
            Nat.add_assoc]
        rw [← this, ByteArray.data_append, Array.toList_append]
      · rw [Array.toList_push]; simp

/-- A fast code-block after `addPieces` is the spec `addPieces` of its image (B.10.8, D.4). -/
theorem addPieces_eq (d : ByteArray) : ∀ (rs : List (Nat × ByteRange)) (cb : CodeBlock) (cont : Bool),
    blockOf d (JPEG2000.Tier2.Packet.addPieces cb cont rs) =
      Spec.Tier2.addPieces (blockOf d cb) cont (rs.map fun x => (x.1, rb d x.2))
  | [], cb, cont => rfl
  | (p, rg) :: rs, cb, cont => by
    simp only [JPEG2000.Tier2.Packet.addPieces, Spec.Tier2.addPieces, List.map_cons]
    rw [addPieces_eq d rs]
    congr 1
    simp only [blockOf]
    congr 1
    have hl : (cb.segments.toList.map (segOf d)).getLast? = (cb.segments.back?).map (segOf d) := by
      rw [back?_toList, List.getLast?_map]
    rw [hl]
    cases cont <;> cases hb : cb.segments.back? with
    | none => simp [segOf, segment_bytes, pushRange_bytes]
    | some s =>
      first
      | simp [segOf, segment_bytes, pushRange_bytes]
      | (simp only [Option.map_some, Array.toList_push, Array.toList_pop, List.map_append,
          List.map_dropLast, List.map_cons, List.map_nil]
         simp [segOf, segment_bytes, pushRange_bytes])

/-- The byte list of a reader. -/
def rbytes (r : Reader) : List UInt8 := bytesFrom r.data r.pos r.stop

/-- Length of a reader's byte list. -/
theorem length_rbytes (r : Reader) : (rbytes r).length = r.stop - r.pos :=
  length_bytesFrom _ _ r.stop_le

/-- **B.10.8, one contribution**: `takePieces` over the body reader follows the spec over its
byte list; each piece's bytes are those of its range. -/
theorem takePieces_sim : ∀ (ps : List (Nat × Nat)) (r : Reader),
    Res (fun (x : List (Nat × ByteRange) × Reader) (y : List (Nat × List UInt8) × List UInt8) =>
        y.1 = x.1.map (fun z => (z.1, rb r.data z.2)) ∧ y.2 = rbytes x.2 ∧ x.2.data = r.data ∧
        x.2.stop = r.stop)
      (JPEG2000.Tier2.Packet.takePieces r ps) (Spec.Tier2.takePieces ps (rbytes r))
  | [], r => ⟨rfl, rfl, rfl, rfl⟩
  | (p, len) :: ps, r => by
    simp only [JPEG2000.Tier2.Packet.takePieces, Spec.Tier2.takePieces, length_rbytes]
    have hpl := r.pos_le
    by_cases hl : r.pos + len > r.stop
    · simp only [hl, ↓reduceIte, show len > r.stop - r.pos by omega]; trivial
    · simp only [hl, ↓reduceIte, show ¬ len > r.stop - r.pos by omega]
      simp only [Reader.skip, show r.pos + len ≤ r.stop by omega, ↓reduceDIte, ok_bind]
      have hdrop : (rbytes r).drop len = rbytes { r with pos := r.pos + len, pos_le := by omega } := by
        simp only [rbytes, bytesFrom_add]
      rw [hdrop]
      refine Res.bind (takePieces_sim ps { r with pos := r.pos + len, pos_le := by omega })
        fun x y ⟨h1, h2, h3, h4⟩ => ?_
      refine ⟨?_, h2, h3, h4⟩
      simp only [h1, List.map_cons, List.cons.injEq, Prod.mk.injEq, true_and, and_true]
      rw [rb_eq]
      simp only [rbytes, bytesFrom, ByteRange.stop, List.take_drop, List.take_take]
      congr 2; omega

/-- The loop body of `readBody` (as elaborated). -/
def bodyBody (c : Contribution) (s : Array BandState × Reader) :
    Except Error (ForInStep (Array BandState × Reader)) := do
  let (rs, body') ← JPEG2000.Tier2.Packet.takePieces s.2 c.pieces
  match s.1[c.band]? with
  | some bs =>
    match bs.blocks[c.block]? with
    | some cb =>
      pure (ForInStep.yield (s.1.setIfInBounds c.band
        { band := bs.band, rect := bs.rect, maxZero := bs.maxZero, incl := bs.incl, zbp := bs.zbp,
          blocks := bs.blocks.setIfInBounds c.block (JPEG2000.Tier2.Packet.addPieces cb c.cont rs) },
        body'))
    | _ => do
      throw (Error.malformed JPEG2000.Tier2.Packet.loc "code-block index out of range")
      pure (ForInStep.yield (s.1, body'))
  | _ => do
    throw (Error.malformed JPEG2000.Tier2.Packet.loc "band index out of range")
    pure (ForInStep.yield (s.1, body'))

/-- `readBody` as a fold of `bodyBody` over the contributions. -/
theorem readBody_eq (st : PrecState) (cs : Array Contribution) (body : Reader) :
    JPEG2000.Tier2.Packet.readBody st cs body =
      (do
        let s ← forIn cs.toList (st.bands, body) bodyBody
        pure ({ style := st.style, bands := s.1 }, s.2)) := by
  unfold JPEG2000.Tier2.Packet.readBody
  dsimp only
  rw [Array.forIn_toList]
  rfl

/-- Band arrays related index by index. -/
def BRel (buf : ByteArray) (bands : Array BandState) (sbands : List BandSt) : Prop :=
  ∀ j : Nat, ORel (BandRel buf) bands[j]? sbands[j]?

/-- Related band arrays have equal lengths. -/
theorem BRel.size {buf : ByteArray} {bands : Array BandState} {sbands : List BandSt}
    (h : BRel buf bands sbands) : bands.size = sbands.length := by
  rcases Nat.lt_trichotomy bands.size sbands.length with h1 | h1 | h1
  · have := h bands.size
    rw [Array.getElem?_eq_none (Nat.le_refl _), List.getElem?_eq_getElem h1] at this
    exact absurd this id
  · exact h1
  · have := h sbands.length
    rw [List.getElem?_eq_none (Nat.le_refl _), Array.getElem?_eq_getElem h1] at this
    exact absurd this id

/-- Replacing a band by a related one keeps band arrays related. -/
theorem BRel.set {buf : ByteArray} {bands : Array BandState} {sbands : List BandSt}
    (h : BRel buf bands sbands) (i : Nat) (fb : BandState) (sb : BandSt) (hb : BandRel buf fb sb) :
    BRel buf (bands.setIfInBounds i fb) (sbands.set i sb) := by
  intro j
  rw [Array.getElem?_setIfInBounds, List.getElem?_set, h.size]
  split
  · split
    · exact hb
    · trivial
  · exact h j

/-- **B.10.8**: the fast body loop follows the spec `readBody`. -/
theorem bodyLoop_sim (buf : ByteArray) : ∀ (cs : List Contribution) (bands : Array BandState)
    (body : Reader) (sp : PrecSt), body.data = buf → BRel buf bands sp.bands →
    Res (fun (x : Array BandState × Reader) (y : PrecSt × List UInt8) =>
        BRel buf x.1 y.1.bands ∧ y.1.style = sp.style ∧ y.2 = rbytes x.2 ∧ x.2.data = buf ∧
          x.2.stop = body.stop)
      (forIn cs (bands, body) bodyBody) (Spec.Tier2.readBody sp cs (rbytes body))
  | [], bands, body, sp, hd, hR => by
    simp only [List.forIn_nil, Spec.Tier2.readBody]
    exact ⟨hR, rfl, rfl, hd, rfl⟩
  | c :: cs, bands, body, sp, hd, hR => by
    simp only [List.forIn_cons, Spec.Tier2.readBody, bodyBody, bind_assoc]
    refine Res.bind (takePieces_sim c.pieces body) fun ⟨rs, body'⟩ ⟨rs', l'⟩ ⟨h1, h2, h3, h4⟩ => ?_
    dsimp only at h1 h2 h3 h4 ⊢
    subst h1 h2
    have hb := hR c.band
    revert hb
    cases hfb : bands[c.band]? with
    | none =>
      cases sp.bands[c.band]? with
      | none => intro _; exact Res.error _ _
      | some _ => intro h; exact absurd h id
    | some fb =>
      cases hsb : sp.bands[c.band]? with
      | none => intro h; exact absurd h id
      | some sb =>
        intro hb
        dsimp only
        have hget : sb.blocks[c.block]? = (fb.blocks[c.block]?).map (blockOf buf) := by
          rw [hb.2.2.2.2.2.2.2.2.2, List.getElem?_map, Array.getElem?_toList]
        rw [hget]
        cases hcb : fb.blocks[c.block]? with
        | none => exact Res.error _ _
        | some cb =>
          dsimp only [Option.map]
          simp only [pure_bind']
          have hb' : BandRel buf
              { band := fb.band, rect := fb.rect, maxZero := fb.maxZero, incl := fb.incl, zbp := fb.zbp,
                blocks := fb.blocks.setIfInBounds c.block (JPEG2000.Tier2.Packet.addPieces cb c.cont rs) }
              { band := sb.band, rect := sb.rect, w := sb.w, h := sb.h, maxZero := sb.maxZero,
                incl := sb.incl, zbp := sb.zbp,
                blocks := sb.blocks.set c.block (Spec.Tier2.addPieces (blockOf buf cb) c.cont
                    (rs.map (fun z => (z.1, rb body.data z.2)))) } := by
            obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩ := hb
            refine ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, ?_⟩
            dsimp only
            rw [e10, Array.toList_setIfInBounds, List.map_set, addPieces_eq, hd]
          have hR' := hR.set c.band _ _ hb'
          have := bodyLoop_sim buf cs _ body' { style := sp.style, bands := _ } (h3.trans hd) hR'
          exact Res.mono this fun x y ⟨g1, g2, g3, g4, g5⟩ => ⟨g1, g2, g3, g4, g5.trans h4⟩

/-- **B.10.8, one packet body**: `readBody` follows the spec. -/
theorem readBody_sim (buf : ByteArray) (fp : PrecState) (sp : PrecSt) (hR : PrecRel buf fp sp)
    (cs : Array Contribution) (body : Reader) (hd : body.data = buf) :
    Res (fun (x : PrecState × Reader) (y : PrecSt × List UInt8) =>
        PrecRel buf x.1 y.1 ∧ y.2 = rbytes x.2 ∧ x.2.data = buf ∧ x.2.stop = body.stop)
      (JPEG2000.Tier2.Packet.readBody fp cs body) (Spec.Tier2.readBody sp cs.toList (rbytes body)) := by
  rw [readBody_eq, ← bind_pure (Spec.Tier2.readBody sp cs.toList (rbytes body))]
  refine Res.bind (bodyLoop_sim buf cs.toList fp.bands body sp hd hR.2) fun x y ⟨h1, h2, h3, h4, h5⟩ => ?_
  exact ⟨⟨by rw [h2, hR.1], h1⟩, h3, h4, h5⟩

end JPEG2000.Spec.Tier2Equiv
