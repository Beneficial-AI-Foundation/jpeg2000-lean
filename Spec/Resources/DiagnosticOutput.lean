import Spec.Resources.DiagnosticCost
import Spec.Resources.NativeCost

/-!
# Native output diagnostics (Plan.md §§3–5, 7, S3)

T.800 A.5.1, B.2, equations B-12 and B-14, and G.1. Trace allocation on
the reduced SIZ grids, then placement in the destination passed by the public
grid traversal. A compact G.1 preparation error survives in the trace when
the exact temporary succeeds. The cell loops themselves construct no messages.
-/

namespace JPEG2000.Spec.Resources.DiagnosticOutput

open JPEG2000.Bytes JPEG2000.Header JPEG2000.Marker JPEG2000.NativeOutput
open DiagnosticCost

/-- Common numeric bound for both aggregate proposals, the old component's
backing and declared bytes, G.1 operands and the three applicable limit fields. -/
def scalarCap (L : Limits) :=
  38 + L.maxDecompLevels + L.maxDecodedBytes + 16*L.maxWorkSamples +
    8*(L.maxComponents*L.maxImageArea)

/-- Each compact component can discard one G.1 message before its final check.
A mismatched component count can fail before any component is visited. -/
def writeCount (L : Limits) := 1 + 2*L.maxComponents

private theorem span (a b d : Nat) : cdiv b d - cdiv a d ≤ b-a := by
  cases d with
  | zero => simp [cdiv]
  | succ d =>
    have mult : b-a ≤ (b-a)*(d+1) := by rw [Nat.mul_succ]; omega
    have bound := Nat.div_le_div_right (c := d+1)
      (show b+(d+1)-1 ≤ (a+(d+1)-1)+(b-a)*(d+1) by omega)
    rw [Nat.add_mul_div_right _ _ (Nat.succ_pos d)] at bound
    exact Nat.sub_le_of_le_add (by simpa [cdiv,Nat.add_comm] using bound)

private theorem sampleBytes (depth : Nat) : bytesPerSample depth ≤ 8 := by
  unfold bytesPerSample
  grind

private theorem sumBound {α : Type} (xs : List α) (f : α → Nat) (n : Nat)
    (bound : ∀ x ∈ xs, f x ≤ n) : (xs.map f).sum ≤ xs.length*n := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have head := bound x (by simp)
    have tail := ih (fun y hy => bound y (by simp [hy]))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.succ_mul]
    omega

/-- Both proposed totals are bounded immediately after parsing, even when the
first allocation guard rejects. A component's declared bytes use its SIZ depth. -/
theorem proposed {L : Limits} {data : ByteArray} {h : Header}
    (parsed : Header.parse L data = .ok h) (red : Nat) :
    let rs := layout h.siz red
    cells rs ≤ L.maxComponents*L.maxImageArea ∧
    decodedBytes rs ≤ 8*(L.maxComponents*L.maxImageArea) := by
  let rs := layout h.siz red
  have size : rs.size ≤ L.maxComponents := by
    simpa [rs,layout,SIZ.csiz] using (HeaderWork.parse_storage parsed).2.1
  have area (x : Rect × Component) (mem : x ∈ rs.toList) : x.1.width*x.1.height ≤ L.maxImageArea := by
    obtain ⟨c,_,rfl⟩ := Array.mem_map.mp (show x ∈ layout h.siz red by simpa using mem)
    exact Nat.le_trans (Nat.mul_le_mul (Nat.le_trans (span ..) (span ..))
      (Nat.le_trans (span ..) (span ..))) (parse_within parsed).2.2.1.2.2.1
  have bytes (x : Rect × Component) (mem : x ∈ rs.toList) :
      x.1.width*x.1.height*bytesPerSample x.2.depth.toNat ≤ L.maxImageArea*8 :=
    Nat.mul_le_mul (area x mem) (sampleBytes _)
  change cells rs ≤ _ ∧ decodedBytes rs ≤ _
  unfold cells decodedBytes
  rw [array_foldl_sum _ (fun (x : Rect × Component) => x.1.width*x.1.height) (fun _ _ => rfl),
    array_foldl_sum _ (fun (x : Rect × Component) => x.1.width*x.1.height*bytesPerSample x.2.depth.toNat)
      (fun _ _ => rfl)]
  have a := sumBound rs.toList _ _ area
  have b := sumBound rs.toList _ _ bytes
  simp only [Array.length_toList] at a b
  exact ⟨Nat.le_trans a (Nat.mul_le_mul_right _ size), Nat.le_trans b (by
    simpa [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm] using Nat.mul_le_mul_right (L.maxImageArea*8) size)⟩

private def mapRows {α β : Type} {cap n : Nat} (xs : Array α)
    (f : (i : Nat) → α → i < xs.size → Except Error β)
    (each : ∀ i hi, Trace cap (f i xs[i] hi) n)
    (k j : Nat) (len : k+j = xs.size) (acc : Array β) :
    Trace cap (Array.mapFinIdxM.map xs f k j len acc) (n*k) := by
  match k with
  | 0 => exact doneTrace acc
  | k+1 =>
    rw [Array.mapFinIdxM.map,Nat.mul_succ]
    exact bindTrace (each j (by omega)) fun b _ => mapRows xs f each k (j+1) (by omega) (acc.push b)

private def malformed {α : Type} {cap : Nat} (s : String) (len : s.utf8ByteSize ≤ 128) :
    Trace cap (Except.error (.malformed (.at .decode) s) : Except Error α) 1 :=
  let m := Sigma.mk s (oneFixed (cap := cap) s len)
  ⟨[m],by simp,by intro e eq; cases eq; exact ⟨Nat.zero_le _,m,by simp,rfl⟩⟩

/-- One output component allocates its selected backing or reports the exact
fixed precision diagnostic. The parsed SIZ invariant selects the zero-event case. -/
def allocOneTrace (cap : Nat) (r : Rect) (c : Component) :
    Trace cap (allocOne r c) (if 1 ≤ c.depth.toNat ∧ c.depth.toNat ≤ 38 then 0 else 1) := by
  unfold allocOne
  by_cases hd : 1 ≤ c.depth.toNat ∧ c.depth.toNat ≤ 38
  · simp only [dite_eq_left hd,ite_eq_left hd]
    split <;> exact doneTrace _
  · simp only [dite_eq_right hd,ite_eq_right hd]
    exact malformed _ (by decide)

/-- Trace the actual allocator after public reduction admission and parsing.
Parsed precision makes every reached zero-backing allocation message-free. -/
def allocationTrace {L : Limits} {data : ByteArray} {h : Header} {red : Nat}
    (admitted : red ≤ L.maxDecompLevels) (parsed : Header.parse L data = .ok h) :
    Trace (scalarCap L) (allocOutput L h.siz red) 0 := by
  obtain ⟨wc,bc⟩ := proposed parsed red
  unfold allocOutput
  apply bindTrace (checkedTrace _ _ _ _ (Nat.zero_le _) (by unfold scalarCap; omega))
  intro _ _
  apply bindTrace (checkedTrace _ _ _ _ (Nat.zero_le _) (by unfold scalarCap; omega))
  intro _ _
  apply bindTrace (checkedTrace _ _ _ _ (Nat.zero_le _) (by unfold scalarCap; omega))
  intro _ _
  unfold Array.mapFinIdxM
  apply widen (j := 0*(layout h.siz red).size) _ (by simp)
  apply mapRows
  intro i hi
  have validIndex : i < h.siz.components.size := by simpa [layout] using hi
  have mem := Array.getElem_mem validIndex
  have precision := NativePlacement.parsed_depth parsed _ mem
  simp only [layout,Array.getElem_map]
  simpa only [ite_eq_left precision] using allocOneTrace (scalarCap L) _ h.siz.components[i]

private def unsupported {α : Type} {cap : Nat} (stage : Stage) {s : String} (b : Built cap s) :
    Trace cap (Except.error (.unsupported (.at stage) s) : Except Error α) 1 :=
  ⟨[⟨s,b⟩],by simp,by intro e eq; cases eq; exact ⟨Nat.zero_le _,⟨s,b⟩,by simp,rfl⟩⟩

private def dcTrace {cap depth F : Nat} (signed : Bool) (hd : depth ≤ cap) (hf : F ≤ cap) :
    Trace cap (JPEG2000.MCT.DcShift.make signed depth F) 1 := by
  unfold JPEG2000.MCT.DcShift.make
  dsimp only
  split
  · exact doneTrace _
  · apply unsupported .mct
    apply closeExpr (catExpr (catExpr (catExpr (catExpr (catExpr (catExpr
      (litExpr _ "component range (signed ") (litExpr _ (toString signed))) (litExpr _ ", "))
      (decExpr hd)) (litExpr _ " bits, ")) (decExpr hf)) (litExpr _ " fractional bits) exceeds Int32"))
    · cases signed <;> decide
    · decide

private def finishTrace {cap : Nat} (r : Rect) (c : Component) (depth) (b : Storage) :
    Trace cap (finish r c depth b) 1 := by
  unfold finish
  split
  · exact doneTrace _
  · exact malformed _ (by decide)

private def wideTrace {cap : Nat} (L : Limits) (p : WidePlane) (src : Source) (ox oy F : Nat)
    (work : p.width*p.height ≤ cap) (bytes : p.width*p.height*bytesPerSample p.range.depth ≤ cap) :
    Trace cap (JPEG2000.WideOutput.blit L (.at .decode) p src.width src.height ox oy F src.read) 1 := by
  unfold JPEG2000.WideOutput.blit
  apply bindTrace (checkedTrace _ _ _ _ (Nat.zero_le _) work)
  intro _ _
  apply bindTrace (checkedTrace _ _ _ _ (Nat.zero_le _) bytes)
  intro _ _
  split
  · exact doneTrace _
  · exact malformed _ (by decide)

private theorem fillShape {N : Nat} (f : Fin N → Int32) (n : Nat) (hn : n ≤ N)
    (p : JPEG2000.DWT53.Buf N) :
    (fill f n hn p).1.width = p.1.width ∧ (fill f n hn p).1.height = p.1.height := by
  induction n generalizing p with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih => exact ih _ _

private theorem mapShape {N : Nat} (f : Int32 → Int32) (p : JPEG2000.DWT53.Buf N) (i : Nat) :
    (JPEG2000.MCT.map1 f p i).1.width = p.1.width ∧
    (JPEG2000.MCT.map1 f p i).1.height = p.1.height := by
  rw [JPEG2000.MCT.map1]
  split
  · exact mapShape f _ (i+1)
  · exact ⟨rfl,rfl⟩
termination_by N-i

private theorem narrowShape (s : Source) (r : NativeSampleRange) (fits) (F : Nat) :
    let p := narrowTile s r fits F
    p.width = s.width ∧ p.height = s.height := by
  have ex (src : Source) : (exactTile src r fits F).width = src.width ∧
      (exactTile src r fits F).height = src.height := fillShape ..
  cases s with
  | exact => exact ex _
  | plane p =>
    unfold narrowTile
    dsimp only
    split
    · split <;> exact mapShape ..
    · exact ex _

-- In the plane case the checked G.1 constructor is evaluated even when its
-- error is discarded in favour of exactTile. An exact source skips it.
private def narrowBlitTrace {cap : Nat} (p : Plane) (s : Source) (r : NativeSampleRange) (fits)
    (ox oy F : Nat) (hd : r.depth ≤ cap) (hf : F ≤ cap)
    (hx : ox+s.width ≤ p.width) (hy : oy+s.height ≤ p.height) :
    Trace cap (Assemble.blit p (narrowTile s r fits F) ox oy) 1 := by
  have dims := narrowShape s r fits F
  have fit : ox+(narrowTile s r fits F).width ≤ p.width ∧
      oy+(narrowTile s r fits F).height ≤ p.height := by simpa only [dims.1,dims.2] using And.intro hx hy
  simp only [Assemble.blit,fit]
  cases s with
  | exact => exact doneTrace _
  | plane => exact includeTrace (dcTrace r.signed hd hf) (doneTrace (k := 0) _)

/-- Both destination guards use the full old component. A malformed source
shape fails before conversion. A contained compact tile preserves its shape
through ordinary G.1 or the exact fill, so its blitter's containment test passes. -/
def componentTrace {cap : Nat} (L : Limits) (dst : OutputComponent) (r : Rect) (F : Nat)
    (src : Source) (work : dst.rect.width*dst.rect.height ≤ cap)
    (bytes : dst.rect.width*dst.rect.height*bytesPerSample dst.format.depth.toNat ≤ cap)
    (depth : dst.format.depth.toNat ≤ cap) (frac : F ≤ cap) :
    Trace cap (writeComponent L dst r F src) 2 := by
  cases geom : fitsTile dst.rect r src with
  | false =>
    rw [Spec.NativeOutput.writeComponent_badGeometry _ _ _ _ _ geom]
    exact widen (malformed _ (by decide)) (by decide)
  | true =>
    cases dst with
    | mk d c hd storage valid =>
      cases storage with
      | wide p =>
        simp only [Storage.matches,Bool.and_eq_true,beq_iff_eq] at valid
        obtain ⟨⟨⟨⟨hw,hh⟩,_⟩,hp⟩,_⟩ := valid
        simp only [writeComponent,geom,Bool.not_true,Bool.false_eq_true,↓reduceIte]
        apply bindTrace (wideTrace L p src _ _ F (by simpa only [hw,hh] using work)
          (by simpa only [hw,hh,hp] using bytes))
        exact fun q _ => finishTrace _ _ _ (.wide q)
      | narrow p =>
        obtain ⟨⟨hw,hh⟩,hc⟩ : (p.width = d.width ∧ p.height = d.height) ∧ compact c := by
          simpa only [Storage.matches,Bool.and_eq_true,beq_iff_eq] using valid
        simp only [writeComponent,geom,Bool.not_true,Bool.false_eq_true,↓reduceIte]
        apply bindTrace (checkedTrace _ _ _ _ (Nat.zero_le _) work)
        intro _ _
        apply bindTrace (checkedTrace _ _ _ _ (Nat.zero_le _) bytes)
        intro _ _
        let range : NativeSampleRange := ⟨_,c.signed,hd,_,_,rfl,rfl⟩
        have fits : -2147483648 ≤ range.lo ∧ range.hi ≤ 2147483647 := by simpa [compact] using hc
        have ge : fitsTile d r src := geom
        simp only [fitsTile,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at ge
        apply bindTrace (narrowBlitTrace p src range fits _ _ F depth frac
          (by rw [hw]; unfold Rect.width at *; omega) (by rw [hh]; unfold Rect.height at *; omega))
        exact fun q _ => finishTrace _ _ _ (.narrow q)

private theorem termBound {α : Type} (f : α → Nat) {xs : List α} {a : α} (ha : a ∈ xs) :
    f a ≤ (xs.map f).sum := by
  induction xs with
  | nil => cases ha
  | cons x xs ih =>
    simp only [List.mem_cons] at ha
    simp only [List.map_cons,List.sum_cons]
    rcases ha with rfl | ha
    · omega
    · have := ih ha; omega

/-- Every old component of the current destination, including components beyond
a failing callback, obeys uniform bounds on both values passed to the blitters. -/
theorem destinationRow {L : Limits} {dst : Array OutputComponent}
    (backing : (dst.toList.map Spec.NativeOutput.backingBytes).sum ≤ 8*L.maxWorkSamples) :
    ∀ d ∈ dst, d.rect.width*d.rect.height ≤ 2*L.maxWorkSamples ∧
      d.rect.width*d.rect.height*bytesPerSample d.format.depth.toNat ≤ 16*L.maxWorkSamples := by
  intro d hd
  have one := Nat.le_trans (termBound Spec.NativeOutput.backingBytes (by simpa using hd)) backing
  rw [Spec.NativeOutput.backing_size] at one
  have cells : d.rect.width*d.rect.height ≤ 2*L.maxWorkSamples := by
    split at one <;> omega
  have bytes := Nat.mul_le_mul cells (sampleBytes d.format.depth.toNat)
  exact ⟨cells,by omega⟩

private theorem fracBound (s : SIZ) (mct : Bool) (i : Nat) : Assemble.fracBitsOf s mct i ≤ 26 := by
  unfold Assemble.fracBitsOf
  split <;> exact Nat.sub_le ..

/-- Trace a native tile callback given the retained backing bound. The complete
old component row is available at entry, including when this write is rejected.
The public fractional scale comes from the effective SIZ/MCT selection. -/
def writeTrace {L : Limits} {data : ByteArray} {h : Header} {red : Nat}
    (admitted : red ≤ L.maxDecompLevels) (parsed : Header.parse L data = .ok h)
    (dst : Array OutputComponent)
    (backing : (dst.toList.map Spec.NativeOutput.backingBytes).sum ≤ 8*L.maxWorkSamples)
    (tile : JPEG2000.Decode.CenteredTile) :
    Trace (scalarCap L) (writeTile L h.siz red tile.layout tile.coding dst tile.sources) (writeCount L) := by
  unfold writeTile
  apply bindTrace (checkedTrace _ _ _ _ (Nat.zero_le _) (by unfold scalarCap; omega))
  intro _ _
  split
  · rename_i counts
    have count : dst.size ≤ L.maxComponents := by
      rw [counts.1]; exact (HeaderWork.parse_storage parsed).2.1
    unfold Array.mapFinIdxM
    apply widen (j := 2*dst.size) _ (by change _ ≤ 1+2*L.maxComponents; omega)
    apply mapRows
    intro i hi
    dsimp only
    split
    · exact widen (malformed _ (by decide)) (by decide)
    · split
      · exact widen (unsupported .decode (oneFixed _ (by decide))) (by decide)
      · obtain ⟨wc,bc⟩ := destinationRow backing dst[i] (Array.getElem_mem ..)
        have depth := dst[i].precision.2
        apply componentTrace <;> unfold scalarCap
        · omega
        · omega
        · omega
        · split
          · exact Nat.zero_le _
          · have := fracBound h.siz (tile.coding.mctApplies h.siz) i; omega
  · exact widen (malformed _ (by decide)) (by change 1 ≤ 1+2*L.maxComponents; omega)

private theorem prepared {L : Limits} {data : ByteArray} {red : Nat} {h dst}
    (entry : PublicPacketWork.prepareTiles L data red = .ok (h,dst)) :
    red ≤ L.maxDecompLevels ∧ Header.parse L data = .ok h := by
  unfold PublicPacketWork.prepareTiles at entry
  obtain ⟨u,checked,tail⟩ := Tier2Equiv.bind_ok entry
  obtain ⟨_,parsed,tail⟩ := Tier2Equiv.bind_ok tail
  obtain ⟨_,_,ret⟩ := Tier2Equiv.bind_ok tail
  cases ret
  cases u
  exact ⟨(Limits.check_eq_ok_iff ..).1 checked,parsed⟩

/-- A parsed allocator rejects exactly at the first excessive aggregate.
The error records the full proposal and the caller's original limit. -/
theorem allocation_refusal {L : Limits} {data : ByteArray} {h : Header} {red : Nat}
    (admitted : red ≤ L.maxDecompLevels) (parsed : Header.parse L data = .ok h) (e : Error) :
    let rs := layout h.siz red
    allocOutput L h.siz red = .error e ↔
      (L.maxWorkSamples < cells rs ∧ e = .limitExceeded (.at .decode) .workSamples
        (cells rs) L.maxWorkSamples) ∨
      (cells rs ≤ L.maxWorkSamples ∧ L.maxDecodedBytes < decodedBytes rs ∧
        e = .limitExceeded (.at .decode) .decodedBytes (decodedBytes rs) L.maxDecodedBytes) := by
  dsimp only
  by_cases work : cells (layout h.siz red) ≤ L.maxWorkSamples
  · by_cases bytes : decodedBytes (layout h.siz red) ≤ L.maxDecodedBytes
    · obtain ⟨dst,ok⟩ := (NativeCost.allocation_work parsed red).2 admitted work bytes
      simp [ok,Nat.not_lt_of_ge work,Nat.not_lt_of_ge bytes]
    · simp [allocOutput,Limits.check,Limits.checkLe,Limits.bound,admitted,work,bytes,
        Nat.not_lt_of_ge work,Nat.lt_of_not_ge bytes,bind,Except.bind,eq_comm]
  · simp [allocOutput,Limits.check,Limits.checkLe,Limits.bound,admitted,work,
      Nat.lt_of_not_ge work,bind,Except.bind,eq_comm]

/-- The public allocator emits zero text events. On refusal its typed diagnostic
reaches both APIs before any tile visit, with its original value and bound. -/
theorem public_allocation {L : Limits} {data : ByteArray} {opts : DecodeOptions} {h : Header}
    (admitted : opts.reduce ≤ L.maxDecompLevels) (parsed : Header.parse L data = .ok h) :
    let z := allocationTrace admitted parsed
    z.messages = [] ∧ ∀ e, allocOutput L h.siz opts.reduce = .error e →
      PublicPacketWork.measure L data opts.reduce = ([],.error e) ∧
      decodeCodestream L data opts.reduce = .error e ∧ JPEG2000.decode L data opts = .error e ∧
      storedPayload false e ≤ 6 + Text.byteBound (scalarCap L) 128 24 + 2*bits (scalarCap L) := by
  let z := allocationTrace admitted parsed
  refine ⟨List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero z.countBound),?_⟩
  intro e bad
  have hc : L.check JPEG2000.Decode.loc .decompLevels opts.reduce = .ok () :=
    (Limits.check_eq_ok_iff ..).2 admitted
  have entry : PublicPacketWork.prepareTiles L data opts.reduce = .error e := by
    simp [PublicPacketWork.prepareTiles,hc,parsed,bad,bind,Except.bind]
  obtain ⟨empty,raw,display⟩ := PublicPacketWork.admission_error entry
  exact ⟨empty,raw,display,trace_retained z bad⟩

open PacketTraversal (TileVisit gridPrefix)

/-- The production placement callback, with the argument order of the grid fold. -/
abbrev writeAt (L : Limits) (h : Header) (red : Nat) (dst : Array OutputComponent)
    (tile : JPEG2000.Decode.CenteredTile) :=
  writeTile L h.siz red tile.layout tile.coding dst tile.sources

/-- The destination immediately before the visited tile, with its actual pass
and tile-part cursors and accumulated saturation. -/
abbrev Before {L : Limits} {h : Header} {data : ByteArray} {red : Nat}
    (initial : Array OutputComponent) (idx : Array (Array Nat)) (pre : List TileVisit)
    (v : TileVisit) (dst : Array OutputComponent) (sat : Nat) :=
  gridPrefix L h data initial (JPEG2000.Decode.centeredTile L h data red) (·.saturated)
    (writeAt L h red) idx pre.length = .ok (dst,v.passesBefore,sat,v.cursor)

section

variable {L : Limits} {data : ByteArray} {red : Nat} {pre : List TileVisit} {v : TileVisit}
    {tail : List TileVisit} (visited : (PublicPacketWork.measure L data red).1 = pre ++ v::tail)
    {h : Header} {initial dst : Array OutputComponent} {idx : Array (Array Nat)} {sat : Nat}
    (entry : PublicPacketWork.prepareTiles L data red = .ok (h,initial))
    (index : NativeCost.ranks L h = .ok idx)
    (before : Before (L := L) (h := h) (data := data) (red := red) initial idx pre v dst sat)

include visited entry index before in
private theorem retained : (dst.toList.map Spec.NativeOutput.backingBytes).sum ≤ 8*L.maxWorkSamples := by
  obtain ⟨h',ini',idx',dst',sat',entry',index',before',_,_,cap⟩ :=
    NativeCost.destination_storage L data red visited
  rw [entry] at entry'
  cases entry'
  rw [index] at index'
  cases index'
  unfold Before at before
  rw [before] at before'
  cases before'
  exact cap

/-- Trace at the exact destination named by the production prefix. The
centered input is an explicit parameter, so the callback can be used directly
in a fold continuation before inspecting its result. -/
def publicWriteTrace (tile : JPEG2000.Decode.CenteredTile) :
    Trace (scalarCap L) (writeAt L h red dst tile) (writeCount L) :=
  writeTrace (prepared entry).1 (prepared entry).2 dst (retained visited entry index before) tile

end

/-- Every visited tile supplies its old destination, including a failing write.
Packet selection and successful centered reconstruction identify the actual
argument of the callback. Its expression work, storage and returned payload
are bounded without assuming the write or final decode succeeds. -/
theorem public_writes {L : Limits} {data : ByteArray} {red : Nat} {pre v tail}
    (visited : (PublicPacketWork.measure L data red).1 = pre ++ v::tail) :
    ∃ h initial idx dst sat, ∃ (entry : PublicPacketWork.prepareTiles L data red = .ok (h,initial))
      (index : NativeCost.ranks L h = .ok idx)
      (before : Before (L := L) (h := h) (data := data) (red := red) initial idx pre v dst sat),
      v.tile = pre.length ∧
      (∀ d ∈ dst, d.rect.width*d.rect.height ≤ 2*L.maxWorkSamples ∧
        d.rect.width*d.rect.height*bytesPerSample d.format.depth.toNat ≤ 16*L.maxWorkSamples) ∧
      ∀ a tile, SegmentHistory.packetStore L h data idx v.tile v.cursor v.passesBefore = .ok a →
        JPEG2000.Decode.centeredTile L h data red v.tile a = .ok tile →
        let z := publicWriteTrace visited entry index before tile
        (z.messages.map (fun m => m.2.tree.work)).sum ≤ writeCount L*Text.workBound (scalarCap L) 128 24 ∧
        (z.messages.map (fun m => m.2.tree.storage)).sum ≤ writeCount L*Text.workBound (scalarCap L) 128 24 ∧
        ∀ e, writeAt L h red dst tile = .error e →
          storedPayload false e ≤ 6 + Text.byteBound (scalarCap L) 128 24 + 2*bits (scalarCap L) := by
  obtain ⟨h,initial,idx,dst,sat,entry,index,before,number,_,bound⟩ :=
    NativeCost.destination_storage L data red visited
  refine ⟨h,initial,idx,dst,sat,entry,index,before,number,destinationRow bound,?_⟩
  intro a tile _ _
  let z := publicWriteTrace visited entry index before tile
  exact ⟨(trace_cost z).1,trace_storage z,fun _ bad => trace_retained z bad⟩

end JPEG2000.Spec.Resources.DiagnosticOutput
