import Spec.ColorResources

/-!
# Sample access through returned display views (Plan.md §§3–5, 7, S3; T.800 Annex I)

A reader describes the constructors of a particular production plane. Its charge follows
one lookup through the retained arrays down to physical sample bytes. Odd-origin sYCC
edges skip both chroma lookups. A second projection of the same pixel pays again.
-/

namespace JPEG2000.Spec.ColorResources.DisplayPrefix

open JPEG2000 JPEG2000.Color JPEG2000.Bytes JPEG2000.Header

/-- Select one of the three actual projection closures. -/
def projection (q : Color.Channel × Color.Channel × Color.Channel) : Fin 3 → SamplePlane
  | 0 => q.1.plane
  | 1 => q.2.1.plane
  | 2 => q.2.2.plane

/-- A derivation of the production reader. There is deliberately no arbitrary view leaf. -/
inductive Reader : SamplePlane → Type where
  | compact (p : Plane) : Reader (.compact p)
  | native (c : JPEG2000.NativeOutput.OutputComponent) : Reader (.native c)
  | indexed {p : SamplePlane} (tbl : Array Int) (src : Reader p) : Reader (indexedPlane tbl p)
  | replica {p : SamplePlane} (w h : Nat) (xs ys : Array Nat) (src : Reader p) :
    Reader (.view w h fun i => (p.get? (ys.getD (i/w) 0 * p.width + xs.getD (i%w) 0)).getD 0)
  | rgb (off upb : Int64) (w h : Nat) (y cb cr : Color.Channel) (t : SyccIndices)
      (fmt : Format) (k : Fin 3) (luma : Reader y.plane) (blue : Reader cb.plane)
      (red : Reader cr.plane) :
    Reader (projection (syccViews off upb w h y cb cr t.cbx t.cby t.crx t.cry t.edge fmt) k)

/-- Domain tests, sample bytes, table accesses and pixel kernels for one indexed read.
Each successful narrow/wide leaf reads four/eight bytes, respectively. -/
def Reader.measured {p : SamplePlane} (r : Reader p) (i : Nat) : Option Int × Nat :=
  match r with
  | .compact q => ((q.get? i).map Int32.toInt, 1 + if i < q.width*q.height then 4 else 0)
  | .native c => (c.get? i, 1 + match c.storage with
    | .narrow q => if i < q.width*q.height then 4 else 0
    | .wide q => if i < q.width*q.height then 8 else 0)
  | .indexed (p := q) tbl src => if i < q.width*q.height then
      let (index, cost) := src.measured i
      (some (tbl.getD (min (index.getD 0).toNat (tbl.size-1)) 0), 2 + cost)
    else (none,1)
  | .replica (p := q) w h xs ys src => if i < w*h then
      let (v,cost) := src.measured (ys.getD (i/w) 0 * q.width + xs.getD (i%w) 0)
      (some (v.getD 0),3+cost)
    else (none,1)
  | .rgb off upb w h _ cb cr t _ k luma blue red => if i < w*h then
      let x := i%w
      let row := i/w
      let l := luma.measured i
      let chroma := if x < t.edge.getD row 0 then (0,0,0) else
        let b := blue.measured (t.cby.getD row 0 * cb.plane.width + t.cbx.getD x 0)
        let r := red.measured (t.cry.getD row 0 * cr.plane.width + t.crx.getD x 0)
        ((b.1.getD 0).toInt64,(r.1.getD 0).toInt64,4+b.2+r.2)
      let rgb := syccPixel off upb (l.1.getD 0).toInt64 chroma.1 chroma.2.1
      (some ((match k with | 0 => rgb.1 | 1 => rgb.2.1 | 2 => rgb.2.2).toInt),
        4+l.2+chroma.2.2)
    else (none,1)

/-- Erasing the recursive charge gives the production sample at every index. In a
mixed-depth projection this includes the exact subsampled lookup and zero-chroma edge. -/
theorem read_value {p : SamplePlane} (r : Reader p) (i : Nat) : (r.measured i).1 = p.get? i := by
  induction r generalizing i with
  | compact q => rfl
  | native c => rfl
  | indexed tbl src ih =>
    simp only [Reader.measured,indexedPlane,SamplePlane.get?]
    split <;> simp [ih] <;> rfl
  | replica w h xs ys src ih =>
    simp only [Reader.measured,SamplePlane.get?]
    split <;> simp [ih] <;> rfl
  | rgb off upb w h y cb cr t fmt k l b r hl hb hr =>
    match k with
    | 0 | 1 | 2 =>
      simp only [Reader.measured,projection,syccViews,SamplePlane.get?]
      split <;> first | rfl | (split <;> simp [hl,hb,hr] <;> rfl)

/-- Work component of the value-preserving sample meter. -/
def Reader.work {p : SamplePlane} (r : Reader p) (i : Nat) : Nat := (r.measured i).2

/-- One derivation handles all sample indices including out-of-domain defaults. -/
def ReadsWithin (p : SamplePlane) (n : Nat) : Prop := ∃ r : Reader p, ∀ i, r.work i ≤ n

private theorem weaken {p a b} (h : ReadsWithin p a) (le : a ≤ b) : ReadsWithin p b := by
  obtain ⟨r, hr⟩ := h
  exact ⟨r, fun i => Nat.le_trans (hr i) le⟩

private theorem compact (p : Plane) : ReadsWithin (.compact p) 5 := by
  refine ⟨.compact p, fun i => ?_⟩
  simp only [Reader.work, Reader.measured]; split <;> decide

private theorem raw (d : CodestreamImage) (c : Color.Channel) (mem : c ∈ rawChannels d) :
    ReadsWithin c.plane 9 := by
  obtain ⟨dc, _, rfl⟩ := Array.mem_map.mp mem
  cases dc with
  | compact q => exact weaken (compact q.plane) (by decide)
  | native q =>
    refine ⟨.native q, fun i => ?_⟩
    simp only [Reader.work, Reader.measured]
    split <;> split <;> decide

private theorem mapped {L d m cs} (h : MappingWithin L m (rawChannels d) cs)
    (c : Color.Channel) (mem : c ∈ cs) : ReadsWithin c.plane 11 := by
  obtain ⟨xs, eq, all, _⟩ := h.trace
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp (eq.symm ▸ Array.mem_def.mp mem)
  cases all x hx with
  | direct src i atIndex => exact weaken (raw d _ (Array.mem_of_getElem? atIndex)) (by decide)
  | palette src ch i atIndex p col hp rows width height storage =>
    rcases storage with ⟨q,eq,_⟩ | eq
    · rw [eq]; exact weaken (compact _) (by decide)
    · rw [eq]
      obtain ⟨r,hr⟩ := raw d _ (Array.mem_of_getElem? atIndex)
      refine ⟨.indexed _ r, fun i => ?_⟩
      simp only [Reader.work, Reader.measured]
      have h := hr i
      unfold Reader.work at h
      split <;> dsimp only <;> omega

private theorem convertedReads {L ox oy y cb cr q}
    (h : SyccWithin L ox oy y cb cr q) (hy : ReadsWithin y.plane 11)
    (hb : ReadsWithin cb.plane 11) (hr : ReadsWithin cr.plane 11) :
    ∀ k, ReadsWithin (projection q k) 41 := by
  intro k
  obtain ⟨_,⟨r,g,b,er,eg,eb,_⟩ | rfl⟩ := h
  · match k with
    | 0 => rw [projection, er]; exact weaken (compact _) (by decide)
    | 1 => rw [projection, eg]; exact weaken (compact _) (by decide)
    | 2 => rw [projection, eb]; exact weaken (compact _) (by decide)
  · obtain ⟨l,hl⟩ := hy
    obtain ⟨b,hb⟩ := hb
    obtain ⟨r,hr⟩ := hr
    refine ⟨.rgb _ _ _ _ _ _ _ (syccIndices ox oy y cb cr) _ k l b r, fun i => ?_⟩
    simp only [Reader.work,Reader.measured]
    split
    · dsimp only
      split
      · have h := hl i
        unfold Reader.work at h
        dsimp only; omega
      · dsimp only
        exact Nat.add_le_add (Nat.add_le_add_left (hl i) 4)
          (Nat.add_le_add (Nat.add_le_add_left (hb _) 4) (hr _))
    · decide

private theorem channels {L d m cs active cols ox oy out bytes slots}
    (hm : MappingWithin L m (rawChannels d) cs)
    (hc : Converted L active cols ox oy cs out bytes slots) :
    ∀ c ∈ out, ReadsWithin c.plane 41 := by
  intro c mem
  rcases hc with ⟨_,rfl,_,_⟩ | ⟨iy,ib,ir,y,cb,cr,q,_,_,ey,eb,er,_,_,_,h,_,_,rfl⟩
  · exact weaken (mapped hm _ mem) (by decide)
  have pq := convertedReads h (mapped hm _ (Array.mem_of_getElem? ey))
    (mapped hm _ (Array.mem_of_getElem? eb)) (mapped hm _ (Array.mem_of_getElem? er))
  rcases Array.mem_or_eq_of_mem_setIfInBounds mem with mem | rfl
  · rcases Array.mem_or_eq_of_mem_setIfInBounds mem with mem | rfl
    · rcases Array.mem_or_eq_of_mem_setIfInBounds mem with mem | rfl
      · exact weaken (mapped hm _ mem) (by decide)
      · exact pq 0
    · exact pq 1
  · exact pq 2

private theorem replicated {ox oy w h c p} (rep : Replicated ox oy w h c p)
    (src : ReadsWithin c.plane 41) : ReadsWithin p 44 := by
  unfold Replicated at rep
  split at rep
  · exact rep ▸ weaken src (by decide)
  · obtain ⟨_,_,rep⟩ := rep
    split at rep
    · obtain ⟨q,rfl,_⟩ := rep
      exact weaken (compact _) (by decide)
    · rw [rep]
      obtain ⟨r,hr⟩ := src
      refine ⟨.replica _ _ _ _ r, fun i => ?_⟩
      simp only [Reader.work,Reader.measured]
      split
      · exact Nat.add_le_add_left (hr _) 3
      · decide

/-- Actual selected channels, including alpha and other channels, admit bounded sample
reads through all retained production closures. -/
theorem channel_reads {L data opts img} (ok : JPEG2000.decode L data opts = .ok img)
    (c : JPEG2000.Channel) (sel : c ∈ img.channels ∨ img.alpha = some c ∨ c ∈ img.other) :
    ReadsWithin c.plane 44 := by
  obtain ⟨_,_,_,cs,full,_,_,_,_,_,hm,hc,_,_,_,_,_,_,_,_,_,_,rep,_,_,cols,alpha,other,_⟩ :=
    (decode_resources ok).colour
  have mem := sel.elim (cols c) (fun h => h.elim (alpha c) (other c))
  obtain ⟨i,hi,rfl⟩ := Array.mem_iff_getElem.mp mem
  have hj : i < cs.size := rep.1 ▸ hi
  exact replicated (rep.2.2.2.2 i hj hi) (channels hm hc _ (Array.getElem_mem ..))

end JPEG2000.Spec.ColorResources.DisplayPrefix
