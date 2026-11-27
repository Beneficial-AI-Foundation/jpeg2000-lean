import Spec.NativeResources

/-!
# Storage and iteration in the colour kernels (Plan.md §§3–5, 7, S3; T.800 Annex I)

Constructor equalities identify the inputs and arrays kept by lazy readers. Table sizes
are in entries, plane sizes in bytes, and iteration bounds in sample cells.
-/

namespace JPEG2000.Spec.ColorResources

open JPEG2000 JPEG2000.Color JPEG2000.Bytes

/-- All three plane representations read exactly their own grid, including an empty grid. -/
theorem plane_domain (p : SamplePlane) (i : Nat) :
    (p.get? i).isSome ↔ i < p.width * p.height := by
  cases p with
  | compact q => simp [SamplePlane.get?, SamplePlane.width, SamplePlane.height, Plane.get?]
  | view w h f => simp [SamplePlane.get?, SamplePlane.width, SamplePlane.height]
  | native c =>
    cases hs : c.storage <;>
      simp [SamplePlane.get?, SamplePlane.width, SamplePlane.height, CodestreamComponent.get?,
        JPEG2000.NativeOutput.OutputComponent.get?, hs, Plane.get?, WidePlane.get?]

/-- Construction of the retained pair of replication vectors. -/
def replicationIndices (ox oy w h : Nat) (c : Color.Channel) : Array Nat × Array Nat :=
  (chromaIndex ox 1 c.format.dx c.plane.width w, chromaIndex oy 1 c.format.dy c.plane.height h)

/-- Exact fresh storage or captures of the replication kernel. Full-resolution sources
share their plane. A compact copy uses both index vectors as scratch. -/
def Replicated (ox oy w h : Nat) (c : Color.Channel) (p : SamplePlane) : Prop :=
  if Image.atFullRes w h c then p = c.plane else
    let (xs, ys) := replicationIndices ox oy w h c
    xs.size = w ∧ ys.size = h ∧
      match c.plane.compact? with
      | some src => ∃ dst : Plane, p = .compact dst ∧ dst.data.size = 4 * (w*h) ∧
          dst = Image.upLoop src w xs ys (Plane.zero w h) 0 (w*h)
      | none => p = .view w h fun i =>
          (c.plane.get? (ys.getD (i/w) 0 * c.plane.width + xs.getD (i%w) 0)).getD 0

/-- The checked up-sampler either borrows its input, copies its raster, or captures the
input plus vectors of the two axis lengths, including when the area is zero. -/
theorem upsample_resources {ox oy w h : Nat} {c : Color.Channel} {p : SamplePlane}
    (ok : Image.upsample ox oy w h c = .ok p) : Replicated ox oy w h c p := by
  have dims := Resources.upsample_dims ok
  unfold Image.upsample at ok
  unfold Replicated
  split <;> rename_i hf
  · simpa [hf, pure, Except.pure] using ok.symm
  · simp only [hf, Bool.false_eq_true, ↓reduceIte] at ok
    split at ok <;> try contradiction
    refine ⟨by simp [chromaIndex], by simp [chromaIndex], ?_⟩
    split <;> rename_i hs
    · simp only [hs, pure, Except.pure, Except.ok.injEq] at ok
      subst p
      exact ⟨_, rfl, by rw [Plane.size_eq]; exact congrArg (4 * ·) (congr (congrArg Nat.mul dims.1) dims.2), rfl⟩
    · simpa [hs, replicationIndices, pure, Except.pure] using ok.symm

/-- The five actual sYCC index arrays, in chroma-plane order followed by the optional
leading-zero count per row. -/
structure SyccIndices where
  /-- Cb column coordinates. -/
  cbx : Array Nat
  /-- Cb row coordinates. -/
  cby : Array Nat
  /-- Cr column coordinates. -/
  crx : Array Nat
  /-- Cr row coordinates. -/
  cry : Array Nat
  /-- Leading columns to fill with raw zero chroma. -/
  edge : Array Nat

/-- Build the index arrays at the luma resolution exactly as in the converter. -/
def syccIndices (ox oy : Nat) (y cb cr : Color.Channel) : SyccIndices :=
  let w := y.plane.width
  let h := y.plane.height
  ⟨chromaIndex ox y.format.dx cb.format.dx cb.plane.width w,
   chromaIndex oy y.format.dy cb.format.dy cb.plane.height h,
   chromaIndex ox y.format.dx cr.format.dx cr.plane.width w,
   chromaIndex oy y.format.dy cr.format.dy cr.plane.height h,
   zeroChromaCols ox oy w h y.format cb.format cr.format⟩

/-- The two column vectors and two row vectors have their exact axis lengths, and the
edge vector is empty or one entry per row. -/
theorem sycc_indices_size (ox oy : Nat) (y cb cr : Color.Channel) :
    let t := syccIndices ox oy y cb cr
    t.cbx.size = y.plane.width ∧ t.crx.size = y.plane.width ∧
    t.cby.size = y.plane.height ∧ t.cry.size = y.plane.height ∧
    (t.edge.size = 0 ∨ t.edge.size = y.plane.height) := by
  simp only [syccIndices, chromaIndex, Array.size_map, List.size_toArray, List.length_range,
    true_and, zeroChromaCols]
  split
  · split <;> first | exact Or.inl rfl | exact Or.inr (by simp)
  · exact Or.inl rfl

private theorem loop_dims (off upb : Int64) (w : Nat) (y cb cr : Plane)
    (xs ys us vs edge : Array Nat) : ∀ k (r g b : Plane) i,
    let q := syccLoop off upb w y cb cr xs ys us vs r g b i k edge
    q.1.width = r.width ∧ q.1.height = r.height ∧
    q.2.1.width = g.width ∧ q.2.1.height = g.height ∧
    q.2.2.width = b.width ∧ q.2.2.height = b.height
  | 0, _, _, _, _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | k+1, r, g, b, i => by
    simp only [syccLoop]
    by_cases hy : i < y.width*y.height <;> simp only [hy, ↓reduceDIte] <;> try simp only [and_self]
    by_cases hr : i < r.width*r.height <;> simp only [hr, ↓reduceDIte] <;> try simp only [and_self]
    by_cases hg : i < g.width*g.height <;> simp only [hg, ↓reduceDIte] <;> try simp only [and_self]
    by_cases hb : i < b.width*b.height <;> simp only [hb, ↓reduceDIte] <;> try simp only [and_self]
    exact loop_dims off upb w y cb cr xs ys us vs edge k _ _ _ _

private theorem loop_bytes (off upb : Int64) (w h : Nat) (y cb cr : Plane)
    (xs ys us vs edge : Array Nat) :
    let z := Plane.zero w h
    let q := syccLoop off upb w y cb cr xs ys us vs z z z 0 (w*h) edge
    q.1.data.size + q.2.1.data.size + q.2.2.data.size = 4 * (3*(w*h)) := by
  have d := loop_dims off upb w y cb cr xs ys us vs edge (w*h)
    (Plane.zero w h) (Plane.zero w h) (Plane.zero w h) 0
  obtain ⟨d1,d2,d3,d4,d5,d6⟩ := d
  dsimp only
  rw [Plane.size_eq, Plane.size_eq, Plane.size_eq, d1,d2,d3,d4,d5,d6]
  change 4*(w*h) + 4*(w*h) + 4*(w*h) = _
  omega

/-- Successful conversion charges three luma rasters. A compact result materializes
exactly three four-byte rasters. Lazy RGB captures all three source channels and the
same five arrays, whose extents are given by `sycc_indices_size`. -/
def SyccWithin (L : Limits) (ox oy : Nat) (y cb cr : Color.Channel)
    (q : Color.Channel × Color.Channel × Color.Channel) : Prop :=
  let w := y.plane.width
  let h := y.plane.height
  let p := y.format.depth
  let t := syccIndices ox oy y cb cr
  3 * (w*h) ≤ L.maxWorkSamples ∧
    ((∃ r g b : Plane, q.1.plane = .compact r ∧ q.2.1.plane = .compact g ∧
      q.2.2.plane = .compact b ∧ r.data.size + g.data.size + b.data.size = 4 * (3*(w*h))) ∨
    q = syccViews (Int64.ofNat (2^(p-1))) (Int64.ofNat (2^p-1)) w h y cb cr
      t.cbx t.cby t.crx t.cry t.edge {y.format with signed := false})

/-- Resource certificate for the actual converter, including mixed and palette sources. -/
theorem sycc_resources {L : Limits} {ox oy : Nat} {y cb cr : Color.Channel}
    {q : Color.Channel × Color.Channel × Color.Channel} (ok : syccToRgb L ox oy y cb cr = .ok q) :
    SyccWithin L ox oy y cb cr q := by
  simp only [syccToRgb] at ok
  split at ok <;> try contradiction
  split at ok <;> try contradiction
  split at ok <;> try contradiction
  obtain ⟨_, work, h⟩ := Tier2Equiv.bind_ok ok
  refine ⟨(Limits.check_eq_ok_iff ..).mp work, ?_⟩
  split at h
  · split at h
    · cases h
      exact .inl ⟨_, _, _, rfl, rfl, rfl, loop_bytes ..⟩
    · cases h; exact .inr rfl
  · cases h; exact .inr rfl

/-- Fresh plane backing contributed by one up-sampler call. Retained sources and Nat
index vectors are accounted for by the constructor equality in `Replicated`. -/
def replicaBytes (w h : Nat) (src : Color.Channel) (dst : JPEG2000.Channel) : Nat :=
  if Image.atFullRes w h src then 0 else
    match dst.plane with
    | .compact p => p.data.size
    | _ => 0

/-- Aggregate four-byte backing for replication, output loop length and the captured or
borrowed data at every output position, before channel selection. -/
def FullWithin (ox oy w h : Nat) (cs : Array Color.Channel) (ds : Array JPEG2000.Channel) : Prop :=
  ds.size = cs.size ∧
  (List.zipWith (replicaBytes w h) cs.toList ds.toList).sum ≤ 4 * Resources.upCells w h cs ∧
  w*h*ds.size ≤ Resources.channelBytes w h ds ∧
  Resources.channelBytes w h ds = (cs.toList.map fun c => w*h*Header.bytesPerSample c.format.depth).sum ∧
  ∀ i (hs : i < cs.size) (hd : i < ds.size), Replicated ox oy w h cs[i] ds[i].plane

private theorem replica_bound {ox oy w h : Nat} {c : Color.Channel} {d : JPEG2000.Channel}
    (ok : Resources.upsampleChannel ox oy w h c = .ok d) :
    Replicated ox oy w h c d.plane ∧ replicaBytes w h c d ≤
      4 * (if Image.atFullRes w h c then 0 else w*h) := by
  obtain ⟨p, hp, eq⟩ := Tier2Equiv.bind_ok ok
  cases eq
  have rep := upsample_resources hp
  refine ⟨rep, ?_⟩
  unfold replicaBytes
  split <;> rename_i hf
  · simp
  · simp only [Replicated, hf, Bool.false_eq_true, ↓reduceIte] at rep
    obtain ⟨_, _, rep⟩ := rep
    split at rep
    · obtain ⟨dst, rfl, size, _⟩ := rep
      exact Nat.le_of_eq size
    · rw [rep]; exact Nat.zero_le _

/-- The checked array map charges each new compact raster and gives the actual
up-sampler provenance at every position. -/
theorem replication_resources {ox oy w h : Nat} {cs : Array Color.Channel} {ds : Array JPEG2000.Channel}
    (ok : cs.mapM (Resources.upsampleChannel ox oy w h) = .ok ds) : FullWithin ox oy w h cs ds := by
  let cost (c : Color.Channel) := if Image.atFullRes w h c then 0 else w*h
  let declared (c : JPEG2000.Channel) := w*h*Header.bytesPerSample c.depth
  have go (xs : List Color.Channel) (ys : List JPEG2000.Channel)
      (ok : xs.mapM (Resources.upsampleChannel ox oy w h) = .ok ys) :
      ys.length = xs.length ∧ (List.zipWith (replicaBytes w h) xs ys).sum ≤ 4*(xs.map cost).sum ∧
      w*h*ys.length ≤ (ys.map declared).sum ∧
      (ys.map declared).sum = (xs.map fun c => w*h*Header.bytesPerSample c.format.depth).sum ∧
      ∀ i (h1 : i < xs.length) (h2 : i < ys.length), Replicated ox oy w h xs[i] ys[i].plane := by
    induction xs generalizing ys with
    | nil => cases ok; simp
    | cons a xs ih =>
      rw [List.mapM_cons] at ok
      obtain ⟨b, hb, ok⟩ := Tier2Equiv.bind_ok ok
      obtain ⟨bs, hbs, ok⟩ := Tier2Equiv.bind_ok ok
      cases ok
      obtain ⟨len, bound, bytes, same, rel⟩ := ih _ hbs
      have hc := replica_bound hb
      have hd : w*h ≤ declared b := by
        apply Nat.le_trans (Nat.le_of_eq (Nat.mul_one _).symm)
        apply Nat.mul_le_mul_left
        unfold Header.bytesPerSample
        split <;> (try split) <;> (try split) <;> decide
      have depth : b.depth = a.format.depth := by
        obtain ⟨p, _, eq⟩ := Tier2Equiv.bind_ok hb
        cases eq; rfl
      refine ⟨by simp [len], ?_, ?_, ?_, ?_⟩
      · simpa [cost, Nat.mul_add] using Nat.add_le_add hc.2 bound
      · simpa [Nat.mul_succ, Nat.add_comm] using Nat.add_le_add hd bytes
      · simp only [List.map_cons, List.sum_cons, same]; simp [declared, depth]
      · intro i h1 h2
        cases i with
        | zero => exact hc.1
        | succ i => exact rel i (by simpa using h1) (by simpa using h2)
  rw [Array.mapM_eq_mapM_toList] at ok
  cases hh : List.mapM (Resources.upsampleChannel ox oy w h) cs.toList with
  | error e => simp [hh, Functor.map, Except.map] at ok
  | ok ys =>
    rw [hh] at ok; cases ok
    simpa [FullWithin, Resources.upCells, Resources.channelBytes, cost, declared] using go _ _ hh

-- Non-square empty grids exercise each axis independently.
private def emptySource : Color.Channel := ⟨.view 0 0 (fun _ => 0), ⟨38, false, 2, 2⟩⟩

example : (replicationIndices 1 1 7 0 emptySource).1.size = 7 ∧
    (replicationIndices 1 1 7 0 emptySource).2.size = 0 := by simp [replicationIndices, chromaIndex]
example : (replicationIndices 1 1 0 5 emptySource).1.size = 0 ∧
    (replicationIndices 1 1 0 5 emptySource).2.size = 5 := by simp [replicationIndices, chromaIndex]
example : (zeroChromaCols 1 1 0 5 ⟨38,false,1,1⟩ ⟨38,false,2,2⟩ ⟨38,false,2,2⟩).size = 5 := by simp [zeroChromaCols]

private def emptyLuma (w h : Nat) : Color.Channel := ⟨.view w h (fun _ => 0), ⟨38, false, 1, 1⟩⟩

example : let t := syccIndices 1 1 (emptyLuma 0 5) emptySource emptySource
    t.cby.size + t.cry.size + t.edge.size = 15 ∧ t.cbx.size + t.crx.size = 0 := by
  simp [syccIndices, emptyLuma, emptySource, chromaIndex, zeroChromaCols, SamplePlane.width, SamplePlane.height]

example : let t := syccIndices 1 1 (emptyLuma 7 0) emptySource emptySource
    t.cbx.size + t.crx.size = 14 ∧ t.cby.size + t.cry.size + t.edge.size = 0 := by
  simp [syccIndices, emptyLuma, emptySource, chromaIndex, zeroChromaCols, SamplePlane.width, SamplePlane.height]

end JPEG2000.Spec.ColorResources
