import JPEG2000.TileDispatch

/-!
# Loop domains in native colour reconstruction and placement

Plan.md §§3–5 and 7, T.800 B.2–3 and G.1–3. A visit is an iteration of a raster
kernel. The compact eligibility scan and row packer include the failing cell.
The row blitter has an outer iteration even when the inner copy is empty.
-/

namespace JPEG2000.Spec.Resources.TileColorPlacement

open JPEG2000.Bytes JPEG2000.Header JPEG2000.NativeOutput
open JPEG2000.DWT53 (Buf)
open JPEG2000.ReversibleDispatch (fitsRGB rgbAt)
open JPEG2000.IrreversibleDispatch (packRows)

/-- Reverse-raster short-circuit test, counting each predicate call. -/
def scan (p : Nat → Bool) : Nat → Bool × Nat
  | 0 => (true, 0)
  | n+1 => if p n then let t := scan p n; (t.1, t.2+1) else (false, 1)

/-- The pre-RCT scan charges three predecessor reads for each tested triple. -/
theorem colourFits_work (y cb cr : Source) (n : Nat) :
    let m := scan (fun i => fitsRGB (rgbAt y cb cr i)) n
    m.1 = JPEG2000.ReversibleDispatch.colourFits y cb cr n ∧ 3*m.2 ≤ 3*n := by
  induction n with
  | zero => exact ⟨rfl, Nat.le_refl _⟩
  | succ n ih =>
    dsimp only at ih ⊢
    cases hp : fitsRGB (rgbAt y cb cr n) <;>
      simp [scan, JPEG2000.ReversibleDispatch.colourFits, hp, ih.1] <;> omega

/-- An exact view evaluates one inverse RCT on the three retained reads at its index. -/
theorem view_reads (y cb cr : Source) :
    let v := JPEG2000.ReversibleDispatch.views y cb cr
    (∀ i, v.1.read i = (rgbAt y cb cr i.val).1) ∧
    (∀ i, v.2.1.read i = (rgbAt y cb cr i.val).2.1) ∧
    (∀ i, v.2.2.read i = (rgbAt y cb cr i.val).2.2) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- Number of ICT row evaluations, inclusive of the first overflowing value. -/
def packVisits (f : Nat → Int) : Nat → Nat
  | 0 => 0
  | n+1 => if (f n).toInt32.toInt = f n then packVisits f n + 1 else 1

/-- The compact packer's visited suffix equals the full fuel on success. On
failure it includes the comparison on the cell that could not be stored. -/
theorem packRows_work {N : Nat} (f : Nat → Int) (n : Nat) (hn : n ≤ N) (p : Buf N) :
    packVisits f n ≤ n ∧
    (∀ q, packRows f n hn p = some q → packVisits f n = n) ∧
    (packRows f n hn p = none →
      ∃ j, j < n ∧ packVisits f n = n-j ∧ (f j).toInt32.toInt ≠ f j) := by
  induction n generalizing p with
  | zero => simp [packVisits, packRows]
  | succ n ih =>
    by_cases eq : (f n).toInt32.toInt = f n
    · obtain ⟨le, good, bad⟩ := ih (Nat.le_of_lt hn) (p.set n (f n).toInt32 hn)
      simp only [packVisits, packRows, eq, ↓reduceIte]
      refine ⟨by omega, fun q h => by rw [good q h], fun h => ?_⟩
      obtain ⟨j,hj,count,ne⟩ := bad h
      exact ⟨j,by omega,by omega,ne⟩
    · simp only [packVisits, packRows, eq, ↓reduceIte]
      exact ⟨by omega, fun _ h => by contradiction, fun _ => ⟨n,by omega,by omega,eq⟩⟩

/-- Meter for a complete raster kernel with decreasing fuel and a fixed domain. -/
def raster {α : Type} {N : Nat} (step : (i : Fin N) → α → α) :
    (n : Nat) → n ≤ N → α → α × Nat
  | 0, _, s => (s, 0)
  | n+1, h, s =>
    let next := raster step n (Nat.le_of_lt h) (step ⟨n,h⟩ s)
    (next.1, next.2+1)

private theorem raster_count {α : Type} {N : Nat} (step : Fin N → α → α)
    (n : Nat) (hn : n ≤ N) (s : α) : (raster step n hn s).2 = n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp [raster,ih]

/-- Exact G.1 reads one source and sets one four-byte scratch cell per iteration. -/
theorem fill_work {N : Nat} (f : Fin N → Int32) (n : Nat) (hn : n ≤ N) (p : Buf N) :
    raster (fun i (b : Buf N) => b.set i (f i) i.isLt) n hn p =
      (JPEG2000.NativeOutput.fill f n hn p, n) := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih => simp only [raster, JPEG2000.NativeOutput.fill, ih]

/-- Meter the packed single-plane kernel from its current index. -/
def map1Meter {N : Nat} (f : Int32 → Int32) (b : Buf N) (i : Nat) :=
    let step := fun (j : Fin N) (p : Buf N) =>
      let k := N-1-j.val
      have hk : k < N := by have := j.isLt; dsimp [k]; omega
      p.set k (f (p.get k hk)) hk
    raster step (N-i) (Nat.sub_le ..) b

/-- The compact G.1 loop visits each remaining cell once, including the final
empty suffix when the start is beyond the plane. -/
theorem map1_work {N : Nat} (f : Int32 → Int32) (b : Buf N) (i : Nat) :
    map1Meter f b i = (JPEG2000.MCT.map1 f b i,N-i) := by
  dsimp only [map1Meter]
  rw [JPEG2000.MCT.map1]
  split
  · rename_i hi
    have eq : N-i = (N-(i+1))+1 := by omega
    conv => lhs; arg 2; rw [eq]
    simp only [raster, show N-1-(N-(i+1)) = i by omega]
    have next := map1_work f (b.set i (f (b.get i hi)) hi) (i+1)
    dsimp only [map1Meter] at next
    rw [next]
    simp [eq]
  · simp [Nat.sub_eq_zero_of_le (by omega : N ≤ i), raster]
termination_by N-i

/-- Meter the packed three-plane colour kernel from its current index. -/
def map3Meter {N : Nat} (f : Int32 → Int32 → Int32 → Int32 × Int32 × Int32)
    (a b c : Buf N) (i : Nat) :=
    let step := fun (j : Fin N) (p : Buf N × Buf N × Buf N) =>
      let k := N-1-j.val
      have hk : k < N := by have := j.isLt; dsimp [k]; omega
      let v := f (p.1.get k hk) (p.2.1.get k hk) (p.2.2.get k hk)
      (p.1.set k v.1 hk, p.2.1.set k v.2.1 hk, p.2.2.set k v.2.2 hk)
    raster step (N-i) (Nat.sub_le ..) (a,b,c)

/-- A packed RCT iteration reads and writes three cells at the same index. -/
theorem map3_work {N : Nat} (f : Int32 → Int32 → Int32 → Int32 × Int32 × Int32)
    (a b c : Buf N) (i : Nat) :
    map3Meter f a b c i = (JPEG2000.MCT.map3 f a b c i,N-i) := by
  dsimp only [map3Meter]
  rw [JPEG2000.MCT.map3]
  split
  · rename_i hi
    have eq : N-i = (N-(i+1))+1 := by omega
    conv => lhs; arg 2; rw [eq]
    simp only [raster, show N-1-(N-(i+1)) = i by omega]
    let v := f (a.get i hi) (b.get i hi) (c.get i hi)
    have next := map3_work f (a.set i v.1 hi) (b.set i v.2.1 hi) (c.set i v.2.2 hi) (i+1)
    dsimp only [map3Meter] at next
    rw [next]
    simp [eq,v]
  · simp [Nat.sub_eq_zero_of_le (by omega : N ≤ i), raster]
termination_by N-i

/-- Metered copy of the inner loop of the compact blitter. Out-of-bounds checks
can skip a load or store but consume the same iteration. -/
def row (src : Plane) : Nat → Nat → Nat → Plane → Plane × Nat
  | 0, _, _, d => (d,0)
  | k+1, si, di, d =>
    let d := if hs : si < src.width*src.height then
        if hd : di < d.width*d.height then d.set di (src.get si hs) hd else d
      else d
    let t := row src k (si+1) (di+1) d
    (t.1,t.2+1)

private theorem row_eq (s : Plane) (k si di : Nat) (d : Plane) :
    row s k si di d = (Assemble.blitRow s k si di d,k) := by
  induction k generalizing si di d with
  | zero => rfl
  | succ k ih => simp only [row,Assemble.blitRow,ih]

/-- Compact blit meter accumulating row entries as well as cell iterations. -/
def rows (s : Plane) (ox oy : Nat) : Nat → Nat → Plane → Plane × Nat × Nat
  | 0, _, d => (d,0,0)
  | k+1, y, d =>
    let r := row s s.width (y*s.width) ((oy+y)*d.width+ox) d
    let t := rows s ox oy k (y+1) r.1
    (t.1,t.2.1+1,t.2.2+r.2)

/-- A zero-width compact blit still visits every row. -/
theorem blitRows_work (s : Plane) (ox oy k y : Nat) (d : Plane) :
    rows s ox oy k y d = (Assemble.blitRows s ox oy k y d,k,s.width*k) := by
  induction k generalizing y d with
  | zero => simp [rows,Assemble.blitRows]
  | succ k ih => simp only [rows,row_eq,ih,Assemble.blitRows,Nat.mul_succ]

/-- State of the wide blitter with the original containment and range proofs. -/
abbrev WideDst (w h ox oy : Nat) (r : NativeSampleRange) :=
  {p : WidePlane // ox+w ≤ p.width ∧ oy+h ≤ p.height ∧ p.range = r}

/-- The wide blitter applies G.1 while storing, with one source read and one
eight-byte destination update per iteration, and no intermediate raster. -/
theorem blitCells_work {w h : Nat} (ox oy : Nat) (r : NativeSampleRange)
    (kernel : JPEG2000.WideOutput.Kernel r) (read : Fin (w*h) → Int)
    (n : Nat) (hn : n ≤ w*h) (d : WideDst w h ox oy r) :
    let step := fun (i : Fin (w*h)) (p : WideDst w h ox oy r) =>
      let v := kernel.sample (read i)
      let q := p.val.set (JPEG2000.WideOutput.destIndex p.val.width w ox oy i) v.val
        (JPEG2000.WideOutput.destIndex_lt p.property.1 p.property.2.1 i.isLt)
        (by rw [p.property.2.2]; exact v.property)
      (⟨q,p.property⟩ : WideDst w h ox oy r)
    ((raster step n hn d).1.val, (raster step n hn d).2) =
      (JPEG2000.WideOutput.blitCells ox oy r kernel read n hn d.val d.property.1 d.property.2.1 d.property.2.2,n) := by
  dsimp only
  refine Prod.ext ?_ (raster_count ..)
  induction n generalizing d with
  | zero => rfl
  | succ n ih => exact ih _ _


private def tabulateLoop {α : Type} {N : Nat} (f : Fin N → α) (acc : Array α) :
    (n : Nat) → n ≤ N → Array α × Nat
  | 0, _ => (acc,0)
  | n+1, h =>
    let t := tabulateLoop f (acc.push (f ⟨N-n-1,by omega⟩)) n (by omega)
    (t.1,t.2+1)

private theorem tabulate_eq {α : Type} {N : Nat} (f : Fin N → α) (a : Array α)
    (n : Nat) (hn : n ≤ N) :
    tabulateLoop f a n hn = (Array.ofFn.go f a n hn,n) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => simp only [tabulateLoop,Array.ofFn.go,ih]

/-- The `Vector.ofFn` traversal used by promotion and each wide ICT channel:
one callback and one push per index of the channel's own rectangle. -/
def tabulate {α : Type} {N : Nat} (f : Fin N → α) : Vector α N × Nat :=
  let m := tabulateLoop f (Array.emptyWithCapacity N) N (Nat.le_refl _)
  (⟨m.1,by dsimp only [m]; rw [tabulate_eq]; exact Array.size_ofFn⟩,m.2)

/-- Erasing the push counter recovers the vector built by the decoder. -/
theorem tabulate_work {α : Type} {N : Nat} (f : Fin N → α) :
    tabulate f = (Vector.ofFn f,N) := by
  apply Prod.ext
  · apply Vector.ext
    intro i hi
    simp only [tabulate,tabulate_eq]
    rfl
  · simp only [tabulate,tabulate_eq]

end JPEG2000.Spec.Resources.TileColorPlacement
