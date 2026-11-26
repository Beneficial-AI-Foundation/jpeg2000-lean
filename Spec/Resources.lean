import JPEG2000.Image

/-!
# S2 (totality) and S3 (bounded resources) as theorems over `Limits`
(Plan.md §3 rules 2–3, §4 S2/S3, §7 Phase 7 task 7.4; T.800 A.5.1 (`SIZ`), B.2–B.9 (image,
tile, code-block, precinct and packet geometry), B-12/B-14 (component and reduced grids), B.10,
D.3 (coding passes), Annex I (container); see `docs/resources.md`)

## S2 — totality

`decode`, `decodeCodestreamNarrow`, `Image.interleaved8/16` are ordinary kernel-checked definitions:
every loop is structural recursion or fuel bounded by a size checked against `Limits`
(Plan.md §3 rule 2), and the kernel accepted each one. In Lean this *is* totality: a `def`
denotes a total function on every argument, so the formal statement `decode_total` is
trivial. What S2 needs beyond that is that nothing replaces the kernel definition at run time
or escapes the logic:

* no `partial`, `unsafe`, `implemented_by`, `extern` (and no `panic!` / `!` indexing) in
  `JPEG2000/` — enforced textually by `scripts/hygiene.py`; on the constant closure of
  `JPEG2000.decode` (3236 constants, 1843 in `JPEG2000.*`) the closure audit described in
  `docs/resources.md` finds no opaque, `unsafe`, `implemented_by` or `extern` constant of the
  project;
* no `sorryAx`: `#print axioms JPEG2000.decode` (and `decodeCodestreamNarrow`) prints only
  `propext`, `Classical.choice`, `Quot.sound`.

## S3 — bounded resources

Every theorem below is about a **successful** run and bounds the quantities the code checks.
Since task 6.5 the header bounds what the stream *declares* (side, area, tiles) and the sample
and byte budgets bound what is *allocated*: the output grids at the requested reduction and one
tile's reduced working set (a viewer can decode a huge declared image at a reduced resolution):

* input: `data.size ≤ maxInputBytes` (`parse_within`);
* header (`HeaderWithin`, `GeometryWithin`): image side and area, tile count,
  `tiles × Csiz` (`checkGeometry_ok_iff`), and the exact code-block, precinct and packet
  totals of the whole tile grid (`checkWork_within`);
* output of `decodeCodestreamNarrow` (`decodeCodestream_resources`): `reduce ≤ maxDecompLevels`,
  component cells ≤ `maxWorkSamples`, bytes ≤ `maxDecodedBytes`, every plane exactly
  `width × height` (storage `4·width·height` bytes by `Plane.size_eq`);
* output of `decode` (`decode_resources`, `decode_size`): area ≤ `maxImageArea`; channels drawn
  from up-sampled planes whose fresh cells ≤ `maxWorkSamples` and bytes ≤ `maxDecodedBytes`;
  interleaved buffers ≤ `maxDecodedBytes` with their exact size (`interleave_size`);
* intermediate allocation: per tile, all tile-component planes ≤ `maxWorkSamples`
  (`decodeTile_work`, `reconstructTileComp_work`); output planes (`allocOutput_ok`);
* work: packet iteration ≤ `maxPackets` per tile (`decodeTilePacketsWith_ok`), coding passes of
  all tiles ≤ `maxCodingPasses` (`decodeAllTileCodeBlocks_passes`), code-blocks / precincts /
  packets of the tile grid (`checkWork_within`);
* excess ⇒ `limitExceeded`: `checkGeometry_limitOnly`, `parse_error_of_geometry`,
  `decode_limitExceeded_of_geometry` / `_of_area` — once the container and the main header
  parse, a declared geometry outside `Limits` makes `decode` fail with `Error.limitExceeded`
  (the value above the bound), never another error or success;
  `decodeCodestream_limitExceeded_of_output`, `decode_limitExceeded_of_output` / `_of_bytes`
  — once the header parses, output grids at the requested reduction above `maxWorkSamples`
  cells (`outputCells`) or `maxDecodedBytes` bytes (`outputBytes`) make the decoder fail with
  `limitExceeded` before any plane is allocated (`allocOutput_ok_iff`, `allocOutput_limitOnly`).

A step-count theorem ("work ≤ f(Limits, input length)") is not proved here; `docs/resources.md`
gives the formulation and what it needs.
-/
namespace JPEG2000.Spec.Resources
open JPEG2000 JPEG2000.Bytes JPEG2000.Header JPEG2000.TilePart

/-- A bind in `Except` succeeds exactly when both parts do. -/
private theorem bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β} :
    (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp [bind, Except.bind]

/-- A successful `Limits.check` gives the bound. -/
private theorem check_ok {L : Limits} {loc k v} {u : Unit} (h : L.check loc k v = .ok u) :
    v ≤ L.bound k :=
  (Limits.check_eq_ok_iff L loc k v).1 h

/-- Within the bound, `Limits.check` succeeds. -/
private theorem check_ok_of {L : Limits} {loc k v} (h : v ≤ L.bound k) : L.check loc k v = .ok () :=
  (Limits.check_eq_ok_iff L loc k v).2 h

/-- The computation fails, if at all, only with `limitExceeded` for a value above its bound. -/
def LimitOnly {α : Type} (x : Except Error α) : Prop :=
  ∀ e, x = .error e → ∃ loc k v b, e = .limitExceeded loc k v b ∧ b < v

/-- `Limits.check` fails only with `limitExceeded`. -/
private theorem LimitOnly.check (L : Limits) (loc k v) : LimitOnly (L.check loc k v) := by
  intro e he
  obtain ⟨h1, h2⟩ := Limits.checkLe_eq_error he
  exact ⟨_, _, _, _, h1, h2⟩

/-- `LimitOnly` is closed under bind. -/
private theorem LimitOnly.bind {α β : Type} {x : Except Error α} {f : α → Except Error β}
    (hx : LimitOnly x) (hf : ∀ a, LimitOnly (f a)) : LimitOnly (x >>= f) := by
  intro e he
  cases hxe : x with
  | error e' => rw [hxe] at he; cases he; exact hx _ hxe
  | ok a => rw [hxe] at he; exact hf a e he

/-- **Excess is `limitExceeded`** (Plan.md §3 rule 3): `Header.checkGeometry` fails only with `Error.limitExceeded` for a value above its bound. -/
theorem checkGeometry_limitOnly (L : Limits) (mh : Marker.MainHeader) :
    LimitOnly (checkGeometry L mh) := by
  unfold checkGeometry
  repeat (first | apply LimitOnly.bind (LimitOnly.check _ _ _ _); intro _ | exact LimitOnly.check _ _ _ _)

/-- The geometry checks of `Header.checkGeometry` on a `SIZ` segment (what the stream declares): image side, area, tiles, `tiles × components` (≤ `maxCodeBlocks`). The sample and byte budgets are checked on what is allocated, at the requested reduction (`allocOutput_ok`, `decodeTile_work`; task 6.5). -/
def GeometryWithin (L : Limits) (s : Marker.SIZ) : Prop :=
  let img := imageRect s
  img.width ≤ L.maxImageSide ∧ img.height ≤ L.maxImageSide ∧
  img.width * img.height ≤ L.maxImageArea ∧ numTiles s ≤ L.maxTiles ∧
  numTiles s * s.csiz ≤ L.maxCodeBlocks

/-- `Header.checkGeometry` succeeds exactly when the declared geometry is within `Limits` (`GeometryWithin`). -/
theorem checkGeometry_ok_iff (L : Limits) (mh : Marker.MainHeader) :
    checkGeometry L mh = .ok () ↔ GeometryWithin L mh.siz := by
  unfold checkGeometry GeometryWithin
  simp only [bind_ok]
  constructor
  · rintro ⟨_, h1, _, h2, _, h3, _, h4, h5⟩
    exact ⟨check_ok h1, check_ok h2, check_ok h3, check_ok h4, check_ok h5⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨(), check_ok_of h1, (), check_ok_of h2, (), check_ok_of h3, (), check_ok_of h4,
      check_ok_of h5⟩

/-- A loop invariant of `forIn` over a list in `Except`. -/
private theorem forIn_inv {ε α β : Type} (P : β → Prop) (f : α → β → Except ε (ForInStep β))
    (hf : ∀ a b r, P b → f a b = .ok r → P r.value) :
    ∀ (l : List α) (b r : β), P b → forIn l b f = .ok r → P r
  | [], b, r, hb, h => by simp only [List.forIn_nil] at h; cases h; exact hb
  | a :: l, b, r, hb, h => by
    rw [List.forIn_cons] at h
    obtain ⟨st, hst, h⟩ := bind_ok.1 h
    have := hf a b st hb hst
    cases st with
    | done b' => cases h; exact this
    | yield b' => exact forIn_inv P f hf l b' r this h

/-- Work totals within the code-block, precinct and packet limits. -/
def TotalsWithin (L : Limits) (t : Totals) : Prop :=
  t.codeBlocks ≤ L.maxCodeBlocks ∧ t.precincts ≤ L.maxPrecincts ∧ t.packets ≤ L.maxPackets

/-- One tile's contribution to the work totals keeps them within `Limits` (each running total is checked). -/
theorem addTile_within {L : Limits} {s t c tot tot'} (h0 : TotalsWithin L tot)
    (h : addTile L s t c tot = .ok tot') : TotalsWithin L tot' := by
  unfold addTile at h
  simp only [Std.Legacy.Range.forIn_eq_forIn_range'] at h
  obtain ⟨r, hr, h⟩ := bind_ok.1 h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  refine forIn_inv (TotalsWithin L) _ ?_ _ _ _ h0 hr
  intro i b r _ hr
  simp only [bind_ok] at hr
  obtain ⟨_, h1, _, h2, _, h3, h⟩ := hr
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact ⟨check_ok h1, check_ok h2, check_ok h3⟩

/-- **Work totals** (T.800 B.6–B.9): when `Header.checkWork` succeeds, the code-block, precinct and packet totals of the whole tile grid are within `maxCodeBlocks`, `maxPrecincts` and `maxPackets`. -/
theorem checkWork_within {L : Limits} {s d tiles tot} (h : checkWork L s d tiles = .ok tot) :
    TotalsWithin L tot := by
  unfold checkWork at h
  simp only [Std.Legacy.Range.forIn_eq_forIn_range'] at h
  obtain ⟨r, hr, h⟩ := bind_ok.1 h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  refine forIn_inv (fun st : Totals × Nat => TotalsWithin L st.1) _ ?_ _ _ _ ?_ hr
  · intro i b r hb hr
    (repeat' split at hr) <;>
    · simp only [bind_ok] at hr
      obtain ⟨t', ht, h⟩ := hr
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact addTile_within hb ht
  · simp [TotalsWithin]
/-- A parsed codestream passed the geometry and work checks on its own main header. -/
theorem parseCodestreamIn_ok {L : Limits} {data : ByteArray} {range c} {h : Header}
    (hp : parseCodestreamIn L data range c = .ok h) :
    checkGeometry L h.main = .ok () ∧ h.siz = h.main.siz ∧
      ∃ tot, checkWork L h.siz h.defaults h.tiles = .ok tot := by
  unfold parseCodestreamIn at hp
  simp only [bind_ok] at hp
  obtain ⟨r, _, ⟨mh, r'⟩, h1, h2⟩ := hp
  obtain ⟨u, hg, dflt, -, pp, -, tl, -, ov, -, tps, -, tot, hw, he⟩ := h2
  simp only [pure, Except.pure, Except.ok.injEq] at he
  subst he
  exact ⟨hg, rfl, tot, hw⟩

/-- `Header.parse` success: input length, geometry and work checks passed. -/
theorem parse_ok {L : Limits} {data : ByteArray} {h : Header} (hp : Header.parse L data = .ok h) :
    data.size ≤ L.maxInputBytes ∧ checkGeometry L h.main = .ok () ∧ h.siz = h.main.siz ∧
      ∃ tot, checkWork L h.siz h.defaults h.tiles = .ok tot := by
  unfold Header.parse at hp
  simp only [bind_ok] at hp
  obtain ⟨c, hc, hp⟩ := hp
  refine ⟨?_, parseCodestreamIn_ok hp⟩
  unfold Box.parseFile Box.parseFileAux at hc
  simp only [bind_ok] at hc
  obtain ⟨c', ⟨u, hu, -⟩, -⟩ := hc
  exact check_ok hu

/-- The shape of a successful `decodeCodestreamNarrow`: `reduce` and the header were checked, and the output components are the records `allocOutput` built, with planes attached. -/
theorem decodeCodestream_ok {L : Limits} {data : ByteArray} {reduce : Nat} {d : DecodedImage}
    (hd : decodeCodestreamNarrow L data reduce = .ok d) :
    reduce ≤ L.maxDecompLevels ∧ parse L data = .ok d.header ∧ d.reduce = reduce ∧
      ∃ info planes0 planes, Decode.allocOutput L d.header.siz reduce = .ok (info, planes0) ∧
        d.comps = info.zipWith (fun m p => { m with plane := p }) planes := by
  unfold decodeCodestreamNarrow Decode.narrowFromHeader Decode.withTiles at hd
  simp only [bind_ok] at hd
  obtain ⟨_, hr, h, hp, ⟨info, planes0⟩, ha, hd⟩ := hd
  refine ⟨check_ok hr, ?_⟩
  split at hd
  all_goals
    simp only [bind_ok] at hd
    first
    | obtain ⟨_, -, st, -, hd⟩ := hd
    | obtain ⟨st, -, hd⟩ := hd
    simp only [pure, Except.pure, Except.ok.injEq] at hd
    subst hd
    exact ⟨hp, rfl, info, planes0, _, ha, rfl⟩

/-- A left fold that adds `g x` per element is a sum. -/
private theorem list_foldl_sum {α : Type} (f : Nat → α → Nat) (g : α → Nat) (hf : ∀ a x, f a x = a + g x) :
    ∀ (l : List α) (n : Nat), l.foldl f n = n + (l.map g).sum
  | [], n => by simp
  | x :: l, n => by
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, hf]
    rw [list_foldl_sum f g hf l]
    omega

/-- `Array.foldl` adding `g x` per element is the sum of `g` over the elements. -/
private theorem array_foldl_sum {α : Type} (f : Nat → α → Nat) (g : α → Nat) (hf : ∀ a x, f a x = a + g x)
    (xs : Array α) : xs.foldl f 0 = (xs.toList.map g).sum := by
  rw [← Array.foldl_toList, list_foldl_sum f g hf]; simp

/-- Total cells (`width × height`) of decoded components. -/
def compCells (cs : Array DecodedComponent) : Nat :=
  (cs.toList.map fun c => c.width * c.height).sum

/-- Total output bytes of decoded components at `Header.bytesPerSample`. -/
def compBytes (cs : Array DecodedComponent) : Nat :=
  (cs.toList.map fun c => c.width * c.height * bytesPerSample c.depth).sum

/-- Total cells of an array of planes. -/
def planeCells (ps : Array Plane) : Nat :=
  (ps.toList.map fun p => p.width * p.height).sum

/-- **Output allocation** (`Decode.allocOutput`): the component records' cells are within `maxWorkSamples`, their bytes within `maxDecodedBytes`, and the zero planes allocated hold exactly those cells. -/
theorem allocOutput_ok {L : Limits} {s : Marker.SIZ} {reduce : Nat} {info planes0}
    (h : Decode.allocOutput L s reduce = .ok (info, planes0)) :
    compCells info ≤ L.maxWorkSamples ∧ compBytes info ≤ L.maxDecodedBytes ∧
      planeCells planes0 = compCells info := by
  unfold Decode.allocOutput at h
  simp only [bind_ok] at h
  obtain ⟨_, h1, _, h2, h⟩ := h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have e1 := check_ok h1
  have e2 := check_ok h2
  rw [array_foldl_sum (α := Marker.Component × Rect) (fun a x => a + x.2.width * x.2.height)
    (fun x => x.2.width * x.2.height) (fun _ _ => rfl)] at e1
  rw [array_foldl_sum (α := Marker.Component × Rect)
    (fun a x => a + x.2.width * x.2.height * bytesPerSample x.1.depth.toNat)
    (fun x => x.2.width * x.2.height * bytesPerSample x.1.depth.toNat) (fun _ _ => rfl)] at e2
  simp only [Limits.bound] at e1 e2
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [compCells, compBytes, planeCells, Array.toList_map, List.map_map] at * <;>
    first | exact e1 | exact e2 | rfl

/-- Zipping keeps at most the first list's elements, so a sum of a field it preserves can only drop. -/
private theorem list_zipWith_sum_le {α β γ : Type} (f : α → β → γ) (g : γ → Nat) (g' : α → Nat)
    (hf : ∀ a b, g (f a b) = g' a) :
    ∀ (l1 : List α) (l2 : List β), ((List.zipWith f l1 l2).map g).sum ≤ (l1.map g').sum
  | [], _ => by simp
  | _ :: _, [] => by simp
  | a :: l1, b :: l2 => by
    simp only [List.zipWith_cons_cons, List.map_cons, List.sum_cons, hf]
    have := list_zipWith_sum_le f g g' hf l1 l2
    omega

/-- Attaching planes to the component records keeps their cell and byte sums bounded. -/
private theorem compSums_zipWith (info : Array DecodedComponent) (planes : Array Plane) :
    compCells (info.zipWith (fun m p => { m with plane := p }) planes) ≤ compCells info ∧
    compBytes (info.zipWith (fun m p => { m with plane := p }) planes) ≤ compBytes info := by
  simp only [compCells, compBytes, Array.toList_zipWith]
  exact ⟨list_zipWith_sum_le (fun (m : DecodedComponent) (p : Plane) => { m with plane := p }) (fun c : DecodedComponent => c.width * c.height)
      (fun c : DecodedComponent => c.width * c.height) (fun _ _ => rfl) _ _,
    list_zipWith_sum_le (fun (m : DecodedComponent) (p : Plane) => { m with plane := p }) (fun c : DecodedComponent => c.width * c.height * bytesPerSample c.depth)
      (fun c : DecodedComponent => c.width * c.height * bytesPerSample c.depth) (fun _ _ => rfl) _ _⟩

/-- What a successful `Header.parse` guarantees: the input length, `SIZ = main.siz`, the geometry checks, and the work totals of the whole tile grid within `Limits`. -/
def HeaderWithin (L : Limits) (data : ByteArray) (h : Header) : Prop :=
  data.size ≤ L.maxInputBytes ∧ h.siz = h.main.siz ∧ GeometryWithin L h.siz ∧
    ∃ tot, checkWork L h.siz h.defaults h.tiles = .ok tot ∧ TotalsWithin L tot

/-- **S3 for `Header.parse`**: a parsed header satisfies `HeaderWithin`. -/
theorem parse_within {L : Limits} {data : ByteArray} {h : Header}
    (hp : Header.parse L data = .ok h) : HeaderWithin L data h := by
  obtain ⟨h1, h2, h3, tot, h4⟩ := parse_ok hp
  refine ⟨h1, h3, ?_, tot, h4, checkWork_within h4⟩
  rw [h3]; exact (checkGeometry_ok_iff L h.main).1 h2

/-- **S3 for `decodeCodestreamNarrow`** (sizes): `reduce`, the header (`HeaderWithin`) and the output components' cells and bytes are within `Limits`. -/
theorem decodeCodestream_within {L : Limits} {data : ByteArray} {reduce : Nat} {d : DecodedImage}
    (hd : decodeCodestreamNarrow L data reduce = .ok d) :
    reduce ≤ L.maxDecompLevels ∧ HeaderWithin L data d.header ∧
      compCells d.comps ≤ L.maxWorkSamples ∧ compBytes d.comps ≤ L.maxDecodedBytes := by
  obtain ⟨h1, h2, -, info, planes0, planes, h3, h4⟩ := decodeCodestream_ok hd
  obtain ⟨a1, a2, -⟩ := allocOutput_ok h3
  obtain ⟨z1, z2⟩ := compSums_zipWith info planes
  rw [h4]
  exact ⟨h1, parse_within h2, Nat.le_trans z1 a1, Nat.le_trans z2 a2⟩


/-- `Image.upLoop` keeps the destination's dimensions. -/
private theorem upLoop_dims (src : Plane) (w : Nat) (ix iy : Array Nat) :
    ∀ (k : Nat) (dst : Plane) (i : Nat),
      (Image.upLoop src w ix iy dst i k).width = dst.width ∧
      (Image.upLoop src w ix iy dst i k).height = dst.height
  | 0, dst, i => ⟨rfl, rfl⟩
  | k + 1, dst, i => by
    unfold Image.upLoop
    split
    · exact upLoop_dims src w ix iy k _ _
    · exact ⟨rfl, rfl⟩

/-- `Image.upsample` gives a `w × h` plane. -/
theorem upsample_dims {ox oy w h : Nat} {c : Color.Channel} {p : Plane}
    (hu : Image.upsample ox oy w h c = .ok p) : p.width = w ∧ p.height = h := by
  unfold Image.upsample at hu
  by_cases hf : Image.atFullRes w h c = true
  · simp only [hf, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at hu
    subst hu
    simp only [Image.atFullRes, Bool.and_eq_true, beq_iff_eq] at hf
    exact ⟨hf.1.2, hf.2⟩
  · simp only [hf, Bool.false_eq_true, ↓reduceIte] at hu
    split at hu
    · cases hu
    · simp only [pure, Except.pure, Except.ok.injEq] at hu
      subst hu
      exact upLoop_dims _ _ _ _ _ _ _

/-- Two lists related element-wise. -/
inductive Forall2 {α β : Type} (P : α → β → Prop) : List α → List β → Prop
  | nil : Forall2 P [] []
  | cons {a : α} {b : β} {as : List α} {bs : List β} : P a b → Forall2 P as bs →
      Forall2 P (a :: as) (b :: bs)

/-- `List.mapM` in `Except`: every output is related to its input. -/
private theorem list_mapM_forall {ε α β : Type} (f : α → Except ε β) (P : α → β → Prop)
    (hf : ∀ a b, f a = .ok b → P a b) :
    ∀ (xs : List α) (ys : List β), xs.mapM f = .ok ys → Forall2 P xs ys
  | [], ys, h => by simp [List.mapM_nil, pure, Except.pure] at h; subst h; exact .nil
  | x :: xs, ys, h => by
    simp only [List.mapM_cons, bind_ok, pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨y, hy, ys', hys, rfl⟩ := h
    exact .cons (hf x y hy) (list_mapM_forall f P hf xs ys' hys)

/-- `Array.mapM` in `Except`: every output is related to its input. -/
private theorem array_mapM_forall {ε α β : Type} (f : α → Except ε β) (P : α → β → Prop)
    (hf : ∀ a b, f a = .ok b → P a b) (xs : Array α) (ys : Array β)
    (h : xs.mapM f = .ok ys) : Forall2 P xs.toList ys.toList := by
  rw [Array.mapM_eq_mapM_toList] at h
  cases hm : List.mapM f xs.toList with
  | error e => rw [hm] at h; cases h
  | ok l =>
    rw [hm] at h
    simp only [Functor.map, Except.map, Except.ok.injEq] at h
    subst h
    simpa using list_mapM_forall f P hf _ _ hm

/-- A property of every related right element holds for every right element. -/
private theorem forall₂_mem_right {α β : Type} {P : α → β → Prop} {Q : β → Prop} (hP : ∀ a b, P a b → Q b) :
    ∀ {xs : List α} {ys : List β}, Forall2 P xs ys → ∀ y ∈ ys, Q y
  | _, _, .nil => by simp
  | _, _, .cons h hs => by
    intro y hy
    simp only [List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact hP _ _ h
    · exact forall₂_mem_right hP hs y hy

/-- Related lists have equal images under matching projections. -/
private theorem forall₂_map_eq {α β : Type} {P : α → β → Prop} (g : β → Nat) (g' : α → Nat)
    (hP : ∀ a b, P a b → g b = g' a) :
    ∀ {xs : List α} {ys : List β}, Forall2 P xs ys → ys.map g = xs.map g'
  | _, _, .nil => rfl
  | _, _, .cons h hs => by simp [hP _ _ h, forall₂_map_eq g g' hP hs]

/-- `Image.pick` returns an element of the channel array. -/
private theorem pick_mem {full : Array Channel} {i : Nat} {c : Channel} (h : Image.pick full i = .ok c) :
    c ∈ full := by
  unfold Image.pick at h
  split at h
  · rename_i c' hc
    cases h
    exact Array.mem_of_getElem? hc
  · cases h

/-- The channel `decode` builds from one colour-mapped channel (up-sampling to the image area). -/
def upsampleChannel (ox oy w h : Nat) (c : Color.Channel) : Except Error Channel := do
  let plane ← Image.upsample ox oy w h c
  pure { depth := c.format.depth, signed := c.format.signed, plane }

/-- Cells `decode` freshly allocates when up-sampling: `w × h` per channel not already at full resolution. -/
def upCells (w h : Nat) (chans : Array Color.Channel) : Nat :=
  (chans.toList.map fun c => if Image.atFullRes w h c then 0 else w * h).sum

/-- Output bytes of `w × h` channels at `Header.bytesPerSample`. -/
def channelBytes (w h : Nat) (full : Array Channel) : Nat :=
  (full.toList.map fun c => w * h * bytesPerSample c.depth).sum

/-- **S3 for `decode`** (output): the image area is within `maxImageArea`; the channels are drawn from an array `full` of `w × h` planes obtained by up-sampling `chans`, where the freshly allocated cells are within `maxWorkSamples` and the bytes of `full` within `maxDecodedBytes` (a channel listed twice in the layout shares its plane). -/
theorem decode_within {L : Limits} {data : ByteArray} {opts : DecodeOptions} {img : Image}
    (hd : decode L data opts = .ok img) :
    decodeCodestreamNarrow L data opts.reduce = .ok img.decoded ∧
      img.width * img.height ≤ L.maxImageArea ∧
      ∃ chans full, upCells img.width img.height chans ≤ L.maxWorkSamples ∧
        chans.mapM (upsampleChannel img.x0 img.y0 img.width img.height) = .ok full ∧
        channelBytes img.width img.height full ≤ L.maxDecodedBytes ∧
        (∀ c ∈ full, c.plane.width = img.width ∧ c.plane.height = img.height) ∧
        (∀ c ∈ img.channels, c ∈ full) ∧ (∀ a, img.alpha = some a → a ∈ full) ∧
        (∀ c ∈ img.other, c ∈ full) := by
  unfold decode at hd
  simp only [bind_ok] at hd
  obtain ⟨d, hd1, info, -, chans0, -, _, harea, hd⟩ := hd
  generalize Assemble.reduceRect (imageRect d.header.siz) opts.reduce = r at hd harea
  repeat' split at hd
  all_goals
    simp only [bind_ok] at hd
    obtain ⟨x, -, _, hw, _, hb, full, hfull, channels, hch, hd⟩ := hd
  all_goals
    first
    | obtain ⟨al, hal, other, hother, hd⟩ := hd
    | obtain ⟨other, hother, hd⟩ := hd
  all_goals
    simp only [pure, Except.pure, Except.ok.injEq] at hd
    subst hd
    refine ⟨hd1, check_ok harea, x.2, full, ?_, hfull, ?_, ?_, ?_, ?_, ?_⟩
    · have e := check_ok hw
      rw [array_foldl_sum _ (fun c => if Image.atFullRes r.width r.height c = true then 0
        else r.width * r.height) (fun a c => by split <;> simp)] at e
      exact e
    · have e := check_ok hb
      rw [array_foldl_sum _ (fun c : Color.Channel => r.width * r.height * bytesPerSample c.format.depth)
        (fun _ _ => rfl)] at e
      have hm := array_mapM_forall _ (fun (a : Color.Channel) (b : Channel) => b.depth = a.format.depth)
        (fun a b hab => by
          simp only [bind_ok, pure, Except.pure, Except.ok.injEq] at hab
          obtain ⟨_, -, rfl⟩ := hab
          rfl) _ _ hfull
      unfold channelBytes
      rw [forall₂_map_eq (fun c : Channel => r.width * r.height * bytesPerSample c.depth)
        (fun c : Color.Channel => r.width * r.height * bytesPerSample c.format.depth)
        (fun a b hab => by simp only [hab]) hm]
      exact e
    · intro c hc
      refine forall₂_mem_right (P := fun _ b => b.plane.width = r.width ∧ b.plane.height = r.height)
        (fun _ _ h => h) (array_mapM_forall _ _ (fun a b hab => ?_) _ _ hfull) c (Array.mem_def.1 hc)
      simp only [bind_ok, pure, Except.pure, Except.ok.injEq] at hab
      obtain ⟨_, hu, rfl⟩ := hab
      exact upsample_dims hu
    · intro c hc
      exact forall₂_mem_right (P := fun _ b => b ∈ full) (fun _ _ h => h)
        (array_mapM_forall _ _ (fun _ _ h => pick_mem h) _ _ hch) c (Array.mem_def.1 hc)
    · intro a ha
      first
      | (simp only [Functor.map, Except.map] at hal
         split at hal
         · cases hal
         · simp only [Except.ok.injEq] at hal
           subst hal
           simp only [Option.some.injEq] at ha
           subst ha
           exact pick_mem (by assumption))
      | (simp only [pure, Except.pure, Except.ok.injEq] at hal
         subst hal
         cases ha)
    · intro c hc
      exact forall₂_mem_right (P := fun _ b => b ∈ full) (fun _ _ h => h)
        (array_mapM_forall _ _ (fun _ _ h => pick_mem h) _ _ hother) c (Array.mem_def.1 hc)

/-- `pushPixel` appends one sample (1 or 2 bytes) per channel. -/
private theorem pushPixel_size (wide : Bool) (i : Nat) :
    ∀ (cs : List (Plane × Scaler)) (out : ByteArray),
      (pushPixel wide i out cs).size = out.size + cs.length * (if wide then 2 else 1)
  | [], out => by simp [pushPixel]
  | (p, sc) :: rest, out => by
    simp only [pushPixel]
    rw [pushPixel_size wide i rest]
    cases wide <;> simp [ByteArray.size_push, Nat.add_mul] <;> omega

/-- `interleaveLoop` appends `k` pixels. -/
private theorem interleaveLoop_size (wide : Bool) (cs : List (Plane × Scaler)) :
    ∀ (k : Nat) (out : ByteArray) (i : Nat),
      (interleaveLoop wide cs out i k).size = out.size + k * (cs.length * (if wide then 2 else 1))
  | 0, out, i => by simp [interleaveLoop]
  | k + 1, out, i => by
    simp only [interleaveLoop]
    rw [interleaveLoop_size wide cs k, pushPixel_size, Nat.succ_mul]
    omega

/-- **Interleaved output size**: an interleaved buffer has exactly `w·h·channels·(1 or 2)` bytes, within `maxDecodedBytes`. -/
theorem interleave_size {L : Limits} {w h : Nat} {chs : Array Channel} {wide : Bool} {mode : Scaling}
    {buf : ByteArray} (hi : interleave L w h chs wide mode = .ok buf) :
    buf.size = w * h * chs.size * (if wide then 2 else 1) ∧ buf.size ≤ L.maxDecodedBytes := by
  unfold interleave at hi
  simp only [bind_ok] at hi
  obtain ⟨_, -, _, hc, hi⟩ := hi
  simp only [pure, Except.pure, Except.ok.injEq] at hi
  subst hi
  have e := check_ok hc
  simp only [Limits.bound] at e
  have hs : (interleaveLoop wide (chs.toList.map fun c => (c.plane, Scaler.make mode c.depth c.signed
      (if wide then 16 else 8))) (ByteArray.emptyWithCapacity (w * h * chs.size * (if wide then 2 else 1)))
      0 (w * h)).size = w * h * chs.size * (if wide then 2 else 1) := by
    rw [interleaveLoop_size]
    simp only [List.length_map, Array.length_toList]
    rw [show (ByteArray.emptyWithCapacity (w * h * chs.size * (if wide then 2 else 1))).size = 0 from rfl]
    simp [Nat.mul_assoc]
  exact ⟨hs, hs ▸ e⟩

/-- The 8-bit interleaved output is within `maxDecodedBytes`. -/
theorem interleaved8_size {img : Image} {L : Limits} {withAlpha : Bool} {mode : Scaling} {buf : ByteArray}
    (h : img.interleaved8 L withAlpha mode = .ok buf) : buf.size ≤ L.maxDecodedBytes :=
  (interleave_size h).2

/-- The 16-bit interleaved output is within `maxDecodedBytes`. -/
theorem interleaved16_size {img : Image} {L : Limits} {withAlpha : Bool} {mode : Scaling}
    {buf : ByteArray} (h : img.interleaved16 L withAlpha mode = .ok buf) :
    buf.size ≤ L.maxDecodedBytes :=
  (interleave_size h).2

/-- The output cells the decoder allocates for a `SIZ` segment at reduction `reduce`: the sum over the components of the reduced component grid's area (B-12, B-14; `Decode.compImageRect`, the quantity `allocOutput` bounds by `maxWorkSamples`). -/
def outputCells (s : Marker.SIZ) (reduce : Nat) : Nat :=
  (s.components.toList.map fun c =>
    (Decode.compImageRect s c reduce).width * (Decode.compImageRect s c reduce).height).sum

/-- The output bytes at reduction `reduce` (each reduced component grid at `bytesPerSample` of its depth; the quantity `allocOutput` bounds by `maxDecodedBytes`). -/
def outputBytes (s : Marker.SIZ) (reduce : Nat) : Nat :=
  (s.components.toList.map fun c =>
    (Decode.compImageRect s c reduce).width * (Decode.compImageRect s c reduce).height *
      bytesPerSample c.depth.toNat).sum

/-- `Decode.allocOutput` fails only with `limitExceeded`. -/
theorem allocOutput_limitOnly (L : Limits) (s : Marker.SIZ) (reduce : Nat) :
    LimitOnly (Decode.allocOutput L s reduce) := by
  unfold Decode.allocOutput
  refine LimitOnly.bind (LimitOnly.check _ _ _ _) fun _ => ?_
  refine LimitOnly.bind (LimitOnly.check _ _ _ _) fun _ => ?_
  intro e he; cases he

/-- `Decode.allocOutput` succeeds exactly when the output cells and bytes at the reduction are within `maxWorkSamples` and `maxDecodedBytes`. -/
theorem allocOutput_ok_iff (L : Limits) (s : Marker.SIZ) (reduce : Nat) :
    (∃ r, Decode.allocOutput L s reduce = .ok r) ↔
      outputCells s reduce ≤ L.maxWorkSamples ∧ outputBytes s reduce ≤ L.maxDecodedBytes := by
  have e1 : (s.components.map fun c => (c, Decode.compImageRect s c reduce)).foldl
      (fun a (x : Marker.Component × Rect) => a + x.2.width * x.2.height) 0 = outputCells s reduce := by
    rw [array_foldl_sum (α := Marker.Component × Rect) (fun a x => a + x.2.width * x.2.height)
      (fun x => x.2.width * x.2.height) (fun _ _ => rfl)]
    simp only [outputCells, Array.toList_map, List.map_map]; rfl
  have e2 : (s.components.map fun c => (c, Decode.compImageRect s c reduce)).foldl
      (fun a (x : Marker.Component × Rect) => a + x.2.width * x.2.height * bytesPerSample x.1.depth.toNat) 0 =
      outputBytes s reduce := by
    rw [array_foldl_sum (α := Marker.Component × Rect)
      (fun a x => a + x.2.width * x.2.height * bytesPerSample x.1.depth.toNat)
      (fun x => x.2.width * x.2.height * bytesPerSample x.1.depth.toNat) (fun _ _ => rfl)]
    simp only [outputBytes, Array.toList_map, List.map_map]; rfl
  unfold Decode.allocOutput
  simp only [bind_ok]
  constructor
  · rintro ⟨_, _, h1, _, h2, -⟩
    have a := check_ok h1
    have b := check_ok h2
    simp only [Limits.bound] at a b
    exact ⟨e1 ▸ a, e2 ▸ b⟩
  · rintro ⟨h1, h2⟩
    refine ⟨_, (), check_ok_of ?_, (), check_ok_of ?_, rfl⟩
    · simp only [Limits.bound]; rw [e1]; exact h1
    · simp only [Limits.bound]; rw [e2]; exact h2

/-- **Excess ⇒ `limitExceeded`** for `decodeCodestreamNarrow` at a reduction: once the header parses, output grids at reduction `reduce` above `maxWorkSamples` cells or `maxDecodedBytes` bytes make `decodeCodestreamNarrow` fail with `limitExceeded` (value above bound) before any plane is allocated. -/
theorem decodeCodestream_limitExceeded_of_output {L : Limits} {data : ByteArray} {reduce : Nat}
    {h : Header} (hp : Header.parse L data = .ok h)
    (hx : L.maxWorkSamples < outputCells h.siz reduce ∨
      L.maxDecodedBytes < outputBytes h.siz reduce) :
    ∃ loc k v b, decodeCodestreamNarrow L data reduce = .error (.limitExceeded loc k v b) ∧ b < v := by
  unfold decodeCodestreamNarrow Decode.narrowFromHeader
  cases hrd : L.check Decode.loc .decompLevels reduce with
  | error e =>
    obtain ⟨loc', k', v', b', rfl, hlt'⟩ := LimitOnly.check L _ _ _ _ hrd
    exact ⟨loc', k', v', b', by simp only [bind, Except.bind], hlt'⟩
  | ok u =>
    cases ha : Decode.allocOutput L h.siz reduce with
    | ok r =>
      obtain ⟨a, b⟩ := (allocOutput_ok_iff L h.siz reduce).1 ⟨r, ha⟩
      exfalso; rcases hx with hx | hx <;> omega
    | error e =>
      obtain ⟨loc, k, v, b, rfl, hlt⟩ := allocOutput_limitOnly L h.siz reduce _ ha
      exact ⟨loc, k, v, b, by simp only [hp, ha, bind, Except.bind], hlt⟩

/-- **Excess ⇒ `limitExceeded`** for `Header.parse`: once the container and the main header parse, a declared geometry outside `Limits` makes the parse fail with `limitExceeded` (value above bound). -/
theorem parse_error_of_geometry {L : Limits} {data : ByteArray} {c : Box.Container}
    {r r' : Bytes.Reader} {mh : Marker.MainHeader}
    (hc : Box.parseFile L data = .ok c)
    (hr : rangeReader data { offset := c.codestream.start, length := c.codestream.len } = .ok r)
    (hm : Marker.parseMainHeader L r = .ok (mh, r')) (hx : ¬ GeometryWithin L mh.siz) :
    ∃ loc k v b, Header.parse L data = .error (.limitExceeded loc k v b) ∧ b < v := by
  cases hg : checkGeometry L mh with
  | ok u => exact absurd ((checkGeometry_ok_iff L mh).1 hg) hx
  | error e =>
    obtain ⟨loc, k, v, b, rfl, hlt⟩ := checkGeometry_limitOnly L mh _ hg
    refine ⟨loc, k, v, b, ?_, hlt⟩
    unfold Header.parse parseCodestreamIn
    simp only [hc, hr, hm, hg, bind, Except.bind]

/-- **Excess ⇒ `limitExceeded`** for `decode`: once the container and the main header parse, a declared geometry outside `Limits` makes `decode` fail with `limitExceeded` (value above bound), whatever the options. -/
theorem decode_limitExceeded_of_geometry {L : Limits} {data : ByteArray} {opts : DecodeOptions}
    {c : Box.Container} {r r' : Bytes.Reader} {mh : Marker.MainHeader}
    (hc : Box.parseFile L data = .ok c)
    (hr : rangeReader data { offset := c.codestream.start, length := c.codestream.len } = .ok r)
    (hm : Marker.parseMainHeader L r = .ok (mh, r')) (hx : ¬ GeometryWithin L mh.siz) :
    ∃ loc k v b, decode L data opts = .error (.limitExceeded loc k v b) ∧ b < v := by
  obtain ⟨loc, k, v, b, hp, hlt⟩ := parse_error_of_geometry hc hr hm hx
  unfold decode decodeCodestreamNarrow
  cases hrd : L.check Decode.loc .decompLevels opts.reduce with
  | error e =>
    obtain ⟨loc', k', v', b', rfl, hlt'⟩ := LimitOnly.check L _ _ _ _ hrd
    exact ⟨loc', k', v', b', by simp only [bind, Except.bind], hlt'⟩
  | ok u =>
    exact ⟨loc, k, v, b, by simp only [hp, bind, Except.bind], hlt⟩

/-- **Excess ⇒ `limitExceeded`**: a declared image area above `maxImageArea` makes `decode` fail with `limitExceeded`. -/
theorem decode_limitExceeded_of_area {L : Limits} {data : ByteArray} {opts : DecodeOptions}
    {c : Box.Container} {r r' : Bytes.Reader} {mh : Marker.MainHeader}
    (hc : Box.parseFile L data = .ok c)
    (hr : rangeReader data { offset := c.codestream.start, length := c.codestream.len } = .ok r)
    (hm : Marker.parseMainHeader L r = .ok (mh, r'))
    (hx : L.maxImageArea < (imageRect mh.siz).width * (imageRect mh.siz).height) :
    ∃ loc k v b, decode L data opts = .error (.limitExceeded loc k v b) ∧ b < v :=
  decode_limitExceeded_of_geometry hc hr hm fun hg => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hx hg.2.2.1)

/-- **Excess ⇒ `limitExceeded`** for `decode` at a reduction: once the header parses, output grids at reduction `opts.reduce` above `maxWorkSamples` cells or `maxDecodedBytes` bytes make `decode` fail with `limitExceeded` (value above bound). -/
theorem decode_limitExceeded_of_output {L : Limits} {data : ByteArray} {opts : DecodeOptions}
    {h : Header} (hp : Header.parse L data = .ok h)
    (hx : L.maxWorkSamples < outputCells h.siz opts.reduce ∨
      L.maxDecodedBytes < outputBytes h.siz opts.reduce) :
    ∃ loc k v b, decode L data opts = .error (.limitExceeded loc k v b) ∧ b < v := by
  obtain ⟨loc, k, v, b, hd, hlt⟩ := decodeCodestream_limitExceeded_of_output hp hx
  refine ⟨loc, k, v, b, ?_, hlt⟩
  unfold decode
  simp only [hd, bind, Except.bind]

/-- **Excess ⇒ `limitExceeded`**: output bytes at the requested reduction above `maxDecodedBytes` make `decode` fail with `limitExceeded` (task 6.5: the bound is on what is allocated, the reduced grids, not on the declared full-resolution size). -/
theorem decode_limitExceeded_of_bytes {L : Limits} {data : ByteArray} {opts : DecodeOptions}
    {h : Header} (hp : Header.parse L data = .ok h)
    (hx : L.maxDecodedBytes < outputBytes h.siz opts.reduce) :
    ∃ loc k v b, decode L data opts = .error (.limitExceeded loc k v b) ∧ b < v :=
  decode_limitExceeded_of_output hp (.inr hx)

/-- Dimensions of a plane. -/
def dims (p : Plane) : Nat × Nat := (p.width, p.height)

/-- `Assemble.blitRow` keeps the destination's dimensions. -/
private theorem blitRow_dims (src : Plane) :
    ∀ (k si di : Nat) (dst : Plane), dims (Assemble.blitRow src k si di dst) = dims dst
  | 0, _, _, _ => rfl
  | k + 1, si, di, dst => by
    simp only [Assemble.blitRow]
    rw [blitRow_dims src k]
    split
    · split <;> rfl
    · rfl

/-- `Assemble.blitRows` keeps the destination's dimensions. -/
private theorem blitRows_dims (src : Plane) (ox oy : Nat) :
    ∀ (k y : Nat) (dst : Plane), dims (Assemble.blitRows src ox oy k y dst) = dims dst
  | 0, _, _ => rfl
  | k + 1, y, dst => by
    simp only [Assemble.blitRows]
    rw [blitRows_dims src ox oy k, blitRow_dims]

/-- `Assemble.blit` keeps the destination's dimensions. -/
theorem blit_dims {dst src : Plane} {ox oy : Nat} {p : Plane}
    (h : Assemble.blit dst src ox oy = .ok p) : dims p = dims dst := by
  unfold Assemble.blit at h
  split at h
  · cases h; exact blitRows_dims _ _ _ _ _ _
  · cases h

/-- Taking a plane out of an array and putting back one of the same dimensions keeps the array's dimensions. -/
private theorem setIfInBounds_dims {planes : Array Plane} {c : Nat} {p : Plane}
    (hp : dims p = dims (planes.getD c (Plane.zero 0 0))) :
    ((planes.setIfInBounds c (Plane.zero 0 0)).setIfInBounds c p).toList.map dims =
      planes.toList.map dims := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, Array.getElem_toList]
    simp only [List.length_map, Array.length_toList, Array.size_setIfInBounds] at h1
    by_cases hc : c = i
    · subst hc
      rw [Array.getElem_setIfInBounds_self, hp]
      simp [Array.getD, h1]
    · rw [Array.getElem_setIfInBounds_ne (by simpa using h1) hc, Array.getElem_setIfInBounds_ne h1 hc]

/-- `Decode.place` keeps the dimensions of every component plane (tiles are copied in place). -/
theorem place_dims {info : Array DecodedComponent} {planes planes' : Array Plane}
    {t : Assemble.TileOut} (h : Decode.place info planes t = .ok planes') :
    planes'.toList.map dims = planes.toList.map dims := by
  unfold Decode.place at h
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', bind_ok] at h
  obtain ⟨st, hst, h⟩ := h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  refine forIn_inv (fun q : Array Plane => q.toList.map dims = planes.toList.map dims) _ ?_ _ _ _
    rfl hst
  intro c b r hb hr
  repeat' split at hr
  all_goals first
    | cases hr
    | (simp only [bind_ok] at hr
       obtain ⟨p, hp, hr⟩ := hr
       simp only [pure, Except.pure, Except.ok.injEq] at hr
       subst hr
       simp only [ForInStep.value]
       rw [setIfInBounds_dims (blit_dims hp)]
       exact hb)

set_option linter.unusedSimpArgs false in
/-- The output planes of `decodeCodestreamNarrow` keep the dimensions `allocOutput` gave them. -/
theorem decodeCodestream_planes {L : Limits} {data : ByteArray} {reduce : Nat} {d : DecodedImage}
    (hd : decodeCodestreamNarrow L data reduce = .ok d) :
    ∃ info planes0 planes, Decode.allocOutput L d.header.siz reduce = .ok (info, planes0) ∧
      planes.toList.map dims = planes0.toList.map dims ∧
      d.comps = info.zipWith (fun m p => { m with plane := p }) planes := by
  unfold decodeCodestreamNarrow Decode.narrowFromHeader Decode.withTiles at hd
  simp only [bind_ok, Std.Legacy.Range.forIn_eq_forIn_range'] at hd
  obtain ⟨_, -, h, hp, ⟨info, planes0⟩, ha, hd⟩ := hd
  split at hd
  all_goals
    simp only [bind_ok] at hd
    first
    | obtain ⟨_, -, st, hst, hd⟩ := hd
    | obtain ⟨st, hst, hd⟩ := hd
    simp only [pure, Except.pure, Except.ok.injEq] at hd
    subst hd
    refine ⟨info, planes0, st.1, ha, ?_, rfl⟩
    refine forIn_inv (fun q : Array Plane × Nat × Nat × Nat =>
      q.1.toList.map dims = planes0.toList.map dims) _ ?_ _ _ _ rfl hst
    intro t b r hb hr
    repeat' split at hr
    all_goals
      simp only [bind_ok, pure, Except.pure] at hr
    all_goals
      repeat' (first | (obtain ⟨_, _, hr⟩ := (hr : ∃ _, _ ∧ _)) | split at hr | simp only [bind_ok] at hr)
    all_goals
      simp only [pure, Except.pure, Except.ok.injEq] at hr
      subst hr
      simp only [ForInStep.value]
      rw [place_dims (by assumption)]
      exact hb

/-- The planes `allocOutput` allocates have the dimensions of the component records. -/
theorem allocOutput_dims {L : Limits} {s : Marker.SIZ} {reduce : Nat} {info planes0}
    (h : Decode.allocOutput L s reduce = .ok (info, planes0)) :
    planes0.toList.map dims = info.toList.map fun m => (m.width, m.height) := by
  unfold Decode.allocOutput at h
  simp only [bind_ok] at h
  obtain ⟨_, -, _, -, h⟩ := h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  simp only [Array.toList_map, List.map_map]
  rfl

/-- Attaching planes with the records' dimensions gives components whose planes match their declared size. -/
private theorem zipWith_plane_dims :
    ∀ (l1 : List DecodedComponent) (l2 : List Plane),
      l2.map dims = l1.map (fun m => (m.width, m.height)) →
      ∀ c ∈ List.zipWith (fun m p => { m with plane := p }) l1 l2,
        c.plane.width = c.width ∧ c.plane.height = c.height
  | [], _, _ => by simp
  | _ :: _, [], h => by simp at h
  | m :: l1, p :: l2, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    intro c hc
    simp only [List.zipWith_cons_cons, List.mem_cons] at hc
    rcases hc with rfl | hc
    · simp only [dims, Prod.mk.injEq] at h
      exact h.1
    · exact zipWith_plane_dims l1 l2 h.2 c hc

/-- Every output component's plane is exactly `width × height` (so its storage is `4·width·height` bytes, `Plane.size_eq`). -/
theorem decodeCodestream_comp_dims {L : Limits} {data : ByteArray} {reduce : Nat}
    {d : DecodedImage} (hd : decodeCodestreamNarrow L data reduce = .ok d) :
    ∀ c ∈ d.comps, c.plane.width = c.width ∧ c.plane.height = c.height := by
  obtain ⟨info, planes0, planes, ha, hp, hc⟩ := decodeCodestream_planes hd
  intro c hmem
  rw [hc] at hmem
  have hmem' := Array.mem_def.1 hmem
  rw [Array.toList_zipWith] at hmem'
  exact zipWith_plane_dims _ _ (hp.trans (allocOutput_dims ha)) c hmem'

section Iter
open JPEG2000.Progression

/-- `P` is preserved by every successful step of `f`. -/
def StepInv {β α : Type} (P : β → Prop) (f : β → α → Except Error β) : Prop :=
  ∀ b a b', P b → f b a = .ok b' → P b'

/-- `Progression.forRange` preserves a step invariant. -/
private theorem forRange_inv {β : Type} {P : β → Prop} {f : β → Nat → Except Error β} (hf : StepInv P f) :
    ∀ (n s : Nat) (b b' : β), P b → forRange s n f b = .ok b' → P b'
  | 0, s, b, b', hb, h => by
    simp only [forRange, pure, Except.pure, Except.ok.injEq] at h; exact h ▸ hb
  | n + 1, s, b, b', hb, h => by
    simp only [forRange, bind_ok] at h
    obtain ⟨b1, h1, h2⟩ := h
    exact forRange_inv hf n (s + 1) b1 b' (hf _ _ _ hb h1) h2

/-- `List.foldlM` in `Except` preserves a step invariant. -/
private theorem foldlM_inv {β α : Type} {P : β → Prop} {f : β → α → Except Error β} (hf : StepInv P f) :
    ∀ (l : List α) (b b' : β), P b → l.foldlM f b = .ok b' → P b'
  | [], b, b', hb, h => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h; exact h ▸ hb
  | a :: l, b, b', hb, h => by
    simp only [List.foldlM_cons, bind_ok] at h
    obtain ⟨b1, h1, h2⟩ := h
    exact foldlM_inv hf l b1 b' (hf _ _ _ hb h1) h2

/-- `Progression.forVolume` preserves a step invariant (all four progression shapes). -/
private theorem forVolume_inv {β : Type} {P : β → Prop} {f : β → PacketId → Except Error β}
    (hf : StepInv P f) (g : Layout) (v : Volume) (b b' : β) (hb : P b)
    (h : forVolume g v f b = .ok b') : P b' := by
  unfold forVolume at h
  split at h
  · unfold forLRCP at h
    exact forRange_inv (fun b l b' hb h => forRange_inv (fun b r b' hb h =>
      forRange_inv (fun b i b' hb h => forRange_inv (fun b k b' hb h => hf _ _ _ hb h) _ _ _ _ hb h)
      _ _ _ _ hb h) _ _ _ _ hb h) _ _ _ _ hb h
  · unfold forRLCP at h
    exact forRange_inv (fun b l b' hb h => forRange_inv (fun b r b' hb h =>
      forRange_inv (fun b i b' hb h => forRange_inv (fun b k b' hb h => hf _ _ _ hb h) _ _ _ _ hb h)
      _ _ _ _ hb h) _ _ _ _ hb h) _ _ _ _ hb h
  · unfold forPosition at h
    exact foldlM_inv (fun b e b' hb h => forRange_inv (fun b l b' hb h => hf _ _ _ hb h) _ _ _ _ hb h)
      _ _ _ hb h

/-- `Progression.forVolumes` preserves a step invariant (skipped packets keep the state). -/
private theorem forVolumes_inv {β : Type} {P : β → Prop} (g : Layout) :
    ∀ (vs prev : List Volume) (f : β → PacketId → Except Error β) (b b' : β), StepInv P f → P b →
      forVolumes g prev vs f b = .ok b' → P b'
  | [], prev, f, b, b', _, hb, h => by
    simp only [forVolumes, pure, Except.pure, Except.ok.injEq] at h; exact h ▸ hb
  | v :: vs, prev, f, b, b', hf, hb, h => by
    simp only [forVolumes, bind_ok] at h
    obtain ⟨b1, h1, h2⟩ := h
    refine forVolumes_inv g vs _ f b1 b' hf (forVolume_inv ?_ g v b b1 hb h1) h2
    intro c p c' hc hcp
    simp only at hcp
    split at hcp
    · simp only [pure, Except.pure, Except.ok.injEq] at hcp; exact hcp ▸ hc
    · exact hf _ _ _ hc hcp

/-- `Progression.forPackets` preserves a step invariant (in `Except`, any layout). -/
theorem forPackets_inv {β : Type} {P : β → Prop} {f : β → PacketId → Except Error β}
    (hf : StepInv P f) (g : Layout) (o : Marker.Progression) (poc : Array Marker.PocEntry) (b b' : β)
    (hb : P b) (h : forPackets g o poc f b = .ok b') : P b' :=
  forVolumes_inv g _ [] f b b' hf hb h


/-- **Tier-2 work of one tile**: the packet iteration work (`iterationWork`, which bounds the packets visited) is within `maxPackets`, and the tile's coding passes together with the earlier tiles' are within `maxCodingPasses` (or the tile has none). -/
theorem decodeTilePacketsWith_ok {L : Limits} {h : Header} {data : ByteArray} {tp : TileParams}
    {hs : Option ByteArray} {pb : Nat} {t : Tier2.Packet.TileCodeBlocks}
    (ht : Tier2.Packet.decodeTilePacketsWith L h data tp hs pb = .ok t) :
    (∃ g c, Layout.ofHeader h tp.index = .ok (g, c) ∧
      iterationWork g c.progression c.poc ≤ L.maxPackets) ∧
    (pb + t.passes ≤ L.maxCodingPasses ∨ t.passes = 0) := by
  unfold Tier2.Packet.decodeTilePacketsWith at ht
  simp only [bind_ok] at ht
  obtain ⟨⟨g, c⟩, hg, _, hw, ⟨precs, base, spans⟩, -, ⟨buf, parts⟩, -, st, hst, ht⟩ := ht
  simp only [pure, Except.pure, Except.ok.injEq] at ht
  subst ht
  refine ⟨⟨g, c, hg, check_ok hw⟩, ?_⟩
  refine forPackets_inv (P := fun s : Tier2.Packet.LoopState =>
    pb + s.passes ≤ L.maxCodingPasses ∨ s.passes = 0) ?_ _ _ _ _ _ (Or.inr rfl) hst
  intro b p b' _ hb
  simp only at hb
  split at hb
  · simp only [bind_ok] at hb
    obtain ⟨_, -, _, hc, hb⟩ := hb
    simp only [pure, Except.pure, Except.ok.injEq] at hb
    subst hb
    exact Or.inl (check_ok hc)
  · cases hb

/-- `decodeTilePacketsWith_ok` for `Tier2.Headers.decodeWithStream`. -/
theorem decodeWithStream_ok {L : Limits} {h : Header} {data : ByteArray} {tp : TileParams}
    {hs : Option Tier2.Headers.HeaderStream} {pb : Nat} {t : Tier2.Packet.TileCodeBlocks}
    (ht : Tier2.Headers.decodeWithStream L h data tp hs pb = .ok t) :
    (∃ g c, Layout.ofHeader h tp.index = .ok (g, c) ∧
      iterationWork g c.progression c.poc ≤ L.maxPackets) ∧
    (pb + t.passes ≤ L.maxCodingPasses ∨ t.passes = 0) := by
  unfold Tier2.Headers.decodeWithStream at ht
  simp only [bind_ok] at ht
  obtain ⟨t', h1, ht⟩ := ht
  have := decodeTilePacketsWith_ok h1
  repeat' split at ht
  all_goals (try cases ht) <;> exact this

/-- Total coding passes of a list of decoded tiles. -/
def totalPasses (ts : Array Tier2.Packet.TileCodeBlocks) : Nat :=
  (ts.toList.map (·.passes)).sum

/-- **Tier-1 work** (T.800 D.3): the coding passes of all tiles together are within `maxCodingPasses`. -/
theorem decodeAllTileCodeBlocks_passes {L : Limits} {h : Header} {data : ByteArray}
    {ts : Array Tier2.Packet.TileCodeBlocks}
    (ht : Tier2.Headers.decodeAllTileCodeBlocks L h data = .ok ts) :
    totalPasses ts ≤ L.maxCodingPasses := by
  unfold Tier2.Headers.decodeAllTileCodeBlocks at ht
  simp only [Std.Legacy.Range.forIn_eq_forIn_range'] at ht
  split at ht
  all_goals
    simp only [bind_ok] at ht
    obtain ⟨idx, -, st, hst, ht⟩ := ht
    simp only [pure, Except.pure, Except.ok.injEq] at ht
    subst ht
    have := forIn_inv (fun s : Array Tier2.Packet.TileCodeBlocks × Nat =>
      s.2 = totalPasses s.1 ∧ s.2 ≤ L.maxCodingPasses) _ ?_ _ _ _ ⟨rfl, Nat.zero_le _⟩ hst
    · rw [← this.1]; exact this.2
    · intro j b r hb hr
      split at hr
      · simp only [bind_ok] at hr
        obtain ⟨hs, -, t, htd, hr⟩ := hr
        simp only [pure, Except.pure, Except.ok.injEq] at hr
        subst hr
        obtain ⟨-, hp⟩ := decodeWithStream_ok htd
        refine ⟨?_, ?_⟩
        · simp [totalPasses, hb.1]
        · rcases hp with hp | hp
          · exact hp
          · simp only [hp, Nat.add_zero]; exact hb.2
      · cases hr

/-- The work cells of one tile at reduction `reduce`: the sum over its tile-components of the reduced tile-component rectangle's area. -/
def tileCells (g : Layout) (reduce : Nat) : Nat :=
  (g.comps.toList.map fun tc =>
    (Assemble.reduceRect tc.rect reduce).width * (Assemble.reduceRect tc.rect reduce).height).sum

/-- **Per-tile working memory**: the cells of all tile-component planes of a tile (held together until the MCT) are within `maxWorkSamples`. -/
theorem decodeTile_work {L : Limits} {h : Header} {data : ByteArray} {t reduce : Nat}
    {tcb : Option Tier2.Packet.TileCodeBlocks} {out : Assemble.TileOut}
    (hd : Assemble.decodeTile L h data t reduce tcb = .ok out) :
    ∃ g c, Layout.ofHeader h t = .ok (g, c) ∧ tileCells g reduce ≤ L.maxWorkSamples := by
  unfold Assemble.decodeTile Assemble.withCenteredTile at hd
  simp only [bind_ok] at hd
  obtain ⟨⟨g, c⟩, hg, _, hw, -⟩ := hd
  refine ⟨g, c, hg, ?_⟩
  have e := check_ok hw
  rw [array_foldl_sum _ (fun tc : Tier2.Geometry.TileCompGeom =>
    (Assemble.reduceRect tc.rect reduce).width * (Assemble.reduceRect tc.rect reduce).height)
    (fun _ _ => rfl)] at e
  exact e

/-- Each tile-component plane allocated by `reconstructTileComp` is within `maxWorkSamples`. -/
theorem reconstructTileComp_work {L : Limits} {data : ByteArray} {tc : Tier2.Geometry.TileCompGeom}
    {depth F reduce : Nat} {precs : Array (Array Tier2.Packet.PrecinctOut)} {r : Plane × Nat}
    (hd : Assemble.reconstructTileComp L data tc depth F reduce precs = .ok r) :
    (Assemble.reduceRect tc.rect reduce).width * (Assemble.reduceRect tc.rect reduce).height ≤
      L.maxWorkSamples := by
  unfold Assemble.reconstructTileComp at hd
  dsimp only at hd
  split at hd
  · cases hd
  · simp only [bind_ok] at hd
    obtain ⟨pl, hz, -⟩ := hd
    unfold Plane.zeroChecked at hz
    simp only [bind_ok] at hz
    obtain ⟨_, hc, -⟩ := hz
    exact check_ok hc
end Iter

/-! ## The S2 and S3 summary theorems -/

/-- **S2 (totality) as a Lean proposition.** Every Lean `def` denotes a total function, so this
statement is trivially true (`⟨_, rfl⟩`); it is recorded for completeness. The content of S2
is that `decode` is a kernel-checked definition at all — no `partial`, `unsafe`,
`implemented_by` or `extern` anywhere in its closure (enforced by `scripts/hygiene.py`, checked
on the constant closure by the closure audit proposed in `docs/resources.md`) and no
`sorryAx` (`#print axioms JPEG2000.decode`). See the module doc. -/
theorem decode_total (L : Limits) (data : ByteArray) (opts : DecodeOptions) :
    ∃ r, decode L data opts = r :=
  ⟨_, rfl⟩

/-- What a successful `decodeCodestreamNarrow L data reduce` guarantees (S3): `reduce` within
`maxDecompLevels`, the header facts (`HeaderWithin`: input length, geometry, work totals), the
output components' cells within `maxWorkSamples` and bytes within `maxDecodedBytes`, and every
output plane exactly its component's `width × height`. -/
def CodestreamWithin (L : Limits) (data : ByteArray) (reduce : Nat) (d : DecodedImage) : Prop :=
  reduce ≤ L.maxDecompLevels ∧ HeaderWithin L data d.header ∧
    compCells d.comps ≤ L.maxWorkSamples ∧ compBytes d.comps ≤ L.maxDecodedBytes ∧
    ∀ c ∈ d.comps, c.plane.width = c.width ∧ c.plane.height = c.height

/-- What a successful `decode` guarantees about its own output (S3): the image area within
`maxImageArea`; every colour, alpha and other channel taken from an array `full` of
`width × height` planes, obtained by up-sampling `chans`, whose freshly allocated cells are within
`maxWorkSamples` and whose output bytes are within `maxDecodedBytes`. -/
def ImageWithin (L : Limits) (img : Image) : Prop :=
  img.width * img.height ≤ L.maxImageArea ∧
    ∃ chans full, upCells img.width img.height chans ≤ L.maxWorkSamples ∧
      chans.mapM (upsampleChannel img.x0 img.y0 img.width img.height) = .ok full ∧
      channelBytes img.width img.height full ≤ L.maxDecodedBytes ∧
      (∀ c ∈ full, c.plane.width = img.width ∧ c.plane.height = img.height) ∧
      (∀ c ∈ img.channels, c ∈ full) ∧ (∀ a, img.alpha = some a → a ∈ full) ∧
      (∀ c ∈ img.other, c ∈ full)

/-- **S3 for `decodeCodestreamNarrow`** (Plan.md §4): output size and allocation bounded by `Limits`. -/
theorem decodeCodestream_resources {L : Limits} {data : ByteArray} {reduce : Nat}
    {d : DecodedImage} (hd : decodeCodestreamNarrow L data reduce = .ok d) :
    CodestreamWithin L data reduce d := by
  obtain ⟨h1, h2, h3, h4⟩ := decodeCodestream_within hd
  exact ⟨h1, h2, h3, h4, decodeCodestream_comp_dims hd⟩

/-- **S3 for `decode`** (Plan.md §4): the codestream stage's bounds (`CodestreamWithin`, for
the raw component planes kept in `img.decoded`) and the image's own (`ImageWithin`). -/
theorem decode_resources {L : Limits} {data : ByteArray} {opts : DecodeOptions} {img : Image}
    (hd : decode L data opts = .ok img) :
    CodestreamWithin L data opts.reduce img.decoded ∧ ImageWithin L img := by
  obtain ⟨h1, h2, h3⟩ := decode_within hd
  exact ⟨decodeCodestream_resources h1, h2, h3⟩

/-- **S3, the headline numbers**: a decoded image has area at most `maxImageArea`, came from an
input of at most `maxInputBytes`, and its raw component planes hold at most `maxWorkSamples`
cells and `maxDecodedBytes` output bytes. -/
theorem decode_size {L : Limits} {data : ByteArray} {opts : DecodeOptions} {img : Image}
    (hd : decode L data opts = .ok img) :
    data.size ≤ L.maxInputBytes ∧ img.width * img.height ≤ L.maxImageArea ∧
      compCells img.decoded.comps ≤ L.maxWorkSamples ∧
      compBytes img.decoded.comps ≤ L.maxDecodedBytes := by
  obtain ⟨⟨-, ⟨hin, -⟩, hc, hb, -⟩, ha, -⟩ := decode_resources hd
  exact ⟨hin, ha, hc, hb⟩
end JPEG2000.Spec.Resources