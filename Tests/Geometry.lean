import JPEG2000.Tier2.Geometry

/-!
# Tests: tile-component geometry (task 4.2)

Plan.md §3 rule 3, §4 S3, §8; T.800 B.5 (resolutions, sub-bands, B-14/B-15), B.6
(precincts, B-16), B.7 (code-blocks), B.12.1.3 (precinct positions on the reference grid).

* **Hand cases** with values computed by hand from B-14/B-15/B-16: odd offsets, sub-sampling
  `XRsiz = 3`, `YRsiz = 2`, `NL = 0`, precincts smaller than code-blocks (`xcb' = 0`), a 1×1
  tile with empty resolutions and empty bands, reference-grid precinct positions, and each
  error (resolution > NL, precinct out of range, `maxPrecincts`, `maxCodeBlocks`).
* **Consistency** (`checkTileComp`) for every tile-component examined: per resolution,
  `pw · ph = Header.numPrecincts` and the band code-block counts sum to
  `Header.numCodeBlocks`; over resolutions the totals equal `Header.tileCompCounts`; the
  bands of resolution `r` and resolution `r − 1` tile resolution `r` (B-15 vs B-14); every
  precinct is non-empty and inside the resolution, and their areas sum to the resolution's;
  per band, each precinct-band lies in its precinct cell and inside the band, their areas sum
  to the band's, each code-block is non-empty and lies in its code-block cell and in its
  precinct-band, code-block areas sum to the precinct-band's, and code-block counts summed
  over precincts equal the band's; `precinctCodeBlockCounts` agrees with `precinct`; each
  precinct's reference position is in the tile, satisfies the B.12.1.3 condition and maps
  back to its precinct. Containment in distinct grid cells plus equal area sums means the
  rectangles partition the band / resolution.
* **Exhaustive** (small cases, a sweep of 864 parameter combinations): every sample of
  every resolution lies in exactly one precinct, every sample of every band in exactly one
  code-block, and scanning every reference-grid `x` (`y`) of the tile under the B.12.1.3
  condition visits every precinct column (row) exactly once.
* **Corpus**: every T.803 codestream `p0_*.j2k`, `p1_*.j2k` (skipped when absent) is parsed
  with `Limits.default` and `checkTileComp` runs on every tile-component; the totals over the
  image must equal `Header.checkWork`'s. OpenJPEG prints no geometry (`opj_dump` neither), so
  the corpus check is internal consistency against `Header`'s independent counting formulas.
-/

namespace JPEG2000.Tests.Geometry

open JPEG2000 JPEG2000.Header JPEG2000.Marker JPEG2000.TilePart JPEG2000.Tier2.Geometry

/-- Prints a failure line and returns 1 when `ok` is false. -/
def expect (name : String) (ok : Bool) : IO Nat := do
  if ok then return 0
  IO.eprintln s!"  FAIL geometry: {name}"
  return 1

/-- The value of an `Except`, if any. -/
def ok? {ε α : Type} : Except ε α → Option α
  | .ok a => some a
  | .error _ => none

/-- The error kind of an `Except` ("ok" on success). -/
def kind {α : Type} : Except Error α → String
  | .ok _ => "ok"
  | .error (.truncated ..) => "truncated"
  | .error (.malformed ..) => "malformed"
  | .error (.unsupported ..) => "unsupported"
  | .error (.limitExceeded _ k _ _) => s!"limit {k}"

/-- Coding parameters for tests: `nl` levels, code-block exponents, precinct exponents per
resolution (`[]` = none defined, 15/15). -/
def mkParams (nl cbx cby : Nat) (pp : List (Nat × Nat)) : CompParams :=
  { levels := nl, cbWidthExp := cbx, cbHeightExp := cby, cbStyle := 0,
    transform := .reversible53, precinctsDefined := !pp.isEmpty,
    precincts := if pp.isEmpty then (List.replicate (nl + 1) Precinct.default).toArray
      else (pp.map fun (a, b) => ({ ppx := a.toUInt8, ppy := b.toUInt8 } : Precinct)).toArray,
    quantStyle := 0, guardBits := 2, steps := #[], roiShift := 0 }

/-- A component with sub-sampling `dx × dy`. -/
def mkComp (dx dy : Nat) : Component :=
  { signed := false, depth := 8, dx := dx.toUInt8, dy := dy.toUInt8 }

/-- `a ⊆ b` for rectangles (an empty `a` is contained anywhere). -/
def within (a b : Rect) : Bool :=
  rectEmpty a || (b.x0 ≤ a.x0 && a.x1 ≤ b.x1 && b.y0 ≤ a.y0 && a.y1 ≤ b.y1)

/-- Whether a point lies in a rectangle. -/
def mem (r : Rect) (x y : Nat) : Bool := r.x0 ≤ x && x < r.x1 && r.y0 ≤ y && y < r.y1

/-- Sum of a list of naturals. -/
def sum (xs : List Nat) : Nat := xs.foldl (· + ·) 0

/-! ## Consistency checks -/

/-- Checks one resolution (see the module doc); `exhaustive` adds the per-sample and
per-grid-point checks. Returns (failures, code-blocks, precincts). -/
def checkRes (name : String) (tc : TileCompGeom) (r : Nat) (exhaustive : Bool) :
    IO (Nat × Nat × Nat) := do
  let L := Limits.default
  let nm := s!"{name} r={r}"
  match resolution L tc r with
  | .error e => return (← expect s!"{nm}: {e}" false, 0, 0)
  | .ok res =>
  let mut f := 0
  let p := tc.params
  let nl := p.levels
  f := f + (← expect s!"{nm}: numPrecincts"
    (res.numPrecincts == Header.numPrecincts res.rect (p.precincts.getD r Precinct.default)))
  let bandTotal := sum (res.bands.toList.map (·.numCodeBlocks))
  f := f + (← expect s!"{nm}: numCodeBlocks {bandTotal} vs {Header.numCodeBlocks tc.rect p r}"
    (bandTotal == Header.numCodeBlocks tc.rect p r))
  -- Band rectangles vs resolution rectangles (B-14/B-15).
  if r = 0 then
    f := f + (← expect s!"{nm}: LL = res 0" ((res.bands.map (·.rect)) == #[res.rect]))
  else
    let lo := resRect tc.rect nl (r - 1)
    match res.bands[0]?, res.bands[1]?, res.bands[2]? with
    | some hl, some lh, some hh =>
      f := f + (← expect s!"{nm}: band tiling"
        (hl.rect.width + lo.width == res.rect.width &&
         lh.rect.height + lo.height == res.rect.height &&
         hl.rect.y0 == lo.y0 && hl.rect.y1 == lo.y1 && lh.rect.x0 == lo.x0 &&
         lh.rect.x1 == lo.x1 && hh.rect.x0 == hl.rect.x0 && hh.rect.x1 == hl.rect.x1 &&
         hh.rect.y0 == lh.rect.y0 && hh.rect.y1 == lh.rect.y1 &&
         hl.band == .HL && lh.band == .LH && hh.band == .HH))
    | _, _, _ => f := f + (← expect s!"{nm}: three bands" false)
  -- Precincts.
  let mut precArea := 0
  let mut bandCb := res.bands.map fun _ => 0
  let mut bandArea := res.bands.map fun _ => 0
  let mut precs : Array PrecinctGeom := #[]
  for pi in [0:res.numPrecincts] do
    match precinct L res pi with
    | .error e => f := f + (← expect s!"{nm} p={pi}: {e}" false)
    | .ok pg =>
      if exhaustive then precs := precs.push pg
      let pnm := s!"{nm} p={pi}"
      let cx := (res.k0x + pg.px) * 2 ^ res.ppx
      let cy := (res.k0y + pg.py) * 2 ^ res.ppy
      f := f + (← expect s!"{pnm}: precinct rect {repr pg.rect}"
        (!rectEmpty pg.rect && within pg.rect res.rect &&
         within pg.rect ⟨cx, cy, cx + 2 ^ res.ppx, cy + 2 ^ res.ppy⟩ &&
         pg.index == pi && pg.py * res.pw + pg.px == pi))
      precArea := precArea + rectArea pg.rect
      f := f + (← expect s!"{pnm}: counts"
        (res.precinctCodeBlockCounts pi == pg.bands.map (·.codeBlocks.size)))
      -- Reference-grid position (B.12.1.3).
      f := f + (← expect s!"{pnm}: refX {pg.refX} refY {pg.refY}"
        (tc.tile.x0 ≤ pg.refX && pg.refX < tc.tile.x1 && tc.tile.y0 ≤ pg.refY &&
         pg.refY < tc.tile.y1 && res.visitsX pg.refX && res.visitsY pg.refY &&
         res.precinctColAt pg.refX == pg.px && res.precinctRowAt pg.refY == pg.py))
      for h : bi in [0:pg.bands.size] do
        let pb := pg.bands[bi]
        let some bg := res.bands[bi]? | f := f + (← expect s!"{pnm}: band count" false)
        let ex := bg.cbWidthExp
        let ey := bg.cbHeightExp
        let sx := 2 ^ res.bandPpx
        let sy := 2 ^ res.bandPpy
        let bcx := (res.k0x + pg.px) * sx
        let bcy := (res.k0y + pg.py) * sy
        f := f + (← expect s!"{pnm} b={bi}: precinct-band"
          (pb.band == bg.band && within pb.rect bg.rect &&
           within pb.rect ⟨bcx, bcy, bcx + sx, bcy + sy⟩ &&
           pb.codeBlocks.size == pb.cw * pb.ch && (rectEmpty pb.rect == (pb.cw * pb.ch == 0))))
        bandArea := bandArea.modify bi (· + rectArea pb.rect)
        bandCb := bandCb.modify bi (· + pb.codeBlocks.size)
        let mut cbArea := 0
        for cb in pb.codeBlocks do
          let cell : Rect := ⟨cb.gx * 2 ^ ex, cb.gy * 2 ^ ey, (cb.gx + 1) * 2 ^ ex,
            (cb.gy + 1) * 2 ^ ey⟩
          let i := cb.index % pb.cw
          let j := cb.index / pb.cw
          f := f + (← expect s!"{pnm} b={bi} cb={cb.index}: {repr cb.rect}"
            (!rectEmpty cb.rect && within cb.rect pb.rect && within cb.rect cell &&
             cb.gx == pb.rect.x0 / 2 ^ ex + i && cb.gy == pb.rect.y0 / 2 ^ ey + j))
          cbArea := cbArea + rectArea cb.rect
        f := f + (← expect s!"{pnm} b={bi}: code-block areas" (cbArea == rectArea pb.rect))
  f := f + (← expect s!"{nm}: precinct areas {precArea} vs {rectArea res.rect}"
    (precArea == rectArea res.rect))
  f := f + (← expect s!"{nm}: band areas"
    (bandArea == res.bands.map (rectArea ·.rect)))
  f := f + (← expect s!"{nm}: band code-blocks over precincts"
    (bandCb == res.bands.map (·.numCodeBlocks)))
  if exhaustive then
    -- Every resolution sample in exactly one precinct.
    for y in [res.rect.y0:res.rect.y1] do
      for x in [res.rect.x0:res.rect.x1] do
        let n := (precs.filter fun pg => mem pg.rect x y).size
        f := f + (← expect s!"{nm}: sample ({x},{y}) in {n} precincts" (n == 1))
    -- Every band sample in exactly one code-block.
    for h : bi in [0:res.bands.size] do
      let bg := res.bands[bi]
      for y in [bg.rect.y0:bg.rect.y1] do
        for x in [bg.rect.x0:bg.rect.x1] do
          let n := sum (precs.toList.map fun pg =>
            match pg.bands[bi]? with
            | some pb => (pb.codeBlocks.filter fun cb => mem cb.rect x y).size
            | none => 0)
          f := f + (← expect s!"{nm} b={bi}: sample ({x},{y}) in {n} code-blocks" (n == 1))
    -- Scanning the tile under B.12.1.3 visits every precinct column/row once.
    if res.numPrecincts > 0 then
      let cols := (List.range' tc.tile.x0 (tc.tile.x1 - tc.tile.x0)).filter res.visitsX
      f := f + (← expect s!"{nm}: visited columns {cols.map res.precinctColAt}"
        (cols.map res.precinctColAt == List.range res.pw))
      let rows := (List.range' tc.tile.y0 (tc.tile.y1 - tc.tile.y0)).filter res.visitsY
      f := f + (← expect s!"{nm}: visited rows {rows.map res.precinctRowAt}"
        (rows.map res.precinctRowAt == List.range res.ph))
  return (f, bandTotal, res.numPrecincts)

/-- Checks every resolution of a tile-component and the totals against
`Header.tileCompCounts`. Returns (failures, code-blocks, precincts). -/
def checkTileComp (name : String) (tc : TileCompGeom) (exhaustive : Bool) :
    IO (Nat × Nat × Nat) := do
  let mut f := 0
  let mut cb := 0
  let mut pr := 0
  for r in [0:tc.numResolutions] do
    let (f', c, p) ← checkRes name tc r exhaustive
    f := f + f'
    cb := cb + c
    pr := pr + p
  f := f + (← expect s!"{name}: totals ({cb}, {pr}) vs tileCompCounts"
    ((cb, pr) == tileCompCounts tc.rect tc.params))
  return (f, cb, pr)

/-! ## Hand cases -/

/-- Case A: tile `[3,13) × [2,9)`, `NL = 2`, 4×4 code-blocks, no precincts. -/
def caseA : TileCompGeom := tileComp ⟨3, 2, 13, 9⟩ (mkComp 1 1) (mkParams 2 2 2 [])

/-- Case B: tile `[7,50) × [5,31)` with `XRsiz = 3`, `YRsiz = 2`, `NL = 2`, 64×64
code-blocks and precincts (2,2), (1,1), (2,3): precincts smaller than code-blocks. -/
def caseB : TileCompGeom :=
  tileComp ⟨7, 5, 50, 31⟩ (mkComp 3 2) (mkParams 2 6 6 [(2, 2), (1, 1), (2, 3)])

/-- Case C: `NL = 0`, tile `[5,12) × [0,3)`, 4×4 code-blocks. -/
def caseC : TileCompGeom := tileComp ⟨5, 0, 12, 3⟩ (mkComp 1 1) (mkParams 0 2 2 [])

/-- Case D: a 1×1 tile at `(5,5)` with `NL = 3`. -/
def caseD : TileCompGeom := tileComp ⟨5, 5, 6, 6⟩ (mkComp 1 1) (mkParams 3 2 2 [])

/-- The band rectangles of resolution `r`. -/
def bandRects (tc : TileCompGeom) (r : Nat) : Option (List Rect) :=
  (ok? (resolution Limits.default tc r)).map fun res => res.bands.toList.map (·.rect)

/-- Hand-computed values (see each case's docstring; B-12, B-14, B-15, B-16). -/
def handValues : IO Nat := do
  let L := Limits.default
  let mut f := 0
  -- Case A: r0 LL [1,4)×[1,3); r1 HL x [1,3) y [1,3) (res0 y), LH x [1,4) y [0,2);
  -- r2 HL x [1,6) y [1,5) (res1 y), LH x [2,7) y [1,4), HH x [1,6) y [1,4).
  f := f + (← expect "A r0" (bandRects caseA 0 == some [⟨1, 1, 4, 3⟩]))
  f := f + (← expect "A r1" (bandRects caseA 1 ==
    some [⟨1, 1, 3, 3⟩, ⟨1, 0, 4, 2⟩, ⟨1, 0, 3, 2⟩]))
  f := f + (← expect "A r2" (bandRects caseA 2 ==
    some [⟨1, 1, 6, 5⟩, ⟨2, 1, 7, 4⟩, ⟨1, 1, 6, 4⟩]))
  f := f + (← expect "A res rects" ((ok? (resolution L caseA 1)).map (·.rect) ==
    some ⟨2, 1, 7, 5⟩ && (ok? (resolution L caseA 2)).map (·.rect) == some ⟨3, 2, 13, 9⟩))
  -- r2: HL 2×2 code-blocks (x ⌈6/4⌉ − 0, y ⌈5/4⌉ − 0), LH 2×1 (y ⌈4/4⌉ − 0), HH 2×1;
  -- one precinct.
  f := f + (← expect "A r2 counts" ((ok? (resolution L caseA 2)).map (fun r =>
    (r.numPrecincts, r.bands.toList.map (·.numCodeBlocks))) == some (1, [4, 2, 2])))
  match ok? (resolution L caseA 2 >>= fun res => precinct L res 0) with
  | none => f := f + (← expect "A r2 p0" false)
  | some pg =>
    let hl := (pg.bands[0]?.map fun pb => pb.codeBlocks.toList.map (·.rect)).getD []
    f := f + (← expect s!"A r2 HL code-blocks {repr hl}"
      (hl == [⟨1, 1, 4, 4⟩, ⟨4, 1, 6, 4⟩, ⟨1, 4, 4, 5⟩, ⟨4, 4, 6, 5⟩]))
  -- Case B: tile-component x ⌈7/3⌉..⌈50/3⌉ = [3,17), y ⌈5/2⌉..⌈31/2⌉ = [3,16).
  f := f + (← expect "B tc rect" (caseB.rect == ⟨3, 3, 17, 16⟩))
  match ok? (resolution L caseB 1), ok? (resolution L caseB 0) with
  | some r1, some r0 =>
    -- r1: [2,9) × [2,8), PP 1×1: pw = ⌈9/2⌉ − 1 = 4, ph = 4 − 1 = 3; xcb' = ycb' = 0.
    f := f + (← expect "B r1 grid" (r1.rect == ⟨2, 2, 9, 8⟩ && r1.pw == 4 && r1.ph == 3 &&
      r1.bands.toList.map (·.cbWidthExp) == [0, 0, 0] && r1.bandPpx == 0))
    -- step x = 3·2^(1+1) = 12, k0x = 1 → refX(0) = 12 (trx0 = 2 aligned), refX(1) = 24;
    -- step y = 2·2^(1+1) = 8, k0y = 1 → refY(0) = 8, refY(1) = 16.
    f := f + (← expect "B r1 ref" (r1.precinctRefX 0 == 12 && r1.precinctRefX 1 == 24 &&
      r1.precinctRefY 0 == 8 && r1.precinctRefY 1 == 16))
    -- r0: [1,5) × [1,4), PP 2×2: pw = ⌈5/4⌉ − 0 = 2, ph = 1; step x 3·2^4 = 48 →
    -- refX(0) = max(7, 0) = 7, refX(1) = 48; xcb' = min(6, 2) = 2.
    f := f + (← expect "B r0" (r0.rect == ⟨1, 1, 5, 4⟩ && r0.pw == 2 && r0.ph == 1 &&
      r0.precinctRefX 0 == 7 && r0.precinctRefX 1 == 48 && r0.precinctRefY 0 == 5 &&
      r0.bands.toList.map (·.cbWidthExp) == [2]))
    -- precinct 1 of r0: cell [4,8) ∩ [1,5) = [4,5).
    f := f + (← expect "B r0 p1" ((ok? (precinct L r0 1)).map (·.rect) == some ⟨4, 1, 5, 4⟩))
  | _, _ => f := f + (← expect "B resolutions" false)
  -- Case C: NL = 0, one LL band = tile-component, code-blocks ⌈12/4⌉ − ⌊5/4⌋ = 2 by 1.
  f := f + (← expect "C" ((ok? (resolution L caseC 0)).map (fun r =>
    (r.rect, r.numPrecincts, r.bands.toList.map (·.numCodeBlocks))) ==
      some (⟨5, 0, 12, 3⟩, 1, [2])))
  -- Case D: resolutions 0–2 empty; r3 = [5,6)², bands HL, LH empty, HH [2,3)².
  for r in [0:3] do
    f := f + (← expect s!"D r{r} empty"
      ((ok? (resolution L caseD r)).map (·.numPrecincts) == some 0))
  f := f + (← expect "D r3 bands" (bandRects caseD 3 ==
    some [⟨2, 3, 3, 3⟩, ⟨3, 2, 3, 3⟩, ⟨2, 2, 3, 3⟩]))
  f := f + (← expect "D r3 p0 counts" ((ok? (resolution L caseD 3)).map
    (·.precinctCodeBlockCounts 0) == some #[0, 0, 1]))
  return f

/-- Error cases. -/
def errors : IO Nat := do
  let L := Limits.default
  let mut f := 0
  f := f + (← expect "r > NL" (kind (resolution L caseA 3) == "malformed"))
  f := f + (← expect "p out of range"
    (kind (resolution L caseA 2 >>= fun r => precinct L r 1) == "malformed"))
  f := f + (← expect "empty res precinct"
    (kind (resolution L caseD 0 >>= fun r => precinct L r 0) == "malformed"))
  f := f + (← expect "maxPrecincts"
    (kind (resolution { L with maxPrecincts := 11 } caseB 1) == "limit precincts"))
  f := f + (← expect "maxPrecincts ok" (kind (resolution { L with maxPrecincts := 12 } caseB 1) == "ok"))
  f := f + (← expect "maxCodeBlocks (band)"
    (kind (resolution { L with maxCodeBlocks := 3 } caseA 2) == "limit codeBlocks"))
  -- Band-level check passes with 4, precinct-level check with a precomputed resolution.
  match ok? (resolution L caseA 2) with
  | some res => f := f + (← expect "maxCodeBlocks (precinct)"
      (kind (precinct { L with maxCodeBlocks := 3 } res 0) == "limit codeBlocks"))
  | none => f := f + (← expect "A r2" false)
  return f

/-- Exhaustive checks on the hand cases and a sweep of small parameter combinations:
tile origin x0 ∈ {0,1,3}, y0 ∈ {0,2}, size 9×7 or 23×18, NL ∈ {0,1,2,3}, sub-sampling
{1,2,3}×{1,2}, precincts none or (PP grows with r) or (small everywhere), code-blocks 4×4 or
8×4. -/
def sweep : IO Nat := do
  let mut f := 0
  for (nm, tc) in [("A", caseA), ("B", caseB), ("C", caseC), ("D", caseD)] do
    f := f + (← checkTileComp nm tc true).1
  let configs := Id.run do
    let mut acc : Array (Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat) := #[]
    for x0 in [0, 1, 3] do
      for y0 in [0, 2] do
        for (w, hh) in [(9, 7), (23, 18)] do
          for nl in [0, 1, 2, 3] do
            for (dx, dy) in [(1, 1), (2, 1), (3, 2)] do
              for ppk in [0, 1, 2] do
                for (cbx, cby) in [(2, 2), (3, 2)] do
                  acc := acc.push (x0, y0, w, hh, nl, dx, dy, ppk, cbx, cby)
    return acc
  let mut n := 0
  for (x0, y0, w, hh, nl, dx, dy, ppk, cbx, cby) in configs do
    let pp : List (Nat × Nat) := match ppk with
      | 0 => []
      | 1 => (List.range (nl + 1)).map fun r => (if r = 0 then 1 else r + 1, r + 1)
      | _ => (List.range (nl + 1)).map fun r => (if r = 0 then 0 else 1, if r = 0 then 1 else 2)
    let tile : Rect := ⟨x0, y0, x0 + w, y0 + hh⟩
    let tc := tileComp tile (mkComp dx dy) (mkParams nl cbx cby pp)
    n := n + 1
    f := f + (← checkTileComp s!"sweep {repr tile} nl={nl} d={dx},{dy} pp={pp} cb={cbx},{cby}"
      tc true).1
  f := f + (← expect s!"sweep size {n}" (n == 864))
  return f

/-! ## Corpus -/

/-- Directory of the T.803 conformance files. -/
def corpusDir : System.FilePath := "corpus/files/openjpeg-data/input/conformance"

/-- The T.803 codestreams. -/
def corpusFiles : List String :=
  ((List.range 16).map fun i => s!"p0_{if i + 1 < 10 then "0" else ""}{i + 1}.j2k") ++
  ((List.range 7).map fun i => s!"p1_0{i + 1}.j2k")

/-- Checks every tile-component of every T.803 codestream; skipped when absent. -/
def corpus : IO Nat := do
  let mut f := 0
  let mut seen := 0
  for file in corpusFiles do
    let path := corpusDir / file
    if !(← path.pathExists) then continue
    seen := seen + 1
    let data ← IO.FS.readBinFile path
    match parse Limits.default data with
    | .error e => f := f + (← expect s!"{file}: {e}" false)
    | .ok h =>
      let mut cb := 0
      let mut pr := 0
      for t in [0:numTiles h.siz] do
        for c in [0:h.siz.csiz] do
          match ofHeader h t c with
          | .error e => f := f + (← expect s!"{file} t={t} c={c}: {e}" false)
          | .ok tc =>
            f := f + (← expect s!"{file} t={t} c={c}: tile rect"
              (tc.tile == tileRect h.siz t &&
               (h.tiles.find? (·.index == t)).all (fun tp => tp.compRects[c]? == some tc.rect)))
            let (f', c', p') ← checkTileComp s!"{file} t={t} c={c}" tc false
            f := f + f'
            cb := cb + c'
            pr := pr + p'
      match checkWork Limits.default h.siz h.defaults h.tiles with
      | .ok tot => f := f + (← expect s!"{file}: image totals ({cb}, {pr}) vs checkWork"
          (tot.codeBlocks == cb && tot.precincts == pr))
      | .error e => f := f + (← expect s!"{file}: checkWork {e}" false)
  if seen == 0 then IO.println "  geometry: corpus absent, skipped"
  return f

/-- Runs the suite; returns the number of failures. -/
def run : IO Nat := do
  return (← handValues) + (← errors) + (← sweep) + (← corpus)

end JPEG2000.Tests.Geometry
