import JPEG2000.Header

/-!
# Tile-component geometry: resolutions, sub-bands, precincts, code-blocks
(Plan.md §3 rules 1–3, §4 S3; T.800 B.5, B.6, B.7, B.12.1.3–B.12.1.5)

Task 4.2. Given a tile-component (its rectangle on the component grid, B-12, and its merged
`CompParams`), this module computes on demand:

* **resolution `r`** (B.5, B-14): `trx0 = ⌈tcx0 / 2^(NL−r)⌉` etc. (`Header.resRect`), its
  precinct exponents `PPx, PPy` and precinct grid `pw × ph` (B-16, anchored at the origin of
  the resolution grid: `pw = ⌈trx1/2^PPx⌉ − ⌊trx0/2^PPx⌋`, 0 when `trx0 = trx1`);
* **sub-bands** (B.5, B-15): LL with `nb = NL` at `r = 0`; HL, LH, HH with
  `nb = NL − r + 1` above, `tbx0 = ⌈(tcx0 − 2^(nb−1)·xob) / 2^nb⌉` with
  `(xob, yob) = (1,0), (0,1), (1,1)`. All band coordinates are non-negative (the numerator
  is at least `−2^(nb−1)`), so truncated `Nat` subtraction computes them exactly;
* **precinct `p`** (B.6): `px = p mod pw`, `py = p / pw`; its rectangle in the resolution is
  the cell `[(⌊trx0/2^PPx⌋ + px)·2^PPx, +2^PPx)` intersected with the resolution; in each
  sub-band of `r > 0` the precinct cell has exponents `PPx − 1, PPy − 1` and origin
  `(⌊trx0/2^PPx⌋ + px)·2^(PPx−1)` (as OpenJPEG `opj_tcd_init_tile`:
  `tlcbgxstart = ⌈l_tl_prc_x_start / 2⌉`), intersected with the band;
* **code-blocks** (B.7): the partition of each precinct-band into cells of
  `2^xcb' × 2^ycb'` anchored at the band origin (`xcb' = min(xcb, PPx)` at `r = 0`,
  `min(xcb, PPx − 1)` above, `CompParams.effCbWidthExp`), intersected with the precinct-band,
  in raster order. Since `xcb' ≤` the band-level precinct exponent, code-block cells never
  straddle precinct cells, so the code-blocks of all precincts of a band are exactly the
  band's code-blocks (`Header.numCodeBlocks`);
* **reference-grid position of a precinct** (B.12.1.3–B.12.1.5, used by RPCL/PCRL/CPRL): the
  point `(x, y)` of the tile at which the position-driven progression visits it,
  `x = max(tx0, XRsiz · 2^(PPx + NL − r) · (⌊trx0/2^PPx⌋ + px))` (likewise `y`). At that `x`
  the B.12.1.3 condition holds (`x` divisible by `XRsiz·2^(PPx+NL−r)`, or `x = tx0` with
  `trx0·2^(NL−r)` not divisible by `2^(PPx+NL−r)`) and the precinct index computed there
  (`⌊⌈x / (XRsiz·2^(NL−r))⌉ / 2^PPx⌋ − ⌊trx0/2^PPx⌋`, as OpenJPEG `opj_pi_next_rpcl`) is `px`;
  every other grid point satisfying the condition maps to a different precinct. Hence each
  precinct is visited exactly once, at that point.

Empty resolutions have `pw = ph = 0` (no precincts, hence no packets); an empty precinct-band
(zero area) has zero code-blocks but its precinct still yields (empty) packets (B.6).
Nothing is materialised for a whole tile: `resolution` builds only the per-band summaries and
`precinct` only that precinct's code-blocks. Each count is checked against
`Limits.maxPrecincts` / `Limits.maxCodeBlocks` before anything of that size is built
(Plan.md §3 rule 3); the whole-image totals are already bounded by `Header.checkWork`.

`JPEG2000/` must not import `Spec/`, so the sub-band orientation is the local `Band` enum
(the mapping to `Spec.Tier1.Orientation` lives elsewhere).
-/

namespace JPEG2000.Tier2.Geometry

open JPEG2000 JPEG2000.Header JPEG2000.Marker JPEG2000.TilePart

/-! ## Sub-bands -/

/-- Sub-band orientation (T.800 B.5). -/
inductive Band where
  /-- Low-low (resolution 0 only). -/
  | LL
  /-- Horizontally high-pass, vertically low-pass. -/
  | HL
  /-- Horizontally low-pass, vertically high-pass. -/
  | LH
  /-- High-high. -/
  | HH
  deriving Repr, DecidableEq, Inhabited

/-- `xob` of B-15: 1 for HL and HH. -/
def Band.xob : Band → Nat
  | .HL | .HH => 1
  | _ => 0

/-- `yob` of B-15: 1 for LH and HH. -/
def Band.yob : Band → Nat
  | .LH | .HH => 1
  | _ => 0

/-- Band number 0 LL, 1 HL, 2 LH, 3 HH (OpenJPEG's orientation numbering, as in the ledger's
Tier-1 notes; within a resolution `r > 0` the position in `bandsOf r` is `index − 1`). -/
def Band.index : Band → Nat
  | .LL => 0
  | .HL => 1
  | .LH => 2
  | .HH => 3

/-- The bands of resolution `r` in packet order (B.9: LL at `r = 0`; HL, LH, HH above). -/
def bandsOf (r : Nat) : Array Band := if r = 0 then #[.LL] else #[.HL, .LH, .HH]

/-- The decomposition level `nb` of the bands of resolution `r` (B.5): `NL` at `r = 0`,
`NL − r + 1` above. -/
def bandLevel (nl r : Nat) : Nat := if r = 0 then nl else nl - r + 1

/-- One coordinate of a band (B-15): `⌈(c − 2^(nb−1)·o) / 2^nb⌉` (non-negative; the offset
is 0 when `o = 0` or `nb = 0`). -/
def bandCoord (c nb o : Nat) : Nat :=
  let off := if o = 0 ∨ nb = 0 then 0 else 2 ^ (nb - 1)
  cdivPow (c - off) nb

/-- The rectangle of a sub-band in band coordinates (B-15), from the tile-component
rectangle `tc`. -/
def bandRect (tc : Rect) (nb : Nat) (b : Band) : Rect :=
  { x0 := bandCoord tc.x0 nb b.xob, y0 := bandCoord tc.y0 nb b.yob,
    x1 := bandCoord tc.x1 nb b.xob, y1 := bandCoord tc.y1 nb b.yob }

/-- `true` when a rectangle has zero area. -/
def rectEmpty (r : Rect) : Bool := r.x1 ≤ r.x0 || r.y1 ≤ r.y0

/-- Area of a rectangle. -/
def rectArea (r : Rect) : Nat := r.width * r.height

/-- Intersection of a rectangle with the cell `[cx0, cx1) × [cy0, cy1)`; when they are
disjoint along an axis the result is clamped to zero extent (`x1 = x0`) on that axis. -/
def clip (r : Rect) (cx0 cy0 cx1 cy1 : Nat) : Rect :=
  let x0 := max r.x0 cx0
  let y0 := max r.y0 cy0
  { x0, y0, x1 := max x0 (min r.x1 cx1), y1 := max y0 (min r.y1 cy1) }

/-- Number of cells of size `2^e` anchored at 0 meeting `[a0, a1)` (0 if empty):
`⌈a1/2^e⌉ − ⌊a0/2^e⌋`. -/
def gridCount (a0 a1 e : Nat) : Nat := if a1 ≤ a0 then 0 else cdivPow a1 e - a0 / 2 ^ e

/-! ## Records -/

/-- A tile-component (B.3, B-12): the tile on the reference grid, its rectangle on the
component grid, the component's sub-sampling and its merged coding parameters. -/
structure TileCompGeom where
  /-- The tile rectangle on the reference grid (`tx0, ty0, tx1, ty1`, B-6/B-7). -/
  tile : Rect
  /-- The tile-component rectangle (`tcx0 = ⌈tx0 / XRsiz⌉` …, B-12). -/
  rect : Rect
  /-- `XRsiz`. -/
  dx : Nat
  /-- `YRsiz`. -/
  dy : Nat
  /-- Merged coding parameters of this tile-component. -/
  params : CompParams
  deriving Repr, Inhabited

/-- Summary of one sub-band of a resolution (B.5, B.7). -/
structure BandGeom where
  /-- Orientation. -/
  band : Band
  /-- Decomposition level `nb`. -/
  nb : Nat
  /-- Band rectangle in band coordinates (B-15). -/
  rect : Rect
  /-- Effective code-block width exponent `xcb'` (B.6). -/
  cbWidthExp : Nat
  /-- Effective code-block height exponent `ycb'` (B.6). -/
  cbHeightExp : Nat
  /-- Number of code-blocks of the band (over all precincts). -/
  numCodeBlocks : Nat
  deriving Repr, Inhabited

/-- One resolution level of a tile-component (B.5, B.6). -/
structure ResolutionGeom where
  /-- The tile-component. -/
  tc : TileCompGeom
  /-- Resolution index `r` (0 = lowest, `NL` = full). -/
  r : Nat
  /-- Resolution rectangle (B-14). -/
  rect : Rect
  /-- Precinct width exponent `PPx`. -/
  ppx : Nat
  /-- Precinct height exponent `PPy`. -/
  ppy : Nat
  /-- Precinct exponents at band level: `PPx` at `r = 0`, `PPx − 1` above. -/
  bandPpx : Nat
  /-- Precinct height exponent at band level. -/
  bandPpy : Nat
  /-- `⌊trx0 / 2^PPx⌋`: the precinct column of the first precinct. -/
  k0x : Nat
  /-- `⌊try0 / 2^PPy⌋`. -/
  k0y : Nat
  /-- Number of precincts across (B-16; 0 for an empty resolution). -/
  pw : Nat
  /-- Number of precincts down. -/
  ph : Nat
  /-- The sub-bands, in packet order. -/
  bands : Array BandGeom
  deriving Repr, Inhabited

/-- Number of precincts of a resolution. -/
def ResolutionGeom.numPrecincts (res : ResolutionGeom) : Nat := res.pw * res.ph

/-- A code-block (B.7). -/
structure CodeBlockGeom where
  /-- Raster index within its precinct-band (`j·cw + i`). -/
  index : Nat
  /-- Column of the code-block cell in the band's code-block grid (`⌊x0 / 2^xcb'⌋`). -/
  gx : Nat
  /-- Row of the code-block cell in the band's code-block grid. -/
  gy : Nat
  /-- Rectangle in band coordinates (non-empty). -/
  rect : Rect
  deriving Repr, Inhabited, DecidableEq

/-- The part of a precinct lying in one sub-band, with its code-blocks (B.6, B.7). -/
structure PrecinctBandGeom where
  /-- Orientation. -/
  band : Band
  /-- Precinct cell ∩ band, in band coordinates (may have zero area). -/
  rect : Rect
  /-- Code-blocks across (0 if empty). -/
  cw : Nat
  /-- Code-blocks down (0 if empty). -/
  ch : Nat
  /-- The `cw · ch` code-blocks, in raster order. -/
  codeBlocks : Array CodeBlockGeom
  deriving Repr, Inhabited

/-- A precinct of a resolution (B.6). -/
structure PrecinctGeom where
  /-- Precinct index `p = py · pw + px`. -/
  index : Nat
  /-- Column `px`. -/
  px : Nat
  /-- Row `py`. -/
  py : Nat
  /-- Precinct cell ∩ resolution, in resolution coordinates (non-empty). -/
  rect : Rect
  /-- Reference-grid `x` at which the position-driven progressions visit it (B.12.1.3). -/
  refX : Nat
  /-- Reference-grid `y` at which the position-driven progressions visit it. -/
  refY : Nat
  /-- One entry per sub-band of the resolution, in packet order. -/
  bands : Array PrecinctBandGeom
  deriving Repr, Inhabited

/-! ## Constructors -/

/-- The error location of this module. -/
def loc : Location := .at .tier2

/-- The geometry of a tile-component from its tile rectangle, component and parameters. -/
def tileComp (tile : Rect) (comp : Component) (p : CompParams) : TileCompGeom :=
  { tile, rect := compRect tile comp, dx := comp.dx.toNat, dy := comp.dy.toNat, params := p }

/-- The geometry of tile-component `(t, c)` of a parsed header: the tile's merged coding
parameters if it has tile-parts, the main-header defaults otherwise. -/
def ofHeader (h : Header) (t c : Nat) : Except Error TileCompGeom := do
  if t ≥ numTiles h.siz then throw (.malformed loc s!"tile index {t} out of range")
  let some comp := h.siz.components[c]? | throw (.malformed loc s!"component {c} out of range")
  let coding := match h.tiles.find? (·.index == t) with
    | some tp => tp.coding
    | none => h.defaults
  let some p := coding.comps[c]? | throw (.malformed loc s!"no parameters for component {c}")
  return tileComp (tileRect h.siz t) comp p

/-- The summary of one band of resolution `r` (no code-block is built). -/
def bandGeom (tc : TileCompGeom) (r : Nat) (b : Band) : BandGeom :=
  let nb := bandLevel tc.params.levels r
  let rect := bandRect tc.rect nb b
  let ex := tc.params.effCbWidthExp r
  let ey := tc.params.effCbHeightExp r
  { band := b, nb, rect, cbWidthExp := ex, cbHeightExp := ey,
    numCodeBlocks := gridCount rect.x0 rect.x1 ex * gridCount rect.y0 rect.y1 ey }

/-- Resolution `r` of a tile-component (B.5, B.6): rectangle, precinct grid and band
summaries. Fails when `r > NL` or when its precinct count or a band's code-block count
exceeds `Limits.maxPrecincts` / `Limits.maxCodeBlocks`. -/
def resolution (L : Limits) (tc : TileCompGeom) (r : Nat) : Except Error ResolutionGeom := do
  let nl := tc.params.levels
  if r > nl then throw (.malformed loc s!"resolution {r} > NL = {nl}")
  let rect := resRect tc.rect nl r
  let pp := tc.params.precincts.getD r Precinct.default
  let ppx := pp.ppx.toNat
  let ppy := pp.ppy.toNat
  let pw := gridCount rect.x0 rect.x1 ppx
  let ph := gridCount rect.y0 rect.y1 ppy
  L.check loc .precincts (pw * ph)
  let bands := (bandsOf r).map (bandGeom tc r)
  for b in bands do
    L.check loc .codeBlocks b.numCodeBlocks
  return { tc, r, rect, ppx, ppy,
           bandPpx := if r = 0 then ppx else ppx - 1,
           bandPpy := if r = 0 then ppy else ppy - 1,
           k0x := rect.x0 / 2 ^ ppx, k0y := rect.y0 / 2 ^ ppy, pw, ph, bands }

/-- Step of the position-driven progressions for this resolution along `x` on the reference
grid (B.12.1.3): `XRsiz · 2^(PPx + NL − r)`. -/
def ResolutionGeom.refStepX (res : ResolutionGeom) : Nat :=
  res.tc.dx * 2 ^ (res.ppx + (res.tc.params.levels - res.r))

/-- Step along `y`: `YRsiz · 2^(PPy + NL − r)`. -/
def ResolutionGeom.refStepY (res : ResolutionGeom) : Nat :=
  res.tc.dy * 2 ^ (res.ppy + (res.tc.params.levels - res.r))

/-- Reference-grid `x` of precinct column `px` (B.12.1.3, see the module doc):
`max(tx0, XRsiz · 2^(PPx + NL − r) · (⌊trx0/2^PPx⌋ + px))`. -/
def ResolutionGeom.precinctRefX (res : ResolutionGeom) (px : Nat) : Nat :=
  max res.tc.tile.x0 (res.refStepX * (res.k0x + px))

/-- Reference-grid `y` of precinct row `py`. -/
def ResolutionGeom.precinctRefY (res : ResolutionGeom) (py : Nat) : Nat :=
  max res.tc.tile.y0 (res.refStepY * (res.k0y + py))

/-- The precinct column visited at reference-grid `x` by the position-driven progressions
(OpenJPEG `opj_pi_next_*`: `⌊⌈x / (XRsiz·2^(NL−r))⌉ / 2^PPx⌋ − ⌊trx0/2^PPx⌋`). -/
def ResolutionGeom.precinctColAt (res : ResolutionGeom) (x : Nat) : Nat :=
  cdiv x (res.tc.dx * 2 ^ (res.tc.params.levels - res.r)) / 2 ^ res.ppx - res.k0x

/-- The precinct row visited at reference-grid `y`. -/
def ResolutionGeom.precinctRowAt (res : ResolutionGeom) (y : Nat) : Nat :=
  cdiv y (res.tc.dy * 2 ^ (res.tc.params.levels - res.r)) / 2 ^ res.ppy - res.k0y

/-- The B.12.1.3 visiting condition along `x` for this resolution at reference-grid `x`:
`x` divisible by `XRsiz·2^(PPx+NL−r)`, or `x = tx0` and `trx0·2^(NL−r)` not divisible by
`2^(PPx+NL−r)`. -/
def ResolutionGeom.visitsX (res : ResolutionGeom) (x : Nat) : Bool :=
  let l := res.tc.params.levels - res.r
  x % res.refStepX == 0 ||
    (x == res.tc.tile.x0 && (res.rect.x0 * 2 ^ l) % 2 ^ (res.ppx + l) != 0)

/-- The B.12.1.3 visiting condition along `y`. -/
def ResolutionGeom.visitsY (res : ResolutionGeom) (y : Nat) : Bool :=
  let l := res.tc.params.levels - res.r
  y % res.refStepY == 0 ||
    (y == res.tc.tile.y0 && (res.rect.y0 * 2 ^ l) % 2 ^ (res.ppy + l) != 0)

/-- The code-blocks of a precinct-band rectangle `pb` with code-block exponents `ex, ey`
(B.7), in raster order; `cw, ch` are the grid counts (precomputed and limit-checked). -/
def codeBlocksOf (pb : Rect) (ex ey cw ch : Nat) : Array CodeBlockGeom :=
  let gx0 := pb.x0 / 2 ^ ex
  let gy0 := pb.y0 / 2 ^ ey
  (List.range (cw * ch)).toArray.map fun k =>
    let i := k % cw
    let j := k / cw
    let gx := gx0 + i
    let gy := gy0 + j
    { index := k, gx, gy,
      rect := clip pb (gx * 2 ^ ex) (gy * 2 ^ ey) ((gx + 1) * 2 ^ ex) ((gy + 1) * 2 ^ ey) }

/-- The part of precinct `(px, py)` in one band, with its code-block grid size (B.6, B.7);
code-blocks are not built. -/
def precinctBandRect (res : ResolutionGeom) (b : BandGeom) (px py : Nat) : Rect :=
  let sx := 2 ^ res.bandPpx
  let sy := 2 ^ res.bandPpy
  let cx := (res.k0x + px) * sx
  let cy := (res.k0y + py) * sy
  clip b.rect cx cy (cx + sx) (cy + sy)

/-- Number of code-blocks of precinct `p` in each band (B.7), without building them. -/
def ResolutionGeom.precinctCodeBlockCounts (res : ResolutionGeom) (p : Nat) : Array Nat :=
  let px := if res.pw = 0 then 0 else p % res.pw
  let py := if res.pw = 0 then 0 else p / res.pw
  res.bands.map fun b =>
    let pb := precinctBandRect res b px py
    gridCount pb.x0 pb.x1 b.cbWidthExp * gridCount pb.y0 pb.y1 b.cbHeightExp

/-- Precinct `p` of a resolution (B.6, B.7): its rectangle, reference-grid position and,
per band, its code-blocks in raster order. Fails when `p ≥ pw · ph` or when a band's
code-block count exceeds `Limits.maxCodeBlocks` (checked before the code-blocks are
built). -/
def precinct (L : Limits) (res : ResolutionGeom) (p : Nat) : Except Error PrecinctGeom := do
  if p ≥ res.numPrecincts then
    throw (.malformed loc s!"precinct {p} ≥ {res.numPrecincts} in resolution {res.r}")
  let px := p % res.pw
  let py := p / res.pw
  let cx := (res.k0x + px) * 2 ^ res.ppx
  let cy := (res.k0y + py) * 2 ^ res.ppy
  let rect := clip res.rect cx cy (cx + 2 ^ res.ppx) (cy + 2 ^ res.ppy)
  let bands ← res.bands.mapM fun b => do
    let pb := precinctBandRect res b px py
    let cw := gridCount pb.x0 pb.x1 b.cbWidthExp
    let ch := gridCount pb.y0 pb.y1 b.cbHeightExp
    -- `cw` and `ch` are 0 together when `pb` is empty along either axis.
    let (cw, ch) := if cw = 0 ∨ ch = 0 then (0, 0) else (cw, ch)
    L.check loc .codeBlocks (cw * ch)
    let pbg : PrecinctBandGeom :=
      { band := b.band, rect := pb, cw, ch,
        codeBlocks := codeBlocksOf pb b.cbWidthExp b.cbHeightExp cw ch }
    return pbg
  return { index := p, px, py, rect, refX := res.precinctRefX px, refY := res.precinctRefY py,
           bands }

/-- Number of resolutions of a tile-component (`NL + 1`). -/
def TileCompGeom.numResolutions (tc : TileCompGeom) : Nat := tc.params.levels + 1

end JPEG2000.Tier2.Geometry
