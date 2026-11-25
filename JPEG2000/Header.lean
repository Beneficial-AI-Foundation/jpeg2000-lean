import JPEG2000.Error
import JPEG2000.Limits
import JPEG2000.Bytes
import JPEG2000.Box
import JPEG2000.Marker
import JPEG2000.TilePart

/-!
# Codestream header: main + tile-part headers merged and validated
(Plan.md §3 rules 1–3, §4 S2/S3; T.800 A.3, A.4, A.6, B.3–B.6, B.12, E.1, G.2)

Task 1.5. `parseCodestream` runs `Marker.parseMainHeader`, validates the image geometry
against `Limits` (before `TilePart.parseTileParts` allocates its per-tile array), parses the
pointer segments and the tile-parts, merges the coding parameters of every tile present and
validates the cross-segment constraints. `parse` also accepts a JP2 file (`Box.parseFile`),
parsing the codestream range of its `jp2c` box in place (all offsets stay absolute in the
input).

## Precedence (T.800 A.6, Tables A.3/A.4, and the precedence note of A.6)

For a tile-component (tile `t`, component `c`):

* coding style (`SPcod`/`SPcoc`, `Scoc` bit 0): tile COC(c) > tile COD > main COC(c) > main
  COD. In particular a **tile COD overrides a main COC** for every component without a tile
  COC (as OpenJPEG: `opj_j2k_read_cod` in a tile-part header rewrites every `tccp` of the
  tile via `opj_j2k_copy_tile_component_parameters`, and the tile's COC are then applied);
* quantisation: tile QCC(c) > tile QCD > main QCC(c) > main QCD; likewise a **tile QCD
  overrides a main QCC** (OpenJPEG `opj_j2k_read_qcd` copies the tile QCD to all components,
  tile QCC are applied over it);
* ROI shift: tile RGN(c) > main RGN(c) > 0 (A.6.3);
* `SGcod` (progression, layers, MCT) and the SOP/EPH flags: tile COD > main COD;
* progression changes: the tile's POC entries (all its tile-parts, in stream order) replace
  the main header's POC for that tile (A.6.6: "the POC in a tile-part header overrides the
  main header POC for that tile"). **Deviation from OpenJPEG**, which appends tile POCs to
  the main ones; no corpus stream has both.

Precedence is by kind, independent of the order of the segments in a header (T.800).

## Validation (cross-segment checks deferred by tasks 1.3/1.4; strictness choices)

* Before the tile-parts are read (Plan.md §3 rule 3): image width/height (`Xsiz − XOsiz`,
  `Ysiz − YOsiz`) ≤ `maxImageSide`, area ≤ `maxImageArea`, number of tiles ≤ `maxTiles`,
  number of tile-components (tiles × `Csiz`) ≤ `maxCodeBlocks` (each tile-component gets a
  `CompParams` record and later per-tile-component state; no separate `Limits` field
  exists), samples over all components (B.2, sub-sampled sizes) ≤ `maxWorkSamples`, output
  bytes (1/2/4/8 bytes per sample by bit depth) ≤ `maxDecodedBytes`.
* After the merge, from the geometry only (nothing allocated): total code-blocks over every
  tile of the tile grid (tiles without tile-parts use the main-header parameters) ≤
  `maxCodeBlocks`, total precincts ≤ `maxPrecincts`, total packets (layers × precincts,
  B.9) ≤ `maxPackets`. Code-blocks are counted exactly from B.5–B.7 with the effective
  code-block size `xcb' = min(xcb, PPx)` at resolution 0 and `min(xcb, PPx − 1)` above
  (B.6, `effCbWidthExp`).
* Strict (malformed): a second COC/QCC/RGN for the same component in one header (main, or
  one tile's tile-parts) — T.800 A.6.2/A.6.5/A.6.3 allow at most one (OpenJPEG keeps the
  last); quantisation step count: style 0 and 2 need **at least** `3·NL + 1` values for the
  component's `NL` (extra values are ignored, as OpenJPEG; "exactly" would reject a main QCD
  shared by components whose COC has fewer levels, which T.800 permits); style 1 (derived)
  needs `εo ≥ NL − 1` so that every derived exponent `εo − NL + nb` (E-5) is ≥ 0
  (OpenJPEG clamps at 0); MCT (`SGcod` = 1) with `Csiz < 3` is ignored (lenient, as
OpenJPEG; `Coding.mctApplies`; the benchmark `123.j2c` has it), otherwise components 0–2
need equal
  `XRsiz`/`YRsiz` (G.2: the RCT/ICT combine co-sited samples; OpenJPEG skips the MCT with a
  warning when the tile-component sizes differ) and the same wavelet transform in that tile
  (G.2: RCT with 5/3, ICT with 9/7); POC `CSpoc < Csiz`. Lenient (clamped later by the
  progression, B.12, as OpenJPEG): `CEpoc > Csiz`, `REpoc > NL + 1`, `LYEpoc > layers`.
* Not yet: reduced-resolution decoding constraints.
-/

namespace JPEG2000.Header

open JPEG2000 JPEG2000.Bytes JPEG2000.Marker JPEG2000.TilePart

/-! ## Records -/

/-- The merged coding parameters of one tile-component (T.800 A.6.1–A.6.5, after the
precedence rules of the module doc). -/
structure CompParams where
  /-- Number of decomposition levels `NL` (0…32); resolutions are `NL + 1`. -/
  levels : Nat
  /-- Code-block width exponent `xcb + 2` (2…10). -/
  cbWidthExp : Nat
  /-- Code-block height exponent `ycb + 2` (2…10). -/
  cbHeightExp : Nat
  /-- Code-block style byte (T.800 Table A.19). -/
  cbStyle : UInt8
  /-- Wavelet transform. -/
  transform : Transform
  /-- Precinct sizes were given (`Scod`/`Scoc` bit 0 of the segment that applies). -/
  precinctsDefined : Bool
  /-- Precinct size exponents per resolution 0…NL (`NL + 1` entries; 15/15 when none were
  given). -/
  precincts : Array Precinct
  /-- Quantisation style: 0 none, 1 scalar derived, 2 scalar expounded (T.800 Table A.28). -/
  quantStyle : Nat
  /-- Number of guard bits. -/
  guardBits : Nat
  /-- The step size of every sub-band, `3·NL + 1` entries in band order (LL, then HL, LH,
  HH per resolution 1…NL): style 0 exponents with mantissa 0; style 1 derived by E-5
  (`εb = εo − NL + nb`, `μb = μo`); style 2 as given. -/
  steps : Array StepSize
  /-- ROI max-shift value `SPrgn` (0 without RGN). -/
  roiShift : Nat
  deriving Repr, DecidableEq, Inhabited

/-- Coding parameters of a tile (or the main-header defaults): `SGcod`, `Scod` flags, the
progression changes and one `CompParams` per component. -/
structure Coding where
  /-- Progression order. -/
  progression : Progression
  /-- Number of layers. -/
  layers : Nat
  /-- Multiple component transform used. -/
  mct : Bool
  /-- SOP marker segments may be used. -/
  sop : Bool
  /-- EPH markers are used. -/
  eph : Bool
  /-- Progression order changes that apply (tile POC replaces main POC). -/
  poc : Array PocEntry
  /-- Per-component parameters, `Csiz` entries. -/
  comps : Array CompParams
  deriving Repr, DecidableEq, Inhabited

/-- A rectangle `[x0, x1) × [y0, y1)` on the reference grid or a component's grid. -/
structure Rect where
  /-- Left (inclusive). -/
  x0 : Nat
  /-- Top (inclusive). -/
  y0 : Nat
  /-- Right (exclusive). -/
  x1 : Nat
  /-- Bottom (exclusive). -/
  y1 : Nat
  deriving Repr, DecidableEq, Inhabited

/-- Width of a rectangle. -/
def Rect.width (r : Rect) : Nat := r.x1 - r.x0
/-- Height of a rectangle. -/
def Rect.height (r : Rect) : Nat := r.y1 - r.y0

/-- One tile present in the codestream: its geometry (B.3), merged parameters and its
tile-parts. -/
structure TileParams where
  /-- Tile index (`Isot`). -/
  index : Nat
  /-- Tile rectangle on the reference grid (`tx0, ty0, tx1, ty1`, B-6/B-7). -/
  rect : Rect
  /-- Tile-component rectangles (`tcx0 = ⌈tx0 / XRsiz⌉` …, B-12), `Csiz` entries. -/
  compRects : Array Rect
  /-- Merged coding parameters. -/
  coding : Coding
  /-- The tile's tile-parts and pointer data (task 1.4). -/
  tile : Tile
  deriving DecidableEq, Inhabited

/-- A parsed and validated codestream header. -/
structure Header where
  /-- Image and tile size. -/
  siz : SIZ
  /-- Number of tile columns. -/
  numTilesX : Nat
  /-- Number of tile rows. -/
  numTilesY : Nat
  /-- The main-header coding parameters (OpenJPEG's "default tile"), used for tiles
  without tile-part overrides. -/
  defaults : Coding
  /-- The tiles that have tile-parts, sorted by index. -/
  tiles : Array TileParams
  /-- `TLM` segments sorted by `Ztlm`. -/
  tlm : Array TLM
  /-- `PPM` data. -/
  ppm : PPMData
  /-- The main header as parsed (for reference). -/
  main : MainHeader
  /-- The codestream's byte range in the input. -/
  codestream : Box.ByteRange
  /-- The JP2 container (`none` for a raw codestream). -/
  container : Option Box.Container
  deriving DecidableEq, Inhabited

/-! ## Geometry (T.800 B.2–B.7) -/

/-- `⌈a / b⌉` on naturals (0 when `b = 0`). -/
def cdiv (a b : Nat) : Nat := (a + b - 1) / b

/-- `⌈a / 2^k⌉` on integers. -/
def cdivPowI (a : Int) (k : Nat) : Int := -((-a) / ((2 : Int) ^ k))

/-- `⌈a / 2^k⌉` on naturals. -/
def cdivPow (a k : Nat) : Nat := cdiv a (2 ^ k)

/-- The tile rectangle of tile `t` (B.3, B-6/B-7): `p = t mod numTilesX`, `q = t / numTilesX`,
`tx0 = max(XTOsiz + p·XTsiz, XOsiz)`, `tx1 = min(XTOsiz + (p+1)·XTsiz, Xsiz)`. -/
def tileRect (s : SIZ) (t : Nat) : Rect :=
  let nx := numTilesX s
  let p := if nx = 0 then 0 else t % nx
  let q := if nx = 0 then 0 else t / nx
  let xt := s.xtsiz.toNat
  let yt := s.ytsiz.toNat
  { x0 := max (s.xtosiz.toNat + p * xt) s.xosiz.toNat
    y0 := max (s.ytosiz.toNat + q * yt) s.yosiz.toNat
    x1 := min (s.xtosiz.toNat + (p + 1) * xt) s.xsiz.toNat
    y1 := min (s.ytosiz.toNat + (q + 1) * yt) s.ysiz.toNat }

/-- A rectangle on a component's grid (B-12): every coordinate `⌈· / XRsiz⌉`, `⌈· / YRsiz⌉`. -/
def compRect (r : Rect) (c : Component) : Rect :=
  { x0 := cdiv r.x0 c.dx.toNat, y0 := cdiv r.y0 c.dy.toNat,
    x1 := cdiv r.x1 c.dx.toNat, y1 := cdiv r.y1 c.dy.toNat }

/-- The image area on the reference grid (B.2). -/
def imageRect (s : SIZ) : Rect :=
  { x0 := s.xosiz.toNat, y0 := s.yosiz.toNat, x1 := s.xsiz.toNat, y1 := s.ysiz.toNat }

/-- The effective code-block width exponent at resolution `r` (B.6): `min(xcb, PPx)` at
resolution 0, `min(xcb, PPx − 1)` above. -/
def CompParams.effCbWidthExp (p : CompParams) (r : Nat) : Nat :=
  let ppx := (p.precincts.getD r Precinct.default).ppx.toNat
  if r = 0 then min p.cbWidthExp ppx else min p.cbWidthExp (ppx - 1)

/-- The effective code-block height exponent at resolution `r` (B.6). -/
def CompParams.effCbHeightExp (p : CompParams) (r : Nat) : Nat :=
  let ppy := (p.precincts.getD r Precinct.default).ppy.toNat
  if r = 0 then min p.cbHeightExp ppy else min p.cbHeightExp (ppy - 1)

/-- The rectangle of resolution `r` of a tile-component with `NL` levels (B-14):
`trx0 = ⌈tcx0 / 2^(NL − r)⌉` etc. -/
def resRect (tc : Rect) (nl r : Nat) : Rect :=
  { x0 := cdivPow tc.x0 (nl - r), y0 := cdivPow tc.y0 (nl - r),
    x1 := cdivPow tc.x1 (nl - r), y1 := cdivPow tc.y1 (nl - r) }

/-- Number of precincts of a resolution (B-16): `(⌈trx1/2^PPx⌉ − ⌊trx0/2^PPx⌋) · (…y…)`,
0 when the resolution is empty. -/
def numPrecincts (rr : Rect) (pp : Precinct) : Nat :=
  if rr.x1 ≤ rr.x0 ∨ rr.y1 ≤ rr.y0 then 0
  else
    (cdivPow rr.x1 pp.ppx.toNat - rr.x0 / 2 ^ pp.ppx.toNat) *
      (cdivPow rr.y1 pp.ppy.toNat - rr.y0 / 2 ^ pp.ppy.toNat)

/-- One band extent along one axis (B-15): `⌈(tc0 − 2^(nb−1)·o) / 2^nb⌉ … ⌈(tc1 − …)/2^nb⌉`,
then the number of code-blocks `⌈b1/2^e⌉ − ⌊b0/2^e⌋` along it (0 if the band is empty). -/
def bandBlocks1 (c0 c1 nb o e : Nat) : Nat :=
  let off : Int := if o = 0 ∨ nb = 0 then 0 else (2 : Int) ^ (nb - 1)
  let b0 := cdivPowI ((c0 : Int) - off) nb
  let b1 := cdivPowI ((c1 : Int) - off) nb
  if b1 ≤ b0 then 0
  else (cdivPowI b1 e - (b0 / (2 : Int) ^ e)).toNat

/-- Number of code-blocks of resolution `r` of a tile-component (B.5–B.7): over its bands
(LL at `r = 0`, `nb = NL`; HL, LH, HH above, `nb = NL − r + 1`), counted with the effective
code-block size. -/
def numCodeBlocks (tc : Rect) (p : CompParams) (r : Nat) : Nat :=
  let ex := p.effCbWidthExp r
  let ey := p.effCbHeightExp r
  if r = 0 then
    bandBlocks1 tc.x0 tc.x1 p.levels 0 ex * bandBlocks1 tc.y0 tc.y1 p.levels 0 ey
  else
    let nb := p.levels - r + 1
    let bx (o : Nat) := bandBlocks1 tc.x0 tc.x1 nb o ex
    let by_ (o : Nat) := bandBlocks1 tc.y0 tc.y1 nb o ey
    bx 1 * by_ 0 + bx 0 * by_ 1 + bx 1 * by_ 1

/-- Code-blocks and precincts of a tile-component (sums over its resolutions). -/
def tileCompCounts (tc : Rect) (p : CompParams) : Nat × Nat :=
  (List.range (p.levels + 1)).foldl (fun (cb, pr) r =>
    (cb + numCodeBlocks tc p r,
     pr + numPrecincts (resRect tc p.levels r) (p.precincts.getD r Precinct.default))) (0, 0)

/-! ## Merging (T.800 A.6 precedence) -/

/-- `Error.malformed` at a marker-stage offset. -/
def malformed (pos : Nat) (what : String) : Error := .malformed (.atOffset .marker pos) what

/-- Per-component overrides: an array of `csiz` options, set from `(component, value)`
pairs; a second value for the same component is malformed. -/
def overrides {α : Type} (pos : Nat) (what : String) (csiz : Nat) (items : Array (UInt16 × α)) :
    Except Error (Array (Option α)) :=
  items.foldlM (init := Array.replicate csiz none) fun acc (c, v) =>
    match acc[c.toNat]? with
    | some none => .ok (acc.setIfInBounds c.toNat (some v))
    | some (some _) => .error (malformed pos s!"second {what} for component {c}")
    | none => .error (malformed pos s!"{what} component {c} ≥ Csiz {csiz}")

/-- The step sizes of all `3·NL + 1` bands from a quantisation segment (T.800 A.6.4, E-5);
see the module doc for the count rules. -/
def bandSteps (pos : Nat) (nl : Nat) (q : Quantization) : Except Error (Array StepSize) := do
  let nb := 3 * nl + 1
  match q with
  | .none es =>
    if es.size < nb then
      throw (malformed pos s!"{es.size} exponents for {nb} sub-bands (NL = {nl})")
    return (es.extract 0 nb).map fun e => { exponent := e, mantissa := 0 }
  | .expounded ss =>
    if ss.size < nb then
      throw (malformed pos s!"{ss.size} step sizes for {nb} sub-bands (NL = {nl})")
    return ss.extract 0 nb
  | .derived b =>
    if b.exponent.toNat + 1 < nl then
      throw (malformed pos s!"derived exponent {b.exponent} < NL − 1 = {nl - 1}")
    return (Array.range nb).map fun i =>
      if i = 0 then b
      else { b with exponent := b.exponent - ((i - 1) / 3).toUInt8 }

/-- The parameters of one tile-component from its coding style, quantisation and ROI shift. -/
def mkComp (pos : Nat) (s : CodingStyle) (q : QCD) (roi : Nat) : Except Error CompParams := do
  let nl := s.levels.toNat
  let steps ← bandSteps pos nl q.quant
  return {
    levels := nl, cbWidthExp := s.cbWidthExp, cbHeightExp := s.cbHeightExp,
    cbStyle := s.cbStyle, transform := s.transform,
    precinctsDefined := s.precincts.isSome,
    precincts := (Array.range (nl + 1)).map s.precinct,
    quantStyle := (match q.quant with | .none _ => 0 | .derived _ => 1 | .expounded _ => 2),
    guardBits := q.guardBits.toNat, steps, roiShift := roi }

/-- Per-component overrides of one header (main or tile). -/
structure Overrides where
  /-- COC styles per component. -/
  coc : Array (Option CodingStyle)
  /-- QCC parameters per component. -/
  qcc : Array (Option QCD)
  /-- RGN shifts per component. -/
  rgn : Array (Option Nat)

/-- Collects the per-component overrides of a header. -/
def mkOverrides (pos csiz : Nat) (coc : Array COC) (qcc : Array QCC) (rgn : Array RGN) :
    Except Error Overrides := do
  return { coc := ← overrides pos "COC" csiz (coc.map fun c => (c.component, c.style)),
           qcc := ← overrides pos "QCC" csiz (qcc.map fun q => (q.component, q.params)),
           rgn := ← overrides pos "RGN" csiz (rgn.map fun g => (g.component, g.shift.toNat)) }

/-- Checks the POC entries (`CSpoc < Csiz`). -/
def checkPoc (pos csiz : Nat) (poc : Array PocEntry) : Except Error Unit :=
  poc.forM fun e =>
    if e.compStart.toNat < csiz then .ok ()
    else .error (malformed pos s!"POC CSpoc {e.compStart} ≥ Csiz {csiz}")

/-- Whether the multiple component transform is applied to a tile with this coding (G.2):
`SGcod` MCT set and `Csiz ≥ 3`. With `Csiz < 3` the flag is ignored (as OpenJPEG, which
warns; seen in the benchmark file `123.j2c`). -/
def Coding.mctApplies (s : SIZ) (c : Coding) : Bool := c.mct && s.csiz ≥ 3

/-- Checks the MCT constraints of a tile's (or the default) coding (G.2). -/
def checkMct (pos : Nat) (s : SIZ) (c : Coding) : Except Error Unit := do
  if !c.mct then return
  -- Csiz < 3: the MCT is not applied (lenient, as OpenJPEG; see `mctApplies`).
  let some c0 := s.components[0]? | return
  let some c1 := s.components[1]? | return
  let some c2 := s.components[2]? | return
  unless c0.dx = c1.dx ∧ c0.dx = c2.dx ∧ c0.dy = c1.dy ∧ c0.dy = c2.dy do
    throw (malformed pos "MCT over components 0–2 with different sub-sampling")
  let ts := (c.comps.extract 0 3).map (·.transform)
  unless ts.all (· = ts.getD 0 .reversible53) do
    throw (malformed pos "MCT over components 0–2 with different wavelet transforms")

/-- The main-header coding parameters (OpenJPEG's "default tile"). -/
def mainCoding (mh : MainHeader) : Except Error Coding := do
  let pos := mh.endPos
  let csiz := mh.siz.csiz
  let ov ← mkOverrides pos csiz mh.coc mh.qcc mh.rgn
  let comps ← (Array.range csiz).mapM fun c =>
    mkComp pos ((ov.coc.getD c none).getD mh.cod.style) ((ov.qcc.getD c none).getD mh.qcd)
      ((ov.rgn.getD c none).getD 0)
  let poc := mh.poc.foldl (fun a p => a ++ p.entries) #[]
  checkPoc pos csiz poc
  let c : Coding := { progression := mh.cod.progression, layers := mh.cod.layers.toNat,
                      mct := mh.cod.mct, sop := mh.cod.sop, eph := mh.cod.eph, poc, comps }
  checkMct pos mh.siz c
  return c

/-- The segments of a tile's tile-part headers, by kind. -/
structure TileSegs where
  /-- COD (at most one, first tile-part). -/
  cod : Option COD := none
  /-- QCD (at most one, first tile-part). -/
  qcd : Option QCD := none
  /-- COC segments. -/
  coc : Array COC := #[]
  /-- QCC segments. -/
  qcc : Array QCC := #[]
  /-- RGN segments. -/
  rgn : Array RGN := #[]
  /-- POC entries of every tile-part, in stream order. -/
  poc : Array PocEntry := #[]

/-- Sorts a tile's header segments by kind. -/
def tileSegs (t : Tile) : TileSegs :=
  t.parts.foldl (fun acc p => p.segments.foldl (fun acc s =>
    match s with
    | .cod c => { acc with cod := some c }
    | .qcd q => { acc with qcd := some q }
    | .coc c => { acc with coc := acc.coc.push c }
    | .qcc q => { acc with qcc := acc.qcc.push q }
    | .rgn g => { acc with rgn := acc.rgn.push g }
    | .poc p => { acc with poc := acc.poc ++ p.entries }
    | _ => acc) acc) {}

/-- The merged coding of one tile (precedence of the module doc). `mainOv` are the main
header's overrides, `defaults` its coding (shared when the tile overrides nothing). -/
def tileCoding (mh : MainHeader) (mainOv : Overrides) (defaults : Coding) (t : Tile) :
    Except Error Coding := do
  let pos := (t.parts[0]?.map (·.pos)).getD mh.endPos
  let csiz := mh.siz.csiz
  let ts := tileSegs t
  let poc := if ts.poc.isEmpty then defaults.poc else ts.poc
  checkPoc pos csiz poc
  let cod := ts.cod.getD mh.cod
  let sg : Coding :=
    { defaults with
      progression := cod.progression, layers := cod.layers.toNat, mct := cod.mct,
      sop := cod.sop, eph := cod.eph, poc := poc }
  let c ← if ts.cod.isNone ∧ ts.qcd.isNone ∧ ts.coc.isEmpty ∧ ts.qcc.isEmpty ∧ ts.rgn.isEmpty
    then pure sg
    else do
      let ov ← mkOverrides pos csiz ts.coc ts.qcc ts.rgn
      let comps ← (Array.range csiz).mapM fun c =>
        let style := match ov.coc.getD c none, ts.cod with
          | some s, _ => s
          | none, some d => d.style
          | none, none => (mainOv.coc.getD c none).getD mh.cod.style
        let quant := match ov.qcc.getD c none, ts.qcd with
          | some q, _ => q
          | none, some q => q
          | none, none => (mainOv.qcc.getD c none).getD mh.qcd
        let roi := match ov.rgn.getD c none with
          | some s => s
          | none => (mainOv.rgn.getD c none).getD 0
        mkComp pos style quant roi
      pure { sg with comps }
  checkMct pos mh.siz c
  return c

/-! ## Validation against `Limits` (Plan.md §3 rule 3, §4 S3) -/

/-- Output bytes per sample for a bit depth (1, 2, 4 or 8). -/
def bytesPerSample (depth : Nat) : Nat :=
  if depth ≤ 8 then 1 else if depth ≤ 16 then 2 else if depth ≤ 32 then 4 else 8

/-- Geometry checks before any per-tile allocation (see the module doc). -/
def checkGeometry (L : Limits) (mh : MainHeader) : Except Error Unit := do
  let s := mh.siz
  let loc : Location := .atOffset .marker 2
  let img := imageRect s
  L.check loc .imageSide img.width
  L.check loc .imageSide img.height
  L.check loc .imageArea (img.width * img.height)
  let nt := numTiles s
  L.check loc .tiles nt
  L.check loc .codeBlocks (nt * s.csiz)
  let samples := s.components.toList.map fun c =>
    let r := compRect img c
    (r.width * r.height, bytesPerSample c.depth.toNat)
  L.check loc .workSamples (samples.foldl (fun a (n, _) => a + n) 0)
  L.check loc .decodedBytes (samples.foldl (fun a (n, b) => a + n * b) 0)

/-- Totals of the work estimate: code-blocks, precincts, packets. -/
structure Totals where
  /-- Code-blocks so far. -/
  codeBlocks : Nat := 0
  /-- Precincts so far. -/
  precincts : Nat := 0
  /-- Packets so far. -/
  packets : Nat := 0

/-- Adds one tile's code-blocks, precincts and packets to the totals and checks them. -/
def addTile (L : Limits) (s : SIZ) (t : Nat) (c : Coding) (tot : Totals) :
    Except Error Totals := do
  let loc : Location := .atOffset .marker 2
  let rect := tileRect s t
  let mut tot := tot
  for i in [0:s.csiz] do
    let p := c.comps.getD i default
    let comp := s.components.getD i default
    let (cb, pr) := tileCompCounts (compRect rect comp) p
    tot := { codeBlocks := tot.codeBlocks + cb, precincts := tot.precincts + pr,
             packets := tot.packets + c.layers * pr }
    L.check loc .codeBlocks tot.codeBlocks
    L.check loc .precincts tot.precincts
    L.check loc .packets tot.packets
  return tot

/-- Checks the code-block, precinct and packet totals over the whole tile grid. `tiles` is
sorted by index; tiles without tile-parts use `defaults`. -/
def checkWork (L : Limits) (s : SIZ) (defaults : Coding) (tiles : Array TileParams) :
    Except Error Totals := do
  let mut tot : Totals := {}
  let mut j := 0
  for t in [0:numTiles s] do
    let here := match tiles[j]? with
      | some tp => if tp.index = t then some tp.coding else none
      | none => none
    if here.isSome then j := j + 1
    tot ← addTile L s t (here.getD defaults) tot
  return tot

/-! ## Drivers -/

/-- Parses and validates a raw codestream occupying `range` of `data` (SOC … EOC): main
header, geometry checks, pointer segments, tile-parts, merge, cross-segment and work
checks. Offsets in the result are absolute in `data`. -/
def parseCodestreamIn (L : Limits) (data : ByteArray) (range : Box.ByteRange)
    (container : Option Box.Container) : Except Error Header := do
  let r ← rangeReader data { offset := range.start, length := range.len }
  let (mh, r) ← parseMainHeader L r
  checkGeometry L mh
  let defaults ← mainCoding mh
  let (tlm, ppm) ← parsePointers L mh data
  let tiles ← parseTileParts L mh r
  let mainOv ← mkOverrides mh.endPos mh.siz.csiz mh.coc mh.qcc mh.rgn
  let tps ← tiles.mapM fun t => do
    let coding ← tileCoding mh mainOv defaults t
    let rect := tileRect mh.siz t.index
    let tp : TileParams := { index := t.index, rect, coding, tile := t,
                             compRects := mh.siz.components.map (compRect rect) }
    return tp
  let _ ← checkWork L mh.siz defaults tps
  return { siz := mh.siz, numTilesX := numTilesX mh.siz, numTilesY := numTilesY mh.siz,
           defaults, tiles := tps, tlm, ppm, main := mh, codestream := range, container }

/-- Parses and validates a raw JPEG 2000 codestream (the whole of `data`). -/
def parseCodestream (L : Limits) (data : ByteArray) : Except Error Header := do
  L.check (.atOffset .marker 0) .inputBytes data.size
  parseCodestreamIn L data ⟨0, data.size⟩ none

/-- Parses a JP2 file or a raw codestream (T.800 Annex I via `Box.parseFile`), then the
codestream in place. `container` is `some` for a JP2 file. -/
def parse (L : Limits) (data : ByteArray) : Except Error Header := do
  let c ← Box.parseFile L data
  parseCodestreamIn L data c.codestream (if c.fileType.isSome then some c else none)

end JPEG2000.Header
