import Encode.Tier1
import Encode.Tier2
import Encode.Marker
import Encode.TilePart
import Spec.DWT53
import Spec.DWT97
import Spec.MCT
import Spec.Quant
import JPEG2000.Header
import JPEG2000.Tier2.Packet

/-!
# Reference encoder: image → raw J2K codestream (one tile, one layer, LRCP, plain mode)

Plan.md §5.3 (a deliberately simple encoder for tests and proofs, never in the public API),
§4 C10 (`decode (encode img) = img` for 5/3 + RCT — proved later, task 7.3). Task 7.2.
T.800 clauses: A.2–A.6 (main header: SOC, SIZ, COD, QCD), A.4 (SOT, SOD, EOC), G.1 (DC level
shift), G.2 (RCT, ICT), Annex F.4 (forward DWT), E.1 (quantisation), Annex D (Tier-1, via
`Encode.Tier1`), B.6–B.12 (precincts, code-blocks, packets, LRCP, via `Encode.Tier2`).

## The codestream

One tile covering the image (`XOsiz = YOsiz = 0`, `XTsiz = Xsiz`, `YTsiz = Ysiz`), no
sub-sampling (`XRsiz = YRsiz = 1`), one tile-part; `COD`: LRCP, one layer, `NL` levels,
code-block exponents as given, code-block style 0 (plain), default precincts (`PPx = PPy =
15`), no `SOP`/`EPH`, MCT when asked for and `Csiz ≥ 3`; `QCD`: style 0 (reversible, no
quantisation) or style 2 (irreversible, scalar expounded with mantissa 0). The geometry of
code-blocks and the `Mb` of every band are computed with the **decoder's own functions**
(`Header.mkComp` on the very `COD`/`QCD` written, `Tier2.Geometry.resolution`/`precinct`,
`JPEG2000.Tier2.Packet.bandMb`), so the encoder puts code-blocks exactly where the decoder looks.

## Pipeline, stage by stage (each the mirror of a decoder stage)

1. DC level shift (G.1): unsigned samples minus `2^(depth−1)` (`Spec.MCT.dcOffset`).
2. MCT (G.2) on components 0–2 when enabled and `Csiz ≥ 3`: `Spec.MCT.rctFwd` (reversible;
   inverse theorem C7 `rctInv_rctFwd`) or `Spec.MCT.ictFwd` (irreversible, over `Rat`).
3. Forward DWT (F.4): `Spec.DWT53.sdMulti` (reversible; inverse theorem C6
   `srMulti_sdMulti`), or the 9/7 `Spec.DWT97.sd2d`/`deinterleave` level by level over `Rat`
   with the LL input of every level rounded down to a multiple of `2^−32` (`sdMulti97`; keeps
   the rationals small — the variant is lossy anyway).
4. Bands (B.5, B-15): band `b` of resolution `r` is read from the decomposition in band
   coordinates on `Tier2.Geometry.bandRect` — `sdMulti` deinterleaves, so a band's grid is
   indexed by band coordinates exactly as B-15 numbers them (the tile origin is 0).
5. Quantisation (E.1): reversible — none (index = coefficient); irreversible — deadzone
   scalar quantiser `q = sign(y)·⌊|y| / Δb⌋` with `Δb = 2^(Rb − εb)` (`μb = 0`).
6. Exponents and guard bits (E.1, E-2: `Mb = G + εb − 1`): reversible — `G = 2`,
   `εb = max(Rb, Kb − 1)` with `Rb = depth + log2 gain_b` (largest over components) and `Kb`
   the bit count of the band's largest magnitude, so `Mb ≥ Kb`; irreversible —
   `εb = Rb − stepLog2` (fixed by the step) and `G = max(2, max_b (Kb − εb + 1))` (≤ 7).
7. Tier-1 (Annex D): `Encode.Tier1.encodeCodeBlock` on each code-block's indices (the mirror
   of the spec Tier-1 decoder; MQ theorem C1).
8. Tier-2 (B.9–B.12): `Encode.Tier2.encodeTileLRCP` (tag trees through
   `Spec.TagTree.encodeAll`, C4).
9. Markers (A.2–A.6): `Encode.Marker` / `Encode.TilePart` serialisers (round trips proved in
   `Spec.MarkerRoundTrip` / `Spec.TilePartRoundTrip`).

Errors (`JPEG2000.Error`, stage `decode` — the encoder has no stage of its own): image or
parameters out of range (no components, size mismatch, sample outside the bit depth,
`NL > 32`, code-block exponents outside `2…10` or summing above 12, an exponent above 31,
more than 7 guard bits needed, more than 164 passes in a code-block (Table B.4), a tile-part longer than `2^32 − 1` bytes).
-/

namespace JPEG2000.Encode

open JPEG2000 JPEG2000.Marker JPEG2000.Header JPEG2000.Tier2.Geometry

/-! ## Inputs -/

/-- One image component: bit depth, signedness and samples in raster order. -/
structure Component where
  /-- Bit depth (1…38). -/
  depth : Nat
  /-- Signed samples. -/
  signed : Bool := false
  /-- `width · height` samples, raster order. -/
  samples : Array Int
  deriving Repr, Inhabited

/-- An image: all components share the image size (no sub-sampling). -/
structure Image where
  /-- Width in samples. -/
  width : Nat
  /-- Height in samples. -/
  height : Nat
  /-- The components (1…16384). -/
  comps : Array Component
  deriving Repr, Inhabited

/-- Encoding parameters. -/
structure Params where
  /-- Decomposition levels `NL` (0…32). -/
  levels : Nat := 5
  /-- Code-block width exponent (2…10). -/
  cbWidthExp : Nat := 6
  /-- Code-block height exponent (2…10, sum with the width exponent ≤ 12). -/
  cbHeightExp : Nat := 6
  /-- `true`: 5/3 + RCT, lossless; `false`: 9/7 + ICT, quantised. -/
  reversible : Bool := true
  /-- Use the multiple component transform (only when there are at least 3 components). -/
  mct : Bool := true
  /-- Irreversible only: `log₂` of the quantisation step `Δb` of every band (`εb = Rb −
  stepLog2`). -/
  stepLog2 : Int := -1
  deriving Repr, Inhabited

/-- What the encoder produced for one code-block (for tests). -/
structure BlockInfo where
  /-- Component. -/
  comp : Nat
  /-- Resolution. -/
  res : Nat
  /-- Precinct index. -/
  prec : Nat
  /-- Band index within the precinct (packet order). -/
  band : Nat
  /-- Code-block index within the precinct-band (raster). -/
  block : Nat
  /-- Coding passes. -/
  numPasses : Nat
  /-- Zero bit-planes. -/
  zeroBitPlanes : Nat
  /-- The codeword. -/
  data : ByteArray

/-- The encoder's result: the codestream and, for tests, its code-blocks (component,
resolution, precinct, band, code-block order) and its quantisation choices. -/
structure Encoded where
  /-- The raw J2K codestream (SOC … EOC). -/
  codestream : ByteArray
  /-- Every code-block. -/
  blocks : Array BlockInfo
  /-- Guard bits written. -/
  guardBits : Nat
  /-- Band exponents `εb` written (band order). -/
  exponents : Array Nat

/-- The error location of the encoder. -/
def loc : Location := .at .decode

/-- An argument error. -/
def bad (what : String) : Error := .malformed loc s!"encoder: {what}"

/-! ## Transforms -/

/-- The DWT rectangle of a `w × h` tile at the origin. -/
def dwtRect (w h : Nat) : Spec.DWT53.Rect := { u0 := 0, u1 := w, v0 := 0, v1 := h }

/-- The sample at `(u, v)` of a raster plane of width `w` (0 outside). -/
def at2 {α : Type} [Inhabited α] (a : Array α) (w : Nat) (u v : Int) : α :=
  a.getD (v.toNat * w + u.toNat) default

/-- `x` rounded down to a multiple of `2^−F`. -/
def roundDown (F : Nat) (x : Rat) : Rat := ((x * ((2 ^ F : Nat) : Rat)).floor : Rat) / ((2 ^ F : Nat) : Rat)

/-- The 9/7 forward transform over `n` levels (F.4.1) as `Spec.DWT97.sdMulti`, except that
the input of every level is rounded down to a multiple of `2^−32` and materialised. -/
def sdMulti97 : Spec.DWT53.Rect → Nat → Spec.DWT97.Grid → Spec.DWT97.Dec
  | _, 0, g => ⟨g, []⟩
  | r, n + 1, g =>
    let g' := Spec.DWT97.memo r ⟨fun u v => roundDown 32 (g.get u v)⟩
    let b := Spec.DWT97.deinterleave (Spec.DWT97.sd2d r g')
    let d := sdMulti97 r.half n b.1
    ⟨d.ll, (b.2.1, b.2.2.1, b.2.2.2) :: d.details⟩

/-- Band `b` of resolution `r` of a 5/3 decomposition with `nl` levels. -/
def band53 (d : Spec.DWT53.Dec) (nl r : Nat) (b : Band) : Spec.DWT53.Grid :=
  if r = 0 then d.ll
  else match d.details[nl - r]?, b with
    | some (g, _, _), .HL => g
    | some (_, g, _), .LH => g
    | some (_, _, g), .HH => g
    | _, _ => ⟨fun _ _ => 0⟩

/-- Band `b` of resolution `r` of a 9/7 decomposition with `nl` levels. -/
def band97 (d : Spec.DWT97.Dec) (nl r : Nat) (b : Band) : Spec.DWT97.Grid :=
  if r = 0 then d.ll
  else match d.details[nl - r]?, b with
    | some (g, _, _), .HL => g
    | some (_, g, _), .LH => g
    | some (_, _, g), .HH => g
    | _, _ => ⟨fun _ _ => 0⟩

/-- `2^e` as a rational for an integer `e`. -/
def pow2 (e : Int) : Rat :=
  if e ≥ 0 then ((2 ^ e.toNat : Nat) : Rat) else 1 / ((2 ^ (-e).toNat : Nat) : Rat)

/-- The deadzone scalar quantiser (E.1, encoder side): `sign(y)·⌊|y| / Δ⌋`. -/
def quantise (delta y : Rat) : Int :=
  if y < 0 then -((-y) / delta).floor else (y / delta).floor

/-! ## Bands -/

/-- A band's coefficients (quantisation indices) on its rectangle, raster order. -/
structure BandData where
  /-- Band rectangle (band coordinates, B-15). -/
  rect : Header.Rect
  /-- `rect.width · rect.height` indices. -/
  vals : Array Int
  deriving Inhabited

/-- Materialises band `b` of resolution `r` (decomposition level `bandLevel nl r`) of a tile
`w × h` from a coefficient function in band coordinates. -/
def bandData (w h nl r : Nat) (b : Band) (get : Int → Int → Int) : BandData :=
  let rect := bandRect { x0 := 0, y0 := 0, x1 := w, y1 := h } (bandLevel nl r) b
  let bw := rect.width
  { rect, vals := Array.ofFn (n := bw * rect.height) fun i =>
      get (rect.x0 + i.val % bw : Nat) (rect.y0 + i.val / bw : Nat) }

/-- All bands of a component: `[r][i]` is the `i`-th band of `bandsOf r`. -/
def compBands (w h nl : Nat) (get : Nat → Band → Int → Int → Int) : Array (Array BandData) :=
  (Array.range (nl + 1)).map fun r => (bandsOf r).map fun b => bandData w h nl r b (get r b)

/-- The largest magnitude of a band. -/
def BandData.maxMag (d : BandData) : Nat := d.vals.foldl (fun m v => max m v.natAbs) 0

/-! ## Code-blocks -/

/-- The Tier-1 orientation of a band. -/
def orient : Band → Spec.Tier1.Orientation
  | .LL => .LL
  | .HL => .HL
  | .LH => .LH
  | .HH => .HH

/-- The indices of a code-block (rectangle in band coordinates) from its band's data. -/
def blockCoeffs (d : BandData) (cb : Header.Rect) : Array Int :=
  let cw := cb.width
  let bw := d.rect.width
  Array.ofFn (n := cw * cb.height) fun i =>
    d.vals.getD ((cb.y0 + i.val / cw - d.rect.y0) * bw + (cb.x0 + i.val % cw - d.rect.x0)) 0

/-- Encodes the code-blocks of one tile-component: per resolution, per precinct, the Tier-2
band inputs, and the code-block records. -/
def encodeComp (L : Limits) (tc : TileCompGeom) (c : Nat) (bands : Array (Array BandData)) :
    Except Error (Array (Array (Array Tier2.BandIn)) × Array BlockInfo) := do
  let mut out : Array (Array (Array Tier2.BandIn)) := #[]
  let mut infos : Array BlockInfo := #[]
  for r in [0:tc.params.levels + 1] do
    let res ← resolution L tc r
    let mut precs : Array (Array Tier2.BandIn) := #[]
    for p in [0:res.numPrecincts] do
      let pg ← precinct L res p
      let mut bis : Array Tier2.BandIn := #[]
      for bi in [0:pg.bands.size] do
        let some pb := pg.bands[bi]? | throw (bad "band index")
        let d := (bands.getD r #[]).getD bi default
        let mb := JPEG2000.Tier2.Packet.bandMb tc.params r pb.band
        let mut blocks : Array Tier2.BlockIn := #[]
        for cb in pb.codeBlocks do
          let o ← Tier1.encodeCodeBlock cb.rect.width cb.rect.height (orient pb.band) mb
            (blockCoeffs d cb.rect)
          if o.numPasses > 164 then throw (bad "more than 164 coding passes in a code-block")
          let data : ByteArray := ⟨o.bytes.toArray⟩
          blocks := blocks.push { numPasses := o.numPasses, zeroBitPlanes := o.zeroBitPlanes, data }
          infos := infos.push { comp := c, res := r, prec := p, band := bi, block := cb.index,
                                numPasses := o.numPasses, zeroBitPlanes := o.zeroBitPlanes, data }
        bis := bis.push { cw := pb.cw, ch := pb.ch, maxZero := mb + tc.params.roiShift, blocks }
      precs := precs.push bis
    out := out.push precs
  return (out, infos)

/-! ## Checks -/

/-- Validates the image and parameters (see the module doc). -/
def check (L : Limits) (p : Params) (img : Image) : Except Error Unit := do
  if img.width = 0 ∨ img.height = 0 then throw (bad "empty image")
  L.check loc .imageSide img.width
  L.check loc .imageSide img.height
  L.check loc .imageArea (img.width * img.height)
  if img.comps.size = 0 then throw (bad "no components")
  L.check loc .components img.comps.size
  if p.levels > 32 then throw (bad "more than 32 decomposition levels")
  unless 2 ≤ p.cbWidthExp ∧ p.cbWidthExp ≤ 10 ∧ 2 ≤ p.cbHeightExp ∧ p.cbHeightExp ≤ 10 ∧
      p.cbWidthExp + p.cbHeightExp ≤ 12 do
    throw (bad "code-block exponents outside 2…10 or summing above 12")
  for c in img.comps do
    unless 1 ≤ c.depth ∧ c.depth ≤ 38 do throw (bad s!"bit depth {c.depth}")
    if c.samples.size ≠ img.width * img.height then throw (bad "sample count ≠ width · height")
    let lo := Spec.MCT.sampleMin c.signed c.depth
    let hi := Spec.MCT.sampleMax c.signed c.depth
    unless c.samples.all (fun s => lo ≤ s ∧ s ≤ hi) do
      throw (bad "sample outside the component's range")

/-! ## Coefficients of every component -/

/-- The DC-shifted planes (G.1). -/
def shifted (img : Image) : Array (Array Int) :=
  img.comps.map fun c => c.samples.map (· - Spec.MCT.dcOffset c.signed c.depth)

/-- Applies a pointwise three-component transform to planes 0–2. -/
def mct3 {α : Type} [Inhabited α] (f : Spec.MCT.Triple α → Spec.MCT.Triple α)
    (ps : Array (Array α)) : Array (Array α) :=
  let p0 := ps.getD 0 #[]
  let p1 := ps.getD 1 #[]
  let p2 := ps.getD 2 #[]
  let ts := Array.ofFn (n := p0.size) fun i =>
    f (p0.getD i default, p1.getD i default, p2.getD i default)
  let ps := ps.setIfInBounds 0 (ts.map (·.1))
  let ps := ps.setIfInBounds 1 (ts.map (·.2.1))
  ps.setIfInBounds 2 (ts.map (·.2.2))

/-- Reversible path: per component, all bands of the 5/3 decomposition (indices =
coefficients). -/
def bands53 (p : Params) (img : Image) (useMct : Bool) : Array (Array (Array BandData)) :=
  let ps := shifted img
  let ps := if useMct then mct3 Spec.MCT.rctFwd ps else ps
  let w := img.width
  let h := img.height
  ps.map fun pl =>
    let d := Spec.DWT53.sdMulti (dwtRect w h) p.levels ⟨fun u v => at2 pl w u v⟩
    compBands w h p.levels fun r b => (band53 d p.levels r b).get

/-- Irreversible path: per component, all bands of the 9/7 decomposition, quantised with
`Δb = 2^(depth_c + gain_b − εb)` (`exps` in band order). -/
def bands97 (p : Params) (img : Image) (useMct : Bool) (exps : Array Nat) :
    Array (Array (Array BandData)) :=
  let ps : Array (Array Rat) := (shifted img).map (·.map fun (x : Int) => (↑x : Rat))
  let ps := if useMct then mct3 Spec.MCT.ictFwd ps else ps
  let w := img.width
  let h := img.height
  (ps.zip img.comps).map fun (pl, c) =>
    let d := sdMulti97 (dwtRect w h) p.levels ⟨fun u v => at2 pl w u v⟩
    compBands w h p.levels fun r b =>
      let i := Spec.Quant.bandIndex r b
      let delta := pow2 ((c.depth + Spec.Quant.log2Gain b : Nat) - (exps.getD i 0 : Int))
      fun u v => quantise delta ((band97 d p.levels r b).get u v)

/-- The band ranges `Rb` (largest over components), band order. -/
def ranges (p : Params) (img : Image) : Array Nat :=
  let dmax := img.comps.foldl (fun m c => max m c.depth) 0
  (Array.range (p.levels + 1)).flatMap fun r =>
    (bandsOf r).map fun b => dmax + Spec.Quant.log2Gain b

/-- The largest band magnitude over components, band order. -/
def bandMaxMags (bs : Array (Array (Array BandData))) (nl : Nat) : Array Nat :=
  (Array.range (nl + 1)).flatMap fun r =>
    (bandsOf r).mapIdx fun i _ =>
      bs.foldl (fun m comp => max m ((comp.getD r #[]).getD i default).maxMag) 0

/-! ## The encoder -/

/-- **Encodes an image** (see the module doc), returning the codestream with the per
code-block details. -/
def encodeDetailed (p : Params) (img : Image) : Except Error Encoded := do
  let L := Limits.default
  check L p img
  let useMct := p.mct && img.comps.size ≥ 3
  let rs := ranges p img
  -- Coefficients, exponents and guard bits.
  let (bands, guard, exps) ← if p.reversible then do
      let bands := bands53 p img useMct
      let ks := (bandMaxMags bands p.levels).map Tier1.numBits
      let exps := (rs.zip ks).map fun (rb, k) => max rb (k - 1)
      pure (bands, 2, exps)
    else do
      let exps ← rs.mapM fun (rb : Nat) => (do
        let e : Int := (rb : Int) - p.stepLog2
        if e < 0 then throw (bad s!"step 2^{p.stepLog2} gives a negative exponent")
        pure e.toNat : Except Error Nat)
      let bands := bands97 p img useMct exps
      let ks := (bandMaxMags bands p.levels).map Tier1.numBits
      let g := (ks.zip exps).foldl (fun g (k, e) => max g (k + 1 - e)) 2
      pure (bands, g, exps)
  if exps.any (· > 31) then throw (bad "a band exponent above 31")
  if guard > 7 then throw (bad s!"{guard} guard bits needed")
  -- Header records.
  let w := img.width
  let h := img.height
  let siz : SIZ :=
    { rsiz := 0, xsiz := w.toUInt32, ysiz := h.toUInt32, xosiz := 0, yosiz := 0,
      xtsiz := w.toUInt32, ytsiz := h.toUInt32, xtosiz := 0, ytosiz := 0,
      components := img.comps.map fun c =>
        { signed := c.signed, depth := c.depth.toUInt8, dx := 1, dy := 1 } }
  let style : CodingStyle :=
    { levels := p.levels.toUInt8, xcb := (p.cbWidthExp - 2).toUInt8,
      ycb := (p.cbHeightExp - 2).toUInt8, cbStyle := 0,
      transform := if p.reversible then .reversible53 else .irreversible97, precincts := none }
  let cod : COD :=
    { sop := false, eph := false, progression := .lrcp, layers := 1, mct := useMct, style }
  let qcd : QCD :=
    { guardBits := guard.toUInt8,
      quant := if p.reversible then .none (exps.map (·.toUInt8))
               else .expounded (exps.map fun e => { exponent := e.toUInt8, mantissa := 0 }) }
  -- The decoder's own view of the coding parameters and geometry.
  let params ← mkComp 0 style qcd 0
  let tile : Header.Rect := { x0 := 0, y0 := 0, x1 := w, y1 := h }
  -- Tier-1 and Tier-2.
  let mut prec := #[]
  let mut infos := #[]
  for c in [0:img.comps.size] do
    let tc := tileComp tile (siz.components.getD c default) params
    let (pc, ic) ← encodeComp L tc c (bands.getD c #[])
    prec := prec.push pc
    infos := infos ++ ic
  let data := Tier2.encodeTileLRCP prec
  -- Markers.
  let psot := 12 + 2 + data.size
  if psot ≥ 2 ^ 32 then throw (bad "tile-part longer than 2^32 − 1 bytes")
  let sot : TilePart.SOT := { isot := 0, psot := psot.toUInt32, tpsot := 0, tnsot := 1 }
  let m := Encode.Marker.pack
  let codestream :=
    m (Encode.Marker.be16 Code.SOC) ++
    Encode.Marker.segment Code.SIZ (Encode.Marker.serializeSIZ siz) ++
    Encode.Marker.segment Code.COD (Encode.Marker.serializeCOD cod) ++
    Encode.Marker.segment Code.QCD (Encode.Marker.serializeQCD qcd) ++
    Encode.Marker.segment Code.SOT (Encode.TilePart.serializeSOT sot) ++
    m (Encode.Marker.be16 Code.SOD) ++ data ++ m (Encode.Marker.be16 Code.EOC)
  return { codestream, blocks := infos, guardBits := guard, exponents := exps }

/-- **Encodes an image** into a raw J2K codestream (SOC … EOC). -/
def encode (p : Params) (img : Image) : Except Error ByteArray :=
  (·.codestream) <$> encodeDetailed p img

end JPEG2000.Encode
