import JPEG2000.Error
import JPEG2000.Limits
import JPEG2000.Bytes
import JPEG2000.Box
import JPEG2000.Decode

/-!
# Colour: colour space, palette, component mapping, channel definitions (Plan.md §1, §9)

Task 6.1. Turns the JP2 header boxes read by `JPEG2000.Box` (T.800 Annex I) into what a
renderer needs, without any colour management of its own:

* **Colour space** (T.800 I.5.3.3; ISO 15444-2 M.11.7): `resolveColourSpace` picks the first
  `colr` box whose `METH` is 1 (enumerated: 16 sRGB, 17 greyscale, 18 sYCC, other `EnumCS`
  values kept with their code) or 2 (restricted ICC, profile bytes passed through as a byte
  range). `METH` 3 (any ICC, JPX) and 4 (vendor) boxes are **skipped** for rendering, as
  OpenJPEG does (`opj_jp2_read_colr`) and as T.800 Table I.9 requires of a conforming JP2
  reader; `PREC`/`APPROX` are ignored (JP2 reader behaviour). MuPDF and pdf.js both decode JPX
  with OpenJPEG and therefore inherit this choice; the PDF's own `/ColorSpace` overrides all
  of it anyway (ISO 32000-2 §7.4.9, Plan.md §9). The `METH` 3/4 bytes stay available in
  `Jp2Header.colr` for a consumer that wants them. No ICC transform is done here (pass-through).
* **Palette and component mapping** (I.5.3.4, I.5.3.5): `resolveMapping` validates `pclr`
  and `cmap` against the codestream's component count; `applyMapping` / `applyPalette` build
  the output channels. A palette index outside `0 … NE−1` is **clamped** (negative → 0, too
  large → `NE − 1`), as `opj_jp2_apply_pclr`. Unsigned entries keep all their stored bytes,
  even when padding bits are set, as in OpenJPEG. Signed entries are sign-extended from their
  declared depth (T.800 I.5.3.4). Wide table entries retain their exact integer values.
* **Channel definitions** (I.5.3.6): `channelLayout` validates `cdef` (every channel defined
  exactly once, indices and associations in range, as `opj_jp2_check_color`) and orders the
  colour channels by association, identifies the whole-image opacity channel (`Typ` 1, or 2
  for premultiplied) and lists the rest.
* **sYCC → sRGB** (T.800 I.5.3.3 Table I.10, IEC 61966-2-1 Amd. 1): `syccToRgb`, integer
  arithmetic transcribing OpenJPEG's `sycc_to_rgb` (`R = Y + 1.402·Cr`, `G = Y − (0.344·Cb +
  0.714·Cr)`, `B = Y + 1.772·Cb`, products truncated toward zero, clamped to `[0, 2^p − 1]`,
  chroma offset `2^(p−1)` with `p` the luma depth). Sub-sampled chroma is upsampled by
  replication on the reference grid. For 4:2:2 and 4:2:0 we follow OpenJPEG 2.5.3's edge
  rules. An odd vertical origin in 4:2:0 gives the first row raw zero chroma. An odd
  horizontal origin gives the first column raw zero chroma on every 4:2:2 row and on the
  first row of each 4:2:0 pair (including a final unpaired row). The second row of each
  pair uses the first stored chroma sample at the left edge.

Bounds (Plan.md §3 rules 2 and 3): channel counts are checked against `maxComponents`, every
new plane against `maxWorkSamples` (and their running total too) before allocation; every
loop runs on fuel equal to a size already checked.
-/

namespace JPEG2000.Color

open JPEG2000 JPEG2000.Box JPEG2000.Bytes

/-- `malformed` at the colour stage. -/
def malformed (what : String) : Error := .malformed (.at .color) what

/-- `unsupported` at the colour stage. -/
def unsupported (what : String) : Error := .unsupported (.at .color) what

/-! ## Colour space -/

/-- The colour space a JP2 reader resolves from the `colr` boxes (T.800 I.5.3.3). -/
inductive ColourSpace where
  /-- Enumerated sRGB (`EnumCS` 16). -/
  | sRGB
  /-- Enumerated greyscale (`EnumCS` 17). -/
  | greyscale
  /-- Enumerated sYCC (`EnumCS` 18); see `syccToRgb`. -/
  | sYCC
  /-- Another enumerated colour space (JPX, ISO 15444-2 Table M.25: e.g. 12 CMYK, 14 CIELab,
  20 e-sRGB, 21 ROMM-RGB), with its parameter bytes. -/
  | enumerated (enumCs : UInt32) (params : ByteRange)
  /-- A restricted ICC profile (`METH` 2): the profile bytes in the input, passed through. -/
  | icc (profile : ByteRange)
  /-- No usable colour specification (raw codestream, or only `METH` 3/4 boxes). -/
  | unknown
  deriving Repr, DecidableEq, Inhabited

/-- The colour space used for rendering: the first `colr` with `METH` 1 or 2; `METH` 3 and 4
boxes are skipped (decision of task 6.1, as OpenJPEG; see the module doc). -/
def resolveColourSpace (h : Jp2Header) : ColourSpace :=
  match h.colr.find? (fun c => c.meth == 1 || c.meth == 2) with
  | some { method := .enumerated cs params, .. } =>
    if cs == enumSRGB then .sRGB
    else if cs == enumGrey then .greyscale
    else if cs == enumSYCC then .sYCC
    else .enumerated cs params
  | some { method := .icc _ profile, .. } => .icc profile
  | _ => .unknown

/-- Number of colours of a JPX enumerated colour space (ISO 15444-2 Table M.25), if known. -/
def enumColours (cs : UInt32) : Option Nat :=
  match cs.toNat with
  | 0 | 15 | 17 => some 1
  | 1 | 3 | 4 | 9 | 11 | 14 | 16 | 18 | 19 | 20 | 21 | 22 | 23 | 24 => some 3
  | 12 | 13 => some 4
  | _ => none

/-- Number of colours of an ICC profile from its header's data colour space signature
(ICC.1 7.2.6, bytes 16–19 of the profile), if recognised. -/
def iccColours (data : ByteArray) (r : ByteRange) : Option Nat :=
  if r.len < 20 || r.start + r.len > data.size then none else
  let b (k : Nat) : Nat := (data.data[r.start + 16 + k]?.getD 0).toNat
  let sig : Nat := ((b 0 * 256 + b 1) * 256 + b 2) * 256 + b 3
  if sig == 0x47524159 then some 1                                  -- 'GRAY'
  else if sig == 0x52474220 || sig == 0x58595A20 || sig == 0x4C616220   -- 'RGB ' 'XYZ ' 'Lab '
      || sig == 0x4C757620 || sig == 0x59436272 || sig == 0x59787920    -- 'Luv ' 'YCbr' 'Yxy '
      || sig == 0x48535620 || sig == 0x484C5320 || sig == 0x434D5920    -- 'HSV ' 'HLS ' 'CMY '
    then some 3
  else if sig == 0x434D594B then some 4                             -- 'CMYK'
  else if sig % 0x1000000 == 0x434C52 then                          -- 'nCLR', n = 2…F
    let n := sig / 0x1000000
    if 0x32 ≤ n ∧ n ≤ 0x39 then some (n - 0x30)
    else if 0x41 ≤ n ∧ n ≤ 0x46 then some (n - 0x41 + 10) else none
  else none

/-- Number of colour channels a colour space has (`data` is the input, for ICC headers). -/
def ColourSpace.numColours (data : ByteArray) : ColourSpace → Option Nat
  | .sRGB | .sYCC => some 3
  | .greyscale => some 1
  | .enumerated cs _ => enumColours cs
  | .icc r => iccColours data r
  | .unknown => none

/-! ## Palette and component mapping (T.800 I.5.3.4, I.5.3.5) -/

/-- Where an output channel's samples come from. -/
inductive Source where
  /-- `MTYP` 0: the codestream component, used directly. -/
  | direct (cmp : Nat)
  /-- `MTYP` 1: the component's samples index palette column `col`. -/
  | palette (cmp col : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- The validated channel mapping: one source per output channel, and the palette if any
channel uses it. -/
structure Mapping where
  /-- One source per output channel, in channel order. -/
  sources : Array Source
  /-- The palette (present when some source is `palette`). -/
  palette : Option Palette := none
  deriving Repr, DecidableEq, Inhabited

/-- Depth (1…38) and signedness of a `B_i` / `BPC`-style byte. -/
def bitsDepth (b : UInt8) : Nat × Bool := ((b &&& 0x7F).toNat + 1, b &&& 0x80 != 0)

/-- Check the palette shape and the maximum Part 1 precision. -/
def checkPalette (p : Palette) : Except Error Unit := do
  if p.ne == 0 || p.npc == 0 then throw (malformed "pclr: NE or NPC is 0")
  if p.bits.size != p.npc || p.entries.size != p.ne * p.npc then
    throw (malformed "pclr: entry table does not match NE × NPC")
  for b in p.bits do
    if (bitsDepth b).1 > 38 then throw (unsupported "pclr: column depth exceeds 38 bits")

/-- Validates one `cmap` entry against `nComps` components and the palette. -/
def entrySource (nComps : Nat) (p : Palette) (e : CmapEntry) : Except Error Source := do
  if e.cmp.toNat ≥ nComps then
    throw (malformed s!"cmap: component {e.cmp} ≥ Csiz {nComps}")
  match e.mtyp with
  | 0 =>
    if e.pcol != 0 then throw (malformed s!"cmap: direct use with PCOL {e.pcol} ≠ 0")
    return .direct e.cmp.toNat
  | 1 =>
    if e.pcol.toNat ≥ p.npc then
      throw (malformed s!"cmap: palette column {e.pcol} ≥ NPC {p.npc}")
    return .palette e.cmp.toNat e.pcol.toNat
  | m => throw (malformed s!"cmap: MTYP {m} not 0 or 1")

/-- OpenJPEG's repair of a "weird" `cmap` (`opj_jp2_check_color`, issues 235/447): with a
single codestream component, `NPC` entries, and some palette column named by no entry, every
entry `i` becomes a palette mapping of column `i`. -/
def fixWeirdCmap (nComps : Nat) (p : Palette) (cm : ComponentMapping) : ComponentMapping :=
  if nComps == 1 && cm.size == p.npc &&
      (List.range p.npc).any (fun c => !cm.any (fun e => e.pcol.toNat == c)) then
    cm.mapIdx fun i e => { e with mtyp := 1, pcol := i.toUInt8 }
  else cm

/-- Validates `pclr` + `cmap` against a codestream with `nComps` components (T.800 I.5.3.4,
I.5.3.5): the channel count is checked against `maxComponents`; each entry's component must
exist, `MTYP` ∈ {0, 1}, `PCOL` = 0 for direct use and < `NPC` for palette use. -/
def mappingOf (L : Limits) (p : Palette) (cm : ComponentMapping) (nComps : Nat) :
    Except Error Mapping := do
  L.check (.at .color) .components cm.size
  if cm.isEmpty then throw (malformed "cmap: no entries")
  checkPalette p
  let cm := fixWeirdCmap nComps p cm
  let sources ← cm.mapM (entrySource nComps p)
  return { sources, palette := some p }

/-- The identity mapping: channel `i` is component `i`. -/
def identityMapping (nComps : Nat) : Mapping :=
  { sources := (List.range nComps).toArray.map .direct }

/-- The channel mapping a JP2 header defines for `nComps` codestream components. A `pclr`
without `cmap` is ignored (identity mapping), as OpenJPEG does (`cmap` without `pclr` is
rejected by `Box.parseJp2h`). -/
def resolveMapping (L : Limits) (h : Jp2Header) (nComps : Nat) : Except Error Mapping :=
  match h.pclr, h.cmap with
  | some p, some cm => mappingOf L p cm nComps
  | _, _ => do
    L.check (.at .color) .components nComps
    return identityMapping nComps

/-- Sample format of one channel: depth, signedness and sub-sampling factors. -/
structure Format where
  /-- Bit depth (1…38). -/
  depth : Nat
  /-- Signed samples. -/
  signed : Bool
  /-- Horizontal sub-sampling `XRsiz`. -/
  dx : Nat := 1
  /-- Vertical sub-sampling `YRsiz`. -/
  dy : Nat := 1
  deriving Repr, DecidableEq, Inhabited

/-- The format of each codestream component (T.800 A.5.1). -/
def componentFormats (comps : Array Marker.Component) : Array Format :=
  comps.map fun c => { depth := c.depth.toNat, signed := c.signed,
                       dx := c.dx.toNat, dy := c.dy.toNat }

/-- The format of each output channel: a direct channel keeps its component's, a palette
channel takes the column's depth and sign and the component's sub-sampling. -/
def Mapping.formats (m : Mapping) (comps : Array Format) : Array Format :=
  m.sources.map fun
    | .direct c => comps.getD c default
    | .palette c col =>
      let f := comps.getD c default
      let (d, s) := match m.palette with
        | some p => bitsDepth (p.bits.getD col 0)
        | none => (f.depth, f.signed)
      { f with depth := d, signed := s }

/-- A row-major channel. Compact images use their original buffer. A view borrows its
source and evaluates exact samples by index, including replication and palette lookup. -/
inductive SamplePlane where
  /-- Original four-byte cells. -/
  | compact (p : Plane)
  /-- A borrowed native codestream component in its format-selected storage. -/
  | native (c : NativeOutput.OutputComponent)
  /-- Exact samples of a grid, computed from retained buffers. -/
  | view (w h : Nat) (read : Nat → Int)

instance : Coe Plane SamplePlane := ⟨.compact⟩

/-- Width of the channel grid. -/
def SamplePlane.width : SamplePlane → Nat
  | .compact p => p.width
  | .native c => match c.storage with | .narrow p => p.width | .wide p => p.width
  | .view w _ _ => w

/-- Height of the channel grid. -/
def SamplePlane.height : SamplePlane → Nat
  | .compact p => p.height
  | .native c => match c.storage with | .narrow p => p.height | .wide p => p.height
  | .view _ h _ => h

/-- Exact integer at a row-major index on this grid. -/
@[inline] def SamplePlane.get? : SamplePlane → Nat → Option Int
  | .compact p, i => (p.get? i).map Int32.toInt
  | .native c, i => (CodestreamComponent.native c).get? i
  | .view w h read, i => if i < w * h then some (read i) else none

/-- Borrow the existing four-byte plane when the channel has compact storage. -/
def SamplePlane.compact? : SamplePlane → Option Plane
  | .compact p => some p
  | .native c => match c.storage with | .narrow p => some p | .wide _ => none
  | .view .. => none

/-- A decoded channel on its component grid. -/
structure Channel where
  /-- The samples. -/
  plane : SamplePlane
  /-- Depth, sign and sub-sampling. -/
  format : Format

/-- A parsed palette entry. Unsigned columns keep the stored bytes (OpenJPEG
compatibility). Signed columns sign-extend the low `depth` bits (T.800 I.5.3.4). -/
def entryValue (bi : UInt8) (e : UInt64) : Int :=
  let (d, s) := bitsDepth bi
  if !s then e.toNat else
  let v := e.toNat % 2 ^ d
  if v ≥ 2 ^ (d - 1) then Int.ofNat v - Int.ofNat (2 ^ d) else Int.ofNat v

/-- Column `col` of a palette as a lookup table of `NE` exact samples. -/
def paletteColumn (p : Palette) (col : Nat) : Array Int :=
  let bi := p.bits.getD col 0
  (List.range p.ne).toArray.map fun j => entryValue bi (p.entries.getD (j * p.npc + col) 0)

/-- The table entry for index sample `v`: indices are clamped to `[0, size − 1]`, as
`opj_jp2_apply_pclr`. -/
@[inline] def lookup (tbl : Array Int32) (v : Int32) : Int32 :=
  let idx := if v < 0 then 0 else min v.toInt.toNat (tbl.size - 1)
  tbl.getD idx 0

/-- Writes `lookup tbl (src i)` into `dst` for `i` = `i₀ …` (fuel `k`). -/
def mapPlane (tbl : Array Int32) (src dst : Plane) (i : Nat) : Nat → Plane
  | 0 => dst
  | k + 1 =>
    if h1 : i < src.width * src.height then
      if h2 : i < dst.width * dst.height then
        mapPlane tbl src (dst.set i (lookup tbl (src.get i h1)) h2) (i + 1) k
      else dst
    else dst

/-- Applies a palette column to an index plane (a new plane of the same size, checked against
`maxWorkSamples`). -/
def palettePlane (L : Limits) (tbl : Array Int32) (src : Plane) : Except Error Plane := do
  let dst ← Plane.zeroChecked L (.at .color) src.width src.height
  return mapPlane tbl src dst 0 (src.width * src.height)

/-- Palette lookup with an exact index, clamped before table access (I.5.3.4). -/
def indexedPlane (tbl : Array Int) (src : SamplePlane) : SamplePlane :=
  .view src.width src.height fun i =>
    tbl.getD (min ((src.get? i).getD 0).toNat (tbl.size - 1)) 0

/-- Builds the output channels from the codestream components (`comps`, in component order)
by a validated mapping. Direct channels share the component's plane. Palette channels with
compact indices and values use the four-byte kernel. Others borrow the index plane and
retain exact table entries. The running palette area is checked against `maxWorkSamples`. -/
def applyMapping (L : Limits) (m : Mapping) (comps : Array Channel) :
    Except Error (Array Channel) := do
  let fmts := m.formats (comps.map (·.format))
  let (out, _) ← (m.sources.zip fmts).foldlM (init := ((#[] : Array Channel), 0))
    fun (out, total) (src, fmt) => do
      match src with
      | .direct c =>
        let some ch := comps[c]? | throw (malformed s!"component {c} missing")
        return (out.push ch, total)
      | .palette c col =>
        let some ch := comps[c]? | throw (malformed s!"component {c} missing")
        let some p := m.palette | throw (malformed "palette mapping without pclr")
        let total := total + ch.plane.width * ch.plane.height
        L.check (.at .color) .workSamples total
        let tbl := paletteColumn p col
        let plane ← match ch.plane.compact? with
          | some src =>
            if tbl.all (fun v => -2147483648 ≤ v && v ≤ 2147483647) then
              SamplePlane.compact <$> palettePlane L (tbl.map Int32.ofInt) src
            else pure (indexedPlane tbl ch.plane)
          | none => pure (indexedPlane tbl ch.plane)
        return (out.push { plane, format := fmt }, total)
  return out

/-- Validates `pclr` + `cmap` against the components and applies them (T.800 I.5.3.4,
I.5.3.5): the output channels in `cmap` order. -/
def applyPalette (L : Limits) (p : Palette) (cm : ComponentMapping) (comps : Array Channel) :
    Except Error (Array Channel) := do
  let m ← mappingOf L p cm comps.size
  applyMapping L m comps

/-! ## Channel definitions (T.800 I.5.3.6) -/

/-- How the output channels are used. -/
structure ChannelLayout where
  /-- The colour channels in colour order (colour 1, 2, …): channel indices. -/
  colours : Array Nat
  /-- The whole-image opacity channel (`Typ` 1 or 2 with `Asoc` 0), if any. -/
  alpha : Option Nat := none
  /-- The opacity is premultiplied (`Typ` 2). -/
  premultiplied : Bool := false
  /-- Every other channel (unspecified, per-colour opacity, extra), in channel order. -/
  other : Array Nat := #[]
  deriving Repr, DecidableEq, Inhabited

/-- Validates a `cdef` box against `n` channels, as `opj_jp2_check_color`: every `Cn` < `n`;
every `Asoc` ∉ {0, 65535} has `Asoc − 1 < n`; every channel is defined exactly once. -/
def checkCdef (n : Nat) (defs : Array ChannelDef) : Except Error Unit := do
  for d in defs do
    if d.cn.toNat ≥ n then throw (malformed s!"cdef: channel {d.cn} ≥ {n} channels")
    if d.asoc != 0 && d.asoc != 65535 && d.asoc.toNat - 1 ≥ n then
      throw (malformed s!"cdef: association {d.asoc} > {n} channels")
  let seen := defs.foldl (fun s d => s.setIfInBounds d.cn.toNat (s.getD d.cn.toNat 0 + 1))
    (Array.replicate n (0 : Nat))
  if seen.any (· != 1) then
    throw (malformed "cdef: channels not each defined exactly once")

/-- The colour channel for colour `k` (1-based): the `Typ` 0 entry with `Asoc` = `k`, which
must be unique. -/
def colourChannel (defs : Array ChannelDef) (k : Nat) : Except Error Nat :=
  match (defs.filter fun d => d.typ == 0 && d.asoc.toNat == k).toList with
  | [d] => .ok d.cn.toNat
  | [] => .error (malformed s!"cdef: no channel for colour {k}")
  | _ => .error (malformed s!"cdef: several channels for colour {k}")

/-- The channel layout of `n` channels (T.800 I.5.3.6). `nColours` is the colour count of
the colour space if known.

* With `cdef` (validated by `checkCdef`): colour `k` is the `Typ` 0 channel with `Asoc` `k`
  for `k = 1 … nColours` (when unknown, the colours named by `Typ` 0 entries, which must be
  `1 … m`); the alpha channel is the first `Typ` 1/2 channel with `Asoc` 0.
* Without `cdef`: channels `0 … min(nColours, n) − 1` are the colours (all channels when the
  count is unknown) and the rest are `other`; no channel is alpha (T.800 gives opacity only
  through `cdef`). -/
def channelLayout (nColours : Option Nat) (n : Nat) (cdef : Option (Array ChannelDef)) :
    Except Error ChannelLayout := do
  match cdef with
  | none =>
    let k := min (nColours.getD n) n
    return { colours := (List.range k).toArray,
             other := ((List.range n).drop k).toArray }
  | some defs =>
    checkCdef n defs
    let m := match nColours with
      | some k => k
      | none => (defs.filter fun d => d.typ == 0 && d.asoc != 0 && d.asoc != 65535).size
    let colours ← (List.range m).toArray.mapM fun k => colourChannel defs (k + 1)
    let alphaDef := (defs.qsort (fun a b => a.cn < b.cn)).find? fun d =>
      (d.typ == 1 || d.typ == 2) && d.asoc == 0
    let alpha := alphaDef.map (·.cn.toNat)
    let other := (List.range n).toArray.filter fun i => !colours.contains i && alpha != some i
    return { colours, alpha, premultiplied := alphaDef.any (·.typ == 2), other }

/-! ## Resolution of a JP2 header -/

/-- Everything colour-related a renderer needs, resolved from the JP2 header. -/
structure Info where
  /-- The colour space (`unknown` for a raw codestream). -/
  space : ColourSpace
  /-- The channel mapping (identity unless `pclr` + `cmap`). -/
  mapping : Mapping
  /-- The format of each output channel. -/
  formats : Array Format
  /-- How the output channels are used. -/
  layout : ChannelLayout
  deriving Repr, DecidableEq, Inhabited

/-- Resolves colour information for a codestream whose SIZ lists `comps`, with the JP2
header `hdr?` (`none` for a raw codestream) and the input `data` (for ICC headers). Validates
`pclr`/`cmap`/`cdef` against the codestream (T.800 I.5.3.3–I.5.3.6). `ihdr`/`bpcc` are not
compared with SIZ; SIZ governs, as in OpenJPEG. -/
def resolve (L : Limits) (data : ByteArray) (hdr? : Option Jp2Header)
    (comps : Array Marker.Component) : Except Error Info := do
  let nComps := comps.size
  let (space, mapping, cdef) ← match hdr? with
    | none => do
      L.check (.at .color) .components nComps
      pure (ColourSpace.unknown, identityMapping nComps, none)
    | some h => do
      let m ← resolveMapping L h nComps
      pure (resolveColourSpace h, m, h.cdef)
  let formats := mapping.formats (componentFormats comps)
  let layout ← channelLayout (space.numColours data) mapping.sources.size cdef
  return { space, mapping, formats, layout }

/-! ## sYCC → sRGB (T.800 Table I.10; OpenJPEG `color_sycc_to_rgb`) -/

/-- One sample of OpenJPEG's `sycc_to_rgb` in integer arithmetic: chroma offset `off`, upper
bound `upb`; products truncated toward zero and results clamped to `[0, upb]`. -/
@[inline] def syccPixel (off upb y cb cr : Int64) : Int64 × Int64 × Int64 :=
  let cb := cb - off
  let cr := cr - off
  let clamp (v : Int64) : Int64 := if v < 0 then 0 else if v > upb then upb else v
  (clamp (y + 1402 * cr / 1000),
   clamp (y - (344 * cb + 714 * cr) / 1000),
   clamp (y + 1772 * cb / 1000))

/-- For each luma column (or row) `i` of a component starting at `c0 = ⌈o/dl⌉` on a grid with
luma factor `dl`, the index of the chroma sample (factor `dc`, `wc` samples) whose grid cell
contains it, clamped to `[0, wc − 1]` (replication). -/
def chromaIndex (o dl dc wc n : Nat) : Array Nat :=
  let l0 := (o + dl - 1) / dl
  let c0 := (o + dc - 1) / dc
  (List.range n).toArray.map fun i => min ((l0 + i) * dl / dc - c0) (wc - 1)

/-- The three output planes, filled for `i = i₀ …` (fuel `k`). The first
`zeroCols[row]` pixels on a row use raw zero for both chroma samples. -/
def syccLoop (off upb : Int64) (w : Nat) (y cb cr : Plane)
    (cbx cby crx cry : Array Nat) (r g b : Plane) (i k : Nat) (zeroCols : Array Nat := #[]) :
    Plane × Plane × Plane :=
  match k with
  | 0 => (r, g, b)
  | k + 1 =>
    if hy : i < y.width * y.height then
      if hr : i < r.width * r.height then
      if hg : i < g.width * g.height then
      if hb : i < b.width * b.height then
        let x := i % w
        let row := i / w
        let (vcb, vcr) := if x < zeroCols.getD row 0 then (0, 0) else
          ((cb.get? (cby.getD row 0 * cb.width + cbx.getD x 0)).getD 0,
           (cr.get? (cry.getD row 0 * cr.width + crx.getD x 0)).getD 0)
        let (vr, vg, vb) := syccPixel off upb (y.get i hy).toInt64 vcb.toInt64 vcr.toInt64
        syccLoop off upb w y cb cr cbx cby crx cry
          (r.set i vr.toInt32 hr) (g.set i vg.toInt32 hg) (b.set i vb.toInt32 hb) (i + 1) k zeroCols
      else (r, g, b) else (r, g, b) else (r, g, b)
    else (r, g, b)

/-- Converts sYCC channels (Y, Cb, Cr) to sRGB at the luma channel's resolution (T.800 Table
I.10, OpenJPEG `color_sycc_to_rgb`). `ox`, `oy` are the image area origin `XOsiz`, `YOsiz`.
Sub-sampled chroma is replicated (see the module doc). The luma depth `p` must be ≤ 38; the
outputs are unsigned `p`-bit channels with the luma's sub-sampling. -/
def syccToRgb (L : Limits) (ox oy : Nat) (y cb cr : Channel) :
    Except Error (Channel × Channel × Channel) := do
  let p := y.format.depth
  if p == 0 || p > 38 then throw (unsupported s!"sYCC: luma depth {p} not in 1..38")
  let fs := [y.format, cb.format, cr.format]
  if fs.any (fun f => f.dx == 0 || f.dy == 0) then
    throw (malformed "sYCC: zero sub-sampling factor")
  let (w, h) := (y.plane.width, y.plane.height)
  if w * h > 0 &&
      (cb.plane.width * cb.plane.height == 0 || cr.plane.width * cr.plane.height == 0) then
    throw (malformed "sYCC: empty chroma plane")
  L.check (.at .color) .workSamples (3 * (w * h))
  let cbx := chromaIndex ox y.format.dx cb.format.dx cb.plane.width w
  let cby := chromaIndex oy y.format.dy cb.format.dy cb.plane.height h
  let crx := chromaIndex ox y.format.dx cr.format.dx cr.plane.width w
  let cry := chromaIndex oy y.format.dy cr.format.dy cr.plane.height h
  let zeroCols :=
    if y.format.dx == 1 && y.format.dy == 1 && cb.format.dx == 2 && cr.format.dx == 2 &&
        cb.format.dy == cr.format.dy && (cb.format.dy == 1 || cb.format.dy == 2) then
      let dy := cb.format.dy
      let offx := ox % 2
      let offy := oy % dy
      if offx == 0 && offy == 0 then #[] else
        (Array.range h).map fun row =>
          if row < offy then w else if (row - offy) % dy == 0 then offx else 0
    else #[]
  let off : Int64 := Int64.ofNat (2 ^ (p - 1))
  let upb : Int64 := Int64.ofNat (2 ^ p - 1)
  let fmt : Format := { y.format with signed := false }
  let channel (plane : SamplePlane) : Channel := { plane, format := fmt }
  if let (some yp, some cbp, some crp) := (y.plane.compact?, cb.plane.compact?, cr.plane.compact?) then
    if p ≤ 31 then
      let z := Plane.zero w h
      let (r, g, b) := syccLoop off upb w yp cbp crp cbx cby crx cry z z z 0 (w * h) zeroCols
      return (channel r, channel g, channel b)
  -- Parsed 38-bit palette columns occupy at most five bytes including padding.
  -- The chroma products and sums in syccPixel therefore fit Int64 on either path.
  let pixel (i : Nat) :=
    let x := i % w
    let row := i / w
    let chroma (c : Channel) (xs ys : Array Nat) :=
      if x < zeroCols.getD row 0 then 0 else
        ((c.plane.get? (ys.getD row 0 * c.plane.width + xs.getD x 0)).getD 0).toInt64
    syccPixel off upb ((y.plane.get? i).getD 0).toInt64
      (chroma cb cbx cby) (chroma cr crx cry)
  return (channel (.view w h fun i => (pixel i).1.toInt),
          channel (.view w h fun i => (pixel i).2.1.toInt),
          channel (.view w h fun i => (pixel i).2.2.toInt))

end JPEG2000.Color
