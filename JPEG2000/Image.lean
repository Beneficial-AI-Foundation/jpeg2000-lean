import JPEG2000.Decode
import JPEG2000.Color

/-!
# `JPEG2000.decode`: the consumer API (Plan.md §1 "What we build", §9)

Task 6.2. `decode L data opts` turns a JP2 file or a raw codestream into an `Image`: the
colour channels at full resolution in colour order, the opacity channel, the colour space
and ICC profile needed to convert, and the raw per-component planes. `Image.interleaved8` /
`Image.interleaved16` give a pixel-interleaved buffer scaled to 8 or 16 bits per sample.

## Pipeline

1. `decodeCodestream` (task 5.5): one plane per codestream component on its own grid
   (T.800 B.2, B-12, B-14 for `reduce`).
2. `Color.resolve` (task 6.1): colour space (T.800 I.5.3.3), `pclr`/`cmap` mapping
   (I.5.3.4, I.5.3.5), `cdef` layout (I.5.3.6).
3. Palette: `Color.applyMapping` (unless `applyPalette := false`; then the channels are the
   codestream components, all treated as colours, and `cdef` is not used).
4. sYCC → sRGB (`Color.syccToRgb`, T.800 Table I.10) on the three colour channels when
   `convertSycc` (the default). A raw codestream (colour space `unknown`) with three
   components of which the first has equal sub-sampling factors and the second is
   horizontally sub-sampled is taken as sYCC, the heuristic of OpenJPEG's
   `opj_decompress` (`inferSycc`; OpenJPEG applies it even to declared spaces, we only to
   `unknown`). With fewer than three colour channels no conversion is done.
5. Up-sampling to the image area on the (reduced) reference grid by **replication**: the
   output sample at reference column `X` takes the component sample whose grid cell
   contains it, `⌊X / XRsiz⌋ − ⌈XOsiz / XRsiz⌉`, clamped to the component (the first
   column for an odd origin), as `Color.chromaIndex`. This is OpenJPEG's display
   up-sampling (`opj_decompress -upsample`, and its `sycc420_to_rgb` for even origins);
   no interpolation.
6. `cdef` layout: colours in colour order, the whole-image opacity channel (`Typ` 1, or 2 =
   premultiplied), the rest as `other`.

## Bit-depth scaling for display (`interleaved8`, `interleaved16`)

Signed samples are first offset by `2^(d−1)` (so the most negative value maps to 0); then
the unsigned `d`-bit value `u` is scaled to `t` = 8 or 16 bits:

* `Scaling.linear` (default): `⌊(u·(2^t − 1) + ⌊(2^d − 1)/2⌋) / (2^d − 1)⌋`, i.e. the
  linear map of `[0, 2^d − 1]` onto `[0, 2^t − 1]` rounded to nearest (ISO 32000-2 §8.9.5:
  samples are scaled linearly over the range of their bit depth). Exact for `d = t`;
  `1 ↦ 2^t − 1` for 1-bit samples.
* `Scaling.opj`: OpenJPEG's `opj_decompress -p tS` (`scale_component`): `u >> (d − t)` when
  `d > t`, `⌊u·(2^t − 1)/(2^d − 1)⌋` when `d < t`. The two differ by at most 1.

The display scaler accepts native depths 1…38. Its unsigned input is below `2^38`,
and its 8- or 16-bit multiplier is below `2^16`. The numerator, including the rounding
term, fits in `UInt64`. The current decoder supplies planes of `Int32` samples (through
31 unsigned bits or 32 signed bits).

16-bit output is **big-endian** (most significant byte first), the order of 16-bit samples
in PDF image data (ISO 32000-2 §8.9.2). By default the alpha channel is **not** included
(`withAlpha := false`): a PDF consumer takes colour and soft mask separately
(`Image.smaskInData`).

## PDF (`/SMaskInData`, ISO 32000-2 §7.4.9, Plan.md §9)

`smaskInData img m`: for `m` = 1 or 2 the opacity channel as a soft mask (premultiplied when
`m = 2` or the file's `cdef` says so); `none` for 0, any other value, or no opacity channel.
The PDF's `/ColorSpace` override and dimension re-validation are the consumer's (safe-pdf).

## Limits

Before allocating: the image area against `maxImageArea`; the cells of all up-sampled planes
against `maxWorkSamples`; the output channels at `Header.bytesPerSample` against
`maxDecodedBytes`; an interleaved buffer against `maxDecodedBytes`. Palette and sYCC planes
are checked by `Color`. Every loop runs on fuel equal to a size already checked.
-/

namespace JPEG2000

open JPEG2000.Bytes JPEG2000.Header

/-- One image channel at the image's full resolution (`plane` is `width × height` of the
image): samples as decoded (after palette / colour conversion), with depth and sign. -/
structure Channel where
  /-- Bit depth of the samples (1…32). -/
  depth : Nat
  /-- Samples are signed. -/
  signed : Bool
  /-- The samples, row-major, `Int32` cells. -/
  plane : Plane

instance : Inhabited Channel := ⟨{ depth := 1, signed := false, plane := Plane.zero 0 0 }⟩

/-- A soft mask selected by `/SMaskInData`. -/
structure SoftMask where
  /-- The opacity samples. -/
  channel : Channel
  /-- The colour samples are premultiplied by the opacity. -/
  premultiplied : Bool

/-- Options of `decode`. -/
structure DecodeOptions where
  /-- Number of finest resolution levels to discard (OpenJPEG `-r`). -/
  reduce : Nat := 0
  /-- Apply `pclr`/`cmap` (otherwise the channels are the raw codestream components). -/
  applyPalette : Bool := true
  /-- Convert sYCC to sRGB. -/
  convertSycc : Bool := true
  /-- Take a raw codestream whose components look like sub-sampled YCC as sYCC. -/
  inferSycc : Bool := true
  deriving Repr, DecidableEq, Inhabited

/-- A decoded image (Plan.md §1 "Output"). -/
structure Image where
  /-- Width of the image area (`Xsiz − XOsiz`, at the chosen reduction). -/
  width : Nat
  /-- Height of the image area (`Ysiz − YOsiz`, at the chosen reduction). -/
  height : Nat
  /-- Left edge of the image area on the (reduced) reference grid. -/
  x0 : Nat
  /-- Top edge of the image area on the (reduced) reference grid. -/
  y0 : Nat
  /-- Colour space of `channels` (sYCC converted: `sRGB`). -/
  space : Color.ColourSpace
  /-- The colour channels in colour order (`cdef` association order), full resolution. -/
  channels : Array Channel
  /-- The whole-image opacity channel, if `cdef` defines one. -/
  alpha : Option Channel := none
  /-- The opacity is premultiplied (`cdef` `Typ` 2). -/
  premultiplied : Bool := false
  /-- Other channels (unspecified type, per-colour opacity, extra), full resolution. -/
  other : Array Channel := #[]
  /-- The restricted ICC profile (`colr` `METH` 2), copied from the input. -/
  iccProfile : Option ByteArray := none
  /-- The codestream decode: header (with the JP2 boxes) and per-component planes on their
  own grids. -/
  decoded : DecodedImage

namespace Image

/-- The error location of this stage (colour composition). -/
def loc : Location := .at .color

/-- The raw per-component planes, each on its own grid (for consumers that want them). -/
def decodedComponents (img : Image) : Array DecodedComponent := img.decoded.comps

/-! ## Up-sampling to the reference grid -/

/-- Fills `dst[i] = src[iy[i / w] · src.width + ix[i % w]]` for `i = i₀ …` (fuel `k`). -/
def upLoop (src : Plane) (w : Nat) (ix iy : Array Nat) (dst : Plane) (i : Nat) : Nat → Plane
  | 0 => dst
  | k + 1 =>
    if h : i < dst.width * dst.height then
      let v := (src.get? (iy.getD (i / w) 0 * src.width + ix.getD (i % w) 0)).getD 0
      upLoop src w ix iy (dst.set i v h) (i + 1) k
    else dst

/-- A channel is already at the image resolution (no up-sampling needed). -/
def atFullRes (w h : Nat) (c : Color.Channel) : Bool :=
  c.format.dx == 1 && c.format.dy == 1 && c.plane.width == w && c.plane.height == h

/-- The channel on the `w × h` image area with origin `(ox, oy)` on the reference grid, by
replication (see the module doc). Allocates a new plane unless `atFullRes`; the caller has
checked the cells against `maxWorkSamples`. -/
def upsample (ox oy w h : Nat) (c : Color.Channel) : Except Error Plane := do
  if atFullRes w h c then return c.plane
  let p := c.plane
  if w * h > 0 && p.width * p.height == 0 then
    throw (.unsupported loc "a component has no samples inside the image area")
  let ix := Color.chromaIndex ox 1 c.format.dx p.width w
  let iy := Color.chromaIndex oy 1 c.format.dy p.height h
  return upLoop p w ix iy (Plane.zero w h) 0 (w * h)

/-! ## Colour -/

/-- OpenJPEG's (`opj_decompress`) test for a three-component image to be sYCC: component 0
has `XRsiz = YRsiz` and component 1 is horizontally sub-sampled. -/
def looksSycc (comps : Array DecodedComponent) : Bool :=
  match comps[0]?, comps[1]? with
  | some c0, some c1 => comps.size == 3 && c0.dx == c0.dy && c1.dx != 1
  | _, _ => false

/-- Converts the three colour channels (`colours`) from sYCC to sRGB in place; leaves the
channels as they are (and the space sYCC) when there are not exactly three colours. -/
def convertSycc (L : Limits) (ox oy : Nat) (colours : Array Nat)
    (chans : Array Color.Channel) : Except Error (Color.ColourSpace × Array Color.Channel) := do
  match colours.toList with
  | [iy, icb, icr] =>
    let some y := chans[iy]? | throw (.malformed loc "sYCC: luma channel missing")
    let some cb := chans[icb]? | throw (.malformed loc "sYCC: Cb channel missing")
    let some cr := chans[icr]? | throw (.malformed loc "sYCC: Cr channel missing")
    let (r, g, b) ← Color.syccToRgb L ox oy y cb cr
    return (.sRGB, ((chans.setIfInBounds iy r).setIfInBounds icb g).setIfInBounds icr b)
  | _ => return (.sYCC, chans)

/-- The channel at index `i` of the composed channels. -/
def pick (full : Array Channel) (i : Nat) : Except Error Channel :=
  match full[i]? with
  | some c => .ok c
  | none => .error (.malformed loc s!"channel {i} missing")

end Image

open Image in
/-- **Decodes a JP2 file or a raw JPEG 2000 codestream** into an `Image` (Plan.md §1): the
pipeline of the module doc. Every stage's error propagates; every allocation is checked
against `L` first. -/
def decode (L : Limits) (data : ByteArray) (opts : DecodeOptions := {}) :
    Except Error Image := do
  let d ← decodeCodestream L data opts.reduce
  let siz := d.header.siz
  let hdr? := d.header.container.bind (·.header)
  let info ← Color.resolve L data hdr? siz.components
  let comps : Array Color.Channel := d.comps.map fun c =>
    { plane := c.plane, format := { depth := c.depth, signed := c.signed, dx := c.dx, dy := c.dy } }
  -- palette and channel layout
  let (mapping, layout) :=
    if opts.applyPalette || info.mapping.palette.isNone then (info.mapping, info.layout)
    else (Color.identityMapping comps.size,
          ({ colours := (List.range comps.size).toArray } : Color.ChannelLayout))
  let chans ← Color.applyMapping L mapping comps
  -- the image area on the (reduced) reference grid
  let r := Assemble.reduceRect (imageRect siz) opts.reduce
  let (ox, oy, w, h) := (r.x0, r.y0, r.width, r.height)
  L.check loc .imageArea (w * h)
  -- colour space, sYCC
  let space := if info.space == .unknown && opts.inferSycc && looksSycc d.comps then .sYCC
    else info.space
  let (space, chans) ←
    if space == .sYCC && opts.convertSycc then convertSycc L ox oy layout.colours chans
    else pure (space, chans)
  -- up-sampling, after checking what it allocates and the size of the output
  let upCells := chans.foldl (fun a c => if atFullRes w h c then a else a + w * h) 0
  L.check loc .workSamples upCells
  L.check loc .decodedBytes
    (chans.foldl (fun a c => a + w * h * bytesPerSample c.format.depth) 0)
  let full ← chans.mapM fun c => do
    let plane ← upsample ox oy w h c
    pure ({ depth := c.format.depth, signed := c.format.signed, plane } : Channel)
  let channels ← layout.colours.mapM (pick full)
  let alpha ← match layout.alpha with
    | some i => some <$> pick full i
    | none => pure none
  let other ← layout.other.mapM (pick full)
  let iccProfile := match info.space with
    | .icc pr => some (data.extract pr.start (pr.start + pr.len))
    | _ => none
  return { width := w, height := h, x0 := ox, y0 := oy, space, channels, alpha,
           premultiplied := layout.alpha.isSome && layout.premultiplied, other, iccProfile,
           decoded := d }

/-! ## Bit-depth scaling and interleaving -/

/-- How samples are scaled to the output depth (see the module doc). -/
inductive Scaling where
  /-- Linear map of the full ranges, rounded to nearest (default). -/
  | linear
  /-- OpenJPEG's `opj_decompress -p tS`: shift down, `⌊·⌋` linear up. -/
  | opj
  deriving Repr, DecidableEq, Inhabited

/-- The scaling of an unsigned `d`-bit value `u ≤ 2^d − 1` to `t` bits, on `Nat` (the
specification of `Scaler.apply`). -/
def scaleNat (mode : Scaling) (d t u : Nat) : Nat :=
  if d == t then u
  else match mode with
    | .linear => (u * (2 ^ t - 1) + (2 ^ d - 1) / 2) / (2 ^ d - 1)
    | .opj => if d > t then u / 2 ^ (d - t) else u * (2 ^ t - 1) / (2 ^ d - 1)

/-- Linear scaling stays within the output range. -/
theorem scaleNat_linear_le (d t u : Nat) (hu : u ≤ 2 ^ d - 1) :
    scaleNat .linear d t u ≤ 2 ^ t - 1 := by
  unfold scaleNat
  split
  · rename_i hdt
    have : d = t := by simpa using hdt
    subst this; exact hu
  · simp only
    by_cases h0 : 2 ^ d - 1 = 0
    · rw [h0, Nat.div_zero]; exact Nat.zero_le _
    · apply (Nat.div_le_iff_le_mul_add_pred (by omega)).2
      have h1 : u * (2 ^ t - 1) ≤ (2 ^ d - 1) * (2 ^ t - 1) := Nat.mul_le_mul_right _ hu
      have h2 : (2 ^ d - 1) / 2 ≤ 2 ^ d - 1 - 1 := by omega
      omega

/-- Precomputed `UInt64` parameters scaling one channel to `t` bits. -/
structure Scaler where
  /-- Offset added first (`2^(d−1)` for signed samples, else 0). -/
  off : Int64
  /-- Largest input value `2^d − 1`. -/
  maxIn : Int64
  /-- Identity (`d = t`). -/
  ident : Bool
  /-- Shift down by `shift` (OpenJPEG mode, `d > t`). -/
  down : Bool
  /-- The shift amount `d − t`. -/
  shift : UInt64
  /-- Numerator factor `2^t − 1`. -/
  mul : UInt64
  /-- Rounding term (`⌊(2^d − 1)/2⌋` linear, 0 OpenJPEG). -/
  half : UInt64
  /-- Denominator `2^d − 1` (≥ 1). -/
  den : UInt64

/-- The scaler of a channel of depth `d` (1…38) and sign `s` to `t` bits. -/
def Scaler.make (mode : Scaling) (d : Nat) (s : Bool) (t : Nat) : Scaler :=
  let den := max 1 (2 ^ d - 1)
  { off := if s then Int64.ofNat (2 ^ (d - 1)) else 0
    maxIn := Int64.ofNat den
    ident := d == t
    down := mode == .opj && d > t
    shift := (d - t).toUInt64
    mul := (2 ^ t - 1).toUInt64
    half := if mode == .linear then (den / 2).toUInt64 else 0
    den := den.toUInt64 }

@[inline] private def Scaler.scaleUnsigned (s : Scaler) (u : UInt64) : UInt64 :=
  if s.ident then u
  else if s.down then u >>> s.shift
  else (u * s.mul + s.half) / s.den

/-- Scales a narrow component sample after adding its signed offset and clamping. -/
@[inline] def Scaler.apply (s : Scaler) (v : Int32) : UInt64 :=
  let x := v.toInt64 + s.off
  let u := if x < 0 then 0 else if x > s.maxIn then s.maxIn.toUInt64 else x.toUInt64
  s.scaleUnsigned u

/-- Scales an exact native component sample, including 38-bit signed or unsigned values.
Offset and clamp precede conversion to the unsigned fixed-width display kernel. -/
@[inline] def Scaler.applyNative (s : Scaler) (v : Int) : UInt64 :=
  let u := min s.maxIn.toInt.toNat (v + s.off.toInt).toNat
  s.scaleUnsigned u.toUInt64

private theorem scaleUnsigned_make (mode : Scaling) {d t u : Nat} (s : Bool)
    (hd : 1 ≤ d) (hd' : d ≤ 38) (ht : t ≤ 16) (hu : u ≤ 2^d - 1) :
    ((Scaler.make mode d s t).scaleUnsigned u.toUInt64).toNat = scaleNat mode d t u := by
  have h1 := Nat.pow_le_pow_right (by decide : 0 < 2) hd
  have h38 := Nat.pow_le_pow_right (by decide : 0 < 2) hd'
  have h16 := Nat.pow_le_pow_right (by decide : 0 < 2) ht
  have den : max 1 (2^d - 1) = 2^d - 1 := Nat.max_eq_right (by omega)
  have mul : u * (2^t - 1) ≤ (2^38) * (2^16) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hu64 : u < 2^64 := by omega
  have hd64 : 2^d - 1 < 2^64 := by omega
  have ht64 : 2^t - 1 < 2^64 := by omega
  have hh64 : (2^d - 1) / 2 < 2^64 := by omega
  have hm64 : u * (2^t - 1) < 2^64 := by omega
  have ha64 : u * (2^t - 1) + (2^d - 1) / 2 < 2^64 := by omega
  have hs64 : d - t < 64 := by omega
  have hs' : d - t < 2^64 := by omega
  cases mode <;> by_cases he : d = t <;> by_cases hdown : t < d <;>
    simp [Scaler.make, Scaler.scaleUnsigned, scaleNat, he, hdown, den, UInt64.toNat_add,
      UInt64.toNat_mul, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt hu64, Nat.mod_eq_of_lt hd64, Nat.mod_eq_of_lt ht64,
      Nat.mod_eq_of_lt hh64, Nat.mod_eq_of_lt hm64, Nat.mod_eq_of_lt ha64,
      Nat.mod_eq_of_lt hs64, Nat.mod_eq_of_lt hs']

/-- For every admitted component depth through 38 bits and output depth up to 16,
native display scaling equals clamping and the mathematical scaling formula. -/
theorem Scaler.applyNative_make_eq (mode : Scaling) {d t : Nat} (s : Bool) (v : Int)
    (hd : 1 ≤ d) (hd' : d ≤ 38) (ht : t ≤ 16) :
    ((Scaler.make mode d s t).applyNative v).toNat =
      scaleNat mode d t (min (2^d - 1) (v + (if s then (2 : Int)^(d - 1) else 0)).toNat) := by
  have h1 := Nat.pow_le_pow_right (by decide : 0 < 2) hd
  have h38 := Nat.pow_le_pow_right (by decide : 0 < 2) hd'
  have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) (show d - 1 ≤ 38 by omega)
  have den : max 1 (2^d - 1) = 2^d - 1 := Nat.max_eq_right (by omega)
  have cast (x : Nat) (hx : x ≤ 2^38) : (Int64.ofNat x).toInt = x := by
    change (Int64.ofInt (x : Int)).toInt = _
    exact Int64.toInt_ofInt_of_le (by omega) (by omega)
  have hoff : (Scaler.make mode d s t).off.toInt = (if s then (2 : Int)^(d - 1) else 0) := by
    cases s <;> simp [Scaler.make, cast _ hpow]
  have hmax : (Scaler.make mode d s t).maxIn.toInt.toNat = 2^d - 1 := by
    simp [Scaler.make, den, cast _ (show 2^d - 1 ≤ 2^38 by omega)]
  simp only [Scaler.applyNative, hmax, hoff]
  exact scaleUnsigned_make mode s hd hd' ht (Nat.min_le_left ..)

/-- Appends pixel `i` of every channel (1 byte, or 2 bytes big-endian, per sample). -/
def pushPixel (wide : Bool) (i : Nat) (out : ByteArray) : List (Plane × Scaler) → ByteArray
  | [] => out
  | (p, s) :: rest =>
    let u := s.apply ((p.get? i).getD 0)
    let out := if wide then (out.push (u >>> 8).toUInt8).push u.toUInt8 else out.push u.toUInt8
    pushPixel wide i out rest

/-- Appends pixels `i = i₀ …` (fuel `k`). -/
def interleaveLoop (wide : Bool) (cs : List (Plane × Scaler)) (out : ByteArray) (i : Nat) :
    Nat → ByteArray
  | 0 => out
  | k + 1 => interleaveLoop wide cs (pushPixel wide i out cs) (i + 1) k

/-- Interleaves `width × height` channels into one buffer of 8-bit (`wide = false`) or
16-bit big-endian (`wide = true`) samples, pixel by pixel, channels in the given order, each
scaled by `mode`. The buffer size is checked against `maxDecodedBytes` first; every plane must
be `width × height`. -/
def interleave (L : Limits) (width height : Nat) (chs : Array Channel) (wide : Bool)
    (mode : Scaling := .linear) : Except Error ByteArray := do
  for c in chs do
    if c.plane.width != width || c.plane.height != height then
      throw (.malformed Image.loc "channel size differs from the image size")
  let n := width * height
  let size := n * chs.size * (if wide then 2 else 1)
  L.check Image.loc .decodedBytes size
  let t := if wide then 16 else 8
  let cs := chs.toList.map fun c => (c.plane, Scaler.make mode c.depth c.signed t)
  return interleaveLoop wide cs (ByteArray.emptyWithCapacity size) 0 n

namespace Image

/-- The channels interleaved: colours, then (with `withAlpha`) the opacity channel. -/
def outChannels (img : Image) (withAlpha : Bool) : Array Channel :=
  match withAlpha, img.alpha with
  | true, some a => img.channels.push a
  | _, _ => img.channels

/-- The image as interleaved 8-bit samples (colours, then alpha with `withAlpha`), scaled
for display (see the module doc). -/
def interleaved8 (img : Image) (L : Limits) (withAlpha : Bool := false)
    (mode : Scaling := .linear) : Except Error ByteArray :=
  interleave L img.width img.height (img.outChannels withAlpha) false mode

/-- The image as interleaved 16-bit big-endian samples (colours, then alpha with
`withAlpha`), scaled for display (see the module doc). -/
def interleaved16 (img : Image) (L : Limits) (withAlpha : Bool := false)
    (mode : Scaling := .linear) : Except Error ByteArray :=
  interleave L img.width img.height (img.outChannels withAlpha) true mode

/-- The soft mask a PDF `/SMaskInData` value selects (ISO 32000-2 §7.4.9): for 1 and 2 the
opacity channel (premultiplied for 2, or when `cdef` says so); `none` for 0, other values,
or an image without an opacity channel. -/
def smaskInData (img : Image) (mode : Nat) : Option SoftMask :=
  if mode == 1 || mode == 2 then
    img.alpha.map fun a => { channel := a, premultiplied := mode == 2 || img.premultiplied }
  else none

end Image

end JPEG2000
