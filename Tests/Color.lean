import JPEG2000.Color
import JPEG2000.Header

/-!
# Tests: colour space, palette, component mapping, channel definitions (task 6.1)

Plan.md §1, §9; T.800 I.5.3.3–I.5.3.6. Hand cases for palette mapping (clamping, signed
columns, mixed direct/palette channels, OpenJPEG's weird-`cmap` repair), `cmap`/`cdef`
validation errors, channel layouts, colour space resolution (including the `METH` 3 skip),
and sYCC → sRGB checked against a transcription of OpenJPEG's `sycc_to_rgb` (double
precision, as in C) and its 4:2:0 / 4:2:2 loops. The corpus part resolves the nine JP2
conformance files (and the two JP2 non-regression files) and checks colour space, channel
formats and layout; `file9.jp2`'s 256 × 3 palette is applied to an index ramp.
-/

namespace JPEG2000.Tests.Color

open JPEG2000 JPEG2000.Box JPEG2000.Bytes JPEG2000.Color

/-- Runs one named check, printing a line on failure; returns 1 on failure, 0 on success. -/
def expect (name : String) (ok : Bool) : IO Nat := do
  if ok then return 0
  IO.eprintln s!"  FAIL color: {name}"
  return 1

/-- The error of an `Except`, if any. -/
def err? {ε α : Type} : Except ε α → Option ε
  | .ok _ => none
  | .error e => some e

/-- The value of an `Except`, if any. -/
def ok? {ε α : Type} : Except ε α → Option α
  | .ok a => some a
  | .error _ => none

/-- Whether a result is a `malformed` error. -/
def isMalformed {α : Type} (r : Except Error α) : Bool :=
  match err? r with
  | some (.malformed ..) => true
  | _ => false

/-- Whether a result is an `unsupported` error. -/
def isUnsupported {α : Type} (r : Except Error α) : Bool :=
  match err? r with
  | some (.unsupported ..) => true
  | _ => false

/-- Whether a result is a `limitExceeded` error. -/
def isLimit {α : Type} (r : Except Error α) : Bool :=
  match err? r with
  | some e => e.isLimit
  | none => false

/-- A plane from row-major values. -/
def mkPlane (w h : Nat) (vs : List Int) : Plane :=
  (vs.zipIdx.foldl (fun p (v, i) => (p.set? i (Int32.ofInt v)).getD p) (Plane.zero w h))

/-- A plane's values, row-major. -/
def vals (p : Plane) : List Int :=
  (List.range (p.width * p.height)).map fun i => ((p.get? i).getD 0).toInt

/-- An unsigned 8-bit channel. -/
def ch8 (w h : Nat) (vs : List Int) (dx dy : Nat := 1) : Channel :=
  { plane := mkPlane w h vs, format := { depth := 8, signed := false, dx, dy } }

/-! ## Palette and component mapping -/

/-- A 4-entry, 2-column palette: column 0 unsigned 8-bit, column 1 signed 8-bit. -/
def pal : Palette :=
  { ne := 4, npc := 2, bits := #[7, 0x87],
    entries := #[10, 0xFF, 20, 0x80, 30, 0x7F, 40, 0x01] }

/-- Palette mapping: clamping, sign extension, column order, mixed direct use. -/
def paletteTests : IO Nat := do
  let idx := ch8 2 2 [-1, 0, 2, 9]
  let other := ch8 2 2 [5, 6, 7, 8]
  let mut f := 0
  let r := applyPalette {} pal #[⟨0, 1, 1⟩, ⟨0, 1, 0⟩] #[idx]
  f := f + (← expect "palette: clamped, signed column 1 first"
    ((ok? r).map (·.toList.map (vals ·.plane)) == some [[-1, -1, 127, 1], [10, 10, 30, 40]]))
  f := f + (← expect "palette: formats"
    ((ok? r).map (·.toList.map fun c => (c.format.depth, c.format.signed))
      == some [(8, true), (8, false)]))
  let r2 := applyPalette {} pal #[⟨1, 0, 0⟩, ⟨0, 1, 0⟩] #[idx, other]
  f := f + (← expect "palette: direct + palette"
    ((ok? r2).map (·.toList.map (vals ·.plane)) == some [[5, 6, 7, 8], [10, 10, 30, 40]]))
  f := f + (← expect "cmap: component ≥ Csiz" (isMalformed (applyPalette {} pal #[⟨1, 1, 0⟩] #[idx])))
  f := f + (← expect "cmap: MTYP 2" (isMalformed (applyPalette {} pal #[⟨0, 2, 0⟩] #[idx])))
  f := f + (← expect "cmap: direct PCOL ≠ 0" (isMalformed (applyPalette {} pal #[⟨0, 0, 1⟩] #[idx])))
  f := f + (← expect "cmap: PCOL ≥ NPC" (isMalformed (applyPalette {} pal #[⟨0, 1, 2⟩] #[idx])))
  f := f + (← expect "cmap: empty" (isMalformed (applyPalette {} pal #[] #[idx])))
  f := f + (← expect "cmap: channel count over maxComponents"
    (isLimit (applyPalette Limits.strict pal (Array.replicate 5 ⟨0, 1, 0⟩) #[idx])))
  f := f + (← expect "pclr: 32-bit unsigned column unsupported"
    (isUnsupported (applyPalette {} { pal with bits := #[31, 0x87] } #[⟨0, 1, 0⟩] #[idx])))
  f := f + (← expect "pclr: 32-bit signed column ok"
    ((ok? (applyPalette {} { pal with bits := #[7, 0x9F] } #[⟨0, 1, 1⟩] #[idx])).isSome))
  f := f + (← expect "pclr: inconsistent entry table"
    (isMalformed (applyPalette {} { pal with ne := 5 } #[⟨0, 1, 0⟩] #[idx])))
  f := f + (← expect "palette: workSamples limit"
    (isLimit (applyPalette { maxWorkSamples := 3 } pal #[⟨0, 1, 0⟩] #[idx])))
  -- OpenJPEG issue 235/447 repair: one component, NPC entries all direct.
  let m := mappingOf {} pal #[⟨0, 0, 0⟩, ⟨0, 0, 0⟩] 1
  f := f + (← expect "cmap: weird cmap repaired"
    ((ok? m).map (·.sources) == some #[.palette 0 0, .palette 0 1]))
  let m2 := mappingOf {} pal #[⟨0, 0, 0⟩, ⟨1, 0, 0⟩] 2
  f := f + (← expect "cmap: two components not repaired"
    ((ok? m2).map (·.sources) == some #[.direct 0, .direct 1]))
  -- pclr without cmap: ignored.
  let h : Jp2Header := { ihdr := default, pclr := some pal }
  f := f + (← expect "pclr without cmap: identity"
    ((ok? (resolveMapping {} h 3)).map (·.sources) == some #[.direct 0, .direct 1, .direct 2]))
  return f

/-! ## Channel definitions -/

/-- `cdef` validation and channel layouts. -/
def cdefTests : IO Nat := do
  let mut f := 0
  let lay (nc : Option Nat) (n : Nat) (ds : List (Nat × Nat × Nat)) :=
    channelLayout nc n (some (ds.toArray.map fun (c, t, a) => ⟨c.toUInt16, t.toUInt16, a.toUInt16⟩))
  f := f + (← expect "cdef: reversed colours (file2)"
    (ok? (lay (some 3) 3 [(0, 0, 3), (1, 0, 2), (2, 0, 1)]) == some { colours := #[2, 1, 0] }))
  f := f + (← expect "cdef: RGBA alpha first"
    (ok? (lay (some 3) 4 [(0, 1, 0), (1, 0, 1), (2, 0, 2), (3, 0, 3)])
      == some { colours := #[1, 2, 3], alpha := some 0 }))
  f := f + (← expect "cdef: premultiplied grey + alpha"
    (ok? (lay (some 1) 2 [(1, 2, 0), (0, 0, 1)])
      == some { colours := #[0], alpha := some 1, premultiplied := true }))
  f := f + (← expect "cdef: per-colour opacity and unspecified are other"
    (ok? (lay (some 1) 3 [(0, 0, 1), (1, 1, 1), (2, 65535, 65535)])
      == some { colours := #[0], other := #[1, 2] }))
  f := f + (← expect "cdef: unknown colour count from Typ 0"
    (ok? (lay none 3 [(0, 0, 2), (1, 0, 1), (2, 1, 0)])
      == some { colours := #[1, 0], alpha := some 2 }))
  f := f + (← expect "cdef: incomplete" (isMalformed (lay (some 1) 2 [(0, 0, 1)])))
  f := f + (← expect "cdef: duplicate channel"
    (isMalformed (lay (some 1) 2 [(0, 0, 1), (0, 1, 0)])))
  f := f + (← expect "cdef: channel index out of range"
    (isMalformed (lay (some 1) 1 [(1, 0, 1)])))
  f := f + (← expect "cdef: association out of range"
    (isMalformed (lay (some 1) 2 [(0, 0, 1), (1, 1, 3)])))
  f := f + (← expect "cdef: colour without channel"
    (isMalformed (lay (some 3) 3 [(0, 0, 1), (1, 0, 2), (2, 1, 0)])))
  f := f + (← expect "cdef: two channels for one colour"
    (isMalformed (lay (some 1) 2 [(0, 0, 1), (1, 0, 1)])))
  f := f + (← expect "no cdef: RGB + extra"
    (ok? (channelLayout (some 3) 4 none) == some { colours := #[0, 1, 2], other := #[3] }))
  f := f + (← expect "no cdef: unknown space, all colours"
    (ok? (channelLayout none 2 none) == some { colours := #[0, 1] }))
  f := f + (← expect "no cdef: more colours than channels"
    (ok? (channelLayout (some 3) 1 none) == some { colours := #[0] }))
  return f

/-! ## Colour space -/

/-- `colr` resolution, including the METH 3 / 4 skip. -/
def spaceTests : IO Nat := do
  let mk (cs : List ColourSpec) : Jp2Header := { ihdr := default, colr := cs.toArray }
  let e (cs : Nat) : ColourSpec := { meth := 1, prec := 0, approx := 0,
                                     method := .enumerated cs.toUInt32 ⟨0, 0⟩ }
  let icc3 : ColourSpec := { meth := 3, prec := 0, approx := 0, method := .icc false ⟨5, 7⟩ }
  let icc2 : ColourSpec := { meth := 2, prec := 0, approx := 0, method := .icc true ⟨9, 11⟩ }
  let ven : ColourSpec := { meth := 4, prec := 0, approx := 0, method := .vendor ⟨1, 2⟩ }
  let mut f := 0
  f := f + (← expect "colr: none" (resolveColourSpace (mk []) == .unknown))
  f := f + (← expect "colr: sRGB" (resolveColourSpace (mk [e 16, e 17]) == .sRGB))
  f := f + (← expect "colr: grey" (resolveColourSpace (mk [e 17]) == .greyscale))
  f := f + (← expect "colr: sYCC" (resolveColourSpace (mk [e 18]) == .sYCC))
  f := f + (← expect "colr: METH 3 skipped" (resolveColourSpace (mk [icc3, e 12]) == .enumerated 12 ⟨0, 0⟩))
  f := f + (← expect "colr: METH 3 + 4 only" (resolveColourSpace (mk [icc3, ven]) == .unknown))
  f := f + (← expect "colr: METH 2 first" (resolveColourSpace (mk [icc2, e 16]) == .icc ⟨9, 11⟩))
  f := f + (← expect "enum colours" ([12, 14, 17, 21, 99].map (enumColours ·)
    == [some 4, some 3, some 1, some 3, none]))
  -- ICC header data colour space at bytes 16..19 of the profile.
  let prof (sig : String) : ByteArray :=
    (List.replicate 3 (0 : UInt8) ++ List.replicate 16 0 ++ sig.toList.map (fun c : Char => c.toNat.toUInt8)
      ++ List.replicate 8 0).toByteArray
  f := f + (← expect "icc colours"
    (["GRAY", "RGB ", "CMYK", "6CLR", "FCLR", "ABCD"].map (fun s => iccColours (prof s) ⟨3, 28⟩)
      == [some 1, some 3, some 4, some 6, some 15, none]))
  f := f + (← expect "icc range outside input" (iccColours (prof "RGB ") ⟨3, 40⟩ == none))
  return f

/-! ## sYCC -/

/-- OpenJPEG's `sycc_to_rgb` transcribed (C `double` arithmetic, `(int)` truncation). -/
def opjSycc (off upb y cb cr : Int) : Int × Int × Int :=
  let cb := Float.ofInt (cb - off)
  let cr := Float.ofInt (cr - off)
  let yf := y
  let clamp (v : Int) : Int := if v < 0 then 0 else if v > upb then upb else v
  (clamp (yf + (1.402 * cr).toInt64.toInt),
   clamp (yf - (0.344 * cb + 0.714 * cr).toInt64.toInt),
   clamp (yf + (1.772 * cb).toInt64.toInt))

/-- Our pixel conversion as `Int`s. -/
def ourSycc (off upb y cb cr : Int) : Int × Int × Int :=
  let (r, g, b) := syccPixel (Int64.ofInt off) (Int64.ofInt upb) (Int64.ofInt y)
    (Int64.ofInt cb) (Int64.ofInt cr)
  (r.toInt, g.toInt, b.toInt)

/-- Whether our pixel agrees with OpenJPEG's: each channel equal, or off by one where the exact
value of its product (`1402·Cr`, `344·Cb + 714·Cr`, `1772·Cb`, over 1000) is an integer, so
that the C `double` result (and its truncation) depends on rounding, and on the platform's
FMA contraction of `0.344·Cb + 0.714·Cr`. Returns `(agrees, exactly equal)`. -/
def agrees (off upb y cb cr : Int) : Bool × Bool :=
  let (r, g, b) := ourSycc off upb y cb cr
  let (r', g', b') := opjSycc off upb y cb cr
  let cbv := cb - off
  let crv := cr - off
  let near (a a' num : Int) : Bool := a == a' || (num % 1000 == 0 && (a - a').natAbs ≤ 1)
  (near r r' (1402 * crv) && near g g' (344 * cbv + 714 * crv) && near b b' (1772 * cbv),
   r == r' && g == g' && b == b')

/-- `(disagreements, boundary differences)` over all 8-bit `(Cb, Cr)` pairs for one `Y`. -/
def sweep8 (y : Int) : Nat × Nat :=
  (List.range 256).foldl (fun acc (cb : Nat) => (List.range 256).foldl (fun (bad, bd) (cr : Nat) =>
    let (ok, eq) := agrees 128 255 y cb cr
    (if ok then bad else bad + 1, if ok && !eq then bd + 1 else bd)) acc) (0, 0)

/-- `(disagreements, boundary differences)` over `n` pseudo-random samples at depth `p`
(LCG). -/
def sweepRandom (p n : Nat) : Nat × Nat := Id.run do
  let off : Int := 2 ^ (p - 1)
  let upb : Int := 2 ^ p - 1
  let mut s : Nat := 12345 + p
  let mut bad := 0
  let mut bd := 0
  for _ in [0:n] do
    s := (s * 1103515245 + 12345) % 2147483648
    let y := s % (2 ^ p)
    s := (s * 1103515245 + 12345) % 2147483648
    let cb := s % (2 ^ p)
    s := (s * 1103515245 + 12345) % 2147483648
    let cr := s % (2 ^ p)
    let (ok, eq) := agrees off upb y cb cr
    if !ok then bad := bad + 1
    if ok && !eq then bd := bd + 1
  return (bad, bd)

/-- OpenJPEG's `sycc420_to_rgb` loop for an even origin (pairs of columns and rows share a
chroma sample), on lists: returns the R plane. -/
def opj420R (w h : Nat) (y cb cr : List Int) (cw : Nat) : List Int :=
  (List.range (w * h)).map fun i =>
    let x := i % w
    let r := i / w
    let ci := (r / 2) * cw + x / 2
    (opjSycc 128 255 (y.getD i 0) (cb.getD ci 0) (cr.getD ci 0)).1

/-- sYCC conversion tests. -/
def syccTests : IO Nat := do
  let mut f := 0
  for y in ([0, 77, 255] : List Int) do
    let (bad, bd) := sweep8 y
    f := f + (← expect s!"sYCC 8-bit sweep Y = {y} ({bad} disagreements, {bd} boundary)" (bad == 0))
  for p in ([10, 12, 16] : List Nat) do
    let (bad, bd) := sweepRandom p 20000
    f := f + (← expect s!"sYCC {p}-bit random ({bad} disagreements, {bd} boundary)" (bad == 0))
  -- 4:2:0, 5 × 3 luma (odd sizes), 3 × 2 chroma, origin 0.
  let yv : List Int := (List.range 15).map fun i => Int.ofNat (i * 17 % 256)
  let cbv : List Int := [10, 200, 128, 40, 90, 250]
  let crv : List Int := [250, 30, 128, 60, 180, 5]
  let res := syccToRgb {} 0 0 (ch8 5 3 yv) (ch8 3 2 cbv 2 2) (ch8 3 2 crv 2 2)
  f := f + (← expect "sYCC 4:2:0 = OpenJPEG loop"
    ((ok? res).map (fun (r, _, _) => vals r.plane) == some (opj420R 5 3 yv cbv crv 3)))
  -- 4:2:2 (dy = 1): rows do not share chroma.
  let res2 := syccToRgb {} 0 0 (ch8 4 2 [1, 2, 3, 4, 5, 6, 7, 8])
    (ch8 2 2 [0, 255, 128, 64] 2 1) (ch8 2 2 [128, 128, 0, 255] 2 1)
  let exp2 := (List.range 8).map fun i =>
    let ci := (i / 4) * 2 + (i % 4) / 2
    (opjSycc 128 255 (Int.ofNat (i + 1)) ([0, 255, 128, 64].getD ci 0)
      ([128, 128, 0, 255].getD ci 0)).2.2
  f := f + (← expect "sYCC 4:2:2 B = OpenJPEG loop"
    ((ok? res2).map (fun (_, _, b) => vals b.plane) == some exp2))
  -- Odd origin XOsiz = 1: luma at grid 1, 2, 3; chroma (dx 2) at grid 2, 4. Luma 1 takes
  -- chroma sample 0 (replicated; OpenJPEG feeds raw 0), luma 2 and 3 share chroma sample 0.
  let res3 := syccToRgb {} 1 0 (ch8 3 1 [100, 100, 100]) (ch8 2 1 [200, 10] 2 1)
    (ch8 2 1 [128, 128] 2 1)
  let b3 := (opjSycc 128 255 100 200 128).2.2
  f := f + (← expect "sYCC odd origin replicates"
    ((ok? res3).map (fun (_, _, b) => vals b.plane) == some [b3, b3, b3]))
  f := f + (← expect "sYCC: depth 32 unsupported"
    (isUnsupported (syccToRgb {} 0 0 { ch8 1 1 [0] with format := { depth := 32, signed := false } }
      (ch8 1 1 [0]) (ch8 1 1 [0]))))
  f := f + (← expect "sYCC: empty chroma" (isMalformed (syccToRgb {} 0 0 (ch8 1 1 [0])
    (ch8 0 0 []) (ch8 1 1 [0]))))
  f := f + (← expect "sYCC: workSamples limit"
    (isLimit (syccToRgb { maxWorkSamples := 8 } 0 0 (ch8 2 2 [0, 0, 0, 0]) (ch8 2 2 [0, 0, 0, 0])
      (ch8 2 2 [0, 0, 0, 0]))))
  return f

/-! ## Corpus -/

/-- Expected colour information of a corpus JP2 file. -/
structure Expected where
  /-- File name. -/
  name : String
  /-- Expected colour space (byte ranges compared only by constructor and code). -/
  space : String
  /-- Number of colours of the colour space. -/
  nColours : Option Nat
  /-- Expected layout. -/
  layout : ChannelLayout
  /-- Expected (depth, signed, dx, dy) per output channel. -/
  formats : List (Nat × Bool × Nat × Nat)

/-- A short description of a colour space for comparison. -/
def spaceName : ColourSpace → String
  | .sRGB => "sRGB"
  | .greyscale => "grey"
  | .sYCC => "sYCC"
  | .enumerated cs _ => s!"enum {cs}"
  | .icc _ => "icc"
  | .unknown => "unknown"

/-- Unsigned 8-bit, no sub-sampling. -/
def u8 : Nat × Bool × Nat × Nat := (8, false, 1, 1)

/-- Expectations from reading the files' boxes (see the module doc of `JPEG2000.Color`):
file1 sRGB; file2 sYCC with a reversed `cdef`; file3 sYCC 4:2:0; file4 greyscale; file5
restricted ICC (RGB) before a ROMM-RGB (21) `colr`; file6 12-bit greyscale; file7 16-bit
restricted ICC (RGB) before an e-sRGB (20) `colr`; file8 restricted ICC (GRAY); file9 sRGB
through a 256 × 3 palette of one 8-bit component. -/
def expected : List (String × Expected) :=
  let rgb : ChannelLayout := { colours := #[0, 1, 2] }
  let grey : ChannelLayout := { colours := #[0] }
  [("conformance", ⟨"file1.jp2", "sRGB", some 3, rgb, [u8, u8, u8]⟩),
   ("conformance", ⟨"file2.jp2", "sYCC", some 3, { colours := #[2, 1, 0] }, [u8, u8, u8]⟩),
   ("conformance", ⟨"file3.jp2", "sYCC", some 3, rgb, [u8, (8, false, 2, 2), (8, false, 2, 2)]⟩),
   ("conformance", ⟨"file4.jp2", "grey", some 1, grey, [u8]⟩),
   ("conformance", ⟨"file5.jp2", "icc", some 3, rgb, [u8, u8, u8]⟩),
   ("conformance", ⟨"file6.jp2", "grey", some 1, grey, [(12, false, 1, 1)]⟩),
   ("conformance", ⟨"file7.jp2", "icc", some 3, rgb,
      [(16, false, 1, 1), (16, false, 1, 1), (16, false, 1, 1)]⟩),
   ("conformance", ⟨"file8.jp2", "icc", some 1, grey, [u8]⟩),
   ("conformance", ⟨"file9.jp2", "sRGB", some 3, rgb, [u8, u8, u8]⟩),
   -- METH 3 CMYK ICC first, then enumerated CMYK (12): the ICC box is skipped.
   ("nonregression", ⟨"issue208.jp2", "enum 12", some 4, { colours := #[0, 1, 2, 3] },
      [u8, u8, u8, u8]⟩),
   ("nonregression", ⟨"issue559-eci-090-CIELab.jp2", "enum 14", some 3, rgb,
      [(16, false, 1, 1), (16, false, 1, 1), (16, false, 1, 1)]⟩)]

/-- Root of the fetched corpus. -/
def corpusDir : System.FilePath := "corpus/files/openjpeg-data/input"

/-- Resolves one corpus file and compares with its expectation. -/
def checkFile (e : Expected) (d : ByteArray) : IO Nat := do
  match Header.parse {} d with
  | .error err => expect s!"{e.name}: header parse ({err})" false
  | .ok h =>
    let hdr := h.container.bind (·.header)
    match resolve {} d hdr h.siz.components with
    | .error err => expect s!"{e.name}: resolve ({err})" false
    | .ok info =>
      let mut f := 0
      f := f + (← expect s!"{e.name}: space {spaceName info.space}" (spaceName info.space == e.space))
      f := f + (← expect s!"{e.name}: colours" (info.space.numColours d == e.nColours))
      f := f + (← expect s!"{e.name}: layout {repr info.layout}" (info.layout == e.layout))
      f := f + (← expect s!"{e.name}: formats"
        (info.formats.toList.map (fun x => (x.depth, x.signed, x.dx, x.dy)) == e.formats))
      return f

/-- file9: the palette maps an index ramp 0…255 to its entries, and the mapping validates
against the SIZ from `Header.parse`. -/
def file9Palette (d : ByteArray) : IO Nat := do
  match Header.parse {} d with
  | .error err => expect s!"file9: parse ({err})" false
  | .ok h =>
    let some hdr := h.container.bind (·.header) | expect "file9: no JP2 header" false
    let some p := hdr.pclr | expect "file9: no pclr" false
    let some cm := hdr.cmap | expect "file9: no cmap" false
    let mut f := 0
    f := f + (← expect "file9: palette 256 × 3, 8-bit"
      (p.ne == 256 && p.npc == 3 && p.bits == #[7, 7, 7]))
    f := f + (← expect "file9: mapping sources"
      ((ok? (resolveMapping {} hdr h.siz.components.size)).map (·.sources)
        == some #[.palette 0 0, .palette 0 1, .palette 0 2]))
    let ramp := ch8 16 16 ((List.range 256).map Int.ofNat)
    match applyPalette {} p cm #[ramp] with
    | .error err => f := f + (← expect s!"file9: apply ({err})" false)
    | .ok chs =>
      let ok := (List.range 3).all fun c =>
        vals ((chs.getD c (ramp)).plane) == (List.range 256).map fun j =>
          Int.ofNat (p.entries.getD (j * 3 + c) 0).toNat
      f := f + (← expect "file9: ramp maps to entries" (chs.size == 3 && ok))
      f := f + (← expect "file9: first entries black, white"
        ((chs.map fun c => vals c.plane |>.take 2).toList == [[0, 255], [0, 255], [0, 255]]))
    return f

/-- Corpus tests; skip (0 failures) when the corpus is absent. -/
def corpusTests : IO Nat := do
  if !(← corpusDir.pathExists) then
    IO.println s!"  color: corpus not present at {corpusDir}, skipping corpus tests"
    return 0
  let mut f := 0
  for (dir, e) in expected do
    let p := corpusDir / dir / e.name
    if !(← p.pathExists) then
      IO.println s!"  color: {p} missing, skipped"
      continue
    f := f + (← checkFile e (← IO.FS.readBinFile p))
  let p9 := corpusDir / "conformance" / "file9.jp2"
  if ← p9.pathExists then
    f := f + (← file9Palette (← IO.FS.readBinFile p9))
  return f

/-- Runs every colour test; returns the number of failures. -/
def run : IO Nat := do
  return (← paletteTests) + (← cdefTests) + (← spaceTests) + (← syccTests) + (← corpusTests)

end JPEG2000.Tests.Color
