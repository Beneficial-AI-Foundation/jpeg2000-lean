import JPEG2000.Marker
import Spec.Resources.DiagnosticMarker
import Tests.Box

/-!
# Unit and corpus tests: main-header marker segments (task 1.3)

Plan.md §4 S2/S3, §8; T.800 Annex A (A.2 marker layout, A.5.1 SIZ, A.6.1–A.6.6 COD/COC/
RGN/QCD/QCC/POC, A.9 CRG/COM). Hand-built segment bodies for every type, including error
cases (bad lengths, out-of-range fields, `Csiz ≥ 257` two-byte component indices), and the
main headers of the 23 T.803 streams compared with values taken from `opj_dump -i`
(OpenJPEG 2.5.3); the corpus part is skipped when the files are absent.
-/

namespace JPEG2000.Tests.Marker

open JPEG2000 JPEG2000.Bytes JPEG2000.Marker

/-- Runs one named check, printing a line on failure; returns 1 on failure, 0 on success. -/
def expect (name : String) (ok : Bool) : IO Nat := do
  if ok then return 0
  IO.eprintln s!"  FAIL marker: {name}"
  return 1

/-- The outcome class of a parse: `ok`, `truncated`, `malformed`, `unsupported`, `limit`. -/
def kind {α : Type} : Except Error α → String
  | .ok _ => "ok"
  | .error (.truncated ..) => "truncated"
  | .error (.malformed ..) => "malformed"
  | .error (.unsupported ..) => "unsupported"
  | .error (.limitExceeded ..) => "limit"

/-- The value of an `Except`, if any. -/
def ok? {ε α : Type} : Except ε α → Option α
  | .ok a => some a
  | .error _ => none

/-- A reader over a list of bytes. -/
def rd (bs : List UInt8) : Reader := Reader.ofByteArray bs.toByteArray

/-- Big-endian 16-bit bytes. -/
def be16 (v : Nat) : List UInt8 := [(v / 256 % 256).toUInt8, (v % 256).toUInt8]

/-- Big-endian 32-bit bytes. -/
def be32 (v : Nat) : List UInt8 := be16 (v / 65536 % 65536) ++ be16 (v % 65536)

/-- A SIZ body: grid, offsets, tile size/offset, and components `(Ssiz, XRsiz, YRsiz)`. -/
def sizBody (x y xo yo xt yt xto yto : Nat) (comps : List (UInt8 × UInt8 × UInt8)) :
    List UInt8 :=
  be16 0 ++ be32 x ++ be32 y ++ be32 xo ++ be32 yo ++ be32 xt ++ be32 yt ++ be32 xto ++
    be32 yto ++ be16 comps.length ++ comps.flatMap fun (s, a, b) => [s, a, b]

/-- A simple valid SIZ body: 64×32 image, one tile, `n` 8-bit components. -/
def sizN (n : Nat) : List UInt8 := sizBody 64 32 0 0 64 32 0 0 (List.replicate n (7, 1, 1))

/-- A marker segment: marker, `Lxxx` = body length + 2, body. -/
def seg (m : Nat) (body : List UInt8) : List UInt8 := be16 m ++ be16 (body.length + 2) ++ body

/-- A valid COD body: no precincts, LRCP, 1 layer, no MCT, 2 levels, 64×64, 5/3. -/
def codBody : List UInt8 := [0, 0] ++ be16 1 ++ [0, 2, 4, 4, 0, 1]

/-- A valid QCD body: no quantisation, 2 guard bits, 7 bands. -/
def qcdBody : List UInt8 := [0x40] ++ List.replicate 7 (0x40 : UInt8)

/-- A codestream main header followed by `SOT`: SOC, SIZ, the given segments. -/
def stream (siz : List UInt8) (segs : List UInt8) : List UInt8 :=
  be16 0xFF4F ++ seg 0xFF51 siz ++ segs ++ be16 0xFF90 ++ be16 10

/-- Parses a stream with the default limits. -/
def mh (bs : List UInt8) : Except Error (MainHeader × Reader) :=
  parseMainHeader Limits.default (rd bs)

/-! ## Corpus table (values from `opj_dump -i`, OpenJPEG 2.5.3) -/

/-- Per-component image values: `dx`, `dy`, `prec`, `sgnd`. -/
structure CompRow where
  /-- Horizontal sub-sampling. -/
  dx : Nat
  /-- Vertical sub-sampling. -/
  dy : Nat
  /-- Bit depth. -/
  prec : Nat
  /-- Signedness (0/1). -/
  sgnd : Nat

/-- Per-component effective coding values (after COC/QCC/RGN), as `opj_dump` prints them. -/
structure CodingRow where
  /-- `Scoc` (precincts defined, 0/1). -/
  csty : Nat
  /-- Number of resolutions (levels + 1). -/
  numres : Nat
  /-- Code-block width exponent. -/
  cblkw : Nat
  /-- Code-block height exponent. -/
  cblkh : Nat
  /-- Code-block style byte. -/
  cblksty : Nat
  /-- Transform (0 = 9/7, 1 = 5/3). -/
  qmfbid : Nat
  /-- Quantisation style. -/
  qntsty : Nat
  /-- Guard bits. -/
  numgbits : Nat
  /-- ROI shift. -/
  roishift : Nat
  /-- Precinct size bytes per resolution (`PPx + 16·PPy`). -/
  precincts : List Nat

/-- One T.803 stream's expected main header. -/
structure Row where
  /-- File name. -/
  file : String
  /-- `XOsiz, YOsiz, Xsiz, Ysiz`. -/
  img : Nat × Nat × Nat × Nat
  /-- `XTOsiz, YTOsiz, XTsiz, YTsiz`. -/
  tile : Nat × Nat × Nat × Nat
  /-- `Csiz`. -/
  csiz : Nat
  /-- Run-length encoded components. -/
  comps : List (Nat × CompRow)
  /-- `Scod`. -/
  scod : Nat
  /-- Progression order. -/
  prg : Nat
  /-- Layers. -/
  layers : Nat
  /-- MCT. -/
  mct : Nat
  /-- Run-length encoded per-component coding values. -/
  coding : List (Nat × CodingRow)
  /-- Offset of the first SOT. -/
  endPos : Nat
  /-- Marker index `(code, pos, len)`. -/
  markers : List (Nat × Nat × Nat)

/-- The 23 T.803 streams (p0_01–p0_16, p1_01–p1_07). -/
def table : List Row := [
  { file := "p0_01.j2k", img := (0, 0, 128, 128),
    tile := (0, 0, 128, 128), csiz := 1,
    comps := [(1, ⟨1,1,8,0⟩)],
    scod := 0, prg := 1, layers := 1, mct := 0,
    coding := [(1, ⟨0,4,6,6,0,1,0,2,0,[255,255,255,255]⟩)],
    endPos := 74, markers := [(65359, 0, 2), (65361, 2, 43), (65372, 45, 15), (65362, 60, 14)] },
  { file := "p0_02.j2k", img := (0, 0, 127, 126),
    tile := (0, 0, 127, 126), csiz := 1,
    comps := [(1, ⟨2,1,8,0⟩)],
    scod := 6, prg := 0, layers := 6, mct := 0,
    coding := [(1, ⟨0,4,5,5,52,1,0,3,0,[255,255,255,255]⟩)],
    endPos := 134, markers := [(65359, 0, 2), (65361, 2, 43), (65362, 45, 14), (65363, 59, 11), (65372, 70, 15), (65380, 85, 47)] },
  { file := "p0_03.j2k", img := (0, 0, 256, 256),
    tile := (0, 0, 128, 128), csiz := 1,
    comps := [(1, ⟨1,1,4,1⟩)],
    scod := 2, prg := 3, layers := 8, mct := 0,
    coding := [(1, ⟨0,2,6,6,0,1,0,2,0,[255,255]⟩)],
    endPos := 298, markers := [(65359, 0, 2), (65361, 2, 43), (65362, 45, 14), (65372, 59, 7), (65373, 66, 10), (65375, 76, 11), (65379, 87, 8), (65380, 95, 47), (65380, 142, 58), (65380, 200, 68), (65365, 268, 30)] },
  { file := "p0_04.j2k", img := (0, 0, 640, 480),
    tile := (0, 0, 640, 480), csiz := 3,
    comps := [(3, ⟨1,1,8,0⟩)],
    scod := 1, prg := 1, layers := 20, mct := 1,
    coding := [(3, ⟨1,7,6,6,4,0,2,3,0,[119,119,119,119,119,119,119]⟩)],
    endPos := 250, markers := [(65359, 0, 2), (65361, 2, 49), (65362, 51, 21), (65372, 72, 43), (65373, 115, 44), (65373, 159, 44), (65380, 203, 47)] },
  { file := "p0_05.j2k", img := (0, 0, 1024, 1024),
    tile := (0, 0, 1024, 1024), csiz := 4,
    comps := [(2, ⟨1,1,8,0⟩), (2, ⟨2,2,8,0⟩)],
    scod := 0, prg := 3, layers := 7, mct := 0,
    coding := [(1, ⟨0,7,5,5,0,0,1,3,0,[255,255,255,255,255,255,255]⟩), (1, ⟨0,4,5,5,0,0,2,3,0,[255,255,255,255]⟩), (1, ⟨0,7,5,5,0,0,2,3,0,[255,255,255,255,255,255,255]⟩), (1, ⟨0,7,5,5,0,1,0,3,0,[255,255,255,255,255,255,255]⟩)],
    endPos := 225, markers := [(65359, 0, 2), (65361, 2, 52), (65362, 54, 14), (65363, 68, 11), (65363, 79, 11), (65372, 90, 43), (65373, 133, 8), (65373, 141, 25), (65380, 166, 47), (65365, 213, 12)] },
  { file := "p0_06.j2k", img := (0, 0, 513, 129),
    tile := (0, 0, 513, 129), csiz := 4,
    comps := [(1, ⟨1,1,12,0⟩), (1, ⟨2,1,12,0⟩), (1, ⟨1,2,12,0⟩), (1, ⟨2,2,12,0⟩)],
    scod := 0, prg := 2, layers := 4, mct := 0,
    coding := [(1, ⟨0,7,6,6,0,0,2,3,11,[255,255,255,255,255,255,255]⟩), (1, ⟨0,7,6,6,0,0,2,4,0,[255,255,255,255,255,255,255]⟩), (1, ⟨0,7,6,6,0,0,2,5,0,[255,255,255,255,255,255,255]⟩), (1, ⟨0,7,6,6,0,1,0,6,0,[255,255,255,255,255,255,255]⟩)],
    endPos := 242, markers := [(65359, 0, 2), (65361, 2, 52), (65362, 54, 14), (65372, 68, 43), (65373, 111, 44), (65373, 155, 44), (65373, 199, 25), (65363, 224, 11), (65374, 235, 7)] },
  { file := "p0_07.j2k", img := (0, 0, 2048, 2048),
    tile := (0, 0, 128, 128), csiz := 3,
    comps := [(3, ⟨1,1,12,1⟩)],
    scod := 6, prg := 1, layers := 8, mct := 0,
    coding := [(3, ⟨0,4,6,6,0,1,0,1,0,[255,255,255,255]⟩)],
    endPos := 98, markers := [(65359, 0, 2), (65361, 2, 49), (65362, 51, 14), (65372, 65, 15), (65380, 80, 18)] },
  { file := "p0_08.j2k", img := (0, 0, 513, 3072),
    tile := (0, 0, 513, 3072), csiz := 3,
    comps := [(3, ⟨1,1,12,1⟩)],
    scod := 6, prg := 4, layers := 30, mct := 0,
    coding := [(1, ⟨0,7,6,6,0,1,0,4,0,[255,255,255,255,255,255,255]⟩), (1, ⟨0,8,5,5,0,1,0,4,0,[255,255,255,255,255,255,255,255]⟩), (1, ⟨0,9,6,6,0,1,0,4,0,[255,255,255,255,255,255,255,255,255]⟩)],
    endPos := 199, markers := [(65359, 0, 2), (65361, 2, 49), (65362, 51, 14), (65363, 65, 11), (65363, 76, 11), (65363, 87, 11), (65372, 98, 27), (65373, 125, 25), (65373, 150, 31), (65380, 181, 18)] },
  { file := "p0_09.j2k", img := (0, 0, 17, 37),
    tile := (0, 0, 17, 37), csiz := 1,
    comps := [(1, ⟨1,1,8,0⟩)],
    scod := 0, prg := 0, layers := 1, mct := 0,
    coding := [(1, ⟨0,6,6,6,0,0,2,1,0,[255,255,255,255,255,255]⟩)],
    endPos := 114, markers := [(65359, 0, 2), (65361, 2, 43), (65362, 45, 14), (65372, 59, 37), (65380, 96, 18)] },
  { file := "p0_10.j2k", img := (0, 0, 256, 256),
    tile := (0, 0, 128, 128), csiz := 3,
    comps := [(3, ⟨4,4,8,0⟩)],
    scod := 0, prg := 0, layers := 2, mct := 1,
    coding := [(3, ⟨0,4,6,6,0,1,0,0,0,[255,255,255,255]⟩)],
    endPos := 80, markers := [(65359, 0, 2), (65361, 2, 49), (65362, 51, 14), (65372, 65, 15)] },
  { file := "p0_11.j2k", img := (0, 0, 128, 1),
    tile := (0, 0, 128, 128), csiz := 1,
    comps := [(1, ⟨1,1,8,0⟩)],
    scod := 5, prg := 0, layers := 1, mct := 0,
    coding := [(1, ⟨1,1,6,6,32,1,0,3,0,[23]⟩)],
    endPos := 113, markers := [(65359, 0, 2), (65361, 2, 43), (65362, 45, 15), (65372, 60, 6), (65380, 66, 47)] },
  { file := "p0_12.j2k", img := (0, 0, 3, 5),
    tile := (0, 0, 3, 5), csiz := 1,
    comps := [(1, ⟨1,1,8,0⟩)],
    scod := 2, prg := 0, layers := 1, mct := 0,
    coding := [(1, ⟨0,4,5,5,4,1,0,3,0,[255,255,255,255]⟩)],
    endPos := 121, markers := [(65359, 0, 2), (65361, 2, 43), (65362, 45, 14), (65372, 59, 15), (65380, 74, 47)] },
  { file := "p0_13.j2k", img := (0, 0, 1, 1),
    tile := (0, 0, 1, 1), csiz := 257,
    comps := [(257, ⟨1,1,8,0⟩)],
    scod := 0, prg := 1, layers := 1, mct := 1,
    coding := [(1, ⟨0,2,5,5,16,1,0,2,0,[255,255]⟩), (1, ⟨0,2,5,5,16,1,0,3,0,[255,255]⟩), (1, ⟨0,2,6,6,0,1,0,2,0,[255,255]⟩), (1, ⟨0,2,5,5,16,1,0,2,11,[255,255]⟩), (253, ⟨0,2,5,5,16,1,0,2,0,[255,255]⟩)],
    endPos := 947, markers := [(65359, 0, 2), (65361, 2, 811), (65362, 813, 14), (65363, 827, 12), (65372, 839, 9), (65373, 848, 11), (65373, 859, 11), (65374, 870, 8), (65375, 878, 22), (65380, 900, 47)] },
  { file := "p0_14.j2k", img := (0, 0, 49, 49),
    tile := (0, 0, 49, 49), csiz := 3,
    comps := [(3, ⟨1,1,8,0⟩)],
    scod := 0, prg := 0, layers := 1, mct := 1,
    coding := [(3, ⟨0,6,6,6,0,1,0,1,0,[255,255,255,255,255,255]⟩)],
    endPos := 104, markers := [(65359, 0, 2), (65361, 2, 49), (65362, 51, 14), (65372, 65, 21), (65380, 86, 18)] },
  { file := "p0_15.j2k", img := (0, 0, 256, 256),
    tile := (0, 0, 128, 128), csiz := 1,
    comps := [(1, ⟨1,1,4,1⟩)],
    scod := 2, prg := 3, layers := 8, mct := 0,
    coding := [(1, ⟨0,2,6,6,0,1,0,2,0,[255,255]⟩)],
    endPos := 298, markers := [(65359, 0, 2), (65361, 2, 43), (65362, 45, 14), (65372, 59, 7), (65373, 66, 10), (65375, 76, 11), (65379, 87, 8), (65380, 95, 47), (65380, 142, 58), (65380, 200, 68), (65365, 268, 30)] },
  { file := "p0_16.j2k", img := (0, 0, 128, 128),
    tile := (0, 0, 128, 128), csiz := 1,
    comps := [(1, ⟨1,1,8,0⟩)],
    scod := 0, prg := 1, layers := 3, mct := 0,
    coding := [(1, ⟨0,4,6,6,0,1,0,2,0,[255,255,255,255]⟩)],
    endPos := 74, markers := [(65359, 0, 2), (65361, 2, 43), (65362, 45, 14), (65372, 59, 15)] },
  { file := "p1_01.j2k", img := (5, 128, 127, 227),
    tile := (1, 101, 127, 126), csiz := 1,
    comps := [(1, ⟨2,1,8,0⟩)],
    scod := 6, prg := 0, layers := 5, mct := 0,
    coding := [(1, ⟨0,4,5,5,52,1,0,3,0,[255,255,255,255]⟩)],
    endPos := 132, markers := [(65359, 0, 2), (65361, 2, 43), (65362, 45, 14), (65363, 59, 11), (65372, 70, 15), (65380, 85, 47)] },
  { file := "p1_02.j2k", img := (0, 0, 640, 480),
    tile := (0, 0, 640, 480), csiz := 3,
    comps := [(3, ⟨1,1,8,0⟩)],
    scod := 1, prg := 0, layers := 19, mct := 1,
    coding := [(3, ⟨1,7,6,6,10,0,2,3,0,[119,136,153,170,187,204,221]⟩)],
    endPos := 250, markers := [(65359, 0, 2), (65361, 2, 49), (65362, 51, 21), (65372, 72, 43), (65373, 115, 44), (65373, 159, 44), (65380, 203, 47)] },
  { file := "p1_03.j2k", img := (0, 0, 1024, 1024),
    tile := (0, 0, 1024, 1024), csiz := 4,
    comps := [(2, ⟨1,1,8,0⟩), (2, ⟨2,2,8,0⟩)],
    scod := 0, prg := 3, layers := 10, mct := 0,
    coding := [(1, ⟨0,7,5,5,5,0,1,3,0,[255,255,255,255,255,255,255]⟩), (1, ⟨0,4,5,5,5,0,2,3,0,[255,255,255,255]⟩), (1, ⟨0,7,5,5,5,0,2,3,0,[255,255,255,255,255,255,255]⟩), (1, ⟨0,7,5,5,5,1,0,3,0,[255,255,255,255,255,255,255]⟩)],
    endPos := 43939, markers := [(65359, 0, 2), (65361, 2, 52), (65362, 54, 14), (65363, 68, 11), (65363, 79, 11), (65372, 90, 43), (65373, 133, 8), (65373, 141, 25), (65380, 166, 47), (65376, 213, 43714), (65365, 43927, 12)] },
  { file := "p1_04.j2k", img := (0, 0, 1024, 1024),
    tile := (0, 0, 128, 128), csiz := 1,
    comps := [(1, ⟨1,1,12,0⟩)],
    scod := 0, prg := 0, layers := 1, mct := 0,
    coding := [(1, ⟨0,4,6,6,0,0,2,2,0,[255,255,255,255]⟩)],
    endPos := 374, markers := [(65359, 0, 2), (65361, 2, 43), (65362, 45, 14), (65372, 59, 25), (65365, 84, 262), (65380, 346, 28)] },
  { file := "p1_05.j2k", img := (17, 12, 529, 524),
    tile := (8, 2, 37, 37), csiz := 3,
    comps := [(3, ⟨1,1,8,0⟩)],
    scod := 7, prg := 3, layers := 2, mct := 1,
    coding := [(3, ⟨1,8,3,6,25,0,2,3,0,[68,68,68,68,68,68,68,68]⟩)],
    endPos := 100711, markers := [(65359, 0, 2), (65361, 2, 49), (65362, 51, 22), (65372, 73, 49), (65380, 122, 47), (65376, 169, 318), (65376, 487, 472), (65376, 959, 387), (65376, 1346, 364), (65376, 1710, 502), (65376, 2212, 413), (65376, 2625, 491), (65376, 3116, 426), (65376, 3542, 468), (65376, 4010, 425), (65376, 4435, 441), (65376, 4876, 490), (65376, 5366, 383), (65376, 5749, 463), (65376, 6212, 231), (65376, 6443, 329), (65376, 6772, 485), (65376, 7257, 362), (65376, 7619, 429), (65376, 8048, 559), (65376, 8607, 422), (65376, 9029, 517), (65376, 9546, 438), (65376, 9984, 517), (65376, 10501, 461), (65376, 10962, 511), (65376, 11473, 502), (65376, 11975, 373), (65376, 12348, 447), (65376, 12795, 234), (65376, 13029, 339), (65376, 13368, 524), (65376, 13892, 473), (65376, 14365, 482), (65376, 14847, 575), (65376, 15422, 458), (65376, 15880, 530), (65376, 16410, 452), (65376, 16862, 455), (65376, 17317, 496), (65376, 17813, 483), (65376, 18296, 537), (65376, 18833, 383), (65376, 19216, 480), (65376, 19696, 251), (65376, 19947, 340), (65376, 20287, 581), (65376, 20868, 430), (65376, 21298, 555), (65376, 21853, 573), (65376, 22426, 410), (65376, 22836, 581), (65376, 23417, 469), (65376, 23886, 478), (65376, 24364, 423), (65376, 24787, 513), (65376, 25300, 566), (65376, 25866, 418), (65376, 26284, 529), (65376, 26813, 249), (65376, 27062, 332), (65376, 27394, 495), (65376, 27889, 399), (65376, 28288, 465), (65376, 28753, 532), (65376, 29285, 410), (65376, 29695, 490), (65376, 30185, 391), (65376, 30576, 422), (65376, 30998, 354), (65376, 31352, 354), (65376, 31706, 402), (65376, 32108, 339), (65376, 32447, 407), (65376, 32854, 219), (65376, 33073, 334), (65376, 33407, 521), (65376, 33928, 411), (65376, 34339, 512), (65376, 34851, 585), (65376, 35436, 425), (65376, 35861, 515), (65376, 36376, 412), (65376, 36788, 486), (65376, 37274, 364), (65376, 37638, 431), (65376, 38069, 515), (65376, 38584, 375), (65376, 38959, 490), (65376, 39449, 244), (65376, 39693, 417), (65376, 40110, 620), (65376, 40730, 472), (65376, 41202, 594), (65376, 41796, 646), (65376, 42442, 463), (65376, 42905, 632), (65376, 43537, 495), (65376, 44032, 531), (65376, 44563, 439), (65376, 45002, 540), (65376, 45542, 591), (65376, 46133, 454), (65376, 46587, 532), (65376, 47119, 277), (65376, 47396, 345), (65376, 47741, 510), (65376, 48251, 414), (65376, 48665, 445), (65376, 49110, 511), (65376, 49621, 388), (65376, 50009, 482), (65376, 50491, 395), (65376, 50886, 425), (65376, 51311, 417), (65376, 51728, 442), (65376, 52170, 481), (65376, 52651, 408), (65376, 53059, 400), (65376, 53459, 213), (65376, 53672, 400), (65376, 54072, 592), (65376, 54664, 436), (65376, 55100, 507), (65376, 55607, 554), (65376, 56161, 433), (65376, 56594, 553), (65376, 57147, 401), (65376, 57548, 513), (65376, 58061, 459), (65376, 58520, 500), (65376, 59020, 561), (65376, 59581, 463), (65376, 60044, 472), (65376, 60516, 243), (65376, 60759, 356), (65376, 61115, 589), (65376, 61704, 453), (65376, 62157, 529), (65376, 62686, 593), (65376, 63279, 467), (65376, 63746, 519), (65376, 64265, 469), (65376, 64734, 482), (65376, 65216, 491), (65376, 65707, 500), (65376, 66207, 570), (65376, 66777, 483), (65376, 67260, 524), (65376, 67784, 266), (65376, 68050, 401), (65376, 68451, 573), (65376, 69024, 436), (65376, 69460, 574), (65376, 70034, 631), (65376, 70665, 479), (65376, 71144, 586), (65376, 71730, 421), (65376, 72151, 519), (65376, 72670, 474), (65376, 73144, 525), (65376, 73669, 572), (65376, 74241, 461), (65376, 74702, 575), (65376, 75277, 281), (65376, 75558, 329), (65376, 75887, 493), (65376, 76380, 414), (65376, 76794, 444), (65376, 77238, 526), (65376, 77764, 402), (65376, 78166, 517), (65376, 78683, 379), (65376, 79062, 407), (65376, 79469, 413), (65376, 79882, 432), (65376, 80314, 482), (65376, 80796, 406), (65376, 81202, 425), (65376, 81627, 228), (65376, 81855, 408), (65376, 82263, 630), (65376, 82893, 512), (65376, 83405, 607), (65376, 84012, 709), (65376, 84721, 537), (65376, 85258, 615), (65376, 85873, 503), (65376, 86376, 558), (65376, 86934, 534), (65376, 87468, 547), (65376, 88015, 640), (65376, 88655, 515), (65376, 89170, 586), (65376, 89756, 290), (65376, 90046, 371), (65376, 90417, 566), (65376, 90983, 481), (65376, 91464, 597), (65376, 92061, 613), (65376, 92674, 487), (65376, 93161, 628), (65376, 93789, 479), (65376, 94268, 528), (65376, 94796, 477), (65376, 95273, 546), (65376, 95819, 586), (65376, 96405, 488), (65376, 96893, 666), (65376, 97559, 305), (65376, 97864, 158), (65376, 98022, 210), (65376, 98232, 169), (65376, 98401, 213), (65376, 98614, 224), (65376, 98838, 175), (65376, 99013, 232), (65376, 99245, 171), (65376, 99416, 181), (65376, 99597, 171), (65376, 99768, 203), (65376, 99971, 215), (65376, 100186, 183), (65376, 100369, 230), (65376, 100599, 112)] },
  { file := "p1_06.j2k", img := (0, 0, 12, 12),
    tile := (0, 0, 3, 3), csiz := 3,
    comps := [(3, ⟨1,1,8,0⟩)],
    scod := 6, prg := 3, layers := 1, mct := 1,
    coding := [(3, ⟨0,5,6,5,40,0,2,3,0,[255,255,255,255,255]⟩)],
    endPos := 143, markers := [(65359, 0, 2), (65361, 2, 49), (65362, 51, 14), (65372, 65, 31), (65380, 96, 47)] },
  { file := "p1_07.j2k", img := (4, 0, 12, 12),
    tile := (4, 0, 12, 12), csiz := 2,
    comps := [(1, ⟨4,1,8,0⟩), (1, ⟨1,1,8,0⟩)],
    scod := 7, prg := 2, layers := 1, mct := 0,
    coding := [(1, ⟨1,2,6,6,0,1,0,2,0,[0,17]⟩), (1, ⟨1,2,6,6,0,1,0,2,0,[17,34]⟩)],
    endPos := 133, markers := [(65359, 0, 2), (65361, 2, 46), (65362, 48, 16), (65363, 64, 13), (65372, 77, 9), (65380, 86, 47)] }
  ]

/-- Expands a run-length list. -/
def expand {α : Type} : List (Nat × α) → List α
  | [] => []
  | (n, a) :: rest => List.replicate n a ++ expand rest

/-- `opj_dump`-style values of one component of a parsed header. -/
def compValues (c : Component) : List Nat :=
  [c.dx.toNat, c.dy.toNat, c.depth.toNat, if c.signed then 1 else 0]

/-- The effective coding values of component `c` (last COC/QCC/RGN for `c` wins). -/
def codingValues (h : MainHeader) (c : Nat) : List Nat :=
  let st := ((h.coc.toList.filter (·.component.toNat == c)).getLast?.map (·.style)).getD
    h.cod.style
  let q := ((h.qcc.toList.filter (·.component.toNat == c)).getLast?.map (·.params)).getD h.qcd
  let roi := ((h.rgn.toList.filter (·.component.toNat == c)).getLast?.map (·.shift.toNat)).getD 0
  let qs := match q.quant with | .none _ => 0 | .derived _ => 1 | .expounded _ => 2
  [if st.precincts.isSome then 1 else 0, st.levels.toNat + 1, st.cbWidthExp, st.cbHeightExp,
   st.cbStyle.toNat, st.transform.toUInt8.toNat, qs, q.guardBits.toNat, roi] ++
  (List.range (st.levels.toNat + 1)).map fun r => (st.precinct r).toUInt8.toNat

/-- Compares a parsed header with a table row; returns the mismatching field names. -/
def compare (row : Row) (h : MainHeader) : List String :=
  let s := h.siz
  let chk (n : String) (b : Bool) : List String := if b then [] else [n]
  chk "img" ((s.xosiz.toNat, s.yosiz.toNat, s.xsiz.toNat, s.ysiz.toNat) == row.img) ++
  chk "tile" ((s.xtosiz.toNat, s.ytosiz.toNat, s.xtsiz.toNat, s.ytsiz.toNat) == row.tile) ++
  chk "csiz" (s.csiz == row.csiz) ++
  chk "comps" (s.components.toList.map compValues ==
    (expand row.comps).map fun c => [c.dx, c.dy, c.prec, c.sgnd]) ++
  chk "scod" (h.cod.scod.toNat == row.scod) ++
  chk "prg" (h.cod.progression.toUInt8.toNat == row.prg) ++
  chk "layers" (h.cod.layers.toNat == row.layers) ++
  chk "mct" ((if h.cod.mct then 1 else 0) == row.mct) ++
  chk "coding" ((List.range s.csiz).map (codingValues h) ==
    (expand row.coding).map fun c =>
      [c.csty, c.numres, c.cblkw, c.cblkh, c.cblksty, c.qmfbid, c.qntsty, c.numgbits,
       c.roishift] ++ c.precincts) ++
  chk "endPos" (h.endPos == row.endPos) ++
  -- OpenJPEG's index omits the parameterless markers 0xFF30–0xFF3F (p0_02 has an 0xFF30)
  chk "markers" ((h.markers.toList.filter (fun m => m.code < 0xFF30 || m.code > 0xFF3F)).map
    (fun m => (m.code.toNat, m.pos, m.len)) == row.markers)

/-- Directory of the T.803 streams (relative to the repository root). -/
def corpusDir : System.FilePath := "corpus/files/openjpeg-data/input/conformance"

/-- Parses every T.803 stream's main header and compares it with `table`; skips absent
files (reports how many were checked). -/
def corpus : IO Nat := do
  let mut f := 0
  let mut checked := 0
  for row in table do
    let p := corpusDir / row.file
    if !(← p.pathExists) then continue
    checked := checked + 1
    let data ← IO.FS.readBinFile p
    match parseMainHeader Limits.default (Reader.ofByteArray data) with
    | .error e => f := f + (← expect s!"{row.file}: {e}" false)
    | .ok (h, r) =>
      let bad := compare row h
      f := f + (← expect s!"{row.file}: mismatch in {bad}" bad.isEmpty)
      f := f + (← expect s!"{row.file}: reader at SOT" (r.pos == h.endPos))
  if checked == 0 then IO.println "  marker: corpus absent, skipped"
  else if checked < table.length then
    IO.println s!"  marker: {checked}/{table.length} corpus streams present"
  return f

/-! ## Hand-built segments -/

/-- Checks the outcome class of a parse. -/
def expectKind {α : Type} (name : String) (k : String) (x : Except Error α) : IO Nat :=
  expect s!"{name}: expected {k}, got {kind x}" (kind x == k)

-- A later malformed colour box is ignored, seven QCD exponent checks succeed, and
-- the final marker word fails. Check the constructions as well as the returned error.
private def diagnosticOrder : IO Nat := do
  let header := Tests.Box.ihdr 32 64 3 7 ++ Tests.Box.colrEnum 16 ++ Tests.Box.box "colr" []
  let main := be16 0xFF4F ++ seg 0xFF51 (sizN 3) ++ seg 0xFF52 codBody ++ seg 0xFF5C qcdBody
  let data := (Tests.Box.sig ++ Tests.Box.ftyp ++ Tests.Box.box "jp2h" header ++
    Tests.Box.box "jp2c" (main ++ be16 10)).toByteArray
  let trace := Spec.Resources.DiagnosticMarker.throughMainTrace Limits.default data
    (Nat.le_max_left ..) (Nat.le_max_right ..)
  let discarded := "colr shorter than 3 bytes"
  let exponent := "reserved bits in exponent byte 0x40"
  let returned := "expected a marker, found 0xa"
  let labels := (trace.messages.map (·.1)).filter ([discarded, exponent, returned].contains ·)
  let expected := Error.malformed (.atOffset .marker (data.size - 2)) returned
  let events ← expect "discarded colr and seven eager QCD checks before marker failure"
    (labels == [discarded] ++ List.replicate 7 exponent ++ [returned])
  let result ← expect "invalid marker retains its absolute JP2 offset"
    (Tests.Box.err? (decodeCodestream Limits.default data 0) == some expected &&
     Tests.Box.err? (JPEG2000.decode Limits.default data) == some expected)
  return events + result

/-- Unit tests of the segment parsers and the driver. -/
def units : IO Nat := do
  let mut f := 0
  let L := Limits.default
  let S := Limits.strict
  -- SIZ
  let siz := ok? (parseSIZ L (rd (sizBody 100 50 10 5 64 32 3 2
    [(0x87, 1, 2), (0x0B, 2, 1)])))
  f := f + (← expect "SIZ fields" (siz.map (fun s =>
    (s.xsiz, s.ysiz, s.xosiz, s.yosiz, s.xtsiz, s.ytsiz, s.xtosiz, s.ytosiz, s.csiz))
      == some (100, 50, 10, 5, 64, 32, 3, 2, 2)))
  f := f + (← expect "SIZ components" (siz.map (fun s => s.components.toList.map compValues)
      == some [[1, 2, 8, 1], [2, 1, 12, 0]]))
  f := f + (← expect "Ssiz recomputed" (siz.map (fun s => s.components.toList.map (·.ssiz))
      == some [0x87, 0x0B]))
  f := f + (← expectKind "SIZ Csiz 0" "malformed" (parseSIZ L (rd (sizN 0))))
  f := f + (← expectKind "SIZ trailing byte" "malformed" (parseSIZ L (rd (sizN 1 ++ [0]))))
  f := f + (← expectKind "SIZ missing component bytes" "malformed"
    (parseSIZ L (rd ((sizN 2).dropLast))))
  f := f + (← expectKind "SIZ truncated in fixed part" "truncated"
    (parseSIZ L (rd ((sizN 1).take 20))))
  f := f + (← expectKind "SIZ Csiz 5 > strict 4" "limit" (parseSIZ S (rd (sizN 5))))
  f := f + (← expectKind "SIZ Csiz 16385" "malformed"
    (parseSIZ L (rd (sizBody 64 32 0 0 64 32 0 0 [] |>.take 36 |> (· ++ be16 16385)))))
  f := f + (← expectKind "SIZ depth 38 ok" "ok"
    (parseSIZ L (rd (sizBody 64 32 0 0 64 32 0 0 [(37, 1, 1)]))))
  f := f + (← expectKind "SIZ depth 39" "malformed"
    (parseSIZ L (rd (sizBody 64 32 0 0 64 32 0 0 [(38, 1, 1)]))))
  f := f + (← expectKind "SIZ XRsiz 0" "malformed"
    (parseSIZ L (rd (sizBody 64 32 0 0 64 32 0 0 [(7, 0, 1)]))))
  f := f + (← expectKind "SIZ YRsiz 0" "malformed"
    (parseSIZ L (rd (sizBody 64 32 0 0 64 32 0 0 [(7, 1, 0)]))))
  f := f + (← expectKind "SIZ XOsiz = Xsiz" "malformed"
    (parseSIZ L (rd (sizBody 64 32 64 0 64 32 0 0 [(7, 1, 1)]))))
  f := f + (← expectKind "SIZ tile width 0" "malformed"
    (parseSIZ L (rd (sizBody 64 32 0 0 0 32 0 0 [(7, 1, 1)]))))
  f := f + (← expectKind "SIZ XTOsiz > XOsiz" "malformed"
    (parseSIZ L (rd (sizBody 64 32 4 0 64 32 5 0 [(7, 1, 1)]))))
  f := f + (← expectKind "SIZ first tile misses image" "malformed"
    (parseSIZ L (rd (sizBody 64 32 10 0 4 32 5 0 [(7, 1, 1)]))))
  -- COD
  let cod := ok? (parseCOD L (rd codBody))
  f := f + (← expect "COD fields" (cod.map (fun c =>
    (c.sop, c.eph, c.progression, c.layers, c.mct, c.style.levels, c.style.cbWidthExp,
     c.style.cbHeightExp, c.style.transform, c.style.precincts.isNone, c.scod))
      == some (false, false, .lrcp, 1, false, 2, 6, 6, .reversible53, true, 0)))
  let codP := [7, 4] ++ be16 300 ++ [1, 3, 3, 5, 0x3F, 0, 0x00, 0x11, 0x77, 0xF5]
  f := f + (← expect "COD with precincts, SOP, EPH, MCT" ((ok? (parseCOD L (rd codP))).map
    (fun c => (c.scod, c.progression, c.layers, c.mct, c.style.cbWidthExp, c.style.cbHeightExp,
      c.style.bypass, c.style.segSymbols, c.style.transform,
      c.style.precincts.map (·.toList.map Precinct.toUInt8)))
      == some (7, .cprl, 300, true, 5, 7, true, true, .irreversible97,
               some [0x00, 0x11, 0x77, 0xF5])))
  f := f + (← expectKind "COD missing precinct byte" "truncated"
    (parseCOD L (rd codP.dropLast)))
  f := f + (← expectKind "COD trailing byte" "malformed" (parseCOD L (rd (codBody ++ [0]))))
  f := f + (← expectKind "COD reserved Scod bit" "malformed"
    (parseCOD L (rd ([8] ++ codBody.drop 1))))
  f := f + (← expectKind "COD progression 5" "malformed"
    (parseCOD L (rd ([0, 5] ++ codBody.drop 2))))
  f := f + (← expectKind "COD 0 layers" "malformed"
    (parseCOD L (rd ([0, 0] ++ be16 0 ++ codBody.drop 4))))
  f := f + (← expectKind "COD 17 layers > strict 16" "limit"
    (parseCOD S (rd ([0, 0] ++ be16 17 ++ codBody.drop 4))))
  f := f + (← expectKind "COD MCT 2" "unsupported"
    (parseCOD L (rd ([0, 0] ++ be16 1 ++ [2] ++ codBody.drop 5))))
  let codWith (lv xcb ycb sty tr : UInt8) : List UInt8 := [0, 0] ++ be16 1 ++ [0, lv, xcb, ycb, sty, tr]
  f := f + (← expectKind "COD 32 levels ok" "ok" (parseCOD L (rd (codWith 32 4 4 0 1))))
  f := f + (← expectKind "COD 33 levels" "malformed" (parseCOD L (rd (codWith 33 4 4 0 1))))
  f := f + (← expectKind "COD 9 levels > strict 8" "limit" (parseCOD S (rd (codWith 9 4 4 0 1))))
  f := f + (← expectKind "COD xcb 9" "malformed" (parseCOD L (rd (codWith 2 9 0 0 1))))
  f := f + (← expectKind "COD xcb+ycb 9" "malformed" (parseCOD L (rd (codWith 2 5 4 0 1))))
  f := f + (← expectKind "COD xcb 8 ycb 0 ok" "ok" (parseCOD L (rd (codWith 2 8 0 0 1))))
  f := f + (← expectKind "COD HT bit" "unsupported" (parseCOD L (rd (codWith 2 4 4 0x40 1))))
  f := f + (← expectKind "COD style bit 7" "malformed" (parseCOD L (rd (codWith 2 4 4 0x80 1))))
  f := f + (← expectKind "COD transform 2" "unsupported" (parseCOD L (rd (codWith 2 4 4 0 2))))
  f := f + (← expectKind "COD PPx 0 above resolution 0" "malformed"
    (parseCOD L (rd ([1, 0] ++ be16 1 ++ [0, 1, 4, 4, 0, 1, 0x00, 0x10]))))
  -- COC
  f := f + (← expect "COC 1-byte index" ((ok? (parseCOC L 3 (rd ([2, 0] ++ codBody.drop 5)))).map
    (fun c => (c.component, c.style.levels)) == some (2, 2)))
  f := f + (← expect "COC 2-byte index (Csiz 300)"
    ((ok? (parseCOC L 300 (rd (be16 260 ++ [1, 1, 4, 4, 0, 0, 0x55, 0x66])))).map
      (fun c => (c.component, c.style.transform,
        c.style.precincts.map (·.toList.map Precinct.toUInt8)))
      == some (260, .irreversible97, some [0x55, 0x66])))
  f := f + (← expectKind "COC 1-byte form read with Csiz 300" "malformed"
    (parseCOC L 300 (rd ([2, 0] ++ codBody.drop 5))))
  f := f + (← expectKind "COC index ≥ Csiz" "malformed"
    (parseCOC L 3 (rd ([3, 0] ++ codBody.drop 5))))
  f := f + (← expectKind "COC reserved Scoc bit" "malformed"
    (parseCOC L 3 (rd ([0, 2] ++ codBody.drop 5))))
  -- QCD / QCC
  f := f + (← expect "QCD none" ((ok? (parseQCD (rd qcdBody))).map
    (fun q => (q.guardBits, q.sqcd, q.quant)) == some (2, 0x40, .none (List.replicate 7 8).toArray)))
  f := f + (← expect "QCD derived" ((ok? (parseQCD (rd ([0x21] ++ be16 0x4A12)))).map
    (fun q => (q.guardBits, q.sqcd, q.quant)) == some (1, 0x21, .derived ⟨9, 0x212⟩)))
  f := f + (← expect "QCD expounded" ((ok? (parseQCD (rd ([0x42] ++ be16 0x8801 ++ be16 0x07FF)))).map
    (fun q => (q.quant, match q.quant with
      | .expounded ss => ss.toList.map StepSize.toUInt16 | _ => []))
      == some (.expounded #[⟨17, 1⟩, ⟨0, 0x7FF⟩], [0x8801, 0x07FF])))
  f := f + (← expectKind "QCD derived, 2 values" "malformed"
    (parseQCD (rd ([0x21] ++ be16 1 ++ be16 2))))
  f := f + (← expectKind "QCD expounded odd length" "malformed"
    (parseQCD (rd ([0x02] ++ be16 1 ++ [3]))))
  f := f + (← expectKind "QCD none, no bands" "malformed" (parseQCD (rd [0x40])))
  f := f + (← expectKind "QCD none, 98 bands" "malformed"
    (parseQCD (rd ([0x40] ++ List.replicate 98 8))))
  f := f + (← expectKind "QCD style 3" "malformed" (parseQCD (rd ([0x03] ++ be16 1))))
  f := f + (← expectKind "QCD exponent low bits" "malformed" (parseQCD (rd [0x40, 0x41])))
  f := f + (← expectKind "QCD empty" "truncated" (parseQCD (rd [])))
  f := f + (← expect "QCC 2-byte index" ((ok? (parseQCC 300 (rd (be16 299 ++ qcdBody)))).map
    (·.component) == some 299))
  f := f + (← expectKind "QCC index ≥ Csiz" "malformed" (parseQCC 2 (rd ([2] ++ qcdBody))))
  -- RGN
  f := f + (← expect "RGN" ((ok? (parseRGN 3 (rd [1, 0, 7]))).map (fun g => (g.component, g.shift))
    == some (1, 7)))
  f := f + (← expect "RGN 2-byte index" ((ok? (parseRGN 1000 (rd (be16 999 ++ [0, 4])))).map
    (·.component) == some 999))
  f := f + (← expectKind "RGN Srgn 1" "unsupported" (parseRGN 3 (rd [1, 1, 7])))
  f := f + (← expectKind "RGN short" "truncated" (parseRGN 3 (rd [1, 0])))
  f := f + (← expectKind "RGN trailing" "malformed" (parseRGN 3 (rd [1, 0, 7, 0])))
  -- POC
  let poc1 : List UInt8 := [0, 0] ++ be16 5 ++ [3, 0, 2]
  f := f + (← expect "POC one entry, CEpoc 0 = 256" ((ok? (parsePOC L 3 (rd poc1))).map
    (fun p => p.entries.toList.map fun e =>
      (e.resStart, e.compStart, e.layerEnd, e.resEnd, e.compEndRaw, e.compEnd 3, e.order))
      == some [(0, 0, 5, 3, 0, 256, .rpcl)]))
  let poc2 : List UInt8 := [1] ++ be16 258 ++ be16 1 ++ [33] ++ be16 0 ++ [4]
  f := f + (← expect "POC 9-byte entries (Csiz 300), two entries" ((ok? (parsePOC L 300
    (rd (poc2 ++ poc2)))).map (fun p => p.entries.toList.map fun e =>
      (e.compStart, e.resEnd, e.compEnd 300, e.order))
      == some [(258, 33, 16384, .cprl), (258, 33, 16384, .cprl)]))
  f := f + (← expectKind "POC 7-byte entry with Csiz 300" "malformed" (parsePOC L 300 (rd poc1)))
  f := f + (← expectKind "POC empty" "malformed" (parsePOC L 3 (rd [])))
  f := f + (← expectKind "POC RSpoc = REpoc" "malformed"
    (parsePOC L 3 (rd ([3, 0] ++ be16 5 ++ [3, 0, 2]))))
  f := f + (← expectKind "POC REpoc 34" "malformed"
    (parsePOC L 3 (rd ([0, 0] ++ be16 5 ++ [34, 0, 2]))))
  f := f + (← expectKind "POC LYEpoc 0" "malformed"
    (parsePOC L 3 (rd ([0, 0] ++ be16 0 ++ [3, 0, 2]))))
  f := f + (← expectKind "POC CSpoc ≥ CEpoc" "malformed"
    (parsePOC L 3 (rd ([0, 2] ++ be16 1 ++ [3, 2, 2]))))
  f := f + (← expectKind "POC Ppoc 5" "malformed"
    (parsePOC L 3 (rd ([0, 0] ++ be16 1 ++ [3, 1, 5]))))
  f := f + (← expectKind "POC 33 entries > strict 32" "limit"
    (parsePOC S 3 (rd ((List.replicate 33 poc1).flatten))))
  -- COM, CRG
  f := f + (← expect "COM" ((ok? (parseCOM (rd ([0, 1] ++ "hi".toUTF8.toList)))).map
    (fun c => (c.rcom, c.data.toList)) == some (1, [104, 105])))
  f := f + (← expectKind "COM short" "truncated" (parseCOM (rd [0])))
  f := f + (← expect "CRG" ((ok? (parseCRG 2 (rd (be16 1 ++ be16 2 ++ be16 3 ++ be16 4)))).map
    (·.offsets.toList) == some [(1, 2), (3, 4)]))
  f := f + (← expectKind "CRG wrong length" "malformed" (parseCRG 2 (rd (be16 1 ++ be16 2))))
  -- driver
  let minimal := stream (sizN 1) (seg 0xFF52 codBody ++ seg 0xFF5C qcdBody)
  f := f + (← expect "main header minimal" (match mh minimal with
    | .ok (h, r) => h.endPos == 2 + 43 + 14 + 12 && r.pos == h.endPos &&
        h.markers.toList.map (fun m => (m.code.toNat, m.pos, m.len)) ==
          [(0xFF4F, 0, 2), (0xFF51, 2, 43), (0xFF52, 45, 14), (0xFF5C, 59, 12)] &&
        (ok? r.u16be).map (·.1) == some 0xFF90
    | .error _ => false))
  let rich := stream (sizN 300)
    (seg 0xFF5C qcdBody ++ seg 0xFF52 codBody ++ seg 0xFF53 (be16 299 ++ [0] ++ codBody.drop 5) ++
     seg 0xFF5D (be16 5 ++ qcdBody) ++ seg 0xFF5E (be16 7 ++ [0, 3]) ++
     seg 0xFF5F poc2 ++ seg 0xFF64 [0, 1, 65] ++ seg 0xFF63 (List.replicate 1200 0) ++
     seg 0xFF50 [1, 2, 3, 4] ++ seg 0xFF55 [0, 0] ++ seg 0xFF57 [1] ++ seg 0xFF60 [2] ++
     be16 0xFF30 ++ seg 0xFF70 [9, 9])
  f := f + (← expect "main header with every segment type (Csiz 300)" (match mh rich with
    | .ok (h, _) =>
      h.coc.toList.map (·.component) == [299] && h.qcc.toList.map (·.component) == [5] &&
      h.rgn.toList.map (·.component) == [7] && h.poc.size == 1 && h.com.size == 1 &&
      (h.crg.map (·.offsets.size)) == some 300 && (h.cap.map (·.length)) == some 4 &&
      h.pointers.toList.map (fun s => (s.code.toNat, s.length)) ==
        [(0xFF55, 2), (0xFF57, 1), (0xFF60, 1)] &&
      h.unknown.toList.map (fun s => (s.code.toNat, s.length)) == [(0xFF70, 2)] &&
      (h.cap.map (fun c => (c.bytes rich.toByteArray).toList)) == some [1, 2, 3, 4] &&
      h.markers.size == 16
    | .error _ => false))
  let hdr := seg 0xFF52 codBody ++ seg 0xFF5C qcdBody
  f := f + (← expectKind "no SOC" "malformed" (mh (minimal.drop 2)))
  f := f + (← expectKind "COD before SIZ" "malformed"
    (mh (be16 0xFF4F ++ seg 0xFF52 codBody ++ seg 0xFF51 (sizN 1))))
  f := f + (← expectKind "missing COD" "malformed"
    (mh (stream (sizN 1) (seg 0xFF5C qcdBody))))
  f := f + (← expectKind "missing QCD" "malformed"
    (mh (stream (sizN 1) (seg 0xFF52 codBody))))
  f := f + (← expectKind "second COD" "malformed"
    (mh (stream (sizN 1) (hdr ++ seg 0xFF52 codBody))))
  f := f + (← expectKind "second QCD" "malformed"
    (mh (stream (sizN 1) (hdr ++ seg 0xFF5C qcdBody))))
  f := f + (← expectKind "second SIZ" "malformed"
    (mh (stream (sizN 1) (hdr ++ seg 0xFF51 (sizN 1)))))
  f := f + (← expectKind "SOD in main header" "malformed"
    (mh (stream (sizN 1) (hdr ++ be16 0xFF93))))
  f := f + (← expectKind "PPT in main header" "malformed"
    (mh (stream (sizN 1) (hdr ++ seg 0xFF61 [0]))))
  f := f + (← expectKind "non-marker bytes" "malformed"
    (mh (stream (sizN 1) (hdr ++ [0x12, 0x34]))))
  f := f + (← expectKind "Lxxx 1" "malformed"
    (mh (stream (sizN 1) (hdr ++ be16 0xFF64 ++ be16 1))))
  f := f + (← expectKind "segment runs past the end" "truncated"
    (mh (be16 0xFF4F ++ seg 0xFF51 (sizN 1) ++ hdr ++ be16 0xFF64 ++ be16 40 ++ [0, 0])))
  f := f + (← expectKind "no SOT" "truncated" (mh (be16 0xFF4F ++ seg 0xFF51 (sizN 1) ++ hdr)))
  f := f + (← expectKind "bad Lsiz" "malformed"
    (mh (stream (sizN 1 ++ [0]) hdr)))
  f := f + (← expectKind "error inside a COC" "malformed"
    (mh (stream (sizN 1) (hdr ++ seg 0xFF53 ([1, 0] ++ codBody.drop 5)))))
  f := f + (← expectKind "POC entries over strict limit in total" "limit"
    (parseMainHeader { Limits.default with maxPocEntries := 1 }
      (rd (stream (sizN 3) (hdr ++ seg 0xFF5F poc1 ++ seg 0xFF5F poc1)))))
  f := f + (← expectKind "Csiz over strict limit" "limit"
    (parseMainHeader S (rd (stream (sizN 5) hdr))))
  return f

/-- Runs the suite; returns the number of failures. -/
def run : IO Nat := do
  return (← units) + (← diagnosticOrder) + (← corpus)

end JPEG2000.Tests.Marker
