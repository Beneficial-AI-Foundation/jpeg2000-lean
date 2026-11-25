import JPEG2000.Image
import Tests.Decode

/-!
# `image-dump`: decoded planes as PGX files (task 6.3b)

Plan.md §8.2 (differential testing against OpenJPEG), §8.3 (PDF corpus), §9 (consumer API).
T.800 Annex B (component geometry), Annex I (JP2 colour handling, via `JPEG2000.decode`).

`lake exe image-dump <in.jpx|.jp2|.j2k> <outprefix> [reduce]` decodes the file with
`JPEG2000.decode Limits.default` (default `DecodeOptions`, discarding `reduce` resolution levels,
as `opj_decompress -r`) and writes

* `<outprefix>_raw_<k>.pgx` — codestream component `k` on its own grid, as
  `decodeCodestream` produced it (before palette, colour conversion, up-sampling);
* `<outprefix>_img_<k>.pgx` — output channel `k` of the `Image` at the image size: the colour
  channels in colour order, then the opacity channel, then the other channels.

and prints one line per plane plus the colour facts, for `scripts/diff-images.py`:

```
space <ColourSpace after conversion>   icc <bytes|none>   declared <ColourSpace of the file>
sycc_converted <true|false>   (declared sYCC, or OpenJPEG's heuristic on a space-less stream)
raw <k> <w> <h> <depth> <signed> <reversible>
img <k> <colour|alpha|other> <w> <h> <depth> <signed>
```

If `decode` fails but `decodeCodestream` succeeds, the raw planes are still written and the
line `error image <message>` is printed (exit 0); if the codestream itself fails,
`error decode <message>` and exit 1. PGX files are big-endian (`PG ML ±d w h`), 1, 2 or 4
bytes per sample, as OpenJPEG writes them.
-/

namespace JPEG2000.Tests.ImageDump

open JPEG2000 JPEG2000.Bytes

/-- PGX bytes of a `w × h` plane with the given depth and sign (two's complement storage). -/
def pgx (w h depth : Nat) (signed : Bool) (p : Plane) : ByteArray := Id.run do
  let bps := if depth ≤ 8 then 1 else if depth ≤ 16 then 2 else 4
  let hdr := s!"PG ML {if signed then "-" else "+"}{depth} {w} {h}\n"
  let mut out := ByteArray.emptyWithCapacity (hdr.utf8ByteSize + w * h * bps)
  out := out.append hdr.toUTF8
  for i in [0:w * h] do
    let v : UInt32 := ((p.get? i).getD 0).toUInt32
    if bps == 4 then out := out.push (v >>> 24).toUInt8 |>.push (v >>> 16).toUInt8
    if bps ≥ 2 then out := out.push (v >>> 8).toUInt8
    out := out.push v.toUInt8
  return out

/-- Writes the raw codestream components; returns the description lines. -/
def dumpRaw (d : DecodedImage) (pre : String) : IO (Array String) := do
  let mut lines := #[]
  for k in [0:d.comps.size] do
    let c := d.comps[k]!
    IO.FS.writeBinFile s!"{pre}_raw_{k}.pgx" (pgx c.width c.height c.depth c.signed c.plane)
    let rev := JPEG2000.Tests.Decode.reversibleComp d.header k
    lines := lines.push s!"raw {k} {c.width} {c.height} {c.depth} {c.signed} {rev}"
  return lines

/-- Short form of a colour space. -/
def spaceName : Color.ColourSpace → String
  | .sRGB => "sRGB"
  | .greyscale => "greyscale"
  | .sYCC => "sYCC"
  | .enumerated cs _ => s!"enumerated-{cs}"
  | .icc _ => "icc"
  | .unknown => "unknown"

/-- Writes the image channels; returns the description lines. -/
def dumpImage (img : Image) (pre : String) : IO (Array String) := do
  let chans : Array (String × JPEG2000.Channel) :=
    img.channels.map (("colour", ·)) ++ (img.alpha.toArray.map (("alpha", ·))) ++
      img.other.map (("other", ·))
  let mut lines := #[]
  for k in [0:chans.size] do
    let (role, c) : String × JPEG2000.Channel := chans[k]!
    IO.FS.writeBinFile s!"{pre}_img_{k}.pgx" (pgx img.width img.height c.depth c.signed c.plane)
    lines := lines.push s!"img {k} {role} {img.width} {img.height} {c.depth} {c.signed}"
  return lines

/-- Decodes `path` at resolution reduction `r` and writes the PGX files under `pre`. -/
def run (path pre : String) (r : Nat) : IO UInt32 := do
  let data ← IO.FS.readBinFile path
  match JPEG2000.decode Limits.default data { reduce := r } with
  | .ok img =>
    let hdr? := img.decoded.header.container.bind (·.header)
    let declared := (hdr?.map Color.resolveColourSpace).getD .unknown
    let sycc := declared == .sYCC || (declared == .unknown && Image.looksSycc img.decoded.comps)
    IO.println s!"space {spaceName img.space}"
    IO.println s!"icc {(img.iccProfile.map (·.size.repr)).getD "none"}"
    IO.println s!"declared {spaceName declared}"
    IO.println s!"sycc_converted {sycc}"
    for l in ← dumpRaw img.decoded pre do IO.println l
    for l in ← dumpImage img pre do IO.println l
    return 0
  | .error e =>
    match JPEG2000.decodeCodestream Limits.default data r with
    | .ok d =>
      for l in ← dumpRaw d pre do IO.println l
      IO.println s!"error image {e}"
      return 0
    | .error e2 =>
      IO.println s!"error decode {e2}"
      return 1

/-- `image-dump <file> <outprefix> [reduce]`. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | [path, pre] => run path pre 0
  | [path, pre, r] =>
    match r.toNat? with
    | some r => run path pre r
    | none => IO.eprintln s!"image-dump: bad reduce {r}"; return 2
  | _ =>
    IO.eprintln "usage: image-dump <file.jpx|file.jp2|file.j2k> <outprefix> [reduce]"
    return 2

end JPEG2000.Tests.ImageDump

/-- Entry point of `lake exe image-dump`. -/
def main (args : List String) : IO UInt32 := JPEG2000.Tests.ImageDump.main args
