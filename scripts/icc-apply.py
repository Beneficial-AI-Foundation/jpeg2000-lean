#!/usr/bin/env python3
"""Apply an ICC profile to raw interleaved samples with lcms2's `tificc` (task 6.3a).

Test-only colour management (Plan.md section 1: the library passes ICC profiles through and
never applies them).  The JP2 conformance harness (`Tests/JP2.lean`) uses this to reproduce
what OpenJPEG's `opj_decompress` does with a `colr` METH 2 profile
(`color_apply_icc_profile` in `src/bin/common/color.c` at uclouvain/openjpeg@8314119):

    cmsCreateTransform(<embedded profile>, TYPE_{RGB,GRAY}_{8,16},
                       cmsCreate_sRGBProfile(), TYPE_RGB_{8,16},
                       <rendering intent of the profile header>, 0)

i.e. embedded profile -> lcms2's built-in sRGB, at the header's rendering intent, default
(precalculated) optimisation, 8-bit when the precision is <= 8 and 16-bit otherwise; a grey
profile yields RGB.  `tificc -i<profile> -o*sRGB -t<intent> -w<bits>` builds the same
transform (its default `-c1` adds no flags).

Usage (run from anywhere; paths are arguments):

    python3 -I scripts/icc-apply.py --check
    python3 -I scripts/icc-apply.py --profile P.icc --width W --height H --channels 1|3 \
        --bits 8|16 [--intent N] IN.raw OUT.raw

IN.raw holds W*H*channels samples, interleaved, 1 byte each (8 bits) or 2 bytes big-endian
(16 bits).  OUT.raw receives W*H*3 samples (RGB) in the same format.  The intent defaults to
the profile header's (bytes 64..67).

Exit status: 0 success; 1 failure (tificc error, malformed output); 2 bad usage; 3 skipped
because `tificc` (Debian/Ubuntu package `liblcms2-utils`) is not on PATH.

Python standard library only; the TIFF files are written and read here (uncompressed,
single strip in, any strips out).
"""
import argparse
import os
import shutil
import struct
import subprocess
import sys
import tempfile

SKIP = 3


def write_tiff(path, width, height, channels, bits, data):
    """Writes a big-endian, uncompressed, single-strip TIFF of the raw samples."""
    photometric = 2 if channels == 3 else 1
    n_tags = 10
    ifd_off = 8
    ifd_size = 2 + 12 * n_tags + 4
    bps_off = ifd_off + ifd_size
    data_off = bps_off + (2 * channels if channels > 2 else 0)
    if channels > 2:
        bps_field = (3, channels, bps_off)
    else:
        bps_field = (3, 1, bits)  # one short, stored in the value field

    def tag(code, typ, count, value):
        if typ == 3 and count == 1:
            return struct.pack(">HHIHH", code, typ, count, value, 0)
        return struct.pack(">HHII", code, typ, count, value)

    tags = [
        tag(256, 4, 1, width),
        tag(257, 4, 1, height),
        tag(258, *bps_field),
        tag(259, 3, 1, 1),
        tag(262, 3, 1, photometric),
        tag(273, 4, 1, data_off),
        tag(277, 3, 1, channels),
        tag(278, 4, 1, height),
        tag(279, 4, 1, len(data)),
        tag(284, 3, 1, 1),
    ]
    with open(path, "wb") as f:
        f.write(b"MM" + struct.pack(">HI", 42, ifd_off))
        f.write(struct.pack(">H", n_tags) + b"".join(tags) + struct.pack(">I", 0))
        if channels > 2:
            f.write(struct.pack(">" + "H" * channels, *([bits] * channels)))
        f.write(data)


TYPE_SIZE = {1: 1, 2: 1, 3: 2, 4: 4, 16: 8}


def read_tiff(path):
    """Reads an uncompressed, chunky TIFF; returns (width, height, channels, bits, raw
    big-endian samples)."""
    with open(path, "rb") as f:
        d = f.read()
    if d[:2] == b"II":
        e = "<"
    elif d[:2] == b"MM":
        e = ">"
    else:
        raise ValueError("not a TIFF")
    (off,) = struct.unpack(e + "I", d[4:8])
    (n,) = struct.unpack(e + "H", d[off:off + 2])
    tags = {}
    for k in range(n):
        p = off + 2 + 12 * k
        code, typ, count = struct.unpack(e + "HHI", d[p:p + 8])
        size = TYPE_SIZE.get(typ, 1) * count
        vp = p + 8 if size <= 4 else struct.unpack(e + "I", d[p + 8:p + 12])[0]
        if typ == 3:
            vals = struct.unpack(e + "H" * count, d[vp:vp + 2 * count])
        elif typ in (4, 16):
            ch = "I" if typ == 4 else "Q"
            vals = struct.unpack(e + ch * count, d[vp:vp + TYPE_SIZE[typ] * count])
        else:
            vals = tuple(d[vp:vp + count])
        tags[code] = vals
    width, height = tags[256][0], tags[257][0]
    channels = tags.get(277, (1,))[0]
    bits = tags.get(258, (1,))[0]
    if tags.get(259, (1,))[0] != 1:
        raise ValueError("compressed output TIFF (compression %d)" % tags[259][0])
    if channels > 1 and tags.get(284, (1,))[0] != 1:
        raise ValueError("planar output TIFF")
    raw = b"".join(d[o:o + c] for o, c in zip(tags[273], tags[279]))
    need = width * height * channels * (bits // 8)
    if len(raw) < need:
        raise ValueError("short output TIFF data")
    raw = raw[:need]
    if bits == 16 and e == "<":
        raw = b"".join(raw[i + 1:i + 2] + raw[i:i + 1] for i in range(0, len(raw), 2))
    return width, height, channels, bits, raw


def header_intent(profile):
    """The rendering intent of an ICC profile header (bytes 64..67), 0 if absent."""
    with open(profile, "rb") as f:
        h = f.read(68)
    return struct.unpack(">I", h[64:68])[0] if len(h) >= 68 else 0


def main(argv):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--check", action="store_true", help="exit 0 if tificc is available")
    ap.add_argument("--profile")
    ap.add_argument("--width", type=int)
    ap.add_argument("--height", type=int)
    ap.add_argument("--channels", type=int, choices=(1, 3))
    ap.add_argument("--bits", type=int, choices=(8, 16))
    ap.add_argument("--intent", type=int)
    ap.add_argument("input", nargs="?")
    ap.add_argument("output", nargs="?")
    a = ap.parse_args(argv)
    tificc = shutil.which("tificc")
    if tificc is None:
        print("SKIP: tificc not found (apt install liblcms2-utils)")
        return SKIP
    if a.check:
        print("tificc: " + tificc)
        return 0
    if None in (a.profile, a.width, a.height, a.channels, a.bits, a.input, a.output):
        ap.print_usage(sys.stderr)
        return 2
    with open(a.input, "rb") as f:
        data = f.read()
    expect = a.width * a.height * a.channels * (a.bits // 8)
    if len(data) != expect:
        print("input has %d bytes, expected %d" % (len(data), expect), file=sys.stderr)
        return 2
    intent = header_intent(a.profile) if a.intent is None else a.intent
    with tempfile.TemporaryDirectory(prefix="icc-apply-") as tmp:
        src = os.path.join(tmp, "in.tif")
        dst = os.path.join(tmp, "out.tif")
        write_tiff(src, a.width, a.height, a.channels, a.bits, data)
        cmd = [tificc, "-i" + os.path.abspath(a.profile), "-o*sRGB", "-t%d" % intent,
               "-w%d" % a.bits, src, dst]
        r = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        if r.returncode != 0 or not os.path.exists(dst):
            sys.stderr.write("tificc failed (%d): %s\n" % (r.returncode, r.stdout.decode(errors="replace")))
            return 1
        try:
            w, h, c, b, raw = read_tiff(dst)
        except (ValueError, KeyError, struct.error) as ex:
            print("bad tificc output: %s" % ex, file=sys.stderr)
            return 1
    if (w, h, c, b) != (a.width, a.height, 3, a.bits):
        print("unexpected tificc output %dx%d, %d channels, %d bits" % (w, h, c, b), file=sys.stderr)
        return 1
    with open(a.output, "wb") as f:
        f.write(raw)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
