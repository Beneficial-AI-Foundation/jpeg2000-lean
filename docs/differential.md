# Differential testing against an instrumented OpenJPEG

Milestones M3 and M4 (Plan.md) compare our Tier-2 and Tier-1 results with OpenJPEG code-block by
code-block: "every T.803 stream yields the same per-code-block segments as OpenJPEG" and
"code-blocks extracted from T.803 streams decode identically to OpenJPEG". OpenJPEG's public API
exposes neither, so we build a patched `opj_decompress` that writes them to a text file. This
document is the contract between that dump (task 4.6a) and our side (task 4.6b: a Lean exe that
writes the same format, and the diff script).

OpenJPEG is a **test-only tool**, not a dependency of the Lean libraries: no Lake dependency, and
nothing under `JPEG2000/`, `Spec/` or `Encode/` uses it.

## Building

```
scripts/build-opj-instrumented.sh            # prints the binary path on its last line
scripts/build-opj-instrumented.sh --force    # rebuild
```

* Source: OpenJPEG **v2.5.3**, commit `210a8a5690d0da66f02d49420d7176a21ef409dc` (the annotated
  tag's target), tarball `https://github.com/uclouvain/openjpeg/archive/<commit>.tar.gz`,
  SHA-256 `a7e669f502ad14d93f374a850113a2857447bfbfd389c8e278888053b0e3abcc` (hard-coded; the
  script refuses on mismatch).
* The tarball is downloaded into a fresh `mktemp -d` directory (deleted afterwards), extracted,
  patched with `patch -p1 < scripts/opj-instrument.patch`, configured with
  `cmake -DCMAKE_BUILD_TYPE=Release -DBUILD_SHARED_LIBS=OFF -DBUILD_CODEC=ON -DOPJ_USE_THREAD=OFF`
  and only the `opj_decompress` target is built.
* Installed as `.lake/opj-instrumented/bin/opj_decompress_dump` (`.lake/` is git-ignored). A stamp
  file `.lake/opj-instrumented/stamp` (commit, tarball hash, patch hash) makes reruns a no-op; a
  changed patch triggers a rebuild.
* Exits 0 with a "skipping" message when cmake, a C compiler (`$CC`, `cc`, `gcc`, `clang`),
  `patch`, curl/wget or a SHA-256 tool (`sha256sum`, else `shasum -a 256`) is missing. No
  GNU-only flags, so macOS works too. A build takes ~5 s on 8 cores.
* `OPJ_USE_THREAD=OFF` makes OpenJPEG's thread pool run every Tier-1 job synchronously, so the
  dump order is deterministic (two runs give byte-identical files). It is still not a sorted
  order — see "Order" below.

## Running

```
OPJ_DUMP_FILE=out.dump .lake/opj-instrumented/bin/opj_decompress_dump -i in.j2k -o tmp/x.pgx -quiet
```

* No `OPJ_DUMP_FILE` (or an empty value): no file is written, behaviour is stock OpenJPEG.
  Decoded images are byte-identical to the system `opj_decompress` 2.5.3 (checked on p0_04,
  p0_10, p0_13, p1_05).
* The file is created (truncated) on the first code-block, so a stream with no code-blocks
  leaves no file; treat a missing file as empty.
* `OPJ_DUMP_DATA_FULL=1` adds a `data` line after each `cb` line; `OPJ_DUMP_COEF_FULL=1` adds a
  `vals` line after each `coef` line (only the exact value `1` enables them).
* Always decode the whole image (no `-r`, `-l`, `-d`, `-t`): with reduced layers OpenJPEG's
  `real_num_segs`/`real_num_passes` differ from what the stream contains.
* `.pgx` output works for every corpus file (one file per component; p0_13 writes 257).

## Format (version 1)

Text, one record per line, `\n`-terminated, fields separated by single spaces, `key=value`
pairs in the fixed order shown. All integers are decimal; hashes are 16 lowercase hex digits.
Lists are comma-separated without spaces; an empty list is `-`.

The first line is `opjdump 1`.

### `cb` — Tier-2 result for one code-block (before Tier-1)

```
cb tile=T comp=C res=R band=B prec=P cblk=K x0=X0 y0=Y0 x1=X1 y1=Y1 sty=S Mb=M numbps=N zbp=Z passes=NP segs=NS len=L corrupt=0 seglens=l1,l2,.. segpasses=p1,p2,.. seghash=h1,h2,.. hash=H
```

| key | meaning |
|---|---|
| `tile` | tile index (`Isot`, raster over the tile grid) |
| `comp` | component index |
| `res` | resolution level r, 0 = lowest (the NL LL band), up to NL |
| `band` | OpenJPEG band number: 0 = LL (only at `res=0`), 1 = HL, 2 = LH, 3 = HH |
| `prec` | precinct index within the resolution level, raster over the resolution's precinct grid (B.6) |
| `cblk` | code-block index within the precinct's band part, raster over its code-block grid (B.7) |
| `x0 y0 x1 y1` | code-block rectangle in **band coordinates** (B-15, `tbx0`… scale), half-open, clipped to the precinct's part of the band; width `x1−x0`, height `y1−y0` |
| `sty` | code-block style byte `SPcod`/`SPcoc` (Table A.19: 1 bypass, 2 reset, 4 termall, 8 vertically causal, 16 pterm, 32 segsym); decimal |
| `Mb` | Mb of equation E-2: `G + εb − 1` (OpenJPEG `band->numbps`), from the QCD/QCC of this tile-component |
| `numbps` | OpenJPEG `cblk->numbps = Mb − zbp` = number of magnitude bit-planes coded for this block (Tier-1 starts at bit-plane `numbps − 1`, plus the ROI shift, see `coef`); `-` if the code-block was never included |
| `zbp` | **T.800 zero bit-planes** (B.10.5 tag tree value) = `Mb − numbps`; `-` if never included |
| `passes` | total coding passes over all layers |
| `segs` | number of codeword segments |
| `len` | total data bytes over all segments (sum of the chunks OpenJPEG collected) |
| `corrupt` | 1 if OpenJPEG flagged the block's data as corrupted (then it decodes it as all zero) |
| `seglens` | byte length of each codeword segment, in order |
| `segpasses` | number of coding passes in each segment, in order (= `segmentPasses` in our Tier-2) |
| `seghash` | FNV-1a 64 of each segment's bytes |
| `hash` | FNV-1a 64 of all segment bytes concatenated in segment order (= of the `data` line) |

A code-block that is never included has `numbps=- zbp=- passes=0 segs=0 len=0 seglens=-
segpasses=- seghash=- hash=cbf29ce484222325` (the FNV offset basis = hash of no bytes).

Segment `i`'s bytes are bytes `[l1+…+l(i−1), l1+…+li)` of the concatenated data; across layers
and tile-parts they are the per-packet contributions in packet order (our `Segment.bytes`).
In every corpus run `Σ seglens = len` and `Σ segpasses = passes`.

`data` line (only with `OPJ_DUMP_DATA_FULL=1`): `data <hex of all bytes>` (lowercase, no
separators), or `data -` when `len=0`.

### `coef` — Tier-1 result for one code-block

```
coef tile=T comp=C res=R band=B prec=P cblk=K w=W h=H roi=S nz=N hash=H
```

`tile … cblk` as in `cb`; `w = x1−x0`, `h = y1−y0`; `roi` = the component's ROI shift `SPrgn`
(0 without RGN); `nz` = number of non-zero coefficients; `hash` = FNV-1a 64 over the `w·h`
values in raster order (row by row, `y` outer, `x` inner), each as a 4-byte **little-endian
two's-complement int32**.

`vals` line (only with `OPJ_DUMP_COEF_FULL=1`): `vals v0 v1 … v(w·h−1)` in the same order,
signed decimal.

### Values: what exactly is dumped

The dumped value of a coefficient is the **T.800 Annex D sign·magnitude at the 2^p scale with no
reconstruction offset**, i.e. exactly `Spec.Tier1.Coeff.value` (bit-plane `p` adds `2^p`;
`0` if the coefficient never became significant). It is taken right after OpenJPEG's Tier-1
(`opj_t1_decode_cblk`), **before** OpenJPEG's ROI descaling (`roishift`) and before
dequantisation / the reversible `/2`.

Transformation applied (`opj_dump_t800` in the patch). OpenJPEG decodes bit-plane `p` with
`bpno_plus_one = p + 1` and works at twice the scale with a midpoint:
* significance at plane `p` stores `±(2^(p+1) | 2^p) = ±3·2^p` (`oneplushalf`);
* a refinement bit at plane `p` adds `±2^p` (`poshalf`) towards larger magnitude for bit 1 and
  smaller for bit 0.

By induction `|v| = 2·m + 2^L`, where `m` is the T.800 magnitude and `L` the lowest bit-plane
decoded for this coefficient. All bits of `2·m` lie at positions `≥ L+1`, so `2^L` is the lowest
set bit of `|v|`, and

```
m = (|v| & (|v| − 1)) >> 1,   dumped value = sign(v) · m
```

is exact (no rounding), for every truncation point. Checked against a simulation of OpenJPEG's
update rules on 200 000 random bit sequences (all agree). Note the bit-plane count: Tier-1 runs
`numbps + roi` bit-planes (OpenJPEG `bpno_plus_one = roishift + numbps`, refused if `≥ 31`), so
for RGN streams (p0_03 and p0_15 `roi=7`, p0_06 `roi=9`, p0_13 `roi=11`; only the components
carrying an RGN marker) the values are still scaled up
by the ROI shift (Annex H) and the Lean side must compare against its Tier-1 output before its own
ROI step.

HT (Part 15) code-blocks get a `cb` line but no `coef` line (none in the corpus).

### Which code-blocks, and order

* Exactly the code-blocks OpenJPEG iterates in `opj_t1_decode_cblks` (every precinct × its
  `cw × ch` code-block grid) **with non-zero area** (`x1 > x0` and `y1 > y0`), decoded at full
  resolution. Our side must emit the same set: every non-empty code-block of every precinct.
* Each `cb` line is followed by its `coef` line (with `data`/`vals` lines interleaved when
  enabled). Within a tile the order is comp, res, band, prec, cblk (lexicographic).
* **Tiles appear in OpenJPEG's decode order, not index order** (p0_10: 0, 1, 3, 2; p0_07 does not
  start at tile 0). The diff script must key records by `(tile, comp, res, band, prec, cblk)`
  rather than compare line by line.

### FNV-1a 64

`h := 0xcbf29ce484222325; for each byte b: h := (h XOR b) * 0x100000001b3 mod 2^64`. Lean:
`bs.foldl (fun h b => (h ^^^ b.toUInt64) * 0x100000001b3) 0xcbf29ce484222325` on `UInt64`.
(FNV is a checksum, not a cryptographic hash; with `OPJ_DUMP_*_FULL=1` full bytes/values are
available when a hash mismatch needs explaining.)

## Corpus run (4.6a, all 32 files decode with exit 0)

| file | lines | cb (= coef) | included | | file | lines | cb (= coef) | included |
|---|---|---|---|---|---|---|---|---|
| p0_01 | 21 | 10 | 10 | | p1_01 | 27 | 13 | 13 |
| p0_02 | 27 | 13 | 13 | | p1_02 | 565 | 282 | 280 |
| p0_03 | 33 | 16 | 16 | | p1_03 | 5151 | 2575 | 2534 |
| p0_04 | 565 | 282 | 280 | | p1_04 | 1281 | 640 | 618 |
| p0_05 | 5151 | 2575 | 2534 | | p1_05 | 69637 | 34818 | 7485 |
| p0_06 | 245 | 122 | 101 | | p1_06 | 505 | 252 | 180 |
| p0_07 | 15361 | 7680 | 7680 | | p1_07 | 97 | 48 | 30 |
| p0_08 | 5047 | 2523 | 2523 | | file1.jp2 | 619 | 309 | 309 |
| p0_09 | 33 | 16 | 14 | | file2.jp2 | 547 | 273 | 273 |
| p0_10 | 241 | 120 | 120 | | file3.jp2 | 319 | 159 | 159 |
| p0_11 | 5 | 2 | 2 | | file4.jp2 | 207 | 103 | 103 |
| p0_12 | 17 | 8 | 8 | | file5.jp2 | 619 | 309 | 309 |
| p0_13 | 515 | 257 | 256 | | file6.jp2 | 207 | 103 | 103 |
| p0_14 | 97 | 48 | 42 | | file7.jp2 | 547 | 273 | 273 |
| p0_15 | 33 | 16 | 16 | | file8.jp2 | 207 | 103 | 103 |
| p0_16 | 21 | 10 | 10 | | file9.jp2 | 207 | 103 | 103 |

(`lines` includes the `opjdump 1` header; "included" = `cb` lines with `numbps` ≠ `-`.)
Styles seen: `sty` ∈ {0, 4, 5, 10, 16, 25, 32, 40, 52}. p0_10 prints OpenJPEG's
"color_sycc_to_rgb CAN NOT CONVERT" on stderr (an output colour-conversion message, same with the
stock binary).
