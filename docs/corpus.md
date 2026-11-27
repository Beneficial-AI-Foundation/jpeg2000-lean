# Test corpus

Plan.md §8.1 (conformance), §8.4 (benchmark set); §10 open question "Licensing of
conformance files"; §11 risk "Conformance data licence".

## What is committed

Only `corpus/manifest.json`. Every file it lists is downloaded into the git-ignored
`corpus/files/<path>` and verified by size and SHA-256. Nothing downloaded is committed
(see "Licence" below).

## Fetching

```
python3 -I scripts/fetch-corpus.py                  # download missing/wrong files, verify all
python3 -I scripts/fetch-corpus.py --check          # verify only, no network; exit 1 on any failure
python3 -I scripts/fetch-corpus.py --role benchmark # restrict to a role (repeatable)
python3 -I scripts/fetch-corpus.py --only p0_0      # restrict to paths containing TEXT (repeatable)
python3 -I scripts/fetch-corpus.py --check --root DIR   # verify a copy somewhere else
python3 -I scripts/fetch-corpus.py --list [--role R]    # list entries, no I/O on files
```

Standard library only. Paths resolve from the script's location, not the current directory.
A download goes to `<target>.part`, is rejected and deleted if it is larger than the
manifest size or its SHA-256 differs, and is only then renamed into place. In fetch mode a
present file with the wrong size or hash is reported, deleted and fetched again; `--check`
never touches the network or the files. Manifest paths with `..`, empty or absolute
components are refused, and URLs must start with `https://raw.githubusercontent.com/`.
`urllib` honours `HTTPS_PROXY`. The last line is always
`<mode>: N files verified (B bytes) under <dir>; F fetched; K failed`. A second run with
everything present makes no network requests.

## Source

All files come from [uclouvain/openjpeg-data](https://github.com/uclouvain/openjpeg-data)
at the pinned commit `39524bd3a601d90ed8e0177559400d23945f96a9` (2024-11-13, "Update
expected files for openjpeg PR 1559"), fetched as
`https://raw.githubusercontent.com/uclouvain/openjpeg-data/<sha>/<path>`. The repository is
large (about 400 MB) and is not cloned. When the manifest was built, each download was also
checked against the git blob SHA-1 in the tree listing of that commit (recorded as
`git_blob_sha1`).

Thresholds come from OpenJPEG's own test suite,
[uclouvain/openjpeg](https://github.com/uclouvain/openjpeg) at commit
`8314119b067c0fc77834731168daaebd379fdb12`, file `tests/conformance/CMakeLists.txt`,
which cites T.803 Tables C.1/C.4 (class 0), C.6/C.7 (class 1) and G.1 (JP2).

## Manifest format (`version: 1`)

Top level: `description`; `sources.openjpeg-data` (`repository`, `commit`, `commit_date`,
`url_prefix`, `licence.conformance`, `licence.nonregression`); `thresholds_source`
(`repository`, `commit`, `file`, `note`); `files`.

Each entry of `files`:

| field | meaning |
|---|---|
| `path` | relative to `corpus/files/`; mirrors the source path: `openjpeg-data/<repo path>` |
| `url` | raw URL at the pinned commit |
| `sha256`, `size` | what the fetcher verifies |
| `git_blob_sha1` | the blob id in the pinned tree (provenance; not checked by the fetcher) |
| `roles` | one or more of `conformance-stream`, `reference-decode`, `jp2`, `benchmark`, `notice` |
| `licence` | key into `sources.openjpeg-data.licence` (`conformance` or `nonregression`) |
| `profile`, `test` | conformance streams: profile 0/1, test name `p0_01`… |
| `components_compared` | conformance streams: how many components OpenJPEG compares (`CP0_nbC_list`/`CP1_nbC_list`; p0_13 has 257 components, only 4 are compared) |
| `codestream` | streams: main-header SIZ/COD summary (size, components, bit depths, signedness, subsampling, tile count, layers, levels, progression, code-block size, code-block style, wavelet, MCT, Rsiz). Main header only: tile-part COD/COC/QCD overrides are not reflected |
| `jp2_boxes` | JP2 files: `colr` method/enumeration and presence of `pclr`/`cdef`/`cmap`/`res` |
| `stream` | reference decodes: the `path` of the stream they belong to |
| `class`, `component`, `reduce` | reference decodes: T.803 class, component index, resolution reduction (opj `-r`) at which the reference is produced |
| `thresholds` | `peak` (maximum absolute sample error), `mse` (mean squared error), `source`; JP2 refs add `per_component: true` |
| `note` | free text (benchmark entries) |

## Contents (132 files, 82,875,894 bytes)

| role | files | notes |
|---|---|---|
| `conformance-stream` | 23 | T.803 profile 0 `p0_01`…`p0_16`, profile 1 `p1_01`…`p1_07` (`input/conformance`) |
| `reference-decode` | 87 | 18 class-0 profile-0 (`c0p0_*`, incl. `03r0/r1`, `15r0/r1`), 8 class-0 profile-1 (`c0p1_*`, incl. `04r0/r3`), 35 class-1 profile-0 (`c1p0_NN_K`, one per component), 17 class-1 profile-1 (`c1p1_NN_K`), 9 JP2 TIFFs `jp2_1…9.tif` |
| `jp2` | 9 | T.803 JP2 file-format tests `file1.jp2`…`file9.jp2` |
| `benchmark` | 15 | 4 of them also in the conformance directory (see below) |
| `notice` | 1 | `input/conformance/COPYRIGHT` (fetched so every local copy carries the notice) |

Class-1 references are full-resolution per-component PGX files compared on all
`components_compared` components; class-0 references are the first component only, at the
`reduce` factor. Notes from the data: `p0_03` and `p0_15` are byte-identical (T.803 erratum,
recorded in `input/conformance/VERSION.txt`); `c1p0_08_*` is at `reduce 1`; class-0 profile-1
`p1_05`/`p1_06` have `peak 128, mse 16384`, effectively unchecked. The class-0 thresholds
come from a block that is **commented out** in OpenJPEG (it only runs class 1), so they are
transcribed but untested upstream; JP2 tolerances are peak 4 / MSE 1 per RGB component after
8-bit RGB conversion (`-p 8S -force-rgb`). Thresholds were taken from OpenJPEG, not from the
T.803 text itself, which was not consulted.

Not included: the Kakadu-supplied `a*_mono.j2c`…`g*_colr.j2c` streams, the Richter
`subsampling_*`/`zoo2` files and their PPM references in `input/conformance`; OpenJPEG's own
non-regression baselines (`baseline/nonregression/opj_*`, `opj_dump` outputs); and the
remaining ~250 `input/nonregression` files (crash reproducers, encoder inputs). Add them
when the differential (§8.2), adversarial (§8.7) or fuzzing (§8.6) work needs them.

## Benchmark set (Plan §8.4)

Every stream here decodes in OpenJPEG's own test suite (none is a `!opj_decompress`
expected-failure case in `tests/nonregression/test_suite.ctest.in` at the commit above).

| file | size | Mpx | comps | bits | wavelet | tiles | layers | prog |
|---|---|---|---|---|---|---|---|---|
| conformance `zoo1.jp2` | 3906x2602 | 10.16 | 3 (2x2 chroma) | 8 | 9-7 | 1 | 6 | LRCP |
| `Bretagne2.j2k` | 2592x1944 | 5.04 | 3 | 8 | 5-3 | 25 | 3 | LRCP |
| conformance `p0_07.j2k` | 2048x2048 | 4.19 | 3 | 12 signed | 5-3 | 256 | 8 | RLCP |
| `123.j2c` | 1800x1800 | 3.24 | 1 | 16 | 5-3 (11 levels) | 1 | 1 | LRCP |
| `kodak_2layers_lrcp.j2c` | 2048x1556 | 3.19 | 3 | 12 | 9-7 | 1 | 2 | LRCP |
| `movie_00000.j2k` | 1920x1080 | 2.07 | 3 | 8 | 5-3 (rate-truncated) | 1 | 1 | LRCP |
| `_00042.j2k` | 1920x1080 | 2.07 | 3 | 12 | 9-7 (DCI 2K, Rsiz 3) | 1 | 1 | CPRL |
| conformance `p0_08.j2k` | 513x3072 | 1.58 | 3 | 12 signed | 5-3 | 1 | 30 | CPRL |
| conformance `p1_03.j2k` | 1024x1024 | 1.05 | 4 | 8 | 9-7 | 1 | 10 | PCRL |
| `test_lossless.j2k` | 1024x1024 | 1.05 | 1 | 12 | 5-3 | 1 | 1 | LRCP |
| `issue208.jp2` | 842x1249 | 1.05 | 4 (CMYK) | 8 | 9-7 | 20 | 1 | RLCP |
| `pacs.ge.j2k` | 512x512 | 0.26 | 1 | 16 signed | 5-3 | 1 | 16 | LRCP |
| `buxI.j2k` | 512x512 | 0.26 | 1 | 16 | 9-7 | 1 | 2 | LRCP |
| `issue559-eci-090-CIELab.jp2` | 424x212 | 0.09 | 3 (CIELab) | 16 | 9-7 | 8 | 6 | RLCP |
| `cthead1.j2k` | 256x256 | 0.07 | 1 | 8 | 5-3 | 1 | 1 | LRCP |

Covered: reversible 5-3 and irreversible 9-7; 8, 12 and 16 bit (signed and unsigned); 1, 3
and 4 components; single tile and 8-256 tiles; 1 to 30 layers; progression orders LRCP, RLCP, PCRL and CPRL;
raw codestreams and JP2; 0.07 to 10.2 Mpx.

**Not covered (do not assume otherwise):**

* **Large images (≥ 20 Mpx)**: the largest stream that OpenJPEG's suite decodes is `zoo1.jp2`
  at 10.2 Mpx. The only bigger ones in openjpeg-data (`issue391.jp2` 15.4 Mpx,
  `issue420.jp2` 18.7 Mpx, `issue432.jp2` with a bogus 2.3 Gpx header) are expected-failure
  crash reproducers. A ≥ 20 Mpx stream must come from elsewhere (e.g. encoded with
  `opj_compress` from a large raw image, or from the PDF corpus, §8.3).
* RPCL progression in the benchmark set (it occurs in conformance `p0_06`, `p1_07`).
* "Lossless" is not verified: the `wavelet` column is the COD transform; reversible streams
  may still be rate-truncated (`movie_00000.j2k` is about 1.6 % of raw size).
* Precinct partitions, ROI, code-block bypass/termination modes as benchmark axes (they occur
  only in the small conformance streams).
* HTJ2K (Part 15), out of scope (Plan §1).

## Licence

* **Conformance files** (`input/conformance`, `baseline/conformance`): the `COPYRIGHT` file
  shipped with them states they were developed by Algo Vision Technology GmbH, Aware Inc.,
  Kodak Inc. and Ricoh Innovations Inc. for ITU-T T.803 | ISO/IEC 15444-4, Copyright (c)
  2002. The holders "agree not to assert" copyright against ITU, ISO/IEC and users of the
  JPEG 2000 standards for use of the files "for use in hardware or software products claiming
  conformance to or testing conformance to the JPEG 2000 Standard"; "no right to these files
  is granted for non JPEG 2000 Standard uses"; the notice "must be included in all copies or
  derivative works". This is a non-assertion for conformance use, not an open licence, so
  the files are **not committed**; they are fetched, together with `COPYRIGHT`, into the
  git-ignored directory.
* **Non-regression files** (`input/nonregression`, used for 11 benchmark streams): the
  repository states no licence (`gh api repos/uclouvain/openjpeg-data` reports
  `license: null`; there is no LICENSE file; `README.md` only says the files serve the
  OpenJPEG test suite; `input/nonregression/README.txt` traces several files to bug reports,
  a Google group and the Debian bug tracker). Treated as all rights reserved by their
  authors: **fetch-only**, never redistributed.

Answer to Plan §10 "Licensing of conformance files" (M0): fetch-only; only the manifest is
committed.

## Regenerating the manifest

The manifest was built once from the tree listing of the pinned commit
(`gh api repos/uclouvain/openjpeg-data/git/trees/<sha>?recursive=1`) and OpenJPEG's
`tests/conformance/CMakeLists.txt`, with downloads in a fresh scratch directory outside the
repository; the threshold lists were parsed from that file, not retyped. Moving to a new
commit means: new tree listing, re-download, re-hash, re-check thresholds against the then
current OpenJPEG file, and update the commit fields here and in the manifest.

## PDF-extracted JPX corpus (Plan §8.3, task 6.3b)

The JPEG 2000 images this library exists for are the `JPXDecode` streams inside PDFs. This
corpus is those streams, extracted from public PDFs.

### Sources (scanned 2026-11-25)

* **safe-pdf's corpus** (81 PDFs: 74 arXiv, 6 ntsb.gov, 1 uscis.gov): `pdfimages -list` and a
  byte search for `JPXDecode` find **no JPX image** (8321 Flate/raw, 821 DCT, 31 CCITT). It
  contributes nothing here.
* **pdf.js** `test/pdfs/` at commit `98100629a8ab3c6625c82a5ab5b9a82457f415f3` (1105
  committed PDFs, scanned in full): 16 contain `JPXDecode`; 15 are used. `issue3371.pdf` is
  encrypted and refused by both qpdf and poppler ("Incorrect password"), so it is left out.
  The 15 mix documents attached to bug reports or perf tests (`issue5475`, `issue5481`,
  `issue5549`, `issue5567`, `issue12213`, `issue19326`, `issue19517`, `S2`, `perf_codecs_jpx`) and
  hand-made edge cases (`jpx_numcomps`, `jpx_smaskindata`, `jpx_subsampling`,
  `jp2k-resetprob`, `bug_jpx`, `red_stamp`). Linked (`.link`, not committed) PDFs were not
  fetched: their hosts are arbitrary and CI could not reach them.
* **pikepdf** `tests/resources/` at `0c3b58ff2f28769596037367fe7245e51b486bbe`:
  `pike-jp2.pdf`, `pike-flate-jp2.pdf` (the same codestream behind `[/FlateDecode
  /JPXDecode]`, exercising the filter chain).
* **Apache PDFBox** `tools/src/test/resources/input/ImageIOUtil/` at
  `28fe61f4ad64ea2c474de775113028b4cfea981e`: `JPXTestCMYK.pdf`, `JPXTestGrey.pdf`,
  `JPXTestRGB.pdf`.
* Searched without result: py-pdf/sample-files, pypdf, pdfminer.six, PyMuPDF, qpdf,
  pdfplumber (no JPX PDFs); PDFium's test corpus is on `pdfium.googlesource.com`, which the
  sandbox's network policy blocks (HTTP 403), so it was not considered.

Licences (`sources.pdf-pdf.js`, `sources.pdf-pikepdf`, `sources.pdf-pdfbox` in the
manifest): the repositories are Apache-2.0 / MPL-2.0 / Apache-2.0, but the pdf.js test PDFs
are mostly bug-report attachments with no licence of their own. All are treated like the
non-regression files: **fetch-only**, pinned by commit and SHA-256, never committed.

### Manifest layout

* The 20 source PDFs are ordinary `files` entries with role **`pdf-source`**, path
  `pdf-sources/<repo>/<name>.pdf`, raw GitHub URL at the pinned commit, `sha256`, `size`,
  `git_blob_sha1` (checked against the pdf.js tree listing when the manifest was built).
  `scripts/fetch-corpus.py` downloads and verifies them like every other file, so CI gets
  them (152 `files` entries in total now).
* The extracted streams are the top-level list **`pdf_jpx`** (not in `files`: they have no
  URL, and `fetch-corpus.py` would try to download them). Each entry: `path`
  (`pdf-jpx/<pdf>-<obj>.jpx`), `sha256`, `size`, `roles: ["pdf-jpx"]`, `source_pdf` (the
  `files` path), `object` `[num, gen]`, `filters` (the `/Filter` chain), `format` (`jp2` or
  `j2k`), `pdf_image` (the image dictionary facts that matter for rendering: `Width`,
  `Height`, `ColorSpace` with indirect objects resolved, `BitsPerComponent`,
  `SMaskInData`, `Decode`, `Matte`, `Intent`, `SMask: present`), `codestream` (main-header
  SIZ/COD summary), and where applicable `also_in` (the same bytes in another object/PDF),
  `jp2_boxes.colr` (the JP2 colour specification for the CMYK comparison), `recorded_plane`
  (one constant reference plane for the entry's SHA-256), `reduce`, and `note`.

### Contents: 42 streams (8,464,640 bytes) from 19 PDFs

46 `JPXDecode` streams, 42 distinct (4 duplicates recorded in `also_in`). 31 JP2 files, 11
raw codestreams. 24 reversible 5/3, 18 irreversible 9/7. 1 to 5 components; 4, 8 and 16 bit;
sub-sampled chroma (2x2, 2x1, odd origin); 1 to 12 tiles; `/SMaskInData` 1 and 2 with and
without `/Matte`; `/ColorSpace` absent (JPX colour governs: `issue5475`, `issue5481`,
`issue5549`, `perf_codecs_jpx`, `jpx_smaskindata-7`), Device{Gray,RGB,CMYK}, ICCBased,
Indexed (over a 4-bit JP2 palette), DeviceN with 2 and 5 colorants. The largest,
`issue19517-8.jpx`, is 12608 x 16806 x 4 (212 Mpx, a rendered map, one tile): under
`Limits.default` our decoder decodes it at `reduce >= 1` and refuses full resolution
(`workSamples` 847,560,192 > 2^28) since task 6.5 made the sample/byte budgets bound the
reduced output grids; with raised limits it decodes at full resolution bit-identically to
OpenJPEG (`Tests/LargeImage.lean`). Its manifest entry has `"reduce": 2`.

### Extracting

```
python3 -I scripts/fetch-corpus.py      # fetches the source PDFs (and everything else)
python3 -I scripts/extract-pdf-jpx.py   # extracts missing/wrong pdf-jpx files, verifies all
python3 -I scripts/extract-pdf-jpx.py --check   # verify only
python3 -I scripts/extract-pdf-jpx.py --scan    # print pdf_jpx entries for every JPX stream
```

Needs `qpdf` (11+, for `--json=2`); skips with a message without it or without the source
PDFs. A stream is the object's raw data (`qpdf --show-object=N,G --raw-stream-data`:
decrypted, still encoded) with the filters before `/JPXDecode` undone (only `/FlateDecode`
without predictor occurs and is supported), i.e. exactly what a PDF reader hands its JPEG
2000 decoder. Every result is checked against the manifest's size and SHA-256 before it is
written; a second run extracts nothing. Cross-check when the list was built: 39 of the 42
equal `pdfimages -jp2` output byte for byte; poppler crashes on `bug_jpx.pdf` and does not
emit the two 1x1 images that no page draws (`issue19326-11`, `issue19517-13`).

When rebuilding the list with `--scan`, carry over the hand-written `recorded_plane`,
`jp2_boxes`, `reduce` and `note` fields for matching SHA-256 values.

### Image differential (`scripts/diff-images.py`)

Run `lake build image-dump` and `python3 -I scripts/diff-images.py --jp2 --verbose`.
The differential verifies each file's SHA-256 and checks component count, dimensions,
depth, sign and every sample. The **codestream** comparison uses raw components or the RGB
channels when OpenJPEG infers sYCC. The **jp2** comparison uses the consumer channels from
`JPEG2000.decode`, including palette, component mapping, channel definitions and colour
conversion. The peak error limit per component is 0 for reversible coding and 1 for
irreversible coding, with an additional 1 for sYCC conversion. Both decoders use the
manifest's resolution reduction (`issue19517-8` uses 2). The default size limit is 40
megapixels at the reduced resolution.

With OpenJPEG 2.5.3, **42/42 PDF streams passed**, including every JP2 comparison.
With `--jp2`, 51/51 files passed, with zero known deviations, failures, size skips or
absent files. The differential delegates the ICC rendering of conformance files 5, 7 and
8 to the TIFF suite. With lcms2 2.16 installed, `lake exe tests` passed all nine TIFF
references, including those three.

* `bug_jpx-15` is a bare codestream. Its manifest entry records the OpenJPEG reference
  obtained with two empty tile-parts omitted. Only `image-dump` decodes the original.
  Its raw output and consumer image each matched the single unsigned 8-bit 128×64
  reference plane exactly, including all 8,192 zero samples. A wrong hash, decode error,
  different plane format or nonzero sample fails the comparison.
* `JPXTestCMYK-12` declares JP2 enumerated colour space 12. OpenJPEG writes four CMYK
  channels to TIFF and renders three RGB channels for PGX. The harness compares all four
  JP2 consumer colour channels to the TIFF. OpenJPEG's multiplicative CMYK formula uses
  binary32 normalization and truncates to 8-bit RGB. A C compiler can fuse the multiply
  and subtract during normalization. The harness selects a rounding mode using only the
  OpenJPEG TIFF and PGX, requiring an exact match across all three RGB planes. On this
  machine fused rounding matched. The harness applies that conversion to the consumer
  channels and compares them directly to native OpenJPEG PGX at the irreversible limit of 1.

  | Comparison | Peak by channel | MSE by channel |
  |---|---|---|
  | Bare codestream | 1, 1, 1, 1 | 0.0001, 0.0002, 0.0002, 0.0001 |
  | JP2 consumer CMYK vs OpenJPEG TIFF | 1, 1, 1, 1 | 0.0001, 0.0002, 0.0002, 0.0001 |
  | OpenJPEG TIFF rendered to RGB vs OpenJPEG PGX | 0, 0, 0 | 0, 0, 0 |
  | JP2 consumer rendered to RGB vs native OpenJPEG PGX | 1, 1, 1 | 0.0003, 0.0003, 0.0003 |

  A separate test simulated non-fused PGX from the same TIFF samples. Calibration selected
  non-fused rounding exactly, and the direct consumer comparison failed at peaks 2, 2, 2.
  Native results above were measured on AArch64.

* `issue12213-16` has two comparisons. The bare codestream yields the 4-bit index plane.
  The JP2 comparison applies the palette and compares the three channel planes before
  display scaling. OpenJPEG writes unsigned PGX with declared depth 4 and full stored
  palette bytes, including 191 and 255. Both comparisons are bit-exact. In the PDF the
  image dictionary supplies its own `/Indexed` colour space.
* `jpx_subsampling-11` and its even-origin control `jpx_subsampling-10` are bare
  codestreams. The comparison uses RGB after OpenJPEG's inferred 4:2:0 sYCC conversion.
  At origin (1, 1), row 0 takes raw zero Cb and Cr before the chroma offset is subtracted.
  At column 0 the first row of each subsequent pair takes raw zero and the second row
  takes the first stored chroma sample. The final unpaired row also starts with raw zero.
  All three RGB planes are bit-exact for both origins. Ordinary component upsampling
  still replicates the nearest edge sample.

CI (Linux) runs the fetch, `extract-pdf-jpx.py` and `diff-images.py`; it fails on any
deviation not recorded in the manifest.
