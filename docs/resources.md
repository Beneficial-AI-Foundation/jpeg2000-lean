# S2 (totality) and S3 (bounded resources): what is proved

Task 7.4 (Plan.md §4 S2, S3; §3 rules 2–3). Theorems are in `Spec/Resources.lean`
(namespace `JPEG2000.Spec.Resources`). Every theorem depends only on `propext`,
`Classical.choice`, `Quot.sound`.

## S2 — totality

> `decode` is a total function, accepted by the termination checker, on every byte string.

In Lean every `def` the kernel accepts denotes a total function, so the literal statement
(`decode_total : ∀ L data opts, ∃ r, decode L data opts = r`) is proved by `⟨_, rfl⟩` and
carries no information. S2's real content is that **the kernel definition is what runs** and
that it is a genuine definition:

| Obligation | How it is discharged |
|---|---|
| No `partial` (opaque constant with a hidden recursive implementation), `unsafe`, `implemented_by`, `extern` in the decoder | `scripts/hygiene.py` (textual, every file under `JPEG2000/`, `Spec/`, `Encode/`); and the closure audit below (semantic, on the constants `decode` actually uses) |
| No `panic!`, `get!`, `xs[i]!` | `scripts/hygiene.py` |
| No `sorry` in the definitions | `#print axioms JPEG2000.decode` and `#print axioms JPEG2000.decodeCodestream` print `[propext, Classical.choice, Quot.sound]` (both declarations are in `scripts/axioms.lean`) |
| Every loop terminates | kernel: structural recursion or fuel; each fuel is a size already checked against `Limits` (Plan.md §3 rule 2) |

The hygiene guard runs `lake env lean scripts/closure.lean` on `decodeCodestream`,
`decode` and both image interleavers. The audit resolves each entry point, walks the
types and values in its kernel dependency graph and reports how many declarations it
visited. It rejects reachable unsafe declarations and `sorryAx`, as well as project
axioms, opaque definitions, externs and implementation overrides. Lean's generated
constructor index is recognized by its parent inductive and the pinned compiler's
`T.ctorIdx._impl` replacement. Lean core primitives remain part of the trusted runtime.
A negative check through a private wrapper detected a hidden partial function, and a
separate check detected a safe-looking definition with a replacement implementation.

## S3 — bounded resources

> Output size, intermediate allocation and work are bounded by explicit functions of `Limits`
> and the input length; excess is `Error.limitExceeded`.

The successful-run S3 theorems give the checked budgets and bounds derived from the
actual data structures. The principal quantities are listed below.

| Quantity | Bound | Theorem |
|---|---|---|
| input length | `maxInputBytes` | `parse_within`, `decode_size` |
| declared image side, area, tiles, `tiles × Csiz` (full resolution) | `maxImageSide`, `maxImageArea`, `maxTiles`, `maxCodeBlocks` | `checkGeometry_ok_iff` (`GeometryWithin`), `parse_within` |
| code-blocks, precincts, packets of the whole tile grid (exact totals, `Header.checkWork`) | `maxCodeBlocks`, `maxPrecincts`, `maxPackets` | `checkWork_within` |
| `reduce` | `maxDecompLevels` | `decodeCodestream_resources` |
| output component planes at the requested `reduce` (cells `outputCells` / bytes `outputBytes` at `bytesPerSample`); each plane exactly `width × height` | `maxWorkSamples` / `maxDecodedBytes` | `allocOutput_ok`, `allocOutput_ok_iff`, `decodeCodestream_resources` |
| `decode`: image area | `maxImageArea` | `decode_resources`, `decode_size` |
| `decode`: up-sampled channels (fresh cells / bytes; every channel, alpha and other channel is one of them, `w × h`) | `maxWorkSamples` / `maxDecodedBytes` | `decode_resources` (`ImageWithin`) |
| interleaved 8/16-bit buffer (exact size `w·h·n·(1|2)`) | `maxDecodedBytes` | `interleave_size`, `interleaved8_size`, `interleaved16_size` |
| Aggregate reduced component areas of one tile before reconstruction | `maxWorkSamples` | `NativeResources.centeredTile_work`, `NativeResources.centeredTile_limitExceeded` |
| Whole-image physical packet visits plus POC membership tests, including a rejecting prefix | `maxTiles × maxPackets` | `PublicPacketWork.decode_packet_work` |
| Admitted packet passes across all attempted tiles | `maxCodingPasses` | `PublicPacketWork.decode_packet_work` |

`JPEG2000.Spec.NativeResources.decodeCodestream_resources` bounds native output storage for the public
`decodeCodestream` on both compact and mixed-depth images. A successful decode retains
the requested reduction, the component order and metadata from SIZ, and each component's
reduced grid. Exact reads succeed precisely at indices below its area. Across all output
components, the cell count is at most `maxWorkSamples`, the declared output size is at most
`maxDecodedBytes`, and the physical backing arrays occupy at most `8 × maxWorkSamples`
bytes. Compact backing uses four bytes per cell and wide backing uses eight. The
`Spec.Resources` Int32 plane theorems also remain available for `decodeCodestreamNarrow`.

The public tile loop first obtains the effective layout and checks the sum of the
reduced component areas. If the sum exceeds `maxWorkSamples`, it returns the exact
`limitExceeded` value before reconstructing any component. The check covers both
present and omitted tiles, including mixed wavelets. Intermediate wavelet buffers
and repeated work during a wide retry are separate obligations below.

### Parsing, geometry and byte gathering

For an input of `N` bytes, `HeaderWork.parse_input_excess` gives the exact
input-size error from `Header.parse` when `N > maxInputBytes`. On success,
`parse_storage` bounds the codestream range by `N` and its main marker and
segment-reference entries by the codestream length. The box, marker and
tile-part loop fuel theorems preserve the error on a rejecting prefix. A
completed box advances by at least eight bytes, a marker visit by at least two,
and a completed tile-part edge by at least four.

`HeaderWork.sortUnique_work` covers sorting the TLM, PPM, PPT and PLT byte keys
before checking for duplicates. For `n` records, the pinned insertion sort calls
its comparator at most `n²` times. Including the projected key list and adjacent
duplicate checks gives at most `n² + 2n` charged operations. The measured
routine returns the same sorted array or the same first-duplicate diagnostic.

After geometry admission, `checkWork_visits` bounds component evaluations by
`maxCodeBlocks`, including the final evaluation on rejection. Completed precinct
initialization retains at most `maxPrecincts` states and at most
`51 × maxCodeBlocks × maxPrecincts` nested block and tag-tree entries.
`ppmChunks_account` charges four length bytes and the consumed payload for each
completed packed-header chunk. `ppmChunks_fuel` also covers a failed split.

Direct Tier-1 input borrows the original buffer. With `K` source ranges and
`S` segments, the fragmented path returns at most `K × N` bytes. Its
conservative copy charge is at most `(2K + S) × K × N` byte writes when every
append copies its whole result. `tier1Input_copy_charge` accounts for both copy
folds, and `tileData_copy_charge` tracks tile-part copies already completed on
rejection. The multiplicity of ranges in actual packet output remains an input
to these bounds.

### Packet traversal

`Spec.Resources.PublicPacketWork.decode_packet_work` applies to every input, limit
record and reduction. Erasing its trace returns the exact result of
`decodeCodestream`, including the diagnostic on failure. Rejection during header
admission or native output allocation has an empty packet trace. Each later entry
records the tile, the number of passes already admitted and the current tile-part
cursor. An omitted tile has an empty packet log.

`PublicPacketWork.admission_error` proves that both public entry points return
the same error from reduction admission, header parsing or native output
allocation, with the same location, kind and payload and zero packet visits. When the reduction and input length both exceed their limits,
`admission_excess` identifies the reduction error. With an admitted reduction,
an oversized input yields the input-size error at byte zero.

A physical visit counts one innermost progression position, including positions
skipped because an earlier POC volume covered them. Each earlier volume tested
for membership adds one operation. Their combined count is at most the number of
present tiles times `maxPackets`. All passes admitted from packet contributions
sum to at most `maxCodingPasses`, even if reconstruction or placement later fails.
A rejecting packet still counts as an attempt. For example, the pinned
`issue12213-16.jpx` stream admits 564 passes over 90 packet attempts and three tiles.
A zero-pass budget records the first attempt and returns the exact limit error
for its proposed seven passes.

### Tier-1 block work

The compact and wide meters follow the segment schedule, raw or MQ decisions,
stripe scans, restarts and termination checks. Erasing a meter gives the same
result or error as its decoder. For a parsed block with `S` supplied segments
and `P` supplied passes, `Tier1Work.parsed_call_work` gives the per-attempt bound

```
26,006 + 8,510 × S + 66,002 × min(P, 874)
```

in structural work units. One compact attempt followed by a wide retry charges
at most twice this quantity. The bound covers all code-block styles, including
an early return. Validated work buffers have at most 4,096 wide coefficient cells
or 8,196 words in each compact work array. `Tier1Work.parsed_cells` gives a
magnitude below `2^292` and a last plane at most 291 for every returned wide cell.
To obtain whole-image work, the per-attempt charges must still be summed over
the blocks and retries actually selected by reconstruction.

### Coefficient assembly

For each component selected by the native tile dispatcher,
`AssemblyCost.parsed_component_work` counts the resolutions, precincts, bands
and block records actually visited, including skipped zero-pass blocks. The meter
returns the same component result or error. It retains the work of a failed
compact prefix when the dispatcher restarts assembly at wide precision.

For reduced component area `A`, the bound is `5*A + 2*topology`. The area term
covers initialising four packed bytes and one wide integer slot per cell across
both attempts. The topology term includes Tier-1 decoding, fragmented input
gathering, dequantisation and placement for the supplied block records.
`AssemblyCost.native_budget` connects `A` to the checked aggregate tile area.
`AssemblyCost.component_budget` replaces the topology sum with a numeric
bound given the precincts per resolution, bands per precinct, blocks per band,
segments per block and translated ranges per block. The remaining packet-history
proof must establish these counts for the actual packet store.

### Wide integer arithmetic

`Spec.Resources.WideArithmetic` bounds the operands of dequantisation, integer
lifting and the inverse colour transforms before the final clamp. For a parsed
tile, the per-block inputs are a magnitude below `2^292` and a last plane at
most 291. The effective quantisation parameters then give a magnitude bound
of `2^372` through coefficient assembly, including the biased dividend before
division. A 5/3 level adds at most 12 to the magnitude exponent. A 9/7 level
adds at most 540, including the two axes and the operands of the rounded
fixed-point products. RCT adds at most 3, and ICT adds at most 21.

`Resources.centeredTile_signed_width` combines the Tier-1 and arithmetic
theorems at the ordinary tile traversal. For every parsed header and every
successful centred tile, each source read needs at most
`395 + 540 × L.maxDecompLevels` signed bits, or 17,675 at the default limit.
The bound applies before placement and G.1 clamping, including omitted tiles.
Converting it to live storage requires the number of simultaneous
values and a size model for their representation.

### Native tile colour and placement

`TileColorPlacement.native_tile_work` follows a parsed tile through the native
colour transform and output writer, preserving their result and exact errors.
Let `C = maxComponents`, `S = maxImageSide`, `W = maxWorkSamples` and let `B`
be the logical charge for one wide integer slot. The combined structural charge
is at most `6 + (13+S)*C + (42+3*B)*W`. This includes packed ICT and its wide
retry, the rasters retained when a later component fails, lazy RCT reads, G.1
clamping and both blitters. The side-length term covers row visits by the packed
blitter even when the tile has zero width.

The placement continuation alone costs at most `(2+S)*C + 18*W`.
`placement_read_domain` bounds the three predecessor reads per lazy RCT sample
by `3*W` over the tile. Component reconstruction before colour, the output
backing and the later JP2 display stage have separate bounds.

### Colour, replication and display

`JPEG2000.Spec.ColorResources.decode_resources` applies to every successful public
`JPEG2000.decode L data opts`. Its `raw` field gives the complete native codestream
certificate above. Its `image` and `colour` fields cover the reduced reference grid,
the actual selected mapping, conversion, upsampled planes and channel selection. Write
`W = L.maxWorkSamples`, `S = L.maxImageSide`, `C = L.maxComponents` and
`P = L.maxPaletteEntries`.

| Quantity | Bound | Evidence |
|---|---:|---|
| Retained raw component byte arrays | `8 W` bytes | `Within.raw.physical` |
| Fresh compact palette, sRGB and replication rasters | Each stage ≤ `4 W` bytes. Raw plus all three stages ≤ `20 W` bytes | `BackingWithin`, `mapping_backing`, `SyccWithin`, `FullWithin` |
| Original JP2 palette, even if disabled | Exactly `NE × NPC` UInt64 entries and `NPC` depth tags, with `NE ≤ P`, `NPC ≤ 255` | `Within.palette`, `retained_palette` |
| Expanded palette columns | ≤ `C P` exact integer entries. Compact conversion can also build an Int32 column of the same length | `MappedFrom`, `MappingWithin.trace` |
| sYCC coordinate and edge tables | Two vectors of luma width, two of luma height, and zero or one entry per luma row. Total ≤ `5 S` | `sycc_indices_size`, `Converted` |
| Replication indices | Width plus height per replicated channel, ≤ `2 C S` entries in total | `upsample_resources`, `ColourWithin` |
| Ordered output records and display scaler records | Colours ≤ `C + 1`, other channels ≤ `C`, optional whole-image alpha adds at most one. These bounds also hold at zero area | `resolved_layout_size`, `Within.display` |
| Full-grid sample visits and declared bytes | `width × height × full.size ≤ channelBytes ≤ L.maxDecodedBytes` | `replication_resources`, `ColourWithin` |
| Restricted ICC profile copy | ≤ input length | `ColourWithin` |
| Interleaved output | For `n = width × height × (img.outChannels alpha).size`, exactly `n` bytes at 8 bits and `2 n` at 16 bits, or the exact decoded-byte limit error | `Within.display`, `interleave_resources` |

Each palette lookup view captures the source plane and its exact column. Each lazy RGB
channel reads from the three mapped sources using the same five index arrays. Replication
can retain that RGB view or a palette view together with its own pair of coordinate
vectors. Direct selection, including alpha and other channels, shares the selected
plane. The sample-byte bound charges each construction once, including compact rasters
that may have been released before return. The separate table bound counts up to
`2 C P + 5 S + 2 C S` entries for colour kernels. Lean exposes plane byte lengths and
array lengths. Runtime object headers, allocator capacity, transient list/map scaffolding
and the heap representation of boxed integers have no byte price in these statements.

The palette fold charges the sum of index-plane areas even for lazy outputs. The compact
RGB loop has luma-area fuel, its three output rasters together have at most `W` cells,
and the total charged replication area is at most `W`. Axis bounds also apply at zero
area. For example, replication on a 7 × 0 grid builds seven column entries, and a
0 × 5 grid can retain five row entries. An empty palette index raster can still capture
a full lookup column. The standalone mapping entry point checks source count before
building output formats and column length before constructing each lookup table.

For every colour, alpha and other channel, `Channel.get? i` succeeds exactly when
`i < width × height`. Outside the raster it returns `none` and a zero-default read yields
zero. The interleavers visit one sample per selected channel per pixel under either
scaling mode. `Within.loops` identifies the selected compact or native kernel, its
image-area fuel and the exact length of its per-pixel scaler list. The public
certificate allows a separate display budget and also covers
out-of-range indexed byte reads. These are loop lengths and storage bounds. A machine
instruction count requires a cost model.

**Declared versus allocated (task 6.5).** The header bounds what the stream *declares*
(side, area, tiles, tile-components, at full resolution: absurd headers are refused before
the tile-parts are read); `maxWorkSamples`/`maxDecodedBytes` bound what is *allocated*, at
the requested reduction: the native output grids (`NativeOutput.allocOutput`, B-14), reduced
planes for one tile at a time, `decode`'s channels and
buffers. The compact raw path uses four-byte cells and the wide path uses eight-byte cells.
The colour bounds above apply after the raw result is returned. Tile reconstruction has
its own resource audit.

**Excess ⇒ `limitExceeded`.** `checkGeometry_limitOnly`: the geometry check fails only with
`limitExceeded` (value > bound). `decode_limitExceeded_of_geometry` (and the `_of_area`
corollary): if the container (`Box.parseFile`) and the main header (`parseMainHeader`) parse
and the declared geometry violates `GeometryWithin` — e.g. area > `maxImageArea` — then
`decode L data opts = .error (.limitExceeded loc k v b)` with `b < v`, for every `opts`. The
precondition is needed: a stream malformed before the end of its main header fails with
`malformed`/`truncated` first. (A too-large `reduce` is also `limitExceeded`, checked first.)
`public_limitExceeded_of_output`, `decode_limitExceeded_of_output` and
`decode_limitExceeded_of_bytes`: if `Header.parse L data = .ok h` and the output at the
requested reduction exceeds `maxWorkSamples` cells (`outputCells h.siz reduce`) or
`maxDecodedBytes` bytes (`outputBytes h.siz reduce`), the decoder fails with `limitExceeded`
before any plane is allocated (`allocOutput_ok_iff`, `allocOutput_limitOnly`). Before 6.5,
`decode_limitExceeded_of_bytes` took the main-header hypotheses and the full-resolution
`declaredBytes`; the bound moved to what is allocated, so its precondition is now the whole
header (the check runs after the tile-part headers are parsed).

### Maintenance

The statements name checked quantities (`GeometryWithin` mirrors `checkGeometry`;
`allocOutput_ok`/`outputCells`/`outputBytes` the reduced output grids; `tileCells` the
per-tile set). The proofs unfold `decodeCodestreamNarrow`, `Decode.allocOutput`, `decode`,
`Assemble.decodeTile`, `reconstructTileComp`, `Header.checkGeometry`/`checkWork`,
`Tier2.Packet.decodeTilePacketsWith` and `Tier2.Headers.decodeAllTileCodeBlocks`: an edit
there must re-check `lake env lean Spec/Resources.lean` (as with the C9 skeletons). Task 6.5
dropped the full-resolution `workSamples`/`decodedBytes` checks from `checkGeometry` (and
from `GeometryWithin`); `decode_limitExceeded_of_bytes` now rests on `allocOutput`'s check.

### Remaining public resource bounds

The public codestream and image output sizes, palette backing, per-channel domains
and interleaver lengths above are proved. To finish S3, the following bounds must
also account for the work performed before an error.

* **Local packet operations (7.4c1h).** Price the work
  inside each attempted packet, including tag-tree and segment handling before
  pass admission, and the setup of progression volumes even when empty.
* **Reconstruction (7.4c2s2 and 7.4c2s4).** The checked decoder can retry using wide
  coefficients. Apply the wide integer bounds to both attempts and bound lifting and
  colour-transform visits, temporary line arrays and live planes across levels.
* **Parsing and gathering (7.4c3a–c).** Bound the inner payload, sorting
  and descriptor operations on early rejection. Derive range and segment
  multiplicity from actual Tier-2 output and aggregate the copy charges.
  Include temporary geometry, index and tag-tree storage on failing prefixes
  and the original input buffer in the storage bound.
* **Composition (7.4c4).** Give explicit functions of `Limits` and input length
  for public work and intermediate allocation. Connect each counted operation
  to its decoder loop, including the prefix traversed before rejection.
