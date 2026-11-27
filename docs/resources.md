# S2 (totality) and S3 (bounded resources): what is proved

The public S2/S3 results for Plan.md §§3–4 are in `Spec/Resources/PublicAPI.lean`
and `Spec/Resources.lean`. The axiom registry and runtime dependency audit cover
the proofs and the four production entry points, respectively.

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
rejection. `SegmentHistory.store_bounds` supplies the segment and range counts
for blocks from the public packet decoder.

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

Before the packet quota check, `PacketLocalWork.preflight_work` bounds the
calculation of the actual progression schedule size from parsed limits. After
precinct initialization, `parsed_setup` covers the loops for all five
progression orders, including empty volumes and repeated component scans.
A spatial progression table holds at most
`maxComponents * (maxDecompLevels + 1) * maxPrecincts` entries. The measured
merge sort on `n` entries costs at most `n + 8*n² + 1` charged operations.

`PacketLocalWork.decode_attempts` connects each attempted packet in the public
trace to its incoming precinct state and reader. The reservation for all
attempts is at most `maxTiles * maxPackets * attemptBudget L`. It includes
tag-tree walks, packet bit reads, segment-length decoding and body construction
before a cumulative pass refusal. `body_range_bytes` bounds bytes skipped by
the unread body extent, including the completed pieces of a failing contribution.
`packet_prefix_storage` bounds growth in segment and range records before
translation to the original tile-part byte ranges. For a completed tile,
`completed_store` identifies the actual final precinct states and the table
used to translate every output range. Their pre-translation records total at
most `out.packets * recordGrowth L`, with `out.packets ≤ maxPackets` and one
table entry per source tile-part.

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
`ReconstructionCost.public_work` accumulates the selected block and retry
charges over the reached tiles on this input.

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
segments per block and translated ranges per block. `ReconstructionCost.storeCaps`
provides the public caps using the packet-store evidence in `SegmentHistory.store_bounds`.

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
The following sections use cell counts and rounded signed-magnitude byte widths
to bound wavelet scratch and retained component storage.

### Inverse wavelet visits and storage

For reduced component area `A` and retained depth `D`, a checked packed 5/3
or 9/7 attempt visits at most `4 + 32*A + D*(5*D + 4500*A + 5)` operations.
Repeated halving of the four rectangle coordinates is included at every level.
The row and batched-column scratch buffer contains at most `8*A` packed cells.
`WaveletCost.compact_allocation` separately bounds copies when the backing is
shared across updates.

For either checked wide transform, `wide53_work` and `wide97_work` bound visits
by `5 + 2*A + D*(10 + 100*A)`, array headers by `1 + D*(3 + 12*A)`, outer
references by `2*A*D` and freshly materialised integer slots by `A + 13*A*D`.
The area and depth are capped by their admission limits on rejection. With
input magnitudes at most `2^b`, the signed-width bounds for intermediate
operands are `b + 12*D + 2` bits for 5/3 and `b + 540*D + 2` for 9/7.
`retry53_work` and `retry97_work` charge the packed allowance if that path is
attempted and the wide allowance if the dispatcher retries.

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

`PublicPacketWork.decode_placement_work` sums this charge over the ordinary
codestream decoder's grid loop. A tile that fails during colour or placement
contributes its prefix. A failure at admission or packet selection adds zero
colour and placement work. The result or error agrees with `decodeCodestream`,
and the total charge is at most the number of visited tiles times the per-tile
bound above, hence at most `maxTiles` times that bound.

For component rasters retained before MCT, `component_signed_width` proves
a bound of `374 + 540*maxDecompLevels` signed bits per wide sample. This also
applies to a completed component when a later component fails.
`centeredTile_backing_bytes` sums the packed bytes and the actual rounded
signed-magnitude bytes of the wide cells in the retained predecessor rasters.
Their total is at most `(4 + ceil((374 + 540*maxDecompLevels)/8))*W`, with
2,207 bytes per wide sample at the default depth limit. This logical payload
counts shared lazy RCT predecessors once. Runtime object and allocator overhead
are outside the byte measure.

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

For arbitrary input bytes, `MappingPrefix.image_mapping_work` follows the native decode
through JP2 metadata resolution and channel mapping. It returns the same first error and
bounds this stage by `metadataBudget L data.size`. The single-component CMAP repair can
restart a scan for each palette column. The bound counts those scans and the lookup that
rejects a source. Palette raster visits accumulate across channels. For `c` raw channels,
`mappingBudget L c = 1 + 2c + 5C + C(2 + 9P) + 17W`.

`DisplayPrefix.display_work` covers the subsequent conversion, replication, channel
selection and ICC copy, bounded by `displayBudget L data.size`. An earlier mapping
failure incurs zero work in this stage. A later rejection includes the work already done.
`selected_reads` follows each selected channel through its actual palette, RGB and
replication views and bounds one sample read by 44 logical operations. The separate
`public_interleaving_work` theorem applies to either output precision, either scaling
mode and either alpha choice. Its bound is `interleavingBudget L budget`, where
`budget.maxDecodedBytes` is the caller's limit for that interleaving request. Even an
empty selection can traverse the pixel grid.

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

For a CDEF table with `d` records, `ColorResources.alpha_work` counts the
pinned array quicksort's comparisons and the subsequent opacity search.
Together they cost at most `(d-1)*(d+3) + d`. It returns the same optional
definition used by the channel layout, including its premultiplication type.
An absent opacity record requires a scan of all sorted definitions.

`ColorResources.layout_work` accounts for the complete JP2 channel layout,
including the first malformed channel or association, duplicate or missing
channels, the colour-association lookup that fails, and the final filter for
unassigned channels. Let `n` be the mapped channel count, `d` the CDEF length
(zero if absent) and `m` the declared colour count (or `d` if unknown). The
bound in record visits and temporary index slots is
`5*n + 5*d + 2*m + m*(1+3*d) + (d-1)*(d+3) + d + n*(1+m)`.
It applies even when no pixels are produced. The validator alone charges at
most `3*d + 2*n` and does not allocate its channel-count table until all
references pass the first scan.

At `Color.resolve`, `resolve_layout_work` bounds the mapped channel count by
`maxComponents`. Recognised enumerated and ICC colour spaces request at most
15 colours, including the ICC `FCLR` signature. An unknown colour space uses
the CDEF count. `retained_cdef` traces the parsed unsigned 16-bit count through
native decoding. Thus `image_layout_work` gives a limit-only bound at the
display API with `n = maxComponents` and `d = m = 65535`. The sharper bound
above applies when the actual record count is known. Early native and mapping
errors incur zero layout charge. A layout error propagates unchanged through
the public decoder.

`GeometryInit.image_geometry_work` and `decode_geometry_work` sum header and
tile geometry through the first failing stage. Write `T = maxTiles`,
`C = maxComponents`, `B = maxCodeBlocks`, `D = maxDecompLevels + 1` and
`P = maxPrecincts`. One tile layout costs at most `A = 2 + T + C*(6+T)`;
packet geometry costs at most `I = C*(5+D*(17+P*(78+87*B)))`. The total is
at most `4*T + B*(5+5*D) + T*(A+I+A)` visits, descriptor constructions and
logical entry reservations or initializations. This includes building arrays
before the aggregate precinct or block check rejects them. The returned
store carries bounded precinct, band and code-block counts at every resolution.

For each tile reached by the native decoder, `ReconstructionCost.decode_work`
charges packed assembly, its possible wide retry, transforms, colour and
placement through the first failing component or write. The parameters in
`Prices` let callers count visits, headers, references, logical bytes or
visits weighted by operand width. A wide Tier-1 cell occupies up to 43 logical
bytes with flags. The wide Mallat input uses up to 47 bytes per cell.
`live_workspace` accounts for already reconstructed components beside packed
and wide work planes and transform scratch. At the public decoder, `ReconstructionCost.public_work` obtains all five caps
from the actual header and packet history. A block has at most
`S = maxPackets * 6 * maxCodeBlocks * (1 + maxPassesPerCodeBlock)` segment
descriptors and at most `K = S * maxTilePartsPerTile` translated ranges.
`SegmentHistory.tile_translation_work` bounds source-range probes across the
actual output spans by `maxPrecincts * K`. For input of length `N` and at most
`M` tile parts, the tile gather charges at most `M*(N+M*N)` byte writes. A
fragmented block charges at most `(2*K+S)*(K*N)` byte writes. A direct block
borrows the input.

### Header parsing and packed packet headers

`HeaderPayload.parse_work` follows the public parser through JP2 boxes,
marker payloads, tile-part assembly and geometry admission. Its result
includes the exact error on a rejecting input. The charge counts reached
callbacks, sort operations and logical descriptor slots. For instance, a
truncated payload can incur array reads even though the parser returns no
header.

`sort_calls` bounds the number of calls to the four byte-key sorts by
`2 + maxTiles * (1 + maxTilePartsPerTile)`. The two main-header sorts order
TLM and PPM records. Tile assembly sorts PPT records once per present tile
and PLT records once per part. Empty tables still pass through the sort.
A duplicate PPM index stops the parser at its second sort.

`decode_header_work` includes the public decoder's reduction check, its
header parse, the once-per-grid PPM rank construction, and packed-stream
selection at each visited tile cursor. The rank step is reached only after
native destination allocation succeeds. With input length `N`, `V` visited
tiles and a logical price `B` for a wide integer slot, the combined header
and placement charge is bounded by
`headerBudget L N + rankBudget L + V * (selectionBudget L N + placementBudget B L)`.
`V ≤ maxTiles` gives the bound in terms of caller limits and input length.

### Combined native decoder bound

`NativeCost.decode_work` applies to every byte array, limit record and requested
reduction. The measured result equals `decodeCodestream`, including its first error.
For `N` input bytes and `V` tiles actually visited, the charge is at most
`NativeCost.prefixBudget L N V`. Setting `V = L.maxTiles` gives the input-independent
tile allowance in `NativeCost.budget L N`.

The charge includes the original `N` bytes, reduced component rectangles, destination
allocation, header and geometry work, packet traversal, gathers and reconstruction.
Shared placement work appears once in the combined stage charge. A separate copy
allowance covers a destination write that needs fresh backing.
`destination_storage` follows the actual prefix of completed tiles and proves that
the backing lengths still match the original allocation at the next tile, including
when that tile fails. Their sum is at most `8 * L.maxWorkSamples` bytes.
`attempted_storage` accounts for packet contributions consumed before a later failure.

### Maintenance

The statements name checked quantities (`GeometryWithin` mirrors `checkGeometry`;
`allocOutput_ok`/`outputCells`/`outputBytes` the reduced output grids; `tileCells` the
per-tile set). The proofs unfold `decodeCodestreamNarrow`, `Decode.allocOutput`, `decode`,
`Assemble.decodeTile`, `reconstructTileComp`, `Header.checkGeometry`/`checkWork`,
`Tier2.Packet.decodeTilePacketsWith` and `Tier2.Headers.decodeAllTileCodeBlocks`: an edit
there must re-check `lake env lean Spec/Resources.lean` (as with the C9 skeletons). Task 6.5
dropped the full-resolution `workSamples`/`decodedBytes` checks from `checkGeometry` (and
from `GeometryWithin`); `decode_limitExceeded_of_bytes` now rests on `allocOutput`'s check.

### Diagnostic construction on the public paths

`DiagnosticCost` counts decimal and hexadecimal digits, copied prefixes and temporary
storage at the construction site. A passed marker check can still evaluate its message.
The SOC/SIZ prefix constructs at most `6 * L.maxComponents + 24` messages. Each SOT
prefix constructs at most 14, and the tile-part reader visits at most `data.size`
such prefixes. A failed JP2 signature check can construct and then discard a nested
box error. The proofs also cover the PPM count mismatch, SOP, colour resolver errors
and the counts retained by the two interleavers.

Each parser stage may bound its own offsets and numeric fields. Before joining stages,
`Trace.raiseCap` places their traces under a common upper bound. The ordered strings
and their expression trees stay identical, so the composed trace retains each stage's
actual digit conversions, copies and temporary storage.

An oversized reduction yields a typed error that refers to the caller's natural.
`reduction_storage` bounds the decoder-owned payload by seven logical units.
`caller_render_unbounded` proves that formatting this error after the call can
produce arbitrarily many bytes, even for a fixed input and fixed limits.

`DiagnosticBox.public_box` covers the entire JP2 container parser. Its trace
contains at most `17 + 12 * (L.maxBoxes + 1)` messages. The top-level loop
descends into at most one JP2 header. It can discard a malformed later colour
specification after accepting an earlier one. The bound includes both the
successful checks and the discarded error. On empty input, the raw probe and
first box read each produce a truncation before the parser returns its signature
error. Recognizing an admitted raw codestream produces no container messages.

`DiagnosticMarker.public_cost` bounds the main-header diagnostic work and temporary
storage on every input. It counts the checks reached between SOC and the first SOT,
including eager messages on successful COD, QCD and other marker payloads. On a
main-header error, both public decoders return its original marker-stage offset
within the codestream range. A rejected cumulative POC count can reach twice
`maxPocEntries` when both contributing counts individually fit the limit.

`DiagnosticMarker.public_throughMain` composes the container and main-header
traces up to geometry validation. A successful JP2 container can have discarded
an earlier colour-box diagnostic before the main-header parser encounters its
first error. The combined bound charges both events and gives the exact error
returned by the native and display decoders.

`DiagnosticPointers.public_cost` counts pointer payload reads and diagnostic
construction once main-header geometry and coding checks admit the input.
For an input of length `N` and tile-part limit `T`, the pointer pass produces
at most `2*(T+1) + 2 + N*(2*T+8)` diagnostic events. Their scalar fields fit
`max (2^32) (max N (2*T+1))`. This covers a four-byte packed-header length
split across physical PPM segments and a cumulative TLM count that exceeds the
limit after both individual segments pass. Both public decoders preserve the
resulting error and its absolute marker offset.

`DiagnosticTileMarkers.public_header` covers each tile header reached by the
public parser. For `N` input bytes and a POC-entry limit of `P`, it bounds the
diagnostic count by `N * (10*P + 285) + 1`. A final short marker read constructs
both the reader error and its replacement for the missing SOD. Successful
headers pass the updated, admitted POC count to the next tile-part and keep
PPT data ranges within the backing input. A PLT length occupies at most 32 bits.

`DiagnosticTilePart.public_cost` follows the complete tile-part loop and its
assembly pass. It counts a failed outer marker read before the replacement EOC
error, sorts PPT indices across a tile and PLT indices within a part, and
charges the nested decimal expression when a corrected TNsot still disagrees
with the number of parts. A packet-count refusal includes the full PLT count
of the tile that pushed the total over its limit.

`DiagnosticCoding.public_cost` covers main defaults, the repeated collection
of component overrides and per-tile coding. A successful merge contributes no
message. The first rejecting merge contributes one message with the source
offset and the values used by that merge. Rebuilding the same main override
tables after successful main coding still costs work. Its second validation
cannot emit a duplicate-component diagnostic.

`DiagnosticGeometry.geometry_refusal` gives the first excessive value in
header geometry order. `work_refusal` identifies the tile, component and
running totals at the first excess in code-blocks, precincts or packets,
including tiles with default coding and no tile-part. Both checks retain the
marker location at offset 2 on raw and JP2 inputs. Each constructs zero text
messages. For `P = 256 * 2^64`, the computed work-check value fits the maximum
of `maxCodeBlocks + 3*P`, `maxPrecincts + P` and `maxPackets + 65535*P`
even when the guard refuses it.

`DiagnosticPacket.decode_work` adds the Tier-2 diagnostic charge to native work.
For a prefix with `V` visited tiles and `A` attempted packets, the diagnostic
charge is bounded by `(1 + 2*V + 2*A) * eventBudget (tileCap L data.size)`.
The first term covers the shared PPM rank check. A packet can discard a failed
optional SOP read before returning its result. A packed-header length mismatch
can follow a successful packet iteration and translation of its byte ranges.
Both public decoders propagate the refusing tile's error and stop visiting tiles.

`DiagnosticCodeBlock.reader_messages` gives the exact messages for each
compact or wide Tier-1 reader call. A successful call constructs no message.
A rejected call constructs one fixed string of at most 128 UTF-8 bytes.
The source-range scan stops at its first invalid range, including when the
invalid range is in a later segment. For a block in the visited packet store,
`public_readers` bounds that scan by the original segment and range counts,
and each admitted Tier-1 schedule by 91 compact or 874 wide coding passes.
Component reconstruction can charge the two attempts separately when it retries.

`DiagnosticComponent.public_components` follows the tile’s combined workspace
check and the actual sequence of components before tile colour conversion.
Each component constructs at most two text messages. A compact precision
failure can be discarded when a wide retry succeeds. When a later component
fails, the trace includes its compact and final errors after any earlier
component messages. The tile bound is twice `maxComponents` events. Typed
workspace refusals can stop the tile before its first block reader.

`DiagnosticColour.messages` extends that same component trace through tile
colour conversion. An RCT shape error can format six dimensions. Each axis
is at most 2³², even when the other axis is zero. The combined area of the
first three actual source planes fits the admitted tile-workspace limit.
Colour conversion contributes at most one additional text construction and
preserves the earlier reader visits and retry messages.

`DiagnosticImage.image_diagnostics` covers the public image path after native
decoding succeeds. Mapping, sYCC conversion, upsampling and channel selection
construct at most one diagnostic string in total. A typed refusal retains its
computed value and the corresponding limit. The display checks examine work
samples before decoded bytes. Their respective folds are bounded by
`maxImageArea * maxComponents` and eight times that product, including the
channel that caused a refusal. On a successful image, `interleaver_diagnostics`
also covers independent 8- or 16-bit output limits. A byte refusal stores the
required output size and the interleaver caller's byte ceiling.

`DiagnosticImage.compose_native` extends a native trace to the public image
result under a common scalar bound. A native refusal preserves the exact error
and every earlier message. A native success appends the display trace in order,
so earlier messages from recovered compact errors are still counted.

On a parsed header, `DiagnosticOutput.proposed` bounds both allocation proposals
before either guard runs. The number of cells is at most
`maxComponents * maxImageArea`, and the proposed bytes are at most eight times
that product. A refusing allocator visits zero tiles and both public decoders
return its typed error. Each reached writer uses the destination left by its
predecessors, including the current component on a failed write.

`DiagnosticHeader.headerTrace` orders the complete container, marker, geometry,
coding, pointer and tile-part traces through the final header work check.
`DiagnosticNative.native_events` preserves this prefix and appends the actual
native reconstruction trace only after header success. That suffix uses the
concrete allocator, centred tile-colour callback and destination writer.
Packet records precede their tile’s component retries, colour and placement
events. At an admitted reduction, `native_bounds` bounds both diagnostic
construction work and cumulative temporary storage by
`eventBudget L data.size * Text.workBound (scalarCap L data.size) 128 24`
in the `DiagnosticNative` namespace. The final retained record and the caller’s
oversized reduction have their own bounds.

### Public bounds on every input

`PublicAPI.codestream_resources`, `decode_resources` and `interleaved_resources`
identify the measured result with the production call for every byte array, limit
record and decode option. They bound both work and cumulative logical storage,
including paths that return an error after allocating earlier intermediates.
The native and image results on success carry the `NativeResources.Within` and
`ColorResources.Within` certificates. These give separate bounds on physical
raster bytes, declared output bytes, samples, palette entries and channel views.
The interleaved result carries the exact output byte count for the requested
channel and alpha selection, scaling mode and sample width.

For input length `N` and decode limits `L`, the following formulas use
`PublicAPI` names unless otherwise qualified.

| Entry point | Closed ceiling for either charge |
|---|---|
| `decodeCodestream` | `nativeBudget L N`. Native source budget plus the native event allowance times the work per expression, plus the maximum retained record. |
| `decode` | `budget L N = sourceBudget L N + expressionBudget L N + recordBudget L N`. Source work adds the native, mapping and post-mapping display meters. |
| `decode` followed by `interleaved8` or `interleaved16` with independent limits `B` | `interleavedBudget L B N = budget L N + DisplayPrefix.interleavingBudget L B + 8 + 2 * L.maxImageArea * (L.maxComponents + 2)`. |

The combined image trace allows one display message after all native events.
Its scalar cap is the maximum of the native and display caps. With cap `c`
and combined event count `E`, `expressionBudget` is
`E * Text.workBound c 128 24`, and `recordBudget` is
`max 7 (6 + Text.byteBound c 128 24 + 2 * bits c)`.
`trace_stages` preserves the original sequence of expression trees, including
discarded errors before a successful retry. An excessive caller reduction
builds zero messages and retains seven units, borrowing the caller's natural
number. The measurements end when the API returns, before a caller formats its error.

The common numerical ceiling sums stage-specific logical units. Source charges
cover visits, array headers and references, backing bytes, and operand widths
at the documented stage prices. Diagnostic work prices constructors and copies.
Its storage column sums temporary allocations and the owned error fields. Using
the inclusive source charge in each column conservatively charges an allocation
even if its backing could be reused. Cumulative logical storage includes every
charged allocation that could still be live. Host allocator overhead, wall-clock
time and RSS have separate empirical measurements in the performance phase.

`PublicAPI.allocation_limits` preserves the checked operands and exact first
refusal at public entry, native output allocation and the display grid. Reduction
precedes input length. Once either allocation stage is reached, excess work
samples precede excess declared bytes. The native result precedes metadata and
display validation. `DiagnosticGeometry.geometry_refusal` and `work_refusal`
cover the intermediate header checks. The tag-tree node guard uses the derived
ceiling `4 * maxCodeBlocks` after checking the leaf grid against `maxCodeBlocks`.
The independent interleaver propagates a decoding error with zero additional
charge. After image success it checks the proposed byte count against the
interleaver caller's own `maxDecodedBytes`, including on a zero-sized output.
