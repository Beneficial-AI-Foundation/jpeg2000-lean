import JPEG2000.Error

/-!
# Resource limits (Plan.md §3 rule 3, §4 S3, §9)

Every stage takes an explicit `Limits` value. Every size the stream declares (T.800 Annex A
marker fields, Annex I box lengths) and every count derived from it (tiles, code-blocks,
packets, coding passes) is checked against the matching field **before** anything of that
size is allocated or iterated; excess yields `Error.limitExceeded` (via `Limits.check`). The
fields also justify the fuel of the decoder's loops (Plan.md §3 rule 2).

Two kinds of field:

* **Format bounds** (`maxComponents`, `maxTiles`, `maxTilePartsPerTile`, `maxLayers`,
  `maxDecompLevels`, `maxPaletteEntries`): the default is the largest value T.800 permits,
  so the default limits reject no conforming stream on these grounds; a caller may tighten
  them.
* **Resource caps** (`maxInputBytes`, `maxImageSide`, `maxImageArea`, `maxDecodedBytes`,
  `maxWorkSamples`, `maxCodeBlocks`, `maxPrecincts`, `maxPackets`, `maxCodingPasses`, …):
  chosen for an embedded decoder in a PDF viewer (Plan.md §9: safe-pdf's `maxImagePixels`
  and `maxDecodedTotalBytes` map onto `maxImageArea` and `maxDecodedBytes`).

`Limits.strict` is a tight variant for fuzzing and tests.
-/

namespace JPEG2000

/-- Explicit resource limits for the decoder (Plan.md §4 S3). Sizes are in bytes, areas and
work in samples, counts in items. -/
structure Limits where
  /-- Maximum input length in bytes (the JP2 file or raw codestream). Default 2³⁰ (1 GiB),
  as safe-pdf's `maxInputBytes`. -/
  maxInputBytes : Nat := 1 <<< 30
  /-- Maximum image width and height (`Xsiz − XOsiz`, `Ysiz − YOsiz`, T.800 A.5.1) in
  reference-grid samples. T.800 allows up to 2³² − 1; default 2¹⁷ = 131072, ample for scans
  at 600 dpi of A0 sheets while keeping per-row quantities small. -/
  maxImageSide : Nat := 1 <<< 17
  /-- Maximum image area (width × height on the reference grid). Default 2²⁸ (268 M samples,
  16384²), equal to safe-pdf's `maxImagePixels` (Plan.md §9). -/
  maxImageArea : Nat := 1 <<< 28
  /-- Maximum number of components (`Csiz`, T.800 A.5.1: 1 ≤ Csiz ≤ 16384). Default 16384,
  the format bound; memory is bounded separately by `maxDecodedBytes` and
  `maxWorkSamples`. -/
  maxComponents : Nat := 16384
  /-- Maximum number of tiles. T.800 A.4.2: the tile index `Isot` is in 0…65534, so a
  codestream has at most 65535 tiles. Default 65535, the format bound. -/
  maxTiles : Nat := 65535
  /-- Maximum number of tile-parts of one tile. T.800 A.4.2: `TPsot` is in 0…254 and
  `TNsot` ≤ 255. Default 255, the format bound. -/
  maxTilePartsPerTile : Nat := 255
  /-- Maximum number of tile-parts in the whole codestream. The format bound is
  65535 × 255; default 2¹⁸ = 262144, bounding the per-tile-part bookkeeping. -/
  maxTileParts : Nat := 1 <<< 18
  /-- Maximum number of quality layers (`SGcod` layers field, T.800 A.6.1, Table A.14:
  1…65535). Default 65535, the format bound; the work is bounded by `maxPackets`. -/
  maxLayers : Nat := 65535
  /-- Maximum number of decomposition levels (`SPcod`/`SPcoc` field, T.800 A.6.1,
  Table A.15: 0…32, i.e. up to 33 resolution levels). Default 32, the format bound. -/
  maxDecompLevels : Nat := 32
  /-- Maximum number of code-blocks in the whole image (all tiles, components, resolutions,
  sub-bands). Code-blocks are at least 4×4 (T.800 A.6.1, `xcb`, `ycb` ≥ 2), so a
  2²⁸-sample image could have 2²⁴ per component; default 2²², i.e. 64×64 blocks over
  2²⁸ samples, which real encoders do not exceed. -/
  maxCodeBlocks : Nat := 1 <<< 22
  /-- Maximum number of precincts in the whole image (T.800 B.6). Default 2²², as
  `maxCodeBlocks` (a non-empty precinct holds at least one code-block). -/
  maxPrecincts : Nat := 1 <<< 22
  /-- Maximum number of packets in the whole image (layers × resolutions × components ×
  precincts, T.800 B.9). Default 2²⁴; bounds the tier-2 work and the progression iteration
  (theorem C5's packet set). -/
  maxPackets : Nat := 1 <<< 24
  /-- Maximum number of coding passes over all code-blocks (T.800 B.10.6, D.3). Default 2²⁶
  (on average 16 passes per code-block at `maxCodeBlocks`); bounds the total tier-1 work. -/
  maxCodingPasses : Nat := 1 <<< 26
  /-- Maximum number of coding passes of one code-block. Without ROI a code-block has at
  most `3·Mb − 2` passes with `Mb = G + εb − 1 ≤ 7 + 31 − 1 = 37` (T.800 E.1), i.e. 109;
  ROI max-shift (Annex H) adds bit-planes. Default 255, a generous bound that also fits the
  pass counter in a byte. -/
  maxPassesPerCodeBlock : Nat := 255
  /-- Maximum total size in bytes of the decoded output (all component planes at their
  output sample width: 1 byte up to 8 bits, 2 bytes up to 16). Default 2³⁰ (1 GiB), equal
  to safe-pdf's `maxDecodedTotalBytes` (Plan.md §9). -/
  maxDecodedBytes : Nat := 1 <<< 30
  /-- Maximum number of coefficient/sample cells held at once in working buffers (tier-1
  output, DWT and MCT planes). Default 2²⁸ (1 GiB at 32-bit cells); bounds the
  intermediate allocation of S3. -/
  maxWorkSamples : Nat := 1 <<< 28
  /-- Maximum number of progression-order-change entries over all `POC` markers (T.800
  A.6.6). Default 4096 (one `POC` segment holds at most 7281; real streams use a few). -/
  maxPocEntries : Nat := 4096
  /-- Maximum number of palette entries of a JP2 `pclr` box (T.800 I.5.3.4: NE is
  1…1024). Default 1024, the format bound. -/
  maxPaletteEntries : Nat := 1024
  /-- Maximum number of boxes read from a JP2/JPX file (T.800 Annex I). Default 4096 (a JP2
  file has about ten; metadata boxes such as `xml ` and `uuid` add a few). -/
  maxBoxes : Nat := 4096
  /-- Maximum nesting depth of superboxes (`jp2h`, `res `, `uinf`, …; T.800 I.4). Default
  8 (JP2 nests at most 2–3 deep). -/
  maxBoxDepth : Nat := 8
  deriving Repr, DecidableEq, Inhabited

namespace Limits

/-- The default limits (each field's default; see the field docstrings). -/
def default : Limits := {}

/-- Tight limits for fuzzing and tests: small images (1024² samples, 2²² output bytes), few
components, tiles, layers and levels, so that a fuzzer explores structure rather than
spending time on large allocations. Every value is ≤ the corresponding `default` value. -/
def strict : Limits where
  maxInputBytes := 1 <<< 22
  maxImageSide := 4096
  maxImageArea := 1 <<< 20
  maxComponents := 4
  maxTiles := 256
  maxTilePartsPerTile := 16
  maxTileParts := 1024
  maxLayers := 16
  maxDecompLevels := 8
  maxCodeBlocks := 1 <<< 14
  maxPrecincts := 1 <<< 14
  maxPackets := 1 <<< 16
  maxCodingPasses := 1 <<< 18
  maxPassesPerCodeBlock := 128
  maxDecodedBytes := 1 <<< 22
  maxWorkSamples := 1 <<< 22
  maxPocEntries := 32
  maxPaletteEntries := 256
  maxBoxes := 64
  maxBoxDepth := 4

/-- The bound a `Limits` value sets for a limit kind (the field named by the kind). -/
def bound (L : Limits) : LimitKind → Nat
  | .inputBytes => L.maxInputBytes
  | .imageSide => L.maxImageSide
  | .imageArea => L.maxImageArea
  | .components => L.maxComponents
  | .tiles => L.maxTiles
  | .tilePartsPerTile => L.maxTilePartsPerTile
  | .tileParts => L.maxTileParts
  | .layers => L.maxLayers
  | .decompLevels => L.maxDecompLevels
  | .codeBlocks => L.maxCodeBlocks
  | .precincts => L.maxPrecincts
  | .packets => L.maxPackets
  | .codingPasses => L.maxCodingPasses
  | .passesPerCodeBlock => L.maxPassesPerCodeBlock
  | .decodedBytes => L.maxDecodedBytes
  | .workSamples => L.maxWorkSamples
  | .pocEntries => L.maxPocEntries
  | .paletteEntries => L.maxPaletteEntries
  | .boxes => L.maxBoxes
  | .boxDepth => L.maxBoxDepth

/-- Checks `value ≤ bound`; otherwise `Error.limitExceeded loc kind value bound`. The
general form, for bounds computed from several fields. -/
def checkLe (loc : Location) (kind : LimitKind) (value bound : Nat) : Except Error Unit :=
  if value ≤ bound then .ok () else .error (.limitExceeded loc kind value bound)

/-- Checks `value ≤ L.bound kind` (Plan.md §3 rule 3); otherwise
`Error.limitExceeded loc kind value (L.bound kind)`. -/
def check (L : Limits) (loc : Location) (kind : LimitKind) (value : Nat) : Except Error Unit :=
  checkLe loc kind value (L.bound kind)

/-- `checkLe` succeeds exactly when the value is within the bound. -/
theorem checkLe_eq_ok_iff (loc : Location) (kind : LimitKind) (value bound : Nat) :
    checkLe loc kind value bound = .ok () ↔ value ≤ bound := by
  unfold checkLe
  by_cases h : value ≤ bound <;> simp [h]

/-- `check` succeeds exactly when the value is within the limit's bound. -/
theorem check_eq_ok_iff (L : Limits) (loc : Location) (kind : LimitKind) (value : Nat) :
    L.check loc kind value = .ok () ↔ value ≤ L.bound kind :=
  checkLe_eq_ok_iff loc kind value (L.bound kind)

/-- When `checkLe` fails, it fails with the `limitExceeded` error for that kind, value and
bound, and the value exceeds the bound. -/
theorem checkLe_eq_error {loc : Location} {kind : LimitKind} {value bound : Nat} {e : Error}
    (h : checkLe loc kind value bound = .error e) :
    e = .limitExceeded loc kind value bound ∧ bound < value := by
  unfold checkLe at h
  by_cases hv : value ≤ bound
  · simp [hv] at h
  · simp [hv] at h
    exact ⟨h.symm, Nat.lt_of_not_le hv⟩

/-- Every bound of `strict` is at most the corresponding bound of `default`. -/
theorem strict_le_default (k : LimitKind) : strict.bound k ≤ default.bound k := by
  cases k <;> decide

end Limits

end JPEG2000
