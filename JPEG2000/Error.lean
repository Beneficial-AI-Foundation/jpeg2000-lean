/-!
# Structured errors (Plan.md §3 rule 3, §4 S3 and S5)

Every failure of the decoder is a value of `JPEG2000.Error`, never an exception or a panic
(Plan.md §3 rule 1). An error names the pipeline stage that produced it (Plan.md §3, the
stage diagram: Annex I boxes, Annex A markers, Annex B tier-2, Annex C MQ, Annex D tier-1,
Annex E/H quantisation, Annex F DWT, Annex G MCT, assembly and colour) and, where meaningful,
the byte offset in the input. This keeps failures local and visible (S5): a caller can tell
which code-block, packet or tile failed and why.

Resource limits (`JPEG2000.Limits`) are reported as `Error.limitExceeded` with the
`LimitKind` that tripped, the declared value and the bound (S3). The kinds are defined here
so that this module has no project imports; `JPEG2000/Limits.lean` maps each kind to its
field.
-/

namespace JPEG2000

/-- The pipeline stage at which an error arose (Plan.md §3). -/
inductive Stage where
  /-- JP2/JPX box layer (T.800 Annex I). -/
  | box
  /-- Codestream main and tile-part headers (T.800 Annex A). -/
  | marker
  /-- Packet headers, tag trees, progression (T.800 Annex B). -/
  | tier2
  /-- MQ arithmetic decoder (T.800 Annex C). -/
  | mq
  /-- EBCOT bit-plane decoding of a code-block (T.800 Annex D). -/
  | tier1
  /-- Dequantisation and ROI max-shift (T.800 Annex E, H). -/
  | quant
  /-- Inverse discrete wavelet transform (T.800 Annex F). -/
  | dwt
  /-- Inverse multiple-component transform, DC shift, clamp (T.800 Annex G). -/
  | mct
  /-- Assembly of tiles, sub-sampling, palette and channel mapping (T.800 Annex B, I). -/
  | assemble
  /-- Colour specification and conversion (T.800 Annex I). -/
  | color
  /-- The top-level decode entry point (argument checks before any stage runs). -/
  | decode
  deriving Repr, DecidableEq, Inhabited

/-- Short lower-case name of a stage, as printed in error messages. -/
def Stage.toString : Stage → String
  | .box => "box"
  | .marker => "marker"
  | .tier2 => "tier2"
  | .mq => "mq"
  | .tier1 => "tier1"
  | .quant => "quant"
  | .dwt => "dwt"
  | .mct => "mct"
  | .assemble => "assemble"
  | .color => "color"
  | .decode => "decode"

instance : ToString Stage := ⟨Stage.toString⟩

/-- Where an error arose: the stage and, when the error is tied to a position in the input,
the byte offset (from the start of the input given to `decode`). -/
structure Location where
  /-- The stage that reported the error. -/
  stage : Stage
  /-- Byte offset in the input, if meaningful. -/
  offset : Option Nat := none
  deriving Repr, DecidableEq, Inhabited

/-- A location at a stage, with no byte offset. -/
def Location.at (stage : Stage) : Location := { stage }

/-- A location at a stage and byte offset. -/
def Location.atOffset (stage : Stage) (offset : Nat) : Location := { stage, offset := some offset }

/-- Renders a location as `stage` or `stage@offset`. -/
def Location.toString (l : Location) : String :=
  match l.offset with
  | none => l.stage.toString
  | some o => s!"{l.stage}@{o}"

instance : ToString Location := ⟨Location.toString⟩

/-- Which resource limit was exceeded (Plan.md §4 S3). Each kind corresponds to exactly one
field of `JPEG2000.Limits` (see `Limits.bound`). -/
inductive LimitKind where
  /-- Input length in bytes (`Limits.maxInputBytes`). -/
  | inputBytes
  /-- Image width or height (`Limits.maxImageSide`). -/
  | imageSide
  /-- Image area in reference-grid samples (`Limits.maxImageArea`). -/
  | imageArea
  /-- Number of components (`Limits.maxComponents`). -/
  | components
  /-- Number of tiles (`Limits.maxTiles`). -/
  | tiles
  /-- Tile-parts of one tile (`Limits.maxTilePartsPerTile`). -/
  | tilePartsPerTile
  /-- Tile-parts of the whole codestream (`Limits.maxTileParts`). -/
  | tileParts
  /-- Quality layers (`Limits.maxLayers`). -/
  | layers
  /-- Decomposition levels (`Limits.maxDecompLevels`). -/
  | decompLevels
  /-- Code-blocks of the whole image (`Limits.maxCodeBlocks`). -/
  | codeBlocks
  /-- Precincts of the whole image (`Limits.maxPrecincts`). -/
  | precincts
  /-- Packets of the whole image (`Limits.maxPackets`). -/
  | packets
  /-- Coding passes of the whole image (`Limits.maxCodingPasses`). -/
  | codingPasses
  /-- Coding passes of one code-block (`Limits.maxPassesPerCodeBlock`). -/
  | passesPerCodeBlock
  /-- Total decoded output bytes (`Limits.maxDecodedBytes`). -/
  | decodedBytes
  /-- Coefficient/sample working memory in samples (`Limits.maxWorkSamples`). -/
  | workSamples
  /-- Progression-order-change entries (`Limits.maxPocEntries`). -/
  | pocEntries
  /-- Palette entries of a JP2 `pclr` box (`Limits.maxPaletteEntries`). -/
  | paletteEntries
  /-- Number of boxes in a JP2/JPX file (`Limits.maxBoxes`). -/
  | boxes
  /-- Nesting depth of JP2/JPX superboxes (`Limits.maxBoxDepth`). -/
  | boxDepth
  deriving Repr, DecidableEq, Inhabited

/-- Name of a limit kind, as printed in error messages (the `Limits` field without `max`). -/
def LimitKind.toString : LimitKind → String
  | .inputBytes => "inputBytes"
  | .imageSide => "imageSide"
  | .imageArea => "imageArea"
  | .components => "components"
  | .tiles => "tiles"
  | .tilePartsPerTile => "tilePartsPerTile"
  | .tileParts => "tileParts"
  | .layers => "layers"
  | .decompLevels => "decompLevels"
  | .codeBlocks => "codeBlocks"
  | .precincts => "precincts"
  | .packets => "packets"
  | .codingPasses => "codingPasses"
  | .passesPerCodeBlock => "passesPerCodeBlock"
  | .decodedBytes => "decodedBytes"
  | .workSamples => "workSamples"
  | .pocEntries => "pocEntries"
  | .paletteEntries => "paletteEntries"
  | .boxes => "boxes"
  | .boxDepth => "boxDepth"

instance : ToString LimitKind := ⟨LimitKind.toString⟩

/-- Errors produced by the decoder. Every constructor carries a `Location`. -/
inductive Error where
  /-- The input ended before a structure it declares was complete (a box, marker segment,
  tile-part or code-block segment runs past the end of the data). -/
  | truncated (loc : Location) (what : String)
  /-- The input violates T.800 (a reserved value, an inconsistent length, an impossible
  parameter combination). `what` is a short description. -/
  | malformed (loc : Location) (what : String)
  /-- A valid feature that this decoder deliberately leaves out (Plan.md §1). -/
  | unsupported (loc : Location) (what : String)
  /-- A declared or derived quantity `value` exceeds the bound `bound` of the limit `kind`
  (Plan.md §3 rule 3). Reported before anything of that size is allocated. -/
  | limitExceeded (loc : Location) (kind : LimitKind) (value bound : Nat)
  deriving Repr, DecidableEq, Inhabited

namespace Error

/-- The location carried by an error. -/
def loc : Error → Location
  | .truncated l _ | .malformed l _ | .unsupported l _ | .limitExceeded l _ _ _ => l

/-- The stage at which an error arose. -/
def stage (e : Error) : Stage := e.loc.stage

/-- The byte offset of an error, if it has one. -/
def offset? (e : Error) : Option Nat := e.loc.offset

/-- Whether an error is a resource-limit error. Classifies by constructor, never by text. -/
def isLimit : Error → Bool
  | .limitExceeded .. => true
  | _ => false

/-- Whether an error is a truncation. Classifies by constructor, never by text. -/
def isTruncated : Error → Bool
  | .truncated .. => true
  | _ => false

/-- Human-readable rendering: `kind at stage[@offset]: details`. -/
protected def toString : Error → String
  | .truncated l w => s!"truncated at {l}: {w}"
  | .malformed l w => s!"malformed at {l}: {w}"
  | .unsupported l w => s!"unsupported at {l}: {w}"
  | .limitExceeded l k v b => s!"limit exceeded at {l}: {k} = {v} > {b}"

instance : ToString Error := ⟨Error.toString⟩

end Error

end JPEG2000
