import JPEG2000.Error
import JPEG2000.Limits

/-!
# Unit tests: `Limits` and `Error` (Plan.md §3 rule 3, §4 S3, S5; task 0.2)

Checks the documented defaults against the T.800 format bounds, the `strict` variant, the
`Limits.check` helper and the rendering and classification of `Error` values.
-/

namespace JPEG2000.Tests.Basic

open JPEG2000

/-- Runs one named check, printing a line on failure; returns 1 on failure, 0 on success. -/
def expect (name : String) (ok : Bool) : IO Nat := do
  if ok then return 0
  IO.eprintln s!"  FAIL basic: {name}"
  return 1

/-- Whether an `Except` is `.ok`. -/
def isOk {ε α : Type} : Except ε α → Bool
  | .ok _ => true
  | .error _ => false

/-- The error of an `Except`, if any (`Except` has no `BEq` instance). -/
def err? {ε α : Type} : Except ε α → Option ε
  | .ok _ => none
  | .error e => some e

/-- All limit kinds, for exhaustive checks. -/
def allKinds : List LimitKind :=
  [.inputBytes, .imageSide, .imageArea, .components, .tiles, .tilePartsPerTile, .tileParts,
   .layers, .decompLevels, .codeBlocks, .precincts, .packets, .codingPasses,
   .passesPerCodeBlock, .decodedBytes, .workSamples, .pocEntries, .paletteEntries, .boxes,
   .boxDepth]

/-- Runs the suite; returns the number of failures. -/
def run : IO Nat := do
  let d := Limits.default
  let s := Limits.strict
  let loc := Location.atOffset .marker 42
  let mut f := 0
  -- documented defaults: T.800 format bounds
  f := f + (← expect "default components = 16384 (Csiz)" (d.maxComponents == 16384))
  f := f + (← expect "default tiles = 65535 (Isot < 65535)" (d.maxTiles == 65535))
  f := f + (← expect "default tile-parts/tile = 255" (d.maxTilePartsPerTile == 255))
  f := f + (← expect "default layers = 65535" (d.maxLayers == 65535))
  f := f + (← expect "default decomposition levels = 32" (d.maxDecompLevels == 32))
  f := f + (← expect "default palette entries = 1024" (d.maxPaletteEntries == 1024))
  -- documented defaults: resource caps
  f := f + (← expect "default image area = 2^28" (d.maxImageArea == 268435456))
  f := f + (← expect "default decoded bytes = 2^30" (d.maxDecodedBytes == 1073741824))
  f := f + (← expect "default input bytes = 2^30" (d.maxInputBytes == 1073741824))
  f := f + (← expect "default = {}" (d == ({} : Limits)))
  -- strict is tighter everywhere and positive
  f := f + (← expect "strict ≤ default for every kind"
    (allKinds.all fun k => s.bound k ≤ d.bound k))
  f := f + (← expect "strict bounds positive" (allKinds.all fun k => 0 < s.bound k))
  f := f + (← expect "strict ≠ default" (s != d))
  -- bound maps kinds to the right fields
  f := f + (← expect "bound components" (d.bound .components == d.maxComponents))
  f := f + (← expect "bound decompLevels" (d.bound .decompLevels == 32))
  f := f + (← expect "bound boxDepth (strict)" (s.bound .boxDepth == 4))
  -- check / checkLe
  f := f + (← expect "check at bound ok" (isOk (d.check loc .components 16384)))
  f := f + (← expect "check below bound ok" (isOk (d.check loc .components 3)))
  f := f + (← expect "check zero ok" (isOk (d.check loc .layers 0)))
  f := f + (← expect "check over bound fails"
    (err? (d.check loc .components 16385) == some (.limitExceeded loc .components 16385 16384)))
  f := f + (← expect "strict rejects 9 levels"
    (err? (s.check loc .decompLevels 9) == some (.limitExceeded loc .decompLevels 9 8)))
  f := f + (← expect "default rejects 33 levels"
    (err? (d.check loc .decompLevels 33) == some (.limitExceeded loc .decompLevels 33 32)))
  f := f + (← expect "checkLe custom bound"
    (err? (Limits.checkLe loc .imageArea 101 100) == some (.limitExceeded loc .imageArea 101 100)
      && isOk (Limits.checkLe loc .imageArea 100 100)))
  -- Error accessors and classification
  let eT := Error.truncated (Location.atOffset .box 7) "jp2c box"
  let eM := Error.malformed (Location.at .tier1) "bad pass count"
  let eU := Error.unsupported (Location.at .color) "ICC profile"
  let eL := Error.limitExceeded loc .tiles 70000 65535
  f := f + (← expect "stage" (eT.stage == .box && eM.stage == .tier1 && eL.stage == .marker))
  f := f + (← expect "offset?" (eT.offset? == some 7 && eM.offset? == none))
  f := f + (← expect "isLimit" (eL.isLimit && !eM.isLimit && !eT.isLimit && !eU.isLimit))
  f := f + (← expect "isTruncated" (eT.isTruncated && !eM.isTruncated))
  f := f + (← expect "DecidableEq distinguishes" (eT != eM && eL == eL))
  -- toString
  f := f + (← expect "toString truncated"
    (toString eT == "truncated at box@7: jp2c box"))
  f := f + (← expect "toString malformed"
    (toString eM == "malformed at tier1: bad pass count"))
  f := f + (← expect "toString unsupported"
    (toString eU == "unsupported at color: ICC profile"))
  f := f + (← expect "toString limit"
    (toString eL == "limit exceeded at marker@42: tiles = 70000 > 65535"))
  return f

end JPEG2000.Tests.Basic
