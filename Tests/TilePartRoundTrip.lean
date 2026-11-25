import JPEG2000.TilePart
import Encode.TilePart

/-!
# Tests: tile-part marker-segment serialise-then-parse round trip (task 1.10)

Plan.md §4 M1, §5.3, §8; T.800 A.4.2 (SOT), A.7.1 (TLM), A.7.3 (PLT), A.7.4 (PPM),
A.7.5 (PPT). Executable counterpart of `Spec.TilePartRoundTrip`:

* hand-built records: SOT edge values, TLM with every `ST`/`SP`, PLT lengths at every
  7-bit boundary up to `2^32 − 1`, PPM/PPT over a source buffer;
* the 23 T.803 streams: every SOT, TLM, PLT, PPM and PPT segment (main header and every
  tile-part header) is parsed, re-serialised and compared byte for byte with the original
  body, then re-parsed (same record; for PPM/PPT same `Z` and the same data bytes). The
  streams known to carry TLM (p0_03, p0_05, p0_15, p1_03, p1_04), PLT (p0_07), PPM (p1_05)
  and PPT (p1_02, p1_06) must yield at least one segment of that type. Skipped when the
  corpus is absent.
-/

namespace JPEG2000.Tests.TilePartRoundTrip

open JPEG2000 JPEG2000.Bytes JPEG2000.Marker JPEG2000.TilePart JPEG2000.Encode.Marker
  JPEG2000.Encode.TilePart

/-- Runs one named check, printing a line on failure; returns 1 on failure, 0 on success. -/
def expect (name : String) (ok : Bool) : IO Nat := do
  if ok then return 0
  IO.eprintln s!"  FAIL tile-part round trip: {name}"
  return 1

/-- The value of an `Except`, if any. -/
def ok? {ε α : Type} : Except ε α → Option α
  | .ok a => some a
  | .error _ => none

/-- Parses a serialised body with a parser. -/
def reparse {α : Type} (p : Reader → Except Error α) (b : ByteArray) : Option α :=
  ok? (p (Reader.ofByteArray b))

/-- PPM re-parse check: same `Zppm`, range `[1, 1 + length)` holding the same bytes. -/
def ppmOk (src : ByteArray) (p : PPM) : Bool :=
  let b := serializePPM p src
  match reparse parsePPM b with
  | some q => q.zppm == p.zppm && q.body == { offset := 1, length := p.body.length } &&
      q.body.bytes b == p.body.bytes src
  | none => false

/-- PPT re-parse check: same `Zppt`, range `[1, 1 + length)` holding the same bytes. -/
def pptOk (src : ByteArray) (p : PPT) : Bool :=
  let b := serializePPT p src
  match reparse parsePPT b with
  | some q => q.zppt == p.zppt && q.body == { offset := 1, length := p.body.length } &&
      q.body.bytes b == p.body.bytes src
  | none => false

/-! ## Hand-built records -/

/-- SOT unit round trips. -/
def sotUnits : IO Nat := do
  let mut f := 0
  let sots : List SOT :=
    [{ isot := 0, psot := 0, tpsot := 0, tnsot := 0 },
     { isot := 65534, psot := 14, tpsot := 254, tnsot := 255 },
     { isot := 0x1234, psot := 0xFFFFFFFF, tpsot := 3, tnsot := 3 },
     { isot := 7, psot := 0x01020304, tpsot := 9, tnsot := 0 }]
  for s in sots do
    f := f + (← expect s!"SOT {repr s}" (reparse parseSOT (serializeSOT s) == some s))
  let s0 : SOT := { isot := 0x1234, psot := 0x01020304, tpsot := 5, tnsot := 6 }
  f := f + (← expect "SOT bytes" ((serializeSOT s0).toList == [0x12, 0x34, 1, 2, 3, 4, 5, 6]))
  return f

/-- TLM unit round trips for every `ST`/`SP`. -/
def tlmUnits : IO Nat := do
  let L := Limits.default
  let mut f := 0
  for st in [(0 : UInt8), 1, 2] do
    for sp in [false, true] do
      let tile : Nat → Option UInt16 := fun i =>
        if st == 0 then none else if st == 1 then some (255 - i).toUInt16
        else some (65535 - i).toUInt16
      let len : Nat → UInt32 := fun i =>
        if sp then (0xFFFFFFFF - i).toUInt32 else (65535 - i).toUInt32
      let es : Array TlmEntry := (Array.range 5).map fun i => { tile := tile i, length := len i }
      let t : TLM := { ztlm := 9, st, sp, entries := es }
      f := f + (← expect s!"TLM st={st} sp={sp}" (reparse (parseTLM L) (serializeTLM t) == some t))
      f := f + (← expect s!"TLM size st={st} sp={sp}"
        ((serializeTLM t).size == 2 + 5 * (st.toNat + if sp then 4 else 2)))
  let empty : TLM := { ztlm := 0, st := 2, sp := true, entries := #[] }
  f := f + (← expect "TLM empty" (reparse (parseTLM L) (serializeTLM empty) == some empty))
  return f

/-- PLT unit round trips and canonical varint bytes. -/
def pltUnits : IO Nat := do
  let mut f := 0
  let lens : Array Nat := #[0, 1, 127, 128, 129, 16383, 16384, 2097151, 2097152,
    268435455, 268435456, 4294967295]
  let p : PLT := { zplt := 3, lengths := lens }
  f := f + (← expect "PLT boundaries" (reparse parsePLT (serializePLT p) == some p))
  f := f + (← expect "PLT empty" (reparse parsePLT (serializePLT { zplt := 0, lengths := #[] }) ==
    some { zplt := 0, lengths := #[] }))
  f := f + (← expect "varint 0" (encodeVarint 0 == [0]))
  f := f + (← expect "varint 127" (encodeVarint 127 == [0x7F]))
  f := f + (← expect "varint 128" (encodeVarint 128 == [0x81, 0x00]))
  f := f + (← expect "varint 16384" (encodeVarint 16384 == [0x81, 0x80, 0x00]))
  f := f + (← expect "varint 2^32-1" (encodeVarint 4294967295 == [0x8F, 0xFF, 0xFF, 0xFF, 0x7F]))
  return f

/-- PPM/PPT unit round trips over a source buffer. -/
def ppUnits : IO Nat := do
  let src : ByteArray := ⟨#[0xFF, 0x60, 0, 7, 4, 0xAA, 0xBB, 0xCC, 0xDD, 0xEE]⟩
  let mut f := 0
  for (off, len) in [(5, 1), (5, 5), (0, 10), (3, 2)] do
    let rg : ByteRange := { offset := off, length := len }
    f := f + (← expect s!"PPM {off} {len}" (ppmOk src { zppm := 4, body := rg }))
    f := f + (← expect s!"PPT {off} {len}" (pptOk src { zppt := 255, body := rg }))
  return f

/-! ## T.803 streams -/

/-- The 23 T.803 codestreams. -/
def streams : List String :=
  (List.range 16).map (fun i => s!"p0_{if i + 1 < 10 then "0" else ""}{i + 1}") ++
  (List.range 7).map (fun i => s!"p1_0{i + 1}")

/-- Directory of the T.803 conformance files. -/
def corpusDir : System.FilePath := "corpus/files/openjpeg-data/input/conformance"

/-- Streams that must contain a segment of the given type. -/
def required : List (String × UInt16) :=
  [("p0_03", Code.TLM), ("p0_05", Code.TLM), ("p0_15", Code.TLM), ("p1_03", Code.TLM),
   ("p1_04", Code.TLM), ("p0_07", Code.PLT), ("p1_05", Code.PPM), ("p1_02", Code.PPT),
   ("p1_06", Code.PPT)]

/-- Segment counts per type: SOT, TLM, PLT, PPM, PPT. -/
abbrev Counts := Array Nat

/-- Index of a pointer/SOT marker code in `Counts`. -/
def slot (c : UInt16) : Option Nat :=
  if c == Code.SOT then some 0 else if c == Code.TLM then some 1
  else if c == Code.PLT then some 2 else if c == Code.PPM then some 3
  else if c == Code.PPT then some 4 else none

/-- Checks one marker segment of the stream; `none` for other marker types, else whether
it round-trips (bytes identical, re-parse equal). -/
def checkSegment (data : ByteArray) (m : MarkerPos) : Option Bool :=
  let rg : ByteRange := { offset := m.pos + 4, length := m.len - 4 }
  let orig := rg.bytes data
  let sub := ok? (rangeReader data rg)
  match sub with
  | none => some false
  | some r =>
    if m.code == Code.SOT then
      some (match ok? (parseSOT r) with
        | some s => serializeSOT s == orig && reparse parseSOT (serializeSOT s) == some s
        | none => false)
    else if m.code == Code.TLM then
      some (match ok? (parseTLM Limits.default r) with
        | some t => serializeTLM t == orig &&
            reparse (parseTLM Limits.default) (serializeTLM t) == some t
        | none => false)
    else if m.code == Code.PLT then
      some (match ok? (parsePLT r) with
        | some p => serializePLT p == orig && reparse parsePLT (serializePLT p) == some p
        | none => false)
    else if m.code == Code.PPM then
      some (match ok? (parsePPM r) with
        | some p => serializePPM p data == orig && ppmOk data p
        | none => false)
    else if m.code == Code.PPT then
      some (match ok? (parsePPT r) with
        | some p => serializePPT p data == orig && pptOk data p
        | none => false)
    else none

/-- Checks every SOT/TLM/PLT/PPM/PPT of one stream; returns failures and per-type counts. -/
def checkStream (file : String) (data : ByteArray) : IO (Nat × Counts) := do
  let L := Limits.default
  let res := do
    let (mh, r) ← parseMainHeader L (Reader.ofByteArray data)
    let ts ← parseTileParts L mh r
    return (mh, ts)
  match res with
  | .error e => return (← expect s!"{file}: parse {e}" false, #[0, 0, 0, 0, 0])
  | .ok (mh, ts) =>
    let markers := mh.markers ++ (ts.flatMap fun t => t.parts.flatMap (·.markers))
    let mut f := 0
    let mut counts : Counts := #[0, 0, 0, 0, 0]
    for m in markers do
      match checkSegment data m, slot m.code with
      | some ok, some i =>
        counts := counts.modify i (· + 1)
        f := f + (← expect s!"{file}: marker {hex m.code.toNat} at {m.pos}" ok)
      | _, _ => pure ()
    return (f, counts)

/-- Runs the corpus checks; skips absent files. -/
def corpus : IO Nat := do
  let mut f := 0
  let mut checked := 0
  let mut total : Counts := #[0, 0, 0, 0, 0]
  for file in streams do
    let p := corpusDir / (file ++ ".j2k")
    if !(← p.pathExists) then continue
    checked := checked + 1
    let (g, counts) ← checkStream file (← IO.FS.readBinFile p)
    f := f + g
    total := (total.zip counts).map fun (a, b) => a + b
    for (rf, code) in required do
      if rf == file then
        let n := (slot code).bind (counts[·]?) |>.getD 0
        f := f + (← expect s!"{file}: no {hex code.toNat} segment found" (n > 0))
  if checked == 0 then IO.println "  tile-part round trip: corpus absent, skipped"
  else
    IO.println s!"  tile-part round trip: {checked}/{streams.length} streams; SOT {total[0]?.getD 0}, TLM {total[1]?.getD 0}, PLT {total[2]?.getD 0}, PPM {total[3]?.getD 0}, PPT {total[4]?.getD 0} segments byte-identical check"
  return f

/-- Runs all tile-part round-trip tests; returns the number of failures. -/
def run : IO Nat := do
  return (← sotUnits) + (← tlmUnits) + (← pltUnits) + (← ppUnits) + (← corpus)

end JPEG2000.Tests.TilePartRoundTrip
