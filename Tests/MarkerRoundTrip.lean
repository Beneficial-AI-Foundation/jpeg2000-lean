import JPEG2000.Marker
import Encode.Marker

/-!
# Tests: marker-segment serialise-then-parse round trip (task 1.6)

Plan.md §4 M1, §5.3, §8; T.800 Annex A. Executable counterpart of `Spec.MarkerRoundTrip`:

* hand-built records of every segment type (both component-index widths, every
  quantisation style, precincts on/off) are serialised, re-parsed and compared;
* the main headers of the 23 T.803 streams (`p0_*.j2k`, `p1_*.j2k`) are parsed with
  `parseMainHeader`; every SIZ/COD/COC/QCD/QCC/RGN/POC/COM/CRG segment is re-serialised and
  re-parsed (must give the same record) and its bytes compared with the original segment body
  (all these encodings are canonical: the parsers reject non-zero reserved bits and store
  every field raw). Also `segment` against the original marker + `Lxxx` + body. Skipped when
  the corpus is absent.
-/

namespace JPEG2000.Tests.MarkerRoundTrip

open JPEG2000 JPEG2000.Bytes JPEG2000.Marker JPEG2000.Encode.Marker

/-- Runs one named check, printing a line on failure; returns 1 on failure, 0 on success. -/
def expect (name : String) (ok : Bool) : IO Nat := do
  if ok then return 0
  IO.eprintln s!"  FAIL marker round trip: {name}"
  return 1

/-- The value of an `Except`, if any. -/
def ok? {ε α : Type} : Except ε α → Option α
  | .ok a => some a
  | .error _ => none

/-- Parses a serialised body with a parser. -/
def reparse {α : Type} (p : Reader → Except Error α) (b : ByteArray) : Option α :=
  ok? (p (Reader.ofByteArray b))

/-! ## Hand-built records -/

/-- A coding style with or without precincts. -/
def style (prec : Bool) : CodingStyle :=
  { levels := 3, xcb := 4, ycb := 3, cbStyle := 0x3F, transform := .reversible53,
    precincts := if prec then some #[⟨0, 0⟩, ⟨7, 8⟩, ⟨15, 15⟩, ⟨1, 1⟩] else none }

/-- A SIZ with `n` components of varied depth, sign and sub-sampling. -/
def siz (n : Nat) : SIZ :=
  { rsiz := 0x4000, xsiz := 0x12345678, ysiz := 1000, xosiz := 0x12345000, yosiz := 7,
    xtsiz := 0x1000, ytsiz := 0xFFFFFFFF, xtosiz := 0x12344FFF, ytosiz := 0,
    components := (Array.range n).map fun i =>
      { signed := i % 2 == 1, depth := (i % 38 + 1).toUInt8, dx := (i % 255 + 1).toUInt8,
        dy := 255 } }

/-- Unit round trips for every segment type. -/
def units : IO Nat := do
  let L := Limits.default
  let mut f := 0
  for n in [1, 3, 256, 257, 300] do
    f := f + (← expect s!"SIZ n={n}" (reparse (parseSIZ L) (serializeSIZ (siz n)) == some (siz n)))
  for prec in [false, true] do
    for (sop, eph, mct) in [(false, false, false), (true, false, true), (true, true, false)] do
      let c : COD := { sop, eph, progression := .cprl, layers := 0xFFFF, mct,
                       style := style prec }
      f := f + (← expect s!"COD {prec} {sop} {eph}" (reparse (parseCOD L) (serializeCOD c) == some c))
    for csiz in [3, 256, 257, 16384] do
      let c : COC := { component := (csiz - 1).toUInt16, style := style prec }
      f := f + (← expect s!"COC {prec} csiz={csiz}"
        (reparse (parseCOC L csiz) (serializeCOC csiz c) == some c))
  let quants : List Quantization :=
    [.none #[31, 0, 8], .derived ⟨31, 2047⟩, .expounded #[⟨0, 0⟩, ⟨17, 1234⟩, ⟨31, 2047⟩],
     .none (Array.replicate 97 9), .expounded (Array.replicate 97 ⟨5, 5⟩)]
  for q in quants do
    for g in [0, 2, 7] do
      let d : QCD := { guardBits := g, quant := q }
      f := f + (← expect s!"QCD g={g}" (reparse parseQCD (serializeQCD d) == some d))
      for csiz in [1, 257] do
        let c : QCC := { component := (csiz - 1).toUInt16, params := d }
        f := f + (← expect s!"QCC csiz={csiz}"
          (reparse (parseQCC csiz) (serializeQCC csiz c) == some c))
  for csiz in [2, 300] do
    let g : RGN := { component := 1, shift := 37 }
    f := f + (← expect s!"RGN csiz={csiz}" (reparse (parseRGN csiz) (serializeRGN csiz g) == some g))
    let p : POC := { entries := #[
      { resStart := 0, compStart := 0, layerEnd := 1, resEnd := 33, compEndRaw := 0, order := .lrcp },
      { resStart := 32, compStart := 1, layerEnd := 0xFFFF, resEnd := 33, compEndRaw := 2,
        order := .cprl }] }
    f := f + (← expect s!"POC csiz={csiz}" (reparse (parsePOC L csiz) (serializePOC csiz p) == some p))
    let crg : CRG := { offsets := (Array.range csiz).map fun i => (i.toUInt16, (65535 - i).toUInt16) }
    f := f + (← expect s!"CRG csiz={csiz}" (reparse (parseCRG csiz) (serializeCRG crg) == some crg))
  for c in [({ rcom := 1, data := "Kakadu".toUTF8 } : COM), { rcom := 0, data := .empty },
            { rcom := 7, data := ⟨#[0, 255, 0xFF, 0x90]⟩ }] do
    f := f + (← expect "COM" (reparse parseCOM (serializeCOM c) == some c))
  -- segment framing
  let body := serializeCOD { sop := false, eph := false, progression := .lrcp, layers := 1,
                             mct := false, style := style false }
  let seg := segment Code.COD body
  f := f + (← expect "segment framing"
    (seg.toList == [0xFF, 0x52, 0, (body.size + 2).toUInt8] ++ body.toList))
  return f

/-! ## T.803 main headers -/

/-- The 23 T.803 codestreams. -/
def streams : List String :=
  (List.range 16).map (fun i => s!"p0_{if i + 1 < 10 then "0" else ""}{i + 1}.j2k") ++
  (List.range 7).map (fun i => s!"p1_0{i + 1}.j2k")

/-- Directory of the T.803 conformance files. -/
def corpusDir : System.FilePath := "corpus/files/openjpeg-data/input/conformance"

/-- The original body bytes of the marker segment at `m` (after `Lxxx`). -/
def origBody (data : ByteArray) (m : MarkerPos) : ByteArray := data.extract (m.pos + 4) (m.pos + m.len)

/-- Re-serialises one stream's main header, re-parses every segment and compares records and
bytes; returns the number of failures and the number of segments checked. -/
def checkStream (file : String) (data : ByteArray) : IO (Nat × Nat) := do
  let L := Limits.default
  match parseMainHeader L (Reader.ofByteArray data) with
  | .error e => return (← expect s!"{file}: parse {e}" false, 0)
  | .ok (h, _) =>
    let csiz := h.siz.csiz
    let mut f := 0
    let mut n := 0
    -- record round trips
    f := f + (← expect s!"{file} SIZ" (reparse (parseSIZ L) (serializeSIZ h.siz) == some h.siz))
    f := f + (← expect s!"{file} COD" (reparse (parseCOD L) (serializeCOD h.cod) == some h.cod))
    f := f + (← expect s!"{file} QCD" (reparse parseQCD (serializeQCD h.qcd) == some h.qcd))
    for c in h.coc do
      f := f + (← expect s!"{file} COC" (reparse (parseCOC L csiz) (serializeCOC csiz c) == some c))
    for c in h.qcc do
      f := f + (← expect s!"{file} QCC" (reparse (parseQCC csiz) (serializeQCC csiz c) == some c))
    for c in h.rgn do
      f := f + (← expect s!"{file} RGN" (reparse (parseRGN csiz) (serializeRGN csiz c) == some c))
    for c in h.poc do
      f := f + (← expect s!"{file} POC" (reparse (parsePOC L csiz) (serializePOC csiz c) == some c))
    for c in h.com do
      f := f + (← expect s!"{file} COM" (reparse parseCOM (serializeCOM c) == some c))
    if let some c := h.crg then
      f := f + (← expect s!"{file} CRG" (reparse (parseCRG csiz) (serializeCRG c) == some c))
    -- byte identity, matching the marker index against the records in stream order
    let mut iCoc := 0
    let mut iQcc := 0
    let mut iRgn := 0
    let mut iPoc := 0
    let mut iCom := 0
    for m in h.markers do
      let ser : Option ByteArray :=
        if m.code == Code.SIZ then some (serializeSIZ h.siz)
        else if m.code == Code.COD then some (serializeCOD h.cod)
        else if m.code == Code.QCD then some (serializeQCD h.qcd)
        else if m.code == Code.COC then (h.coc[iCoc]?).map (serializeCOC csiz)
        else if m.code == Code.QCC then (h.qcc[iQcc]?).map (serializeQCC csiz)
        else if m.code == Code.RGN then (h.rgn[iRgn]?).map (serializeRGN csiz)
        else if m.code == Code.POC then (h.poc[iPoc]?).map (serializePOC csiz)
        else if m.code == Code.COM then (h.com[iCom]?).map serializeCOM
        else if m.code == Code.CRG then h.crg.map serializeCRG
        else none
      if m.code == Code.COC then iCoc := iCoc + 1
      if m.code == Code.QCC then iQcc := iQcc + 1
      if m.code == Code.RGN then iRgn := iRgn + 1
      if m.code == Code.POC then iPoc := iPoc + 1
      if m.code == Code.COM then iCom := iCom + 1
      match ser with
      | none =>
        let known := [Code.COC, Code.QCC, Code.RGN, Code.POC, Code.COM, Code.CRG]
        if known.contains m.code then
          f := f + (← expect s!"{file} marker {m.code} at {m.pos}: no record" false)
      | some b =>
        n := n + 1
        f := f + (← expect s!"{file} bytes of marker {m.code} at {m.pos}" (b == origBody data m))
        f := f + (← expect s!"{file} segment {m.code} at {m.pos}"
          (segment m.code b == data.extract m.pos (m.pos + m.len)))
    return (f, n)

/-- Runs the corpus checks; skips absent files. -/
def corpus : IO Nat := do
  let mut f := 0
  let mut checked := 0
  let mut segs := 0
  for file in streams do
    let p := corpusDir / file
    if !(← p.pathExists) then continue
    checked := checked + 1
    let (g, n) ← checkStream file (← IO.FS.readBinFile p)
    f := f + g
    segs := segs + n
  if checked == 0 then IO.println "  marker round trip: corpus absent, skipped"
  else
    IO.println s!"  marker round trip: {checked}/{streams.length} streams, {segs} segments byte-identical check"
  return f

/-- Runs all marker round-trip tests; returns the number of failures. -/
def run : IO Nat := do
  return (← units) + (← corpus)

end JPEG2000.Tests.MarkerRoundTrip
