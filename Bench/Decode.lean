import JPEG2000.Image
import Lean.Data.Json

/-!
# Decoder benchmark (task 8.1): `lake exe bench`

Plan.md §6 (speed targets, measured on the benchmark set), §8.4; `docs/performance.md`
(the OpenJPEG 2.5.3 baseline and the 2x budget).

`lake exe bench [--runs N] [--files a,b,..] [--manifest PATH] [--root DIR]` decodes every
corpus file whose manifest role list contains `benchmark`, `N` times each (default 5, after
one warm-up), and prints one Markdown table row per file with the median wall time (ms, from
`IO.monoNanosNow`, one thread) of

* `decodeCodestream` (planes only),
* `JPEG2000.decode` (colour handling, up-sampling) and `Image.interleaved8`,
* the per-stage split: Tier-2 (packet headers and code-block segments, all tiles, plus the
  header parse), Tier-1 (all code-blocks), dequantisation, inverse DWT, MCT + DC shift +
  clamp, and the remaining glue (layout, plane allocation, copying tiles into the component
  planes);

and the ratio of decode + interleave to the OpenJPEG 1-thread time (`opj1` below; OpenJPEG's
figure includes process start-up and the output write, ours does not).

The stage split is MEASUREMENT-ONLY: `stagedDecode` replicates the pipeline loops of
`JPEG2000.decodeCodestream`, `Assemble.decodeTile` and `Assemble.reconstructTileComp` (read
from `JPEG2000/Decode.lean`, `JPEG2000/Assemble.lean`), calling the same stage functions with
a clock around each call. It does not replace them; the sum of its stages is compared with
the real `decodeCodestream` time in the "sum/cs" sanity column. Files that fail to decode or
are refused by `Limits` get an error row.
-/

namespace JPEG2000.Bench.Decode

open JPEG2000 JPEG2000.Bytes JPEG2000.Marker JPEG2000.Header JPEG2000.TilePart
  JPEG2000.Tier2.Geometry JPEG2000.Tier2.Packet JPEG2000.Assemble

/-- OpenJPEG 2.5.3 `opj_decompress -threads 1` wall times in ms (process start-up, decode and
output write), from `docs/performance.md` "Baseline" (task 0.6). -/
def opj1 : List (String × Nat) :=
  [("p0_07.j2k", 824), ("p0_08.j2k", 402), ("p1_03.j2k", 120), ("zoo1.jp2", 648),
   ("Bretagne2.j2k", 720), ("kodak_2layers_lrcp.j2c", 349), ("123.j2c", 267),
   ("movie_00000.j2k", 73), ("_00042.j2k", 77), ("test_lossless.j2k", 87),
   ("pacs.ge.j2k", 21), ("buxI.j2k", 17), ("issue208.jp2", 47),
   ("issue559-eci-090-CIELab.jp2", 22), ("cthead1.j2k", 4)]

/-- Per-stage nanosecond totals of one staged decode. -/
structure Stages where
  /-- Header parse. -/
  parse : Nat := 0
  /-- Tier-2 packet decoding. -/
  tier2 : Nat := 0
  /-- Tier-1 block decoding. -/
  tier1 : Nat := 0
  /-- Dequantisation into the plane. -/
  dequant : Nat := 0
  /-- Inverse DWT. -/
  dwt : Nat := 0
  /-- Inverse MCT, DC shift and clamp. -/
  mct : Nat := 0
  /-- Everything else: layout, allocation, tile placement. -/
  glue : Nat := 0
  deriving Inhabited

/-- The measurement monad. -/
abbrev M := ExceptT Error IO

/-- Lifts a pure result into `M`. -/
def ex {α : Type} (e : Except Error α) : M α := ExceptT.mk (pure e)

/-- Forces a pure result at this point of the IO sequence (strict call, not inlined). -/
@[noinline] def force {α : Type} (e : Except Error α) : IO (Except Error α) := pure e

/-- Wall time in ns of evaluating the pure computation `f ()` (forced between the two clock
reads), with its result. -/
def timed {α : Type} (f : Unit → Except Error α) : M (α × Nat) := do
  let t0 ← IO.monoNanosNow
  let r ← (force (f ()) : M α)
  let t1 ← IO.monoNanosNow
  return (r, t1 - t0)

/-- Measurement-only replica of `decodeCodestream` (reduce = 0) with per-stage clocks. -/
def stagedDecode (L : Limits) (data : ByteArray) : M Stages := do
  let tStart ← IO.monoNanosNow
  let mut st : Stages := {}
  let (h, d) ← timed fun _ => Header.parse L data
  st := { st with parse := d }
  let s := h.siz
  let (info, planes0) ← ex (Decode.allocOutput L s 0)
  let mut planes := planes0
  let idx ← if h.ppm.segments.isEmpty then pure #[] else ex (Tier2.Headers.ppmChunkIndex L h)
  let mut passes := 0
  let mut j := 0
  for t in [0:numTiles s] do
    let present := match h.tiles[j]? with
      | some tp => if tp.index = t then some tp else none
      | none => none
    let tcb ← match present with
      | some tp => do
        let (x, d) ← timed fun _ => do
          let hs ← Tier2.Headers.headerStreamAt h data tp (idx.getD j #[])
          Tier2.Headers.decodeWithStream L h data tp hs passes
        st := { st with tier2 := st.tier2 + d }
        pure (some x)
      | none => pure none
    if present.isSome then j := j + 1
    if let some x := tcb then passes := passes + x.passes
    -- replica of `Assemble.decodeTile`
    let (g, coding) ← ex (Progression.Layout.ofHeader h t)
    let mct := coding.mctApplies s
    let mut tplanes : Array Plane := #[]
    for c in [0:g.numComps] do
      let tc := g.comp c
      let comp := s.components.getD c default
      let F := fracBitsOf s mct c
      let precs := match tcb with
        | some x => x.comps.getD c #[]
        | none => #[]
      -- replica of `reconstructTileComp`
      let p := tc.params
      let nl := p.levels
      let rect := reduceRect tc.rect 0
      let mut plane ← ex (Plane.zeroChecked L Assemble.loc rect.width rect.height)
      for r in [0:min (nl + 1) precs.size] do
        for prec in precs.getD r #[] do
          for bo in prec.bands do
            for cb in bo.blocks do
              if cb.numPasses != 0 && !rectEmpty cb.geom.rect then
                let (o, d1) ← timed fun _ => decodeBlock data p r bo.band cb
                let ((pl, _), d2) ← timed fun _ => do
                  let q := Spec.Quant.bandQuant p comp.depth.toNat r bo.band
                  Quant.dequantBlock plane rect nl r bo.band cb.geom.rect q F o
                plane := pl
                st := { st with tier1 := st.tier1 + d1, dequant := st.dequant + d2 }
      let (out, d3) ← timed fun _ => if p.transform == .reversible53 then DWT53.idwt53 plane rect nl
        else DWT97.idwt97 plane rect nl
      st := { st with dwt := st.dwt + d3 }
      tplanes := tplanes.push out
    if mct then
      let (pl, d) ← timed fun _ => inverseMct ((g.comp 0).params.transform == .reversible53) tplanes
      tplanes := pl
      st := { st with mct := st.mct + d }
    let mut outs : Array (Rect × Plane) := #[]
    for c in [0:g.numComps] do
      let tc := g.comp c
      let comp := s.components.getD c default
      let rev := tc.params.transform == .reversible53
      let F := if rev then 0 else fracBitsOf s mct c
      let (dc, d) ← timed fun _ => MCT.DcShift.make comp.signed comp.depth.toNat F
      let pl := tplanes.getD c (Plane.zero 0 0)
      tplanes := tplanes.setIfInBounds c (Plane.zero 0 0)
      let (pl, d') ← timed fun _ => pure (if rev then MCT.dcShiftClampRev dc pl
        else MCT.dcShiftClampIrrev dc pl)
      st := { st with mct := st.mct + d + d' }
      outs := outs.push (reduceRect tc.rect 0, pl)
    let tout : TileOut := { tile := t, comps := outs, saturated := 0 }
    planes ← ex (Decode.place info planes tout)
  -- keep `planes` alive so nothing is dropped early
  if planes.size > 1000000 then throw (.malformed Assemble.loc "unreachable")
  let tEnd ← IO.monoNanosNow
  let sum := st.parse + st.tier2 + st.tier1 + st.dequant + st.dwt + st.mct
  return { st with glue := (tEnd - tStart) - sum }

/-- Median of a non-empty list of numbers (upper middle for even length). -/
def median (xs : List Nat) : Nat :=
  let a := xs.toArray.qsort (· < ·)
  a.getD (a.size / 2) 0

/-- Milliseconds with one decimal from ns. -/
def ms (ns : Nat) : String :=
  let t := (ns + 50000) / 100000
  s!"{t / 10}.{t % 10}"

/-- `a / b` with two decimals. -/
def ratio (a b : Nat) : String :=
  if b == 0 then "n/a" else
  let t := (a * 100 + b / 2) / b
  s!"{t / 100}.{if t % 100 < 10 then "0" else ""}{t % 100}"

/-- A decimal string `"4.19"` as hundredths. -/
def hundredths (s : String) : Nat :=
  match s.splitOn "." with
  | [a] => a.toNat!.mul 100
  | [a, b] => a.toNat!.mul 100 + ((b ++ "00").take 2).toNat!
  | _ => 0

/-- One timed pass: `decodeCodestream`, `decode`, `interleaved8` times and the staged split. -/
def onePass (L : Limits) (data : ByteArray) :
    IO (Except Error (Nat × Nat × Nat × Stages)) := do
  let t0 ← IO.monoNanosNow
  match decodeCodestream L data with
  | .error e => return .error e
  | .ok d =>
    let t1 ← IO.monoNanosNow
    -- keep the result observable
    let sz := d.comps.foldl (fun a c => a + c.plane.width) 0
    let t1 := if sz == 0xFFFFFFFFFF then 0 else t1
    let t2 ← IO.monoNanosNow
    match decode L data with
    | .error e => return .error e
    | .ok img =>
      let t3 ← IO.monoNanosNow
      match img.interleaved8 L with
      | .error e => return .error e
      | .ok out =>
        let t4 ← IO.monoNanosNow
        let t4 := if out.size == 0xFFFFFFFFFF then 0 else t4
        match ← (stagedDecode L data).run with
        | .error e => return .error e
        | .ok st => return .ok (t1 - t0, t3 - t2, t4 - t3, st)

/-- One benchmark row (Markdown) or an error row. -/
def benchFile (L : Limits) (runs : Nat) (name mpx path : String) : IO String := do
  let data ← try IO.FS.readBinFile path catch _ =>
    return s!"| {name} | {mpx} | file missing | | | | | | | | | | | | | |"
  match ← onePass L data with   -- warm-up, also the error probe
  | .error e => return s!"| {name} | {mpx} | ERROR: {toString e} | | | | | | | | | | | | | |"
  | .ok _ =>
  let mut rs : Array (Nat × Nat × Nat × Stages) := #[]
  for _ in [0:runs] do
    match ← onePass L data with
    | .ok r => rs := rs.push r
    | .error _ => pure ()
  let l := rs.toList
  let cs := median (l.map (·.1))
  let dec := median (l.map (·.2.1))
  let il := median (l.map (·.2.2.1))
  let sts := l.map (·.2.2.2)
  let st : Stages := {
    parse := median (sts.map (·.parse)), tier2 := median (sts.map (·.tier2)),
    tier1 := median (sts.map (·.tier1)), dequant := median (sts.map (·.dequant)),
    dwt := median (sts.map (·.dwt)), mct := median (sts.map (·.mct)),
    glue := median (sts.map (·.glue)) }
  let total := dec + il
  let sum := st.parse + st.tier2 + st.tier1 + st.dequant + st.dwt + st.mct + st.glue
  let opj := (opj1.lookup name).getD 0
  -- Mpx/s in tenths: mpx100 / 100 / (total / 1e9) * 10
  let rate := hundredths mpx * 100000000 / (max total 1)
  return s!"| {name} | {mpx} | {ms cs} | {ms dec} | {ms il} | {ms total} | {rate / 10}.{rate % 10} | {ms (st.tier2 + st.parse)} | {ms st.tier1} | {ms st.dequant} | {ms st.dwt} | {ms st.mct} | {ms st.glue} | {ratio sum cs} | {opj} | {ratio total (opj * 1000000)} |"

/-- The header line and separator of the table. -/
def tableHeader : String :=
  "| file | Mpx | decodeCodestream ms | decode ms | interleaved8 ms | total ms | Mpx/s | Tier-2 ms | Tier-1 ms | dequant ms | DWT ms | MCT+DC ms | glue ms | sum/cs | OpenJPEG 1-thread ms | total / OpenJPEG |\n|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|"

/-- Entry point. -/
def main (args : List String) : IO UInt32 := do
  let mut runs := 5
  let mut manifest := "corpus/manifest.json"
  let mut root := "corpus/files"
  let mut only : Option (List String) := none
  let mut rest := args
  repeat
    match rest with
    | "--runs" :: n :: t => runs := n.toNat?.getD 5; rest := t
    | "--manifest" :: p :: t => manifest := p; rest := t
    | "--root" :: p :: t => root := p; rest := t
    | "--files" :: f :: t => only := some (f.splitOn ","); rest := t
    | [] => break
    | a :: _ =>
      IO.eprintln s!"bench: unknown argument {a}"
      return 2
  let txt ← IO.FS.readFile manifest
  let some files := (do
      let j ← (Lean.Json.parse txt).toOption
      let fs ← (j.getObjVal? "files").toOption
      (fs.getArr?).toOption) | do IO.eprintln "bench: bad manifest"; return 1
  IO.println tableHeader
  for f in files do
    let roles := ((f.getObjVal? "roles").toOption.bind (·.getArr?.toOption)).getD #[]
    let isBench := roles.any fun r => r.getStr?.toOption == some "benchmark"
    let path := (f.getObjVal? "path" |>.toOption.bind (·.getStr?.toOption)).getD ""
    let name := (path.splitOn "/").getLast?.getD path
    let mpx := (f.getObjVal? "codestream" |>.toOption.bind (·.getObjVal? "megapixels" |>.toOption)
      |>.map (·.compress)).getD "0"
    let wanted := match only with
      | some l => l.contains name
      | none => isBench
    if wanted then
      IO.println (← benchFile {} runs name mpx s!"{root}/{path}")
      (← IO.getStdout).flush
  return 0

end JPEG2000.Bench.Decode

/-- Executable entry point. -/
def main (args : List String) : IO UInt32 := JPEG2000.Bench.Decode.main args
