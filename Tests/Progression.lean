import JPEG2000.Progression
import Spec.Progression

/-!
# Tests: progression orders and POC (task 4.3)

Plan.md §4 C5, §8; T.800 B.12.1.1–B.12.1.5, B.12.2.

C5 and fast = spec are proved (`Spec.Progression.c5`, `c5_poc`, `forPackets_eq_spec`); these
tests guard the executable definitions themselves:

* **Sweep** over small tiles with odd offsets, 1–3 components with sub-sampling 1/2/3,
  `NL` 0–3, precinct exponents 0–2 per resolution and 1–2 layers, all five orders: the
  iterator (`forPackets`) equals the point-by-point B.12 scan (`Spec.Progression.packets`),
  has no duplicates, has `Layout.numPackets` elements, every element is in the packet set,
  and `Layout.pw/ph` agree with `Geometry.resolution`. Each case also runs with POC lists
  (overlapping volumes, out-of-range `CEpoc`/`REpoc`/`LYEpoc`, volumes covering nothing):
  iterator = spec, no duplicates, members = packet set ∩ union of the volumes.
* **Corpus**: every tile of every T.803 codestream (`p0_*`, `p1_*`; skipped when absent) with
  `Limits.default`: the layout is `WF`; the sequence has no duplicates, lies in the packet
  set and has `numPackets` elements (POC: as many as packet-set packets in some volume);
  where the tile is small enough (scan work ≤ `JPEG2000_PROGRESSION_SPEC_WORK`, default
  400000) the iterator equals the point-by-point spec. T.803 POC streams: p0_03/p0_15 (every
  tile), p0_07 (one tile), p0_13.
-/

namespace JPEG2000.Tests.Progression

open JPEG2000 JPEG2000.Header JPEG2000.Marker JPEG2000.TilePart JPEG2000.Tier2.Geometry
open JPEG2000.Progression
open JPEG2000.Spec.Progression (packets precAt)

/-- Prints a failure line and returns 1 when `ok` is false. -/
def expect (name : String) (ok : Bool) : IO Nat := do
  if ok then return 0
  IO.eprintln s!"  FAIL progression: {name}"
  return 1

/-- The iterator's sequence, collected. -/
def fastList (g : Layout) (o : Progression) (poc : Array PocEntry) : Array PacketId :=
  Id.run (forPackets (m := Id) g o poc (fun acc p => pure (acc.push p)) #[])

/-- Order key of a packet for duplicate detection. -/
def pkey (p : PacketId) : List Nat := [p.comp, p.res, p.prec, p.layer]

/-- No duplicates (sort, compare neighbours). -/
def noDups (ps : Array PacketId) : Bool :=
  let s := ps.toList.mergeSort (fun a b => decide (pkey a ≤ pkey b))
  (s.zip s.tail).all fun (a, b) => a != b

/-- Whether a packet is in the packet set (decidable `InPacketSet`). -/
def inSet (g : Layout) (p : PacketId) : Bool :=
  p.layer < g.layers && p.comp < g.numComps && p.res ≤ g.levels p.comp &&
    p.prec < g.pw p.comp p.res * g.ph p.comp p.res

/-- Coding parameters: `nl` levels, precinct exponents per resolution (`[]` = 15/15). -/
def mkParams (nl : Nat) (pp : List (Nat × Nat)) : CompParams :=
  { levels := nl, cbWidthExp := 2, cbHeightExp := 2, cbStyle := 0,
    transform := .reversible53, precinctsDefined := !pp.isEmpty,
    precincts := (pp.map fun (a, b) => ({ ppx := a.toUInt8, ppy := b.toUInt8 } : Precinct)).toArray,
    quantStyle := 0, guardBits := 2, steps := #[], roiShift := 0 }

/-- A layout from a tile and per-component `(dx, dy, NL, precinct exponents)`. -/
def mkLayout (tile : Rect) (layers : Nat) (cs : List (Nat × Nat × Nat × List (Nat × Nat))) :
    Layout :=
  { tile, layers, comps := (cs.map fun (dx, dy, nl, pp) =>
      tileComp tile { signed := false, depth := 8, dx := dx.toUInt8, dy := dy.toUInt8 }
        (mkParams nl pp)).toArray }

/-- A POC entry (raw fields). -/
def poc (rs cs le re ce : Nat) (o : Progression) : PocEntry :=
  { resStart := rs.toUInt8, compStart := cs.toUInt16, layerEnd := le.toUInt16,
    resEnd := re.toUInt8, compEndRaw := ce.toUInt16, order := o }

/-- `Layout.pw/ph` agree with `Geometry.resolution` for every component and resolution. -/
def geomAgrees (g : Layout) : Bool :=
  (List.range g.numComps).all fun i =>
    (List.range (g.levels i + 1)).all fun r =>
      match resolution Limits.default (g.comp i) r with
      | .ok res => res.pw == g.pw i r && res.ph == g.ph i r &&
          (List.range res.pw).all (fun px => res.precinctRefX px == g.refX i r px) &&
          (List.range res.ph).all (fun py => res.precinctRefY py == g.refY i r py)
      | .error _ => false

/-- All five orders. -/
def orders : List Progression := [.lrcp, .rlcp, .rpcl, .pcrl, .cprl]

/-- Checks one layout with a POC list (empty = none). -/
def checkCase (name : String) (g : Layout) (pocs : Array PocEntry) : IO Nat := do
  let mut f := 0
  for o in orders do
    let fast := fastList g o pocs
    let spec := packets g o pocs
    let vols := volumes g o pocs
    let expected := (JPEG2000.Spec.Progression.order g .lrcp).filter fun p =>
      vols.any (·.contains p)
    let ok := fast.toList == spec && noDups fast && fast.all (inSet g) &&
      fast.size == expected.length &&
      (!pocs.isEmpty || fast.size == g.numPackets)
    f := f + (← expect s!"{name} {repr o} poc={pocs.size}" ok)
  return f

/-- Component configurations of the sweep. -/
def compSets : List (List (Nat × Nat)) :=
  [[(1, 1)], [(2, 1)], [(1, 1), (2, 2)], [(1, 1), (3, 2)], [(2, 3), (3, 1), (1, 2)],
   [(3, 3), (2, 2), (1, 1)]]

/-- Tiles of the sweep (odd offsets, small and thin). -/
def tiles : List Rect :=
  [⟨0, 0, 8, 8⟩, ⟨1, 2, 14, 11⟩, ⟨5, 3, 12, 7⟩, ⟨3, 7, 4, 13⟩, ⟨7, 5, 23, 19⟩]

/-- Precinct exponents for resolution `r` of component `c`, variant `k`. -/
def ppFor (k c r : Nat) : Nat × Nat :=
  match k with
  | 0 => (15, 15)
  | 1 => (1, 1)
  | 2 => ((r + c) % 3, (r + 2 * c + 1) % 3)
  | _ => (if r = 0 then 0 else 1 + (r + c) % 2, 2 - (r + c) % 3)

/-- The POC lists exercised for a layout with `nc` components. -/
def pocLists (nc : Nat) : List (Array PocEntry) :=
  [#[],
   #[poc 0 0 1 2 nc .rpcl, poc 0 0 2 4 nc .lrcp],
   #[poc 1 0 2 3 1 .pcrl, poc 0 0 1 33 0 .cprl, poc 0 0 3 33 255 .rlcp],
   #[poc 2 (nc - 1) 1 3 nc .cprl, poc 0 0 2 1 nc .rpcl],
   #[poc 0 0 1 1 1 .lrcp]]

/-- The sweep (see module doc). Returns failures and the number of layouts. -/
def sweep : IO (Nat × Nat) := do
  let mut f := 0
  let mut n := 0
  for cs in compSets do
    for tile in tiles do
      for nlv in [0, 1, 2, 3] do
        for k in [0, 1, 2, 3] do
          let comps := cs.zipIdx.map fun ((dx, dy), c) =>
            let nl := (nlv + c) % 4
            (dx, dy, nl, (List.range (nl + 1)).map (ppFor k c))
          let layers := 1 + (nlv + k) % 2
          let g := mkLayout tile layers comps
          n := n + 1
          let name := s!"tile {repr tile} comps {repr comps} L={layers}"
          f := f + (← expect s!"{name}: WF" (decide g.WF))
          f := f + (← expect s!"{name}: geometry" (geomAgrees g))
          for pocs in pocLists cs.length do
            f := f + (← checkCase name g pocs)
  return (f, n)

/-! ## Corpus -/

/-- Directory of the T.803 conformance files. -/
def corpusDir : System.FilePath := "corpus/files/openjpeg-data/input/conformance"

/-- The T.803 codestreams. -/
def corpusFiles : List String :=
  ((List.range 16).map fun i => s!"p0_{if i + 1 < 10 then "0" else ""}{i + 1}.j2k") ++
  ((List.range 7).map fun i => s!"p1_0{i + 1}.j2k")

/-- Checks every tile of every T.803 codestream; skipped when absent. -/
def corpus : IO Nat := do
  let maxWork := ((← IO.getEnv "JPEG2000_PROGRESSION_SPEC_WORK").bind String.toNat?).getD 400000
  let mut f := 0
  let mut seen := 0
  let mut total := 0
  for file in corpusFiles do
    let path := corpusDir / file
    if !(← path.pathExists) then continue
    seen := seen + 1
    let data ← IO.FS.readBinFile path
    match parse Limits.default data with
    | .error e => f := f + (← expect s!"{file}: {e}" false)
    | .ok h =>
      let mut pocTiles := 0
      let mut specChecked := 0
      for t in [0:numTiles h.siz] do
        match Layout.ofHeader h t with
        | .error e => f := f + (← expect s!"{file} t={t}: {e}" false)
        | .ok (g, c) =>
          let name := s!"{file} t={t}"
          f := f + (← expect s!"{name}: WF" (decide g.WF))
          let fast := fastList g c.progression c.poc
          total := total + fast.size
          let vols := volumes g c.progression c.poc
          let expected := if c.poc.isEmpty then g.numPackets else
            ((JPEG2000.Spec.Progression.order g .lrcp).filter fun p =>
              vols.any (·.contains p)).length
          if !c.poc.isEmpty then pocTiles := pocTiles + 1
          f := f + (← expect s!"{name}: count {fast.size} vs {expected}"
            (fast.size == expected))
          f := f + (← expect s!"{name}: no duplicates" (noDups fast))
          f := f + (← expect s!"{name}: in packet set" (fast.all (inSet g)))
          let work := g.tile.width * g.tile.height * (g.maxLevels + 1) * g.numComps *
            (vols.length)
          if work ≤ maxWork then
            specChecked := specChecked + 1
            f := f + (← expect s!"{name}: fast = spec"
              (fast.toList == packets g c.progression c.poc))
      IO.println s!"  progression: {file} {repr h.defaults.progression} tiles={numTiles h.siz} poc-tiles={pocTiles} spec-checked={specChecked}"
  if seen == 0 then IO.println "  progression: corpus absent, skipped"
  else IO.println s!"  progression: corpus {seen} files, {total} packets"
  return f

/-- Runs the suite; returns the number of failures. -/
def run : IO Nat := do
  let (f1, n) ← sweep
  IO.println s!"  progression: sweep {n} layouts × 5 orders × {(pocLists 1).length} POC lists"
  return f1 + (← corpus)

end JPEG2000.Tests.Progression
