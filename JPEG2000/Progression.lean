import JPEG2000.Tier2.Geometry

/-!
# Progression orders and POC as explicit iterators
(Plan.md §3 rules 1–3, §4 C5, §5.2 "Tier-2"; T.800 B.9, B.12.1.1–B.12.1.5, B.12.2, A.6.6)

Task 4.3. A tile's packets are identified by `PacketId = (layer, resolution, component,
precinct)` (B.9); the packet set of a tile is every `(l, r, i, k)` with `l < L`, `i < Csiz`,
`r ≤ NL_i` and `k < numprecincts(i, r)` (B-16, `Layout.InPacketSet`). This module produces
the packet sequence of a tile **lazily** as a monadic fold (`forPackets`): the packet
decoder (4.4) consumes each packet as it is produced and nothing of the size of the packet
set is materialised.

* **Volumes.** Every progression is iterated as a *progression volume* (B.12.2):
  layers `[0, LYEpoc)`, resolutions `[RSpoc, REpoc)`, components `[CSpoc, CEpoc)` and an
  order. Without POC the tile has one volume covering everything (`Volume.full`); with POC
  the volumes are the POC entries in stream order (tile POC replaces main POC,
  `Header.Coding.poc`). Bounds are clamped as OpenJPEG (`opj_pi_create_decode`,
  `opj_pi_update_decode_poc`): `LYEpoc` to `L`, `CEpoc` to `Csiz`, and resolutions above a
  component's `NL_i` are skipped.
* **Layer/resolution-driven orders** (B.12.1.1 LRCP, B.12.1.2 RLCP) are nested loops
  (`forRange`, structurally recursive, no list allocated).
* **Position-driven orders** (B.12.1.3 RPCL, B.12.1.4 PCRL, B.12.1.5 CPRL). T.800 scans every
  reference-grid point `(x, y)` of the tile and visits, for each component and resolution,
  the precinct "at" that point when the B.12.1.3 divisibility condition holds. Each precinct
  is visited exactly once, at its reference position `(refX, refY)` (Geometry module doc,
  `Spec.Progression` proves it). Scanning the tile point by point is far too slow, and
  OpenJPEG's shortcut (stepping by the minimum precinct step over components/resolutions)
  can skip positions when sub-sampling factors are not powers of two of each other. Instead
  this module lists the precincts of the volume, tags each with its order key
  (RPCL `(r, y, x, i, k)`, PCRL `(y, x, i, r, k)`, CPRL `(i, y, x, r, k)` with `(x, y)` its
  reference position) and sorts them (`List.mergeSort`, `O(P log P)` for `P` precincts of
  the tile, bounded by `Limits.maxPrecincts` through `Header.checkWork`); the layers are the
  innermost loop. `Spec.Progression.forVolume_eq_spec` proves that this is exactly the
  point-by-point scan of T.800.
* **POC "already sent".** A packet is emitted at its first occurrence only (B.12.2: packets
  already sent by an earlier volume are skipped; OpenJPEG's `pi->include`). Volume `j`
  skips a packet that lies in one of the volumes `0 … j − 1` (`Volume.contains`): every
  packet of the packet set in an earlier volume has been emitted by that volume. Packets in
  no volume are never emitted (OpenJPEG iterates only the POC volumes).

Work: the iteration visits `Σ_j |volume_j ∩ packet set|` packets and checks each against at
most `j` earlier volumes; `iterationWork` computes that total so the caller can bound it
against `Limits` before iterating (the packet count itself is bounded by
`Header.checkWork`, the number of POC entries by `Limits.maxPocEntries`).
-/

namespace JPEG2000.Progression

open JPEG2000 JPEG2000.Header JPEG2000.Marker JPEG2000.TilePart JPEG2000.Tier2.Geometry

/-- A packet of a tile (B.9): layer `l`, resolution `r`, component `i`, precinct `k`
(raster index `py · pw + px` within the resolution). -/
structure PacketId where
  /-- Quality layer. -/
  layer : Nat
  /-- Resolution level (0 = lowest). -/
  res : Nat
  /-- Component index. -/
  comp : Nat
  /-- Precinct index within the resolution. -/
  prec : Nat
  deriving Repr, DecidableEq, Inhabited

/-- A precinct of a tile: component, resolution, precinct index. -/
structure PrecRef where
  /-- Component index. -/
  comp : Nat
  /-- Resolution level. -/
  res : Nat
  /-- Precinct index within the resolution. -/
  prec : Nat
  deriving Repr, DecidableEq, Inhabited

/-- The packet of a precinct in layer `l`. -/
def PrecRef.packet (e : PrecRef) (l : Nat) : PacketId := ⟨l, e.res, e.comp, e.prec⟩

/-- The geometry a tile's progression depends on: the tile rectangle on the reference grid,
the number of layers and one `TileCompGeom` per component (whose `rect` is the
tile-component rectangle of B-12). -/
structure Layout where
  /-- The tile on the reference grid. -/
  tile : Rect
  /-- Number of quality layers `L`. -/
  layers : Nat
  /-- Per-component geometry, `Csiz` entries. -/
  comps : Array TileCompGeom
  deriving Repr, Inhabited

namespace Layout

/-- Number of components. -/
def numComps (g : Layout) : Nat := g.comps.size

/-- Component `i` (a default value out of range). -/
def comp (g : Layout) (i : Nat) : TileCompGeom := g.comps.getD i default

/-- `NL_i`. -/
def levels (g : Layout) (i : Nat) : Nat := (g.comp i).params.levels

/-- `Nmax = max_i NL_i` (0 without components). -/
def maxLevels (g : Layout) : Nat := (g.comps.toList.map (·.params.levels)).foldr max 0

/-- The rectangle of resolution `r` of component `i` (B-14). -/
def resRect (g : Layout) (i r : Nat) : Rect := Header.resRect (g.comp i).rect (g.levels i) r

/-- Precinct width exponent `PPx` of resolution `r` of component `i` (15 by default). -/
def ppx (g : Layout) (i r : Nat) : Nat :=
  ((g.comp i).params.precincts.getD r Precinct.default).ppx.toNat

/-- Precinct height exponent `PPy`. -/
def ppy (g : Layout) (i r : Nat) : Nat :=
  ((g.comp i).params.precincts.getD r Precinct.default).ppy.toNat

/-- Number of precincts across (B-16; 0 for an empty resolution). Same formula as
`Geometry.resolution`. -/
def pw (g : Layout) (i r : Nat) : Nat :=
  gridCount (g.resRect i r).x0 (g.resRect i r).x1 (g.ppx i r)

/-- Number of precincts down. -/
def ph (g : Layout) (i r : Nat) : Nat :=
  gridCount (g.resRect i r).y0 (g.resRect i r).y1 (g.ppy i r)

/-- `numprecincts(i, r)`, 0 when `r > NL_i`. -/
def numPrecincts (g : Layout) (i r : Nat) : Nat :=
  if r ≤ g.levels i then g.pw i r * g.ph i r else 0

/-- Reference-grid `x` at which the position-driven orders visit precinct column `px` of
resolution `r` of component `i`: `max(tx0, XRsiz · 2^(PPx + NL − r) · (⌊trx0/2^PPx⌋ + px))`
(as `Geometry.ResolutionGeom.precinctRefX`). -/
def refX (g : Layout) (i r px : Nat) : Nat :=
  let p := g.ppx i r
  max g.tile.x0 ((g.comp i).dx * 2 ^ (p + (g.levels i - r)) * ((g.resRect i r).x0 / 2 ^ p + px))

/-- Reference-grid `y` of precinct row `py`. -/
def refY (g : Layout) (i r py : Nat) : Nat :=
  let p := g.ppy i r
  max g.tile.y0 ((g.comp i).dy * 2 ^ (p + (g.levels i - r)) * ((g.resRect i r).y0 / 2 ^ p + py))

/-- The packet set of the tile (B.9): `l < L`, `i < Csiz`, `r ≤ NL_i`,
`k < numprecincts(i, r)`. -/
def InPacketSet (g : Layout) (p : PacketId) : Prop :=
  p.layer < g.layers ∧ p.comp < g.numComps ∧ p.res ≤ g.levels p.comp ∧
    p.prec < g.pw p.comp p.res * g.ph p.comp p.res

/-- Number of packets of the tile, `L · Σ_i Σ_{r ≤ NL_i} numprecincts(i, r)`. -/
def numPackets (g : Layout) : Nat :=
  g.layers * (List.range g.numComps).foldl (fun a i =>
    (List.range (g.levels i + 1)).foldl (fun a r => a + g.numPrecincts i r) a) 0

/-- Well-formedness assumed by the position-driven orders: every component has non-zero
sub-sampling and its rectangle is the tile-component rectangle of B-12
(`tcx0 = ⌈tx0 / XRsiz⌉` …). `Geometry.tileComp` builds exactly this. -/
def WF (g : Layout) : Prop :=
  ∀ i, i < g.numComps →
    1 ≤ (g.comp i).dx ∧ 1 ≤ (g.comp i).dy ∧
    (g.comp i).rect = { x0 := cdiv g.tile.x0 (g.comp i).dx, y0 := cdiv g.tile.y0 (g.comp i).dy,
                        x1 := cdiv g.tile.x1 (g.comp i).dx, y1 := cdiv g.tile.y1 (g.comp i).dy }

instance (g : Layout) : Decidable g.WF := by unfold WF; infer_instance

/-- The layout of tile `t` of a parsed header (`Geometry.ofHeader` per component) and the
tile's merged coding parameters. -/
def ofHeader (h : Header) (t : Nat) : Except Error (Layout × Coding) := do
  if t ≥ numTiles h.siz then throw (.malformed loc s!"tile index {t} out of range")
  let coding := match h.tiles.find? (·.index == t) with
    | some tp => tp.coding
    | none => h.defaults
  let comps ← (Array.range h.siz.csiz).mapM fun c => Tier2.Geometry.ofHeader h t c
  return ({ tile := tileRect h.siz t, layers := coding.layers, comps }, coding)

end Layout

/-! ## Volumes -/

/-- A progression volume (B.12.2): layers `[0, layerEnd)`, resolutions
`[resStart, resEnd)`, components `[compStart, compEnd)`, iterated in `order`. -/
structure Volume where
  /-- Layer end (exclusive), `LYEpoc`. -/
  layerEnd : Nat
  /-- Resolution start, `RSpoc`. -/
  resStart : Nat
  /-- Resolution end (exclusive), `REpoc`. -/
  resEnd : Nat
  /-- Component start, `CSpoc`. -/
  compStart : Nat
  /-- Component end (exclusive), `CEpoc`. -/
  compEnd : Nat
  /-- Progression order `Ppoc`. -/
  order : Progression
  deriving Repr, DecidableEq, Inhabited

/-- The single volume of a tile without POC: every packet, in the COD progression order. -/
def Volume.full (g : Layout) (o : Progression) : Volume :=
  { layerEnd := g.layers, resStart := 0, resEnd := g.maxLevels + 1, compStart := 0,
    compEnd := g.numComps, order := o }

/-- The volume of a POC entry (`CEpoc = 0` read as 256/16384, `PocEntry.compEnd`). -/
def Volume.ofPoc (csiz : Nat) (e : PocEntry) : Volume :=
  { layerEnd := e.layerEnd.toNat, resStart := e.resStart.toNat, resEnd := e.resEnd.toNat,
    compStart := e.compStart.toNat, compEnd := e.compEnd csiz, order := e.order }

/-- Whether a packet lies in a volume. -/
def Volume.InVolume (v : Volume) (p : PacketId) : Prop :=
  p.layer < v.layerEnd ∧ v.resStart ≤ p.res ∧ p.res < v.resEnd ∧ v.compStart ≤ p.comp ∧
    p.comp < v.compEnd

instance (v : Volume) (p : PacketId) : Decidable (v.InVolume p) := by
  unfold Volume.InVolume; infer_instance

/-- `InVolume` as a `Bool`. -/
def Volume.contains (v : Volume) (p : PacketId) : Bool := decide (v.InVolume p)

/-- Clamped layer end `min(LYEpoc, L)`. -/
def Volume.le (g : Layout) (v : Volume) : Nat := min v.layerEnd g.layers
/-- Clamped resolution end `min(REpoc, Nmax + 1)`. -/
def Volume.re (g : Layout) (v : Volume) : Nat := min v.resEnd (g.maxLevels + 1)
/-- Clamped component end `min(CEpoc, Csiz)`. -/
def Volume.ce (g : Layout) (v : Volume) : Nat := min v.compEnd g.numComps

/-- The volumes of a tile: the POC entries if any, else the single full volume. -/
def volumes (g : Layout) (order : Progression) (poc : Array PocEntry) : List Volume :=
  if poc.isEmpty then [Volume.full g order] else poc.toList.map (Volume.ofPoc g.numComps)

/-! ## Iteration -/

section
variable {m : Type → Type} [Monad m] {β : Type}

/-- `f` folded over `s, s+1, …, s+n−1` (structural recursion on `n`, no list built). -/
@[specialize] def forRange (s n : Nat) (f : β → Nat → m β) (b : β) : m β :=
  match n with
  | 0 => pure b
  | n + 1 => do
    let b ← f b s
    forRange (s + 1) n f b

/-- B.12.1.1 LRCP over a volume: `l`, `r`, `i`, `k`. -/
def forLRCP (g : Layout) (v : Volume) (f : β → PacketId → m β) (b : β) : m β :=
  forRange 0 (v.le g) (fun b l =>
    forRange v.resStart (v.re g - v.resStart) (fun b r =>
      forRange v.compStart (v.ce g - v.compStart) (fun b i =>
        forRange 0 (g.numPrecincts i r) (fun b k => f b ⟨l, r, i, k⟩) b) b) b) b

/-- B.12.1.2 RLCP over a volume: `r`, `l`, `i`, `k`. -/
def forRLCP (g : Layout) (v : Volume) (f : β → PacketId → m β) (b : β) : m β :=
  forRange v.resStart (v.re g - v.resStart) (fun b r =>
    forRange 0 (v.le g) (fun b l =>
      forRange v.compStart (v.ce g - v.compStart) (fun b i =>
        forRange 0 (g.numPrecincts i r) (fun b k => f b ⟨l, r, i, k⟩) b) b) b) b

/-- The precincts of a volume (components, then resolutions, then precinct index). -/
def precRefs (g : Layout) (v : Volume) : List PrecRef :=
  (List.range' v.compStart (v.ce g - v.compStart)).flatMap fun i =>
    (List.range' v.resStart (v.re g - v.resStart)).flatMap fun r =>
      (List.range (g.numPrecincts i r)).map fun k => ⟨i, r, k⟩

/-- The order key of a precinct for a position-driven order, with `(x, y)` its
reference-grid position: RPCL `(r, y, x, i, k)`, PCRL `(y, x, i, r, k)`, CPRL
`(i, y, x, r, k)` (lexicographic). -/
def posKey (g : Layout) (o : Progression) (e : PrecRef) : List Nat :=
  let pw := g.pw e.comp e.res
  let x := g.refX e.comp e.res (e.prec % pw)
  let y := g.refY e.comp e.res (e.prec / pw)
  match o with
  | .rpcl => [e.res, y, x, e.comp, e.prec]
  | .pcrl => [y, x, e.comp, e.res, e.prec]
  | _ => [e.comp, y, x, e.res, e.prec]

/-- The precincts of a volume in the order of a position-driven progression: tagged with
their keys and sorted. -/
def sortedPrecincts (g : Layout) (v : Volume) : List PrecRef :=
  (((precRefs g v).map fun e => (posKey g v.order e, e)).mergeSort
    (fun a b => decide (a.1 ≤ b.1))).map (·.2)

/-- B.12.1.3–B.12.1.5 over a volume: the sorted precincts, layers innermost. -/
def forPosition (g : Layout) (v : Volume) (f : β → PacketId → m β) (b : β) : m β :=
  (sortedPrecincts g v).foldlM (fun b e => forRange 0 (v.le g) (fun b l => f b (e.packet l)) b) b

/-- The packets of one volume in its order. -/
def forVolume (g : Layout) (v : Volume) (f : β → PacketId → m β) (b : β) : m β :=
  match v.order with
  | .lrcp => forLRCP g v f b
  | .rlcp => forRLCP g v f b
  | _ => forPosition g v f b

/-- The volumes in turn; volume `j` skips the packets of volumes `0 … j − 1` (`prev`). -/
def forVolumes (g : Layout) (prev : List Volume) : List Volume → (β → PacketId → m β) → β → m β
  | [], _, b => pure b
  | v :: vs, f, b => do
    let b ← forVolume g v (fun b p => if prev.any (·.contains p) then pure b else f b p) b
    forVolumes g (prev ++ [v]) vs f b

/-- The packet sequence of a tile (B.12): `f` folded over every packet in progression order,
POC volumes in turn with already-sent packets skipped. -/
def forPackets (g : Layout) (order : Progression) (poc : Array PocEntry)
    (f : β → PacketId → m β) (b : β) : m β :=
  forVolumes g [] (volumes g order poc) f b

end

/-- The number of packets the iteration of `forPackets` visits over all volumes, weighted by
the number of earlier volumes each is checked against: `Σ_j (j + 1) · |volume_j ∩ packet
set|`. A caller bounds it against `Limits` before iterating (adversarial POC lists repeat the
whole packet set in every volume). -/
def iterationWork (g : Layout) (order : Progression) (poc : Array PocEntry) : Nat :=
  let count (v : Volume) : Nat :=
    (List.range' v.compStart (v.ce g - v.compStart)).foldl (fun a i =>
      (List.range' v.resStart (v.re g - v.resStart)).foldl
        (fun a r => a + g.numPrecincts i r) a) 0
  ((volumes g order poc).zipIdx.map fun (v, j) => (j + 1) * v.le g * count v).foldl (· + ·) 0

end JPEG2000.Progression
