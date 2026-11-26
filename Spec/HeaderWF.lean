import Spec.Equiv

/-!
# `HeaderWF`: what header parsing guarantees to the C9 composition

Plan.md §4 (C9), §5.1; T.800 A.6.4 (QCD/QCC: `SPqcd` step sizes, `εb` 5 bits, `μb` 11 bits,
Table A.30), A.6.1/A.6.2 and G.2 (the RCT goes with the 5/3 filter, the ICT with the 9/7 one, on
components 0–2). Task 7.1e.

`headerWF : Spec.Equiv.HeaderWF`: for every header `Header.parse` accepts and every tile layout
`Progression.Layout.ofHeader` builds from it,

* every tile-component's step sizes have mantissas `< 2^11` (`ParamsWF`): `Marker.readStepSize`
  masks `μb` to 11 bits (`v &&& 0x7FF`); style 0 sets `μb = 0`; style 1 (`bandSteps`, E-5)
  copies `μo`; the merge (`mainCoding`, `tileCoding`, `overrides`) only selects among parsed
  QCD/QCC segments of the main header and of the tile's tile-part headers;
* when the MCT applies (`Coding.mctApplies`: `SGcod` MCT and `Csiz ≥ 3`), components 0–2 use the
  same wavelet transform: `checkMct` rejects otherwise, for the main-header defaults and for every
  tile's merged coding, and `Layout.ofHeader`/`Geometry.ofHeader` pick that same coding
  (`codingOf`).

The proof walks the parser: `readQuant_wf` → main-header segment loop (`AccWF`) →
`parseMainHeader_wf` (`MainWF`); tile-part header loop, tile-part loop and tile assembly
(`SegWF`, `PartWF`, `StWF`, `TileWF`) → `parseTileParts_wf`; then the merge (`CodingWF`,
`MctWF`) → `parse_wf` (`HdrWF`) → `headerWF`. Nothing is assumed: HeaderWF holds as stated in
`Spec/Equiv.lean`.
-/

namespace JPEG2000.Spec.HeaderWF

open JPEG2000 JPEG2000.Bytes JPEG2000.Marker JPEG2000.TilePart JPEG2000.Header
open JPEG2000.Spec.Tier2Equiv (bind_ok)

/-- A step size whose mantissa fits 11 bits. -/
def StepWF (s : StepSize) : Prop := s.mantissa.toNat < 2048

/-- Every step size of a quantisation segment has an 11-bit mantissa. -/
def QuantWF : Quantization → Prop
  | .none _ => True
  | .derived b => StepWF b
  | .expounded ss => ∀ s ∈ ss, StepWF s

/-- `QuantWF` of a QCD/QCC parameter set. -/
def QcdWF (q : QCD) : Prop := QuantWF q.quant

/-- `readStepSize` masks the mantissa to 11 bits. -/
private theorem readStepSize_wf {r : Reader} {s : StepSize} {r' : Reader}
    (h : readStepSize r = .ok (s, r')) : StepWF s := by
  unfold readStepSize at h
  obtain ⟨⟨v, r1⟩, -, h⟩ := bind_ok h
  cases h
  unfold StepWF
  simp only [UInt16.toNat_and]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

/-- `readArray f` keeps an invariant that every item `f` reads satisfies. -/
theorem readArray_inv {α : Type} (P : α → Prop) (f : Reader → Except Error (α × Reader))
    (hf : ∀ r a r', f r = .ok (a, r') → P a) :
    ∀ (n : Nat) (acc : Array α) (r : Reader) (out : Array α) (r' : Reader),
    (∀ x ∈ acc, P x) → readArray f acc n r = .ok (out, r') → ∀ x ∈ out, P x
  | 0, acc, r, out, r', ha, h => by
    simp only [readArray, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h; exact ha
  | n + 1, acc, r, out, r', ha, h => by
    simp only [readArray] at h
    split at h
    · cases h
    · rename_i a r'' hf'
      refine readArray_inv P f hf n _ _ out r' ?_ h
      intro x hx
      rcases Array.mem_push.1 hx with hx | rfl
      · exact ha x hx
      · exact hf _ _ _ hf'

/-- A parsed QCD/QCC parameter set has 11-bit mantissas. -/
private theorem readQuant_wf {r : Reader} {q : QCD} (h : readQuant r = .ok q) : QcdWF q := by
  unfold readQuant at h
  obtain ⟨⟨s, r1⟩, -, h⟩ := bind_ok h
  dsimp only at h
  generalize s &&& 0x1F = k at h
  split at h
  · repeat (obtain ⟨_, _, h⟩ := bind_ok h)
    cases h; trivial
  · obtain ⟨⟨b, r2⟩, hb, h⟩ := bind_ok h
    obtain ⟨_, -, h⟩ := bind_ok h
    cases h; exact readStepSize_wf hb
  · obtain ⟨_, -, h⟩ := bind_ok h
    obtain ⟨⟨ss, r2⟩, hss, h⟩ := bind_ok h
    obtain ⟨_, -, h⟩ := bind_ok h
    cases h
    exact readArray_inv StepWF readStepSize (fun _ _ _ => readStepSize_wf) _ _ _ _ _
      (by simp) hss
  · cases h

/-- See `readQuant_wf`: a parsed QCC. -/
private theorem parseQCC_wf {csiz : Nat} {r : Reader} {q : QCC} (h : parseQCC csiz r = .ok q) :
    QcdWF q.params := by
  unfold parseQCC at h
  obtain ⟨_, -, h⟩ := bind_ok h
  obtain ⟨p, hp, h⟩ := bind_ok h
  cases h; exact readQuant_wf hp


/-- Main-header accumulator invariant: its QCD and QCC parameters are `QcdWF`. -/
def AccWF (acc : Acc) : Prop :=
  (∀ q, acc.qcd = some q → QcdWF q) ∧ ∀ q ∈ acc.qcc, QcdWF q.params

/-- `if true = true` reduces to its first branch. -/
private theorem ite_t {α : Type} (a b : α) : (if true = true then a else b) = a := rfl
/-- `if false = true` reduces to its second branch. -/
private theorem ite_f {α : Type} (a b : α) : (if false = true then a else b) = b := rfl

/-- Provenance of the markers that supply coding styles and quantisation. -/
def SegmentRead (L : Limits) : TileSegment → Prop
  | .cod d => ∃ r, parseCOD L r = .ok d
  | .coc d => ∃ n r, parseCOC L n r = .ok d
  | .qcd q => ∃ r, parseQCD r = .ok q
  | .qcc q => ∃ n r, parseQCC n r = .ok q
  | _ => True

/-- Provenance of the default and per-component marker fields collected in a header. -/
structure FieldsRead (L : Limits) (d : Option COD) (ds : Array COC)
    (q : Option QCD) (qs : Array QCC) : Prop where
  /-- The default coding style came from a COD marker. -/
  cod : ∀ x, d = some x → SegmentRead L (.cod x)
  /-- Each component style came from a COC marker. -/
  coc : ∀ x ∈ ds, SegmentRead L (.coc x)
  /-- The default quantisation came from a QCD marker. -/
  qcd : ∀ x, q = some x → SegmentRead L (.qcd x)
  /-- Each component quantisation came from a QCC marker. -/
  qcc : ∀ x ∈ qs, SegmentRead L (.qcc x)

private theorem all_push {α : Type} {P : α → Prop} {xs : Array α} {x : α}
    (hs : ∀ y ∈ xs, P y) (hx : P x) : ∀ y ∈ xs.push x, P y := by
  intro y hy
  rcases Array.mem_push.1 hy with hy | rfl
  · exact hs _ hy
  · exact hx

/-- Adding a main-header segment preserves the marker sources. -/
private theorem addSegment_wf {L : Limits} {csiz : Nat} {acc acc' : Acc} {m : UInt16} {body : Reader}
    (ha : FieldsRead L acc.cod acc.coc acc.qcd acc.qcc) (h : addSegment L csiz acc m body = .ok acc') :
    FieldsRead L acc'.cod acc'.coc acc'.qcd acc'.qcc := by
  unfold addSegment at h
  generalize (m == Code.COD) = b1 at h
  generalize (m == Code.COC) = b2 at h
  generalize (m == Code.QCD) = b3 at h
  generalize (m == Code.QCC) = b4 at h
  generalize (m == Code.RGN) = b5 at h
  generalize (m == Code.POC) = b6 at h
  generalize (m == Code.COM) = b7 at h
  generalize (m == Code.CRG) = b8 at h
  generalize (m == Code.CAP) = b9 at h
  generalize (m == Code.TLM || m == Code.PLM || m == Code.PPM) = b10 at h
  cases b1
  case true =>
    rw [ite_t] at h
    obtain ⟨_, -, h⟩ := bind_ok h
    obtain ⟨d, hd, h⟩ := bind_ok h
    cases h
    exact { ha with cod := fun _ e => by cases e; exact ⟨_, hd⟩ }
  rw [ite_f] at h
  cases b2
  case true =>
    rw [ite_t] at h
    obtain ⟨d, hd, h⟩ := bind_ok h
    cases h
    exact { ha with coc := all_push ha.coc ⟨_, _, hd⟩ }
  rw [ite_f] at h
  cases b3
  case true =>
    rw [ite_t] at h
    obtain ⟨_, -, h⟩ := bind_ok h
    obtain ⟨q, hq, h⟩ := bind_ok h
    cases h
    exact { ha with qcd := fun _ e => by cases e; exact ⟨_, hq⟩ }
  rw [ite_f] at h
  cases b4
  case true =>
    rw [ite_t] at h
    obtain ⟨q, hq, h⟩ := bind_ok h
    cases h
    exact { ha with qcc := all_push ha.qcc ⟨_, _, hq⟩ }
  rw [ite_f] at h
  cases b5
  case true =>
    rw [ite_t] at h
    obtain ⟨_, -, h⟩ := bind_ok h
    cases h; exact ha
  rw [ite_f] at h
  cases b6
  case true =>
    rw [ite_t] at h
    repeat (obtain ⟨_, _, h⟩ := bind_ok h)
    cases h; exact ha
  rw [ite_f] at h
  cases b7
  case true =>
    rw [ite_t] at h
    obtain ⟨_, -, h⟩ := bind_ok h
    cases h; exact ha
  rw [ite_f] at h
  cases b8
  case true =>
    rw [ite_t] at h
    obtain ⟨_, -, h⟩ := bind_ok h
    obtain ⟨_, -, h⟩ := bind_ok h
    cases h; exact ha
  rw [ite_f] at h
  cases b9
  case true =>
    rw [ite_t] at h
    obtain ⟨_, -, h⟩ := bind_ok h
    cases h; exact ha
  rw [ite_f] at h
  cases b10
  case true =>
    rw [ite_t] at h
    cases h; exact ha
  rw [ite_f] at h
  · cases h; exact ha

/-- The main-header loop preserves the marker sources. -/
private theorem segmentLoop_wf {L : Limits} {csiz : Nat} :
    ∀ (fuel : Nat) (acc : Acc) (r : Reader) (out : Acc) (r' : Reader),
    FieldsRead L acc.cod acc.coc acc.qcd acc.qcc → segmentLoop L csiz fuel acc r = .ok (out, r') →
    FieldsRead L out.cod out.coc out.qcd out.qcc
  | 0, acc, r, out, r', _, h => by simp only [segmentLoop] at h; cases h
  | fuel + 1, acc, r, out, r', ha, h => by
    simp only [segmentLoop] at h
    split at h
    · cases h
    split at h
    · cases h; exact ha
    split at h
    · cases h
    split at h
    · exact segmentLoop_wf fuel _ _ out r' (by exact ha) h
    split at h
    · cases h
    split at h
    · cases h
    split at h
    · cases h
    · rename_i hadd
      exact segmentLoop_wf fuel _ _ out r' (addSegment_wf (by exact ha) hadd) h

/-- Main-header invariant: QCD and every QCC have 11-bit mantissas. -/
def MainWF (mh : MainHeader) : Prop := QcdWF mh.qcd ∧ ∀ q ∈ mh.qcc, QcdWF q.params

/-- A parsed main header retains the SIZ reader and all four marker sources. -/
theorem parseMainHeader_fields {L : Limits} {r : Reader} {mh : MainHeader} {r' : Reader}
    (h : parseMainHeader L r = .ok (mh, r')) : (∃ body, parseSIZ L body = .ok mh.siz) ∧
      FieldsRead L (some mh.cod) mh.coc (some mh.qcd) mh.qcc := by
  unfold parseMainHeader at h
  obtain ⟨⟨soc, r1⟩, -, h⟩ := bind_ok h
  obtain ⟨_, -, h⟩ := bind_ok h
  obtain ⟨⟨m, r2⟩, -, h⟩ := bind_ok h
  obtain ⟨_, -, h⟩ := bind_ok h
  obtain ⟨⟨body, len, r3⟩, -, h⟩ := bind_ok h
  obtain ⟨siz, hsiz, h⟩ := bind_ok h
  obtain ⟨⟨acc, r4⟩, hl, h⟩ := bind_ok h
  cases hc : acc.cod <;> simp only [hc] at h
  · cases h
  cases hq : acc.qcd <;> simp only [hq] at h
  · cases h
  · cases h
    have hw := segmentLoop_wf _ _ _ _ _ (by constructor <;> simp) hl
    exact ⟨⟨_, hsiz⟩, hc ▸ hq ▸ hw⟩

private theorem parseMainHeader_wf {L : Limits} {r : Reader} {mh : MainHeader} {r' : Reader}
    (h : parseMainHeader L r = .ok (mh, r')) : MainWF mh := by
  have hw := (parseMainHeader_fields h).2
  obtain ⟨_, hq⟩ := hw.qcd _ rfl
  refine ⟨readQuant_wf hq, ?_⟩
  intro q hmem
  obtain ⟨_, _, hq⟩ := hw.qcc q hmem
  exact parseQCC_wf hq


/-- A tile-part header segment: QCD/QCC parameters are `QcdWF`. -/
def SegWF : TileSegment → Prop
  | .qcd q => QcdWF q
  | .qcc q => QcdWF q.params
  | _ => True

/-- Every segment of a tile-part header is `SegWF`. -/
def PartWF (p : TilePartHeader) : Prop := ∀ s ∈ p.segments, SegWF s

/-- Every tile-part of a tile is `PartWF`. -/
def TileWF (t : Tile) : Prop := ∀ p ∈ t.parts, PartWF p

/-- Every newly recorded coding or quantisation segment comes from its marker reader. -/
private theorem addTileSegment_wf {L : Limits} {csiz : Nat} {first ppm : Bool} {acc acc' : TPAcc}
    {m : UInt16} {body : Reader} (ha : ∀ s ∈ acc.segments, SegmentRead L s)
    (h : addTileSegment L csiz first ppm acc m body = .ok acc') : ∀ s ∈ acc'.segments, SegmentRead L s := by
  unfold addTileSegment at h
  dsimp only at h
  generalize (firstPartOnly m && !first) = b0 at h
  cases b0
  case true =>
    rw [ite_t] at h
    obtain ⟨_, h1, -⟩ := bind_ok h; cases h1
  rw [ite_f] at h
  have hp : ∀ x, SegmentRead L x → ∀ s ∈ (acc.segments.push x), SegmentRead L s :=
    fun _ => all_push ha
  generalize (m == Code.COD) = b1 at h
  generalize (m == Code.COC) = b2 at h
  generalize (m == Code.QCD) = b3 at h
  generalize (m == Code.QCC) = b4 at h
  generalize (m == Code.RGN) = b5 at h
  generalize (m == Code.POC) = b6 at h
  generalize (m == Code.PPT) = b7 at h
  generalize (m == Code.PLT) = b8 at h
  generalize (m == Code.COM) = b9 at h
  cases b1
  case true =>
    rw [ite_t] at h
    obtain ⟨_, -, h⟩ := bind_ok h
    obtain ⟨_, hd, h⟩ := bind_ok h
    cases h; exact hp _ ⟨_, hd⟩
  rw [ite_f] at h
  cases b2
  case true =>
    rw [ite_t] at h
    obtain ⟨_, hd, h⟩ := bind_ok h
    cases h; exact hp _ ⟨_, _, hd⟩
  rw [ite_f] at h
  cases b3
  case true =>
    rw [ite_t] at h
    obtain ⟨_, -, h⟩ := bind_ok h
    obtain ⟨q, hq, h⟩ := bind_ok h
    cases h; exact hp _ ⟨_, hq⟩
  rw [ite_f] at h
  cases b4
  case true =>
    rw [ite_t] at h
    obtain ⟨q, hq, h⟩ := bind_ok h
    cases h; exact hp _ ⟨_, _, hq⟩
  rw [ite_f] at h
  cases b5
  case true =>
    rw [ite_t] at h
    obtain ⟨_, -, h⟩ := bind_ok h
    cases h; exact hp _ trivial
  rw [ite_f] at h
  cases b6
  case true =>
    rw [ite_t] at h
    repeat (obtain ⟨_, _, h⟩ := bind_ok h)
    cases h; exact hp _ trivial
  rw [ite_f] at h
  cases b7
  case true =>
    rw [ite_t] at h
    obtain ⟨_, -, h⟩ := bind_ok h
    obtain ⟨_, -, h⟩ := bind_ok h
    cases h; exact hp _ trivial
  rw [ite_f] at h
  cases b8
  case true =>
    rw [ite_t] at h
    obtain ⟨_, -, h⟩ := bind_ok h
    cases h; exact hp _ trivial
  rw [ite_f] at h
  cases b9
  case true =>
    rw [ite_t] at h
    obtain ⟨_, -, h⟩ := bind_ok h
    cases h; exact hp _ trivial
  rw [ite_f] at h
  cases h; exact hp _ trivial

/-- The tile-part header loop preserves segment provenance. -/
private theorem headerLoop_wf {L : Limits} {csiz : Nat} {first ppm : Bool} :
    ∀ (fuel : Nat) (acc : TPAcc) (r : Reader) (out : TPAcc) (r' : Reader),
    (∀ s ∈ acc.segments, SegmentRead L s) → headerLoop L csiz first ppm fuel acc r = .ok (out, r') →
    ∀ s ∈ out.segments, SegmentRead L s
  | 0, acc, r, out, r', _, h => by simp only [headerLoop] at h; cases h
  | fuel + 1, acc, r, out, r', ha, h => by
    simp only [headerLoop] at h
    split at h
    · cases h
    split at h
    · cases h; exact ha
    split at h
    · cases h
    split at h
    · exact headerLoop_wf fuel _ _ out r' (by exact ha) h
    split at h
    · cases h
    split at h
    · cases h
    split at h
    · cases h
    · rename_i hadd
      exact headerLoop_wf fuel _ _ out r' (addTileSegment_wf (by exact ha) hadd) h


/-- Tile-part loop invariant: every tile-part recorded so far is `PartWF`. -/
def StWF (st : State) : Prop := ∀ ps ∈ st.parts, ∀ p ∈ ps, PartWF p

private abbrev PartRead (L : Limits) (p : TilePartHeader) :=
  ∀ s ∈ p.segments, SegmentRead L s

private abbrev StateRead (L : Limits) (st : State) :=
  ∀ ps ∈ st.parts, ∀ p ∈ ps, PartRead L p

/-- An element of `xs.modify i f` is an element of `xs` or `f` of one. -/
private theorem mem_modify {α : Type} {xs : Array α} {i : Nat} {f : α → α} {y : α}
    (hy : y ∈ xs.modify i f) : y ∈ xs ∨ ∃ x ∈ xs, y = f x := by
  obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.1 hy
  have hj' : j < xs.size := by simpa [Array.size_modify] using hj
  rw [Array.getElem_modify]
  split
  · exact Or.inr ⟨xs[j], Array.getElem_mem hj', rfl⟩
  · exact Or.inl (Array.getElem_mem hj')

/-- Reading one tile-part preserves the sources of all recorded segments. -/
private theorem readTilePart_wf {c : Ctx} {st st' : State} {r r' : Reader} (hs : StateRead c.limits st)
    (h : readTilePart c st r = .ok (st', r')) : StateRead c.limits st' := by
  unfold readTilePart at h
  dsimp only at h
  obtain ⟨⟨_, r1⟩, -, h⟩ := bind_ok h
  obtain ⟨⟨body, len, r2⟩, -, h⟩ := bind_ok h
  obtain ⟨sot, -, h⟩ := bind_ok h
  obtain ⟨_, -, h⟩ := bind_ok h
  obtain ⟨_, -, h⟩ := bind_ok h
  obtain ⟨_, -, h⟩ := bind_ok h
  obtain ⟨_, -, h⟩ := bind_ok h
  obtain ⟨_, -, h⟩ := bind_ok h
  obtain ⟨_, -, h⟩ := bind_ok h
  split at h <;> (split at h <;> (try cases h))
  all_goals
    obtain ⟨stop, -, h⟩ := bind_ok h
    obtain ⟨⟨tp, rNext⟩, -, h⟩ := bind_ok h
    obtain ⟨⟨acc, rData⟩, hl, h⟩ := bind_ok h
    cases h
    have ha := headerLoop_wf _ _ _ _ _ (by simp) hl
    intro ps hps p hp
    dsimp only at hps
    rcases mem_modify hps with hps | ⟨x, hx, rfl⟩
    · exact hs ps hps p hp
    · rcases Array.mem_push.1 hp with hp | rfl
      · exact hs x hx p hp
      · exact ha

/-- The tile-part loop preserves segment provenance. -/
private theorem tilePartLoop_wf {c : Ctx} :
    ∀ (fuel : Nat) (st : State) (r : Reader) (out : State),
    StateRead c.limits st → tilePartLoop c fuel st r = .ok out → StateRead c.limits out
  | 0, st, r, out, _, h => by simp only [tilePartLoop] at h; cases h
  | fuel + 1, st, r, out, hs, h => by
    simp only [tilePartLoop] at h
    split at h
    · cases h
    split at h
    · cases h; exact hs
    split at h
    · cases h
    split at h
    · cases h
    · rename_i hrd
      exact tilePartLoop_wf fuel _ _ out (readTilePart_wf hs hrd) h

/-- `assembleTile` keeps the tile-parts it is given. -/
private theorem assembleTile_parts {corr : Bool} {i : Nat} {parts : Array TilePartHeader} {t : Tile}
    (h : assembleTile corr i parts = .ok t) : t.parts = parts := by
  unfold assembleTile at h
  dsimp only at h
  split at h <;> split at h <;>
    first
    | (obtain ⟨_, h1, -⟩ := bind_ok h; cases h1)
    | (obtain ⟨_, -, h⟩ := bind_ok h; obtain ⟨_, -, h⟩ := bind_ok h; cases h; rfl)

/-- Assembling tile-parts into tiles preserves segment provenance. -/
private theorem assembleTiles_wf {L : Limits} {corr : Bool} {parts : Array (Array TilePartHeader)}
    (hp : ∀ ps ∈ parts, ∀ p ∈ ps, PartRead L p) :
    ∀ (n i packets : Nat) (acc out : Array Tile), (∀ t ∈ acc, ∀ p ∈ t.parts, PartRead L p) →
    assembleTiles L corr parts n i packets acc = .ok out → ∀ t ∈ out, ∀ p ∈ t.parts, PartRead L p
  | 0, i, packets, acc, out, ha, h => by
    simp only [assembleTiles, Except.ok.injEq] at h; subst h; exact ha
  | n + 1, i, packets, acc, out, ha, h => by
    simp only [assembleTiles] at h
    split at h
    · exact assembleTiles_wf hp n _ _ acc out ha h
    split at h
    · cases h
    rename_i t ht
    split at h
    · cases h
    refine assembleTiles_wf hp n _ _ _ out ?_ h
    intro t' ht'
    rcases Array.mem_push.1 ht' with ht' | rfl
    · exact ha t' ht'
    · intro p hpm
      rw [assembleTile_parts ht] at hpm
      cases hg : parts[i]? with
      | none => rw [hg] at hpm; simp at hpm
      | some ps => rw [hg] at hpm; exact hp ps (Array.mem_of_getElem? hg) p hpm

/-- The style and quantisation fields of every tile-part originate in marker reads. -/
theorem parseTileParts_fields {L : Limits} {mh : MainHeader} {r : Reader} {tiles : Array Tile}
    (h : parseTileParts L mh r = .ok tiles) :
    ∀ t ∈ tiles, ∀ p ∈ t.parts, ∀ s ∈ p.segments, SegmentRead L s := by
  unfold parseTileParts at h
  dsimp only at h
  obtain ⟨_, -, h⟩ := bind_ok h
  obtain ⟨st, hst, h⟩ := bind_ok h
  have hw := tilePartLoop_wf _ _ _ _ (by
    intro ps hps
    rw [Array.mem_replicate] at hps
    rw [hps.2]; intro p hp; simp at hp) hst
  exact assembleTiles_wf hw _ _ _ _ _ (by simp) h


private theorem parseTileParts_wf {L : Limits} {mh : MainHeader} {r : Reader} {tiles : Array Tile}
    (h : parseTileParts L mh r = .ok tiles) : ∀ t ∈ tiles, TileWF t := by
  intro t ht p hp s hs
  have hread := parseTileParts_fields h t ht p hp s hs
  cases s with
  | qcd q => obtain ⟨_, hq⟩ := hread; exact readQuant_wf hq
  | qcc q => obtain ⟨_, _, hq⟩ := hread; exact parseQCC_wf hq
  | _ => trivial

/-- Every step size of a tile-component's parameters has an 11-bit mantissa. -/
def CompWF (p : CompParams) : Prop := ∀ st ∈ p.steps, StepWF st

/-- Every component of a coding is `CompWF`. -/
def CodingWF (c : Coding) : Prop := ∀ p ∈ c.comps, CompWF p

/-- An element of `xs.extract a b` is an element of `xs`. -/
theorem mem_extract {α : Type} {xs : Array α} {a b : Nat} {y : α} (hy : y ∈ xs.extract a b) :
    y ∈ xs := by
  obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.1 hy
  rw [Array.getElem_extract]
  apply Array.getElem_mem

/-- The band step sizes of a `QuantWF` segment have 11-bit mantissas (E-5 keeps `μo`). -/
private theorem bandSteps_wf {pos nl : Nat} {q : Quantization} {ss : Array StepSize} (hq : QuantWF q)
    (h : bandSteps pos nl q = .ok ss) : ∀ st ∈ ss, StepWF st := by
  unfold bandSteps at h
  dsimp only at h
  split at h
  · split at h
    · cases h
    · cases h
      intro st hst
      obtain ⟨e, -, rfl⟩ := Array.mem_map.1 hst
      show (0 : UInt16).toNat < 2048
      decide
  · split at h
    · cases h
    · cases h
      intro st hst
      exact hq st (mem_extract hst)
  · split at h
    · cases h
    · cases h
      intro st hst
      obtain ⟨i, -, rfl⟩ := Array.mem_map.1 hst
      split
      · exact hq
      · exact hq

/-- `mkComp` from a `QcdWF` segment is `CompWF`. -/
private theorem mkComp_wf {pos : Nat} {s : CodingStyle} {q : QCD} {roi : Nat} {p : CompParams}
    (hq : QcdWF q) (h : mkComp pos s q roi = .ok p) : CompWF p := by
  unfold mkComp at h
  obtain ⟨ss, hss, h⟩ := bind_ok h
  cases h
  exact bandSteps_wf hq hss

/-- `List.foldlM` keeps an invariant that each step on a list element keeps. -/
private theorem foldlM_mem_inv {α β : Type} (P : β → Prop) (f : β → α → Except Error β) :
    ∀ (l : List α), (∀ a ∈ l, ∀ b r, P b → f b a = .ok r → P r) →
    ∀ (b r : β), P b → l.foldlM f b = .ok r → P r
  | [], _, b, r, hb, h => by simp only [List.foldlM_nil] at h; cases h; exact hb
  | a :: l, hf, b, r, hb, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨b', h1, h2⟩ := bind_ok h
    exact foldlM_mem_inv P f l (fun a' ha' => hf a' (List.mem_cons_of_mem a ha'))
      b' r (hf a (List.mem_cons_self) b b' hb h1) h2

/-- Every value of `overrides` comes from an item, so it satisfies what all items do. -/
theorem overrides_inv {α : Type} (P : α → Prop) {pos csiz : Nat} {what : String}
    {items : Array (UInt16 × α)} {out : Array (Option α)} (hi : ∀ x ∈ items, P x.2)
    (h : overrides pos what csiz items = .ok out) : ∀ o ∈ out, ∀ v, o = some v → P v := by
  unfold overrides at h
  rw [← Array.foldlM_toList] at h
  refine foldlM_mem_inv (fun (acc : Array (Option α)) => ∀ o ∈ acc, ∀ v, o = some v → P v) _
    items.toList ?_ _ _ ?_ h
  · intro x hx acc r hacc hstep
    obtain ⟨c, v⟩ := x
    dsimp only at hstep
    split at hstep
    · cases hstep
      intro o ho w hw
      obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.1 ho
      have hj' : j < acc.size := by simpa using hj
      rw [Array.getElem_setIfInBounds hj'] at hw
      split at hw
      · cases hw; exact hi _ (Array.mem_def.2 hx)
      · exact hacc _ (Array.getElem_mem hj') w hw
    · cases hstep
    · cases hstep
  · intro o ho v hv
    rw [Array.mem_replicate] at ho
    rw [ho.2] at hv; cases hv

/-- `xs.getD i none` is `none` or an element of `xs`. -/
theorem getD_none {α : Type} (P : α → Prop) {xs : Array (Option α)} {i : Nat} {v : α}
    (hx : ∀ o ∈ xs, ∀ v, o = some v → P v) (h : xs.getD i none = some v) : P v := by
  rw [Array.getD_eq_getD_getElem?] at h
  cases hg : xs[i]? with
  | none => rw [hg] at h; cases h
  | some o => rw [hg] at h; exact hx o (Array.mem_of_getElem? hg) v h

/-- `(xs.getD i none).getD d` satisfies `P` when `d` and every entry do. -/
theorem getD_getD {α : Type} (P : α → Prop) {xs : Array (Option α)} {i : Nat} {d : α}
    (hx : ∀ o ∈ xs, ∀ v, o = some v → P v) (hd : P d) : P ((xs.getD i none).getD d) := by
  cases hg : xs.getD i none with
  | none => exact hd
  | some v => exact getD_none P hx hg

/-- The MCT constraint of a coding (G.2): when the MCT applies, components 0–2 have the
transform of component 0. -/
def MctWF (s : SIZ) (c : Coding) : Prop :=
  c.mctApplies s = true → ∀ i, i < 3 → ∀ p0 pi, c.comps[0]? = some p0 → c.comps[i]? = some pi →
    pi.transform = p0.transform

/-- A successful `checkMct` gives `MctWF`. -/
private theorem checkMct_wf {pos : Nat} {s : SIZ} {c : Coding} (h : checkMct pos s c = .ok ()) :
    MctWF s c := by
  intro hm i hi p0 pi h0 hpi
  unfold Coding.mctApplies at hm
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hm
  unfold checkMct at h
  simp only [hm.1, Bool.not_true] at h
  rw [ite_f] at h
  have hs : 3 ≤ s.components.size := hm.2
  rw [Array.getElem?_eq_getElem (by omega : 0 < s.components.size),
    Array.getElem?_eq_getElem (by omega : 1 < s.components.size),
    Array.getElem?_eq_getElem (by omega : 2 < s.components.size)] at h
  dsimp only at h
  split at h
  · split at h
    · rename_i hall
      obtain ⟨hic, hpi'⟩ := Array.getElem?_eq_some_iff.1 hpi
      obtain ⟨h0c, h0'⟩ := Array.getElem?_eq_some_iff.1 h0
      have hsz : i < ((c.comps.extract 0 3).map (·.transform)).size := by
        simp only [Array.size_map, Array.size_extract]; omega
      have := Array.all_eq_true.1 hall i hsz
      simp only [decide_eq_true_eq, Array.getElem_map, Array.getElem_extract, Nat.zero_add,
        Array.getD_eq_getD_getElem?, Array.getElem?_map] at this
      rw [hpi'] at this
      rw [this]
      simp [Array.getElem?_extract, h0]
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega))]; rfl
    · cases h
  · obtain ⟨_, h1, -⟩ := bind_ok h; cases h1


/-- Every element of a successful `List.mapM` result comes from a call on a list element. -/
private theorem listMapM_mem {α β : Type} (P : β → Prop) (f : α → Except Error β) :
    ∀ (l : List α), (∀ a ∈ l, ∀ b, f a = .ok b → P b) → ∀ (out : List β), l.mapM f = .ok out →
    ∀ y ∈ out, P y
  | [], _, out, h, y, hy => by simp [List.mapM_nil] at h; cases h; simp at hy
  | a :: l, hf, out, h, y, hy => by
    rw [List.mapM_cons] at h
    obtain ⟨b, hb, h⟩ := bind_ok h
    obtain ⟨bs, hbs, h⟩ := bind_ok h
    cases h
    simp only [List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact hf a List.mem_cons_self y hb
    · exact listMapM_mem P f l (fun a' ha' => hf a' (List.mem_cons_of_mem a ha')) bs hbs y hy

/-- Array version of `listMapM_mem`. -/
theorem arrayMapM_mem {α β : Type} (P : β → Prop) (f : α → Except Error β) (xs : Array α)
    (hf : ∀ a ∈ xs, ∀ b, f a = .ok b → P b) (out : Array β) (h : xs.mapM f = .ok out) :
    ∀ y ∈ out, P y := by
  rw [Array.mapM_eq_mapM_toList] at h
  cases hm : List.mapM f xs.toList with
  | error e => rw [hm] at h; cases h
  | ok l =>
    rw [hm] at h; cases h
    intro y hy
    exact listMapM_mem P f xs.toList (fun a ha => hf a (Array.mem_def.2 ha)) l hm y
      (by simpa using hy)

/-- The main-header coding is `CodingWF` and `MctWF`. -/
private theorem mainCoding_wf {mh : MainHeader} {c : Coding} (hm : MainWF mh) (h : mainCoding mh = .ok c) :
    CodingWF c ∧ MctWF mh.siz c := by
  unfold mainCoding at h
  dsimp only at h
  obtain ⟨ov, hov, h⟩ := bind_ok h
  obtain ⟨comps, hcomps, h⟩ := bind_ok h
  obtain ⟨_, -, h⟩ := bind_ok h
  obtain ⟨u, hmct, h⟩ := bind_ok h
  cases h
  refine ⟨?_, checkMct_wf hmct⟩
  unfold mkOverrides at hov
  obtain ⟨coc, -, hov⟩ := bind_ok hov
  obtain ⟨qcc, hqcc, hov⟩ := bind_ok hov
  obtain ⟨rgn, -, hov⟩ := bind_ok hov
  cases hov
  have hq := overrides_inv QcdWF (by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := Array.mem_map.1 hx
    exact hm.2 q hq) hqcc
  refine arrayMapM_mem CompWF _ _ ?_ comps hcomps
  intro a _ b hb
  exact mkComp_wf (getD_getD QcdWF hq hm.1) hb

/-- Tile-segment invariant: QCD and every QCC are `QcdWF`. -/
def TSegsWF (ts : TileSegs) : Prop :=
  (∀ q, ts.qcd = some q → QcdWF q) ∧ ∀ q ∈ ts.qcc, QcdWF q.params

/-- `List.foldl` keeps an invariant that each step on a list element keeps. -/
theorem list_foldl_inv {α β : Type} (P : β → Prop) (f : β → α → β) :
    ∀ (l : List α), (∀ a ∈ l, ∀ b, P b → P (f b a)) → ∀ b, P b → P (l.foldl f b)
  | [], _, _, hb => hb
  | a :: l, hf, b, hb => list_foldl_inv P f l (fun a' ha' => hf a' (List.mem_cons_of_mem a ha'))
      _ (hf a List.mem_cons_self b hb)

/-- The segments of a `TileWF` tile sort into a `TSegsWF` record. -/
private theorem tileSegs_wf {t : Tile} (ht : TileWF t) : TSegsWF (tileSegs t) := by
  unfold tileSegs
  rw [← Array.foldl_toList]
  refine list_foldl_inv TSegsWF _ _ ?_ _ ⟨by simp, by simp⟩
  intro p hp acc hacc
  rw [← Array.foldl_toList]
  refine list_foldl_inv TSegsWF _ _ ?_ _ hacc
  intro s hs acc' hacc'
  have hsw := ht p (Array.mem_def.2 hp) s (Array.mem_def.2 hs)
  cases s with
  | qcd q =>
    refine ⟨?_, hacc'.2⟩
    intro q' e; cases e; exact hsw
  | qcc q =>
    refine ⟨hacc'.1, ?_⟩
    intro x hx
    rcases Array.mem_push.1 hx with hx | rfl
    · exact hacc'.2 x hx
    · exact hsw
  | _ => exact hacc'


/-- The QCC overrides of `mkOverrides` from `QcdWF` QCCs are `QcdWF`. -/
private theorem mkOverrides_qcc {pos csiz : Nat} {coc : Array COC} {qcc : Array QCC} {rgn : Array RGN}
    {ov : Overrides} (hq : ∀ q ∈ qcc, QcdWF q.params) (h : mkOverrides pos csiz coc qcc rgn = .ok ov) :
    ∀ o ∈ ov.qcc, ∀ v, o = some v → QcdWF v := by
  unfold mkOverrides at h
  obtain ⟨_, -, h⟩ := bind_ok h
  obtain ⟨qs, hqs, h⟩ := bind_ok h
  obtain ⟨_, -, h⟩ := bind_ok h
  cases h
  exact overrides_inv QcdWF (by
    intro x hx
    obtain ⟨q, hq', rfl⟩ := Array.mem_map.1 hx
    exact hq q hq') hqs

/-- A tile's merged coding is `CodingWF` and `MctWF`. -/
private theorem tileCoding_wf {mh : MainHeader} {mainOv : Overrides} {defaults c : Coding} {t : Tile}
    (hm : MainWF mh) (hov : ∀ o ∈ mainOv.qcc, ∀ v, o = some v → QcdWF v) (hd : CodingWF defaults)
    (ht : TileWF t) (h : tileCoding mh mainOv defaults t = .ok c) :
    CodingWF c ∧ MctWF mh.siz c := by
  unfold tileCoding at h
  dsimp only at h
  obtain ⟨_, -, h⟩ := bind_ok h
  have hts := tileSegs_wf ht
  split at h
  · obtain ⟨c', hc', h⟩ := bind_ok h
    obtain ⟨u, hmct, h⟩ := bind_ok h
    cases h; cases hc'
    exact ⟨hd, checkMct_wf hmct⟩
  · obtain ⟨ov, hov', h⟩ := bind_ok h
    obtain ⟨comps, hcomps, h⟩ := bind_ok h
    obtain ⟨c', hc', h⟩ := bind_ok h
    obtain ⟨u, hmct, h⟩ := bind_ok h
    cases h; cases hc'
    refine ⟨?_, checkMct_wf hmct⟩
    have hq := mkOverrides_qcc hts.2 hov'
    refine arrayMapM_mem CompWF _ _ ?_ comps hcomps
    intro a _ b hb
    refine mkComp_wf ?_ hb
    split
    · rename_i q _; exact getD_none QcdWF hq (by assumption)
    · rename_i q _ hq2; exact hts.1 q hq2
    · exact getD_getD QcdWF hov hm.1


/-- What a successfully parsed codestream guarantees about its codings: the main-header
defaults and every tile's merged coding have 11-bit mantissas and satisfy the MCT constraint. -/
def HdrWF (h : Header) : Prop :=
  (CodingWF h.defaults ∧ MctWF h.siz h.defaults) ∧
    ∀ tp ∈ h.tiles, CodingWF tp.coding ∧ MctWF h.siz tp.coding

/-- A parsed codestream is `HdrWF`. -/
private theorem parseCodestreamIn_wf {L : Limits} {data : ByteArray} {rg : Box.ByteRange}
    {ct : Option Box.Container} {h : Header} (hp : parseCodestreamIn L data rg ct = .ok h) :
    HdrWF h := by
  unfold parseCodestreamIn at hp
  obtain ⟨_, -, hp⟩ := bind_ok hp
  obtain ⟨⟨mh, r⟩, hmh, hp⟩ := bind_ok hp
  obtain ⟨_, -, hp⟩ := bind_ok hp
  obtain ⟨defaults, hdef, hp⟩ := bind_ok hp
  obtain ⟨_, -, hp⟩ := bind_ok hp
  obtain ⟨tiles, htiles, hp⟩ := bind_ok hp
  obtain ⟨mainOv, hov, hp⟩ := bind_ok hp
  obtain ⟨tps, htps, hp⟩ := bind_ok hp
  obtain ⟨_, -, hp⟩ := bind_ok hp
  cases hp
  have hm := parseMainHeader_wf hmh
  have hd := mainCoding_wf hm hdef
  have hovq := mkOverrides_qcc hm.2 hov
  have hts := parseTileParts_wf htiles
  refine ⟨hd, ?_⟩
  refine arrayMapM_mem (fun tp => CodingWF tp.coding ∧ MctWF mh.siz tp.coding) _ tiles ?_ tps htps
  intro t ht tp htp
  obtain ⟨c, hc, htp⟩ := bind_ok htp
  cases htp
  exact tileCoding_wf hm hovq hd.1 (hts t ht) hc

/-- **A parsed header is `HdrWF`**: main-header defaults and every tile's coding have 11-bit
mantissas (T.800 A.6.4) and pass the MCT check (G.2). -/
theorem parse_wf {L : Limits} {data : ByteArray} {h : Header} (hp : Header.parse L data = .ok h) :
    HdrWF h := by
  unfold Header.parse at hp
  obtain ⟨_, -, hp⟩ := bind_ok hp
  exact parseCodestreamIn_wf hp

/-- The coding that applies to tile `t` (as `Layout.ofHeader` and `Geometry.ofHeader` pick it). -/
def codingOf (h : Header) (t : Nat) : Coding :=
  match h.tiles.find? (·.index == t) with
  | some tp => tp.coding
  | none => h.defaults

/-- The coding of any tile of an `HdrWF` header is `CodingWF` and `MctWF`. -/
private theorem codingOf_wf {h : Header} (hw : HdrWF h) (t : Nat) :
    CodingWF (codingOf h t) ∧ MctWF h.siz (codingOf h t) := by
  unfold codingOf
  split
  · rename_i tp htp
    exact hw.2 tp (Array.mem_of_find?_eq_some htp)
  · exact hw.1

/-- `Geometry.ofHeader` takes component `c`'s parameters from `codingOf h t`. -/
theorem geom_params {h : Header} {t c : Nat} {tc : Tier2.Geometry.TileCompGeom}
    (hg : Tier2.Geometry.ofHeader h t c = .ok tc) : (codingOf h t).comps[c]? = some tc.params := by
  unfold Tier2.Geometry.ofHeader at hg
  dsimp only at hg
  repeat' split at hg
  all_goals first
    | (cases hg; done)
    | (cases hg; assumption)

/-- A successful `List.mapM` has the input's length and is the calls index-wise. -/
private theorem listMapM_get {α β : Type} (f : α → Except Error β) :
    ∀ (l : List α) (out : List β), l.mapM f = .ok out →
    out.length = l.length ∧ ∀ i (hi : i < l.length) (ho : i < out.length), f l[i] = .ok out[i]
  | [], out, h => by
    simp [List.mapM_nil] at h; cases h; simp
  | a :: l, out, h => by
    rw [List.mapM_cons] at h
    obtain ⟨b, hb, h⟩ := bind_ok h
    obtain ⟨bs, hbs, h⟩ := bind_ok h
    cases h
    have ih := listMapM_get f l bs hbs
    refine ⟨by simp [ih.1], ?_⟩
    intro i hi ho
    cases i with
    | zero => exact hb
    | succ i => exact ih.2 i (by simpa using hi) (by simpa using ho)

/-- Array version of `listMapM_get`. -/
private theorem arrayMapM_get {α β : Type} (f : α → Except Error β) (xs : Array α) (out : Array β)
    (h : xs.mapM f = .ok out) :
    out.size = xs.size ∧ ∀ i (hi : i < xs.size) (ho : i < out.size), f xs[i] = .ok out[i] := by
  rw [Array.mapM_eq_mapM_toList] at h
  cases hm : List.mapM f xs.toList with
  | error e => rw [hm] at h; cases h
  | ok l =>
    rw [hm] at h; cases h
    have := listMapM_get f xs.toList l hm
    refine ⟨by simpa using this.1, ?_⟩
    intro i hi ho
    have := this.2 i (by simpa using hi) (by simpa using ho)
    simpa using this


/-- **`HeaderWF` holds** (task 7.1e): for every successfully parsed header, every tile-component
of every tile layout has step-size mantissas `< 2^11` (`readStepSize` masks them to 11 bits), and in
a tile where the MCT applies, components 0–2 use the same wavelet transform (`checkMct`). -/
theorem headerWF : Spec.Equiv.HeaderWF := by
  intro L data h hp t g coding hl
  have hc := codingOf_wf (parse_wf hp) t
  unfold Progression.Layout.ofHeader at hl
  dsimp only at hl
  split at hl
  · cases hl
  obtain ⟨comps, hcomps, hl⟩ := bind_ok hl
  cases hl
  have hmem : ∀ tc ∈ comps, CompWF tc.params :=
    arrayMapM_mem (fun tc => CompWF tc.params) _ _ (by
      intro c _ tc htc
      exact hc.1 _ (Array.mem_of_getElem? (geom_params htc))) comps hcomps
  have hget := arrayMapM_get _ _ _ hcomps
  have hcomp : ∀ c (hc : c < comps.size),
      (codingOf h t).comps[c]? = some (Progression.Layout.comp
        { tile := tileRect h.siz t, layers := (codingOf h t).layers, comps } c).params := by
    intro c hcs
    have hr : c < (Array.range h.siz.csiz).size := by rw [← hget.1]; exact hcs
    have := hget.2 c hr hcs
    simp only [Array.getElem_range] at this
    have e : Progression.Layout.comp
        { tile := tileRect h.siz t, layers := (codingOf h t).layers, comps } c = comps[c] := by
      simp [Progression.Layout.comp, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hcs]
    rw [e]; exact geom_params this
  refine ⟨?_, ?_⟩
  · intro c st hst
    unfold Progression.Layout.comp at hst
    rw [Array.getD_eq_getD_getElem?] at hst
    cases hg : comps[c]? with
    | none =>
      rw [hg] at hst
      change st ∈ (#[] : Array StepSize) at hst
      simp at hst
    | some tc =>
      rw [hg] at hst
      exact hmem tc (Array.mem_of_getElem? hg) st hst
  · intro hm c hc3
    have hsz : 3 ≤ comps.size := by
      rw [hget.1, Array.size_range]
      unfold Coding.mctApplies at hm
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hm
      exact hm.2
    exact hc.2 hm c hc3 _ _ (hcomp 0 (by omega)) (hcomp c (by omega))

end JPEG2000.Spec.HeaderWF
