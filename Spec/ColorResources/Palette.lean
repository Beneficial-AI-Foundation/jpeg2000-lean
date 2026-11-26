import Spec.NativeResources

/-!
# Retained JP2 palette table (Plan.md §§3–5, 7, S3; T.800 I.5.3.4)

The raw header retains the entire parsed row-major table even when mapping is disabled.
Its UInt64 entries and column tags are counted separately from each expanded lookup column.
-/

namespace JPEG2000.Spec.ColorResources

open JPEG2000 JPEG2000.Box JPEG2000.Bytes

/-- Size of the raw palette arrays retained by the codestream header. -/
def PaletteWithin (L : Limits) (p : Palette) : Prop :=
  p.ne ≤ L.maxPaletteEntries ∧ p.npc ≤ 255 ∧ p.bits.size = p.npc ∧ p.entries.size = p.ne*p.npc

private theorem many {α : Type} (f : Reader → Except Error (α × Reader)) :
    ∀ k r acc out, readMany f r acc k = .ok out → out.1.size = acc.size+k
  | 0, _, _, _, ok => by cases ok; rfl
  | k+1, r, acc, out, ok => by
    rw [readMany] at ok
    obtain ⟨⟨v,r'⟩, _, ok⟩ := Tier2Equiv.bind_ok ok
    rw [many f k _ _ _ ok, Array.size_push]; omega

private theorem row (bits : Array UInt8) (r : Reader) (acc : Array UInt64) (out : Array UInt64 × Reader)
    (ok : bits.foldlM (fun (s : Array UInt64 × Reader) bi => do
        let (v,r') ← readBE s.2 0 (entryBytes bi)
        return (s.1.push v,r')) (acc,r) = .ok out) : out.1.size = acc.size+bits.size := by
  rw [← Array.foldlM_toList] at ok
  generalize _eq : bits.toList = xs at ok
  suffices h : out.1.size = acc.size+xs.length by simpa [← _eq] using h
  clear _eq
  induction xs generalizing acc r with
  | nil => cases ok; rfl
  | cons x xs ih =>
    rw [List.foldlM_cons] at ok
    obtain ⟨⟨a,r'⟩, ha, ht⟩ := Tier2Equiv.bind_ok ok
    obtain ⟨⟨v,r''⟩, _, ret⟩ := Tier2Equiv.bind_ok ha
    cases ret
    rw [ih _ _ ht, Array.size_push, List.length_cons]
    dsimp only
    omega

private theorem rows (width : Nat) (f : Reader → Array UInt64 → Except Error (Array UInt64 × Reader))
    (hf : ∀ r acc out, f r acc = .ok out → out.1.size = acc.size+width) :
    ∀ k r acc out, parsePclr.rows f r acc k = .ok out → out.1.size = acc.size+k*width
  | 0, _, _, _, ok => by cases ok; simp
  | k+1, r, acc, out, ok => by
    rw [parsePclr.rows] at ok
    obtain ⟨⟨a,r'⟩, ha, ht⟩ := Tier2Equiv.bind_ok ok
    rw [rows width f hf k _ _ _ ht, hf _ _ _ ha, Nat.succ_mul]
    omega

private theorem parsed {L b p} (ok : parsePclr L b = .ok p) : PaletteWithin L p := by
  unfold parsePclr at ok
  obtain ⟨⟨ne,r⟩, _, ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨⟨npc,r'⟩, _, ok⟩ := Tier2Equiv.bind_ok ok
  by_cases bad : (ne.toNat == 0 || decide (ne.toNat > 1024)) = true
  · simp only [bad, ↓reduceIte] at ok; contradiction
  simp only [bad, Bool.false_eq_true, ↓reduceIte] at ok
  obtain ⟨_, limit, ok⟩ := Tier2Equiv.bind_ok ok
  by_cases hz : (npc.toNat == 0) = true
  · simp only [hz, ↓reduceIte] at ok; contradiction
  simp only [hz, Bool.false_eq_true, ↓reduceIte] at ok
  by_cases small : r'.remaining < npc.toNat
  · simp only [small, ↓reduceIte] at ok; contradiction
  simp only [small, ↓reduceIte] at ok
  obtain ⟨⟨bits,r''⟩, hb, ok⟩ := Tier2Equiv.bind_ok ok
  by_cases deep : (bits.any fun x => (x &&& 0x7F) + 1 > 38) = true
  · simp only [deep, ↓reduceIte] at ok; contradiction
  simp only [deep, Bool.false_eq_true, ↓reduceIte] at ok
  by_cases short : r''.remaining < ne.toNat * bits.foldl (fun s x => s + entryBytes x) 0
  · simp only [short, ↓reduceIte] at ok; contradiction
  simp only [short, ↓reduceIte] at ok
  obtain ⟨⟨es,r'''⟩, he, ok⟩ := Tier2Equiv.bind_ok ok
  cases ok
  have hb' : bits.size = npc.toNat := by simpa using many _ _ _ _ _ hb
  have he' := rows bits.size _ (row bits) _ _ _ _ he
  refine ⟨(Limits.check_eq_ok_iff ..).mp limit, ?_, hb', ?_⟩
  · change npc.toNat ≤ 255
    have := npc.toNat_lt; omega
  · simpa [hb'] using he'

private def Good (L : Limits) (p : Option Palette) : Prop :=
  ∀ v, p = some v → PaletteWithin L v

private theorem add {L a b out} (good : Good L a.pclr) (ok : addHeaderBox L a b = .ok out) :
    Good L out.pclr := by
  unfold addHeaderBox at ok
  repeat' first
    | (split at ok <;> try contradiction)
    | (obtain ⟨_, _, ok⟩ := Tier2Equiv.bind_ok ok)
  all_goals cases ok
  all_goals first | exact good | (intro v eq; cases eq; apply parsed; assumption)

private theorem headerLoop_good {L : Limits} :
    ∀ k r a n out, Good L a.pclr → headerLoop L r a n k = .ok out → Good L out.1.pclr
  | 0, r, a, n, out, g, ok => by
    simp only [headerLoop] at ok; split at ok <;> cases ok; exact g
  | k+1, r, a, n, out, g, ok => by
    rw [headerLoop] at ok
    split at ok
    · cases ok; exact g
    · obtain ⟨_, _, ok⟩ := Tier2Equiv.bind_ok ok
      obtain ⟨⟨b,r'⟩, _, ok⟩ := Tier2Equiv.bind_ok ok
      obtain ⟨a', ha, ok⟩ := Tier2Equiv.bind_ok ok
      exact headerLoop_good k _ _ _ _ (add g ha) ok

private theorem jp2h {L b n h} (ok : parseJp2h L b n = .ok h) : Good L h.1.pclr := by
  unfold parseJp2h at ok
  obtain ⟨_, _, ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨⟨a,n'⟩, ha, ok⟩ := Tier2Equiv.bind_ok ok
  have g := headerLoop_good _ _ _ _ _ (by intro v hv; cases hv) ha
  dsimp only at ok
  repeat' first | (split at ok <;> try contradiction) | (obtain ⟨_, _, ok⟩ := Tier2Equiv.bind_ok ok)
  all_goals cases ok; exact g

private theorem top_good {L : Limits} :
    ∀ k r h n out, Good L (h.bind Jp2Header.pclr) → topLoop L r h n k = .ok out → Good L out.1.pclr
  | 0, r, h, n, out, g, ok => by simp only [topLoop] at ok; split at ok <;> contradiction
  | k+1, r, h, n, out, g, ok => by
    rw [topLoop] at ok
    split at ok <;> try contradiction
    obtain ⟨_, _, ok⟩ := Tier2Equiv.bind_ok ok
    obtain ⟨⟨b,r'⟩, _, ok⟩ := Tier2Equiv.bind_ok ok
    dsimp only at ok
    split at ok
    · split at ok <;> try contradiction
      cases ok
      exact g
    · split at ok
      · obtain ⟨⟨a,n'⟩, ha, ok⟩ := Tier2Equiv.bind_ok ok
        exact top_good k _ (some a) _ _ (jp2h ha) ok
      · exact top_good k _ _ _ _ g ok

private theorem container_good {L data c} (ok : parseFile L data = .ok c) :
    Good L (c.header.bind Jp2Header.pclr) := by
  obtain ⟨a, aux, h⟩ := Tier2Equiv.bind_ok ok
  unfold parseFileAux at aux
  obtain ⟨_, _, aux⟩ := Tier2Equiv.bind_ok aux
  split at h <;> cases h
  split at aux
  · cases aux; intro v hv; cases hv
  · dsimp only at aux
    split at aux <;> try contradiction
    obtain ⟨⟨sig,r⟩, _, aux⟩ := Tier2Equiv.bind_ok aux
    split at aux <;> try contradiction
    obtain ⟨⟨v,r'⟩, _, aux⟩ := Tier2Equiv.bind_ok aux
    split at aux <;> try contradiction
    obtain ⟨⟨fb,r''⟩, _, aux⟩ := Tier2Equiv.bind_ok aux
    split at aux <;> try contradiction
    obtain ⟨ft, _, aux⟩ := Tier2Equiv.bind_ok aux
    obtain ⟨⟨h,cs⟩, top, aux⟩ := Tier2Equiv.bind_ok aux
    cases aux
    exact top_good _ _ _ _ _ (by intro v hv; cases hv) top

/-- The full original JP2 palette, including columns not selected for display, is
bounded even when the caller disables palette expansion. -/
private theorem retained_header {L data h} (ok : Header.parse L data = .ok h) :
    Good L ((h.container.bind Container.header).bind Jp2Header.pclr) := by
  obtain ⟨c, hc, ok⟩ := Tier2Equiv.bind_ok ok
  unfold Header.parseCodestreamIn at ok
  obtain ⟨r, _, ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨⟨mh,r⟩, _, ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨_, _, ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨defaults, _, ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨⟨tlm,ppm⟩, _, ok⟩ := Tier2Equiv.bind_ok ok
  repeat obtain ⟨_, _, ok⟩ := Tier2Equiv.bind_ok ok
  cases ok
  by_cases present : c.fileType.isSome = true
  · simpa only [present, ↓reduceIte, Option.bind_some] using container_good hc
  · simp [present, Good]

/-- Every original JP2 palette kept by a decoded codestream has its checked row count,
one tag per column and exactly one UInt64 value per row and column. -/
theorem retained_palette {L data reduce d} (ok : decodeCodestream L data reduce = .ok d) :
    ∀ p, ((d.header.container.bind Container.header).bind Jp2Header.pclr) = some p → PaletteWithin L p := by
  obtain ⟨_, _, tail⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨h, hp, _⟩ := Tier2Equiv.bind_ok tail
  rw [(CodestreamDispatch.native_geometry hp ok).1]
  exact retained_header hp

end JPEG2000.Spec.ColorResources
