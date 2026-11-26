import Spec.Equiv

/-!
# Packet traversal for native C9

Plan.md §§3–5, 7. The production and reference traversals use the same parsed
header, A.7.4–A.7.5 packet-header stream and B.9–B.12 cumulative pass budget.
The packet comparison includes rejection for unconsumed packed-header bytes.
`decode_of_stages` lifts a relation on output stores through both executable
loops. Reconstruction receives the successful packet calls for the current
tile, including both stores on the original input. The other stages cover
placement on the B-14 grid and final output (Annexes D–G).
-/

namespace JPEG2000.Spec.NativeTraversal

open JPEG2000.Header JPEG2000.TilePart JPEG2000.Tier2.Packet
open JPEG2000.Tier2.Headers
open JPEG2000.Spec.Decode
open JPEG2000.Spec.Tier2Equiv (Res)

/-- Origin of the optional stores passed to reconstruction at tile `t`,
with tile-part cursor `j` and incoming pass count `passes`. -/
inductive PacketOrigin (L : Limits) (h : Header) (data : ByteArray) (t j passes : Nat) :
    Option TileCodeBlocks → Option Spec.Tier2.TileOut → Prop where
  /-- The cursor is exhausted or points to another tile index. -/
  | absent (missing : (h.tiles[j]?.map (·.index)) ≠ some t) :
      PacketOrigin L h data t j passes none none
  /-- Both decoders read the stream selected by the same chunk index and
  returned these stores, with identical pass counts and corresponding precincts. -/
  | present {idx : Array (Array Nat)} {tp : TileParams} {hs : Option HeaderStream}
      {d : TileCodeBlocks} {s : Spec.Tier2.TileOut}
      (chunks : (if h.ppm.segments.isEmpty then pure #[] else ppmChunkIndex L h) = .ok idx)
      (selected : h.tiles[j]? = some tp) (index : tp.index = t)
      (stream : headerStreamAt h data tp (idx.getD j #[]) = .ok hs)
      (packets : JPEG2000.Tier2.Headers.decodeWithStream L h data tp hs passes = .ok d)
      (reference : Spec.Tier2.decodeWithStream L h data tp hs passes = .ok s)
      (precincts : s.comps = Tier2Equiv.image data d) (count : s.passes = d.passes) :
      PacketOrigin L h data t j passes (some d) (some s)

/-- Stage obligations for one admitted reduction and parsed header. The output
invariant is indexed by the next tile and accumulated production saturation.
The reference decoder adds zero to its saturation counter on every iteration. -/
structure Stages {P T R : Type} (L : Limits) (data : ByteArray) (reduce : Nat) (h : Header)
    (initial : Except Error P) (tile : Nat → Option TileCodeBlocks → Except Error T)
    (saturated : T → Nat) (write : P → T → Except Error P) (finish : P → Nat → R)
    (I : Array DecodedComponent → Nat → Nat → P → Array SamplePlane → Prop)
    (TileRel : Nat → T → Decode.TileOut → Prop) (Result : R → SpecImage → Prop) : Prop where
  /-- Allocation rejects together or establishes the initial invariant. -/
  alloc : Res (fun dst (ip : Array DecodedComponent × Array Bytes.Plane) =>
    I ip.1 0 0 dst (initPlanes ip.2)) initial (JPEG2000.Decode.allocOutput L h.siz reduce)
  /-- Reconstruct the same in-range tile from the two actual optional packet stores. -/
  reconstruct : ∀ t, t < numTiles h.siz → ∀ j passes d s,
    PacketOrigin L h data t j passes d s →
    Res (TileRel t) (tile t d) (Decode.decodeTile L h t reduce s)
  /-- Successful placement advances the invariant by one tile and its saturation count. -/
  place : ∀ info planes, JPEG2000.Decode.allocOutput L h.siz reduce = .ok (info, planes) →
    ∀ t, t < numTiles h.siz → ∀ sat dst ref out sout, I info t sat dst ref → TileRel t out sout →
    Res (I info (t + 1) (sat + saturated out)) (write dst out) (Decode.place info ref sout)
  /-- The invariant after the last tile relates the two completed images. -/
  finishRel : ∀ info planes, JPEG2000.Decode.allocOutput L h.siz reduce = .ok (info, planes) →
    ∀ sat dst ref, I info (numTiles h.siz) sat dst ref →
    Result (finish dst sat)
      ⟨h, info.zipWith (fun m p => { info := m, samples := p.samples }) ref⟩

private theorem remember {A B : Type} {P : A → B → Prop} {x : Except Error A} {y : Except Error B}
    (rel : Res P x y) : Res (fun a b => P a b ∧ x = .ok a ∧ y = .ok b) x y := by
  cases x <;> cases y <;> simp_all [Res]

private theorem branch_bind {A B : Type} (c : Prop) [Decidable c] (x y : Except Error A)
    (k : A → Except Error B) :
    (if c then x >>= k else y >>= k) = ((if c then x else y) >>= k) := by
  split <;> rfl

private def Yield {A B : Type} (I : A → B → Prop) : ForInStep A → ForInStep B → Prop
  | .yield a, .yield b => I a b
  | _, _ => False

private theorem range_sim {A B : Type} (n : Nat) (I : Nat → A → B → Prop)
    (f : Nat → A → Except Error (ForInStep A)) (g : Nat → B → Except Error (ForInStep B))
    (step : ∀ i, i < n → ∀ a b, I i a b → Res (Yield (I (i + 1))) (f i a) (g i b))
    (a : A) (b : B) (start : I 0 a b) :
    Res (I n) (forIn [0:n] a f) (forIn [0:n] b g) := by
  have loop : ∀ k i, i + k = n → ∀ x y, I i x y →
      Res (I n) (forIn (List.range' i k) x f) (forIn (List.range' i k) y g) := by
    intro k
    induction k with
    | zero => intro i hi x y hxy; simpa using hi ▸ hxy
    | succ k ih =>
      intro i hi x y hxy
      simp only [List.range'_succ, List.forIn_cons]
      apply Res.bind (step i (by omega) x y hxy)
      intro u v huv
      cases u <;> cases v <;> simp only [Yield] at huv
      exact ih (i + 1) (by omega) _ _ huv
  simpa [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size] using
    loop n 0 (by omega) a b start

private abbrev State (P : Type) := P × Nat × Nat × Nat

private def Invariant {P : Type} (I : Nat → Nat → P → Array SamplePlane → Prop) (t : Nat)
    (a : State P) (b : State (Array SamplePlane)) : Prop :=
  a.2.1 = b.2.1 ∧ a.2.2.2 = b.2.2.2 ∧ b.2.2.1 = 0 ∧ I t a.2.2.1 a.1 b.1

/-- Correspondence of the ordinary `withTiles` pipeline and `Spec.Decode.decode`
at every reduction. The caller supplies allocation, tile reconstruction, placement
and finish for each successful parse under the original limits. The shared checks
and two-sided packet simulation discharge every traversal rejection. -/
theorem decode_of_stages {P T R : Type} (L : Limits) (data : ByteArray) (reduce : Nat)
    (initial : Header → Except Error P) (tile : Header → Nat → Option TileCodeBlocks → Except Error T)
    (saturated : T → Nat) (write : Header → P → T → Except Error P) (finish : Header → P → Nat → R)
    (I : Header → Array DecodedComponent → Nat → Nat → P → Array SamplePlane → Prop)
    (TileRel : Header → Nat → T → Decode.TileOut → Prop) (Result : R → SpecImage → Prop)
    (stages : L.check JPEG2000.Decode.loc .decompLevels reduce = .ok () →
      ∀ h, Header.parse L data = .ok h →
        Stages L data reduce h (initial h) (tile h) saturated (write h) (finish h) (I h) (TileRel h) Result) :
    Res Result (do
      L.check JPEG2000.Decode.loc .decompLevels reduce
      let h ← Header.parse L data
      let dst ← initial h
      JPEG2000.Decode.withTiles L h data dst (tile h) saturated (write h) (finish h))
      (Decode.decode L data reduce) := by
  unfold Decode.decode codestreamWith
  apply Res.bind (Res.self _)
  rintro u _ ⟨rfl, checked⟩
  cases u
  apply Res.bind (Res.self _)
  rintro h _ ⟨rfl, parsed⟩
  have st := stages checked h parsed
  apply Res.bind (remember st.alloc)
  rintro dst ⟨info, planes⟩ ⟨start, _, allocated⟩
  unfold JPEG2000.Decode.withTiles
  dsimp only
  rw [branch_bind, branch_bind]
  apply Res.bind (Res.self _)
  rintro idx _ ⟨rfl, chunks⟩
  apply Res.bind (P := Invariant (I h info) (numTiles h.siz))
  · apply range_sim (I := Invariant (I h info))
    · intro t ht a b hab
      obtain ⟨dst, n, sat, j⟩ := a
      obtain ⟨ref, sn, ssat, sj⟩ := b
      obtain ⟨hp, hj, hs, related⟩ := hab
      dsimp only at hp hj hs related ⊢
      subst sn sj ssat
      have tail {d s} (origin : PacketOrigin L h data t j n d s) (next cursor : Nat) :
          Res (Yield (Invariant (I h info) (t + 1)))
            (do let out ← tile h t d
                let p ← write h dst out
                pure (.yield (p, next, sat + saturated out, cursor)))
            (do let out ← Decode.decodeTile L h t reduce s
                let p ← Decode.place info ref out
                pure (.yield (p, next, 0, cursor))) := by
        apply Res.bind (st.reconstruct t ht j n d s origin)
        intro out sout tiles
        apply Res.bind (st.place info planes allocated t ht sat dst ref out sout related tiles)
        intro p q pq
        exact ⟨rfl, rfl, rfl, pq⟩
      cases selected : h.tiles[j]? with
      | none =>
        simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, pure_bind]
        exact tail (.absent (by simp [selected])) n j
      | some tp =>
        by_cases index : tp.index = t
        · simp only [index, ↓reduceIte, Option.isSome_some, pure_bind]
          apply Res.bind (Res.self _)
          rintro hs _ ⟨rfl, stream⟩
          apply Res.bind (remember (Tier2Equiv.decodeWithStream_sim L h data tp hs n
            (fun _ _ layout => Tier2Equiv.ofHeader_wf (Equiv.parse_dxdy parsed) layout)))
          rintro d s ⟨⟨precincts, count⟩, packets, reference⟩
          simp only [count]
          exact tail (.present chunks selected index stream packets reference precincts count)
            (n + d.passes) (j + 1)
        · simp only [index, ↓reduceIte, Option.isSome_none, Bool.false_eq_true, pure_bind]
          exact tail (.absent (by simp [selected, index])) n j
    · exact ⟨rfl, rfl, rfl, start⟩
  · intro a b hab
    exact st.finishRel info planes allocated _ _ _ hab.2.2.2

end JPEG2000.Spec.NativeTraversal
