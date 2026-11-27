import Spec.Tier1Equiv.Basic

/-!
# C3 (plain mode), part 2: the simulation relation and the contexts

Plan.md §4 (C3), §5.2 "Tier-1 / EBCOT" (simulation relation between flag words and spec
state); T.800 D.3.1–D.3.4, Tables D.1–D.4. Task 3.6.

`Rel w h b start s d` relates the fast state `s : JPEG2000.Tier1.St` (MQ decoder, bordered flag
words, bordered magnitudes) to the spec state `d : Spec.Tier1.DecState`:

* the MQ registers and contexts are related by `Spec.MQEquiv.Rel` (C2);
* for every in-block `(x, y)` and bit `j < 16`, bit `j` of the flag word at `bidx w x y` is
  `specBit`: bits 0–7 the significance of the eight neighbours (N, W, E, S, NW, NE, SW, SE —
  `{}`, i.e. insignificant, outside the block), bits 8–11 `sig ∧ sign` of N, W, E, S, bits
  12–15 the coefficient's own `sig`, `sig ∧ sign`, `visited`, `refined`;
* magnitudes agree modulo `2^32` (the `UInt32` wrap; the spec invariant of part 4 bounds
  them below `2^31`);
* sizes: bordered arrays `(w + 2)(h + 2)`, coefficient array `w · h`.

Border words and bits 16–31 are unconstrained. From the relation, every context and every
test the fast decoder computes from a flag word equals the spec's (`zc_rel`, `sign_rel`,
`mr_rel`, `sigTest_rel`, …).
-/

namespace JPEG2000.Spec.Tier1Equiv

open JPEG2000
open JPEG2000.Tier2.Geometry (Band)
open JPEG2000.Spec.Tier1 (Coeff Geom DecState Orientation NeighbourSign)

/-- The spec geometry of a plain-mode block (vertically causal formation off). -/
def sgeom (w h : Nat) (b : Band) : Geom := { width := w, height := h, orient := orientOf b }

/-- The fast geometry, as `JPEG2000.Tier1.decodeCodeBlockExact` builds it. -/
def fgeo (w h : Nat) (b : Band) : Tier1.Geo :=
  { w, h, st := w + 2, zc := Tier1.zcFor b, hzc := Tier1.zcFor_size b }

/-- The neighbour read by flag bit `j` (bits 0–7: N, W, E, S, NW, NE, SW, SE; bits 8–11 repeat
N, W, E, S). -/
def nbPos (j : Nat) (x y : Int) : Int × Int :=
  match j % 8 with
  | 0 => (x, y - 1)
  | 1 => (x - 1, y)
  | 2 => (x + 1, y)
  | 3 => (x, y + 1)
  | 4 => (x - 1, y - 1)
  | 5 => (x + 1, y - 1)
  | 6 => (x - 1, y + 1)
  | _ => (x + 1, y + 1)

/-- Bit `j` of the flag word that the spec state `cs` prescribes at `(x, y)`. -/
def specBit (g : Geom) (cs : Array Coeff) (x y : Nat) (j : Nat) : Bool :=
  if j < 12 then
    let c := g.coeffAt cs (nbPos j x y).1 (nbPos j x y).2
    if j < 8 then c.sig else c.sig && c.sign
  else
    let c := g.coeffAt cs x y
    if j = 12 then c.sig
    else if j = 13 then c.sig && c.sign
    else if j = 14 then c.visited
    else if j = 15 then c.refined
    else false

/-- The simulation relation between the fast state `s` and the spec state `d` (module doc). -/
structure Rel (w h : Nat) (b : Band) (start : Nat) (s : Tier1.St) (d : DecState) : Prop where
  /-- MQ registers and contexts (C2's relation). -/
  mq : MQEquiv.Rel start s.mq d.mq d.cxs
  /-- Size of the bordered flag array. -/
  fsize : s.flags.size = (w + 2) * (h + 2)
  /-- Size of the bordered magnitude array. -/
  msize : s.mags.size = (w + 2) * (h + 2)
  /-- Size of the spec coefficient array. -/
  csize : d.coeffs.size = w * h
  /-- Flag bits 0–15 of every in-block word. -/
  flag : ∀ x y j, x < w → y < h → j < 16 →
    bt (Tier1.fget s.flags (bidx w x y)) j = specBit (sgeom w h b) d.coeffs x y j
  /-- Magnitudes, modulo `2^32`. -/
  mag : ∀ x y, x < w → y < h →
    (Tier1.fget s.mags (bidx w x y)).toNat = ((sgeom w h b).coeffAt d.coeffs x y).mag % 2 ^ 32

/-! ## Bits of the flag word, one by one -/

section bits
variable {w h : Nat} {b : Band} {start : Nat} {s : Tier1.St} {d : DecState}
variable (R : Rel w h b start s d) {x y : Nat} (hx : x < w) (hy : y < h)
include R hx hy

/-- Neighbour significance bits 0–7. -/
theorem bit_nb (j : Nat) (hj : j < 8) :
    bt (Tier1.fget s.flags (bidx w x y)) j =
      ((sgeom w h b).coeffAt d.coeffs (nbPos j x y).1 (nbPos j x y).2).sig := by
  rw [R.flag x y j hx hy (by omega)]; simp [specBit, show j < 12 by omega, hj]

/-- Neighbour sign bits 8–11. -/
theorem bit_nbneg (j : Nat) (hj1 : 8 ≤ j) (hj : j < 12) :
    bt (Tier1.fget s.flags (bidx w x y)) j =
      (((sgeom w h b).coeffAt d.coeffs (nbPos j x y).1 (nbPos j x y).2).sig &&
       ((sgeom w h b).coeffAt d.coeffs (nbPos j x y).1 (nbPos j x y).2).sign) := by
  rw [R.flag x y j hx hy (by omega)]; simp [specBit, hj, show ¬ j < 8 by omega]

/-- Own bits 12–15. -/
theorem bit_own :
    bt (Tier1.fget s.flags (bidx w x y)) 12 = ((sgeom w h b).coeffAt d.coeffs x y).sig ∧
    bt (Tier1.fget s.flags (bidx w x y)) 13 =
      (((sgeom w h b).coeffAt d.coeffs x y).sig && ((sgeom w h b).coeffAt d.coeffs x y).sign) ∧
    bt (Tier1.fget s.flags (bidx w x y)) 14 = ((sgeom w h b).coeffAt d.coeffs x y).visited ∧
    bt (Tier1.fget s.flags (bidx w x y)) 15 = ((sgeom w h b).coeffAt d.coeffs x y).refined := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [R.flag x y _ hx hy (by decide)] <;> simp [specBit]

end bits

/-! ## Spec contexts in terms of neighbour states (vertically causal formation off) -/

/-- `nbAt` is `coeffAt` in the plain geometry. -/
@[simp] theorem nbAt_sgeom (w h : Nat) (b : Band) (cs : Array Coeff) (y : Nat) (nx ny : Int) :
    (sgeom w h b).nbAt cs y nx ny = (sgeom w h b).coeffAt cs nx ny := by
  rfl

/-- The spec's "some neighbour is significant" from the eight neighbour states. -/
theorem anySig_eq (w h : Nat) (b : Band) (cs : Array Coeff) (x y : Nat) :
    (sgeom w h b).anySigNeighbour cs x y =
      ((List.range 8).any fun j =>
        ((sgeom w h b).coeffAt cs (nbPos j x y).1 (nbPos j x y).2).sig) := by
  simp only [Geom.anySigNeighbour, Geom.sigCounts, Geom.nbSig, nbAt_sgeom]
  simp only [List.range, List.range.loop, List.any_cons, List.any_nil, nbPos]
  try simp only [Nat.reduceMod]
  generalize ((sgeom w h b).coeffAt cs (↑x - 1) ↑y).sig = a1
  generalize ((sgeom w h b).coeffAt cs (↑x + 1) ↑y).sig = a2
  generalize ((sgeom w h b).coeffAt cs ↑x (↑y - 1)).sig = a3
  generalize ((sgeom w h b).coeffAt cs ↑x (↑y + 1)).sig = a4
  generalize ((sgeom w h b).coeffAt cs (↑x - 1) (↑y - 1)).sig = a5
  generalize ((sgeom w h b).coeffAt cs (↑x + 1) (↑y - 1)).sig = a6
  generalize ((sgeom w h b).coeffAt cs (↑x - 1) (↑y + 1)).sig = a7
  generalize ((sgeom w h b).coeffAt cs (↑x + 1) (↑y + 1)).sig = a8
  cases a1 <;> cases a2 <;> cases a3 <;> cases a4 <;> cases a5 <;> cases a6 <;> cases a7 <;>
    cases a8 <;> decide

/-! ## Contexts and tests: fast = spec -/

/-- A byte is non-zero iff its value is. -/
theorem u8_bne (x : UInt8) : (x != 0) = !decide (x.toNat = 0) := by
  by_cases h : x = 0
  · subst h; rfl
  · have : x.toNat ≠ 0 := fun h' => h (UInt8.toNat_inj.mp (by simpa using h'))
    simp [h, this]

/-- `NeighbourSign.ofBits` ignores the sign of an insignificant neighbour. -/
theorem ofBits_and (a n : Bool) : NeighbourSign.ofBits a (a && n) = NeighbourSign.ofBits a n := by
  cases a <;> rfl


section ctx
variable {w h : Nat} {b : Band} {start : Nat} {s : Tier1.St} {d : DecState}
variable (R : Rel w h b start s d) {x y : Nat} (hx : x < w) (hy : y < h)
include R hx hy

/-- Zero coding (Table D.1): the look-up equals the spec context. -/
theorem zc_rel :
    Tier1.zcCtx (Tier1.zcFor b) (Tier1.zcFor_size b) (Tier1.fget s.flags (bidx w x y)) =
      (sgeom w h b).zcCtx d.coeffs x y := by
  rw [zcCtx_eq, zcOf_eq]
  simp only [bitOf_lt8 _ _ (show 0 < 8 by decide), bitOf_lt8 _ _ (show 1 < 8 by decide),
    bitOf_lt8 _ _ (show 2 < 8 by decide), bitOf_lt8 _ _ (show 3 < 8 by decide),
    bitOf_lt8 _ _ (show 4 < 8 by decide), bitOf_lt8 _ _ (show 5 < 8 by decide),
    bitOf_lt8 _ _ (show 6 < 8 by decide), bitOf_lt8 _ _ (show 7 < 8 by decide)]
  have e : ∀ j, j < 8 → (Tier1.fget s.flags (bidx w x y)).toNat.testBit j =
      ((sgeom w h b).coeffAt d.coeffs (nbPos j x y).1 (nbPos j x y).2).sig :=
    fun j hj => bit_nb R hx hy j hj
  rw [e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide), e 4 (by decide),
    e 5 (by decide), e 6 (by decide), e 7 (by decide)]
  simp only [Geom.zcCtx, Geom.sigCounts, Geom.nbSig, nbAt_sgeom, nbPos, Nat.reduceMod]
  rfl

/-- Sign coding (Tables D.2, D.3): the look-up entry is the spec context `* 2 + XORbit`. -/
theorem sign_rel :
    (Tier1.scEntry (Tier1.fget s.flags (bidx w x y))).toNat =
      ((sgeom w h b).signContext d.coeffs x y).1 * 2 +
        if ((sgeom w h b).signContext d.coeffs x y).2 then 1 else 0 := by
  rw [scEntry_eq]
  have e : ∀ j, j < 8 → bt (Tier1.fget s.flags (bidx w x y)) j =
      ((sgeom w h b).coeffAt d.coeffs (nbPos j x y).1 (nbPos j x y).2).sig :=
    fun j hj => bit_nb R hx hy j hj
  have e' : ∀ j, 8 ≤ j → j < 12 → bt (Tier1.fget s.flags (bidx w x y)) j =
      (((sgeom w h b).coeffAt d.coeffs (nbPos j x y).1 (nbPos j x y).2).sig &&
       ((sgeom w h b).coeffAt d.coeffs (nbPos j x y).1 (nbPos j x y).2).sign) :=
    fun j hj1 hj => bit_nbneg R hx hy j hj1 hj
  rw [e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide),
    e' 8 (by decide) (by decide), e' 9 (by decide) (by decide), e' 10 (by decide) (by decide),
    e' 11 (by decide) (by decide)]
  simp only [scSpec, ofBits_and, Geom.signContext, Geom.nbSign, nbAt_sgeom, nbPos,
    Nat.reduceMod]

/-- The decision context and `XORbit` of the sign look-up (`becomeSig`'s `e >>> 1`, `e &&& 1`). -/
theorem sign_rel' :
    ((Tier1.scEntry (Tier1.fget s.flags (bidx w x y))) >>> 1).toNat =
      ((sgeom w h b).signContext d.coeffs x y).1 ∧
    ((Tier1.scEntry (Tier1.fget s.flags (bidx w x y))) &&& 1 != 0) =
      ((sgeom w h b).signContext d.coeffs x y).2 := by
  have hs := sign_rel R hx hy
  generalize Tier1.scEntry (Tier1.fget s.flags (bidx w x y)) = e at hs ⊢
  generalize ((sgeom w h b).signContext d.coeffs x y) = r at hs ⊢
  obtain ⟨c, xb⟩ := r
  have h1 : (e >>> 1).toNat = e.toNat / 2 := by
    simp [UInt8.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  have h2 : (e &&& 1).toNat = e.toNat % 2 := by
    rw [UInt8.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod _ 1
  refine ⟨by rw [h1, hs]; cases xb <;> simp <;> omega, ?_⟩
  rw [u8_bne, h2, hs]; cases xb <;> simp <;> omega

/-- `f &&& SIG == 0` is "not significant". -/
theorem sigTest_rel :
    (Tier1.fget s.flags (bidx w x y) &&& Tier1.SIG == 0) =
      !((sgeom w h b).coeffAt d.coeffs x y).sig := by
  rw [and_eq_zero_iff _ _ (by decide)]
  simp [List.range, List.range.loop, Tier1.SIG, testBit_lit, bt]
  rw [← (bit_own R hx hy).1]; rfl

/-- `f &&& SIG_NBRS != 0` is "some neighbour is significant". -/
theorem nbrTest_rel :
    (Tier1.fget s.flags (bidx w x y) &&& Tier1.SIG_NBRS != 0) =
      (sgeom w h b).anySigNeighbour d.coeffs x y := by
  have : (Tier1.fget s.flags (bidx w x y) &&& Tier1.SIG_NBRS != 0) =
      !(Tier1.fget s.flags (bidx w x y) &&& Tier1.SIG_NBRS == 0) := rfl
  rw [this, and_eq_zero_iff _ _ (by decide), anySig_eq]
  have e : ∀ j, j < 8 → bt (Tier1.fget s.flags (bidx w x y)) j =
      ((sgeom w h b).coeffAt d.coeffs (nbPos j x y).1 (nbPos j x y).2).sig :=
    fun j hj => bit_nb R hx hy j hj
  simp only [List.range, List.range.loop, List.any_cons, List.any_nil, Tier1.SIG_NBRS, bt,
    testBit_lit, UInt32.reduceToNat]
  simp only [bt] at e
  simp [e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide), e 4 (by decide),
    e 5 (by decide), e 6 (by decide), e 7 (by decide)]

/-- `f &&& (SIG ||| VIS) == 0` is "neither significant nor visited". -/
theorem sigVisTest_rel :
    (Tier1.fget s.flags (bidx w x y) &&& (Tier1.SIG ||| Tier1.VIS) == 0) =
      (!((sgeom w h b).coeffAt d.coeffs x y).sig && !((sgeom w h b).coeffAt d.coeffs x y).visited) := by
  rw [and_eq_zero_iff _ _ (by decide)]
  obtain ⟨o1, -, o3, -⟩ := bit_own R hx hy
  simp only [bt] at o1 o3
  simp [List.range, List.range.loop, Tier1.SIG, Tier1.VIS, testBit_lit, bt, o1, o3]

/-- `f &&& VIS == 0` is "not visited". -/
theorem visTest_rel :
    (Tier1.fget s.flags (bidx w x y) &&& Tier1.VIS == 0) =
      !((sgeom w h b).coeffAt d.coeffs x y).visited := by
  rw [and_eq_zero_iff _ _ (by decide)]
  obtain ⟨-, -, o3, -⟩ := bit_own R hx hy
  simp only [bt] at o3
  simp [List.range, List.range.loop, Tier1.VIS, testBit_lit, bt, o3]

/-- Magnitude refinement (Table D.4): the computed context equals the spec context. -/
theorem mr_rel :
    Tier1.mrCtxOf (Tier1.fget s.flags (bidx w x y)) = (sgeom w h b).mrCtx d.coeffs x y := by
  have hn := nbrTest_rel R hx hy
  have href : (Tier1.fget s.flags (bidx w x y) &&& Tier1.REF != 0) =
      ((sgeom w h b).coeffAt d.coeffs x y).refined := by
    have : (Tier1.fget s.flags (bidx w x y) &&& Tier1.REF != 0) =
        !(Tier1.fget s.flags (bidx w x y) &&& Tier1.REF == 0) := rfl
    rw [this, and_eq_zero_iff _ _ (by decide)]
    obtain ⟨-, -, -, o4⟩ := bit_own R hx hy
    simp only [bt] at o4
    simp [List.range, List.range.loop, Tier1.REF, testBit_lit, bt, o4]
  simp only [Tier1.mrCtxOf, Geom.mrCtx, Spec.Tier1.mrContext, href, hn, Bool.not_not]
  all_goals (split <;> simp_all)

end ctx

end JPEG2000.Spec.Tier1Equiv
