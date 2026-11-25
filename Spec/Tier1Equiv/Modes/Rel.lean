import Spec.Tier1Equiv
import JPEG2000.Tier1.Modes

/-!
# C3 (all code-block styles), part 1: the mode-aware simulation relation

Plan.md §4 (C3), §5.2 "Tier-1 / EBCOT" (staged modes); T.800 D.3.1–D.3.4, D.6 (raw bit
reader), D.7 (vertically causal context formation), Tables D.1–D.4. Task 7.1c.

The plain-mode relation `Spec.Tier1Equiv.Rel` (task 3.6) is generalised in two directions:

* **Vertically causal context formation.** The geometry is `gV w h b vc` (`vertCausal := vc`)
  and neighbour bits 0–11 of a flag word are prescribed by `Geom.nbAt` (a neighbour hidden by
  `Geom.hidden` reads as insignificant), `specBitV`. The fast decoder realises this at write
  time (`JPEG2000.Tier1.setSig` skips the row above at stripe tops), so its flag words carry
  exactly the hidden-aware bits and every context look-up stays one table read.
* **The coder.** `Coder start raw` relates the fast `MQ.Dec` record either to the spec MQ
  registers and contexts (`MQEquiv.Rel`, an MQ codeword segment starting at buffer offset
  `start`), or — in a raw (bypass) segment — to the spec raw reader `RawState` (`RawSim`)
  with the 19 context states still related (`MQEquiv.CxRel`; they persist across a raw
  segment).

`RelM w h b vc start raw s d` is the relation; from it every context and test computed from a
flag word equals the spec's under `gV` (`zc_relM`, `sign_relM'`, `mr_relM`, `sigTest_relM`,
`nbrTest_relM`, `sigVisTest_relM`, `visTest_relM`, `rlTest_relM`).
-/

namespace JPEG2000.Spec.Tier1EquivM

open JPEG2000
open JPEG2000.Tier2.Geometry (Band)
open JPEG2000.Spec.Tier1 (Coeff Geom DecState Orientation NeighbourSign RawState)
open JPEG2000.Spec.Tier1Equiv

/-! ## Geometry -/

/-- The spec geometry of a block of a style with vertically causal flag `vc`
(`Spec.Tier1.CodeBlock.geom`). -/
def gV (w h : Nat) (b : Band) (vc : Bool) : Geom :=
  { width := w, height := h, orient := orientOf b, vertCausal := vc }

/-- Coefficient reads do not depend on the vertically causal flag. -/
theorem coeffAt_gV (w h : Nat) (b : Band) (vc : Bool) :
    (gV w h b vc).coeffAt = (sgeom w h b).coeffAt := rfl

/-- Coefficient writes do not depend on the vertically causal flag. -/
theorem setCoeff_gV (w h : Nat) (b : Band) (vc : Bool) :
    (gV w h b vc).setCoeff = (sgeom w h b).setCoeff := rfl

/-- Bit `j` of the flag word that the spec state `cs` prescribes at `(x, y)` under geometry
`g`: bits 0–11 read the neighbours through `Geom.nbAt` (hidden ones are insignificant), bits
12–15 the coefficient's own state. -/
def specBitV (g : Geom) (cs : Array Coeff) (x y : Nat) (j : Nat) : Bool :=
  if j < 12 then
    let c := g.nbAt cs y (nbPos j x y).1 (nbPos j x y).2
    if j < 8 then c.sig else c.sig && c.sign
  else ownBit (g.coeffAt cs x y) j

/-! ## The coder -/

/-- The raw (D.6) bit reader simulation: the fast `MQ.Dec` record used as a raw reader
(`JPEG2000.Tier1.rawBit`: `c` the current byte, `ct` its unread bits, `pos` the absolute byte
pointer) against the spec `RawState` of a segment starting at buffer offset `start`. -/
structure RawSim (start : Nat) (d : MQ.Dec) (r : RawState) : Prop where
  /-- The current byte. -/
  c : d.c.toNat = r.byte
  /-- Unread bits. -/
  ct : d.ct.toNat = r.ct
  /-- At most 8 unread bits. -/
  ctle : r.ct ≤ 8
  /-- The current byte is a byte. -/
  blt : r.byte < 256
  /-- The pointer, offset by the segment start. -/
  pos : d.pos = start + r.pos
  /-- Every byte read agrees (`0xFF` past the end on both sides). -/
  data : ∀ j, (d.byteAt (start + j)).toNat = Spec.MQ.byteAt r.data j

/-- The coder relation: an MQ segment (`raw = false`: C2's `MQEquiv.Rel`) or a raw segment
(`raw = true`: `RawSim` and the contexts). -/
def Coder (start : Nat) : Bool → MQ.Dec → Spec.MQ.State → Spec.MQ.Contexts → RawState → Prop
  | false, mq, q, cxs, _ => MQEquiv.Rel start mq q cxs
  | true, mq, _, cxs, r => RawSim start mq r ∧ MQEquiv.CxRel mq.cx cxs

/-- **The mode-aware simulation relation** between the fast state `s` and the spec state `d`
(module doc). -/
structure RelM (w h : Nat) (b : Band) (vc : Bool) (start : Nat) (raw : Bool)
    (s : JPEG2000.Tier1.St) (d : DecState) : Prop where
  /-- MQ or raw coder. -/
  coder : Coder start raw s.mq d.mq d.cxs d.raw
  /-- Size of the bordered flag array. -/
  fsize : s.flags.size = (w + 2) * (h + 2)
  /-- Size of the bordered magnitude array. -/
  msize : s.mags.size = (w + 2) * (h + 2)
  /-- Size of the spec coefficient array. -/
  csize : d.coeffs.size = w * h
  /-- Flag bits 0–15 of every in-block word. -/
  flag : ∀ x y j, x < w → y < h → j < 16 →
    bt (JPEG2000.Tier1.fget s.flags (bidx w x y)) j = specBitV (gV w h b vc) d.coeffs x y j
  /-- Magnitudes, modulo `2^32`. -/
  mag : ∀ x y, x < w → y < h →
    (JPEG2000.Tier1.fget s.mags (bidx w x y)).toNat =
      ((gV w h b vc).coeffAt d.coeffs x y).mag % 2 ^ 32

/-! ## Bits of the flag word -/

section bits
variable {w h : Nat} {b : Band} {vc : Bool} {start : Nat} {raw : Bool} {s : JPEG2000.Tier1.St}
  {d : DecState}
variable (R : RelM w h b vc start raw s d) {x y : Nat} (hx : x < w) (hy : y < h)
include R hx hy

/-- Neighbour significance bits 0–7. -/
theorem bitV_nb (j : Nat) (hj : j < 8) :
    bt (JPEG2000.Tier1.fget s.flags (bidx w x y)) j =
      ((gV w h b vc).nbAt d.coeffs y (nbPos j x y).1 (nbPos j x y).2).sig := by
  rw [R.flag x y j hx hy (by omega)]; simp [specBitV, show j < 12 by omega, hj]

/-- Neighbour sign bits 8–11. -/
theorem bitV_nbneg (j : Nat) (hj1 : 8 ≤ j) (hj : j < 12) :
    bt (JPEG2000.Tier1.fget s.flags (bidx w x y)) j =
      (((gV w h b vc).nbAt d.coeffs y (nbPos j x y).1 (nbPos j x y).2).sig &&
       ((gV w h b vc).nbAt d.coeffs y (nbPos j x y).1 (nbPos j x y).2).sign) := by
  rw [R.flag x y j hx hy (by omega)]; simp [specBitV, hj, show ¬ j < 8 by omega]

/-- Own bits 12–15. -/
theorem bitV_own :
    bt (JPEG2000.Tier1.fget s.flags (bidx w x y)) 12 = ((gV w h b vc).coeffAt d.coeffs x y).sig ∧
    bt (JPEG2000.Tier1.fget s.flags (bidx w x y)) 13 =
      (((gV w h b vc).coeffAt d.coeffs x y).sig && ((gV w h b vc).coeffAt d.coeffs x y).sign) ∧
    bt (JPEG2000.Tier1.fget s.flags (bidx w x y)) 14 =
      ((gV w h b vc).coeffAt d.coeffs x y).visited ∧
    bt (JPEG2000.Tier1.fget s.flags (bidx w x y)) 15 =
      ((gV w h b vc).coeffAt d.coeffs x y).refined := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [R.flag x y _ hx hy (by decide)] <;> simp [specBitV, ownBit]

end bits

/-! ## Spec "some neighbour is significant" -/

/-- The spec's `anySigNeighbour` from the eight (hidden-aware) neighbour states. -/
theorem anySig_eqV (g : Geom) (cs : Array Coeff) (x y : Nat) :
    g.anySigNeighbour cs x y =
      ((List.range 8).any fun j => (g.nbAt cs y (nbPos j x y).1 (nbPos j x y).2).sig) := by
  simp only [Geom.anySigNeighbour, Geom.sigCounts, Geom.nbSig]
  simp only [List.range, List.range.loop, List.any_cons, List.any_nil, nbPos]
  try simp only [Nat.reduceMod]
  generalize (g.nbAt cs y (↑x - 1) ↑y).sig = a1
  generalize (g.nbAt cs y (↑x + 1) ↑y).sig = a2
  generalize (g.nbAt cs y ↑x (↑y - 1)).sig = a3
  generalize (g.nbAt cs y ↑x (↑y + 1)).sig = a4
  generalize (g.nbAt cs y (↑x - 1) (↑y - 1)).sig = a5
  generalize (g.nbAt cs y (↑x + 1) (↑y - 1)).sig = a6
  generalize (g.nbAt cs y (↑x - 1) (↑y + 1)).sig = a7
  generalize (g.nbAt cs y (↑x + 1) (↑y + 1)).sig = a8
  cases a1 <;> cases a2 <;> cases a3 <;> cases a4 <;> cases a5 <;> cases a6 <;> cases a7 <;>
    cases a8 <;> decide

/-! ## Contexts and tests: fast = spec -/

section ctx
variable {w h : Nat} {b : Band} {vc : Bool} {start : Nat} {raw : Bool} {s : JPEG2000.Tier1.St}
  {d : DecState}
variable (R : RelM w h b vc start raw s d) {x y : Nat} (hx : x < w) (hy : y < h)
include R hx hy

/-- Zero coding (Table D.1, hidden-aware counts): the look-up equals the spec context. -/
theorem zc_relM :
    JPEG2000.Tier1.zcCtx (JPEG2000.Tier1.zcFor b) (JPEG2000.Tier1.zcFor_size b)
        (JPEG2000.Tier1.fget s.flags (bidx w x y)) =
      (gV w h b vc).zcCtx d.coeffs x y := by
  rw [zcCtx_eq, zcOf_eq]
  simp only [bitOf_lt8 _ _ (show 0 < 8 by decide), bitOf_lt8 _ _ (show 1 < 8 by decide),
    bitOf_lt8 _ _ (show 2 < 8 by decide), bitOf_lt8 _ _ (show 3 < 8 by decide),
    bitOf_lt8 _ _ (show 4 < 8 by decide), bitOf_lt8 _ _ (show 5 < 8 by decide),
    bitOf_lt8 _ _ (show 6 < 8 by decide), bitOf_lt8 _ _ (show 7 < 8 by decide)]
  have e : ∀ j, j < 8 → (JPEG2000.Tier1.fget s.flags (bidx w x y)).toNat.testBit j =
      ((gV w h b vc).nbAt d.coeffs y (nbPos j x y).1 (nbPos j x y).2).sig :=
    fun j hj => bitV_nb R hx hy j hj
  rw [e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide), e 4 (by decide),
    e 5 (by decide), e 6 (by decide), e 7 (by decide)]
  simp only [Geom.zcCtx, Geom.sigCounts, Geom.nbSig, nbPos, Nat.reduceMod]
  rfl

/-- Sign coding (Tables D.2, D.3, hidden-aware): the look-up entry is the spec context
`* 2 + XORbit`. -/
theorem sign_relM :
    (JPEG2000.Tier1.scEntry (JPEG2000.Tier1.fget s.flags (bidx w x y))).toNat =
      ((gV w h b vc).signContext d.coeffs x y).1 * 2 +
        if ((gV w h b vc).signContext d.coeffs x y).2 then 1 else 0 := by
  rw [scEntry_eq]
  have e : ∀ j, j < 8 → bt (JPEG2000.Tier1.fget s.flags (bidx w x y)) j =
      ((gV w h b vc).nbAt d.coeffs y (nbPos j x y).1 (nbPos j x y).2).sig :=
    fun j hj => bitV_nb R hx hy j hj
  have e' : ∀ j, 8 ≤ j → j < 12 → bt (JPEG2000.Tier1.fget s.flags (bidx w x y)) j =
      (((gV w h b vc).nbAt d.coeffs y (nbPos j x y).1 (nbPos j x y).2).sig &&
       ((gV w h b vc).nbAt d.coeffs y (nbPos j x y).1 (nbPos j x y).2).sign) :=
    fun j hj1 hj => bitV_nbneg R hx hy j hj1 hj
  rw [e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide),
    e' 8 (by decide) (by decide), e' 9 (by decide) (by decide), e' 10 (by decide) (by decide),
    e' 11 (by decide) (by decide)]
  simp only [scSpec, ofBits_and, Geom.signContext, Geom.nbSign, nbPos, Nat.reduceMod]
  rfl

/-- The decision context and `XORbit` of the sign look-up. -/
theorem sign_relM' :
    ((JPEG2000.Tier1.scEntry (JPEG2000.Tier1.fget s.flags (bidx w x y))) >>> 1).toNat =
      ((gV w h b vc).signContext d.coeffs x y).1 ∧
    ((JPEG2000.Tier1.scEntry (JPEG2000.Tier1.fget s.flags (bidx w x y))) &&& 1 != 0) =
      ((gV w h b vc).signContext d.coeffs x y).2 := by
  have hs := sign_relM R hx hy
  generalize JPEG2000.Tier1.scEntry (JPEG2000.Tier1.fget s.flags (bidx w x y)) = e at hs ⊢
  generalize ((gV w h b vc).signContext d.coeffs x y) = r at hs ⊢
  obtain ⟨c, xb⟩ := r
  have h1 : (e >>> 1).toNat = e.toNat / 2 := by
    simp [UInt8.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  have h2 : (e &&& 1).toNat = e.toNat % 2 := by
    rw [UInt8.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod _ 1
  refine ⟨by rw [h1, hs]; cases xb <;> simp <;> omega, ?_⟩
  rw [u8_bne, h2, hs]; cases xb <;> simp <;> omega

/-- `f &&& SIG == 0` is "not significant". -/
theorem sigTest_relM :
    (JPEG2000.Tier1.fget s.flags (bidx w x y) &&& JPEG2000.Tier1.SIG == 0) =
      !((gV w h b vc).coeffAt d.coeffs x y).sig := by
  rw [and_eq_zero_iff _ _ (by decide)]
  simp [List.range, List.range.loop, JPEG2000.Tier1.SIG, testBit_lit, bt]
  rw [← (bitV_own R hx hy).1]; rfl

/-- `f &&& SIG_NBRS != 0` is "some (visible) neighbour is significant". -/
theorem nbrTest_relM :
    (JPEG2000.Tier1.fget s.flags (bidx w x y) &&& JPEG2000.Tier1.SIG_NBRS != 0) =
      (gV w h b vc).anySigNeighbour d.coeffs x y := by
  have : (JPEG2000.Tier1.fget s.flags (bidx w x y) &&& JPEG2000.Tier1.SIG_NBRS != 0) =
      !(JPEG2000.Tier1.fget s.flags (bidx w x y) &&& JPEG2000.Tier1.SIG_NBRS == 0) := rfl
  rw [this, and_eq_zero_iff _ _ (by decide), anySig_eqV]
  have e : ∀ j, j < 8 → bt (JPEG2000.Tier1.fget s.flags (bidx w x y)) j =
      ((gV w h b vc).nbAt d.coeffs y (nbPos j x y).1 (nbPos j x y).2).sig :=
    fun j hj => bitV_nb R hx hy j hj
  simp only [List.range, List.range.loop, List.any_cons, List.any_nil, JPEG2000.Tier1.SIG_NBRS,
    bt, testBit_lit, UInt32.reduceToNat]
  simp only [bt] at e
  simp [e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide), e 4 (by decide),
    e 5 (by decide), e 6 (by decide), e 7 (by decide)]

/-- `f &&& (SIG ||| VIS) == 0` is "neither significant nor visited". -/
theorem sigVisTest_relM :
    (JPEG2000.Tier1.fget s.flags (bidx w x y) &&& (JPEG2000.Tier1.SIG ||| JPEG2000.Tier1.VIS) == 0) =
      (!((gV w h b vc).coeffAt d.coeffs x y).sig &&
        !((gV w h b vc).coeffAt d.coeffs x y).visited) := by
  rw [and_eq_zero_iff _ _ (by decide)]
  obtain ⟨o1, -, o3, -⟩ := bitV_own R hx hy
  simp only [bt] at o1 o3
  simp [List.range, List.range.loop, JPEG2000.Tier1.SIG, JPEG2000.Tier1.VIS, testBit_lit, bt, o1, o3]

/-- `f &&& VIS == 0` is "not visited". -/
theorem visTest_relM :
    (JPEG2000.Tier1.fget s.flags (bidx w x y) &&& JPEG2000.Tier1.VIS == 0) =
      !((gV w h b vc).coeffAt d.coeffs x y).visited := by
  rw [and_eq_zero_iff _ _ (by decide)]
  obtain ⟨-, -, o3, -⟩ := bitV_own R hx hy
  simp only [bt] at o3
  simp [List.range, List.range.loop, JPEG2000.Tier1.VIS, testBit_lit, bt, o3]

/-- `f &&& NEG != 0` is "significant and negative". -/
theorem negTest_relM :
    (JPEG2000.Tier1.fget s.flags (bidx w x y) &&& JPEG2000.Tier1.NEG != 0) =
      (((gV w h b vc).coeffAt d.coeffs x y).sig && ((gV w h b vc).coeffAt d.coeffs x y).sign) := by
  have : (JPEG2000.Tier1.fget s.flags (bidx w x y) &&& JPEG2000.Tier1.NEG != 0) =
      !(JPEG2000.Tier1.fget s.flags (bidx w x y) &&& JPEG2000.Tier1.NEG == 0) := rfl
  rw [this, and_eq_zero_iff _ _ (by decide)]
  obtain ⟨-, o2, -, -⟩ := bitV_own R hx hy
  simp only [bt] at o2
  simp [List.range, List.range.loop, JPEG2000.Tier1.NEG, testBit_lit, bt, o2]

/-- Magnitude refinement (Table D.4): the computed context equals the spec context. -/
theorem mr_relM :
    JPEG2000.Tier1.mrCtxOf (JPEG2000.Tier1.fget s.flags (bidx w x y)) =
      (gV w h b vc).mrCtx d.coeffs x y := by
  have hn := nbrTest_relM R hx hy
  have href : (JPEG2000.Tier1.fget s.flags (bidx w x y) &&& JPEG2000.Tier1.REF != 0) =
      ((gV w h b vc).coeffAt d.coeffs x y).refined := by
    have : (JPEG2000.Tier1.fget s.flags (bidx w x y) &&& JPEG2000.Tier1.REF != 0) =
        !(JPEG2000.Tier1.fget s.flags (bidx w x y) &&& JPEG2000.Tier1.REF == 0) := rfl
    rw [this, and_eq_zero_iff _ _ (by decide)]
    obtain ⟨-, -, -, o4⟩ := bitV_own R hx hy
    simp only [bt] at o4
    simp [List.range, List.range.loop, JPEG2000.Tier1.REF, testBit_lit, bt, o4]
  simp only [JPEG2000.Tier1.mrCtxOf, Geom.mrCtx, Spec.Tier1.mrContext, href, hn, Bool.not_not]
  all_goals (split <;> simp_all)

/-- The run-length word test: insignificant, not visited, no (visible) significant
neighbour. -/
theorem rlTest_relM :
    (JPEG2000.Tier1.fget s.flags (bidx w x y) &&&
        (JPEG2000.Tier1.SIG ||| JPEG2000.Tier1.VIS ||| JPEG2000.Tier1.SIG_NBRS) == 0) =
      (!((gV w h b vc).coeffAt d.coeffs x y).sig && !((gV w h b vc).coeffAt d.coeffs x y).visited &&
        !(gV w h b vc).anySigNeighbour d.coeffs x y) := by
  have e : (JPEG2000.Tier1.SIG ||| JPEG2000.Tier1.VIS ||| JPEG2000.Tier1.SIG_NBRS) =
      (JPEG2000.Tier1.SIG ||| JPEG2000.Tier1.VIS) ||| JPEG2000.Tier1.SIG_NBRS := rfl
  have key : ∀ f M N : UInt32, (f &&& (M ||| N) == 0) = ((f &&& M == 0) && (f &&& N == 0)) := by
    intro f M N
    have : f &&& (M ||| N) = (f &&& M) ||| (f &&& N) := by
      apply UInt32.toNat_inj.mp; simp [UInt32.toNat_and, UInt32.toNat_or, Nat.and_or_distrib_left]
    rw [this]
    have k2 := or_test (f &&& M) (f &&& N) 0xFFFFFFFF
    have : ∀ u : UInt32, u &&& 0xFFFFFFFF = u := by
      intro u; apply UInt32.toNat_inj.mp
      rw [UInt32.toNat_and]
      have := u.toNat_lt
      have h' : (0xFFFFFFFF : UInt32).toNat = 2 ^ 32 - 1 := rfl
      rw [h', Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_eq_of_lt this
    simp only [this] at k2; exact k2
  rw [e, key, sigVisTest_relM R hx hy]
  have hn := nbrTest_relM R hx hy
  rw [show (JPEG2000.Tier1.fget s.flags (bidx w x y) &&& JPEG2000.Tier1.SIG_NBRS != 0) =
    !(JPEG2000.Tier1.fget s.flags (bidx w x y) &&& JPEG2000.Tier1.SIG_NBRS == 0) from rfl] at hn
  rw [← hn, Bool.not_not]

end ctx

end JPEG2000.Spec.Tier1EquivM
