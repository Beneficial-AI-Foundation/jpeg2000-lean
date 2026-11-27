import JPEG2000.MQ
import Spec.MQ

/-!
# Agreement of the fast MQ tables with Table C.2

Plan.md §4 (C2), §5.2 "MQ decoder"; T.800 Annex C, Table C.2 and Figures C.16/C.17.

The fast decoder `JPEG2000.MQ` reads the whole context transition of `LPS_EXCHANGE` /
`MPS_EXCHANGE` from one entry of `JPEG2000.MQ.qeTab`, indexed by the packed context byte
`index <<< 1 ||| mps`. This file proves, for every one of the 256 bytes, that the entry agrees
with the specification `JPEG2000.Spec.MQ.qeAt` (rows of `qeTable`, row 0 past row 46): the
`Qe` value, the state after an MPS renormalisation and the state after an LPS renormalisation
(with the MPS sense switched when `SWITCH = 1`). It is a building block of C2 (task 2.5).
-/

namespace JPEG2000.Spec.MQTable

open JPEG2000.MQ

/-- The context state a packed byte stands for: `index = b >>> 1`, `mps = b AND 1`. -/
def stateOf (b : UInt8) : Spec.MQ.CxState := ⟨b.toNat / 2, b.toNat % 2 == 1⟩

/-- `mkEntry n` agrees with Table C.2 for every packed context byte `n < 256` (checked by
the kernel over all 256 values). -/
theorem mkEntry_agree : ∀ n, n < 256 →
    let st := stateOf n.toUInt8
    let e := Spec.MQ.qeAt st.index
    ((mkEntry n) >>> 16).toNat = e.qe ∧
    stateOf ((mkEntry n) >>> 8).toUInt8 = { st with index := e.nmps } ∧
    stateOf (mkEntry n).toUInt8 =
      { index := e.nlps, mps := if e.switch then !st.mps else st.mps } := by
  decide +kernel

/-- `entry s` is `mkEntry s.toNat`. -/
theorem entry_eq (s : UInt8) : entry s = mkEntry s.toNat := by
  simp [entry, qeTab]

/-- `qeTab_agree`: for every context byte `s`, the fast table entry `entry s` gives the
`Qe` of Table C.2 for the state `stateOf s` (bits 31..16), the packed state after an MPS
exchange (bits 15..8: `NMPS`, same MPS) and after an LPS exchange (bits 7..0: `NLPS`, MPS
switched iff `SWITCH`), exactly as `Spec.MQ.lpsExchange` / `Spec.MQ.mpsExchange`. -/
theorem qeTab_agree (s : UInt8) :
    let st := stateOf s
    let e := Spec.MQ.qeAt st.index
    ((entry s) >>> 16).toNat = e.qe ∧
    stateOf ((entry s) >>> 8).toUInt8 = { st with index := e.nmps } ∧
    stateOf (entry s).toUInt8 =
      { index := e.nlps, mps := if e.switch then !st.mps else st.mps } := by
  have h := mkEntry_agree s.toNat (UInt8.toNat_lt s)
  rw [entry_eq]
  simpa using h

/-- The packed initial contexts stand for the spec's initial contexts (for `inits` below
128, where an index fits in seven bits). -/
theorem stateOf_packCx (i : Nat) (h : i < 128) : stateOf (packCx i false) = ⟨i, false⟩ := by
  have h1 : (UInt8.ofNat (i * 2)).toNat = i * 2 := by
    simp only [UInt8.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  simp only [stateOf, packCx, Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Nat.toUInt8, h1]
  congr 1 <;> simp <;> omega

end JPEG2000.Spec.MQTable
