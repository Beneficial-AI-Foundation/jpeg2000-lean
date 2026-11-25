/-
Axiom audit, run by `scripts/check-hygiene.sh` via `lake env lean scripts/axioms.lean`
(Plan.md section 3 rule 1, task 0.3).

Every top-level theorem of the project must depend only on `propext`, `Classical.choice` and
`Quot.sound` (CLAUDE.md, Plan.md section 3).  The guard parses the output of this file and
fails on any other axiom (including `sorryAx`, `Lean.ofReduceBool`, `Lean.trustCompiler` and
the auxiliary axioms `native_decide` creates), and on any `#print axioms` line that produced
no result.  `scripts/hygiene.py` also fails if a non-private `theorem` in `JPEG2000/` or
`Spec/` is not listed here.

To add a check: make sure the module is reachable from the imports below (the umbrellas
import every module), then add one line
    #print axioms Namespace.theorem_name
under a comment naming the task.  This file is a shared registry (CLAUDE.md): subagents report
the lines to add; the orchestrator adds them.  It is outside the libraries and never imported.
-/
import JPEG2000
import Spec
import Encode

/-! ## Guard self-check

Two theorems defined here so that the check exercises a real `#print axioms` result even
before the project has theorems: one with no axioms, one that uses all three allowed ones. -/

namespace AxiomsSelfCheck

/-- No axioms at all. -/
theorem noAxioms (a b : Nat) : a + b = b + a := Nat.add_comm a b

/-- Excluded middle: depends on `propext`, `Classical.choice`, `Quot.sound`. -/
theorem allowedAxioms (p : Prop) : p ∨ ¬p := Classical.em p

end AxiomsSelfCheck

#print axioms AxiomsSelfCheck.noAxioms
#print axioms AxiomsSelfCheck.allowedAxioms

/-! ## Project theorems (one line per top-level theorem, grouped by task) -/

-- Phase 0, task 0.2: limits (JPEG2000/Limits.lean)
#print axioms JPEG2000.Limits.checkLe_eq_ok_iff
#print axioms JPEG2000.Limits.check_eq_ok_iff
#print axioms JPEG2000.Limits.checkLe_eq_error
#print axioms JPEG2000.Limits.strict_le_default

-- Phase 1, task 1.1: bytes (JPEG2000/Bytes.lean)
#print axioms JPEG2000.Bytes.Reader.pos_le_size
#print axioms JPEG2000.Bytes.Reader.u8_pos
#print axioms JPEG2000.Bytes.Reader.u16be_pos
#print axioms JPEG2000.Bytes.Reader.u32be_pos
#print axioms JPEG2000.Bytes.Reader.u64be_pos
#print axioms JPEG2000.Bytes.Reader.skip_pos
#print axioms JPEG2000.Bytes.Reader.take_spec
#print axioms JPEG2000.Bytes.Reader.u8_error
#print axioms JPEG2000.Bytes.BitReader.load_pos
#print axioms JPEG2000.Bytes.BitReader.bit_pos
#print axioms JPEG2000.Bytes.BitReader.bitsAux_pos
#print axioms JPEG2000.Bytes.BitReader.bits_pos
#print axioms JPEG2000.Bytes.BitReader.align_pos
#print axioms JPEG2000.Bytes.size_pushZeros
#print axioms JPEG2000.Bytes.get_pushZeros
#print axioms JPEG2000.Bytes.Plane.zero_dims
#print axioms JPEG2000.Bytes.Plane.set_dims
#print axioms JPEG2000.Bytes.Plane.get_set_self
#print axioms JPEG2000.Bytes.Plane.get_set_ne
#print axioms JPEG2000.Bytes.Plane.get_zero

-- Phase 1, task 1.2: boxes (JPEG2000/Box.lean)
#print axioms JPEG2000.Box.parseFile_range

-- Phase 2, task 2.1: MQ spec (Spec/MQ.lean)
#print axioms JPEG2000.Spec.MQ.qe_bounds
#print axioms JPEG2000.Spec.MQ.qeAt_qe_bounds
#print axioms JPEG2000.Spec.MQ.bit15_iff
#print axioms JPEG2000.Spec.MQ.bytein_A
#print axioms JPEG2000.Spec.MQ.bytein_C_lt
#print axioms JPEG2000.Spec.MQ.bytein_CT_le
#print axioms JPEG2000.Spec.MQ.bytein_pos_le
#print axioms JPEG2000.Spec.MQ.bytein_data
#print axioms JPEG2000.Spec.MQ.renormStep_A
#print axioms JPEG2000.Spec.MQ.renormLoop_bit15
#print axioms JPEG2000.Spec.MQ.renormd_fuel_suffices
#print axioms JPEG2000.Spec.MQ.lpsExchange_A
#print axioms JPEG2000.Spec.MQ.decode_A_range
