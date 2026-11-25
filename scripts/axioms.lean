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
