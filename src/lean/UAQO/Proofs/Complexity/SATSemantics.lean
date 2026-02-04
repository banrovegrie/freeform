/-
  Proofs for SAT semantics axioms in Hardness.lean.

  Eliminates:
  - satisfies_iff_countUnsatisfied_zero
-/
import UAQO.Complexity.Basic

namespace UAQO.Complexity.Proofs

open UAQO.Complexity

/-- An assignment satisfies a formula iff it has 0 unsatisfied clauses.

    Proof: satisfies means all clauses evaluate to true (evalCNF = true),
    which means the filter of unsatisfied clauses (those evaluating to false)
    is empty, which means its length equals 0. -/
theorem satisfies_iff_countUnsatisfied_zero_proof (f : CNFFormula) (z : Fin (2^f.numVars)) :
    satisfies (finToAssignment f.numVars z) f ↔ countUnsatisfiedClauses f z = 0 := by
  simp only [satisfies, evalCNF, countUnsatisfiedClauses]
  constructor
  · -- Forward: satisfies → count = 0
    intro h
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro c hc
    have heval := List.all_eq_true.mp h c hc
    simp only [Bool.not_eq_true]
    exact Bool.eq_false_iff.mpr (Bool.not_not.mp (Bool.not_eq_false.mpr heval))
  · -- Backward: count = 0 → satisfies
    intro h
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff] at h
    rw [List.all_eq_true]
    intro c hc
    specialize h c hc
    simp only [Bool.not_eq_true] at h
    exact Bool.not_eq_false.mp h

end UAQO.Complexity.Proofs
