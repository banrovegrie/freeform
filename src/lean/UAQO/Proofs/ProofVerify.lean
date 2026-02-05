/-
  Verification file for all proofs.

  Imports all proof modules to verify they compile correctly.
-/

-- Mathlib bridges
import UAQO.Proofs.Mathlib.FinsetArithmetic

-- Foundations proofs
import UAQO.Proofs.Foundations.VariationalPrinciple

-- Spectral proofs
import UAQO.Proofs.Spectral.A2Bounds
import UAQO.Proofs.Spectral.ShermanMorrison
import UAQO.Proofs.Spectral.EigenvalueCondition
import UAQO.Proofs.Spectral.MatrixDetLemma
import UAQO.Proofs.Spectral.GapBoundsProofs

-- Adiabatic proofs
import UAQO.Proofs.Adiabatic.ScheduleProperties

-- Complexity proofs
import UAQO.Proofs.Complexity.SATSemantics
import UAQO.Proofs.Complexity.ModifiedHamDeg
import UAQO.Proofs.Complexity.BetaModifiedHam
import UAQO.Proofs.Complexity.LagrangeInterp

namespace UAQO.Proofs

/-!
# Axiom Elimination Status

## Fully Proved (0 sorry in all proof files)

### Core Quantum Mechanics
- `eigenvalue_condition` (EigenvalueCondition.lean - FULL PROOF)
  Key insight: non-degenerate eigenvalues (d_k=1) are NOT eigenvalues of H(s) for s>0.
- `variational_principle` (SpectralTheory.lean - full proof using spectral decomposition)
- `variational_minimum` (SpectralTheory.lean - full proof via ground eigenstate)
- `shermanMorrison_resolvent` (GapBounds.lean - full proof via matrix verification)

### SAT Semantics
- `satisfies_iff_countUnsatisfied_zero` (SATSemantics.lean)
- `threeSATDegPositive_ground` (SATSemantics.lean)

### Modified Hamiltonian
- `modifiedHam_deg_sum` (Hardness.lean - now a theorem)
- `modifiedHam_deg_count` (ModifiedHamDeg.lean - full proof)
- `betaModifiedHam_deg_sum` (BetaModifiedHam.lean)
- `betaModifiedHam_deg_count` (BetaModifiedHam.lean)
- `betaModifiedHam_eigenval_ordered` (Hardness.lean - proved with gap constraint)
- `betaModifiedHam_eigenval_ordered_strict` (Hardness.lean - proved with strict gap constraint)
- `betaModifiedHam_eigenval_bounds` (Hardness.lean - proved with eigenvalue bound hypothesis)

### Auxiliary
- `lagrange_interpolation` (LagrangeInterp.lean)
- `adiabaticHam_hermitian` (GapBoundsProofs.lean - H(s) is Hermitian)
- `diagonalHam_hermitian` (GapBoundsProofs.lean - diagonal Hamiltonian is Hermitian)
- `expectation_hermitian_real` (GapBoundsProofs.lean - expectation of Hermitian has real value)

### Mathlib Bridge (GapBoundsProofs.lean)
- `exists_eigenvalue_of_hermitian` - extracts eigenvalue/eigenvector from Matrix.IsHermitian
- `mathlib_to_our_eigenvalue` - converts Mathlib eigenvalue to our IsEigenvalue
- `adiabaticHam_matrix_hermitian` - converts our IsHermitian to Matrix.IsHermitian
- `min_eigenvalue_of_hermitian` - minimum eigenvalue using Finset.min'
- `min_eigenvalue_to_our` - converts minimum eigenvalue to our IsEigenvalue
- `euclideanSpace_inner_eq_star_dotProduct` - inner product equals star dotProduct
- `complex_norm_sq_eq_normSq` - ‖z‖² = Complex.normSq z
- `euclideanSpace_norm_sq_eq_normSquared` - EuclideanSpace norm to our normSquared
- `spectral_expansion_quadratic_form` - FULL PROOF: phi* A phi = Σ_k λ_k |c_k|²
- `parseval_normSquared` - FULL PROOF: Σ_k |⟨v_k|phi⟩|² = normSquared phi
- `weighted_sum_ge_min_times_sum` - FULL PROOF: convex combination bound
- `expectation_ge_min_eigenvalue` - FULL PROOF: expectation ≥ min eigenvalue
- `groundEnergy_variational_bound_proof` - FULL PROOF: E0 ≤ ⟨phi|H|phi⟩

## Axioms with Formulation Issues (3 axioms)
These appear to have bugs or are unprovable as stated:
- `A2_lower_bound` (A2Bounds.lean) - bound direction reversed
- `avoidedCrossing_bound`, `piecewiseSchedule_monotone` (ScheduleProperties.lean) - missing hypothesis

## Removed Axioms
- `threeSATWellFormed_numVars` - REMOVED: was unused and unprovable without well-formedness constraints
  (CNFFormula.numVars is a field, not derived from clauses)

## External Foundations (9 axioms - kept as axioms)
Standard complexity theory and physics axioms:
- `threeSAT_in_NP`, `threeSAT_NP_complete` (Cook-Levin theorem)
- `sharpThreeSAT_in_SharpP`, `sharpThreeSAT_complete` (Valiant's theorem)
- `sharpP_solves_NP`, `degeneracy_sharpP_hard` (Oracle complexity)
- `adiabaticTheorem`, `eigenpath_traversal` (Quantum adiabatic theorem)
- `resolvent_distance_to_spectrum` (Spectral theory)

## Remaining Axioms (16 axioms needing proofs)

### GapBounds.lean (7 axioms) - Require axiom-to-theorem conversion
- `groundEnergy_variational_bound` - proof available in GapBoundsProofs.lean
- `firstExcited_lower_bound` - needs spectral decomposition
- `gap_bound_left_axiom` - depends on variational bound
- `gap_at_avoided_crossing_axiom` - perturbation analysis
- `gap_bound_right_axiom` - resolvent method (Sherman-Morrison available)
- `gap_bound_all_s_axiom` - combines regional bounds
- `gap_minimum_at_crossing_axiom` - structural result

### RunningTime.lean (4 axioms) - Depend on gap bounds
- `mainResult1` - running time T = O(1/Δ)
- `runningTime_ising_bound` - Ising model bound
- `lowerBound_unstructuredSearch` - BBBV lower bound
- `runningTime_matches_lower_bound` - optimality

### Hardness.lean (5 axioms) - Complexity results
- `mainResult2` - NP-hardness of approximating A1
- `A1_approx_implies_P_eq_NP` - P vs NP implication
- `A1_polynomial_in_beta` - A1 is polynomial in β
- `mainResult3` - #P-hardness of exact computation
- `mainResult3_robust` - robustness to exponential errors

## Bridge Files (no axioms eliminated, provide Mathlib connections)
- `MatrixDetLemma.lean` - connects outerProd/innerProd to Mathlib equivalents
  Uses Mathlib's `det_add_replicateCol_mul_replicateRow` for matrix determinant lemma
-/

end UAQO.Proofs
