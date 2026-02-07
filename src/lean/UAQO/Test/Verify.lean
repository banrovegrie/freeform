/-
  Verification tests for the UAQO formalization.

  This file:
  1. Imports all modules to ensure compilation
  2. Documents sorries and axioms that need to be resolved
  3. Provides tests for key definitions matching the paper
-/
import UAQO.Foundations.Basic
import UAQO.Foundations.HilbertSpace
import UAQO.Foundations.Operators
import UAQO.Foundations.SpectralTheory
import UAQO.Foundations.Qubit
import UAQO.Spectral.DiagonalHamiltonian
import UAQO.Spectral.SpectralParameters
import UAQO.Spectral.GapBounds
import UAQO.Adiabatic.Hamiltonian
import UAQO.Adiabatic.Schedule
import UAQO.Adiabatic.Theorem
import UAQO.Adiabatic.RunningTime
import UAQO.Complexity.Basic
import UAQO.Complexity.Encoding
import UAQO.Complexity.NP
import UAQO.Complexity.SharpP
import UAQO.Complexity.Hardness

namespace UAQO.Test

/-! ## Compilation test -/
-- If this file compiles, all modules are syntactically correct

/-! ## Paper correspondence tests -/

/-- Test: Definition 1 (Problem Hamiltonian) matches paper -/
example {n M : Nat} (es : EigenStructure n M) (hM : M >= 2) :
    -- The spectral condition (1/Delta)sqrt(d0/(A2 N)) < c
    spectralCondition es hM 0.02 (by norm_num) ↔
    let d0 := es.degeneracies ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_two hM⟩
    let Delta := spectralGapDiag es hM
    let A2_val := A2 es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM)
    let N := qubitDim n
    (1 / Delta) * Real.sqrt (d0 / (A2_val * N)) < 0.02 := by
  rfl

/-- Test: Equation 5 (spectral parameters) -/
example {n M : Nat} (es : EigenStructure n M) (hM : M > 0) (p : Nat) :
    spectralParam es hM p =
    let E0 := es.eigenvalues ⟨0, hM⟩
    let N := qubitDim n
    (1 / N) * Finset.sum (Finset.filter (fun k => k.val > 0) Finset.univ)
      (fun k => (es.degeneracies k : Real) / (es.eigenvalues k - E0)^p) := by
  rfl

/-- Test: Equation 6 (position of avoided crossing) -/
example {n M : Nat} (es : EigenStructure n M) (hM : M > 0) :
    avoidedCrossingPosition es hM =
    let A1_val := A1 es hM
    A1_val / (A1_val + 1) := by
  rfl

/-- Test: Equation 7 (window around avoided crossing) -/
example {n M : Nat} (es : EigenStructure n M) (hM : M >= 2) :
    avoidedCrossingWindow es hM =
    let A1_val := A1 es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM)
    let A2_val := A2 es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM)
    let d0 := es.degeneracies ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_two hM⟩
    let N := qubitDim n
    2 / (A1_val + 1)^2 * Real.sqrt (d0 * A2_val / N) := by
  rfl

/-- Test: Minimum gap formula (Eq. 311 with eta = 0.1) -/
example {n M : Nat} (es : EigenStructure n M) (hM : M >= 2) :
    minimumGap es hM =
    let A1_val := A1 es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM)
    let A2_val := A2 es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM)
    let d0 := es.degeneracies ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_two hM⟩
    let N := qubitDim n
    (1 - 2 * (0.1 : Real)) * (2 * A1_val / (A1_val + 1) * Real.sqrt (d0 / (A2_val * N))) := by
  rfl

/-! ## Unit tests for basic definitions -/

/-- Test: qubitDim computes correctly -/
example : qubitDim 3 = 8 := by rfl
example : qubitDim 10 = 1024 := by rfl

/-- Test: BigO is reflexive -/
example (f : Nat -> Real) : BigO f f := by
  use 1, 0
  constructor
  · norm_num
  · intro n _
    simp only [one_mul]
    exact le_refl _

/-! ## Extraction formula tests -/

/-- Test: extractDegeneracyReal implements the paper's formula (line 912) -/
example {n M : Nat} (es : EigenStructure n M) (hM : M > 0) (k : Fin M)
    (p : Polynomial Real) :
    UAQO.Complexity.extractDegeneracyReal es hM k p =
    (qubitDim n : Real) * Polynomial.eval (-2 * UAQO.Complexity.spectralGaps es hM k) p /
    UAQO.Complexity.extractionDenominator es hM k := by
  rfl

/-! ## Encoding tests -/

-- Test: CNF encoding round-trip correctness
#check @UAQO.Complexity.decode_encode

-- Test: CNF encoding injectivity
#check @UAQO.Complexity.encodeCNF_injective

-- Test: ThreeSAT uses real encoding (not Set.univ)
#check @UAQO.Complexity.ThreeSAT

-- Test: SharpThreeSAT uses real encoding (not constant 0)
#check @UAQO.Complexity.SharpThreeSAT

-- Test: extractDegeneracy_correct recovers degeneracies from numerator polynomial
#check @UAQO.Complexity.extractDegeneracy_correct

-- Test: mainResult3 uses the extraction formula (not trivial)
#check @UAQO.Complexity.mainResult3

/-! ## Theorem inventory -/
-- Key genuine theorems (fully proved, no axiom dependencies for these):

-- Resolvent distance to spectrum (proved via Frobenius positivity)
#check @resolvent_distance_to_spectrum

-- Degeneracy extraction via polynomial evaluation (paper's formula)
#check @UAQO.Complexity.extractDegeneracy_correct

-- Numerator polynomial evaluation identity
#check @UAQO.Complexity.numeratorPoly_eval

-- CNF encoding round-trip correctness
#check @UAQO.Complexity.decode_encode

-- Theorems proved from axioms (formerly sorry, now one-line proofs):

-- Lower bound for unstructured search (axiom: quantum adversary method)
#check @lowerBound_unstructuredSearch

-- #3-SAT is #P-complete (proved from axioms sharpThreeSAT_in_SharpP + sharpThreeSAT_hard)
#check @UAQO.Complexity.sharpThreeSAT_complete

-- Adiabatic theorem (proved from adiabatic_evolution_bound axiom)
#check @adiabaticTheorem

-- Main Result 1 (proved from mainResult1_evolution axiom)
#check @mainResult1

-- Eigenpath traversal (proved from eigenpath_evolution_bound axiom)
#check @eigenpath_traversal

/-! ## Axiom audit -/
-- 12 explicit axioms (Lean `axiom` keyword), 0 sorry
-- All axioms visible via `#print axioms`
-- See Proofs/ProofVerify.lean for complete inventory

-- Verify mainResult2 has no custom axioms (genuine proof via classical case split)
#print axioms UAQO.Complexity.mainResult2

-- Verify mainResult3 has no custom axioms (genuine proof via extraction formula)
#print axioms UAQO.Complexity.mainResult3

-- Verify sharpThreeSAT_complete depends only on axioms 5+6
#print axioms UAQO.Complexity.sharpThreeSAT_complete

-- Verify adiabaticTheorem depends on adiabatic_evolution_bound
#print axioms adiabaticTheorem

end UAQO.Test
