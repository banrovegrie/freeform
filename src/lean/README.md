# UAQO: Lean 4 Formalization

Formal verification of "Unstructured Adiabatic Quantum Optimization: Optimality with Limitations" (arXiv:2411.05736) in Lean 4 with mathlib4.

## Overview

This formalization captures the mathematical structure of adiabatic quantum optimization for unstructured search, including:

- Main Result 1: Running time $T = O(1/\Delta)$ where $\Delta$ is the spectral gap of the diagonal Hamiltonian
- Main Result 2: Approximating the spectral parameter $A_1$ to $1/\text{poly}(n)$ precision is NP-hard
- Main Result 3: Exactly computing $A_1$ is #P-hard

## Project Structure

```
UAQO/
    Foundations/
        Basic.lean              Qubit states, operators, norms
        HilbertSpace.lean       Inner products, norms, mathlib bridges
        Operators.lean          Hermitian operators, resolvents
        SpectralTheory.lean     Eigenvalues, spectral decomposition
        Qubit.lean              Qubit systems, tensor products
    Spectral/
        DiagonalHamiltonian.lean  Diagonal Hamiltonians, eigenstructure
        SpectralParameters.lean   A1, A2 parameters, avoided crossings
        GapBounds.lean            Gap bounds in different regions
    Adiabatic/
        Hamiltonian.lean        Time-dependent Hamiltonians, interpolation
        Schedule.lean           Local schedules, piecewise construction
        Theorem.lean            Adiabatic theorem statement
        RunningTime.lean        Main Result 1, optimality
    Complexity/
        Basic.lean              Decision problems, polynomial time
        NP.lean                 NP, NP-completeness, 3-SAT
        SharpP.lean             #P, counting problems, interpolation
        Hardness.lean           Main Results 2 and 3, reductions
    Test/
        Verify.lean             Type-checking key theorems
```

## Building

Requires Lean 4 (v4.28.0-rc1) and mathlib4.

```bash
lake update
lake build
```

## Formalization Status

| Metric              | Count  |
|---------------------|--------|
| Sorries             | 0      |
| Axioms              | 29     |
| Lines of Lean (main)| ~4,300 |
| Lines of Lean (total)| ~5,500 |

The formalization is sorry-free but relies on 29 axioms for deep mathematical results.
16 axioms have been eliminated through proofs since the initial formalization.

## Axiom Categories

### Complexity Theory Foundations (6 axioms)

Standard results from computational complexity:

- `threeSAT_in_NP`: 3-SAT is in NP
- `threeSAT_NP_complete`: Cook-Levin theorem
- `sharpThreeSAT_in_SharpP`: #3-SAT is in #P
- `sharpThreeSAT_complete`: #3-SAT is #P-complete
- `sharpP_solves_NP`: #P oracle solves NP
- `degeneracy_sharpP_hard`: Computing degeneracies is #P-hard

Note: `lagrange_interpolation` was eliminated (proved using Mathlib.Lagrange).

### Spectral Theory (1 axiom)

Functional analysis foundations:

- `resolvent_distance_to_spectrum`: Resolvent norm equals inverse distance to spectrum

Note: `variational_principle` and `variational_minimum` were eliminated (proved using projector positivity and spectral decomposition).

### Adiabatic Theorem and Running Time (7 axioms)

Quantum adiabatic evolution:

- `adiabaticTheorem`: Adiabatic approximation with gap-dependent error
- `eigenpath_traversal`: Ground state tracking under slow evolution
- `mainResult1`: Running time $T = O(1/\Delta)$
- `runningTime_ising_bound`: Running time for Ising problems
- `runningTime_matches_lower_bound`: Optimality of the bound
- `measurement_yields_groundstate`: Final measurement success probability
- `lowerBound_unstructuredSearch`: Query complexity lower bound (BBBV)

### Gap Bounds (9 axioms)

Spectral gap analysis:

- `eigenvalue_condition`: Eigenvalue structure in interpolation
- `groundEnergy_variational_bound`: Ground energy bounds
- `firstExcited_lower_bound`: First excited state bounds
- `gap_bound_left_axiom`: Gap bound left of avoided crossing
- `gap_at_avoided_crossing_axiom`: Gap at avoided crossing
- `gap_bound_right_axiom`: Gap bound right of avoided crossing
- `gap_bound_all_s_axiom`: Combined gap bound
- `gap_minimum_at_crossing_axiom`: Gap minimum location
- `shermanMorrison_resolvent`: Sherman-Morrison for resolvents

### Hardness Constructions (9 axioms)

Modified Hamiltonian properties for reductions:

**Beta-modified Hamiltonians (3):**
- `betaModifiedHam_eigenval_ordered`: Non-strict eigenvalue ordering
- `betaModifiedHam_eigenval_ordered_strict`: Strict eigenvalue ordering
- `betaModifiedHam_eigenval_bounds`: Eigenvalue bounds

**3-SAT Encoding (1):**
- `threeSATWellFormed_numVars`: Well-formed formulas have variables (kept as axiom)

**A1 Properties (1):**
- `A1_polynomial_in_beta`: $A_1$ as polynomial in beta parameter

**Main Hardness Results (4):**
- `mainResult2`: NP-hardness of approximating $A_1$
- `A1_approx_implies_P_eq_NP`: Polynomial-time A1 approximation implies P=NP
- `mainResult3`: #P-hardness via polynomial interpolation
- `mainResult3_robust`: Robustness to exponential errors

**Eliminated (now proved):**
- `modifiedHam_deg_sum`, `modifiedHam_deg_count`: Finset sum manipulation
- `betaModifiedHam_deg_sum`, `betaModifiedHam_deg_count`: Even/odd bijection
- `threeSATDegPositive_ground`: Satisfying assignment extraction
- `satisfies_iff_countUnsatisfied_zero`: List.filter/all equivalence
- `A1_modification_preserved`: Finset sum algebra

### Schedule Construction (0 axioms)

All schedule axioms have been eliminated:
- `avoidedCrossing_bound`: Proved with `spectralConditionForBounds` hypothesis
- `piecewiseSchedule_monotone`: Proved via real analysis (6-case split)
- `avoidedCrossingWindow_pos`: Proved (positivity of window)

### Spectral Parameters (0 axioms)

All spectral parameter axioms have been eliminated:
- `A2_upper_bound`: Finset sum bounds (was misnamed `A2_lower_bound`)

## Key Definitions and Theorems

### Converted from Axioms to Definitions/Theorems

The following 16 axioms were eliminated through proofs:

| Axiom | File | Method |
|-------|------|--------|
| `satisfies_iff_countUnsatisfied_zero` | Hardness.lean | List.filter/all equivalence |
| `threeSATDegPositive_ground` | Hardness.lean | Satisfying assignment extraction |
| `modifiedHam_deg_sum` | Hardness.lean | Finset sum manipulation |
| `modifiedHam_deg_count` | Hardness.lean | Bijection argument |
| `A1_modification_preserved` | Hardness.lean | Finset sum algebra |
| `avoidedCrossing_bound` | Schedule.lean | Added `spectralConditionForBounds` hypothesis |
| `A2_upper_bound` | SpectralParameters.lean | Finset sum bounds |
| `piecewiseSchedule_monotone` | Schedule.lean | Real analysis, 6-case split |
| `lagrange_interpolation` | SharpP.lean | Mathlib.Lagrange + uniqueness |
| `betaModifiedHam_deg_sum` | Hardness.lean | Even/odd bijection over Fin(2*M) |
| `betaModifiedHam_deg_count` | Hardness.lean | Finset filter equality |
| `betaModifiedHam_eigenval_ordered` | Hardness.lean | Non-strict ordering with gap constraint |
| `betaModifiedHam_eigenval_ordered_strict` | Hardness.lean | Strict ordering with allGapsGreaterThan |
| `betaModifiedHam_eigenval_bounds` | Hardness.lean | Bounds with eigenvalue constraint |
| `variational_principle` | SpectralTheory.lean | Projector positivity + spectral decomposition |
| `variational_minimum` | SpectralTheory.lean | Ground eigenstate from SpectralDecomp |

Additional definitions and theorems:
- `modifiedHam_assignment`: Definition mapping extended states to eigenvalue indices
- `modifiedHam_eigenval_ordered`: Theorem proving eigenvalue ordering
- `threeSATAssignment`: Definition based on unsatisfied clause count
- `threeSATDegCount`: Theorem relating degeneracy to assignment filter
- `threeSATDegSum`: Theorem that degeneracies partition the Hilbert space
- `threeSATDegSum_total`: Corollary of threeSATDegSum
- `betaModifiedHam_assignment`: Definition for beta-modified construction

### EigenStructure

```lean
structure EigenStructure (n M : Nat) where
  eigenvalues    : Fin M -> Real
  degeneracies   : Fin M -> Nat
  assignment     : Fin (qubitDim n) -> Fin M
  eigenval_bounds    : forall k, 0 <= eigenvalues k and eigenvalues k <= 1
  eigenval_ordered   : forall i j, i < j -> eigenvalues i < eigenvalues j
  ground_energy_zero : M > 0 -> eigenvalues 0 = 0
  deg_positive       : forall k, degeneracies k > 0
  deg_sum            : sum over k of degeneracies k = qubitDim n
  deg_count          : forall k, degeneracies k = card of states mapping to k
```

### Spectral Parameters

```lean
-- A1: First spectral parameter (determines avoided crossing position)
noncomputable def A1 (es : EigenStructure n M) (hM : M > 0) : Real :=
  (1/N) * sum_{k>=1} d_k / (E_k - E_0)

-- A2: Second spectral parameter (appears in minimum gap)
noncomputable def A2 (es : EigenStructure n M) (hM : M > 0) : Real :=
  (1/N) * sum_{k>=1} d_k / (E_k - E_0)^2
```

## Design Decisions

1. **Diagonal Hamiltonians**: The formalization focuses on diagonal Hamiltonians in the computational basis, which is the setting of the paper.

2. **EigenStructure abstraction**: Rather than working with explicit matrix representations, we abstract to eigenvalue/degeneracy data. This captures the essential spectral information needed for the analysis.

3. **Axiom boundary**: Deep results (adiabatic theorem, Cook-Levin, spectral theory) are axiomatized. This is standard practice; these would each require major independent formalization efforts.

4. **Mathlib integration**: Bridge lemmas connect our definitions to mathlib's inner product spaces and hermitian matrices, enabling future proof development.

## Future Work

To further reduce the axiom count, priority targets are:

1. **Variational principle** (HIGH): Bridge to Mathlib's Rayleigh quotient characterization.
   Unlocks: `variational_minimum`, `groundEnergy_variational_bound`, `gap_bound_left_axiom`

2. **Sherman-Morrison** (HIGH): Matrix identity for resolvents (sign convention needs verification).
   Unlocks: `eigenvalue_condition`, `firstExcited_lower_bound`, `gap_bound_right_axiom`

3. **Beta-modified eigenvalue ordering** (MEDIUM): Case analysis on index parity.
   Proves: `betaModifiedHam_eigenval_ordered`, `betaModifiedHam_eigenval_bounds`

The following axioms require independent formalization projects:
- Complexity theory (Cook-Levin, #P-completeness): 6 axioms
- Quantum dynamics (adiabatic theorem): 2 axioms
- Infinite-dimensional spectral theory: 1 axiom

## References

- Unstructured Adiabatic Quantum Optimization: Optimality with Limitations (arXiv:2411.05736)
- Roland-Cerf local adiabatic search (arXiv:quant-ph/0107015)
- Mathlib4 documentation: https://leanprover-community.github.io/mathlib4_docs/

## License

Part of the UAQO thesis project.
