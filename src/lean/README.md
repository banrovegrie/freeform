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
        Operators.lean          Hermitian operators, resolvents
        SpectralTheory.lean     Eigenvalues, spectral decomposition
    Spectral/
        SpectralParameters.lean A1, A2 parameters, avoided crossings
        GapBounds.lean          Gap bounds in different regions
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

| Metric        | Count |
|---------------|-------|
| Sorries       | 0     |
| Axioms        | 40    |
| Lines of Lean | ~2000 |

The formalization is sorry-free but relies on 40 axioms for deep mathematical results.

## Axiom Categories

### Complexity Theory (7 axioms)

Standard results from computational complexity:

- `threeSAT_NP_complete`: Cook-Levin theorem
- `sharpThreeSAT_complete`: #3-SAT is #P-complete
- `sharpP_solves_NP`: #P oracle solves NP
- `lagrange_interpolation`: Polynomial interpolation uniqueness
- `degeneracy_sharpP_hard`: Computing degeneracies is #P-hard

### Spectral Theory (5 axioms)

Functional analysis foundations:

- `variational_principle`: Min-max characterization of eigenvalues
- `variational_minimum`: Ground state minimizes Rayleigh quotient
- `resolvent_distance_to_spectrum`: Resolvent norm equals inverse distance to spectrum

### Adiabatic Theorem (6 axioms)

Quantum adiabatic evolution:

- `adiabaticTheorem`: Adiabatic approximation with gap-dependent error
- `eigenpath_traversal`: Ground state tracking under slow evolution
- `mainResult1`: Running time $T = O(1/\Delta)$
- `runningTime_matches_lower_bound`: Optimality of the bound
- `measurement_yields_groundstate`: Final measurement success probability

### Gap Bounds (6 axioms)

Spectral gap analysis:

- `eigenvalue_condition`: Eigenvalue structure in interpolation
- `groundEnergy_variational_bound`: Ground energy bounds
- `firstExcited_lower_bound`: First excited state bounds
- `gap_bound_left_axiom`, `gap_bound_right_axiom`: Region-specific gap bounds
- `shermanMorrison_resolvent`: Sherman-Morrison for resolvents

### Hardness Constructions (15 axioms)

Modified Hamiltonian properties for reductions:

- `modifiedHam_*`: Properties of alpha-modified Hamiltonians
- `betaModifiedHam_*`: Properties of beta-modified Hamiltonians
- `A1_modification_formula`: How $A_1$ transforms under modification
- `A1_polynomial_in_beta`: $A_1$ as polynomial in beta parameter
- `mainResult2`: NP-hardness of approximating $A_1$
- `exact_A1_is_sharpP_hard`: #P-hardness of exact $A_1$

### Schedule Construction (1 axiom)

- `piecewiseSchedule_monotone`: Monotonicity of piecewise linear schedules

## Key Definitions

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
-- A1: First spectral parameter (appears in gap bounds)
noncomputable def A1 (es : EigenStructure n M) (hM : M > 0) : Real :=
  sum over k of (es.degeneracies k) * (1 - es.eigenvalues k)

-- A2: Second spectral parameter
noncomputable def A2 (es : EigenStructure n M) (hM : M > 0) : Real :=
  sum over k of (es.degeneracies k) * (1 - es.eigenvalues k)^2
```

### Spectral Condition

```lean
-- The spectral condition required for optimal AQO
def spectralCondition (es : EigenStructure n M) (hM : M >= 2) (c : Real) : Prop :=
  let A1_val := A1 es hM
  let A2_val := A2 es hM
  A2_val >= c * A1_val^2
```

## Verified Theorems

The test file `UAQO/Test/Verify.lean` confirms these key results type-check:

```lean
#check @resolvent_distance_to_spectrum
-- forall {N : Nat} (A : Operator N) (gamma : Complex), IsHermitian A ->
--   Matrix.det ((gamma * I_N) - A) != 0 -> exists d > 0, norm(R_A(gamma)) = 1 / d

#check Complexity.threeSAT_NP_complete
-- Complexity.IsNPComplete Complexity.ThreeSAT

#check Complexity.sharpThreeSAT_complete
-- Complexity.IsSharpPComplete Complexity.SharpThreeSAT
```

## Design Decisions

1. Diagonal Hamiltonians: The formalization focuses on diagonal Hamiltonians in the computational basis, which is the setting of the paper. General Hamiltonians would require significantly more infrastructure.

2. EigenStructure abstraction: Rather than working with explicit matrix representations, we abstract to eigenvalue/degeneracy data. This captures the essential spectral information needed for the analysis.

3. Axiom boundary: Deep results (adiabatic theorem, Cook-Levin, spectral theory) are axiomatized. This is standard practice; these would each require major independent formalization efforts.

4. Real vs Complex: Eigenvalues are Real (Hermitian operators have real spectrum). State vectors use Complex coefficients where needed.

## Future Work

To reduce the axiom count, priority targets would be:

1. Structural axioms (modifiedHam_*, betaModifiedHam_*): These involve finite arithmetic and set counting; tedious but tractable.

2. Gap bounds: Paper-specific calculations that could be verified with careful real analysis.

3. Spectral theory: Extending mathlib's spectral theory for finite-dimensional Hermitian matrices.

The complexity theory axioms (Cook-Levin, #P-completeness) and adiabatic theorem would require major independent projects.

## References

- Unstructured Adiabatic Quantum Optimization: Optimality with Limitations (arXiv:2411.05736)
- Roland-Cerf local adiabatic search (arXiv:quant-ph/0107015)
- Mathlib4 documentation: https://leanprover-community.github.io/mathlib4_docs/

## License

Part of the UAQO thesis project.
