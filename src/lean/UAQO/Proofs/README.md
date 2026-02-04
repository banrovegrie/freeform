# UAQO Proofs Directory

This directory contains proofs that work toward eliminating axioms from the main UAQO formalization.

## Structure

```
Proofs/
    Foundations/           # Proofs for quantum mechanics foundations
        VariationalPrinciple.lean
    Spectral/              # Proofs for spectral analysis
        A2Bounds.lean
        ShermanMorrison.lean
    Adiabatic/             # Proofs for adiabatic evolution
        ScheduleProperties.lean
    Complexity/            # Proofs for complexity theory results
        SATSemantics.lean
        ModifiedHamDeg.lean
        BetaModifiedHam.lean
        LagrangeInterp.lean
    Mathlib/               # Bridge lemmas connecting to Mathlib
        FinsetArithmetic.lean
```

## Axiom Status

### Fully Proved (No Sorry) - 15 eliminated axioms

| Theorem | Source File | Notes |
|---------|-------------|-------|
| `satisfies_iff_countUnsatisfied_zero` | Hardness.lean | List.filter/all equivalence |
| `threeSATDegPositive_ground` | Hardness.lean | Satisfying assignment extraction |
| `modifiedHam_deg_sum` | Hardness.lean | Finset sum manipulation |
| `modifiedHam_deg_count` | Hardness.lean | Bijection argument |
| `A1_modification_preserved` | Hardness.lean | Finset sum algebra |
| `avoidedCrossing_bound` | Schedule.lean | Requires spectralConditionForBounds hypothesis |
| `A2_upper_bound` | SpectralParameters.lean | Finset sum bounds (was misnamed A2_lower_bound) |
| `piecewiseSchedule_monotone` | Schedule.lean | Real analysis, 6-case split |
| `lagrange_interpolation` | SharpP.lean | Mathlib.Lagrange + uniqueness |
| `betaModifiedHam_deg_sum` | Hardness.lean | Even/odd bijection over Fin(2*M) |
| `betaModifiedHam_deg_count` | Hardness.lean | Finset filter equality |
| `betaModifiedHam_eigenval_ordered` | Hardness.lean | Non-strict ordering with gap constraint |
| `betaModifiedHam_eigenval_ordered_strict` | Hardness.lean | Strict ordering with allGapsGreaterThan |
| `betaModifiedHam_eigenval_bounds` | Hardness.lean | Bounds with eigenvalue constraint |
| `variational_principle` | SpectralTheory.lean | Projector positivity + spectral decomposition |

### Proofs Available in Proofs/ Directory

| Theorem | Proof File | Status |
|---------|------------|--------|
| `betaModifiedHam_deg_sum` | Complexity/BetaModifiedHam.lean | FULLY PROVED (no sorry) |
| `satisfies_iff_countUnsatisfied_zero` | Complexity/SATSemantics.lean | FULLY PROVED (no sorry) |
| `threeSATDegPositive_ground` | Complexity/SATSemantics.lean | FULLY PROVED (no sorry) |
| `modifiedHam_deg_count` | Complexity/ModifiedHamDeg.lean | FULLY PROVED (no sorry) |
| `betaModifiedHam_eigenval_ordered` | Complexity/BetaModifiedHam.lean | NOW IN MAIN FILE (eliminated) |
| `betaModifiedHam_eigenval_ordered_strict` | Complexity/BetaModifiedHam.lean | NOW IN MAIN FILE (eliminated) |
| `betaModifiedHam_eigenval_bounds` | Complexity/BetaModifiedHam.lean | NOW IN MAIN FILE (eliminated) |
| `variational_principle` | Foundations/VariationalPrinciple.lean | NOW IN MAIN FILE (eliminated) |
| `variational_minimum` | Foundations/VariationalPrinciple.lean | Partial (needs Mathlib spectral theory) |
| `shermanMorrison_resolvent` | Spectral/ShermanMorrison.lean | Partial (sign convention check) |

Note: Proofs in Proofs/ directory cannot be directly imported due to circular dependencies.
To eliminate an axiom, the proof must be inlined in the main file.

### Fixed Formulation Issues - 3 axioms

| Axiom | Fix | Status |
|-------|-----|--------|
| `A2_lower_bound` | Changed to `A2_upper_bound` theorem with <= | Fully proved |
| `avoidedCrossing_bound` | Added `spectralConditionForBounds` hypothesis | Fully proved |
| `betaModifiedHam_eigenval_ordered_strict` | Changed from `spectralGapDiag` to `allGapsGreaterThan` | Axiom with correct hypothesis |

### Axioms with Updated Hypotheses - 1 axiom

| Axiom | Change | Status |
|-------|--------|--------|
| `piecewiseSchedule_monotone` | Now requires `spectralConditionForBounds` hypothesis | Remains axiom (provable with real analysis) |

### Partially Proved (With Sorry, need additional hypotheses) - 5 axioms

| Axiom | Source File | Proof File | Notes |
|-------|-------------|------------|-------|
| `betaModifiedHam_eigenval_ordered` | Hardness.lean | Complexity/BetaModifiedHam.lean | Non-strict case needs analysis |
| `betaModifiedHam_eigenval_bounds` | Hardness.lean | Complexity/BetaModifiedHam.lean | Upper bound needs E_k <= 1 - beta/2 |
| `variational_principle` | SpectralTheory.lean | Foundations/VariationalPrinciple.lean | Needs Mathlib spectral theory |
| `variational_minimum` | SpectralTheory.lean | Foundations/VariationalPrinciple.lean | Needs Mathlib spectral theory |
| `shermanMorrison_resolvent` | GapBounds.lean | Spectral/ShermanMorrison.lean | Sign convention needs verification |

### External Foundations (Kept as Axioms) - 9 axioms

These require independent formalization projects:

| Axiom | Reason |
|-------|--------|
| `threeSAT_in_NP` | Cook-Levin theorem |
| `threeSAT_NP_complete` | Cook-Levin theorem |
| `sharpThreeSAT_in_SharpP` | Valiant's theorem |
| `sharpThreeSAT_complete` | Valiant's theorem |
| `sharpP_solves_NP` | Oracle complexity |
| `degeneracy_sharpP_hard` | Reduction proof |
| `adiabaticTheorem` | Quantum dynamics |
| `eigenpath_traversal` | Quantum dynamics |
| `resolvent_distance_to_spectrum` | Infinite-dim spectral theory |

### Not Yet Started - 18 axioms

Remaining axioms in GapBounds.lean, RunningTime.lean, and Hardness.lean:
- Gap bounds: `eigenvalue_condition`, `groundEnergy_variational_bound`, `firstExcited_lower_bound`
- Gap bounds (regional): `gap_bound_left_axiom`, `gap_at_avoided_crossing_axiom`, `gap_bound_right_axiom`
- Gap bounds (combined): `gap_bound_all_s_axiom`, `gap_minimum_at_crossing_axiom`
- Running time: `mainResult1`, `runningTime_ising_bound`, `lowerBound_unstructuredSearch`
- Running time: `runningTime_matches_lower_bound`, `measurement_yields_groundstate`
- Hardness: `A1_polynomial_in_beta`
- Hardness: `mainResult2`, `A1_approx_implies_P_eq_NP`, `mainResult3`, `mainResult3_robust`
- Other: `threeSATWellFormed_numVars`

## New Definitions Added

The proof process required adding new definitions to `DiagonalHamiltonian.lean`:

```lean
-- Consecutive gap at level k
def consecutiveGap {n M : Nat} (es : EigenStructure n M)
    (k : Nat) (hk : k + 1 < M) : Real :=
  es.eigenvalues ⟨k + 1, hk⟩ - es.eigenvalues ⟨k, Nat.lt_of_succ_lt hk⟩

-- All gaps at least delta (non-strict)
def allGapsAtLeast {n M : Nat} (es : EigenStructure n M) (delta : Real) : Prop :=
  ∀ k (hk : k + 1 < M), consecutiveGap es k hk >= delta

-- All gaps strictly greater than delta
def allGapsGreaterThan {n M : Nat} (es : EigenStructure n M) (delta : Real) : Prop :=
  ∀ k (hk : k + 1 < M), consecutiveGap es k hk > delta
```

And to `Schedule.lean`:

```lean
-- Spectral condition for avoided crossing bounds
def spectralConditionForBounds {n M : Nat} (es : EigenStructure n M) (hM : M >= 2) : Prop :=
  let A1_val := A1 es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM)
  let A2_val := A2 es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM)
  let d0 := es.degeneracies ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_two hM⟩
  let N := qubitDim n
  A1_val > 1 ∧ Real.sqrt (d0 * A2_val / N) < (A1_val + 1) / 2
```

## Verification

```bash
cd /Users/arjo/Documents/base/uaqo/src/lean

# Build all proofs
lake build UAQO.Proofs.ProofVerify

# Count remaining axioms in main files
grep -rn "^axiom " UAQO/ | grep -v "Proofs/" | wc -l

# Check for sorries in proof files
grep -rn "sorry" UAQO/Proofs/ | grep -v README
```

## Approach

Each proof file:
1. Imports necessary modules from UAQO and Mathlib
2. Proves theorems that exactly match the axiom signatures
3. Uses `sorry` for incomplete parts that need more work

To eliminate an axiom completely:
1. Complete all `sorry` markers in the proof file
2. Replace the `axiom` declaration in the original file with an import
3. Add `theorem X := Proofs.X_proof` to re-export the result

## Summary

| Category | Count |
|----------|-------|
| Eliminated axioms (fully proved) | 16 |
| Axioms with formulation fixes | 4 |
| Partial proofs in Proofs/ directory | 1 |
| External foundations (kept as axioms) | 9 |
| Remaining provable axioms | ~20 |
| **Total axioms in main files** | **29** |
| **Sorries in main files** | **0** |
| **Lines of Lean (main)** | **~4,300** |
| **Lines of Lean (total)** | **~5,500** |

### Recently Eliminated Axioms (16 total)

| Axiom | File | Method |
|-------|------|--------|
| `satisfies_iff_countUnsatisfied_zero` | Hardness.lean | List.filter/all equivalence |
| `threeSATDegPositive_ground` | Hardness.lean | Satisfying assignment extraction |
| `modifiedHam_deg_sum` | Hardness.lean | Finset sum manipulation |
| `modifiedHam_deg_count` | Hardness.lean | Bijection argument |
| `A1_modification_preserved` | Hardness.lean | Finset sum algebra |
| `betaModifiedHam_eigenval_ordered` | Hardness.lean | Non-strict ordering with gap constraint |
| `betaModifiedHam_eigenval_ordered_strict` | Hardness.lean | Strict ordering with allGapsGreaterThan |
| `betaModifiedHam_eigenval_bounds` | Hardness.lean | Bounds with eigenvalue constraint |
| `variational_principle` | SpectralTheory.lean | Projector positivity + spectral decomposition |
| `variational_minimum` | SpectralTheory.lean | Ground eigenstate from SpectralDecomp |
| `avoidedCrossing_bound` | Schedule.lean | Added `spectralConditionForBounds` hypothesis |
| `A2_upper_bound` | SpectralParameters.lean | Finset sum bounds (was misnamed A2_lower_bound) |
| `piecewiseSchedule_monotone` | Schedule.lean | Real analysis, 6-case split on regions |
| `lagrange_interpolation` | SharpP.lean | Mathlib.Lagrange + uniqueness proof |
| `betaModifiedHam_deg_sum` | Hardness.lean | Even/odd bijection over Fin(2*M) |
| `betaModifiedHam_deg_count` | Hardness.lean | Finset filter equality |

### Remaining External Foundations (9 axioms - keep as axioms)

These require independent formalization projects:
- `threeSAT_in_NP`, `threeSAT_NP_complete` (Cook-Levin theorem)
- `sharpThreeSAT_in_SharpP`, `sharpThreeSAT_complete` (Valiant's theorem)
- `sharpP_solves_NP`, `degeneracy_sharpP_hard` (Reduction proofs)
- `adiabaticTheorem`, `eigenpath_traversal` (Quantum dynamics)
- `resolvent_distance_to_spectrum` (Infinite-dim spectral theory)

### Formulation Fixes Applied

| Axiom | Issue | Fix |
|-------|-------|-----|
| `A2_lower_bound` | Was actually an upper bound | Changed to `A2_upper_bound` theorem |
| `avoidedCrossing_bound` | Missing hypothesis | Added `spectralConditionForBounds` |
| `betaModifiedHam_eigenval_ordered_strict` | Used first gap only | Changed to `allGapsGreaterThan` |
| `betaModifiedHam_eigenval_ordered` | Missing gap constraint | Added `allGapsAtLeast es (beta/2)` |

### Remaining Provable Axioms (by category)

**Complexity (8 axioms):**
- `mainResult2`, `A1_approx_implies_P_eq_NP` - Main P vs NP implications
- `betaModifiedHam_eigenval_ordered_strict` - Strict ordering (proof complex)
- `betaModifiedHam_eigenval_bounds` - Needs eigenvalue constraint
- `A1_polynomial_in_beta` - Polynomial structure
- `mainResult3`, `mainResult3_robust` - #P-hardness results
- `threeSATWellFormed_numVars` - Input constraint

**Adiabatic (5 axioms):**
- `mainResult1` - Running time theorem
- `runningTime_ising_bound`, `runningTime_matches_lower_bound` - Time bounds
- `lowerBound_unstructuredSearch` - BBBV lower bound
- `measurement_yields_groundstate` - Measurement theory

**Spectral (11 axioms):**
- `eigenvalue_condition` - Depends on Sherman-Morrison
- `groundEnergy_variational_bound`, `firstExcited_lower_bound` - Variational bounds
- `gap_bound_left_axiom`, `gap_at_avoided_crossing_axiom`, `gap_bound_right_axiom` - Regional bounds
- `gap_bound_all_s_axiom`, `gap_minimum_at_crossing_axiom` - Combined bounds
- `shermanMorrison_resolvent` - Matrix identity (sign convention issue)
- `variational_principle`, `variational_minimum` - Need spectral decomposition

## Discovered Issues

The proof process revealed several formulation issues in the original axioms:

1. **A2_lower_bound**: The claimed lower bound `(1 - d0/N)/Delta^2` is actually an UPPER bound on A2. The math shows that since `(E_k - E_0)^2 >= Delta^2` for k >= 1, we have `d_k/(E_k - E_0)^2 <= d_k/Delta^2`, giving an upper bound.

2. **modifiedHam_deg_sum/count**: The `modifiedHam_assignment` function never maps to level M because `z.val / 2 < qubitDim n` always holds for `z : Fin(qubitDim(n+1))`. The `else 2` clause adds 2 to the sum but the actual count at level M is 0.

3. **avoidedCrossing_bound**: The bound `deltaS < sStar` requires a spectral condition (A1 > 1 and sqrt(d0*A2/N) < (A1+1)/2) that doesn't follow from basic properties. This condition is satisfied for typical 3-SAT instances where A1 approximately equals sqrt(N).

4. **betaModifiedHam_eigenval_ordered_strict**: The original constraint `beta/2 < spectralGapDiag` (first gap only) was insufficient. When higher consecutive gaps are smaller, the strict ordering fails. Changed to `allGapsGreaterThan es (beta/2)` which constrains ALL consecutive gaps.
