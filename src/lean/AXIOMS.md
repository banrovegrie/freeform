# UAQO Axiom Documentation

This document catalogs all 25 axioms in the UAQO Lean formalization, organized by category with justifications for why each remains an axiom.

## Summary

| Category | Count | Status |
|----------|-------|--------|
| External Foundations | 9 | Keep as axioms (standard results) |
| Gap Bounds | 6 | Could be proved with more spectral theory |
| Running Time | 4 | Depend on gap bounds + adiabatic theorem |
| Hardness | 5 | Main complexity results |
| Spectral Theory | 1 | Requires infinite-dim functional analysis |

Total: 25 axioms (including 1 in Proofs/)

## External Foundations (9 axioms)

These are well-established results from complexity theory and physics that would require substantial independent formalization efforts.

### Cook-Levin Theorem (2 axioms)

**File**: `UAQO/Complexity/NP.lean`

```lean
axiom threeSAT_in_NP : InNP ThreeSAT
```
**Justification**: Standard result. 3-SAT is in NP because a satisfying assignment can be verified in polynomial time.

```lean
axiom threeSAT_NP_complete : IsNPComplete ThreeSAT
```
**Justification**: Cook-Levin theorem (1971). Proving this requires formalizing Turing machines and polynomial-time reductions.

### Valiant's Theorem (2 axioms)

**File**: `UAQO/Complexity/SharpP.lean`

```lean
axiom sharpThreeSAT_in_SharpP : InSharpP SharpThreeSAT
```
**Justification**: #3-SAT counts satisfying assignments, which is computable by a counting Turing machine.

```lean
axiom sharpThreeSAT_complete : IsSharpPComplete SharpThreeSAT
```
**Justification**: Valiant's theorem (1979). Requires formalizing parsimonious reductions.

### Oracle Complexity (2 axioms)

**File**: `UAQO/Complexity/SharpP.lean`

```lean
axiom sharpP_solves_NP (prob : CountingProblem) (hSharpP : IsSharpPComplete prob)
    (dec : DecisionProblem) (hNP : IsNPComplete dec) :
    ExistsPolytimeReductionWithOracle dec prob
```
**Justification**: A #P oracle can solve NP problems (count > 0 iff satisfiable).

```lean
axiom degeneracy_sharpP_hard : IsSharpPHard DegeneracyProblem
```
**Justification**: Counting degeneracies of quantum Hamiltonians is #P-hard via reduction from #3-SAT.

### Adiabatic Theorem (2 axioms)

**File**: `UAQO/Adiabatic/Theorem.lean`

```lean
axiom adiabaticTheorem {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2) (schedule : LocalSchedule es)
    (T : Real) (hT : T >= schedule.runningTime) :
    FinalOverlap (adiabaticEvolution es schedule T) >= 1 - schedule.epsilon
```
**Justification**: The quantum adiabatic theorem requires formalizing time-dependent Schrodinger dynamics and spectral gap integration.

```lean
axiom eigenpath_traversal {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2) (schedule : LocalSchedule es)
    (T : Real) (hT : T >= schedule.runningTime) :
    TraversesEigenpath (adiabaticEvolution es schedule T)
```
**Justification**: Eigenpath traversal follows from adiabatic theorem analysis.

### Spectral Theory (1 axiom)

**File**: `UAQO/Foundations/Operators.lean`

```lean
axiom resolvent_distance_to_spectrum {N : Nat} (A : Operator N) (gamma : Complex)
    (hNotEig : forall lambda, IsEigenvalue A lambda -> gamma != lambda) :
    exists (bound : Real), bound > 0 /\ OperatorNorm ((gamma • 1 - A)^(-1)) <= 1 / bound
```
**Justification**: Resolvent norm bound by distance to spectrum. For finite-dimensional matrices, Mathlib may have this; for infinite-dimensional, requires functional analysis.

## Gap Bounds (6 axioms)

These axioms characterize the spectral gap of the adiabatic Hamiltonian H(s). They could be proved with more development of spectral theory for H(s).

**File**: `UAQO/Spectral/GapBounds.lean`

```lean
axiom firstExcited_lower_bound {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2) (s : Real) (hs : 0 <= s /\ s <= 1) :
    exists (E1 : Real), IsEigenvalue (adiabaticHam es s hs) E1 /\
      E1 >= s * es.eigenvalues (Fin.mk 0 _) /\
      exists (E0 : Real), IsEigenvalue (adiabaticHam es s hs) E0 /\ E0 < E1
```
**Justification**: Lower bound on first excited state. Requires spectral decomposition of H(s).
**Proof Strategy**: Use variational principle with trial states.

```lean
axiom gap_bound_left_axiom {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2) (s : Real) (hs : 0 <= s /\ s <= 1)
    (hs_left : s <= avoidedCrossingPosition es) :
    spectralGap (adiabaticHam es s hs) >= gapBoundLeft es s
```
**Justification**: Gap bound for s left of avoided crossing (Eq. 317 in paper).
**Proof Strategy**: Variational analysis with trial state.

```lean
axiom gap_at_avoided_crossing_axiom {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2) (hcond : spectralConditionForBounds es) :
    spectralGap (adiabaticHam es (avoidedCrossingPosition es) _) >= gapAtCrossing es
```
**Justification**: Gap at avoided crossing point (Eq. 311 in paper).
**Proof Strategy**: Perturbation analysis at s*.

```lean
axiom gap_bound_right_axiom {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2) (s : Real) (hs : 0 <= s /\ s <= 1)
    (hs_right : s >= avoidedCrossingPosition es)
    (hcond : spectralConditionForBounds es) :
    spectralGap (adiabaticHam es s hs) >= gapBoundRight es s
```
**Justification**: Gap bound for s right of avoided crossing (Lemma 5 in paper).
**Proof Strategy**: Resolvent method with Sherman-Morrison (already proved).

```lean
axiom gap_bound_all_s_axiom {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2) (s : Real) (hs : 0 <= s /\ s <= 1)
    (hcond : spectralConditionForBounds es) :
    spectralGap (adiabaticHam es s hs) >= gapBoundAllS es s
```
**Justification**: Combined gap bound for all s in [0,1].
**Proof Strategy**: Case split on s relative to crossing, apply regional bounds.

```lean
axiom gap_minimum_at_crossing_axiom {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2) (hcond : spectralConditionForBounds es) :
    minimumGap es = gapAtCrossing es
```
**Justification**: Minimum gap occurs at avoided crossing.
**Proof Strategy**: Structural result from gap analysis.

## Running Time (4 axioms)

These depend on gap bounds and the adiabatic theorem.

**File**: `UAQO/Adiabatic/RunningTime.lean`

```lean
axiom mainResult1 {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2) (hcond : spectralConditionForBounds es)
    (delta : Real) (hdelta : minimumGap es = delta) :
    exists (T : Real), T = O(1 / delta) /\ AchievesHighOverlap es T
```
**Justification**: Main Result 1 of the paper. Running time T = O(1/Delta).
**Dependencies**: gap_bound_all_s_axiom, adiabaticTheorem.

```lean
axiom runningTime_ising_bound {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2) (hcond : spectralConditionForBounds es)
    (hIsing : IsingModel es) :
    exists (T : Real), T = O(sqrt (qubitDim n)) /\ AchievesHighOverlap es T
```
**Justification**: Specialization to Ising model gives T = O(sqrt(N)).
**Dependencies**: mainResult1.

```lean
axiom lowerBound_unstructuredSearch :
    forall (algorithm : QuantumSearchAlgorithm),
    ExpectedQueriesForUnstructuredSearch algorithm >= Omega(sqrt N)
```
**Justification**: BBBV lower bound (1997). Requires quantum query complexity formalization.

```lean
axiom runningTime_matches_lower_bound {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2) (hcond : spectralConditionForBounds es) :
    OptimalRunningTime es (sqrt (qubitDim n))
```
**Justification**: Optimality - upper bound matches BBBV lower bound.
**Dependencies**: mainResult1, lowerBound_unstructuredSearch.

## Hardness (5 axioms)

Main complexity results of the paper.

**File**: `UAQO/Complexity/Hardness.lean`

```lean
axiom mainResult2 (approx : A1Approximator) :
    CanDistinguishThreshold approx -> ImpliesPEqualsNP approx
```
**Justification**: Main Result 2. Approximating A1 to 1/poly(n) is NP-hard.
**Proof Strategy**: Threshold distinction argument.

```lean
axiom A1_approx_implies_P_eq_NP :
    ExistsPolynomialA1Approximator -> P_equals_NP
```
**Justification**: Corollary of Main Result 2.

```lean
axiom A1_polynomial_in_beta {n M : Nat} (es : EigenStructure n M) (hM : M >= 2) :
    exists (p : Polynomial Real), A1_as_function_of_beta es = p.eval
```
**Justification**: A1 is a polynomial in beta parameter.
**Proof Strategy**: Coefficient analysis of A1 formula.

```lean
axiom mainResult3 (computer : A1ExactComputer) :
    IsPolynomialTime computer -> SharpPHard computer
```
**Justification**: Main Result 3. Exactly computing A1 is #P-hard.
**Proof Strategy**: Lagrange interpolation (already proved) + allLevelsPopulated.

```lean
axiom mainResult3_robust :
    forall (approx : A1Approximator),
    ApproximationError approx <= ExponentiallySmall ->
    SharpPHard approx
```
**Justification**: Robustness - #P-hardness persists with exponentially small errors.
**Proof Strategy**: Berlekamp-Welch algorithm for error correction.

## Proof Auxiliary (1 axiom)

**File**: `UAQO/Proofs/Spectral/GapBoundsProofs.lean`

```lean
axiom adiabatic_emax_nonneg {n M : Nat} (es : EigenStructure n M) (hM : M >= 2)
    (s : Real) (hs : 0 <= s /\ s <= 1)
    (hHerm : (adiabaticHam es s hs).IsHermitian)
    (E_max : Real)
    (hmax_bound : forall i : Fin (qubitDim n), hHerm.eigenvalues i <= E_max) : E_max >= 0
```
**Justification**: Maximum eigenvalue of H(s) is non-negative.
**Proof Outline**:
- At s = 0: H(0) = -|psi0><psi0| has eigenvalue 0 (N-1 fold degeneracy)
- At s = 1: H(1) = H_z has non-negative eigenvalues
- For 0 < s < 1: State |0> - |1> is orthogonal to psi0, so expectation >= 0

**Gap**: Requires connecting `IsEigenvalue` to `hHerm.eigenvalues` via Mathlib's spectral theorem.

## Path to Elimination

### Immediately Provable (with effort)
1. `adiabatic_emax_nonneg` - Need Mathlib spectral theorem connection
2. `firstExcited_lower_bound` - Variational principle
3. `threeSATWellFormed_numVars` - Simple lemma (unused)

### Require Spectral Decomposition of H(s)
4-9. Gap bound axioms - Depend on spectral structure of adiabatic Hamiltonian

### Require Gap Bounds
10-13. Running time axioms - Chain from gap bounds + adiabatic theorem

### Require Complexity Infrastructure
14-18. Hardness axioms - Need polynomial analysis, threshold arguments

### External (Keep as Axioms)
19-25. Cook-Levin, Valiant, BBBV, adiabatic theorem - Standard results

## Verification

```bash
# Count axioms (excluding Proofs/)
grep -rn "^axiom " UAQO/ | grep -v "Proofs/" | wc -l  # 24

# Count axioms in Proofs/
grep -rn "^axiom " UAQO/Proofs/ | wc -l  # 1

# Total: 25 axioms
```
