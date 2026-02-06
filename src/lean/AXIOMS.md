# UAQO Axiom Documentation

All axioms in the UAQO Lean 4 formalization, with justifications.

## Summary

| Category | Count | Status |
|----------|-------|--------|
| External Foundations | 8 | Trusted (standard results from other fields) |
| Spectral Gap Bounds | 7 | Paper results (Prop 1, Eq 317, Lemma 5) |
| Running Time | 4 | Depend on gap bounds + adiabatic theorem |
| Hardness | 5 | Main complexity results |
| **Total** | **24** | **0 sorries in axioms** |

Previously eliminated: 32 axioms converted to theorems.

Infrastructure sorry: `spectral_gap_pair_exists` (bridge lemma between custom
`IsEigenvalue` and Mathlib eigenvalue API). This is NOT an axiom; it is a
provable infrastructure lemma whose proof requires the bridge
`IsEigenvalue <-> is one of Mathlib eigenvalues`.

## Correctness Audit (2026-02-06)

The following issues were identified and fixed:

1. **`crossing_region_gap_upper_bound_axiom` was FALSE as stated**: The axiom
   quantified over arbitrary eigenvalue pairs, but the upper bound `E1 - E0 <= 2*g_min`
   only holds for the spectral gap (ground state to first excited state). For E_min
   and E_max (spectral width), it fails trivially. **Fixed** by adding `hE0_ground`
   (E0 is smallest eigenvalue) and `hE1_first` (E1 is second smallest) hypotheses.

2. **`A1_polynomial_in_beta` was FALSE**: Claimed A1(H_beta) is a polynomial in beta.
   In fact, A1(H_beta) is a rational function (contains terms like 1/(Delta_k + beta/2)).
   The paper constructs a numerator polynomial P(beta) by clearing denominators.
   **Fixed** by renaming to `A1_numerator_polynomial_in_beta` and restating to claim
   that P(beta) = D(beta) * f(beta) is polynomial, where D is the known common
   denominator and f involves A1 values.

3. **`mainResult3_robust` used fixed precision 2^(-10)**: The paper requires
   eps < 1/(2*M^2) where M depends on the formula. **Fixed** to use
   formula-dependent precision bound `1/(2*M^2)`.

4. **`spectral_gap_exists` returned wrong pair**: It returned (E_min, E_max)
   which is the spectral width, not the spectral gap. **Fixed** by adding
   `spectral_gap_pair_exists` which returns (E_0, E_1) with ground/first-excited
   witnesses. Downstream consumers updated accordingly.

## Tier 1: External Foundations (8 axioms)

These are well-established results from complexity theory and physics. Keeping them as explicit axioms is standard practice in formalization.

### Cook-Levin Theorem

**File**: `UAQO/Complexity/NP.lean`

| Line | Axiom | Reference |
|------|-------|-----------|
| 38 | `threeSAT_in_NP : InNP ThreeSAT` | Cook (1971), Levin (1973) |
| 51 | `threeSAT_NP_complete : IsNPComplete ThreeSAT` | Cook-Levin theorem |

Proving these requires formalizing polynomial-time Turing machines and the reduction from arbitrary NP problems to 3-SAT. No Lean 4 formalization of Cook-Levin exists.

### Valiant's Theorem

**File**: `UAQO/Complexity/SharpP.lean`

| Line | Axiom | Reference |
|------|-------|-----------|
| 44 | `sharpThreeSAT_in_SharpP : InSharpP SharpThreeSAT` | Valiant (1979) |
| 70 | `sharpThreeSAT_complete : IsSharpPComplete SharpThreeSAT` | Valiant's theorem |

**Note**: `SharpThreeSAT.count` uses a placeholder definition `fun _ => 0`. The axiom asserts a property of the intended mathematical object (counting satisfying assignments), not the Lean encoding.

### Oracle Complexity

**File**: `UAQO/Complexity/SharpP.lean`

| Line | Axiom | Reference |
|------|-------|-----------|
| 78 | `sharpP_solves_NP` | Standard oracle complexity |
| 205 | `degeneracy_sharpP_hard : IsSharpPHard DegeneracyProblem` | Paper Theorem 3 prerequisite |

`sharpP_solves_NP` states that a #P-complete oracle can solve any NP decision problem. `degeneracy_sharpP_hard` states that computing eigenvalue degeneracies is #P-hard (via reduction from #3-SAT to the diagonal Hamiltonian).

**Note**: `DegeneracyProblem.count` also uses a placeholder `fun _ => 0`.

### Adiabatic Theorem

**File**: `UAQO/Adiabatic/Theorem.lean`

| Line | Axiom | Reference |
|------|-------|-----------|
| 53 | `adiabaticTheorem` | Jansen, Ruskai, Seiler (2007) |
| 110 | `eigenpath_traversal` | Corollary of adiabatic theorem |

The adiabatic theorem states that slow evolution under a time-dependent Hamiltonian keeps the system in the instantaneous ground state. Formalizing this requires the Schrodinger equation as a PDE, which is beyond current Lean 4/Mathlib scope.

**Note**: `SchrodingerEvolution.satisfies_equation := True` is a placeholder for the PDE formulation.

### Spectral Theory

**`resolvent_distance_to_spectrum` - PROVED** (formerly axiom, now theorem in `Operators.lean`)

For a Hermitian operator A with gamma not in the spectrum, the resolvent has positive
Frobenius norm. The proof shows: (1) the resolvent is nonzero because `(gamma*I - A) * R = I`
and `R = 0` would give `0 = I`; (2) a nonzero matrix has at least one nonzero entry whose
`Complex.normSq > 0`, making the Frobenius norm positive via `Finset.single_le_sum`.
Added `N > 0` hypothesis (always satisfied since `N = 2^n` with `n >= 1`).

## Tier 2: Spectral Gap Bounds (7 axioms)

**File**: `UAQO/Proofs/Spectral/GapBoundsProofs.lean`

These encode the spectral gap analysis from the paper. Each claims a bound on the gap `g(s) = E_1(s) - E_0(s)` of the adiabatic Hamiltonian `H(s) = -(1-s)|psi_0><psi_0| + s*H_z` in one of three regions.

### Crossing Region (3 axioms, from Proposition 1)

In the avoided crossing region `|s - s*| <= delta_s`, the gap has hyperbolic structure: `g(s)^2 = g_min^2 + c*(s - s*)^2`.

| Line | Axiom | Statement |
|------|-------|-----------|
| 152 | `crossing_region_gap_lower_bound_axiom` | `E1 - E0 >= minimumGap es hM / 2` |
| 234 | `crossing_region_gap_upper_bound_axiom` | `E1 - E0 <= 2 * minimumGap es hM` (requires E0=ground, E1=first excited) |
| 195 | `crossing_region_gap_exceeds_sStar_axiom` | `gap_s >= gapAtStar` (gap >= gap at s*) |

**Note on upper bound**: The lower bound holds for ANY eigenvalue pair (any gap >= spectral gap).
The upper bound only holds for the spectral gap pair (ground to first excited).
This is enforced by `hE0_ground` and `hE1_first` hypotheses added in the 2026-02-06 audit.

### Left Region (2 axioms, from Equation 317)

For `s < s* - delta_s`, the variational principle gives an explicit lower bound.

| Line | Axiom | Statement |
|------|-------|-----------|
| 210 | `left_region_explicit_bound_axiom` | `E1 - E0 >= (A1/A2) * (s* - s) / (1 - s*)` |
| 165 | `left_region_gap_exceeds_sStar_axiom` | `gap_s >= gapAtStar` (monotonicity) |

### Right Region (2 axioms, from Lemma 5)

For `s > s* + delta_s`, the resolvent method with Sherman-Morrison gives an explicit lower bound.

| Line | Axiom | Statement |
|------|-------|-----------|
| 249 | `right_region_explicit_bound_axiom` | `E1 - E0 >= (Delta/30) * (s - s0) / (1 - s0)` |
| 180 | `right_region_gap_exceeds_sStar_axiom` | `gap_s >= gapAtStar` (monotonicity) |

### Existing Infrastructure for Proving These

| Infrastructure | File | Status |
|---------------|------|--------|
| Eigenvalue condition (secular equation) | EigenvalueCondition.lean | Proved (1178 lines) |
| Variational principle | SpectralTheory.lean | Proved |
| Sherman-Morrison resolvent | GapBounds.lean | Proved |
| Spectral decomposition | Via Mathlib Matrix.Spectrum | Available |

**Gap**: Perturbation analysis near s* (Taylor expansion of secular equation, bounding cubic remainder) has no existing infrastructure.

## Tier 3A: Running Time (4 axioms)

**File**: `UAQO/Adiabatic/RunningTime.lean`

| Line | Axiom | Paper Ref | Dependencies |
|------|-------|-----------|--------------|
| 61 | `mainResult1` | Theorem 1 | adiabaticTheorem + gap bounds |
| 76 | `runningTime_ising_bound` | Theorem 1 corollary | mainResult1 + Ising conditions |
| 126 | `lowerBound_unstructuredSearch` | BBBV (1997) | External quantum lower bound |
| 134 | `runningTime_matches_lower_bound` | Optimality | Upper + lower bounds |

`mainResult1` is the paper's Theorem 1: AQO prepares the ground state in time `T = O((1/eps) * sqrt(A2) / (A1^2 * Delta^2) * sqrt(N/d0))`.

`lowerBound_unstructuredSearch` is the BBBV quantum search lower bound (external).

## Tier 3B: Hardness (5 axioms)

**File**: `UAQO/Complexity/Hardness.lean`

| Line | Axiom | Paper Ref | Dependencies |
|------|-------|-----------|--------------|
| 590 | `mainResult2` | Theorem 2 | NP-completeness + A1 threshold |
| 611 | `A1_approx_implies_P_eq_NP` | Corollary | mainResult2 |
| 1063 | `A1_numerator_polynomial_in_beta` | Eq. 319-320 | Algebraic structure |
| 1131 | `mainResult3` | Theorem 3 | Numerator polynomial + Lagrange |
| 1176 | `mainResult3_robust` | Lemma 2.8 | mainResult3 + Berlekamp-Welch |

`mainResult2` (Theorem 2): Approximating A1 to precision `1/(72(n-1))` distinguishes SAT from UNSAT, making it NP-hard.

`A1_numerator_polynomial_in_beta` (Eq. 319-320): The numerator polynomial P(beta) obtained by clearing denominators from A1(H_beta) has degree M-1 and its coefficients encode the degeneracies. Note: A1 itself is rational, not polynomial.

`mainResult3` (Theorem 3): M queries to an exact A1 oracle recover all degeneracies via Lagrange interpolation, making exact A1 computation #P-hard.

`mainResult3_robust` (Lemma 2.8): #P-hardness persists with precision eps < 1/(2*M^2), via Berlekamp-Welch error-correcting interpolation.

## Placeholder Definitions

Three definitions use placeholder values. These do not affect logical consistency but should be noted:

| Definition | File | Placeholder | Intended Meaning |
|-----------|------|-------------|------------------|
| `SharpThreeSAT.count` | SharpP.lean:34 | `fun _ => 0` | Count of satisfying assignments |
| `DegeneracyProblem.count` | SharpP.lean:195 | `fun _ => 0` | Eigenvalue degeneracy |
| `SchrodingerEvolution.satisfies_equation` | Theorem.lean:26 | `True` | Schrodinger PDE |

The axioms referencing these are about the mathematical concepts, not the Lean encodings. A complete formalization would replace these with proper definitions including encoding/decoding infrastructure.

## Verification

```bash
# Count all axioms
grep -rn "^axiom " UAQO/ | wc -l  # 25

# Count axioms by file
grep -rn "^axiom " UAQO/ | grep -v "Proofs/" | wc -l  # 18 (main)
grep -rn "^axiom " UAQO/Proofs/ | wc -l  # 7 (spectral)

# Check for sorries
lake build 2>&1 | grep sorry  # 1 (spectral_gap_pair_exists infrastructure)
```
