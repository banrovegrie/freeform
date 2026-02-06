# Findings

## Research Results

### 1. Axiom Catalog (25 total, 0 sorries)

**Files containing axioms** (7 files):
- `Foundations/Operators.lean:367` - 1 axiom (resolvent_distance_to_spectrum)
- `Adiabatic/Theorem.lean:53,110` - 2 axioms (adiabaticTheorem, eigenpath_traversal)
- `Adiabatic/RunningTime.lean:61,76,126,134` - 4 axioms
- `Complexity/NP.lean:38,51` - 2 axioms (Cook-Levin)
- `Complexity/SharpP.lean:44,70,78,205` - 4 axioms (Valiant + oracle)
- `Complexity/Hardness.lean:590,611,1061,1121,1162` - 5 axioms
- `Proofs/Spectral/GapBoundsProofs.lean:152-254` - 7 axioms

### 2. Mathlib4 Infrastructure

**Version**: Lean v4.28.0-rc1, Mathlib from main branch

**Available for spectral theory**:
- `Matrix.IsHermitian.eigenvalues0` - ordered eigenvalues
- `Matrix.IsHermitian.eigenvectorBasis` - orthonormal eigenbasis
- `Matrix.IsHermitian.mulVec_eigenvectorBasis` - A*v_k = lambda_k*v_k
- Spectral decomposition: A = sum_k lambda_k |v_k><v_k|

**Available for polynomials**:
- `Lagrange.interpolate` - polynomial interpolation (already used)
- `Polynomial.eval`, `Polynomial.natDegree`, degree bounds

**NOT available**:
- Resolvent operator theory (must build custom)
- Complexity classes NP/#P (fully custom)
- Quantum mechanics (fully custom)
- Spectral norm for finite-dimensional operators

### 3. Existing Proof Infrastructure

**Already proved** (31 former axioms eliminated):
- `eigenvalue_condition` - 1178-line proof via Matrix Determinant Lemma
- `groundEnergy_variational_bound` - spectral theorem + Parseval
- `shermanMorrison_resolvent` - matrix inverse verification
- `variational_principle` - projector positivity + spectral decomp
- `lagrange_interpolation` - Mathlib.Lagrange + uniqueness
- All SAT semantics lemmas (6 total)
- All beta-modified Hamiltonian lemmas (6 total)
- `complex_cauchy_schwarz` - full Cauchy-Schwarz proof
- `measurement_yields_groundstate` - measurement probability bound

## Key Insights

### Insight 1: Placeholder Definitions Are the Critical Blocker

Three definitions use placeholder values that prevent meaningful proofs:

1. **`SharpThreeSAT.count := fun _ => 0`** (SharpP.lean:34-38)
   - This makes `sharpThreeSAT_in_SharpP` **impossible to prove correctly**
   - The function returns 0 for ALL inputs, but #3-SAT should count satisfying assignments
   - Fixing requires: full encoding/decoding infrastructure for CNF formulas

2. **`DegeneracyProblem.count := fun _ => 0`** (SharpP.lean:195-199)
   - Same issue: always returns 0 instead of actual degeneracy count
   - `degeneracy_sharpP_hard` axiom asserts this is #P-hard, but the definition computes nothing

3. **`SchrodingerEvolution.satisfies_equation := True`** (Theorem.lean:26)
   - The Schrodinger equation is a placeholder `True`
   - `adiabaticTheorem` axiom relies on this but the PDE formulation is absent
   - This is acceptable: the adiabatic theorem is a physics result, not a math result to formalize

**Impact**: For (1) and (2), the axioms are about the CONCEPT (#3-SAT counting, degeneracy counting) not the specific Lean definition. The placeholder definitions are fine IF we document that the axiom asserts a property of the intended mathematical object, not the Lean encoding.

### Insight 2: Axiom Dependency Structure

```
                    ┌── threeSAT_in_NP ──┐
                    │                     ├── mainResult2 ── A1_approx_implies_P_eq_NP
                    │── threeSAT_NP_complete ──┘
                    │
adiabaticTheorem ───┤── mainResult1 ── runningTime_ising_bound
eigenpath_traversal │                    └── runningTime_matches_lower_bound
                    │                              ↑
                    │                    lowerBound_unstructuredSearch
                    │
sharpThreeSAT_*  ───┤── degeneracy_sharpP_hard ── mainResult3 ── mainResult3_robust
                    │                                  ↑
                    │              A1_polynomial_in_beta
                    │
gap axioms (7) ─────┴── downstream gap theorems (all proved from axioms)
resolvent_distance ──── (used in resolvent analysis)
```

### Insight 3: The 7 Spectral Axioms Are the Core Formalization Target

These 7 axioms represent the deepest original mathematics in the paper:
- 3 crossing region axioms (Proposition 1): g(s) bounds via secular equation hyperbolic structure
- 2 left region axioms (Eq 317): variational bound + monotonicity
- 2 right region axioms (Lemma 5): resolvent bound + monotonicity

The secular equation analysis is the common prerequisite. Key infrastructure already exists:
- `eigenvalue_condition` proves that eigenvalues satisfy the secular equation
- `shermanMorrison_resolvent` proves the Sherman-Morrison formula
- `variational_principle` proves the variational lower bound

**What's missing**: The perturbation analysis near s* that extracts the hyperbolic structure from the secular equation. This is the main proof effort.

### Insight 4: runningTime_ising_bound and runningTime_matches_lower_bound Are Provable Now

`runningTime_ising_bound` says: if Delta >= 1/n^p, A1 <= n^q, A2 <= n^r, then T = O(poly(n) * sqrt(N/d0) / eps). This is pure algebra: substitute the polynomial bounds into the `runningTime` formula and factor out.

`runningTime_matches_lower_bound` says: T = Theta(sqrt(N/d0)) up to polylog. This combines the upper bound (from runningTime formula) with the structural observation that the running time has the right scaling.

Both should be provable with ~200-300 lines each using existing infrastructure.

### Insight 5: A1_polynomial_in_beta Requires Substantial Algebra

The A1 formula for the beta-modified Hamiltonian expands to:
  A1(H_beta) = (1/2N) sum_{k>=1} d_k [1/E_k + 1/(E_k + beta/2)]

This is a rational function of beta. To show it's polynomial of degree M-1:
1. Common denominator: product of (E_k)(E_k + beta/2) terms
2. Numerator is polynomial in beta
3. After simplification, degree is M-1 (one term per eigenvalue level)
4. Coefficients encode degeneracies

This requires careful algebraic manipulation. Estimated: ~500-800 lines.

### Insight 6: mainResult2, mainResult3, mainResult3_robust Are Composite

These three axioms don't contain deep mathematical content themselves — they COMBINE Tier 1 foundations with Tier 2 algebraic results:

- `mainResult2`: Given A1 approximation to precision 1/(72(n-1)), can distinguish SAT/UNSAT. Proof: A1 differs by Theta(1/n) between SAT and UNSAT instances (from spectral analysis).
- `mainResult3`: M queries to exact A1 oracle recover all degeneracies via Lagrange interpolation. Proof: A1_polynomial_in_beta + lagrange_interpolation (already proved).
- `mainResult3_robust`: Same with error correction. Proof: mainResult3 + berlekamp_welch (already proved).

Once `A1_polynomial_in_beta` is proved, mainResult3 and mainResult3_robust should follow in ~200 lines each.

### Insight 7: Paper Proof Difficulty Map (from paper analysis agent)

| Result | Technique | Difficulty | Est. Lines |
|--------|-----------|------------|------------|
| Secular equation | Rank-one eigenvalue analysis | Low | ~100 |
| Avoided crossing (Lemma A1) | Taylor expansion + IVT | Medium-High | ~500 |
| Gap in crossing window | Direct computation | Low-Medium | ~200 |
| Left gap (Eq 317) | Variational with trial state | Low-Medium | ~300 |
| Right gap (Lemma 5) | Resolvent + Sherman-Morrison | **High** | ~800+ |
| Running time composition | Integral evaluation | Medium | ~300 |
| NP-hardness | Tensor product + partial fractions | Medium | ~400 |
| #P-hardness | Polynomial interpolation | Medium-High | ~400 |

The RIGHT GAP (Lemma 5) is the hardest: requires proving f(s) monotonically decreasing via calculus (f = u/v, show u'v - uv' < 0). This is ~150 lines of algebra in the paper and substantially more in Lean.

The LEFT GAP (Eq 317) is more tractable: construct ansatz |phi> = (1/sqrt(A2*N)) sum sqrt(d_k)/(E_k-E_0) |k>, compute <phi|H(s)|phi>, use variational principle.

### Insight 8: Existing Infrastructure Coverage

The paper analysis reveals strong alignment between what's already proved and what's needed:

| Paper Result | Required Infrastructure | Already Proved? |
|-------------|------------------------|-----------------|
| Secular equation | Rank-one perturbation | eigenvalue_condition (1178 lines) |
| Left gap variational | Variational principle | variational_principle |
| Right gap resolvent | Sherman-Morrison | shermanMorrison_resolvent |
| Spectral decomposition | Hermitian eigenbasis | Via Mathlib Matrix.Spectrum |
| Lagrange interpolation | Polynomial uniqueness | lagrange_interpolation |
| Berlekamp-Welch | Error-correcting interp | berlekamp_welch |
| Cauchy-Schwarz | Inner product bound | complex_cauchy_schwarz |
| Measurement bound | Fidelity -> probability | measurement_yields_groundstate |

Gap: The **perturbation analysis near s*** (Taylor expansion of secular equation, bounding cubic remainder) has NO existing infrastructure.

## Blockers & Risks

### Critical Risks

1. **Secular equation perturbation analysis complexity**: The hyperbolic structure proof may be substantially harder to formalize than the paper suggests. The paper uses asymptotic expansions that are difficult in Lean.

2. **Type-level encoding mismatches**: The formalization uses `EigenStructure n M` as the core type, but some axioms reference intermediate types (`A1Approximator`, `A1ExactComputer`, `threeSATToPartialHamiltonian`). These type relationships need careful verification.

3. **Spectral gap at s* is defined differently from the paper**: Need to verify `minimumGap` definition matches the paper's g_min = 2A1/(A1+1) * sqrt(d0/(N*A2)).

### Medium Risks

4. **Build times**: Adding ~5000-7000 lines of proofs may significantly increase build time. Mathlib dependency already adds substantial compile time.

5. **Placeholder definitions**: The count functions returning 0 are semantically wrong. A reviewer may flag this even if axioms are documented.

### Low Risks

6. **Lint warnings**: 4 existing warnings about unused variables. Easy to fix.

7. **README inaccuracies**: Currently claims different axiom counts. Must update for publication.
