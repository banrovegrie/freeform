# UAQO Lean Formalization: Publication-Ready Plan

## Goal
Make the formalization publication-worthy: correct, complete, robust. Every axiom either proved or explicitly justified. Zero sorries. Clear separation between machine-verified mathematics and trusted external results.

## Current State
| Metric | Current | Target |
|--------|---------|--------|
| Axioms | 25 | 0 provable axioms remaining |
| Sorries | 0 | 0 |
| Build | Passes (2540 jobs) | Passes |
| Eliminated axioms | 31 | 31+ |

## Strategy: Three-Tier Classification

Not all 25 axioms are equal. A publication-worthy formalization clearly separates:

**Tier 1 - TRUSTED FOUNDATIONS (9 axioms)**: External results from other fields (Cook-Levin, Valiant, adiabatic theorem). These are standard in formalization literature. Kept as explicit `axiom` with documentation linking to published proofs. This is honest and standard practice.

**Tier 2 - PAPER RESULTS TO PROVE (11 axioms)**: Results from our paper that CAN be formalized. The spectral gap bounds (7), running time composition (2), and algebraic structure (2). These should be converted from axioms to theorems.

**Tier 3 - HIGH-LEVEL THEOREMS (5 axioms)**: Main results that are compositions of Tier 1 + Tier 2. These become theorems once their dependencies are proved. `mainResult1`, `mainResult2`, `mainResult3`, etc.

## Detailed Axiom Classification

### Tier 1: Trusted Foundations (9 axioms - KEEP as axioms)

These are well-established results from other fields. Keeping them as axioms is standard practice in formalization (analogous to Mathlib's `sorry`-free but axiom-reliant approach for ZFC).

| # | Axiom | Justification | Status |
|---|-------|---------------|--------|
| 1 | `threeSAT_in_NP` | Cook-Levin (1971). Could prove by constructing Verifier but adds ~500 lines for a textbook result. | KEEP |
| 2 | `threeSAT_NP_complete` | Cook-Levin theorem. Requires TM formalization (~3000+ lines). No Mathlib support. | KEEP |
| 3 | `sharpThreeSAT_in_SharpP` | Valiant (1979). Placeholder `count := fun _ => 0` means proof impossible without fixing encoding. | KEEP |
| 4 | `sharpThreeSAT_complete` | Valiant's theorem. Requires parsimonious reduction infrastructure. | KEEP |
| 5 | `sharpP_solves_NP` | Oracle complexity. Trivial conceptually (count > 0 iff SAT) but type-level encoding is substantial. | KEEP |
| 6 | `degeneracy_sharpP_hard` | Reduction from #3-SAT to degeneracy. Core paper contribution but requires placeholder fix. | KEEP |
| 7 | `adiabaticTheorem` | Jansen et al. Requires Schrodinger PDE formalization. `satisfies_equation := True` is placeholder. | KEEP |
| 8 | `eigenpath_traversal` | Follows from adiabatic theorem at intermediate times. Same PDE dependency. | KEEP |
| 9 | `resolvent_distance_to_spectrum` | Spectral theory for normal operators. Mathlib lacks this; would need ~200 lines. | PROVABLE |

**Action**: Document each with paper/textbook reference. Add `AXIOMS.md` file.

### Tier 2: Provable Paper Results (11 axioms - PROVE)

#### Spectral Gap Bounds (7 axioms in GapBoundsProofs.lean)

These encode the spectral analysis from Proposition 1, Equation 317, and Lemma 5 of the paper. Each claims a specific inequality about the spectral gap g(s) in one of three regions.

| # | Axiom | Paper Ref | Proof Strategy |
|---|-------|-----------|----------------|
| 10 | `crossing_region_gap_lower_bound_axiom` | Prop 1 | Secular equation hyperbolic structure: g(s)^2 = g_min^2 + c(s-s*)^2 |
| 11 | `crossing_region_gap_upper_bound_axiom` | Prop 1 | Same hyperbolic structure with window constraint |
| 12 | `left_region_explicit_bound_axiom` | Eq 317 | Variational principle with trial state |
| 13 | `right_region_explicit_bound_axiom` | Lemma 5 | Sherman-Morrison resolvent bound (infrastructure exists) |
| 14 | `left_region_gap_exceeds_sStar_axiom` | Eq 317 | Monotonicity from variational bound |
| 15 | `right_region_gap_exceeds_sStar_axiom` | Lemma 5 | Monotonicity from resolvent bound |
| 16 | `crossing_region_gap_exceeds_sStar_axiom` | Prop 1 | Direct from hyperbolic structure |

**Proof approach**: Each needs the secular equation analysis. The secular equation is:
  1/(1-s) = (1/N) sum_k d_k/(s*E_k - lambda)

Near the avoided crossing s*, this has hyperbolic structure. The key identity is:
  g(s)^2 = g_min^2 + c*(s - s*)^2

This gives all crossing region bounds. The left/right explicit bounds need the variational and resolvent methods respectively, which are partially built (ShermanMorrison.lean exists).

**Estimated effort per axiom**: 200-500 lines each, totaling ~2000-3500 lines.

#### Running Time (2 provable axioms)

| # | Axiom | Strategy |
|---|-------|----------|
| 17 | `runningTime_ising_bound` | Direct algebra: substitute polynomial bounds into `runningTime` formula |
| 18 | `runningTime_matches_lower_bound` | Combine upper bound (from runningTime) with lower bound structure |

**Note**: `mainResult1` (Theorem 1) and `lowerBound_unstructuredSearch` (BBBV) are Tier 3 / external.

#### Algebraic Structure (2 provable axioms)

| # | Axiom | Strategy |
|---|-------|----------|
| 19 | `A1_polynomial_in_beta` | Explicit algebra: expand A1 formula for beta-modified Hamiltonian, collect terms in beta. Degree M-1 follows from partial fraction decomposition. |
| 20 | `A1_approx_implies_P_eq_NP` | Direct corollary of mainResult2: if precision < 1/poly(n), distinguish SAT/UNSAT in poly time. |

### Tier 3: Composite Main Results (5 axioms)

These become theorems once Tier 2 is done and Tier 1 foundations are in place.

| # | Axiom | Dependencies | Strategy |
|---|-------|-------------|----------|
| 21 | `mainResult1` | adiabaticTheorem + gap bounds + schedule | Combine adiabatic theorem (T1) with gap bounds (T2) and local schedule integration |
| 22 | `mainResult2` | NP-completeness + A1 threshold | Show A1 distinguishes SAT/UNSAT at precision 1/(72(n-1)) |
| 23 | `mainResult3` | A1_polynomial_in_beta + Lagrange | M queries to A1 oracle recover polynomial, extract d_0 |
| 24 | `mainResult3_robust` | mainResult3 + Berlekamp-Welch | Error-correcting interpolation with 3M points |
| 25 | `lowerBound_unstructuredSearch` | BBBV (1997) | External quantum lower bound. Could prove or keep as axiom. |

## Phase Plan

### Phase 0: Correctness Audit [IMMEDIATE]

Before any new proofs, verify the existing formalization is correct:

1. **Verify axiom type signatures match the paper**
   - Cross-reference each axiom statement with the corresponding paper theorem/lemma
   - Check: are the hypotheses sufficient? Are there missing conditions?
   - Known issue: `SharpThreeSAT.count := fun _ => 0` is a placeholder

2. **Verify downstream theorem usage**
   - For each axiom, trace how it's used in theorems that depend on it
   - Check: could any axiom be FALSE as stated? This would make downstream theorems vacuously provable.
   - Known concern: `A1_approx_implies_P_eq_NP` should follow from `mainResult2` + Cook-Levin but is stated independently

3. **Check for logical consistency**
   - No axiom should contradict another
   - The 7 spectral axioms must be mutually consistent with the secular equation

4. **Fix placeholder definitions**
   - `SharpThreeSAT.count := fun _ => 0` makes `sharpThreeSAT_in_SharpP` unprovable
   - `DegeneracyProblem.count := fun _ => 0` makes `degeneracy_sharpP_hard` unprovable
   - `SchrodingerEvolution.satisfies_equation := True` makes `adiabaticTheorem` imprecise
   - Decision: either fix these or document them clearly as modeling choices

### Phase 1: Documentation [BEFORE PROVING]

Create `AXIOMS.md` documenting all 25 axioms:
- Mathematical statement in standard notation
- Paper reference (theorem/equation number)
- Justification for keeping as axiom vs proving
- Dependencies (what uses this axiom)
- Known issues or limitations

Update `README.md` with honest counts and clear status.

### Phase 2: Prove resolvent_distance_to_spectrum [1 axiom]

**Why first**: This is the only Tier 1 axiom that CAN be proved with current Mathlib.

For finite-dimensional Hermitian matrices over C, the resolvent norm equals the inverse distance to spectrum. Proof outline:
1. Hermitian A has real eigenvalues lambda_k and orthonormal eigenbasis v_k
2. R_A(gamma) = sum_k |v_k><v_k| / (gamma - lambda_k)
3. ||R_A(gamma)|| = max_k 1/|gamma - lambda_k| = 1/min_k|gamma - lambda_k| = 1/dist(gamma, spectrum)

Mathlib has: Matrix.IsHermitian.eigenvectorBasis, eigenvalues, spectral decomposition.

**Estimated**: ~200 lines.

### Phase 3: Prove Spectral Gap Bounds [7 axioms]

This is the core mathematical contribution of the formalization. The proofs require formalizing the secular equation analysis from the paper.

**Step 3a**: Formalize the secular equation
- Prove: eigenvalues of H(s) = -(1-s)|psi_0><psi_0| + s*H_z satisfy the secular equation
- This leverages the Matrix Determinant Lemma (already proved in MatrixDetLemma.lean)

**Step 3b**: Prove crossing region bounds (axioms 10, 11, 16)
- The hyperbolic structure g(s)^2 = g_min^2 + c(s-s*)^2 gives:
  - Lower bound: g(s) >= g_min (axiom 16 and 10 with /2 factor)
  - Upper bound: g(s) <= 2*g_min within the window (axiom 11)

**Step 3c**: Prove left region bound (axioms 12, 14)
- Variational principle with a trial state
- Eq 317: gap >= (A1/A2)(s*-s)/(1-s*)

**Step 3d**: Prove right region bound (axioms 13, 15)
- Sherman-Morrison resolvent (infrastructure exists in ShermanMorrison.lean)
- Lemma 5: gap >= (Delta/30)(s-s0)/(1-s0)

**Estimated**: ~3000-4000 lines total for all 7 axioms.

### Phase 4: Prove Running Time and Algebraic Structure [4 axioms]

**4a**: `runningTime_ising_bound` - Direct algebraic substitution
**4b**: `runningTime_matches_lower_bound` - Combine bounds
**4c**: `A1_polynomial_in_beta` - Partial fraction expansion
**4d**: `A1_approx_implies_P_eq_NP` - Corollary

**Estimated**: ~500-800 lines.

### Phase 5: Prove Main Results [3-5 axioms, depends on Tier 1 decisions]

Once Phases 2-4 are done, the main results become provable IF we accept Tier 1 axioms:
- `mainResult1` = adiabaticTheorem (T1) + gap bounds (T2) + schedule integration
- `mainResult2` = NP-completeness (T1) + A1 threshold (T2)
- `mainResult3` = Lagrange interpolation (proved) + A1_polynomial_in_beta (T2)
- `mainResult3_robust` = Berlekamp-Welch (proved) + mainResult3

`lowerBound_unstructuredSearch` (BBBV) decision: keep as Tier 1 axiom or formalize.

**Estimated**: ~1000-1500 lines.

### Phase 6: Final Audit and Publication Polish

1. Re-run full build
2. Count: 0 sorries, <=9 axioms (all Tier 1)
3. Update AXIOMS.md, README.md, ProofVerify.lean
4. Clean lint warnings
5. Add paper cross-references to all key theorems

## Success Criteria for Publication

A formalization paper should demonstrate:

1. **Scope**: All three main results (Theorems 1-3) formalized
2. **Depth**: Non-trivial proofs (spectral analysis, not just type-checking)
3. **Honesty**: Clear documentation of what's assumed vs proved
4. **Zero sorries**: No proof gaps
5. **Minimal trusted base**: Only well-established external results as axioms
6. **Builds cleanly**: `lake build` succeeds with 0 errors

## Risk Assessment

| Risk | Impact | Mitigation |
|------|--------|------------|
| Secular equation formalization is harder than expected | High | Can keep spectral axioms with enhanced documentation |
| Placeholder definitions prevent proofs | Medium | Fix placeholders OR restructure as hypotheses |
| Axiom type signatures don't match paper | Critical | Phase 0 audit catches this |
| New proofs break existing build | Medium | Incremental approach, build after each change |

## Decisions Log
- [2026-02-06] Plan created. Research agents launched.
- [2026-02-06] Research complete. Plan finalized with three-tier strategy.
- [2026-02-06] Key insight: placeholder definitions (count := 0, satisfies_equation := True) must be addressed for publication honesty.
