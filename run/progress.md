# Progress Log

## Session: 2026-02-06

### Actions Taken
- Created planning files (task_plan.md, findings.md, progress.md)
- Launched 3 research agents:
  1. Axiom catalog agent (comprehensive analysis of all 25 axioms)
  2. Lean 4 / Mathlib4 infrastructure agent (what's available for proofs)
  3. Paper mathematics agent (detailed proof techniques from the paper)

### Research Complete
- All 25 axioms cataloged with full type signatures and file locations
- Mathlib4 infrastructure mapped: spectral theory, polynomial, matrix norms available
- Key blockers identified: placeholder definitions, secular equation complexity
- Three-tier classification established (Trusted Foundations / Provable / Composite)

### Plan Finalized
- Phase 0: Correctness audit (verify axiom statements match paper)
- Phase 1: Documentation (AXIOMS.md, README update)
- Phase 2: Prove resolvent_distance_to_spectrum (1 axiom, ~200 lines)
- Phase 3: Prove spectral gap bounds (7 axioms, ~3000-4000 lines)
- Phase 4: Prove running time + algebraic structure (4 axioms, ~500-800 lines)
- Phase 5: Prove main results (3-5 axioms, ~1000-1500 lines)
- Phase 6: Final audit and publication polish

### Key Decision
Publication strategy: keep 9 Tier 1 axioms (external foundations) with full documentation. Prove remaining 16 axioms. This is honest, standard practice in formalization literature, and achievable.

### Phase 0: Correctness Audit (COMPLETE)

Launched spectral and hardness audit agents. Found critical issues:

1. **`crossing_region_gap_upper_bound_axiom` was FALSE**: Quantified over arbitrary
   eigenvalue pairs but upper bound only holds for spectral gap pair. Fixed by adding
   `hE0_ground` and `hE1_first` hypotheses. Updated all downstream consumers:
   - `crossing_region_gap_upper_bound` wrapper
   - `sStar_gap_upper_bound` derived theorem
   - `gap_at_sStar_bounds` lemma (added ground/first-excited to existential)
   - `gap_at_avoided_crossing_proof` (switched to `spectral_gap_pair_exists`)
   - `gap_minimum_at_crossing_proof` (switched to `spectral_gap_pair_exists`)

2. **`A1_polynomial_in_beta` was FALSE**: A1(H_beta) is rational, not polynomial.
   Renamed to `A1_numerator_polynomial_in_beta`. Restated to describe the numerator
   polynomial P(beta) = D(beta) * f(beta) where D is the known common denominator.

3. **`mainResult3_robust` used fixed precision**: Changed from `2^(-10)` to
   formula-dependent `1/(2*M^2)`.

4. **`spectral_gap_exists` returned wrong pair**: Added `spectral_gap_pair_exists`
   returning (E_0, E_1) with ground/first-excited witnesses. Contains 1 sorry
   (bridge lemma: IsEigenvalue <-> Mathlib eigenvalue).

### Phase 1: Documentation (COMPLETE)

- Updated AXIOMS.md with audit findings and corrected axiom descriptions
- Updated README.md with audit results and renamed axiom
- Updated ProofVerify.lean references

### Phase 2: Prove resolvent_distance_to_spectrum (COMPLETE)

- Proved `resolvent_distance_to_spectrum` in Operators.lean
- Proof strategy: nonzero resolvent (R=0 implies 0=I contradiction) + Frobenius positivity
- Added `N > 0` hypothesis (always satisfied: N = 2^n with n >= 1)
- Axiom count: 25 → 24

### Phase 2b: Eliminate spectral_gap_pair_exists sorry (COMPLETE)

- Proved bridge lemma `isEigenvalue_is_mathlib_eigenvalue` in GapBoundsProofs.lean
  - Strategy: eigenbasis expansion + Parseval. If E is eigenvalue with eigenvector v,
    expand v in orthonormal eigenbasis. Hermiticity + eigenvalue mismatch force all
    inner products to zero, contradicting ||v||^2 > 0.
- Proved `spectral_gap_pair_exists` using bridge lemma + `min_eigenvalue_to_our` + `Finset.min'`
- Key technical challenges resolved:
  - `conj` vs `Complex.conj` vs `star` matching: used existing `conj_ofReal'` from EigenvalueCondition.lean
  - EuclideanSpace ↔ Fin N → C coercion: used `apply hne; ext i; exact hall i` pattern
  - Eigenvalue coercion rewriting: used `simp only` instead of `rwa`
- Updated AXIOMS.md, README.md, ProofVerify.lean documentation

### Build Status
- Full build: 2540 jobs, 0 errors
- Sorries: 0
- Axioms: 24 (8 external + 7 spectral + 4 running time + 5 hardness)

### Status
PHASE 0-2 COMPLETE - Ready for Phase 3 (spectral gap bounds)
