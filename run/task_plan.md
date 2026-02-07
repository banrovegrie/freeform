# UAQO Lean 4 Formalization: Remaining Work Plan

## Status Summary

| Phase | Status | Notes |
|-------|--------|-------|
| Phase 1: Honest axiomatization | COMPLETE | 4 placeholders replaced with honest sorry |
| Phase 3: CNF encoding | COMPLETE | Full encoding/decoding with round-trip proof |
| Phase 4.5: Revert weakened defs | PARTIAL | CountingReduction restored, lowerBound sorry |
| Phase 2: Gap bound proof | NOT STARTED | Hardest part, axiomatized via FullSpectralHypothesis |
| Phase 4: Strengthen main results | NOT STARTED | Depends partially on Phase 2 |
| Phase 5: Documentation | NOT STARTED | Final pass |

## Current Build State

- 2541 build jobs, 0 errors
- 9 sorry statements (all honest, documented)
- 0 hidden placeholders

### Sorry Inventory

| File | Line | What | Why |
|------|------|------|-----|
| Basic.lean | 96 | IsPolynomialTime | Turing machines beyond Mathlib |
| Theorem.lean | 25 | SatisfiesSchrodingerEquation | PDE beyond Mathlib |
| Theorem.lean | 77 | evol.satisfies_equation | Depends on above |
| Theorem.lean | 152 | evol.satisfies_equation | Depends on above |
| RunningTime.lean | 240 | lowerBound_unstructuredSearch | Quantum adversary method |
| NP.lean | 48 | threeSAT_in_NP | Needs IsPolynomialTime |
| SharpP.lean | 52 | sharpThreeSAT_in_SharpP | Needs IsPolynomialTime |
| SharpP.lean | 93 | sharpThreeSAT_complete | Needs IsPolynomialTime |
| SharpP.lean | 237 | DegeneracyProblem.count | Eigenvalue encoding |
| SharpP.lean | 248 | degeneracy_sharpP_hard | Needs IsPolynomialTime |
| Hardness.lean | 788 | A1_approx_implies_P_eq_NP | Needs IsPolynomialTime |

Note: RunningTime.lean line 79 has satisfies_equation := sorry too.

## Phase 2: Gap Bound (FullSpectralHypothesis)

### What FullSpectralHypothesis captures

Located in GapBoundsProofs.lean (line 69-76):
```
structure FullSpectralHypothesis (es : EigenStructure n M) (hM : M >= 2) : Prop where
  cond : spectralConditionForBounds es hM
  gap  : forall s in [0,1], E0 < E1 -> E1 - E0 >= minimumGap es hM
```

### Assessment: Is proving this tractable?

**Available infrastructure (all fully proved):**
- Secular equation F(s,lambda) and its derivative
- Strict monotonicity of F on pole-free intervals
- Pole behavior (tendsto_top, tendsto_bot)
- Unique root below ground eigenvalue (IVT)
- Ground eigenvalue = secular root characterization
- Eigenvalue condition via Matrix Determinant Lemma
- Sherman-Morrison resolvent formula
- Variational principle
- A1, A2 spectral parameter positivity and bounds

**Missing for proof (5 lemmas ~1500 lines):**

1. Left Region Bound (~300 lines) — Eq. 317
   - Trial state construction + variational principle
   - Tractable with existing infrastructure

2. Crossing Region (~400 lines) — Proposition 1
   - Second-order secular equation analysis
   - Taylor expansion around avoided crossing
   - HARDEST PART — novel perturbation theory

3. Right Region Bound (~450 lines) — Lemma 5
   - Sherman-Morrison + resolvent norm bound
   - Moderately tractable

4. Eigenvalue Continuity (~200 lines)
   - Implicit function theorem for secular roots
   - Tractable

5. Gluing (~150 lines)
   - Case split + combine regional bounds
   - Easy once 1-4 are done

### Verdict

Phase 2 is a genuine multi-week research effort. The crossing region analysis
(Lemma 2) is the mathematical heart of the paper and requires deep perturbation
theory. This is NOT tractable in a single session.

**Decision: Keep FullSpectralHypothesis as explicit axiom** with the following
honest documentation:
- Cite paper's Proposition 1
- Explain that secular equation infrastructure is complete
- Note that the quantitative bound requires 5 additional lemmas
- Classify as "Layer 2: explicit hypothesis" not "Layer 1: proved"

## Phase 4: Strengthen Main Results (tractable parts)

### 4A: Theorem.lean — adiabaticTheorem

Current state: `exists evol` with trivially constructed witness (ground state
substituted as evolution). The `satisfies_equation` field uses sorry.

**Assessment:** Cannot improve without formalizing Schrodinger PDE. Keep as is.
The honest axiom (SatisfiesSchrodingerEquation) correctly documents the limitation.

### 4B: Hardness.lean — mainResult2

Current state: Uses classical case split on satisfiability. This is a genuine
limitation — the two-query protocol structure is present but the proof is
not constructive.

**Assessment:** The proof would need:
- Modified Hamiltonian construction (already exists: toModifiedPartial)
- A1 difference bound (already exists: betaModified_A1_diff_pos)
- SAT encoding correctness (already exists: threeSAT_satisfiable_iff_degPositive)
The proof structure is already sound. The sorry dependency is only on
IsPolynomialTime for the final P=NP implication.

### 4C: Hardness.lean — mainResult3

Current state: Uses extractDegeneracy_correct and numeratorPoly_eval (genuine).
Already connected to real encoding via SharpThreeSAT.

**Assessment:** Already in good shape. No further work needed.

### 4D: RunningTime.lean — lowerBound_unstructuredSearch

Current state: sorry. Would need quantum adversary method.

**Assessment:** Keep as sorry. Quantum adversary method is a substantial
formalization effort (Ambainis 2000).

## Phase 5: Documentation

### What needs updating

1. **ProofVerify.lean** — Update sorry count and locations
   - Currently says "0 hidden placeholders, ~24 genuine theorems"
   - Verify this matches reality
   - Make sure decodeCNF_impl is listed as RESOLVED

2. **Test/Verify.lean** — Verify all rfl tests pass
   - Already updated with encoding import
   - Check that all paper equation tests are present

3. **MEMORY.md** — Update with current state

### What does NOT need updating

- README.md is for the thesis, not the Lean formalization
- CLAUDE.md is project instructions, not formalization docs

## Actionable Next Steps (this session)

1. [x] Build verification — confirmed 2541 jobs, 0 errors
2. [ ] Verify ProofVerify.lean sorry list matches reality
3. [ ] Verify Test/Verify.lean is complete
4. [ ] Check if any sorries in RunningTime.lean can be improved
5. [ ] Update MEMORY.md to reflect final state
6. [ ] Final documentation pass on ProofVerify.lean
