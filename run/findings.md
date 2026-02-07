# Findings: UAQO Lean 4 Formalization Strengthening

## Phase 1+3 Results (Completed)

### Encoding Infrastructure
- Unary encoding scheme: n ones + zero for Nat, variable index + sign for Literal
- Length-prefixed clauses, length-prefixed formula
- Round-trip correctness fully proved (decode_encode)
- Injectivity fully proved (encodeCNF_injective)
- Key pattern: recursive encodeNat definition, not List.replicate

### Sorry Classification

**Irreducible axioms (cannot be eliminated with current Mathlib):**
- IsPolynomialTime — needs Turing machine model
- SatisfiesSchrodingerEquation — needs operator-valued ODE theory
- DegeneracyProblem.count — needs eigenvalue encoding infrastructure

**Downstream sorries (depend on irreducible axioms):**
- threeSAT_in_NP — depends on IsPolynomialTime
- sharpThreeSAT_in_SharpP — depends on IsPolynomialTime
- sharpThreeSAT_complete — depends on IsPolynomialTime
- degeneracy_sharpP_hard — depends on IsPolynomialTime
- A1_approx_implies_P_eq_NP — depends on IsPolynomialTime
- lowerBound_unstructuredSearch — quantum adversary method

**Structural sorries (from SatisfiesSchrodingerEquation):**
- Theorem.lean:77 — adiabaticTheorem evolution construction
- Theorem.lean:152 — eigenpath_traversal evolution construction
- RunningTime.lean:79 — mainResult1 evolution construction

## Gap Bound Analysis

FullSpectralHypothesis is the only remaining mathematical axiom that could
potentially be eliminated. The secular equation infrastructure is complete:
- 8 theorems in SecularEquation.lean, all proved
- Monotonicity, pole behavior, root existence/uniqueness
- Ground eigenvalue characterization

What's missing: quantitative gap bound from secular equation roots to
minimumGap. This requires:
1. Perturbation theory near avoided crossing (novel analysis)
2. Variational bound in left region
3. Resolvent bound in right region
4. Eigenvalue continuity
5. Gluing argument

This is a multi-week mathematical research effort, not a coding task.

## Lean 4 Patterns Learned

- `simp only [defn, List.append_assoc, roundtrip_lemma]` for match-heavy proofs
- DON'T use List.replicate in recursive encodings — use pattern matching
- `show` tactic fails when associativity differs — use `simp only` instead
- `sorry` as definition body creates an opaque Prop (honest axiom pattern)
- `Classical.decPred` for decidable predicates from classical logic
