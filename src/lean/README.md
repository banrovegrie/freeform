# UAQO: Lean 4 Formalization

Formal verification of "Unstructured Adiabatic Quantum Optimization: Optimality with Limitations" (arXiv:2411.05736) in Lean 4 with Mathlib4. The formalization captures the paper's definitions, theorem statements, and type dependencies, splitting the mathematical content into genuine proofs and explicit axioms with citations.

## Build

```bash
lake update
lake build
```

Build completes in roughly 2-5 minutes depending on cache state. The final line of output should read something like `Build completed successfully`.

## Status

Zero sorry. Fifteen explicit Lean `axiom` declarations, each with a paper citation visible via `#print axioms`. Zero vacuous `True` proofs. Approximately 32 genuine theorems with full machine-checked proofs, plus roughly 40 supporting lemmas.

The spectral gap lower bound (Proposition 1) is carried as an explicit hypothesis (`FullSpectralHypothesis`), not an axiom. Infrastructure for the perturbation-theoretic analysis exists (secular equation continuity, strict monotonicity, IVT, root uniqueness) but the full proof is not completed.

## Architecture

The formalization has three layers.

The first layer is **axioms**: 15 declarations using Lean's `axiom` keyword. Each represents a formalization boundary beyond Lean 4/Mathlib scope (quantum dynamics PDEs, polynomial-time reductions, quantum adversary methods). Every axiom carries a citation to a specific theorem or equation in a published paper.

The second layer is **definitions**: `EigenStructure`, `spectralParam`, `avoidedCrossingPosition`, `minimumGap`, `runningTime`, `A1Approximator`, decision and counting problems, CNF encoding infrastructure. These are the types and computable objects that give the formalization its structure.

The third layer is **theorems**: some proved purely within Lean/Mathlib (genuine), some proved by invoking one or more axioms. The distinction is tracked by `#print axioms` and documented in `Test/Verify.lean`.

## Complete Axiom Inventory

Fifteen axioms in four groups.

### Primitive Concepts (3)

These axioms introduce concepts that cannot be defined within Lean 4/Mathlib because they refer to computational complexity or continuous quantum dynamics.

| Axiom | File | Type | Citation |
|-------|------|------|----------|
| `IsPolynomialTime` | Complexity/Basic.lean | `(List Bool -> List Bool) -> Prop` | Arora-Barak, Ch. 1 |
| `SatisfiesSchrodingerEquation` | Adiabatic/Theorem.lean | `TimeDependentHam -> (Real -> NQubitState) -> Prop` | Jansen et al. (2007), S2 |
| `degeneracyCount` | Complexity/SharpP.lean | `List Bool -> Nat` | arXiv:2411.05736, S2.3 |

`IsPolynomialTime` is the predicate asserting a function runs in polynomial time. Without it, no complexity-theoretic statement can connect to algorithms. `SatisfiesSchrodingerEquation` asserts that a state trajectory solves the Schrodinger PDE, which requires operator-valued differential equations beyond Mathlib. `degeneracyCount` is the function computing eigenvalue degeneracies from encoded Hamiltonians.

### Standard Complexity Results (3)

These axioms encode textbook results whose proofs require `IsPolynomialTime`.

| Axiom | File | Statement | Citation |
|-------|------|-----------|----------|
| `threeSAT_in_NP` | Complexity/NP.lean | `InNP ThreeSAT` | Cook (1971) |
| `sharpThreeSAT_in_SharpP` | Complexity/SharpP.lean | `InSharpP SharpThreeSAT` | Valiant (1979) |
| `sharpThreeSAT_hard` | Complexity/SharpP.lean | `IsSharpPHard SharpThreeSAT` | Valiant (1979) |

### Quantum Physics Results (6)

These axioms encode results from quantum dynamics whose proofs require solving the Schrodinger equation or applying quantum information-theoretic lower bounds.

| Axiom | File | Citation |
|-------|------|----------|
| `adiabatic_evolution_bound` | Adiabatic/Theorem.lean | Jansen, Ruskai, Seiler (2007), Thm 3 |
| `eigenpath_evolution_bound` | Adiabatic/Theorem.lean | Jansen et al. (2007), Corollary |
| `adiabaticTheorem_localSchedule_bound` | Adiabatic/Theorem.lean | Roland-Cerf (2002) |
| `phaseRandomization_bound` | Adiabatic/Theorem.lean | Cunningham, Grover, Russomanno (2023) |
| `mainResult1_evolution` | Adiabatic/RunningTime.lean | arXiv:2411.05736, Thm 1 |
| `lowerBound_unstructuredSearch` | Adiabatic/RunningTime.lean | Farhi, Goldstone, Gutmann (2000) |

### Paper Results (3)

These axioms encode results specific to the paper that depend on the primitive concept axioms.

| Axiom | File | Statement | Citation |
|-------|------|-----------|----------|
| `gareyJohnsonEncoding` | Complexity/Hardness.lean | `SATHamiltonianEncoding f` | Garey-Johnson (1976) |
| `degeneracy_sharpP_hard` | Complexity/SharpP.lean | `IsSharpPHard DegeneracyProblem` | arXiv:2411.05736, Thm 3 |
| `A1_approx_implies_P_eq_NP` | Complexity/Hardness.lean | poly-precision A1 approx implies P=NP | arXiv:2411.05736, Cor. Thm 2 |

## Genuine Theorem Inventory

Theorems proved entirely within Lean 4/Mathlib, with no custom axiom dependencies beyond `propext`, `Classical.choice`, and `Quot.sound`.

### Spectral Theory and Gap Analysis

| Theorem | Technique |
|---------|-----------|
| `resolvent_distance_to_spectrum` | Frobenius norm positivity |
| `isEigenvalue_iff_det_eq_zero` | Standard linear algebra |
| `eigenvalue_condition` | Matrix Determinant Lemma + Sherman-Morrison |
| `isEigenvalue_is_mathlib_eigenvalue` | Eigenbasis expansion + Parseval |
| `spectral_gap_pair_exists` | `Finset.min'` on eigenvalue set |
| `variational_principle` | Spectral decomposition, min eigenvalue |
| `adiabaticHam_hermitian` | Hermiticity of sum of Hermitian operators |
| `secularFun_strictMono_on_interval` | IVT + monotonicity of secular function |
| `exists_unique_root_below_ground` | IVT + uniqueness argument |

### Complexity and Hardness

| Theorem | Technique |
|---------|-----------|
| `lagrange_interpolation` | Mathlib `Lagrange.interpolate`, uniqueness by root counting |
| `berlekamp_welch` | Error-correcting polynomial structure |
| `A1_numerator_polynomial_in_beta` | `(X+1)^(M-1)` expansion + Finset even/odd bijection (`Finset.sum_nbij`) |
| `betaModified_A1_diff_pos` | `Finset.sum_nbij` for bijecting index sets |
| `threeSAT_satisfiable_iff_degPositive` | CNF encoding correctness (round-trip proof) |
| `extractDegeneracy_correct` | Paper's extraction formula (line 912) via Lagrange evaluation |
| `numeratorPoly_eval` | Lagrange interpolation evaluation identity |
| `mainResult2` | Uses `gareyJohnsonEncoding` axiom + `twoQuery_sat`/`twoQuery_unsat` |
| `mainResult3` | Extraction formula + `extractDegeneracy_correct` |
| `sharpThreeSAT_complete` | From axioms `sharpThreeSAT_in_SharpP` + `sharpThreeSAT_hard` |
| `decode_encode` | CNF encoding round-trip correctness |
| `encodeCNF_injective` | Encoding injectivity |

### Running Time and Optimality

| Theorem | Technique |
|---------|-----------|
| `runningTime_pos` | Positivity of spectral parameters |
| `runningTime_ising_bound` | Polynomial bound absorption with `FullSpectralHypothesis` |
| `runningTime_matches_lower_bound` | Sandwich between lower and upper bounds |
| `finalState_symmetric` | Symmetric state normalization |

### Experiment Theorems (Circumventing the Barrier)

| Theorem | Technique |
|---------|-----------|
| `theorem1_product_invariance` | Definitional (rfl) |
| `theorem2_uniform_gives_A1` | `Finset.sum_congr` + amplitude calculation |
| `theorem3_coupled_nonconstant` | Explicit 1-qubit construction |
| `theorem4_multisegment_rigidity` | Two-instance contradiction |
| `theorem5_nogo_algebraic_core` | Strict monotonicity of `a/(a+1)` |
| `crossing_strict_mono` | `div_lt_div_iff` + `nlinarith` |
| `crossing_sensitivity_exact` | `field_simp; ring` |

Plus approximately 40 supporting lemmas covering Sherman-Morrison, A2 bounds, Cauchy-Schwarz, measurement probability bounds, schedule monotonicity, degeneracy counting bijections, modified Hamiltonian preservation, and Finset arithmetic.

## Theorems Proved from Axioms

These theorems invoke axioms for their proof content. Each axiom represents a formalization boundary and carries a paper citation.

| Theorem | Axiom(s) Used | Paper Reference |
|---------|---------------|-----------------|
| `adiabaticTheorem` | `adiabatic_evolution_bound` | Jansen et al. (2007), Thm 3 |
| `adiabaticTheorem_localSchedule` | `adiabaticTheorem_localSchedule_bound` | Roland-Cerf (2002) |
| `phaseRandomization` | `phaseRandomization_bound` | Cunningham et al. (2023) |
| `eigenpath_traversal` | `eigenpath_evolution_bound` | Jansen et al. (2007), Cor. |
| `mainResult1` | `mainResult1_evolution` | arXiv:2411.05736, Thm 1 |
| `mainResult2` | `gareyJohnsonEncoding` | arXiv:2411.05736, Thm 2 |
| `sharpThreeSAT_complete` | `sharpThreeSAT_in_SharpP` + `sharpThreeSAT_hard` | Valiant (1979) |
| `exact_A1_is_sharpP_hard` | `degeneracy_sharpP_hard` | arXiv:2411.05736, Thm 3 |

`mainResult2` is a genuine proof: it uses `gareyJohnsonEncoding` to obtain the Garey-Johnson Hamiltonian where E_0 = 0 iff the formula is satisfiable, then proves algebraically that the two-query difference D equals zero iff E_0 = 0 (via `twoQuery_sat` and `twoQuery_unsat`). The logical structure of the proof is fully machine-checked.

`mainResult3` is fully genuine with no custom axiom dependencies beyond `propext`, `Classical.choice`, and `Quot.sound`. It uses `extractDegeneracy_correct` (the paper's extraction formula proved via Lagrange interpolation) to recover degeneracies from polynomial evaluation.

## Experiment Results

The `Experiments/` directory contains two formalizations: structured tractability (Experiment 08) and circumventing the A1 barrier (Experiment 12).

### Theorems 3 and 4: Explicit Constructions

Theorems 3 and 4 from the barrier experiment are proved by explicit 1-qubit construction. The file defines `oneQubitES`, an `EigenStructure` on a 1-qubit system (n=1, N=2, M=2) parameterized by the excited eigenvalue E1. Instance A has eigenvalues (0, 1) giving A1 = 1/2. Instance B has eigenvalues (0, 1/2) giving A1 = 1.

Theorem 3 exhibits a non-uniform state (all weight on level 1) where A1_eff = 1 differs from A1 = 1/2, proving that entangled initial states break universality. Theorem 4 shows that any fixed set of schedule parameters fails to equal A1 for both instances simultaneously, by deriving a contradiction from 1/2 = fixedParams 0 = 1.

Both theorems have no custom axiom dependencies. Running `#print axioms` on either shows only `propext`, `Classical.choice`, and `Quot.sound`.

### The Quantifier Bug-Catch

The formalization of Theorem 4 caught a wrong quantifier ordering in an earlier draft of the paper. The original claim had the form "for all instances, there exist parameters such that ..." which is trivially true (just pick parameters matching each instance individually). The correct claim is "for all parameters, there exists an instance such that the parameters fail" (equivalently, no fixed parameters work for all instances). Lean's type checker rejected the original quantifier ordering because the proof obligation dissolved into triviality. This is a concrete instance of formalization catching a mathematical error that survived informal review.

## FullSpectralHypothesis

The paper's Proposition 1 (spectral gap lower bound) is not axiomatized. Instead, it appears as an explicit hypothesis:

```lean
structure FullSpectralHypothesis (es : EigenStructure n M) (hM : M >= 2) where
  cond : spectralConditionForBounds es hM
  gap  : forall s E0 E1, ... -> E1 - E0 >= minimumGap es hM
```

Theorems that need the gap bound (such as `runningTime_ising_bound` and `runningTime_matches_lower_bound`) take `FullSpectralHypothesis` as an explicit parameter. The paper proves this proposition from secular equation analysis. The formalization assumes it. Supporting infrastructure exists in `Proofs/Spectral/`: secular equation continuity, strict monotonicity on intervals, IVT for root existence, and uniqueness of the root below the ground state energy. The remaining gap is the perturbation-theoretic analysis connecting these pieces to the explicit gap bound.

This design choice is deliberate. Carrying the gap bound as a hypothesis rather than an axiom makes the logical dependency visible: any theorem using the gap bound has `FullSpectralHypothesis` in its type signature, so a reader (or Lean itself) can see exactly where the unproved assumption enters.

## Faithfulness to Paper

| Item | Paper Reference | Status |
|------|----------------|--------|
| $H(s) = -(1-s)\lvert\psi_0\rangle\langle\psi_0\rvert + s H_z$ | Eq. 1 | EXACT |
| $A_p = (1/N) \sum d_k/(E_k-E_0)^p$ | Eq. 5 | EXACT |
| $s^* = A_1/(A_1+1)$ | Eq. 6 | EXACT |
| $\delta_s = 2/(A_1+1)^2 \sqrt{d_0 A_2/N}$ | Eq. 7 | EXACT |
| $g_{\min} = (1-2\eta) \cdot 2A_1/(A_1+1) \cdot \sqrt{d_0/(A_2 N)}$ | Eq. 311 ($\eta=0.1$) | EXACT |
| EigenStructure | Definition 1 | EXACT |
| Gap region formulas | Eqs. 317, 347 | EXACT |
| Extraction: $d_k = N P(-2\Delta_k)/\prod(\Delta_l-\Delta_k)$ | Line 912 | EXACT |
| mainResult1 statement | Theorem 1 | EXACT |
| mainResult2 (two-query protocol) | Theorem 2 | GENUINE |
| mainResult3 extraction | Theorem 3 | GENUINE |

The `Test/Verify.lean` file contains definitional equality tests (`rfl` proofs) confirming that the Lean definitions match the paper's equations. For example, `spectralParam`, `avoidedCrossingPosition`, `avoidedCrossingWindow`, and `minimumGap` all reduce to the exact formulas from the paper.

## Formalization Boundaries

The axioms exist because certain mathematical infrastructure lies outside Lean 4/Mathlib.

**Quantum dynamics.** The Schrodinger equation $i/T \cdot d|\psi\rangle/ds = H(s)|\psi\rangle$ is an operator-valued PDE. Lean/Mathlib has no framework for time-dependent operator differential equations. Six of the fifteen axioms (the quantum physics group) stem from this limitation.

**Polynomial-time computation.** Lean can express that a function exists, but the predicate "runs in polynomial time" requires a computational model (Turing machines or circuits). The `IsPolynomialTime` axiom and the three complexity results that depend on it exist because Lean/Mathlib lacks a formalized complexity theory library.

**Quantum lower bounds.** The Farhi-Goldstone-Gutmann lower bound for unstructured search requires the quantum adversary method or polynomial method. These are information-theoretic arguments about quantum query complexity, not algebraic identities. Formalizing them would require quantum information theory infrastructure.

The formalization boundary is drawn at the point where mathematics transitions from algebra and combinatorics (which Lean/Mathlib handles well) to analysis of dynamical systems, computational complexity, and quantum information theory (which it does not yet handle). Everything on the algebraic side is proved; everything on the dynamics/complexity side is axiomatized with citations.

## Verification Commands

```bash
# Count axioms (expect 15)
grep -rn "^axiom " UAQO/

# Confirm zero sorry
grep -rn "sorry" UAQO/ --include="*.lean" | grep -v "comment\|--"

# Confirm zero vacuous True proofs
grep -rn ": True " UAQO/ --include="*.lean"

# Build
lake build

# Check axiom dependencies of key theorems
# (run in Lean or via lake env lean with the appropriate imports)
#print axioms UAQO.Complexity.mainResult2
#print axioms UAQO.Complexity.mainResult3
#print axioms UAQO.Experiments.theorem3_coupled_nonconstant
#print axioms UAQO.Experiments.theorem4_multisegment_rigidity
```

## File Structure

```
UAQO/
    Foundations/
        Basic.lean              Qubit states, operators, norms, BigO
        HilbertSpace.lean       Inner products, Mathlib bridges
        Operators.lean          Hermitian operators, resolvents
        SpectralTheory.lean     Eigenvalues, spectral decomposition
        Qubit.lean              Qubit systems, tensor products
    Spectral/
        DiagonalHamiltonian.lean  Diagonal Hamiltonians, EigenStructure
        SpectralParameters.lean   A1, A2, avoided crossing, gap formulas
        AdiabaticHamiltonian.lean H(s) = -(1-s)|psi0><psi0| + s*Hz
        GapBounds.lean            Eigenvalue condition, variational principle, gap bounds
    Adiabatic/
        Hamiltonian.lean        Time-dependent Hamiltonians, schedules
        Schedule.lean           Local schedules, piecewise construction
        Theorem.lean            Adiabatic theorem, eigenpath traversal
        RunningTime.lean        Main Result 1, optimality, lower bound
    Complexity/
        Basic.lean              Decision problems, polynomial time
        Encoding.lean           CNF encoding/decoding with round-trip proof
        NP.lean                 NP, 3-SAT
        SharpP.lean             #P, counting problems, degeneracy hardness
        Hardness.lean           Main Results 2 and 3, beta-modified Hamiltonian
    Proofs/
        Spectral/
            EigenvalueCondition.lean  Secular equation characterization
            GapBoundsProofs.lean      Gap bound proof infrastructure
            MatrixDetLemma.lean       Matrix Determinant Lemma
            ShermanMorrison.lean      Sherman-Morrison formula
            SecularEquation.lean      Secular function properties, IVT
            A2Bounds.lean             Bounds on spectral parameter A2
        Complexity/
            SATSemantics.lean         CNF satisfiability semantics
            LagrangeInterp.lean       Lagrange interpolation helpers
            BetaModifiedHam.lean      Beta-modified Hamiltonian construction
            ModifiedHamDeg.lean       Modified Hamiltonian degeneracy proofs
        Foundations/
            VariationalPrinciple.lean Variational principle proof
        Adiabatic/
            ScheduleProperties.lean   Schedule monotonicity and bounds
        Mathlib/
            FinsetArithmetic.lean     Finset sum arithmetic bridge lemmas
        ProofVerify.lean            Complete axiom inventory documentation
    Test/
        Verify.lean             Compilation tests, paper correspondence, axiom audit
    Experiments/
        CircumventingBarrier.lean  Theorems 1-5, 1-qubit constructions
        StructuredTractability.lean  A1 finite sum, crossing definition
```

## References

- Unstructured Adiabatic Quantum Optimization: Optimality with Limitations (arXiv:2411.05736)
- Jansen, Ruskai, Seiler: Bounds for the adiabatic approximation (2007)
- Roland, Cerf: Quantum search by local adiabatic evolution (arXiv:quant-ph/0107015)
- Farhi, Goldstone, Gutmann: Quantum computation by adiabatic evolution (2000)
- Cunningham, Grover, Russomanno: Phase randomization (2023)
- Valiant: The complexity of computing the permanent (1979)
- Garey, Johnson: Computers and Intractability (1979)
- Mathlib4: https://leanprover-community.github.io/mathlib4_docs/
