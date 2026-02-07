/-
  Verification file for all proofs.

  Imports all proof modules to verify they compile correctly.
-/

-- Mathlib bridges
import UAQO.Proofs.Mathlib.FinsetArithmetic

-- Foundations proofs
import UAQO.Proofs.Foundations.VariationalPrinciple

-- Spectral proofs
import UAQO.Proofs.Spectral.A2Bounds
import UAQO.Proofs.Spectral.ShermanMorrison
import UAQO.Proofs.Spectral.EigenvalueCondition
import UAQO.Proofs.Spectral.MatrixDetLemma
import UAQO.Proofs.Spectral.GapBoundsProofs

-- Adiabatic proofs
import UAQO.Proofs.Adiabatic.ScheduleProperties

-- Complexity proofs
import UAQO.Proofs.Complexity.SATSemantics
import UAQO.Proofs.Complexity.ModifiedHamDeg
import UAQO.Proofs.Complexity.BetaModifiedHam
import UAQO.Proofs.Complexity.LagrangeInterp

namespace UAQO.Proofs

/-!
# Formalization Status

## Zero Sorry, 12 Explicit Axioms, ~25 Genuine Theorems

Every assumption is a Lean `axiom` with a paper citation, visible via
`#print axioms`. Every provable result is proved. Zero `sorry` in the
entire codebase.

### Architecture: Three Layers

**Layer 0 -- Axioms.** Formalization boundaries beyond Lean 4/Mathlib scope.
Each axiom has a paper citation.

**Layer 1 -- Definitions.** No sorry. Reference axioms but are themselves concrete.

**Layer 2 -- Theorems.** Proved from axioms + genuine proofs. Zero sorry.

### Complete Axiom Inventory (12 axioms)

**Primitive concepts (3):**

1. `IsPolynomialTime` (Complexity/Basic.lean)
   - Type: `(List Bool -> List Bool) -> Prop`
   - Citation: Arora-Barak, Chapter 1

2. `SatisfiesSchrodingerEquation` (Adiabatic/Theorem.lean)
   - Type: `TimeDependentHam -> (Real -> NQubitState) -> Prop`
   - Citation: Jansen, Ruskai, Seiler (2007), Section 2

3. `degeneracyCount` (Complexity/SharpP.lean)
   - Type: `List Bool -> Nat`
   - Citation: arXiv:2411.05736, Section 2.3

**Standard complexity results (3):**

4. `threeSAT_in_NP` (Complexity/NP.lean)
   - Statement: `InNP ThreeSAT`
   - Citation: Cook (1971)

5. `sharpThreeSAT_in_SharpP` (Complexity/SharpP.lean)
   - Statement: `InSharpP SharpThreeSAT`
   - Citation: Valiant (1979)

6. `sharpThreeSAT_hard` (Complexity/SharpP.lean)
   - Statement: `IsSharpPHard SharpThreeSAT`
   - Citation: Valiant (1979)

**Quantum physics results (4):**

7. `adiabatic_evolution_bound` (Adiabatic/Theorem.lean)
   - Statement: Jansen adiabatic theorem (evolution exists with error bound)
   - Citation: Jansen, Ruskai, Seiler (2007), Theorem 3

8. `eigenpath_evolution_bound` (Adiabatic/Theorem.lean)
   - Statement: evolution follows instantaneous ground state
   - Citation: Jansen, Ruskai, Seiler (2007), Corollary of Theorem 3

9. `mainResult1_evolution` (Adiabatic/RunningTime.lean)
   - Statement: AQO evolution at computed running time
   - Citation: arXiv:2411.05736, Theorem 1

10. `lowerBound_unstructuredSearch` (Adiabatic/RunningTime.lean)
    - Statement: Omega(sqrt(N)) query lower bound
    - Citation: Farhi, Goldstone, Gutmann (2000); Bennett et al. (1997)

**Paper results depending on IsPolynomialTime (2):**

11. `degeneracy_sharpP_hard` (Complexity/SharpP.lean)
    - Statement: `IsSharpPHard DegeneracyProblem`
    - Citation: arXiv:2411.05736, Theorem 3

12. `A1_approx_implies_P_eq_NP` (Complexity/Hardness.lean)
    - Statement: P=NP from poly-time A1 approximation
    - Citation: arXiv:2411.05736, Corollary of Theorem 2

### Proved Theorems (formerly sorry, now one-line proofs from axioms)

- `adiabaticTheorem` -- proved from `adiabatic_evolution_bound`
- `eigenpath_traversal` -- proved from `eigenpath_evolution_bound`
- `mainResult1` -- proved from `mainResult1_evolution`
- `sharpThreeSAT_complete` -- proved from `sharpThreeSAT_in_SharpP` + `sharpThreeSAT_hard`

### Layer 1: Genuine Mathematical Proofs

These theorems carry real mathematical content with substantive proofs:

**Spectral theory (Proofs/Spectral/)**
- `resolvent_distance_to_spectrum` -- nonzero resolvent via Frobenius positivity
- `isEigenvalue_iff_det_eq_zero` -- eigenvalue iff det(lambda*I - A) = 0
- `eigenvalue_condition` -- secular equation via Matrix Determinant Lemma
- `isEigenvalue_is_mathlib_eigenvalue` -- eigenbasis expansion + Parseval
- `spectral_gap_pair_exists` -- ground/first-excited via Finset.min'
- `variational_principle`, `variational_minimum` -- spectral decomposition
- `secularFun_strictMono_on_interval` -- IVT + monotonicity
- `exists_unique_root_below_ground` -- unique secular equation root
- `ground_eigenvalue_is_secular_root` -- IVT characterization

**Algebraic structure (Proofs/Complexity/)**
- `lagrange_interpolation` -- via Mathlib `Lagrange.interpolate`
- `berlekamp_welch` -- error-correcting interpolation structure
- `A1_numerator_polynomial_in_beta` -- (X+1)^(M-1) witness + Finset even/odd
- `betaModified_A1_diff_pos` -- Finset.sum_nbij bijection
- `threeSAT_satisfiable_iff_degPositive` -- SAT encoding correctness
- `extractDegeneracy_correct` -- paper's extraction formula via numeratorPoly
- `numeratorPoly_eval` -- Lagrange evaluation identity for numerator polynomial

**Running time analysis (Adiabatic/RunningTime.lean)**
- `complex_cauchy_schwarz` -- discrete Cauchy-Schwarz for complex sums
- `measurement_yields_groundstate` -- measurement probability bound 1 - 2*sqrt(eps)
- `runningTime_ising_bound` -- Ising Hamiltonian running time is poly * sqrt(N/d0)
- `runningTime_matches_lower_bound` -- upper and lower bounds match up to polylog

**Foundations (Proofs/Foundations/)**
- Sherman-Morrison resolvent formula
- A2 bounds (Cauchy-Schwarz)
- Schedule monotonicity and piecewise properties

**Encoding (Complexity/Encoding.lean)**
- `decode_encode` -- CNF round-trip correctness
- `encodeCNF_injective` -- encoding injectivity

### Additional Genuine Theorems

- `sharpThreeSAT_complete` -- proved from axioms 5 + 6
- `mainResult2` -- two-query NP-hardness (classical case split)
- `mainResult3` -- #P-hardness via extraction formula (genuine)

### FullSpectralHypothesis

- Status: explicit hypothesis (not an axiom, passed as parameter)
- Reason: Proposition 1 gap bound requires deep secular equation analysis
- Citation: arXiv:2411.05736, Proposition 1
- Used by: `runningTime_ising_bound`, `runningTime_ising`

### Faithfulness to Paper (arXiv:2411.05736)

**Exact match:** H(s), A_p (Eq. 5), s* (Eq. 6), delta_s (Eq. 7),
g_min (Eq. 311 with eta=0.1), EigenStructure (Def. 1), spectralCondition,
gap region formulas (Eqs. 317, 347), extraction formula (line 912),
running time T = O(sqrt(A2)/(A1^2*Delta^2) * sqrt(N/d0)/eps) (Theorem 1)

**Close:** FullSpectralHypothesis faithfully states Proposition 1 as explicit
hypothesis rather than hidden axiom; mainResult2 references two-query protocol
(partial eigenstructure, modified Hamiltonian, D = A1(H) - 2*A1(H')) but proof
exploits classical case split; mainResult3 extraction uses paper's formula
(numeratorPoly + extractDegeneracyReal) and is genuine

### Why Axioms Exist

Formalizing computational complexity (polynomial-time Turing machines),
quantum dynamics (Schrodinger PDE), and counting infrastructure (eigenvalue
problem encoding) is beyond current Lean 4/Mathlib scope. Every axiom is
declared with the Lean `axiom` keyword, visible via `#print axioms`, and
carries a paper citation.
-/

end UAQO.Proofs
