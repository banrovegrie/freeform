# Experiment 12: Circumventing the Barrier - todo.md

## Plans

### 1. Higher-rank investigation (Gap 1)
- [x] Derive the rank-k secular determinant
  - Target: $\det(I_k - (1-s)U^\dagger(sH_z-\lambda I)^{-1}U)=0$.
- [x] Specialize to rank-2 projector $P = |\psi_0\rangle\langle\psi_0| + |\phi\rangle\langle\phi|$
  - Target: explicit 2x2 reduced equation and crossing proxy at $\lambda=sE_0$.
- [x] Resolve outcome honestly
  - Outcome obtained: negative result on fixed-degeneracy two-level families.
  - New result in `proof.md`: Proposition 6.
  - Generalized reduced rank-k scaling law in `proof.md`: Proposition 6A.
  - Commuting multilevel extension in `proof.md`: Proposition 6B.
  - General noncommuting multilevel trace no-go in `proof.md`: Proposition 6C.
- [x] Add numerics for higher-rank analysis in `lib/ancilla_spectrum.py`

### 2. Cross-experiment synthesis (Gap 3)
- [x] Pull exact theorem/proposition hooks from neighboring experiments
  - Exp 05 Theorem 1
  - Exp 10 Theorem 2
  - Exp 13 Theorem 2
  - Exp 08 Propositions 8, 9, 13
- [x] Add a formal circumvention landscape proposition in `proof.md`
  - New result: Proposition 7 (CAN vs CANNOT list with explicit scope).

### 3. Chapter 9 integration (Gap 4)
- [x] Read Chapter 9 outline in top-level `README.md`
- [x] Produce insertion outline with theorem mapping
- [x] Sync narrative in `main.md` and this `todo.md`

### 4. Lean formalization (Gap 2)
- [x] Create experiment-local Lean project under `lean/`
- [x] Add basic definitions for spectral weights and crossing map
- [x] Encode Theorem 2 statement (universality)
- [x] Encode Theorem 5 composition form (1-4 imply 5), with component core statements
- [x] Build check (`lake build`)

### 5. Final consistency pass
- [x] Re-read `proof.md` end-to-end for numbering and notation consistency
- [x] Verify no non-ASCII remains in modified experiment files

## Progress

- 2026-02-06 (initial state)
  - Theorems 1-5 already complete in `proof.md`.
  - Escape-routes section present but higher-rank route unresolved.
  - No experiment-local Lean directory.

- 2026-02-06 (this pass)
  - Added Part VIII in `proof.md` with rank-k determinant setup and rank-2 analysis.
  - Added Proposition 6 (rank-2 obstruction on fixed-degeneracy two-level families).
  - Added Proposition 6A (rank-k two-level scaling law with excited-support condition).
  - Added Proposition 6B (commuting multilevel extension beyond two-level families).
  - Added Proposition 6C (general multilevel trace no-go without commutation).
  - Added Part IX in `proof.md` with Proposition 7 (circumvention landscape across experiments).
  - Updated `main.md` with new results, revised open questions, and explicit cross-experiment theorem links.
  - Extended `lib/ancilla_spectrum.py` with rank-2 verification suite (`verify_theorem6_rank2`).
  - Strengthened Proposition 6 numerics to test multiple two-level degeneracies (`d0=1,2,3`) and added optional deep stress mode (`--deep`).
  - Added Proposition 6A numerics (`verify_proposition6A_rankk`) for rank-4 reduced determinant scaling checks.
  - Added Proposition 6B numerics (`verify_proposition6B_commuting_multilevel`) and deep stress test (`deep_verify_proposition6B_commuting_multilevel`).
  - Created `lean/` package with:
    - `CircumventingBarrier/Basic.lean`
    - `CircumventingBarrier/Universality.lean`
    - `CircumventingBarrier/NoGo.lean`
    - `CircumventingBarrier/Rank2TwoLevel.lean`
    - `CircumventingBarrier/RankKTwoLevel.lean`
    - `CircumventingBarrier/RankKMultilevelCommuting.lean`
    - `CircumventingBarrier/RankKMultilevelTraceNoGo.lean`
    - `CircumventingBarrier/OperatorCore134.lean`
    - top-level `CircumventingBarrier.lean`
    - `README.md` (build + axiom boundary)
    - `lakefile.lean`, `lean-toolchain`
  - Lean build status: `lake build` succeeds.
  - Reduced one avoidable Lean axiom: uncoupled crossing injectivity is now proved in `NoGo.lean` for the physical regime $A_1>0$.
  - Removed the previous Theorem 2 axiom by proving the theorem-2 core in `Universality.lean` (singleton-assignment permutation form).
  - Added Lean proofs for Proposition 6A algebraic core in `RankKTwoLevel.lean` (branch rewrite and non-constancy in Delta).
  - Added Lean proofs for Proposition 6 algebraic scaling core in `Rank2TwoLevel.lean` (reduced/normalized equivalence and root scaling form).
  - Added Lean proofs for Proposition 6B algebraic core in `RankKMultilevelCommuting.lean` (single-gap profile non-constancy and multilevel split identity).
  - Added Lean proofs for Proposition 6C algebraic core in `RankKMultilevelTraceNoGo.lean` (trace-drift contradiction against root-multiset invariance).
  - Added `OperatorCore134.lean` with operator-reduction cores for Theorems 1/3/4 (product-sector invariance and reduced action equivalence; coupled asymptotic crossing non-constancy; segment-2 rigidity map).
  - Strengthened `NoGo.lean` composition packaging so `theorem5_statement` now explicitly includes Theorem 2 and Theorem 4 core statements in addition to uncoupled/coupled non-constancy.
  - Strengthened `Universality.lean` with the converse direction and `singletonInvariant_iff_uniform` characterization in the normalized regime.
  - Strengthened `NoGo.lean` again so `theorem5_statement` explicitly packages all core components (Theorems 1-4) together with uncoupled/coupled non-constancy conclusions.
  - Removed remaining Lean axioms by proving model-level core abstractions for Theorems 1/3/4 in `NoGo.lean`.
  - Installed `numpy` and executed full numerical suite end-to-end: all checks pass, including generalized Proposition 6 tests.
  - Executed deep randomized stress verification for Proposition 6 (1920 random cases): all checks pass.
  - Executed deep randomized stress verification for Proposition 6A (1296 random cases): all checks pass.
  - Hardened deep residual checks with scale-normalized metrics (rank-2 and rank-k reduced equations) to remove ill-conditioning artifacts from raw polynomial/determinant magnitudes.
  - Added a post-deep robustness sweep across seeds `1,2,3,4,5,11,13,17,19,23` for both Proposition 6 and 6A stress tests: all passes.
  - Added explicit branchwise checks of the closed-form identity $s=A_1/(A_1+\kappa(N-d_0)/N)$ in both Proposition 6 and Proposition 6A verification (standard and deep modes): all passes.

## Findings

### A. Higher-rank result (new)
- Rank-k case is governed by a matrix secular condition, not a scalar one.
- For rank-2, the reduced crossing proxy is a quadratic in $x=(1-s)/s$:
  \[
  1 - x(A_1+B_1) + x^2(A_1B_1-|C_1|^2)=0.
  \]
- On two-level family $(E_0=0, E_1=\Delta, 1 \le d_0 < N)$, each positive root has form $x(\Delta)=\kappa\Delta$, so
  \[
  s(\Delta)=\frac{1}{1+\kappa\Delta}=
  \frac{A_1}{A_1+\kappa\frac{N-d_0}{N}}.
  \]
  Therefore crossing remains spectrum-dependent for fixed instance-independent rank-2 projectors.
- Rank-k extension (Proposition 6A): with $B=U_{\mathrm{exc}}^\dagger U_{\mathrm{exc}}$, reduced roots satisfy
  \[
  \det(I_k - xB/\Delta)=0,\quad x_i(\Delta)=\Delta/\mu_i,\ \mu_i>0.
  \]
  So every excited-support branch depends nontrivially on $\Delta$ and $A_1$.
- Commuting multilevel extension (Proposition 6B): with commuting excited blocks $B_\ell$,
  \[
  \det\!\Big(I_k - x\sum_{\ell\ge 1}(E_\ell-E_0)^{-1}B_\ell\Big)=0
  \]
  decouples branchwise after simultaneous diagonalization, and any branch with support on a varied level stays spectrum-dependent.
- General noncommuting extension (Proposition 6C): if a varied level has nonzero trace weight, $\mathrm{tr}(A)$ drifts strictly with that gap, so the full positive-root multiset cannot stay invariant.
- Remaining open multilevel obstruction now narrowed to branch-level decoupling for non-commuting $B_\ell$.

### B. Circumvention landscape (new synthesis)
- CAN circumvent:
  - circuit model (Exp 10, Theorem 2),
  - adaptive measurement (Exp 05, Theorem 1),
  - quantum pre-estimation of $A_1$ (Exp 13, Theorem 2),
  - structured tractability regimes (Exp 08, Propositions 8/9/13).
- CANNOT circumvent inside fixed instance-independent Hamiltonian engineering:
  - product ancillas, non-uniform fixed initial states, fixed couplings, multi-segment rank-one paths, full rank-one class (Theorems 1-5), rank-2 on fixed-degeneracy two-level families (Proposition 6), rank-k excited-support branches on fixed-degeneracy two-level families (Proposition 6A), and commuting multilevel block families with varied supported levels (Proposition 6B).
  - also impossible: full noncommuting multilevel positive-root-set invariance under varied supported levels (Proposition 6C).

### C. Chapter 9 insertion outline
- Placement in Chapter 9 (`README.md`, "Information Gap"):
  - Insert after "Adaptive Schedules" and before "Measure Condition and Scaling".
- Narrative sequence:
  1. Exp 05: adaptive measurements recover optimal runtime.
  2. Exp 12: ask whether static Hamiltonian modification can do the same.
  3. Answer: no within fixed instance-independent rank-one design; rank-2 also obstructed on canonical family.
  4. End with cross-model circumvention landscape (Exp 05/08/10/13 + Exp 12).
- Proposition mapping:
  - Theorem 2 (universality) -> Chapter 9 subsection "Why static modifications fail".
  - Theorem 5 + Propositions 6/6A -> subsection "No-go boundary".
  - Proposition 6B -> subsection "Higher-rank multilevel extension (commuting case)".
  - Proposition 6C -> subsection "Noncommuting multilevel trace no-go".
  - Proposition 7 -> subsection "What works / what does not" (capstone synthesis).

### D. Lean status
- Current local Lean formalization is statement-heavy by design:
  - Theorem 2 core is proved in a singleton-assignment permutation form.
  - Theorem 5 is encoded as a composition theorem from component statements.
  - Proposition 6C core is encoded as a trace-drift contradiction against root-multiset invariance.
  - Theorem 1/3/4 now include operator-reduction core lemmas in `OperatorCore134.lean` in addition to composition-level encoding.
  - Current explicit axiom count in experiment-local package: 0.

### E. Residual formalization gap (for full operator-level certainty)
- Not yet formalized in Lean at full Hilbert-space/operator level:
  - tensor-product subspace decomposition proof of Theorem 1,
  - large-$\Delta$ coupled-ancilla asymptotic proof of Theorem 3,
  - full multi-segment operator-level reduction for Theorem 4.
- Current package proves algebraic/model-level cores with zero axioms; full physics-level mechanization remains future work.
