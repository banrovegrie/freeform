# Experiment 10: Information-Theoretic Limits -- todo.md

## Plans

### A. Completion checklist for this pass

- [x] Read required files in Experiment 10 (`main.md`, `proof.md`, Lean files, `lib/verify.py`).
- [x] Read experiment conventions (`src/experiments/README.md`, `src/experiments/CLAUDE.md`).
- [x] Read neighboring experiment overviews (`08`, `12`, `13` main files).
- [x] Add precision-aware proposition chaining Exp 07 and Exp 13 (Gap 3).
- [x] Add cross-experiment synthesis theorem integrating Exps 08, 10, 12, 13 (Gap 1).
- [x] Resolve Conjecture 5 by theorem-grade proof or counterexample.
- [x] Resolve the remaining worst-case open item with explicit assumptions (addendum layer).
- [x] Update `main.md` results/novelty/open-questions narrative to match new theorem set.
- [x] Run all numerical checks in `lib/verify.py`.
- [x] Remove Lean axioms and keep only assumption-parameterized external interfaces.
- [x] Add `main2.md` / `proof2.md` to avoid further crowding while preserving rigor.
- [x] Final consistency sweep across `proof.md`, `main.md`, `todo.md`.

### B. Chapter 9 insertion outline (capstone placement)

**Placement decision.**
Insert Experiment 10 after Chapter 9 section "The Ignorance Taxonomy" and before the chapter's final "Central Claim" paragraph.
Logical flow:
1. Exps 04/07/02/05/06 classify information-runtime tradeoffs inside AQO.
2. Ignorance Taxonomy synthesizes those AQO-internal regimes.
3. Experiment 10 asks whether that barrier is universal across models.
4. Answer: no; circuit model bypasses the AQO information barrier.

**Theorem mapping for Chapter 9 text.**
1. `proof.md` Thms 1-2 -> Chapter 9 proposition "Universal query limit and circuit achievability."
2. `proof.md` Thms 3-4 + Props 6-8 -> Chapter 9 theorem "Model separation and $A_1$-blindness."
3. `proof.md` Thms 6-7 -> Chapter 9 corollary "Bit-runtime information law inside fixed AQO."
4. `proof.md` Prop 9 -> Chapter 9 proposition "Precision-aware pre-computation bridge (Exp 13 link)."
5. `proof.md` Thm 8 -> Chapter 9 capstone theorem "Complete model comparison."
6. `proof.md` Prop 10 + Thm 9 and `proof2.md` Thm 10 -> Chapter 9 post-capstone note
   "literal continuous-time barrier conjecture is false; normalized worst-case reformulation is true."

**How the model table integrates with the Ignorance Taxonomy.**
The taxonomy table remains the intra-adiabatic layer. The new table is a super-table:
- AQO rows are imported from taxonomy levels.
- Circuit row shows an orthogonal branch with 0 spectral bits and optimal runtime.
- Exp 12 row marks structural no-go within rank-one instance-independent AQO design.
- Exp 13 rows quantify estimation complexity of the AQO information bottleneck.

**Precision bridge placement.**
Place immediately before the capstone theorem:
- First state "each missing bit doubles AQO time" (Thm 7).
- Then state "recovering those bits costs Theta(2^{n/2}) quantumly, Theta(2^n) classically" (Prop 9 + Exp 13).
- Then state full model-comparison theorem (Thm 8).


## Progress

- 2026-02-06: Imported exact references from Exp 12 Theorem 5, Exp 13 Theorems 2-5, and Exp 08 Propositions 8-12.
- 2026-02-06: Added `proof.md` Part VIII proposition on quantum pre-computation tradeoff (Gap 3).
- 2026-02-06: Added `proof.md` Part IX constant-control rank-one counterexample (Proposition 10) and theorem-level refutation of literal Conjecture 5 (Theorem 9).
- 2026-02-06: Added `proof.md` Part X "Complete Model Comparison Theorem" with scope and cross-experiment table (Gap 1).
- 2026-02-06: Extended `lib/verify.py` with Test 6 for precision-aware quantum/classical pre-computation scaling.
- 2026-02-06: Extended `lib/verify.py` with Test 7 for Part IX continuous-time rank-one counterexample scaling.
- 2026-02-06: Chapter 9 insertion outline finalized in this file (Gap 4).
- 2026-02-06: Updated `main.md` (results table, novelty assessment, open questions, and cross-experiment synthesis framing).
- 2026-02-06: Ran `python3 src/experiments/10_information_theoretic/lib/verify.py`; all seven tests passed.
- 2026-02-06: Added Lean statements for precision-aware runtime composition in `lean/InformationTheoretic/Basic.lean` and exported checks in `lean/InformationTheoretic.lean`.
- 2026-02-06: Replaced `axiom` declarations for BBBV/Durr-Hoyer with assumption-parameterized `Prop` interfaces in Lean and updated theorem signatures accordingly.
- 2026-02-06: Completed full Lean workspace build from `src/experiments/` via `lake build InformationTheoretic` (3079-3084 jobs depending on cache state), including successful typechecking of the new lemmas.
- 2026-02-06: Re-ran `lake build InformationTheoretic` after cache warmup; build replayed cleanly and confirmed stable incremental state.
- 2026-02-06: Ran direct check `lake env lean 10_information_theoretic/lean/InformationTheoretic.lean`; all `#check` declarations printed with no errors.
- 2026-02-06: Re-ran `python3 src/experiments/10_information_theoretic/lib/verify.py` after Lean refactor and Part IX update; all seven numerical tests still pass.
- 2026-02-06: Tightened Lean external-bound interfaces to be runtime-parameterized (`N, d_0, T`) to avoid vacuous/unsatisfiable universal quantification over `T : Real`.
- 2026-02-06: Re-ran full Lean build and direct Lean file check after interface tightening; both succeed.
- 2026-02-06: Re-ran full numerical suite after all document and Lean updates; all seven tests pass again.
- 2026-02-07: Added `proof2.md` with Theorem 10 (normalized worst-case lower bound) and Proposition 11 (normalization necessity), plus `main2.md` summary.
- 2026-02-07: Added cross-references from `main.md` / `proof.md` to the addendum files.
- 2026-02-07: Added README convention note for optional `main2.md` / `proof2.md` continuation files.
- 2026-02-07: Extended `lib/verify.py` with Test 8 for normalized worst-case scaling specialization.
- 2026-02-07: Added Lean identity `normalized_lower_bound_specialization` to support the addendum scaling specialization.
- 2026-02-07: Re-ran full verification after addendum integration (`lake build`, direct `lake env lean`, and `verify.py`); all checks pass.


## Findings

### New results now in Experiment 10

1. **Complete cross-experiment synthesis theorem.**
`proof.md` Part X now combines:
- Exp 10 model-separation and $A_1$-blindness results,
- Exp 12 no-go theorem for rank-one instance-independent modified Hamiltonians,
- Exp 13 tight estimation complexity at precision $2^{-n/2}$,
- Exp 08 structured tractability conditions that collapse pre-computation hardness.

2. **Precision-aware bridge from information bits to runtime.**
`proof.md` Proposition 9 now states:
- Quantum estimate-$A_1$-then-evolve pipeline runs in $O(2^{n/2} p(n))$.
- Classical estimate-$A_1$-then-evolve needs $\Omega(2^n)$ in worst case.
- The estimation gap equals the model gap scale.

3. **Conjecture 5 resolved at statement level.**
`proof.md` Part IX now includes:
- Proposition 10: explicit continuous-time rank-one constant-control protocol on
  $H_z=\mathbb{I}-P_0$ with exact success formula and
  $T=\Theta(\sqrt{N/d_0})$.
- Theorem 9: literal Conjecture 5 is false.
- Updated obstruction remark for the remaining worst-case formulation.

4. **Worst-case open item resolved under explicit normalization.**
`proof2.md` proves:
- Proposition 11: unnormalized physical-time lower bounds are ill-posed by time-rescaling.
- Theorem 10: with normalized controls ($|g(t)|\le 1$), worst-case runtime on the scaled
  unstructured family satisfies
  $T=\Omega(\sqrt{N/d_0}/\delta)$, and with $\delta=N^{-1/2}$ gives
  $T=\Omega(N/\sqrt{d_0})$.

### Open threads that remain

1. Characterize equivalent lower-bound formulations for unbounded controls in terms of
   oracle action budgets rather than raw time.
2. Tight lower bounds for classical communication complexity (not only query complexity) remain open.
3. Scope extension beyond ground-state finding (energy estimation/spectrum tasks) is outside this experiment's theorem scope.
