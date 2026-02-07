# Experiment 13: Intermediate Hardness -- todo.md

## Plans

### Gap 1: Precision Landscape
- [x] Add a precision phase diagram proposition covering:
  - $\epsilon = \Theta(1)$
  - $\epsilon = 1/\mathrm{poly}(n)$
  - $\epsilon = 2^{-cn}$ for $c < 1/2$
  - $\epsilon = 2^{-n/2}$
  - $\epsilon = 2^{-cn}$ for $c > 1/2$
  - $\epsilon = 2^{-\mathrm{poly}(n)}$
- [x] Add figure-like summary table in `proof.md`.
- [x] Chain existing theorems (paper Thms 2-3, Exp13 Thms 1-7) without re-deriving.

### Gap 2: Structured Instance Investigation (Exp 08 Link)
- [x] State whether Theorem 7 transfers to structured families.
- [x] Characterize bounded-treewidth complexity at $2^{-n/2}$.
- [x] Characterize ferromagnetic Ising with consistent fields at $2^{-n/2}$.
- [x] State precise condition for when Exp 08 tractability extends to schedule-level precision.

### Gap 3: Promise-Class Characterization
- [x] Add parameterized promise-time proposition for $\mathrm{A1\mbox{-}EST}_\epsilon$.
- [x] Explain why PromiseBQP-type polynomial-time behavior does not capture $\epsilon = 2^{-n/2}$ in the query model.
- [x] Document class mismatch honestly as an unresolved completeness question.

### Gap 4: Chapter 9 Integration
- [x] Read Chapter 9 structure in `README.md` (Ignorance Taxonomy, Central Claim).
- [x] Add concrete insertion outline to `main.md`.
- [x] Position Experiment 13 as bridge between hardness and information-cost narrative.

### Verification and Consistency
- [x] Extend `lib/verify.py` with precision-landscape scaling checks.
- [x] Run `lib/verify.py` and `lib/deep_verify.py` after edits.
- [x] Add and run stress suite `lib/robust_verify.py`.
- [x] Final notation/style consistency pass.

### Lean Hardening
- [x] Create `lean/` package for Experiment 13.
- [x] Formalize discrete scaling core for Propositions 8-10.
- [x] Add finite schedule-barrier certificate module.
- [x] Run Lean build and top-level check.

### Absolute Formalization Extension (Ongoing)
- [ ] Fully formalize Theorem-1 interpolation barrier (all-parameter inequality chain, not only discrete certificates).
- [ ] Formalize theorem-chain composition from paper Theorems 2-3 and Exp13 Theorems 1-7 in Lean (beyond narrative citation).
- [ ] Formalize approximate-counting lower-bound core used in Theorem 4 (query lower bound side) with explicit constants.
- [ ] Formalize ETH-conditional computational reduction details used in Theorem 5.


## Progress

- Read all required files:
  - `CLAUDE.md`
  - `src/experiments/README.md`
  - `src/experiments/CLAUDE.md`
  - `src/experiments/13_intermediate_hardness/main.md`
  - `src/experiments/13_intermediate_hardness/proof.md`
  - `src/experiments/13_intermediate_hardness/lib/verify.py`
  - `src/experiments/13_intermediate_hardness/lib/deep_verify.py`
  - `src/experiments/08_structured_tractability_v2/main.md`
  - `src/experiments/10_information_theoretic/main.md`
  - `src/experiments/12_circumventing_barrier/main.md`
- Added to `proof.md`:
  - Proposition 8: Precision phase diagram with complexity table and proof.
  - Proposition 9: Structured-family bridge to Experiment 08.
  - Proposition 10: Promise-time characterization and class mismatch remark.
- Updated `main.md`:
  - Added new proposition summaries.
  - Added precision-dependent complexity table.
  - Updated open questions to reflect resolved/remaining points.
  - Expanded cross-experiment connections (08, 10, 12, 05, 04).
  - Added Chapter 9 insertion outline aligned with README structure.
  - Updated status section to include new completed contributions.
  - Tightened Proposition 9 wording to use Exp 08 parameter constraints
    ($\mu$, $K$) instead of an unstated runtime lower-bound assumption.
- Updated `lib/verify.py`:
  - Added `verify_precision_phase_diagram()`.
  - Added exponent and smooth-scaling checks across $\epsilon$ regimes.
- Verification runs completed:
  - `python3 src/experiments/13_intermediate_hardness/lib/verify.py` (all checks passed)
  - `python3 src/experiments/13_intermediate_hardness/lib/deep_verify.py` (all checks passed)
  - `python3 src/experiments/13_intermediate_hardness/lib/robust_verify.py` (all stress checks passed, including exhaustive barrier checks on 2572 small-parameter instances)
- Lean verification completed:
  - `cd src/experiments/13_intermediate_hardness/lean && lake build` (build success)
  - `cd src/experiments/13_intermediate_hardness/lean && lake env lean IntermediateHardness.lean` (all declarations checked)
  - Added extra phase-diagram hardening lemmas:
    `q_next_doubles`, `sep_next_doubles`.
  - Added symbolic schedule-barrier inequality proof:
    `scheduleErrorProxy_gt_half`.
  - Added barrier-grid finite certificate:
    `barrierAllUpTo_1024`.
- Added "Absolute Formalization Extension" checklist to track remaining proof-assistant work required for end-to-end machine-checked certainty.


## Findings

### 1. Precision landscape is now explicit
- Query-complexity core law is continuous in precision:
  - Quantum: $\Theta(1/\epsilon)$
  - Classical: $\Theta(1/\epsilon^2)$
- At $\epsilon = 2^{-n/2}$ this specializes to:
  - Quantum: $\Theta(2^{n/2})$
  - Classical: $\Theta(2^n)$
- The structural boundary at $2^{-n/2}$ is a proof-technique boundary (interpolation fails), not a discontinuity in the core query law.
- For $\epsilon = 2^{-cn}$ with $c>1/2$, the query law is explicit, while #P-hardness is tied to whether $cn$ reaches the paper's interpolation threshold polynomial.

### 2. Theorem 7 is worst-case, not family-preserving
- Theorem 7 does not automatically impose hardness inside restricted structured families from Experiment 08.
- Bounded treewidth gives exact polynomial-time computation of $A_1$ for $w=O(\log n)$ (in particular constant width), so schedule precision is tractable there.
- Ferromagnetic Ising bridge (Exp 08, Prop 13) requires $\mu \le \eta/(6B)$; at $\eta=2^{-n/2}$ this forces $1/\mu = \Omega(B2^{n/2})$, so under standard per-query $\mathrm{poly}(n,1/\mu,\log(1/\delta))$ dependence the induced method is not polynomial-time in $n$.

### 3. Promise-class status is clarified but incomplete
- Best current statement is parameterized:
  - $\mathrm{A1\mbox{-}EST}_\epsilon \in \mathrm{FBQTIME}(\sqrt{N} + 1/(\epsilon\Delta_1)\cdot\mathrm{poly}(n))$.
- At $\epsilon=2^{-n/2}$ this gives $\mathrm{FBQTIME}(2^{n/2}\mathrm{poly}(n))$, which is beyond PromiseBQP-type polynomial-time behavior in the query model.
- No natural completeness theorem is established yet for this precision regime.

### 4. Chapter 9 placement is now concrete
- Placement: between "The Ignorance Taxonomy" and "Central Claim" in Chapter 9.
- Role: quantitative bridge from hardness claims to explicit information-cost scaling at schedule precision.
- Supporting box: structured-family caveat (Exp 08) to avoid over-generalizing worst-case hardness.

### 5. Remaining execution items
- Absolute machine-checked end-to-end formalization is not complete yet.
- Discrete/core statements are formalized; full reduction-level formalization remains.

### 6. Lean formalization status
- Added a self-contained Lean package in `src/experiments/13_intermediate_hardness/lean/`.
- Formalized discrete core statements that back Propositions 8-10.
- Added symbolic barrier inequality on the precision grid (all exponents).
- Added finite barrier certificate `barrierAllUpTo_1024` for schedule-proxy inequality.
- Current scope is the algebraic/query-scaling skeleton on the precision grid; it does not yet encode the full paper reductions or ETH assumptions.
