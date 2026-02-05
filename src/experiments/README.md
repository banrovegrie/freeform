# Experiments

New ideas, explorations, and rough drafts extending the published work on adiabatic quantum optimization.


## Purpose

This directory is a staging area for content that is not yet ready for `src/chapters/`. Ideas are developed here before they mature into formal thesis sections.

The thesis is built on a single published paper (`paper/`). This directory is where we go beyond it. The paper establishes the foundation. The experiments here aim to extend that foundation with new contributions: generalizations, alternative approaches, open questions pursued further. A thesis that merely explains existing work is a report. A thesis that advances it is a contribution.


## Structure

Each experiment lives in a numbered directory `0x_name/` with standardized contents:

```
0x_experiment_name/
+-- main.md              # Overview: problem, conjectures, status, references
+-- proof.md             # Full mathematical proof (the main deliverable)
+-- lib/                 # Supporting code (Python, numerical experiments)
|   +-- *.py
|   +-- requirements.txt
+-- lean/                # Formal verification (Lean 4 + Mathlib)
|   +-- lakefile.lean
|   +-- lean-toolchain
|   +-- ExperimentName/
|       +-- Basic.lean
|       +-- *.lean
+-- notes/               # Working notes, literature, scratchpad
    +-- *.md
```

**File purposes**:
- `main.md`: Overview - problem statement, conjectures, approach, status, references. Navigable summary.
- `proof.md`: The actual work - full theorems with complete proofs. This becomes the thesis chapter.
- `lib/`: Numerical validation, computational experiments, figures
- `lean/`: End-to-end complete formal verification (optional)
- `notes/`: Literature surveys, failed attempts, scratchpad, intermediate drafts


## Guidelines

Work here is expected to be rough. The goal is exploration rather than polish. However:
- Notation should align with the published paper to ease later integration.
- Claims should be clearly labeled as CONJECTURE, THEOREM (with proof), or EMPIRICAL.
- Failed attempts are valuable and should be documented honestly.
- Literature surveys should verify novelty before deep investment.

When an experiment matures sufficiently, extract the relevant content into the appropriate chapter file and archive the experiment with a note.


## Current Experiments

### Complete

| ID | Name | Key Result |
|----|------|------------|
| 02 | robust_schedules | Hedging over $[u_L, u_R]$ achieves error ratio $(u_R - u_L)$. Constant-factor approximation with bounded uncertainty. Lean formalized. |
| 04 | separation_theorem | Gap-uninformed fixed schedules require $\Omega(2^{n/2})$ overhead. Lean formalized. |
| 05 | adaptive_schedules | Adaptive AQO with $\Theta(n)$ measurements achieves $T = O(T_{\inf})$. Circumvents classical hardness. |
| 06 | measure_condition | $T = \Theta(1/\Delta_*^{3-2/\alpha})$ where $\alpha$ is gap flatness. Dichotomy conjecture is FALSE - scaling forms a spectrum. Lean formalized. |
| 07 | partial_information | $T(\varepsilon) = T_{\inf} \cdot \Theta(\max(1, \varepsilon/\delta_{A_1}))$. Linear interpolation, no thresholds. Lean verified. |

### Proposed

| ID | Name | Open Question |
|----|------|---------------|
| 08 | structured_tractability_v2 | Are there NP-hard problems with tractable $A_1$? |
| 10 | information_theoretic | Is the adiabatic framework uniquely limited compared to circuit model? |
| 11 | schedule_optimality | Does the paper's gap profile satisfy Guo-An's measure condition? What does Guo-An's variational optimality say about the paper's schedule? |
| 12 | circumventing_barrier | Can modified Hamiltonians (ancillas, intermediate paths) make $s^*$ independent of the problem spectrum? |
| 13 | intermediate_hardness | What is the complexity of estimating $A_1$ to the algorithmically relevant precision $2^{-n/2}$? |


## Templates

### main.md (Overview)

```markdown
# [Experiment Name]

## Problem Statement
What question are we trying to answer?

## Why Novel
What existing work is related? What gap does this fill?

## Conjectures
State precise mathematical claims to prove/disprove.

## Approach
Strategy for attacking the problem.

## Status
Current state: Proposed / Exploratory / Complete

## References
Related papers and prior work.
```

### proof.md (The Work)

No template. Write the mathematics as it develops. The structure emerges from the content.

This is the main deliverable - what eventually becomes a thesis chapter.

Needs to be absolutely correct, robust and complete.

## References

These papers form the basis for all experiments:

1. Original paper (`paper/`): $A_1$ NP-hard, optimal AQO runtime $O(2^{n/2})$
2. Guo-An 2025 (`citations/`): Power-law schedules, measure condition, $p=3/2$ optimality
3. Other relevant papers (`references/`) that our original paper refers to
