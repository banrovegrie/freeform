# Tests

Alignment tests for thesis quality control.

## The Standard

A reader should finish this thesis understanding adiabatic quantum optimization better than any other single source would give them.

- The writing should be clear enough to teach.
- Precise and rigorous enough that Shantanav finds no errors. State what results achieve and what they do not.
- Honest, personal and reflective. The goal is new perspective: understanding reality better or building practical things.

The published paper is the foundation. The thesis explains it deeply and weaves the background into a unified whole. It proposes directions beyond the paper (legitimate future work, even if unproven) and `src/experiments/` is where we try to realize them. What succeeds gets folded back into the thesis.

## Purpose

This directory contains prompts and checklists that verify consistency and correctness across the thesis. These are not unit tests in the software sense but rather structured reminders and verification procedures.

## Contents

### Notation Consistency
Verify that mathematical notation remains consistent across chapters. Common terms to check: hermitian, unitary, spectral gap, Hamiltonian, ground state, adiabatic path.

### Taste Comparisons
Compare draft sections against `taste/zeeshan_ms_thesis.md` and `taste/dewolf_phd_thesis.md` to ensure we exceed the baseline quality. Check against `taste/README.md` patterns.

### Math Verification
Prompts for cross-checking mathematical statements against the published paper in `paper/`. LLMs hallucinate notation and details invisibly. Import math directly where possible.

### Definition Tracking
Before introducing any definition, check if it already exists in earlier chapters. Maintain a running list of defined terms to prevent redundancy.

## Usage

- Run these checks before finalizing any chapter. Feed relevant test content to the LLM along with the draft section to catch errors early.
- Perform multiple passes through each chapter. Iterate till satisfied. Also, writing later chapters deepens understanding of earlier ones. Revisit as needed.
