# Task Plan: Write Introduction and Conclusion Chapters

## Goal
Write first drafts of `src/chapters/introduction.tex` (Chapter 1) and `src/chapters/conclusion.tex` (Chapter 10/Conclusion) that bind the entire thesis into a unified, deeply motivated work. These must exceed the paper's introduction and discussion in depth, accessibility, and motivation. They must read as if written by someone deeply immersed in the subject.

## Status: `complete`

## Context

### Thesis Structure (Chapters 2-9 + Appendix complete)
- Ch 2: Physics and Computation (classical mechanics, complexity, optimization encoding, adiabatic heuristic)
- Ch 3: Quantum Computation (qubits, circuits, BQP, Grover's algorithm, BBBV lower bound)
- Ch 4: Adiabatic Quantum Computation (AQC model, adiabatic theorem, Roland-Cerf benchmark)
- Ch 5: Adiabatic Quantum Optimization (cost-to-Hamiltonian, symmetric subspace, spectral parameters A_p, crossing position, gap approximation)
- Ch 6: Spectral Analysis (left gap bound via variational, right gap bound via resolvent, complete piecewise profile)
- Ch 7: Optimal Schedule (adaptive schedule, runtime T = O-tilde(sqrt(N/d_0)))
- Ch 8: Hardness of Optimality (NP-hardness of A_1 at 1/poly, #P-hardness at exact, interpolation barrier, quantum algorithm, classical lower bound, quadratic separation)
- Ch 9: Information Gap (ORIGINAL CONTRIBUTIONS: separation theorem, interpolation theorem, hedging theorem, quantum bypass, gap geometry, no-go theorems, computational nature of A_1, partition function connections, tractability results)
- Appendix: Formalization (Lean 4, 330 theorems, 15 axioms, zero sorry)

### Central Narrative Arc
The thesis asks: can AQO match Grover's quadratic speedup for optimization? Yes -- but at an ironic cost. The optimal schedule requires computing A_1, which is NP-hard. The information gap is intrinsic to the computational model, not the computational task. Chapter 9 extends this into a complete taxonomy of the information cost and proves that no instance-independent modification within the rank-one framework can eliminate the spectrum dependence.

### Key Style Requirements
- No filler, no signaling, no hedging where commitment is warranted
- Build tension before definitions; reader should want the concept before it arrives
- Transitions carry argument, not navigation
- Show authorial voice like Penrose -- curious, warm, not arrogant
- Every sentence carries information
- Exceed Aaronson's intro/conclusion in rigor while matching its motivational clarity

## Phases

### Phase 1: Introduction Chapter Spine Design — `in_progress`
Identify the 4-5 questions the introduction must answer, in order.

**Spine:**
1. What is the thesis about? (The tension between computational models and physical optimization)
2. Why does it matter? (AQO is physically motivated, experimentally deployed, polynomially equivalent to circuits -- but provable guarantees are absent)
3. What does the thesis prove? (Optimality with limitations -- the information gap)
4. What is new beyond the paper? (Chapter 9 contributions, formalization)
5. How does the thesis unfold? (Chapter map as inevitable narrative, not arbitrary enumeration)

### Phase 2: Introduction Chapter Draft — `pending`
Write the full introduction.tex content.

**Structure plan:**
- Opening (1-2 paragraphs): Hook through the tension between knowing the answer exists and finding it. The Hamiltonian encodes the solution but does not reveal it. The circuit model has Grover. Does the adiabatic model?
- Section 1: The Adiabatic Idea (~2-3 paragraphs): AQC as physically motivated alternative, universality, the gap-controlled runtime. Not definitions -- motivation. Why this model exists and what it promises.
- Section 2: The Question (~2-3 paragraphs): Can AQO match Grover for general optimization? Why this is non-obvious. The spectrum is richer than the Grover case. Prior partial results (Znidaric-Horvat, Hen). The lower bound of Farhi et al.
- Section 3: The Answer and Its Cost (~3-4 paragraphs): Yes, with optimal schedule. But the schedule needs A_1 to exponential precision. NP-hard to approximate, #P-hard exactly. The information gap. This cost is absent from the circuit model.
- Section 4: Beyond the Paper (~2-3 paragraphs): Chapter 9 contributions -- the information gap has precise mathematical structure. No-go theorems. Gap geometry. Quantum bypass. Partition function connections. Formalization.
- Section 5: Thesis Overview (~4-5 paragraphs): Chapter-by-chapter map as narrative flow. Each chapter answers a question the previous one left open.

### Phase 3: Conclusion Chapter Spine Design — `pending`
Identify what the conclusion must accomplish.

**Spine:**
1. What did the reader gain? (Restate the arc in one paragraph -- not repetition, synthesis)
2. What is achieved precisely? (Sharp theorem statements with honest scope)
3. What remains open? (Concrete open problems, not vague gestures)
4. What does it mean? (Connection to broader landscape -- AQC-circuit equivalence, the role of structure, the information gap as a general phenomenon)

### Phase 4: Conclusion Chapter Draft — `pending`
Write the full conclusion.tex content.

**Structure plan:**
- Opening (1-2 paragraphs): Synthesis paragraph. The thesis asked whether AQO can match Grover. The answer is yes, with a sharp caveat. The caveat has structure.
- Section 1: What Is Proved (~3-4 paragraphs): Technical summary without re-proving. Gap bounds, optimal runtime, hardness ladder (NP to #P), information gap taxonomy, no-go theorems, formalization. Explicit bounds and honest limitations.
- Section 2: Open Problems (~4-6 paragraphs): Each open problem gets motivation, current state, and what would constitute progress.
  - Can intermediate Hamiltonians or ancillas circumvent the hardness? (Ch 9 narrows possibilities)
  - Precise complexity of A_1 at 2^{-n/2} precision
  - Local-driver AQO (H_0 = sum sigma_x^j) -- the standard setting
  - Gap geometry beyond rank-one
  - Structured tractability results
  - Non-adiabatic continuous-time algorithms sharing the same bottleneck
- Section 3: The Broader Picture (~2-3 paragraphs): What the information gap tells us about quantum optimization more generally. The pattern: algorithm design creates information requirements absent from the problem specification. Connect to variational algorithms, quantum annealing schedules, and the emerging theory of adiabatic schedule design. End with what remains to be understood.

### Phase 5: Review and Consistency — `pending`
- Check all cross-references to existing chapters
- Verify all cited references exist in references.bib
- Check notation consistency with chapters 2-9
- Verify no re-definitions of terms defined in earlier chapters
- Run the teaching test: could a graduate student new to AQO follow the introduction?
- Run the floor test: does the intro exceed the paper's introduction on every point it covers?

## Decisions
- Introduction has NO subsections (per CLAUDE.md: "Not a lot of subsections. Chapters and sections best."). Use sections only.
- Conclusion has sections for Open Problems and Broader Picture.
- Introduction opens with tension, not definitions.
- Chapter map in introduction uses implicit transitions (each chapter's question arises from the previous chapter's answer), not a numbered list.
- No abstract written in this task (separate task).

## Files to Create/Modify
- `src/chapters/introduction.tex` — full first draft
- `src/chapters/conclusion.tex` — full first draft
- `findings.md` — track style decisions and cross-reference checks
- `progress.md` — session log
