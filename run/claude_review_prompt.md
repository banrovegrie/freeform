Hi Claude, I need a complete holistic review of my thesis chapters 5–8. These chapters form the core technical arc of a master's thesis on adiabatic quantum optimization, based on published paper arXiv:2411.05736.

The chapters are:
- @src/chapters/chapter5.tex — Adiabatic Quantum Optimization
- @src/chapters/chapter6.tex — Spectral Analysis
- @src/chapters/chapter7.tex — Optimal Schedule
- @src/chapters/chapter8.tex — Hardness of Optimality

The source of truth is @paper/v3-quantum.tex. The thesis must exceed the paper in every dimension: exposition depth, motivation, accessibility, and narrative.

## Review Infrastructure

Read these test specifications first — they define the review criteria:
- @src/tests/agent-reviewer.md (peer review: technical soundness, presentation, originality, significance, literature, reproducibility)
- @src/tests/check-math.md (math correctness, notation consistency, hallucination detection)
- @src/tests/check-taste.md (prose quality: scaffolding, filler, vague claims, fake intuition, depth, structural coherence)
- @src/tests/agent-writer.md (voice, rhythm, lexical tells, intellectual engagement, intellectual history)
- @src/tests/check-format.md (ASCII, delimiters, LaTeX basics)
- @CLAUDE.md (thesis guidelines)

## Phase 1: Per-Chapter Deep Review (use subagents in parallel)

Spawn four parallel subagents, one per chapter. Each subagent must:

1. Read the full chapter file
2. Read the corresponding sections of paper/v3-quantum.tex (the paper is structured as: Sections 1-2 = setup → ch5, Section 3 = spectral analysis → ch6, Section 4 = optimal schedule → ch7, Section 5 = hardness → ch8, plus Appendices)
3. Read the test specifications listed above
4. Run ALL FIVE tests against the chapter:
   a. **agent-reviewer.md** — Full peer review with scores for all 6 dimensions. For paper-related content, do line-by-line formula verification against paper/v3-quantum.tex
   b. **check-math.md** — Verify every theorem statement, every bound, every constant against the paper. Flag hallucinated math. Check notation consistency using the reference table in check-math.md
   c. **check-taste.md** — Check all 15 failure modes. Pay special attention to #14 (insufficient depth vs. paper) and #11 (fake intuition). For each section, apply the floor test: is the thesis thinner than the paper anywhere?
   d. **agent-writer.md** — Full 5-pass humanization check. Does the writing have a discernible author? Check rhythm, lexical tells, intellectual engagement, intellectual history
   e. **check-format.md** — ASCII compliance, delimiter balance, LaTeX issues

5. For each chapter, also evaluate:
- Does the chapter opening build tension and motivation before formalism?
- Does ev produce output in this format:

```
## Chapter X: [Title]

### Executive Summary
Assessment: [Strong Accept / Accept / Weak Accept / Borderline / Weak Reject / Reject]
One-sentence justification.

### Scores (from agent-reviewer.md)
| Dimension | Score /10 | Notes |
|-----------|-----------|-------|
| Technical Soundness | | |
| Presentation Quality | | |
| Significance | | |
| Literature & Context | | |
| Reproducibility | | |

### Paper Comparison
- What the thesis adds beyond the paper: [list]
- What the paper has that the thesis lacks: [list]
- Formula/bound deviations found: [list with line numbers]

### Baseline Comparison
- vs. de Wolf: [assessment]
- vs. Zeeshan: [assessment]

### Math Check (check-math.md)
[PASS/WARN/FAIL with specific line references]

### Taste Check (check-taste.md)
[PASS/WARN/FAIL with specific line references and failure mode IDs]

### Writer Check (agent-writer.md)
[PASS/WARN/FAIL with specific line references]

### Format Check (check-format.md)
[PASS/WARN/FAIL with speA_p, A_1, A_2 defined in ch5, used consistently in ch6-8
   - g(s), g_min, s*, delta_s same meaning everywhere
   - H(s), H_0, H_z, H_P naming conventions
   - varepsilon (never epsilon)
   - Theorem/lemma numbering and cross-references

3. **No Redundant Definitions**: Check that no concept is defined twice across chapters. Common risks: Hermitian, unitary, spectral gap, eigenvalue decomposition.

4. **Depth Gradient**: The exposition should deepen across the arc. Ch5 should be the most accessible (setting up the problem for a newcomer). Ch8 should be the most technical (hardness proofs). Check that this gradient exists.

5. **The Paper is a Subset**: Verify that every section of paper/v3-quantum.tex relevant to chapters 5-8 is covered in the thesis, and the thesis adds substantial value (more motivation, more intuition, fuller derivations, better examples) everywhere. Flag any place where the paper provides more detail than the thesis.

6. **Personal Voice**: Across all four chapters, are there enough mom(ordered by severity)
1. ...

## Significant Issues (ordered by priority)
1. ...

## Comparison to Baselines
- vs. the paper: [is the thesis genuinely better as exposition?]
- vs. de Wolf: [writing quality comparison]
- vs. Zeeshan: [writing quality comparison]
- vs. Aaronson papers: [intellectual engagement comparison]

## Specific Recommendations
[Top 5 highest-impact changes]

## Overall Scores
| Criterion | Score | Notes |
|-----------|-------|-------|
| Story consistency across chapters | /10 | |
| Elaboration beyond paper | /10 | |
| Exposition and writing quality | /10 | |
| Development, presentation, journey | /10 | |
| Math correctness and notation | /10 | |
| Depth, motivation, accessibility | /10 | |
| Better than baselines | /10 | |
| Personal voice and authenticity | /10 | |
```
