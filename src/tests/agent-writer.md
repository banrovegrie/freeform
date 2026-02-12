# Writer Check

## Purpose

Verify prose quality end-to-end: argument quality, voice, taste, rhythm, precision, and reader outcome.

This file is the primary writing gate. It carries the burden of both writing quality and human presence. Use it as the canonical standard when reviewing chapters.

## Calibration Sources

Use these files as the style and quality baseline:

- `README.md` (On Writing section)
- `taste/README.md` and the papers/theses in `taste/`

Do not imitate surface style. Extract the underlying habits: clear stakes, explicit assumptions, precise claims, strong transitions, and visible intellectual judgment.

## Non-Negotiable Outcome

A section passes only if all three hold:

1. The reader can state the question the section answers and why it matters.
2. The reader can reconstruct the logic chain with explicit hypotheses.
3. The reader can do something new afterward (predict behavior, spot failure conditions, or explain tradeoffs).

If prose is correct but the reader gains no usable capability, the writing fails.

## Failure Modes

### 1. Missing Question or Stakes

The section opens with content but not purpose.

Signs:
- Cold start into notation, theorem statements, or derivations.
- No sentence explaining why the section exists now.
- Topic labels instead of claims/questions.

Tests:
- First paragraph must answer: what are we trying to resolve, and why does it matter?
- If the first paragraph can be dropped into any chapter unchanged, it fails.

### 2. Broken Narrative Spine

Sections do not build; order feels arbitrary.

Signs:
- Sections can be reordered with little damage.
- Concepts are introduced and never used.
- Results appear before dependencies are established.

Tests:
- Dependency test: list what this section uses from earlier and what later sections use from it.
- If either list is empty for a central section, investigate. If both are empty, FAIL.

### 3. Unmotivated Formalism

Definitions/theorems appear before reader need is established.

Signs:
- Formal statement arrives without plain-language reason.
- Parameter names appear before parameter role is explained.
- Bulk notation frontloading.

Tests:
- For each definition/theorem, check pattern: motivation -> formal statement -> interpretation.
- Missing motivation for core objects is FAIL.

### 4. Theorem-Proof Desert

Long formal stretches have no interpretation or consequence.

Signs:
- Proof ends and section immediately moves on.
- No statement of what was gained, ruled out, or enabled.
- No explanation of which assumptions carried weight.

Tests:
- After each major proof, require a short interpretation paragraph.
- If reader cannot answer "so what changed?", FAIL.

### 5. Weak Openings, Transitions, or Closings

Section boundaries do not carry argument.

Signs:
- Transitions only navigate ("next we discuss") and add no content.
- Closings stop abruptly after last equation/proof.
- Forward links are absent or generic.

Tests:
- Opening test: why now?
- Closing test: what did we establish, and what question does it open?
- Transition test: does transition carry argument, orientation, or texture? Pure navigation ("next we discuss") fails; a sentence that builds anticipation or reframes the question passes even if it carries no new technical fact.

### 6. Authorless Voice and Missing Judgment

Text is factual but anonymous; no intellectual ownership.

Signs:
- No explicit evaluative judgment where judgment is needed.
- No ownership language ("we choose", "we rely on", "our constraint is").
- Alternatives are presented without decision criteria.

Tests:
- Remove names/citations; if no authorial stance remains, FAIL.
- Ask: what does the writer think is the key tension here?

### 7. Flat Intellectual Temperature

Routine and surprising points are narrated at the same temperature.

Signs:
- Key lemmas and bookkeeping receive identical emphasis.
- No marking of subtle points or failure modes.
- No honest limitations or catches.

Tests:
- In a 6-10 page span, identify sentences that calibrate importance.
- If none exist in central material, WARN or FAIL depending on severity.

### 8. Bloat and Throat-Clearing

Prose announces moves instead of executing them.

Signs:
- "It is worth noting that", "Importantly", "In this section we will discuss".
- "The key insight is" followed by obvious restatement.
- "As mentioned above" used as filler.

Important distinction: not every transitional or anticipatory sentence is bloat. Sentences that orient the reader, set expectations, build anticipation, or provide rhetorical rhythm are part of good essayistic writing. "A concrete example makes this vivid" is warm connective prose, not bloat. "It is worth noting that" is bloat because it adds no content and no texture. The test is whether the sentence contributes to the reader's experience (pacing, anticipation, warmth, orientation) even if it does not carry new technical information. If it contributes texture or rhythm, keep it. If it is purely mechanical throat-clearing with no rhetorical function, flag it.

Tests:
- For a suspected phrase, ask two questions: (1) Is meaning unchanged if deleted? (2) Is the reading experience unchanged if deleted? Both must be yes to flag. A sentence that carries no information but improves pacing or builds anticipation is not bloat.
- Persistent bloat clusters are WARN; central sections with heavy bloat can be FAIL.
- Never flag warm transitions, rhetorical questions that drive sections, or sentences that set up examples or figures as bloat.

### 9. Hedge Fog and Sycophancy

Writing avoids taking positions.

Signs:
- "One could argue", "it is generally believed", "some researchers think".
- Symmetric treatment of alternatives with no criteria.
- Praise language replacing analysis.

Tests:
- Require explicit comparison criteria when alternatives are discussed.
- If a section never commits to a position where it should, FAIL.

### 10. Vague Claims and Missing Quantification

Claims lack explicit bounds, assumptions, or definitions.

Signs:
- "efficient", "optimal", "significant", "mild assumptions" without specifics.
- Complexity claims without parameter dependencies.
- Claims of correctness without domain/caveat.

Tests:
- Every strong claim must carry bound + conditions + scope.
- Vague claim about central result is FAIL.

### 11. Fake Intuition and Math-Adjacent Imprecision

"Intuition" restates facts or uses technically-sounding but wrong prose.

Signs:
- "The gap ensures adiabaticity" style causal shortcuts.
- "The Hamiltonian encodes the solution" without mechanism.
- Explanations that cannot support predictions.

Tests:
- Prediction test: can reader predict at least one consequence from the intuition?
- Precision test: rewrite sentence formally. If meaning changes, original was imprecise.

### 12. Register Drift, Passive Pileup, and Nominalization

Style loses energy or consistency.

Signs:
- Jarring or uncontrolled alternation between stiff bureaucratic and casual voice.
- Repeated passive structures ("it is shown that").
- Verb-to-noun inflation ("perform an analysis of" instead of "analyze").

Note: intentional register variation is a feature of good writing, not a defect. The best technical prose is formal during proofs and warmer during motivation, interpretation, and transitions. Penrose shifts register constantly and it works because each shift serves a purpose. Only flag register changes that feel accidental or jarring, not deliberate modulation.

Tests:
- Sample 10-15 sentences; check for jarring uncontrolled shifts, not deliberate variation.
- If sentence energy collapses across a paragraph, WARN.

### 13. Pacing and Rhythm Failure

Cadence does not track thought complexity.

Signs:
- Uniform paragraph function over long stretches.
- Key insights rushed, routine parts over-expanded.
- Repeated sentence templates ("We show X. We prove Y...").

Tests:
- Function-map test: classify five consecutive paragraphs as `setup`, `definition`, `proof move`, `interpretation`, `transition`.
- Insight-allocation test: locate the most fragile step. It should receive extra explanation.
- Cadence test: sentence-count uniformity is weak evidence only; use with other signals.

### 14. Lexical Artifact Clusters (Supporting Evidence Only)

Certain phrases correlate with generic generated prose.

High-signal artifacts:
- "delve", "multifaceted", "realm", "cornerstone", "tapestry"
- "it is worth noting that", "it should be noted that"
- "this serves as", "this stands as"
- paragraph-initial "Moreover" without contrast

Medium-signal artifacts:
- "crucial/crucially", "robust" (non-technical), "nuanced"
- "facilitate", "leverage" (as verb), "shed light on"

Rules:
- Artifact presence alone cannot trigger FAIL.
- Use artifacts only to corroborate structural/voice failures.

### 15. Citation and Intellectual-History Failure

Citations are dumped or disconnected from explanation.

Signs:
- Citation lists with no contribution summary.
- Non-obvious claims with no citation or proof.
- Key concept presented as if it appeared fully formed.

Tests:
- Each citation should answer: what does this source contribute here?
- For central ideas, explain refinement path or limitation of earlier formulations when relevant.

### 16. Insufficient Depth Relative to Source Material

Thesis exposition is thinner than its own source paper where it should teach more.

Signs:
- Source paper gives more detail than thesis on the same point.
- Core proofs are only sketched without compensating explanation.
- Definitions are stated without "why this object" explanation.

Tests:
- Floor test: thesis must match or exceed source detail, or explicitly defer with clear reference.
- Teaching test: could a strong graduate student reconstruct and extend the argument from this section?

## Positive Criteria

A section passes when:

1. Opening states the question and stakes clearly.
2. Section order reflects dependency order.
3. Definitions/theorems are motivated before formalized.
4. After proofs, interpretation states what changed and why it matters.
5. Authorial judgment is visible and accountable.
6. Claims are precise with explicit bounds and assumptions.
7. Intuition is predictive, not decorative.
8. Transitions carry argument, not just navigation.
9. Rhythm follows thinking: slow on insight, concise on routine steps.
10. Register is consistent, active, and readable.
11. Citations are integrated with explanation.
12. Reader exits with new capability, not just new vocabulary.
13. Prose has warmth and varied pace. Good writing is not dry. It pulls the reader forward through anticipation, surprise, concrete vignettes, and sentences that reward attention. Do not penalize sentences that build reader engagement even if they carry no new theorem.

## Severity

**FAIL:** Undermines thesis purpose.
- Missing motivation for a central definition/theorem.
- Vague or imprecise claim about central results.
- Structural disconnection of a central section.
- No interpretable payoff after major proof blocks.
- Authorless voice across a full section.
- Depth below source-paper baseline on central material.

**WARN:** Local weakness, fixable in revision.
- Bloat/filler clusters.
- Flat emphasis in local spans.
- Weak transition/closing.
- Template sentence loops.
- Citation quality issues that do not break argument validity.
- Lexical artifact clusters with otherwise sound argument.

## Procedure

For short sections, one pass is enough. For chapter-length material, use multi-pass review.

**Pass 0 (calibration):**
- Read 1-2 pages from `taste/` references to reset quality baseline.

**Pass 1 (spine):**
- Map section questions and dependencies.
- Flag sections with unclear purpose.

**Pass 2 (section boundaries):**
- Check opening motivation, transition content, closing payoff.

**Pass 3 (paragraph craft):**
- Check motivation-formalism-interpretation cycle.
- Run pacing/function-map and insight-allocation tests.

**Pass 4 (sentence precision):**
- Hunt vague claims, hedge fog, passive pileup, nominalization, fake intuition.
- Verify all strong claims carry conditions and bounds.

**Pass 5 (reader outcome):**
- Complete sentence: "Now the reader can ___."
- If generic/empty, section fails regardless of local polish.

## Output Format

Report findings with symptom, consequence, and rewrite direction.

```
FAIL: Structural and writing-quality failures
  - ch4.tex:23
    symptom: spectral gap definition appears before any motivating question
    consequence: reader cannot infer why this object is needed
    rewrite_direction: add one motivation paragraph naming the obstruction this definition resolves
  - ch5.tex:67
    symptom: "the gap ensures adiabaticity" uses incorrect causal shorthand
    consequence: plants false mental model for runtime dependence
    rewrite_direction: restate with rate-gap relationship and explicit assumptions

WARN: Local quality weaknesses
  - ch2.tex:45
    symptom: repeated bloat openers ("Importantly", "It is worth noting")
    consequence: slows pacing and signals meta-writing over argument
    rewrite_direction: delete bloat and lead with the claim
  - ch3.tex:112
    symptom: "efficient" claim lacks complexity expression
    consequence: reader cannot evaluate scope or compare methods
    rewrite_direction: provide explicit asymptotic bound with parameter dependencies

PASS: Writing is rigorous, motivated, and reader-progressive
```
