# Taste Check

## Purpose

Verify that writing embodies good qualities rather than naming them.

For notation consistency, see `check-math.md`. For formatting, see `check-format.md`. This test covers prose quality.

## Failure Modes

### 1. Scaffolding Leakage

Phrases that announce technique rather than execute it:

- "To provide intuition..." / "The key insight is..." / "It is worth noting..."
- "Importantly," / "Interestingly," / "In other words,"

**Test:** Delete the phrase. If the sentence still works, the phrase was scaffolding.

**Borderline acceptable:** "Recall that X" when X appeared chapters ago. Forward references like "Section 4 proves..." are acceptable when orienting the reader.

### 2. Sycophancy

Avoiding positions or hedging everything:

- "One could argue..." (argue it or don't)
- "It is generally believed..." (cite or state directly)
- "Some researchers think..." (which ones?)

**Test:** Does the writing compare approaches and say which is better, or explain why context determines the choice? Genuine "it depends" is acceptable when the dependencies are stated.

**Passing example:** "Roland and Cerf's schedule achieves optimal runtime for the unstructured case, but requires global gap knowledge that may be unavailable in practice."

### 3. Parroting

Restating without adding:

- "As mentioned above..." / "As we have seen..."
- Summarizing a paragraph in its final sentence
- Section intros that list contents without motivation

**Test:** Delete the suspected sentence. Is information lost? If no, delete it.

**Passing example:** Chapter summaries that synthesize across sections and connect to the thesis arc add value. Sentence-level recaps do not.

### 4. Filler

Sentences carrying no information:

- "This is an important topic in quantum computing."
- "Much research has been done in this area."
- "Further investigation is warranted."

**Test:** Replace the subject with something unrelated. If it still sounds plausible, it's filler.

**Passing example:** "The adiabatic theorem bounds runtime in terms of the minimum spectral gap" is not filler - it makes a specific claim.

### 5. Vague Claims

Assertions without precision:

- "efficient" without complexity bounds
- "optimal" without proof or definition
- "significant improvement" without quantification
- "under mild assumptions" without stating them

**Passing example:** "The algorithm runs in time $O(\sqrt{N/d_0})$ where $d_0$ is the ground state degeneracy."

### 6. Missing Motivation

- Definitions appearing before the reader wants them
- Theorems without context for what gap they fill
- Sections starting with formalism instead of questions

**Test:** Before each definition, is there a sentence explaining why we need it?

**Passing example:** "To state the runtime bound precisely, we need to characterize the spectral structure. Definition 3.1 introduces the spectral parameters A_p that capture this structure."

### 7. Grandstanding

- "This groundbreaking result..."
- "For the first time ever..."
- "The implications are profound..."

State what is achieved. Delete adjectives claiming significance.

### 8. Structural Incoherence

- Sections that could be reordered without consequence
- Arguments that don't build on each other
- Later sections not using concepts from earlier ones

**Dependency test:** For this section, list: (a) what concepts it uses from earlier sections, (b) what later sections use from it. If both lists are empty, the section is disconnected.

**"So what" test:** After reading a section, can you answer: What question does this section answer? How does the answer matter for the thesis? If unclear, the section lacks purpose.

**Thesis arc test:** Does this section explain something from the paper (2411.05736), weave necessary background, or propose/support a direction beyond the paper? A section serving none of these is disconnected from the thesis.

### 9. Citation Problems

- Citation dumps substituting for understanding
- Missing citations for non-obvious claims
- Citing without engaging (dropping "[17]" without discussing what [17] says)

**Test:** For each citation, does the text explain what the cited work contributes? For each non-obvious claim, is there a citation or proof? Missing citation for a claim is WARN. Citation dump (3+ citations in one sentence with no discussion) is WARN. Both together is FAIL.

### 10. Math-Adjacent Imprecision

Prose describing mathematical objects with technically-sounding but wrong or empty language:

- "The Hamiltonian encodes the solution" (how? what does "encodes" mean?)
- "The gap ensures adiabaticity" (wrong causation - it's the relationship between gap and evolution rate)
- "The system evolves to the ground state" (conflates ideal and actual behavior)

**Test:** For any sentence making a claim about a mathematical object, can you write a precise version? If the precise version says something different, the original was imprecise.

**BAD:** "The adiabatic theorem guarantees success."
**GOOD:** "The adiabatic theorem bounds the error: the final state is $\varepsilon$-close to the ground state if $T = O(1/(g_{\min}^2 \cdot \varepsilon))$."

### 11. Fake Intuition

Claims to explain that actually restate:

- "Intuitively, X because Y" where Y is just X in different words
- "This happens due to quantum effects" (what effects?)
- "The algorithm exploits the structure" (which structure? how?)

**Test:** After reading the intuition, could someone unfamiliar with the topic predict a consequence or answer a follow-up question? If no, the intuition is fake.

**BAD:** "The avoided crossing occurs because the two states compete for the role of ground state."
**GOOD:** "The avoided crossing is sharp when ground state degeneracy $d_0$ is small: the coupling scales as $\sqrt{d_0/N}$, so fewer ground states means weaker mixing and a smaller gap." (Reader can now predict: larger $d_0$ widens the crossing.)

### 12. Quantum-Specific Failures

**Bra-ket cargo culting:** Using Dirac notation to signal rigor without adding precision.
- Test: Remove all bra-kets from a sentence. Does it lose information? If not, the notation was decoration.

**Superposition/entanglement as explanations:**
- "Superposition allows exploring all solutions" - FAIL (anthropomorphizes, misleading)
- "Entanglement enables the speedup" - WARN without specifying mechanism
- "Quantum parallelism" as causal explanation - FAIL

These terms should describe mathematical structure, not serve as causal agents.

**Passing example:** "The initial state $|+\rangle^{\otimes n}$ has equal amplitude on all basis states. Under adiabatic evolution, amplitude concentrates on the ground state(s) of $H_P$, provided evolution is slow relative to the minimum gap."

### 13. Complexity Theater

Making simple ideas sound complicated:

- Jargon when plain language works: "leverage the spectral properties" vs "use the eigenvalues"
- Unnecessarily abstract: "The map phi induces a correspondence" vs "phi matches each s to some t"
- Multi-sentence explanations of one-sentence ideas

**Test:** Can a graduate student understand this on first read? If a simpler explanation exists, use it.

This doesn't mean avoiding technical depth. The adiabatic theorem is genuinely subtle. But "$H(s)$ interpolates between $H_0$ and $H_P$" needs no elaboration.

## Positive Criteria

A section passes when:

1. Each sentence advances understanding
2. Results are stated with explicit bounds and conditions
3. Definitions have preceding motivation
4. Comparisons take positions (or explain why context matters)
5. The section serves the thesis's argument and could not be removed
6. Intuitions are testable (reader can predict consequences)
7. Technical prose is precise enough to be wrong (and isn't)

## Thesis-Specific Checks

A thesis differs from a paper:

1. **Teaching burden:** Readers may be learning the field. Would a graduate student new to AQO understand this section?
2. **Mastery demonstration:** The author must show deep understanding. Does the writing show understanding beyond what's in cited sources?
3. **Narrative arc:** Chapters must build toward the thesis argument. Does this chapter connect to chapters before and after it?

## Severity

**FAIL:** Undermines the thesis's purpose.
- Missing motivation for a definition the thesis relies on
- Vague claim about the thesis's own results
- Section that serves no structural purpose
- Fake intuition for a central concept
- Math-adjacent imprecision about the main results

**WARN:** Local and fixable.
- Scaffolding phrases
- Filler sentences
- Minor hedging
- Bra-ket decoration
- Complexity theater on peripheral topics

## Procedure

For long chapters (10+ pages), use multiple passes:

**Pass 1 (structure):** Read section headings and first/last paragraphs.
- Check structural coherence (failure mode 8)
- Identify sections with unclear purpose
- Flag for detailed review

**Pass 2 (sampling):** For each section:
- First paragraph: Does it motivate the section?
- Final paragraph: Does it connect forward?
- Sample 2-3 paragraphs: Check failure modes 1-7, 10-13

**Pass 3 (targeted):** For flagged sections:
- Full sentence-by-sentence analysis
- Mark specific lines

For short sections, a single pass through all failure modes suffices.

## Output Format

```
FAIL: Structural problems
  - ch4.tex:23-31: Spectral gap definition lacks motivation
  - ch5.tex:67: "The gap ensures adiabaticity" - wrong causation, rewrite

WARN: Local fixes
  - ch2.tex:45: "Interestingly" - delete
  - ch3.tex:112: "efficient" - add O(?) bound
  - ch3.tex:89: Bra-kets add no information - simplify or justify

PASS: Section meets standards
```
