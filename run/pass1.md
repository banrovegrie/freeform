# Pass 1: Per-Chapter Reviews

## Chapter 5: Adiabatic Quantum Optimization

Assessment: Accept | Tech: 9 | Presentation: 7 | Significance: 8 | Literature: 7

Math check: PASS. All formulas verified against paper: $A_p$ definition, $s^* = A_1/(A_1+1)$, $\delta_s$, $g_{\min}$, spectral condition. No deviations.

Strengths: Running example (unstructured search) is pedagogically excellent. Synthesis section (5.7) clearly states central tensions. Mathematical precision throughout.

Significant issues:
- ch5:72-79 Spectral parameters $A_p$ defined before reader wants them. No tension built. Add 2-3 sentences before Definition 5.1 explaining why aggregating spectral information this way is necessary.
- ch5:103-115 Spectral condition appears abruptly. Explain "why" before "what": the two-level approximation accuracy requires the crossing window to be narrow.
- ch5:80-82 "Higher $p$ emphasizes levels closer to ground" stated but not unpacked. Explain what this means for $A_1$ controlling crossing position vs $A_2$ controlling gap width.
- ch5:62-63 "Single avoided crossing" asserted without mechanism. Explain how rank-one structure decouples antisymmetric subspaces.

Taste/Humanize: PASS with notes. No AI lexical tells. Good "we" usage. Could use more intellectual engagement ("this is surprising," "the elegance here is...").

## Chapter 6: Spectral Analysis

Assessment: Accept | Tech: 9 | Presentation: 9 | Significance: 9 | Literature: 8

Math check: PASS. All formulas match paper exactly: left bound $A_1(A_1+1)/A_2 \cdot (s^-s)$, right bound $(\Delta/30)(s-s_0)/(1-s_0)$, $f(s^)=4$ for $k=1/4$, $P(1/4)=1/30$. Variational ansatz, Sherman-Morrison, resolvent bounds all verified.

Strengths: Exceptional motivation (lines 8-10, 15-17). Clear proof strategy communication upfront. Pedagogical depth significantly exceeds paper. Running example calculations throughout. Complete gap profile theorem with figure ties everything together.

Significant issues:
- ch6:116 Childs-Goldstone and Chakraborty et al cited but not engaged with. Expand to explain what they contributed and why it's applicable here.
- ch6:84-86 Concavity alternative proof mentioned but not developed. Either expand or remove.
- ch6:186 $\epsilon_0 = d_0/N$ introduced abruptly. Add one defining sentence.

Taste/Humanize: PASS. Author perspective visible throughout. Natural rhythmic variation. No AI tells.

## Chapter 7: Optimal Schedule

Assessment: Accept | Tech: 9 | Presentation: 9 | Significance: 9 | Literature: 8

Math check: PASS with clarification needed. All derivations correct. Constants 2, 4, 40, 4, 6 match paper. $b=1/10$, $k=1/4$ correct. Continuity of $g_0$ verified at both boundaries.

Key finding: Thesis uses $A_1(A_1+1)$ in runtime denominator, which is correct and matches the paper's own appendix proof. The paper's main result statement (Theorem 1) incorrectly has $A_1^2$. The thesis should acknowledge this discrepancy.

Strengths: Exceptional pedagogical clarity. Complete proofs with full detail (integration by parts, Riesz formula). Running example computed at every stage. Rigorous constant tracking throughout.

Significant issues:
- ch7:381 Add footnote acknowledging paper's $A_1^2$ vs correct $A_1(A_1+1)$ discrepancy.
- ch7:354 $\Delta A_2 \leq A_1$ used without justification. Add brief derivation.
- ch7:44 Roland-Cerf "requires knowing the exact gap" slightly imprecise. Could be tight lower bound.

Taste/Humanize: PASS. Excellent motivation. No AI tells. Good intellectual engagement.

## Chapter 8: Hardness of Optimality

Assessment: Weak Accept | Tech: 7 | Presentation: 6 | Originality: 8 | Significance: 8

Math check: WARN. Paper-based content (Theorems 8.1-8.2) all verified correct. Original contributions (Theorems 8.3-8.5) have sound proof structures but gaps:

Critical issues (must fix):
- ch8:230-234 Lebesgue function bound $\Lambda_M(x^*) \leq (2B+1)^{M-1}/(M-1)!$ lacks derivation. Central to Theorem 8.3. Add 3-5 lines deriving or cite source.
- ch8:304-309 Hypergeometric KL divergence $D_j = O(t^2/N^2)$ sketched. Central to Theorem 8.5. Derive briefly or cite.
- ch8:282 Oracle complexity "O(1) queries to $O_H$" imprecise. Clarify per-application cost.

Significant issues:
- ch8:207-210 No first-person voice for original contributions. Add "We address this open problem by..."
- ch8:211-257 Interpolation barrier lacks intuitive setup. Add 2-3 sentences before Theorem 8.3 explaining why Lebesgue function grows exponentially.
- ch8:254-257 Boson sampling / random circuit analogy mentioned but not explained.

Taste: WARN. "crucial" overused (medium-confidence AI tell, 2x). Some scaffolding at line 25. Prose mostly clean but lacks strong authorial voice in original sections.

# Phase 2: Cross-Chapter Synthesis

## 1. Story Arc Continuity

The arc Ch5 -> Ch6 -> Ch7 -> Ch8 is strong and logically coherent:

| Chapter | Question | Answers | Opens |
|---------|----------|---------|-------|
| 5 | What is AQO's spectral structure? | Single crossing at $s^*$, gap $g_{\min}$, window $\delta_s$ | How to bound $g(s)$ everywhere? |
| 6 | Can we bound the gap tightly? | Yes: variational (left), resolvent (right), complete profile | How to convert gap bounds to runtime? |
| 7 | What runtime does the gap profile yield? | $T = O(\sqrt{A_2}/(\Delta^2 A_1(A_1+1)) \cdot \sqrt{N/d_0}/\varepsilon)$ | Can we compute the schedule? |
| 8 | Can the schedule be computed efficiently? | NP-hard approximate, #P-hard exact. Interpolation barrier at $2^{-n/2}$. | Can the barrier be circumvented? |

Transitions: Ch5->Ch6 good (Section 5.7 sets up Ch6 explicitly). Ch6->Ch7 good (complete profile connects to runtime integral). Ch7->Ch8 good (line 406 asks whether $A_1$ can be computed). No gaps.

## 2. Notation Consistency

PASS. Notation is remarkably consistent across all four chapters:
- $A_p$, $s^*$, $\delta_s$, $g(s)$, $g_{\min}$, $g_0$ all used correctly
- Only $\varepsilon$ used (never $\epsilon$)
- $H(s)$, $H_0$, $H_z$ consistent throughout
- $d_0$, $d_k$, $N$, $M$ consistent

One minor extension: Ch8 introduces $\Delta_k = E_k - E_0$ for all $k$, extending $\Delta = E_1 - E_0$ from Ch5-7. Add a transitional sentence.

## 3. No Redundant Definitions

PASS. Key definitions ($A_p$, $s^*$, $\delta_s$, $g_{\min}$, spectral condition) defined once in Ch5, used without re-definition thereafter. Chapters reference earlier definitions by equation number.

## 4. Depth Gradient

The depth increases appropriately:
- Ch5 (setup): Definitions, structure, running example. Correct depth for foundation.
- Ch6 (technical core): Full proofs with variational and resolvent methods. Deepest technical chapter.
- Ch7 (synthesis): Combines Ch5-6 results into main runtime theorem. Appropriate integration depth.
- Ch8 (extensions): Paper results + original contributions. Good mix of reproduction and novelty.

Issue: Ch8 original contributions (Sec 8.3) are shallower than earlier chapters. The interpolation barrier proof has gaps that Ch6's proofs don't. This creates a depth dip where there should be a depth peak (since these are original contributions).

## 5. Paper-as-Subset Verification

The paper's content maps cleanly:

| Paper Section | Thesis Chapter | Coverage |
|---------------|---------------|----------|
| Sec 1-2 (Setup) | Ch5 | Superset: more motivation, running example |
| Sec 3 (Spectrum) | Ch5-6 | Superset: full proofs, pedagogical depth |
| Sec 4 (Schedule) | Ch7 | Superset: complete derivations, all constants |
| Sec 5 (Hardness) | Ch8 | Superset: + interpolation barrier, quantum algorithm, classical lower bound |
| Appendix A-I (Crossing) | Ch5 | Covered |
| Appendix A-II ($f$ monotone) | Ch6 | Covered |
| Appendix A-III (Adiabatic thm) | Ch7 | Covered |
| Appendix A-IV (Runtime proof) | Ch7 | Covered, corrects $A_1^2$ to $A_1(A_1+1)$ |
| Discussion | Ch8 end | Partially covered, some open questions noted |

The thesis is a strict superset of the paper. No paper content is missing.

## 6. Personal Voice

| Chapter | Voice Level | Notes |
|---------|-------------|-------|
| 5 | Medium | Good "we" usage, decent engagement, but could be stronger on "what surprised us" |
| 6 | Strong | Clear authorial perspective, honest about trade-offs ("conservative by factor 30") |
| 7 | Strong | Excellent motivation, intellectual engagement with material |
| 8 | Weak | Paper sections fine, but original contributions lack first-person voice |

Pattern: Voice is strongest where the author is explaining established work deeply (Ch6-7) and weakest where the author should be strongest: their own original contributions (Ch8 Sec 8.3). This needs attention.

## 7. Overall Scores

| Dimension | Ch5 | Ch6 | Ch7 | Ch8 | Avg |
|-----------|-----|-----|-----|-----|-----|
| Mathematical Correctness | 9 | 9 | 9 | 7 | 8.5 |
| Presentation/Exposition | 7 | 9 | 9 | 6 | 7.75 |
| Notational Consistency | 9 | 9 | 9 | 8 | 8.75 |
| Depth Beyond Paper | 7 | 9 | 9 | 8 | 8.25 |
| Personal Voice | 6 | 8 | 8 | 5 | 6.75 |
| Story Arc / Flow | 8 | 9 | 9 | 7 | 8.25 |
| Literature Engagement | 7 | 8 | 8 | 7 | 7.5 |
| Originality | 6 | 7 | 7 | 8 | 7.0 |

## 8. Top 5 Highest-Impact Recommendations

1. **Fix proof gaps in Ch8 original contributions.** The Lebesgue function bound (ch8:230-234) and hypergeometric KL divergence (ch8:304-309) are the only mathematical gaps in the entire thesis. These are in the original material, which an examiner will scrutinize most closely. Add derivations or citations. Impact: prevents examiner rejection.

2. **Add voice to Ch8 Section 8.3.** Original contributions are the thesis's strongest card but are written with the least authorial presence. Add first person ("We prove...", "Our approach..."), explain why you chose this approach, and build intuition before the formal proof. Compare to de Wolf's thesis where every original result has the author visibly thinking. Impact: transforms weakest section into strongest.

3. **Build tension before spectral parameters in Ch5.** Definition 5.1 arrives before the reader wants it. Two sentences explaining why aggregating spectral information this way is necessary would make the entire subsequent arc (Ch5-7) more compelling. The reader should crave $A_p$ before seeing it. Impact: improves first impression; Ch5 is the examiner's entry point.

4. **Acknowledge the paper's $A_1^2$ vs $A_1(A_1+1)$ discrepancy.** The thesis correctly follows the appendix proof, but an examiner who checks against Theorem 1 will be confused. A footnote in Ch7 resolves this preemptively. Impact: prevents examiner confusion at the main result.

5. **Strengthen Ch8 interpolation barrier with intuition and proof roadmap.** Add 3 sentences before Theorem 8.3 explaining why polynomial extrapolation amplifies errors exponentially, and add a proof strategy paragraph stating the three-stage error propagation. This is your best original result; it deserves the clearest exposition. Impact: makes thesis's strongest contribution accessible.

# Summary

Overall verdict: Chapters 5-7 are strong (Accept). Chapter 8 is weaker (Weak Accept) primarily because original contributions have proof gaps and lack authorial voice.

The 5 actions that matter most:

1. Fix proof gaps in Ch8 Sec 8.3: Lebesgue function bound and hypergeometric KL divergence need derivations or citations. An examiner will check these first.
2. Add voice to Ch8 original work: "We prove...", "Our approach differs...", intuitive setup before Theorem 8.3. Your best results deserve your strongest writing.
3. Build tension before $A_p$ in Ch5: Two sentences explaining why we need these parameters before Definition 5.1. This is the examiner's entry point.
4. Footnote the $A_1^2$ vs $A_1(A_1+1)$ discrepancy in Ch7: The thesis is correct; the paper's main result statement has a typo. Note this preemptively.
5. Add proof roadmap to Theorem 8.3: Three-stage error propagation (oracle noise -> Lebesgue amplification -> denominator factor) should be stated upfront.

What's already working well: Notation consistency across all four chapters is excellent. The story arc Ch5->Ch6->Ch7->Ch8 is logically tight. Running examples throughout Ch5-7 are pedagogically strong. Ch6-7 exposition significantly exceeds the paper. No mathematical errors found in Ch5-7.
