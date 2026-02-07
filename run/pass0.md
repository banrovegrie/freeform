A holistic review of chapters 5–8 identified issues at three severity levels. This is an attempt to fix all of them. The chapters form a connected arc (problem setup → spectral analysis → optimal schedule → hardness), so fixes must preserve cross-chapter coherence.

Read these first:
- @CLAUDE.md (writing guidelines — every sentence must carry information, no scaffolding, no filler)
- @src/tests/check-taste.md (failure modes to avoid when writing new text)
- @src/tests/agent-humanize.md (voice calibration — de Wolf level: technically precise AND personally present)
- @taste/README.md (style guide with author patterns)
- @paper/v3-quantum.tex (source of truth for all math)

Then read all four chapters:
- @src/chapters/chapter5.tex
- @src/chapters/chapter6.tex
- @src/chapters/chapter7.tex
- @src/chapters/chapter8.tex

## Chapter 8: Hardness of Optimality (HIGHEST PRIORITY)

Ch8 scored weakest: Tech 7, Presentation 6, Voice 5. Original contributions (Sec 8.3 onward) have proof gaps and lack authorial voice. An examiner will scrutinize original work most closely. Fix Ch8 first.

### 8-A. CRITICAL: Derive Lebesgue function bound (~line 230-234)

The bound $\Lambda_M(x^*) \leq (2B+1)^{M-1}/(M-1)!$ is central to Theorem 8.3 but lacks derivation. Add 3-5 lines deriving it or cite a precise source. The derivation should explain *why* the Lebesgue function grows: it measures how polynomial interpolation amplifies pointwise errors. For $M$ nodes in an interval of width $2B$, the Lebesgue function is $\Lambda_M(x) = \sum_j |\ell_j(x)|$ where $\ell_j$ are Lagrange basis polynomials. For equally spaced integer nodes, each $|\ell_j(x^*)|$ is bounded by a product of ratios of node distances, giving the stated factorial bound. Check `references/mds/` for approximation theory references. If none exist, derive from first principles.

### 8-B. CRITICAL: Derive hypergeometric KL divergence (~line 304-309)

The bound $D_j = O(t^2/N^2)$ is sketched but not derived. Expand: state the two hypergeometric distributions explicitly (one with $d_0$ marked items, one with $d_0 \pm 1$), write the KL divergence formula, and show the $O(t^2/N^2)$ bound follows from Taylor expansion of the log ratio when $t \ll N$. This is central to Theorem 8.5 (Grover separation).

### 8-C. CRITICAL: Clarify oracle model (~line 282)

"O(1) queries to $O_H$" is imprecise. State the oracle model explicitly: "Each query to $O_H$ accepts a bitstring $z \in \{0,1\}^n$ and returns the eigenvalue $E_z$, at unit cost." This matches the paper's convention.

### 8-D. Add voice to original contributions (Sec 8.3 onward, ~line 207-257)

The original contributions are written with the least authorial presence — exactly backward. Be surgical:
- At the opening of the interpolation barrier section, add 1-2 first-person sentences: "We now turn to the gap between NP-hardness at $1/\text{poly}(n)$ precision and #P-hardness at exponential precision. The paper leaves this intermediate regime open. We show that polynomial interpolation — the technique behind the #P-hardness result — breaks down at the algorithmically relevant precision $2^{-n/2}$."
- Before Theorem 8.3, add a proof roadmap: "The proof proceeds in three stages: (i) the oracle reveals $A_1$ through polynomially many noisy evaluations, (ii) the Lebesgue function of the interpolation nodes amplifies these errors exponentially, (iii) the required precision $2^{-n/2}$ exceeds what the amplified polynomial can deliver."
- After Theorem 8.3, add one sentence reflecting on the result's meaning.
- Before Theorem 8.5 (quantum algorithm), motivate: "The interpolation barrier is a classical obstruction. A quantum algorithm that avoids interpolation entirely can do better."
- Do NOT add hedging, filler, or scaffolding. Just state the intellectual content directly.

Read the author's voice in Ch6 lines 8-10 and Ch7 lines 11-13 for calibration. Match that engagement level.

### 8-E. Boson sampling analogy (~line 254-257)

Mentioned but not explained. Either expand to 2-3 sentences explaining the structural parallel (hardness of pre-computation as a barrier to quantum advantage) or delete the mention. Do not leave unexplained analogies.

### 8-F. MINOR: "crucial" appears twice — AI lexical tell

Replace both instances with direct language: "the bound requires...", "the distinction matters because...", or simply delete the word.

### 8-G. MINOR: Scaffolding at line 25

Check line 25 for a scaffolding phrase. Delete it and let the sentence stand on its content.

### 8-H. MINOR: Δ_k transition

Ch8 introduces $\Delta_k = E_k - E_0$ for all $k$, extending $\Delta = E_1 - E_0$ from earlier chapters. Add one sentence at first use: "We extend the notation $\Delta = E_1 - E_0$ to all levels: $\Delta_k = E_k - E_0$ for $k \geq 1$."

## Chapter 5: Adiabatic Quantum Optimization (SECOND PRIORITY)

Ch5 scored Accept (Tech 9, Presentation 7, Voice 6). Math is solid but this is the examiner's entry point — motivation before key definitions needs strengthening.

### 5-A. Build tension before A_p (~line 72-79)

Definition 5.1 introduces $A_p$ before the reader wants it. Before the definition, add 2-3 sentences: "The crossing position $s^*$ depends on the full eigenvalue structure of $H_z$ — not just the ground and first excited energies, but all $M$ levels and their degeneracies. To distill this structure into quantities that directly control the algorithm's behavior, we define a family of spectral parameters that aggregate the spectrum with different weightings." This creates a gap that Definition 5.1 fills.

### 5-B. Explain spectral condition context (~line 103-115)

The spectral condition appears abruptly. Before it, add 1-2 sentences: "The two-level approximation near the crossing is accurate when the window $\delta_s$ is narrow compared to $[0,1]$. Since $\delta_s = O(\sqrt{d_0 A_2/N})$, this requires the spectral parameters to be polynomially bounded — a condition we now make explicit."

### 5-C. Unpack "higher p emphasizes levels closer to ground" (~line 80-82)

Stated but not explained. Expand to 2-3 sentences: "$A_1$ weights each level by $1/(E_k - E_0)$, giving most influence to levels just above the ground state. $A_2$ weights by $1/(E_k - E_0)^2$, amplifying this: a level at energy $E_0 + \varepsilon$ contributes $O(1/\varepsilon^2)$ to $A_2$ but only $O(1/\varepsilon)$ to $A_1$. As a result, $A_1$ controls where the crossing occurs (it sets $s^*$), while $A_2$ controls how sharp the crossing is (it appears in $g_{\min}$ and $\delta_s$)."

### 5-D. Explain single avoided crossing mechanism (~line 62-63)

Asserted without mechanism. Add 1-2 sentences: "The rank-one structure of $H_0$ restricts the coupling to the $M$-dimensional symmetric subspace. Within this subspace, the two lowest eigenvalues undergo a single avoided crossing as the ground state character transitions from the uniform superposition to $H_z$'s ground states. The remaining $N - M$ eigenvalues in the orthogonal complement evolve monotonically."

### 5-E. MINOR: Strengthen voice (at most 2-3 sentences total across chapter)

Add intellectual engagement only where natural:
- Near the gap formula, something like: "The gap scales as $\sqrt{d_0/N}$: more ground states strengthen the coupling and widen the crossing."
- Near the crossing position: "That $s^*$ depends only on $A_1$ — a single spectral summary — is the structural reason the schedule has a closed form."

Do not overdo it. If a sentence reads as performative, delete it.

## Chapter 7: Optimal Schedule (THIRD PRIORITY)

Ch7 scored Accept (Tech 9, Presentation 9). Only minor issues.

### 7-A. Footnote: A₁² vs A₁(A₁+1) discrepancy (~line 381)

The thesis correctly uses $A_1(A_1+1)$ in the runtime denominator, following the paper's appendix proof. But the paper's main Theorem 1 statement has $A_1^2$. Add a footnote: "The paper's Theorem 1 states $A_1^2$ in the denominator; the correct expression from the proof in Appendix A-IV is $A_1(A_1+1)$. We follow the proof."

### 7-B. Justify ΔA₂ ≤ A₁ (~line 354)

Used without justification. Add a brief derivation: "Since $E_k - E_0 \geq \Delta$ for all $k \geq 1$, we have $A_1 = (1/N)\sum_{k \geq 1} d_k/(E_k - E_0) \geq (1/N)\sum_{k \geq 1} d_k \cdot \Delta/(E_k - E_0)^2 = \Delta A_2$." (Or the correct chain — verify against the paper.)

### 7-C. MINOR: Roland-Cerf precision (~line 44)

"requires knowing the exact gap" is slightly imprecise. Change to: "requires knowing a tight lower bound on the gap" or "requires knowledge of the gap profile" since the local adiabatic condition works with lower bounds.

## Chapter 6: Spectral Analysis (LOWEST PRIORITY)

Ch6 scored highest: Tech 9, Presentation 9, Voice 8. Minimal fixes.

### 6-A. Engage with Childs-Goldstone and Chakraborty et al (~line 116)

Cited but not engaged with. Add 1-2 sentences explaining what they contributed: "Childs, Gosset, and Webb~[cite] used a different resolvent approach for Hamiltonian simulation; our application of Sherman-Morrison to the rank-one perturbation structure is more direct for this setting. Chakraborty, Novo, and Roland~[cite] introduced the eigenpath framework that informs the schedule construction of Chapter 7." (Adjust to match what the citations actually say.)

### 6-B. Concavity alternative (~line 84-86)

Mentioned but not developed. Either add 2 sentences explaining why concavity gives the same bound (the ground energy is concave in $s$ because it's a pointwise minimum of affine functions, so any tangent line at $s^*$ lies above $\lambda_0(s)$, giving the same slope bound), or remove the mention.

### 6-C. MINOR: ε₀ = d₀/N (~line 186)

Introduced abruptly. Add one defining sentence: "Define $\varepsilon_0 = d_0/N$, the fraction of the Hilbert space occupied by ground states."

## After all fixes

Run these checks:

1. Compile the thesis: `cd src && make` — verify LaTeX builds cleanly
2. Run @src/tests/check-math.md on all four chapters — verify no new math errors
3. Run @src/tests/check-taste.md on ch5 and ch8 — verify no scaffolding or filler was added
4. Run @src/tests/agent-humanize.md on ch8 — verify voice improved, not worsened
5. Spot-check cross-chapter notation: verify $A_p$, $s^*$, $\delta_s$, $g_{\min}$, $\varepsilon$ (never $\epsilon$) are still consistent

## Global constraints

- Do NOT rewrite sections that are working. Ch6 and Ch7 scored 9/9 on presentation — leave those sections alone except for the specific fixes above.
- Do NOT add emotive language or grandstanding. Target voice: de Wolf (precise AND present). Not Aaronson-level commentary — more restrained than that.
- Do NOT simplify math to add accessibility. Add explanation *alongside* the math.
- Every new sentence must carry information. Apply CLAUDE.md's deletion test: if removing the sentence loses no information, do not add it.
- Total additions across all four chapters should be roughly 40-60 lines of LaTeX. These are surgical fixes, not rewrites.
- Preserve the existing running example (M=2 unstructured search) wherever it appears. Do not disrupt it.
