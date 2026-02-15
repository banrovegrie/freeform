# Findings: Introduction and Conclusion Drafting

## Chapter Opening Patterns (from existing chapters)
Each chapter opens by connecting to what came before and stating what question it answers:
- Ch 2: "Three people walk into a room with the same problem..." (narrative hook, then question)
- Ch 3: "Chapter 2 translated combinatorial optimization into ground-state energy minimization..." (bridge, then tension)
- Ch 4: "Chapter 3 closed the circuit-query model cleanly..." (bridge, then new question: information cost)
- Ch 5: "In the circuit model, unstructured optimization is already understood..." (contrast, then challenge)
- Ch 6: "Chapter 5 established the crossing window..." (bridge, then what remains)
- Ch 7: "The spectral gap of H(s) is now bounded..." (bridge, then runtime question)
- Ch 8: "The optimal schedule from Chapter 7 achieves a quadratic speedup, but..." (bridge, then caveat)
- Ch 9: "The adiabatic algorithm works..." (affirmation, then the discrepancy that is this chapter's subject)

Pattern: each chapter acknowledges the previous chapter's achievement, then identifies the gap or tension that motivates the current chapter. The introduction must set up the first link in this chain.

## Key Notation Already Established
- |psi_0> = |+>^n (Ch 3)
- H_z diagonal problem Hamiltonian (Ch 2, formalized Ch 5)
- H(s) = -(1-s)|psi_0><psi_0| + sH_z (Ch 4)
- A_p = (1/N) sum d_k/(E_k - E_0)^p (Ch 4-5)
- s* = A_1/(A_1+1) (Ch 4-5)
- g_min = Theta(sqrt(d_0/(N*A_2))) (Ch 5-6)
- Delta = E_1 - E_0 (Ch 3+)

Introduction should NOT define any of these. It should only name the concepts (spectral gap, avoided crossing, schedule) informally.

## Paper Introduction vs Thesis Introduction
The paper's introduction is ~5 dense paragraphs covering: AQC motivation, AQO formulation, the question (can AQO match Grover?), results (gap bounds + hardness), and article organization. It is competent but compressed. The thesis introduction must:
1. Decompose each of those compressed points into motivated exposition
2. Add the Chapter 9 contributions (not in the paper)
3. Add the formalization contribution (not in the paper)
4. Build tension before each technical point rather than stating results immediately
5. Provide the narrative arc that makes the chapter structure feel inevitable

## Aaronson Style Analysis
- Opens with personal/philosophical hook (Conway's Game of Life)
- Uses a concrete conundrum (Shor forces a trilemma) as the driving tension
- Introduces a recurring framing device (the "Beast" of quantum mechanics)
- States contributions modestly but precisely
- Uses concrete worked examples with multiple interpretations
- Summary chapters use the "keep/discard" intuition framing

For this thesis: the equivalent tension is the gap between model equivalence (AQC = circuits up to polynomial overhead) and operational cost (AQO needs information that circuits do not). The "beast" equivalent is the information gap itself.

## Cross-Reference Requirements
Introduction must reference:
- braida2024unstructured (the paper)
- farhi2000adiabatic, farhi2001adiabatic (AQC origins)
- aharonov2007adiabatic (AQC universality)
- roland2002quantum or roland2004quantum (adiabatic Grover)
- Grover1996, bennett1997strengths (circuit-model search)
- jansen2007bounds (adiabatic theorem)
- farhi2008fail (lower bound)
- altshuler2010anderson (exponential gaps for random instances)
- albash2018adiabatic (AQC review)
- valiant1979complexity (#P)
- cook1971complexity (Cook's theorem)

Conclusion must reference:
- braida2024unstructured (the paper)
- durr1996quantum (Durr-Hoyer)
- Guo-An framework (guo2024analytic or similar -- check bib)
- moura2021lean4 (Lean 4)
- johnson2011quantum (quantum annealing)
