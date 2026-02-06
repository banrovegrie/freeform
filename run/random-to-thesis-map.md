## Rough files in order

1. rough/pertubation_theory.tex Section 1 (corrections to c, eta) -> Ch 5/6
2. rough/pertubation_theory.tex Section 2 (MaxCut NP-hardness, lines 142-186) -> Ch 8 (NOT in paper)
3. rough/pertubation_theory.tex Section 3 (perturbation theory, lines 188-259) -> Ch 5/6
4. rough/pertubation_theory.tex Section 4 (eigenvalue of Hamiltonian, lines 260-471) -> Ch 5/6
5. rough/rightHalfBound.tex (resolvent right bound, f(s) monotonicity) -> Ch 6
6. rough/rightHalfBound.tex (time complexity calculation, lines 226-239) -> Ch 7
7. rough/rightHalfBound.tex (alternative proofs, lines 241-305) -> Ch 6 (explored, not used)
8. rough/AQCbound.tex Lemmas 1-3 (error bound, pseudoinverse, projector bounds) -> Ch 7
9. rough/AQCbound.tex Theorem 1 (constant rate) -> Ch 7
10. rough/AQCbound.tex Theorem 2 + Corollary (adaptive rate) -> Ch 7
11. rough/AQCbound.tex "Applied to model" (B_1, B_2 computation) -> Ch 7
12. rough/AQCbound.tex "Grover search" (integral lemma, |Delta'| <= 2, H'' = 0) -> Ch 7
13. rough/A1hardness.tex (original NP-hardness proof, lines 58-109) -> Ch 8
14. rough/A1hardness.tex (MaxCut reduction, lines 173-215) -> Ch 8 (NOT in paper)
15. rough/A1hardness.tex (3-local lemma, lines 216-332) -> Ch 8
16. rough/anExplicitBound.tex (explicit gap bound with polynomial root analysis, lines 29-89) -> Ch 6 (not used)
17. rough/anExplicitBound.tex (integral formulas for runtime, lines 91-98) -> Ch 7 (not used)
18. rough/answers_to_reviews.tex Section 1 (why eigenvalue eq insufficient for right bound, lines 27-35) -> Ch 6 (motivation)
19. rough/answers_to_reviews.tex Section 3 (simplified right bound s_0=s* case, lines 71-93) -> Ch 6 (not used, weaker constant)
20. rough/answers_to_reviews.tex Section "Concise adiabatic theorem" (lines 95-183) -> Ch 7
21. rough/answers_to_reviews.tex Section "B_1, B_2 integration" (lines 146-183) -> Ch 7
22. rough/answers_to_reviews.tex Section "Commutator bounds" (lines 185-255, coefficient 4.77) -> Ch 7
23. rough/answers_to_reviews.tex Section "MaxCut hardness" (lines 261-305) -> Ch 8 (NOT in paper)
24. rough/tqc-extended-abstract.tex (conference compressed version) -> Ch 1 (narrative structure reference)
25. rough/old-paper.tex -> superseded by v3-quantum.tex
26. rough/quantum-aqc-crossing.tex -> superseded by v3-quantum.tex

## References files in order

1. farhi2000adiabatic (original AQC proposal) -> Ch 4
2. farhi2001adiabatic (AQC applied to NP-complete, Exact Cover) -> Ch 4
3. roland2002quantum (local adiabatic evolution, Grover speedup) -> Ch 4/5/7
4. jansen2007bounds (rigorous adiabatic theorem bounds) -> Ch 4/7
5. boixo2009eigenpath (eigenpath traversal, phase randomization) -> Ch 7
6. cunningham2024eigenpath (improved eigenpath traversal) -> Ch 7
7. aharonov2007adiabatic (AQC = standard QC, universality) -> Ch 4
8. aharonov2003stategeneration (adiabatic state generation, stat zero knowledge) -> Ch 4
9. albash2018adiabatic (AQC review, multiple crossings) -> Ch 4/5
10. horvat2006exponential (exponential complexity, gap sqrt(d_0/2^n)) -> Ch 5
11. hen2014continuous (continuous-time algorithms, random Hamiltonian) -> Ch 5
12. farhi2008fail (how to make AQA fail, projector lower bound Omega(sqrt(N))) -> Ch 4/5/8
13. vandam2001powerful (how powerful is AQC, Grover speedup, exp lower bound) -> Ch 4/5/8
14. chakraborty2020optimality (optimality of spatial search via CTQW) -> Ch 5/6
15. arthurthesis (Braida PhD: analog QC for graph problems) -> Ch 5/8
16. altshuler2010anderson (Anderson localization fails AQO) -> Ch 4/9
17. reichardt2004adiabatic (AQO and local minima) -> Ch 4
18. choi2011different (different AQO algorithms) -> Ch 4
19. somma2012quantum (quantum speedup by annealing, glued trees) -> Ch 4
20. krovi2010adiabatic (adiabatic condition, Markov chains) -> Ch 4
21. elgart2012note (switching adiabatic theorem) -> Ch 7
22. dalzell2023mind (super-Grover speedup, jump to end) -> Ch 4/9
23. kempe2006complexity (local Hamiltonian QMA-complete) -> Ch 2/8
24. barahona1982computational (Ising spin glass NP-hard) -> Ch 2/5
25. lucas2014ising (Ising formulations of NP problems) -> Ch 2/5
26. Karp1972 (NP-completeness reductions) -> Ch 2
27. valiant1979complexity (#P complexity class) -> Ch 2/8
28. arora2009computational (complexity theory textbook) -> Ch 2
29. gurvits2005mixed (mixed discriminants #P-hard) -> Ch 8
30. movassagh2023hardness (hardness of random circuits) -> Ch 2
31. ambainis2004quantumsearch (quantum search survey, Grover + extensions) -> Ch 3
32. abrams1999quantum (quantum eigenvalue finding) -> Ch 3
33. childs2004spatial (spatial search by quantum walk) -> Ch 3
34. chakraborty2016spatial (spatial search optimal for almost all graphs) -> Ch 3
35. chakraborty2019power (block-encoded matrix powers) -> Ch 3
36. chakraborty2024implementing (linear combination of unitaries) -> Ch 3
37. ge2019faster (ground state preparation) -> Ch 3/4
38. lin2020optimalpolynomial (optimal eigenstate filtering) -> Ch 3
39. lin2020nearoptimalground (near-optimal ground state prep) -> Ch 3/4
40. an2022qlstimeoptimal (time-optimal adiabatic QLS) -> Ch 4
41. subasi2019qlsadiabatic (QLS inspired by AQC) -> Ch 4
42. berry2020timedependent (time-dependent Hamiltonian simulation) -> Ch 3/4
43. aaronson2011bosonsampling (computational complexity of linear optics) -> Ch 2
44. bouland2019complexity (quantum random circuit sampling) -> Ch 2
45. bremner2017achievingquantum (quantum supremacy) -> Ch 2
46. garnerone2012pagerank (adiabatic PageRank) -> Ch 4
47. johnson2011quantum (quantum annealing hardware, D-Wave) -> Ch 4
48. callison2019finding (quantum walks for spin glass) -> Ch 4
49. hastings2013obstructions (obstructions to classical simulation) -> Ch 4
50. Hastings2021powerofadiabatic (power of AQC, no sign problem) -> Ch 4
51. gilyen2021subexponential (subexponential advantage AQC) -> Ch 4
