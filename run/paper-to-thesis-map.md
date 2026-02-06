# Paper-to-Thesis Map

## Chapter 1: Introduction
Paper sections: narrative framing
Rough sources:
- rough/tqc-extended-abstract.tex -- use as narrative structure reference; extract the compressed storyline (problem, result, significance) to shape the introduction arc

## Chapter 2: Computational Complexity
Paper sections: 1.1 Preliminaries (complexity-theoretic definitions)
References:
- Karp1972 -- introduce NP-completeness reductions; derive or walk through at least one canonical reduction (e.g. 3-SAT to Clique) to ground the reader
- arora2009computational -- cite as textbook backbone; use for definitions of P, NP, BQP, promise problems; elaborate the polynomial hierarchy enough for Ch 8
- valiant1979complexity -- introduce #P formally; explain the counting-vs-decision distinction with examples; needed for Ch 8's #P-hardness
- kempe2006complexity -- introduce local Hamiltonian problem and QMA-completeness; explain the connection between ground-state energy estimation and verification; derive the key reduction idea
- barahona1982computational -- introduce Ising spin glass NP-hardness; explain how combinatorial optimization maps to physics; motivates the AQO setting
- lucas2014ising -- elaborate Ising formulations of NP problems; walk through 1-2 explicit encodings (e.g. MaxCut, number partitioning); connects combinatorial problems to Hamiltonians
- movassagh2023hardness -- introduce hardness of random quantum circuits; cite for quantum computational supremacy context
- aaronson2011bosonsampling -- cite for computational complexity of linear optics; explain boson sampling as evidence for quantum advantage
- bouland2019complexity -- cite for quantum random circuit sampling complexity
- bremner2017achievingquantum -- cite for quantum supremacy framework

## Chapter 3: Quantum Algorithms
Paper sections: 1.1 Preliminaries (quantum algorithms background)
References:
- ambainis2004quantumsearch -- elaborate quantum search beyond Grover; introduce amplitude amplification, optimality of O(sqrt(N)); derive the lower bound argument (polynomial method or adversary)
- abrams1999quantum -- introduce quantum phase estimation (QPE); derive the circuit and error analysis; this is foundational for eigenvalue problems throughout
- childs2004spatial -- introduce spatial search by continuous-time quantum walk; derive the search Hamiltonian and explain why it achieves O(sqrt(N))
- chakraborty2016spatial -- elaborate spatial search optimality for almost all graphs; explain the spectral condition for optimal search
- chakraborty2019power -- introduce block-encoded matrix powers; explain how block-encoding enables polynomial transformations of Hamiltonians
- chakraborty2024implementing -- introduce linear combination of unitaries (LCU); derive the basic LCU lemma; connects to Hamiltonian simulation
- ge2019faster -- introduce ground state preparation via eigenstate filtering; explain the spectral gap assumption and overlap condition
- lin2020optimalpolynomial -- elaborate optimal polynomial eigenstate filtering; derive the Chebyshev-based filter and its complexity; connects to Ch 7's adiabatic approach
- lin2020nearoptimalground -- cite for near-optimal ground state preparation; compare adiabatic vs. filtering approaches
- berry2020timedependent -- introduce time-dependent Hamiltonian simulation; derive product formula or truncated Dyson series bounds; foundational for implementing adiabatic evolution

## Chapter 4: Adiabatic Quantum Computation
Paper sections: 1.1 Preliminaries (AQC definitions), 1.3 Related Work (AQC-specific)
References:
- farhi2000adiabatic -- introduce the original AQC proposal; derive the basic framework (initial Hamiltonian, problem Hamiltonian, interpolation); explain the adiabatic condition informally
- farhi2001adiabatic -- elaborate AQC for NP-complete problems; walk through the Exact Cover instance; explain why the gap structure determines runtime
- roland2002quantum -- introduce local adiabatic evolution; derive the schedule that adapts to gap; explain how this recovers O(sqrt(N)) for Grover -- this is the key predecessor to Ch 7
- jansen2007bounds -- derive the rigorous adiabatic theorem; state the bound with explicit constants; explain the role of gap, derivatives, boundary terms -- foundational for Ch 7
- aharonov2007adiabatic -- introduce AQC = standard QC equivalence; explain the universality construction; cite for completeness of the AQC model
- aharonov2003stategeneration -- cite for adiabatic state generation and statistical zero knowledge connection
- albash2018adiabatic -- cite as comprehensive AQC review; use for multiple crossings discussion and open problems
- farhi2008fail -- introduce how to make AQA fail; derive the projector Hamiltonian lower bound Omega(sqrt(N)); key negative result motivating Ch 5's analysis
- vandam2001powerful -- introduce quantum speedup in AQC; derive the exponential lower bound for certain instances; explain what "powerful" means in this context
- altshuler2010anderson -- introduce Anderson localization as obstacle to AQO; explain the physical mechanism; motivates Ch 9's information gap
- reichardt2004adiabatic -- cite for AQO and local minima; explain the tunneling problem
- choi2011different -- cite for different AQO Hamiltonian choices; explain the design space
- somma2012quantum -- introduce quantum speedup by simulated annealing; derive the glued-trees example; contrast with AQC approach
- krovi2010adiabatic -- cite for adiabatic condition and Markov chain connection
- dalzell2023mind -- introduce super-Grover speedups; explain when "jumping to the end" beats adiabatic; motivates Ch 9
- ge2019faster -- cite also here for ground state prep as alternative to adiabatic path
- lin2020nearoptimalground -- cite also here for comparison with adiabatic approach
- an2022qlstimeoptimal -- cite for time-optimal quantum linear systems via adiabatic methods
- subasi2019qlsadiabatic -- cite for QLS inspired by AQC; explain the connection
- berry2020timedependent -- cite also here for implementing the adiabatic evolution efficiently
- garnerone2012pagerank -- cite for adiabatic PageRank as application
- johnson2011quantum -- cite for quantum annealing hardware (D-Wave); explain the experimental context
- callison2019finding -- cite for quantum walks applied to spin glass optimization
- hastings2013obstructions -- cite for obstructions to classical simulation of quantum systems
- Hastings2021powerofadiabatic -- cite for power of AQC when there is no sign problem
- gilyen2021subexponential -- cite for subexponential quantum advantage via AQC

## Chapter 5: Adiabatic Quantum Optimization
Paper sections:
- 1.2 Summary of our results
- 1.3 Related Work (Ch 2-4 if beyond AQO or Ch 5 if AQO)
- 2.1 Spectrum of the adiabatic Hamiltonian
- 2.2 Finding the Position of Avoided Crossing (Lemmas 2-3, delta_pm, gap in window)
- A.1 Ground and first excited energies near the avoided crossing
Rough sources:
- rough/pertubation_theory.tex Section 1 (corrections to c, eta) -- derive the perturbation corrections; explain physical meaning of c and eta parameters
- rough/pertubation_theory.tex Section 3 (perturbation theory, lines 188-259) -- elaborate the perturbation expansion; derive eigenvalue corrections order by order
- rough/pertubation_theory.tex Section 4 (eigenvalue of Hamiltonian, lines 260-471) -- derive the full eigenvalue structure; extract the characteristic equation and its solutions
References:
- roland2002quantum -- contextualize how local adiabatic evolution set the stage; compare schedule assumptions
- albash2018adiabatic -- cite for review context; use for multiple crossings discussion
- horvat2006exponential -- introduce the exponential complexity result; derive gap = sqrt(d_0/2^n); explain how degeneracy controls hardness
- hen2014continuous -- cite for continuous-time algorithm perspective; explain random Hamiltonian context
- farhi2008fail -- contextualize the Omega(sqrt(N)) lower bound; explain why projector Hamiltonians are worst case
- vandam2001powerful -- contextualize the exponential lower bound instances
- chakraborty2020optimality -- introduce optimality of spatial search via CTQW; explain the spectral techniques shared with AQO analysis
- arthurthesis -- cite Braida's thesis for analog QC perspective on graph problems
- barahona1982computational -- cite for Ising NP-hardness context
- lucas2014ising -- cite for Ising formulation context

## Chapter 6: Spectral Analysis
Paper sections:
- 2.2 Finding the Position of Avoided Crossing (Lemma 4: left bound, Lemma 5: right bound)
- A.2 Proof that f(s) is monotonically decreasing
Rough sources:
- rough/pertubation_theory.tex Section 1 (corrections to c, eta) -- reuse perturbation correction details as needed for spectral bounds
- rough/pertubation_theory.tex Section 3-4 -- extract eigenvalue structure details for the resolvent analysis
- rough/rightHalfBound.tex (resolvent right bound, f(s) monotonicity) -- derive the resolvent-based right bound in full; explain why the eigenvalue equation alone is insufficient (cf. answers_to_reviews)
- rough/rightHalfBound.tex (alternative proofs, lines 241-305) -- explored but not used; keep as reference for alternative approaches
- rough/anExplicitBound.tex (explicit gap bound, lines 29-89) -- not used in final version but explains the polynomial root analysis approach
- rough/answers_to_reviews.tex Section 1 (lines 27-35) -- use the motivation: why the eigenvalue equation is insufficient for the right bound; this explains the need for the resolvent approach
- rough/answers_to_reviews.tex Section 3 (lines 71-93) -- not used (weaker constant), but documents the s_0=s* simplification
References:
- chakraborty2020optimality -- elaborate the spectral techniques for CTQW optimality; explain shared resolvent methods

## Chapter 7: Optimal Schedule
Paper sections:
- 2.3 Optimal adiabatic schedule and running time
- A.3 Adiabatic Theorem and the running time of AQC
- A.3.1 Adiabatic Eigenpath Traversal
- A.3.2 Scaling the derivative of the schedule with the gap
- A.4 Proof of Theorem 1
Rough sources:
- rough/rightHalfBound.tex (time complexity calculation, lines 226-239) -- derive the time complexity from the gap integral
- rough/AQCbound.tex Lemmas 1-3 (error bound, pseudoinverse, projector bounds) -- derive each lemma; explain the role of pseudoinverse in adiabatic error analysis
- rough/AQCbound.tex Theorem 1 (constant rate) -- derive the constant-rate adiabatic theorem; explain why constant rate is suboptimal
- rough/AQCbound.tex Theorem 2 + Corollary (adaptive rate) -- derive the adaptive-rate theorem; explain the gap-dependent schedule; this is the main result
- rough/AQCbound.tex "Applied to model" (B_1, B_2 computation) -- derive B_1, B_2 for the unstructured search Hamiltonian; explicit computation
- rough/AQCbound.tex "Grover search" (integral lemma, |Delta'| <= 2, H'' = 0) -- derive the integral identity; explain why H'' = 0 for linear interpolation and |Delta'| <= 2
- rough/anExplicitBound.tex (integral formulas, lines 91-98) -- not used but documents runtime integral formulas
- rough/answers_to_reviews.tex "Concise adiabatic theorem" (lines 95-183) -- derive the concise version; compare with Jansen et al.
- rough/answers_to_reviews.tex "B_1, B_2 integration" (lines 146-183) -- explicit integration details for B_1, B_2
- rough/answers_to_reviews.tex "Commutator bounds" (lines 185-255, coefficient 4.77) -- derive the commutator bound; explain the 4.77 coefficient origin
References:
- roland2002quantum -- derive Roland-Cerf local adiabatic schedule; compare with the optimal schedule derived here
- jansen2007bounds -- derive the Jansen-Ruskai-Seiler adiabatic theorem; compare constants and assumptions with the paper's version
- boixo2009eigenpath -- introduce eigenpath traversal; derive the phase randomization technique; explain the connection to adiabatic runtime
- cunningham2024eigenpath -- elaborate improved eigenpath traversal; derive the tighter bounds; compare with the adaptive schedule
- elgart2012note -- cite for switching adiabatic theorem; explain the switching function approach as alternative

## Chapter 8: Hardness of Optimality
Paper sections:
- 3.1 NP-hardness of estimating A_1 to a low precision
- 3.2 #P-hardness of estimating A_1 (nearly) exactly
Rough sources:
- rough/pertubation_theory.tex Section 2 (MaxCut NP-hardness, lines 142-186) -- NOT in paper; contains the MaxCut reduction for NP-hardness; elaborate if used as remark
- rough/A1hardness.tex (original NP-hardness proof, lines 58-109) -- derive the full NP-hardness reduction; extract the gap amplification argument
- rough/A1hardness.tex (MaxCut reduction, lines 173-215) -- NOT in paper; contains MaxCut-to-A1 reduction; elaborate if used
- rough/A1hardness.tex (3-local lemma, lines 216-332) -- derive the 3-local Hamiltonian construction; explain the locality reduction
- rough/answers_to_reviews.tex "MaxCut hardness" (lines 261-305) -- NOT in paper; additional MaxCut hardness argument from reviewer response
References:
- kempe2006complexity -- elaborate local Hamiltonian QMA-completeness; derive the key reduction used in the NP-hardness proof
- valiant1979complexity -- elaborate #P and its role; derive or explain at least one #P-complete problem (permanent) to motivate the #P-hardness result
- farhi2008fail -- contextualize the lower bound; explain how projector Hamiltonians connect to hardness
- vandam2001powerful -- contextualize; explain how the hardness of schedule optimization differs from hardness of the optimization problem itself
- gurvits2005mixed -- introduce mixed discriminants as #P-hard; derive the connection to permanent; used in the #P-hardness reduction
- arthurthesis -- cite Braida's thesis for related hardness results in analog QC
- barahona1982computational -- cite for Ising NP-hardness as ingredient in reductions

## Chapter 9: Information Gap
Paper sections:
- 4 Discussion
Rough sources: (none mapped directly; original contribution from experiments)
References:
- altshuler2010anderson -- elaborate Anderson localization as information barrier; derive the physical mechanism; explain why lack of structure information forces suboptimal schedules
- dalzell2023mind -- elaborate super-Grover speedups when problem structure is known; derive the "jump to end" argument; explain the information-runtime tradeoff

## Chapter 10: Future Directions
Paper sections: (none; original)
Rough sources: (none)
References: (to be determined based on open problems identified)

## Paper sections in order

1. **1 Introduction**
2. 1.1 Preliminaries -> Ch 2-4
3. 1.2 Summary of our results -> Ch 5
4. 1.3 Related Work -> Ch 2-4 if beyond AQO or Ch 5 if AQO
5. **2 Optimal adiabatic quantum optimization algorithm**
6. 2.1 Spectrum of the adiabatic Hamiltonian -> Ch 5
7. 2.2 Finding the Position of Avoided Crossing -> Ch 5 (Lemmas 2-3), Ch 6 (Lemmas 4-5)
8. 2.3 Optimal adiabatic schedule and running time -> Ch 7
9. **3 Hardness of predicting the position of the Avoided Crossing**
10. 3.1 NP-hardness of estimating A_1 to a low precision -> Ch 8
11. 3.2 #P-hardness of estimating A_1 (nearly) exactly -> Ch 8
12. **4 Discussion -> Ch 9**
13. **Appendix A**
13. A.1 Ground and first excited energies near the avoided crossing -> Ch 5
14. A.2 Proof that f(s) is monotonically decreasing -> Ch 6
15. A.3 Adiabatic Theorem and the running time of AQC -> Ch 7
16. A.3.1 Adiabatic Eigenpath Traversal -> Ch 7
17. A.3.2 Scaling the derivative of the schedule with the gap -> Ch 7
18. A.4 Proof of Theorem 1 -> Ch 7
