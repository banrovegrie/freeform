# Unstructured Adiabatic Quantum Optimization

My master's thesis on Unstructured Adiabatic Quantum Optimization, supervised by Shantanav Chakraborty. Built on the published paper [Unstructured Adiabatic Quantum Optimization: Optimality with Limitations](https://arxiv.org/abs/2411.05736) (Braida, Chakraborty, Chaudhuri, Cunningham, Menavlikar, Novo, Roland, 2025).

Make sure that the way this thesis would be written is satisfactory to Prof. Shantanav Chakraborty (check `taste/` for papers by him). We also aim to beat the baseline expectations of the theses we have with us in `taste/` (of Zeeshan Ahmed and Ronald de Wolf).

## Table of Contents

### Frontmatter

- Epigraph
- Abstract
- Acknowledgments
- List of Theorems / List of Figures

### Chapter 1: Introduction

| Section | Content |
|---------|---------|
| 1.1 The Ground State Problem | Nature finds ground states. Can we harness this for computation? Physical motivation for Hamiltonian-based quantum computing. |
| 1.2 Quantum Speedups for Optimization | Grover's $\sqrt{N}$ speedup. Circuit model achieves it via amplitude amplification. |
| 1.3 The Adiabatic Alternative | Condensed matter connections, quantum annealing. Universality: AQC equivalent to circuit model. |
| 1.4 The Central Question | Can AQO match Grover? The $\Omega(2^{n/2})$ lower bound. |
| 1.5 What This Thesis Establishes | Main Result 1: optimal runtime. Main Result 2: NP-hard. Main Result 3: #P-hard. The surprise revealed. |
| 1.6 How to Read This Thesis | Roadmap. Running examples introduced. |

### Chapter 2: Quantum Computation

| Section | Content |
|---------|---------|
| 2.1 Quantum Mechanics Foundations | States, evolution, measurement. Hilbert spaces, Dirac notation, unitaries. Two-pass: intuition then formalism. |
| 2.2 Composite Systems and Entanglement | Tensor products. The strangeness that enables quantum speedups. |
| 2.3 Spectral Theory | Eigenvalues, decomposition, spectral gap. The resolvent $R_A(\gamma) = (\gamma I - A)^{-1}$. Sherman-Morrison formula. |
| 2.4 The Circuit Model | Gates, circuits, BQP. Universal computation. |
| 2.5 Grover's Algorithm | Unstructured search in $O(\sqrt{N})$. Geometric visualization. Optimality. |
| 2.6 Amplitude Amplification | Extension to optimization. Finding ground states in the circuit model. |

### Chapter 3: Adiabatic Quantum Computation

| Section | Content |
|---------|---------|
| 3.1 Computational Complexity | P, NP, NP-completeness. 3-SAT. The Local Hamiltonian problem. |
| 3.2 Counting Complexity | #P, #P-hardness. Valiant's theorem. Why counting is harder than deciding. |
| 3.3 What is Adiabaticity? | Foundational physics (from slow vs fast, hierarchical dynamics of systems etc.) and more. |
| 3.4 Quantum Adiabatic Theorems | Born-Fock (1928) to Jansen-Ruskai-Seiler. The bound $T \geq \mathrm{poly}(1/g_{\min}, 1/\varepsilon)$. |
| 3.5 Adiabatic Quantum Computation | $H(s) = (1-s)H_0 + sH_P$. Universality theorem. |
| 3.6 Encoding Optimization Problems | Ising Hamiltonians: $H_\sigma = \sum J_{ij} \sigma_z^i \sigma_z^j + \sum h_j \sigma_z^j$. NP-hard problems as ground states. |
| 3.7 Global vs Local Adiabaticity | Constant rate vs adaptive. Roland-Cerf for Grover: achieving $\sqrt{N}$. |
| 3.8 The Gap Challenge | For general $H_P$, where is the avoided crossing? Setup for spectral analysis. |

### Chapter 4: Spectral Analysis of Adiabatic Optimization

This chapter develops the technical machinery for bounding the spectral gap throughout the adiabatic evolution. We divide $[0,1]$ into three regions and apply different techniques to each.

| Section | Content |
|---------|---------|
| 4.1 Setup and Strategy | $H(s) = -(1-s)|\psi_0\rangle\langle\psi_0| + sH_z$. Overview: why three regions, why different tools. |
| 4.2 The Symmetric Subspace | $\mathcal{H}_S = \mathrm{span}\{|k\rangle\}$. The $M$-dimensional invariant subspace. Reduction from $N$ to $M$ dimensions. |
| 4.3 The Eigenvalue Equation | Implicit equation: $1/(1-s) = (1/N) \sum_k d_k/(sE_k - \lambda)$. Structure of solutions. |
| 4.4 The Spectral Parameters | $A_p = (1/N) \sum_{k \geq 1} d_k/(E_k - E_0)^p$. Central role of $A_1$ in everything that follows. |
| 4.5 The Avoided Crossing | Position $s^* = A_1/(A_1+1)$. Window $\delta_s = (2/(A_1+1)^2) \sqrt{d_0 A_2/N}$. Minimum gap $g_{\min} = (2A_1/(A_1+1)) \sqrt{d_0/(A_2 N)}$. |
| 4.6 Gap Bounds: Left Region | Variational principle with ansatz $|\phi\rangle$. Bound: $g(s) \geq (A_1(A_1+1)/A_2)(s^*-s)$. |
| 4.7 Gap Bounds: Right Region | Resolvent method. Line $\gamma(s)$ between eigenvalues. Sherman-Morrison. Bound: $g(s) \geq (\Delta/30)(s-s_0)/(1-s_0)$. |
| 4.8 Synthesis | Three-region picture unified. Figure: true gap vs bounds. |

### Chapter 5: The Optimal Adiabatic Algorithm

| Section | Content |
|---------|---------|
| 5.1 The Local Schedule | $ds/dt \sim g(s)^2$. Integrating to find total time. |
| 5.2 A Simplified Adiabatic Theorem | Phase randomization extension to continuous time. |
| 5.3 Running Time: The Three Integrals | $I_{\text{left}} + I_{\text{window}} + I_{\text{right}}$. Dominant contribution analysis. |
| 5.4 The Main Result | **Theorem (Main Result 1)**: $T = O((1/\varepsilon) (\sqrt{A_2}/(A_1^2 \Delta^2)) \sqrt{2^n/d_0})$. |
| 5.5 Optimality for Ising Hamiltonians | When $\Delta \geq 1/\mathrm{poly}(n)$: $A_1$, $A_2$ bounded. Runtime $T = \widetilde{O}(\sqrt{2^n/d_0})$ matches lower bound. |
| 5.6 What the Algorithm Requires | Knowledge of $s^*$ to precision $O(\delta_s)$. This means knowing $A_1$ to precision $\sim 2^{-n/2}$. |

### Chapter 6: The Hardness of Optimality

| Section | Content |
|---------|---------|
| 6.1 The Hidden Requirement | Schedule construction needs $A_1$ to precision $\delta_s$. |
| 6.2 Disambiguation via $A_1$ | Given $H$ with promise on $E_0$. Two $A_1$ queries distinguish cases. |
| 6.3 The Modified Hamiltonian | $H' = H \otimes (I + \sigma_z)/2$. Effect on spectrum and $A_1$. |
| 6.4 NP-Hardness | **Theorem (Main Result 2)**: Two calls to oracle for $A_1$ at precision $\varepsilon < 1/(72(n-1))$ solve 3-SAT. |
| 6.5 Polynomial Interpolation | Query $A_1(H'(x))$ for $O(\mathrm{poly}(n))$ values. Reconstruct polynomial $P(x)$. Extract degeneracies $d_k$. |
| 6.6 #P-Hardness | **Theorem (Main Result 3)**: $O(\mathrm{poly}(n))$ calls to exact $A_1$ oracle extract all degeneracies. #P-hard. |
| 6.7 Robustness | Paturi's lemma, Berlekamp-Welch. Hardness at $\varepsilon = O(2^{-\mathrm{poly}(n)})$. |
| 6.8 The Fundamental Asymmetry | Circuit model has no such barrier. The precision gap: required $\sim 2^{-n/2}$, NP-hard at $1/\mathrm{poly}(n)$. |

### Chapter 7: Conclusion

This chapter synthesizes results, presents explorations beyond the paper, and identifies open problems.

| Section | Content |
|---------|---------|
| 7.1 Summary of Results | The trilogy: optimal algorithm, NP-hard preprocessing, #P-hard exactly. |
| 7.2 What We Explored | Quantum calibration idea: can experiments estimate $A_1$? Loschmidt echo approach attempted. |
| 7.3 What We Found | **Validated**: gap formula $g_{\min} = 2A_1 \sqrt{d_0/(A_2 N)}$ for time-independent $H(r)$. Resonance at $r = A_1$. **Failed**: Loschmidt echo calibration does not work; multi-level interference destroys signature. |
| 7.4 The Precision Gap | What is complexity at intermediate precisions $2^{-n^\alpha}$? Open problem. |
| 7.5 The Standard AQO Setting | $H_0 = -\sum \sigma_x^j$. Multiple crossings. Different spectral structure. |
| 7.6 Open Problems | Tractable classes. Catalyst qubits. QAOA connections. Noise effects. |
| 7.7 Closing Remarks | The deeper question: what do these barriers tell us about quantum speedups? |
