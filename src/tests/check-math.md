# Math and Notation Check

## Purpose

Verify mathematical correctness: statements match the published paper, and notation is consistent throughout. LLMs may hallucinate math invisibly and make errors which a human expert would immediately.

## Reference

Source of truth: `paper/` (the published paper 2411.05736).

## Notation Reference

Canonical notation from the paper (`paper/v3-quantum.tex`). This is the exhaustive reference for the thesis.

### A. LaTeX Macros

| Macro | Expands To | Usage |
|-------|------------|-------|
| `\defeq` | `\coloneqq` | Definition assignment := |
| `\bigket{x}` | `\left\|x\right\rangle` | Enlarged ket |
| `\bigbra{x}` | `\left\langle x\right\|` | Enlarged bra |
| `\ip{x}{y}` | `\langle x\|y\rangle` | Inner product |
| `\ketbra{x}{y}` | `\|x\rangle\langle y\|` | Outer product |
| `\braketbra{x}{A}{y}` | `\langle x\|A\|y\rangle` | Matrix element |
| `\norm{A}` | `\left\lVert A\right\rVert` | Spectral norm |
| `\trnorm{A}` | `\left\lVert A\right\rVert_1` | Trace norm |
| `\infnorm{A}` | `\left\lVert A\right\rVert_\infty` | Infinity norm |
| `\spnorm{A}` | `\left\lVert A\right\rVert` | Spectral norm |
| `\maxnorm{A}` | `\left\lVert A\right\rVert_{\max}` | Max norm |
| `\bigO{x}` | `\mathcal{O}(x)` | Big-O |
| `\bigOt{x}` | `\widetilde{\mathcal{O}}(x)` | Big-O tilde |
| `\littleo{x}` | `o(x)` | little-o |
| `\tr{A}` | `\Tr[A]` | Trace with brackets |
| `\sgn{x}` | `\mathrm{sgn}(x)` | Sign function |
| `\rank{x}` | `\mathrm{rank}(x)` | Rank |
| `\argmax` | `\arg\,\max` | Argmax |
| `\argmin` | `\arg\,\min` | Argmin |
| `\diff` | `d\!` | Differential |
| `\od[n]{x}{y}` | `d^n x / dy^n` | Ordinary derivative |
| `\Ref` | `\mathrm{Ref}` | Reference operator |
| `\Id` | `\mathrm{Id}` | Identity |
| `\AND` | `\mathrm{AND}` | Boolean AND |
| `\Pr` | `\mathrm{Pr}` | Probability |
| `\Tr` | `\mathrm{Tr}` | Trace |
| `\im` | `\mathrm{im}` | Image |
| `\Haar` | `\mathrm{Haar}` | Haar measure |
| `\cupdot` | `\overset{.}{\cup}` | Union with dot |
| `\pvp` | `\vec{p}'` | Vector with prime |

### B. Complexity Classes

| Notation | LaTeX | Description |
|----------|-------|-------------|
| NP | `\NP` | Nondeterministic polynomial |
| #P | `\sharpP` | Sharp-P counting class |
| MAX | `\MAXproblem` | MAX problem class |
| SAT | `\SAT` | Satisfiability |

### C. Quantum States

| Notation | LaTeX | Description |
|----------|-------|-------------|
| ket psi | `\ket{\psi}` | Generic quantum state |
| bra psi | `\bra{\psi}` | Dual state |
| ket psi_0 | `\ket{\psi_0}` | Initial superposition state |
| ket + tensor n | `\ket{+}^{\otimes n}` | Equal superposition n qubits |
| ket 0 tensor n | `\ket{0}^{\otimes n}` | All-zeros state |
| ket k | `\ket{k}` | Symmetric subspace eigenstate |
| ket k^(ell) | `\ket{k^{(\ell)}}` | Fourier basis state |
| ket z | `\ket{z}` | Computational basis state |
| ket phi | `\ket{\phi}` | Variational ansatz state |
| ket v(1) | `\ket{v(1)}` | Final ground state superposition |

### D. Hamiltonians

| Notation | LaTeX | Description |
|----------|-------|-------------|
| H(s) | `H(s)` | Adiabatic Hamiltonian |
| H_0 | `H_0` | Initial Hamiltonian: -ket psi_0 bra psi_0 |
| H_P | `H_P` | Problem Hamiltonian (generic) |
| H_z | `H_z` | Problem Hamiltonian diagonal in comp basis |
| H_sigma | `H_\sigma` | Ising spin Hamiltonian |
| bar H(s) | `\bar{H}(s)` | H(s) restricted to symmetric subspace |
| H'(x) | `H'(x)` | Modified Hamiltonian with extra spin |
| H_k | `H_k` | k-th clause Hamiltonian (3-SAT reduction) |

### E. Pauli and Projection Operators

| Notation | LaTeX | Description |
|----------|-------|-------------|
| sigma_z | `\sigma_z` | Pauli Z matrix |
| sigma_x | `\sigma_x` | Pauli X matrix |
| sigma_z^j | `\sigma_z^{j}` | Pauli Z on qubit j |
| sigma_+^(n+1) | `\sigma_+^{(n+1)}` | Raising operator on qubit n+1 |
| P(s) | `P(s)` | Ground state projector |
| Q(s) | `Q(s)` | Excited state projector: I - P |
| P_z^(ell) | `P_z^{(\ell)}` | Projector onto eigenstate ell |
| I | `I` | Identity operator |
| P_{x_l} | `P_{x_l}` | Projector: (I - sigma_z)/2 |
| P_{bar x_l} | `P_{\overline{x}_l}` | Projector: (I + sigma_z)/2 |

### F. Eigenvalues of H(s)

| Notation | LaTeX | Description |
|----------|-------|-------------|
| lambda(s) | `\lambda(s)` | Generic eigenvalue of H(s) |
| lambda_0(s) | `\lambda_0(s)` | Ground state eigenvalue |
| lambda_1(s) | `\lambda_1(s)` | First excited eigenvalue |

### G. Eigenvalues of H_z (Problem Hamiltonian)

| Notation | LaTeX | Description |
|----------|-------|-------------|
| E_k | `E_k` | k-th distinct eigenvalue |
| E_0 | `E_0` | Ground state energy (normalized to 0) |
| E_1 | `E_1` | First excited energy |
| E_{M-1} | `E_{M-1}` | Highest eigenvalue |
| E_z | `E_z` | Eigenvalue corresponding to bitstring z |

### H. Spectral Gap Parameters

| Notation | LaTeX | Description |
|----------|-------|-------------|
| Delta | `\Delta` | Spectral gap of H_z: E_1 - E_0 |
| Delta_k | `\Delta_k` | Gap: E_k - E_0 |
| g(s) | `g(s)` | Spectral gap of H(s) |
| g_0(s) | `g_0(s)` | Lower bound on g(s) |
| g_min | `g_{\min}` | Minimum spectral gap of H(s) |

### I. Degeneracies and Dimensions

| Notation | LaTeX | Description |
|----------|-------|-------------|
| d_k | `d_k` | Degeneracy of eigenvalue E_k |
| d_0 | `d_0` | Ground state degeneracy |
| d'_0 | `d'_0` | Modified ground state degeneracy |
| M | `M` | Number of distinct eigenvalues |
| N | `N` | Total dimension: 2^n |
| n | `n` | Number of qubits |

### J. Spectral Parameters A_p

| Notation | LaTeX | Definition |
|----------|-------|------------|
| A_p | `A_p` | (1/N) sum_{k=1}^{M-1} d_k / (E_k - E_0)^p |
| A_1 | `A_1` | Spectral parameter p=1 |
| A_2 | `A_2` | Spectral parameter p=2 |
| A_3 | `A_3` | Spectral parameter p=3 |
| A_1(H) | `A_1(H)` | A_1 for Hamiltonian H |
| tilde A_1(H) | `\widetilde{A}_1(H)` | Approximation of A_1 |

### K. Avoided Crossing Position

| Notation | LaTeX | Definition |
|----------|-------|------------|
| s^* | `s^*` | Position: A_1 / (A_1 + 1) |
| delta_s | `\delta_s` | Half-width: (2/(A_1+1)^2) sqrt(d_0 A_2 / N) |

### L. Intervals

| Notation | LaTeX | Definition |
|----------|-------|------------|
| I_{s leftarrow} | `\mathcal{I}_{s^{\leftarrow}}` | [0, s^* - delta_s) |
| I_{s^*} | `\mathcal{I}_{s^*}` | [s^* - delta_s, s^* + delta_s] |
| I_{s rightarrow} | `\mathcal{I}_{s^{\rightarrow}}` | (s^* + delta_s, 1] |

### M. Schedule and Time Parameters

| Notation | LaTeX | Description |
|----------|-------|-------------|
| s | `s` | Schedule parameter in [0,1] |
| s(t) | `s(t)` | Schedule function |
| K(s) | `K(s)` | Time as function of schedule |
| K'(s) | `K'(s)` | Derivative of schedule |
| T | `T` | Total evolution time |
| t | `t` | Physical time |

### N. Error and Fidelity

| Notation | LaTeX | Description |
|----------|-------|-------------|
| varepsilon | `\varepsilon` | Error/infidelity |
| epsilon | `\epsilon` | DO NOT USE (use varepsilon) |
| nu(s) | `\nu(s)` | Adiabatic error bound |

### O. Resolvent and Gap Bounds

| Notation | LaTeX | Description |
|----------|-------|-------------|
| R_A(gamma) | `R_A(\gamma)` | Resolvent: (gamma I - A)^{-1} |
| R_{H(s)}(gamma) | `R_{H(s)}(\gamma)` | Resolvent of H(s) |
| gamma(s) | `\gamma(s)` | Reference line for resolvent |
| beta(s) | `\beta(s)` | Offset: a(s - s_0)/(1 - s_0) |
| s_0 | `s_0` | Auxiliary parameter for reference line |
| a | `a` | Slope parameter: 4k^2 Delta/3 |
| k | `k` | Constant: 1/4 |
| f(s) | `f(s)` | Monotonically decreasing bound function |

### P. Eigenvalue Corrections Near AC

| Notation | LaTeX | Description |
|----------|-------|-------------|
| delta_+(s) | `\delta_+(s)` | Ground state correction |
| delta_-(s) | `\delta_-(s)` | First excited correction |
| delta_0^+(s) | `\delta^+_0(s)` | Approximation to delta_+ |
| delta_0^-(s) | `\delta^-_0(s)` | Approximation to delta_- |
| eta | `\eta` | Small constant (= 0.1) |

### Q. Spectral Condition Constants

| Notation | LaTeX | Description |
|----------|-------|-------------|
| c | `c` | Small constant (< 0.02) |
| kappa | `\kappa` | Scaling constant |
| kappa' | `\kappa'` | Scaling: (1+2c)/(1-2c) sqrt(1+(1-2c)^2) |

### R. Sets and Spaces

| Notation | LaTeX | Description |
|----------|-------|-------------|
| H (calligraphic) | `\mathcal{H}` | Hilbert space |
| H_S | `\mathcal{H}_S` | Symmetric subspace (dim M) |
| H_S^perp | `\mathcal{H}^{\perp}_S` | Orthogonal complement |
| Omega_k | `\Omega_k` | Bitstrings with eigenvalue E_k |
| {0,1}^n | `\{0,1\}^n` | n-bit strings |
| [0,1] | `[0,1]` | Unit interval |
| [k] | `[k]` | Set {0,1,...,k} or {1,...,k} context-dependent |
| Z | `\mathbb{Z}` | Integers |
| N | `\mathbb{N}` | Natural numbers |
| R | `\mathbb{R}` | Real numbers |
| C | `\mathbb{C}` | Complex numbers |
| R^+ | `\mathbb{R}^+` | Positive reals |
| sigma(H) | `\sigma(H)` | Spectrum of H |
| F | `\mathbb{F}` | Generic field |

### S. Asymptotic Notation

| Notation | LaTeX | Usage |
|----------|-------|-------|
| O(f) | `O(f)` or `\bigO{f}` | Upper bound |
| Omega(f) | `\Omega(f)` | Lower bound |
| Theta(f) | `\Theta(f)` | Tight bound |
| o(f) | `o(f)` or `\littleo{f}` | Strictly smaller |
| O tilde(f) | `\widetilde{O}(f)` or `\bigOt{f}` | O hiding polylog |
| poly(n) | `\poly(n)` | Polynomial in n |
| polylog(n) | `\polylog(n)` | Polylogarithmic |

### T. Boolean SAT Notation

| Notation | LaTeX | Description |
|----------|-------|-------------|
| x_i | `x_i` | Boolean variable |
| bar x_i | `\bar{x}_i` or `\overline{x}_i` | Negation |
| lor | `\lor` | Boolean OR |
| land | `\land` | Boolean AND |
| F | `F` | Boolean formula |
| a_k, b_k, c_k | `a_k`, `b_k`, `c_k` | Literals in clause |
| m | `m` | Number of clauses |

### U. Hardness Proof Notation

| Notation | LaTeX | Description |
|----------|-------|-------------|
| C_varepsilon | `\mathcal{C}_\varepsilon` | Classical procedure |
| mu_1, mu_2 | `\mu_1`, `\mu_2` | Threshold parameters |
| f(x) | `f(x)` | Function for polynomial interpolation |
| P(x) | `P(x)` | Polynomial for extracting degeneracies |
| tilde P(x) | `\widetilde{P}(x)` | Approximate polynomial |
| D(x_i) | `D(x_i)` | Error bound |
| deg(P) | `\mathrm{deg}(P)` | Degree of polynomial |

### V. IQP and Quantum Circuits

| Notation | LaTeX | Description |
|----------|-------|-------------|
| C_{IQP} | `\mathcal{C}_{IQP}` | IQP circuit |
| e^{i pi/8 H} | `e^{i\frac{\pi}{8}H_\sigma}` | IQP unitary |

### W. Calculus Operators

| Notation | LaTeX | Description |
|----------|-------|-------------|
| d/ds | `\od{}{s}` or `d/ds` | Total derivative |
| partial/partial s | `\partial/\partial s` | Partial derivative |
| H'(s) | `H'(s)` | First derivative of H |
| H''(s) | `H''(s)` | Second derivative of H |
| f'(s) | `f'(s)` | Derivative of f |
| u', v' | `u'`, `v'` | Derivatives in proof |
| integral | `\int_0^1 ds` | Integral |
| sum | `\sum_k` | Summation |
| prod | `\prod_k` | Product |

### X. Adiabatic Theorem (Appendix)

| Notation | LaTeX | Description |
|----------|-------|-------------|
| (H^+)' | `(H^+)'` | Derivative of pseudoinverse |
| P_H | `P_H` | Projector onto ground space of H |
| Q_H | `Q_H` | Complement projector: I - P_H |
| Gamma | `\Gamma` | Contour circle in complex plane (Riesz) |
| R_H(z) | `R_H(z)` | Resolvent at complex z |
| z | `z` | Complex variable in Riesz formula |
| B_1, B_2 | `B_1`, `B_2` | Integral bounds for schedule |
| p | `p` | Schedule parameter: 1 <= p <= 2 |
| b | `b` | Shrinking factor: 1/10 |
| varepsilon_0 | `\varepsilon_0` | Actual error of algorithm |
| P' | `P'` | Derivative of projector |
| P'' | `P''` | Second derivative of projector |

### Y. Projector and Derivative Bounds

| Notation | LaTeX | Description |
|----------|-------|-------------|
| norm P' | `\lVert P'\rVert` | Norm of projector derivative |
| norm P'' | `\lVert P''\rVert` | Norm of second derivative |
| norm H' | `\lVert H'\rVert` | Norm of Hamiltonian derivative |
| norm H'' | `\lVert H''\rVert` | Norm of second Hamiltonian derivative |
| g' | `g'` | Derivative of gap function |
| abs g' | `\|g'\|` | Absolute value of gap derivative |
| sup_s | `\sup_{s\in[0,1]}` | Supremum over s |

### Z. Miscellaneous

| Notation | LaTeX | Description |
|----------|-------|-------------|
| tensor | `\otimes` | Tensor product |
| oplus | `\oplus` | Direct sum |
| dagger | `^\dagger` | Conjugate transpose |
| + (pseudoinverse) | `^+` | Moore-Penrose pseudoinverse |
| ^{-1} | `^{-1}` | Matrix inverse |
| QED | `\QEDB` | End of proof |
| J_{ij} | `J_{ij}` | Ising coupling constant |
| h_j | `h_j` | Ising local field |
| langle i,j rangle | `\langle i,j\rangle` | Edge/neighbor notation |
| alpha_k | `\alpha_k` | Eigenstate coefficients |
| gamma | `\gamma` | Overlap: bra psi_0 ket psi |
| ell | `\ell` | Index variable |
| rho | `\rho` | Density matrix |
| h | `h` | Limit variable (lim h->0) |
| u, v | `u`, `v` | Auxiliary proof variables |
| diff s | `\diff{s}` | Differential element |
| oint | `\oint_\Gamma` | Contour integral |
| 2 pi i | `2\pi i` | Complex factor in Riesz |
| r | `r` | Parameter in time-independent Ham |

### AA. Citation Conventions

| Format | Example |
|--------|---------|
| arXiv refs | `arXiv:quant-ph/0001106` |
| DOI | `\path{doi:10.1137/...}` |
| URLs | `\url{https://...}` |
| Journal style | Italicized journal name |
| In-text cite | `\cite{farhi2000adiabatic}` or `Ref.~\cite{...}` |
| Multi-cite | `\cite{key1, key2}` |

### BB. Theorem Environment Names

| Environment | Usage |
|-------------|-------|
| theorem | Main theorems (numbered) |
| lemma | Supporting lemmas |
| corollary | Direct consequences |
| definition | Formal definitions |
| assumption | Problem assumptions |
| claim | Claims within proofs |
| remark | Explanatory notes |
| fact | Known facts |
| prop | Propositions |
| inputmod | Input model spec |
| problem | Problem statements |

### CC. Key Equation Labels

| Label | Content |
|-------|---------|
| `eq:spectral-parameters` | A_p definition |
| `eq:spectral-condition` | Spectral condition on Delta |
| `eq:general-H(s)` | Adiabatic Hamiltonian |
| `eq:position-ac` | s^* = A_1/(A_1+1) |
| `eq:interval-ac` | delta_s definition |
| `eq:min-gap` | g_min formula |
| `eq:Ising_Ham` | Ising Hamiltonian H_sigma |
| `eq:resolvent-definition` | Resolvent R_A(gamma) |
| `eq:sherman-morrison` | Sherman-Morrison formula |
| `eq:summation-equality` | Eigenvalue condition |
| `eq:delta_0` | delta_0^pm formula |
| `eq:adiabatic-time` | Running time T |

### Common Inconsistencies to Flag

| Wrong | Correct | Note |
|-------|---------|------|
| `$\epsilon$` | `$\varepsilon$` | Always use varepsilon |
| `$s^{\star}$` | `$s^*$` | Use asterisk not star |
| `$g_{min}$` | `$g_{\min}$` | Use backslash min |
| `$\mathbb{H}$` | `$\mathcal{H}$` | Hilbert space is calligraphic |
| `$H_{problem}$` | `$H_z$` or `$H_P$` | Use canonical names |
| `$\Delta E$` | `$\Delta$` | Gap symbol alone |
| `$A_1, A_2$` | `$A_1$`, `$A_2$` | Each in own math mode if in text |
| `\lvert x \rvert` | `\ket{x}` | Use braket package |
| `_` outside math | `\_` or `$H_0$` | Escape or use math mode |

Note: The paper uses `$$..$$` for display math throughout, so this convention is acceptable.

### Notation Verification Procedure

**Manual check for common violations:**

```bash
# Check for epsilon instead of varepsilon
grep -rn '\\epsilon[^_]' src/chapters/*.tex

# Check for star instead of asterisk in s^*
grep -rn 's\^{\\star}' src/chapters/*.tex

# Check for g_{min} instead of g_{\min}
grep -rn 'g_{min}' src/chapters/*.tex

# Check for blackboard H instead of calligraphic
grep -rn '\\mathbb{H}' src/chapters/*.tex
```

**Agent check procedure:**

When checking a file for notation consistency:

1. Scan for the common inconsistencies listed above
2. Verify Hamiltonian naming follows conventions (H_0, H_z, H_P, H(s))
3. Check spectral parameters use canonical forms (A_1, A_2, Delta, g(s))
4. Verify error terms use varepsilon not epsilon
5. Check avoided crossing notation uses s^* and delta_s
6. Do NOT flag standard symbol reuse across sections (e.g., varepsilon for error in one section and precision in another). Only flag when two meanings collide in the same proof, equation, or tightly coupled argument

## Criteria

### Notation Consistency

1. Same symbol means same thing within a single proof or theorem statement
2. Definitions appear before use
3. No symbol redefined with different meaning in the same local context (proof, theorem, or tightly coupled argument)
4. Standard notation from paper used
5. Reusing standard letters (varepsilon, delta, mu, eta, C, etc.) across different sections with locally clear meaning is standard mathematical practice and should not be flagged

### Mathematical Correctness

5. Theorems match paper statements exactly (bounds, conditions, conclusions)
6. Definitions match paper
7. Constants are correct (not approximated)
8. All conditions/assumptions stated

### Common Hallucination Patterns

- Off-by-one: `O(n)` vs `O(n-1)`, `>=` vs `>`
- Missing conditions: theorem requires X but X not stated
- Wrong constants: `A_1` vs `A_2`, factor of 2 errors
- Simplified bounds: `O(sqrt(N))` when paper says `O(sqrt(N/d_0))`
- Inverted inequalities

## Key Results to Verify

**Runtime:**
```
T = O((1/epsilon) * (sqrt(A_2)/(A_1(A_1+1) * Delta^2)) * sqrt(2^n/d_0))
```

**Gap bounds:**
```
g_min = (2*A_1/(A_1+1)) * sqrt(d_0/(A_2*N))
s* = A_1/(A_1+1)
delta_s = (2/(A_1+1)^2) * sqrt(d_0*A_2/N)
```

**Hardness:**
- NP-hard at precision `epsilon < 1/(72(n-1))`
- #P-hard with `O(poly(n))` exact queries

## Output Format

```
PASS: Math and notation verified

WARN: Minor issues
  - ch4.tex:87: Bound O(sqrt(N)), paper has O(sqrt(N/d_0)) - add note if d_0=1 assumed

FAIL: Errors
  - ch5.tex:42: g_min missing (A_1+1) denominator
  - ch3.tex uses "gamma" for gap, ch4.tex uses "g" - standardize
```
