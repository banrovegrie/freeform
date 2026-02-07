# Intermediate Hardness: Complexity of A_1 at Precision 2^{-n/2}

## Problem Statement

The paper proves two hardness results for approximating $A_1$. At inverse-polynomial precision ($\epsilon < 1/\mathrm{poly}(n)$), the problem is NP-hard via a local Hamiltonian reduction (Theorem 2). At exponential precision ($\epsilon = O(2^{-\mathrm{poly}(n)})$), the problem is #P-hard via polynomial interpolation and Paturi's lemma (Theorem 3). But the adiabatic algorithm needs $A_1$ at precision $\epsilon = 2^{-n/2}$, which falls strictly between these two regimes.

**Central Question**: What is the complexity of estimating $A_1$ to additive precision $2^{-n/2}$?


## Why Novel

The paper explicitly identifies this gap (Discussion, p.983):
> "It would be interesting to explore the precise complexity of estimating the position of the avoided crossing to the desired accuracy."

And more specifically (Section 3.2, p.962):
> "these proof techniques based on polynomial interpolation do not allow us to conclude anything about the hardness of the approximation of $A_1(H)$ up to the additive error tolerated by the adiabatic algorithm."

The algorithmically relevant precision $2^{-n/2}$ is exactly at the boundary where:
- The polynomial interpolation technique breaks down
- Classical brute force ($O(2^n/d_0)$ time) is too slow by a factor of $2^{n/2}$
- Quantum amplitude estimation achieves $O(2^{n/2})$ time

This places the problem at a classical-quantum separation.


## Results

**Status**: RESOLVED (7 theorems + 3 propositions)

### Theorem 1 (Polynomial Interpolation Barrier)
The polynomial interpolation technique of paper Section 3.2 requires precision $\epsilon = 2^{-n - O(M \log n)}$ to extract exact degeneracies. At $\epsilon = 2^{-n/2}$, the amplified error exceeds $1/2$ and rounding fails. The #P-hardness argument does not extend to precision $2^{-n/2}$.

### Theorem 2 (Quantum Algorithm for $A_1$)
There exists a quantum algorithm estimating $A_1$ to precision $\epsilon$ using $O(\sqrt{N} + 1/(\epsilon \cdot \Delta_1))$ queries. For $\epsilon = 2^{-n/2}$: $O(2^{n/2} \cdot \mathrm{poly}(n))$.

### Theorem 3 (Classical Query Lower Bound)
Any classical algorithm estimating $A_1$ to precision $\epsilon$ requires $\Omega(1/\epsilon^2)$ queries. At $\epsilon = 2^{-n/2}$: $\Omega(2^n)$.

### Corollary (Quadratic Separation)
Estimating $A_1$ to precision $2^{-n/2}$ exhibits a quadratic quantum-classical separation: $O(2^{n/2} \cdot \mathrm{poly}(n))$ quantum vs $\Omega(2^n)$ classical.

### Theorem 4 (Tight Quantum Query Complexity)
The quantum query complexity of $A_1$ estimation to precision $\epsilon$ is $\Omega(1/\epsilon)$, via reduction from approximate counting and the Heisenberg limit for quantum phase estimation. Combined with Theorem 2: the quantum query complexity at $\epsilon = 2^{-n/2}$ is $\Theta(2^{n/2})$. Both quantum and classical bounds are now tight:

| Model | Complexity | Source |
|-------|-----------|--------|
| Quantum | $\Theta(1/\epsilon)$ | Theorems 2 and 4 |
| Classical | $\Theta(1/\epsilon^2)$ | Theorem 3 and brute force |

### Theorem 5 (Computational Complexity Under ETH)
Under the Exponential Time Hypothesis, any classical algorithm estimating $A_1$ to precision $2^{-n/2}$ requires $2^{\Omega(n)}$ time. The quantum algorithm runs in $O(2^{n/2} \cdot \mathrm{poly}(n))$ time. This establishes a quadratic quantum speedup in the computational model (not just the query model), conditional on ETH.

### Theorem 6 (Generic Polynomial Extrapolation Barrier)
Any polynomial extrapolation scheme of degree $d$ that evaluates outside the interpolation interval has Lebesgue function $\Lambda_d(x^*) \ge 2^{d-1}$. This amplification is inherent: no rearrangement of interpolation nodes, no alternative polynomial basis, and no change of variables can circumvent it. The paper's specific construction is not uniquely vulnerable; the entire class of polynomial-interpolation-based reductions fails at $\epsilon = 2^{-n/2}$.

### Theorem 7 (Structure Irrelevance)
For every $M \ge 2$ and every gap structure, there exist diagonal Hamiltonians for which $A_1$ estimation to precision $\epsilon$ requires $\Omega(1/\epsilon)$ quantum queries and $\Omega(1/\epsilon^2)$ classical queries. The sum-of-reciprocals structure of $A_1$ provides no worst-case advantage over generic mean estimation: $M = 2$ instances (where $A_1$ reduces to approximate counting) are the hardest case.

### Proposition 8 (Precision Phase Diagram)
Complexity as a function of precision $\epsilon$ is now explicit. In the core query family, complexity scales continuously as $\Theta(1/\epsilon)$ quantum and $\Theta(1/\epsilon^2)$ classical. Regime values:
- $\epsilon = \Theta(1)$: trivial constant-precision approximation
- $\epsilon = 1/\mathrm{poly}(n)$: NP-hard computationally (paper Theorem 2)
- $\epsilon = 2^{-cn}$, $0 < c < 1/2$: quantum $\Theta(2^{cn})$, classical $\Theta(2^{2cn})$
- $\epsilon = 2^{-n/2}$: quantum $\Theta(2^{n/2})$, classical $\Theta(2^n)$
- $\epsilon = 2^{-cn}$, $c > 1/2$: same query scaling, and #P-hard once $cn$ exceeds the paper's interpolation threshold; below that threshold the computational status remains open
- $\epsilon = 2^{-\mathrm{poly}(n)}$: #P-hard (paper Theorem 3)

### Proposition 9 (Structured Families, via Experiment 08)
Theorem 7 is worst-case over unrestricted diagonal Hamiltonians, so it does not automatically transfer to restricted structured families. For bounded treewidth local energies (Exp 08, Proposition 8), $A_1$ is exactly computable in polynomial time (for bounded/logarithmic width), so precision $2^{-n/2}$ is also polynomial-time tractable. For ferromagnetic Ising with consistent fields (Exp 08, Proposition 13), the reduction requires $\mu \le \eta/(6B)$; at $\eta = 2^{-n/2}$ this forces $1/\mu = \Omega(B2^{n/2})$, so under the standard per-query dependence $\mathrm{poly}(n,1/\mu,\log(1/\delta))$ the induced method is not polynomial-time at schedule precision.

### Proposition 10 (Promise-Time Characterization)
At precision $\epsilon$, the natural containment is parameterized:
$\mathrm{A1\mbox{-}EST}_\epsilon \in \mathrm{FBQTIME}(\sqrt{N} + 1/(\epsilon\Delta_1)\cdot \mathrm{poly}(n))$ (Theorem 2), with core lower bound $\Omega(1/\epsilon)$ (Theorem 4). At $\epsilon = 2^{-n/2}$ this gives $\mathrm{FBQTIME}(2^{n/2}\mathrm{poly}(n))$, so the natural description is parameterized-time rather than PromiseBQP-type polynomial-time behavior in the query model.


## Complete Complexity Landscape

**Query complexity at $\epsilon = 2^{-n/2}$** (tight, for $\Delta_1 = \Theta(1)$):

| Model | Lower Bound | Upper Bound | Source |
|-------|-------------|-------------|--------|
| Quantum | $\Omega(2^{n/2})$ | $O(2^{n/2})$ | Thms 4, 2 |
| Classical | $\Omega(2^n)$ | $O(2^n)$ | Thm 3, brute force |

**Precision-dependent core query scaling**:

| Model | Complexity in $\epsilon$ | Source |
|-------|---------------------------|--------|
| Quantum | $\Theta(1/\epsilon)$ | Thm 4 + Thm 2 (core family) |
| Classical | $\Theta(1/\epsilon^2)$ | Thm 3 + sampling upper bound |

**Computational complexity** (under ETH):

| Model | Time | Source |
|-------|------|--------|
| Quantum | $O(2^{n/2} \cdot \mathrm{poly}(n))$ | Thm 2 |
| Classical | $2^{\Omega(n)}$ | Thm 5 |

**Proof technique barrier**: Polynomial extrapolation requires precision $2^{-\Omega(d)}$ for degree-$d$ interpolation (Thm 6). At $d = \mathrm{poly}(n)$, the required $\epsilon = 2^{-\Omega(n)}$ is exponentially below $2^{-n/2}$.


## Proof Techniques

### Barrier Analysis (Theorems 1, 6)

The paper's #P-hardness proof (Section 3.2) constructs an auxiliary Hamiltonian $H'(x)$, defines a function $f(x) = 2A_1(H'(x)) - A_1(H)$, and forms a reconstruction polynomial $P(x)$ of degree $M - 1$. Error amplification from oracle noise to degeneracy error grows as $2^{O(M \log n)}$. Theorem 6 proves this is inherent: any polynomial extrapolation outside the interpolation interval amplifies by at least $2^{d-1}$ (from the Lebesgue function lower bound for extrapolation).

### Quantum Mean Estimation (Theorem 2)

$A_1$ is the mean of $g(x) = 1/(E_x - E_0)$ over the uniform distribution. Rescaling to $h(x) = \Delta_1 \cdot g(x) \in [0,1]$ and applying amplitude estimation (Brassard-Hoyer-Mosca-Tapp 2002) estimates the mean to precision $\delta$ in $O(1/\delta)$ applications of a quantum oracle. Ground energy $E_0$ is found via Durr-Hoyer quantum minimum finding in $O(\sqrt{N})$ queries.

### Tight Quantum Lower Bound (Theorem 4)

For $M = 2$, $A_1$ estimation is equivalent to approximate counting (estimating $|S|/N$ for a hidden set $S$). The quantum lower bound $\Omega(1/\epsilon)$ follows from the Heisenberg limit for phase estimation: the Grover iterate encodes $|S|/N$ in its eigenphase, and estimating an eigenphase to precision $\delta$ requires $\Omega(1/\delta)$ applications (Giovannetti-Lloyd-Maccone 2006, quantum Cramer-Rao bound).

### Classical Lower Bound (Theorem 3)

Adversarial instances where $|S| = N/2$ vs $|S| = N/2 + t$ reduce $A_1$ estimation to hypothesis testing under hypergeometric sampling. Le Cam's two-point method with KL divergence gives $\Omega(1/\epsilon^2)$ queries.

### ETH Computational Bound (Theorem 5)

The paper's NP-hardness reduction from 3-SAT creates an $O(n)$-qubit Hamiltonian. Under ETH (3-SAT on $n$ variables requires $2^{\Omega(n)}$ time), the same lower bound applies to $A_1$ estimation. The quantum algorithm replaces oracle queries with circuit evaluations, running in $O(2^{n/2} \cdot \mathrm{poly}(n))$ time.

### Structure Irrelevance (Theorem 7)

Hard instances embed into any $M$-level structure by concentrating degeneracy in the first two levels. Higher levels contribute $O(\mathrm{poly}(n)/2^n) = o(2^{-n/2})$ to $A_1$, invisible at precision $2^{-n/2}$.


## Why $2^{-n/2}$?

The paper's optimal local schedule (Section 2.2) parameterizes the avoided crossing at $s^* = A_1/(A_1 + 1)$. The gap remains $\Theta(g_{\min})$ throughout an interval $[s^* - \delta_s, s^* + \delta_s]$ where $\delta_s = \frac{2}{(A_1+1)^2}\sqrt{d_0 A_2/N}$. The required precision in $A_1$ is $\delta_s \cdot (A_1+1)^2 = 2\sqrt{d_0 A_2/N}$, which depends on $d_0, A_2, N$ but not on $A_1$ itself. For the worst case $d_0 = O(1)$ and $A_2 = O(1)$: the required precision is $O(\sqrt{1/N}) = O(2^{-n/2})$.


## Open Questions (Revised)

1. Can $\mathrm{A1\mbox{-}EST}_{2^{-n/2}}$ be shown complete for a natural parameterized promise/function class (beyond the current $\mathrm{FBQTIME}(2^{n/2}\mathrm{poly}(n))$ characterization)?
2. Can a non-interpolation reduction establish #P-hardness at $\epsilon = 2^{-n/2}$? (Theorems 1 and 6 rule out polynomial extrapolation only.)
3. Which additional structured families from Experiment 08 admit exact or schedule-precision polynomial-time $A_1$ estimation beyond bounded treewidth?
4. Can one prove tight computational lower bounds for the quantum side (not only query lower bounds), matching the $\Theta(1/\epsilon)$ query law?


## Connection to Other Experiments

- **Experiment 08 (structured tractability v2):** Proposition 9 closes the loop. Bounded-treewidth families keep $A_1$ tractable even at schedule precision, while ferromagnetic partition-function approximations are polynomial only at coarser precision unless stronger structure is present.
- **Experiment 10 (information-theoretic):** Proposition 8 supplies the quantitative precision curve behind the information-runtime narrative: each additional bit of $A_1$ precision doubles classical effort and gives a quadratic quantum advantage in the core model.
- **Experiment 12 (circumventing barrier):** Since Hamiltonian modifications do not remove $A_1$ dependence in the rank-one framework, the intermediate-hardness complexity map becomes operationally central.
- **Experiment 05 (adaptive schedules):** Adaptive measurement bypasses pre-computing $A_1$; this experiment quantifies the cost when one chooses estimation instead.
- **Experiment 04 (separation theorem):** The $\epsilon = 2^{-n/2}$ point gives the concrete numerical bridge between ignorance penalties and computable schedule information.


## Chapter 9 Integration Plan

Placement follows `README.md` Chapter 9 ("Information Gap"), between
"The Ignorance Taxonomy" and "Central Claim", with a short bridge from
the partial-information section.

1. **Subsection: Precision Phase Diagram for $A_1$**
   Use Proposition 8 table as the chapter's complexity-vs-precision figure.
   Message: query scaling is smooth in $\epsilon$, but proof techniques bifurcate at
   $\epsilon = 2^{-n/2}$.
2. **Subsection: Intermediate Precision as the Operational Threshold**
   Insert Theorems 1-4 summary: interpolation barrier + tight
   $\Theta(2^{n/2})$ vs $\Theta(2^n)$ query bounds.
3. **Bridge paragraph to the Central Claim**
   "The information cost of AQO is not only NP-hard at coarse precision;
   at schedule precision it is quantitatively a quadratic quantum-classical
   separation."
4. **Structured-family caveat box (cross-ref Exp 08)**
   Insert Proposition 9 to separate worst-case hardness from tractable
   structured subclasses.
5. **Open-problem handoff**
   Move promise-class completeness and non-interpolation #P-hardness targets
   to Chapter 11 open problems.


## References

1. Paper Section 3.1 - NP-hardness of A_1 at inverse-polynomial precision
2. Paper Section 3.2 - Paturi amplification and its limitations
3. Paper Discussion, p.983 - Explicit open problem on precision complexity
4. Durr-Hoyer 1996 - Quantum minimum finding
5. Brassard-Hoyer-Mosca-Tapp 2002 - Quantum amplitude estimation
6. Paturi 1992 - Polynomial interpolation amplification lemma
7. Giovannetti-Lloyd-Maccone 2006 - Quantum metrology / Heisenberg limit
8. Impagliazzo-Paturi 2001 - Exponential Time Hypothesis


## Status

**Phase**: Resolved

Seven theorems and three integration propositions now cover the experiment goals:

1. **Tight query complexity** (Theorems 2-4): $\Theta(2^{n/2})$ quantum, $\Theta(2^n)$ classical. Both bounds tight.
2. **Computational complexity** (Theorem 5): Under ETH, quadratic quantum speedup holds in the computational model.
3. **Generic proof barrier** (Theorems 1, 6): Polynomial extrapolation inherently requires $\epsilon = 2^{-\Omega(n)}$. New proof ideas needed for #P-hardness at $2^{-n/2}$.
4. **Structure irrelevance** (Theorem 7): $M = 2$ instances are worst-case. The sum-of-reciprocals structure of $A_1$ cannot be exploited.
5. **Precision landscape** (Proposition 8): full complexity-vs-precision diagram, including intermediate $2^{-cn}$ regimes.
6. **Structured-family bridge** (Proposition 9): explicit compatibility/incompatibility with Experiment 08 tractability results.
7. **Promise-time framing** (Proposition 10): precise parameterized class statement for the $2^{-n/2}$ regime.
8. **Lean formalization (core discrete skeleton)**: machine-checked scaling lemmas for Propositions 8-10 in `lean/`.

**Novelty assessment**: Theorem 4 (tight quantum bound via approximate counting equivalence) and Theorem 5 (ETH-conditional computational speedup) are the primary novel contributions. Theorem 6 (generic extrapolation barrier) provides a structural insight beyond the paper's specific construction. Theorem 7 (structure irrelevance) closes a natural question.

**Open problem note**: Directly addresses the paper's explicit open problem (Discussion, p.983; Section 3.2, p.962). The answer is now two-layered: query complexity varies smoothly with precision, but $\epsilon = 2^{-n/2}$ is the structural boundary where interpolation-based #P-hardness arguments fail and schedule-level information cost becomes explicit.

Full proofs in proof.md, numerical verification in `lib/verify.py` and
`lib/deep_verify.py`, and stress verification in `lib/robust_verify.py`.


## Lean Verification

Formalization is now included at:

- `src/experiments/13_intermediate_hardness/lean/IntermediateHardness/Basic.lean`
- `src/experiments/13_intermediate_hardness/lean/IntermediateHardness/PhaseDiagram.lean`
- `src/experiments/13_intermediate_hardness/lean/IntermediateHardness/BarrierGrid.lean`
- `src/experiments/13_intermediate_hardness/lean/IntermediateHardness/StructuredBridge.lean`
- `src/experiments/13_intermediate_hardness/lean/IntermediateHardness/PromiseTime.lean`
- `src/experiments/13_intermediate_hardness/lean/IntermediateHardness.lean`

Scope of formalization:

1. Core grid scaling: $\epsilon_k = 2^{-k}$, $Q(\epsilon_k)=2^k$, $C(\epsilon_k)=2^{2k}$, $C/Q=2^k$, with one-bit refinement laws $Q_{k+1}=2Q_k$ and $(C/Q)_{k+1}=2(C/Q)_k$.
2. Threshold specialization: $k = n/2$ (schedule-relevant precision point).
3. Schedule-barrier symbolic proof on the grid: `scheduleErrorProxy_gt_half` proves the proxy inequality for all exponents.
4. Schedule-barrier finite certificate: `barrierAllUpTo_1024` machine-checks the proxy inequality on exponents $0,\ldots,1024$.
5. Structured bridge core: exact estimators and inverse-precision runtime specialization.
6. Promise-time core: constant-factor lower/upper matching on the precision grid.

Reproducible commands:

```bash
cd src/experiments/13_intermediate_hardness/lean
lake build
lake env lean IntermediateHardness.lean
```

Additional stress verification:

```bash
python3 src/experiments/13_intermediate_hardness/lib/robust_verify.py
```

This suite includes randomized stress checks and an exhaustive small-parameter
barrier sweep (2572 distinct integer-gap instances).
