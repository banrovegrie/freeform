# Adaptive Schedules: Fundamental Limits of Adaptive Probing

## Problem Statement

The gap-uninformed separation theorem (experiment 04) proves that any fixed schedule
not knowing the gap position requires $\Omega(2^{n/2})$ more time than informed schedules.
The original paper leaves open the question:

> "Can this limitation be overcome when one only has access to a device operating in
> the adiabatic setting (along with a classical computer)?"

We answer this question affirmatively.


## Why Novel

From comprehensive literature survey (see notes/literature_survey.md):

**What IS known**:
- Gap-informed optimal schedules achieve $T_{\text{inf}} = O(\sqrt{N/d_0})$ (Roland-Cerf 2002, original paper)
- Gap oracle model: $O(\log(1/\Delta_*))$ queries suffice (Jarret et al. 2018)
- Heuristic adaptive methods work numerically (Han-Park-Choi 2025, Shingu-Hatomura 2025)
- Computing $s^*$ classically is NP-hard (original paper)

**What is NOT known** (the gap we fill):
- Rigorous proof that adaptive AQO matches informed runtime
- Explicit protocol achieving this with proven complexity
- Lower bound on measurements needed
- Resolution of the open question from the original paper


## Main Results

### Theorem 1 (Adaptive Matches Informed)

There exists an adaptive AQO algorithm making $O(n)$ measurements that achieves:
$$T_{\text{adaptive}} = O(T_{\text{inf}}) = O\left(\sqrt{N/d_0}\right)$$

**Significance**: Adaptive AQO fully matches the gap-informed optimal runtime.
The classical NP-hardness of computing $s^*$ does not prevent quantum adaptive
algorithms from achieving optimal performance.

### Theorem 2 (Measurement Lower Bound)

Any adaptive algorithm achieving $T = O(T_{\text{inf}})$ requires $\Omega(n)$ measurements.

**Significance**: The $O(n)$ measurements in Theorem 1 are necessary. Binary search is optimal.

### Corollary (Complete Characterization)

$$
\begin{aligned}
T_{\text{uninformed}} &= \Omega(2^{n/2} \cdot T_{\text{inf}}) &&\text{[experiment 04]} \\
T_{\text{adaptive}} &= O(T_{\text{inf}}) &&\text{[this work]} \\
T_{\text{informed}} &= O(T_{\text{inf}}) &&\text{[original paper]}
\end{aligned}
$$

Adaptivity provides exponential improvement, fully matching the informed case
with $\Theta(n)$ measurements.


## The Protocol

### Binary Search with Phase Estimation

**Phase 1: Location** ($O(n)$ measurements, $O(T_{\text{inf}})$ time)
1. Binary search for crossing position $s^*$
2. Each iteration: adiabatic evolution to midpoint, phase estimation to check ground state
3. After $O(n)$ iterations: know $s^*$ to precision $O(\Delta_*)$

**Phase 2: Execution** ($O(T_{\text{inf}})$ time)
1. Use knowledge of $s^*$ to construct informed schedule
2. Evolve carefully, slow only near $[s^* - \Delta_*, s^* + \Delta_*]$
3. Achieve fidelity $1 - \varepsilon$ in time $O(T_{\text{inf}})$

**Key Insight**: Phase estimation can distinguish ground from excited state with
cost $O(1/\Delta(s))$. Summing over binary search iterations gives total $O(T_{\text{inf}})$.


## Technical Details

### Why This Works

1. **Classical vs Quantum Hardness**: COMPUTING $s^*$ classically is NP-hard, but
   DETECTING $s^*$ quantumly is efficient via phase estimation.

2. **Gap Profile**: The gap $\Delta(s) \geq c|s - s^*|$ away from the crossing.
   This means measurements far from $s^*$ are cheap.

3. **Dyadic Structure**: Binary search midpoints form a dyadic grid. For any $s^*$,
   only $O(1)$ midpoints are within distance $\varepsilon$ for each scale $\varepsilon$.

4. **Geometric Sum**: Total phase estimation cost is $\sum_j O(2^j) = O(2^{n/2})$,
   where $j$ indexes the distance scale.

### Why $\Omega(n)$ Measurements Are Necessary

- $s^*$ can be anywhere in $[s_L, s_R]$ with width $\Theta(1)$
- To locate $s^*$ to precision $\Delta_* = O(2^{-n/2})$, need $n/2$ bits of information
- Each measurement gives $O(1)$ bits (binary: ground vs excited)
- Measurements needed: $\Omega(n)$


## Connection to Other Experiments

- **04** (separation theorem): Establishes the uninformed lower bound we circumvent
- **07** (partial information): Related question about imprecise $A_1$ knowledge


## References

1. Original paper: Hardness of computing $s^*$ (Theorem 2, 3)
2. Roland-Cerf 2002: Local adiabatic evolution (quant-ph/0107015)
3. Guo-An 2025: Power-law scheduling (arxiv:2512.10329)
4. Han-Park-Choi 2025: Constant speed adaptive (arxiv:2510.01923)
5. Jarret-Lackey-Liu-Wan 2018: Gap oracle model (arxiv:1810.04686)


## Status

**Phase**: Complete

**Main contributions**:
1. Rigorous proof: Adaptive AQO achieves $T = O(T_{\text{inf}})$
2. Explicit protocol: Binary search with phase estimation
3. Lower bound: $\Omega(n)$ measurements necessary
4. Resolution of open question from original paper
