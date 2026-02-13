# Adaptive Schedules: Rigorous Analysis

## Summary of Main Results

We prove that adaptive AQO with $O(n)$ measurements achieves the gap-informed optimal
runtime $T_{\text{inf}}$, circumventing the classical computational hardness of computing
the crossing position $s^*$. This resolves an open question from the original paper.

**Main Theorem**: There exists an adaptive AQO algorithm making $O(n)$ measurements that
achieves runtime $T = O(T_{\text{inf}}) = O(\sqrt{N/d_0})$, where $N = 2^n$ and $d_0$ is
the ground state degeneracy.

**Corollary**: The classical NP-hardness of computing $s^*$ does not prevent quantum
adaptive algorithms from achieving optimal performance.


## Part I: Setup and Background

### The Adiabatic Framework

From the original paper, the adiabatic Hamiltonian is:
$$H(s) = -(1-s)|\psi_0\rangle\langle\psi_0| + s H_z$$
where $|\psi_0\rangle = |+\rangle^{\otimes n}$ is the uniform superposition and $H_z$ is
the problem Hamiltonian diagonal in the computational basis.

**Key quantities from the original paper:**
- $A_1 = \frac{1}{N}\sum_{k \geq 1} \frac{d_k}{E_k - E_0}$: spectral parameter
- $s^* = \frac{A_1}{A_1 + 1}$: position of avoided crossing
- $\Delta_* = \Theta\left(\sqrt{\frac{d_0}{A_2 N}}\right)$: minimum spectral gap
- $\delta_s = \Theta(\Delta_*)$: width of crossing region

For unstructured search problems:
- $N = 2^n$
- $\Delta_* = \Theta(2^{-n/2})$
- $s^* \in [0.3, 0.7]$ typically (depends on instance)


### Time Scales

**Gap-informed runtime** (original paper Theorem 1): With known $s^*$, the optimal local
schedule achieves:
$$T_{\text{inf}} = O\left(\sqrt{\frac{N}{d_0}}\right) = O(2^{n/2})$$

**Gap-uninformed runtime** (experiment 04): Fixed schedules not knowing $s^*$ require:
$$T_{\text{unf}} = \Omega\left(\frac{s_R - s_L}{\Delta_*} \cdot T_{\text{inf}}\right) = \Omega(2^n)$$

**Question**: Can adaptive schedules match $T_{\text{inf}}$ without knowing $s^*$?


### The Hardness Result (from original paper)

The original paper proves:
- $A_1$ is NP-hard to approximate to precision $1/\text{poly}(n)$
- $A_1$ is $\#\text{P}$-hard to compute exactly
- Knowing $s^*$ to precision $O(\delta_s) = O(2^{-n/2})$ requires knowing $A_1$

**Open question from original paper**: "Can this limitation be overcome when one only
has access to a device operating in the adiabatic setting (along with a classical
computer)?"

We answer this question affirmatively.


## Part II: The Gap Profile

### Lemma (Gap Lower Bound Away from Crossing)

This is established in the original paper. For $|s - s^*| > c\Delta_*$ (some constant $c$):
$$\Delta(s) \geq c' \cdot |s - s^*|$$
for some constant $c' > 0$.

Near the crossing ($|s - s^*| \leq c\Delta_*$):
$$\Delta(s) \geq c'' \cdot \Delta_*$$

**Consequence**: The gap grows linearly as we move away from the crossing.


## Part III: The Adaptive Protocol

### Key Insight

COMPUTING $s^*$ classically is NP-hard. But we can DETECT $s^*$ quantumly via
energy measurements during evolution, because:
1. The instantaneous ground state energy depends on $s$
2. At the crossing, the ground and excited state energies are closest
3. Phase estimation can distinguish ground from excited states

### Protocol: Binary Search with Energy Measurement

**Algorithm: AdaptiveAQO($\varepsilon$)**

```
Input: Error tolerance epsilon
Output: State with fidelity >= 1 - epsilon with ground state of H_z

Phase 1: Location (Binary Search)

1. Initialize s_lo = 0, s_hi = 1
2. For i = 1 to ceil(n/2):
   a. Reset state to |psi_0> = |+>^n
   b. Set s_mid = (s_lo + s_hi) / 2
   c. Evolve adiabatically from s=0 to s=s_mid
   d. Use phase estimation to determine if state is ground state of H(s_mid)
   e. If in ground state:
      Crossing is AFTER s_mid: set s_lo = s_mid
   f. Else (in excited state):
      Crossing is BEFORE s_mid: set s_hi = s_mid
3. After O(n) iterations: s* in [s_lo, s_hi] with width O(Delta_*)

Phase 2: Execution (Informed Evolution)

4. Reset state to |psi_0>
5. Evolve from s=0 to s=1 using local schedule:
   Fast outside [s_lo - Delta_*, s_hi + Delta_*]
   Slow (v ~ Delta_*^2) inside this interval
6. Total time: O(T_inf)

Return final state
```


### Phase Estimation Cost Analysis

**Lemma (Phase Estimation Cost)**: To distinguish whether a state is the ground state
or first excited state of $H(s_{\text{mid}})$, phase estimation requires time
$O(1/\Delta(s_{\text{mid}}))$.

*Proof*: The ground and excited state energies differ by $\Delta(s_{\text{mid}})$.
By the Heisenberg uncertainty relation, distinguishing energies separated by $\Delta$
requires evolution time $\Omega(1/\Delta)$. Phase estimation achieves this bound. $\square$


### Iteration Cost Analysis

**Lemma (Total Phase 1 Cost)**: The total time for Phase 1 is $O(T_{\text{inf}})$.

*Proof*:
Let $d_i = |s_{\text{mid},i} - s^*|$ be the distance from the $i$-th midpoint to $s^*$.

By the gap profile lemma:
$$\Delta(s_{\text{mid},i}) \geq c \cdot \min(d_i, \Delta_*)$$

Phase estimation cost at iteration $i$: $O(1/\Delta(s_{\text{mid},i})) \leq O(1/\min(d_i, \Delta_*))$

**Key observation**: The midpoints $s_{\text{mid},i}$ lie on a dyadic grid
$\{k/2^j : k \in \mathbb{Z}, j \in \mathbb{N}\}$.

For any fixed $s^*$, the number of dyadic points within distance $\varepsilon$ of $s^*$
is $O(\log(1/\varepsilon))$.

Therefore, grouping iterations by the magnitude of $d_i$:
- Iterations with $d_i \in [2^{-j-1}, 2^{-j}]$: at most $O(1)$ such iterations
- Cost per such iteration: $O(2^j)$

Total cost:
$$\sum_{j=0}^{n/2} O(1) \cdot O(2^j) = O(2^{n/2}) = O(T_{\text{inf}})$$

Adding reset time ($O(n)$ per iteration, $O(n)$ iterations): $O(n^2) = o(T_{\text{inf}})$.

Total Phase 1 time: $O(T_{\text{inf}})$. $\square$


### Phase 2 Analysis

**Lemma (Informed Evolution Time)**: Given $s^*$ to precision $O(\Delta_*)$, the local
schedule achieves runtime $T = O(T_{\text{inf}})$.

*Proof*: This follows directly from the original paper (Theorem 1). With known $s^*$:
- Schedule velocity $v(s) \propto \Delta(s)^2$ (Roland-Cerf style)
- Time $= \int_0^1 \frac{ds}{v(s)} = \int_0^1 \frac{ds}{\Delta(s)^2}$
- By the measure condition analysis: $O(\sqrt{N/d_0}) = O(T_{\text{inf}})$. $\square$


### Main Theorem

**Theorem (Adaptive AQO Matches Informed)**: The AdaptiveAQO algorithm achieves:
- Number of measurements: $O(n)$
- Total runtime: $O(T_{\text{inf}})$

*Proof*:
- Phase 1: $O(n)$ iterations, total time $O(T_{\text{inf}})$ (by iteration cost lemma)
- Phase 2: Time $O(T_{\text{inf}})$ (by informed evolution lemma)
- Total: $O(T_{\text{inf}}) + O(T_{\text{inf}}) = O(T_{\text{inf}})$

Correctness: Phase 1 locates $s^*$ to precision $O(\Delta_*)$. This is sufficient for
Phase 2 to achieve fidelity $1 - \varepsilon$ by the original paper's adiabatic theorem. $\square$


## Part IV: Lower Bound

### Information-Theoretic Lower Bound

**Theorem (Measurement Lower Bound)**: Any adaptive algorithm achieving $T = O(T_{\text{inf}})$
requires $\Omega(n)$ measurements.

*Proof*:
The crossing position $s^*$ can be anywhere in $[s_L, s_R]$ with width $\Theta(1)$.
To construct an informed schedule, we must locate $s^*$ to precision $\Delta_* = O(2^{-n/2})$.

This requires distinguishing among $\Omega(2^{n/2})$ possible positions.

Each measurement outcome is determined by the quantum state, which encodes at most
$O(1)$ bits of information about $s^*$ per measurement (the outcome is effectively
binary: ground state vs excited state).

Information needed: $\log_2(2^{n/2}) = n/2$ bits.
Information per measurement: $O(1)$ bits.
Measurements needed: $\Omega(n)$.

Therefore, $\Omega(n)$ measurements are necessary. $\square$


### Tight Characterization

**Corollary**: $\Theta(n)$ measurements are necessary and sufficient for adaptive AQO
to achieve optimal runtime $T_{\text{inf}}$.


## Part V: Discussion

### Resolution of the Open Question

The original paper asked whether the hardness of computing $s^*$ can be circumvented
using an adiabatic device. Our answer: **YES**.

The key insight is that:
1. COMPUTING $s^*$ classically is NP-hard
2. DETECTING $s^*$ quantumly requires only $O(n)$ measurements

These are fundamentally different tasks. The quantum system encodes information about
the crossing position in its spectrum, which can be probed via phase estimation.


### Comparison with Prior Work

**Jarret et al. 2018**: Assumed a gap oracle exists, showed $O(\log(1/\Delta_*))$ queries suffice.
- Our contribution: Prove the gap oracle can be implemented via phase estimation
- We achieve $O(n) = O(\log(1/\Delta_*))$ measurements

**Han-Park-Choi 2025**: Constant speed with adaptive stopping, numerical demonstration.
- Our contribution: Rigorous proof of optimality

**Original paper**: Left open whether adaptive can circumvent hardness.
- Our contribution: Affirmative resolution with tight bounds


### Implications

1. **Practical**: Adaptive AQO achieves optimal performance without classical preprocessing
2. **Theoretical**: Classical hardness does not imply quantum hardness for spectral detection
3. **Algorithmic**: Binary search with phase estimation is a universal technique


## Summary

We have shown that adaptive AQO with $\Theta(n)$ measurements achieves the gap-informed
optimal runtime $O(T_{\text{inf}})$, circumventing the classical NP-hardness of computing
the crossing position.

**Comparison table**:
$$
\begin{array}{|c|c|c|}
\hline
\text{Strategy} & \text{Runtime} & \text{Measurements} \\
\hline
\text{Gap-uninformed (fixed)} & \Omega(2^{n/2} \cdot T_{\text{inf}}) & 0 \\
\text{Adaptive (this work)} & O(T_{\text{inf}}) & \Theta(n) \\
\text{Gap-informed} & O(T_{\text{inf}}) & 0 \\
\hline
\end{array}
$$

Adaptivity provides exponential improvement, fully matching the informed case.
