# Intermediate Hardness: Complexity of A_1 at Precision 2^{-n/2}

## Problem Statement

The paper proves that approximating $A_1$ to inverse-polynomial precision is NP-hard (via polynomial interpolation from Paturi's lemma). At exponential precision $2^{-\text{poly}(n)}$, the problem is #P-hard. But the adiabatic algorithm needs $A_1$ at precision $\epsilon = 2^{-n/2}$, which falls in a gap between these two regimes.

**Central Question**: What is the complexity of estimating $A_1$ to additive precision $2^{-n/2}$?


## Why Novel

The paper explicitly identifies this gap (Discussion, p.983):
> "It would be interesting to explore the precise complexity of estimating the position of the avoided crossing to the desired accuracy."

And more specifically (Section 3.2, p.962):
> "these proof techniques based on polynomial interpolation do not allow us to conclude anything about the hardness of the approximation of $A_1(H)$ up to the additive error tolerated by the adiabatic algorithm."

The algorithmically relevant precision $2^{-n/2}$ is exactly at the boundary where:
- The polynomial interpolation technique breaks down
- Classical brute force ($O(2^n/d_0)$ time) is too slow by a factor of $2^{n/2}$
- Quantum amplitude estimation might achieve $O(2^{n/2})$ time

This places the problem at a potential classical-quantum separation.


## Conjectures

### Conjecture 1 (Quantum Amplitude Estimation)
There exists a quantum algorithm that estimates $A_1$ to precision $2^{-n/2}$ in time $O(2^{n/2})$.

**Approach**: Encode $f(x) = 1/(E_x - E_0)$ as a quantum subroutine (via QPE on $H_z$), then use quantum mean estimation to compute
```
A_1 = (1/N) sum_x f(x) = E_x[f(x)]
```
Amplitude estimation gives precision $\epsilon$ in $O(1/\epsilon)$ evaluations. With $\epsilon = 2^{-n/2}$ this is $O(2^{n/2})$.

### Conjecture 2 (Classical Lower Bound)
Any classical algorithm estimating $A_1$ to precision $2^{-n/2}$ requires $\omega(2^{n/2})$ time (assuming standard complexity assumptions).

### Conjecture 3 (Intermediate Complexity)
$A_1$ estimation at precision $2^{-n/2}$ is in BQP but not in P. The problem sits strictly between the known hardness regimes:
```
1/poly(n): NP-hard
2^{-n/2}: BQP (conjectured), not in P (conjectured)
2^{-poly(n)}: #P-hard
```


## Approach

### Strategy 1: Analyze Barrier at 2^{-n/2}

**Polynomial interpolation fails**. Paturi's lemma amplifies NP-hardness from precision $1/\text{poly}(n)$ to $2^{-O(n^2)}$ via degree-$O(n)$ polynomial interpolation. But:
- The amplification factor is $2^{O(n^2)}$, reaching precision $2^{-O(n^2)}$
- To reach $2^{-n/2}$ from $1/\text{poly}$ would need interpolation degree $O(\sqrt{n})$
- Degree-$O(\sqrt{n})$ interpolation does not preserve NP-hardness (too few evaluation points)

**NP-hardness reduction blocked**. A reduction from an NP-hard promise problem would require the promise gap to be $2^{-n/2}$, but the local Hamiltonian problem has promise gap $1/\text{poly}(n)$.

### Strategy 2: Quantum Mean Estimation

The key observation: $A_1$ is a mean value
```
A_1 = E_{x ~ uniform}[1 / (E_x - E_0)]
```

To estimate this quantumly:
1. Prepare $|\psi_0\rangle = (1/\sqrt{N}) \sum_x |x\rangle$ (uniform superposition, easy)
2. Apply QPE on $H_z$ to get eigenvalue estimates
3. Compute $1/(E_x - E_0)$ into an ancilla register
4. Use amplitude estimation on the ancilla

The precision of QPE limits the inner computation, but with $O(\text{poly}(n))$ ancilla qubits, the precision is sufficient. The outer amplitude estimation then gives $A_1$ to precision $2^{-n/2}$ in $O(2^{n/2})$ total queries.

### Strategy 3: Classical Sampling Analysis

Classical approach: sample $x$ uniformly, evaluate $E_x = \langle x | H_z | x \rangle$, compute sample mean of $1/(E_x - E_0)$.

By Hoeffding's inequality, precision $\epsilon$ requires $O(1/\epsilon^2)$ samples. For $\epsilon = 2^{-n/2}$, this is $O(2^n)$ samples. Each sample costs $O(\text{poly}(n))$ to evaluate. Total: $O(2^n \cdot \text{poly}(n))$.

This is the brute-force bound. The question is whether classical algorithms can do better. Variance reduction helps if the variance of $1/(E_x - E_0)$ is small, but for general instances the variance can be $\Theta(1/\Delta^2)$, which does not help.


## Technical Details

### Precision Landscape

| Precision | Known Complexity | Technique |
|-----------|-----------------|-----------|
| $1/\text{poly}(n)$ | NP-hard | Direct reduction from partition function |
| $2^{-O(n)}$ | NP-hard | Paturi amplification (degree-$O(n)$ interpolation) |
| $2^{-n/2}$ | **Unknown** | Falls in the gap |
| $2^{-O(n^2)}$ | NP-hard | Paturi amplification (degree-$O(n^2)$ ... but actually $O(n)$ suffices to $2^{-O(n^2)}$) |
| $2^{-\text{poly}(n)}$ | #P-hard | Exact counting reduction |

The $2^{-n/2}$ regime is precisely where:
- Polynomial interpolation runs out of amplification power
- The adiabatic algorithm needs the answer
- Quantum speedup (quadratic over classical sampling) would suffice

### Why 2^{-n/2}?
The paper's runtime is $T = O(\sqrt{N/d_0}) = O(2^{n/2}/\sqrt{d_0})$. The schedule parameterization is $s^* = A_1/(A_1 + 1)$. An error $\delta$ in $s^*$ costs $O(\delta / g_{\min}^2)$ additional runtime. Since $g_{\min} = \Theta(2^{-n/2})$, we need $\delta = O(g_{\min}^2) = O(2^{-n})$ in $s^*$, which translates to $O(2^{-n/2})$ precision in $A_1$ (via the derivative $ds^*/dA_1 = 1/(A_1+1)^2 = \Theta(1)$).

### Connection to Experiment 05
Experiment 05 showed that adaptive measurement (binary search + QPE) achieves optimal runtime without knowing $A_1$ in advance. This is an alternative to estimating $A_1$ directly. The two approaches are complementary:
- Experiment 05: avoid computing $A_1$ entirely (adaptive)
- This experiment: compute $A_1$ quantumly (one-shot)

Both achieve $O(2^{n/2})$ total cost, but through different mechanisms.


## Results

**Status**: PROPOSED

No results yet. The main tasks are:
1. Formalize the polynomial interpolation barrier at $2^{-n/2}$
2. Verify the quantum amplitude estimation approach (Conjecture 1)
3. Investigate whether classical lower bounds can be proved


## Open Questions

1. Is there a classical algorithm for $A_1$ at precision $2^{-n/2}$ faster than $O(2^n)$?
2. Can the quantum amplitude estimation approach handle the division by $(E_x - E_0)$ when $\Delta$ is exponentially small?
3. Is the problem complete for some natural complexity class at precision $2^{-n/2}$?
4. Are there intermediate precisions (between $1/\text{poly}$ and $2^{-n/2}$) with sharp complexity transitions?


## Connection to Other Experiments

- Complements 05 (adaptive schedules): alternative approach to the A_1 barrier (estimate vs. bypass)
- Complements 12 (circumventing barrier): if circumvention fails, quantum estimation is the fallback
- Informs 08 (structured tractability): tractable A_1 at 2^{-n/2} would mean AQO is in BQP for those instances
- Relates to 04 (separation theorem): quantifies the information cost of gap-uninformed algorithms


## References

1. Paper Section 3.1 - NP-hardness of A_1 at inverse-polynomial precision
2. Paper Section 3.2 - Paturi amplification and its limitations
3. Paper Discussion, p.983 - Explicit open problem on precision complexity
4. Brassard-Hoyer-Mosca-Tapp 2002 - Quantum amplitude estimation
5. Paturi 1992 - Polynomial interpolation amplification lemma
6. Montanaro 2015 - Quantum speedup of Monte Carlo methods


## Status

**Phase**: Proposed

**Open problem note**: Directly addresses the paper's explicit open problem on the complexity of $A_1$ estimation at the algorithmically relevant precision. Also addresses Section 3.2's acknowledgment that polynomial interpolation techniques cannot reach this regime.

Next steps:
1. Formalize the polynomial interpolation barrier
2. Design quantum amplitude estimation circuit for $A_1$
3. Prove or refute classical lower bound at $2^{-n/2}$
4. Survey related intermediate-precision hardness results
