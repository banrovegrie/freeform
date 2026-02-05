# Schedule Optimality: Connecting Gap Profile to Variational Framework

## Problem Statement

The paper derives an optimal local schedule $K(s) \propto g(s)^2$ from the adiabatic condition and the Cauchy-Schwarz integral inequality. Guo-An (2025) independently develops a variational framework for power-law schedules $u'(s) \propto \Delta^p(u(s))$, proving $p = 3/2$ is optimal under a measure condition on the gap.

These are two approaches to the same optimization. Neither paper connects them.

**Central Questions**:
1. Does the paper's piecewise-linear gap profile satisfy Guo-An's measure condition?
2. What constant $C$ arises, and how does it depend on spectral parameters?
3. Does Guo-An's framework recover the paper's runtime $T = O(\sqrt{N A_2 / d_0})$?
4. Does $p = 3/2$ improve on the paper's $p = 2$ schedule?


## Why Novel

The paper predates Guo-An, so the connection cannot appear in either work. Experiment 06 established that the paper's gap has flatness $\alpha = 1$ (the boundary case for the measure condition). This experiment makes the connection explicit and extracts quantitative consequences.

Specifically:
- The paper computes $K(s) \propto g(s)^2$, which corresponds to $p = 2$ in Guo-An's parameterization
- Guo-An proves $p = 3/2$ is variationally optimal for gaps satisfying the measure condition
- The paper's gap satisfies the measure condition (as a corollary of $\alpha = 1$ from experiment 06)
- So $p = 3/2$ applied to the paper's Hamiltonian should match the asymptotic scaling with better constants


## Conjectures

### Conjecture 1 (Measure Condition Holds)
The gap profile $g(s)$ from the paper's spectral analysis satisfies the measure condition
```
mu({s in [0,1] : g(s) <= x}) <= C * x
```
with
```
C = O(A_2 / (A_1(A_1 + 1)) + 1/Delta)
```
computable from the spectral parameters $A_1$, $A_2$, $\Delta$.

### Conjecture 2 (Runtime Recovery)
Applying Guo-An's power-law theorem with the paper's gap profile recovers
```
T = O(sqrt(N * A_2 / d_0))
```
matching the paper's Theorem 2.5 (up to constant factors).

### Conjecture 3 (Optimal Power)
The paper's schedule corresponds to $p = 2$. Guo-An's optimal $p = 3/2$ gives the same asymptotic scaling $T = O(\sqrt{N A_2 / d_0})$ with an improved constant prefactor.

### Conjecture 4 (Grover Case)
For the Grover problem ($M = 2$, uniform spectrum): $C = O(1)$, matching Guo-An's exact computation.


## Approach

### Step 1: Compute Sublevel Set Measure
From the paper's gap bounds (Chapter 6):
- Left regime ($s < s^*$): $g(s) \geq c_L |s - s^*|$
- Crossing regime ($|s - s^*| < \delta$): $g(s) \geq g_{\min}$
- Right regime ($s > s^*$): $g(s) \geq c_R |s - s^*|$

The sublevel set $\{s : g(s) \leq x\}$ has measure at most $O(x / \min(c_L, c_R))$ for $x > g_{\min}$. This is linear in $x$, so $\alpha = 1$ and the measure condition holds.

### Step 2: Extract Constant C
The slopes $c_L$, $c_R$ are determined by spectral parameters:
- $c_L \sim A_1 (A_1 + 1) / A_2$ from the left-of-crossing derivative
- $c_R \sim \Delta$ from the right-of-crossing derivative

So $C = O(1/\min(c_L, c_R)) = O(A_2 / (A_1(A_1 + 1)) + 1/\Delta)$.

### Step 3: Apply Guo-An's Runtime Theorem
Guo-An Theorem 3.4: under the measure condition with constant $C$, the $p$-schedule achieves
```
T = O(C^{1/(2p-1)} / Delta_*^{3 - 2/(2p-1)})
```
Substitute $C$ and $\Delta_* = g_{\min} = \Theta(\sqrt{d_0 / N} \cdot A_1 / (A_1 + 1) \cdot 1/\sqrt{A_2})$.

### Step 4: Compare p = 2 and p = 3/2
Evaluate the runtime expression for both values. The asymptotic scaling should match; the difference is in the constant.


## Technical Details

### Gap Profile Summary (from Chapter 6)
The paper proves a piecewise gap bound:
```
g(s) >= {
  2(1-s) * A_1(A_1+1) / ((A_1+1)^2 * A_2)   for s < s* - delta
  g_min                                         for |s - s*| < delta
  2s * Delta / (1 + Delta)                      for s > s* + delta
}
```
where $s^* = A_1 / (A_1 + 1)$ and $g_{\min} = 2A_1 / (A_1 + 1) \cdot \sqrt{d_0 / (N A_2)}$.

### Guo-An's Framework
A schedule $u: [0,1] \to [0,1]$ reparameterizes the adiabatic path. The $p$-schedule satisfies
```
u'(s) = Delta^p(u(s)) / integral_0^1 Delta^p(u) du
```
Key results:
- $p = 1$: constant speed (baseline)
- $p = 2$: proportional to gap squared (matches paper)
- $p = 3/2$: variationally optimal under measure condition

### Connection to Experiment 06
Experiment 06 proved $T = \Theta(1/\Delta_*^{3 - 2/\alpha})$ where $\alpha$ is the flatness exponent. For the paper's gap, $\alpha = 1$, giving $T = \Theta(1/\Delta_*)$. This is the regime where the measure condition holds, confirming consistency.


## Results

**Status**: PROPOSED

No results yet. The argument is outlined above; the main work is verifying the constant $C$ computation and confirming the runtime recovery.


## Open Questions

1. Does the constant improvement from $p = 3/2$ over $p = 2$ have practical significance?
2. For what range of $A_1$ values does the improvement matter most?
3. Can Guo-An's framework suggest schedules beyond power-law that do even better?
4. Does the connection extend to non-adiabatic algorithms?


## Connection to Other Experiments

- Builds on 06 (measure condition): uses $\alpha = 1$ classification
- Related to 02 (robust schedules): alternative schedule optimality criterion
- Related to 07 (partial information): schedule computation requires gap knowledge
- Complements 12 (circumventing barrier): even with optimal schedule, A_1 dependence remains


## References

1. Paper Section 2.1-2.2 - Gap analysis and optimal schedule derivation
2. Guo-An 2025 Sections 3-4 - Power-law schedules and measure condition
3. Experiment 06 - $\alpha = 1$ classification for paper's gap
4. Jansen-Ruskai-Seiler 2007 - Adiabatic error bounds underlying both frameworks


## Status

**Phase**: Proposed

**Open problem note**: This is a new observation connecting the paper and Guo-An. Neither paper makes this connection because the paper predates Guo-An.

Next steps:
1. Verify measure condition computation with explicit $C$
2. Confirm runtime recovery matches paper's Theorem 2.5
3. Compute constant factor improvement from $p = 3/2$
4. Check Grover case ($C = O(1)$) as sanity check
