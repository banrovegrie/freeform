# Partial Information: The Interpolation Theorem

## Problem Statement

The original paper establishes two extremes:

1. **Fully informed**: Knowing $A_1$ to precision $O(2^{-n/2})$ gives optimal runtime $T_{\inf} = O(\sqrt{2^n/d_0})$.
2. **Fully uninformed**: Not knowing $A_1$ requires $T_{\text{unf}} = \Omega(2^{n/2} \cdot T_{\inf})$ (from experiment 04).

**Central Question**: If you know $A_1$ to intermediate precision $\varepsilon$, what runtime can you achieve?


## Why Novel

The paper shows:
1. NP-hardness kicks in at precision $1/\text{poly}(n)$
2. Required precision for optimality is $2^{-n/2}$
3. Gap between these is exponentially large

This experiment characterizes the entire interpolation between these extremes. This is not addressed in the original paper or any known follow-up work.


## Main Result

**Theorem (Interpolation).**
For $A_1$ precision $\varepsilon$ (meaning $|A_{1,\text{est}} - A_1| \leq \varepsilon$):
$$T(\varepsilon) = T_{\inf} \cdot \Theta\left(\max\left(1, \frac{\varepsilon}{\delta_{A_1}}\right)\right)$$
where $\delta_{A_1} = \Theta(2^{-n/2})$ is the required precision for optimality.

For unstructured search:
$$T(\varepsilon) = T_{\inf} \cdot \Theta\left(\max\left(1, \varepsilon \cdot 2^{n/2}\right)\right)$$

**Key Finding: The interpolation is LINEAR in $\varepsilon$.**


## Implications

1. **No threshold behavior.** Every bit of precision helps linearly. No phase transitions.

2. **NP-hardness is operationally significant.** Precision $1/\text{poly}(n)$ is NP-hard, and it gives $T \sim T_{\inf} \cdot 2^{n/2}/\text{poly}(n)$. This is still exponentially worse than optimal.

3. **Exponential precision is necessary.** To achieve $T = O(T_{\inf})$, you need $\varepsilon = O(2^{-n/2})$.

4. **The hardness barrier is "hard".** Even polynomial improvements in precision only give polynomial improvements in runtime. The exponential gap remains.


## Original Conjectures (Assessed)

From the initial problem statement:

1. **Conjecture 1 (Smooth Interpolation):** CONFIRMED. The formula is $T(\varepsilon) = T_{\inf} \cdot \max(1, \varepsilon/\delta_{A_1})$.

2. **Conjecture 2 (Threshold Behavior):** REFUTED. No thresholds exist, just smooth linear degradation.

3. **Conjecture 3 (Graceful Degradation $\sim 1/\varepsilon$):** REFUTED. The scaling is $T \sim \varepsilon$ (linear), NOT $T \sim 1/\varepsilon$. Precision $1/\text{poly}(n)$ gives exponential overhead.


## Status

**Phase**: Complete

**Completed:**
1. Full mathematical proof in `proof.md`
2. Lean formalization in `lean/` directory with complete verification:
   - `interpolation_lower_bound`: $T(\varepsilon) \geq T_{\inf} \cdot \max(1, \varepsilon/\delta_{A_1})$
   - `interpolation_upper_bound`: $T(\varepsilon) \leq C \cdot T_{\inf} \cdot \max(1, \varepsilon/\delta_{A_1})$
   - `full_precision_optimal`: When $\varepsilon = \delta_{A_1}$, the ratio is 1
   - `crossingPosition_deriv`: $d(s^*)/d(A_1) = 1/(A_1+1)^2$
   - All theorems depend only on standard axioms (propext, Classical.choice, Quot.sound)


## Connection to Other Experiments

1. Directly extends 04 (separation theorem)
2. Informs 05 (adaptive schedules): measurements give partial information
3. Complements 01 (complexity at intermediate precision)


## References

1. Experiment 04: Gap-uninformed separation theorem
2. Original paper: Precision requirements, Theorem 1
3. Guo-An 2025: Error scaling analysis
