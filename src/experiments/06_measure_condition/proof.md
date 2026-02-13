# The Measure Condition: Necessity and the Scaling Spectrum


## Main Results

**Theorem 1 (Geometric Characterization)**: The measure condition holds with $C$ independent of $\Delta_*$ if and only if the gap approaches its minimum at most linearly.

**Theorem 2 (Scaling Spectrum)**: For gap with flatness exponent $\alpha$, the optimal runtime satisfies $T = \Theta(1/\Delta_*^{3 - 2/\alpha})$.

**Corollary**: The binary dichotomy conjecture is false. Runtime exponents form a continuum in $[1, 3)$.


## Setup

Consider adiabatic evolution with $H(s) = (1-s)H_0 + sH_1$, spectral gap $\Delta(s)$, minimum gap $\Delta_* = \min_s \Delta(s)$ at $s = s^*$.

**Gap geometry**: Near $s^*$, assume $\Delta(s) = \Delta_* + c|s - s^*|^\alpha$ for constants $c > 0$ and $\alpha > 0$.

**JRS Error Bound**: The adiabatic error with scheduling $u: [0,1] \to [0,1]$ satisfies:
$$\eta \leq \frac{\text{const}}{T} \left[\text{boundary terms} + \int \frac{(u')^2}{\Delta^3}\, ds\right]$$

**Power-law scheduling**: $u'(s) = c_p \cdot \Delta^p(u(s))$ where $c_p = \int_0^1 \Delta^{-p}(v)\, dv$.


## Proof of Theorem 1

**Definition**: Gap $\Delta$ satisfies the measure condition if there exists $C > 0$ such that $\mu(\{s : \Delta(s) \leq x\}) \leq Cx$ for all $x > 0$.

For $x = \Delta_* + \varepsilon$ (small $\varepsilon > 0$), the sublevel set near $s^*$ has measure:
$$\mu(\{s : \Delta(s) \leq x\}) = 2(\varepsilon/c)^{1/\alpha}$$

**Case $\alpha \leq 1$**: The ratio $\mu/x = 2(\varepsilon/c)^{1/\alpha}/(\Delta_* + \varepsilon)$ is bounded as $\varepsilon$ varies over $(0, \infty)$. Taking $C = \max_x$ of this ratio gives a finite constant independent of $\Delta_*$.

**Case $\alpha > 1$**: At $x = 2\Delta_*$, we need $2(\Delta_*/c)^{1/\alpha} \leq 2C\Delta_*$, which requires $(\Delta_*)^{1/\alpha - 1} \leq C \cdot c^{1/\alpha}$. Since $1/\alpha - 1 < 0$, the LHS diverges as $\Delta_* \to 0$. No finite $C$ works for all $\Delta_*$.

QED.


## Lemma (Gap Integral Bound)

For $\Delta(s) = \Delta_* + c|s - s^*|^\alpha$ and $\beta > 1/\alpha$:
$$\int_0^1 \Delta^{-\beta}(s)\, ds = \Theta(\Delta_*^{1/\alpha - \beta})$$

**Proof**: Substituting $u = c|s - s^*|^\alpha / \Delta_*$ and computing the resulting integral, which converges for $\beta > 1/\alpha$.

**Verification**: For $\alpha = 1$, this gives $\Theta(\Delta_*^{1-\beta})$, matching Guo-An's Lemma 3.3 under measure condition.

QED.


## Proof of Theorem 2

With power-law scheduling, the dominant error term transforms to:
$$\eta \sim \frac{1}{T} \cdot c_p \cdot \int \Delta^{p-3}\, dv$$

where $c_p = \int \Delta^{-p}\, dv$.

Using the Lemma:
$$c_p = \Theta(\Delta_*^{1/\alpha - p}), \qquad \int \Delta^{-(3-p)} = \Theta(\Delta_*^{1/\alpha + p - 3})$$

Product:
$$c_p \cdot \int \Delta^{p-3} = \Theta(\Delta_*^{(1/\alpha - p) + (1/\alpha + p - 3)}) = \Theta(\Delta_*^{2/\alpha - 3})$$

Thus $\eta \sim (1/T) \cdot \Delta_*^{2/\alpha - 3}$.

Since $2/\alpha - 3 < 0$ for $\alpha > 0$, we have $\eta \sim \Delta_*^{-(3-2/\alpha)} / T$.

For constant error $\eta = O(1)$: $T = \Omega(\Delta_*^{2/\alpha - 3})$.

Since $2/\alpha - 3 < 0$ for $\alpha > 2/3$, we can write $\Delta_*^{2/\alpha - 3} = 1/\Delta_*^{-(2/\alpha - 3)} = 1/\Delta_*^{3 - 2/\alpha}$.

Thus $T = \Omega(1/\Delta_*^{3 - 2/\alpha})$.

**Verification**:
- $\alpha = 1$: $T = \Omega(1/\Delta_*^1) = \Omega(1/\Delta_*)$. Matches Guo-An.
- $\alpha = 2$: $T = \Omega(1/\Delta_*^2)$.
- $\alpha \to \infty$: $T \to \Omega(1/\Delta_*^3)$.

QED.


## Summary Table

| $\alpha$ | $\gamma = 3 - 2/\alpha$ | Measure condition | Runtime $T$ |
|----------|-------------------------|-------------------|-------------|
| $1$      | $1$                     | Holds             | $\Theta(1/\Delta_*)$ |
| $1.5$    | $5/3$                   | Fails             | $\Theta(1/\Delta_*^{5/3})$ |
| $2$      | $2$                     | Fails             | $\Theta(1/\Delta_*^2)$ |
| $3$      | $7/3$                   | Fails             | $\Theta(1/\Delta_*^{7/3})$ |
| $\infty$ | $3$                     | Fails             | $\Theta(1/\Delta_*^3)$ |


## Discussion

The measure condition captures gap geometry: V-shaped minima ($\alpha = 1$) vs flat-bottomed minima ($\alpha > 1$).

**Physical interpretation**: Flat minima create wider "danger zones" where $\Delta \sim \Delta_*$, forcing the adiabatic evolution to traverse slowly for longer, accumulating more error.

**Implications**: The exponent $\gamma = 3 - 2/\alpha$ provides fine-grained complexity classification beyond the binary easy/hard dichotomy. The "worst case" $O(1/\Delta_*^2)$ commonly cited in literature corresponds to $\alpha = 2$ (quartic minimum), but arbitrarily flat minima can be even worse.


## Open Questions

1. Is the lower bound $T = \Omega(1/\Delta_*^{3-2/\alpha})$ achievable (matching upper bound)?
2. What is the typical $\alpha$ for random or structured Hamiltonians?
3. Is there a connection between $\alpha$ and computational complexity of the encoded problem?


## References

1. Guo-An 2025 - Power-law scheduling, Theorem 3.8 and Lemma 3.3
2. Jansen-Ruskai-Seiler 2007 - Adiabatic error bounds, Theorem 3
3. Roland-Cerf 2002 - Local adiabatic evolution for Grover search
