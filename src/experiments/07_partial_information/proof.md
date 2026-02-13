# Partial Information: The Interpolation Theorem

This extends the gap-uninformed separation theorem (experiment 04) to the case of partial information about $A_1$.


## Setup

We inherit definitions from experiment 04. Additionally:

**Definition ($A_1$ Precision).**
An algorithm has $A_1$ precision $\varepsilon$ if it has access to an estimate $A_{1,\text{est}}$ satisfying $|A_{1,\text{est}} - A_1| \leq \varepsilon$.

**Definition (Crossing Position Uncertainty).**
Given $A_1$ precision $\varepsilon$, the uncertainty in the crossing position $s^* = A_1/(A_1+1)$ is:
$$\delta_{s^*} := |s^*_{\text{est}} - s^*| \quad \text{where} \quad s^*_{\text{est}} = A_{1,\text{est}}/(A_{1,\text{est}} + 1)$$

**Definition (Crossing Width).**
The crossing width $\delta_s$ is the width of the region where the gap is close to its minimum:
$$\delta_s = \frac{2\sqrt{d_0 A_2 / N}}{(A_1 + 1)^2}$$
This is $\Theta(2^{-n/2})$ for typical unstructured search instances.

**Definition (Required Precision).**
The required precision for optimality is:
$$\delta_{A_1} := (A_1 + 1)^2 \cdot \delta_s = 2\sqrt{d_0 A_2 / N}$$
This is $\Theta(2^{-n/2})$ for unstructured search.


## Part I: Precision Propagation

**Lemma 1 ($A_1$ to $s^*$ Precision).**
If $|A_{1,\text{est}} - A_1| \leq \varepsilon$, then:
$$|s^*_{\text{est}} - s^*| \leq \frac{\varepsilon}{(A_1 + 1)^2} \cdot (1 + O(\varepsilon/A_1))$$

For $\varepsilon \ll A_1$, this simplifies to:
$$|s^*_{\text{est}} - s^*| \leq \frac{\varepsilon}{(A_1 + 1)^2}$$

*Proof.*
The function $f(x) = x/(x+1)$ has derivative $f'(x) = 1/(x+1)^2$.

By the mean value theorem, there exists $\xi$ between $A_1$ and $A_{1,\text{est}}$ such that:
$$|s^* - s^*_{\text{est}}| = |f(A_1) - f(A_{1,\text{est}})| = |f'(\xi)| \cdot |A_1 - A_{1,\text{est}}|$$

Since $|A_{1,\text{est}} - A_1| \leq \varepsilon$, we have $\xi \in [A_1 - \varepsilon, A_1 + \varepsilon]$.

For the upper bound, we need the maximum of $|f'(\xi)| = 1/(\xi+1)^2$ over this interval. Since $f'$ is decreasing for $\xi > 0$, the maximum occurs at $\xi = A_1 - \varepsilon$:
$$|f'(\xi)| \leq \frac{1}{(A_1 - \varepsilon + 1)^2} = \frac{1}{(A_1 + 1)^2} \cdot \frac{1}{(1 - \varepsilon/(A_1+1))^2} = \frac{1}{(A_1 + 1)^2} \cdot (1 + O(\varepsilon/A_1))$$

Therefore:
$$|s^*_{\text{est}} - s^*| \leq \frac{\varepsilon}{(A_1 + 1)^2} \cdot (1 + O(\varepsilon/A_1))$$

For $\varepsilon \ll A_1$ (which holds for any useful precision since $A_1 = \Theta(1)$):
$$|s^*_{\text{est}} - s^*| \leq \frac{\varepsilon}{(A_1 + 1)^2}$$
QED.


## Part II: The Effective Gap Class

**Definition ($\varepsilon$-Informed Gap Class).**
Given estimate $A_{1,\text{est}}$ with precision $\varepsilon$, define the uncertainty interval:
$$s_L(\varepsilon) = s^*_{\text{est}} - \frac{\varepsilon}{(A_{1,\text{est}} + 1)^2}, \quad s_R(\varepsilon) = s^*_{\text{est}} + \frac{\varepsilon}{(A_{1,\text{est}} + 1)^2}$$

The $\varepsilon$-informed gap class is:
$$\mathcal{G}_\varepsilon := \mathcal{G}(s_L(\varepsilon), s_R(\varepsilon), \Delta_*)$$

By Lemma 1, the true crossing position $s^*$ lies in $[s_L(\varepsilon), s_R(\varepsilon)]$.

**Lemma 2 (Uncertainty Interval Width).**
The width of the uncertainty interval is:
$$W(\varepsilon) := s_R(\varepsilon) - s_L(\varepsilon) = \frac{2\varepsilon}{(A_1 + 1)^2} \cdot (1 + O(\varepsilon/A_1))$$

*Proof.* Direct from the definition and Lemma 1. QED.


## Part III: Lower Bound from Separation Theorem

**Theorem 1 (Partial Information Lower Bound).**
Any fixed schedule achieving error $\leq \delta$ for all gap functions in $\mathcal{G}_\varepsilon$ requires time:
$$T(\varepsilon) \geq \frac{W(\varepsilon)}{\sqrt{\delta} \cdot \Delta_*} = \frac{2\varepsilon}{(A_1+1)^2 \cdot \sqrt{\delta} \cdot \Delta_*} \cdot (1 + O(\varepsilon/A_1))$$

*Proof.*
By Theorem 1 of experiment 04 (the separation theorem), any fixed schedule achieving error $\leq \delta$ for all gap functions in $\mathcal{G}(s_L, s_R, \Delta_*)$ requires:
$$T \geq \frac{s_R - s_L}{\sqrt{\delta} \cdot \Delta_*}$$

Applying this to $\mathcal{G}_\varepsilon$ with interval width $W(\varepsilon)$:
$$T(\varepsilon) \geq \frac{W(\varepsilon)}{\sqrt{\delta} \cdot \Delta_*}$$

Substituting $W(\varepsilon)$ from Lemma 2 gives the result. QED.


## Part IV: Trivial Lower Bound

**Theorem 2 (Informed Lower Bound).**
Any schedule (informed or not) achieving error $\leq \delta$ requires time:
$$T \geq T_{\inf} := c \cdot \frac{\delta_s}{\sqrt{\delta} \cdot \Delta_*}$$
for some constant $c > 0$, where $\delta_s$ is the crossing width.

*Proof.*
Even with perfect knowledge of $s^*$, the schedule must traverse the crossing region where the gap is close to $\Delta_*$. This region has width $\delta_s$. By the adiabatic theorem (Jansen-Ruskai-Seiler), the velocity in this region must satisfy $v \leq \sqrt{\delta} \cdot \Delta_*$. Therefore:
$$T \geq \frac{\delta_s}{v} \geq \frac{\delta_s}{\sqrt{\delta} \cdot \Delta_*}$$

This is the informed lower bound $T_{\inf}$ (up to constants). QED.

**Remark.** The achievability of $T_{\inf}$ (that there exists a schedule achieving this time) is established in Roland-Cerf (2002) and Guo-An (2025). We take this as given.


## Part V: The Interpolation Theorem

**Theorem 3 (Interpolation).**
For $A_1$ precision $\varepsilon$, the optimal time satisfies:
$$T(\varepsilon) = \Theta\left(T_{\inf} \cdot \max\left(1, \frac{\varepsilon}{\delta_{A_1}}\right)\right)$$

where $\delta_{A_1} = 2\sqrt{d_0 A_2 / N}$ is the required precision.

*Proof.*

**Lower bound:**

Case 1: $\varepsilon \geq \delta_{A_1}$.
From Theorem 1:
$$T(\varepsilon) \geq \frac{2\varepsilon}{(A_1+1)^2 \cdot \sqrt{\delta} \cdot \Delta_*}$$

The informed time is $T_{\inf} = \Theta(\delta_s / (\sqrt{\delta} \cdot \Delta_*))$.

Taking the ratio:
$$\frac{T(\varepsilon)}{T_{\inf}} \geq \Theta\left(\frac{\varepsilon}{(A_1+1)^2 \cdot \delta_s}\right)$$

Now, $\delta_s = 2\sqrt{d_0 A_2 / N} / (A_1+1)^2$, so:
$$(A_1+1)^2 \cdot \delta_s = 2\sqrt{d_0 A_2 / N} = \delta_{A_1}$$

Therefore:
$$\frac{T(\varepsilon)}{T_{\inf}} \geq \Theta\left(\frac{\varepsilon}{\delta_{A_1}}\right)$$

Case 2: $\varepsilon < \delta_{A_1}$.
From Theorem 2, $T(\varepsilon) \geq T_{\inf}$ regardless of precision.

Combining: $T(\varepsilon) \geq \Theta(T_{\inf} \cdot \max(1, \varepsilon / \delta_{A_1}))$.

**Upper bound (achievability):**

For $\varepsilon \geq \delta_{A_1}$: A schedule that is uniformly slow (velocity $\sqrt{\delta} \cdot \Delta_*$) over the uncertainty interval $[s_L(\varepsilon), s_R(\varepsilon)]$ and fast elsewhere achieves:
$$T = O\left(\frac{W(\varepsilon)}{\sqrt{\delta} \cdot \Delta_*}\right) = O\left(T_{\inf} \cdot \frac{\varepsilon}{\delta_{A_1}}\right)$$

For $\varepsilon < \delta_{A_1}$: The optimal informed schedule achieves $T = O(T_{\inf})$.

Combining: $T(\varepsilon) \leq O(T_{\inf} \cdot \max(1, \varepsilon / \delta_{A_1}))$.

**Conclusion:**
$$T(\varepsilon) = \Theta\left(T_{\inf} \cdot \max\left(1, \frac{\varepsilon}{\delta_{A_1}}\right)\right)$$
QED.


## Part VI: Explicit Formula for Unstructured Search

**Corollary (Unstructured Search).**
For $n$-qubit unstructured search with $d_0 = O(1)$, $A_1 = \Theta(1)$, $A_2 = \Theta(1)$:
$$\delta_{A_1} = 2\sqrt{d_0 A_2 / N} = \Theta(2^{-n/2})$$

Therefore:
$$T(\varepsilon) = T_{\inf} \cdot \Theta\left(\max\left(1, \varepsilon \cdot 2^{n/2}\right)\right)$$

*Proof.* Direct substitution of $N = 2^n$ and the constant bounds on $d_0$, $A_1$, $A_2$. QED.

**Explicit values:**

| Precision $\varepsilon$ | $T(\varepsilon) / T_{\inf}$ |
|----------------------|--------------------------|
| $2^{-n/2}$           | $\Theta(1)$              |
| $2^{-n/3}$           | $\Theta(2^{n/6})$        |
| $2^{-n/4}$           | $\Theta(2^{n/4})$        |
| $1/n$                | $\Theta(2^{n/2}/n)$      |
| $1/\text{poly}(n)$   | $\Theta(2^{n/2}/\text{poly}(n))$ |
| $1$                  | $\Theta(2^{n/2})$        |


## Summary

**Main Result:**
$$T(\varepsilon) = T_{\inf} \cdot \Theta\left(\max\left(1, \frac{\varepsilon}{\delta_{A_1}}\right)\right)$$

where:
- $T_{\inf}$ = optimal informed time
- $\delta_{A_1} = \Theta(2^{-n/2})$ = required precision for optimality
- $\varepsilon$ = precision in $A_1$

**Key Properties:**
1. Linear interpolation in $\varepsilon$ (not sqrt, not threshold)
2. $T \geq T_{\inf}$ always (trivial lower bound)
3. $T = \Theta(T_{\inf})$ when $\varepsilon \leq \delta_{A_1}$ (sufficient precision)
4. $T = \Theta(T_{\inf} \cdot \varepsilon/\delta_{A_1})$ when $\varepsilon > \delta_{A_1}$ (insufficient precision)

**Implications:**
- NP-hardness at precision $1/\text{poly}(n)$ gives $T = \Theta(T_{\inf} \cdot 2^{n/2}/\text{poly}(n))$
- This is nearly the full exponential overhead
- No threshold behavior or graceful degradation
