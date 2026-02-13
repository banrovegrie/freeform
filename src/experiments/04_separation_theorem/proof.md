# Gap-Uninformed Separation Theorem: Proof

## Part I: Setup

**Definition 1 (Adiabatic Evolution).**
For Hamiltonians $H_0$, $H_1$, the interpolated Hamiltonian is $H(s) = (1-s)H_0 + sH_1$ for $s \in [0,1]$. A schedule $u: [0,T] \to [0,1]$ with $u(0) = 0$, $u(T) = 1$ determines the time-dependent evolution via $H(u(t))$.

**Definition 2 (Gap Function).**
The gap function $g: [0,1] \to \mathbb{R}_+$ is $g(s) = E_1(s) - E_0(s)$, the difference between first excited and ground state energies of $H(s)$. We assume $g$ has a unique minimum $\Delta_* = \min_s g(s)$ achieved at some $s = s^*$.

**Definition 3 (Fixed Schedule).**
A schedule $u$ is fixed if it is determined before observing any instance-specific properties. The schedule depends only on the problem size n and target error $\varepsilon$, not on spectral properties like $s^*$ or $\Delta_*$.

**Definition 4 (Gap Class).**
The gap class $\mathcal{G}(s_L, s_R, \Delta_*)$ consists of all gap functions $g$ satisfying:
- The minimum $g(s^*) = \Delta_*$ is achieved at some $s^* \in [s_L, s_R]$
- $g(s) > \Delta_*$ for all $s \neq s^*$
- The gap is positive everywhere: $g(s) > 0$ for all $s \in [0,1]$

**Definition 5 (Velocity Profile and Time).**
A schedule $u$ with total time $T$ induces a velocity profile $v(s) > 0$ representing the rate at which the evolution traverses the $s$-domain. The total evolution time is:

$$T = \int_0^1 \frac{1}{v(s)} \, ds$$

**Definition 6 (Crossing Error Model).**
Following Jansen-Ruskai-Seiler, the error contribution near a gap minimum at $s^*$ with gap value $\Delta_*$ and local velocity $v$ is proportional to:

$$\text{error} \sim v^2 / \Delta_*^2$$

For the schedule to achieve fidelity $1-\varepsilon$ at the crossing, we require:

$$v^2 / \Delta_*^2 \leq \varepsilon$$

This defines the maximum allowable velocity at the crossing:

$$v_{\text{slow}} := \sqrt{\varepsilon} \cdot \Delta_*$$


## Part II: The Geometric Argument

The key insight is that this is a two-player game: the schedule designer moves first, then an adversary picks the worst-case gap function. The separation emerges purely from geometry.

**Gap-Informed vs Gap-Uninformed.**

For a gap-informed schedule:
- Knows $s^*$ exactly
- Only needs to be slow ($v \leq v_{\text{slow}}$) in the crossing region near $s^*$
- Can be arbitrarily fast elsewhere (limited only by error outside the crossing)

For a gap-uninformed schedule:
- Knows only that $s^*$ is somewhere in $[s_L, s_R]$
- Must be prepared for ANY gap function in the class
- Must be slow EVERYWHERE in $[s_L, s_R]$

**Why Uninformed Must Be Slow Everywhere (Adversarial Argument).**
Suppose the uninformed schedule has velocity $v(s') > v_{\text{slow}}$ at some point $s' \in [s_L, s_R]$. The adversary constructs a gap function $g' \in \mathcal{G}(s_L, s_R, \Delta_*)$ with minimum at $s' = s^*$. Since the schedule is too fast at the crossing, the error exceeds $\varepsilon$. This contradicts the requirement that the schedule work for ALL gap functions in the class.

Therefore: Any schedule that achieves error $\leq \varepsilon$ for all $g \in \mathcal{G}$ must satisfy $v(s) \leq v_{\text{slow}}$ for ALL $s \in [s_L, s_R]$.


## Part III: Formal Theorem Statements

**Lemma 1 (Adversarial Gap Construction).**
For any $s_{\text{adv}} \in [s_L, s_R]$ and $\Delta_* > 0$, there exists a gap function $g_{\text{adv}} \in \mathcal{G}(s_L, s_R, \Delta_*)$ with minimum at $s^* = s_{\text{adv}}$.

*Proof.* Define $g_{\text{adv}}(s) = \Delta_* + (s - s_{\text{adv}})^2$. This satisfies:
- $g_{\text{adv}}(s_{\text{adv}}) = \Delta_*$ (minimum value)
- $g_{\text{adv}}(s) > \Delta_*$ for $s \neq s_{\text{adv}}$ (unique minimum)
- $g_{\text{adv}}(s) > 0$ for all $s$ (positive, since $\Delta_* > 0$)
- $s_{\text{adv}} \in [s_L, s_R]$ by assumption

Therefore $g_{\text{adv}} \in \mathcal{G}(s_L, s_R, \Delta_*)$. QED.

**Lemma 2 (Velocity Bound).**
Let $u$ be a fixed schedule achieving error $\leq \varepsilon$ for all $g \in \mathcal{G}(s_L, s_R, \Delta_*)$. Then for all $s \in [s_L, s_R]$:

$$v(s)^2 \leq \varepsilon \cdot \Delta_*^2$$

Equivalently: $v(s) \leq \sqrt{\varepsilon} \cdot \Delta_* = v_{\text{slow}}$.

*Proof.* Suppose $v(s')^2 > \varepsilon \cdot \Delta_*^2$ for some $s' \in [s_L, s_R]$. By Lemma 1, there exists $g' \in \mathcal{G}$ with minimum at $s'$. The crossing error is $v(s')^2 / \Delta_*^2 > \varepsilon$. Contradiction. QED.

**Theorem 1 (Uninformed Time Lower Bound).**
For any fixed schedule achieving error $\leq \varepsilon$ for all $g \in \mathcal{G}(s_L, s_R, \Delta_*)$:

$$T_{\text{unf}} \geq \frac{s_R - s_L}{v_{\text{slow}}} = \frac{s_R - s_L}{\sqrt{\varepsilon} \cdot \Delta_*}$$

*Proof.* By Lemma 2, $v(s) \leq v_{\text{slow}}$ for all $s \in [s_L, s_R]$. The total time satisfies:

$$T = \int_0^1 \frac{1}{v(s)} \, ds \geq \int_{s_L}^{s_R} \frac{1}{v(s)} \, ds \geq \int_{s_L}^{s_R} \frac{1}{v_{\text{slow}}} \, ds = \frac{s_R - s_L}{v_{\text{slow}}}$$

QED.

**Assumption 1 (Informed Schedule Achievability).**
There exists a gap-informed schedule that achieves error $\leq \varepsilon$ with time:

$$T_{\text{inf}} = \Theta(\Delta_* / v_{\text{slow}}) = \Theta(1 / \sqrt{\varepsilon})$$

*Justification.* This follows from the analysis of optimal adiabatic schedules (Roland-Cerf 2002, Guo-An 2025). The informed schedule can be fast everywhere except near the crossing, where it spends time $O(\Delta_* / v_{\text{slow}})$. The contribution from outside the crossing is subdominant.

This is NOT proven within our formal framework - it is an external result from the adiabatic quantum computing literature that we take as given.

**Theorem 2 (Separation Ratio).**
Under Assumption 1, the ratio of uninformed to informed time satisfies:

$$T_{\text{unf}} / T_{\text{inf}} \geq (s_R - s_L) / \Delta_*$$

*Proof.* From Theorem 1 and Assumption 1:

$$T_{\text{unf}} / T_{\text{inf}} \geq \frac{(s_R - s_L) / v_{\text{slow}}}{\Theta(\Delta_* / v_{\text{slow}})} = \Theta\!\left(\frac{s_R - s_L}{\Delta_*}\right)$$

The $v_{\text{slow}}$ factors cancel. The ratio depends only on geometric quantities: uncertainty interval width $(s_R - s_L)$ and crossing width $(\Delta_*)$. QED.

**Corollary (Unstructured Search).**
For n-qubit unstructured search:
- $\Delta_* = \Theta(2^{-n/2})$ (from UAQO paper, Theorem 1)
- $s_R - s_L = \Theta(1)$ (from $A_1 \in [\Omega(1), O(\text{poly}(n))]$ for Ising instances)

Therefore:

$$T_{\text{unf}} / T_{\text{inf}} = \Omega(2^{n/2})$$


## Part IV: Connection to Computational Complexity

The minimax theorem (Part III) is a pure game-theoretic result about the gap class $\mathcal{G}$. The connection to computational complexity is:

**Observation (Relevance of Gap-Uninformed Model).**
For an algorithm to use a gap-informed schedule, it must determine $s^* = A_1/(A_1+1)$, which requires computing $A_1$ to reasonable precision.

The UAQO paper proves:
- Computing $A_1$ to precision $1/\text{poly}(n)$ is NP-hard
- Computing $A_1$ exactly is #P-hard

**Corollary (Algorithmic Implication).**
Any adiabatic algorithm satisfying:
1. Uses a fixed (non-adaptive) schedule
2. Has polynomial-time classical preprocessing

must use a gap-uninformed schedule, and therefore incurs the $\Omega(2^{n/2})$ penalty from Theorem 2.

**Important Distinction.**
This does NOT say "NP-hardness implies $2^{n/2}$ slowdown." The logical structure is:
- NP-hardness forces the gap-uninformed model (for fixed schedules with poly-time preprocessing)
- The gap-uninformed model has a $2^{n/2}$ minimax lower bound (from geometry)
- Therefore, this class of algorithms pays the penalty

The $2^{n/2}$ factor comes from the minimax geometry, not from computational complexity directly.


## Part V: Caveats and Scope

**1. Assumption 1 is External.**
The informed schedule achievability (Assumption 1) is taken from the physics literature, not proven here. Our formal contribution is the uninformed lower bound (Theorem 1) and the adversarial construction (Lemmas 1-2).

**2. Minimax vs. Single-Instance.**
Theorem 2 is worst-case over the gap class $\mathcal{G}$. For a specific instance with fixed (but unknown) $s^*$, a fixed schedule might happen to be slow there.

**3. Adaptive Methods Circumvent the Barrier.**
Han-Park-Choi (2025) achieve $O(1/\Delta_*)$ without prior gap knowledge by measuring during evolution. Our theorem applies only to FIXED schedules.

**4. Average-Case vs. Worst-Case.**
The adversarial construction creates worst-case instances. For natural distributions, performance may be better.

**5. Error Model Simplification.**
The crossing error model (Definition 6) captures the essential scaling but simplifies the full JRS integral bounds. The key property used is that error scales as $v^2/\Delta^2$.


## Summary

**What We Prove (Formally):**
1. Adversarial gap construction (Lemma 1)
2. Velocity bound for uninformed schedules (Lemma 2)
3. Algebraic separation ratio given time formulas (Theorem 2)

**What We Assume (From Literature):**
1. Crossing error model scaling (Definition 6, from JRS)
2. Informed schedule achievability (Assumption 1, from Roland-Cerf/Guo-An)

**Main Result:**
For fixed schedules over gap class $\mathcal{G}(s_L, s_R, \Delta_*)$:

$$T_{\text{unf}} / T_{\text{inf}} \geq (s_R - s_L) / \Delta_*$$

For unstructured search: $\Omega(2^{n/2})$.
