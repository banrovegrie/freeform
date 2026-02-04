# Gap-Uninformed Separation Theorem: Proof

## Part I: Setup

**Definition 1 (Adiabatic Evolution).**
For Hamiltonians H_0, H_1, the interpolated Hamiltonian is H(s) = (1-s)H_0 + sH_1 for s in [0,1]. A schedule u: [0,T] -> [0,1] with u(0) = 0, u(T) = 1 determines the time-dependent evolution via H(u(t)).

**Definition 2 (Gap Function).**
The gap function g: [0,1] -> R_+ is g(s) = E_1(s) - E_0(s), the difference between first excited and ground state energies of H(s). We assume g has a unique minimum Delta_star = min_s g(s) achieved at some s = s*.

**Definition 3 (Fixed Schedule).**
A schedule u is fixed if it is determined before observing any instance-specific properties. The schedule depends only on the problem size n and target error epsilon, not on spectral properties like s* or Delta_star.

**Definition 4 (Gap Class).**
The gap class G(s_L, s_R, Delta_star) consists of all gap functions g satisfying:
- The minimum g(s*) = Delta_star is achieved at some s* in [s_L, s_R]
- g(s) > Delta_star for all s != s*
- The gap is positive everywhere: g(s) > 0 for all s in [0,1]

**Definition 5 (Velocity Profile and Time).**
A schedule u with total time T induces a velocity profile v(s) > 0 representing the rate at which the evolution traverses the s-domain. The total evolution time is:
```
T = integral_0^1 (1/v(s)) ds
```

**Definition 6 (Crossing Error Model).**
Following Jansen-Ruskai-Seiler, the error contribution near a gap minimum at s* with gap value Delta_star and local velocity v is proportional to:
```
error ~ v^2 / Delta_star^2
```
For the schedule to achieve fidelity 1-epsilon at the crossing, we require:
```
v^2 / Delta_star^2 <= epsilon
```
This defines the maximum allowable velocity at the crossing:
```
v_slow := sqrt(epsilon) * Delta_star
```


## Part II: The Geometric Argument

The key insight is that this is a two-player game: the schedule designer moves first, then an adversary picks the worst-case gap function. The separation emerges purely from geometry.

**Gap-Informed vs Gap-Uninformed.**

For a gap-informed schedule:
- Knows s* exactly
- Only needs to be slow (v <= v_slow) in the crossing region near s*
- Can be arbitrarily fast elsewhere (limited only by error outside the crossing)

For a gap-uninformed schedule:
- Knows only that s* is somewhere in [s_L, s_R]
- Must be prepared for ANY gap function in the class
- Must be slow EVERYWHERE in [s_L, s_R]

**Why Uninformed Must Be Slow Everywhere (Adversarial Argument).**
Suppose the uninformed schedule has velocity v(s') > v_slow at some point s' in [s_L, s_R]. The adversary constructs a gap function g' in G(s_L, s_R, Delta_star) with minimum at s' = s*. Since the schedule is too fast at the crossing, the error exceeds epsilon. This contradicts the requirement that the schedule work for ALL gap functions in the class.

Therefore: Any schedule that achieves error <= epsilon for all g in G must satisfy v(s) <= v_slow for ALL s in [s_L, s_R].


## Part III: Formal Theorem Statements

**Lemma 1 (Adversarial Gap Construction).**
For any s_adv in [s_L, s_R] and Delta_star > 0, there exists a gap function g_adv in G(s_L, s_R, Delta_star) with minimum at s* = s_adv.

*Proof.* Define g_adv(s) = Delta_star + (s - s_adv)^2. This satisfies:
- g_adv(s_adv) = Delta_star (minimum value)
- g_adv(s) > Delta_star for s != s_adv (unique minimum)
- g_adv(s) > 0 for all s (positive, since Delta_star > 0)
- s_adv in [s_L, s_R] by assumption

Therefore g_adv in G(s_L, s_R, Delta_star). QED.

**Lemma 2 (Velocity Bound).**
Let u be a fixed schedule achieving error <= epsilon for all g in G(s_L, s_R, Delta_star). Then for all s in [s_L, s_R]:
```
v(s)^2 <= epsilon * Delta_star^2
```
Equivalently: v(s) <= sqrt(epsilon) * Delta_star = v_slow.

*Proof.* Suppose v(s')^2 > epsilon * Delta_star^2 for some s' in [s_L, s_R]. By Lemma 1, there exists g' in G with minimum at s'. The crossing error is v(s')^2 / Delta_star^2 > epsilon. Contradiction. QED.

**Theorem 1 (Uninformed Time Lower Bound).**
For any fixed schedule achieving error <= epsilon for all g in G(s_L, s_R, Delta_star):
```
T_unf >= (s_R - s_L) / v_slow = (s_R - s_L) / (sqrt(epsilon) * Delta_star)
```

*Proof.* By Lemma 2, v(s) <= v_slow for all s in [s_L, s_R]. The total time satisfies:
```
T = integral_0^1 (1/v(s)) ds >= integral_{s_L}^{s_R} (1/v(s)) ds
  >= integral_{s_L}^{s_R} (1/v_slow) ds = (s_R - s_L) / v_slow
```
QED.

**Assumption 1 (Informed Schedule Achievability).**
There exists a gap-informed schedule that achieves error <= epsilon with time:
```
T_inf = Theta(Delta_star / v_slow) = Theta(1 / sqrt(epsilon))
```

*Justification.* This follows from the analysis of optimal adiabatic schedules (Roland-Cerf 2002, Guo-An 2025). The informed schedule can be fast everywhere except near the crossing, where it spends time O(Delta_star / v_slow). The contribution from outside the crossing is subdominant.

This is NOT proven within our formal framework - it is an external result from the adiabatic quantum computing literature that we take as given.

**Theorem 2 (Separation Ratio).**
Under Assumption 1, the ratio of uninformed to informed time satisfies:
```
T_unf / T_inf >= (s_R - s_L) / Delta_star
```

*Proof.* From Theorem 1 and Assumption 1:
```
T_unf / T_inf >= [(s_R - s_L) / v_slow] / [Theta(Delta_star / v_slow)]
              = Theta((s_R - s_L) / Delta_star)
```
The v_slow factors cancel. The ratio depends only on geometric quantities: uncertainty interval width (s_R - s_L) and crossing width (Delta_star). QED.

**Corollary (Unstructured Search).**
For n-qubit unstructured search:
- Delta_star = Theta(2^{-n/2}) (from UAQO paper, Theorem 1)
- s_R - s_L = Theta(1) (from A_1 in [Omega(1), O(poly(n))] for Ising instances)

Therefore:
```
T_unf / T_inf = Omega(2^{n/2})
```


## Part IV: Connection to Computational Complexity

The minimax theorem (Part III) is a pure game-theoretic result about the gap class G. The connection to computational complexity is:

**Observation (Relevance of Gap-Uninformed Model).**
For an algorithm to use a gap-informed schedule, it must determine s* = A_1/(A_1+1), which requires computing A_1 to reasonable precision.

The UAQO paper proves:
- Computing A_1 to precision 1/poly(n) is NP-hard
- Computing A_1 exactly is #P-hard

**Corollary (Algorithmic Implication).**
Any adiabatic algorithm satisfying:
1. Uses a fixed (non-adaptive) schedule
2. Has polynomial-time classical preprocessing

must use a gap-uninformed schedule, and therefore incurs the Omega(2^{n/2}) penalty from Theorem 2.

**Important Distinction.**
This does NOT say "NP-hardness implies 2^{n/2} slowdown." The logical structure is:
- NP-hardness forces the gap-uninformed model (for fixed schedules with poly-time preprocessing)
- The gap-uninformed model has a 2^{n/2} minimax lower bound (from geometry)
- Therefore, this class of algorithms pays the penalty

The 2^{n/2} factor comes from the minimax geometry, not from computational complexity directly.


## Part V: Caveats and Scope

**1. Assumption 1 is External.**
The informed schedule achievability (Assumption 1) is taken from the physics literature, not proven here. Our formal contribution is the uninformed lower bound (Theorem 1) and the adversarial construction (Lemmas 1-2).

**2. Minimax vs. Single-Instance.**
Theorem 2 is worst-case over the gap class G. For a specific instance with fixed (but unknown) s*, a fixed schedule might happen to be slow there.

**3. Adaptive Methods Circumvent the Barrier.**
Han-Park-Choi (2025) achieve O(1/Delta_star) without prior gap knowledge by measuring during evolution. Our theorem applies only to FIXED schedules.

**4. Average-Case vs. Worst-Case.**
The adversarial construction creates worst-case instances. For natural distributions, performance may be better.

**5. Error Model Simplification.**
The crossing error model (Definition 6) captures the essential scaling but simplifies the full JRS integral bounds. The key property used is that error scales as v^2/Delta^2.


## Summary

**What We Prove (Formally):**
1. Adversarial gap construction (Lemma 1)
2. Velocity bound for uninformed schedules (Lemma 2)
3. Algebraic separation ratio given time formulas (Theorem 2)

**What We Assume (From Literature):**
1. Crossing error model scaling (Definition 6, from JRS)
2. Informed schedule achievability (Assumption 1, from Roland-Cerf/Guo-An)

**Main Result:**
For fixed schedules over gap class G(s_L, s_R, Delta_star):
```
T_unf / T_inf >= (s_R - s_L) / Delta_star
```

For unstructured search: Omega(2^{n/2}).
