# Error Analysis for AQO with Imprecise A_1

This document develops Proposal 4 from the research proposals. The goal is to understand the performance degradation when AQO is run with an imprecise estimate of the avoided crossing position.


## Setup and Notation

We follow the notation from the paper exactly.

The adiabatic Hamiltonian:
```
H(s) = -(1-s)|psi_0><psi_0| + s*H_z
```

The spectral parameter:
```
A_1 = (1/N) * sum_{k=1}^{M-1} d_k / (E_k - E_0)
```

The exact avoided crossing position:
```
s* = A_1 / (A_1 + 1)
```

The width of the crossing region:
```
delta_s = (2 / (A_1 + 1)^2) * sqrt(d_0 * A_2 / N)
```

The minimum spectral gap:
```
g_min = (2*A_1 / (A_1 + 1)) * sqrt(d_0 / (A_2 * N))
```


## The Imprecision Model

Suppose we have an estimate A_1_est = A_1 + delta, where delta is the estimation error.

The estimated crossing position:
```
s*_est = A_1_est / (A_1_est + 1)
       = (A_1 + delta) / (A_1 + delta + 1)
```

Taylor expansion for small delta/A_1:
```
s*_est = s* + delta/(A_1 + 1)^2 + O(delta^2)
```

Let epsilon_s = delta / (A_1 + 1)^2 be the induced error in the crossing position.


## Key Questions

Q1: When is epsilon_s small relative to delta_s?

We need:
```
epsilon_s << delta_s
delta / (A_1 + 1)^2 << (2 / (A_1 + 1)^2) * sqrt(d_0 * A_2 / N)
delta << 2 * sqrt(d_0 * A_2 / N)
```

For typical Ising Hamiltonians:
- A_2 = Theta(1) to Theta(poly(n))
- d_0 is the number of solutions

If delta = 1/poly(n) (the NP-hard threshold), we need:
```
1/poly(n) << sqrt(d_0 / N)
sqrt(d_0) >> sqrt(N) / poly(n)
d_0 >> N / poly(n)^2
```

This requires exponentially many solutions, which is not typical. Therefore, NP-hard precision is generally insufficient.


Q2: What happens when the schedule is misaligned?

The optimal local schedule has derivative:
```
ds/dt proportional to g(s)^2
```

where g(s) is the spectral gap at s.

With an imprecise estimate, we use:
```
ds/dt proportional to g_est(s)^2
```

where g_est(s) is the gap computed using s*_est instead of s*.


## Gap Analysis with Misaligned Schedule

From the paper, the gap to the left of the crossing (s < s* - delta_s):
```
g(s) >= (A_1 / A_2) * (s* - s) / (1 - s*)
```

And to the right (s > s* + delta_s):
```
g(s) >= (Delta / 30) * (s - s_0) / (1 - s_0)
```

Within the crossing region (|s - s*| < delta_s):
```
g(s) = Theta(g_min)
```


### Case 1: Overestimate (delta > 0)

If s*_est > s*, the estimated crossing region is shifted right.

The schedule will:
- Move too fast through the actual crossing (thinking the gap is larger)
- Move too slow after the crossing (thinking it's still in the critical region)

The dangerous zone is s in [s*, s*_est]. Here:
- Actual gap: approximately g_min (we're in or near the true crossing)
- Estimated gap: larger than g_min (we think we're left of the crossing)

The adiabatic condition requires:
```
|ds/dt| << g(s)^2
```

If we use g_est(s) > g(s), we violate this condition.


### Case 2: Underestimate (delta < 0)

If s*_est < s*, the estimated crossing is shifted left.

The schedule will:
- Move too slow before the actual crossing
- Move too fast through and after the crossing

Less dangerous initially, but the rush through the crossing accumulates error.


## Quantitative Error Bound

Let F denote the final ground state fidelity. From the adiabatic theorem:
```
1 - F <= O(T^{-2} * Integral_0^1 [|H'(s)|^2 / g(s)^4 + |H''(s)| / g(s)^2] ds)
```

For the local schedule, |ds/dt| = c / g_est(s)^2, where c is a normalization constant.

The integral becomes:
```
Integral_0^1 [g_est(s)^4 / g(s)^4 + g_est(s)^2 / g(s)^2] * (1/g_est(s)^2) ds
= Integral_0^1 [g_est(s)^2 / g(s)^4 + 1 / g(s)^2] ds
```

The problematic term is g_est(s)^2 / g(s)^4 when g_est(s) >> g(s).


### Critical Contribution

In the region s in [s*, s*_est] (assuming delta > 0):

- True gap: g(s) approx g_min
- Estimated gap: g_est(s) approx (A_1/A_2) * (s*_est - s) / (1-s*_est)

At s = s*, the estimated gap is:
```
g_est(s*) = (A_1/A_2) * (s*_est - s*) / (1-s*_est)
          = (A_1/A_2) * epsilon_s / (1-s*)
          = (A_1/A_2) * (delta / (A_1+1)^2) / (1/(A_1+1))
          = (A_1/A_2) * delta / (A_1+1)
```

The ratio:
```
g_est(s*) / g_min = [(A_1/A_2) * delta / (A_1+1)] / [(2*A_1 / (A_1+1)) * sqrt(d_0/(A_2*N))]
                  = [delta / (2*A_2)] * sqrt(N*A_2 / d_0)
                  = (delta / 2) * sqrt(N / (d_0 * A_2))
```

For this to be O(1), we need:
```
delta = O(sqrt(d_0 * A_2 / N))
```

This is precisely the required precision delta_s! The analysis confirms that the NP-hard precision 1/poly(n) is insufficient when d_0 is not exponentially large.


## Runtime Overhead

When running with imprecise A_1, the effective runtime T_eff required to achieve fidelity 1-epsilon is:

```
T_eff = T_optimal * f(delta)
```

where f(delta) captures the overhead.


### Derivation of f(delta)

The adiabatic error integral in the critical region:
```
Error_critical = O(g_est^2 / g_min^4 * |critical region width|)
```

The critical region width is max(delta_s, |epsilon_s|) = max(delta_s, delta/(A_1+1)^2).

If delta >> delta_s * (A_1+1)^2 = 2*sqrt(d_0*A_2/N):
```
Error_critical = O(delta^2 / (A_2 * (A_1+1)^2) * 1/g_min^4 * delta/(A_1+1)^2)
               = O(delta^3 / (A_2 * g_min^4 * (A_1+1)^4))
```

Substitute g_min^4 = 16*A_1^4 / (A_1+1)^4 * d_0^2 / (A_2^2 * N^2):
```
Error_critical = O(delta^3 * A_2 * N^2 / (16 * A_1^4 * d_0^2))
```

To achieve Error_critical = epsilon, we need either:
1. Reduce delta (improve precision), or
2. Increase T (runtime overhead)

The runtime scaling goes as:
```
T_eff = T_optimal * (delta / delta_required)^{3/2}
```

where delta_required = O(sqrt(d_0 * A_2 / N)).


## Main Result (Conjecture)

**Theorem (Conjectured)**: Let A_1_est be an estimate of A_1 with error |A_1_est - A_1| <= delta. Then adiabatic quantum optimization using the local schedule constructed from A_1_est achieves ground state fidelity 1-epsilon in time:

```
T = O(1/epsilon * sqrt(A_2)/A_1^2 * Delta^{-2} * sqrt(N/d_0) * max(1, delta/delta_s)^{3/2})
```

where delta_s = 2*sqrt(d_0*A_2/N) / (A_1+1)^2.

**Corollary**:
- If delta <= delta_s: optimal runtime is achieved
- If delta = 1/poly(n): runtime overhead is exp(n/4) for typical instances
- If delta = 2^{-n/4}: runtime overhead is poly(n)


## Implications

1. **Practical Relevance**: Even significant imprecision (delta = 2^{-n/4} vs required 2^{-n/2}) only causes polynomial overhead.

2. **Hardness Gap**: The NP-hard threshold (1/poly(n)) is far from useful. The #P-hard threshold (2^{-poly(n)}) is overkill.

3. **Middle Ground**: There may exist algorithms that achieve intermediate precision 2^{-n^alpha} for some alpha in (1/4, 1/2) in polynomial time, which would be practically useful.


## Open Problems

1. Prove the conjectured theorem rigorously.

2. Characterize the overhead function f(delta) more precisely.

3. Determine if there exist heuristic methods to estimate A_1 with error delta = 2^{-n/4} in polynomial time.

4. Analyze the overhead for underestimation (delta < 0) vs overestimation (delta > 0) - is one direction more forgiving?


## Numerical Validation Plan

1. For n = 10-16, construct random Ising instances.
2. Compute exact A_1 and perturb it by various delta.
3. Simulate AQO with exact and perturbed schedules.
4. Measure fidelity vs runtime for each delta.
5. Fit the relationship to test T_eff = T_optimal * f(delta).


## Connection to Guo-An Results

The Guo-An paper (2025) shows that power-law schedules u'(s) ~ Delta^p can achieve 1/Delta gap dependence under a measure condition on the gap.

Key observation: their results require knowledge of Delta(s) = g(s), not A_1 directly.

If we only know A_1 imprecisely, we might still construct a reasonable approximation to the gap function:
```
g_approx(s) = { estimated curve based on A_1_est }
```

Their Theorem suggests:
```
T_Guo-An ~ 1/g_min * (1 + gap_measure_constant)
```

vs the standard adiabatic theorem:
```
T_standard ~ 1/g_min^2
```

The power-law schedule provides a quadratic improvement in gap dependence. Combined with imprecise A_1:
- Standard adiabatic: T = O(N/d_0 * f(delta))
- Guo-An schedule: T = O(sqrt(N/d_0) * g(delta))

where g(delta) is hopefully less severe than f(delta) due to the gap improvement.


## Next Steps

1. Formalize the conjectured theorem with rigorous proof.
2. Implement numerical simulations to validate.
3. Explore the Guo-An connection for improved overhead bounds.
4. Write up results for publication.
