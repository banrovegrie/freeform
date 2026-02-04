# Theorem: Minimax Optimality of Gap-Uninformed Schedules

## Setup

Consider the adiabatic Hamiltonian:
```
H(s) = (1-s)H_0 + s·H_1,  s ∈ [0,1]
```

The spectral gap Δ(s) = E_1(s) - E_0(s) has a minimum at some s* ∈ [0,1].

**Assumption (Gap Class)**: The gap function Δ belongs to the class:
```
G = { Δ : Δ* = min_s Δ(s) ≥ δ_min > 0,
      Δ(s) ≥ Δ* + c·|s - s*| for |s - s*| ≤ ε,
      s* ∈ [s_L, s_R] }
```

This says:
- Gap has positive minimum δ_min
- Gap is V-shaped near the minimum (linear growth away from s*)
- The location s* of the minimum is unknown but bounded in [s_L, s_R]


## Adiabatic Error

From Jansen-Ruskai-Seiler (as used by Guo-An), the adiabatic error is:
```
η ≤ (C/T) · F[u, Δ]
```
where the error functional is:
```
F[u, Δ] = ∫₀¹ [|u''(s)|/Δ²(u(s)) + A·(u'(s))²/Δ³(u(s))] ds + boundary terms
```


## Gap-Informed Optimal Schedule

Guo-An proves: For known Δ(s), the optimal schedule satisfies:
```
u'(s) = c_p · Δ^p(u(s)),  p = 3/2
```

This achieves:
```
F[u_opt, Δ] = O(1/Δ*)
```


## Gap-Uninformed Schedule

A schedule u(s) is **gap-uninformed** if it doesn't depend on the specific Δ(·).

**Definition (Minimax Optimality)**: A gap-uninformed schedule u* is minimax optimal over G if:
```
u* = argmin_u max_{Δ ∈ G} F[u, Δ]
```


## Main Theorem

**Theorem 1 (Minimax Optimality of Uniform Slow Schedule)**:

Let G be the gap class defined above with uncertainty range Δs = s_R - s_L.

(a) **Lower bound**: For any gap-uninformed schedule u:
```
max_{Δ ∈ G} F[u, Δ] ≥ Ω(Δs / Δ*²)
```

(b) **Upper bound**: The uniform slow schedule defined by:
```
u'(s) = v_fast   for s ∉ [s_L - ε, s_R + ε]
u'(s) = v_slow   for s ∈ [s_L - ε, s_R + ε]
```
with v_slow = Δ*² / C' achieves:
```
max_{Δ ∈ G} F[u_uniform, Δ] = O(Δs / Δ*²)
```

**Corollary**: The uniform slow schedule is minimax optimal (up to constants).


## Proof of Lower Bound

Consider any gap-uninformed schedule u(s).

**Claim**: There exists s' ∈ [s_L, s_R] such that |u'(s')| ≥ (s_R - s_L) / T' for some T' = O(T).

*Proof*: By mean value theorem, since u(s_R) - u(s_L) ≥ some positive constant, the average velocity over [s_L, s_R] is at least Ω(1/T).

**Adversarial construction**: Place the gap minimum at s* = s'.

For this Δ ∈ G:
- Near s', we have Δ(s) ≈ Δ*
- The error integral includes:
  ```
  ∫_{near s'} (u'(s))² / Δ³(u(s)) ds ≥ (u'(s'))² · δ / Δ*³
  ```
  where δ is the width of the region where Δ ≈ Δ*.

Since |u'(s')| ≥ Ω(1/T) and δ = O(Δ*), we get:
```
F[u, Δ] ≥ Ω(1/(T²Δ*²))
```

Wait, this doesn't give the Δs dependence directly. Let me reconsider...

**Revised argument**:

For any schedule u, define the "slowness" at s as ρ(s) = 1/|u'(s)|.

The total time is: T = ∫₀¹ ρ(s) ds

For the schedule to work for ALL possible s* ∈ [s_L, s_R], it must be slow enough near each possible s*.

**Key observation**: The error near the crossing scales as:
```
error near s* ≈ δ_s / (ρ(s*)² · Δ*²)
```
where δ_s is the crossing width.

To keep this below ε, we need ρ(s*) ≥ Ω(1 / (Δ* · √ε)).

Since this must hold for ALL s* ∈ [s_L, s_R]:
```
∫_{s_L}^{s_R} ρ(s) ds ≥ (s_R - s_L) · Ω(1 / (Δ* · √ε))
```

This gives:
```
T ≥ Ω(Δs / (Δ* · √ε))
```

For constant error ε = O(1):
```
T ≥ Ω(Δs / Δ*)
```

Hmm, this is T scaling, not F scaling. Let me reconcile with Guo-An's framework...

**Reconciliation**: Guo-An shows that with optimal schedule:
- T = O(1/Δ*) gives η = O(1)

For gap-uninformed:
- T = O(Δs/Δ*) needed for η = O(1)

Separation: factor of Δs.


## Proof of Upper Bound

The uniform slow schedule has:
```
u'(s) = v_slow   for s ∈ [s_L - ε, s_R + ε]
u'(s) = v_fast   otherwise
```

For any Δ ∈ G with minimum at s* ∈ [s_L, s_R]:
- Near s*: the schedule passes at speed v_slow
- The error contribution near s* is O(v_slow² / Δ*³ · δ_s)
- With v_slow = Δ* / C', this is O(1/Δ*)

Time to traverse [s_L - ε, s_R + ε]: T_slow = (Δs + 2ε) / v_slow = O(Δs / Δ*)

Total time: T = T_slow + O(1) = O(Δs / Δ*)

**Therefore**: The uniform slow schedule achieves error O(1) with time O(Δs / Δ*). □


## Interpretation

**Gap-informed optimal**: T = O(1/Δ*) for error O(1)
**Gap-uninformed optimal**: T = O(Δs/Δ*) for error O(1)

**Separation factor**: Δs

For the unstructured search problem:
- s* = A_1/(A_1+1) where A_1 is NP-hard to compute
- Without knowing A_1, we have Δs = O(1) (s* could be anywhere in a constant range)
- Δ* = O(2^{-n/2})

Therefore:
- Gap-informed: T = O(2^{n/2})
- Gap-uninformed: T = O(2^{n/2}) · O(1) = O(2^{n/2})

Wait, this says there's NO asymptotic separation for unstructured search!

Let me reconsider...

**The issue**: For unstructured search, Δ* = O(2^{-n/2}) regardless of schedule. The separation is in the CONSTANT factor, not the asymptotic scaling.

**Correct statement**: The gap-uninformed schedule requires time (1 + Δs·Δ*/δ_s) times larger than optimal.

For Δs = O(1), Δ* = O(2^{-n/2}), δ_s = O(2^{-n/2}):
- Factor = 1 + O(1) · O(2^{-n/2}) / O(2^{-n/2}) = O(1)

So the separation is a CONSTANT factor, not exponential!

This is actually more nuanced than I initially thought.


## Revised Conclusion

**Theorem (Corrected)**: For gap-uninformed schedules:

1. The runtime overhead compared to optimal is O(Δs / δ_s) where:
   - Δs = uncertainty in crossing position s*
   - δ_s = width of the crossing region

2. For unstructured search: Δs / δ_s = O(1) · O(2^{n/2}) = O(2^{n/2})
   - This IS exponential!

3. The uniform slow schedule is minimax optimal up to constants.


## Connection to Paper

The paper's "local schedule" achieves T = O(√(N/d_0)) by slowing down near s*.

The gap-uninformed "uniform slow" schedule slows down over a wider range, achieving T = O(Δs · √(N/d_0) / δ_s).

For Δs = O(1) and δ_s = O(√(d_0/N)):
- Uniform slow: T = O(√(N/d_0) · √(N/d_0)) = O(N/d_0)

This matches the separation theorem from earlier!
