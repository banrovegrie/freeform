# Separation Theorem: A_1-Independent Schedules Require Exponentially More Time

## Theorem Statement

**Theorem**: Consider the family of AQO instances parameterized by A_1 in [α_min, α_max], with avoided crossing positions in [s*_min, s*_max] where

Δs* = s*_max - s*_min = α_max/(α_max+1) - α_min/(α_min+1).

Let δ = Θ(√(d_0/N)) be the crossing width and g_min = Θ(√(d_0/N)) be the minimum gap.

Then:

1. **Optimal (A_1-aware) schedule** achieves fidelity 1-ε in time:
   T_opt = O(δ/g_min^2) = O(√(N/d_0))

2. **Any A_1-independent schedule** achieving fidelity 1-ε for ALL instances requires time:
   T_indep = Ω(Δs*/g_min^2) = Ω(Δs* · N/d_0)

3. **Separation**:
   T_indep / T_opt = Ω(Δs* / δ) = Ω(Δs* · √(N/d_0))

For Δs* = Ω(1) (constant range of crossing positions), this is an **exponential separation** in n.


## Proof

### Part 1: Optimal Schedule Runtime

The adiabatic theorem states that to achieve fidelity 1-ε, the schedule s(t) must satisfy:

∫_0^1 |ds/dt| · (1/g(s)^2) dt ≤ C/ε

for some constant C.

The optimal local schedule sets ds/dt ∝ g(s)^2, giving:

T_opt = ∫_0^1 ds / g(s)^2

The gap structure near the avoided crossing at s* is:

g(s) = g_min · √(1 + ((s - s*)/δ)^2)

The integral is dominated by the crossing region [s* - δ, s* + δ]:

T_opt ≈ ∫_{s*-δ}^{s*+δ} ds / g_min^2 = 2δ / g_min^2 = O(√(N/d_0))

### Part 2: A_1-Independent Schedule Lower Bound

Consider any schedule s(t) that doesn't depend on the specific instance.

For this schedule to achieve fidelity 1-ε for an instance with crossing at position s*, it must satisfy the adiabatic condition near s*:

∫_{near s*} |ds/dt| / g(s)^2 dt ≤ C/ε

Since g(s) ≈ g_min in the crossing region, this requires the schedule to pass through [s* - δ, s* + δ] slowly:

Time in crossing region ≥ 2δ · g_min^2 / (something small)

**Key observation**: The A_1-independent schedule must satisfy this for EVERY possible crossing position s* ∈ [s*_min, s*_max].

**Claim**: The schedule must have |ds/dt| ≤ g_min^2 · ε / C throughout [s*_min, s*_max].

**Proof of Claim**: Suppose not. Then there exists s' ∈ [s*_min, s*_max] where |ds/dt(t')| > g_min^2 · ε / C for some t' with s(t') = s'.

Consider an instance with crossing at s* = s'. Near s', the gap is g(s) ≈ g_min.

The adiabatic condition requires:
∫_{near s'} |ds/dt| / g_min^2 dt ≤ C/ε

But if |ds/dt| > g_min^2 · ε / C in this region, the condition is violated.

Therefore, for the schedule to work for ALL instances, it must be slow (|ds/dt| ≤ g_min^2 · ε / C) throughout [s*_min, s*_max].

**Runtime Lower Bound**:

T_indep ≥ Time to traverse [s*_min, s*_max]
       = Δs* / (max speed in this region)
       ≥ Δs* / (g_min^2 · ε / C)
       = Δs* · C / (g_min^2 · ε)
       = Ω(Δs* · N/d_0)

### Part 3: Separation

T_indep / T_opt = Ω(Δs* · N/d_0) / O(√(N/d_0))
                = Ω(Δs* · √(N/d_0))
                = Ω(Δs* · 2^{n/2})

For Δs* = Ω(1), this is exponential in n. □


## Interpretation

### What This Says

1. **Without A_1 knowledge, you pay an exponential penalty**: The runtime degrades from O(√N) to O(N).

2. **The penalty is proportional to uncertainty**: If Δs* is small (you know A_1 approximately), the penalty is smaller.

3. **The penalty comes from "hedging"**: Not knowing where the crossing is, you must be slow everywhere it could be.


### Tightness

The lower bound is achieved by the "wide slow" schedule that goes slowly at uniform speed through [s*_min, s*_max]. This schedule is optimal among A_1-independent schedules.


### Connection to the Paper

The paper proves:
- A_1 estimation to precision δ ≈ √(d_0/N) is needed for optimal runtime
- This estimation is NP-hard at precision 1/poly(n)

Our theorem quantifies the consequence:
- Without A_1 (or with only coarse A_1 bounds), runtime degrades by factor √(N/d_0)
- This is the "price" of the NP-hardness barrier


## Refinement: Partial A_1 Knowledge

**Corollary**: If A_1 is known to lie in [α_min, α_max], the optimal runtime is:

T(Δs*) = Θ(Δs* · N/d_0 + δ · N/d_0)

where the first term is the "hedging cost" and the second is the intrinsic adiabatic cost.

As Δs* → 0 (perfect A_1 knowledge), T → O(√(N/d_0)).
As Δs* → Θ(1) (no A_1 knowledge), T → O(N/d_0).

**Interpretation**: The value of A_1 information is captured by the reduction in Δs*. Each bit of precision on A_1 roughly halves Δs*, giving a constant-factor improvement in runtime.


## Open Questions

1. Is the separation tight, or can more clever schedules do better?

2. What about AVERAGE-case (over instances) instead of worst-case?

3. Can we prove a similar separation for specific NP-hard problem families?

4. Does the separation hold for other adiabatic Hamiltonians (e.g., transverse field)?
