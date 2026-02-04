# Theoretical Separation: A_1-Independent Schedules Must Be Suboptimal

## Goal

Prove rigorously that any schedule not depending on A_1 must have worse performance than the optimal A_1-aware schedule.


## Setup

Consider the family of Hamiltonians H_α parameterized by α ∈ [α_min, α_max]:

H_α(s) = -(1-s)|ψ_0⟩⟨ψ_0| + s·H_z^{(α)}

where H_z^{(α)} is designed so that A_1(H_z^{(α)}) = α.

The avoided crossing position is s*_α = α/(α+1).


## The Adiabatic Condition

From the adiabatic theorem, to maintain fidelity 1-ε, the schedule must satisfy:

∫_0^1 |ds/dt| / g(s)^2 dt ≤ C/ε

where g(s) is the spectral gap and C is a constant.

Rearranging: the total evolution time must satisfy

T ≥ (C/ε) · ∫_0^1 ds / g(s)^2


## Gap Structure

Near the avoided crossing at s*_α:

g(s) ≈ g_min · √(1 + ((s - s*_α)/δ_α)^2)

where:
- g_min = O(√(d_0/N)) is the minimum gap
- δ_α = O(√(d_0/N)) is the width of the crossing region

Outside the crossing region, g(s) = Ω(1).


## Optimal Schedule (knowing α)

The optimal local schedule slows down only near s*_α:

ds/dt ∝ g(s)^2

This gives total time:

T_opt(α) = O(1/g_min^2 · δ_α) = O(√(N/d_0))


## A_1-Independent Schedule

Now consider any schedule s(t) that doesn't know α.

**Key observation**: The schedule must handle ALL possible α ∈ [α_min, α_max].

The crossing positions span the range:

[s*_min, s*_max] = [α_min/(α_min+1), α_max/(α_max+1)]

Let Δs* = s*_max - s*_min.


## Lower Bound Argument

**Claim**: Any A_1-independent schedule achieving fidelity 1-ε for all α must have runtime at least:

T ≥ Ω(√(N/d_0) · Δs*/δ)

where δ = O(√(d_0/N)) is the crossing width.


**Proof sketch**:

1. The schedule must slow down enough near s*_α for EVERY α in the range.

2. Since the schedule doesn't know α, it must slow down over the ENTIRE interval [s*_min, s*_max].

3. In this interval, the gap could be as small as g_min for some α.

4. The time spent in this interval must satisfy:

   T_interval ≥ (Δs*) · 1/g_min^2 = Δs* · N/d_0

5. Wait, this is too pessimistic. Let me reconsider...

Actually, the gap is only small near the TRUE s*_α, not everywhere in [s*_min, s*_max].

For a given α, the gap is small only in [s*_α - δ, s*_α + δ].


**Revised argument**:

Consider a discrete set of α values: α_1, α_2, ..., α_k with corresponding s*_1, s*_2, ..., s*_k.

Choose them so that the crossing regions are disjoint:
s*_{i+1} - s*_i > 2δ

The number of such disjoint crossings is:
k = Ω(Δs* / δ) = Ω(Δs* · √(N/d_0))

For an A_1-independent schedule:
- It doesn't know which α_i is the true parameter
- It must achieve fidelity 1-ε for ALL α_i

**Key lemma**: If a schedule achieves fidelity 1-ε for instance with crossing at s*_i, it must spend time Ω(1/g_min^2 · δ) in the interval [s*_i - δ, s*_i + δ].

**Proof**: The adiabatic condition requires ∫ |ds/dt| / g(s)^2 dt ≤ C/ε near the crossing. Since g(s) ≈ g_min in this region, we need time Ω(δ/g_min^2).

**Lower bound**: An A_1-independent schedule must spend time Ω(δ/g_min^2) near EACH of the k possible crossings.

But wait - this isn't right either. The schedule can spend most of its time near one crossing and still achieve high fidelity for that instance. The other instances would fail.

**Correct formulation**:

For an A_1-independent schedule to achieve fidelity 1-ε for ALL instances, consider the "worst-case" instance.

Given schedule s(t), define:

f(s) = ∫_{t: s(t) ∈ [s-δ, s+δ]} dt / g_min^2

This measures how much "adiabaticity budget" is allocated to position s.

For fidelity 1-ε at instance with s*_i = s, we need f(s) ≥ C/ε.

If we want fidelity 1-ε for ALL instances (all s*_i), we need:

f(s*_i) ≥ C/ε for all i

The total time is:
T = ∫_0^T dt ≥ ∑_i (time in [s*_i - δ, s*_i + δ])

If the crossing regions are disjoint (which we can arrange), these intervals don't overlap.

Therefore:
T ≥ k · (δ/g_min^2) · (C/ε)
  = Ω(Δs*/δ) · δ/g_min^2
  = Ω(Δs* / g_min^2)
  = Ω(Δs* · N/d_0)


**Comparison to optimal**:

Optimal (knowing α): T_opt = O(√(N/d_0))

A_1-independent: T_indep ≥ Ω(Δs* · N/d_0)

**Separation**:

T_indep / T_opt ≥ Ω(Δs* · √(N/d_0))

For Δs* = Ω(1) (reasonable range of A_1 values), this is:

T_indep / T_opt ≥ Ω(√(N/d_0)) = Ω(2^{n/2})

**This is an exponential separation!**


## Theorem Statement

**Theorem**: Let [α_min, α_max] be a range of A_1 values with

Δs* = α_max/(α_max+1) - α_min/(α_min+1) = Ω(1).

Any schedule s(t) that achieves fidelity 1-ε for ALL instances with A_1 ∈ [α_min, α_max] must have runtime:

T ≥ Ω((Δs*/ε) · N/d_0)

In contrast, the optimal A_1-aware schedule achieves fidelity 1-ε in time:

T_opt = O((1/ε) · √(N/d_0))

The separation is Ω(Δs* · √(N/d_0)), which is exponential in n for constant Δs*.


## Interpretation

This theorem says:
1. **A_1 knowledge is exponentially valuable** for worst-case runtime
2. Without knowing A_1, you must "hedge" across all possible crossings
3. The cost of hedging is proportional to the uncertainty range Δs*


## Caveats

1. This is a WORST-CASE result. For typical instances, the separation may be smaller.

2. The argument assumes you want fidelity 1-ε for ALL instances. If you only care about EXPECTED fidelity, the result changes.

3. The lower bound might be loose - a tighter analysis could sharpen it.


## Connection to the Paper

The paper proves:
- Optimal schedule requires knowing A_1 to precision δ_s ≈ √(d_0/N)
- Computing A_1 to this precision is NP-hard

Our theorem adds:
- WITHOUT this knowledge, the runtime degrades by factor √(N/d_0)
- This quantifies the "cost" of the NP-hardness barrier


## What Remains

1. Formalize the proof (make the adiabatic theorem application rigorous)
2. Check if the lower bound is tight
3. Consider average-case instead of worst-case
4. Relate to specific problem families (not just parameterized instances)
