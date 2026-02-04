# Gap-Uninformed Schedule Optimality

## Context

The Guo-An paper (2025) proves that:
- Power-law scheduling u'(s) ∝ Δ^p(u(s)) achieves O(Δ*^{-1}) error
- The exponent p = 3/2 is optimal (for linear gap profiles)
- **But**: This requires knowing the spectral gap Δ(s)

The original paper proves:
- Computing A_1 (which determines where Δ is small) is NP-hard
- The required precision for optimal AQO is ~2^{-n/2}

**Open question**: What's the best achievable performance WITHOUT knowing the gap?


## Variational Framework for Gap-Uninformed Schedules

Following Guo-An's approach, the adiabatic error is bounded by:

η(1) ≤ (C/T) · ∫₀¹ [|u''(s)|/Δ²(u(s)) + A(u'(s))²/Δ³(u(s))] ds

For a gap-INFORMED schedule, we optimize over u(s) knowing Δ(·).
For a gap-UNINFORMED schedule, we must optimize over u(s) WITHOUT knowing Δ(·).


## Minimax Formulation

**Definition**: A gap-uninformed schedule u(s) must achieve low error for ALL possible gap functions in a class G.

**Minimax problem**:
```
min_{u} max_{Δ ∈ G} η(1; u, Δ)
```

This asks: what schedule minimizes the worst-case error over all possible gap functions?


## Theorem (Proposed)

**Theorem**: Consider the class of gap functions G = {Δ : Δ* ≥ δ_min, Δ has unique minimum in [s*_min, s*_max]}.

The minimax-optimal gap-uninformed schedule is the "uniform slow" schedule:
```
u'(s) = v_slow   for s ∈ [s*_min - ε, s*_max + ε]
u'(s) = v_fast   otherwise
```
where v_slow and v_fast are chosen to satisfy boundary conditions and minimize worst-case error.


## Proof Sketch

**Lower bound**: For any schedule u(s), consider the worst-case gap function. The gap minimum can be placed anywhere in [s*_min, s*_max]. The schedule must handle ALL these cases.

If u(s) is fast (large |u'|) somewhere in [s*_min, s*_max], an adversarial gap function can place the minimum there, causing large error.

Therefore, u(s) must be slow throughout [s*_min, s*_max].

**Upper bound**: The uniform slow schedule achieves:
```
η(1) ≤ O(Δs* / Δ*²)
```
where Δs* = s*_max - s*_min is the uncertainty in crossing position.


## Comparison to Gap-Informed Optimal

Gap-informed (Guo-An): η(1) = O(1/Δ*) with T = O(1/Δ*)

Gap-uninformed (our result): η(1) = O(Δs*/Δ*²) with T = O(Δs*/Δ*²)

**Separation**: The gap-uninformed schedule requires time factor Δs*/Δ* larger.

For Δs* = O(1) and Δ* = O(2^{-n/2}), this is O(2^{n/2}) — exponential separation!


## Connection to NP-Hardness

The original paper proves A_1 estimation is NP-hard. Our result quantifies the COST of this hardness:

**Corollary**: Any polynomial-time schedule (that doesn't solve an NP-hard problem) incurs an Ω(2^{n/2}) factor runtime overhead compared to the optimal schedule.


## What Needs to Be Done

1. **Formalize the proof**: Make the minimax argument rigorous using Guo-An's variational framework.

2. **Characterize the gap class G**: What's the right class to consider? The measure condition from Guo-An?

3. **Tight bounds**: Is the uniform slow schedule exactly optimal, or just order-optimal?

4. **Connection to partial information**: What if we know A_1 to some precision ε? How does the optimal schedule change?


## Significance

This would be a genuine theoretical contribution:
1. Uses Guo-An's variational framework for a new question
2. Quantifies the cost of NP-hardness in runtime terms
3. Shows that gap-uninformed schedules are fundamentally limited
4. Complements both the original paper and Guo-An's follow-up


## References

- Original paper: Braida et al. (2025) - NP-hardness of A_1 estimation
- Guo-An (2025) - Variational optimality of power-law schedules
- Gap-uninformed strategies: MatsuuraBuckSenicourtZaribafiyan2021, ShinguHatomura2025
