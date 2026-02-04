# Gap-Uninformed Separation Theorem

## Problem Statement

For adiabatic quantum optimization, how much slower is a gap-uninformed schedule (one that must work for all instances with gap minimum somewhere in an interval [s_L, s_R]) compared to a gap-informed schedule (one that knows the exact crossing position s*)?

This is a minimax problem: the uninformed schedule designer moves first, then an adversary picks the worst-case gap function from the class.

## Why Novel

Extensive literature search (2026-02-04) found no prior work proving minimax lower bounds for fixed gap-uninformed adiabatic schedules. Related work:

- **Roland-Cerf 2002**: Local adiabatic evolution achieves O(sqrt(N)) by adapting schedule to gap. Requires gap knowledge.
- **Jansen-Ruskai-Seiler 2007**: Rigorous error bounds with gap dependence. Provides error analysis used here.
- **Guo-An 2025**: Power-law scheduling achieves O(1/Delta). Requires gap knowledge.
- **Han-Park-Choi 2025**: Achieves O(1/Delta) without prior knowledge via ADAPTIVE measurement during evolution.

The gap: no paper proves an adversarial/minimax lower bound for FIXED uninformed schedules.

See `lib/literature_survey.md` for the complete survey.

## Main Result

**Theorem (Gap-Uninformed Separation).**
For any fixed schedule that must work for all gap functions in G(s_L, s_R, Delta_star):
```
T_uninformed / T_informed >= (s_R - s_L) / Delta_star
```

**Corollary (Unstructured Search).**
For n-qubit unstructured search: separation is Omega(2^{n/2}).

## What Is Proven (End-to-End)

The proof has a clear logical chain:

1. **Adversarial Construction** (Lemma 1): For any s in [s_L, s_R], we construct a valid gap function g(s') = Delta_star + (s' - s)^2 with minimum at s.

2. **Velocity Bound** (Lemma 2): If a schedule achieves error <= epsilon for ALL gaps in G, then v(s)^2 <= epsilon * Delta_star^2 for ALL s in [s_L, s_R]. (If the schedule were fast at any point, the adversary places the gap there.)

3. **Time Lower Bound** (Theorem 1): Since v <= v_slow everywhere in [s_L, s_R], the uninformed time satisfies T_unf >= (s_R - s_L) / v_slow.

4. **Separation Ratio** (Theorem 2): Combined with informed achievability, T_unf / T_inf >= (s_R - s_L) / Delta_star.

## What Is Assumed (From Physics Literature)

1. **Error Model**: Crossing error scales as v^2/Delta^2 (from Jansen-Ruskai-Seiler bounds)
2. **Informed Achievability**: A gap-informed schedule can achieve T_inf = Theta(Delta_star/v_slow) (from Roland-Cerf, Guo-An)

## Status

Complete.

- Mathematical proof verified (see `proof.md`)
- Lean formalization complete with no sorry statements (see `lean/`)
- Only standard Lean axioms used (propext, Classical.choice, Quot.sound)
- Literature survey confirms novelty (see `lib/literature_survey.md`)

## Caveats

1. **Minimax, not single-instance**: Worst-case over a class of instances.
2. **Fixed schedules only**: Adaptive methods (Han-Park-Choi) circumvent this barrier.
3. **Informed achievability assumed**: Taken from physics literature, not proven here.
4. **Potentially folklore**: The argument is simple; may be considered obvious by experts.

See `lib/critical_assessment.md` for detailed analysis.

## File Structure

```
04_separation_theorem/
├── main.md              # This file (overview)
├── proof.md             # Rigorous mathematical proof
├── notes/               # Working notes and drafts
├── lib/                 # Literature survey, critical assessment
└── lean/                # Formal verification
    ├── SeparationTheorem.lean       # Summary and main #check statements
    └── SeparationTheorem/
        ├── Basic.lean               # Definitions and error model
        └── Separation.lean          # Main theorems
```

## References

1. **UAQO paper** (Chaudhuri et al. 2025): A_1 NP-hard, optimal runtime Theta(2^{n/2})
2. **Jansen-Ruskai-Seiler 2007**: Error bounds (assumed)
3. **Guo-An 2025**: Informed schedule achievability (assumed)
4. **Han-Park-Choi 2025**: Adaptive methods that circumvent the barrier
