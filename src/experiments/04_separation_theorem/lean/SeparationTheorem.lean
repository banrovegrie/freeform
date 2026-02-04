/-
  Gap-Uninformed Separation Theorem

  Formal verification of the gap-uninformed separation theorem for
  adiabatic quantum optimization.

  MAIN RESULT:
  For any fixed schedule that must work for all gap functions with
  minimum in [s_L, s_R], the separation ratio from gap-informed is:

      T_uninformed / T_informed >= (s_R - s_L) / Delta_star

  For unstructured search with n qubits: Omega(2^{n/2})

  WHAT IS PROVEN (end-to-end):
  1. Adversarial construction: for any s in [s_L, s_R], we can build a valid
     gap function with minimum at s (Lemma `adversarialGap_in_class`)
  2. Velocity bound: if schedule works for all gaps in class, then
     v(s)^2 <= epsilon * Delta_star^2 for all s in [s_L, s_R]
     (Theorem `velocity_bounded_everywhere`)
  3. Separation ratio: given the time-velocity relationship T = width/v,
     the ratio is (s_R - s_L) / Delta_star
     (Theorem `separation_ratio_geometric`)

  WHAT IS ASSUMED (from physics literature):
  1. Crossing error model: error ~ v^2/Delta^2 (from Jansen-Ruskai-Seiler)
  2. Time-velocity relationship: T = width/v for constant-velocity traversal
  3. Informed schedule achievability: T_inf = Theta(Delta_star/v_slow)
     (from Roland-Cerf 2002, Guo-An 2025)

  THE LOGICAL CHAIN:
  adversarial_construction → velocity_bound → slow_region_width → separation_ratio

  Reference: Extends "Unstructured Adiabatic Quantum Optimization: Optimality
  with Limitations" (Braida, Chakraborty, Chaudhuri, Cunningham, Menavlikar,
  Novo, Roland, 2025)
-/

import SeparationTheorem.Basic
import SeparationTheorem.Separation

namespace SeparationTheorem

/-! ## Main Results -/

#check gap_uninformed_separation_theorem
#check velocity_bounded_everywhere
#check adversarialGap_in_class
#check separation_ratio
#check unstructured_search_separation

/-! ## Verified Claims

**1. Adversarial Construction (Lemma `adversarialGap_in_class`)**
For any point s in [s_L, s_R], we can construct a gap function
g(s') = Delta_star + (s' - s)^2 with minimum at s that belongs
to the gap class G(s_L, s_R, Delta_star).

**2. Velocity Bound (Theorem `velocity_bounded_everywhere`)**
Any schedule achieving error epsilon for all gaps in
G(s_L, s_R, Delta_star) must have velocity bounded by
sqrt(epsilon) * Delta_star at EVERY point in [s_L, s_R].

This is the KEY result: the adversary can place the gap minimum
at any point, so the schedule must be prepared for all of them.

**3. Separation Ratio (Theorem `separation_ratio`)**
Given:
- Uninformed slow region width: (s_R - s_L)
- Informed slow region width: Delta_star
- Both use same v_slow for same error

The ratio T_unf / T_inf = (s_R - s_L) / Delta_star
is independent of v_slow (it cancels).

**4. Unstructured Search (Theorem `unstructured_search_separation`)**
For n-qubit unstructured search with Delta_star = 2^{-n/2}
and uncertainty interval width 0.4, the separation is:
0.4 * 2^{n/2} = Omega(2^{n/2})

**5. Main Theorem (Theorem `gap_uninformed_separation_theorem`)**
Combines the velocity bound and separation ratio into a single statement
that captures the complete result.
-/

/-! ## What This Proves

The Lean formalization establishes an end-to-end proof of:

"If a schedule must work for ALL gap functions in G(s_L, s_R, Delta_star),
 then v(s) <= v_slow for ALL s in [s_L, s_R]."

Combined with the time-velocity relationship T = width/v_slow, this gives:
- T_unf >= (s_R - s_L) / v_slow  (slow over entire interval)
- T_inf = Delta_star / v_slow    (slow over crossing only, assumed achievable)
- T_unf / T_inf >= (s_R - s_L) / Delta_star

The separation is purely geometric: the ratio of slow region widths.
-/

end SeparationTheorem
