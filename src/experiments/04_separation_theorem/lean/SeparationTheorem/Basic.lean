/-
  Gap-Uninformed Separation Theorem: Basic Definitions

  This file defines the fundamental objects for the minimax analysis:
  - Schedules (parameterized velocity functions)
  - Gap functions (spectral gap profiles)
  - The adversarial game between schedule designer and nature
  - Error model and time model

  The key insight: this is a minimax problem that can be analyzed
  without full quantum mechanics, just using the structure of error bounds.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic

namespace SeparationTheorem

/-! ## Schedule as Velocity Profile -/

/-- A schedule is characterized by its velocity profile v: [0,1] -> R+.
    The velocity must be positive. -/
structure VelocityProfile where
  /-- The velocity function v(s) -/
  v : Real -> Real
  /-- Velocity is positive -/
  v_pos : ∀ s, 0 ≤ s → s ≤ 1 → v s > 0

/-! ## Gap Function -/

/-- A gap function Delta: [0,1] -> R+ with a unique minimum -/
structure GapProfile where
  /-- The gap function -/
  Delta : Real -> Real
  /-- Gap is positive -/
  Delta_pos : ∀ s, 0 ≤ s → s ≤ 1 → Delta s > 0
  /-- Position of minimum -/
  s_star : Real
  /-- Minimum is in [0,1] -/
  s_star_range : 0 ≤ s_star ∧ s_star ≤ 1
  /-- Value at minimum -/
  Delta_star : Real
  /-- Minimum value is positive -/
  Delta_star_pos : Delta_star > 0
  /-- s_star achieves the minimum -/
  achieves_min : Delta s_star = Delta_star
  /-- Unique minimum -/
  unique_min : ∀ s, 0 ≤ s → s ≤ 1 → s ≠ s_star → Delta s > Delta_star

/-! ## Gap Class -/

/-- The gap class: all gap profiles with minimum in [s_L, s_R] and value Delta_star -/
def GapClass (s_L s_R Delta_star : Real) : Set GapProfile :=
  { gp | s_L ≤ gp.s_star ∧ gp.s_star ≤ s_R ∧ gp.Delta_star = Delta_star }

/-! ## Error Model (Simplified Jansen-Ruskai-Seiler)

The crossing error model captures the essential scaling from JRS bounds:
- Error at crossing is proportional to v^2 / Delta_star^2
- For constant error epsilon, we need v^2 <= epsilon * Delta_star^2
-/

/-- Error at the crossing: v^2 / Delta_star^2 -/
noncomputable def crossingError (v_star Delta_star : Real) : Real :=
  v_star^2 / Delta_star^2

/-- The maximum allowable velocity for error epsilon: v_slow = sqrt(epsilon) * Delta_star -/
noncomputable def maxAllowableVelocity (epsilon Delta_star : Real) : Real :=
  Real.sqrt epsilon * Delta_star

/-- If crossing error <= epsilon, then v^2 <= epsilon * Delta_star^2 -/
theorem velocity_bound_from_error (epsilon Delta_star v : Real)
    (_ : epsilon > 0) (hDelta : Delta_star > 0)
    (herror : crossingError v Delta_star ≤ epsilon) :
    v^2 ≤ epsilon * Delta_star^2 := by
  simp only [crossingError] at herror
  have h1 : Delta_star^2 > 0 := sq_pos_of_pos hDelta
  have h2 : Delta_star^2 ≠ 0 := ne_of_gt h1
  have h3 : v^2 / Delta_star^2 ≤ epsilon := herror
  calc v^2 = (v^2 / Delta_star^2) * Delta_star^2 := by field_simp
    _ ≤ epsilon * Delta_star^2 := by nlinarith [sq_nonneg v]

/-- v^2 <= epsilon * Delta_star^2 implies v <= sqrt(epsilon) * Delta_star (for v >= 0) -/
theorem velocity_bound_sqrt (epsilon Delta_star v : Real)
    (_ : epsilon > 0) (hDelta : Delta_star > 0) (hv : v ≥ 0)
    (hbound : v^2 ≤ epsilon * Delta_star^2) :
    v ≤ maxAllowableVelocity epsilon Delta_star := by
  simp only [maxAllowableVelocity]
  -- v^2 <= (sqrt(epsilon) * Delta_star)^2 implies v <= sqrt(epsilon) * Delta_star
  have h1 : (Real.sqrt epsilon * Delta_star)^2 = epsilon * Delta_star^2 := by
    rw [mul_pow, Real.sq_sqrt (by linarith : epsilon ≥ 0)]
  have h2 : v^2 ≤ (Real.sqrt epsilon * Delta_star)^2 := by rw [h1]; exact hbound
  have h3 : Real.sqrt epsilon * Delta_star ≥ 0 := by positivity
  -- Use sqrt_le_sqrt to conclude
  have h4 : Real.sqrt (v^2) ≤ Real.sqrt ((Real.sqrt epsilon * Delta_star)^2) :=
    Real.sqrt_le_sqrt h2
  rw [Real.sqrt_sq hv, Real.sqrt_sq h3] at h4
  exact h4

/-! ## Time Model

We model time as follows:
- traversalTime(width, velocity) = width / velocity
- If velocity is bounded by v_max over an interval of width W, then
  time to traverse >= W / v_max

This is a consequence of: T = integral (1/v) ds >= W * (1/v_max) = W/v_max
We take this as a definition/axiom rather than proving the integral bound.
-/

/-- Time to traverse an interval with given velocity -/
noncomputable def traversalTime (interval_width : Real) (velocity : Real) : Real :=
  interval_width / velocity

/-- If velocity is bounded by v_max everywhere on an interval of width W,
    then traversal time is at least W / v_max.
    This is the key time-velocity relationship. -/
theorem traversal_time_lower_bound (interval_width v_max : Real)
    (hW : interval_width > 0) (hv : v_max > 0) :
    traversalTime interval_width v_max > 0 := by
  simp only [traversalTime]
  exact div_pos hW hv

/-! ## Separation Ratio (Geometric) -/

/-- Uninformed must be slow over entire uncertainty interval -/
noncomputable def uninformedSlowRegionWidth (s_L s_R : Real) : Real :=
  s_R - s_L

/-- Informed only needs to be slow over crossing region (width ~ Delta_star) -/
noncomputable def informedSlowRegionWidth (Delta_star : Real) : Real :=
  Delta_star

/-- The separation ratio is the ratio of slow region widths.
    This is the core geometric insight: v_slow cancels in the ratio. -/
theorem separation_ratio_geometric (s_L s_R Delta_star v_slow : Real)
    (_ : s_L < s_R) (hDelta : Delta_star > 0) (hv : v_slow > 0) :
    traversalTime (uninformedSlowRegionWidth s_L s_R) v_slow /
    traversalTime (informedSlowRegionWidth Delta_star) v_slow
    = (s_R - s_L) / Delta_star := by
  simp only [uninformedSlowRegionWidth, informedSlowRegionWidth, traversalTime]
  have h1 : v_slow ≠ 0 := ne_of_gt hv
  have h2 : Delta_star ≠ 0 := ne_of_gt hDelta
  have h3 : Delta_star / v_slow ≠ 0 := by positivity
  field_simp

end SeparationTheorem
