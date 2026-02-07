/-
  Information-Theoretic Limits: Basic Definitions and Algebraic Verifications

  This file formalizes the algebraic core of Experiment 10:
  1. The uninformed runtime algebra: a * sqrt(a^2/d) = a^2/sqrt(d)
  2. The geometric series bound for Durr-Hoyer analysis
  3. The crossing position s* = A_1/(A_1+1) and its properties
  4. The model separation structure (from assumption-parameterized external results)
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace InformationTheoretic

/-! ## Part I: Uninformed Runtime Algebra -/

/-- The key algebra: a * sqrt(a^2/d) = a^2/sqrt(d) for a, d > 0.
    Instantiated: 2^{n/2} * sqrt(2^n/d_0) = 2^n/sqrt(d_0).
    This was the CRITICAL bug site (originally stated as 2^n/d_0). -/
theorem runtime_algebra_abstract (a d : Real) (ha : a > 0) (_hd : d > 0) :
    a * Real.sqrt (a^2 / d) = a^2 / Real.sqrt d := by
  rw [Real.sqrt_div (le_of_lt (sq_pos_of_pos ha))]
  rw [Real.sqrt_sq (le_of_lt ha)]
  ring

/-- The old claim (a^2/d) is strictly weaker than correct (a^2/sqrt(d)) for d > 1. -/
theorem correct_bound_stronger (a d : Real) (ha : a > 0) (hd : d > 1) :
    a^2 / Real.sqrt d > a^2 / d := by
  have hd_pos : d > 0 := by linarith
  have hsqrt_pos : Real.sqrt d > 0 := Real.sqrt_pos_of_pos hd_pos
  have hsqrt_lt_d : Real.sqrt d < d := by
    have hsq : Real.sqrt d * Real.sqrt d = d := Real.mul_self_sqrt (le_of_lt hd_pos)
    have hsqrt_gt_one : Real.sqrt d > 1 := by
      calc Real.sqrt d > Real.sqrt 1 := Real.sqrt_lt_sqrt (by norm_num) hd
        _ = 1 := Real.sqrt_one
    nlinarith
  rw [gt_iff_lt, div_lt_div_iff₀ hd_pos hsqrt_pos]
  nlinarith [sq_pos_of_pos ha]

/-! ## Part II: Geometric Series for Durr-Hoyer -/

/-- sqrt(2) < 1.5 -/
theorem sqrt_two_lt_three_halves : Real.sqrt 2 < 1.5 := by
  have : (1.5 : Real) ≥ 0 := by norm_num
  rw [show (1.5 : Real) = Real.sqrt (1.5^2) from (Real.sqrt_sq this).symm]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

/-- The geometric series bound: 2 + sqrt(2) < 3.5. -/
theorem geometric_series_bound : 2 + Real.sqrt 2 < 3.5 := by
  linarith [sqrt_two_lt_three_halves]

/-! ## Part III: Crossing Position -/

/-- The crossing position as a function of A_1 -/
noncomputable def crossingPosition (A_1 : Real) : Real := A_1 / (A_1 + 1)

/-- The derivative 1/(A_1+1)^2 is positive for A_1 > 0. -/
theorem crossing_derivative_positive (A_1 : Real) (hA : A_1 > 0) :
    1 / (A_1 + 1)^2 > 0 :=
  div_pos one_pos (sq_pos_of_pos (by linarith))

/-- s* is strictly between 0 and 1 for A_1 > 0. -/
theorem crossing_in_unit_interval (A_1 : Real) (hA : A_1 > 0) :
    0 < crossingPosition A_1 ∧ crossingPosition A_1 < 1 := by
  refine ⟨div_pos hA (by linarith), ?_⟩
  simp only [crossingPosition]
  rw [div_lt_one (by linarith : A_1 + 1 > 0)]
  linarith

/-- For Grover with N=4: A_1 = 3/4, s* = 3/7 -/
theorem grover_n4_crossing :
    crossingPosition (3/4 : Real) = 3/7 := by
  simp only [crossingPosition]; norm_num

/-- s* is increasing in A_1 -/
theorem crossing_monotone (A_1 A_1' : Real) (hA : A_1 > 0) (hA' : A_1' > A_1) :
    crossingPosition A_1 < crossingPosition A_1' := by
  simp only [crossingPosition]
  have h1 : A_1 + 1 > 0 := by linarith
  have h2 : A_1' + 1 > 0 := by linarith
  rw [div_lt_div_iff₀ h1 h2]
  nlinarith

/-! ## Part IV: Model Separation Structure -/

/-- BBBV lower bound as an external assumption interface for a candidate runtime `T`
    (no global axiom). -/
def bbbv_lower_bound (N d_0 T : Real)
    (_hN : N > 0) (_hd : d_0 > 0) (_hd_le : d_0 ≤ N) : Prop :=
    ∃ c : Real, c > 0 ∧ T ≥ c * Real.sqrt (N / d_0)

/-- Durr-Hoyer upper bound as an external assumption interface for a candidate runtime
    `T` (no global axiom). -/
def durr_hoyer_upper_bound (N d_0 T : Real)
    (_hN : N > 0) (_hd : d_0 > 0) (_hd_le : d_0 ≤ N) : Prop :=
    ∃ C : Real, C > 0 ∧ T ≤ C * Real.sqrt (N / d_0)

/-- If both external bounds are provided, then query complexity is Theta(sqrt(N/d_0)). -/
theorem main_theorem (N d_0 T : Real) (hN : N > 0) (hd : d_0 > 0) (hd_le : d_0 ≤ N)
    (hbbbv : bbbv_lower_bound N d_0 T hN hd hd_le)
    (hdh : durr_hoyer_upper_bound N d_0 T hN hd hd_le) :
    bbbv_lower_bound N d_0 T hN hd hd_le ∧
    durr_hoyer_upper_bound N d_0 T hN hd hd_le :=
  ⟨hbbbv, hdh⟩

/-- Combining separation ratio with runtime algebra:
    If T_unf >= R * T_inf and T_inf = c * sqrt(N/d_0),
    then T_unf >= R * c * sqrt(N/d_0).
    With R = (s_R-s_L)/Delta_* and sqrt(N/d_0) = a^2/sqrt(d_0),
    this gives T_unf = Omega(N/sqrt(d_0)). -/
theorem separation_gives_uninformed_bound
    (T_unf T_inf R : Real)
    (_hTinf_pos : T_inf > 0) (hR : R > 0)
    (hratio : T_unf ≥ R * T_inf) :
    ∀ (lb : Real), T_inf ≥ lb → T_unf ≥ R * lb := by
  intro lb hlb
  calc T_unf ≥ R * T_inf := hratio
    _ ≥ R * lb := by nlinarith

/-! ## Part V: Precision-Aware Runtime Composition -/

/-- If quantum pre-computation and adiabatic evolution are each bounded by
    constants times `sqrt(N/d_0)`, then the composed pipeline is also
    `O(sqrt(N/d_0))`. This is the algebraic core behind Proposition 9. -/
theorem precompute_plus_adiabatic_scaling
    (N d_0 q a cq ca : Real)
    (_hN : N > 0) (_hd : d_0 > 0)
    (hq : q ≤ cq * Real.sqrt (N / d_0))
    (ha : a ≤ ca * Real.sqrt (N / d_0)) :
    q + a ≤ (cq + ca) * Real.sqrt (N / d_0) := by
  nlinarith

/-- If classical pre-computation already costs `Omega(N/d_0)`, adding an
    adiabatic execution phase cannot improve that leading-order lower bound. -/
theorem classical_precompute_dominates
    (N d_0 q a : Real)
    (_hN : N > 0) (_hd : d_0 > 0)
    (hq : q ≥ N / d_0) (ha : a ≥ 0) :
    q + a ≥ N / d_0 := by
  nlinarith

/-! ## Part VI: Continuous-Time Counterexample Algebra -/

/-- Phase cancellation used in the constant-control rank-one protocol:
    sqrt(eps) * (pi / (2 * sqrt(eps))) = pi / 2 for eps > 0. -/
theorem constant_control_phase_cancellation (eps : Real) (heps : eps > 0) :
    Real.sqrt eps * (Real.pi / (2 * Real.sqrt eps)) = Real.pi / 2 := by
  have hsqrt_ne : Real.sqrt eps ≠ 0 := ne_of_gt (Real.sqrt_pos_of_pos heps)
  field_simp [hsqrt_ne]

/-- Closed-form success probability reaches 1 at the first resonance time:
    eps + (1-eps) sin^2(sqrt(eps) * pi/(2 sqrt(eps))) = 1. -/
theorem constant_control_success_at_tstar (eps : Real) (heps : eps > 0) :
    eps + (1 - eps) *
      (Real.sin (Real.sqrt eps * (Real.pi / (2 * Real.sqrt eps))))^2 = 1 := by
  rw [constant_control_phase_cancellation eps heps]
  rw [Real.sin_pi_div_two]
  ring

/-! ## Part VII: Normalized Worst-Case Scaling Identity -/

/-- Specialization used in proof2:
    sqrt(N/d_0) divided by delta = 1/sqrt(N) equals N/sqrt(d_0). -/
theorem normalized_lower_bound_specialization
    (N d_0 : Real) (hN : N > 0) (hd : d_0 > 0) :
    Real.sqrt (N / d_0) / (1 / Real.sqrt N) = N / Real.sqrt d_0 := by
  have hsN : Real.sqrt N > 0 := Real.sqrt_pos_of_pos hN
  have hsq : (Real.sqrt N)^2 = N := by
    rw [sq]
    simpa using (Real.mul_self_sqrt (le_of_lt hN))
  have hcore := runtime_algebra_abstract (Real.sqrt N) d_0 hsN hd
  have hmul : Real.sqrt N * Real.sqrt (N / d_0) = N / Real.sqrt d_0 := by
    simpa [hsq] using hcore
  calc
    Real.sqrt (N / d_0) / (1 / Real.sqrt N)
      = Real.sqrt (N / d_0) * Real.sqrt N := by
          field_simp [ne_of_gt hsN]
    _ = N / Real.sqrt d_0 := by
          simpa [mul_comm] using hmul

end InformationTheoretic
