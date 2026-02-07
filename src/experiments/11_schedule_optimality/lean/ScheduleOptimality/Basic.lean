/-
  Schedule Optimality: Basic Definitions

  Defines the key objects for connecting the paper's gap profile
  to Guo-An's variational framework:
  - Piecewise gap lower bound parameters
  - Sublevel set measure for piecewise-linear gaps
  - Measure condition constant
  - Grover gap (exact)

  The key insight: the paper's V-shaped gap profile satisfies
  the measure condition with C = O(1) for fixed spectral parameters.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace ScheduleOptimality

/-! ## Spectral Parameters -/

/-- Spectral parameters of the problem Hamiltonian -/
structure SpectralParams where
  /-- First spectral parameter A_1 = (1/N) sum d_k/(E_k - E_0) -/
  A1 : Real
  /-- Second spectral parameter A_2 = (1/N) sum d_k/(E_k - E_0)^2 -/
  A2 : Real
  /-- Spectral gap Delta = E_1 - E_0 -/
  Delta : Real
  /-- Hilbert space dimension -/
  N : Real
  /-- Ground state degeneracy -/
  d0 : Real
  /-- Positivity conditions -/
  hA1_pos : A1 > 0
  hA2_pos : A2 > 0
  hDelta_pos : Delta > 0
  hN_pos : N > 0
  hd0_pos : d0 > 0

/-- Crossing position s* = A_1/(A_1 + 1) -/
noncomputable def SpectralParams.sStar (p : SpectralParams) : Real :=
  p.A1 / (p.A1 + 1)

/-- Left slope c_L = A_1(A_1+1)/A_2 -/
noncomputable def SpectralParams.cL (p : SpectralParams) : Real :=
  p.A1 * (p.A1 + 1) / p.A2

/-- Algebraic gap value g_hat = 2A_1/(A_1+1) * sqrt(d_0/(N*A_2)) -/
noncomputable def SpectralParams.gHat (p : SpectralParams) : Real :=
  2 * p.A1 / (p.A1 + 1) * Real.sqrt (p.d0 / (p.N * p.A2))

/-- Half-window width delta_s = g_hat / c_L -/
noncomputable def SpectralParams.deltaS (p : SpectralParams) : Real :=
  p.gHat / p.cL

/-- Right prefactor c_R = Delta/30 -/
noncomputable def SpectralParams.cR (p : SpectralParams) : Real :=
  p.Delta / 30

/-- s* is in (0, 1) -/
theorem SpectralParams.sStar_pos (p : SpectralParams) : p.sStar > 0 := by
  simp only [SpectralParams.sStar]
  apply div_pos p.hA1_pos
  have hden : p.A1 + 1 > 0 := by linarith [p.hA1_pos]
  exact hden

theorem SpectralParams.sStar_lt_one (p : SpectralParams) : p.sStar < 1 := by
  simp only [SpectralParams.sStar]
  have h1 : p.A1 + 1 > 0 := by linarith [p.hA1_pos]
  rw [div_lt_one h1]
  linarith

/-- c_L is positive -/
theorem SpectralParams.cL_pos (p : SpectralParams) : p.cL > 0 := by
  simp only [SpectralParams.cL]
  apply div_pos
  · exact mul_pos p.hA1_pos (by linarith [p.hA1_pos])
  · exact p.hA2_pos

/-- g_hat is positive -/
theorem SpectralParams.gHat_pos (p : SpectralParams) : p.gHat > 0 := by
  simp only [SpectralParams.gHat]
  apply mul_pos
  · apply mul_pos
    · apply mul_pos (by norm_num : (2 : Real) > 0) p.hA1_pos
    · exact inv_pos.mpr (by linarith [p.hA1_pos])
  · exact Real.sqrt_pos.mpr (div_pos p.hd0_pos (mul_pos p.hN_pos p.hA2_pos))

/-- c_L * delta_s = g_hat (exact identity) -/
theorem SpectralParams.cL_deltaS_eq_gHat (p : SpectralParams) :
    p.cL * p.deltaS = p.gHat := by
  simp only [SpectralParams.deltaS]
  rw [mul_div_cancel₀]
  exact ne_of_gt p.cL_pos

/-! ## Grover Specialization -/

/-- Grover spectral parameters for dimension N -/
noncomputable def groverParams (N : Real) (hN : N > 1) : SpectralParams where
  A1 := (N - 1) / N
  A2 := (N - 1) / N
  Delta := 1
  N := N
  d0 := 1
  hA1_pos := div_pos (by linarith) (by linarith)
  hA2_pos := div_pos (by linarith) (by linarith)
  hDelta_pos := by norm_num
  hN_pos := by linarith
  hd0_pos := by norm_num

/-! ## Grover Exact Gap -/

/-- The exact Grover gap squared: g(s)^2 = (2s-1)^2(1-1/N) + 1/N -/
noncomputable def groverGapSq (N : Real) (s : Real) : Real :=
  (2 * s - 1) ^ 2 * (1 - 1 / N) + 1 / N

/-- Grover gap squared is at least 1/N -/
theorem groverGapSq_ge (N : Real) (hN : N ≥ 1) (s : Real) :
    groverGapSq N s ≥ 1 / N := by
  simp only [groverGapSq]
  have h1 : (2 * s - 1) ^ 2 ≥ 0 := sq_nonneg _
  have h2 : 1 - 1 / N ≥ 0 := by
    have hN_pos : N > 0 := lt_of_lt_of_le (by norm_num : (0 : Real) < 1) hN
    have hdiv : 1 / N ≤ 1 := by
      rw [div_le_one hN_pos]
      exact hN
    linarith
  linarith [mul_nonneg h1 h2]

/-- Grover gap squared achieves minimum 1/N at s = 1/2 -/
theorem groverGapSq_min (N : Real) (_hN : N > 0) :
    groverGapSq N (1/2) = 1 / N := by
  simp only [groverGapSq]
  ring_nf

/-- Grover gap squared at endpoints equals 1 -/
theorem groverGapSq_at_zero (N : Real) (hN : N > 0) :
    groverGapSq N 0 = 1 := by
  simp only [groverGapSq]
  have hN_ne : N ≠ 0 := ne_of_gt hN
  field_simp
  ring

theorem groverGapSq_at_one (N : Real) (hN : N > 0) :
    groverGapSq N 1 = 1 := by
  simp only [groverGapSq]
  have hN_ne : N ≠ 0 := ne_of_gt hN
  field_simp
  ring

/-! ## Sublevel Set Measure for Grover

For the Grover gap on [0,1], the sublevel set {s in [0,1] : g(s) <= x}
has measure:
- 0                           if x < 1/sqrt(N)
- sqrt((Nx^2 - 1)/(N-1))     if 1/sqrt(N) <= x <= 1
- 1                           if x > 1
-/

/-- The unconstrained sublevel measure formula for Grover -/
noncomputable def groverSublevelMeasure (N : Real) (x : Real) : Real :=
  if x < 1 / Real.sqrt N then 0
  else if x ≤ 1 then Real.sqrt ((N * x ^ 2 - 1) / (N - 1))
  else 1

/-- Grover measure ratio: mu(x)/x -/
noncomputable def groverMeasureRatio (N : Real) (x : Real) : Real :=
  groverSublevelMeasure N x / x

/-! ## Measure Condition Constant -/

/-- The measure condition constant from Theorem A -/
noncomputable def measureConstant (p : SpectralParams) (s0 : Real) : Real :=
  3 * p.A2 / (p.A1 * (p.A1 + 1)) + 30 * (1 - s0) / p.Delta

/-- The measure condition constant is positive -/
theorem measureConstant_pos (p : SpectralParams) (s0 : Real) (hs0 : s0 < 1) :
    measureConstant p s0 > 0 := by
  simp only [measureConstant]
  apply add_pos
  · apply div_pos
    · exact mul_pos (by linarith : (3 : Real) > 0) p.hA2_pos
    · exact mul_pos p.hA1_pos (by linarith [p.hA1_pos])
  · apply div_pos
    · exact mul_pos (by norm_num : (30 : Real) > 0) (by linarith)
    · exact p.hDelta_pos

/-! ## Runtime Constants -/

/-- The integral constant I from Theorem C -/
noncomputable def integralConstant (p : SpectralParams) (s0 : Real) : Real :=
  3 / p.cL + 900 * (1 - s0) ^ 2 * p.cL / p.Delta ^ 2

/-- The integral constant is positive (first term is positive) -/
theorem integralConstant_pos (p : SpectralParams) (s0 : Real) :
    integralConstant p s0 > 0 := by
  simp only [integralConstant]
  have h1 : 3 / p.cL > 0 := div_pos (by norm_num : (3 : Real) > 0) p.cL_pos
  have h2 : 900 * (1 - s0) ^ 2 * p.cL / p.Delta ^ 2 ≥ 0 :=
    div_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num : (0 : Real) ≤ 900) (sq_nonneg _))
        (le_of_lt p.cL_pos))
      (sq_nonneg _)
  linarith

end ScheduleOptimality
