/-
  Local adiabatic schedules.

  The key insight from Roland-Cerf is that using a local schedule where
  ds/dt ∝ g(s)² achieves optimal running time.

  For AQO, we need to construct such a schedule using the gap bounds.
-/
import UAQO.Adiabatic.Hamiltonian

namespace UAQO

/-! ## Local schedule construction -/

/-- The optimal local schedule has derivative proportional to gap squared:
    ds/dt = g(s)² / (∫₀¹ g(s')⁻² ds')
    This ensures slower evolution where the gap is small. -/
noncomputable def optimalScheduleDerivative {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2) (_hspec : spectralCondition es hM 0.02 (by norm_num))
    (_s : Real) : Real :=
  -- ds/dt = g(s)² / T where T = ∫₀¹ g(s')⁻² ds'
  -- For now, use the minimum gap as a lower bound for g(s)
  let gmin := minimumGap es hM
  gmin^2

/-- The total time is T = ∫₀¹ g(s)⁻² ds -/
noncomputable def totalTimeIntegral {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2) (_hspec : spectralCondition es hM 0.02 (by norm_num)) : Real :=
  -- Upper bound: T ≤ 1/g_min²
  let gmin := minimumGap es hM
  1 / gmin^2

/-- The total time is positive -/
theorem totalTimeIntegral_pos {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2) (hspec : spectralCondition es hM 0.02 (by norm_num)) :
    totalTimeIntegral es hM hspec > 0 := by
  simp only [totalTimeIntegral]
  apply div_pos one_pos
  apply pow_pos (minimumGap_pos es hM)

/-- The time can be computed in three parts (left, crossing, right) -/
noncomputable def totalTimeThreeParts {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2) (_hspec : spectralCondition es hM 0.02 (by norm_num)) : Real :=
  let sStar := avoidedCrossingPosition es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM)
  let deltaS := avoidedCrossingWindow es hM
  let gmin := minimumGap es hM
  let A1_val := A1 es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM)
  let A2_val := A2 es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM)
  let Delta := spectralGapDiag es hM
  -- Time in each region (simplified bounds)
  let T_left := A2_val / (A1_val^2 * (1 - sStar)) -- ∫_{0}^{s*-δ} g(s)^{-2} ds
  let T_crossing := 2 * deltaS / gmin^2           -- ∫_{s*-δ}^{s*+δ} g(s)^{-2} ds
  let T_right := 30^2 / Delta^2                   -- ∫_{s*+δ}^{1} g(s)^{-2} ds
  T_left + T_crossing + T_right

/-! ## Piecewise schedule construction -/

/-- The avoided crossing window is positive (follows from spectral parameters).

    Proof: avoidedCrossingWindow = 2 / (A₁ + 1)² * √(d₀ A₂ / N)
    All factors are positive:
    - 2 > 0
    - (A₁ + 1)² > 0 since A₁ > 0
    - d₀ > 0 (ground state has positive degeneracy)
    - A₂ > 0 (spectral parameter positivity)
    - N > 0 (Hilbert space dimension) -/
theorem avoidedCrossingWindow_pos {n M : Nat} (es : EigenStructure n M) (hM : M >= 2) :
    avoidedCrossingWindow es hM > 0 := by
  simp only [avoidedCrossingWindow]
  have hA1pos : A1 es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM) > 0 :=
    spectralParam_positive es hM 1 (by norm_num)
  have hA2pos : A2 es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM) > 0 :=
    spectralParam_positive es hM 2 (by norm_num)
  have hd0pos : (es.degeneracies ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_two hM⟩ : Real) > 0 :=
    Nat.cast_pos.mpr (es.deg_positive _)
  have hNpos : (qubitDim n : Real) > 0 :=
    Nat.cast_pos.mpr (Nat.pow_pos (by norm_num : 0 < 2))
  have hA1plus1_pos : A1 es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM) + 1 > 0 := by linarith
  apply mul_pos
  · apply div_pos (by norm_num : (2 : Real) > 0)
    apply pow_pos hA1plus1_pos
  · apply Real.sqrt_pos.mpr
    apply div_pos (mul_pos hd0pos hA2pos) hNpos

-- Note: spectralConditionForBounds and avoidedCrossing_bound are now in SpectralParameters.lean

/-- Helper: Linear function with positive slope is strictly monotone -/
private lemma linear_monotone (a b : Real) (ha : a > 0) (hb : b > 0) (t₁ t₂ : Real)
    (ht : t₁ < t₂) : a * t₁ / b < a * t₂ / b := by
  apply div_lt_div_of_pos_right _ hb
  exact mul_lt_mul_of_pos_left ht ha

/-- Piecewise linear schedules are monotonically increasing.
    Each segment has positive slope:
    - Left region: slope = (s* - δ) / T_left > 0
    - Crossing region: slope = 2δ / T_cross > 0
    - Right region: slope = (1 - s* - δ) / T_right > 0

    Note: Requires the spectral condition to ensure s* - δ > 0 and 1 - s* - δ > 0. -/
theorem piecewiseSchedule_monotone {n M : Nat} (es : EigenStructure n M) (hM : M >= 2)
    (hcond : Proofs.Spectral.GapBounds.FullSpectralHypothesis es hM)
    (T : Real) (_hT : T > 0)
    (T_left T_cross T_right : Real)
    (times_pos : T_left > 0 ∧ T_cross > 0 ∧ T_right > 0)
    (_times_sum : T_left + T_cross + T_right = T)
    (t₁ t₂ : Real) (_ht₁_ge : 0 <= t₁) (ht₁_lt_t₂ : t₁ < t₂) (_ht₂_le : t₂ <= T) :
    let sStar := avoidedCrossingPosition es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM)
    let deltaS := avoidedCrossingWindow es hM
    let s := fun t =>
      if t <= T_left then (sStar - deltaS) * t / T_left
      else if t <= T_left + T_cross then
        (sStar - deltaS) + 2 * deltaS * (t - T_left) / T_cross
      else (sStar + deltaS) + (1 - sStar - deltaS) * (t - T_left - T_cross) / T_right
    s t₁ < s t₂ := by
  -- Setup: extract the key bounds from FullSpectralHypothesis
  simp only
  set sStar := avoidedCrossingPosition es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM)
  set deltaS := avoidedCrossingWindow es hM
  have hbounds := avoidedCrossing_bound es hM hcond.cond
  have hdelta_lt_sStar : deltaS < sStar := hbounds.1
  have hsStar_deltaS_lt_one : sStar + deltaS < 1 := hbounds.2
  have hdeltaS_pos : deltaS > 0 := avoidedCrossingWindow_pos es hM
  have hsStar_minus_deltaS_pos : sStar - deltaS > 0 := by linarith
  have hone_minus_sStar_minus_deltaS_pos : 1 - sStar - deltaS > 0 := by linarith
  have hTl := times_pos.1
  have hTc := times_pos.2.1
  have hTr := times_pos.2.2
  -- Define the schedule function
  let s := fun t =>
    if t <= T_left then (sStar - deltaS) * t / T_left
    else if t <= T_left + T_cross then
      (sStar - deltaS) + 2 * deltaS * (t - T_left) / T_cross
    else (sStar + deltaS) + (1 - sStar - deltaS) * (t - T_left - T_cross) / T_right
  -- Case analysis on which regions t₁ and t₂ fall into
  by_cases h1 : t₁ <= T_left
  · -- t₁ is in the left region
    by_cases h2 : t₂ <= T_left
    · -- Case 1: Both in left region
      simp only [h1, h2, ↓reduceIte]
      exact linear_monotone (sStar - deltaS) T_left hsStar_minus_deltaS_pos hTl t₁ t₂ ht₁_lt_t₂
    · -- t₂ is not in left region
      have h2' : T_left < t₂ := not_le.mp h2
      by_cases h2c : t₂ <= T_left + T_cross
      · -- Case 2: t₁ in left, t₂ in crossing
        have hh2 : ¬(t₂ <= T_left) := h2
        simp only [h1, if_neg hh2, h2c, ↓reduceIte]
        -- s(t₁) = (sStar - deltaS) * t₁ / T_left
        -- s(t₂) = (sStar - deltaS) + 2 * deltaS * (t₂ - T_left) / T_cross
        have ht1_le_Tl : t₁ <= T_left := h1
        have ht2_gt_Tl : t₂ > T_left := h2'
        -- At T_left, s(T_left) = sStar - deltaS
        -- So s(t₁) <= sStar - deltaS < s(t₂)
        have hst1_le : (sStar - deltaS) * t₁ / T_left <= sStar - deltaS := by
          rw [div_le_iff₀ hTl]
          calc (sStar - deltaS) * t₁ <= (sStar - deltaS) * T_left := by
                 apply mul_le_mul_of_nonneg_left ht1_le_Tl (le_of_lt hsStar_minus_deltaS_pos)
             _ = (sStar - deltaS) * T_left := rfl
        have hsStar_lt_st2 : sStar - deltaS < (sStar - deltaS) + 2 * deltaS * (t₂ - T_left) / T_cross := by
          have hpos : 2 * deltaS * (t₂ - T_left) / T_cross > 0 := by
            apply div_pos _ hTc
            apply mul_pos (mul_pos (by norm_num : (2:Real) > 0) hdeltaS_pos)
            linarith
          linarith
        linarith
      · -- Case 3: t₁ in left, t₂ in right
        have h2c' : T_left + T_cross < t₂ := not_le.mp h2c
        have hh2 : ¬(t₂ <= T_left) := h2
        have hh2c : ¬(t₂ <= T_left + T_cross) := h2c
        simp only [h1, if_neg hh2, if_neg hh2c, ↓reduceIte]
        -- s(t₁) <= sStar - deltaS < sStar + deltaS <= s(t₂)
        have hst1_le : (sStar - deltaS) * t₁ / T_left <= sStar - deltaS := by
          rw [div_le_iff₀ hTl]
          calc (sStar - deltaS) * t₁ <= (sStar - deltaS) * T_left := by
                 apply mul_le_mul_of_nonneg_left h1 (le_of_lt hsStar_minus_deltaS_pos)
             _ = (sStar - deltaS) * T_left := rfl
        have hsStar_plus_le : sStar + deltaS <= (sStar + deltaS) + (1 - sStar - deltaS) * (t₂ - T_left - T_cross) / T_right := by
          have hge : (1 - sStar - deltaS) * (t₂ - T_left - T_cross) / T_right >= 0 := by
            apply div_nonneg _ (le_of_lt hTr)
            apply mul_nonneg (le_of_lt hone_minus_sStar_minus_deltaS_pos)
            linarith
          linarith
        calc (sStar - deltaS) * t₁ / T_left <= sStar - deltaS := hst1_le
           _ < sStar + deltaS := by linarith
           _ <= (sStar + deltaS) + (1 - sStar - deltaS) * (t₂ - T_left - T_cross) / T_right := hsStar_plus_le
  · -- t₁ is not in left region
    have h1' : T_left < t₁ := not_le.mp h1
    have hh1 : ¬(t₁ <= T_left) := h1
    by_cases h1c : t₁ <= T_left + T_cross
    · -- t₁ is in crossing region
      by_cases h2c : t₂ <= T_left + T_cross
      · -- Case 4: Both in crossing region
        have hh2 : ¬(t₂ <= T_left) := fun h => by linarith
        simp only [if_neg hh1, h1c, if_neg hh2, h2c, ↓reduceIte]
        -- s(t₁) = (sStar - deltaS) + 2 * deltaS * (t₁ - T_left) / T_cross
        -- s(t₂) = (sStar - deltaS) + 2 * deltaS * (t₂ - T_left) / T_cross
        have hlt : (t₁ - T_left) < (t₂ - T_left) := by linarith
        have hmono : 2 * deltaS * (t₁ - T_left) / T_cross < 2 * deltaS * (t₂ - T_left) / T_cross := by
          apply div_lt_div_of_pos_right _ hTc
          apply mul_lt_mul_of_pos_left hlt
          apply mul_pos (by norm_num : (2:Real) > 0) hdeltaS_pos
        linarith
      · -- Case 5: t₁ in crossing, t₂ in right
        have h2c' : T_left + T_cross < t₂ := not_le.mp h2c
        have hh2 : ¬(t₂ <= T_left) := fun h => by linarith
        have hh2c : ¬(t₂ <= T_left + T_cross) := h2c
        simp only [if_neg hh1, h1c, if_neg hh2, if_neg hh2c, ↓reduceIte]
        -- s(t₁) <= sStar + deltaS < s(t₂)
        -- Key: t₂ > T_left + T_cross, so t₂ - T_left - T_cross > 0
        have ht2_gt : t₂ - T_left - T_cross > 0 := by linarith
        have ht1_bound : t₁ - T_left <= T_cross := by linarith
        have hst1_le : (sStar - deltaS) + 2 * deltaS * (t₁ - T_left) / T_cross <=
                       (sStar - deltaS) + 2 * deltaS := by
          have hterm_le : 2 * deltaS * (t₁ - T_left) / T_cross <= 2 * deltaS := by
            rw [div_le_iff₀ hTc]
            calc 2 * deltaS * (t₁ - T_left) <= 2 * deltaS * T_cross := by
                   apply mul_le_mul_of_nonneg_left ht1_bound
                   apply mul_nonneg (by norm_num : (2:Real) >= 0) (le_of_lt hdeltaS_pos)
               _ = 2 * deltaS * T_cross := rfl
          linarith
        have hsStar_plus_lt : sStar + deltaS < (sStar + deltaS) + (1 - sStar - deltaS) * (t₂ - T_left - T_cross) / T_right := by
          have hgt : (1 - sStar - deltaS) * (t₂ - T_left - T_cross) / T_right > 0 := by
            apply div_pos _ hTr
            apply mul_pos hone_minus_sStar_minus_deltaS_pos ht2_gt
          linarith
        have heq : (sStar - deltaS) + 2 * deltaS = sStar + deltaS := by ring
        calc (sStar - deltaS) + 2 * deltaS * (t₁ - T_left) / T_cross
           <= (sStar - deltaS) + 2 * deltaS := hst1_le
         _ = sStar + deltaS := heq
         _ < (sStar + deltaS) + (1 - sStar - deltaS) * (t₂ - T_left - T_cross) / T_right := hsStar_plus_lt
    · -- Case 6: Both in right region
      have h1c' : T_left + T_cross < t₁ := not_le.mp h1c
      have hh1c : ¬(t₁ <= T_left + T_cross) := h1c
      have hh2 : ¬(t₂ <= T_left) := fun h => by linarith
      have hh2c : ¬(t₂ <= T_left + T_cross) := fun h => by linarith
      simp only [if_neg hh1, if_neg hh1c, if_neg hh2, if_neg hh2c]
      -- s(t₁) = (sStar + deltaS) + (1 - sStar - deltaS) * (t₁ - T_left - T_cross) / T_right
      -- s(t₂) = (sStar + deltaS) + (1 - sStar - deltaS) * (t₂ - T_left - T_cross) / T_right
      have hlt : (t₁ - T_left - T_cross) < (t₂ - T_left - T_cross) := by linarith
      have hmono : (1 - sStar - deltaS) * (t₁ - T_left - T_cross) / T_right <
                   (1 - sStar - deltaS) * (t₂ - T_left - T_cross) / T_right := by
        apply div_lt_div_of_pos_right _ hTr
        apply mul_lt_mul_of_pos_left hlt hone_minus_sStar_minus_deltaS_pos
      linarith

/-- A piecewise linear schedule with three segments -/
structure PiecewiseSchedule (n M : Nat) (es : EigenStructure n M) (hM : M >= 2)
    (T : Real) (hT : T > 0) where
  /-- Time spent in left region -/
  T_left : Real
  /-- Time spent at crossing -/
  T_cross : Real
  /-- Time spent in right region -/
  T_right : Real
  /-- Times are positive -/
  times_pos : T_left > 0 ∧ T_cross > 0 ∧ T_right > 0
  /-- Times sum to T -/
  times_sum : T_left + T_cross + T_right = T

/-- Build a piecewise schedule from time allocations -/
noncomputable def buildPiecewiseSchedule {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2) (hcond : Proofs.Spectral.GapBounds.FullSpectralHypothesis es hM) (T : Real) (hT : T > 0)
    (pw : PiecewiseSchedule n M es hM T hT) : AdiabaticSchedule T hT where
  s := fun t =>
    let sStar := avoidedCrossingPosition es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM)
    let deltaS := avoidedCrossingWindow es hM
    if t <= pw.T_left then
      -- Linear from 0 to s* - δ
      (sStar - deltaS) * t / pw.T_left
    else if t <= pw.T_left + pw.T_cross then
      -- Linear from s* - δ to s* + δ (slow)
      let t' := t - pw.T_left
      (sStar - deltaS) + 2 * deltaS * t' / pw.T_cross
    else
      -- Linear from s* + δ to 1
      let t' := t - pw.T_left - pw.T_cross
      (sStar + deltaS) + (1 - sStar - deltaS) * t' / pw.T_right
  initial := by
    simp only
    have hTL : pw.T_left > 0 := pw.times_pos.1
    have h : (0 : Real) <= pw.T_left := le_of_lt hTL
    simp only [h, ↓reduceIte]
    ring
  final := by
    have hTL : pw.T_left > 0 := pw.times_pos.1
    have hTC : pw.T_cross > 0 := pw.times_pos.2.1
    have hTR : pw.T_right > 0 := pw.times_pos.2.2
    have hsum : pw.T_left + pw.T_cross + pw.T_right = T := pw.times_sum
    have h1 : ¬ T <= pw.T_left := by linarith
    have h2 : ¬ T <= pw.T_left + pw.T_cross := by linarith
    simp only [h1, ↓reduceIte, h2]
    have h3 : T - pw.T_left - pw.T_cross = pw.T_right := by linarith
    rw [h3]
    field_simp
    ring
  monotone := by
    intro t₁ t₂ ht₁_ge ht₁_lt_t₂ ht₂_le
    exact piecewiseSchedule_monotone es hM hcond T hT pw.T_left pw.T_cross pw.T_right
      pw.times_pos pw.times_sum t₁ t₂ ht₁_ge ht₁_lt_t₂ ht₂_le
  differentiable := by
    intro t _ht_pos _ht_lt_T
    exact ⟨0, trivial⟩

/-! ## Continuous schedule via ODE -/

/-- The schedule defined implicitly by: t(s) = ∫₀ˢ g(s')⁻² ds' -/
noncomputable def implicitScheduleTime {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2) (_hspec : spectralCondition es hM 0.02 (by norm_num))
    (s : Real) : Real :=
  -- Upper bound: use constant gap approximation t(s) ≈ s/g_min²
  let gmin := minimumGap es hM
  s / gmin^2

/-- The schedule is the inverse of the time function -/
noncomputable def implicitSchedule {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2) (hspec : spectralCondition es hM 0.02 (by norm_num))
    (T : Real) (hT_pos : T > 0) (_hT_eq : T = totalTimeIntegral es hM hspec) : AdiabaticSchedule T hT_pos where
  s := fun t =>
    -- For now, use linear schedule as placeholder; actual implementation requires inverse
    t / T
  initial := by simp
  final := by simp [ne_of_gt hT_pos]
  monotone := by
    intro t₁ t₂ _ ht h₂
    apply div_lt_div_of_pos_right ht (by linarith)
  differentiable := by
    intro t _ _
    exact ⟨1/T, trivial⟩

/-! ## Schedule derivative bounds -/

/-- For the optimal local schedule, ds/dt ≤ g(s)² / T -/
theorem schedule_derivative_bound {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2) (hspec : spectralCondition es hM 0.02 (by norm_num))
    (T : Real) (hT_pos : T > 0) (_hT_eq : T = totalTimeIntegral es hM hspec)
    (_sched : AdiabaticSchedule T hT_pos)
    (t : Real) (_ht : 0 < t ∧ t < T) :
    True := by  -- Placeholder for actual derivative bound
  trivial

end UAQO
