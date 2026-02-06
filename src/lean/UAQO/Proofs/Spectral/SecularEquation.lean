/-
  Secular equation analysis for the adiabatic Hamiltonian.

  The eigenvalues of H(s) = -(1-s)|ψ₀⟩⟨ψ₀| + s·H_z satisfy the secular equation:
    1/(1-s) = (1/N) Σ_k d_k/(s·E_k - λ)

  This file analyzes the secular equation function F(s,λ) and its roots:
  - F is strictly increasing in λ on each interval between poles
  - There are exactly M roots (one per interval)
  - The ground state eigenvalue is the root in (-∞, s·E₀)
  - Near the avoided crossing s*, the gap has hyperbolic structure

  These results form the foundation for proving the 7 spectral gap bound axioms.

  Reference: Section 2.2 of arXiv:2411.05736
-/
import UAQO.Spectral.AdiabaticHamiltonian
import UAQO.Spectral.SpectralParameters
import UAQO.Proofs.Spectral.EigenvalueCondition

namespace UAQO.Proofs.Spectral.SecularEquation

open UAQO Finset

/-! ## The secular equation function -/

/-- The secular equation function F(s,λ) = (1/N) Σ_k d_k/(s·E_k - λ) - 1/(1-s).
    Eigenvalues of H(s) that are not degenerate eigenvalues of s·H_z satisfy F(s,λ) = 0. -/
noncomputable def secularFun {n M : Nat} (es : EigenStructure n M)
    (_hM : M > 0) (s : Real) (lambda : Real) : Real :=
  let N := (qubitDim n : Real)
  (1 / N) * Finset.sum Finset.univ (fun k : Fin M =>
    (es.degeneracies k : Real) / (s * es.eigenvalues k - lambda)) - 1 / (1 - s)

/-- The derivative of the secular function with respect to λ.
    ∂F/∂λ = (1/N) Σ_k d_k/(s·E_k - λ)² > 0 when λ ≠ s·E_k for all k. -/
noncomputable def secularFunDeriv {n M : Nat} (es : EigenStructure n M)
    (_hM : M > 0) (s : Real) (lambda : Real) : Real :=
  let N := (qubitDim n : Real)
  (1 / N) * Finset.sum Finset.univ (fun k : Fin M =>
    (es.degeneracies k : Real) / (s * es.eigenvalues k - lambda)^2)

/-! ## Positivity of the derivative -/

/-- Each term in the derivative sum is non-negative. -/
lemma secularFunDeriv_term_nonneg {n M : Nat} (es : EigenStructure n M)
    (s : Real) (lambda : Real) (k : Fin M) :
    (es.degeneracies k : Real) / (s * es.eigenvalues k - lambda)^2 ≥ 0 := by
  apply div_nonneg
  · exact Nat.cast_nonneg _
  · exact sq_nonneg _

/-- Each term in the derivative sum is strictly positive when λ ≠ s·E_k. -/
lemma secularFunDeriv_term_pos {n M : Nat} (es : EigenStructure n M)
    (s : Real) (lambda : Real) (k : Fin M)
    (hne : lambda ≠ s * es.eigenvalues k) :
    (es.degeneracies k : Real) / (s * es.eigenvalues k - lambda)^2 > 0 := by
  apply div_pos
  · exact Nat.cast_pos.mpr (es.deg_positive k)
  · apply sq_pos_of_ne_zero
    exact sub_ne_zero.mpr (Ne.symm hne)

/-- The derivative is non-negative everywhere it's defined. -/
theorem secularFunDeriv_nonneg {n M : Nat} (es : EigenStructure n M)
    (_hM : M > 0) (s : Real) (lambda : Real) :
    secularFunDeriv es _hM s lambda ≥ 0 := by
  unfold secularFunDeriv
  apply mul_nonneg
  · exact div_nonneg (le_of_lt (zero_lt_one)) (Nat.cast_nonneg _)
  · exact Finset.sum_nonneg (fun k _ => secularFunDeriv_term_nonneg es s lambda k)

/-- The derivative is strictly positive when λ is not a pole. -/
theorem secularFunDeriv_pos {n M : Nat} (es : EigenStructure n M)
    (hM : M > 0) (s : Real) (lambda : Real)
    (hne : ∀ k : Fin M, lambda ≠ s * es.eigenvalues k) :
    secularFunDeriv es hM s lambda > 0 := by
  unfold secularFunDeriv
  apply mul_pos
  · exact div_pos one_pos (Nat.cast_pos.mpr (Nat.pow_pos (by norm_num : 0 < 2)))
  · exact Finset.sum_pos (fun k _ => secularFunDeriv_term_pos es s lambda k (hne k))
      ⟨⟨0, hM⟩, Finset.mem_univ _⟩

/-! ## Properties at poles and boundaries -/

/-- The secular equation connects to the eigenvalue condition.
    From eigenvalue_condition_proof: λ is an eigenvalue of H(s) iff
    either λ = s·E_k (degenerate) or F(s,λ) = 0. -/
theorem secular_equation_characterizes_eigenvalues {n M : Nat} (es : EigenStructure n M)
    (hM : M > 0) (s : Real) (hs : 0 < s ∧ s < 1) (lambda : Real)
    (hne : ∀ k : Fin M, lambda ≠ s * es.eigenvalues k) :
    IsEigenvalue (adiabaticHam es s ⟨le_of_lt hs.1, le_of_lt hs.2⟩) lambda ↔
    secularFun es hM s lambda = 0 := by
  have hcond := eigenvalue_condition_proof es hM s hs lambda
  constructor
  · -- Forward: eigenvalue → F = 0
    intro heig
    rw [hcond] at heig
    rcases heig with ⟨z, hz_eq, _⟩ | ⟨hne', hsec⟩
    · -- Case λ = s·E_k: contradicts hne
      exact absurd hz_eq (hne (es.assignment z))
    · -- Case secular equation holds
      unfold secularFun
      linarith [hsec]
  · -- Backward: F = 0 → eigenvalue
    intro hF
    rw [hcond]
    right
    constructor
    · exact hne
    · -- secularFun = 0 means 1/(1-s) = (1/N) Σ d_k/(sE_k - λ)
      unfold secularFun at hF
      linarith

/-! ## Monotonicity of the secular function -/

/-- Each term d_k/(sE_k - λ) is strictly increasing in λ when the denominator
    doesn't change sign. The proof uses: if λ₁ < λ₂ and sE_k is on the same side
    of both, then d_k/(sE_k - λ₂) > d_k/(sE_k - λ₁). -/
lemma secularTerm_strictMono {n M : Nat} (es : EigenStructure n M)
    (s : Real) (lambda1 lambda2 : Real) (k : Fin M)
    (hlt : lambda1 < lambda2)
    (hne1 : lambda1 ≠ s * es.eigenvalues k)
    (hne2 : lambda2 ≠ s * es.eigenvalues k)
    -- Both λ's on the same side of sE_k (no sign change)
    (hsame : (s * es.eigenvalues k - lambda1) * (s * es.eigenvalues k - lambda2) > 0) :
    (es.degeneracies k : Real) / (s * es.eigenvalues k - lambda1) <
    (es.degeneracies k : Real) / (s * es.eigenvalues k - lambda2) := by
  let a := s * es.eigenvalues k
  let d := (es.degeneracies k : Real)
  have hd_pos : d > 0 := Nat.cast_pos.mpr (es.deg_positive k)
  have ha1 : a - lambda1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hne1)
  have ha2 : a - lambda2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hne2)
  -- (a - λ₂) < (a - λ₁) since λ₁ < λ₂
  have h_sub : a - lambda2 < a - lambda1 := by linarith
  -- Product positive means same sign
  rcases (mul_pos_iff.mp (le_of_lt hsame |>.lt_of_ne (Ne.symm (ne_of_gt hsame)))) with
    ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- Case 1: both positive
    -- 0 < a - λ₂ < a - λ₁, d > 0
    -- d/(a - λ₁) < d/(a - λ₂) because smaller denominator → larger fraction
    exact div_lt_div_of_pos_left hd_pos h2 h_sub
  · -- Case 2: both negative
    -- a - λ₂ < a - λ₁ < 0
    -- Equivalently: λ₂ - a > λ₁ - a > 0
    -- d/(a - λ₁) is negative with smaller absolute value
    -- d/(a - λ₂) is negative with larger absolute value... NO, this is wrong direction
    -- Actually: |a - λ₂| > |a - λ₁|, and both are negative
    -- d/(a - λ₂) > d/(a - λ₁) because d > 0, a-λ₂ more negative → d/(a-λ₂) less negative
    -- Wait: d > 0 and a - λ₂ < a - λ₁ < 0
    -- d/(a - λ₂) = d / (negative, larger magnitude) = less negative
    -- d/(a - λ₁) = d / (negative, smaller magnitude) = more negative
    -- So d/(a - λ₂) > d/(a - λ₁) ✓
    -- Use: for d > 0 and x < y < 0, d/x > d/y (dividing by more negative gives less negative)
    exact div_lt_div_of_neg_left hd_pos h1 h_sub

/-- The secular function evaluated at two points in the same interval.
    If λ₁ < λ₂ and both are in the same interval between poles,
    then F(s,λ₁) < F(s,λ₂).

    This is because ∂F/∂λ > 0 on each pole-free interval. -/
theorem secularFun_strictMono_on_interval {n M : Nat} (es : EigenStructure n M)
    (hM : M > 0) (s : Real) (lambda1 lambda2 : Real)
    (hlt : lambda1 < lambda2)
    (hne1 : ∀ k : Fin M, lambda1 ≠ s * es.eigenvalues k)
    (hne2 : ∀ k : Fin M, lambda2 ≠ s * es.eigenvalues k)
    -- Both λ₁, λ₂ are in the same interval (no pole between them)
    (h_same_interval : ∀ k : Fin M,
      (s * es.eigenvalues k < lambda1 ∧ s * es.eigenvalues k < lambda2) ∨
      (lambda1 < s * es.eigenvalues k ∧ lambda2 < s * es.eigenvalues k) ∨
      (s * es.eigenvalues k ≤ lambda1 ∧ lambda2 ≤ s * es.eigenvalues k)) :
    secularFun es hM s lambda1 < secularFun es hM s lambda2 := by
  -- Key insight: ∂F/∂λ = (1/N) Σ d_k/(sE_k - λ)² > 0 on each pole-free interval.
  -- So F is strictly increasing. The proof uses the mean value theorem:
  -- F(λ₂) - F(λ₁) = F'(c) · (λ₂ - λ₁) > 0 for some c ∈ (λ₁, λ₂).
  -- Alternatively, we show each term d_k/(sE_k - λ) is strictly increasing on the interval.
  --
  -- d/dλ [d_k/(sE_k - λ)] = d_k/(sE_k - λ)² > 0
  -- This means: for λ₁ < λ₂ in the same interval,
  --   d_k/(sE_k - λ₂) > d_k/(sE_k - λ₁) when sE_k > λ₂ (both denoms positive)
  --   d_k/(sE_k - λ₂) > d_k/(sE_k - λ₁) when λ₁ > sE_k (both denoms negative)
  sorry

/-! ## Root structure -/

/-- The secular function goes to +∞ as λ approaches a pole from below. -/
theorem secularFun_tendsto_top_from_below {n M : Nat} (es : EigenStructure n M)
    (hM : M > 0) (s : Real) (hs : 0 < s) (k : Fin M) :
    ∀ ε > 0, ∃ δ > 0, ∀ lambda,
      s * es.eigenvalues k - δ < lambda →
      lambda < s * es.eigenvalues k →
      secularFun es hM s lambda > 1/ε := by
  sorry -- TODO: d_k/(sE_k - λ) → +∞ as λ → (sE_k)⁻

/-- The secular function goes to -∞ as λ approaches a pole from above. -/
theorem secularFun_tendsto_bot_from_above {n M : Nat} (es : EigenStructure n M)
    (hM : M > 0) (s : Real) (hs : 0 < s) (k : Fin M) :
    ∀ ε > 0, ∃ δ > 0, ∀ lambda,
      s * es.eigenvalues k < lambda →
      lambda < s * es.eigenvalues k + δ →
      secularFun es hM s lambda < -(1/ε) := by
  sorry -- TODO: d_k/(sE_k - λ) → -∞ as λ → (sE_k)⁺

/-- Below the lowest pole, F(s,λ) → -1/(1-s) < 0 as λ → -∞. -/
theorem secularFun_neg_at_neg_infty {n M : Nat} (es : EigenStructure n M)
    (hM : M > 0) (s : Real) (hs : 0 < s ∧ s < 1) :
    ∀ ε > 0, ∃ L, ∀ lambda,
      lambda < L →
      (∀ k : Fin M, lambda < s * es.eigenvalues k) →
      |secularFun es hM s lambda + 1/(1-s)| < ε := by
  sorry -- TODO: Sum → 0 as λ → -∞

/-- There is exactly one root of F(s,·) in (-∞, s·E₀).
    This root is the ground state eigenvalue of H(s). -/
theorem exists_unique_root_below_ground {n M : Nat} (es : EigenStructure n M)
    (hM : M > 0) (s : Real) (hs : 0 < s ∧ s < 1) :
    ∃! lambda, lambda < s * es.eigenvalues ⟨0, hM⟩ ∧
      secularFun es hM s lambda = 0 := by
  sorry -- TODO: IVT + monotonicity

/-- The ground state eigenvalue of H(s) is determined by the secular equation.
    It is the unique λ < s·E₀ with F(s,λ) = 0. -/
theorem ground_eigenvalue_is_secular_root {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2) (s : Real) (hs : 0 < s ∧ s < 1) :
    ∃ E0 : Real,
      IsEigenvalue (adiabaticHam es s ⟨le_of_lt hs.1, le_of_lt hs.2⟩) E0 ∧
      E0 < s * es.eigenvalues ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_two hM⟩ ∧
      secularFun es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM) s E0 = 0 ∧
      (∀ E, IsEigenvalue (adiabaticHam es s ⟨le_of_lt hs.1, le_of_lt hs.2⟩) E → E0 ≤ E) := by
  sorry -- TODO: Combine secular equation with spectral theory

/-! ## Behavior near the avoided crossing -/

/-- At s = s*, the two eigenvalues closest to the crossing point are separated by g_min.

    The secular equation near s* reduces to a 2×2 effective system:
    F(s,λ) ≈ 0 gives λ²(s) ≈ λ_cross² + c·(s-s*)²
    where λ_cross corresponds to the crossing eigenvalue and c depends on A₁, A₂. -/
theorem gap_near_avoided_crossing {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2) (hcond : spectralConditionForBounds es hM)
    (s : Real) (hs : 0 < s ∧ s < 1) :
    ∃ (E0 E1 : Real),
      IsEigenvalue (adiabaticHam es s ⟨le_of_lt hs.1, le_of_lt hs.2⟩) E0 ∧
      IsEigenvalue (adiabaticHam es s ⟨le_of_lt hs.1, le_of_lt hs.2⟩) E1 ∧
      E0 < E1 ∧
      (∀ E, IsEigenvalue (adiabaticHam es s ⟨le_of_lt hs.1, le_of_lt hs.2⟩) E → E0 ≤ E) ∧
      -- The gap is bounded below by g_min/4
      E1 - E0 ≥ minimumGap es hM / 4 := by
  sorry -- TODO: Main spectral analysis result

end UAQO.Proofs.Spectral.SecularEquation
