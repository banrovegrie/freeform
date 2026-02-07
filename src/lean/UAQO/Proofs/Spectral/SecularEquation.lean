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
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.GroupWithZero

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
  -- Algebraic approach: show d/(a-λ₂) - d/(a-λ₁) > 0
  -- = d(λ₂-λ₁)/((a-λ₂)(a-λ₁)) > 0  since d > 0, λ₂-λ₁ > 0, product > 0
  set a := s * es.eigenvalues k
  set d := (es.degeneracies k : Real)
  have hd_pos : d > 0 := Nat.cast_pos.mpr (es.deg_positive k)
  have ha1 : a - lambda1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hne1)
  have ha2 : a - lambda2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hne2)
  suffices h : d / (a - lambda2) - d / (a - lambda1) > 0 by linarith
  rw [div_sub_div _ _ ha2 ha1]
  apply div_pos
  · -- Numerator: d*(a-λ₁) - (a-λ₂)*d = d*(λ₂-λ₁) > 0
    have hnum : d * (a - lambda1) - (a - lambda2) * d = d * (lambda2 - lambda1) := by ring
    rw [hnum]
    exact mul_pos hd_pos (sub_pos.mpr hlt)
  · -- Denominator: (a-λ₂)*(a-λ₁) > 0
    have hprod : (a - lambda2) * (a - lambda1) = (a - lambda1) * (a - lambda2) := mul_comm _ _
    rw [hprod]; exact hsame

/-- When two points are in the same interval between poles, the denominator products are positive. -/
private lemma same_interval_product_pos {a x y : Real}
    (h : (a < x ∧ a < y) ∨ (x < a ∧ y < a) ∨ (a ≤ x ∧ y ≤ a))
    (hlt : x < y) :
    (a - x) * (a - y) > 0 := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact mul_pos_of_neg_of_neg (sub_neg.mpr h1) (sub_neg.mpr h2)
  · exact mul_pos (sub_pos.mpr h1) (sub_pos.mpr h2)
  · linarith

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
  -- Each term d_k/(sE_k - λ) is strictly increasing in λ on each pole-free interval.
  -- Sum of strictly increasing functions is strictly increasing. The -1/(1-s) cancels.
  unfold secularFun
  -- Suffices to show the sum part is strictly increasing (constant cancels)
  suffices h_sum :
      (Finset.sum Finset.univ (fun k : Fin M =>
        (es.degeneracies k : Real) / (s * es.eigenvalues k - lambda1))) <
      (Finset.sum Finset.univ (fun k : Fin M =>
        (es.degeneracies k : Real) / (s * es.eigenvalues k - lambda2))) by
    have hN_pos : (1 : Real) / (qubitDim n : Real) > 0 :=
      div_pos one_pos (Nat.cast_pos.mpr (Nat.pow_pos (by norm_num : 0 < 2)))
    linarith [mul_lt_mul_of_pos_left h_sum hN_pos]
  apply Finset.sum_lt_sum
  · -- Each term: term(lambda1) ≤ term(lambda2)
    intro k _
    exact le_of_lt (secularTerm_strictMono es s lambda1 lambda2 k hlt (hne1 k) (hne2 k)
      (same_interval_product_pos (h_same_interval k) hlt))
  · -- At least one strict: use k = 0
    exact ⟨⟨0, hM⟩, Finset.mem_univ _, secularTerm_strictMono es s lambda1 lambda2 ⟨0, hM⟩ hlt
      (hne1 _) (hne2 _) (same_interval_product_pos (h_same_interval _) hlt)⟩

/-! ## Root structure -/

/-- Reverse triangle inequality: |a + b| ≥ |a| - |b|. -/
private lemma reverse_triangle (a b : Real) : |a + b| ≥ |a| - |b| := by
  have h := abs_sub_abs_le_abs_sub a (-b)
  rw [abs_neg] at h
  have : a - -b = a + b := by ring
  rw [this] at h
  -- h : ||a| - |b|| ≤ |a + b|
  linarith [le_abs_self (|a| - |b|)]

theorem secularFun_tendsto_top_from_below {n M : Nat} (es : EigenStructure n M)
    (hM : M > 0) (s : Real) (hs : 0 < s) (k : Fin M) :
    ∀ ε > 0, ∃ δ > 0, ∀ lambda,
      s * es.eigenvalues k - δ < lambda →
      lambda < s * es.eigenvalues k →
      secularFun es hM s lambda > 1/ε := by
  intro ε hε
  set N := (qubitDim n : Real) with hN_def
  set Ek := es.eigenvalues k
  have hN_pos : N > 0 := Nat.cast_pos.mpr (Nat.pow_pos (by norm_num : 0 < 2))
  have hdk_pos : (es.degeneracies k : Real) > 0 := Nat.cast_pos.mpr (es.deg_positive k)
  -- Distinct eigenvalues at different indices
  have hE_ne : ∀ j : Fin M, j ≠ k → es.eigenvalues j ≠ Ek := by
    intro j hj heq
    have : j.val ≠ k.val := fun h => hj (Fin.ext h)
    rcases Nat.lt_or_gt_of_ne this with h | h
    · exact absurd heq (ne_of_lt (es.eigenval_ordered j k h))
    · exact absurd heq.symm (ne_of_lt (es.eigenval_ordered k j h))
  set others := Finset.univ.filter (fun j : Fin M => j ≠ k)
  -- B = Σ_{j≠k} 2d_j/(s|Ej-Ek|) bounds the rest sum from below
  set B := others.sum (fun j => 2 * (es.degeneracies j : Real) / (s * |es.eigenvalues j - Ek|))
  have hB_nn : B ≥ 0 := Finset.sum_nonneg fun j _ =>
    div_nonneg (mul_nonneg two_pos.le (Nat.cast_nonneg _)) (mul_nonneg hs.le (abs_nonneg _))
  -- Minimum pole distance
  obtain ⟨δ₀, hδ₀_pos, hδ₀_le⟩ : ∃ δ₀ > 0, ∀ j : Fin M, j ≠ k →
      δ₀ ≤ s * |es.eigenvalues j - Ek| / 2 := by
    by_cases hM1 : M ≤ 1
    · exact ⟨1, one_pos, fun j hj => absurd (Fin.ext (show j.val = k.val by omega)) hj⟩
    · push_neg at hM1
      have hne : others.Nonempty := by
        rw [Finset.filter_nonempty_iff]
        by_cases hk0 : k.val = 0
        · exact ⟨⟨1, hM1⟩, Finset.mem_univ _, fun h => by simp [Fin.ext_iff] at h; omega⟩
        · exact ⟨⟨0, hM⟩, Finset.mem_univ _, fun h => by simp [Fin.ext_iff] at h; omega⟩
      let S := others.image (fun j => s * |es.eigenvalues j - Ek| / 2)
      refine ⟨S.min' (hne.image _), ?_, ?_⟩
      · have hmem := Finset.min'_mem S (hne.image _)
        simp only [S, Finset.mem_image] at hmem
        obtain ⟨j, hj, hj_eq⟩ := hmem
        rw [← hj_eq]
        exact div_pos (mul_pos hs (abs_pos.mpr (sub_ne_zero.mpr
          (hE_ne j (Finset.mem_filter.mp hj).2)))) two_pos
      · intro j hj
        exact Finset.min'_le S _ (Finset.mem_image.mpr
          ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩, rfl⟩)
  -- Target value for d_k/δ
  set T := N / ε + B + N * |1 / (1 - s)| + 1
  have hT_pos : T > 0 := by
    linarith [div_nonneg hN_pos.le hε.le, mul_nonneg hN_pos.le (abs_nonneg (1/(1-s)))]
  -- Choose δ
  use min δ₀ (↑(es.degeneracies k) / T)
  refine ⟨lt_min hδ₀_pos (div_pos hdk_pos hT_pos), ?_⟩
  intro lambda hL hU
  have hgp : s * Ek - lambda > 0 := sub_pos.mpr hU
  have hgs : s * Ek - lambda < min δ₀ (↑(es.degeneracies k) / T) := by linarith
  -- Pole separation: |sEj - λ| ≥ s|Ej-Ek|/2
  have hps : ∀ j : Fin M, j ≠ k →
      |s * es.eigenvalues j - lambda| ≥ s * |es.eigenvalues j - Ek| / 2 := by
    intro j hj
    have heq : s * es.eigenvalues j - lambda =
        s * (es.eigenvalues j - Ek) + (s * Ek - lambda) := by ring
    rw [heq]
    have habs_eq : |s * Ek - lambda| = s * Ek - lambda := abs_of_pos hgp
    calc |s * (es.eigenvalues j - Ek) + (s * Ek - lambda)|
        ≥ |s * (es.eigenvalues j - Ek)| - |s * Ek - lambda| := reverse_triangle _ _
      _ = s * |es.eigenvalues j - Ek| - |s * Ek - lambda| := by rw [abs_mul, abs_of_pos hs]
      _ = s * |es.eigenvalues j - Ek| - (s * Ek - lambda) := by rw [habs_eq]
      _ ≥ s * |es.eigenvalues j - Ek| - δ₀ := by linarith [lt_of_lt_of_le hgs (min_le_left _ _)]
      _ ≥ s * |es.eigenvalues j - Ek| / 2 := by linarith [hδ₀_le j hj]
  -- Each rest term: -(2d_j/(s|Ej-Ek|)) ≤ d_j/(sEj - λ)
  have hterm : ∀ j ∈ others,
      -(2 * ↑(es.degeneracies j) / (s * |es.eigenvalues j - Ek|)) ≤
      ↑(es.degeneracies j) / (s * es.eigenvalues j - lambda) := by
    intro j hj
    have hj_ne := (Finset.mem_filter.mp hj).2
    have hden_pos : s * |es.eigenvalues j - Ek| / 2 > 0 :=
      div_pos (mul_pos hs (abs_pos.mpr (sub_ne_zero.mpr (hE_ne j hj_ne)))) two_pos
    have hrewrite : 2 * ↑(es.degeneracies j) / (s * |es.eigenvalues j - Ek|) =
        ↑(es.degeneracies j) / (s * |es.eigenvalues j - Ek| / 2) := by ring
    rw [hrewrite]
    -- -(d/(a/2)) ≤ -(d/|sEj-λ|) ≤ d/(sEj-λ)
    have h1 : ↑(es.degeneracies j) / |s * es.eigenvalues j - lambda| ≤
        ↑(es.degeneracies j) / (s * |es.eigenvalues j - Ek| / 2) :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg _) hden_pos (hps j hj_ne)
    -- -|d/(sEj-λ)| ≤ d/(sEj-λ)
    have h2 : -(↑(es.degeneracies j) / |s * es.eigenvalues j - lambda|) ≤
        ↑(es.degeneracies j) / (s * es.eigenvalues j - lambda) := by
      rw [show ↑(es.degeneracies j) / |s * es.eigenvalues j - lambda| =
        |↑(es.degeneracies j) / (s * es.eigenvalues j - lambda)| from by
        rw [abs_div]; congr 1; exact (abs_of_nonneg (Nat.cast_nonneg _)).symm]
      exact neg_abs_le _
    linarith
  -- Rest sum ≥ -B
  have hrest : others.sum (fun j => ↑(es.degeneracies j) / (s * es.eigenvalues j - lambda)) ≥ -B := by
    have hB_neg : -B = others.sum (fun j => -(2 * ↑(es.degeneracies j) / (s * |es.eigenvalues j - Ek|))) :=
      (Finset.sum_neg_distrib ..).symm
    rw [hB_neg]
    exact Finset.sum_le_sum hterm
  -- Split full sum = k-th term + rest
  have hsplit : Finset.sum Finset.univ (fun j : Fin M =>
      ↑(es.degeneracies j) / (s * es.eigenvalues j - lambda)) =
    ↑(es.degeneracies k) / (s * Ek - lambda) +
    others.sum (fun j => ↑(es.degeneracies j) / (s * es.eigenvalues j - lambda)) := by
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ k)]
    congr 1; apply Finset.sum_congr
    · ext j; constructor
      · intro hj; exact Finset.mem_filter.mpr ⟨Finset.mem_univ j,
          (Finset.mem_erase.mp hj).1⟩
      · intro hj; exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp hj).2,
          Finset.mem_univ j⟩
    · intros; rfl
  -- d_k/(sEk - λ) > T (from δ choice)
  have hdk_large : ↑(es.degeneracies k) / (s * Ek - lambda) > T := by
    have hgs2 : s * Ek - lambda < ↑(es.degeneracies k) / T :=
      lt_of_lt_of_le hgs (min_le_right _ _)
    have h_mul : T * (s * Ek - lambda) < ↑(es.degeneracies k) := by
      calc T * (s * Ek - lambda) < T * (↑(es.degeneracies k) / T) :=
            mul_lt_mul_of_pos_left hgs2 hT_pos
        _ = ↑(es.degeneracies k) := by field_simp
    rw [gt_iff_lt]
    rwa [lt_div_iff₀ hgp]
  -- Assemble: F(s,λ) > 1/ε
  unfold secularFun
  rw [hsplit]
  have h_sum_lb : ↑(es.degeneracies k) / (s * Ek - lambda) +
      others.sum (fun j => ↑(es.degeneracies j) / (s * es.eigenvalues j - lambda)) ≥
      T - B := by linarith [hrest]
  have h_TB : (1 / N) * (T - B) - |1 / (1 - s)| ≥ 1 / ε := by
    have hTB_val : T - B = N / ε + N * |1 / (1 - s)| + 1 := by simp [T]; ring
    rw [hTB_val]
    have : (1 / N) * (N / ε + N * |1 / (1 - s)| + 1) =
      1 / ε + |1 / (1 - s)| + 1 / N := by field_simp
    linarith [div_pos one_pos hN_pos]
  -- -1/(1-s) ≥ -|1/(1-s)| since x ≤ |x|
  have h_abs_bound : -(1 / (1 - s)) ≥ -(|1 / (1 - s)|) := neg_le_neg (le_abs_self _)
  have h_neg_eq : -1 / (1 - s) = -(1 / (1 - s)) := neg_div _ _
  -- Now combine: (1/N)(sum) - 1/(1-s) ≥ (1/N)(T-B) - |1/(1-s)| ≥ 1/ε
  have hN_inv_pos : (1 : Real) / N > 0 := div_pos one_pos hN_pos
  nlinarith [mul_le_mul_of_nonneg_left h_sum_lb hN_inv_pos.le]

/-- The secular function goes to -∞ as λ approaches a pole from above. -/
theorem secularFun_tendsto_bot_from_above {n M : Nat} (es : EigenStructure n M)
    (hM : M > 0) (s : Real) (hs : 0 < s) (k : Fin M) :
    ∀ ε > 0, ∃ δ > 0, ∀ lambda,
      s * es.eigenvalues k < lambda →
      lambda < s * es.eigenvalues k + δ →
      secularFun es hM s lambda < -(1/ε) := by
  intro ε hε
  set N := (qubitDim n : Real) with hN_def
  set Ek := es.eigenvalues k
  have hN_pos : N > 0 := Nat.cast_pos.mpr (Nat.pow_pos (by norm_num : 0 < 2))
  have hdk_pos : (es.degeneracies k : Real) > 0 := Nat.cast_pos.mpr (es.deg_positive k)
  have hE_ne : ∀ j : Fin M, j ≠ k → es.eigenvalues j ≠ Ek := by
    intro j hj heq
    have : j.val ≠ k.val := fun h => hj (Fin.ext h)
    rcases Nat.lt_or_gt_of_ne this with h | h
    · exact absurd heq (ne_of_lt (es.eigenval_ordered j k h))
    · exact absurd heq.symm (ne_of_lt (es.eigenval_ordered k j h))
  set others := Finset.univ.filter (fun j : Fin M => j ≠ k)
  set B := others.sum (fun j => 2 * (es.degeneracies j : Real) / (s * |es.eigenvalues j - Ek|))
  obtain ⟨δ₀, hδ₀_pos, hδ₀_le⟩ : ∃ δ₀ > 0, ∀ j : Fin M, j ≠ k →
      δ₀ ≤ s * |es.eigenvalues j - Ek| / 2 := by
    by_cases hM1 : M ≤ 1
    · exact ⟨1, one_pos, fun j hj => absurd (Fin.ext (show j.val = k.val by omega)) hj⟩
    · push_neg at hM1
      have hne : others.Nonempty := by
        rw [Finset.filter_nonempty_iff]
        by_cases hk0 : k.val = 0
        · exact ⟨⟨1, hM1⟩, Finset.mem_univ _, fun h => by simp [Fin.ext_iff] at h; omega⟩
        · exact ⟨⟨0, hM⟩, Finset.mem_univ _, fun h => by simp [Fin.ext_iff] at h; omega⟩
      let S := others.image (fun j => s * |es.eigenvalues j - Ek| / 2)
      refine ⟨S.min' (hne.image _), ?_, ?_⟩
      · have hmem := Finset.min'_mem S (hne.image _)
        simp only [S, Finset.mem_image] at hmem
        obtain ⟨j, hj, hj_eq⟩ := hmem; rw [← hj_eq]
        exact div_pos (mul_pos hs (abs_pos.mpr (sub_ne_zero.mpr
          (hE_ne j (Finset.mem_filter.mp hj).2)))) two_pos
      · intro j hj
        exact Finset.min'_le S _ (Finset.mem_image.mpr
          ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩, rfl⟩)
  have hB_nn : B ≥ 0 := Finset.sum_nonneg fun j _ =>
    div_nonneg (mul_nonneg two_pos.le (Nat.cast_nonneg _)) (mul_nonneg hs.le (abs_nonneg _))
  set T := N / ε + B + N * |1 / (1 - s)| + 1
  have hT_pos : T > 0 := by
    linarith [div_nonneg hN_pos.le hε.le, mul_nonneg hN_pos.le (abs_nonneg (1/(1-s)))]
  use min δ₀ (↑(es.degeneracies k) / T)
  refine ⟨lt_min hδ₀_pos (div_pos hdk_pos hT_pos), ?_⟩
  intro lambda hL hU
  -- λ > sEk, so sEk - λ < 0 and λ - sEk > 0
  have hgn : s * Ek - lambda < 0 := sub_neg.mpr hL
  have hgp' : lambda - s * Ek > 0 := by linarith
  have hgs : lambda - s * Ek < min δ₀ (↑(es.degeneracies k) / T) := by linarith
  -- Pole separation (same as before — |sEk - λ| < δ₀)
  have hps : ∀ j : Fin M, j ≠ k →
      |s * es.eigenvalues j - lambda| ≥ s * |es.eigenvalues j - Ek| / 2 := by
    intro j hj
    have heq : s * es.eigenvalues j - lambda =
        s * (es.eigenvalues j - Ek) + (s * Ek - lambda) := by ring
    rw [heq]
    have habs_eq : |s * Ek - lambda| = lambda - s * Ek := by
      rw [abs_of_neg hgn]; ring
    calc |s * (es.eigenvalues j - Ek) + (s * Ek - lambda)|
        ≥ |s * (es.eigenvalues j - Ek)| - |s * Ek - lambda| := reverse_triangle _ _
      _ = s * |es.eigenvalues j - Ek| - |s * Ek - lambda| := by rw [abs_mul, abs_of_pos hs]
      _ = s * |es.eigenvalues j - Ek| - (lambda - s * Ek) := by rw [habs_eq]
      _ ≥ s * |es.eigenvalues j - Ek| - δ₀ := by linarith [lt_of_lt_of_le hgs (min_le_left _ _)]
      _ ≥ s * |es.eigenvalues j - Ek| / 2 := by linarith [hδ₀_le j hj]
  -- Each rest term upper bounded: d_j/(sEj-λ) ≤ 2d_j/(s|Ej-Ek|)
  have hterm : ∀ j ∈ others,
      ↑(es.degeneracies j) / (s * es.eigenvalues j - lambda) ≤
      2 * ↑(es.degeneracies j) / (s * |es.eigenvalues j - Ek|) := by
    intro j hj
    have hj_ne := (Finset.mem_filter.mp hj).2
    have hden_pos : s * |es.eigenvalues j - Ek| / 2 > 0 :=
      div_pos (mul_pos hs (abs_pos.mpr (sub_ne_zero.mpr (hE_ne j hj_ne)))) two_pos
    -- d/(sEj-λ) ≤ |d/(sEj-λ)| = d/|sEj-λ| ≤ 2d/(s|Ej-Ek|)
    calc ↑(es.degeneracies j) / (s * es.eigenvalues j - lambda)
        ≤ |↑(es.degeneracies j) / (s * es.eigenvalues j - lambda)| := le_abs_self _
      _ = ↑(es.degeneracies j) / |s * es.eigenvalues j - lambda| := by
          rw [abs_div, abs_of_nonneg (Nat.cast_nonneg' _)]
      _ ≤ ↑(es.degeneracies j) / (s * |es.eigenvalues j - Ek| / 2) :=
          div_le_div_of_nonneg_left (Nat.cast_nonneg _) hden_pos (hps j hj_ne)
      _ = 2 * ↑(es.degeneracies j) / (s * |es.eigenvalues j - Ek|) := by ring
  -- Rest sum ≤ B
  have hrest : others.sum (fun j => ↑(es.degeneracies j) / (s * es.eigenvalues j - lambda)) ≤ B :=
    Finset.sum_le_sum hterm
  -- Split full sum
  have hsplit : Finset.sum Finset.univ (fun j : Fin M =>
      ↑(es.degeneracies j) / (s * es.eigenvalues j - lambda)) =
    ↑(es.degeneracies k) / (s * Ek - lambda) +
    others.sum (fun j => ↑(es.degeneracies j) / (s * es.eigenvalues j - lambda)) := by
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ k)]
    congr 1; apply Finset.sum_congr
    · ext j; constructor
      · intro hj; exact Finset.mem_filter.mpr ⟨Finset.mem_univ j,
          (Finset.mem_erase.mp hj).1⟩
      · intro hj; exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp hj).2,
          Finset.mem_univ j⟩
    · intros; rfl
  -- d_k/(sEk-λ) < -T (since sEk-λ < 0 and |sEk-λ| < δ ≤ dk/T)
  have hdk_neg : ↑(es.degeneracies k) / (s * Ek - lambda) < -T := by
    -- d_k/(sEk-λ) = -d_k/(λ-sEk), and λ-sEk < dk/T, so d_k/(λ-sEk) > T
    have hgs2 : lambda - s * Ek < ↑(es.degeneracies k) / T :=
      lt_of_lt_of_le hgs (min_le_right _ _)
    have h_pos_large : ↑(es.degeneracies k) / (lambda - s * Ek) > T := by
      have h_mul : T * (lambda - s * Ek) < ↑(es.degeneracies k) := by
        calc T * (lambda - s * Ek) < T * (↑(es.degeneracies k) / T) :=
              mul_lt_mul_of_pos_left hgs2 hT_pos
          _ = ↑(es.degeneracies k) := by field_simp
      rw [gt_iff_lt]; rwa [lt_div_iff₀ hgp']
    -- dk/(sEk-λ) = -dk/(λ-sEk) < -T
    have : ↑(es.degeneracies k) / (s * Ek - lambda) =
        -(↑(es.degeneracies k) / (lambda - s * Ek)) := by
      rw [show s * Ek - lambda = -(lambda - s * Ek) from by ring, div_neg]
    linarith
  -- Assemble: F(s,λ) < -(1/ε)
  unfold secularFun; rw [hsplit]
  have h_sum_ub : ↑(es.degeneracies k) / (s * Ek - lambda) +
      others.sum (fun j => ↑(es.degeneracies j) / (s * es.eigenvalues j - lambda)) <
      -T + B := by linarith [hrest]
  have h_TB : (1 / N) * (-T + B) + |1 / (1 - s)| ≤ -(1 / ε) := by
    have hTB_val : -T + B = -(N / ε + N * |1 / (1 - s)| + 1) := by simp [T]; ring
    rw [hTB_val]
    have : (1 / N) * (-(N / ε + N * |1 / (1 - s)| + 1)) =
      -(1 / ε + |1 / (1 - s)| + 1 / N) := by field_simp
    linarith [div_pos one_pos hN_pos]
  have h_abs_ub : -(1 / (1 - s)) ≤ |1 / (1 - s)| := by
    linarith [neg_abs_le (1 / (1 - s))]
  have hN_inv_pos : (1 : Real) / N > 0 := div_pos one_pos hN_pos
  nlinarith [mul_lt_mul_of_pos_left h_sum_ub hN_inv_pos]

/-- Below the lowest pole, F(s,λ) → -1/(1-s) < 0 as λ → -∞. -/
theorem secularFun_neg_at_neg_infty {n M : Nat} (es : EigenStructure n M)
    (hM : M > 0) (s : Real) (hs : 0 < s ∧ s < 1) :
    ∀ ε > 0, ∃ L, ∀ lambda,
      lambda < L →
      (∀ k : Fin M, lambda < s * es.eigenvalues k) →
      |secularFun es hM s lambda + 1/(1-s)| < ε := by
  intro ε hε
  -- Choose L so that sE₀ - λ > 1/ε
  use s * es.eigenvalues ⟨0, hM⟩ - 1/ε
  intro lambda hL h_below
  -- Abbreviations
  set N := (qubitDim n : Real) with hN_def
  set E₀ := es.eigenvalues ⟨0, hM⟩
  -- Positivity
  have hN_pos : N > 0 := Nat.cast_pos.mpr (Nat.pow_pos (by norm_num : 0 < 2))
  have hdiff_pos : ∀ k : Fin M, s * es.eigenvalues k - lambda > 0 :=
    fun k => sub_pos.mpr (h_below k)
  -- Key identity: secularFun + 1/(1-s) = (1/N) * Σ d_k/(sE_k - λ)
  -- Since value ≥ 0, suffices to show value < ε
  suffices h_bound : (1 / N) * Finset.sum Finset.univ (fun k : Fin M =>
      (es.degeneracies k : Real) / (s * es.eigenvalues k - lambda)) < ε by
    have hkey : secularFun es hM s lambda + 1 / (1 - s) =
        (1 / N) * Finset.sum Finset.univ (fun k : Fin M =>
          (es.degeneracies k : Real) / (s * es.eigenvalues k - lambda)) := by
      unfold secularFun; ring
    rw [hkey]
    have hnn : 0 ≤ (1 / N) * Finset.sum Finset.univ (fun k : Fin M =>
        (es.degeneracies k : Real) / (s * es.eigenvalues k - lambda)) :=
      mul_nonneg (div_nonneg one_pos.le hN_pos.le)
        (Finset.sum_nonneg fun k _ => le_of_lt (div_pos (Nat.cast_pos.mpr (es.deg_positive k)) (hdiff_pos k)))
    rw [abs_of_nonneg hnn]; exact h_bound
  -- E₀ ≤ E_k for all k (eigenvalues ordered)
  have hE₀_min : ∀ k : Fin M, E₀ ≤ es.eigenvalues k := by
    intro k
    by_cases hk0 : (k : Nat) = 0
    · have : k = ⟨0, hM⟩ := Fin.ext hk0
      rw [this]
    · exact le_of_lt (es.eigenval_ordered ⟨0, hM⟩ k (show (0 : Nat) < k from by omega))
  -- sE₀ - λ > 0
  have hbase_pos : s * E₀ - lambda > 0 := hdiff_pos ⟨0, hM⟩
  -- sE₀ - λ > 1/ε
  have hbase_large : s * E₀ - lambda > 1 / ε := by linarith
  -- Each term d_k/(sE_k - λ) ≤ d_k/(sE₀ - λ)  [bigger denom → smaller frac]
  have h_term_le : ∀ k ∈ Finset.univ, (es.degeneracies k : Real) / (s * es.eigenvalues k - lambda) ≤
      (es.degeneracies k : Real) / (s * E₀ - lambda) := by
    intro k _
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) hbase_pos
    linarith [mul_le_mul_of_nonneg_left (hE₀_min k) (le_of_lt hs.1)]
  -- Σ d_k/(sE_k - λ) ≤ Σ d_k/(sE₀ - λ) = (Σ d_k)/(sE₀ - λ) = N/(sE₀ - λ)
  have hsum_le : Finset.sum Finset.univ (fun k : Fin M =>
      (es.degeneracies k : Real) / (s * es.eigenvalues k - lambda)) ≤
      N / (s * E₀ - lambda) := by
    calc Finset.sum Finset.univ (fun k => (↑(es.degeneracies k) : Real) / (s * es.eigenvalues k - lambda))
        ≤ Finset.sum Finset.univ (fun k => (↑(es.degeneracies k) : Real) / (s * E₀ - lambda)) :=
          Finset.sum_le_sum h_term_le
      _ = (Finset.sum Finset.univ (fun k : Fin M => (es.degeneracies k : Real))) / (s * E₀ - lambda) :=
          (Finset.sum_div ..).symm
      _ = N / (s * E₀ - lambda) := by
          congr 1
          -- Σ (d_k : ℝ) = N = qubitDim n
          rw [hN_def]
          have h := es.deg_sum  -- : Σ d_k = qubitDim n (in ℕ)
          exact_mod_cast h
  -- (1/N) * sum ≤ (1/N) * N/(sE₀ - λ) = 1/(sE₀ - λ) < ε
  calc (1 / N) * Finset.sum Finset.univ _
      ≤ (1 / N) * (N / (s * E₀ - lambda)) :=
        mul_le_mul_of_nonneg_left hsum_le (div_nonneg one_pos.le hN_pos.le)
    _ = 1 / (s * E₀ - lambda) := by field_simp
    _ < ε := by
        have h := (one_div_lt_one_div hbase_pos (div_pos one_pos hε)).mpr hbase_large
        rwa [one_div_one_div] at h

/-- The secular function is continuous on any interval below all poles. -/
private lemma secularFun_continuousOn {n M : Nat} (es : EigenStructure n M)
    (hM : M > 0) (s : Real) (a b : Real) (_hab : a ≤ b)
    (h_below : ∀ k : Fin M, b < s * es.eigenvalues k) :
    ContinuousOn (fun lambda => secularFun es hM s lambda) (Set.Icc a b) := by
  unfold secularFun
  -- F(λ) = (1/N) * Σ_k d_k/(sE_k - λ) - 1/(1-s)
  apply ContinuousOn.sub
  · -- (1/N) * Σ_k ...
    apply ContinuousOn.mul continuousOn_const
    apply continuousOn_finset_sum
    intro k _
    -- d_k / (sE_k - λ)
    apply ContinuousOn.div continuousOn_const
    · exact ContinuousOn.sub continuousOn_const continuousOn_id
    · intro lambda hl
      have : lambda ≤ b := (Set.mem_Icc.mp hl).2
      exact ne_of_gt (sub_pos.mpr (lt_of_le_of_lt this (h_below k)))
  · exact continuousOn_const

/-- There is exactly one root of F(s,·) in (-∞, s·E₀).
    This root is the ground state eigenvalue of H(s). -/
theorem exists_unique_root_below_ground {n M : Nat} (es : EigenStructure n M)
    (hM : M > 0) (s : Real) (hs : 0 < s ∧ s < 1) :
    ∃! lambda, lambda < s * es.eigenvalues ⟨0, hM⟩ ∧
      secularFun es hM s lambda = 0 := by
  set E₀ := es.eigenvalues ⟨0, hM⟩
  set sE₀ := s * E₀
  have hs_pos := hs.1
  have hs_lt1 := hs.2
  have h1ms_pos : 1 - s > 0 := by linarith
  -- Eigenvalue ordering: E₀ ≤ E_k for all k
  have hEk_ge : ∀ k : Fin M, E₀ ≤ es.eigenvalues k := by
    intro k
    by_cases hk0 : (k : Nat) = 0
    · have : k = ⟨0, hM⟩ := Fin.ext hk0; rw [this]
    · exact le_of_lt (es.eigenval_ordered ⟨0, hM⟩ k (show (0 : Nat) < k from by omega))
  -- Step 1: Point b where F(b) > 0 (near the first pole from below)
  obtain ⟨δ, hδ_pos, hδ⟩ := secularFun_tendsto_top_from_below es hM s hs_pos ⟨0, hM⟩ 1 one_pos
  set b := sE₀ - δ / 2 with hb_def
  have hb_lt : b < sE₀ := by rw [hb_def]; linarith
  have hb_range : sE₀ - δ < b := by rw [hb_def]; linarith
  have hFb : secularFun es hM s b > 0 := by linarith [hδ b hb_range hb_lt]
  -- Step 2: Point a where F(a) < 0 (far left, using neg_at_neg_infty)
  have hε_pos : (0 : Real) < 1 / (2 * (1 - s)) := div_pos one_pos (mul_pos two_pos h1ms_pos)
  obtain ⟨L, hL⟩ := secularFun_neg_at_neg_infty es hM s hs (1 / (2 * (1 - s))) hε_pos
  set a := min (L - 1) (b - 1)
  have ha_lt_L : a < L := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have ha_lt_b : a < b := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have ha_le_b : a ≤ b := le_of_lt ha_lt_b
  have ha_lt_sE₀ : a < sE₀ := lt_trans ha_lt_b hb_lt
  -- a is below all poles
  have ha_below : ∀ k : Fin M, a < s * es.eigenvalues k := by
    intro k
    calc a < sE₀ := ha_lt_sE₀
      _ ≤ s * es.eigenvalues k := mul_le_mul_of_nonneg_left (hEk_ge k) hs_pos.le
  -- F(a) < 0
  have hFa : secularFun es hM s a < 0 := by
    have h := hL a ha_lt_L (fun k => ha_below k)
    rw [abs_lt] at h
    have hval : -(1 / (1 - s)) + 1 / (2 * (1 - s)) = -(1 / (2 * (1 - s))) := by
      field_simp; ring
    linarith [h.2, hε_pos]
  -- b is below all poles
  have hb_below : ∀ k : Fin M, b < s * es.eigenvalues k := by
    intro k
    calc b < sE₀ := hb_lt
      _ ≤ s * es.eigenvalues k := mul_le_mul_of_nonneg_left (hEk_ge k) hs_pos.le
  -- Step 3: Continuity of F on [a, b]
  have hcont : ContinuousOn (fun lambda => secularFun es hM s lambda) (Set.Icc a b) :=
    secularFun_continuousOn es hM s a b ha_le_b hb_below
  -- Step 4: Apply IVT to get a root in [a, b]
  have h_ivt : (0 : Real) ∈ (fun lambda => secularFun es hM s lambda) '' Set.Icc a b := by
    have := intermediate_value_Icc ha_le_b hcont
    apply this
    exact ⟨le_of_lt hFa, le_of_lt hFb⟩
  obtain ⟨r, hr_in, hFr⟩ := h_ivt
  have hr_le_b : r ≤ b := (Set.mem_Icc.mp hr_in).2
  have hr_lt_sE₀ : r < sE₀ := lt_of_le_of_lt hr_le_b hb_lt
  -- Helper: any point < sE₀ is below all poles and not equal to any pole
  have below_poles : ∀ x, x < sE₀ → ∀ k : Fin M, x < s * es.eigenvalues k := by
    intro x hx k; exact lt_of_lt_of_le hx (mul_le_mul_of_nonneg_left (hEk_ge k) hs_pos.le)
  have ne_poles : ∀ x, x < sE₀ → ∀ k : Fin M, x ≠ s * es.eigenvalues k := by
    intro x hx k; exact ne_of_lt (below_poles x hx k)
  -- Step 5: Existence + Uniqueness
  refine ⟨r, ⟨hr_lt_sE₀, hFr⟩, ?_⟩
  -- Uniqueness: strict monotonicity on (-∞, sE₀)
  intro r' ⟨hr'_lt, hFr'⟩
  by_contra h_ne
  -- Both r and r' are below sE₀, so F is strictly monotone between them
  have h_mono : ∀ x y, x < y → y < sE₀ →
      secularFun es hM s x < secularFun es hM s y := by
    intro x y hxy hy
    exact secularFun_strictMono_on_interval es hM s x y hxy
      (ne_poles x (lt_trans hxy hy)) (ne_poles y hy)
      (fun k => Or.inr (Or.inl ⟨below_poles x (lt_trans hxy hy) k, below_poles y hy k⟩))
  rcases lt_or_gt_of_ne h_ne with hlt | hlt
  · linarith [h_mono r' r hlt hr_lt_sE₀]
  · linarith [h_mono r r' hlt hr'_lt]


/-- The ground state eigenvalue of H(s) is determined by the secular equation.
    It is the unique λ < s·E₀ with F(s,λ) = 0.

    PROOF STRATEGY:
    1. exists_unique_root_below_ground gives unique root r < s·E₀ with F(s,r) = 0
    2. secular_equation_characterizes_eigenvalues (backward): F = 0 → IsEigenvalue
    3. Every eigenvalue E satisfies eigenvalue_condition_proof:
       (a) E = s·E_k (degenerate) ≥ s·E₀ > r, or
       (b) F(s,E) = 0; if E < s·E₀ then uniqueness gives E = r, else E ≥ s·E₀ > r -/
theorem ground_eigenvalue_is_secular_root {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2) (s : Real) (hs : 0 < s ∧ s < 1) :
    ∃ E0 : Real,
      IsEigenvalue (adiabaticHam es s ⟨le_of_lt hs.1, le_of_lt hs.2⟩) E0 ∧
      E0 < s * es.eigenvalues ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_two hM⟩ ∧
      secularFun es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM) s E0 = 0 ∧
      (∀ E, IsEigenvalue (adiabaticHam es s ⟨le_of_lt hs.1, le_of_lt hs.2⟩) E → E0 ≤ E) := by
  have hM0 : M > 0 := Nat.lt_of_lt_of_le Nat.zero_lt_two hM
  -- Step 1: Get unique secular root r < s·E₀ with F(s,r) = 0
  obtain ⟨r, ⟨hr_lt, hFr⟩, hr_unique⟩ := exists_unique_root_below_ground es hM0 s hs
  -- Step 2: Eigenvalue ordering: E₀ ≤ E_k for all k
  have hEk_ge : ∀ k : Fin M, es.eigenvalues ⟨0, hM0⟩ ≤ es.eigenvalues k := by
    intro k
    by_cases hk0 : (k : Nat) = 0
    · have : k = ⟨0, hM0⟩ := Fin.ext hk0; rw [this]
    · exact le_of_lt (es.eigenval_ordered ⟨0, hM0⟩ k (show (0 : Nat) < k from by omega))
  -- r < s·E_k for all k
  have hr_below : ∀ k : Fin M, r < s * es.eigenvalues k :=
    fun k => lt_of_lt_of_le hr_lt (mul_le_mul_of_nonneg_left (hEk_ge k) hs.1.le)
  -- r ≠ s·E_k for all k
  have hr_ne : ∀ k : Fin M, r ≠ s * es.eigenvalues k :=
    fun k => ne_of_lt (hr_below k)
  -- Step 3: r is an eigenvalue via secular equation characterization (backward direction)
  have hr_eig : IsEigenvalue (adiabaticHam es s ⟨le_of_lt hs.1, le_of_lt hs.2⟩) r :=
    (secular_equation_characterizes_eigenvalues es hM0 s hs r hr_ne).mpr hFr
  -- Step 4: r ≤ all eigenvalues (the minimality argument)
  refine ⟨r, hr_eig, hr_lt, hFr, ?_⟩
  intro E hE
  -- Use eigenvalue characterization: E is either degenerate or secular
  have hE_cond := (eigenvalue_condition_proof es hM0 s hs E).mp hE
  rcases hE_cond with ⟨z, hz_eq, _⟩ | ⟨hE_ne, hE_sec⟩
  · -- Degenerate case: E = s·E(z) ≥ s·E₀ > r
    rw [hz_eq]; exact le_of_lt (hr_below (es.assignment z))
  · -- Secular case: E ≠ s·E_k and secular equation holds
    by_cases hE_lt : E < s * es.eigenvalues ⟨0, hM0⟩
    · -- E < s·E₀: E is a secular root below first pole, so E = r by uniqueness
      have hFE : secularFun es hM0 s E = 0 := by
        unfold secularFun; linarith [hE_sec]
      exact le_of_eq (hr_unique E ⟨hE_lt, hFE⟩).symm
    · -- E ≥ s·E₀ > r
      push_neg at hE_lt; linarith [hr_lt]

end UAQO.Proofs.Spectral.SecularEquation
