/-
  Spectral parameters A_p for diagonal Hamiltonians.

  These parameters are central to the paper: they determine the position of the
  avoided crossing (via A_1) and appear in the running time bound.

  Definition from the paper (Eq. 5):
    A_p = (1/N) Σ_{k=1}^{M-1} d_k / (E_k - E_0)^p

  where p ∈ ℕ.
-/
import UAQO.Spectral.DiagonalHamiltonian

namespace UAQO

/-! ## Spectral parameters -/

/-- The spectral parameter A_p = (1/N) Σ_{k≥1} d_k / (E_k - E_0)^p -/
noncomputable def spectralParam {n M : Nat} (es : EigenStructure n M)
    (hM : M > 0) (p : Nat) : Real :=
  let E0 := es.eigenvalues ⟨0, hM⟩
  let N := qubitDim n
  (1 / N) * Finset.sum (Finset.filter (fun k => k.val > 0) Finset.univ)
    (fun k => (es.degeneracies k : Real) / (es.eigenvalues k - E0)^p)

notation "A_" p => spectralParam _ _ p

/-- A_1 specifically, most important for the avoided crossing position -/
noncomputable def A1 {n M : Nat} (es : EigenStructure n M) (hM : M > 0) : Real :=
  spectralParam es hM 1

/-- A_2, appears in the running time and minimum gap -/
noncomputable def A2 {n M : Nat} (es : EigenStructure n M) (hM : M > 0) : Real :=
  spectralParam es hM 2

/-! ## Spectral parameters for partial eigenstructures -/

/-- A_1 for partial eigenstructures. Terms with d_k = 0 contribute 0.
    This is well-defined even for UNSAT formulas where d_0 = 0. -/
noncomputable def A1_partial {n M : Nat} (pes : PartialEigenStructure n M)
    (hM : M > 0) : Real :=
  let E0 := pes.eigenvalues ⟨0, hM⟩
  let N := qubitDim n
  (1 / N) * Finset.sum (Finset.filter (fun k : Fin M => k.val > 0) Finset.univ)
    (fun k => (pes.degeneracies k : Real) / (pes.eigenvalues k - E0))

/-- A_p for partial eigenstructures (generalized) -/
noncomputable def spectralParam_partial {n M : Nat} (pes : PartialEigenStructure n M)
    (hM : M > 0) (p : Nat) : Real :=
  let E0 := pes.eigenvalues ⟨0, hM⟩
  let N := qubitDim n
  (1 / N) * Finset.sum (Finset.filter (fun k : Fin M => k.val > 0) Finset.univ)
    (fun k => (pes.degeneracies k : Real) / (pes.eigenvalues k - E0)^p)

/-- A1_partial agrees with A1 when all degeneracies are positive -/
theorem A1_partial_eq_A1 {n M : Nat} (es : EigenStructure n M) (hM : M > 0) :
    A1_partial es.toPartial hM = A1 es hM := by
  simp only [A1_partial, A1, spectralParam, EigenStructure.toPartial, pow_one]

/-! ## The function f(x) for #P-hardness -/

/-- The function f(x) = (1/2^n) * sum_k d_k/(Delta_k + x/2) for #P-hardness.

    PAPER REFERENCE: Eq. 14, line 898 in the paper.

    This function arises from the beta-modified Hamiltonian H'(x) where:
    - Eigenvalues are E_{2k} = E_k and E_{2k+1} = E_k + x/2
    - f(x) relates to A_1(H'(x)) via a product with the denominator polynomial

    Key property: f(x) is a rational function whose numerator P(x) has degree M-1.
    The coefficients of P encode the degeneracies d_k, enabling extraction via
    Lagrange interpolation. -/
noncomputable def sharpPFunction {n M : Nat} (es : EigenStructure n M)
    (hM : M > 0) (x : Real) : Real :=
  let E0 := es.eigenvalues ⟨0, hM⟩
  let N := qubitDim n
  (1 / N) * Finset.sum Finset.univ (fun k : Fin M =>
    (es.degeneracies k : Real) / (es.eigenvalues k - E0 + x / 2))

/-- The denominator polynomial: prod_k (Delta_k + x/2).

    When multiplied by f(x), this yields a polynomial P(x) of degree M-1
    whose coefficients encode the degeneracies. -/
noncomputable def sharpPDenominator {n M : Nat} (es : EigenStructure n M)
    (hM : M > 0) (x : Real) : Real :=
  let E0 := es.eigenvalues ⟨0, hM⟩
  Finset.prod Finset.univ (fun k : Fin M => es.eigenvalues k - E0 + x / 2)

/-- The numerator polynomial P(x) = prod_k(Delta_k + x/2) * f(x).

    This polynomial has degree M-1 and its evaluations at -2*Delta_k
    (appropriately scaled) yield the degeneracies d_k. -/
noncomputable def sharpPNumerator {n M : Nat} (es : EigenStructure n M)
    (hM : M > 0) (x : Real) : Real :=
  sharpPDenominator es hM x * sharpPFunction es hM x

/-! ## Key properties of spectral parameters -/

/-- A_p is positive for p ≥ 1 when M ≥ 2 -/
theorem spectralParam_positive {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2) (p : Nat) (_hp : p >= 1) :
    spectralParam es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM) p > 0 := by
  simp only [spectralParam]
  apply mul_pos
  · apply div_pos one_pos
    simp only [qubitDim]
    exact Nat.cast_pos.mpr (Nat.pow_pos (by norm_num : 0 < 2))
  · apply Finset.sum_pos
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      apply div_pos
      · exact Nat.cast_pos.mpr (es.deg_positive k)
      · apply pow_pos
        have h0 : (0 : Nat) < M := Nat.lt_of_lt_of_le Nat.zero_lt_two hM
        have hord := es.eigenval_ordered ⟨0, h0⟩ k
        linarith [hord hk]
    · use ⟨1, hM⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      norm_num

/-- A_2 ≤ (N-d_0)/N * Δ^{-2} = (1 - d_0/N) / Δ²

    A₂ = (1/N) Σ_{k≥1} d_k / (E_k - E₀)² and each term has (E_k - E₀)² ≥ Δ²,
    so d_k/(E_k - E₀)² ≤ d_k/Δ², giving A₂ ≤ (1/N) Σ_{k≥1} d_k/Δ² = (N-d₀)/(NΔ²).

    Note: The original axiom incorrectly claimed this was a lower bound. -/
theorem A2_upper_bound {n M : Nat} (es : EigenStructure n M) (hM : M >= 2) :
    A2 es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM) <=
    (1 - (es.degeneracies ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_two hM⟩ : Real) / qubitDim n) /
    (spectralGapDiag es hM)^2 := by
  -- Setup
  simp only [A2, spectralParam, spectralGapDiag]
  have hM0 : M > 0 := Nat.lt_of_lt_of_le Nat.zero_lt_two hM
  have hN : (qubitDim n : Real) > 0 := Nat.cast_pos.mpr (Nat.pow_pos (by norm_num : 0 < 2))
  have hE0 : es.eigenvalues ⟨0, hM0⟩ = 0 := es.ground_energy_zero hM0
  have hDelta : es.eigenvalues ⟨1, hM⟩ - es.eigenvalues ⟨0, hM0⟩ > 0 := by
    have h := es.eigenval_ordered ⟨0, hM0⟩ ⟨1, hM⟩
    simp only [Fin.mk_lt_mk] at h
    linarith [h Nat.zero_lt_one]
  let Delta := es.eigenvalues ⟨1, hM⟩ - es.eigenvalues ⟨0, hM0⟩
  -- Key: for k >= 1, (E_k - E_0)^2 >= Delta^2, so d_k/(E_k - E_0)^2 <= d_k/Delta^2
  have hterm_bound : ∀ k ∈ Finset.filter (fun k : Fin M => k.val > 0) Finset.univ,
      (es.degeneracies k : Real) / (es.eigenvalues k - es.eigenvalues ⟨0, hM0⟩)^2 <=
      (es.degeneracies k : Real) / Delta^2 := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    have hk1 : k ≥ ⟨1, hM⟩ := by
      simp only [Fin.le_iff_val_le_val]
      omega
    have hEk : es.eigenvalues k - es.eigenvalues ⟨0, hM0⟩ >= Delta := by
      have h1 : es.eigenvalues ⟨1, hM⟩ <= es.eigenvalues k := by
        cases Nat.lt_or_eq_of_le hk1 with
        | inl hlt => exact le_of_lt (es.eigenval_ordered ⟨1, hM⟩ k hlt)
        | inr heq =>
          have hkeq : k = ⟨1, hM⟩ := Fin.ext heq.symm
          rw [hkeq]
      linarith
    have hdk : (es.degeneracies k : Real) >= 0 := Nat.cast_nonneg _
    have hDelta_sq : Delta^2 > 0 := sq_pos_of_pos hDelta
    have hEk_sq : (es.eigenvalues k - es.eigenvalues ⟨0, hM0⟩)^2 >= Delta^2 := by
      apply sq_le_sq' (by linarith) hEk
    apply div_le_div_of_nonneg_left hdk hDelta_sq hEk_sq
  -- Sum of terms is bounded
  have hsum_bound : Finset.sum (Finset.filter (fun k : Fin M => k.val > 0) Finset.univ)
      (fun k => (es.degeneracies k : Real) / (es.eigenvalues k - es.eigenvalues ⟨0, hM0⟩)^2) <=
    Finset.sum (Finset.filter (fun k : Fin M => k.val > 0) Finset.univ)
      (fun k => (es.degeneracies k : Real) / Delta^2) := Finset.sum_le_sum hterm_bound
  -- Factor out 1/Delta^2
  have hsum_factor : Finset.sum (Finset.filter (fun k : Fin M => k.val > 0) Finset.univ)
      (fun k => (es.degeneracies k : Real) / Delta^2) =
    (1 / Delta^2) * Finset.sum (Finset.filter (fun k : Fin M => k.val > 0) Finset.univ)
      (fun k => (es.degeneracies k : Real)) := by
    rw [← Finset.sum_div]
    have hDelta_sq : Delta^2 ≠ 0 := ne_of_gt (sq_pos_of_pos hDelta)
    field_simp
  -- Sum of degeneracies for k >= 1 is N - d_0
  have hsum_deg : Finset.sum (Finset.filter (fun k : Fin M => k.val > 0) Finset.univ)
      (fun k => (es.degeneracies k : Real)) =
    (qubitDim n : Real) - (es.degeneracies ⟨0, hM0⟩ : Real) := by
    have htotal : Finset.sum Finset.univ (fun k : Fin M => (es.degeneracies k : Real)) =
        (qubitDim n : Real) := by
      have h := es.deg_sum
      simp only [← Nat.cast_sum] at h ⊢
      exact congrArg Nat.cast h
    -- Split the full sum into k=0 and k>0 parts
    have h0_only : Finset.filter (fun k : Fin M => ¬k.val > 0) Finset.univ = {⟨0, hM0⟩} := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, not_lt,
                 Nat.le_zero]
      constructor
      · intro hk; ext; exact hk
      · intro hk; simp [hk]
    have hsplit : Finset.sum Finset.univ (fun k : Fin M => (es.degeneracies k : Real)) =
        Finset.sum (Finset.filter (fun k : Fin M => ¬k.val > 0) Finset.univ)
          (fun k => (es.degeneracies k : Real)) +
        Finset.sum (Finset.filter (fun k : Fin M => k.val > 0) Finset.univ)
          (fun k => (es.degeneracies k : Real)) := by
      rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
          (p := fun k : Fin M => k.val > 0)]
      ring
    rw [h0_only, Finset.sum_singleton] at hsplit
    linarith [htotal, hsplit]
  -- Now put it all together
  calc (1 / qubitDim n) * Finset.sum (Finset.filter (fun k => k.val > 0) Finset.univ)
         (fun k => (es.degeneracies k : Real) / (es.eigenvalues k - es.eigenvalues ⟨0, hM0⟩)^2)
      <= (1 / qubitDim n) * Finset.sum (Finset.filter (fun k => k.val > 0) Finset.univ)
           (fun k => (es.degeneracies k : Real) / Delta^2) := by
        apply mul_le_mul_of_nonneg_left hsum_bound (div_nonneg one_pos.le hN.le)
    _ = (1 / qubitDim n) * ((1 / Delta^2) * Finset.sum (Finset.filter (fun k => k.val > 0) Finset.univ)
           (fun k => (es.degeneracies k : Real))) := by rw [hsum_factor]
    _ = (1 / qubitDim n) * ((1 / Delta^2) * ((qubitDim n : Real) - (es.degeneracies ⟨0, hM0⟩ : Real))) := by
        rw [hsum_deg]
    _ = (1 - (es.degeneracies ⟨0, hM0⟩ : Real) / qubitDim n) / Delta^2 := by
        have hDelta_sq : Delta^2 ≠ 0 := ne_of_gt (sq_pos_of_pos hDelta)
        field_simp

/-- Simpler lower bound: A_2 ≥ d₁/(NΔ²) where d₁ is the first excited state degeneracy.
    This follows because the k=1 term alone in the sum gives this contribution. -/
theorem A2_lower_bound_simple {n M : Nat} (es : EigenStructure n M) (hM : M >= 2) :
    A2 es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM) >=
    (es.degeneracies ⟨1, hM⟩ : Real) / (qubitDim n * (spectralGapDiag es hM)^2) := by
  simp only [A2, spectralParam, spectralGapDiag]
  have hM0 : M > 0 := Nat.lt_of_lt_of_le Nat.zero_lt_two hM
  have hN : (qubitDim n : Real) > 0 := Nat.cast_pos.mpr (Nat.pow_pos (by norm_num : 0 < 2))
  have hDelta : es.eigenvalues ⟨1, hM⟩ - es.eigenvalues ⟨0, hM0⟩ > 0 := by
    have h := es.eigenval_ordered ⟨0, hM0⟩ ⟨1, hM⟩
    simp only [Fin.mk_lt_mk] at h
    linarith [h Nat.zero_lt_one]
  have hE0 : es.eigenvalues ⟨0, hM0⟩ = 0 := es.ground_energy_zero hM0
  -- The k=1 term in the sum is d₁ / (E₁ - E₀)² = d₁ / Δ²
  have h1_in : ⟨1, hM⟩ ∈ Finset.filter (fun k : Fin M => k.val > 0) Finset.univ := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    norm_num
  have hterm_nonneg : ∀ k ∈ Finset.filter (fun k : Fin M => k.val > 0) Finset.univ,
      (es.degeneracies k : Real) / (es.eigenvalues k - es.eigenvalues ⟨0, hM0⟩)^2 >= 0 := by
    intro k _
    apply div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  have hsum_ge : Finset.sum (Finset.filter (fun k : Fin M => k.val > 0) Finset.univ)
      (fun k => (es.degeneracies k : Real) / (es.eigenvalues k - es.eigenvalues ⟨0, hM0⟩)^2) >=
      (es.degeneracies ⟨1, hM⟩ : Real) / (es.eigenvalues ⟨1, hM⟩ - es.eigenvalues ⟨0, hM0⟩)^2 := by
    apply Finset.single_le_sum hterm_nonneg h1_in
  calc (1 / qubitDim n) * Finset.sum (Finset.filter (fun k => k.val > 0) Finset.univ)
         (fun k => (es.degeneracies k : Real) / (es.eigenvalues k - es.eigenvalues ⟨0, hM0⟩)^2)
      >= (1 / qubitDim n) * ((es.degeneracies ⟨1, hM⟩ : Real) /
           (es.eigenvalues ⟨1, hM⟩ - es.eigenvalues ⟨0, hM0⟩)^2) := by
        apply mul_le_mul_of_nonneg_left hsum_ge (div_nonneg one_pos.le hN.le)
    _ = (es.degeneracies ⟨1, hM⟩ : Real) /
          (qubitDim n * (es.eigenvalues ⟨1, hM⟩ - es.eigenvalues ⟨0, hM0⟩)^2) := by
        field_simp

/-! ## The spectral condition (Definition 1 in the paper) -/

/-- The spectral condition: (1/Δ)√(d_0/(A_2 N)) < c for small constant c -/
def spectralCondition {n M : Nat} (es : EigenStructure n M) (hM : M >= 2)
    (c : Real) (_hc : c > 0) : Prop :=
  let d0 := es.degeneracies ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_two hM⟩
  let Delta := spectralGapDiag es hM
  let A2_val := A2 es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM)
  let N := qubitDim n
  (1 / Delta) * Real.sqrt (d0 / (A2_val * N)) < c

/-- For Ising Hamiltonians with Δ ≥ 1/poly(n), the spectral condition holds
    when c is large enough and the system parameters are suitable.
    The hypothesis hd0_small encodes the key requirement that d₀ is not too large
    relative to the other parameters. -/
theorem spectralCondition_ising {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2)
    (_hDelta : spectralGapDiag es hM >= 1 / (n : Real))
    (c : Real) (hc : c > 0) (_hcLarge : c >= 1 / (n : Real))
    (hd0_small : (es.degeneracies ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_two hM⟩ : Real) <
                 c^2 * (spectralGapDiag es hM)^2 *
                 A2 es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM) * qubitDim n) :
    spectralCondition es hM c hc := by
  simp only [spectralCondition]
  have hA2pos : A2 es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM) > 0 :=
    spectralParam_positive es hM 2 (by norm_num)
  have hNpos : (qubitDim n : Real) > 0 :=
    Nat.cast_pos.mpr (Nat.pow_pos (by norm_num : 0 < 2))
  have hDeltaPos : spectralGapDiag es hM > 0 := spectralGap_positive es hM
  have hd0pos : (es.degeneracies ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_two hM⟩ : Real) > 0 :=
    Nat.cast_pos.mpr (es.deg_positive _)
  have hdenom_pos : A2 es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM) * qubitDim n > 0 :=
    mul_pos hA2pos hNpos
  -- We need: (1/Δ) * √(d₀/(A₂N)) < c
  -- Rewrite as: √(d₀/(A₂N)) < Δ * c (note the order after inv_mul_lt_iff₀)
  rw [one_div, inv_mul_lt_iff₀ hDeltaPos]
  -- Need: √(d₀/(A₂N)) < Δ * c
  have hDeltac_pos : spectralGapDiag es hM * c > 0 := mul_pos hDeltaPos hc
  rw [Real.sqrt_lt' hDeltac_pos]
  -- Need: d₀/(A₂N) < (Δc)²
  rw [mul_pow, div_lt_iff₀ hdenom_pos]
  calc (es.degeneracies ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_two hM⟩ : Real)
      < c^2 * (spectralGapDiag es hM)^2 *
         A2 es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM) * qubitDim n := hd0_small
    _ = (spectralGapDiag es hM)^2 * c^2 *
         (A2 es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM) * qubitDim n) := by ring

/-! ## Key formulas involving A_1 -/

/-- The position of the avoided crossing: s* = A_1 / (A_1 + 1) -/
noncomputable def avoidedCrossingPosition {n M : Nat} (es : EigenStructure n M)
    (hM : M > 0) : Real :=
  let A1_val := A1 es hM
  A1_val / (A1_val + 1)

notation "s*" => avoidedCrossingPosition

/-- s* is in (0, 1) when A_1 > 0 -/
theorem avoidedCrossing_in_interval {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2) :
    0 < avoidedCrossingPosition es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM) ∧
    avoidedCrossingPosition es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM) < 1 := by
  simp only [avoidedCrossingPosition, A1]
  have hA1pos : spectralParam es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM) 1 > 0 :=
    spectralParam_positive es hM 1 (by norm_num)
  constructor
  · apply div_pos hA1pos
    linarith
  · rw [div_lt_one (by linarith : 0 < spectralParam es _ 1 + 1)]
    linarith

/-- The window around the avoided crossing: δ_s = 2/(A_1+1)² √(d_0 A_2/N) -/
noncomputable def avoidedCrossingWindow {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2) : Real :=
  let A1_val := A1 es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM)
  let A2_val := A2 es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM)
  let d0 := es.degeneracies ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_two hM⟩
  let N := qubitDim n
  2 / (A1_val + 1)^2 * Real.sqrt (d0 * A2_val / N)

notation "δ_s" => avoidedCrossingWindow

/-- The minimum spectral gap: g_min = (1-2*eta) * 2A_1/(A_1+1) * sqrt(d_0/(A_2*N))
    where eta = 0.1 is the perturbation parameter from Proposition 1 (Eq. 311).

    The (1-2*eta) = 0.8 prefactor arises from the secular equation analysis:
    the gap bound holds in the interval [s* - eta*delta_s, s* + eta*delta_s]
    rather than the full avoided crossing region. -/
noncomputable def minimumGap {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2) : Real :=
  let A1_val := A1 es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM)
  let A2_val := A2 es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM)
  let d0 := es.degeneracies ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_two hM⟩
  let N := qubitDim n
  (1 - 2 * (0.1 : Real)) * (2 * A1_val / (A1_val + 1) * Real.sqrt (d0 / (A2_val * N)))

notation "g_min" => minimumGap

/-- The minimum gap is positive -/
theorem minimumGap_pos {n M : Nat} (es : EigenStructure n M) (hM : M >= 2) :
    minimumGap es hM > 0 := by
  simp only [minimumGap]
  have hA1pos : A1 es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM) > 0 :=
    spectralParam_positive es hM 1 (by norm_num)
  have hA2pos : A2 es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM) > 0 :=
    spectralParam_positive es hM 2 (by norm_num)
  have hd0pos : (es.degeneracies ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_two hM⟩ : Real) > 0 :=
    Nat.cast_pos.mpr (es.deg_positive _)
  have hNpos : (qubitDim n : Real) > 0 :=
    Nat.cast_pos.mpr (Nat.pow_pos (by norm_num : 0 < 2))
  have hA1plus1_pos : A1 es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM) + 1 > 0 := by linarith
  have heta : (1 : Real) - 2 * 0.1 > 0 := by norm_num
  apply mul_pos heta
  apply mul_pos
  · exact div_pos (mul_pos (by norm_num : (2 : Real) > 0) hA1pos) hA1plus1_pos
  · exact Real.sqrt_pos.mpr (div_pos hd0pos (mul_pos hA2pos hNpos))

/-- The minimum gap scales as sqrt(d_0/N) -/
theorem minimumGap_scaling {n M : Nat} (es : EigenStructure n M) (hM : M >= 2) :
    ∃ (c : Real), c > 0 ∧
    minimumGap es hM <= c * Real.sqrt ((es.degeneracies ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_two hM⟩ : Real) / qubitDim n) := by
  simp only [minimumGap]
  let A1_val := A1 es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM)
  let A2_val := A2 es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM)
  let d0 := (es.degeneracies ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_two hM⟩ : Real)
  let N := (qubitDim n : Real)
  have hA2pos : A2_val > 0 := spectralParam_positive es hM 2 (by norm_num)
  have hA1pos : A1_val > 0 := spectralParam_positive es hM 1 (by norm_num)
  have hNpos : N > 0 := Nat.cast_pos.mpr (Nat.pow_pos (by norm_num : 0 < 2))
  have hd0nn : d0 >= 0 := Nat.cast_nonneg _
  have heta : (1 : Real) - 2 * 0.1 = 0.8 := by norm_num
  use 2 / Real.sqrt A2_val
  constructor
  · apply div_pos (by norm_num : (2 : Real) > 0)
    exact Real.sqrt_pos.mpr hA2pos
  · have h1 : A1_val / (A1_val + 1) < 1 := by
      rw [div_lt_one (by linarith)]
      linarith
    -- The (1-2*eta) factor is <= 1, so we can drop it
    have hprefactor_le : (1 : Real) - 2 * 0.1 <= 1 := by norm_num
    have hinner_nonneg : 2 * A1_val / (A1_val + 1) * Real.sqrt (d0 / (A2_val * N)) >= 0 := by
      apply mul_nonneg
      · apply div_nonneg (mul_nonneg (by norm_num : (0 : Real) <= 2) (le_of_lt hA1pos))
        linarith
      · exact Real.sqrt_nonneg _
    calc (1 - 2 * (0.1 : Real)) * (2 * A1_val / (A1_val + 1) * Real.sqrt (d0 / (A2_val * N)))
        <= 1 * (2 * A1_val / (A1_val + 1) * Real.sqrt (d0 / (A2_val * N))) := by
           apply mul_le_mul_of_nonneg_right hprefactor_le hinner_nonneg
      _ = 2 * (A1_val / (A1_val + 1)) * Real.sqrt (d0 / (A2_val * N)) := by ring
      _ <= 2 * 1 * Real.sqrt (d0 / (A2_val * N)) := by
           apply mul_le_mul_of_nonneg_right
           apply mul_le_mul_of_nonneg_left (le_of_lt h1) (by norm_num : (0 : Real) <= 2)
           apply Real.sqrt_nonneg
      _ = 2 * Real.sqrt (d0 / (A2_val * N)) := by ring
      _ = 2 * Real.sqrt ((d0 / N) / A2_val) := by
           congr 1; rw [div_div]; ring_nf
      _ = 2 * (Real.sqrt (d0 / N) / Real.sqrt A2_val) := by
           rw [Real.sqrt_div (div_nonneg hd0nn (le_of_lt hNpos))]
      _ = 2 / Real.sqrt A2_val * Real.sqrt (d0 / N) := by ring

/-! ## Three regions of s for gap bounds -/

/-- Left of avoided crossing: I_{s←} = [0, s* - δ_s) -/
def leftRegion {n M : Nat} (es : EigenStructure n M) (hM : M >= 2) (s : Real) : Prop :=
  0 <= s ∧ s < avoidedCrossingPosition es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM) -
             avoidedCrossingWindow es hM

/-- Around avoided crossing: I_{s*} = [s* - δ_s, s* + δ_s] -/
def avoidedCrossingRegion {n M : Nat} (es : EigenStructure n M) (hM : M >= 2) (s : Real) : Prop :=
  let sStar := avoidedCrossingPosition es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM)
  let delta := avoidedCrossingWindow es hM
  |s - sStar| <= delta

/-- Right of avoided crossing: I_{s→} = (s* + δ_s, 1] -/
def rightRegion {n M : Nat} (es : EigenStructure n M) (hM : M >= 2) (s : Real) : Prop :=
  avoidedCrossingPosition es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM) +
    avoidedCrossingWindow es hM < s ∧ s <= 1

/-! ## Spectral condition for bounds

The spectral condition ensures the avoided crossing window is properly contained
within the interval [0, 1]. This is required for the gap bound proofs. -/

/-- Spectral condition for bounds: ensures the avoided crossing window δ_s is small
    relative to s* so that:
    - δ < s* (crossing window is within the valid region)
    - s* + δ < 1 (crossing completes before end of evolution) -/
def spectralConditionForBounds {n M : Nat} (es : EigenStructure n M) (hM : M >= 2) : Prop :=
  let A1_val := A1 es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM)
  let A2_val := A2 es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM)
  let d0 := es.degeneracies ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_two hM⟩
  let N := qubitDim n
  A1_val > 1 ∧ Real.sqrt (d0 * A2_val / N) < (A1_val + 1) / 2

/-- The avoided crossing window is within bounds: δ < s* and s* + δ < 1.

    Note: Requires the spectral condition `spectralConditionForBounds` as a hypothesis.
    This condition is satisfied for typical 3-SAT instances but not all eigenstructures. -/
theorem avoidedCrossing_bound {n M : Nat} (es : EigenStructure n M) (hM : M >= 2)
    (hcond : spectralConditionForBounds es hM) :
    let sStar := avoidedCrossingPosition es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM)
    let deltaS := avoidedCrossingWindow es hM
    deltaS < sStar ∧ sStar + deltaS < 1 := by
  simp only [avoidedCrossingPosition, avoidedCrossingWindow, spectralConditionForBounds] at *
  have hM0 : M > 0 := Nat.lt_of_lt_of_le Nat.zero_lt_two hM
  have hA1gt1 : A1 es hM0 > 1 := hcond.1
  have hA1pos : A1 es hM0 > 0 := by linarith
  have hA1plus1_pos : A1 es hM0 + 1 > 0 := by linarith
  have hsqrt_bound : Real.sqrt (↑(es.degeneracies ⟨0, hM0⟩) * A2 es hM0 / ↑(qubitDim n)) < (A1 es hM0 + 1) / 2 := hcond.2
  -- The proof follows from the spectral condition
  constructor
  · -- deltaS < sStar
    -- deltaS = 2/(A1+1)^2 * sqrt(d0*A2/N)
    -- sStar = A1/(A1+1)
    -- Need: 2/(A1+1)^2 * sqrt(...) < A1/(A1+1)
    -- i.e., 2/(A1+1) * sqrt(...) < A1
    -- i.e., sqrt(...) < A1*(A1+1)/2
    -- This follows from hsqrt_bound: sqrt(...) < (A1+1)/2 < A1*(A1+1)/2 when A1 > 1
    calc 2 / (A1 es hM0 + 1) ^ 2 * Real.sqrt (↑(es.degeneracies ⟨0, hM0⟩) * A2 es hM0 / ↑(qubitDim n))
        < 2 / (A1 es hM0 + 1) ^ 2 * ((A1 es hM0 + 1) / 2) := by
            apply mul_lt_mul_of_pos_left hsqrt_bound
            apply div_pos (by norm_num : (2 : Real) > 0)
            apply pow_pos hA1plus1_pos
      _ = 1 / (A1 es hM0 + 1) := by field_simp
      _ < A1 es hM0 / (A1 es hM0 + 1) := by
            apply div_lt_div_of_pos_right _ hA1plus1_pos
            linarith
  · -- sStar + deltaS < 1
    -- Need: A1/(A1+1) + 2/(A1+1)^2 * sqrt(...) < 1
    -- From hsqrt_bound: sqrt(...) < (A1+1)/2
    -- So: 2/(A1+1)^2 * sqrt(...) < 2/(A1+1)^2 * (A1+1)/2 = 1/(A1+1)
    -- Thus: A1/(A1+1) + deltaS < A1/(A1+1) + 1/(A1+1) = 1
    have hdeltaS_bound : 2 / (A1 es hM0 + 1) ^ 2 * Real.sqrt (↑(es.degeneracies ⟨0, hM0⟩) * A2 es hM0 / ↑(qubitDim n)) < 1 / (A1 es hM0 + 1) := by
      calc 2 / (A1 es hM0 + 1) ^ 2 * Real.sqrt (↑(es.degeneracies ⟨0, hM0⟩) * A2 es hM0 / ↑(qubitDim n))
          < 2 / (A1 es hM0 + 1) ^ 2 * ((A1 es hM0 + 1) / 2) := by
              apply mul_lt_mul_of_pos_left hsqrt_bound
              apply div_pos (by norm_num : (2 : Real) > 0)
              apply pow_pos hA1plus1_pos
        _ = 1 / (A1 es hM0 + 1) := by field_simp
    calc A1 es hM0 / (A1 es hM0 + 1) + 2 / (A1 es hM0 + 1) ^ 2 * Real.sqrt (↑(es.degeneracies ⟨0, hM0⟩) * A2 es hM0 / ↑(qubitDim n))
        < A1 es hM0 / (A1 es hM0 + 1) + 1 / (A1 es hM0 + 1) := by linarith
      _ = (A1 es hM0 + 1) / (A1 es hM0 + 1) := by ring
      _ = 1 := by field_simp

end UAQO
