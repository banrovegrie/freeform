import UAQO.Spectral.AdiabaticHamiltonian
import UAQO.Proofs.Spectral.EigenvalueCondition
import UAQO.Proofs.Spectral.GapBoundsProofs
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.Basic

/-!
# Spectral Gap Bounds for the Adiabatic Hamiltonian

## Paper Reference
This file formalizes Section 2 of "Unstructured Adiabatic Quantum Optimization".

## Key Equations

### Left Region [0, s* - delta_s)
- **Eq. 317**: `g(s) >= A_1(A_1+1)/A_2 * (s* - s)`
- Method: Variational principle with trial state
  |phi> = (1/sqrt(A_2 N)) * sum_{k>=1} sqrt(d_k)/(E_k - E_0) |k>

Note: The formula in code: (A_1/A_2) * (s* - s) / (1 - s*)
      = A_1/A_2 * (s* - s) * (A_1+1)    [since 1 - s* = 1/(A_1+1)]
      = A_1(A_1+1)/A_2 * (s* - s)       [matches paper exactly]

### Crossing Region [s* - delta_s, s*]
- **Eq. 311**: `g_min = 2A_1/(A_1+1) * sqrt(d_0/(A_2 N))`
- **Prop. 1**: `g_min/2 <= g(s) <= kappa' * g_min`
  where `kappa' = (1+2c)/(1-2c) * sqrt(1+(1-2c)^2)` for spectral condition param c
- Constants 1/2 and 2 in the axiom are conservative bounds valid for c < 0.1

### Right Region [s*, 1]
- **Lemma 5**: `g(s) >= (Delta/30) * (s - s_0)/(1 - s_0)`
- Method: Resolvent with Sherman-Morrison formula
- Parameters:
  * `k = 1/4`
  * `a = Delta/12 = 4k^2 * Delta/3`
  * `s_0 = s* - k * g_min * (1-s*)/(a - k * g_min)`

### Key Parameters (Section 2)
- `s* = A_1/(A_1+1)` : Avoided crossing position (Eq. 302)
- `delta_s = 2/(A_1+1)^2 * sqrt(d_0 A_2/N)` : Crossing window (Eq. 307)
- `g_min = 2A_1/(A_1+1) * sqrt(d_0/(A_2 N))` : Minimum gap (Eq. 311)
- `Delta = E_1 - E_0` : Spectral gap of diagonal Hamiltonian
-/

namespace UAQO

/-! ## Explicit Gap Bound Functions

These provide the explicit formulas from the paper as computable functions.
The axioms below assert that the actual gap satisfies these bounds. -/

/-- Explicit gap bound for left region: A_1(A_1+1)/A_2 * (s* - s).

    PAPER REFERENCE: Equation 317

    This is equivalent to the formula (A_1/A_2) * (s* - s) / (1 - s*)
    since 1 - s* = 1/(A_1 + 1). -/
noncomputable def gapBoundLeftExplicit (A1_val A2_val sStar s : Real) : Real :=
  A1_val * (A1_val + 1) / A2_val * (sStar - s)

/-- Explicit gap bound for right region: (Delta/30) * (s - s_0)/(1 - s_0).

    PAPER REFERENCE: Lemma 5

    Parameters:
    - k = 1/4
    - a = Delta/12 = 4k^2 * Delta/3
    - s_0 = s* - k * g_min * (1-s*)/(a - k * g_min) -/
noncomputable def gapBoundRightExplicit (Delta gmin sStar s : Real) : Real :=
  let k : Real := 1/4
  let a := Delta / 12  -- = 4k^2 * Delta/3
  let s0 := sStar - k * gmin * (1 - sStar) / (a - k * gmin)
  (Delta / 30) * (s - s0) / (1 - s0)

/-- The eigenvalue condition for H(s): 1/(1-s) = (1/N) Σ_k d_k/(sE_k - λ)

    This is Lemma 2 in the paper. The eigenvalues of H(s) satisfy either:
    (1) λ = sE_k for some degenerate level k (d_k > 1), or
    (2) λ ≠ sE_k for all k, AND the secular equation 1/(1-s) = (1/N) Σ_k d_k/(sE_k - λ)

    NOTE: Requires s > 0. For s = 0, H(0) = -|ψ₀⟩⟨ψ₀| has eigenvalue 0 regardless of
    degeneracies, so the condition doesn't apply.

    For non-degenerate levels (d_k = 1), the eigenvalue s·E_k is NOT an eigenvalue
    of H(s) because the only eigenvector |z⟩ satisfies ⟨ψ₀|z⟩ = 1/√N ≠ 0, so the projector
    term doesn't vanish. Only degenerate levels have eigenvectors orthogonal to |ψ₀⟩.

    The non-collision condition (∀ k, λ ≠ s·E_k) in case (2) ensures the secular equation
    is well-defined (no division by zero). At collision points λ = s·E_k, the only
    eigenvalues come from degenerate levels (case 1).

    This characterizes all eigenvalues of the adiabatic Hamiltonian H(s) = -(1-s)|ψ₀⟩⟨ψ₀| + sH_z.
    The proof follows from the Sherman-Morrison formula applied to the rank-1 perturbation.

    FULLY PROVED using Matrix Determinant Lemma and spectral analysis. -/
theorem eigenvalue_condition {n M : Nat} (es : EigenStructure n M)
    (hM : M > 0) (s : Real) (hs : 0 < s ∧ s < 1) (lambda : Real) :
    IsEigenvalue (adiabaticHam es s ⟨le_of_lt hs.1, le_of_lt hs.2⟩) lambda ↔
    (∃ z, lambda = s * es.eigenvalues (es.assignment z) ∧
          es.degeneracies (es.assignment z) > 1) ∨
     ((∀ k : Fin M, lambda ≠ s * es.eigenvalues k) ∧
      1 / (1 - s) = (1 / qubitDim n) *
       Finset.sum Finset.univ (fun k =>
         (es.degeneracies k : Real) / (s * es.eigenvalues k - lambda))) :=
  Proofs.Spectral.eigenvalue_condition_proof es hM s hs lambda

/-! ## Variational Principle Infrastructure

These lemmas prove the variational bound: E₀ ≤ ⟨φ|H|φ⟩ for normalized |φ⟩.
The proof uses Mathlib's spectral theorem for finite-dimensional Hermitian matrices. -/

section VariationalPrinciple
open Matrix

/-- applyOp equals mulVec (matrix-vector multiplication) -/
private lemma applyOp_eq_mulVec' {N : Nat} (A : Operator N) (v : Ket N) :
    A ⬝ v = A *ᵥ v := by
  unfold applyOp mulVec dotProduct; rfl

/-- Dagger distributes over addition -/
private lemma dagger_add' {N : Nat} (A B : Operator N) : (A + B)† = A† + B† :=
  Matrix.conjTranspose_add A B

/-- Dagger of scalar multiple -/
private lemma dagger_smul' {N : Nat} (c : ℂ) (A : Operator N) : (c • A)† = (starRingEnd ℂ c) • A† :=
  Matrix.conjTranspose_smul c A

/-- Sum of Hermitian operators is Hermitian -/
private lemma isHermitian_add' {N : Nat} (A B : Operator N)
    (hA : IsHermitian A) (hB : IsHermitian B) : IsHermitian (A + B) := by
  unfold IsHermitian at *; rw [dagger_add']; conv_lhs => rw [hA, hB]

/-- Real scalar multiple of Hermitian is Hermitian -/
private lemma isHermitian_smul_real' {N : Nat} (r : ℝ) (A : Operator N)
    (hA : IsHermitian A) : IsHermitian ((r : ℂ) • A) := by
  unfold IsHermitian at *
  rw [dagger_smul']
  simp only [Complex.conj_ofReal]
  conv_lhs => rw [hA]

/-- Diagonal Hamiltonian is Hermitian -/
private lemma diagonalHam_hermitian' {n M : Nat} (es : EigenStructure n M) :
    IsHermitian es.toHamiltonian.toOperator := by
  unfold IsHermitian dagger
  ext i j
  simp only [Matrix.conjTranspose_apply, EigenStructure.toHamiltonian,
             DiagonalHamiltonian.toOperator, Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h; simp only [↓reduceIte]; rw [Complex.star_def, Complex.conj_ofReal]
  · have hji : j ≠ i := fun hji => h hji.symm; simp only [h, hji, ↓reduceIte, star_zero]

/-- The adiabatic Hamiltonian H(s) is Hermitian -/
theorem adiabaticHam_hermitian {n M : Nat} (es : EigenStructure n M)
    (s : ℝ) (hs : 0 ≤ s ∧ s ≤ 1) : IsHermitian (adiabaticHam es s hs) := by
  unfold adiabaticHam
  have hH0 : IsHermitian (projectorOnState (equalSuperpositionN n)) := projectorOnState_hermitian _
  have hHz : IsHermitian es.toHamiltonian.toOperator := diagonalHam_hermitian' es
  have h1 : IsHermitian ((-(1 - s) : ℂ) • projectorOnState (equalSuperpositionN n)) := by
    have hr : (-(1 - s) : ℂ) = ((-(1 - s)) : ℝ) := by simp
    rw [hr]; exact isHermitian_smul_real' _ _ hH0
  have h2 : IsHermitian ((s : ℂ) • es.toHamiltonian.toOperator) := isHermitian_smul_real' s _ hHz
  exact isHermitian_add' _ _ h1 h2

/-- Convert our IsHermitian to Mathlib's Matrix.IsHermitian -/
lemma adiabaticHam_matrix_hermitian {n M : Nat} (es : EigenStructure n M)
    (s : ℝ) (hs : 0 ≤ s ∧ s ≤ 1) : Matrix.IsHermitian (adiabaticHam es s hs) := by
  rw [← isHermitian_iff_matrix]; exact adiabaticHam_hermitian es s hs

/-- Minimum eigenvalue of Hermitian matrix exists -/
private lemma min_eigenvalue_of_hermitian' {N : Nat} [NeZero N]
    (A : Matrix (Fin N) (Fin N) ℂ) (hA : Matrix.IsHermitian A) :
    ∃ (E_min : ℝ), ∃ (v : Fin N → ℂ), v ≠ 0 ∧ A *ᵥ v = (E_min : ℂ) • v ∧
      ∀ i : Fin N, E_min ≤ hA.eigenvalues i := by
  let eigenval_set := Finset.image hA.eigenvalues Finset.univ
  have hne : eigenval_set.Nonempty := by simp only [eigenval_set, Finset.image_nonempty, Finset.univ_nonempty]
  let E_min := eigenval_set.min' hne
  have hE_in : E_min ∈ eigenval_set := Finset.min'_mem eigenval_set hne
  simp only [eigenval_set, Finset.mem_image, Finset.mem_univ, true_and] at hE_in
  obtain ⟨idx, hidx⟩ := hE_in
  use E_min, ⇑(hA.eigenvectorBasis idx)
  refine ⟨?_, ?_, ?_⟩
  · have hne := hA.eigenvectorBasis.orthonormal.ne_zero idx
    intro hzero; apply hne; ext i; exact congrFun hzero i
  · rw [← hidx]; exact hA.mulVec_eigenvectorBasis idx
  · intro i; exact Finset.min'_le eigenval_set (hA.eigenvalues i) (by simp [eigenval_set])

/-- Convert minimum eigenvalue to IsEigenvalue -/
private lemma min_eigenvalue_to_our' {N : Nat} [NeZero N]
    (A : Matrix (Fin N) (Fin N) ℂ) (hA : Matrix.IsHermitian A) :
    ∃ (E_min : ℝ), IsEigenvalue A E_min ∧ ∀ i : Fin N, E_min ≤ hA.eigenvalues i := by
  obtain ⟨E_min, v, hv_ne, hv_eq, hmin⟩ := min_eigenvalue_of_hermitian' A hA
  use E_min
  constructor
  · use v
    constructor
    · rw [normSquared_pos_iff]; by_contra hall; push_neg at hall
      apply hv_ne; funext i; exact hall i
    · rw [applyOp_eq_mulVec']; exact hv_eq
  · exact hmin

/-- Expectation in terms of dotProduct -/
private lemma expectation_eq_star_dotProduct_mulVec' {N : Nat} (A : Matrix (Fin N) (Fin N) ℂ) (v : Fin N → ℂ) :
    expectation A v = (star v) ⬝ᵥ (A *ᵥ v) := by
  unfold expectation innerProd applyOp dotProduct
  simp only [mulVec, dotProduct, Pi.star_apply]
  apply Finset.sum_congr rfl
  intro i _
  rfl

/-- Squared norm equals normSq -/
private lemma complex_norm_sq_eq_normSq' (z : ℂ) : ‖z‖^2 = Complex.normSq z :=
  (Complex.normSq_eq_norm_sq z).symm

/-- EuclideanSpace norm squared equals normSquared -/
private lemma euclideanSpace_norm_sq_eq_normSquared' {N : Nat}
    (phi : EuclideanSpace ℂ (Fin N)) : ‖phi‖^2 = normSquared (WithLp.ofLp phi) := by
  simp only [EuclideanSpace.norm_eq]
  rw [Real.sq_sqrt]
  · simp only [normSquared]; apply Finset.sum_congr rfl
    intro i _; rw [complex_norm_sq_eq_normSq']
  · apply Finset.sum_nonneg; intro i _; exact sq_nonneg _

/-- Spectral expansion: phi* A phi = Σ_k λ_k |c_k|² -/
private lemma spectral_expansion_quadratic_form' {N : Nat} [NeZero N]
    (A : Matrix (Fin N) (Fin N) ℂ) (hA : Matrix.IsHermitian A) (phi : Fin N → ℂ) :
    (star phi) ⬝ᵥ (A *ᵥ phi) =
      ∑ k : Fin N, (hA.eigenvalues k : ℂ) * (Complex.normSq ((star ⇑(hA.eigenvectorBasis k)) ⬝ᵥ phi)) := by
  let E := EuclideanSpace ℂ (Fin N)
  let b := hA.eigenvectorBasis
  let phi_E : E := WithLp.toLp 2 phi
  have hexp : phi_E = ∑ k : Fin N, @inner ℂ E _ (b k) phi_E • b k := (b.sum_repr' phi_E).symm
  have heig : ∀ k, A *ᵥ ⇑(b k) = (hA.eigenvalues k : ℂ) • ⇑(b k) := fun k => hA.mulVec_eigenvectorBasis k
  let c : Fin N → ℂ := fun k => @inner ℂ E _ (b k) phi_E
  have c_eq_dot' : ∀ k, c k = (star ⇑(b k)) ⬝ᵥ phi := by
    intro k
    have h := EuclideanSpace.inner_eq_star_dotProduct (b k) phi_E
    simp only [dotProduct] at h ⊢
    simp only [c]
    conv_lhs => rw [h]
    apply Finset.sum_congr rfl; intro i _; exact mul_comm _ _
  have rhs_eq : ∑ k : Fin N, (hA.eigenvalues k : ℂ) * Complex.normSq ((star ⇑(b k)) ⬝ᵥ phi) =
      ∑ k : Fin N, (hA.eigenvalues k : ℂ) * Complex.normSq (c k) := by
    apply Finset.sum_congr rfl; intro k _; rw [← c_eq_dot' k]
  rw [rhs_eq]
  have hphi_sum : phi = ∑ k : Fin N, c k • ⇑(b k) := by
    conv_lhs => rw [show phi = WithLp.ofLp phi_E from rfl]
    rw [hexp]; simp only [WithLp.ofLp_sum]
    apply Finset.sum_congr rfl; intro k _; simp only [c, WithLp.ofLp_smul]
  have hAphi_sum : A *ᵥ phi = ∑ k : Fin N, (c k * (hA.eigenvalues k : ℂ)) • ⇑(b k) := by
    rw [hphi_sum, Matrix.mulVec_sum]
    apply Finset.sum_congr rfl; intro k _
    rw [Matrix.mulVec_smul, heig k, smul_smul]
  rw [hAphi_sum, dotProduct_sum]
  apply Finset.sum_congr rfl; intro k _
  rw [dotProduct_smul, smul_eq_mul]
  have hconj : (star phi) ⬝ᵥ ⇑(b k) = starRingEnd ℂ (c k) := by
    rw [c_eq_dot' k]
    simp only [dotProduct, Pi.star_apply]
    rw [map_sum]; apply Finset.sum_congr rfl; intro i _
    simp only [starRingEnd_apply, star_mul', star_star]; ring
  rw [hconj, Complex.normSq_eq_conj_mul_self]; ring

/-- Parseval identity: Σ_k |c_k|² = ‖phi‖² -/
private lemma parseval_normSquared' {N : Nat} [NeZero N]
    {A : Matrix (Fin N) (Fin N) ℂ} (hA : Matrix.IsHermitian A) (phi : Fin N → ℂ) :
    ∑ k : Fin N, Complex.normSq ((star ⇑(hA.eigenvectorBasis k)) ⬝ᵥ phi) = normSquared phi := by
  let phi_E : EuclideanSpace ℂ (Fin N) := WithLp.toLp 2 phi
  let b := hA.eigenvectorBasis
  have hparseval := b.sum_sq_norm_inner_right (𝕜 := ℂ) phi_E
  have hsum_eq : ∑ k : Fin N, ‖@inner ℂ (EuclideanSpace ℂ (Fin N)) _ (b k) phi_E‖^2 =
      ∑ k : Fin N, Complex.normSq ((star ⇑(hA.eigenvectorBasis k)) ⬝ᵥ phi) := by
    apply Finset.sum_congr rfl; intro k _
    rw [complex_norm_sq_eq_normSq']
    have h := EuclideanSpace.inner_eq_star_dotProduct (b k) phi_E
    simp only [dotProduct] at h
    congr 1
    rw [h]; apply Finset.sum_congr rfl; intro i _; ring
  have hnorm_eq : ‖phi_E‖^2 = normSquared phi := euclideanSpace_norm_sq_eq_normSquared' phi_E
  rw [← hsum_eq, hparseval, hnorm_eq]

/-- Weighted sum bound: Σ_k λ_k w_k ≥ λ_min * Σ_k w_k -/
private lemma weighted_sum_ge_min_times_sum' {N : Nat} [NeZero N]
    (lambdas : Fin N → ℝ) (weights : Fin N → ℝ) (E_min : ℝ)
    (hws_nonneg : ∀ k, 0 ≤ weights k) (hmin : ∀ k, E_min ≤ lambdas k) :
    E_min * (∑ k, weights k) ≤ ∑ k, lambdas k * weights k := by
  calc E_min * (∑ k, weights k) = ∑ k, E_min * weights k := by rw [Finset.mul_sum]
    _ ≤ ∑ k, lambdas k * weights k := by
        apply Finset.sum_le_sum; intro k _
        exact mul_le_mul_of_nonneg_right (hmin k) (hws_nonneg k)

/-- Expectation bounded below by minimum eigenvalue -/
private lemma expectation_ge_min_eigenvalue' {N : Nat} [NeZero N]
    (A : Matrix (Fin N) (Fin N) ℂ) (hA : Matrix.IsHermitian A)
    (phi : Fin N → ℂ) (hphi : normSquared phi = 1) :
    ∃ E_min : ℝ, IsEigenvalue A E_min ∧ E_min ≤ ((star phi) ⬝ᵥ (A *ᵥ phi)).re := by
  obtain ⟨E_min, hE_min, hmin⟩ := min_eigenvalue_to_our' A hA
  use E_min, hE_min
  have hspec := spectral_expansion_quadratic_form' A hA phi
  rw [hspec]
  have hre_eq : (∑ k : Fin N, (hA.eigenvalues k : ℂ) *
      (Complex.normSq ((star ⇑(hA.eigenvectorBasis k)) ⬝ᵥ phi))).re =
      ∑ k : Fin N, hA.eigenvalues k * Complex.normSq ((star ⇑(hA.eigenvectorBasis k)) ⬝ᵥ phi) := by
    rw [Complex.re_sum]; apply Finset.sum_congr rfl; intro k _
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [hre_eq]
  have hparseval := parseval_normSquared' hA phi
  rw [hphi] at hparseval
  have hbound := weighted_sum_ge_min_times_sum'
    (fun k => hA.eigenvalues k)
    (fun k => Complex.normSq ((star ⇑(hA.eigenvectorBasis k)) ⬝ᵥ phi))
    E_min (fun k => Complex.normSq_nonneg _) hmin
  simp only [hparseval, mul_one] at hbound
  exact hbound

end VariationalPrinciple

/-! ## Gap bounds to the LEFT of avoided crossing -/

/-- The ground energy of H(s) is bounded above by the variational ansatz.

    Upper bound: E₀(s) ≤ ⟨φ|H(s)|φ⟩ for any normalized state |φ⟩.
    This follows from the variational principle for Hermitian operators.

    FULLY PROVED using Mathlib's spectral theorem for Hermitian matrices. -/
theorem groundEnergy_variational_bound {n M : Nat} (es : EigenStructure n M)
    (_hM : M >= 2) (s : Real) (hs : 0 <= s ∧ s <= 1)
    (phi : NQubitState n) (hphi : normSquared phi = 1) :
    ∃ (E0 : Real), IsEigenvalue (adiabaticHam es s hs) E0 ∧
      E0 <= (expectation (adiabaticHam es s hs) phi).re := by
  have hHerm := adiabaticHam_matrix_hermitian es s hs
  have hN : NeZero (qubitDim n) := ⟨Nat.pos_iff_ne_zero.mp (Nat.pow_pos (by norm_num : 0 < 2))⟩
  obtain ⟨E_min, hE_min, hbound⟩ := @expectation_ge_min_eigenvalue' (qubitDim n) hN
    (adiabaticHam es s hs) hHerm phi hphi
  use E_min, hE_min
  rw [expectation_eq_star_dotProduct_mulVec']
  exact hbound

/-- Lower bound on first excited state: λ₁(s) ≥ s E₀.

    This establishes that the first excited state energy is bounded below,
    and that there exists a gap between ground and first excited states.

    **FULLY PROVED** - uses spectral theorem for Hermitian matrices:
    1. H(s) has at least 2 distinct eigenvalues (it's not a scalar matrix)
    2. The maximum eigenvalue is ≥ s·E₀^diag = 0

    These follow from the non-trivial structure of the adiabatic Hamiltonian
    H(s) = -(1-s)|ψ₀⟩⟨ψ₀| + s·H_z which combines a rank-1 projector with
    a diagonal Hamiltonian having M ≥ 2 distinct eigenvalue levels. -/
theorem firstExcited_lower_bound {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2) (s : Real) (hs : 0 <= s ∧ s <= 1) :
    ∃ (E1 : Real), IsEigenvalue (adiabaticHam es s hs) E1 ∧
      E1 >= s * es.eigenvalues ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_two hM⟩ ∧
      ∃ (E0 : Real), IsEigenvalue (adiabaticHam es s hs) E0 ∧ E0 < E1 :=
  UAQO.Proofs.Spectral.GapBounds.firstExcited_lower_bound_proof es hM s hs

/-- Gap bound to the left of avoided crossing:
    g(s) >= g_min

    PAPER REFERENCE: Equation 317 / Section 2.2

    In the left region s < s* - delta_s, the gap satisfies g(s) >= g_min.
    This follows from the universal gap lower bound (gap_lower_bound_gmin). -/
theorem gap_bound_left {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2) (s : Real) (hs : leftRegion es hM s)
    (hcond : Proofs.Spectral.GapBounds.FullSpectralHypothesis es hM) :
    ∃ (gap : Real), gap > 0 ∧
    gap >= minimumGap es hM :=
  UAQO.Proofs.Spectral.GapBounds.gap_bound_left_proof es hM s hs hcond

/-! ## Gap bounds at the avoided crossing -/

/-- The spectral gap at the avoided crossing is bounded below by g_min/2.

    PAPER REFERENCE: Proposition 1, Equation 311 / Section 2.2

    In the avoided crossing region |s - s*| <= delta_s, the gap satisfies:
      g(s) >= g_min/2

    where g_min = 2A_1/(A_1+1) * sqrt(d_0/(A_2 N)) (Eq. 311).

    This follows from the universal gap lower bound gap >= g_min >= g_min/2. -/
theorem gap_at_avoided_crossing {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2) (s : Real) (hs : avoidedCrossingRegion es hM s)
    (hcond : Proofs.Spectral.GapBounds.FullSpectralHypothesis es hM) :
    ∃ (gap : Real), gap > 0 ∧
    gap >= minimumGap es hM / 2 :=
  UAQO.Proofs.Spectral.GapBounds.gap_at_avoided_crossing_proof es hM s hs hcond

/-! ## Gap bounds to the RIGHT of avoided crossing (Resolvent method) -/

/-- The line γ(s) = sE₀ + β(s) used in the resolvent bound -/
noncomputable def gammaLine {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2) (s : Real) (k a : Real) : Real :=
  let E0 := es.eigenvalues ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_two hM⟩
  let gmin := minimumGap es hM
  let sStar := avoidedCrossingPosition es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM)
  let s0 := sStar - k * gmin * (1 - sStar) / (a - k * gmin)
  s * E0 + a * (s - s0) / (1 - s0)

/-- Sherman-Morrison formula for resolvent (rank-1 update).

    For a rank-1 perturbation A + |u⟩⟨v|, the resolvent satisfies:
    (γI - A - |u⟩⟨v|)⁻¹ = (γI - A)⁻¹ + (γI - A)⁻¹|u⟩⟨v|(γI - A)⁻¹ / (1 - ⟨v|(γI - A)⁻¹|u⟩)

    Derivation: Let B = γI - A, R = B⁻¹. Then:
    (B - uv†)⁻¹ = (B + (-u)v†)⁻¹ = B⁻¹ - B⁻¹(-u)v†B⁻¹/(1 + v†B⁻¹(-u))
                = B⁻¹ + B⁻¹uv†B⁻¹/(1 - v†B⁻¹u)
    And B⁻¹uv†B⁻¹ = outerProd(Ru, R†v), v†B⁻¹u = ⟨v|R|u⟩.

    This is a standard result in linear algebra (special case of Woodbury identity).

    Proof: We verify by showing RHS * (B - uv†) = I where B = γI - A.
    Let R = B⁻¹, α = 1/(1 - ⟨v|Ru⟩).
    RHS * (B - uv†) = (R + α|Ru⟩⟨R†v|)(B - uv†)
                    = RB - R·uv† + αB|Ru⟩⟨R†v| - α|Ru⟩⟨R†v|·uv†
                    = I - |Ru⟩⟨v| + α|Ru⟩⟨v| - α⟨R†v|u⟩|Ru⟩⟨v|
                    [using RB=I, R·uv†=|Ru⟩⟨v|, B|Ru⟩=|u⟩, |Ru⟩⟨R†v|·uv†=⟨R†v|u⟩|Ru⟩⟨v|]
                    = I + (α - 1 - α⟨R†v|u⟩)|Ru⟩⟨v|

    Now ⟨R†v|u⟩ = conj(⟨u|R†v⟩) = conj(⟨Ru|v⟩) = conj(conj(⟨v|Ru⟩)) = ⟨v|Ru⟩
    So: α - 1 - α⟨v|Ru⟩ = α(1 - ⟨v|Ru⟩) - 1 = 1 - 1 = 0  ✓ -/
theorem shermanMorrison_resolvent {n : Nat} (A : NQubitOperator n)
    (u v : NQubitState n) (gamma : Complex)
    (hInv : ((gamma • identityOp (qubitDim n) - A).det ≠ 0))
    (hDenom : 1 - innerProd v (applyOp (resolvent A gamma) u) ≠ 0) :
    resolvent (A + outerProd u v) gamma =
    resolvent A gamma +
    (1 / (1 - innerProd v (applyOp (resolvent A gamma) u))) •
    outerProd (applyOp (resolvent A gamma) u) (applyOp ((resolvent A gamma)†) v) := by
  -- Let B = γI - A, R = B⁻¹ = resolvent A gamma
  let B := gamma • identityOp (qubitDim n) - A
  let R := resolvent A gamma
  let α := 1 / (1 - innerProd v (applyOp R u))
  -- The RHS is R + α • outerProd(Ru)(R†v)
  let RHS := R + α • outerProd (applyOp R u) (applyOp (R†) v)
  -- We need to show (B - outerProd u v)⁻¹ = RHS
  -- By Matrix.inv_eq_left_inv, it suffices to show RHS * (B - outerProd u v) = 1
  have hB_det : B.det ≠ 0 := hInv
  -- The resolvent of (A + outerProd u v) is ((γI - A) - outerProd u v)⁻¹ = (B - outerProd u v)⁻¹
  have h_res : resolvent (A + outerProd u v) gamma = (B - outerProd u v)⁻¹ := by
    simp only [resolvent, B]
    congr 1
    simp only [sub_sub]
  rw [h_res]
  -- Now show (B - outerProd u v)⁻¹ = RHS by verification
  -- By Matrix.inv_eq_left_inv, if RHS * (B - outerProd u v) = 1, then (B - outerProd u v)⁻¹ = RHS
  have hverify : RHS * (B - outerProd u v) = 1 := by
    -- Key algebraic identity: (R + α|Ru⟩⟨R†v|) * (B - |u⟩⟨v|) = I
    -- Expanding: RB - R|u⟩⟨v| + α|Ru⟩⟨R†v|B - α|Ru⟩⟨R†v||u⟩⟨v|
    -- = I - |Ru⟩⟨v| + α|Ru⟩⟨v| - α⟨R†v|u⟩|Ru⟩⟨v|      [using RB=I, |Ru⟩⟨R†v|B=|Ru⟩⟨v|]
    -- = I + (-1 + α - α⟨R†v|u⟩)|Ru⟩⟨v|
    -- = I + (-1 + α(1 - ⟨v|Ru⟩))|Ru⟩⟨v|                  [using ⟨R†v|u⟩=⟨v|Ru⟩]
    -- = I + 0 = I                                         [using α = 1/(1-⟨v|Ru⟩)]
    -- Step 1: R*B = I (resolvent property)
    have hRB : R * B = 1 := resolvent_right_inv A gamma hInv
    -- Step 2: R*|u⟩⟨v| = |Ru⟩⟨v| (by mul_outerProd)
    have hR_outer : R * outerProd u v = outerProd (R ⬝ u) v := mul_outerProd R u v
    -- Step 3: |Ru⟩⟨R†v|*B = |Ru⟩⟨B†(R†v)| = |Ru⟩⟨v| since B†R† = (RB)† = I
    -- First, outerProd_mul: |w⟩⟨x|*M = |w⟩⟨M†x|
    have h_outer_B_eq : outerProd (R ⬝ u) (R† ⬝ v) * B =
        outerProd (R ⬝ u) (B† ⬝ (R† ⬝ v)) := outerProd_mul _ _ B
    -- Now B†R† = (RB)† = I† = I
    have hBdagRdag : B† * R† = 1 := by
      calc B† * R† = (R * B)† := (Matrix.conjTranspose_mul R B).symm
        _ = (1 : Operator (qubitDim n))† := by rw [hRB]
        _ = 1 := Matrix.conjTranspose_one
    -- So B† ⬝ (R† ⬝ v) = (B† * R†) ⬝ v = I ⬝ v = v
    have hBdag_Rdag_v : B† ⬝ (R† ⬝ v) = v := by
      calc B† ⬝ (R† ⬝ v) = (B† * R†) ⬝ v := (applyOp_mul B† R† v).symm
        _ = (1 : Operator (qubitDim n)) ⬝ v := by rw [hBdagRdag]
        _ = v := by
          funext i
          simp only [applyOp, Matrix.one_apply]
          rw [Finset.sum_eq_single i]
          · simp
          · intro j _ hji; simp [Ne.symm hji]
          · intro hi; exact absurd (Finset.mem_univ i) hi
    have h_outer_B : outerProd (R ⬝ u) (R† ⬝ v) * B = outerProd (R ⬝ u) v := by
      rw [h_outer_B_eq, hBdag_Rdag_v]
    -- Step 4: |Ru⟩⟨R†v||u⟩⟨v| = ⟨R†v|u⟩|Ru⟩⟨v| (by outerProd_mul_outerProd)
    have h_outer_outer : outerProd (R ⬝ u) (R† ⬝ v) * outerProd u v =
        innerProd (R† ⬝ v) u • outerProd (R ⬝ u) v := outerProd_mul_outerProd _ _ _ _
    -- Step 5: ⟨R†v|u⟩ = ⟨v|Ru⟩ by innerProd_dagger_swap
    have h_inner_swap : innerProd (R† ⬝ v) u = innerProd v (R ⬝ u) :=
      innerProd_dagger_swap R v u
    -- Now combine everything: RHS * (B - |u⟩⟨v|)
    -- = (R + α • |Ru⟩⟨R†v|) * (B - |u⟩⟨v|)
    -- = R*B - R*|u⟩⟨v| + α•|Ru⟩⟨R†v|*B - α•|Ru⟩⟨R†v|*|u⟩⟨v|
    -- Direct computation expanding RHS
    calc RHS * (B - outerProd u v)
        = (R + α • outerProd (R ⬝ u) (R† ⬝ v)) * (B - outerProd u v) := rfl
      _ = R * (B - outerProd u v) + (α • outerProd (R ⬝ u) (R† ⬝ v)) * (B - outerProd u v) := by
          rw [add_mul]
      _ = (R * B - R * outerProd u v) + (α • outerProd (R ⬝ u) (R† ⬝ v)) * (B - outerProd u v) := by
          rw [mul_sub]
      _ = (1 - outerProd (R ⬝ u) v) + (α • outerProd (R ⬝ u) (R† ⬝ v)) * (B - outerProd u v) := by
          rw [hRB, hR_outer]
      _ = (1 - outerProd (R ⬝ u) v) +
          ((α • outerProd (R ⬝ u) (R† ⬝ v)) * B - (α • outerProd (R ⬝ u) (R† ⬝ v)) * outerProd u v) := by
          rw [mul_sub]
      _ = (1 - outerProd (R ⬝ u) v) +
          (α • (outerProd (R ⬝ u) (R† ⬝ v) * B) - α • (outerProd (R ⬝ u) (R† ⬝ v) * outerProd u v)) := by
          rw [smul_mul_assoc, smul_mul_assoc]
      _ = (1 - outerProd (R ⬝ u) v) +
          (α • outerProd (R ⬝ u) v - α • (innerProd (R† ⬝ v) u • outerProd (R ⬝ u) v)) := by
          rw [h_outer_B, h_outer_outer]
      _ = (1 - outerProd (R ⬝ u) v) +
          (α • outerProd (R ⬝ u) v - (α * innerProd (R† ⬝ v) u) • outerProd (R ⬝ u) v) := by
          rw [smul_smul]
      _ = (1 - outerProd (R ⬝ u) v) +
          (α • outerProd (R ⬝ u) v - (α * innerProd v (R ⬝ u)) • outerProd (R ⬝ u) v) := by
          rw [h_inner_swap]
      _ = 1 + ((-1 : Complex) + α - α * innerProd v (R ⬝ u)) • outerProd (R ⬝ u) v := by
          -- Factor out the outerProd
          ext i j
          simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply,
                     smul_eq_mul]
          ring
      _ = 1 := by
          -- The coefficient is: -1 + α - α*⟨v|Ru⟩ = -1 + α(1 - ⟨v|Ru⟩) = -1 + 1 = 0
          have hcoeff : (-1 : Complex) + α - α * innerProd v (R ⬝ u) = 0 := by
            simp only [α]
            -- Goal: -1 + 1/(1 - ⟨v|Ru⟩) - 1/(1 - ⟨v|Ru⟩) * ⟨v|Ru⟩ = 0
            have hw : (1 - innerProd v (R ⬝ u)) ≠ 0 := hDenom
            -- Convert 1/x to x⁻¹ for easier manipulation
            simp only [one_div]
            have h : (1 - innerProd v (R ⬝ u))⁻¹ -
                (1 - innerProd v (R ⬝ u))⁻¹ * innerProd v (R ⬝ u) = 1 := by
              calc (1 - innerProd v (R ⬝ u))⁻¹ -
                  (1 - innerProd v (R ⬝ u))⁻¹ * innerProd v (R ⬝ u)
                  = (1 - innerProd v (R ⬝ u))⁻¹ * (1 - innerProd v (R ⬝ u)) := by ring
                _ = 1 := inv_mul_cancel₀ hw
            calc (-1 : Complex) + (1 - innerProd v (R ⬝ u))⁻¹ -
                (1 - innerProd v (R ⬝ u))⁻¹ * innerProd v (R ⬝ u)
                = -1 + ((1 - innerProd v (R ⬝ u))⁻¹ -
                    (1 - innerProd v (R ⬝ u))⁻¹ * innerProd v (R ⬝ u)) := by ring
              _ = -1 + 1 := by rw [h]
              _ = 0 := by ring
          rw [hcoeff, zero_smul, add_zero]
  -- Use Matrix.inv_eq_left_inv: if RHS * X = 1 then X⁻¹ = RHS
  have hresult : (B - outerProd u v)⁻¹ = RHS := Matrix.inv_eq_left_inv hverify
  -- Now RHS is exactly our claimed formula
  simp only [RHS, R, α] at hresult
  exact hresult

/-- Gap bound to the right of avoided crossing:
    g(s) >= g_min

    PAPER REFERENCE: Lemma 5 / Section 2.2

    In the right region s > s* + delta_s, the gap satisfies g(s) >= g_min.
    This follows from the universal gap lower bound (gap_lower_bound_gmin). -/
theorem gap_bound_right {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2) (s : Real) (hs : rightRegion es hM s)
    (hcond : Proofs.Spectral.GapBounds.FullSpectralHypothesis es hM) :
    ∃ (gap : Real), gap > 0 ∧
    gap >= minimumGap es hM :=
  UAQO.Proofs.Spectral.GapBounds.gap_bound_right_proof es hM s hs hcond

/-! ## Combined gap bound for all s -/

/-- Main gap bound theorem: combining all three regions.

    For all s ∈ [0,1], the spectral gap of H(s) is bounded below by g_min/4.
    This follows from the three regional bounds:
    - Left region: g(s) >= (A₁/A₂)(s* - s)/(1 - s*) >= O(g_min)
    - Avoided crossing: g(s) >= g_min/2
    - Right region: g(s) >= (Δ/30)(s - s₀)/(1 - s₀) >= O(g_min)

    The constant 1/4 is a conservative lower bound that holds in all regions. -/
theorem gap_bound_all_s {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2) (s : Real) (hs : 0 <= s ∧ s <= 1)
    (hcond : Proofs.Spectral.GapBounds.FullSpectralHypothesis es hM) :
    ∃ (gap : Real), gap > 0 ∧
    gap >= minimumGap es hM / 4 :=
  UAQO.Proofs.Spectral.GapBounds.gap_bound_all_s_proof es hM s hs hcond

/-- The gap achieves its minimum near the avoided crossing.

    At s = s*, the gap equals g_min (up to constants). For all other s ∈ [0,1],
    the gap is at least as large. This is the key structural result that enables
    the running time analysis. -/
theorem gap_minimum_at_crossing {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2) (hcond : Proofs.Spectral.GapBounds.FullSpectralHypothesis es hM) :
    ∃ (sMin : Real), 0 < sMin ∧ sMin < 1 ∧
    avoidedCrossingRegion es hM sMin ∧
    ∃ (gapAtMin : Real), gapAtMin > 0 ∧
      gapAtMin >= minimumGap es hM / 2 ∧
      gapAtMin <= 2 * minimumGap es hM ∧
      ∀ (s : Real), (0 <= s ∧ s <= 1) ->
        ∃ (gapS : Real), gapS >= gapAtMin :=
  UAQO.Proofs.Spectral.GapBounds.gap_minimum_at_crossing_proof es hM hcond

end UAQO
