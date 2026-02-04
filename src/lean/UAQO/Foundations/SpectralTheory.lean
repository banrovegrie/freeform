/-
  Spectral theory for Hermitian operators.

  We define eigenvalues, eigenvectors, spectral decomposition, and the spectral gap.
-/
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Data.Real.Basic
import UAQO.Foundations.Operators

namespace UAQO

/-! ## Eigenvalues and eigenvectors -/

/-- An eigenvalue-eigenvector pair for operator A -/
structure EigenPair (N : Nat) where
  eigenvalue : Real  -- Hermitian operators have real eigenvalues
  eigenvector : Ket N
  normalized : normSquared eigenvector = 1

/-- A is an eigenvalue of A if Av = λv for some nonzero v -/
def IsEigenvalue {N : Nat} (A : Operator N) (lambda : Real) : Prop :=
  ∃ (v : Ket N), normSquared v > 0 ∧ applyOp A v = (lambda : Complex) • v

/-- The spectrum of an operator is the set of its eigenvalues -/
def Spectrum {N : Nat} (A : Operator N) : Set Real :=
  { lambda | IsEigenvalue A lambda }

/-! ## Spectral decomposition of Hermitian operators -/

/-- A spectral decomposition of a Hermitian operator with M distinct eigenvalues -/
structure SpectralDecomp (N M : Nat) (A : Operator N) where
  eigenvalues : Fin M -> Real
  degeneracies : Fin M -> Nat
  /-- The eigenprojectors for each eigenspace -/
  projectors : Fin M -> Operator N
  /-- Eigenvalues are ordered -/
  ordered : ∀ i j, i < j -> eigenvalues i < eigenvalues j
  /-- Degeneracies are positive (each eigenspace is nonempty) -/
  deg_positive : ∀ k, degeneracies k > 0
  /-- Degeneracies sum to N -/
  deg_sum : Finset.sum Finset.univ degeneracies = N
  /-- Each projector is a genuine projector (Hermitian + idempotent) -/
  projector_isProjector : ∀ k, IsProjector (projectors k)
  /-- Each projector projects onto its eigenspace -/
  projector_rank : ∀ k, trace (projectors k) = degeneracies k
  /-- Projectors are orthogonal -/
  projector_orthogonal : ∀ i j, i ≠ j -> projectors i * projectors j = 0
  /-- Projectors sum to identity -/
  projector_complete : Finset.sum Finset.univ projectors = identityOp N
  /-- Spectral decomposition holds -/
  spectral_decomp : A = Finset.sum Finset.univ
    (fun k => (eigenvalues k : Complex) • projectors k)
  /-- Ground state existence: there exists a normalized eigenvector for each eigenvalue -/
  eigenstate_exists : ∀ k, ∃ (psi : Ket N), normSquared psi = 1 ∧
    applyOp (projectors k) psi = psi

/-! ## Spectral gap -/

/-- The spectral gap of an operator is the difference between its two smallest eigenvalues -/
noncomputable def spectralGap (N M : Nat) (A : Operator N)
    (sd : SpectralDecomp N M A) (hM : M >= 2) : Real :=
  sd.eigenvalues ⟨1, hM⟩ - sd.eigenvalues ⟨0, Nat.lt_of_lt_of_le (by norm_num : 0 < 2) hM⟩

notation "Δ(" A ")" => spectralGap _ _ A

/-- The spectral gap is positive when there are at least 2 distinct eigenvalues -/
theorem spectralGap_pos (N M : Nat) (A : Operator N)
    (sd : SpectralDecomp N M A) (hM : M >= 2) :
    spectralGap N M A sd hM > 0 := by
  simp only [spectralGap]
  have h0 : 0 < M := Nat.lt_of_lt_of_le (by norm_num : 0 < 2) hM
  have h := sd.ordered ⟨0, h0⟩ ⟨1, hM⟩
  simp only [Fin.mk_lt_mk] at h
  linarith [h (by norm_num : (0 : Nat) < 1)]

/-! ## Minimum eigenvalue (ground energy) -/

/-- The minimum eigenvalue of a Hermitian operator (requires M > 0) -/
noncomputable def groundEnergy (N M : Nat) (A : Operator N)
    (sd : SpectralDecomp N M A) (hM : M > 0) : Real :=
  sd.eigenvalues ⟨0, hM⟩

notation "E₀(" A ")" => groundEnergy _ _ A

/-! ## Variational principle -/

/-- The variational principle: ⟨φ|A|φ⟩ ≥ E₀ for any normalized state φ.

    This is a fundamental result in spectral theory stating that the expectation
    value of a Hermitian operator is bounded below by its smallest eigenvalue.
    The proof uses the spectral decomposition A = Σ_k E_k P_k to show:
    ⟨φ|A|φ⟩ = Σ_k E_k |⟨k|φ⟩|² ≥ E₀ Σ_k |⟨k|φ⟩|² = E₀ -/
theorem variational_principle (N M : Nat) (A : Operator N)
    (sd : SpectralDecomp N M A) (hM : M > 0) (phi : Ket N)
    (hphi : normSquared phi = 1) :
    (expectation A phi).re >= groundEnergy N M A sd hM := by
  -- Step 1: Use spectral decomposition A = Σ_k E_k • P_k
  have hspec := sd.spectral_decomp
  -- Compute expectation using spectral decomposition
  have h_exp : expectation A phi = expectation (Finset.sum Finset.univ
      (fun k => (sd.eigenvalues k : Complex) • sd.projectors k)) phi := by
    exact congrArg (fun B => expectation B phi) hspec
  -- Step 2: Expectation of sum = sum of expectations
  have h_sum : expectation (Finset.sum Finset.univ
      (fun k => (sd.eigenvalues k : Complex) • sd.projectors k)) phi =
      Finset.sum Finset.univ (fun k => expectation ((sd.eigenvalues k : Complex) • sd.projectors k) phi) := by
    exact expectation_finsum Finset.univ _ phi
  -- Step 3: Expectation of E_k • P_k = E_k * expectation P_k
  have h_smul : ∀ k, expectation ((sd.eigenvalues k : Complex) • sd.projectors k) phi =
      (sd.eigenvalues k : Complex) * expectation (sd.projectors k) phi := by
    intro k
    exact expectation_smul (sd.eigenvalues k : Complex) (sd.projectors k) phi
  -- Combine into main expression
  have h_main : expectation A phi = Finset.sum Finset.univ (fun k =>
      (sd.eigenvalues k : Complex) * expectation (sd.projectors k) phi) := by
    rw [h_exp, h_sum]
    congr 1
    ext k
    exact h_smul k
  -- Step 4: Take real part - real part of sum equals sum of real parts
  have hre_sum : (Finset.sum Finset.univ (fun k =>
      (sd.eigenvalues k : Complex) * expectation (sd.projectors k) phi)).re =
      Finset.sum Finset.univ (fun k =>
        (sd.eigenvalues k : Complex).re * (expectation (sd.projectors k) phi).re) := by
    rw [Complex.re_sum]
    congr 1
    ext k
    rw [Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re]
    ring
  -- Step 5: Each projector expectation has non-negative real part
  have hproj_nonneg : ∀ k, (expectation (sd.projectors k) phi).re >= 0 := by
    intro k
    exact projector_expectation_nonneg (sd.projectors k) (sd.projector_isProjector k) phi
  -- Step 6: E_0 <= E_k for all k (from ordering)
  have hE0_le : ∀ k : Fin M, sd.eigenvalues ⟨0, hM⟩ <= sd.eigenvalues k := by
    intro k
    by_cases hk0 : k.val = 0
    · have hk_eq : k = ⟨0, hM⟩ := Fin.ext hk0
      rw [hk_eq]
    · have h0k : (0 : Nat) < k.val := Nat.pos_of_ne_zero hk0
      have hlt := sd.ordered ⟨0, hM⟩ k (Fin.mk_lt_mk.mpr h0k)
      exact le_of_lt hlt
  -- Step 7: Sum of projector expectations = 1 (using projector_complete)
  have hsum_one : (Finset.sum Finset.univ (fun k =>
      expectation (sd.projectors k) phi)).re = 1 := by
    rw [← expectation_finsum]
    rw [sd.projector_complete]
    rw [expectation_identity, hphi]
    rfl
  -- Step 8: Lower bound by E_0 * (sum of expectation real parts)
  have hbound : Finset.sum Finset.univ (fun k =>
        sd.eigenvalues k * (expectation (sd.projectors k) phi).re) >=
      sd.eigenvalues ⟨0, hM⟩ * Finset.sum Finset.univ (fun k =>
        (expectation (sd.projectors k) phi).re) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k _
    have hnneg := hproj_nonneg k
    have hle := hE0_le k
    exact mul_le_mul_of_nonneg_right hle hnneg
  -- Final calculation
  rw [h_main, hre_sum]
  simp only [Complex.ofReal_re]
  calc Finset.sum Finset.univ (fun k =>
        sd.eigenvalues k * (expectation (sd.projectors k) phi).re)
      >= sd.eigenvalues ⟨0, hM⟩ * Finset.sum Finset.univ (fun k =>
        (expectation (sd.projectors k) phi).re) := hbound
    _ = sd.eigenvalues ⟨0, hM⟩ * (Finset.sum Finset.univ (fun k =>
        expectation (sd.projectors k) phi)).re := by
          congr 1
          rw [Complex.re_sum]
    _ = sd.eigenvalues ⟨0, hM⟩ * 1 := by rw [hsum_one]
    _ = groundEnergy N M A sd hM := by simp [groundEnergy]

/-- The minimum is achieved by ground state.

    This states that there exists a normalized eigenstate achieving the ground energy.
    The ground eigenstate is constructed from the ground projector P₀. -/
theorem variational_minimum (N M : Nat) (A : Operator N)
    (sd : SpectralDecomp N M A) (hM : M > 0) :
    ∃ (psi : Ket N), normSquared psi = 1 ∧
      (expectation A psi).re = groundEnergy N M A sd hM := by
  -- Get a normalized ground eigenstate from eigenstate_exists
  obtain ⟨psi, hpsi_norm, hpsi_eigen⟩ := sd.eigenstate_exists ⟨0, hM⟩
  use psi
  constructor
  · exact hpsi_norm
  · -- Show ⟨psi|A|psi⟩ = E_0
    -- Since P_0 psi = psi and A = Σ E_k P_k:
    -- ⟨psi|A|psi⟩ = Σ E_k ⟨psi|P_k|psi⟩
    -- For k ≠ 0: ⟨psi|P_k|psi⟩ = ⟨P_0 psi|P_k|psi⟩ = ⟨psi|P_0 P_k|psi⟩ = 0
    -- For k = 0: ⟨psi|P_0|psi⟩ = ⟨psi|psi⟩ = 1
    -- So ⟨psi|A|psi⟩ = E_0 · 1 = E_0
    have hspec := sd.spectral_decomp
    have h_exp : expectation A psi = expectation (Finset.sum Finset.univ
        (fun k => (sd.eigenvalues k : Complex) • sd.projectors k)) psi := by
      exact congrArg (fun B => expectation B psi) hspec
    rw [h_exp, expectation_finsum]
    simp only [expectation_smul]
    -- The sum equals E_0 * expectation P_0 psi + Σ_{k≠0} E_k * expectation P_k psi
    -- For k ≠ 0, expectation P_k psi = 0
    have h_orthog : ∀ k : Fin M, k ≠ ⟨0, hM⟩ →
        expectation (sd.projectors k) psi = 0 := by
      intro k hk
      -- P_k P_0 = 0 for k ≠ 0
      have hPkP0 : sd.projectors k * sd.projectors ⟨0, hM⟩ = 0 :=
        sd.projector_orthogonal k ⟨0, hM⟩ hk
      -- ⟨psi|P_k|psi⟩ = ⟨psi|P_k P_0|psi⟩ (since P_0 psi = psi)
      simp only [expectation, innerProd]
      -- applyOp P_k psi = applyOp P_k (applyOp P_0 psi) = applyOp (P_k * P_0) psi
      have h1 : applyOp (sd.projectors k) psi =
          applyOp (sd.projectors k) (applyOp (sd.projectors ⟨0, hM⟩) psi) := by
        rw [hpsi_eigen]
      rw [h1, ← applyOp_mul, hPkP0]
      -- applyOp 0 psi = 0
      simp only [applyOp]
      simp [Matrix.zero_apply]
    -- For k = 0, expectation P_0 psi = ‖psi‖² = 1
    have h_ground : expectation (sd.projectors ⟨0, hM⟩) psi = 1 := by
      simp only [expectation]
      rw [hpsi_eigen]
      -- innerProd psi psi = normSquared psi (as Complex)
      have h := innerProd_self_eq_normSquared psi
      -- h : (innerProd psi psi).re = normSquared psi
      -- We need innerProd psi psi = 1 (as Complex)
      -- Since innerProd psi psi is real and equals normSquared psi = 1
      have h2 : innerProd psi psi = (normSquared psi : Complex) := by
        apply Complex.ext
        · exact h
        · -- imaginary part is 0
          simp only [innerProd, Complex.ofReal_im]
          rw [Complex.im_sum]
          apply Finset.sum_eq_zero
          intro i _
          simp only [conj_eq_star, star_eq_starRingEnd]
          rw [← Complex.normSq_eq_conj_mul_self]
          exact Complex.ofReal_im _
      rw [h2, hpsi_norm]
      rfl
    -- The sum simplifies to E_0 * 1
    have h_sum : Finset.sum Finset.univ (fun k =>
        (sd.eigenvalues k : Complex) * expectation (sd.projectors k) psi) =
        (sd.eigenvalues ⟨0, hM⟩ : Complex) * 1 := by
      rw [Finset.sum_eq_single (⟨0, hM⟩ : Fin M)]
      · rw [h_ground]
      · intro k _ hk
        rw [h_orthog k hk, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ (⟨0, hM⟩ : Fin M)) h
    rw [h_sum]
    simp only [mul_one, Complex.ofReal_re, groundEnergy]

end UAQO
