/-
  Proof of eigenvalue_condition using the Matrix Determinant Lemma.

  Goal: Show that λ is an eigenvalue of H(s) = -(1-s)|ψ₀⟩⟨ψ₀| + s·H_z iff
  either λ = s·E_k for some k, or the secular equation holds:
  1/(1-s) = (1/N) Σ_k d_k/(s·E_k - λ)
-/
import UAQO.Spectral.AdiabaticHamiltonian
import UAQO.Proofs.Spectral.MatrixDetLemma
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Algebra.Group.Pi.Units
-- Note: We use Mathlib's star_mul', Complex.conj_ofReal for conjugation lemmas.
-- Our innerProd is a custom definition (Finset.sum of conj * v), so innerProd_smul_*
-- lemmas are specific to our definition, not duplicating Mathlib's inner_smul_*.

namespace UAQO.Proofs.Spectral

open UAQO Matrix Finset

/-! ## Key lemmas connecting eigenvalues to determinants -/

/-- For finite-dimensional matrices, λ is an eigenvalue iff det(λI - A) = 0.

    This is a standard result from linear algebra. -/
theorem isEigenvalue_iff_det_eq_zero {N : Nat} [NeZero N] (A : Matrix (Fin N) (Fin N) ℂ)
    (lambda : ℂ) :
    (∃ v : Fin N → ℂ, v ≠ 0 ∧ A *ᵥ v = lambda • v) ↔
    (lambda • (1 : Matrix (Fin N) (Fin N) ℂ) - A).det = 0 := by
  -- Standard linear algebra: λ is eigenvalue iff (λI - A) is singular iff det = 0
  -- Use Matrix.exists_mulVec_eq_zero_iff: ∃ v ≠ 0, M *ᵥ v = 0 ↔ M.det = 0
  constructor
  · -- Forward: if Av = λv for some v ≠ 0, then det(λI - A) = 0
    intro ⟨v, hv_ne, hv_eq⟩
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    use v, hv_ne
    -- Show (λI - A) *ᵥ v = 0
    -- (λI - A) *ᵥ v = λI *ᵥ v - A *ᵥ v = λv - Av = λv - λv = 0
    simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [hv_eq]
    simp
  · -- Backward: if det(λI - A) = 0, then there exists v ≠ 0 with Av = λv
    intro hdet
    rw [← Matrix.exists_mulVec_eq_zero_iff] at hdet
    obtain ⟨v, hv_ne, hv_eq⟩ := hdet
    use v, hv_ne
    -- Show Av = λv given (λI - A) *ᵥ v = 0
    -- (λI - A) *ᵥ v = 0 means λv - Av = 0, so Av = λv
    simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at hv_eq
    -- hv_eq : lambda • v - A *ᵥ v = 0
    -- We need: A *ᵥ v = lambda • v
    have h := sub_eq_zero.mp hv_eq
    -- h : lambda • v = A *ᵥ v
    exact h.symm

/-! ## Structure of the adiabatic Hamiltonian -/

/-- The adiabatic Hamiltonian can be written as s·H_z minus a rank-1 projector.

    H(s) = -(1-s)|ψ₀⟩⟨ψ₀| + s·H_z = s·H_z - (1-s)|ψ₀⟩⟨ψ₀| -/
theorem adiabaticHam_eq {n M : Nat} (es : EigenStructure n M)
    (s : Real) (hs : 0 <= s ∧ s <= 1) :
    adiabaticHam es s hs =
    (s : Complex) • es.toHamiltonian.toOperator +
    (-(1 - s) : Complex) • projectorOnState (equalSuperpositionN n) := by
  unfold adiabaticHam
  rw [add_comm]

/-! ## Helper lemmas for scalar outer products -/

/-- Conjugate distributes over multiplication.
    This is a direct application of Mathlib's star_mul'. -/
lemma conj_mul' (a b : ℂ) : conj (a * b) = conj a * conj b :=
  map_mul (starRingEnd ℂ) a b

/-- Outer product with scaled vectors: outerProd(a•u)(a•v) = |a|²•outerProd(u)(v) -/
lemma outerProd_smul_smul {N : Nat} (a : ℂ) (u v : Ket N) :
    outerProd (a • u) (a • v) = (a * conj a) • outerProd u v := by
  ext i j
  simp only [outerProd, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply, conj_mul']
  ring

/-- Conjugate of a real number is itself.
    This uses Mathlib's Complex.conj_ofReal. -/
lemma conj_ofReal' (a : ℝ) : conj (a : ℂ) = (a : ℂ) :=
  Complex.conj_ofReal a

/-- For real scalars, |a|² = a² -/
lemma outerProd_smul_smul_real {N : Nat} (a : ℝ) (u v : Ket N) :
    outerProd ((a : ℂ) • u) ((a : ℂ) • v) = (a^2 : ℂ) • outerProd u v := by
  rw [outerProd_smul_smul, conj_ofReal']
  simp only [← sq]

/-- For non-negative real scalars, c•outerProd(u)(u) = outerProd(√c•u)(√c•u) -/
lemma smul_outerProd_self_eq_outerProd_sqrt_smul {N : Nat} (c : ℝ) (hc : c ≥ 0) (u : Ket N) :
    (c : ℂ) • outerProd u u = outerProd ((Real.sqrt c : ℂ) • u) ((Real.sqrt c : ℂ) • u) := by
  rw [outerProd_smul_smul_real]
  congr 1
  norm_cast
  exact (Real.sq_sqrt hc).symm

/-- Inner product scales conjugate-linearly in first argument -/
lemma innerProd_smul_left {N : Nat} (a : ℂ) (u v : Ket N) :
    innerProd (a • u) v = conj a * innerProd u v := by
  simp only [innerProd, Pi.smul_apply, smul_eq_mul, conj_mul']
  conv_lhs => arg 2; ext i; rw [mul_assoc]
  rw [← Finset.mul_sum]

/-- Inner product scales linearly in second argument -/
lemma innerProd_smul_right {N : Nat} (a : ℂ) (u v : Ket N) :
    innerProd u (a • v) = a * innerProd u v := by
  simp only [innerProd, Pi.smul_apply, smul_eq_mul]
  conv_lhs => arg 2; ext i; rw [mul_left_comm]
  rw [← Finset.mul_sum]

/-- Operator application distributes over scalar multiplication -/
lemma applyOp_smul {N : Nat} (A : Operator N) (a : ℂ) (v : Ket N) :
    A ⬝ (a • v) = a • (A ⬝ v) := by
  unfold applyOp
  ext i
  simp only [Pi.smul_apply, smul_eq_mul]
  conv_lhs => arg 2; ext j; rw [mul_left_comm]
  rw [← Finset.mul_sum]

/-- Inner product with scaled operator application: ⟨a•u|A(a•v)⟩ = |a|²⟨u|Av⟩ -/
lemma innerProd_smul_applyOp_smul {N : Nat} (A : Operator N) (a : ℂ) (u v : Ket N) :
    innerProd (a • u) (A ⬝ (a • v)) = (a * conj a) * innerProd u (A ⬝ v) := by
  rw [applyOp_smul, innerProd_smul_left, innerProd_smul_right]
  ring

/-! ## Bridge lemmas between UAQO and Mathlib definitions -/

/-- applyOp equals mulVec (matrix-vector multiplication) -/
lemma applyOp_eq_mulVec {N : Nat} (A : Operator N) (v : Ket N) :
    A ⬝ v = A *ᵥ v := by
  unfold applyOp mulVec dotProduct
  rfl

/-- normSquared v > 0 implies v ≠ 0 as a function.
    Note: This uses our custom normSquared definition, not Mathlib's norm.
    Mathlib has norm_pos_iff/norm_ne_zero_iff for their norm. -/
lemma normSquared_pos_imp_ne_zero {N : Nat} (v : Fin N → ℂ) (hv : normSquared v > 0) : v ≠ 0 := by
  rw [normSquared_pos_iff] at hv
  intro heq
  obtain ⟨i, hi⟩ := hv
  rw [heq] at hi
  simp at hi

/-- v ≠ 0 implies normSquared v > 0.
    Note: This uses our custom normSquared definition, not Mathlib's norm. -/
lemma ne_zero_imp_normSquared_pos {N : Nat} (v : Fin N → ℂ) (hv : v ≠ 0) : normSquared v > 0 := by
  rw [normSquared_pos_iff]
  by_contra hall
  push_neg at hall
  apply hv
  ext i
  exact hall i

/-! ## The resolvent of the diagonal Hamiltonian -/

/-- When λ ≠ s·E_k for all k, the matrix (λI - s·H_z) is invertible
    and we can compute its inverse. -/
theorem diag_resolvent_invertible {n M : Nat} (es : EigenStructure n M)
    (_hM : M > 0) (s : Real) (lambda : Real)
    (hne : ∀ k : Fin M, lambda ≠ s * es.eigenvalues k) :
    IsUnit ((lambda : Complex) • (1 : Matrix (Fin (qubitDim n)) (Fin (qubitDim n)) ℂ) -
            (s : Complex) • es.toHamiltonian.toOperator).det := by
  -- The matrix λI - s·H_z is diagonal with entries λ - s·E_{a(z)}
  -- Step 1: Express the matrix as a diagonal matrix
  have hdiag : (lambda : Complex) • (1 : Matrix (Fin (qubitDim n)) (Fin (qubitDim n)) ℂ) -
               (s : Complex) • es.toHamiltonian.toOperator =
               Matrix.diagonal (fun z => (lambda : Complex) - (s : Complex) * es.eigenvalues (es.assignment z)) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
               EigenStructure.toHamiltonian, DiagonalHamiltonian.toOperator, Matrix.diagonal_apply]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij]
  -- Step 2: Compute determinant of diagonal matrix
  rw [hdiag, Matrix.det_diagonal]
  -- Step 3: Show product is nonzero (IsUnit means it's a unit, i.e., nonzero for Complex)
  rw [isUnit_iff_ne_zero]
  rw [Finset.prod_ne_zero_iff]
  intro z _
  -- Each factor (lambda - s * E_{a(z)}) is nonzero
  simp only [ne_eq, sub_eq_zero]
  intro hcontra
  -- hcontra : (lambda : Complex) = (s : Complex) * es.eigenvalues (es.assignment z)
  have hreal : lambda = s * es.eigenvalues (es.assignment z) := by
    have h1 : (lambda : Complex).re = ((s : Complex) * es.eigenvalues (es.assignment z)).re := by
      rw [hcontra]
    simp only [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, mul_zero, sub_zero] at h1
    exact h1
  exact hne (es.assignment z) hreal

/-- The expectation ⟨ψ₀|(λI - s·H_z)⁻¹|ψ₀⟩ equals (1/N) Σ_k d_k/(λ - s·E_k).

    Since |ψ₀⟩ = (1/√N, ..., 1/√N) and (λI - s·H_z) is diagonal:
    ⟨ψ₀|(λI - s·H_z)⁻¹|ψ₀⟩ = (1/N) Σ_z 1/(λ - s·E_{a(z)})
                            = (1/N) Σ_k d_k/(λ - s·E_k) -/
-- Helper: The matrix λI - s·H_z is diagonal
lemma resolvent_matrix_is_diagonal {n M : Nat} (es : EigenStructure n M) (s lambda : Real) :
    (lambda : Complex) • (1 : Matrix (Fin (qubitDim n)) (Fin (qubitDim n)) ℂ) -
    (s : Complex) • es.toHamiltonian.toOperator =
    Matrix.diagonal (fun z => (lambda : Complex) - (s : Complex) * es.eigenvalues (es.assignment z)) := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
             EigenStructure.toHamiltonian, DiagonalHamiltonian.toOperator, Matrix.diagonal_apply]
  by_cases hij : i = j
  · simp [hij]
  · simp [hij]

-- Helper: Inner product of ψ₀ with diagonal matrix applied to ψ₀
lemma innerProd_diagonal_equalSuperposition {N : Nat} [NeZero N] (d : Fin N → ℂ) :
    innerProd (equalSuperposition N) (Matrix.diagonal d *ᵥ equalSuperposition N) =
    (1 / N : ℂ) * Finset.sum Finset.univ d := by
  simp only [innerProd, equalSuperposition, Matrix.mulVec_diagonal]
  -- LHS = Σ_z conj(1/√N) * (d_z * 1/√N)
  --     = Σ_z (1/√N) * (d_z * 1/√N)  (since 1/√N is real)
  --     = (1/N) * Σ_z d_z
  have hsqrt_pos : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (NeZero.pos N))
  have hsqrt_ne : (Real.sqrt N : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt hsqrt_pos
  have hN_ne : (N : ℂ) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    exact NeZero.ne N
  -- conj(1/√N) = 1/√N since √N is real
  have hconj : conj ((1 : ℂ) / (Real.sqrt N : ℂ)) = (1 : ℂ) / (Real.sqrt N : ℂ) := by
    rw [conj_eq_star, Complex.star_def, map_div₀, map_one, Complex.conj_ofReal]
  simp_rw [hconj]
  -- Simplify: (1/√N) * (d z * (1/√N)) = d z / N
  have hsqN : (Real.sqrt N : ℂ) * (Real.sqrt N : ℂ) = (N : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg N), Complex.ofReal_natCast]
  have hsimp : ∀ z, (1 : ℂ) / (Real.sqrt N : ℂ) * (d z * ((1 : ℂ) / (Real.sqrt N : ℂ))) =
      d z / (N : ℂ) := fun z => by
    have hne : (Real.sqrt N : ℂ) ≠ 0 := hsqrt_ne
    field_simp
    rw [sq, hsqN]
    field_simp [hN_ne]
  simp_rw [hsimp]
  rw [← Finset.sum_div]
  field_simp [hN_ne]

-- Helper: Reindex sum over states to sum over energy levels
lemma sum_reindex_by_assignment {n M : Nat} (es : EigenStructure n M)
    (f : Fin M → ℂ) :
    Finset.sum Finset.univ (fun z : Fin (qubitDim n) => f (es.assignment z)) =
    Finset.sum Finset.univ (fun k : Fin M => (es.degeneracies k : ℂ) * f k) := by
  -- For each k, count how many z have assignment z = k
  -- By es.deg_count, this count equals es.degeneracies k
  -- So Σ_z f(a(z)) = Σ_k (#{z : a(z) = k}) * f(k) = Σ_k d_k * f(k)

  -- Use Fintype.sum_fiberwise: Σ_a f(g(a)) = Σ_b (#{a : g(a) = b}) * f(b)
  -- when g : α → β
  have h1 : Finset.sum Finset.univ (fun z => f (es.assignment z)) =
      Finset.sum Finset.univ (fun k =>
        (Finset.filter (fun z => es.assignment z = k) Finset.univ).card • f k) := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
          (g := es.assignment) (f := fun z => f (es.assignment z))]
    · congr 1
      ext k
      -- Sum over {z : a(z) = k} of f(a(z)) = Sum over {z : a(z) = k} of f(k) = #{...} • f(k)
      have heq : ∀ z ∈ Finset.filter (fun z => es.assignment z = k) Finset.univ,
          f (es.assignment z) = f k := fun z hz => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
        rw [hz]
      rw [Finset.sum_congr rfl heq, Finset.sum_const]
    · intro _ _; exact Finset.mem_univ _
  rw [h1]
  congr 1
  ext k
  rw [es.deg_count k, nsmul_eq_mul]

theorem resolvent_expectation_formula {n M : Nat} (es : EigenStructure n M)
    (hM : M > 0) (s : Real) (lambda : Real)
    (hne : ∀ k : Fin M, lambda ≠ s * es.eigenvalues k) :
    let R := ((lambda : Complex) • (1 : Matrix (Fin (qubitDim n)) (Fin (qubitDim n)) ℂ) -
              (s : Complex) • es.toHamiltonian.toOperator)⁻¹
    innerProd (equalSuperpositionN n) (R ⬝ equalSuperpositionN n) =
    (1 / qubitDim n : Complex) * Finset.sum Finset.univ (fun k : Fin M =>
      (es.degeneracies k : Complex) / ((lambda : Complex) - s * es.eigenvalues k)) := by
  intro R

  -- Step 1: The matrix λI - s·H_z is diagonal
  have hdiag := resolvent_matrix_is_diagonal es s lambda

  -- Step 2: Each diagonal entry λ - s·E_{a(z)} is nonzero
  have hdiag_ne : ∀ z, (lambda : ℂ) - (s : ℂ) * es.eigenvalues (es.assignment z) ≠ 0 := fun z => by
    intro hcontra
    have hreal : lambda = s * es.eigenvalues (es.assignment z) := by
      have h1 : ((lambda : ℂ) - (s : ℂ) * es.eigenvalues (es.assignment z)).re = 0 := by
        rw [hcontra]; simp
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
                 mul_zero, sub_zero] at h1
      linarith
    exact hne (es.assignment z) hreal

  -- Step 3: The inverse is diagonal with entries 1/(λ - s·E_{a(z)})
  have hinv_diag : R = Matrix.diagonal (fun z => ((lambda : ℂ) - (s : ℂ) * es.eigenvalues (es.assignment z))⁻¹) := by
    simp only [R, hdiag]
    rw [Matrix.inv_diagonal]
    -- For Pi types with GroupWithZero codomain, when the function is a unit,
    -- Ring.inverse f = f⁻¹ (Pi inverse) = fun z => (f z)⁻¹
    let f := fun z => (lambda : ℂ) - (s : ℂ) * es.eigenvalues (es.assignment z)
    -- The function is a unit since all values are nonzero
    have hunit : IsUnit f := by
      rw [Pi.isUnit_iff]
      intro z
      exact (hdiag_ne z).isUnit
    -- For a unit, Ring.inverse equals the group inverse
    have heq : Ring.inverse f = f⁻¹ := by
      obtain ⟨u, hu⟩ := hunit
      rw [← hu]
      rw [Ring.inverse_unit]
      ext z
      simp only [Units.val_inv_eq_inv_val, Pi.inv_apply]
    rw [heq]
    -- Pi.inv is pointwise
    ext i j
    simp only [Matrix.diagonal_apply, Pi.inv_apply]
    split_ifs <;> rfl

  -- Step 4: Use innerProd_diagonal_equalSuperposition
  haveI : NeZero (qubitDim n) := qubitDim_neZero n

  -- The inner product is (1/N) * sum of diagonal entries
  have hinner : innerProd (equalSuperpositionN n) (R ⬝ equalSuperpositionN n) =
      (1 / qubitDim n : ℂ) * Finset.sum Finset.univ
        (fun z => ((lambda : ℂ) - (s : ℂ) * es.eigenvalues (es.assignment z))⁻¹) := by
    unfold applyOp equalSuperpositionN
    rw [hinv_diag]
    exact innerProd_diagonal_equalSuperposition _

  rw [hinner]
  congr 1
  -- Now reindex the sum from z to k
  -- Σ_z 1/(λ - s·E_{a(z)}) = Σ_k d_k/(λ - s·E_k) = Σ_k d_k * 1/(λ - s·E_k)
  rw [sum_reindex_by_assignment es (fun k => ((lambda : ℂ) - (s : ℂ) * es.eigenvalues k)⁻¹)]
  -- The sums are equal up to rewriting d_k/(λ-s·E_k) = d_k * (λ-s·E_k)⁻¹
  simp only [div_eq_mul_inv]

/-! ## Main theorem: The secular equation -/

/-- The determinant of λI - H(s) factors using the matrix determinant lemma.

    det(λI - H(s)) = det(λI - s·H_z - (-(1-s))|ψ₀⟩⟨ψ₀|)
                   = det(λI - s·H_z) · (1 + (-(1-s))·⟨ψ₀|(λI - s·H_z)⁻¹|ψ₀⟩)
                   = det(λI - s·H_z) · (1 - (1-s)·⟨ψ₀|(λI - s·H_z)⁻¹|ψ₀⟩) -/
theorem det_adiabaticHam_factored {n M : Nat} (es : EigenStructure n M)
    (hM : M > 0) (s : Real) (hs : 0 <= s ∧ s < 1) (lambda : Real)
    (hne : ∀ k : Fin M, lambda ≠ s * es.eigenvalues k) :
    let A := (lambda : Complex) • (1 : Matrix (Fin (qubitDim n)) (Fin (qubitDim n)) ℂ) -
             (s : Complex) • es.toHamiltonian.toOperator
    let psi0 := equalSuperpositionN n
    ((lambda : Complex) • 1 - adiabaticHam es s ⟨hs.1, le_of_lt hs.2⟩).det =
    A.det * (1 + (1 - s : Complex) * innerProd psi0 (A⁻¹ ⬝ psi0)) := by
  -- The proof uses the matrix determinant lemma:
  -- det(A + |u⟩⟨v|) = det(A)(1 + ⟨v|A⁻¹|u⟩)
  --
  -- H(s) = -(1-s)|ψ₀⟩⟨ψ₀| + s·H_z
  -- λI - H(s) = λI - s·H_z + (1-s)|ψ₀⟩⟨ψ₀| = A + (1-s)|ψ₀⟩⟨ψ₀|
  -- Write (1-s)|ψ₀⟩⟨ψ₀| = |u⟩⟨u| where u = √(1-s)·ψ₀
  -- Then det(λI - H(s)) = det(A)(1 + ⟨u|A⁻¹|u⟩) = det(A)(1 + (1-s)⟨ψ₀|A⁻¹|ψ₀⟩)
  intro A psi0

  -- Step 1: Show λI - H(s) = A + (1-s)|ψ₀⟩⟨ψ₀|
  have h_lhs_eq : (lambda : Complex) • 1 - adiabaticHam es s ⟨hs.1, le_of_lt hs.2⟩ =
      A + ((1 : ℝ) - s : Complex) • projectorOnState psi0 := by
    unfold adiabaticHam projectorOnState A
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.add_apply, smul_eq_mul]
    simp only [EigenStructure.toHamiltonian, DiagonalHamiltonian.toOperator,
               outerProd, Matrix.of_apply]
    push_cast
    ring

  -- Step 2: Get hypothesis that 1 - s ≥ 0
  have h1ms_nonneg : (1 : ℝ) - s ≥ 0 := by linarith [hs.2]

  -- Step 3: Use the scalar outerProd lemma
  have h_cast_eq : ((1 : ℝ) - s : ℂ) = ((1 - s : ℝ) : ℂ) := by push_cast; ring
  have h_outerProd_eq : ((1 : ℝ) - s : Complex) • projectorOnState psi0 =
      outerProd ((Real.sqrt (1 - s) : ℂ) • psi0) ((Real.sqrt (1 - s) : ℂ) • psi0) := by
    unfold projectorOnState
    rw [h_cast_eq]
    exact smul_outerProd_self_eq_outerProd_sqrt_smul (1 - s) h1ms_nonneg psi0

  -- Step 4: Get IsUnit hypothesis for A.det
  have hA_unit : IsUnit A.det := diag_resolvent_invertible es hM s lambda hne

  -- Step 5: Apply matrix determinant lemma
  let u := (Real.sqrt (1 - s) : ℂ) • psi0
  have h_det_factored : (A + outerProd u u).det = A.det * (1 + innerProd u (A⁻¹ ⬝ u)) :=
    matrix_det_lemma A u u hA_unit

  -- Step 6: Simplify the inner product term
  -- ⟨√(1-s)·ψ₀|A⁻¹|√(1-s)·ψ₀⟩ = (1-s)⟨ψ₀|A⁻¹|ψ₀⟩
  have h_inner_eq : innerProd u (A⁻¹ ⬝ u) = ((1 : ℝ) - s : Complex) * innerProd psi0 (A⁻¹ ⬝ psi0) := by
    have h := innerProd_smul_applyOp_smul A⁻¹ (Real.sqrt (1 - s) : ℂ) psi0 psi0
    simp only [u] at h ⊢
    rw [h, conj_ofReal']
    congr 1
    -- √(1-s) * √(1-s) = 1 - s
    have hsq : Real.sqrt (1 - s) * Real.sqrt (1 - s) = (1 - s) := Real.mul_self_sqrt h1ms_nonneg
    -- Convert to Complex: need to show (√(1-s) : ℂ) * (√(1-s) : ℂ) = (1 : ℂ) - (s : ℂ)
    rw [← Complex.ofReal_mul, hsq, Complex.ofReal_sub, Complex.ofReal_one]

  -- Step 7: Combine everything
  -- Need to show the coefficient matches
  have h_coeff_eq : ((1 : ℝ) - s : Complex) = (1 - s : Complex) := by push_cast; ring
  rw [h_lhs_eq, h_outerProd_eq]
  change (A + outerProd u u).det = _
  rw [h_det_factored, h_inner_eq, h_coeff_eq]

/-- The eigenvalue condition for H(s).

    λ is an eigenvalue of H(s) = -(1-s)|ψ₀⟩⟨ψ₀| + s·H_z iff
    either (1) λ = s·E_k for some degenerate level k (d_k > 1), or
    (2) λ ≠ s·E_k for all k, AND the secular equation: 1/(1-s) = (1/N) Σ_k d_k/(s·E_k - λ)

    NOTE: Requires s > 0. For s = 0, H(0) = -|ψ₀⟩⟨ψ₀| has eigenvalue 0 regardless
    of degeneracies.

    For non-degenerate levels (d_k = 1), s·E_k is NOT an eigenvalue because the
    only eigenvector |z⟩ satisfies ⟨ψ₀|z⟩ = 1/√N ≠ 0.

    The non-collision condition ensures the secular equation is well-defined. -/
theorem eigenvalue_condition_proof {n M : Nat} (es : EigenStructure n M)
    (hM : M > 0) (s : Real) (hs : 0 < s ∧ s < 1) (lambda : Real) :
    IsEigenvalue (adiabaticHam es s ⟨le_of_lt hs.1, le_of_lt hs.2⟩) lambda ↔
    (∃ z, lambda = s * es.eigenvalues (es.assignment z) ∧
          es.degeneracies (es.assignment z) > 1) ∨
     ((∀ k : Fin M, lambda ≠ s * es.eigenvalues k) ∧
      1 / (1 - s) = (1 / qubitDim n) *
       Finset.sum Finset.univ (fun k =>
         (es.degeneracies k : Real) / (s * es.eigenvalues k - lambda))) := by
  -- The proof connects eigenvalues to determinants, then uses det_adiabaticHam_factored
  -- and resolvent_expectation_formula.
  --
  -- Key insight: For det = 0 when det(A) ≠ 0:
  --   det(A)(1 + (1-s)⟨ψ₀|A⁻¹|ψ₀⟩) = 0  implies  ⟨ψ₀|A⁻¹|ψ₀⟩ = -1/(1-s)
  --   By resolvent formula: (1/N) Σ_k d_k/(λ - s·E_k) = -1/(1-s)
  --   Negating denominators: (1/N) Σ_k d_k/(s·E_k - λ) = 1/(1-s)  ✓

  constructor
  · -- Forward direction: eigenvalue → condition
    intro heigen
    -- Case split: either λ = s·E_k for some k, or the secular equation holds
    by_cases hcase : ∃ k : Fin M, lambda = s * es.eigenvalues k
    · -- Case 1: λ = s·E_k for some k
      -- We must also prove d_k > 1, otherwise λ can't be an eigenvalue
      obtain ⟨k, hk⟩ := hcase
      -- First prove d_k > 1 using the fact that λ is an eigenvalue
      -- Key insight: If λ is eigenvalue with λ = s·E_k, eigenvector must be
      -- orthogonal to |ψ₀⟩, which requires d_k > 1.
      have hdeg_gt1 : es.degeneracies k > 1 := by
        by_contra hdeg_le1
        push_neg at hdeg_le1
        -- d_k ≤ 1, but d_k > 0 (es.deg_positive), so d_k = 1
        have hdeg := es.deg_positive k
        have hdeg_eq1 : es.degeneracies k = 1 := Nat.le_antisymm hdeg_le1 hdeg
        -- From heigen: ∃ v ≠ 0, H(s)v = λv
        obtain ⟨v, hv_pos, hv_eq⟩ := heigen
        have hv_ne : v ≠ 0 := normSquared_pos_imp_ne_zero v hv_pos
        -- H(s)v = -(1-s)|ψ₀⟩⟨ψ₀|v⟩ + s·H_z v = λv = s·E_k·v
        -- So: -(1-s)|ψ₀⟩⟨ψ₀|v⟩ = s·E_k·v - s·H_z v = s(E_k - H_z)v
        -- Taking inner product with v:
        -- -(1-s)⟨ψ₀|v⟩·⟨v|ψ₀⟩ = s⟨v|(E_k - H_z)|v⟩
        -- The RHS is ≤ 0 if v is in the ≥E_k eigenspaces of H_z
        -- But v must have support only in the k eigenspace (otherwise LHS ≠ RHS)
        -- For d_k = 1, the only state in k eigenspace is some basis state |z0⟩
        -- But ⟨ψ₀|z0⟩ = 1/√N ≠ 0, contradiction!
        -- Find the unique state z0 with assignment k
        have hcard := es.deg_count k
        rw [hdeg_eq1] at hcard
        have hfilter_card : (Finset.filter (fun z => es.assignment z = k) Finset.univ).card = 1 := hcard.symm
        -- Get the unique element
        have hfilter_singleton := Finset.card_eq_one.mp hfilter_card
        obtain ⟨z0, hz0_eq⟩ := hfilter_singleton
        have hz0_mem : z0 ∈ Finset.filter (fun z => es.assignment z = k) Finset.univ := by
          rw [hz0_eq]; exact Finset.mem_singleton_self z0
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz0_mem
        -- hz0_mem : es.assignment z0 = k
        -- Now we know the E_k eigenspace is exactly span{|z0⟩}
        -- For v to satisfy H(s)v = s·E_k·v, v must be in this eigenspace
        -- (otherwise H_z v would have components outside E_k)
        -- But then ⟨ψ₀|v⟩ = c·⟨ψ₀|z0⟩ = c/√N for some c ≠ 0
        -- This means the projector term doesn't vanish, contradiction
        -- For this formal proof, we use: if H(s)v = s·E_k·v and d_k = 1,
        -- then v = c·|z0⟩ and the equation becomes impossible (LHS ≠ RHS)

        -- The eigenvector equation: H(s)v = λv with λ = s·E_k
        -- Convert to operator equation
        have hs_bound : 0 ≤ s ∧ s ≤ 1 := ⟨le_of_lt hs.1, le_of_lt hs.2⟩
        rw [adiabaticHam_eq es s hs_bound] at hv_eq
        -- hv_eq: (s • Hz + (-(1-s)) • projector) ⬝ v = (s·E_k) • v
        rw [UAQO.applyOp_add, UAQO.applyOp_smul, UAQO.applyOp_smul] at hv_eq
        -- Now we have: s • (Hz v) + (-(1-s)) • (projector v) = s·E_k • v
        -- For d_k = 1, if v has any component in the E_k eigenspace,
        -- the Hz term gives s·E_k times that component
        -- The projector term gives (-(1-s))·⟨ψ₀|v⟩·|ψ₀⟩ ≠ 0
        -- Since |ψ₀⟩ is not proportional to |z0⟩, we get a contradiction

        -- Key observation: ⟨ψ₀|z0⟩ = 1/√N ≠ 0
        haveI : NeZero (qubitDim n) := qubitDim_neZero n
        have hinner_psi_z0 : innerProd (equalSuperpositionN n) (compBasisState (qubitDim n) z0) =
            (1 : ℂ) / (Real.sqrt (qubitDim n) : ℂ) := by
          simp only [innerProd, equalSuperpositionN, equalSuperposition, compBasisState]
          rw [Finset.sum_eq_single z0]
          · simp only [ite_true, conj_eq_star, Complex.star_def, map_div₀, map_one,
                       Complex.conj_ofReal, mul_one]
          · intro i _ hi
            simp only [hi, ite_false, mul_zero]
          · intro hz0_not_mem
            exact absurd (Finset.mem_univ z0) hz0_not_mem
        have hinner_ne_zero : innerProd (equalSuperpositionN n) (compBasisState (qubitDim n) z0) ≠ 0 := by
          rw [hinner_psi_z0]
          simp only [ne_eq, div_eq_zero_iff, one_ne_zero, Complex.ofReal_eq_zero,
                     Real.sqrt_eq_zero', not_le, false_or]
          exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne (qubitDim n)))

        -- The proof would continue by showing v must be proportional to |z0⟩,
        -- leading to |ψ₀⟩⟨ψ₀|v⟩ ≠ 0, contradicting the eigenvalue equation.
        -- This requires detailed linear algebra. For now, we note this is provable.
        -- The structure: v in 1-dim eigenspace ⟹ v = c|z0⟩ ⟹ ⟨ψ₀|v⟩ ≠ 0
        -- ⟹ projector term ≠ 0 ⟹ H(s)v ≠ s·E_k·v (contradiction with hv_eq)

        -- For a complete proof, we would show that the equation
        -- s • (Hz v) + (-(1-s)) • (|ψ₀⟩⟨ψ₀|v⟩) = (s·E_k) • v
        -- has no nonzero solution when d_k = 1.
        -- Since d_k = 1 means the E_k eigenspace is 1-dimensional,
        -- and |ψ₀⟩ is not in this eigenspace, there's no orthogonal complement.

        -- This is the key mathematical fact: non-degenerate eigenspaces of H_z
        -- cannot produce eigenvalues of H(s) at s·E_k because ⟨ψ₀|z⟩ ≠ 0.
        -- The detailed proof involves showing the eigenvalue equation is inconsistent.

        -- Component-wise analysis would show:
        -- For z0: (s·E_k - (1-s)/N)·(v z0) + (-(1-s)/N)·Σ_{j≠z0}(v j) = (s·E_k)·(v z0)
        -- For j≠z0 with E_j ≠ E_k: (s·E_j)·(v j) + (-(1-s)/N)·Σ_i(v i) = (s·E_k)·(v j)

        -- From the j≠z0 equation: (s·E_j - s·E_k)·(v j) = (1-s)/N·Σ_i(v i)
        -- If E_j ≠ E_k, this determines (v j) in terms of Σ_i(v i)
        -- The consistency conditions lead to a contradiction when d_k = 1.

        -- Since this is a deep linear algebra result, we appeal to the physics:
        -- For non-degenerate levels, there's no eigenvector orthogonal to |ψ₀⟩,
        -- so s·E_k cannot be an eigenvalue of H(s).
        -- The formal proof is technical but follows standard spectral theory.

        -- For the complete formalization, we prove v = 0 component-wise.
        -- The eigenvalue equation: H(s)v = λv with λ = s·E_k
        -- H(s) = s·H_z - (1-s)|ψ₀⟩⟨ψ₀|
        -- Component-wise: s·E_{a(z)}·(v z) - (1-s)·(ψ₀ z)·⟨ψ₀|v⟩ = λ·(v z)

        -- First, compute ⟨ψ₀|v⟩
        let psi0_v := innerProd (equalSuperpositionN n) v

        -- Key fact: The projector acts as |ψ₀⟩⟨ψ₀|v⟩ = psi0_v • |ψ₀⟩
        have hproj_v : applyOp (projectorOnState (equalSuperpositionN n)) v =
            psi0_v • equalSuperpositionN n := by
          unfold projectorOnState
          rw [applyOp_outerProd]

        -- Step 1: Show ⟨ψ₀|v⟩ = 0 from the z = z0 component
        -- At z = z0: s·E_k·(v z0) - (1-s)·(1/√N)·⟨ψ₀|v⟩ = s·E_k·(v z0)
        -- This gives (1-s)·(1/√N)·⟨ψ₀|v⟩ = 0
        -- Since s < 1 and N > 0, we get ⟨ψ₀|v⟩ = 0
        have hpsi0_v_zero : psi0_v = 0 := by
          -- Extract the z0 component from hv_eq
          have hcomp := congr_fun hv_eq z0
          -- Simplify both sides
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hcomp
          -- The diagonal Hamiltonian contribution at z0 gives E_k
          have hHz_z0 : (es.toHamiltonian.toOperator ⬝ v) z0 = (es.eigenvalues k : ℂ) * v z0 := by
            have h := congr_fun (applyOp_diagonalHam es.toHamiltonian v) z0
            simp only [EigenStructure.toHamiltonian, hz0_mem] at h
            exact h
          -- Substitute the Hamiltonian action
          rw [hHz_z0] at hcomp
          -- Now substitute the projector action
          rw [hproj_v] at hcomp
          simp only [Pi.smul_apply, smul_eq_mul, equalSuperpositionN, equalSuperposition] at hcomp
          -- hcomp: s * (E_k * v z0) + (-(1-s)) * (psi0_v * (1/√N)) = λ * v z0
          -- Since λ = s * E_k:
          rw [hk] at hcomp
          -- The s * E_k * v z0 terms cancel, leaving the projector term
          have h1ms_ne : (1 : ℂ) - (s : ℂ) ≠ 0 := by
            simp only [ne_eq, sub_eq_zero]
            intro heq
            have hre : (1 : ℂ).re = (s : ℂ).re := by rw [heq]
            simp only [Complex.one_re, Complex.ofReal_re] at hre
            linarith [hs.2]
          have hsqrtN_ne : (Real.sqrt (qubitDim n) : ℂ) ≠ 0 := by
            simp only [ne_eq, Complex.ofReal_eq_zero, Real.sqrt_eq_zero', not_le]
            exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne (qubitDim n)))
          -- From hcomp: s * E_k * v z0 + (-(1-s)) * psi0_v / √N = s * E_k * v z0
          -- So (-(1-s)) * psi0_v / √N = 0
          have hcancel : (-(1 - (s : ℂ))) * (psi0_v * (1 / (Real.sqrt (qubitDim n) : ℂ))) = 0 := by
            -- hcomp says: s * E_k * v z0 + -(1-s) * psi0_v * (1/√N) = s * E_k * v z0
            -- Rearranging: -(1-s) * psi0_v * (1/√N) = 0
            -- First normalize the coercion: ↑(s * E_k) = ↑s * ↑E_k
            simp only [Complex.ofReal_mul] at hcomp
            -- Also normalize associativity
            have heq : (s : ℂ) * ↑(es.eigenvalues k) * v z0 +
                       -(1 - (s : ℂ)) * (psi0_v * (1 / ↑(Real.sqrt ↑(qubitDim n)))) =
                       (s : ℂ) * ↑(es.eigenvalues k) * v z0 := by
              convert hcomp using 2 <;> ring
            have hsub := sub_eq_zero.mpr heq
            simp only [add_sub_cancel_left] at hsub
            exact hsub
          -- Since (1-s) ≠ 0 and √N ≠ 0, we get psi0_v = 0
          have h1ms_ne' : (-(1 - (s : ℂ))) ≠ 0 := neg_ne_zero.mpr h1ms_ne
          have hdiv : psi0_v * (1 / (Real.sqrt (qubitDim n) : ℂ)) = 0 :=
            (mul_eq_zero.mp hcancel).resolve_left h1ms_ne'
          have hdiv_ne : (1 : ℂ) / (Real.sqrt (qubitDim n) : ℂ) ≠ 0 := by
            simp only [ne_eq, div_eq_zero_iff, one_ne_zero, false_or]
            exact hsqrtN_ne
          exact (mul_eq_zero.mp hdiv).resolve_right hdiv_ne

        -- Step 2: Show v z = 0 for all z ≠ z0
        -- For z ≠ z0: s·E_{a(z)}·(v z) = s·E_k·(v z) (since ⟨ψ₀|v⟩ = 0)
        -- So s·(E_{a(z)} - E_k)·(v z) = 0
        -- Since s > 0 and E_{a(z)} ≠ E_k (by eigenval_ordered when a(z) ≠ k), v z = 0
        have hv_zero_off_z0 : ∀ z, z ≠ z0 → v z = 0 := by
          intro z hz_ne
          -- From hv_eq at component z:
          have hcomp := congr_fun hv_eq z
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hcomp
          -- The diagonal Hamiltonian contribution
          have hHz_z : (es.toHamiltonian.toOperator ⬝ v) z =
              (es.eigenvalues (es.assignment z) : ℂ) * v z := by
            have h := congr_fun (applyOp_diagonalHam es.toHamiltonian v) z
            simp only [EigenStructure.toHamiltonian] at h
            exact h
          rw [hHz_z] at hcomp
          -- Projector term with psi0_v = 0
          rw [hproj_v, hpsi0_v_zero] at hcomp
          simp only [zero_smul, Pi.zero_apply, mul_zero, add_zero] at hcomp
          -- hcomp: s * E_{a(z)} * (v z) = λ * (v z) = s * E_k * (v z)
          rw [hk] at hcomp
          -- Normalize the coercion
          simp only [Complex.ofReal_mul] at hcomp
          -- So s * (E_{a(z)} - E_k) * (v z) = 0
          -- From hcomp: s * E_{a(z)} * v z = s * E_k * v z
          -- Rearranging: s * (E_{a(z)} - E_k) * v z = 0
          have hdiff : (s : ℂ) * ((es.eigenvalues (es.assignment z) : ℂ) -
                       (es.eigenvalues k : ℂ)) * v z = 0 := by
            -- hcomp: s * (E_{a(z)} * v z) = s * E_k * v z
            -- First normalize associativity
            have heq : (s : ℂ) * ↑(es.eigenvalues (es.assignment z)) * v z =
                       (s : ℂ) * ↑(es.eigenvalues k) * v z := by
              calc (s : ℂ) * ↑(es.eigenvalues (es.assignment z)) * v z
                  = (s : ℂ) * (↑(es.eigenvalues (es.assignment z)) * v z) := by ring
                _ = (s : ℂ) * ↑(es.eigenvalues k) * v z := hcomp
            calc (s : ℂ) * ((es.eigenvalues (es.assignment z) : ℂ) - (es.eigenvalues k : ℂ)) * v z
                = (s : ℂ) * ↑(es.eigenvalues (es.assignment z)) * v z -
                  (s : ℂ) * ↑(es.eigenvalues k) * v z := by ring
              _ = (s : ℂ) * ↑(es.eigenvalues k) * v z -
                  (s : ℂ) * ↑(es.eigenvalues k) * v z := by rw [heq]
              _ = 0 := by ring
          -- Since s > 0 and E_{a(z)} ≠ E_k, we get v z = 0
          -- First show a(z) ≠ k since z ≠ z0 and d_k = 1
          have hassign_ne : es.assignment z ≠ k := by
            intro hassign_eq
            -- If a(z) = k then z ∈ filter, but filter has only z0
            have hz_mem' : z ∈ Finset.filter (fun z' => es.assignment z' = k) Finset.univ := by
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              exact hassign_eq
            rw [hz0_eq] at hz_mem'
            simp only [Finset.mem_singleton] at hz_mem'
            exact hz_ne hz_mem'
          -- From a(z) ≠ k and eigenval_ordered, we get E_{a(z)} ≠ E_k
          have heigenval_ne : es.eigenvalues (es.assignment z) ≠ es.eigenvalues k := by
            intro heq_eigenval
            have hord := es.eigenval_ordered
            -- If a(z) < k then E_{a(z)} < E_k (contradiction)
            -- If a(z) > k then E_{a(z)} > E_k (contradiction)
            rcases Nat.lt_trichotomy (es.assignment z).val k.val with hlt | heqv | hgt
            · have hstrictlt := hord ⟨(es.assignment z).val, (es.assignment z).isLt⟩
                                    ⟨k.val, k.isLt⟩ hlt
              simp only [Fin.mk_eq_mk] at hstrictlt
              linarith
            · -- a(z) = k (as Nat), so a(z) = k (as Fin), contradiction with hassign_ne
              exact hassign_ne (Fin.ext heqv)
            · have hstrictgt := hord ⟨k.val, k.isLt⟩
                                    ⟨(es.assignment z).val, (es.assignment z).isLt⟩ hgt
              simp only [Fin.mk_eq_mk] at hstrictgt
              linarith
          -- Now use s > 0 and E_{a(z)} ≠ E_k to conclude v z = 0
          have hs_ne : (s : ℂ) ≠ 0 := by
            simp only [ne_eq, Complex.ofReal_eq_zero]
            linarith [hs.1]
          have hdiff_ne : (es.eigenvalues (es.assignment z) : ℂ) - (es.eigenvalues k : ℂ) ≠ 0 := by
            simp only [ne_eq, sub_eq_zero, Complex.ofReal_inj]
            exact heigenval_ne
          have hprod_ne : (s : ℂ) * ((es.eigenvalues (es.assignment z) : ℂ) -
                          (es.eigenvalues k : ℂ)) ≠ 0 := mul_ne_zero hs_ne hdiff_ne
          exact (mul_eq_zero.mp hdiff).resolve_left hprod_ne

        -- Step 3: From ⟨ψ₀|v⟩ = 0 and v z = 0 for z ≠ z0, show v z0 = 0
        -- ⟨ψ₀|v⟩ = (1/√N) * Σ_z (v z) = 0
        -- With v z = 0 for z ≠ z0: (1/√N) * (v z0) = 0, so v z0 = 0
        have hv_z0_zero : v z0 = 0 := by
          -- ⟨ψ₀|v⟩ = Σ_z conj(ψ₀ z) * (v z) = (1/√N) * Σ_z (v z)
          have hinner_expand : psi0_v = (1 / (Real.sqrt (qubitDim n) : ℂ)) *
              Finset.sum Finset.univ (fun z' => v z') := by
            simp only [psi0_v, innerProd, equalSuperpositionN, equalSuperposition]
            have hconj : conj ((1 : ℂ) / (Real.sqrt (qubitDim n) : ℂ)) =
                         (1 : ℂ) / (Real.sqrt (qubitDim n) : ℂ) := by
              simp only [conj_eq_star, Complex.star_def, map_div₀, map_one, Complex.conj_ofReal]
            simp_rw [hconj]
            rw [← Finset.mul_sum]
          rw [hinner_expand] at hpsi0_v_zero
          have hsqrtN_ne : (1 : ℂ) / (Real.sqrt (qubitDim n) : ℂ) ≠ 0 := by
            simp only [ne_eq, div_eq_zero_iff, one_ne_zero, Complex.ofReal_eq_zero,
                       Real.sqrt_eq_zero', not_le, false_or]
            exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne (qubitDim n)))
          have hsum_zero : Finset.sum Finset.univ (fun z' => v z') = 0 :=
            (mul_eq_zero.mp hpsi0_v_zero).resolve_left hsqrtN_ne
          -- Split sum: v z0 + Σ_{z' ≠ z0} (v z') = 0
          rw [Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ z0)] at hsum_zero
          have hrest_zero : Finset.sum (Finset.univ \ {z0}) (fun z' => v z') = 0 := by
            apply Finset.sum_eq_zero
            intro z' hz'
            simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and] at hz'
            exact hv_zero_off_z0 z' hz'
          rw [hrest_zero, add_zero] at hsum_zero
          exact hsum_zero

        -- Step 4: Conclude v = 0, contradicting hv_ne
        have hv_zero : v = 0 := by
          funext z'
          by_cases hz' : z' = z0
          · rw [hz']; exact hv_z0_zero
          · exact hv_zero_off_z0 z' hz'
        exact hv_ne hv_zero

      -- Now we have hdeg_gt1 : es.degeneracies k > 1
      left
      -- Find a state z with assignment z = k
      have hcard := es.deg_count k
      have hdeg := es.deg_positive k
      have hne : (Finset.filter (fun z => es.assignment z = k) Finset.univ).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro hempty
        have : (Finset.filter (fun z => es.assignment z = k) Finset.univ).card = 0 := by
          rw [hempty]; exact Finset.card_empty
        rw [← hcard] at this
        omega
      obtain ⟨z, hz⟩ := hne
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
      exact ⟨z, by rw [hz, hk], by rw [hz]; exact hdeg_gt1⟩
    · -- Case 2: λ ≠ s·E_k for all k → secular equation must hold
      right
      push_neg at hcase
      -- Since λ is eigenvalue and λ ≠ s·E_k for all k,
      -- by det_adiabaticHam_factored: det(A) ≠ 0 and det = det(A)·(1 + (1-s)·expectation) = 0
      -- So 1 + (1-s)·expectation = 0, giving expectation = -1/(1-s)
      -- By resolvent_expectation_formula, this yields the secular equation

      -- Step 1: Get hypothesis that λ ≠ s·E_k for all states z (via assignment)
      have hne_states : ∀ z : Fin (qubitDim n), lambda ≠ s * es.eigenvalues (es.assignment z) := by
        intro z
        exact hcase (es.assignment z)

      -- Step 2: IsEigenvalue implies det = 0
      -- First get the det factorization
      have hs' : 0 ≤ s ∧ s < 1 := ⟨le_of_lt hs.1, hs.2⟩
      have hdet_factor := det_adiabaticHam_factored es hM s hs' lambda hcase

      -- Step 3: det(A) is nonzero (IsUnit)
      have hA_unit : IsUnit (((lambda : Complex) • (1 : Matrix (Fin (qubitDim n)) (Fin (qubitDim n)) ℂ) -
            (s : Complex) • es.toHamiltonian.toOperator).det) :=
        diag_resolvent_invertible es hM s lambda hcase

      -- Step 4: Use IsEigenvalue to get det = 0
      -- IsEigenvalue means there exists eigenvector, which implies det(λI - H(s)) = 0
      unfold IsEigenvalue at heigen
      have hdet_zero : ((lambda : Complex) • 1 - adiabaticHam es s ⟨le_of_lt hs.1, le_of_lt hs.2⟩).det = 0 := by
        -- From heigen: ∃ v with normSquared v > 0, H(s) ⬝ v = λ • v
        -- This means (λI - H(s)) *ᵥ v = 0, so (λI - H(s)) is singular
        obtain ⟨v, hv_pos, hv_eq⟩ := heigen
        rw [← Matrix.exists_mulVec_eq_zero_iff]
        -- Convert normSquared v > 0 to v ≠ 0
        have hv_ne : v ≠ 0 := normSquared_pos_imp_ne_zero v hv_pos
        use v, hv_ne
        -- Need: (λI - H(s)) *ᵥ v = 0 given H(s) ⬝ v = λ • v
        -- First convert applyOp to mulVec in hv_eq
        rw [applyOp_eq_mulVec] at hv_eq
        simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
        rw [hv_eq]
        simp

      -- Step 5: From det = det(A)·(1 + (1-s)⟨ψ₀|A⁻¹|ψ₀⟩) = 0 and det(A) ≠ 0
      -- we get 1 + (1-s)⟨ψ₀|A⁻¹|ψ₀⟩ = 0
      rw [hdet_factor] at hdet_zero
      have hfactor_zero : 1 + (1 - s : Complex) * innerProd (equalSuperpositionN n)
          (((lambda : Complex) • 1 - (s : Complex) • es.toHamiltonian.toOperator)⁻¹ ⬝ equalSuperpositionN n) = 0 := by
        have hne : (((lambda : Complex) • 1 - (s : Complex) • es.toHamiltonian.toOperator).det) ≠ 0 :=
          hA_unit.ne_zero
        -- det(A) * factor = 0 and det(A) ≠ 0 implies factor = 0
        exact (mul_eq_zero.mp hdet_zero).resolve_left hne

      -- Step 6: Get the resolvent expectation formula
      have hresolv := resolvent_expectation_formula es hM s lambda hcase

      -- Step 7: Convert to the secular equation
      -- From hfactor_zero: 1 + (1-s)⟨ψ₀|A⁻¹|ψ₀⟩ = 0
      -- So ⟨ψ₀|A⁻¹|ψ₀⟩ = -1/(1-s)
      -- By hresolv: ⟨ψ₀|A⁻¹|ψ₀⟩ = (1/N)Σ_k d_k/(λ - s·E_k)
      -- So (1/N)Σ_k d_k/(λ - s·E_k) = -1/(1-s)
      -- Negating denominators: (1/N)Σ_k d_k/(s·E_k - λ) = 1/(1-s)

      -- Extract expectation value from factor equation
      have hexp : innerProd (equalSuperpositionN n)
          (((lambda : Complex) • 1 - (s : Complex) • es.toHamiltonian.toOperator)⁻¹ ⬝ equalSuperpositionN n) =
          -1 / (1 - s : Complex) := by
        have h1ms_ne_real : (1 : ℝ) - s ≠ 0 := by linarith [hs.2]
        have h1ms_ne : (1 - s : Complex) ≠ 0 := by
          simp only [ne_eq, sub_eq_zero]
          intro heq
          have h_re : (1 : ℂ).re = (s : ℂ).re := by rw [heq]
          simp only [Complex.one_re, Complex.ofReal_re] at h_re
          linarith [hs.2]
        -- From 1 + (1-s)*exp = 0, we get exp = -1/(1-s)
        -- The equation is: 1 + (1-s)*exp = 0, so (1-s)*exp = -1
        have hmul : (1 - s : Complex) * innerProd (equalSuperpositionN n)
            (((lambda : Complex) • 1 - (s : Complex) • es.toHamiltonian.toOperator)⁻¹ ⬝ equalSuperpositionN n) = -1 := by
          have h := hfactor_zero
          -- From 1 + x = 0, we get x = -1
          have heq : (1 - (s : ℂ)) * innerProd (equalSuperpositionN n)
              (((lambda : Complex) • 1 - (s : Complex) • es.toHamiltonian.toOperator)⁻¹ ⬝ equalSuperpositionN n) =
              -1 := by
            -- 1 + y = 0 implies y = -1
            have h3 := add_eq_zero_iff_eq_neg.mp h
            -- h3 : 1 = -((1 - ↑s) * ...)
            -- Need: (1 - ↑s) * ... = -1
            -- From 1 = -x, we get x = -1 by neg_eq_iff_eq_neg
            exact neg_eq_iff_eq_neg.mp h3.symm
          exact heq
        -- From (1-s)*exp = -1 and (1-s) ≠ 0, we get exp = -1/(1-s)
        -- Use eq_div_iff: a = b/c ↔ c*a = b (when c ≠ 0)
        have hdiv : innerProd (equalSuperpositionN n)
            (((lambda : Complex) • 1 - (s : Complex) • es.toHamiltonian.toOperator)⁻¹ ⬝ equalSuperpositionN n) =
            -1 / (1 - s : Complex) := by
          rw [eq_div_iff h1ms_ne]
          rw [mul_comm]
          exact hmul
        exact hdiv

      -- Combine with resolvent formula
      rw [hresolv] at hexp
      -- hexp : (1/N) * Σ_k d_k/(λ - s·E_k) = -1/(1-s)

      -- Convert Complex equation to Real equation
      -- The sums are over Real values, so we can extract real parts
      have h1ms_pos : (1 : ℝ) - s > 0 := by linarith [hs.2]
      have h1ms_ne : (1 : ℝ) - s ≠ 0 := ne_of_gt h1ms_pos

      -- The key is to show the Real equation from the Complex one
      -- Note: λ - s·E_k has opposite sign to s·E_k - λ
      -- So (1/N)Σ d_k/(λ - s·E_k) = -(1/N)Σ d_k/(s·E_k - λ)

      -- First, relate sums with opposite denominators
      have hsum_neg : ∀ (f : Fin M → ℝ) (g : Fin M → ℝ),
          (∀ k, g k ≠ 0) → (∀ k, f k / g k = -(f k / (-g k))) := by
        intros f g hg k
        have hgk : g k ≠ 0 := hg k
        have hneg : -g k ≠ 0 := neg_ne_zero.mpr hgk
        field_simp

      -- The Complex sum equals the Real sum (with appropriate casting)
      -- This requires showing that all the imaginary parts are zero
      haveI : NeZero (qubitDim n) := qubitDim_neZero n

      -- From the Complex equality, extract Real equality
      -- Both sides are real numbers (cast to Complex)
      have hN_ne_zero : (qubitDim n : ℝ) ≠ 0 := by
        simp only [ne_eq, Nat.cast_eq_zero]
        exact NeZero.ne (qubitDim n)

      -- Convert the complex equation back to reals
      -- Key insight: all terms are real, so complex equation = real equation
      -- Technical: Convert Complex equation to Real equation
      -- The Complex equation hexp says (1/N)Σ d_k/(λ - s·E_k) = -1/(1-s) in Complex
      -- Since all terms are real numbers (cast to Complex), the Real equation follows
      have hreal_eq : (1 : ℝ) / (qubitDim n) *
          Finset.sum Finset.univ (fun k => (es.degeneracies k : ℝ) / (lambda - s * es.eigenvalues k)) =
          -(1 : ℝ) / (1 - s) := by
        -- Use Complex.ofReal.injective: if (x : ℂ) = (y : ℂ) then x = y for x, y : ℝ
        apply Complex.ofReal_injective
        -- Convert Real to Complex form and use hexp
        push_cast
        exact hexp

      -- Now negate denominators to get the desired form
      -- (1/N)Σ d_k/(λ - s·E_k) = -(1/N)Σ d_k/(s·E_k - λ)
      have hneg_denom : Finset.sum Finset.univ (fun k => (es.degeneracies k : ℝ) / (lambda - s * es.eigenvalues k)) =
          -Finset.sum Finset.univ (fun k => (es.degeneracies k : ℝ) / (s * es.eigenvalues k - lambda)) := by
        rw [← Finset.sum_neg_distrib]
        congr 1
        ext k
        have hdenom_ne : lambda - s * es.eigenvalues k ≠ 0 := by
          intro h
          have : lambda = s * es.eigenvalues k := by linarith
          exact hcase k this
        have hdenom_neg : s * es.eigenvalues k - lambda = -(lambda - s * es.eigenvalues k) := by ring
        rw [hdenom_neg, div_neg, neg_neg]

      -- Combine: (1/N)Σ d_k/(λ - s·E_k) = -1/(1-s)
      --       => -(1/N)Σ d_k/(s·E_k - λ) = -1/(1-s)
      --       => (1/N)Σ d_k/(s·E_k - λ) = 1/(1-s)
      rw [hneg_denom] at hreal_eq
      -- hreal_eq : (1/N) * (- Σ d_k/(s·E_k - λ)) = -1/(1-s)
      -- Multiply both sides by -1: (1/N) * Σ d_k/(s·E_k - λ) = 1/(1-s)
      have hfinal : (1 : ℝ) / (qubitDim n) *
          Finset.sum Finset.univ (fun k => (es.degeneracies k : ℝ) / (s * es.eigenvalues k - lambda)) =
          (1 : ℝ) / (1 - s) := by
        have hmul_neg : (1 : ℝ) / (qubitDim n) * -Finset.sum Finset.univ
            (fun k => (es.degeneracies k : ℝ) / (s * es.eigenvalues k - lambda)) =
            -(1 : ℝ) / (1 - s) := hreal_eq
        -- From a * (-b) = -c, we get a * b = c
        -- Rewrite as: a * (-b) = -(a * b), so -(a*b) = -c, hence a*b = c
        rw [mul_neg] at hmul_neg
        -- hmul_neg : -(1/N * sum) = -1/(1-s)
        -- Negate both sides
        have h := neg_eq_iff_eq_neg.mp hmul_neg
        -- h : 1/N * sum = -(-1/(1-s))
        simp only [neg_neg, neg_div] at h
        exact h

      exact ⟨hcase, hfinal.symm⟩

  · -- Backward direction: condition → eigenvalue
    intro hcond
    cases hcond with
    | inl hexists =>
      -- λ = s·E_k for some degenerate level k (d_k > 1)
      -- Construct an eigenvector orthogonal to |ψ₀⟩
      obtain ⟨z0, hz0_eq, hdeg⟩ := hexists
      let k := es.assignment z0

      -- We have d_k > 1, so find two distinct states with assignment k
      have hcard := es.deg_count k
      have hdeg_k : es.degeneracies k > 1 := hdeg
      have hge2 : (Finset.filter (fun z => es.assignment z = k) Finset.univ).card ≥ 2 := by
        rw [← hcard]; omega
      -- Extract two distinct states
      have hex2 : ∃ z1 z2 : Fin (qubitDim n), z1 ≠ z2 ∧
          es.assignment z1 = k ∧ es.assignment z2 = k := by
        -- Finset.one_lt_card_iff gives existence of two distinct elements
        have hne := Finset.one_lt_card_iff.mp hge2
        obtain ⟨a, b, ha, hb, hab⟩ := hne
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
        exact ⟨a, b, hab, ha, hb⟩
      obtain ⟨z1, z2, hneq, ha1, ha2⟩ := hex2

      -- Construct eigenvector v = e_{z1} - e_{z2}
      -- This is orthogonal to |ψ₀⟩ (equal superposition)
      let v : Ket (qubitDim n) := fun i =>
        if i = z1 then 1 else if i = z2 then -1 else 0

      -- Show v is an eigenvector of H(s) with eigenvalue λ
      unfold IsEigenvalue
      use v
      constructor
      · -- v ≠ 0 (normSquared v > 0)
        have hv_ne : v ≠ 0 := by
          intro hcontra
          have h1 : v z1 = 0 := by rw [hcontra]; rfl
          simp only [v] at h1
          simp at h1
        exact ne_zero_imp_normSquared_pos v hv_ne
      · -- H(s) ⬝ v = λ • v
        -- H(s) = -(1-s)|ψ₀⟩⟨ψ₀| + s·H_z
        -- ⟨ψ₀|v⟩ = (1/√N)(1 + (-1) + 0 + ... + 0) = 0 (since v = e_{z1} - e_{z2})
        -- So |ψ₀⟩⟨ψ₀|v⟩ = 0
        -- H_z v = E_k(e_{z1} - e_{z2}) = E_k v (since a(z1) = a(z2) = k)
        -- H(s) v = 0 + s·E_k v = λ v

          -- Step 1: Compute ⟨ψ₀|v⟩ = 0
          have hinner_zero : innerProd (equalSuperpositionN n) v = 0 := by
            simp only [innerProd, equalSuperpositionN, equalSuperposition, v]
            -- Sum of conj(1/√N) * (if i = z1 then 1 else if i = z2 then -1 else 0)
            -- = (1/√N) * (1 + (-1)) = 0
            haveI : NeZero (qubitDim n) := qubitDim_neZero n
            have hsqrt_real : conj ((1 : ℂ) / (Real.sqrt (qubitDim n) : ℂ)) =
                (1 : ℂ) / (Real.sqrt (qubitDim n) : ℂ) := by
              simp only [conj_eq_star, Complex.star_def, map_div₀, map_one, Complex.conj_ofReal]
            simp_rw [hsqrt_real]
            -- Sum = (1/√N) * Σ_i (if i = z1 then 1 else if i = z2 then -1 else 0)
            rw [← Finset.mul_sum]
            -- The inner sum is just 1 + (-1) = 0
            have hsum : Finset.sum Finset.univ (fun i =>
                if i = z1 then (1 : ℂ) else if i = z2 then -1 else 0) = 0 := by
              rw [Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ z1)]
              simp only [if_true]
              rw [Finset.sum_eq_add_sum_diff_singleton
                  (Finset.mem_sdiff.mpr ⟨Finset.mem_univ z2, by simp [hneq.symm]⟩)]
              simp only [if_false, if_true, hneq.symm]
              have hrest : Finset.sum ((Finset.univ \ {z1}) \ {z2})
                  (fun i => if i = z1 then (1 : ℂ) else if i = z2 then -1 else 0) = 0 := by
                apply Finset.sum_eq_zero
                intro i hi
                simp only [Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_univ, true_and] at hi
                simp [hi.1, hi.2]
              rw [hrest]
              ring
            rw [hsum, mul_zero]

          -- Step 2: |ψ₀⟩⟨ψ₀|v⟩ = 0
          have hproj_zero : applyOp (projectorOnState (equalSuperpositionN n)) v = 0 := by
            unfold projectorOnState
            rw [applyOp_outerProd, hinner_zero, zero_smul]

          -- Step 3: H_z v = E_k * v
          have hHz_v : applyOp (es.toHamiltonian.toOperator) v =
              (es.eigenvalues k : ℂ) • v := by
            rw [applyOp_diagonalHam]
            ext i
            simp only [v, Pi.smul_apply, smul_eq_mul, EigenStructure.toHamiltonian]
            by_cases hi1 : i = z1
            · simp only [hi1, if_true, mul_one]
              -- assignment z1 = k
              rw [ha1]
            · by_cases hi2 : i = z2
              · simp only [hi2, if_true]
                -- assignment z2 = k
                rw [ha2]
              · simp only [hi1, hi2, if_false, mul_zero]

          -- Step 4: H(s) v = s·E_k·v = λ·v
          -- H(s) = -(1-s)|ψ₀⟩⟨ψ₀| + s·H_z
          -- |ψ₀⟩⟨ψ₀| ⬝ v = ⟨ψ₀|v⟩ · |ψ₀⟩ = 0 (by hinner_zero)
          -- So H(s) ⬝ v = s·(H_z ⬝ v) = s·E_k·v = λ·v
          have hs_bound : 0 ≤ s ∧ s ≤ 1 := ⟨le_of_lt hs.1, le_of_lt hs.2⟩
          rw [adiabaticHam_eq es s hs_bound]
          rw [UAQO.applyOp_add, UAQO.applyOp_smul, UAQO.applyOp_smul]
          rw [hproj_zero, smul_zero, add_zero]
          rw [hHz_v]
          -- Now: s • (E_k • v) = λ • v
          -- Since λ = s * E_k, we have s • (E_k • v) = (s * E_k) • v = λ • v
          rw [smul_smul]
          congr 1
          -- Goal: ↑s * ↑(es.eigenvalues k) = ↑lambda
          -- Note: k = es.assignment z0 by definition
          rw [hz0_eq]
          simp only [Complex.ofReal_mul, k]

    | inr hsecular =>
      -- The secular equation 1/(1-s) = (1/N)Σ_k d_k/(s·E_k - λ) holds
      -- AND we have the non-collision condition: λ ≠ s·E_k for all k
      -- This ensures the secular equation is well-defined (no division by zero)
      obtain ⟨hno_collision, hsec_eq⟩ := hsecular
      have hne : ∀ k : Fin M, lambda ≠ s * es.eigenvalues k := hno_collision

      -- Step 2: Use the framework from forward direction (reverse the argument)
      -- With hne, we can use det_adiabaticHam_factored and resolvent_expectation_formula
      haveI : NeZero (qubitDim n) := qubitDim_neZero n

      -- The secular equation in the form we need
      have h1ms_pos : (1 : ℝ) - s > 0 := by linarith [hs.2]
      have h1ms_ne : (1 : ℝ) - s ≠ 0 := ne_of_gt h1ms_pos

      -- Convert secular equation to the resolvent expectation formula
      -- hsecular : 1/(1-s) = (1/N) * Σ d_k/(s·E_k - λ)
      -- We need: (1/N) * Σ d_k/(λ - s·E_k) = -1/(1-s)
      have hexp_real : (1 : ℝ) / (qubitDim n) *
          Finset.sum Finset.univ (fun k => (es.degeneracies k : ℝ) / (lambda - s * es.eigenvalues k)) =
          -(1 : ℝ) / (1 - s) := by
        -- Negate denominators in hsecular
        -- d_k/(s*E_k - λ) = -d_k/(λ - s*E_k)
        have hneg : Finset.sum Finset.univ (fun k => (es.degeneracies k : ℝ) / (s * es.eigenvalues k - lambda)) =
            -Finset.sum Finset.univ (fun k => (es.degeneracies k : ℝ) / (lambda - s * es.eigenvalues k)) := by
          rw [← Finset.sum_neg_distrib]
          congr 1
          ext k
          have hdenom_ne : s * es.eigenvalues k - lambda ≠ 0 := by
            intro h
            have : lambda = s * es.eigenvalues k := by linarith
            exact hne k this
          have hdenom_ne' : lambda - s * es.eigenvalues k ≠ 0 := by
            intro h
            have : lambda = s * es.eigenvalues k := by linarith
            exact hne k this
          -- d_k / (s*E_k - λ) = d_k / (-(λ - s*E_k)) = -d_k / (λ - s*E_k)
          rw [show s * es.eigenvalues k - lambda = -(lambda - s * es.eigenvalues k) by ring]
          rw [div_neg_eq_neg_div]
        rw [hneg] at hsec_eq
        -- hsec_eq : 1/(1-s) = (1/N) * (- Σ d_k/(λ - s·E_k))
        -- So: (1/N) * Σ d_k/(λ - s·E_k) = -1/(1-s)
        rw [mul_neg] at hsec_eq
        -- hsec_eq : 1/(1-s) = -(1/N * sum)
        -- From 1/(1-s) = -(sum'), we get sum' = -1/(1-s)
        -- Rewrite: -(sum') = 1/(1-s) implies sum' = -(1/(1-s)) = -1/(1-s)
        have h : (1 : ℝ) / (qubitDim n) *
            Finset.sum Finset.univ (fun k => (es.degeneracies k : ℝ) / (lambda - s * es.eigenvalues k)) =
            -(1 : ℝ) / (1 - s) := by
          have h1 : -(1 / (qubitDim n : ℝ) * Finset.sum Finset.univ
              (fun k => (es.degeneracies k : ℝ) / (lambda - s * es.eigenvalues k))) = 1 / (1 - s) :=
            hsec_eq.symm
          -- From -x = y, we get x = -y = -(y) = -1/(1-s)
          have h2 := neg_eq_iff_eq_neg.mp h1
          -- h2 : sum' = -(1/(1-s))
          -- -(1/(1-s)) = -1/(1-s) by neg_one_div
          have heq : -(1 : ℝ) / (1 - s) = -((1 : ℝ) / (1 - s)) := by ring
          rw [heq]
          exact h2
        exact h

      -- Step 3: Convert to Complex and use the determinant factorization
      -- This is the reverse of the forward direction: from the secular equation,
      -- derive that det(λI - H(s)) = 0
      --
      -- The key is: det(λI - H(s)) = det(A) * (1 + (1-s)*⟨ψ₀|A⁻¹|ψ₀⟩)
      -- With the secular equation, the factor (1 + (1-s)*⟨ψ₀|A⁻¹|ψ₀⟩) = 0
      -- So det(λI - H(s)) = 0, making λ an eigenvalue

      -- Use det_adiabaticHam_factored
      have hs' : 0 ≤ s ∧ s < 1 := ⟨le_of_lt hs.1, hs.2⟩
      have hdet_factor := det_adiabaticHam_factored es hM s hs' lambda hne

      -- Use resolvent_expectation_formula to relate expectation to sum
      have hresolv := resolvent_expectation_formula es hM s lambda hne

      -- Show the factor equals zero
      have hfactor_zero : 1 + (1 - s : Complex) * innerProd (equalSuperpositionN n)
          (((lambda : Complex) • 1 - (s : Complex) • es.toHamiltonian.toOperator)⁻¹ ⬝ equalSuperpositionN n) = 0 := by
        -- By hresolv: expectation = (1/N) * Σ d_k/(λ - s·E_k) (in Complex)
        -- By hexp_real: (1/N) * Σ d_k/(λ - s·E_k) = -1/(1-s) (in Real)
        -- So: expectation = -1/(1-s) (in Complex)
        -- Then: 1 + (1-s) * (-1/(1-s)) = 1 - 1 = 0
        rw [hresolv]
        -- Now need to show: 1 + (1-s) * (1/N) * Σ d_k/(λ - s·E_k) = 0 in Complex
        -- Convert hexp_real to Complex form
        have hexp_complex : (1 / qubitDim n : Complex) * Finset.sum Finset.univ (fun k : Fin M =>
            (es.degeneracies k : Complex) / ((lambda : Complex) - s * es.eigenvalues k)) =
            -1 / (1 - s : Complex) := by
          -- Use same approach as hreal_eq proof: push_cast and use hexp_real
          have h := hexp_real
          apply_fun Complex.ofReal at h
          push_cast at h
          -- After push_cast, h should match our goal exactly
          exact h
        rw [hexp_complex]
        -- Now: 1 + (1-s) * (-1/(1-s)) = 0
        have h1ms_ne' : (1 - s : Complex) ≠ 0 := by
          simp only [ne_eq, sub_eq_zero]
          intro heq
          have h_re : (1 : ℂ).re = (s : ℂ).re := by rw [heq]
          simp only [Complex.one_re, Complex.ofReal_re] at h_re
          linarith [hs.2]
        field_simp
        ring

      -- Now det(λI - H(s)) = det(A) * 0 = 0
      have hdet_zero : ((lambda : Complex) • 1 - adiabaticHam es s ⟨le_of_lt hs.1, le_of_lt hs.2⟩).det = 0 := by
        rw [hdet_factor]
        rw [hfactor_zero]
        ring

      -- From det = 0, construct an eigenvector
      rw [← Matrix.exists_mulVec_eq_zero_iff] at hdet_zero
      obtain ⟨v, hv_ne, hv_eq⟩ := hdet_zero
      -- v is an eigenvector of H(s) with eigenvalue λ
      unfold IsEigenvalue
      use v
      constructor
      · exact ne_zero_imp_normSquared_pos v hv_ne
      · -- From (λI - H(s)) *ᵥ v = 0, we get H(s) ⬝ v = λ • v
        rw [applyOp_eq_mulVec]
        simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at hv_eq
        -- hv_eq : λ • v - H(s) *ᵥ v = 0, so H(s) *ᵥ v = λ • v
        have h := sub_eq_zero.mp hv_eq
        exact h.symm

end UAQO.Proofs.Spectral
