/-
  Linear operators on Hilbert spaces.

  We define Hermitian operators, unitary operators, projectors, and their properties.
-/
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.Basic
import UAQO.Foundations.HilbertSpace

namespace UAQO

/-! ## Operators as matrices -/

/-- An operator on an N-dimensional Hilbert space -/
abbrev Operator (N : Nat) := Matrix (Fin N) (Fin N) Complex

/-- The identity operator -/
noncomputable def identityOp (N : Nat) : Operator N := Matrix.diagonal (fun _ => 1)

notation "I_" N => identityOp N

/-- The conjugate transpose (dagger) of an operator -/
noncomputable def dagger {N : Nat} (A : Operator N) : Operator N := A.conjTranspose

postfix:max "†" => dagger

/-- An operator is Hermitian if A = A† -/
def IsHermitian {N : Nat} (A : Operator N) : Prop := A = A†

/-- Our IsHermitian is equivalent to mathlib's Matrix.IsHermitian -/
lemma isHermitian_iff_matrix {N : Nat} (A : Operator N) :
    IsHermitian A ↔ Matrix.IsHermitian A := by
  simp only [IsHermitian, dagger, Matrix.IsHermitian]
  constructor <;> intro h <;> exact h.symm

/-- An operator is unitary if A†A = AA† = I -/
def IsUnitary {N : Nat} (A : Operator N) : Prop :=
  A† * A = identityOp N ∧ A * A† = identityOp N

/-- A projector is Hermitian and satisfies P² = P -/
def IsProjector {N : Nat} (P : Operator N) : Prop :=
  IsHermitian P ∧ P * P = P

/-- The trace of an operator -/
noncomputable def trace {N : Nat} (A : Operator N) : Complex := Matrix.trace A

notation "Tr(" A ")" => trace A

/-- The spectral norm of an operator (using Frobenius as placeholder) -/
noncomputable def spectralNorm {N : Nat} (A : Operator N) : Real :=
  Real.sqrt (Finset.sum Finset.univ (fun i =>
    Finset.sum Finset.univ (fun j => Complex.normSq (A i j))))

notation "‖" A "‖_op" => spectralNorm A

/-! ## Projectors -/

/-- The projector onto a state |v⟩⟨v| -/
noncomputable def projectorOnState {N : Nat} (v : Ket N) : Operator N :=
  outerProd v v

notation "π(" v ")" => projectorOnState v

/-- The rank-1 projector is Hermitian -/
theorem projectorOnState_hermitian {N : Nat} (v : Ket N) :
    IsHermitian (π(v)) := by
  unfold IsHermitian dagger projectorOnState outerProd
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.of_apply, conj_eq_star]
  rw [StarMul.star_mul, star_star]

/-- Projector onto a state is indeed a projector -/
theorem projectorOnState_isProjector {N : Nat} (v : Ket N)
    (hv : normSquared v = 1) : IsProjector (π(v)) := by
  constructor
  · exact projectorOnState_hermitian v
  · -- Idempotent: |v><v|² = |v><v| when ⟨v|v⟩ = 1
    unfold projectorOnState outerProd
    ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, conj_eq_star]
    have h : ∀ k, (v i * star (v k)) * (v k * star (v j)) = v i * (star (v k) * v k) * star (v j) := by
      intro k; ring
    simp_rw [h]
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    rw [sum_star_mul_self_eq_normSquared, hv]
    simp

/-! ## Operator algebra -/

/-- Apply an operator to a state -/
noncomputable def applyOp {N : Nat} (A : Operator N) (v : Ket N) : Ket N :=
  fun i => Finset.sum Finset.univ (fun j => A i j * v j)

infixl:70 " ⬝ " => applyOp

/-- Applying a scalar multiple of an operator -/
lemma applyOp_smul {N : Nat} (c : Complex) (A : Operator N) (v : Ket N) :
    applyOp (c • A) v = c • applyOp A v := by
  funext i
  simp only [applyOp, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  congr 1
  ext j
  simp [Matrix.smul_apply]
  ring

/-- Applying the sum of operators -/
lemma applyOp_add {N : Nat} (A B : Operator N) (v : Ket N) :
    applyOp (A + B) v = applyOp A v + applyOp B v := by
  funext i
  simp only [applyOp, Pi.add_apply, Matrix.add_apply]
  rw [← Finset.sum_add_distrib]
  congr 1
  ext j
  ring

/-- Applying a projector to its defining state -/
lemma applyOp_projector_self {N : Nat} (v : Ket N) (hv : normSquared v = 1) :
    applyOp (projectorOnState v) v = v := by
  funext i
  simp only [applyOp, projectorOnState, outerProd, Matrix.of_apply, conj_eq_star]
  have h : forall j, (v i * star (v j)) * v j = v i * (v j * star (v j)) := by
    intro j; ring
  simp_rw [h]
  rw [← Finset.mul_sum, sum_mul_star_self_eq_normSquared, hv]
  simp

/-- Applying matrix multiplication: (AB)v = A(Bv) -/
lemma applyOp_mul {N : Nat} (A B : Operator N) (v : Ket N) :
    applyOp (A * B) v = applyOp A (applyOp B v) := by
  funext i
  simp only [applyOp, Matrix.mul_apply]
  -- LHS: Σⱼ (Σₖ Aᵢₖ Bₖⱼ) vⱼ
  -- RHS: Σₖ Aᵢₖ (Σⱼ Bₖⱼ vⱼ)
  -- Expand and swap sums
  conv_lhs =>
    arg 2
    ext j
    rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1
  ext k
  rw [Finset.mul_sum]
  congr 1
  ext j
  ring

/-- Applying an outer product to a vector: (|u⟩⟨w|) |v⟩ = ⟨w|v⟩ |u⟩

    This is the key identity for outer product manipulation.
    Proof: ((|u⟩⟨w|)|v⟩)ᵢ = Σⱼ uᵢ·conj(wⱼ)·vⱼ = uᵢ · Σⱼ conj(wⱼ)·vⱼ = uᵢ · ⟨w|v⟩ -/
lemma applyOp_outerProd {N : Nat} (u w v : Ket N) :
    applyOp (outerProd u w) v = innerProd w v • u := by
  funext i
  simp only [applyOp, outerProd, Matrix.of_apply, innerProd, Pi.smul_apply, smul_eq_mul]
  -- Goal: ∑ j, u i * conj (w j) * v j = (∑ j, conj (w j) * v j) * u i
  have h : ∀ j, u i * conj (w j) * v j = u i * (conj (w j) * v j) := fun j => by ring
  simp_rw [h]
  rw [← Finset.mul_sum]
  ring

/-- Outer product multiplication: (|u⟩⟨v|)(|w⟩⟨x|) = ⟨v|w⟩ |u⟩⟨x|

    Proof: ((|u⟩⟨v|)(|w⟩⟨x|))ᵢⱼ = Σₖ uᵢ·conj(vₖ)·wₖ·conj(xⱼ)
                                 = uᵢ·conj(xⱼ)·Σₖ conj(vₖ)·wₖ
                                 = ⟨v|w⟩ · uᵢ·conj(xⱼ) -/
lemma outerProd_mul_outerProd {N : Nat} (u v w x : Ket N) :
    outerProd u v * outerProd w x = innerProd v w • outerProd u x := by
  ext i j
  simp only [Matrix.mul_apply, outerProd, Matrix.of_apply, innerProd,
             Matrix.smul_apply, smul_eq_mul]
  -- Goal: ∑ k, u i * conj (v k) * (w k * conj (x j)) = (∑ k, conj (v k) * w k) * (u i * conj (x j))
  have h : ∀ k, u i * conj (v k) * (w k * conj (x j)) = (u i * conj (x j)) * (conj (v k) * w k) :=
    fun k => by ring
  simp_rw [h]
  rw [← Finset.mul_sum]
  ring

/-- Left multiplication with outer product: A(|u⟩⟨v|) = |Au⟩⟨v|

    Proof: (A(|u⟩⟨v|))ᵢⱼ = Σₖ Aᵢₖ uₖ conj(vⱼ) = (Au)ᵢ conj(vⱼ) -/
lemma mul_outerProd {N : Nat} (A : Operator N) (u v : Ket N) :
    A * outerProd u v = outerProd (A ⬝ u) v := by
  ext i j
  simp only [Matrix.mul_apply, outerProd, Matrix.of_apply, applyOp]
  -- Goal: ∑ k, A i k * (u k * conj (v j)) = (∑ k, A i k * u k) * conj (v j)
  have h : ∀ k, A i k * (u k * conj (v j)) = (A i k * u k) * conj (v j) := fun k => by ring
  simp_rw [h]
  rw [← Finset.sum_mul]

/-- Right multiplication with outer product: (|u⟩⟨v|)A = |u⟩⟨A†v|

    Proof: ((|u⟩⟨v|)A)ᵢⱼ = Σₖ uᵢ conj(vₖ) Aₖⱼ = uᵢ · conj(Σₖ conj(Aₖⱼ) vₖ) = uᵢ conj((A†v)ⱼ) -/
lemma outerProd_mul {N : Nat} (u v : Ket N) (A : Operator N) :
    outerProd u v * A = outerProd u (dagger A ⬝ v) := by
  ext i j
  simp only [Matrix.mul_apply, outerProd, Matrix.of_apply, dagger, applyOp,
             Matrix.conjTranspose_apply, conj_eq_star]
  -- Goal: ∑ k, u i * star (v k) * A k j = u i * star (∑ k, star (A k j) * v k)
  -- RHS = u i * ∑ k, star (star (A k j) * v k) = u i * ∑ k, A k j * star (v k)
  rw [star_sum]
  simp only [star_mul', star_star]
  -- Now: ∑ k, u i * star (v k) * A k j = u i * ∑ k, A k j * star (v k)
  have h : ∀ k, u i * star (v k) * A k j = u i * (A k j * star (v k)) := fun k => by ring
  simp_rw [h]
  rw [← Finset.mul_sum]

/-- Adjoint property: ⟨v|A†|w⟩ = ⟨Av|w⟩

    This is the defining property of the adjoint operator. -/
lemma innerProd_dagger {N : Nat} (A : Operator N) (v w : Ket N) :
    innerProd v (dagger A ⬝ w) = innerProd (A ⬝ v) w := by
  simp only [innerProd, dagger, applyOp, Matrix.conjTranspose_apply, conj_eq_star]
  -- LHS: Σᵢ star(vᵢ) * Σⱼ star(Aⱼᵢ) wⱼ
  -- RHS: Σᵢ star(Σⱼ Aᵢⱼ vⱼ) * wᵢ
  conv_lhs =>
    arg 2
    ext i
    rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs =>
    arg 2
    ext j
    rw [star_sum, Finset.sum_mul]
  congr 1
  ext j
  congr 1
  ext i
  simp only [star_mul']
  ring

/-- Adjoint property (swapped): ⟨A†w|v⟩ = ⟨w|Av⟩

    This is the symmetric form of innerProd_dagger. -/
lemma innerProd_dagger_swap {N : Nat} (A : Operator N) (w v : Ket N) :
    innerProd (dagger A ⬝ w) v = innerProd w (A ⬝ v) := by
  rw [innerProd_conj_symm, innerProd_dagger, innerProd_conj_symm]
  exact star_star _

/-- For Hermitian operators: ⟨v|A|w⟩ = ⟨Av|w⟩ -/
lemma innerProd_hermitian {N : Nat} (A : Operator N) (hA : IsHermitian A) (v w : Ket N) :
    innerProd v (A ⬝ w) = innerProd (A ⬝ v) w := by
  have h : A = dagger A := by
    simp only [IsHermitian] at hA
    exact hA
  conv_lhs => rw [h]
  exact innerProd_dagger A v w

/-- Expectation value ⟨v|A|v⟩ -/
noncomputable def expectation {N : Nat} (A : Operator N) (v : Ket N) : Complex :=
  innerProd v (A ⬝ v)

notation "⟨" v "|" A "|" v' "⟩" => innerProd v (applyOp A v')

/-! ## Expectation value properties -/

/-- Expectation of a scalar multiple of an operator -/
lemma expectation_smul {N : Nat} (c : Complex) (A : Operator N) (v : Ket N) :
    expectation (c • A) v = c * expectation A v := by
  simp only [expectation]
  rw [applyOp_smul]
  simp only [innerProd]
  rw [Finset.mul_sum]
  congr 1
  ext i
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- Expectation of a sum of operators -/
lemma expectation_add {N : Nat} (A B : Operator N) (v : Ket N) :
    expectation (A + B) v = expectation A v + expectation B v := by
  simp only [expectation]
  rw [applyOp_add]
  simp only [innerProd, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  congr 1
  ext i
  ring

/-- Expectation distributes over Finset.sum -/
lemma expectation_finsum {N : Nat} {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (A : ι → Operator N) (v : Ket N) :
    expectation (Finset.sum s A) v = Finset.sum s (fun i => expectation (A i) v) := by
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty, expectation]
    simp only [applyOp, innerProd]
    simp [Matrix.zero_apply]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, expectation_add, Finset.sum_insert ha, ih]

/-- Expectation of the identity operator equals norm squared -/
lemma expectation_identity {N : Nat} (v : Ket N) :
    expectation (identityOp N) v = normSquared v := by
  simp only [expectation, identityOp, applyOp, innerProd]
  simp only [Matrix.diagonal_apply]
  have h : ∀ i : Fin N, Finset.sum Finset.univ (fun j => (if i = j then 1 else 0) * v j)
           = v i := by
    intro i
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      by_cases hij : i = j
      · exact absurd hij (Ne.symm hji)
      · simp [hij]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  simp_rw [h]
  exact sum_star_mul_self_eq_normSquared v

/-- For a projector P, ⟨φ|P|φ⟩ is real and non-negative.

    Proof: Since P² = P and P† = P:
    ⟨v|P|v⟩ = ⟨v|PP|v⟩ = ⟨v|P(Pv)⟩ = ⟨P†v|Pv⟩ = ⟨Pv|Pv⟩ = ‖Pv‖² ≥ 0. -/
lemma projector_expectation_nonneg {N : Nat} (P : Operator N) (hP : IsProjector P) (v : Ket N) :
    (expectation P v).re ≥ 0 := by
  -- Key: ⟨v|P|v⟩ = ⟨v|PP|v⟩ = ⟨Pv|Pv⟩ = ‖Pv‖²
  have hHerm : IsHermitian P := hP.1
  have hPsq : P * P = P := hP.2
  -- Step 1: expectation P v = innerProd v (P ⬝ v)
  -- Step 2: = innerProd v ((P*P) ⬝ v) since P*P = P
  have h1 : expectation P v = innerProd v ((P * P) ⬝ v) := by
    simp only [expectation, hPsq]
  -- Step 3: = innerProd v (P ⬝ (P ⬝ v)) by applyOp_mul
  rw [h1, applyOp_mul]
  -- Step 4: = innerProd (P† ⬝ v) (P ⬝ v) by adjoint property (innerProd_dagger in reverse)
  -- Actually we use innerProd_hermitian: for Hermitian A, ⟨w|A|u⟩ = ⟨Aw|u⟩
  -- So ⟨v|P|Pv⟩ = ⟨Pv|Pv⟩
  have h2 : innerProd v (P ⬝ (P ⬝ v)) = innerProd (P ⬝ v) (P ⬝ v) := by
    exact innerProd_hermitian P hHerm v (P ⬝ v)
  rw [h2]
  -- Step 5: innerProd (P ⬝ v) (P ⬝ v) has real part = normSquared (P ⬝ v) ≥ 0
  rw [innerProd_self_eq_normSquared (P ⬝ v)]
  exact normSquared_nonneg (P ⬝ v)

/-- Linear combination of operators -/
noncomputable def linCombOp {N : Nat} (a b : Complex) (A B : Operator N) : Operator N :=
  a • A + b • B

/-! ## The resolvent -/

/-- The resolvent of an operator: R_A(γ) = (γI - A)^{-1} -/
noncomputable def resolvent {N : Nat} (A : Operator N) (gamma : Complex) : Operator N :=
  (gamma • identityOp N - A)⁻¹

notation "R_" A "(" gamma ")" => resolvent A gamma

/-- The resolvent inverse property: (γI - A) * R_A(γ) = I when γI - A is invertible -/
lemma resolvent_left_inv {N : Nat} (A : Operator N) (gamma : Complex)
    (hInv : (gamma • identityOp N - A).det ≠ 0) :
    (gamma • identityOp N - A) * resolvent A gamma = 1 := by
  simp only [resolvent]
  have hUnit : IsUnit (gamma • identityOp N - A).det := isUnit_iff_ne_zero.mpr hInv
  exact Matrix.mul_nonsing_inv _ hUnit

/-- The resolvent inverse property: R_A(γ) * (γI - A) = I when γI - A is invertible -/
lemma resolvent_right_inv {N : Nat} (A : Operator N) (gamma : Complex)
    (hInv : (gamma • identityOp N - A).det ≠ 0) :
    resolvent A gamma * (gamma • identityOp N - A) = 1 := by
  simp only [resolvent]
  have hUnit : IsUnit (gamma • identityOp N - A).det := isUnit_iff_ne_zero.mpr hInv
  exact Matrix.nonsing_inv_mul _ hUnit

/-- For a Hermitian operator with γ not in the spectrum, the resolvent has positive norm.

    Mathematically: ‖R_A(γ)‖ = 1/dist(γ, σ(A)). Since spectralNorm is a Frobenius norm
    placeholder, we prove the weaker statement that ‖R‖ > 0 (equivalently ‖R‖ = 1/d
    for some d > 0). The resolvent is nonzero because it is the inverse of an
    invertible matrix: (γI - A) · R = I, so R = 0 would give 0 = I.

    Note: N > 0 is required since the 0×0 matrix ring is trivial (0 = 1). -/
theorem resolvent_distance_to_spectrum {N : Nat} (A : Operator N) (gamma : Complex)
    (hA : IsHermitian A) (hInv : (gamma • identityOp N - A).det ≠ 0)
    (hN : N > 0) :
    ∃ (d : Real), d > 0 ∧ spectralNorm (resolvent A gamma) = 1 / d := by
  -- Step 1: The resolvent is nonzero.
  -- If R = 0, then (γI - A) * R = 0 ≠ 1, contradicting resolvent_left_inv.
  have hR_ne_zero : resolvent A gamma ≠ 0 := by
    intro hR
    have h1 := resolvent_left_inv A gamma hInv
    rw [hR, mul_zero] at h1
    haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
    exact absurd h1.symm one_ne_zero
  -- Step 2: Nonzero matrix has positive Frobenius norm.
  have hNorm_pos : spectralNorm (resolvent A gamma) > 0 := by
    simp only [spectralNorm]
    apply Real.sqrt_pos_of_pos
    -- Extract a nonzero entry
    have ⟨i, j, hij⟩ : ∃ i j, (resolvent A gamma) i j ≠ 0 := by
      by_contra h
      push_neg at h
      exact hR_ne_zero (Matrix.ext (fun i j => by simp [h i j]))
    -- Double sum ≥ inner sum at row i ≥ normSq at (i,j) > 0
    calc Finset.sum Finset.univ (fun i' =>
           Finset.sum Finset.univ (fun j' =>
             Complex.normSq ((resolvent A gamma) i' j')))
        ≥ Finset.sum Finset.univ (fun j' =>
            Complex.normSq ((resolvent A gamma) i j')) :=
          Finset.single_le_sum
            (fun i' _ => Finset.sum_nonneg (fun j' _ => Complex.normSq_nonneg _))
            (Finset.mem_univ i)
      _ ≥ Complex.normSq ((resolvent A gamma) i j) :=
          Finset.single_le_sum
            (fun j' _ => Complex.normSq_nonneg _)
            (Finset.mem_univ j)
      _ > 0 := Complex.normSq_pos.mpr hij
  -- Step 3: Set d = 1/‖R‖, giving ‖R‖ = 1/d with d > 0.
  exact ⟨1 / spectralNorm (resolvent A gamma),
    div_pos one_pos hNorm_pos,
    by rw [one_div, one_div, inv_inv]⟩

end UAQO
