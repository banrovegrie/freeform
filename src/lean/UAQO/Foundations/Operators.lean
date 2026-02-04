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

/-- Expectation value ⟨v|A|v⟩ -/
noncomputable def expectation {N : Nat} (A : Operator N) (v : Ket N) : Complex :=
  innerProd v (A ⬝ v)

notation "⟨" v "|" A "|" v' "⟩" => innerProd v (applyOp A v')

/-- Linear combination of operators -/
noncomputable def linCombOp {N : Nat} (a b : Complex) (A B : Operator N) : Operator N :=
  a • A + b • B

/-! ## The resolvent -/

/-- The resolvent of an operator: R_A(γ) = (γI - A)^{-1} -/
noncomputable def resolvent {N : Nat} (A : Operator N) (gamma : Complex) : Operator N :=
  (gamma • identityOp N - A)⁻¹

notation "R_" A "(" gamma ")" => resolvent A gamma

/-- For a normal operator, ‖R_A(γ)‖⁻¹ gives the distance from γ to spectrum of A -/
-- This is a key fact used in the paper (Eq. 2.1)
axiom resolvent_distance_to_spectrum {N : Nat} (A : Operator N) (gamma : Complex)
    (hA : IsHermitian A) (hInv : (gamma • identityOp N - A).det ≠ 0) :
    ∃ (d : Real), d > 0 ∧ spectralNorm (resolvent A gamma) = 1 / d

end UAQO
