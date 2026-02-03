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

/-- Projector onto a state is indeed a projector -/
theorem projectorOnState_isProjector {N : Nat} (v : Ket N)
    (hv : normSquared v = 1) : IsProjector (π(v)) := by
  constructor
  · sorry  -- Hermitian: |v><v|^† = |v><v|
  · sorry  -- Idempotent: requires ⟨v|v⟩ = 1

/-- The rank-1 projector is Hermitian -/
theorem projectorOnState_hermitian {N : Nat} (v : Ket N) :
    IsHermitian (π(v)) := by
  sorry  -- Follows from (v_i * conj(v_j))^* = conj(v_i) * v_j = v_j * conj(v_i)

/-! ## Operator algebra -/

/-- Apply an operator to a state -/
noncomputable def applyOp {N : Nat} (A : Operator N) (v : Ket N) : Ket N :=
  fun i => Finset.sum Finset.univ (fun j => A i j * v j)

infixl:70 " ⬝ " => applyOp

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
