/-
  Qubit systems and tensor product structure.

  We define n-qubit systems, the computational basis, and tensor products.
-/
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Data.Fin.Tuple.Basic
import UAQO.Foundations.SpectralTheory

namespace UAQO

/-! ## Single qubit -/

/-- The dimension of an n-qubit system -/
def qubitDim (n : Nat) : Nat := 2^n

instance qubitDim_neZero (n : Nat) : NeZero (qubitDim n) :=
  ⟨Nat.ne_of_gt (Nat.pow_pos (by norm_num : 0 < 2) n)⟩

/-- A qubit is a 2-dimensional quantum system -/
abbrev Qubit := Ket 2

/-- The |0⟩ state -/
noncomputable def ket0 : Qubit := compBasisState 2 ⟨0, by norm_num⟩

/-- The |1⟩ state -/
noncomputable def ket1 : Qubit := compBasisState 2 ⟨1, by norm_num⟩

/-- The |+⟩ state = (|0⟩ + |1⟩)/√2 -/
noncomputable def ketPlus : Qubit :=
  fun _ => 1 / Complex.ofReal (Real.sqrt 2)

/-- The |-⟩ state = (|0⟩ - |1⟩)/√2 -/
noncomputable def ketMinus : Qubit :=
  fun i => if i.val = 0 then 1 / Complex.ofReal (Real.sqrt 2)
           else -1 / Complex.ofReal (Real.sqrt 2)

/-! ## n-qubit systems -/

/-- An n-qubit state -/
abbrev NQubitState (n : Nat) := Ket (qubitDim n)

/-- An n-qubit operator -/
abbrev NQubitOperator (n : Nat) := Operator (qubitDim n)

/-- The computational basis state |z⟩ for bitstring z ∈ {0,1}ⁿ -/
noncomputable def compBasisFromBitstring (n : Nat) (z : Fin (qubitDim n)) :
    NQubitState n :=
  compBasisState (qubitDim n) z

/-- The equal superposition state |ψ₀⟩ = |+⟩^⊗n = (1/√N) Σ_z |z⟩ -/
noncomputable def equalSuperpositionN (n : Nat) : NQubitState n :=
  equalSuperposition (qubitDim n)

notation "|ψ₀^" n "⟩" => equalSuperpositionN n

/-- The initial Hamiltonian H₀ = -|ψ₀⟩⟨ψ₀| -/
noncomputable def initialHamiltonian (n : Nat) : NQubitOperator n :=
  (-1 : Complex) • projectorOnState (equalSuperpositionN n)

notation "H₀^" n => initialHamiltonian n

/-- H₀ has ground energy -1 with ground state |ψ₀⟩ -/
theorem initialHam_groundState (n : Nat) :
    applyOp (initialHamiltonian n) (equalSuperpositionN n) =
    (-1 : Complex) • equalSuperpositionN n := by
  sorry  -- Requires showing projector property

/-! ## Pauli matrices -/

/-- The Pauli X matrix -/
noncomputable def pauliX : Operator 2 :=
  !![0, 1; 1, 0]

/-- The Pauli Y matrix -/
noncomputable def pauliY : Operator 2 :=
  !![0, -Complex.I; Complex.I, 0]

/-- The Pauli Z matrix -/
noncomputable def pauliZ : Operator 2 :=
  !![1, 0; 0, -1]

notation "σₓ" => pauliX
notation "σᵧ" => pauliY
notation "σᵤ" => pauliZ

/-- Pauli Z eigenvalues -/
theorem pauliZ_eigenvalues :
    IsEigenvalue pauliZ 1 ∧ IsEigenvalue pauliZ (-1) := by
  sorry  -- Elementary matrix calculation

/-! ## Bitstring indexing utilities -/

/-- Convert a natural number to an n-bit bitstring -/
def natToBitstring (n : Nat) (k : Fin (2^n)) : Fin n -> Bool :=
  fun i => (k.val / 2^i.val) % 2 = 1

/-- Convert an n-bit bitstring to a natural number -/
def bitstringToNat (n : Nat) (bits : Fin n -> Bool) : Fin (2^n) :=
  ⟨Finset.sum Finset.univ (fun i => if bits i then 2^i.val else 0),
   by sorry⟩  -- Bounded by geometric series

end UAQO
