/-
  Diagonal Hamiltonians (problem Hamiltonians in adiabatic quantum optimization).

  We formalize Hamiltonians H_z that are diagonal in the computational basis,
  as described in the paper (Definition 1).
-/
import UAQO.Foundations.Qubit

namespace UAQO

/-! ## Diagonal Hamiltonians -/

/-- A diagonal Hamiltonian is specified by its eigenvalues at each computational basis state -/
structure DiagonalHamiltonian (n : Nat) where
  /-- The energy function E: {0,1}^n -> [0,1] -/
  energy : Fin (qubitDim n) -> Real
  /-- Energies are in [0, 1] -/
  energy_bounds : ∀ z, 0 <= energy z ∧ energy z <= 1

/-- Convert a diagonal Hamiltonian to an operator -/
noncomputable def DiagonalHamiltonian.toOperator {n : Nat}
    (H : DiagonalHamiltonian n) : NQubitOperator n :=
  Matrix.diagonal (fun z => (H.energy z : Complex))

instance {n : Nat} : CoeFun (DiagonalHamiltonian n) (fun _ => NQubitOperator n) :=
  ⟨DiagonalHamiltonian.toOperator⟩

/-- A diagonal Hamiltonian is Hermitian -/
theorem diagonalHam_hermitian {n : Nat} (H : DiagonalHamiltonian n) :
    IsHermitian H.toOperator := by
  simp [IsHermitian, dagger, DiagonalHamiltonian.toOperator]
  ext i j
  simp [Matrix.diagonal, Matrix.conjTranspose]
  split_ifs with hij
  · simp [hij, conj, Complex.ofReal_re, Complex.ofReal_im]
  · rfl

/-! ## Eigenvalue structure -/

/-- The distinct eigenvalues of a diagonal Hamiltonian -/
structure EigenStructure (n : Nat) (M : Nat) where
  /-- The M distinct eigenvalues, ordered: 0 ≤ E₀ < E₁ < ... < E_{M-1} ≤ 1 -/
  eigenvalues : Fin M -> Real
  /-- The degeneracy of each eigenvalue -/
  degeneracies : Fin M -> Nat
  /-- Which eigenvalue each basis state maps to -/
  assignment : Fin (qubitDim n) -> Fin M
  /-- Eigenvalues are in [0, 1] -/
  eigenval_bounds : ∀ k, 0 <= eigenvalues k ∧ eigenvalues k <= 1
  /-- Eigenvalues are strictly ordered -/
  eigenval_ordered : ∀ i j, i < j -> eigenvalues i < eigenvalues j
  /-- Ground energy is 0 (normalized) -/
  ground_energy_zero : M > 0 -> eigenvalues ⟨0, ‹M > 0›⟩ = 0
  /-- Degeneracies are positive -/
  deg_positive : ∀ k, degeneracies k > 0
  /-- Degeneracies sum to N -/
  deg_sum : Finset.sum Finset.univ degeneracies = qubitDim n
  /-- Degeneracy equals count of states with that eigenvalue -/
  deg_count : ∀ k, degeneracies k =
    (Finset.filter (fun z => assignment z = k) Finset.univ).card

/-- Convert an EigenStructure to a DiagonalHamiltonian -/
noncomputable def EigenStructure.toHamiltonian {n M : Nat}
    (es : EigenStructure n M) : DiagonalHamiltonian n where
  energy := fun z => es.eigenvalues (es.assignment z)
  energy_bounds := fun z => es.eigenval_bounds (es.assignment z)

/-! ## Sets of basis states with same eigenvalue -/

/-- The set Ω_k of basis states with eigenvalue E_k -/
def eigenspace {n M : Nat} (es : EigenStructure n M) (k : Fin M) :
    Finset (Fin (qubitDim n)) :=
  Finset.filter (fun z => es.assignment z = k) Finset.univ

notation "Ω_" k => eigenspace _ k

/-- The cardinality of Ω_k equals the degeneracy -/
theorem eigenspace_card {n M : Nat} (es : EigenStructure n M) (k : Fin M) :
    (eigenspace es k).card = es.degeneracies k := by
  exact (es.deg_count k).symm

/-! ## Symmetric subspace state -/

/-- The symmetric state |k⟩ = (1/√d_k) Σ_{z ∈ Ω_k} |z⟩ -/
noncomputable def symmetricState {n M : Nat} (es : EigenStructure n M) (k : Fin M) :
    NQubitState n :=
  fun i => if es.assignment i = k
           then 1 / Complex.ofReal (Real.sqrt (es.degeneracies k))
           else 0

notation "|" k "⟩_sym" => symmetricState _ k

/-- The symmetric state is normalized -/
theorem symmetricState_normalized {n M : Nat} (es : EigenStructure n M) (k : Fin M) :
    normSquared (symmetricState es k) = 1 := by
  simp [normSquared, symmetricState]
  simp only [Complex.normSq_div, Complex.normSq_one, Complex.normSq_ofReal]
  conv =>
    lhs
    arg 2
    ext i
    rw [if_ite_eq_ite_ite_of_prop (fun h => (h : True)), ite_true_true_false]
  have hcard := eigenspace_card es k
  have hpos : (es.degeneracies k : Real) > 0 := by
    have := es.deg_positive k
    exact Nat.cast_pos.mpr this
  have hsqrt : Real.sqrt (es.degeneracies k) * Real.sqrt (es.degeneracies k) =
               es.degeneracies k := Real.mul_self_sqrt (le_of_lt hpos)
  sorry -- Complete the card/sqrt calculation

/-! ## Spectral gap -/

/-- The spectral gap Δ = E₁ - E₀ -/
noncomputable def spectralGapDiag {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2) : Real :=
  es.eigenvalues ⟨1, hM⟩ - es.eigenvalues ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hM⟩

notation "Δ_" es => spectralGapDiag es

/-- The spectral gap is positive -/
theorem spectralGap_positive {n M : Nat} (es : EigenStructure n M) (hM : M >= 2) :
    spectralGapDiag es hM > 0 := by
  simp [spectralGapDiag]
  have h := es.eigenval_ordered ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hM⟩ ⟨1, hM⟩
  simp at h
  linarith [h Nat.zero_lt_one]

end UAQO
