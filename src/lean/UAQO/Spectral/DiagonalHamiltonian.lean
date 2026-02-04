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

noncomputable instance {n : Nat} : CoeFun (DiagonalHamiltonian n) (fun _ => NQubitOperator n) :=
  ⟨DiagonalHamiltonian.toOperator⟩

/-- A diagonal Hamiltonian is Hermitian -/
theorem diagonalHam_hermitian {n : Nat} (H : DiagonalHamiltonian n) :
    IsHermitian H.toOperator := by
  unfold IsHermitian dagger DiagonalHamiltonian.toOperator
  ext i j
  simp only [Matrix.diagonal, Matrix.conjTranspose_apply, Matrix.of_apply]
  by_cases hij : i = j
  · simp only [hij, ite_true, Complex.star_def, Complex.conj_ofReal]
  · simp only [hij, Ne.symm hij, ite_false, star_zero]

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
  ground_energy_zero : (hM : M > 0) -> eigenvalues ⟨0, hM⟩ = 0
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

/-- Applying a diagonal Hamiltonian multiplies each component by its energy -/
lemma applyOp_diagonalHam {n : Nat} (H : DiagonalHamiltonian n) (v : NQubitState n) :
    applyOp H.toOperator v = fun i => (H.energy i : Complex) * v i := by
  funext i
  simp only [applyOp, DiagonalHamiltonian.toOperator]
  rw [Finset.sum_eq_single i]
  · simp only [Matrix.diagonal_apply_eq, mul_comm]
  · intro j _ hji
    simp only [Matrix.diagonal_apply_ne _ hji.symm, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

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
  simp only [normSquared, symmetricState]
  conv_lhs =>
    arg 2
    ext i
    rw [show Complex.normSq (if es.assignment i = k
                             then 1 / Complex.ofReal (Real.sqrt (es.degeneracies k)) else 0) =
        if es.assignment i = k
        then Complex.normSq (1 / Complex.ofReal (Real.sqrt (es.degeneracies k))) else 0 by
      split_ifs <;> simp [Complex.normSq_zero]]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  simp only [Finset.sum_const]
  have hcard : (Finset.filter (fun x => es.assignment x = k) Finset.univ).card =
               es.degeneracies k := by
    rw [es.deg_count k]
  rw [hcard]
  rw [Complex.normSq_div, Complex.normSq_one, Complex.normSq_ofReal]
  rw [Real.mul_self_sqrt (Nat.cast_nonneg (es.degeneracies k))]
  have hd : (es.degeneracies k : Real) > 0 := Nat.cast_pos.mpr (es.deg_positive k)
  simp only [nsmul_eq_mul]
  field_simp

/-- Applying Hz to the symmetric ground state when E₀ = 0 -/
lemma applyOp_diagonalHam_symmetricGround {n M : Nat} (es : EigenStructure n M)
    (hM : M > 0) (hE0 : es.eigenvalues ⟨0, hM⟩ = 0) :
    applyOp es.toHamiltonian.toOperator (symmetricState es ⟨0, hM⟩) = 0 := by
  rw [applyOp_diagonalHam]
  funext i
  simp only [EigenStructure.toHamiltonian, symmetricState, Pi.zero_apply]
  by_cases h : es.assignment i = ⟨0, hM⟩
  · -- In ground eigenspace: energy is E₀ = 0
    simp only [h, ↓reduceIte, hE0, Complex.ofReal_zero, zero_mul]
  · -- Not in ground eigenspace: amplitude is 0
    simp only [h, ↓reduceIte, mul_zero]

/-! ## Spectral gap -/

/-- The spectral gap Δ = E₁ - E₀ -/
noncomputable def spectralGapDiag {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2) : Real :=
  es.eigenvalues ⟨1, Nat.lt_of_lt_of_le Nat.one_lt_two hM⟩ -
  es.eigenvalues ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_two hM⟩

notation "Δ_" es => spectralGapDiag es

/-- The spectral gap is positive -/
theorem spectralGap_positive {n M : Nat} (es : EigenStructure n M) (hM : M >= 2) :
    spectralGapDiag es hM > 0 := by
  simp only [spectralGapDiag]
  have h0 : (0 : Nat) < M := Nat.lt_of_lt_of_le Nat.zero_lt_two hM
  have h1 : (1 : Nat) < M := Nat.lt_of_lt_of_le Nat.one_lt_two hM
  have h := es.eigenval_ordered ⟨0, h0⟩ ⟨1, h1⟩
  simp only [Fin.mk_lt_mk] at h
  linarith [h Nat.zero_lt_one]

end UAQO
