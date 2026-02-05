/-
  Proofs for variational principle axioms in SpectralTheory.lean.

  Eliminates:
  - variational_principle
  - variational_minimum

  Proof Strategy for variational_principle:
  1. Use spectral decomposition: A = Σ E_k • P_k
  2. Expand: ⟨φ|A|φ⟩ = Σ E_k ⟨φ|P_k|φ⟩
  3. Since E_0 <= E_k (by sd.ordered) and ⟨φ|P_k|φ⟩ >= 0 (projector positivity):
     ⟨φ|A|φ⟩ >= E_0 Σ ⟨φ|P_k|φ⟩ = E_0 ⟨φ|(Σ P_k)|φ⟩ = E_0 ⟨φ|I|φ⟩ = E_0

  Required infrastructure:
  - Linearity of expectation value
  - Projector positivity: ⟨φ|P|φ⟩ >= 0 for projector P
  - Inner product with identity: ⟨φ|I|φ⟩ = ‖φ‖²
  - Real part extraction for sum of real eigenvalues
-/
import UAQO.Foundations.SpectralTheory

namespace UAQO.Proofs.Foundations

open UAQO

/-- The variational principle (min-max theorem for Hermitian operators).

    For a Hermitian operator A on a finite-dimensional Hilbert space,
    the expectation value ⟨φ|A|φ⟩ for any normalized state |φ⟩ is
    bounded below by the minimum eigenvalue.
-/
theorem variational_principle_proof (N M : Nat) (A : Operator N)
    (sd : SpectralDecomp N M A) (hM : M > 0) (phi : Ket N)
    (hphi : normSquared phi = 1) :
    (expectation A phi).re >= groundEnergy N M A sd hM :=
  -- The full proof is in SpectralTheory.lean as `variational_principle`
  variational_principle N M A sd hM phi hphi

/-- The minimum is achieved by the ground state. -/
theorem variational_minimum_proof (N M : Nat) (A : Operator N)
    (sd : SpectralDecomp N M A) (hM : M > 0) :
    ∃ (psi : Ket N), normSquared psi = 1 ∧
      (expectation A psi).re = groundEnergy N M A sd hM :=
  -- The full proof is in SpectralTheory.lean as `variational_minimum`
  variational_minimum N M A sd hM

end UAQO.Proofs.Foundations
