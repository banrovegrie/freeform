/-
  Adiabatic Hamiltonian definition.

  This file contains the core definition of the adiabatic Hamiltonian
  H(s) = -(1-s)|psi0><psi0| + s*Hz

  Extracted to its own file to allow both GapBounds.lean and the
  eigenvalue condition proof to import it without circular dependencies.
-/
import UAQO.Spectral.SpectralParameters

namespace UAQO

/-! ## Adiabatic Hamiltonian -/

/-- The adiabatic Hamiltonian H(s) = -(1-s)|ψ₀⟩⟨ψ₀| + s H_z

    This interpolates between H(0) = -|ψ₀⟩⟨ψ₀| (ground state is equal superposition)
    and H(1) = H_z (diagonal Hamiltonian with computational basis eigenstates).

    The parameter s ∈ [0,1] controls the interpolation. -/
noncomputable def adiabaticHam {n M : Nat} (es : EigenStructure n M)
    (s : Real) (_hs : 0 <= s ∧ s <= 1) : NQubitOperator n :=
  let psi0 := equalSuperpositionN n
  let H0 := projectorOnState psi0
  let Hz := es.toHamiltonian.toOperator
  (-(1 - s) : Complex) • H0 + (s : Complex) • Hz

notation "H(" s ")" => adiabaticHam _ s _

end UAQO
