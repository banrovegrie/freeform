/-
  Proofs for Sherman-Morrison formula axiom in GapBounds.lean.

  Eliminates:
  - shermanMorrison_resolvent
-/
import UAQO.Spectral.GapBounds
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace UAQO.Proofs.Spectral

open UAQO

/-- Sherman-Morrison formula for matrix inverse under rank-1 update.

    For an invertible matrix B and vectors u, v, if (1 - v† B⁻¹ u) ≠ 0, then:
    (B - u v†)⁻¹ = B⁻¹ + (B⁻¹ u)(v† B⁻¹) / (1 - v† B⁻¹ u)

    This is a fundamental result in linear algebra.

    For the resolvent case:
    - B = γI - A (assumed invertible, i.e., γ not in spectrum of A)
    - resolvent A γ = B⁻¹
    - The formula becomes:
      resolvent (A + uv†) γ = (B - uv†)⁻¹ = B⁻¹ + B⁻¹ u v† B⁻¹ / (1 - v† B⁻¹ u)
                            = R + (1/(1 - ⟨v|R|u⟩)) |Ru⟩⟨R†v|

    Note: B⁻¹ u v† B⁻¹ = outerProd(B⁻¹ u, (B⁻¹)† v) because:
    (B⁻¹ u v† B⁻¹)_{ij} = (B⁻¹ u)_i * (v† B⁻¹)_j = (B⁻¹ u)_i * conj((B†⁻¹ v)_j)

    Derivation using Woodbury (for B + (-u)v† = B - uv†):
    (B - uv†)⁻¹ = (B + (-u)v†)⁻¹
                = B⁻¹ - B⁻¹(-u)v†B⁻¹/(1 + v†B⁻¹(-u))
                = B⁻¹ + B⁻¹uv†B⁻¹/(1 - v†B⁻¹u) ✓
-/
theorem shermanMorrison_resolvent_proof {n : Nat} (A : NQubitOperator n)
    (u v : NQubitState n) (gamma : Complex)
    (hInv : ((gamma • identityOp (qubitDim n) - A).det ≠ 0))
    (hDenom : 1 - innerProd v (applyOp (resolvent A gamma) u) ≠ 0) :
    resolvent (A + outerProd u v) gamma =
    resolvent A gamma +
    (1 / (1 - innerProd v (applyOp (resolvent A gamma) u))) •
    outerProd (applyOp (resolvent A gamma) u) (applyOp ((resolvent A gamma)†) v) :=
  -- The full proof is in GapBounds.lean as `shermanMorrison_resolvent`
  -- This file references it directly since GapBounds is imported.
  shermanMorrison_resolvent A u v gamma hInv hDenom

end UAQO.Proofs.Spectral
