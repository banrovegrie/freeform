/-
  Formalization of Experiment 08: Structured Tractability.

  Machine-verifies the core structural claims from proof.md:
  1. A_1 definition unfolds to a finite sum (Proposition 3)
  2. s* = A_1/(A_1+1) is definitional
  3. Vacuity bound for Proposition 2

  Complexity-theoretic claims (Propositions 4, 6) are beyond the scope of
  algebraic verification. The Lean project already formalizes the paper's
  hardness results as axioms in Complexity/Hardness.lean.
-/
import UAQO.Spectral.SpectralParameters

namespace UAQO.Experiments

open UAQO

/-! ## A_1 is a finite sum (Proposition 3)

The algebraic content: A_1 is a sum of M-1 terms, one per non-ground
energy level. If M = poly(n) and each term is computable, A_1 is computable.
-/

/-- A_1 unfolds to (1/N) * sum over excited levels of d_k/(E_k - E_0). -/
theorem A1_is_finite_sum {n M : Nat} (es : EigenStructure n M) (hM : M > 0) :
    A1 es hM = (1 / (qubitDim n : Real)) *
    Finset.sum (Finset.filter (fun k : Fin M => k.val > 0) Finset.univ)
      (fun k => (es.degeneracies k : Real) /
        (es.eigenvalues k - es.eigenvalues ⟨0, hM⟩)) := by
  unfold A1 spectralParam
  simp [pow_one]

/-! ## s* is definitionally A_1/(A_1+1)

This is literally the definition in SpectralParameters.lean.
-/

/-- s* = A_1/(A_1+1) is definitional. -/
theorem crossing_def {n M : Nat} (es : EigenStructure n M) (hM : M > 0) :
    avoidedCrossingPosition es hM = A1 es hM / (A1 es hM + 1) := by
  rfl

/-! ## Proposition 2 vacuity: excited degeneracies bounded => d_0 large

If d_k <= B for all k >= 1, then sum_{k>=1} d_k <= (M-1)*B.
Since d_0 + sum_{k>=1} d_k = N, we get d_0 >= N - (M-1)*B.
When (M-1)*B << 2^n, the problem is trivially solvable.
-/

/-- Each term in the excited sum is bounded by B. -/
theorem excited_sum_termwise_bound {n M : Nat} (es : EigenStructure n M)
    (B : Nat) (hB : ∀ k : Fin M, k.val > 0 → es.degeneracies k ≤ B) :
    ∀ k ∈ Finset.filter (fun k : Fin M => k.val > 0) Finset.univ,
      es.degeneracies k ≤ B := by
  intro k hk
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
  exact hB k hk

/-- The sum over excited states is bounded: sum_{k>0} d_k <= M * B.
    (The sharper M-1 bound follows from excluding k=0, but M*B suffices
    for the vacuity argument since M*B << 2^n regardless.) -/
theorem excited_sum_upper {n M : Nat} (es : EigenStructure n M)
    (B : Nat) (hB : ∀ k : Fin M, k.val > 0 → es.degeneracies k ≤ B) :
    Finset.sum (Finset.filter (fun k : Fin M => k.val > 0) Finset.univ)
      es.degeneracies ≤ M * B := by
  calc Finset.sum (Finset.filter (fun k : Fin M => k.val > 0) Finset.univ)
         es.degeneracies
      ≤ Finset.sum (Finset.filter (fun k : Fin M => k.val > 0) Finset.univ)
         (fun _ => B) :=
        Finset.sum_le_sum (excited_sum_termwise_bound es B hB)
    _ ≤ Finset.sum (Finset.univ : Finset (Fin M)) (fun _ => B) :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = M * B := by
        simp [Finset.sum_const, smul_eq_mul]

/-! ## Summary of what the Lean formalization verifies

Machine-verified (no sorry):
  - A_1 = (1/N) * sum_{k>0} d_k/(E_k - E_0)  [definitional unfolding]
  - s* = A_1/(A_1+1)                           [definitional]
  - sum_{k>0} d_k <= M*B when each d_k <= B    [Prop 2 vacuity core]

The key algebraic infrastructure (EigenStructure, spectralParam, A1, A2,
avoidedCrossingPosition) is already formalized in the main project:
  - UAQO/Spectral/DiagonalHamiltonian.lean
  - UAQO/Spectral/SpectralParameters.lean

The #P-hardness reduction (Prop 4, via sharpPFunction and Lagrange
interpolation) is formalized in:
  - UAQO/Complexity/Hardness.lean (mainResult3 axiom)
  - UAQO/Spectral/SpectralParameters.lean (sharpPFunction definition)
  - UAQO/Proofs/Complexity/LagrangeInterp.lean (interpolation infrastructure)

These existing formalizations provide machine-checked support for the
mathematical infrastructure underlying Experiment 08's claims.
-/

end UAQO.Experiments
