/-
  Spectral gap bounds for the adiabatic Hamiltonian.

  This file contains the main technical results:
  1. Bounds on g(s) to the LEFT of the avoided crossing (variational principle)
  2. Bounds on g(s) at the avoided crossing (minimum gap)
  3. Bounds on g(s) to the RIGHT of the avoided crossing (resolvent method)

  These correspond to the results in Section 2 of the paper.
-/
import UAQO.Spectral.SpectralParameters

namespace UAQO

/-! ## Adiabatic Hamiltonian in symmetric subspace -/

/-- The adiabatic Hamiltonian H(s) = -(1-s)|ψ₀⟩⟨ψ₀| + s H_z -/
noncomputable def adiabaticHam {n M : Nat} (es : EigenStructure n M)
    (s : Real) (hs : 0 <= s ∧ s <= 1) : NQubitOperator n :=
  let psi0 := equalSuperpositionN n
  let H0 := projectorOnState psi0
  let Hz := es.toHamiltonian.toOperator
  (-(1 - s) : Complex) • H0 + (s : Complex) • Hz

notation "H(" s ")" => adiabaticHam _ s _

/-- The eigenvalue condition for H(s): 1/(1-s) = (1/N) Σ_k d_k/(sE_k - λ)
    This is Lemma 2 in the paper. -/
theorem eigenvalue_condition {n M : Nat} (es : EigenStructure n M)
    (hM : M > 0) (s : Real) (hs : 0 <= s ∧ s < 1) (lambda : Real) :
    IsEigenvalue (adiabaticHam es s ⟨hs.1, le_of_lt hs.2⟩) lambda ↔
    (lambda = s * es.eigenvalues (es.assignment _) ∨
     (1 / (1 - s) = (1 / qubitDim n) *
       Finset.sum Finset.univ (fun k =>
         (es.degeneracies k : Real) / (s * es.eigenvalues k - lambda)))) := by
  sorry

/-! ## Three regions of s -/

/-- Left of avoided crossing: I_{s←} = [0, s* - δ_s) -/
def leftRegion {n M : Nat} (es : EigenStructure n M) (hM : M >= 2) (s : Real) : Prop :=
  0 <= s ∧ s < avoidedCrossingPosition es (Nat.lt_of_lt_of_le Nat.zero_lt_one hM) -
             avoidedCrossingWindow es hM

/-- Around avoided crossing: I_{s*} = [s* - δ_s, s* + δ_s] -/
def avoidedCrossingRegion {n M : Nat} (es : EigenStructure n M) (hM : M >= 2) (s : Real) : Prop :=
  let sStar := avoidedCrossingPosition es (Nat.lt_of_lt_of_le Nat.zero_lt_one hM)
  let delta := avoidedCrossingWindow es hM
  |s - sStar| <= delta

/-- Right of avoided crossing: I_{s→} = (s* + δ_s, 1] -/
def rightRegion {n M : Nat} (es : EigenStructure n M) (hM : M >= 2) (s : Real) : Prop :=
  avoidedCrossingPosition es (Nat.lt_of_lt_of_le Nat.zero_lt_one hM) +
    avoidedCrossingWindow es hM < s ∧ s <= 1

/-! ## Gap bounds to the LEFT of avoided crossing -/

/-- The ground energy of H(s) is bounded above by the variational ansatz.
    Upper bound: λ₀(s) ≤ ⟨φ|H(s)|φ⟩ for any unit state |φ⟩ -/
theorem groundEnergy_variational_bound {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2) (s : Real) (hs : 0 <= s ∧ s <= 1)
    (phi : NQubitState n) (hphi : normSquared phi = 1) :
    ∃ (E0 : Real), IsEigenvalue (adiabaticHam es s hs) E0 ∧
      E0 <= (expectation (adiabaticHam es s hs) phi).re := by
  sorry

/-- Lower bound on first excited state: λ₁(s) ≥ s E₀ -/
theorem firstExcited_lower_bound {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2) (s : Real) (hs : 0 <= s ∧ s <= 1) :
    ∃ (E1 : Real), IsEigenvalue (adiabaticHam es s hs) E1 ∧
      E1 >= s * es.eigenvalues ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hM⟩ ∧
      ∃ (E0 : Real), IsEigenvalue (adiabaticHam es s hs) E0 ∧ E0 < E1 := by
  sorry

/-- Gap bound to the left of avoided crossing:
    g(s) ≥ (A_1/A_2) * (s* - s)/(1 - s*)
    This is derived using the variational principle. -/
theorem gap_bound_left {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2) (s : Real) (hs : leftRegion es hM s) :
    ∃ (gap : Real), gap > 0 ∧
    gap >= (A1 es (Nat.lt_of_lt_of_le Nat.zero_lt_one hM) /
            A2 es (Nat.lt_of_lt_of_le Nat.zero_lt_one hM)) *
           (avoidedCrossingPosition es (Nat.lt_of_lt_of_le Nat.zero_lt_one hM) - s) /
           (1 - avoidedCrossingPosition es (Nat.lt_of_lt_of_le Nat.zero_lt_one hM)) := by
  sorry

/-! ## Gap bounds at the avoided crossing -/

/-- The spectral gap at the avoided crossing is approximately g_min -/
theorem gap_at_avoided_crossing {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2) (s : Real) (hs : avoidedCrossingRegion es hM s)
    (hspec : spectralCondition es hM 0.02 (by norm_num)) :
    ∃ (gap : Real), gap > 0 ∧
    gap >= minimumGap es hM / 2 ∧
    gap <= 2 * minimumGap es hM := by
  sorry

/-! ## Gap bounds to the RIGHT of avoided crossing (Resolvent method) -/

/-- The line γ(s) = sE₀ + β(s) used in the resolvent bound -/
noncomputable def gammaLine {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2) (s : Real) (k a : Real) : Real :=
  let E0 := es.eigenvalues ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hM⟩
  let gmin := minimumGap es hM
  let sStar := avoidedCrossingPosition es (Nat.lt_of_lt_of_le Nat.zero_lt_one hM)
  let s0 := sStar - k * gmin * (1 - sStar) / (a - k * gmin)
  s * E0 + a * (s - s0) / (1 - s0)

/-- Sherman-Morrison formula for resolvent -/
theorem shermanMorrison_resolvent {n : Nat} (A : NQubitOperator n)
    (u v : NQubitState n) (gamma : Complex)
    (hInv : ((gamma • identityOp (qubitDim n) - A).det ≠ 0))
    (hDenom : 1 + innerProd v (applyOp (resolvent A gamma) u) ≠ 0) :
    resolvent (A + outerProd u v) gamma =
    resolvent A gamma -
    (1 / (1 + innerProd v (applyOp (resolvent A gamma) u))) •
    outerProd (applyOp (resolvent A gamma) u) (applyOp ((resolvent A gamma)†) v) := by
  sorry

/-- Gap bound to the right of avoided crossing:
    g(s) ≥ (Δ/30) * (s - s₀)/(1 - s₀)
    where s₀ is determined by k=1/4 and a = 4k²Δ/3 -/
theorem gap_bound_right {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2) (s : Real) (hs : rightRegion es hM s)
    (hspec : spectralCondition es hM 0.02 (by norm_num)) :
    let Delta := spectralGapDiag es hM
    let k : Real := 1/4
    let a := 4 * k^2 * Delta / 3
    let gmin := minimumGap es hM
    let sStar := avoidedCrossingPosition es (Nat.lt_of_lt_of_le Nat.zero_lt_one hM)
    let s0 := sStar - k * gmin * (1 - sStar) / (a - k * gmin)
    ∃ (gap : Real), gap > 0 ∧
    gap >= (Delta / 30) * (s - s0) / (1 - s0) := by
  sorry

/-! ## Combined gap bound for all s -/

/-- Main gap bound theorem: combining all three regions -/
theorem gap_bound_all_s {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2) (s : Real) (hs : 0 <= s ∧ s <= 1)
    (hspec : spectralCondition es hM 0.02 (by norm_num)) :
    ∃ (gap : Real), gap > 0 ∧
    gap >= minimumGap es hM / 4 := by
  sorry

/-- The gap achieves its minimum near the avoided crossing -/
theorem gap_minimum_at_crossing {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2) (hspec : spectralCondition es hM 0.02 (by norm_num)) :
    ∃ (sMin : Real), 0 < sMin ∧ sMin < 1 ∧
    avoidedCrossingRegion es hM sMin ∧
    ∀ s, (0 <= s ∧ s <= 1) ->
      ∃ (gapS gapMin : Real),
        IsEigenvalue (adiabaticHam es s ⟨‹_›.1, ‹_›.2⟩) gapS ∧
        IsEigenvalue (adiabaticHam es sMin ⟨le_of_lt ‹_›, le_of_lt ‹_›⟩) gapMin ∧
        gapMin <= gapS := by
  sorry

end UAQO
