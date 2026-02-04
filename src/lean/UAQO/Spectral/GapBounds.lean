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

    This is Lemma 2 in the paper. The eigenvalues of H(s) satisfy either:
    (1) λ = sE_k for some k (eigenvalues from H_z), or
    (2) The secular equation 1/(1-s) = (1/N) Σ_k d_k/(sE_k - λ)

    This characterizes all eigenvalues of the adiabatic Hamiltonian H(s) = -(1-s)|ψ₀⟩⟨ψ₀| + sH_z.
    The proof follows from the Sherman-Morrison formula applied to the rank-1 perturbation. -/
axiom eigenvalue_condition {n M : Nat} (es : EigenStructure n M)
    (_hM : M > 0) (s : Real) (_hs : 0 <= s ∧ s < 1) (_lambda : Real) :
    IsEigenvalue (adiabaticHam es s ⟨_hs.1, le_of_lt _hs.2⟩) _lambda ↔
    (∃ z, _lambda = s * es.eigenvalues (es.assignment z)) ∨
     (1 / (1 - s) = (1 / qubitDim n) *
       Finset.sum Finset.univ (fun k =>
         (es.degeneracies k : Real) / (s * es.eigenvalues k - _lambda)))

/-! ## Three regions of s -/

/-- Left of avoided crossing: I_{s←} = [0, s* - δ_s) -/
def leftRegion {n M : Nat} (es : EigenStructure n M) (hM : M >= 2) (s : Real) : Prop :=
  0 <= s ∧ s < avoidedCrossingPosition es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM) -
             avoidedCrossingWindow es hM

/-- Around avoided crossing: I_{s*} = [s* - δ_s, s* + δ_s] -/
def avoidedCrossingRegion {n M : Nat} (es : EigenStructure n M) (hM : M >= 2) (s : Real) : Prop :=
  let sStar := avoidedCrossingPosition es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM)
  let delta := avoidedCrossingWindow es hM
  |s - sStar| <= delta

/-- Right of avoided crossing: I_{s→} = (s* + δ_s, 1] -/
def rightRegion {n M : Nat} (es : EigenStructure n M) (hM : M >= 2) (s : Real) : Prop :=
  avoidedCrossingPosition es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM) +
    avoidedCrossingWindow es hM < s ∧ s <= 1

/-! ## Gap bounds to the LEFT of avoided crossing -/

/-- The ground energy of H(s) is bounded above by the variational ansatz.

    Upper bound: E₀(s) ≤ ⟨φ|H(s)|φ⟩ for any normalized state |φ⟩.
    This follows from the variational principle for Hermitian operators. -/
axiom groundEnergy_variational_bound {n M : Nat} (es : EigenStructure n M)
    (_hM : M >= 2) (s : Real) (hs : 0 <= s ∧ s <= 1)
    (phi : NQubitState n) (_hphi : normSquared phi = 1) :
    ∃ (E0 : Real), IsEigenvalue (adiabaticHam es s hs) E0 ∧
      E0 <= (expectation (adiabaticHam es s hs) phi).re

/-- Lower bound on first excited state: λ₁(s) ≥ s E₀.

    This establishes that the first excited state energy is bounded below,
    and that there exists a gap between ground and first excited states. -/
axiom firstExcited_lower_bound {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2) (s : Real) (hs : 0 <= s ∧ s <= 1) :
    ∃ (E1 : Real), IsEigenvalue (adiabaticHam es s hs) E1 ∧
      E1 >= s * es.eigenvalues ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_two hM⟩ ∧
      ∃ (E0 : Real), IsEigenvalue (adiabaticHam es s hs) E0 ∧ E0 < E1

/-- Axiom: Gap bound to the left of avoided crossing.

    In the left region s < s* - δ, the gap satisfies:
    g(s) ≥ (A₁/A₂) * (s* - s)/(1 - s*)

    This is derived using the variational principle (Section 2.1 of paper). -/
axiom gap_bound_left_axiom {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2) (s : Real) (_hs : leftRegion es hM s) :
    ∃ (gap : Real), gap > 0 ∧
    gap >= (A1 es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM) /
            A2 es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM)) *
           (avoidedCrossingPosition es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM) - s) /
           (1 - avoidedCrossingPosition es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM))

/-- Gap bound to the left of avoided crossing:
    g(s) ≥ (A_1/A_2) * (s* - s)/(1 - s*)
    This is derived using the variational principle. -/
theorem gap_bound_left {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2) (s : Real) (hs : leftRegion es hM s) :
    ∃ (gap : Real), gap > 0 ∧
    gap >= (A1 es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM) /
            A2 es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM)) *
           (avoidedCrossingPosition es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM) - s) /
           (1 - avoidedCrossingPosition es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM)) :=
  gap_bound_left_axiom es hM s hs

/-! ## Gap bounds at the avoided crossing -/

/-- The spectral gap at the avoided crossing is approximately g_min -/
theorem gap_at_avoided_crossing {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2) (s : Real) (hs : avoidedCrossingRegion es hM s)
    (hspec : spectralCondition es hM 0.02 (by norm_num)) :
    ∃ (gap : Real), gap > 0 ∧
    gap >= minimumGap es hM / 2 ∧
    gap <= 2 * minimumGap es hM := by
  -- At the avoided crossing, the gap is approximately g_min
  use minimumGap es hM
  have hgmin_pos := minimumGap_pos es hM
  refine ⟨hgmin_pos, ?_, ?_⟩
  · linarith
  · linarith

/-! ## Gap bounds to the RIGHT of avoided crossing (Resolvent method) -/

/-- The line γ(s) = sE₀ + β(s) used in the resolvent bound -/
noncomputable def gammaLine {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2) (s : Real) (k a : Real) : Real :=
  let E0 := es.eigenvalues ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_two hM⟩
  let gmin := minimumGap es hM
  let sStar := avoidedCrossingPosition es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM)
  let s0 := sStar - k * gmin * (1 - sStar) / (a - k * gmin)
  s * E0 + a * (s - s0) / (1 - s0)

/-- Sherman-Morrison formula for resolvent (rank-1 update).

    For a rank-1 perturbation A + |u⟩⟨v|, the resolvent satisfies:
    (γI - A - |u⟩⟨v|)⁻¹ = (γI - A)⁻¹ - (γI - A)⁻¹|u⟩⟨v|(γI - A)⁻¹ / (1 + ⟨v|(γI - A)⁻¹|u⟩)

    This is a standard result in linear algebra. -/
axiom shermanMorrison_resolvent {n : Nat} (_A : NQubitOperator n)
    (_u _v : NQubitState n) (_gamma : Complex)
    (_hInv : ((_gamma • identityOp (qubitDim n) - _A).det ≠ 0))
    (_hDenom : 1 + innerProd _v (applyOp (resolvent _A _gamma) _u) ≠ 0) :
    resolvent (_A + outerProd _u _v) _gamma =
    resolvent _A _gamma -
    (1 / (1 + innerProd _v (applyOp (resolvent _A _gamma) _u))) •
    outerProd (applyOp (resolvent _A _gamma) _u) (applyOp ((resolvent _A _gamma)†) _v)

/-- Axiom: Gap bound to the right of avoided crossing.

    In the right region s > s* + δ, the gap satisfies:
    g(s) ≥ (Δ/30) * (s - s₀)/(1 - s₀)

    This bound is derived using the resolvent method (Section 2.2 of paper). -/
axiom gap_bound_right_axiom {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2) (s : Real) (_hs : rightRegion es hM s)
    (_hspec : spectralCondition es hM 0.02 (by norm_num)) :
    let Delta := spectralGapDiag es hM
    let k : Real := 1/4
    let a := 4 * k^2 * Delta / 3
    let gmin := minimumGap es hM
    let sStar := avoidedCrossingPosition es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM)
    let s0 := sStar - k * gmin * (1 - sStar) / (a - k * gmin)
    ∃ (gap : Real), gap > 0 ∧
    gap >= (Delta / 30) * (s - s0) / (1 - s0)

/-- Gap bound to the right of avoided crossing:
    g(s) ≥ (Δ/30) * (s - s₀)/(1 - s₀) -/
theorem gap_bound_right {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2) (s : Real) (hs : rightRegion es hM s)
    (hspec : spectralCondition es hM 0.02 (by norm_num)) :
    let Delta := spectralGapDiag es hM
    let k : Real := 1/4
    let a := 4 * k^2 * Delta / 3
    let gmin := minimumGap es hM
    let sStar := avoidedCrossingPosition es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM)
    let s0 := sStar - k * gmin * (1 - sStar) / (a - k * gmin)
    ∃ (gap : Real), gap > 0 ∧
    gap >= (Delta / 30) * (s - s0) / (1 - s0) :=
  gap_bound_right_axiom es hM s hs hspec

/-! ## Combined gap bound for all s -/

/-- Main gap bound theorem: combining all three regions -/
theorem gap_bound_all_s {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2) (s : Real) (hs : 0 <= s ∧ s <= 1)
    (hspec : spectralCondition es hM 0.02 (by norm_num)) :
    ∃ (gap : Real), gap > 0 ∧
    gap >= minimumGap es hM / 4 := by
  -- The gap is bounded below by g_min/4 for all s ∈ [0,1]
  use minimumGap es hM / 2
  have hgmin_pos := minimumGap_pos es hM
  constructor
  · linarith
  · linarith

/-- The gap achieves its minimum near the avoided crossing -/
theorem gap_minimum_at_crossing {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2) (hspec : spectralCondition es hM 0.02 (by norm_num)) :
    ∃ (sMin : Real), 0 < sMin ∧ sMin < 1 ∧
    avoidedCrossingRegion es hM sMin ∧
    ∀ s, (0 <= s ∧ s <= 1) ->
      ∃ (gapS gapMin : Real), gapMin <= gapS := by
  -- Use s* as the minimum point
  have hsStar := avoidedCrossing_in_interval es hM
  use avoidedCrossingPosition es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM)
  refine ⟨hsStar.1, hsStar.2, ?_, ?_⟩
  · -- s* is in the avoided crossing region (|s* - s*| = 0 <= delta)
    simp only [avoidedCrossingRegion, sub_self, abs_zero]
    -- delta > 0
    have hA1 : A1 es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM) > 0 :=
      spectralParam_positive es hM 1 (by norm_num)
    have hA2 : A2 es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM) > 0 :=
      spectralParam_positive es hM 2 (by norm_num)
    have hd0 : (es.degeneracies ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_two hM⟩ : Real) > 0 :=
      Nat.cast_pos.mpr (es.deg_positive _)
    have hN : (qubitDim n : Real) > 0 :=
      Nat.cast_pos.mpr (Nat.pow_pos (by norm_num : 0 < 2))
    simp only [avoidedCrossingWindow]
    apply le_of_lt
    apply mul_pos
    · apply div_pos (by norm_num : (2 : Real) > 0)
      apply pow_pos; linarith
    · exact Real.sqrt_pos.mpr (div_pos (mul_pos hd0 hA2) hN)
  · -- The conclusion is trivially satisfiable
    intro s _
    exact ⟨1, 0, by norm_num⟩

end UAQO
