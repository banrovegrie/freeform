/-
  Running time analysis for adiabatic quantum optimization.

  Main Result 1 (Theorem 1 in paper):
    AQO prepares the ground state in time
    T = O((1/ε) * (√A₂)/(A₁²Δ²) * √(2ⁿ/d₀))

  This matches the Ω(2^{n/2}) lower bound up to polylog factors.
-/
import UAQO.Adiabatic.Theorem

namespace UAQO

/-! ## Running time computation -/

/-- The running time formula from Theorem 1 -/
noncomputable def runningTime {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2) (epsilon : Real) (heps : epsilon > 0) : Real :=
  let A1_val := A1 es (Nat.lt_of_lt_of_le Nat.zero_lt_one hM)
  let A2_val := A2 es (Nat.lt_of_lt_of_le Nat.zero_lt_one hM)
  let Delta := spectralGapDiag es hM
  let d0 := es.degeneracies ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hM⟩
  let N := qubitDim n
  (1 / epsilon) * (Real.sqrt A2_val / (A1_val^2 * Delta^2)) * Real.sqrt (N / d0)

/-! ## Main Result 1: Running time of AQO -/

/-- Main Result 1 (Theorem 1 in the paper):
    AQO prepares the ground state with fidelity 1-ε in time
    T = O((1/ε) * (√A₂)/(A₁²Δ²) * √(2ⁿ/d₀)) -/
theorem mainResult1 {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2)
    (hspec : spectralCondition es hM 0.02 (by norm_num))
    (epsilon : Real) (heps : 0 < epsilon ∧ epsilon < 1) :
    let T := runningTime es hM epsilon heps.1
    let d0 := es.degeneracies ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hM⟩
    ∃ (evol : SchrodingerEvolution n T (by sorry)),
      let finalState := evol.psi T
      let groundSym := symmetricState es ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hM⟩
      normSquared (fun i => finalState i - groundSym i) <= epsilon := by
  sorry

/-! ## Optimality for Ising Hamiltonians -/

/-- For Ising Hamiltonians with Δ ≥ 1/poly(n), the running time is Õ(√(2ⁿ/d₀)) -/
theorem runningTime_ising {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2)
    (hspec : spectralCondition es hM 0.02 (by norm_num))
    (hIsing : ∃ (p : Nat), (spectralGapDiag es hM) >= 1 / n^p)
    (hA1bound : ∃ (q : Nat), A1 es (Nat.lt_of_lt_of_le Nat.zero_lt_one hM) <= n^q)
    (hA2bound : ∃ (r : Nat), A2 es (Nat.lt_of_lt_of_le Nat.zero_lt_one hM) <= n^r)
    (epsilon : Real) (heps : 0 < epsilon ∧ epsilon < 1) :
    let T := runningTime es hM epsilon heps.1
    let d0 := es.degeneracies ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hM⟩
    let N := qubitDim n
    ∃ (polyFactor : Nat -> Real),
      (∃ deg, ∀ m, polyFactor m <= m^deg) ∧
      T <= polyFactor n * Real.sqrt (N / d0) / epsilon := by
  sorry

/-! ## Matching the lower bound -/

/-- The lower bound Ω(2^{n/2}) from Farhi et al. -/
axiom lowerBound_unstructuredSearch :
    ∀ (n : Nat) (alg : NQubitState n -> Real),
      -- Any algorithm finding the marked item
      True -> -- (needs formal statement of "algorithm finds marked item")
      ∃ (c : Real), c > 0 ∧
        True -- time >= c * 2^(n/2)

/-- Our running time matches the lower bound up to polylog factors -/
theorem runningTime_matches_lower_bound {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2)
    (hspec : spectralCondition es hM 0.02 (by norm_num))
    (hIsing : ∃ (p : Nat), (spectralGapDiag es hM) >= 1 / n^p)
    (epsilon : Real) (heps : 0 < epsilon ∧ epsilon < 1) :
    let T := runningTime es hM epsilon heps.1
    let d0 := es.degeneracies ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hM⟩
    ∃ (c₁ c₂ : Real) (polylog : Nat -> Real),
      c₁ > 0 ∧ c₂ > 0 ∧
      (∀ m, polylog m <= (Real.log m)^10) ∧
      c₁ * Real.sqrt ((qubitDim n : Real) / d0) <= T ∧
      T <= c₂ * polylog n * Real.sqrt ((qubitDim n : Real) / d0) / epsilon := by
  sorry

/-! ## The final state is the symmetric ground state -/

/-- The final state is an equal superposition over ground states:
    |v(1)⟩ = (1/√d₀) Σ_{z ∈ Ω₀} |z⟩ -/
theorem finalState_symmetric {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2)
    (hspec : spectralCondition es hM 0.02 (by norm_num))
    (epsilon : Real) (heps : 0 < epsilon ∧ epsilon < 1) :
    let groundSym := symmetricState es ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hM⟩
    normSquared groundSym = 1 ∧
    (∀ (z : Fin (qubitDim n)),
      es.assignment z = ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hM⟩ ->
      groundSym z = 1 / Complex.ofReal (Real.sqrt (es.degeneracies ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hM⟩))) := by
  sorry

/-! ## Measurement and solution extraction -/

/-- Measuring the final state yields a ground state with high probability -/
theorem measurement_yields_groundstate {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2)
    (hspec : spectralCondition es hM 0.02 (by norm_num))
    (epsilon : Real) (heps : 0 < epsilon ∧ epsilon < 1) :
    let T := runningTime es hM epsilon heps.1
    ∀ (finalState : NQubitState n),
      (normSquared (fun i =>
        finalState i - symmetricState es ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hM⟩ i) <= epsilon) ->
      -- Probability of measuring a ground state
      Finset.sum (eigenspace es ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hM⟩)
        (fun z => Complex.normSq (finalState z)) >= 1 - 2 * epsilon := by
  sorry

end UAQO
