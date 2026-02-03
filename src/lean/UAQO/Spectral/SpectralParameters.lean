/-
  Spectral parameters A_p for diagonal Hamiltonians.

  These parameters are central to the paper: they determine the position of the
  avoided crossing (via A_1) and appear in the running time bound.

  Definition from the paper (Eq. 5):
    A_p = (1/N) Σ_{k=1}^{M-1} d_k / (E_k - E_0)^p

  where p ∈ ℕ.
-/
import UAQO.Spectral.DiagonalHamiltonian

namespace UAQO

/-! ## Spectral parameters -/

/-- The spectral parameter A_p = (1/N) Σ_{k≥1} d_k / (E_k - E_0)^p -/
noncomputable def spectralParam {n M : Nat} (es : EigenStructure n M)
    (hM : M > 0) (p : Nat) : Real :=
  let E0 := es.eigenvalues ⟨0, hM⟩
  let N := qubitDim n
  (1 / N) * Finset.sum (Finset.filter (fun k => k.val > 0) Finset.univ)
    (fun k => (es.degeneracies k : Real) / (es.eigenvalues k - E0)^p)

notation "A_" p => spectralParam _ _ p

/-- A_1 specifically, most important for the avoided crossing position -/
noncomputable def A1 {n M : Nat} (es : EigenStructure n M) (hM : M > 0) : Real :=
  spectralParam es hM 1

/-- A_2, appears in the running time and minimum gap -/
noncomputable def A2 {n M : Nat} (es : EigenStructure n M) (hM : M > 0) : Real :=
  spectralParam es hM 2

/-! ## Key properties of spectral parameters -/

/-- A_p is positive for p ≥ 1 when M ≥ 2 -/
theorem spectralParam_positive {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2) (p : Nat) (hp : p >= 1) : spectralParam es (Nat.lt_of_lt_of_le Nat.zero_lt_one hM) p > 0 := by
  simp [spectralParam]
  apply mul_pos
  · apply div_pos
    · norm_num
    · simp [qubitDim]
      exact Nat.pow_pos (by norm_num) n
  · apply Finset.sum_pos
    · intro k hk
      simp [Finset.mem_filter] at hk
      apply div_pos
      · exact Nat.cast_pos.mpr (es.deg_positive k)
      · apply pow_pos
        have hord := es.eigenval_ordered ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hM⟩ k
        simp at hord
        have hk0 : (0 : Fin M) < k := by
          simp [Fin.lt_iff_val_lt_val]
          exact hk.2
        linarith [hord hk0]
    · simp [Finset.filter_nonempty_iff]
      use ⟨1, hM⟩
      simp

/-- A_2 ≥ (N-d_0)/N * Δ^{-2} ≥ (1 - 1/N) * Δ^{-2} -/
theorem A2_lower_bound {n M : Nat} (es : EigenStructure n M) (hM : M >= 2) :
    A2 es (Nat.lt_of_lt_of_le Nat.zero_lt_one hM) >=
    (1 - (es.degeneracies ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hM⟩ : Real) / qubitDim n) /
    (spectralGapDiag es hM)^2 := by
  sorry -- Requires detailed sum analysis

/-- Simpler lower bound: A_2 ≥ 1 - 1/N -/
theorem A2_lower_bound_simple {n M : Nat} (es : EigenStructure n M) (hM : M >= 2) :
    A2 es (Nat.lt_of_lt_of_le Nat.zero_lt_one hM) >= 1 - 1 / (qubitDim n : Real) := by
  sorry

/-! ## The spectral condition (Definition 1 in the paper) -/

/-- The spectral condition: (1/Δ)√(d_0/(A_2 N)) < c for small constant c -/
def spectralCondition {n M : Nat} (es : EigenStructure n M) (hM : M >= 2)
    (c : Real) (hc : c > 0) : Prop :=
  let d0 := es.degeneracies ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hM⟩
  let Delta := spectralGapDiag es hM
  let A2_val := A2 es (Nat.lt_of_lt_of_le Nat.zero_lt_one hM)
  let N := qubitDim n
  (1 / Delta) * Real.sqrt (d0 / (A2_val * N)) < c

/-- For Ising Hamiltonians with Δ ≥ 1/poly(n), the spectral condition holds -/
theorem spectralCondition_ising {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2)
    (hDelta : spectralGapDiag es hM >= 1 / (n : Real))
    (c : Real) (hc : c > 0) (hcLarge : c >= 1 / (n : Real)) :
    spectralCondition es hM c hc := by
  sorry

/-! ## Key formulas involving A_1 -/

/-- The position of the avoided crossing: s* = A_1 / (A_1 + 1) -/
noncomputable def avoidedCrossingPosition {n M : Nat} (es : EigenStructure n M)
    (hM : M > 0) : Real :=
  let A1_val := A1 es hM
  A1_val / (A1_val + 1)

notation "s*" => avoidedCrossingPosition

/-- s* is in (0, 1) when A_1 > 0 -/
theorem avoidedCrossing_in_interval {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2) :
    0 < avoidedCrossingPosition es (Nat.lt_of_lt_of_le Nat.zero_lt_one hM) ∧
    avoidedCrossingPosition es (Nat.lt_of_lt_of_le Nat.zero_lt_one hM) < 1 := by
  have hA1pos := spectralParam_positive es hM 1 (by norm_num)
  simp [avoidedCrossingPosition, A1]
  constructor
  · apply div_pos hA1pos
    linarith
  · apply div_lt_one_of_lt
    · linarith
    · linarith

/-- The window around the avoided crossing: δ_s = 2/(A_1+1)² √(d_0 A_2/N) -/
noncomputable def avoidedCrossingWindow {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2) : Real :=
  let A1_val := A1 es (Nat.lt_of_lt_of_le Nat.zero_lt_one hM)
  let A2_val := A2 es (Nat.lt_of_lt_of_le Nat.zero_lt_one hM)
  let d0 := es.degeneracies ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hM⟩
  let N := qubitDim n
  2 / (A1_val + 1)^2 * Real.sqrt (d0 * A2_val / N)

notation "δ_s" => avoidedCrossingWindow

/-- The minimum spectral gap: g_min = 2A_1/(A_1+1) √(d_0/(A_2 N)) -/
noncomputable def minimumGap {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2) : Real :=
  let A1_val := A1 es (Nat.lt_of_lt_of_le Nat.zero_lt_one hM)
  let A2_val := A2 es (Nat.lt_of_lt_of_le Nat.zero_lt_one hM)
  let d0 := es.degeneracies ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hM⟩
  let N := qubitDim n
  2 * A1_val / (A1_val + 1) * Real.sqrt (d0 / (A2_val * N))

notation "g_min" => minimumGap

/-- The minimum gap scales as √(d_0/N) -/
theorem minimumGap_scaling {n M : Nat} (es : EigenStructure n M) (hM : M >= 2) :
    ∃ (c : Real), c > 0 ∧
    minimumGap es hM <= c * Real.sqrt ((es.degeneracies ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hM⟩ : Real) / qubitDim n) := by
  sorry

end UAQO
