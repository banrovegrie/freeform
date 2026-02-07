/-
  Proofs for schedule property axioms in Schedule.lean.

  Status:
  - avoidedCrossing_bound: Now a THEOREM in Schedule.lean (not an axiom)
    Requires spectralConditionForBounds hypothesis: A1 > 1 ∧ sqrt(d0*A2/N) < (A1+1)/2
    This condition is satisfied for typical 3-SAT instances where A1 ≈ √N >> 1

  - piecewiseSchedule_monotone: Still an axiom, requires spectralConditionForBounds hypothesis

  The spectral condition ensures:
  1. deltaS < sStar (crossing window starts after s=0)
  2. sStar + deltaS < 1 (crossing window ends before s=1)

  For unstructured search on 3-SAT, A1 ≈ √N - 1, so A1 >> 1 for large instances.
-/
import UAQO.Adiabatic.Schedule

namespace UAQO.Proofs.Adiabatic

open UAQO

/-- The avoided crossing window is within bounds: delta < s* and s* + delta < 1.

    This is now proved as a theorem in Schedule.lean with the spectralConditionForBounds
    hypothesis. The key insight is that for typical 3-SAT instances:
    - A1 ≈ √N >> 1 (so the A1 > 1 condition holds)
    - sqrt(d0*A2/N) is bounded by (A1+1)/2 for well-behaved eigenstructures -/
theorem avoidedCrossing_bound_proof {n M : Nat} (es : EigenStructure n M) (hM : M >= 2)
    (hcond : Spectral.GapBounds.FullSpectralHypothesis es hM) :
    let sStar := avoidedCrossingPosition es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM)
    let deltaS := avoidedCrossingWindow es hM
    deltaS < sStar ∧ sStar + deltaS < 1 :=
  avoidedCrossing_bound es hM hcond.cond

/-- Piecewise linear schedules are monotonically increasing.

    This remains an axiom in Schedule.lean. The proof requires showing that each
    segment has positive slope:
    - Left segment: slope = (sStar - deltaS) / T_left > 0 (requires deltaS < sStar)
    - Crossing segment: slope = 2*deltaS / T_cross > 0 (deltaS > 0 from window_pos)
    - Right segment: slope = (1 - sStar - deltaS) / T_right > 0 (requires sStar + deltaS < 1)

    The slopes being positive follow from avoidedCrossing_bound with spectralConditionForBounds. -/
theorem piecewiseSchedule_monotone_proof {n M : Nat} (es : EigenStructure n M) (hM : M >= 2)
    (hcond : Spectral.GapBounds.FullSpectralHypothesis es hM)
    (T : Real) (hT : T > 0)
    (T_left T_cross T_right : Real)
    (times_pos : T_left > 0 ∧ T_cross > 0 ∧ T_right > 0)
    (times_sum : T_left + T_cross + T_right = T)
    (t₁ t₂ : Real) (ht₁_ge : 0 <= t₁) (ht₁_lt_t₂ : t₁ < t₂) (ht₂_le : t₂ <= T) :
    let sStar := avoidedCrossingPosition es (Nat.lt_of_lt_of_le Nat.zero_lt_two hM)
    let deltaS := avoidedCrossingWindow es hM
    let s := fun t =>
      if t <= T_left then (sStar - deltaS) * t / T_left
      else if t <= T_left + T_cross then
        (sStar - deltaS) + 2 * deltaS * (t - T_left) / T_cross
      else (sStar + deltaS) + (1 - sStar - deltaS) * (t - T_left - T_cross) / T_right
    s t₁ < s t₂ :=
  piecewiseSchedule_monotone es hM hcond T hT T_left T_cross T_right
    times_pos times_sum t₁ t₂ ht₁_ge ht₁_lt_t₂ ht₂_le

end UAQO.Proofs.Adiabatic
