/-
  Structured-family bridge lemmas for Experiment 13.

  These lemmas encode the formal core used in Proposition 9:
  exact computation trivially implies any target precision, while
  inverse-precision algorithms scale as 1/epsilon and therefore evaluate
  to exponential magnitude at epsilon = 2^{-n/2}.
-/
import IntermediateHardness.Basic

namespace IntermediateHardness

/-- An exact estimator agrees with the target value on every instance. -/
def ExactEstimator {AType : Type} (Ahat A : AType -> Rat) : Prop :=
  forall x : AType, Ahat x = A x

/-- Exactness is pointwise reflexive. -/
theorem exactEstimator_refl {AType : Type} (A : AType -> Rat) : ExactEstimator A A := by
  intro x
  rfl

/-- Exactness is transitive. -/
theorem exactEstimator_trans {AType : Type}
    {Ahat1 Ahat2 A : AType -> Rat}
    (h1 : ExactEstimator Ahat1 Ahat2)
    (h2 : ExactEstimator Ahat2 A) : ExactEstimator Ahat1 A := by
  intro x
  calc
    Ahat1 x = Ahat2 x := h1 x
    _ = A x := h2 x

/-- A canonical inverse-precision runtime model T(epsilon) = K/epsilon. -/
def runtimeInvPrecision (K eps : Rat) : Rat := K * Rat.inv eps

/-- Runtime specialization at epsilon = 2^{-k}. -/
theorem runtimeInvPrecision_at_pow2 (K : Rat) (k : Nat) :
    runtimeInvPrecision K (epsPow2 k) = K * ((2 : Rat) ^ k) := by
  unfold runtimeInvPrecision
  change K * qCore (epsPow2 k) = K * ((2 : Rat) ^ k)
  rw [q_epsPow2]

/-- Runtime at schedule precision epsilon = 2^{-n/2}. -/
theorem runtimeInvPrecision_at_threshold (K : Rat) (n : Nat) :
    runtimeInvPrecision K (epsPow2 (n / 2)) = K * ((2 : Rat) ^ (n / 2)) := by
  exact runtimeInvPrecision_at_pow2 K (n / 2)

end IntermediateHardness
