/-
  Discrete phase-diagram formalization for Experiment 13.

  The continuous statement in proof.md is formalized on the canonical
  epsilon_k = 2^{-k} grid. This captures the exact exponents used in
  Proposition 8.
-/
import IntermediateHardness.Basic

namespace IntermediateHardness

/-- A discrete precision regime indexed by exponent k. -/
def phasePoint (k : Nat) : Prod Rat (Prod Rat Rat) :=
  (qCore (epsPow2 k), cCore (epsPow2 k), sepCore (epsPow2 k))

/-- Phase point evaluates to (2^k, (2^k)^2, 2^k). -/
theorem phasePoint_closed_form (k : Nat) :
    phasePoint k =
      ((2 : Rat) ^ k, ((2 : Rat) ^ k) * ((2 : Rat) ^ k), (2 : Rat) ^ k) := by
  unfold phasePoint
  simp [q_epsPow2, c_epsPow2, sep_epsPow2]

/-- Quantum query cost doubles when one precision bit is added. -/
theorem q_next_doubles (k : Nat) :
    qCore (epsPow2 (k + 1)) = (2 : Rat) * qCore (epsPow2 k) := by
  rw [q_epsPow2, q_epsPow2]
  simp [Rat.pow_succ, Rat.mul_comm]

/-- Separation factor doubles when one precision bit is added. -/
theorem sep_next_doubles (k : Nat) :
    sepCore (epsPow2 (k + 1)) = (2 : Rat) * sepCore (epsPow2 k) := by
  rw [sep_epsPow2, sep_epsPow2]
  simp [Rat.pow_succ, Rat.mul_comm]

/-- Algorithmically relevant threshold k = n/2. -/
theorem phasePoint_threshold (n : Nat) :
    phasePoint (n / 2) =
      ((2 : Rat) ^ (n / 2),
       ((2 : Rat) ^ (n / 2)) * ((2 : Rat) ^ (n / 2)),
       (2 : Rat) ^ (n / 2)) := by
  exact phasePoint_closed_form (n / 2)

/-- Constant-precision sanity check: epsilon = 2^{-2} gives (4,16,4). -/
theorem phasePoint_constant_example :
    phasePoint 2 = (4, 16, 4) := by
  native_decide

end IntermediateHardness
