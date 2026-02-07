/-
  Experiment 13: Intermediate Hardness
  Core algebraic formalization for precision-dependent query scaling.

  This file uses only Lean core Rat lemmas (no Mathlib dependency).
-/
import Init.Data.Rat.Lemmas

namespace IntermediateHardness

/-- Precision family epsilon_k = 2^{-k}. -/
def epsPow2 (k : Nat) : Rat := Rat.inv ((2 : Rat) ^ k)

/-- Core quantum query scaling model Q(epsilon) = 1/epsilon. -/
def qCore (eps : Rat) : Rat := Rat.inv eps

/-- Core classical query scaling model C(epsilon) = 1/epsilon^2. -/
def cCore (eps : Rat) : Rat := Rat.inv eps * Rat.inv eps

/-- Core separation factor C/Q = 1/epsilon. -/
def sepCore (eps : Rat) : Rat := cCore eps * Rat.inv (qCore eps)

/-- Positivity of the base constant 2 in Rat. -/
theorem two_pos : (0 : Rat) < 2 := by decide

/-- Strict positivity of 2^k. -/
theorem two_pow_pos (k : Nat) : (0 : Rat) < (2 : Rat) ^ k := by
  exact Rat.pow_pos two_pos

/-- Non-zeroness of 2^k. -/
theorem two_pow_ne_zero (k : Nat) : Ne ((2 : Rat) ^ k) 0 := by
  exact Rat.ne_of_gt (two_pow_pos k)

/-- Quantum core scaling at epsilon = 2^{-k}: Q = 2^k. -/
theorem q_epsPow2 (k : Nat) : qCore (epsPow2 k) = (2 : Rat) ^ k := by
  unfold qCore epsPow2
  simpa using (Rat.inv_inv ((2 : Rat) ^ k))

/-- Classical core scaling at epsilon = 2^{-k}: C = (2^k)^2. -/
theorem c_epsPow2 (k : Nat) :
    cCore (epsPow2 k) = ((2 : Rat) ^ k) * ((2 : Rat) ^ k) := by
  have h := Rat.inv_inv ((2 : Rat) ^ k)
  have hmul := congrArg (fun t : Rat => t * t) h
  simpa [cCore, epsPow2] using hmul

/-- Separation scaling at epsilon = 2^{-k}: C/Q = 2^k. -/
theorem sep_epsPow2 (k : Nat) : sepCore (epsPow2 k) = (2 : Rat) ^ k := by
  have hk : Ne ((2 : Rat) ^ k) 0 := two_pow_ne_zero k
  have hcancel : (2 : Rat) ^ k * Rat.inv ((2 : Rat) ^ k) = 1 := by
    exact Rat.mul_inv_cancel ((2 : Rat) ^ k) hk
  unfold sepCore
  rw [c_epsPow2, q_epsPow2]
  calc
    ((2 : Rat) ^ k * (2 : Rat) ^ k) * Rat.inv ((2 : Rat) ^ k)
        = (2 : Rat) ^ k * ((2 : Rat) ^ k * Rat.inv ((2 : Rat) ^ k)) := by
            rw [Rat.mul_assoc]
    _ = (2 : Rat) ^ k * 1 := by rw [hcancel]
    _ = (2 : Rat) ^ k := by rw [Rat.mul_one]

/-- Schedule threshold mapping: epsilon = 2^{-n/2} is represented by k = n/2. -/
theorem q_at_threshold (n : Nat) :
    qCore (epsPow2 (n / 2)) = (2 : Rat) ^ (n / 2) := by
  exact q_epsPow2 (n / 2)

/-- Classical threshold scaling: C = (2^{n/2})^2 at k = n/2. -/
theorem c_at_threshold (n : Nat) :
    cCore (epsPow2 (n / 2)) =
      ((2 : Rat) ^ (n / 2)) * ((2 : Rat) ^ (n / 2)) := by
  exact c_epsPow2 (n / 2)

/-- Separation at schedule threshold: C/Q = 2^{n/2}. -/
theorem sep_at_threshold (n : Nat) :
    sepCore (epsPow2 (n / 2)) = (2 : Rat) ^ (n / 2) := by
  exact sep_epsPow2 (n / 2)

end IntermediateHardness
