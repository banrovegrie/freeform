/-
  Finite-grid barrier certificates for Experiment 13.

  This module provides machine-checked finite certificates for the
  schedule-level interpolation-barrier proxy inequality on large ranges
  of precision exponents.
-/
import IntermediateHardness.Basic

namespace IntermediateHardness

/-- Proxy schedule-error expression on the epsilon_k = 2^{-k} grid. -/
def scheduleErrorProxy (k : Nat) : Rat := (3 : Rat) * qCore (epsPow2 k)

/-- Closed form: scheduleErrorProxy(k) = 3 * 2^k. -/
theorem scheduleErrorProxy_closed_form (k : Nat) :
    scheduleErrorProxy k = (3 : Rat) * ((2 : Rat) ^ k) := by
  unfold scheduleErrorProxy
  rw [q_epsPow2]

/-- Monotonic lower bound: 1 <= 2^k for all k. -/
theorem one_le_two_pow (k : Nat) : (1 : Rat) <= (2 : Rat) ^ k := by
  induction k with
  | zero =>
      exact Rat.le_refl
  | succ k ih =>
      have h12 : (1 : Rat) <= 2 := by decide
      have hk_nonneg : (0 : Rat) <= (2 : Rat) ^ k := Rat.le_of_lt (two_pow_pos k)
      have hmul : (2 : Rat) ^ k * 1 <= (2 : Rat) ^ k * 2 :=
        Rat.mul_le_mul_of_nonneg_left h12 hk_nonneg
      have hstep : (2 : Rat) ^ k <= (2 : Rat) ^ k * 2 := by
        simpa [Rat.mul_one] using hmul
      have hfinal : (1 : Rat) <= (2 : Rat) ^ k * 2 := Rat.le_trans ih hstep
      simpa [Rat.pow_succ] using hfinal

/-- Coarse lower bound needed for the schedule barrier proxy. -/
theorem three_le_scheduleErrorProxy (k : Nat) :
    (3 : Rat) <= scheduleErrorProxy k := by
  unfold scheduleErrorProxy
  rw [q_epsPow2]
  have h3nonneg : (0 : Rat) <= 3 := by decide
  have hmul : (3 : Rat) * 1 <= (3 : Rat) * ((2 : Rat) ^ k) :=
    Rat.mul_le_mul_of_nonneg_left (one_le_two_pow k) h3nonneg
  simpa [Rat.mul_one] using hmul

/-- Symbolic barrier inequality: schedule proxy is always above 1/2. -/
theorem scheduleErrorProxy_gt_half (k : Nat) :
    ((1 : Rat) / 2) < scheduleErrorProxy k := by
  have htwo_pos : (0 : Rat) < 2 := by decide
  have hone_lt_three_times_two : (1 : Rat) < (3 : Rat) * 2 := by
    have h12 : (1 : Rat) < 2 := by decide
    have h13 : (1 : Rat) <= 3 := by decide
    have h2nonneg : (0 : Rat) <= 2 := by decide
    have h2_le_three_times_two : (2 : Rat) <= (3 : Rat) * 2 := by
      have hmul : (1 : Rat) * 2 <= (3 : Rat) * 2 :=
        Rat.mul_le_mul_of_nonneg_right h13 h2nonneg
      simpa [Rat.mul_one] using hmul
    have h1_le_three_times_two : (1 : Rat) <= (3 : Rat) * 2 :=
      Rat.le_trans (Rat.le_of_lt h12) h2_le_three_times_two
    have hnot : Not ((2 : Rat) <= 1) := (Rat.not_le).2 h12
    have hneq : Ne (1 : Rat) ((3 : Rat) * 2) := by
      intro heq
      have : (2 : Rat) <= 1 := by simpa [heq] using h2_le_three_times_two
      exact hnot this
    exact Rat.lt_of_le_of_ne h1_le_three_times_two hneq
  have hhalf_lt_three : ((1 : Rat) / 2) < 3 := by
    rw [Rat.div_lt_iff htwo_pos]
    simpa [Rat.mul_comm] using hone_lt_three_times_two
  have hhalf_le_three : ((1 : Rat) / 2) <= 3 := Rat.le_of_lt hhalf_lt_three
  have hthree_le : (3 : Rat) <= scheduleErrorProxy k := three_le_scheduleErrorProxy k
  have hle : ((1 : Rat) / 2) <= scheduleErrorProxy k := Rat.le_trans hhalf_le_three hthree_le
  have hnot : Not ((3 : Rat) <= ((1 : Rat) / 2)) := (Rat.not_le).2 hhalf_lt_three
  have hneq : Ne ((1 : Rat) / 2) (scheduleErrorProxy k) := by
    intro heq
    have : (3 : Rat) <= ((1 : Rat) / 2) := by simpa [heq] using hthree_le
    exact hnot this
  exact Rat.lt_of_le_of_ne hle hneq

/-- Boolean form of the barrier inequality (strictly above 1/2). -/
def barrierBool (k : Nat) : Bool :=
  decide (((1 : Rat) / 2) < scheduleErrorProxy k)

/-- Barrier boolean is true for every precision exponent. -/
theorem barrierBool_true (k : Nat) : barrierBool k = true := by
  unfold barrierBool
  simp [scheduleErrorProxy_gt_half k]

/-- Check all exponents from 0 through K. -/
def barrierAllUpTo (K : Nat) : Bool :=
  (List.range (K + 1)).all barrierBool

/-- Symbolic all-range certificate on the finite prefix [0, K]. -/
theorem barrierAllUpTo_true (K : Nat) : barrierAllUpTo K = true := by
  unfold barrierAllUpTo
  refine (List.all_eq_true).2 ?_
  intro x hx
  exact barrierBool_true x

/-- Finite certificate: the barrier proxy holds for all k <= 1024. -/
theorem barrierAllUpTo_1024 : barrierAllUpTo 1024 = true := by
  exact barrierAllUpTo_true 1024

end IntermediateHardness
