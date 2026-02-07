/-
  Promise-time framing lemmas for Experiment 13.

  This file formalizes the discrete core of Proposition 10:
  - lower scaling 2^k
  - upper scaling within a constant factor
  - parameterized bound at threshold k = n/2.
-/
import IntermediateHardness.Basic

namespace IntermediateHardness

/-- Core quantum lower scaling at precision exponent k. -/
def coreLower (k : Nat) : Rat := qCore (epsPow2 k)

/-- A matching upper bound within factor 2 (discrete proxy for Theta). -/
def coreUpper (k : Nat) : Rat := qCore (epsPow2 k) + qCore (epsPow2 k)

/-- Closed form for the lower scaling. -/
theorem coreLower_closed_form (k : Nat) : coreLower k = (2 : Rat) ^ k := by
  unfold coreLower
  exact q_epsPow2 k

/-- Closed form for the upper scaling. -/
theorem coreUpper_closed_form (k : Nat) :
    coreUpper k = ((2 : Rat) ^ k) + ((2 : Rat) ^ k) := by
  unfold coreUpper
  simp [q_epsPow2]

/-- Parameterized bound: sqrt(N)-term + 1/epsilon-term on the k-grid. -/
def parameterizedBound (n k : Nat) : Rat :=
  ((2 : Rat) ^ (n / 2)) + ((2 : Rat) ^ k)

/-- At schedule precision k=n/2, both terms have the same exponent. -/
theorem parameterizedBound_at_threshold (n : Nat) :
    parameterizedBound n (n / 2) =
      ((2 : Rat) ^ (n / 2)) + ((2 : Rat) ^ (n / 2)) := by
  unfold parameterizedBound
  rfl

end IntermediateHardness
