/-
  Experiment 13 Lean Formalization (core discrete skeleton)

  Scope:
  - Precision-grid scaling laws used by Proposition 8.
  - Structured-bridge exactness/runtime lemmas used by Proposition 9.
  - Promise-time constant-factor tightness lemmas used by Proposition 10.

  This package is intentionally self-contained and uses only Lean core.
-/
import IntermediateHardness.Basic
import IntermediateHardness.PhaseDiagram
import IntermediateHardness.BarrierGrid
import IntermediateHardness.StructuredBridge
import IntermediateHardness.PromiseTime

namespace IntermediateHardness

#check epsPow2
#check qCore
#check cCore
#check sepCore

#check q_epsPow2
#check c_epsPow2
#check sep_epsPow2
#check q_at_threshold
#check c_at_threshold
#check sep_at_threshold

#check phasePoint
#check phasePoint_closed_form
#check IntermediateHardness.q_next_doubles
#check IntermediateHardness.sep_next_doubles
#check phasePoint_threshold
#check phasePoint_constant_example

#check scheduleErrorProxy
#check scheduleErrorProxy_closed_form
#check one_le_two_pow
#check three_le_scheduleErrorProxy
#check scheduleErrorProxy_gt_half
#check barrierBool
#check barrierBool_true
#check barrierAllUpTo
#check barrierAllUpTo_true
#check barrierAllUpTo_1024

#check ExactEstimator
#check exactEstimator_refl
#check exactEstimator_trans
#check runtimeInvPrecision
#check runtimeInvPrecision_at_pow2
#check runtimeInvPrecision_at_threshold

#check coreLower
#check coreUpper
#check coreLower_closed_form
#check coreUpper_closed_form
#check parameterizedBound
#check parameterizedBound_at_threshold

end IntermediateHardness
