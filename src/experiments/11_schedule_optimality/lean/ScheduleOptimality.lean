/-
  Schedule Optimality: Connecting Gap Profile to Variational Framework

  Formal verification of the schedule optimality analysis for
  adiabatic quantum optimization.

  MAIN RESULTS:

  **Theorem A (Measure Condition)**
  The paper's piecewise gap profile satisfies Guo-An's measure condition
  with C = 3*A_2/(A_1*(A_1+1)) + 30*(1-s_0)/Delta.

  **Theorem B (Grover Case)**
  C_Grover = 1 for all N >= 2.
  (NOT sqrt(N/(N-1)) -- domain clipping matters.)

  **Theorem C (Runtime Recovery)**
  Both p=2 (paper) and p=3/2 (Guo-An) achieve T = O(1/(epsilon * g_hat)),
  recovering T = O(sqrt(N * A_2 / d_0)).

  WHAT IS PROVEN IN LEAN:
  1. Spectral parameter definitions and positivity (sStar, cL, gHat, deltaS, cR)
  2. Key identity: c_L * delta_s = g_hat exactly
  3. Grover gap formula and its properties (min = 1/N, max = 1, crossing value)
  4. Grover N=4 sanity checks (A_1=3/4, s*=3/7, c_L=7/4, g^2(3/7)=13/49)
  5. Grover sublevel measure at x=1 equals 1 (key step for C=1)
  6. Grover sublevel measure for x>1 equals 1
  7. Grover measure ratio for x>1 equals 1/x
  8. **Full Grover measure ratio bound: mu(x)/x ≤ 1 for all x > 0 (C_Grover = 1)**
  9. Measure condition constant formula (C by definition) and positivity
  10. Integral constant positivity
  11. Runtime algebraic identity: 1/g_hat = (A1+1)/(2A1) * sqrt(NA2/d0)

  AXIOMATIZED (2 total):
  1. Paper's runtime bound (Roland-Cerf local adiabatic condition)
  2. Guo-An's runtime bound (JRS error functional)

  Reference: Extends "Unstructured Adiabatic Quantum Optimization"
  (Braida et al., 2025) and Guo-An (2025).
-/

import ScheduleOptimality.Basic
import ScheduleOptimality.Theorems
import ScheduleOptimality.PartialInfo
import ScheduleOptimality.StructuredInputs

namespace ScheduleOptimality

#check measure_condition_constant_formula
#check measure_condition_constant_pos
#check grover_measure_condition_constant
#check grover_sublevel_above_max
#check grover_ratio_above_max
#check grover_C_equals_one
#check runtime_recovery
#check rcOverhead
#check rcOverhead_ge_one
#check rcOverhead_eq_ratio_of_ge
#check jrs_overhead_exact
#check gShape_rel_exact
#check cLeftShape_rel_exact
#check c2_lt_i_iff
#check isingOpenChainN10
#check structuredC2OverI
#check grover_4_A1
#check grover_4_sStar
#check grover_4_cL
#check grover_4_gap_min
#check grover_4_gap_crossing

/-! ## Axiom Inventory

The following axioms are used beyond Lean's standard axioms:
1. `paper_runtime_bound`: Paper's p=2 runtime (from Roland-Cerf local adiabatic analysis)
2. `guoan_runtime_bound`: Guo-An's p=3/2 runtime (from JRS error functional framework)

Total: 2 axioms. These encode physics results from external papers (Roland-Cerf 2002,
Jansen-Ruskai-Seiler 2007) that cannot be proven from first principles in this formalization.

Previously axiomatized results now proven:
- `runtime_recovery`: Algebraic identity 1/g_hat = (A1+1)/(2A1) * sqrt(NA2/d0)
  (proven via field_simp + Real.sqrt_mul cancellation)
- `grover_C_equals_one`: Full measure ratio bound mu(x)/x ≤ 1 for Grover
  (proven via case split + the key inequality x^2 ≤ 1 for x ∈ [0,1])
-/

#print axioms grover_measure_condition_constant  -- axiom-free
#print axioms grover_C_equals_one                 -- axiom-free (now a theorem)
#print axioms runtime_recovery                    -- axiom-free
#print axioms grover_4_gap_crossing               -- axiom-free

end ScheduleOptimality
