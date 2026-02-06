/-
  Information-Theoretic Limits: Formal Verification

  MAIN RESULT:
  The query complexity of ground state finding is Theta(sqrt(N/d_0)).
  This is achieved by Durr-Hoyer without spectral information.
  The A_1 barrier is model-specific, not information-theoretic.

  WHAT IS PROVEN (end-to-end):
  1. Uninformed runtime algebra: a * sqrt(a^2/d) = a^2/sqrt(d)
     Instantiated: 2^{n/2} * sqrt(2^n/d_0) = 2^n/sqrt(d_0)
     (This was the site of the CRITICAL bug: originally stated as 2^n/d_0)
  2. The old claim (a^2/d) is strictly weaker than correct (a^2/sqrt(d)) for d > 1
  3. Geometric series for Durr-Hoyer: 2 + sqrt(2) < 3.5
  4. Crossing position: s* = A_1/(A_1+1) in (0,1), monotone in A_1
  5. Grover N=4 sanity check: s* = 3/7
  6. Model separation structure (from axiomatized external results)

  WHAT IS AXIOMATIZED (from literature):
  1. BBBV lower bound: Omega(sqrt(N/d_0)) queries (Bennett et al. 1997)
  2. Durr-Hoyer upper bound: O(sqrt(N/d_0)) queries (1996)

  Reference: Experiment 10 of "Unstructured Adiabatic Quantum Optimization"
  thesis project.
-/

import InformationTheoretic.Basic

namespace InformationTheoretic

/-! ## Verified Claims -/

-- Part I: Uninformed Runtime Algebra
#check runtime_algebra_abstract      -- a * sqrt(a^2/d) = a^2/sqrt(d)
#check correct_bound_stronger        -- a^2/sqrt(d) > a^2/d for d > 1

-- Part II: Geometric Series
#check sqrt_two_lt_three_halves      -- sqrt(2) < 1.5
#check geometric_series_bound        -- 2 + sqrt(2) < 3.5

-- Part III: Crossing Position
#check crossingPosition              -- s* = A_1/(A_1+1)
#check crossing_derivative_positive  -- 1/(A_1+1)^2 > 0
#check crossing_in_unit_interval     -- 0 < s* < 1
#check grover_n4_crossing            -- s*(3/4) = 3/7
#check crossing_monotone             -- s* increasing in A_1

-- Part IV: Model Separation (axiomatized)
#check bbbv_lower_bound              -- Omega(sqrt(N/d_0))
#check durr_hoyer_upper_bound        -- O(sqrt(N/d_0))
#check main_theorem                  -- Theta(sqrt(N/d_0))
#check separation_gives_uninformed_bound  -- T_unf >= R * lb

end InformationTheoretic
