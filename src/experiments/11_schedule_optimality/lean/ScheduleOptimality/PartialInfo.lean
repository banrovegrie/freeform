/-
  Partial-information schedule comparison lemmas for Experiment 11.

  This file formalizes the algebraic core used in Proposition I:
  - exact JRS overhead identity under parameter uncertainty
  - basic RC overhead properties for max(1, eps/delta)
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace ScheduleOptimality

/-- RC overhead model used in Proposition I. -/
noncomputable def rcOverhead (eps delta : Real) : Real :=
  max 1 (eps / delta)

/-- JRS overhead model used in Proposition I. -/
noncomputable def jrsOverhead (deltaCOverC deltaGOverG : Real) : Real :=
  ((1 + deltaCOverC) ^ 2) / (1 - deltaGOverG)

/-- Shape factor for g_mod(A): proportional to A/(A+1). -/
noncomputable def gShape (A : Real) : Real := A / (A + 1)

/-- Shape factor for C_left(A): proportional to 1/(A(A+1)). -/
noncomputable def cLeftShape (A : Real) : Real := 1 / (A * (A + 1))

/-- RC overhead is always at least 1. -/
theorem rcOverhead_ge_one (eps delta : Real) : rcOverhead eps delta >= 1 := by
  unfold rcOverhead
  exact le_max_left 1 (eps / delta)

/-- If eps >= delta > 0, RC overhead is exactly eps/delta. -/
theorem rcOverhead_eq_ratio_of_ge
    (eps delta : Real)
    (hdelta : delta > 0)
    (heps : eps >= delta) :
    rcOverhead eps delta = eps / delta := by
  unfold rcOverhead
  apply max_eq_right
  have hdiv : eps / delta >= 1 := by
    have : eps >= delta * 1 := by simpa using heps
    have hdiv' : eps / delta >= (delta * 1) / delta :=
      div_le_div_of_nonneg_right this (le_of_lt hdelta)
    simpa [hdelta.ne'] using hdiv'
  exact hdiv

/-- Exact JRS overhead identity used in Proposition I. -/
theorem jrs_overhead_exact
    (C gmin deltaC deltaG : Real)
    (hC : Ne C 0)
    (hg : Ne gmin 0)
    (hgm : Ne (gmin - deltaG) 0) :
    (((C + deltaC) ^ 2) / (gmin - deltaG)) / (C ^ 2 / gmin)
      = ((1 + deltaC / C) ^ 2) / (1 - deltaG / gmin) := by
  field_simp [hC, hg, hgm]

/-- Useful reparameterization with relative errors a = deltaC/C, b = deltaG/gmin. -/
theorem jrs_overhead_reparam
    (a b : Real) :
    jrsOverhead a b = (1 + 2 * a + a ^ 2) / (1 - b) := by
  unfold jrsOverhead
  ring_nf

/-- Exact relative-variation identity for A/(A+1). -/
theorem gShape_rel_exact
    (A e : Real)
    (hA : Ne A 0)
    (hAe1 : Ne (A + e + 1) 0) :
    gShape (A + e) / gShape A - 1 = e / (A * (A + e + 1)) := by
  unfold gShape
  field_simp [hA, hAe1]
  ring

/-- Exact relative-variation identity for 1/(A(A+1)). -/
theorem cLeftShape_rel_exact
    (A e : Real)
    (_hA : Ne A 0)
    (_hA1 : Ne (A + 1) 0)
    (hAe : Ne (A + e) 0)
    (hAe1 : Ne (A + e + 1) 0) :
    cLeftShape (A + e) / cLeftShape A - 1
      = -(((2 * A + 1) * e + e ^ 2) / ((A + e) * (A + e + 1))) := by
  unfold cLeftShape
  field_simp [hAe, hAe1]
  ring

/-- Exact algebraic criterion used in Theorem E for comparing C^2 and I. -/
theorem c2_lt_i_iff
    (a r cL : Real) :
    (a + r) ^ 2 < a + r ^ 2 * cL ↔
      (cL - 1) * r ^ 2 - 2 * a * r + a * (1 - a) > 0 := by
  have hEq :
      (a + r ^ 2 * cL) - (a + r) ^ 2
        = (cL - 1) * r ^ 2 - 2 * a * r + a * (1 - a) := by
    ring
  constructor
  · intro h
    have h' : 0 < (a + r ^ 2 * cL) - (a + r) ^ 2 := sub_pos.mpr h
    simpa [hEq] using h'
  · intro h
    have h' : 0 < (a + r ^ 2 * cL) - (a + r) ^ 2 := by
      simpa [hEq] using h
    exact sub_pos.mp h'

#check rcOverhead
#check rcOverhead_ge_one
#check rcOverhead_eq_ratio_of_ge
#check jrs_overhead_exact
#check jrs_overhead_reparam
#check gShape_rel_exact
#check cLeftShape_rel_exact
#check c2_lt_i_iff

end ScheduleOptimality
