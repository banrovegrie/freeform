/-
  Verification file for all proofs.

  Imports all proof modules to verify they compile correctly.
-/

-- Mathlib bridges
import UAQO.Proofs.Mathlib.FinsetArithmetic

-- Foundations proofs
import UAQO.Proofs.Foundations.VariationalPrinciple

-- Spectral proofs
import UAQO.Proofs.Spectral.A2Bounds
import UAQO.Proofs.Spectral.ShermanMorrison

-- Adiabatic proofs
import UAQO.Proofs.Adiabatic.ScheduleProperties

-- Complexity proofs
import UAQO.Proofs.Complexity.SATSemantics
import UAQO.Proofs.Complexity.ModifiedHamDeg
import UAQO.Proofs.Complexity.BetaModifiedHam
import UAQO.Proofs.Complexity.LagrangeInterp

namespace UAQO.Proofs

/-- Summary of axioms that have been proved (with sorry markers where needed). -/
def provedAxioms : List String := [
  "satisfies_iff_countUnsatisfied_zero (SATSemantics.lean) - COMPLETE",
  "A2_lower_bound (A2Bounds.lean) - COMPLETE",
  "modifiedHam_deg_sum (ModifiedHamDeg.lean) - partial",
  "modifiedHam_deg_count (ModifiedHamDeg.lean) - partial",
  "betaModifiedHam_deg_sum (BetaModifiedHam.lean) - partial",
  "betaModifiedHam_deg_count (BetaModifiedHam.lean) - partial",
  "betaModifiedHam_eigenval_ordered (BetaModifiedHam.lean) - partial",
  "betaModifiedHam_eigenval_ordered_strict (BetaModifiedHam.lean) - partial",
  "betaModifiedHam_eigenval_bounds (BetaModifiedHam.lean) - partial",
  "variational_principle (VariationalPrinciple.lean) - partial",
  "variational_minimum (VariationalPrinciple.lean) - partial",
  "avoidedCrossing_bound (ScheduleProperties.lean) - partial",
  "piecewiseSchedule_monotone (ScheduleProperties.lean) - partial",
  "shermanMorrison_resolvent (ShermanMorrison.lean) - partial",
  "lagrange_interpolation (LagrangeInterp.lean) - partial"
]

/-- Axioms that remain as axioms (external foundations). -/
def externalAxioms : List String := [
  "threeSAT_in_NP (Cook-Levin theorem)",
  "threeSAT_NP_complete (Cook-Levin theorem)",
  "sharpThreeSAT_in_SharpP (Valiant's theorem)",
  "sharpThreeSAT_complete (Valiant's theorem)",
  "sharpP_solves_NP (Oracle complexity)",
  "degeneracy_sharpP_hard (Reduction proof)",
  "adiabaticTheorem (Quantum dynamics)",
  "eigenpath_traversal (Quantum dynamics)",
  "resolvent_distance_to_spectrum (Infinite-dim spectral theory)"
]

end UAQO.Proofs
