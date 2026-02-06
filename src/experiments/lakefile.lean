import Lake
open Lake DSL

package Experiments where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib HedgingTheorem where
  srcDir := "02_robust_schedules/lean"
  globs := #[.one `HedgingTheorem, .submodules `HedgingTheorem]

lean_lib SeparationTheorem where
  srcDir := "04_separation_theorem/lean"
  globs := #[.one `SeparationTheorem, .submodules `SeparationTheorem]

lean_lib AdaptiveSchedules where
  srcDir := "05_adaptive_schedules/lean"
  globs := #[.one `AdaptiveSchedules, .submodules `AdaptiveSchedules]

lean_lib MeasureCondition where
  srcDir := "06_measure_condition/lean"
  globs := #[.one `MeasureCondition, .submodules `MeasureCondition]

lean_lib PartialInformation where
  srcDir := "07_partial_information/lean"
  globs := #[.one `PartialInformation, .submodules `PartialInformation]

lean_lib InformationTheoretic where
  srcDir := "10_information_theoretic/lean"
  globs := #[.one `InformationTheoretic, .submodules `InformationTheoretic]
