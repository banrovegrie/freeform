import Lake
open Lake DSL

package «MeasureCondition» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «MeasureCondition» where
  globs := #[.submodules `MeasureCondition]
