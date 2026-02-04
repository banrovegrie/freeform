import Lake
open Lake DSL

package «HedgingTheorem» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «HedgingTheorem» where
  globs := #[.one `HedgingTheorem, .submodules `HedgingTheorem]

lean_exe «hedgingtheorem» where
  root := `Main
