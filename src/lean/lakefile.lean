import Lake
open Lake DSL

package «UAQO» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «UAQO» where
  globs := #[.submodules `UAQO]
