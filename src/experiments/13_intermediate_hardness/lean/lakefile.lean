import Lake
open Lake DSL

package "IntermediateHardness" where

@[default_target]
lean_lib IntermediateHardness where
  globs := #[.submodules `IntermediateHardness]
