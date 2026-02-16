import Lake
open Lake DSL

package QHProofs where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib QHProofs where
  srcDir := "."

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.27.0"
