import Lake
open Lake DSL

package «quartic_invariant» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «QuarticInvariant» where
  srcDir := "."
