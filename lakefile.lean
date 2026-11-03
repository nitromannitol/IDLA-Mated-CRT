import Lake
open Lake DSL

package «idla-mated-crt» where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

-- The LQG vocabulary and the harmonic-ball results of Bou-Rabee-Gwynne (arXiv:2208.11795), which this paper cites.
require «harmonic-balls-lqg» from "../Harmonic-Balls-LQG"

@[default_target]
lean_lib «MatedCRT» where
  globs := #[.andSubmodules `MatedCRT]
