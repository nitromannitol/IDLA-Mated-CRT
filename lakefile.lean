import Lake
open Lake DSL

package «idla-mated-crt» where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

-- The LQG vocabulary and the harmonic-ball results of Bou-Rabee-Gwynne (arXiv:2208.11795), which this paper cites.
require «harmonic-balls-lqg» from "../Harmonic-Balls-LQG"

-- The lean-v4.35 line of Lattice-Probability (LQG, GFF and mated-CRT library adapted from Leonardo Bonanno's lean-formalizations).
require «lattice-probability» from git
  "https://github.com/nitromannitol/Lattice-Probability.git" @ "f2f237e88c4487af2231dd0485373c790c7e08c9"

@[default_target]
lean_lib «MatedCRT» where
  globs := #[.andSubmodules `MatedCRT]
