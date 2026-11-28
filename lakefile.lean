import Lake
open Lake DSL

package «idla-mated-crt» where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

-- The LQG vocabulary and the harmonic-ball results of Bou-Rabee-Gwynne (arXiv:2208.11795), which this paper cites.
require «harmonic-balls-lqg» from "../Harmonic-Balls-LQG"

-- The lean-v4.35 line of Lattice-Probability (LQG, GFF and mated-CRT library adapted from Leonardo Bonanno's lean-formalizations).
require «lattice-probability» from git
  "https://github.com/nitromannitol/Lattice-Probability.git" @ "d6a62a31b05650082b76dfa6d43f9602023dd948"

@[default_target]
lean_lib «MatedCRT» where
  globs := #[.andSubmodules `MatedCRT]

/-- The comparator pair `MatedCRTAudit/MainTheorems/` (Theorems 1.4 and 1.6 at the canonical model).
Not a default target: it builds only on demand (`lake build MatedCRTAudit`); the challenge elaborates
with its intentional `sorry`s. -/
lean_lib MatedCRTAudit where
  globs := #[.submodules `MatedCRTAudit]
