import MatedCRT.Defs.Notation
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
# Countable dense families of Hölder tests (E-c2-9)

On a compact set `K` the continuous real functions form a second countable space in the sup norm. Hence,
for fixed Hölder constants, the Hölder functions form a subset with a countable dense subset consisting
of Hölder functions. This is the countable family of test functions used in E-c2-9 (GAPS-SEC3.md) to
approximate an environment-dependent Hölder test, once it has been extended to the closed ball.
-/

namespace MatedCRT

open Metric Set
open scoped NNReal

/-- **Countable dense family of Hölder tests.** For a compact `K ⊆ ℂ` and fixed Hölder constants `C, χ`,
there is a countable family `D` of `(C, χ)`-Hölder continuous functions on `K` such that every
`(C, χ)`-Hölder function `F` on `K` is approximated in sup norm, to any accuracy `δ > 0`, by a member of `D`. -/
theorem exists_countable_holderWith_dense (K : Set ℂ) [CompactSpace K] (C χ : ℝ≥0) :
    ∃ D : Set C(K, ℝ), D.Countable ∧ (∀ G ∈ D, HolderWith C χ G) ∧
      ∀ F : C(K, ℝ), HolderWith C χ F → ∀ δ : ℝ, 0 < δ → ∃ G ∈ D, dist F G < δ := by
  set H : Set C(K, ℝ) := {F | HolderWith C χ ⇑F} with hH
  obtain ⟨t, htH, htc, hdense⟩ := TopologicalSpace.exists_countable_dense_subset H
  refine ⟨t, htH, fun G hG => htc hG, fun F hF δ hδ => ?_⟩
  have hFcl : F ∈ closure t := hdense (show F ∈ H from hF)
  exact Metric.mem_closure_iff.1 hFcl δ hδ

end MatedCRT
