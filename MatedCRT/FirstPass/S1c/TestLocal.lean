import HarmonicBalls.Defs.Laplacian
import Mathlib.Analysis.InnerProductSpace.Laplacian
import MatedCRT.LPStaging.Analysis.LaplacianCalculus

/-!
# Local facts about the Laplacian of test functions (Lemma 1 analytic layer)

Classical calculus, no paper-specific input: the Laplacian `Laplacian.laplacian` (the class field used by
`HarmonicBalls.LaplacianLE`, instance of `InnerProductSpace.Laplacian`) of a `C²` function on `ℂ` is continuous,
and it vanishes where the function vanishes near the point. These are the two properties used when `LaplacianLE`
tests are approximated by a countable family (`HarmonicBalls.IsTestFunction` has compact support inside the ball).
-/

namespace MatedCRT

open Set Filter Topology

/-- The Laplacian of a `C²` function on the complex plane is continuous. -/
theorem continuous_laplacian_of_contDiff {φ : ℂ → ℝ} (h : ContDiff ℝ 2 φ) :
    Continuous (Laplacian.laplacian φ) :=
  LatticeProb.LaplacianCalculus.continuous_laplacian_of_contDiff h

/-- The Laplacian of a function vanishing near `x` vanishes at `x`. -/
theorem laplacian_eq_zero_of_eventually_zero {φ : ℂ → ℝ} {x : ℂ} (h : φ =ᶠ[𝓝 x] 0) :
    Laplacian.laplacian φ x = 0 := by
  have h2 := (InnerProductSpace.laplacian_congr_nhds h).eq_of_nhds
  rw [h2]
  simp [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]

/-- The Laplacian of a test function supported in `U` vanishes outside `U`. -/
theorem laplacian_eq_zero_of_not_mem_tsupport {φ : ℂ → ℝ} {U : Set ℂ} (hφ : tsupport φ ⊆ U) {x : ℂ}
    (hx : x ∉ U) : Laplacian.laplacian φ x = 0 := by
  apply laplacian_eq_zero_of_eventually_zero
  exact notMem_tsupport_iff_eventuallyEq.1 fun h => hx (hφ h)

end MatedCRT
