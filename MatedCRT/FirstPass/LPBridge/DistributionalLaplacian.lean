import HarmonicBalls.Defs.Laplacian
import MatedCRT.LPStaging.Analysis.DistributionalLaplacian

/-!
# Bridge: the distributional Laplacian of HarmonicBalls and of the lattice-probability staging

`HarmonicBalls.LaplacianLE` (HarmonicBalls/Defs/Laplacian.lean) and `LatticeProb.DistribLaplacianLE`
(LPStaging/Analysis/DistributionalLaplacian.lean) have the same definition, so the two notions agree.
-/

namespace MatedCRT

open MeasureTheory

/-- The two distributional inequalities `Δf ≤ μ` on `U` coincide. -/
theorem laplacianLE_iff_distribLaplacianLE (f : ℂ → ℝ) (μ : Measure ℂ) (U : Set ℂ) :
    HarmonicBalls.LaplacianLE f μ U ↔ LatticeProb.DistribLaplacianLE f μ U :=
  Iff.rfl

end MatedCRT
