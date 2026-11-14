import MatedCRT.Defs.RandomWalk

/-!
# Simple random walk trajectory law

The deterministic-start walk law is the Ionescu–Tulcea trajectory measure
with the corresponding Dirac initial distribution.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace MatedCRT

/-- The paper's walk law is the trajectory measure started at a fixed vertex. -/
theorem srwLaw_eq_trajMeasure (m : ℤ → ℤ → ℕ) (a : ℤ) :
    srwLaw m a = Kernel.trajMeasure (Measure.dirac a) (srwHistoryKernel m) := by
  unfold srwLaw Kernel.trajMeasure
  rw [Measure.map_dirac' (by fun_prop), Measure.dirac_bind (Kernel.measurable _)]
  rfl

end MatedCRT
