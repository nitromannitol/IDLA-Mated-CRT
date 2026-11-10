import MatedCRT.FirstPass.Frozen.S1c
import MatedCRT.LPStaging.Prob.AnalyticUniversalMeasurable

/-!
# Bridge: analytic subsets of Polish spaces are null-measurable

`MatedCRT.FrozenUniversalMeasurabilityOfAnalytic` (FirstPass/Frozen/S1c.lean) asserts that, for every Polish
space `X` with its Borel σ-algebra and every finite Borel measure `ν`, each analytic subset of `X` is
`ν`-null-measurable (Lusin; Kechris, Thm 21.10). It follows from the general statement
`LatticeProb.AnalyticSet.nullMeasurableSet` (finite measures on metrizable Hausdorff spaces), since a Polish
space is metrizable, Hausdorff and carries the Borel σ-algebra.
-/

namespace MatedCRT

open MeasureTheory

theorem frozenUniversalMeasurabilityOfAnalytic_holds : FrozenUniversalMeasurabilityOfAnalytic := by
  intro X _ _ _ _ ν hν A hA
  exact LatticeProb.AnalyticSet.nullMeasurableSet ν hA

end MatedCRT
