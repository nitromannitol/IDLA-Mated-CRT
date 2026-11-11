import MatedCRT.FirstPass.Frozen.S2g
import MatedCRT.FirstPass.Frozen.S5c
import MatedCRT.FirstPass.LPBridge.DistributionalLaplacian
import LatticeProb.Analysis.DistributionalLaplacian
import LatticeProb.Analysis.SuperharmonicMinimumPrinciple

/-!
# Bridge: the frozen minimum principles from the super-mean-value minimum principles

`FrozenSuperharmonicMinimumPrinciple` (FirstPass/Frozen/S2g.lean) and `FPStrongMinimumPrinciple`
(FirstPass/Frozen/S5c.lean) follow from the minimum principles of `LatticeProb.SuperMeanValueOn`
(Armitage and Gardiner, *Classical Potential Theory*, §3.2) once a continuous distributionally superharmonic function is
superharmonic in the sphere-average sense. That last step is `LatticeProb.superMeanValueOn_of_distribLaplacianLE`
(MatedCRT/LPStaging/Analysis/DistributionalLaplacian.lean).
-/

namespace MatedCRT

open MeasureTheory Set Filter Topology

/-- The frozen weak minimum principle for distributionally superharmonic functions. -/
theorem frozenSuperharmonicMinimumPrinciple_holds : FrozenSuperharmonicMinimumPrinciple := by
  intro U f hU hbdd hcont hL hfr
  have hsup : LatticeProb.SuperMeanValueOn f U :=
    LatticeProb.superMeanValueOn_of_distribLaplacianLE hU (hcont.mono subset_closure)
      ((laplacianLE_iff_distribLaplacianLE f 0 U).mp hL)
  exact LatticeProb.SuperMeanValueOn.minimum_principle_of_frontier hU hbdd hcont hsup hfr

/-- The frozen strong minimum principle for distributionally superharmonic functions. -/
theorem fpStrongMinimumPrinciple_holds : FPStrongMinimumPrinciple := by
  intro U f hU hconn hcont hL hnn x₀ hx₀ hzero
  have hsup : LatticeProb.SuperMeanValueOn f U :=
    LatticeProb.superMeanValueOn_of_distribLaplacianLE hU hcont
      ((laplacianLE_iff_distribLaplacianLE f 0 U).mp hL)
  exact LatticeProb.SuperMeanValueOn.strong_minimum_principle_of_nonneg hU hconn hcont hsup hnn hx₀ hzero

end MatedCRT
