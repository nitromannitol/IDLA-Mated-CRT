import MatedCRT.FirstPass.Derived.ConeConfigReconstructionProof
import MatedCRT.FirstPass.Derived.PlanarBMConePoints.Holds

/-!
# The reconstruction of the local configurations from the triple-point input alone

The cone-point input `PlanarBMNoTwoSidedConePoints` (Le Gall) holds (`planarBMNoTwoSidedConePoints`), so the
reconstruction of the local configurations of the two quantum cones from the outer data and the residues
(`ConeConfigReconstruction`) follows from the statement on the triple points alone:

* `coneConfigReconstruction_of_peanosphereTriplePoints`: from `CorrelatedBMPeanosphereTriplePointsNoContinuum`
  (the triple points of every Peanosphere curve of almost every correlated Brownian pair contain no continuum);
* `coneConfigReconstruction_of_triplePoints`: from `CorrelatedBMTraversalTriplePointsNoContinuum`.
-/

set_option autoImplicit false

namespace MatedCRT

/-- **`ConeConfigReconstruction` from the triple points of the Peanosphere curves.** -/
theorem coneConfigReconstruction_of_peanosphereTriplePoints
    (hT : GMS310Transfer.CorrelatedBMPeanosphereTriplePointsNoContinuum) (γ : ℝ) :
    ConeConfigReconstruction γ :=
  coneConfigReconstruction_of_peanosphere planarBMNoTwoSidedConePoints hT γ

/-- **`ConeConfigReconstruction` from the triple points of the space-filling SLE traversal.** -/
theorem coneConfigReconstruction_of_triplePoints (hA : CorrelatedBMTraversalTriplePointsNoContinuum) (γ : ℝ) :
    ConeConfigReconstruction γ :=
  coneConfigReconstruction_of_literature planarBMNoTwoSidedConePoints hA γ

end MatedCRT
