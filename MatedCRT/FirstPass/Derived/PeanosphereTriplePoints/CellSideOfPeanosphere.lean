import MatedCRT.FirstPass.Derived.MatingOfTreesCellSideInputsProof
import MatedCRT.FirstPass.Derived.ZeroConeEdgeCountCodeProof

/-!
# The cell-side identity from the triple points of Peanosphere curves

The cell-side identity (`MatingOfTreesCellSideIdentity`) and the absence of continua among the triple points of the
curve of a valid environment (`ValidEnvTriplePointsNoContinuum`) follow from
`CorrelatedBMPeanosphereTriplePointsNoContinuum` (for almost every correlated Brownian pair, the triple points of every
Peanosphere curve of the pair contain no continuum of positive diameter) in place of
`CorrelatedBMTraversalTriplePointsNoContinuum`: the proofs of `validEnvTriplePointsNoContinuum` and
`matingOfTreesCellSideIdentity_of_literature` (`MatingOfTreesCellSideInputsProof.lean`) use the latter only through
the former (`ae_forall_peanosphere_not_containsNondegenerateContinuum`).

## Main statements

* `MatedCRT.validEnvTriplePointsNoContinuum_of_peanosphere`
* `MatedCRT.matingOfTreesCellSideIdentity_of_peanosphere`
-/

set_option autoImplicit false

open MeasureTheory

namespace MatedCRT

/-- **The triple points of the curve of a valid environment contain no continuum**, from
`CorrelatedBMPeanosphereTriplePointsNoContinuum`. In a valid environment the curve is almost surely a Peanosphere
curve of the boundary-length pair `S.bm` (`MatedCRTEnv.IsValid.exists_curve_peanosphere`), whose law is the correlated
Brownian law (coupling field `boundaryLawBM`). -/
theorem validEnvTriplePointsNoContinuum_of_peanosphere {𝒮 : SpaceFillingSLEModel}
    (hT : GMS310Transfer.CorrelatedBMPeanosphereTriplePointsNoContinuum) : ValidEnvTriplePointsNoContinuum 𝒮 := by
  intro γ hγ0 hγ2 Ω _ S hS
  obtain ⟨ηc, hηc, hP, -⟩ := MatedCRTEnv.IsValid.exists_curve_peanosphere S hS
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hC, -⟩ := hS.matingOfTrees
  have hbm : AEMeasurable S.bm S.P := hC.measurable_curves.2.2.2.aemeasurable
  have hT' := ae_of_ae_map hbm (hT γ hγ0 hγ2 _ hC.boundaryLawBM)
  filter_upwards [hηc, hP, hT'] with ω hηω hPω hTω
  rw [← hηω]
  exact hTω _ hPω

/-- **The multiplicities of the mated-CRT map are the frontier-side multiplicities of the cells**
(`MatingOfTreesCellSideIdentity`), from `PlanarBMNoTwoSidedConePoints` (Le Gall) and
`CorrelatedBMPeanosphereTriplePointsNoContinuum`. -/
theorem matingOfTreesCellSideIdentity_of_peanosphere {𝒮 : SpaceFillingSLEModel}
    (hLG : PlanarBMNoTwoSidedConePoints) (hT : GMS310Transfer.CorrelatedBMPeanosphereTriplePointsNoContinuum) :
    MatingOfTreesCellSideIdentity 𝒮 :=
  matingOfTreesCellSideIdentity_of_valid (correlatedBMNoCommonLocalMin hLG)
    (validEnvTriplePointsNoContinuum_of_peanosphere hT)

end MatedCRT
