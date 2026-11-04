import MatedCRT.Proofs.Sec5.GeneralIDLALowerBound.SiteBound
import MatedCRT.Proofs.Sec5.GeneralIDLALowerBound.VisitCount
import MatedCRT.Proofs.Sec5.GeneralIDLALowerBound.GreenHitting
import MatedCRT.Proofs.Sec5.GeneralIDLALowerBound.LateVisitStep

/-!
# Lemma 5.2 from the two annealed steps

All quenched steps of Lemma 5.2 are proved (`greenHittingStep`, `missedSiteVisitStep`, `visitCountLowerTailStep`,
`lateVisitUpperTailStep`, hence `QuenchedSiteBoundStep`). What remains are the two annealed steps: `CellCountStep 𝒮`
(`|V^ε(B_ρ)| ≤ ε^{-2}` with probability tending to `1`, paper line 2155; ESCALATIONS E-c2-2) and
`EnvSigmaMeasurableStep 𝒮` (the environment is measurable for the σ-algebra of `Ω`; ESCALATIONS E-c2-1).
-/

namespace MatedCRT

/-- **Lemma 5.2** from `CellCountStep` and `EnvSigmaMeasurableStep`. -/
theorem generalIDLALowerBound_of_annealedSteps (𝒮 : SpaceFillingSLEModel) (hC : CellCountStep 𝒮)
    (hM : EnvSigmaMeasurableStep 𝒮) : GeneralIDLALowerBoundStmt 𝒮 :=
  generalIDLALowerBound_of_steps 𝒮 greenHittingStep
    (quenchedSiteBound_of_steps missedSiteVisitStep visitCountLowerTailStep lateVisitUpperTailStep) hC hM

end MatedCRT
