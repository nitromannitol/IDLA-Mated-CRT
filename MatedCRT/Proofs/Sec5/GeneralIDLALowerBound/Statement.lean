import MatedCRT.Proofs.Sec5.GeneralIDLALowerBound.SiteBound
import MatedCRT.Proofs.Sec5.GeneralIDLALowerBound.VisitCount
import MatedCRT.Proofs.Sec5.GeneralIDLALowerBound.GreenHitting
import MatedCRT.Proofs.Sec5.GeneralIDLALowerBound.LateVisitStep
import MatedCRT.Proofs.Sec5.GeneralIDLALowerBound.CellCount

/-!
# Lemma 5.2 from the two annealed steps

All quenched steps of Lemma 5.2 are proved (`greenHittingStep`, `missedSiteVisitStep`, `visitCountLowerTailStep`,
`lateVisitUpperTailStep`, hence `QuenchedSiteBoundStep`). What remains are the two annealed steps: `CellCountStep 𝒮`
(`|V^ε(B_ρ)| ≤ ε^{-2}` with probability tending to `1`, paper line 2155), proved from Lemmas 2.7
and 2.8 in CellCount.lean, and `EnvSigmaMeasurableStep 𝒮` (the environment is measurable for the σ-algebra of `Ω`;
a modeling hypothesis.
-/

namespace MatedCRT

/-- **Lemma 5.2** from `CellCountStep` and `EnvSigmaMeasurableStep`. -/
theorem generalIDLALowerBound_of_annealedSteps (𝒮 : SpaceFillingSLEModel) (hC : CellCountStep 𝒮)
    (hM : EnvSigmaMeasurableStep 𝒮) : GeneralIDLALowerBoundStmt 𝒮 :=
  generalIDLALowerBound_of_steps 𝒮 greenHittingStep
    (quenchedSiteBound_of_steps missedSiteVisitStep visitCountLowerTailStep lateVisitUpperTailStep) hC hM

/-- **Lemma 5.2** from Lemma 2.7 (`VolumeGrowthStmt`, BG20 Lemma A.1), Lemma 2.8 (`CellSizeEstimateStmt`, BG20
Lemma 2.4) and the measurability of the environment (`EnvSigmaMeasurableStep`. -/
theorem generalIDLALowerBound_of_inputs (𝒮 : SpaceFillingSLEModel) (h27 : VolumeGrowthStmt)
    (h28 : CellSizeEstimateStmt 𝒮) (hM : EnvSigmaMeasurableStep 𝒮) : GeneralIDLALowerBoundStmt 𝒮 :=
  generalIDLALowerBound_of_annealedSteps 𝒮 (cellCountStep 𝒮 h27 h28) hM

end MatedCRT
