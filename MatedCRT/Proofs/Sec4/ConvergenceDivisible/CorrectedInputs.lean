import MatedCRT.Proofs.Sec4.ConvergenceDivisible.ConeScalingPositivity
import MatedCRT.Proofs.Sec4.SubsequentialConvergence.Corrected
import MatedCRT.Proofs.Sec4.SubsequentialProperties.Corrected

/-!
# Theorem 4.1 from corrected subsequential reductions

This combines the corrected routes for Lemmas 4.6 and 4.8 with the cone-scaling
route for event measurability. The simultaneous compactness assumption remains
explicit (E-x3-2).
-/

namespace MatedCRT

/-- Theorem 4.1 from the corrected Lemma 3.1 and the remaining subsequential
steps. The corrected Lemma 4.4 is supplied by the subsequential reductions. -/
theorem convergenceDivisible_of_corrected_inputs (𝒮 : SpaceFillingSLEModel)
    (h27 : VolumeGrowthStmt) (hscale : ConeEnvironmentScalingStep 𝒮)
    (h47 : EquiboundedStmt 𝒮) (h31 : DiscretePotentialTightnessCorrectedStmt 𝒮)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (h37 : ConvergenceNormalizedExitTimeStmt 𝒮) (h213 : MaximumPrincipleStmt 𝒮)
    (hlocal : OdometerLocalCompactnessCorrectedStep 𝒮)
    (hboundary : OdometerBoundaryUpgradeCorrectedStep 𝒮)
    (hselect : OdometerMeasurableSelectionStep 𝒮)
    (hobs : OdometerObstacleApproximationStep 𝒮)
    (hlap : OdometerDistributionalLimitCorrectedStep 𝒮) : ConvergenceDivisibleStmt 𝒮 :=
  convergenceDivisible_of_scaling 𝒮
    (subsequentialProperties_of_corrected 𝒮 h33 h35 h37 h213 hobs hlap)
    (subsequentialConvergence_of_corrected 𝒮 h47 h31 h35 hlocal hboundary hselect)
    h27 hscale

/-- Theorem 4.1 with equiboundedness and corrected potential tightness reduced
to their inputs. -/
theorem convergenceDivisible_of_corrected_reductions (𝒮 : SpaceFillingSLEModel)
    (h27 : VolumeGrowthStmt) (hscale : ConeEnvironmentScalingStep 𝒮)
    (hm : MepsScalingInput 𝒮) (h218 : ExitTimeUpperBoundStmt 𝒮)
    (hH : DiscreteHolderContinuityCorrectedStep 𝒮)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (h37 : ConvergenceNormalizedExitTimeStmt 𝒮) (h213 : MaximumPrincipleStmt 𝒮)
    (hlocal : OdometerLocalCompactnessCorrectedStep 𝒮)
    (hboundary : OdometerBoundaryUpgradeCorrectedStep 𝒮)
    (hselect : OdometerMeasurableSelectionStep 𝒮)
    (hobs : OdometerObstacleApproximationStep 𝒮)
    (hlap : OdometerDistributionalLimitCorrectedStep 𝒮) : ConvergenceDivisibleStmt 𝒮 :=
  convergenceDivisible_of_corrected_inputs 𝒮 h27 hscale
    (equibounded_of_inputs h27 h218 hm)
    (discretePotentialTightnessCorrected_of_inputs hm h27 h218 hH)
    h33 h35 h37 h213 hlocal hboundary hselect hobs hlap

end MatedCRT
