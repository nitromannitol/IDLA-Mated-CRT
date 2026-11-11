import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.CorrectedHarmonicInputs
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.CorrectedConeScaling

/-! Prepared odometer subsequences using corrected harmonic convergence. -/

namespace MatedCRT

open _root_.HarmonicBalls

/-- Prepared Lemma 4.6 from corrected harmonic convergence and the discrete
estimates, with the deterministic thinning in the corrected quantifier order. -/
theorem subsequentialConvergencePrepared_of_corrected_harmonic_estimates
    (𝒮 : SpaceFillingSLEModel) (hm : MepsScalingInput 𝒮)
    (h210 : DegreeMeasureConvergenceStmt 𝒮) (h34 : IntegralConvergenceGreenFunctionStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hH : DiscreteHolderContinuityCorrectedStep 𝒮)
    (h27 : VolumeGrowthStmt) (hfinite : FiniteDomainDirichletRepresentation)
    (h36 : CorrectedHarmonicConvergenceStmt 𝒮) : SubsequentialConvergencePreparedStmt 𝒮 := by
  have h217 := boundedExitTimeRV_of_steps h27
  have h33 := uniformConvergenceGreenKernel_of_prepared_inputs 𝒮 h210 h34 h214 h28 hm h217 h218 hH
  have h35 := discreteDirichletProblemCorrected_of_corrected_harmonic_estimates 𝒮 h27 hm h210 h34
    h214 h28 h218 hH hfinite h36
  exact subsequentialConvergencePrepared_of_corrected_estimates 𝒮 hm
    (equibounded_of_inputs h27 h218 hm) (discreteLaplacianBoundCorrected 𝒮)
    h33 h35 h218 hH h217 h27

/-- Prepared Lemma 4.8 from corrected harmonic convergence and the discrete
estimates; the distributional identification uses the proved projection
stability of the hat Dirichlet problems. -/
theorem subsequentialPropertiesPrepared_of_corrected_harmonic_estimates
    (𝒮 : SpaceFillingSLEModel) (hm : MepsScalingInput 𝒮)
    (h210 : DegreeMeasureConvergenceStmt 𝒮) (h34 : IntegralConvergenceGreenFunctionStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hH : DiscreteHolderContinuityCorrectedStep 𝒮)
    (h27 : VolumeGrowthStmt) (hfinite : FiniteDomainDirichletRepresentation)
    (h36 : CorrectedHarmonicConvergenceStmt 𝒮) : SubsequentialPropertiesPreparedStmt 𝒮 := by
  have h217 := boundedExitTimeRV_of_steps h27
  have h33 := uniformConvergenceGreenKernel_of_prepared_inputs 𝒮 h210 h34 h214 h28 hm h217 h218 hH
  have h35 := discreteDirichletProblemCorrected_of_corrected_harmonic_estimates 𝒮 h27 hm h210 h34
    h214 h28 h218 hH hfinite h36
  have h37 := convergenceNormalizedExitTime_of_corrected_prepared_estimates 𝒮 hm h33 h35 h217 h218 hH
  have hid := odometerPropertiesPreparedIdentificationStep_of_projection_stability 𝒮 h33 h35 h37
    (maximumPrinciple_of_steps (adjacentCellsMeetAeStep 𝒮)) h28 (hatDirichletProjectionStabilityStep 𝒮)
  exact subsequentialPropertiesPrepared_of_corrected_estimates 𝒮 hm
    (equibounded_of_inputs h27 h218 hm) (discreteLaplacianBoundCorrected 𝒮)
    h33 h35 h218 hH h217 h27 hid

end MatedCRT

#print axioms MatedCRT.subsequentialConvergencePrepared_of_corrected_harmonic_estimates
#print axioms MatedCRT.subsequentialPropertiesPrepared_of_corrected_harmonic_estimates
