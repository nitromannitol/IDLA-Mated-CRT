import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.ProjectedPointwise
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.PreparedExitBoundaryProof

/-! Corrected Dirichlet and divisible-sandpile convergence from Green and
corrected harmonic inputs. -/

namespace MatedCRT

open _root_.HarmonicBalls

/-- Corrected Lemma 3.5 follows from corrected harmonic convergence, Green
convergence, finite-domain representation, and the displayed estimates. -/
theorem discreteDirichletProblemCorrected_of_corrected_harmonic
    (𝒮 : SpaceFillingSLEModel) (h27 : VolumeGrowthStmt) (hm : MepsScalingInput 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hH : DiscreteHolderContinuityCorrectedStep 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (hfinite : FiniteDomainDirichletRepresentation)
    (h36 : CorrectedHarmonicConvergenceStmt 𝒮) (h34 : IntegralConvergenceGreenFunctionStmt 𝒮)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮) (h31 : DiscretePotentialTightnessPreparedStmt 𝒮) :
    DiscreteDirichletProblemCorrectedStmt 𝒮 :=
  discreteDirichletProblemCorrected_of_green_and_prepared 𝒮 h27 hm h218 hH h28 hfinite
    (projectedDirichletPointwiseStep_of_corrected_harmonic 𝒮 hfinite h36 h34 hm) h34 h33 h31

/-- Divisible-sandpile convergence with corrected harmonic convergence in
place of the projected Dirichlet pointwise obligation. -/
theorem convergenceDivisible_of_corrected_harmonic
    (𝒮 : SpaceFillingSLEModel) (hm : MepsScalingInput 𝒮)
    (h210 : DegreeMeasureConvergenceStmt 𝒮) (h34 : IntegralConvergenceGreenFunctionStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hH : DiscreteHolderContinuityCorrectedStep 𝒮)
    (h27 : VolumeGrowthStmt) (hcone : ConeEnvironmentScalingStep 𝒮)
    (hfinite : FiniteDomainDirichletRepresentation) (h36 : CorrectedHarmonicConvergenceStmt 𝒮)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮) (h31 : DiscretePotentialTightnessPreparedStmt 𝒮) :
    ConvergenceDivisibleStmt 𝒮 :=
  convergenceDivisible_of_green_and_prepared_exit_boundary 𝒮 hm h210 h34 h214 h28 h218 hH
    h27 hcone hfinite (projectedDirichletPointwiseStep_of_corrected_harmonic 𝒮 hfinite h36 h34 hm)
    h33 h31

end MatedCRT

#print axioms MatedCRT.discreteDirichletProblemCorrected_of_corrected_harmonic
#print axioms MatedCRT.convergenceDivisible_of_corrected_harmonic
