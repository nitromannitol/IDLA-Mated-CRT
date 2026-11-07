import MatedCRT.Proofs.Sec4.SubsequentialProperties.PreparedCompactnessHolder
import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.PreparedBoundaryProof

/-! Prepared odometer compactness and properties from the discrete estimates. -/

namespace MatedCRT

/-- Corrected Lemma 4.6 from the exit-time, Hölder, and odometer estimates,
with the prepared potential-tightness hypothesis discharged. -/
theorem subsequentialConvergencePrepared_of_estimates
    (𝒮 : SpaceFillingSLEModel) (hm : MepsScalingInput 𝒮)
    (h47 : EquiboundedStmt 𝒮) (h44 : DiscreteLaplacianBoundCorrectedStmt 𝒮)
    (h35 : DiscreteDirichletProblemStmt 𝒮) (h218 : ExitTimeUpperBoundStmt 𝒮)
    (hH : DiscreteHolderContinuityCorrectedStep 𝒮)
    (h37 : ConvergenceNormalizedExitTimeStmt 𝒮) (h217 : BoundedExitTimeRVStmt)
    (h27 : VolumeGrowthStmt) : SubsequentialConvergencePreparedStmt 𝒮 :=
  subsequentialConvergencePrepared_of_exit_and_holder 𝒮 hm h47 h44
    (discretePotentialTightnessPrepared_of_inputs hm h217 h218 hH) h35 h218 hH h37 h217 h27

/-- Corrected Lemma 4.8 from the same estimates and the prepared
every-limit identification. -/
theorem subsequentialPropertiesPrepared_of_estimates
    (𝒮 : SpaceFillingSLEModel) (hm : MepsScalingInput 𝒮)
    (h47 : EquiboundedStmt 𝒮) (h44 : DiscreteLaplacianBoundCorrectedStmt 𝒮)
    (h35 : DiscreteDirichletProblemStmt 𝒮) (h218 : ExitTimeUpperBoundStmt 𝒮)
    (hH : DiscreteHolderContinuityCorrectedStep 𝒮)
    (h37 : ConvergenceNormalizedExitTimeStmt 𝒮) (h217 : BoundedExitTimeRVStmt)
    (h27 : VolumeGrowthStmt) (hid : OdometerPropertiesPreparedIdentificationStep 𝒮) :
    SubsequentialPropertiesPreparedStmt 𝒮 :=
  subsequentialPropertiesPrepared_of_steps 𝒮
    (subsequentialConvergencePrepared_of_estimates 𝒮 hm h47 h44 h35 h218 hH h37 h217 h27) hid

end MatedCRT

#print axioms MatedCRT.subsequentialConvergencePrepared_of_estimates
#print axioms MatedCRT.subsequentialPropertiesPrepared_of_estimates
