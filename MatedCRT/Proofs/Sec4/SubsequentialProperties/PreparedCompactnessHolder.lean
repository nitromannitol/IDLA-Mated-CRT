import MatedCRT.Proofs.Sec4.SubsequentialConvergence.PreparedCompactnessHolder
import MatedCRT.Steps.Sec4.SubsequentialPropertiesPrepared

/-! Prepared odometer properties using the Hölder compactness route. -/

namespace MatedCRT

/-- Corrected Lemma 4.8 follows from the prepared every-limit identification
and the cited estimates used for prepared Hölder compactness. -/
theorem subsequentialPropertiesPrepared_of_exit_and_holder
    (𝒮 : SpaceFillingSLEModel) (hm : MepsScalingInput 𝒮)
    (h47 : EquiboundedStmt 𝒮) (h44 : DiscreteLaplacianBoundCorrectedStmt 𝒮)
    (h31 : DiscretePotentialTightnessPreparedStmt 𝒮) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hH : DiscreteHolderContinuityCorrectedStep 𝒮)
    (h37 : ConvergenceNormalizedExitTimeStmt 𝒮) (h217 : BoundedExitTimeRVStmt)
    (h27 : VolumeGrowthStmt) (hid : OdometerPropertiesPreparedIdentificationStep 𝒮) :
    SubsequentialPropertiesPreparedStmt 𝒮 :=
  subsequentialPropertiesPrepared_of_steps 𝒮
    (subsequentialConvergencePrepared_of_exit_and_holder 𝒮 hm h47 h44 h31 h35
      h218 hH h37 h217 h27) hid

end MatedCRT
