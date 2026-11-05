import MatedCRT.Proofs.IDLA.JointDiscreteLowerBound
import MatedCRT.Proofs.Sec5.GeneralIDLALowerBound.Statement

/-!
# Proposition 5.1 from the inputs of Lemma 5.2

Lemma 5.2 in its relaxed form (`GeneralIDLALowerBoundRelaxedStep`, the hypotheses its proof uses) holds under the
inputs of `generalIDLALowerBound_of_inputs`: Lemma 2.7, Lemma 2.8 and the measurability of the environment
(`EnvSigmaMeasurableStep`, ESCALATIONS E-c2-1). Proposition 5.1 then needs Lemmas 5.3, 5.4, the discrete-cluster form
of Proposition 4.2 and the stopped step `IDLALowerBoundStoppedStep` (MatedCRT/Steps/Sec5/IDLALowerBound.lean).
-/

namespace MatedCRT

/-- **Lemma 5.2 (relaxed)** from Lemma 2.7, Lemma 2.8 and the measurability of the environment. -/
theorem generalIDLALowerBoundRelaxed_of_inputs (𝒮 : SpaceFillingSLEModel) (h27 : VolumeGrowthStmt)
    (h28 : CellSizeEstimateStmt 𝒮) (hM : EnvSigmaMeasurableStep 𝒮) : GeneralIDLALowerBoundRelaxedStep 𝒮 :=
  generalIDLALowerBoundRelaxed_of_steps 𝒮 greenHittingStep
    (quenchedSiteBound_of_steps missedSiteVisitStep visitCountLowerTailStep lateVisitUpperTailStep)
    (cellCountStep 𝒮 h27 h28) hM

/-- **Proposition 5.1** from Lemmas 2.7, 2.8, 5.3, 5.4, the measurability of the environment, the discrete-cluster
form of Proposition 4.2 and the stopped step. -/
theorem iDLALowerBound_of_inputs (𝒮 : SpaceFillingSLEModel) (h27 : VolumeGrowthStmt)
    (h28 : CellSizeEstimateStmt 𝒮) (hM : EnvSigmaMeasurableStep 𝒮) (h53 : MeanValueInequalityStmt 𝒮)
    (h54 : LLowerBoundStmt 𝒮) (hI : DiscreteClusterInnerBoundStep 𝒮) (hstop : IDLALowerBoundStoppedStep 𝒮) :
    IDLALowerBoundStmt 𝒮 :=
  iDLALowerBound_of_steps 𝒮 (generalIDLALowerBoundRelaxed_of_inputs 𝒮 h27 h28 hM) h53 h54 h28 hI hstop

end MatedCRT
