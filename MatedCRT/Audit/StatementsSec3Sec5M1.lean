import MatedCRT.Proofs.Measurability.EnvSigma
import MatedCRT.Steps.Sec3.UniformConvergenceGreenKernel
import MatedCRT.Steps.Sec3.DiscreteDirichletProblem
import MatedCRT.Steps.Sec3.ConvergenceHarmonicFunctions
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.OfInteriorBoundary
import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.Main
import MatedCRT.Proofs.Sec5.LLowerBound.OfInputs
import MatedCRT.Proofs.Sec5.MeanValueInequality.NormalizedStep

/-! A logical check for the quantifier-order issue in Lemma 5.3.
It does not assert that the actual Green-function estimate has this form. -/
namespace MatedCRT.Audit.StatementsSec3Sec5M1

/-- A witness chosen separately for each positive time need not be uniform in time. -/
theorem time_dependent_witness_not_uniform :
    (∀ t : ℝ, 0 < t → ∃ s : ℝ, 0 < s ∧ s < t) ∧
      ¬ (∃ s : ℝ, 0 < s ∧ ∀ t : ℝ, 0 < t → s < t) := by
  constructor
  · intro t ht
    exact ⟨t / 2, by linarith, by linarith⟩
  · rintro ⟨s, hs, h⟩
    have := h (s / 2) (by linarith)
    linarith

/-- The relaxed form of Lemma 5.2 really supplies the Draft statement. -/
theorem relaxed_five_two_implies_draft (𝒮 : SpaceFillingSLEModel)
    (h : GeneralIDLALowerBoundRelaxedStep 𝒮) : GeneralIDLALowerBoundStmt 𝒮 :=
  generalIDLALowerBound_of_relaxed 𝒮 h

/-- The available Lemma 3.1 reduction concludes its corrected form. -/
theorem three_one_corrected_reduction {𝒮 : SpaceFillingSLEModel}
    (hm : MepsScalingInput 𝒮) (h217 : BoundedExitTimeRVStmt)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (h32 : DiscreteHolderContinuityCorrectedStep 𝒮) :
    DiscretePotentialTightnessCorrectedStmt 𝒮 :=
  discretePotentialTightnessCorrected_of_boundedExitTime hm h217 h218 h32

/-- The available Lemma 3.3 reduction consumes the Draft Lemma 3.1. -/
theorem three_three_draft_reduction (𝒮 : SpaceFillingSLEModel)
    (h210 : DegreeMeasureConvergenceStmt 𝒮) (h34 : IntegralConvergenceGreenFunctionStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (h31 : DiscretePotentialTightnessStmt 𝒮) (h213 : MaximumPrincipleStmt 𝒮)
    (hi : GreenKernelInteriorStep 𝒮) (hb : GreenKernelBoundaryStep 𝒮) :
    UniformConvergenceGreenKernelStmt 𝒮 :=
  uniformConvergenceGreenKernel_of_steps 𝒮 h210 h34 h214 h28 h31 h213 hi hb

/-- The available Lemma 3.6 reduction concludes the Draft with two open steps. -/
theorem three_six_draft_reduction (𝒮 : SpaceFillingSLEModel)
    (h211 : RandomWalkToLBMStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (hp : HarmonicPathExitStep 𝒮) (hc : HarmonicExitCellStep 𝒮) :
    ConvergenceHarmonicFunctionsStmt 𝒮 :=
  convergenceHarmonicFunctions_of_steps 𝒮 h211 h28 hp hc

/-- The available Lemma 3.7 reduction consumes the Draft Lemma 3.1. -/
theorem three_seven_draft_reduction (𝒮 : SpaceFillingSLEModel)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮) (h29 : CountingMeasureConvergenceStmt 𝒮)
    (h219 : ExpectedExitTimeExplicitBoundStmt 𝒮) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (h31 : DiscretePotentialTightnessStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (h217 : BoundedExitTimeRVStmt) (hi : NormalizedExitInteriorStep 𝒮)
    (hb : DiscreteExitBoundaryStep 𝒮) : ConvergenceNormalizedExitTimeStmt 𝒮 :=
  convergenceNormalizedExitTime_of_interior_discrete_boundary 𝒮 h33 h29 h219 h35 h31 h28 h217 hi hb

/-- Proposition 5.1 retains the stopped and discrete inner-cluster steps. -/
theorem five_one_draft_reduction (𝒮 : SpaceFillingSLEModel) (h27 : VolumeGrowthStmt)
    (h28 : CellSizeEstimateStmt 𝒮) (h53 : MeanValueInequalityStmt 𝒮)
    (h54 : LLowerBoundStmt 𝒮) (hi : DiscreteClusterInnerBoundStep 𝒮)
    (hs : IDLALowerBoundStoppedStep 𝒮) : IDLALowerBoundStmt 𝒮 :=
  iDLALowerBound_of_volumeGrowth_cellSize 𝒮 h27 h28 h53 h54 hi hs

/-- Lemma 5.4 is reduced to three explicitly stated hypotheses. -/
theorem five_four_draft_reduction (𝒮 : SpaceFillingSLEModel)
    (h215 : GreenFunctionCrudeBoundStmt 𝒮) (h216 : GreenKernelLowerBoundStmt 𝒮)
    (h29 : CountingMeasureConvergenceStmt 𝒮) : LLowerBoundStmt 𝒮 :=
  lLowerBound_of_inputs 𝒮 h215 h216 h29

/-- Lemma 3.5 uses the corrected tightness statement. -/
theorem three_five_draft_reduction (𝒮 : SpaceFillingSLEModel)
    (hGP : HarmonicBalls.GreenPotentialHolderStmt.{0})
    (h36 : ConvergenceHarmonicFunctionsStmt 𝒮) (h34 : IntegralConvergenceGreenFunctionStmt 𝒮)
    (h31 : DiscretePotentialTightnessCorrectedStmt 𝒮) (h213 : MaximumPrincipleStmt 𝒮)
    (h219 : ExpectedExitTimeExplicitBoundStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (hl : DirichletLimitStep 𝒮) (hi : DirichletInteriorStep 𝒮) (hb : DirichletBoundaryStep 𝒮) :
    DiscreteDirichletProblemStmt 𝒮 :=
  discreteDirichletProblem_of_steps 𝒮 hGP h36 h34 h31 h213 h219 h28 hl hi hb

/-- Lemma 5.2 has a reduction with two hypotheses. -/
theorem five_two_draft_reduction (𝒮 : SpaceFillingSLEModel) (h27 : VolumeGrowthStmt)
    (h28 : CellSizeEstimateStmt 𝒮) : GeneralIDLALowerBoundStmt 𝒮 :=
  generalIDLALowerBound_of_volumeGrowth_cellSize 𝒮 h27 h28

/-- Lemma 5.3 uses a surplus step and corrected Lemma 4.4. -/
theorem five_three_draft_reduction (𝒮 : SpaceFillingSLEModel)
    (h44 : DiscreteLaplacianBoundCorrectedStmt 𝒮) (h213 : MaximumPrincipleStmt 𝒮)
    (h41 : ConvergenceDivisibleStmt 𝒮) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hs : MeanValueSurplusStep 𝒮) : MeanValueInequalityStmt 𝒮 :=
  meanValueInequality_of_surplus 𝒮 h44 h213 h41 h33 h218 hs

#print axioms three_five_draft_reduction
#print axioms five_two_draft_reduction
#print axioms five_three_draft_reduction
#print axioms three_one_corrected_reduction
#print axioms three_three_draft_reduction
#print axioms three_six_draft_reduction
#print axioms three_seven_draft_reduction
#print axioms five_one_draft_reduction
#print axioms five_four_draft_reduction
#print axioms time_dependent_witness_not_uniform
#print axioms relaxed_five_two_implies_draft

end MatedCRT.Audit.StatementsSec3Sec5M1
