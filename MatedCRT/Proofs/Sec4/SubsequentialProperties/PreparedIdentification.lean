import MatedCRT.Proofs.Sec4.SubsequentialProperties.Final
import MatedCRT.Proofs.Sec4.SubsequentialProperties.PreparedInputs
import MatedCRT.Steps.Sec2.MaximumPrinciple

/-! Prepared every-limit identification from the existing distributional proof. -/

namespace MatedCRT

/-- The deterministic subsequence in Lemma 4.8 can be chosen uniformly over
positive times, and therefore also supplies the prepared fixed-time version. -/
theorem odometerPropertiesPreparedIdentificationStep_of_subsequentialProperties
    (𝒮 : SpaceFillingSLEModel) (h48 : SubsequentialPropertiesStmt 𝒮) :
    OdometerPropertiesPreparedIdentificationStep 𝒮 := by
  intro γ hγ hγ' ρ hρ hρ' Ω _ S hS t ht e he he0
  obtain ⟨φ, hφ, hφae⟩ := h48 γ hγ hγ' ρ hρ hρ' Ω S hS e he he0
  refine ⟨φ, hφ, ?_⟩
  filter_upwards [hφae] with ω hω
  exact hω t ht

/-- Prepared every-limit identification from Green-kernel convergence,
the discrete Dirichlet problem, normalized exit-time convergence and the
discrete maximum principle. -/
theorem odometerPropertiesPreparedIdentificationStep_of_inputs
    (𝒮 : SpaceFillingSLEModel) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (h35 : DiscreteDirichletProblemStmt 𝒮) (h37 : ConvergenceNormalizedExitTimeStmt 𝒮)
    (h213 : MaximumPrincipleStmt 𝒮) : OdometerPropertiesPreparedIdentificationStep 𝒮 :=
  odometerPropertiesPreparedIdentificationStep_of_subsequentialProperties 𝒮
    (subsequentialProperties_of_inputs 𝒮 h33 h35 h37 h213)

/-- Prepared Lemma 4.8 from the Green-kernel, Dirichlet, exit-time and
Hölder estimates, without a separate identification hypothesis. -/
theorem subsequentialPropertiesPrepared_of_identified_estimates
    (𝒮 : SpaceFillingSLEModel) (hm : MepsScalingInput 𝒮)
    (h47 : EquiboundedStmt 𝒮) (h44 : DiscreteLaplacianBoundCorrectedStmt 𝒮)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hH : DiscreteHolderContinuityCorrectedStep 𝒮)
    (h217 : BoundedExitTimeRVStmt) (h27 : VolumeGrowthStmt) :
    SubsequentialPropertiesPreparedStmt 𝒮 := by
  have h37 := convergenceNormalizedExitTime_of_prepared_estimates 𝒮 hm h33 h35 h217 h218 hH
  have h213 : MaximumPrincipleStmt 𝒮 := maximumPrinciple_of_steps (adjacentCellsMeetAeStep 𝒮)
  exact subsequentialPropertiesPrepared_of_green_and_estimates 𝒮 hm h47 h44 h33 h35
    h218 hH h217 h27 (odometerPropertiesPreparedIdentificationStep_of_inputs 𝒮 h33 h35 h37 h213)

end MatedCRT

#print axioms MatedCRT.odometerPropertiesPreparedIdentificationStep_of_inputs
#print axioms MatedCRT.subsequentialPropertiesPrepared_of_identified_estimates
