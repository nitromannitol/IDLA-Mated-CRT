import MatedCRT.Proofs.Sec4.SubsequentialConvergence.PreparedCompactnessHolder
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.CorrectedPreparedCompactness
import MatedCRT.Proofs.Sec4.SubsequentialProperties.PreparedInputs

/-! Prepared odometer compactness using the corrected Dirichlet input. -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric

/-- The deterministic thinning provides relative compactness and Hölder limits
on one event, using the estimates cited in the proof of Lemma 4.6. -/
def OdometerPreparedCompactnessWithoutDirichletStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  EquiboundedStmt 𝒮 → DiscreteLaplacianBoundCorrectedStmt 𝒮 →
  DiscretePotentialTightnessPreparedStmt 𝒮 →
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ t : ℝ, 0 < t → ∀ e : ℕ → ℝ, (∀ n, 0 < e n) → Tendsto e atTop (𝓝 0) →
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂S.P,
    OdometerPreparedCompactness S ρ t (e ∘ φ) ω

/-- The prepared compactness step follows from median scaling and the cited
exit-time, volume growth, and discrete Hölder estimates. -/
theorem odometerPreparedCompactnessWithoutDirichletStep_of_exit_and_holder
    (𝒮 : SpaceFillingSLEModel) (hm : MepsScalingInput 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hH : DiscreteHolderContinuityCorrectedStep 𝒮)
    (h37 : ConvergenceNormalizedExitTimeStmt 𝒮) (h217 : BoundedExitTimeRVStmt)
    (h27 : VolumeGrowthStmt) : OdometerPreparedCompactnessWithoutDirichletStep 𝒮 := by
  intro h47 h44 h31 γ hγ hγ' ρ hρ hρ' Ω _ S hS t ht e he he0
  obtain ⟨φ, hφ, hboundary⟩ := odometer_prepared_holder_uniform_fixed_time
    𝒮 hm h47 h44 h218 hH h37 h217 h27 hγ hγ' hρ hρ' S hS t ht e he he0
  obtain ⟨θ, hθ, hlocal⟩ := odometerPreparedLocalCompactnessStep_of_mepsScaling 𝒮 hm
    h47 h44 h31 γ hγ hγ' ρ hρ hρ' Ω S hS t ht
    (e ∘ φ) (fun n => he _) (he0.comp hφ.tendsto_atTop)
  refine ⟨φ ∘ θ, hφ.comp hθ, ?_⟩
  filter_upwards [hboundary, hlocal] with ω hboundary hlocal
  apply odometerPreparedCompactness_of_holder_subsequences
  intro ψ hψ
  obtain ⟨κ, hκ, w, hw⟩ := hlocal ψ hψ
  obtain ⟨hh, hc⟩ := hboundary (θ ∘ ψ ∘ κ) (hθ.comp (hψ.comp hκ)) w hw
  obtain ⟨C, χ, hχ, hχ1, hhold⟩ := hh
  exact ⟨κ, hκ, (ball 0 ρ).indicator w, hhold.continuousOn hχ,
    ⟨C, χ, hχ, hχ1, hhold⟩, hc⟩

/-- The corrected prepared odometer convergence follows from the cited
estimates and the projected Dirichlet statement. -/
theorem subsequentialConvergencePrepared_of_corrected_estimates
    (𝒮 : SpaceFillingSLEModel) (hm : MepsScalingInput 𝒮)
    (h47 : EquiboundedStmt 𝒮) (h44 : DiscreteLaplacianBoundCorrectedStmt 𝒮)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮) (h35 : DiscreteDirichletProblemCorrectedStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hH : DiscreteHolderContinuityCorrectedStep 𝒮)
    (h217 : BoundedExitTimeRVStmt) (h27 : VolumeGrowthStmt) :
    SubsequentialConvergencePreparedStmt 𝒮 := by
  have h31 := discretePotentialTightnessPrepared_of_inputs hm h217 h218 hH
  have h37 := convergenceNormalizedExitTime_of_corrected_prepared_estimates 𝒮 hm h33 h35 h217 h218 hH
  have hc := odometerPreparedCompactnessWithoutDirichletStep_of_exit_and_holder 𝒮 hm h218 hH h37 h217 h27
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS t ht e he he0
  obtain ⟨φ, hφ, hcompact⟩ := hc h47 h44 h31 γ hγ hγ2 ρ hρ hρ1 Ω S hS t ht e he he0
  refine ⟨φ, hφ, hcompact, ?_⟩
  exact odometerPreparedSelectionStep 𝒮 γ hγ hγ2 ρ hρ hρ1 Ω S hS t ht
    (e ∘ φ) (fun n => he _) (he0.comp hφ.tendsto_atTop) hcompact

/-- Prepared every-limit properties, conditional on their identification step,
using the projected Dirichlet statement. -/
theorem subsequentialPropertiesPrepared_of_corrected_estimates
    (𝒮 : SpaceFillingSLEModel) (hm : MepsScalingInput 𝒮)
    (h47 : EquiboundedStmt 𝒮) (h44 : DiscreteLaplacianBoundCorrectedStmt 𝒮)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮) (h35 : DiscreteDirichletProblemCorrectedStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hH : DiscreteHolderContinuityCorrectedStep 𝒮)
    (h217 : BoundedExitTimeRVStmt) (h27 : VolumeGrowthStmt)
    (hid : OdometerPropertiesPreparedIdentificationStep 𝒮) :
    SubsequentialPropertiesPreparedStmt 𝒮 :=
  subsequentialPropertiesPrepared_of_steps 𝒮
    (subsequentialConvergencePrepared_of_corrected_estimates 𝒮 hm h47 h44 h33 h35 h218 hH h217 h27) hid

end MatedCRT

#print axioms MatedCRT.subsequentialConvergencePrepared_of_corrected_estimates
#print axioms MatedCRT.subsequentialPropertiesPrepared_of_corrected_estimates
