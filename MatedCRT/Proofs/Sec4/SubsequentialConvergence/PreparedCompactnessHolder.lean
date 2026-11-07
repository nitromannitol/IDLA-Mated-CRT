import MatedCRT.Proofs.Sec4.SubsequentialConvergence.ClosedBallHolder
import MatedCRT.Proofs.Sec4.SubsequentialConvergence.PreparedBoundaryReduction

/-! Prepared odometer compactness from local compactness and Hölder estimates. -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric

/-- The prepared compactness step follows from median scaling and the cited
exit-time, volume growth, and discrete Hölder estimates. -/
theorem odometerPreparedCompactnessStep_of_exit_and_holder
    (𝒮 : SpaceFillingSLEModel) (hm : MepsScalingInput 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hH : DiscreteHolderContinuityCorrectedStep 𝒮)
    (h37 : ConvergenceNormalizedExitTimeStmt 𝒮) (h217 : BoundedExitTimeRVStmt)
    (h27 : VolumeGrowthStmt) : OdometerPreparedCompactnessStep 𝒮 := by
  intro h47 h44 h31 h35 γ hγ hγ' ρ hρ hρ' Ω _ S hS t ht e he he0
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

/-- Corrected Lemma 4.6, conditional on the cited estimates. -/
theorem subsequentialConvergencePrepared_of_exit_and_holder
    (𝒮 : SpaceFillingSLEModel) (hm : MepsScalingInput 𝒮)
    (h47 : EquiboundedStmt 𝒮) (h44 : DiscreteLaplacianBoundCorrectedStmt 𝒮)
    (h31 : DiscretePotentialTightnessPreparedStmt 𝒮) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hH : DiscreteHolderContinuityCorrectedStep 𝒮)
    (h37 : ConvergenceNormalizedExitTimeStmt 𝒮) (h217 : BoundedExitTimeRVStmt)
    (h27 : VolumeGrowthStmt) : SubsequentialConvergencePreparedStmt 𝒮 :=
  subsequentialConvergencePrepared_of_compactness 𝒮 h47 h44 h31 h35
    (odometerPreparedCompactnessStep_of_exit_and_holder 𝒮 hm h218 hH h37 h217 h27)

end MatedCRT
