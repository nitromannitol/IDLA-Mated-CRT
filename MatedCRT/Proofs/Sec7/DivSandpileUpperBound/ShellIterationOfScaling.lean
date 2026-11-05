import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.LocalizedShellIteration
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.ComponentReduction

/-! Shell iteration from mesh scaling and measurable exit events.
The shell iteration is adapted from the work of Leonardo Bonanno. -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric

/-- The logarithmic shell iteration follows from mesh scaling and
null-measurability of each relevant cluster exit event. -/
theorem shellIteration_of_scaling_and_measurable_exit
    (𝒮 : SpaceFillingSLEModel) (hscale : MepsScalingInput 𝒮)
    (hexit : ∀ (γ ρ t : ℝ), 0 < γ → γ < 2 → 0 < ρ → ρ < 1 → 0 < t →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
      NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ} S.P) :
    ShellIterationStep 𝒮 := by
  intro _ hlower hvolume hmass hconv hgreen hcell hodo hadj
    γ hγ hγ' ρ hρ hρ' Ω _ S hS Λ hΛ δ t hδ _ ht
  have hexit' := hexit γ ρ t hγ hγ' hρ hρ' ht Ω S hS Λ hΛ
  obtain ⟨ζ, ω₀, hζ, hζ1, hω, hωd, hlocal⟩ := Sec7.localized_shell_iteration
    𝒮 hconv hgreen hscale hlower hvolume hmass hcell hodo hadj
    γ hγ hγ' ρ hρ hρ' Ω S hS Λ hΛ δ t hδ ht hexit'
  refine ⟨ζ, ω₀, hζ, hζ1, hω, hωd, ?_⟩
  let G : ℕ → Set Ω := fun n => {ω | t < clusterExitTime (Λ ω) ρ ∧
    ball (0 : ℂ) (1 / ((n : ℝ) + 2)) ⊆ Λ ω t}
  obtain ⟨hmono, hmeas, hcover⟩ := Sec7.exists_beforeExit_source_ball_exhaustion
    hγ hγ' hS hvolume hρ hρ' ht Λ hΛ hexit'
  let : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  exact Sec7.tendsToOneOn_of_ae_subset_iUnion S.P _ G _ hmono hmeas hcover hlocal

/-- Proposition 7.1 with the corrected mass and logarithmic survival inputs,
assuming mesh scaling and null-measurable cluster exit events. -/
theorem divSandpileUpperBound_of_scaling_and_measurable_exit
    (𝒮 : SpaceFillingSLEModel) (hscale : MepsScalingInput 𝒮)
    (hexit : ∀ (γ ρ t : ℝ), 0 < γ → γ < 2 → 0 < ρ → ρ < 1 → 0 < t →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
      NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ} S.P)
    (hcone : ConeHarmonicBallsStmt) (hlower : ConstantOrderLowerBoundDivLogStmt 𝒮)
    (hvolume : VolumeGrowthStmt) (hmass : MassBoundOdometerAboveScaleStmt 𝒮)
    (hconv : ConvergenceDivisibleStmt 𝒮) (hgreen : UniformConvergenceGreenKernelStmt 𝒮)
    (hcell : CellSizeEstimateStmt 𝒮) (hodo : OdometerBoundMassStmt 𝒮)
    (hcrude : CrudeUpperBoundStmt 𝒮) : DivSandpileUpperBoundStmt 𝒮 :=
  divSandpileUpperBound_of_shellIteration 𝒮 hcone hlower hvolume hmass hconv hgreen hcell hodo hcrude
    (shellIteration_of_scaling_and_measurable_exit 𝒮 hscale hexit)

end MatedCRT
