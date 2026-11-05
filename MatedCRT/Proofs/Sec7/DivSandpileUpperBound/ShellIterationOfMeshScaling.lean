import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.LocalizedShellIterationOfScaling
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.LocalSourceCover
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.ConditionalMeasurableCover
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.ComponentReduction

/-! Shell iteration from mesh scaling.
The shell iteration is adapted from the work of Leonardo Bonanno. -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric _root_.HarmonicBalls

/-- The logarithmic shell iteration follows from mesh scaling; the exit event
need not be assumed measurable. -/
theorem shellIteration_of_meshScaling
    (𝒮 : SpaceFillingSLEModel) (hscale : MepsScalingInput 𝒮) :
    ShellIterationStep 𝒮 := by
  intro _ hlower hvolume hmass hconv hgreen hcell hodo hadj
    γ hγ hγ' ρ hρ hρ' Ω _ S hS Λ hΛ δ t hδ _ ht
  obtain ⟨ζ, ω₀, hζ, hζ1, hω, hωd, hlocal⟩ := Sec7.localized_shell_iteration_of_scaling
    𝒮 hconv hgreen hscale hlower hvolume hmass hcell hodo hadj
    γ hγ hγ' ρ hρ hρ' Ω S hS Λ hΛ δ t hδ ht
  refine ⟨ζ, ω₀, hζ, hζ1, hω, hωd, ?_⟩
  let G : ℕ → Set Ω := fun n => {ω | ball (0 : ℂ) (1 / ((n : ℝ) + 2)) ⊆
    interior (closure (cluster (S.μ ω) ρ 0 t))}
  obtain ⟨hmono, hmeas, hcover, hsub⟩ := Sec7.exists_localCluster_source_ball_cover
    hγ hγ' hS hvolume hρ hρ' ht Λ hΛ
  let : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  apply Sec7.tendsToOneOn_of_ae_measurable_cover S.P _ G _ hmono hmeas hcover
  intro n
  have hn := hlocal n
  unfold TendsToOneOn at hn ⊢
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hn
    (Eventually.of_forall fun _ => zero_le) ?_
  apply Eventually.of_forall
  intro ε
  apply measure_mono_ae
  filter_upwards [hsub] with ω hω hbad
  exact ⟨⟨hbad.1.1, hω n hbad.1.1 hbad.1.2⟩, hbad.2⟩

/-- Proposition 7.1 from the corrected mass and logarithmic survival inputs and
the external mesh-scaling input. -/
theorem divSandpileUpperBound_of_meshScaling
    (𝒮 : SpaceFillingSLEModel) (hscale : MepsScalingInput 𝒮)
    (hcone : ConeHarmonicBallsStmt) (hlower : ConstantOrderLowerBoundDivLogStmt 𝒮)
    (hvolume : VolumeGrowthStmt) (hmass : MassBoundOdometerAboveScaleStmt 𝒮)
    (hconv : ConvergenceDivisibleStmt 𝒮) (hgreen : UniformConvergenceGreenKernelStmt 𝒮)
    (hcell : CellSizeEstimateStmt 𝒮) (hodo : OdometerBoundMassStmt 𝒮)
    (hcrude : CrudeUpperBoundStmt 𝒮) : DivSandpileUpperBoundStmt 𝒮 :=
  divSandpileUpperBound_of_shellIteration 𝒮 hcone hlower hvolume hmass hconv hgreen hcell hodo hcrude
    (shellIteration_of_meshScaling 𝒮 hscale)

end MatedCRT
