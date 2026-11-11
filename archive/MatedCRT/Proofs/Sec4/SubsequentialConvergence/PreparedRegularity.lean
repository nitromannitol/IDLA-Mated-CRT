import MatedCRT.Proofs.Sec4.SubsequentialConvergence.OdometerInteriorHolder
import MatedCRT.Proofs.Sec4.SubsequentialConvergence.PreparedBoundaryHolder

/-! Interior regularity and boundary decay on a common prepared sequence. -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric
open scoped NNReal

/-- For each fixed time, a single deterministic preparation gives every local
odometer limit along every further subsequence interior Hölder regularity,
continuous uniform convergence on the closed ball, and a common power-law
boundary decay. -/
theorem odometer_prepared_interior_holder_and_boundary_decay
    (𝒮 : SpaceFillingSLEModel) (hm : MepsScalingInput 𝒮)
    (h47 : EquiboundedStmt 𝒮) (h44 : DiscreteLaplacianBoundCorrectedStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hH : DiscreteHolderContinuityCorrectedStep 𝒮)
    (h37 : ConvergenceNormalizedExitTimeStmt 𝒮) (h217 : BoundedExitTimeRVStmt)
    (h27 : VolumeGrowthStmt)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (t : ℝ) (ht : 0 < t) (e : ℕ → ℝ) (he : ∀ n, 0 < e n)
    (he0 : Tendsto e atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂S.P,
      ∃ C χ : ℝ≥0, 0 < χ ∧ χ ≤ 1 ∧
      ∀ ψ : ℕ → ℕ, StrictMono ψ → ∀ w : ℂ → ℝ,
        OdometerLocalLimit S ρ t (e ∘ φ ∘ ψ) ω w →
        (∀ K : Set ℂ, IsCompact K → K ⊆ ball 0 ρ → IsHolderContinuousOn w K) ∧
        ContinuousOn ((ball 0 ρ).indicator w) (closedBall 0 ρ) ∧
        TendstoUniformlyOn
          (fun n => rescaledMatedLeastSupersolution S ρ t (e (φ (ψ n))) ω)
          ((ball 0 ρ).indicator w) atTop (closedBall 0 ρ) ∧
        ∀ x ∈ ball 0 ρ, ∀ y ∈ sphere 0 ρ,
          |w x| ≤ C * dist x y ^ (χ : ℝ) := by
  obtain ⟨φ, hφ, hinterior⟩ := odometer_prepared_local_holder
    𝒮 hm h47 h44 h218 hH h27 hγ hγ2 hρ hρ1 S hS t ht e he he0
  obtain ⟨θ, hθ, hboundary⟩ := odometer_prepared_continuous_uniform_boundary_holder
    𝒮 h37 h217 h27 hγ hγ2 hρ hρ1 S hS (e ∘ φ) (fun n => he _)
      (he0.comp hφ.tendsto_atTop)
  refine ⟨φ ∘ θ, hφ.comp hθ, ?_⟩
  filter_upwards [hinterior, hboundary] with ω hi hb
  obtain ⟨C, χ, hχ, hχ1, hb⟩ := hb
  refine ⟨C, χ, hχ, hχ1, ?_⟩
  intro ψ hψ w hw
  exact ⟨hi (θ ∘ ψ) (hθ.comp hψ) w hw, hb t ht ψ hψ w hw⟩

end MatedCRT
