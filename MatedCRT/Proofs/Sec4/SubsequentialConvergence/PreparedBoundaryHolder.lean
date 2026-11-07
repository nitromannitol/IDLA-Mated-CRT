import MatedCRT.Proofs.Sec4.SubsequentialConvergence.PreparedExitBarrier
import MatedCRT.Proofs.Sec4.SubsequentialConvergence.ExitPotentialHolder
import MatedCRT.Steps.Sec4.SubsequentialConvergence
import MatedCRT.Proofs.Sec4.SubsequentialConvergence.LocalToBoundary

/-! Quantitative boundary decay of prepared odometer limits. -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric
open scoped NNReal

/-- The exit-time barrier gives all local odometer limits along one prepared
sequence a common Hölder rate of decay to zero at the boundary. -/
theorem odometer_prepared_boundary_holder_of_normalized_exit
    (𝒮 : SpaceFillingSLEModel) (h37 : ConvergenceNormalizedExitTimeStmt 𝒮)
    (h217 : BoundedExitTimeRVStmt) (h27 : VolumeGrowthStmt)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (e : ℕ → ℝ) (he : ∀ n, 0 < e n) (he0 : Tendsto e atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂S.P,
      ∃ C χ : ℝ≥0, 0 < χ ∧ χ ≤ 1 ∧
      ∀ t : ℝ, 0 < t → ∀ ψ : ℕ → ℕ, StrictMono ψ → ∀ w : ℂ → ℝ,
        OdometerLocalLimit S ρ t (e ∘ φ ∘ ψ) ω w →
        ∀ x ∈ ball 0 ρ, ∀ y ∈ sphere 0 ρ,
          |w x| ≤ C * dist x y ^ (χ : ℝ) := by
  let R := (ρ + 1) / 2
  have hR : 0 < R := by dsimp [R]; linarith
  have hR1 : R < 1 := by dsimp [R]; linarith
  have hρR : ρ ≤ R := by dsimp [R]; linarith
  obtain ⟨q, hq, hconv⟩ := normalizedExitTime_limit_holder_of_volumeGrowth
    𝒮 h37 h217 h27 hγ hγ2 hR hR1 S hS hρ (ball_subset_ball hρR)
  obtain ⟨φ, hφ, hφae⟩ := exists_ae_uniform_subsequence_random S.P (closedBall 0 ρ)
    (fun ε ω => rescale (S.mε ε) ε (S.η ω)
      (normExitTime (S.mult ε ω) (ballInterior ε (S.η ω) ρ))) q hconv e he he0
  refine ⟨φ, hφ, ?_⟩
  filter_upwards [hq, hφae, ae_abs_rescaledOdometer_le_rescaled_normExitTime
    𝒮 hγ hγ2 hρ hρ1 S hS,
    normalizedExitGreenPotential_ae_boundary_holder_of_volumeGrowth
      𝒮 h27 hγ hγ2 hR1 S hS hρ (ball_subset_ball hρR)] with ω hq hconv hbar hholder
  obtain ⟨C, χ, hχ, hχ1, hdecay⟩ := hholder
  refine ⟨C, χ, hχ, hχ1, ?_⟩
  intro t ht ψ hψ w hw x hx y hy
  have hK : closure ({x} : Set ℂ) ⊆ ball 0 ρ := by
    simpa only [isClosed_singleton.closure_eq, singleton_subset_iff] using hx
  have hwlim := ((hw.2 {x} isCompact_singleton hK).tendsto_at (mem_singleton x)).abs
  have hqlim := ((hconv.tendsto_at (ball_subset_closedBall hx)).comp hψ.tendsto_atTop).abs
  have hle : |w x| ≤ |q ω x| := by
    apply le_of_tendsto_of_tendsto' hwlim hqlim
    intro n
    exact hbar t (e (φ (ψ n))) ht (he _) x
  rw [hq.2 (ball_subset_closedBall hx)] at hle
  exact hle.trans (hdecay x (ball_subset_closedBall hx) y hy)

/-- One deterministic thinning gives both closed-ball uniform convergence
and a common quantitative boundary decay for all local odometer limits. -/
theorem odometer_prepared_continuous_uniform_boundary_holder
    (𝒮 : SpaceFillingSLEModel) (h37 : ConvergenceNormalizedExitTimeStmt 𝒮)
    (h217 : BoundedExitTimeRVStmt) (h27 : VolumeGrowthStmt)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (e : ℕ → ℝ) (he : ∀ n, 0 < e n) (he0 : Tendsto e atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂S.P,
      ∃ C χ : ℝ≥0, 0 < χ ∧ χ ≤ 1 ∧
      ∀ t : ℝ, 0 < t → ∀ ψ : ℕ → ℕ, StrictMono ψ → ∀ w : ℂ → ℝ,
        OdometerLocalLimit S ρ t (e ∘ φ ∘ ψ) ω w →
        ContinuousOn ((ball 0 ρ).indicator w) (closedBall 0 ρ) ∧
        TendstoUniformlyOn
          (fun n => rescaledMatedLeastSupersolution S ρ t (e (φ (ψ n))) ω)
          ((ball 0 ρ).indicator w) atTop (closedBall 0 ρ) ∧
        ∀ x ∈ ball 0 ρ, ∀ y ∈ sphere 0 ρ,
          |w x| ≤ C * dist x y ^ (χ : ℝ) := by
  obtain ⟨φ, hφ, hcontinuous⟩ := odometer_prepared_continuous_uniform_of_normalized_exit
    𝒮 h37 hγ hγ2 hρ hρ1 S hS e he he0
  obtain ⟨θ, hθ, hboundary⟩ := odometer_prepared_boundary_holder_of_normalized_exit
    𝒮 h37 h217 h27 hγ hγ2 hρ hρ1 S hS (e ∘ φ) (fun n => he _)
      (he0.comp hφ.tendsto_atTop)
  refine ⟨φ ∘ θ, hφ.comp hθ, ?_⟩
  filter_upwards [hcontinuous, hboundary] with ω hc hb
  obtain ⟨C, χ, hχ, hχ1, hb⟩ := hb
  refine ⟨C, χ, hχ, hχ1, ?_⟩
  intro t ht ψ hψ w hw
  exact ⟨(hc t ht (θ ∘ ψ) (hθ.comp hψ) w hw).1,
    (hc t ht (θ ∘ ψ) (hθ.comp hψ) w hw).2, hb t ht ψ hψ w hw⟩

end MatedCRT
