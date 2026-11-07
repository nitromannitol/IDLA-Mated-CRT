import MatedCRT.Proofs.Sec4.SubsequentialConvergence.PreparedInteriorHolder
import MatedCRT.Proofs.Sec4.SubsequentialConvergence.PreparedDataBounds
import MatedCRT.Steps.Sec4.SubsequentialConvergence
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.AeTightnessCompactness

/-! Compact-interior Hölder regularity of prepared odometer limits. -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric
open scoped NNReal

/-- Every local odometer limit along a further subsequence is Hölder on each
compact subset of the ball, on one common almost-sure event. -/
theorem odometer_prepared_local_holder_of_polyScales
    (𝒮 : SpaceFillingSLEModel) (hm : MepsScalingInput 𝒮)
    (h47 : EquiboundedStmt 𝒮) (h44 : DiscreteLaplacianBoundCorrectedStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hH : DiscreteHolderContinuityCorrectedStep 𝒮)
    (h27 : VolumeGrowthStmt)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (t : ℝ) (ht : 0 < t) (e : ℕ → ℝ) (he : IsPolySummableScales e) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂S.P,
      ∀ ψ : ℕ → ℕ, StrictMono ψ → ∀ w : ℂ → ℝ,
      OdometerLocalLimit S ρ t (e ∘ φ ∘ ψ) ω w →
      ∀ K : Set ℂ, IsCompact K → K ⊆ ball 0 ρ → IsHolderContinuousOn w K := by
  obtain ⟨φ, hφ, hb⟩ := odometerPreparedDataBoundsStep_of_mepsScaling 𝒮 hm
    h47 h44 γ hγ hγ2 ρ hρ hρ1 Ω S hS t ht e he.1 he.tendsto_zero
  refine ⟨φ, hφ, ?_⟩
  filter_upwards [hb, ae_holderOn_rescale_limit_of_prepared_estimates
    𝒮 hm h218 hH h27 hγ hγ2 hρ hρ1 S hS e he] with ω hb hreg
  obtain ⟨C, hC, hb⟩ := hb
  intro ψ hψ w hw K hK hKD
  have hb' := hψ.tendsto_atTop.eventually hb
  have hconv : ∀ x ∈ K, Tendsto
      (fun n => rescale (S.mε (e (φ (ψ n)))) (e (φ (ψ n))) (S.η ω)
        (matedLeastSupersolution (S.mult (e (φ (ψ n))) ω) (e (φ (ψ n))) (S.η ω) ρ t) x)
      atTop (𝓝 (w x)) := by
    intro x hx
    exact (hw.2 K hK (by simpa only [hK.isClosed.closure_eq] using hKD)).tendsto_at hx
  exact hreg (φ ∘ ψ) (hφ.comp hψ)
    (fun n => matedLeastSupersolution (S.mult (e (φ (ψ n))) ω) (e (φ (ψ n))) (S.η ω) ρ t)
    ⟨C, hC.le⟩ (ball 0 ρ) K w isOpen_ball (Subset.rfl) hK hKD hb' hconv

/-- Every deterministic vanishing mesh sequence admits a deterministic
preparation on which all local odometer limits are locally Hölder. -/
theorem odometer_prepared_local_holder
    (𝒮 : SpaceFillingSLEModel) (hm : MepsScalingInput 𝒮)
    (h47 : EquiboundedStmt 𝒮) (h44 : DiscreteLaplacianBoundCorrectedStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hH : DiscreteHolderContinuityCorrectedStep 𝒮)
    (h27 : VolumeGrowthStmt)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (t : ℝ) (ht : 0 < t) (e : ℕ → ℝ) (he : ∀ n, 0 < e n)
    (he0 : Tendsto e atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂S.P,
      ∀ ψ : ℕ → ℕ, StrictMono ψ → ∀ w : ℂ → ℝ,
      OdometerLocalLimit S ρ t (e ∘ φ ∘ ψ) ω w →
      ∀ K : Set ℂ, IsCompact K → K ⊆ ball 0 ρ → IsHolderContinuousOn w K := by
  obtain ⟨κ, hκ, hκe⟩ := extraction_forall_of_eventually
    (P := fun n k => 0 < e k ∧ e k < (1 / 2 : ℝ) ^ n) fun n => by
      filter_upwards [he0.eventually (gt_mem_nhds (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n))] with k hk
      exact ⟨he k, hk⟩
  have hpoly : IsPolySummableScales (e ∘ κ) := isPolySummableScales_of_lt_half_pow hκe
  obtain ⟨φ, hφ, hreg⟩ := odometer_prepared_local_holder_of_polyScales
    𝒮 hm h47 h44 h218 hH h27 hγ hγ2 hρ hρ1 S hS t ht (e ∘ κ) hpoly
  refine ⟨κ ∘ φ, hκ.comp hφ, ?_⟩
  exact hreg

end MatedCRT
