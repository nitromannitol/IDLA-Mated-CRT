import MatedCRT.Proofs.Sec4.SubsequentialConvergence.PreparedPairModulus
import MatedCRT.Proofs.Sec4.SubsequentialConvergence.OdometerInteriorHolder

/-! Separation-dependent interior estimates for prepared odometer limits. -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric
open scoped NNReal

/-- Along one deterministic preparation, all local odometer limits have a
common two-power interior modulus at radii below their boundary separation. -/
theorem odometer_prepared_pair_modulus_of_polyScales
    (𝒮 : SpaceFillingSLEModel) (hm : MepsScalingInput 𝒮)
    (h47 : EquiboundedStmt 𝒮) (h44 : DiscreteLaplacianBoundCorrectedStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hH : DiscreteHolderContinuityCorrectedStep 𝒮)
    (h27 : VolumeGrowthStmt)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (t : ℝ) (ht : 0 < t) (e : ℕ → ℝ) (he : IsPolySummableScales e) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂S.P,
      ∃ ξ A C₁ q Cm R₁ C : ℝ,
        0 < ξ ∧ 0 ≤ A ∧ 0 ≤ C₁ ∧ 0 < q ∧ 0 ≤ Cm ∧ 0 < R₁ ∧ 0 ≤ C ∧
        ∀ ψ : ℕ → ℕ, StrictMono ψ → ∀ w : ℂ → ℝ,
        OdometerLocalLimit S ρ t (e ∘ φ ∘ ψ) ω w →
        ∀ (x y : ℂ) (r0 : ℝ), 0 ≤ r0 → dist x 0 + r0 < ρ → dist y 0 + r0 < ρ →
        ∀ R : ℝ, 0 < R → R < min R₁ (min r0 1) →
        ‖x - y‖ ≤ ((R / 2) * (R / 2)) / 2 →
        |w x - w y| ≤ Cm * (A * C * (R / 2) ^ ξ + 2 * C * C₁ * R ^ q) := by
  obtain ⟨φ, hφ, hb⟩ := odometerPreparedDataBoundsStep_of_mepsScaling 𝒮 hm
    h47 h44 γ hγ hγ2 ρ hρ hρ1 Ω S hS t ht e he.1 he.tendsto_zero
  refine ⟨φ, hφ, ?_⟩
  filter_upwards [hb, ae_pair_modulus_of_prepared_estimates
    𝒮 hm h218 hH h27 hγ hγ2 hρ hρ1 S hS e he] with ω hb hreg
  obtain ⟨C, hC, hb⟩ := hb
  obtain ⟨ξ, A, C₁, q, Cm, R₁, hξ, hA, hC₁, hq, hCm, hR₁, hreg⟩ := hreg
  refine ⟨ξ, A, C₁, q, Cm, R₁, C, hξ, hA, hC₁, hq, hCm, hR₁, hC.le, ?_⟩
  intro ψ hψ w hw
  have hb' := hψ.tendsto_atTop.eventually hb
  have hconv : ∀ x ∈ ball (0 : ℂ) ρ, Tendsto
      (fun n => rescale (S.mε (e (φ (ψ n)))) (e (φ (ψ n))) (S.η ω)
        (matedLeastSupersolution (S.mult (e (φ (ψ n))) ω) (e (φ (ψ n))) (S.η ω) ρ t) x)
      atTop (𝓝 (w x)) := by
    intro x hx
    exact (hw.2 {x} isCompact_singleton (by simpa using hx)).tendsto_at (mem_singleton x)
  exact hreg (φ ∘ ψ) (hφ.comp hψ)
    (fun n => matedLeastSupersolution (S.mult (e (φ (ψ n))) ω) (e (φ (ψ n))) (S.η ω) ρ t)
    ⟨C, hC.le⟩ w hb' hconv

/-- Every deterministic vanishing mesh sequence admits such a preparation. -/
theorem odometer_prepared_pair_modulus
    (𝒮 : SpaceFillingSLEModel) (hm : MepsScalingInput 𝒮)
    (h47 : EquiboundedStmt 𝒮) (h44 : DiscreteLaplacianBoundCorrectedStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hH : DiscreteHolderContinuityCorrectedStep 𝒮)
    (h27 : VolumeGrowthStmt)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (t : ℝ) (ht : 0 < t) (e : ℕ → ℝ) (he : ∀ n, 0 < e n)
    (he0 : Tendsto e atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂S.P,
      ∃ ξ A C₁ q Cm R₁ C : ℝ,
        0 < ξ ∧ 0 ≤ A ∧ 0 ≤ C₁ ∧ 0 < q ∧ 0 ≤ Cm ∧ 0 < R₁ ∧ 0 ≤ C ∧
        ∀ ψ : ℕ → ℕ, StrictMono ψ → ∀ w : ℂ → ℝ,
        OdometerLocalLimit S ρ t (e ∘ φ ∘ ψ) ω w →
        ∀ (x y : ℂ) (r0 : ℝ), 0 ≤ r0 → dist x 0 + r0 < ρ → dist y 0 + r0 < ρ →
        ∀ R : ℝ, 0 < R → R < min R₁ (min r0 1) →
        ‖x - y‖ ≤ ((R / 2) * (R / 2)) / 2 →
        |w x - w y| ≤ Cm * (A * C * (R / 2) ^ ξ + 2 * C * C₁ * R ^ q) := by
  obtain ⟨κ, hκ, hκe⟩ := extraction_forall_of_eventually
    (P := fun n k => 0 < e k ∧ e k < (1 / 2 : ℝ) ^ n) fun n => by
      filter_upwards [he0.eventually (gt_mem_nhds (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n))] with k hk
      exact ⟨he k, hk⟩
  have hpoly : IsPolySummableScales (e ∘ κ) := isPolySummableScales_of_lt_half_pow hκe
  obtain ⟨φ, hφ, hreg⟩ := odometer_prepared_pair_modulus_of_polyScales
    𝒮 hm h47 h44 h218 hH h27 hγ hγ2 hρ hρ1 S hS t ht (e ∘ κ) hpoly
  exact ⟨κ ∘ φ, hκ.comp hφ, hreg⟩

end MatedCRT
