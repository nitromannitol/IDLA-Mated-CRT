import MatedCRT.Proofs.Sec4.SubsequentialConvergence.OdometerPairModulus
import MatedCRT.Proofs.Sec4.SubsequentialConvergence.PreparedBoundaryHolder

/-! Interior pair estimates and boundary decay on one preparation. -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric
open scoped NNReal

/-- Every limit along a further subsequence has common interior pair and
boundary decay estimates on one almost-sure event. -/
theorem odometer_prepared_pair_and_boundary_moduli
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
      ∃ ξ A C₁ q Cm R₁ C : ℝ, ∃ B χ : ℝ≥0,
        0 < ξ ∧ 0 ≤ A ∧ 0 ≤ C₁ ∧ 0 < q ∧ 0 ≤ Cm ∧ 0 < R₁ ∧ 0 ≤ C ∧ 0 < χ ∧ χ ≤ 1 ∧
        ∀ ψ : ℕ → ℕ, StrictMono ψ → ∀ w : ℂ → ℝ,
        OdometerLocalLimit S ρ t (e ∘ φ ∘ ψ) ω w →
        (∀ (x y : ℂ) (r0 : ℝ), 0 ≤ r0 → dist x 0 + r0 < ρ → dist y 0 + r0 < ρ →
        ∀ R : ℝ, 0 < R → R < min R₁ (min r0 1) →
        ‖x - y‖ ≤ ((R / 2) * (R / 2)) / 2 →
        |w x - w y| ≤ Cm * (A * C * (R / 2) ^ ξ + 2 * C * C₁ * R ^ q)) ∧
        (∀ x ∈ ball 0 ρ, ∀ y ∈ sphere 0 ρ, |w x| ≤ B * dist x y ^ (χ : ℝ)) := by
  obtain ⟨φ, hφ, hi⟩ := odometer_prepared_pair_modulus
    𝒮 hm h47 h44 h218 hH h27 hγ hγ2 hρ hρ1 S hS t ht e he he0
  obtain ⟨θ, hθ, hb⟩ := odometer_prepared_boundary_holder_of_normalized_exit
    𝒮 h37 h217 h27 hγ hγ2 hρ hρ1 S hS (e ∘ φ) (fun n => he _)
      (he0.comp hφ.tendsto_atTop)
  refine ⟨φ ∘ θ, hφ.comp hθ, ?_⟩
  filter_upwards [hi, hb] with ω hi hb
  obtain ⟨ξ, A, C₁, q, Cm, R₁, C, hξ, hA, hC₁, hq, hCm, hR₁, hC, hi⟩ := hi
  obtain ⟨B, χ, hχ, hχ1, hb⟩ := hb
  refine ⟨ξ, A, C₁, q, Cm, R₁, C, B, χ, hξ, hA, hC₁, hq, hCm, hR₁, hC, hχ, hχ1, ?_⟩
  intro ψ hψ w hw
  exact ⟨hi (θ ∘ ψ) (hθ.comp hψ) w hw, hb t ht ψ hψ w hw⟩

end MatedCRT
