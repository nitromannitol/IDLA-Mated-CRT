import MatedCRT.Proofs.Sec4.SubsequentialConvergence.RadiusLimitEventual
import MatedCRT.Proofs.MatingOfTrees.AdjacentCells
import MatedCRT.Proofs.Sec4.SubsequentialConvergence.InverseMeshScaling
import MatedCRT.Proofs.Sec4.SubsequentialConvergence.SmallBallExitPotential
import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.Equicontinuity

/-! A common event for separation-dependent interior estimates. -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls Tightness
open scoped ENNReal NNReal

/-- On one event the two-point estimate holds with common constants for every
further subsequence and every sequence with the stated eventual data bounds. -/
theorem ae_pair_modulus_of_prepared_estimates
    (𝒮 : SpaceFillingSLEModel) (hm : MepsScalingInput 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hH : DiscreteHolderContinuityCorrectedStep 𝒮)
    (h27 : VolumeGrowthStmt)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (e : ℕ → ℝ) (he : IsPolySummableScales e) :
    ∀ᵐ ω ∂S.P, ∃ ξ A C₁ q Cm R₁ : ℝ,
      0 < ξ ∧ 0 ≤ A ∧ 0 ≤ C₁ ∧ 0 < q ∧ 0 ≤ Cm ∧ 0 < R₁ ∧
      ∀ ψ : ℕ → ℕ, StrictMono ψ → ∀ (u : ℕ → ℤ → ℝ) (C : ℝ≥0) (f : ℂ → ℝ),
      (∀ᶠ n in atTop,
        (∀ a ∈ interiorCellVertices (e (ψ n)) (S.η ω) (ball 0 ρ),
          |mLaplacian (S.mult (e (ψ n)) ω) (u n) a| ≤ C) ∧
        (∀ a ∈ cellVertices (e (ψ n)) (S.η ω) (ball 0 ρ),
          |u n a| ≤ (C : ℝ) / e (ψ n))) →
      (∀ x ∈ ball (0 : ℂ) ρ, Tendsto (fun n => rescale (S.mε (e (ψ n))) (e (ψ n))
        (S.η ω) (u n) x) atTop (𝓝 (f x))) →
      ∀ (x y : ℂ) (r0 : ℝ), 0 ≤ r0 → dist x 0 + r0 < ρ → dist y 0 + r0 < ρ →
      ∀ R : ℝ, 0 < R → R < min R₁ (min r0 1) →
      ‖x - y‖ ≤ ((R / 2) * (R / 2)) / 2 →
      |f x - f y| ≤ Cm * (A * C * (R / 2) ^ ξ + 2 * C * C₁ * R ^ q) := by
  obtain ⟨α, hα, h18α⟩ := h218 γ hγ hγ2
  obtain ⟨C₁, hC₁, h18C⟩ := h18α ρ hρ hρ1
  obtain ⟨ξ, A, β, hξ, hξ1, hA, hβ, _, hHχ⟩ := hH γ hγ hγ2 ρ hρ hρ1
  obtain ⟨_, _, _, _, _, hH1⟩ := hHχ 1 1 one_pos le_rfl one_pos
  obtain ⟨Cm, hm⟩ := eventually_inverse_median_scaling_of_mepsScaling 𝒮 hm hγ hγ2 S hS
  filter_upwards [ae_eventually_mem_of_polyHighProb (h18C Ω S hS) he,
    ae_eventually_mem_of_polyHighProb (hH1 Ω S hS) he,
    hS.ae_smallBallExitPotential hγ hγ2 hρ1 h27,
    adjacentCellsMeetAeStep 𝒮 γ hγ hγ2 Ω S hS,
    hS.isAreaParametrized, hS.ae_tendsto_cocompact] with ω h18ω hHω hM hadj hη hp
  obtain ⟨q, hq, r₀, hr₀, hM⟩ := hM
  refine ⟨ξ, A, C₁, q, Cm, r₀, hξ, hA.le, hC₁.le, hq, NNReal.coe_nonneg Cm, hr₀, ?_⟩
  intro ψ hψ u C f hdata hconv
  have hψt := hψ.tendsto_atTop
  have hHball : ∀ᶠ n in atTop, ∀ (x : ℂ) (r : ℝ), 0 < r → ball x r ⊆ ball 0 ρ → ∀ f : ℤ → ℝ,
      (∀ a ∈ interiorCellVertices (e (ψ n)) (S.η ω) (ball x r), matedLaplacian (S.mult (e (ψ n)) ω) f a = 0) →
      ∀ a ∈ interiorCellVertices (e (ψ n)) (S.η ω) (ball x r), ∀ b ∈ cellVertices (e (ψ n)) (S.η ω) (ball x r),
        |f a - f b| * infDist (vertexPoint (e (ψ n)) (S.η ω) a) (frontier (ball x r)) ^ ξ ≤
          A * (⨆ a' : cellVertices (e (ψ n)) (S.η ω) (ball x r), |f a'|) *
            max (e (ψ n) ^ β) ‖vertexPoint (e (ψ n)) (S.η ω) a - vertexPoint (e (ψ n)) (S.η ω) b‖ ^ ξ := by
    filter_upwards [hψt.eventually hHω] with n hn x r hr hxr f hf
    exact (hn (ball x r) f hxr isOpen_ball ((convex_ball x r).isConnected (nonempty_ball.2 hr)) hf).1
  have hQ : ∀ᶠ n in atTop, ∀ D' : Set ℂ, D' ⊆ ball 0 ρ → ∀ a ∈ cellVertices (e (ψ n)) (S.η ω) D',
      expectedExitTime (S.mult (e (ψ n)) ω) (interiorCellVertices (e (ψ n)) (S.η ω) D') a ≤
        ENNReal.ofReal (C₁ * (e (ψ n))⁻¹) * largestExitTimeRV (S.μ ω) (thickening (e (ψ n) ^ α) D') := by
    filter_upwards [hψt.eventually h18ω] with n hn D' hD' a ha
    exact (hn.2 D' hD' a ha).2
  intro x y r0 hr0 hx hy R hR hRlt hxy
  apply Tightness.limit_two_power_modulus_for_pair_of_eventual_exit_estimates
    (m := fun n => S.mult (e (ψ n)) ω) (ε := e ∘ ψ) (mε := fun n => S.mε (e (ψ n)))
    (u := u) (μ := S.μ ω) (ρ := ρ) (β := β) (α := α)
    (Cm := Cm) (C := C) (ξ := ξ) (A := A) (C₁ := C₁) (q := q)
    (fun n => he.1 _) (he.tendsto_zero.comp hψt) hη.1 hp hη.2.2.1
    (NNReal.coe_nonneg Cm)
    (hm (e ∘ ψ) (fun n => he.1 _) (he.tendsto_zero.comp hψt))
    (fun n => hadj _ (he.1 _)) (fun n k => S.mult_succ_ne_zero (he.1 _).le ω k)
    (NNReal.coe_nonneg C) hdata hξ hA.le hβ hα hC₁.le hHball hQ hr0 hx hy hM hconv
    R hR hRlt hxy

end MatedCRT
