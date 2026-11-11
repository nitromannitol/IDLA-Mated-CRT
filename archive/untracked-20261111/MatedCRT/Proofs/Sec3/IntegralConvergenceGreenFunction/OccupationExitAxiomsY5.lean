import MatedCRT.Steps.Sec3.IntegralConvergenceGreenFunction
import MatedCRT.Proofs.LBM.BrownianExitBall

/-! # Finite exit in the Liouville Green occupation identity -/

namespace MatedCRT

open MeasureTheory Set Metric HarmonicBalls

/-- The finite-exit clause of the Green occupation step follows from validity
of the environment. It remains only to prove the occupation identity on a
single full-measure event for all admissible test functions. -/
theorem lbmGreenOccupationStep_of_identity
    {𝒮 : SpaceFillingSLEModel}
    (hidentity : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ (r : ℝ) (z y : ℂ), 0 < r → ball z r ⊆ ball 0 ρ → y ∈ ball z r →
      ∀ᵐ ω ∂S.P, ∀ f : ℂ → ℝ, (∃ M : ℝ, ∀ x ∈ ball z r, |f x| ≤ M) →
        IsHolderContinuousOn f (ball z r) →
        lbmOccupationIntegral (S.clock ω) (ball z r) y f =
          2 * ∫ x in ball z r, greenFunction (ball z r) y x * f x ∂S.μ ω) :
    LBMGreenOccupationStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS r z y hr hD hy
  filter_upwards [hS.ae_lbmExitTime_any_ball_lt_top y z r,
    hidentity γ hγ hγ2 ρ hρ hρ1 Ω S hS r z y hr hD hy] with ω hexit hformula
  exact ⟨hexit, hformula⟩

end MatedCRT

#print axioms MatedCRT.lbmGreenOccupationStep_of_identity
