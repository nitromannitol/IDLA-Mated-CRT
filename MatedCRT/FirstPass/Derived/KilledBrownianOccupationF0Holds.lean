import MatedCRT.FirstPass.Derived.KilledBrownianOccupationHolds
import MatedCRT.FirstPass.Derived.GmcGreenMassAtPole

/-!
# The Liouville-clock occupation identity from the cone field law and uniform integrability

The derived form `frozenLBMGreenOccupationRescaled_of_coneGFFLaw_killedOccupation_derived` takes, besides the
cone field law `hlaw`, the uniform integrability `hU` of the regularized clock integrals and the finiteness `hF0`
of the Green-weighted γ-LQG mass of a disc whose pole is the logarithmic singularity at the origin. The second is
a theorem, `ae_gmcGreenMeasure_ball_lt_top_pole_zero` (with `ρ₂ = (1 + ρ) / 2`); the form below supplies it, so
that `FrozenLBMGreenOccupationRescaled` follows from `hlaw` and `hU` alone.
-/

open MeasureTheory Set Filter Topology Metric MarkovProcess HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.KilledOccupation

/-- `frozenLBMGreenOccupationRescaled_of_coneGFFLaw_killedOccupation_derived` with its binder `hF0` discharged
by `ae_gmcGreenMeasure_ball_lt_top_pole_zero`. -/
theorem frozenLBMGreenOccupationRescaled_of_coneGFFLaw_killedOccupation_F0_derived
    (𝒮 : SpaceFillingSLEModel) (hlaw : ConeUnitDiskGFFLaw)
    (hU : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ (r : ℝ) (z y : ℂ), 0 < r →
      ball z r ⊆ ball 0 ρ → y ∈ ball z r →
      ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (hC' : Ω' → (ℂ → ℝ) → ℝ)
      (hc : Ω' → ℝ → ℂ → ℝ), IsProbabilityMeasure P' → HarmonicBalls.IsWholePlaneGFF P' hC' hc →
      ∀ n : ℕ → ℕ, StrictMono n → dyadicScale (n 0) < 1 - ρ →
      (∀ k : ℕ, clockAnnealedLaw P' (fun ω' => fieldCircleAverage γ (hc ω')) y
        {x | ENNReal.ofReal ((1 / 2 : ℝ) ^ k) <
          clockGapFun γ (exitNN z r) (dyadicScale (n k)) (dyadicScale (n (k + 1))) x}
          ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k)) →
      ∀ g : ℂ → ℝ, Continuous g → (∀ x, 0 ≤ g x) → HasCompactSupport g →
      tsupport g ⊆ ball z r \ ({0, y} : Set ℂ) →
      UniformIntegrable (fun k (p : Ω' × ContinuousPath ℂ) =>
        (∫⁻ u in Icc 0 (exitNN z r p.2), ENNReal.ofReal (g (p.2 u))
          ∂regClockMeasure γ (dyadicScale (n k)) (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) p.1)
            (exitNN z r) p.2).toReal) 1 (P'.prod (planarBrownianMotion y))) :
    FrozenLBMGreenOccupationRescaled 𝒮 :=
  frozenLBMGreenOccupationRescaled_of_coneGFFLaw_killedOccupation_derived 𝒮 hlaw hU
    fun _ hγ hγ2 ρ _ hρ1 _ _ _ _ h0 _ _ _ _ _ _ hG =>
      ae_gmcGreenMeasure_ball_lt_top_pole_zero hG hγ hγ2 (by linarith : ρ < (1 + ρ) / 2)
        (by linarith : (1 + ρ) / 2 < 1) h0

end MatedCRT.KilledOccupation
