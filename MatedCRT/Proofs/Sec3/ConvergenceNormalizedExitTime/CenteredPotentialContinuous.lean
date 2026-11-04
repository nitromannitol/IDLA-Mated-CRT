import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.ExitTimeMassGrowth
import MatedCRT.Steps.Sec3.ConvergenceNormalizedExitTime
import HarmonicBalls.Proofs.Potential.GreenPotentialHolder

/-! Continuity of the Green potential on a ball centered at the origin. -/

namespace MatedCRT

open Set Metric MeasureTheory HarmonicBalls Filter
open scoped ENNReal NNReal

/-- Lemma 2.17 supplies the upper mass growth needed for continuity of the
normalized exit Green potential on an origin-centered ball. -/
theorem normalizedExitGreenPotential_ae_continuousOn_centered
    (𝒮 : SpaceFillingSLEModel) (h217 : BoundedExitTimeRVStmt)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {r : ℝ} (hr : 0 < r) (hball : ball (0 : ℂ) r ⊆ ball 0 ρ) :
    ∀ᵐ ω ∂S.P, ContinuousOn (normalizedExitGreenPotential S r 0 ω) (closedBall 0 r) := by
  obtain ⟨β, hβ, hmass⟩ := ae_smallBallMass_all_small_radii h217 hγ hγ2 hρ hρ1
    S.P S.hC S.hcirc S.μ hS.isConeField
  filter_upwards [hmass, hS.isLQGMeasure] with ω hmassω hμ
  let : IsLocallyFiniteMeasure (S.μ ω) := hμ.isLocallyFiniteMeasure
  obtain ⟨r₀, hr₀, hup⟩ := hmassω
  have hup' : ∀ s, 0 < s → s < r₀ → ∀ x ∈ ball (0 : ℂ) r,
      S.μ ω (ball x s) ≤ ENNReal.ofReal (s ^ β) := by
    intro s hs hsr x hx
    exact hup s hs hsr x (hball hx)
  obtain ⟨_, hholder⟩ := greenPotential_ball_holder_of_upper hr hr₀ hβ hup'
    (measure_ball_lt_top.ne : S.μ ω (ball (0 : ℂ) r) ≠ ⊤)
    (f := fun _ => (1 : ℝ)) (M := 1) (by fun_prop) (by norm_num)
    (Eventually.of_forall (fun _ => by simp))
  let C : ℝ≥0 := ⟨greenPotentialHolderConstant β r₀ (S.μ ω (ball (0 : ℂ) r)).toReal,
    greenPotentialHolderConstant_nonneg hβ hr₀ ENNReal.toReal_nonneg⟩
  let α : ℝ≥0 := ⟨greenPotentialHolderExponent β, (greenPotentialHolderExponent_pos hβ).le⟩
  have hh : HolderOnWith C α
      (fun x => ∫ y in ball (0 : ℂ) r, greenFunction (ball 0 r) x y * 1 ∂S.μ ω)
      (closedBall 0 r) := by
    apply holderOnWith_of_dist_le
    intro x hx y hy
    rw [Real.dist_eq, dist_eq_norm]
    change |(∫ w in ball (0 : ℂ) r, greenFunction (ball 0 r) x w * 1 ∂S.μ ω) -
      (∫ w in ball (0 : ℂ) r, greenFunction (ball 0 r) y w * 1 ∂S.μ ω)| ≤
      greenPotentialHolderConstant β r₀ (S.μ ω (ball (0 : ℂ) r)).toReal *
        ‖x - y‖ ^ greenPotentialHolderExponent β
    simpa only [mul_one] using hholder x hx y hy
  have hc := hh.continuousOn (greenPotentialHolderExponent_pos hβ)
  change ContinuousOn (fun x : ℂ => S.c₀ / 6 *
    ∫ y in ball (0 : ℂ) r, greenFunction (ball 0 r) x y ∂S.μ ω) (closedBall 0 r)
  simpa only [mul_one] using hc.const_mul (S.c₀ / 6)

end MatedCRT
