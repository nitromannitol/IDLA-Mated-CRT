import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.CenteredPotentialLaplacian
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.PotentialContinuous
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.PotentialBoundary

/-! Normalization of the Green-potential Laplacian. -/

namespace MatedCRT

open MeasureTheory Metric Filter Topology Set Laplacian _root_.HarmonicBalls
open scoped ENNReal

/-- Scaling a potential by a nonnegative real scales its negative
distributional Laplacian by the same factor. -/
theorem hasLaplacian_const_mul_zero_left {q : ℂ → ℝ} {μ : Measure ℂ} {U : Set ℂ}
    (hq : HasLaplacian q 0 μ U) {c : ℝ} (hc : 0 ≤ c) :
    HasLaplacian (fun x => c * q x) 0 (ENNReal.ofReal c • μ) U := by
  refine ⟨?_, fun φ hφ => ?_⟩
  · convert hq.1.smul c using 1
  obtain ⟨_, hi, heq⟩ := hq.2 φ hφ
  refine ⟨integrable_zero_measure, hi.smul_measure ENNReal.ofReal_ne_top, ?_⟩
  rw [integral_zero_measure, zero_sub, integral_smul_measure, ENNReal.toReal_ofReal hc, smul_eq_mul]
  calc
    ∫ x, (c * q x) * Δ φ x = c * ∫ x, q x * Δ φ x := by
      simp_rw [mul_assoc]
      rw [integral_const_mul]
    _ = -(c * ∫ x, φ x ∂μ) := by
      rw [heq, integral_zero_measure, zero_sub]
      ring

/-- Lemma 2.17 gives the distributional Laplacian of the normalized exit
potential on an origin-centered ball. -/
theorem normalizedExitGreenPotential_ae_hasLaplacian_centered
    (𝒮 : SpaceFillingSLEModel) (h217 : BoundedExitTimeRVStmt)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {r : ℝ} (hr : 0 < r) (hball : ball (0 : ℂ) r ⊆ ball 0 ρ) :
    ∀ᵐ ω ∂S.P, HasLaplacian (normalizedExitGreenPotential S r 0 ω) 0
      (ENNReal.ofReal (S.c₀ / 6) • S.μ ω) (ball 0 r) := by
  obtain ⟨β, hβ, hmass⟩ := ae_smallBallMass_all_small_radii h217 hγ hγ2 hρ hρ1
    S.P S.hC S.hcirc S.μ hS.isConeField
  filter_upwards [hmass, hS.isLQGMeasure] with ω hmassω hμ
  let : IsLocallyFiniteMeasure (S.μ ω) := hμ.isLocallyFiniteMeasure
  obtain ⟨r₀, hr₀, hup⟩ := hmassω
  have hup' : ∀ s, 0 < s → s < r₀ → ∀ x ∈ ball (0 : ℂ) r,
      S.μ ω (ball x s) ≤ ENNReal.ofReal (s ^ β) := by
    intro s hs hsr x hx
    exact hup s hs hsr x (hball hx)
  have hq := greenPotentialBall_hasLaplacian_of_upper (S.μ ω) hr hr₀ hβ hup'
  have hc : 0 ≤ S.c₀ / 6 := div_nonneg S.c₀_nonneg (by norm_num)
  have heq : normalizedExitGreenPotential S r 0 ω =
      fun x => S.c₀ / 6 * greenPotentialBall (S.μ ω) r x := by
    funext x
    unfold normalizedExitGreenPotential greenPotentialBall
    congr 1
    apply setIntegral_congr_fun measurableSet_ball
    intro y hy
    exact greenFunction_ball_comm r x y
  rw [heq]
  exact hasLaplacian_const_mul_zero_left hq hc

end MatedCRT
