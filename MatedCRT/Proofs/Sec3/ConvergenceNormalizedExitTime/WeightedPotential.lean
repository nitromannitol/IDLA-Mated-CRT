import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.CenteredNormalizedPotential

/-! Weak Laplacian of a Green potential with a bounded nonnegative source. -/

namespace MatedCRT

open MeasureTheory Metric Set Filter Laplacian _root_.HarmonicBalls
open scoped ENNReal

/-- A bounded nonnegative source preserves an upper small-ball mass bound. -/
theorem withDensity_ofReal_le_of_le_one (μ : Measure ℂ) (φ : ℂ → ℝ)
    (hφ : ∀ x, φ x ≤ 1) : μ.withDensity (fun x => ENNReal.ofReal (φ x)) ≤ μ := by
  calc
    μ.withDensity (fun x => ENNReal.ofReal (φ x)) ≤ μ.withDensity 1 := by
      apply withDensity_mono
      filter_upwards with x
      simpa using ENNReal.ofReal_le_ofReal (hφ x)
    _ = μ := withDensity_one

/-- The centered weighted Green potential has the distributional Laplacian
given by the source measure. The potential is written as an integral against
the original measure, as in the buffered-bump comparison. -/
theorem weightedGreenPotentialBall_hasLaplacian
    (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] {R r₀ β c : ℝ}
    (hR : 0 < R) (hr₀ : 0 < r₀) (hβ : 0 < β) (hc : 0 ≤ c)
    (hup : ∀ s, 0 < s → s < r₀ → ∀ x ∈ ball (0 : ℂ) R,
      μ (ball x s) ≤ ENNReal.ofReal (s ^ β))
    (φ : ℂ → ℝ) (hφm : Measurable φ) (hφ0 : ∀ x, 0 ≤ φ x)
    (hφ1 : ∀ x, φ x ≤ 1) :
    HasLaplacian (fun x => c * ∫ y in ball (0 : ℂ) R,
      greenFunction (ball 0 R) x y * φ y ∂μ) 0
      (ENNReal.ofReal c • μ.withDensity (fun x => ENNReal.ofReal (φ x))) (ball 0 R) := by
  let ν := μ.withDensity (fun x => ENNReal.ofReal (φ x))
  have hle : ν ≤ μ := withDensity_ofReal_le_of_le_one μ φ hφ1
  let : IsLocallyFiniteMeasure ν := Measure.isLocallyFiniteMeasure_of_le hle
  have hνup : ∀ s, 0 < s → s < r₀ → ∀ x ∈ ball (0 : ℂ) R,
      ν (ball x s) ≤ ENNReal.ofReal (s ^ β) := by
    intro s hs hs₀ x hx
    exact (hle _).trans (hup s hs hs₀ x hx)
  have h := hasLaplacian_const_mul_zero_left
    (greenPotentialBall_hasLaplacian_of_upper ν hR hr₀ hβ hνup) hc
  have heq : (fun x => c * greenPotentialBall ν R x) =
      (fun x => c * ∫ y in ball (0 : ℂ) R,
        greenFunction (ball 0 R) x y * φ y ∂μ) := by
    funext x
    congr 1
    unfold greenPotentialBall
    change (∫ y in ball (0 : ℂ) R, greenFunction (ball 0 R) y x
      ∂μ.withDensity (fun y => ENNReal.ofReal (φ y))) = _
    have hm : Measurable (fun y : ℂ => ENNReal.ofReal (φ y)) :=
      ENNReal.measurable_ofReal.comp hφm
    rw [setIntegral_withDensity_eq_setIntegral_toReal_smul
      hm (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) _ measurableSet_ball]
    apply setIntegral_congr_fun measurableSet_ball
    intro y hy
    simp [ENNReal.toReal_ofReal (hφ0 y), smul_eq_mul, mul_comm, greenFunction_ball_comm]
  rw [← heq]
  exact h

end MatedCRT
