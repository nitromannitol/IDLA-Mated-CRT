import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.CenteredNormalizedPotential

/-! Boundary continuity for Green potentials of bounded sources. -/

namespace MatedCRT

open MeasureTheory Metric Set Filter Laplacian _root_.HarmonicBalls
open scoped ENNReal NNReal

/-- Under upper power growth, the Green potential of a bounded measurable
source extends continuously to the closed ball. -/
theorem weightedGreenPotentialBall_continuousOn
    (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] {R r₀ β c : ℝ}
    (hR : 0 < R) (hr₀ : 0 < r₀) (hβ : 0 < β)
    (hup : ∀ s, 0 < s → s < r₀ → ∀ x ∈ ball (0 : ℂ) R,
      μ (ball x s) ≤ ENNReal.ofReal (s ^ β))
    (φ : ℂ → ℝ) (hφm : Measurable φ) (hφ0 : ∀ x, 0 ≤ φ x)
    (hφ1 : ∀ x, φ x ≤ 1) :
    ContinuousOn (fun x => c * ∫ y in ball (0 : ℂ) R,
      greenFunction (ball 0 R) x y * φ y ∂μ) (closedBall 0 R) := by
  obtain ⟨_, hh⟩ := greenPotential_ball_holder_of_upper hR hr₀ hβ hup
    (measure_ball_lt_top.ne : μ (ball (0 : ℂ) R) ≠ ⊤)
    (f := φ) (M := 1) hφm.aestronglyMeasurable (by norm_num)
    (Eventually.of_forall fun y => (abs_of_nonneg (hφ0 y)).le.trans (hφ1 y))
  let C : ℝ≥0 := ⟨greenPotentialHolderConstant β r₀ (μ (ball (0 : ℂ) R)).toReal,
    greenPotentialHolderConstant_nonneg hβ hr₀ ENNReal.toReal_nonneg⟩
  let α : ℝ≥0 := ⟨greenPotentialHolderExponent β, (greenPotentialHolderExponent_pos hβ).le⟩
  have hholder : HolderOnWith C α
      (fun x => ∫ y in ball (0 : ℂ) R, greenFunction (ball 0 R) x y * φ y ∂μ)
      (closedBall 0 R) := by
    apply holderOnWith_of_dist_le
    intro x hx y hy
    rw [Real.dist_eq, dist_eq_norm]
    change |(∫ w in ball (0 : ℂ) R, greenFunction (ball 0 R) x w * φ w ∂μ) -
      (∫ w in ball (0 : ℂ) R, greenFunction (ball 0 R) y w * φ w ∂μ)| ≤
      greenPotentialHolderConstant β r₀ (μ (ball (0 : ℂ) R)).toReal *
        ‖x - y‖ ^ greenPotentialHolderExponent β
    simpa only [mul_one] using hh x hx y hy
  exact (hholder.continuousOn (greenPotentialHolderExponent_pos hβ)).const_mul c

end MatedCRT
