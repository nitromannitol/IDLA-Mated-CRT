import MatedCRT.Proofs.Sec4.ConvergenceDivisible.BrownianOscillationStationary
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

/-! # Brownian path Gaussianity and unit-interval maxima -/

namespace MatedCRT

open MeasureTheory ProbabilityTheory MarkovProcess
open scoped NNReal

/-- The unit interval as a compact space of nonnegative times. -/
abbrev UnitTime := Set.Icc ((0 : ℕ) : ℝ≥0) (((0 : ℕ) : ℝ≥0) + 1)

local instance : CompactSpace UnitTime := isCompact_iff_compactSpace.mp isCompact_Icc

/-- The Brownian path restricted to the unit interval, viewed in the sup norm. -/
def unitPathRestriction (w : ContinuousPath ℝ) : C(UnitTime, ℝ) := w.restrict UnitTime

theorem continuous_unitPathRestriction : Continuous unitPathRestriction :=
  ContinuousMap.continuous_restrict UnitTime

/-- Every finite family of evaluations of the restricted Brownian path has a
Gaussian law. -/
theorem unitPathRestriction_finite_gaussian (I : Finset UnitTime) :
    HasGaussianLaw (fun w : ContinuousPath ℝ =>
      I.restrict (fun t => unitPathRestriction w t)) (brownianMotion 0) := by
  have h := (canonical_isPreBrownianReal.isGaussianProcess.comp_right
    (fun t : UnitTime => t.1)).hasGaussianLaw I
  exact h

/-- The oscillation is bounded by twice the supremum norm of the path. -/
theorem unitOscillationMax_le_two_norm (w : ContinuousPath ℝ) :
    unitOscillationMax 0 w ≤ 2 * ‖unitPathRestriction w‖ := by
  let f := unitPathRestriction w
  apply (unitOscillationMax_le_iff 0 w (by positivity)).2
  intro t ht₀ ht₁
  let t' : UnitTime := ⟨t, ht₀, ht₁⟩
  let z : UnitTime := ⟨0, by simp, by simp⟩
  have ht : ‖w t‖ ≤ ‖f‖ := ContinuousMap.norm_coe_le_norm f t'
  have hz : ‖w 0‖ ≤ ‖f‖ := ContinuousMap.norm_coe_le_norm f z
  calc
    |w t - w (0 : ℕ)| = ‖w t - w 0‖ := by simp [Real.norm_eq_abs]
    _ ≤ ‖w t‖ + ‖w 0‖ := norm_sub_le _ _
    _ ≤ 2 * ‖f‖ := by linarith

/-- Gaussianity of the restricted Brownian path gives an integrable unit
oscillation maximum by Fernique's theorem. -/
theorem brownian_unit_max_integrable_of_gaussian
    (hG : HasGaussianLaw unitPathRestriction (brownianMotion 0)) :
    Integrable (unitOscillationMax 0) (brownianMotion 0) := by
  have hnorm : Integrable (fun w => 2 * ‖unitPathRestriction w‖) (brownianMotion 0) :=
    hG.integrable.norm.const_mul 2
  apply hnorm.mono' (continuous_unitOscillationMax 0).aestronglyMeasurable
  filter_upwards with w
  rw [Real.norm_eq_abs, abs_of_nonneg (unitOscillationMax_nonneg 0 w)]
  exact unitOscillationMax_le_two_norm w

theorem convergenceDivisibleEventMeasurable_of_gaussian_unit_path
    (𝒮 : SpaceFillingSLEModel) (h27 : VolumeGrowthStmt)
    (hscale : ConeEnvironmentScalingStep 𝒮) (hpos : ConeScaleRadiusStep)
    (hG : HasGaussianLaw unitPathRestriction (brownianMotion 0)) :
    ConvergenceDivisibleEventMeasurableStep 𝒮 :=
  convergenceDivisibleEventMeasurable_of_brownian_unit_max_integrable 𝒮 h27 hscale hpos
    (brownian_unit_max_integrable_of_gaussian hG)

end MatedCRT
