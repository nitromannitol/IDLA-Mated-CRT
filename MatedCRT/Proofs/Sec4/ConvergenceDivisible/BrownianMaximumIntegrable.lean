import MatedCRT.Proofs.Sec4.ConvergenceDivisible.BrownianPathRotation

/-! # Integrability of the Brownian unit-interval maximum -/

namespace MatedCRT

open MeasureTheory ProbabilityTheory MarkovProcess
open scoped NNReal Real

local instance : CompactSpace UnitTime := isCompact_iff_compactSpace.mp isCompact_Icc

/-- The supremum norm of the Brownian unit path has finite expectation. -/
theorem brownian_unit_path_norm_integrable :
    Integrable (fun w => ‖unitPathRestriction w‖) (brownianMotion 0) := by
  let μ := (brownianMotion 0).map unitPathRestriction
  have hrot := brownian_unit_path_rotation (-(Real.pi / 4))
  obtain ⟨c, hc, hexp⟩ := exists_integrable_exp_sq_of_map_rotation_eq_self hrot
  have hmajor : Integrable (fun f : C(UnitTime, ℝ) =>
      1 + (1 / c) * Real.exp (c * ‖f‖ ^ 2)) μ :=
    (integrable_const 1).add (hexp.const_mul (1 / c))
  have hnorm : Integrable (fun f : C(UnitTime, ℝ) => ‖f‖) μ := by
    apply hmajor.mono' continuous_norm.aestronglyMeasurable
    filter_upwards with f
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg f)]
    have he := Real.add_one_le_exp (c * ‖f‖ ^ 2)
    have hb : ‖f‖ ^ 2 ≤ (1 / c) * Real.exp (c * ‖f‖ ^ 2) := by
      have : ‖f‖ ^ 2 ≤ Real.exp (c * ‖f‖ ^ 2) / c :=
        (le_div_iff₀ hc).2 (by linarith)
      simpa [div_eq_mul_inv, mul_comm] using this
    nlinarith [sq_nonneg (‖f‖ - 1 / 2)]
  exact (integrable_map_measure continuous_norm.aestronglyMeasurable
    continuous_unitPathRestriction.aemeasurable).1 hnorm

/-- Brownian unit-interval oscillations have an integrable maximum. -/
theorem brownian_unit_max_integrable :
    Integrable (unitOscillationMax 0) (brownianMotion 0) := by
  apply (brownian_unit_path_norm_integrable.const_mul 2).mono'
    (continuous_unitOscillationMax 0).aestronglyMeasurable
  filter_upwards with w
  rw [Real.norm_eq_abs, abs_of_nonneg (unitOscillationMax_nonneg 0 w)]
  exact unitOscillationMax_le_two_norm w

theorem convergenceDivisibleEventMeasurable_of_cone_scaling
    (𝒮 : SpaceFillingSLEModel) (h27 : VolumeGrowthStmt)
    (hscale : ConeEnvironmentScalingStep 𝒮) (hpos : ConeScaleRadiusStep) :
    ConvergenceDivisibleEventMeasurableStep 𝒮 :=
  convergenceDivisibleEventMeasurable_of_brownian_unit_max_integrable 𝒮 h27 hscale hpos
    brownian_unit_max_integrable

end MatedCRT
