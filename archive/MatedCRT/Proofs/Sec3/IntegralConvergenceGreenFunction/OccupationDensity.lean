import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.PathOccupationEnergy
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.ApproxClockOccupation
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.RegularizedOccupationLimit
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.ClockGMCNormalization
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Weighted path occupation and regularized clocks -/

namespace MatedCRT

open MeasureTheory Set HarmonicBalls MarkovProcess Filter Topology
open scoped NNReal

/-- Integrating against a density-weighted path occupation measure gives the
weighted time integral along the path. -/
theorem pathOccupationMeasure_withDensity_integral
    (b : ContinuousPath ℂ) (T : ℝ≥0) (w f : ℂ → ℝ)
    (hw : Continuous w) (hw0 : ∀ z, 0 ≤ w z) (hf : Continuous f) :
    (∫ z, f z ∂((pathOccupationMeasure (fun t => b t.toNNReal) T).withDensity
      (fun z => ENNReal.ofReal (w z)))) =
      ∫ t in (0 : ℝ)..(T : ℝ), w (b t.toNNReal) * f (b t.toNNReal) := by
  rw [integral_withDensity_eq_integral_toReal_smul hw.measurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (hw0 _), smul_eq_mul]
  rw [pathOccupationMeasure, integral_map_of_stronglyMeasurable
    (show Measurable (fun t : ℝ => b t.toNNReal) from
      b.continuous.measurable.comp measurable_real_toNNReal)
    (show StronglyMeasurable (fun z => w z * f z) from (hw.mul hf).stronglyMeasurable)]
  rw [intervalIntegral.integral_of_le T.coe_nonneg, integral_Icc_eq_integral_Ioc]

/-- The density-weighted occupation measure for a circle-average clock has
the same test-function integral as its time-changed path up to clock time. -/
theorem lqgClockApprox_weighted_occupation
    (γ ε : ℝ) (hε : ℝ → ℂ → ℝ) (b : ContinuousPath ℂ)
    (hεpos : 0 < ε) (hfield : Continuous (hε ε))
    (T : ℝ≥0) (f : ℂ → ℝ) (hf : Continuous f) :
    (∫ z, f z ∂((pathOccupationMeasure (fun t => b t.toNNReal) T).withDensity
      (fun z => ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * hε ε z))))) =
      ∫ s in (0 : ℝ)..(lqgClockApprox γ hε ε b T),
        f (b (clockInverse (lqgClockApprox γ hε ε b) s.toNNReal)) := by
  rw [pathOccupationMeasure_withDensity_integral b T _ f
    (by fun_prop) (fun z => (mul_pos (Real.rpow_pos_of_pos hεpos _)
      (Real.exp_pos _)).le) hf]
  simpa only [mul_comm] using
    lqgClockApprox_occupation_substitution_local γ ε hε b hεpos hfield T f hf

/-- Pointwise clock convergence identifies the limit of the integrals of
bounded continuous test functions against the regularized occupation chaos. -/
theorem tendsto_gmcApprox_occupation_of_clock_convergence
    {Ω ι : Type*} [MeasurableSpace Ω] {l : Filter ι} [l.IsCountablyGenerated]
    (P : Measure Ω) (γ : ℝ) (ε : ι → ℝ) (hε : Ω → ℝ → ℂ → ℝ)
    (ω : Ω) (b : ContinuousPath ℂ)
    (hεpos : ∀ i, 0 < ε i) (hfield : ∀ i, Continuous (hε ω (ε i)))
    (hvar : ∀ i z, (∫ ω', (hε ω' (ε i) z) ^ 2 ∂P) = Real.log (ε i)⁻¹)
    (G : ℝ≥0 → ℝ) (hGzero : G 0 = 0) (hGcont : Continuous G)
    (hGmono : StrictMono G)
    (hconv : ∀ t, Tendsto (fun i => lqgClockApprox γ (hε ω) (ε i) b t) l (𝓝 (G t)))
    (T : ℝ≥0) (f : ℂ → ℝ) (hf : Continuous f) (C : ℝ)
    (hbound : ∀ z, ‖f z‖ ≤ C) :
    Tendsto (fun i => ∫ z, f z ∂(gmcApprox P
      (pathOccupationMeasure (fun t => b t.toNNReal) T) γ
      (fun ω' z => hε ω' (ε i) z) ω)) l
      (𝓝 (∫ s in (0 : ℝ)..G T, f (b (clockInverse G s.toNNReal)))) := by
  have h := tendsto_lqgClockApprox_weighted_occupation γ ε (hε ω) b hεpos hfield
    G hGzero hGcont hGmono hconv T f hf C hbound
  apply h.congr'
  filter_upwards [] with i
  rw [gmcApprox_eq_clock_density P _ γ (ε i) (hεpos i) _ (hvar i) ω,
    pathOccupationMeasure_withDensity_integral b T _ f (by fun_prop)
      (fun z => (mul_pos (Real.rpow_pos_of_pos (hεpos i) _) (Real.exp_pos _)).le) hf]
  simp only [mul_comm]

end MatedCRT

