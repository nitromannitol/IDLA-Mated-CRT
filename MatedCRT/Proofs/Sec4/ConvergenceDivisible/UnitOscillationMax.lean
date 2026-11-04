import MatedCRT.Proofs.Sec4.ConvergenceDivisible.IdentDistribSublinear
import Mathlib.Topology.ContinuousMap.Compact

/-! # Oscillation maxima of continuous paths -/

namespace MatedCRT

open Filter Set MeasureTheory ProbabilityTheory MarkovProcess Topology
open scoped NNReal

/-- The largest deviation from the left endpoint over a unit interval. -/
noncomputable def unitOscillationMax (n : ℕ) (w : ContinuousPath ℝ) : ℝ := by
  let I : Set ℝ≥0 := Icc (n : ℝ≥0) ((n : ℝ≥0) + 1)
  letI : CompactSpace I := isCompact_iff_compactSpace.mp isCompact_Icc
  exact ‖w.restrict I - ContinuousMap.const I (w (n : ℝ≥0))‖

theorem unitOscillationMax_nonneg (n : ℕ) (w : ContinuousPath ℝ) :
    0 ≤ unitOscillationMax n w := by
  unfold unitOscillationMax
  exact norm_nonneg _

/-- The maximum dominates each increment in the interval. -/
theorem le_unitOscillationMax (n : ℕ) (w : ContinuousPath ℝ) (t : ℝ≥0)
    (hnt : (n : ℝ≥0) ≤ t) (htn : t ≤ (n : ℝ≥0) + 1) :
    |w t - w (n : ℝ≥0)| ≤ unitOscillationMax n w := by
  let I : Set ℝ≥0 := Icc (n : ℝ≥0) ((n : ℝ≥0) + 1)
  let : CompactSpace I := isCompact_iff_compactSpace.mp isCompact_Icc
  let f : C(I, ℝ) := w.restrict I - ContinuousMap.const I (w (n : ℝ≥0))
  have h := ContinuousMap.norm_coe_le_norm f (⟨t, hnt, htn⟩ : I)
  simpa [f, I, unitOscillationMax, Real.norm_eq_abs] using h

/-- Oscillation on a compact interval is a continuous functional of the path. -/
theorem continuous_unitOscillationMax (n : ℕ) : Continuous (unitOscillationMax n) := by
  let I : Set ℝ≥0 := Icc (n : ℝ≥0) ((n : ℝ≥0) + 1)
  let : CompactSpace I := isCompact_iff_compactSpace.mp isCompact_Icc
  have hr : Continuous (fun w : ContinuousPath ℝ => w.restrict I) :=
    ContinuousMap.continuous_restrict I
  have hc : Continuous (fun w : ContinuousPath ℝ =>
      ContinuousMap.const I (w (n : ℝ≥0))) :=
    ContinuousMap.continuous_const'.comp (ContinuousPath.continuous_eval _)
  change Continuous (fun w : ContinuousPath ℝ =>
    ‖w.restrict I - ContinuousMap.const I (w (n : ℝ≥0))‖)
  exact (hr.sub hc).norm

theorem measurable_unitOscillationMax (n : ℕ) : Measurable (unitOscillationMax n) :=
  (continuous_unitOscillationMax n).measurable

/-- The convergence-event reduction using the actual oscillation maxima. -/
theorem convergenceDivisibleEventMeasurable_of_unitOscillationMax
    (𝒮 : SpaceFillingSLEModel) (h27 : VolumeGrowthStmt)
    (hscale : ConeEnvironmentScalingStep 𝒮) (hpos : ConeScaleRadiusStep)
    (hint : Integrable (unitOscillationMax 0) (brownianMotion 0))
    (hid : ∀ n, IdentDistrib (unitOscillationMax n) (unitOscillationMax 0)
      (brownianMotion 0) (brownianMotion 0)) :
    ConvergenceDivisibleEventMeasurableStep 𝒮 :=
  convergenceDivisibleEventMeasurable_of_brownian_oscillation_bound 𝒮 h27 hscale hpos
    unitOscillationMax hint unitOscillationMax_nonneg hid le_unitOscillationMax

end MatedCRT
