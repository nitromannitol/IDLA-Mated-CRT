import MatedCRT.FirstPass.Derived.PaperBallClockPrefix
import MatedCRT.FirstPass.Derived.EuclideanCurveLawSupport
import MatedCRT.FirstPass.Derived.ExitTimeCdfConvergence
import LatticeProb.Prob.NormalizedPrefixCurve
import LatticeProb.Prob.BallClockOscillationEvent

/-! # Laws of normalized exit curves -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Set HarmonicBalls LatticeProb
open LatticeProb.ReparamDistanceIsometry LatticeProb.UnboundedRayIntervalIntegrand
open scoped ENNReal NNReal

/-- The normalized exit curve is measurable for an open domain, with an infinite
exit time totalized to zero duration. -/
theorem measurable_paperNormalizedExitCurve {U : Set ℂ} (hU : IsOpen U) :
    Measurable (fun f : C(ℝ≥0, ℂ) => normalizedPrefixCurve
      (complexToEuclideanPath f) (pathExitTime U f).toNNReal) := by
  exact measurable_normalizedPrefixCurve_toNNReal.comp
    (continuous_complexToEuclideanPath.measurable.prodMk
      (ExitTimeCdf.measurable_pathExitTime hU))

/-- Taking the normalized exit curve commutes with forming a measurable path law. -/
theorem map_paperNormalizedExitCurve_map {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → C(ℝ≥0, ℂ)) (hf : Measurable f)
    {U : Set ℂ} (hU : IsOpen U) :
    (μ.map f).map (fun p => normalizedPrefixCurve
      (complexToEuclideanPath p) (pathExitTime U p).toNNReal) =
    μ.map (fun x => normalizedPrefixCurve
      (complexToEuclideanPath (f x)) (pathExitTime U (f x)).toNNReal) := by
  rw [Measure.map_map (measurable_paperNormalizedExitCurve hU) hf]
  rfl

/-- The paper's stopped embedded walk curve is the normalized exit-curve law
of the embedded continuous walk path. -/
theorem interpolatedWalk_normalizedExitCurve_law
    (μ : Measure (ℕ → ℤ)) (ε : ℝ) (η : ℝ → ℂ)
    {m : ℝ} (hm : 0 ≤ m) {U : Set ℂ} (hU : IsOpen U) :
    (μ.map (interpPathCM (vertexPoint ε η) hm)).map
      (fun p => normalizedPrefixCurve (complexToEuclideanPath p)
        (pathExitTime U p).toNNReal) =
    μ.map (fun x => normalizedPrefixCurve
      (complexToEuclideanPath (interpPathCM (vertexPoint ε η) hm x))
      (pathExitTime U (interpolatedWalk ε η m x)).toNNReal) := by
  rw [map_paperNormalizedExitCurve_map μ _
    (measurable_interpPathCM (vertexPoint ε η) hm) hU]
  congr 1

/-- The normalized ball-exit law in complex coordinates equals the corresponding
ball-clock law of the Euclidean-coordinate path. -/
theorem paperNormalizedBallExitCurve_law (μ : Measure C(ℝ≥0, ℂ)) (r : ℝ) :
    μ.map (fun p => normalizedPrefixCurve (complexToEuclideanPath p)
      (pathExitTime (Metric.ball (0 : ℂ) r) p).toNNReal) =
    (μ.map complexToEuclideanPath).map (fun p => normalizedPrefixCurve p
      (ballClock p r).toNNReal) := by
  have hm : Measurable (fun p : C(ℝ≥0, EuclideanSpace ℝ (Fin 2)) =>
      normalizedPrefixCurve p (ballClock p r).toNNReal) :=
    measurable_normalizedPrefixCurve_toNNReal.comp
      (measurable_id.prodMk (measurable_ballClock_fixed_radius r))
  rw [Measure.map_map hm continuous_complexToEuclideanPath.measurable]
  congr 1
  funext p
  change normalizedPrefixCurve (complexToEuclideanPath p)
    (pathExitTime (Metric.ball (0 : ℂ) r) p).toNNReal =
    normalizedPrefixCurve (complexToEuclideanPath p)
      (ballClock (complexToEuclideanPath p) r).toNNReal
  rw [ballClock_complexToEuclideanPath]

end MatedCRT
end
