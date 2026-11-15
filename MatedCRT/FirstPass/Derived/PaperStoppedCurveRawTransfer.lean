import MatedCRT.FirstPass.S6j.LitUniformStartInvariance
import LatticeProb.Prob.AEFiniteCurveRawEventTransfer

/-! # Raw stopped-path events from finite curve laws -/

set_option autoImplicit false

open MeasureTheory Set HarmonicBalls LatticeProb
open scoped ENNReal NNReal

namespace MatedCRT

/-- A comparison of normalized stopped-curve laws gives the paper's outer-measure
comparison for arbitrary path sets when both exit times are almost surely finite. -/
theorem measure_stopAtExit_le_of_levyProkhorovEDist_lt
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ)
    (f : Ω → C(ℝ≥0, ℂ)) (g : Ξ → C(ℝ≥0, ℂ)) (U V : Set ℂ)
    (hU : ∀ᵐ x ∂μ, pathExitTime U (f x) ≠ ⊤)
    (hV : ∀ᵐ y ∂ν, pathExitTime V (g y) ≠ ⊤)
    (hf : Measurable (fun x => normalizedPrefixCurve
      (ReparamDistanceIsometry.complexToEuclideanPath (f x))
      (pathExitTime U (f x)).toNNReal))
    (hg : Measurable (fun y => normalizedPrefixCurve
      (ReparamDistanceIsometry.complexToEuclideanPath (g y))
      (pathExitTime V (g y)).toNNReal))
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (h : levyProkhorovEDist
      (μ.map (fun x => normalizedPrefixCurve
        (ReparamDistanceIsometry.complexToEuclideanPath (f x))
        (pathExitTime U (f x)).toNNReal))
      (ν.map (fun y => normalizedPrefixCurve
        (ReparamDistanceIsometry.complexToEuclideanPath (g y))
        (pathExitTime V (g y)).toNNReal)) < ENNReal.ofReal δ)
    (A : Set (ℝ≥0 → ℂ)) :
    μ {x | stopAtExit U (f x) ∈ A} ≤
      ν {y | ∃ p ∈ A, cmpEDist (stopAtExit V (g y)) p < ENNReal.ofReal (δ + ε)} +
        ENNReal.ofReal δ := by
  exact measure_extendedStoppedRay_le_of_levyProkhorovEDist_lt μ ν f g
    (fun x => pathExitTime U (f x)) (fun y => pathExitTime V (g y))
    hU hV hf hg hδ hε h A

end MatedCRT
