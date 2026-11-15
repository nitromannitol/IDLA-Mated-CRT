import MatedCRT.FirstPass.S6j.LitUniformStartInvariance
import LatticeProb.Topology.UnboundedRayCurveLaw
import LatticeProb.Topology.ReparamDistanceIsometry

/-! # Ball clocks and stopped curve distances -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Metric Set HarmonicBalls LatticeProb
open LatticeProb.ReparamDistanceIsometry LatticeProb.UnboundedRayIntervalIntegrand
open scoped ENNReal NNReal

/-- The Euclidean-coordinate ball clock is the complex path's exit time. -/
theorem ballClock_complexToEuclideanPath (f : C(ℝ≥0, ℂ)) (r : ℝ) :
    ballClock (complexToEuclideanPath f) r = pathExitTime (ball (0 : ℂ) r) f := by
  have hm (t : ℝ≥0) : complexToEuclideanPath f t ∉
      ball (0 : EuclideanSpace ℝ (Fin 2)) r ↔ f t ∉ ball (0 : ℂ) r := by
    simp [complexToEuclideanPath, Metric.mem_ball]
  unfold ballClock LatticeProb.openExitTime pathExitTime
  refine le_antisymm ?_ ?_
  · refine le_sInf ?_
    rintro _ ⟨t, rfl, ht⟩
    exact iInf_le (fun s : {s : ℝ≥0 // complexToEuclideanPath f s ∉
      ball (0 : EuclideanSpace ℝ (Fin 2)) r} => (s.1 : ℝ≥0∞)) ⟨t, (hm t).2 ht⟩
  · refine le_iInf fun t => ?_
    exact sInf_le ⟨t.1, rfl, (hm t.1).1 t.2⟩

/-- At finite exits, the paper's stopped-ray distance equals the distance between
normalized finite curves in Euclidean coordinates. -/
theorem cmpEDist_stopAtExit_eq_normalizedPrefixCurve
    (f g : C(ℝ≥0, ℂ)) (U V : Set ℂ)
    (hf : pathExitTime U f ≠ ⊤) (hg : pathExitTime V g ≠ ⊤) :
    cmpEDist (stopAtExit U f) (stopAtExit V g) =
      edist (normalizedPrefixCurve (complexToEuclideanPath f) (pathExitTime U f).toNNReal)
        (normalizedPrefixCurve (complexToEuclideanPath g) (pathExitTime V g).toNNReal) := by
  have hfst : stopAtExit U f = fun t => f (min t (pathExitTime U f).toNNReal) := by
    funext t
    simp [stopAtExit, hf]
  have hsnd : stopAtExit V g = fun t => g (min t (pathExitTime V g).toNNReal) := by
    funext t
    simp [stopAtExit, hg]
  rw [hfst, hsnd]
  exact complex_stoppedRay_eq_normalizedPrefixCurve f g _ _

end MatedCRT
end
