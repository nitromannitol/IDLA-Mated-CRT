import MatedCRT.FirstPass.Derived.BrownianExitLawIdentification
import MatedCRT.FirstPass.Derived.StandardBrownianCurveLaw
import LatticeProb.Topology.CurveSpaceComparison

/-!
# Stopped paths and curve classes

The distance modulo time parametrization `cmpEDist` of two paths stopped at their first exit times
equals the distance of their normalized prefix curve classes in the space of curves modulo
parametrization, and the stopped Brownian curve class is the class of the translated Brownian path
stopped at the exit time from the planar domain.
-/

set_option autoImplicit false

open MeasureTheory Set HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

namespace MatedCRT.StopAtExitCurveClass

open LatticeProb LatticeProb.ReparamDistanceIsometry LatticeProb.CurveSpaceComparison
open MatedCRT.TargetLawTemplateEvent MatedCRT.StopAtExitCmp

/-- A path that exits `V` at a finite time is stopped at that time. -/
theorem stopAtExit_eq_of_ne_top {V : Set ℂ} {f : ℝ≥0 → ℂ} (h : pathExitTime V f ≠ ⊤) :
    stopAtExit V f = fun t => f (min t (pathExitTime V f).toNNReal) := by
  funext t
  unfold stopAtExit
  simp [h]

/-- For two continuous paths with finite exit times, the distance modulo parametrization of the
stopped paths is the distance of their normalized prefix curve classes. -/
theorem cmpEDist_stopAtExit_eq_edist_normalizedPrefixCurve (V₁ V₂ : Set ℂ) (f g : C(ℝ≥0, ℂ))
    (hf : pathExitTime V₁ ⇑f ≠ ⊤) (hg : pathExitTime V₂ ⇑g ≠ ⊤) :
    cmpEDist (stopAtExit V₁ ⇑f) (stopAtExit V₂ ⇑g) =
      edist
        (isometryEquiv 2
          (normalizedPrefixCurve (complexToEuclideanPath f) (pathExitTime V₁ ⇑f).toNNReal))
        (isometryEquiv 2
          (normalizedPrefixCurve (complexToEuclideanPath g) (pathExitTime V₂ ⇑g).toNNReal)) := by
  rw [(isometryEquiv 2).isometry.edist_eq, stopAtExit_eq_of_ne_top hf, stopAtExit_eq_of_ne_top hg,
    ← complex_stoppedRay_eq_normalizedPrefixCurve f g]
  rfl

/-- The stopped Brownian curve class of a planar path `b`, read in Euclidean coordinates and
started at `z`, is the class of the translated path `z + b` stopped at its exit time from `U`. -/
theorem stoppedBrownianCurve_complexPathToEuc (U : Set ℂ) (z : ℂ) (b : ContinuousPath ℂ) :
    BouRabeeGwynne.stoppedBrownianCurve (Complex.orthonormalBasisOneI.repr '' U)
        (Complex.orthonormalBasisOneI.repr z) (complexPathToEuc b) =
      isometryEquiv 2
        (normalizedPrefixCurve (complexToEuclideanPath (translatePath z b))
          (pathExitTime U ⇑(translatePath z b)).toNNReal) := by
  have hT : BouRabeeGwynne.continuousExitTime (Complex.orthonormalBasisOneI.repr '' U)
      (Complex.orthonormalBasisOneI.repr z) (complexPathToEuc b) =
        pathExitTime U ⇑(translatePath z b) :=
    BrownianExitLawIdentification.continuousExitTime_complexPathToEuc U z b
  have key : ∀ s : ℝ≥0, Complex.orthonormalBasisOneI.repr z + complexPathToEuc b s =
      complexToEuclideanPath (translatePath z b) s := fun s => by
    rw [complexPathToEuc_apply]
    change _ = Complex.orthonormalBasisOneI.repr (translatePath z b s)
    rw [translatePath_apply, map_add, add_comm]
  unfold BouRabeeGwynne.stoppedBrownianCurve
  rw [← isometryEquiv_project]
  congr 1
  unfold normalizedPrefixCurve
  congr 1
  refine ContinuousMap.ext fun u => ?_
  simp only [BouRabeeGwynne.stoppedBrownianRepresentative, normalizedPathPrefix,
    ContinuousMap.coe_mk, hT]
  exact key _

end MatedCRT.StopAtExitCurveClass
