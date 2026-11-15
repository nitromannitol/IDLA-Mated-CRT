import MatedCRT.FirstPass.Derived.AnisotropicBallExitContinuity
import MatedCRT.FirstPass.Derived.AnisotropicTargetUnbounded
import MatedCRT.FirstPass.Derived.PaperBallClockPrefix

/-! # Ball clock regularity under the anisotropic Brownian target -/

set_option autoImplicit false

open MeasureTheory Set Filter Topology Metric HarmonicBalls MarkovProcess
open MatedCRT.TargetLawTemplateEvent MatedCRT.StopAtExitCmp MatedCRT.TemplateEventCompactOpen
open ReflectedGMS.StatementIngredients
open LatticeProb.UnboundedRayIntervalIntegrand LatticeProb.ReparamDistanceIsometry
open scoped ENNReal NNReal

namespace MatedCRT

/-- The target path has a radius-continuous ball clock at each fixed positive radius. -/
theorem ae_continuousAt_ballClock_anisotropicBrownianTarget
    (target : AnisotropicBrownianTarget) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ (f : BouRabeeGwynne.BrownianPath 2) ∂(target.pathLaw : Measure _),
      ContinuousAt (fun s : ℝ => ballClock f s) r := by
  let F : ContinuousPath ℂ × ℝ → ℝ≥0∞ := fun p =>
    ContinuousPath.exitTime (ball (0 : ℂ) p.2) p.1
  have hmeas : MeasurableSet {f : BouRabeeGwynne.BrownianPath 2 |
      ContinuousAt F (eucPathToComplex f, r)} := by
    exact (IsGδ.setOfPred_continuousAt F).measurableSet.preimage
      ((continuous_eucPathToComplex.prodMk continuous_const).measurable)
  have hmap : Measurable (fun b : ContinuousPath ℂ =>
      linearImageBrownianPath target.factor (complexPathToEuc b)) :=
    (measurable_linearImageBrownianPath _).comp measurable_complexPathToEuc
  have hjoint : ∀ᵐ (f : BouRabeeGwynne.BrownianPath 2) ∂(target.pathLaw : Measure _),
      ContinuousAt F (eucPathToComplex f, r) := by
    rw [pathLaw_eq_map, ae_map_iff hmap.aemeasurable hmeas]
    have h0 : (matrixEquiv (isUnit_det_factor target)) 0 ∈ ball (0 : ℂ) r := by
      simpa [mem_ball] using hr
    filter_upwards [ae_continuousAt_ball_exitTime_linearImage_planarBrownian
      (matrixEquiv (isUnit_det_factor target)) hr h0] with b hb
    rw [linearImageBrownianPath_complexPathToEuc_eq (isUnit_det_factor target),
      eucPathToComplex_complexPathToEuc]
    exact hb
  filter_upwards [hjoint] with f hf
  have hcoord : complexToEuclideanPath (eucPathToComplex f) = f := by
    apply ContinuousMap.ext
    intro t
    change Complex.orthonormalBasisOneI.repr (Complex.orthonormalBasisOneI.repr.symm (f t)) = f t
    exact Complex.orthonormalBasisOneI.repr.apply_symm_apply (f t)
  have hclock (s : ℝ) : ballClock f s = F (eucPathToComplex f, s) := by
    calc
      ballClock f s = ballClock (complexToEuclideanPath (eucPathToComplex f)) s := by rw [hcoord]
      _ = pathExitTime (ball (0 : ℂ) s) (eucPathToComplex f) :=
        ballClock_complexToEuclideanPath _ s
      _ = F (eucPathToComplex f, s) := rfl
  simp_rw [hclock]
  exact hf.comp (continuous_const.prodMk continuous_id).continuousAt

/-- The target supplies the path regularity required by neighboring-exit estimates. -/
theorem ae_ballClock_regular_anisotropicBrownianTarget
    (target : AnisotropicBrownianTarget) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ (f : BouRabeeGwynne.BrownianPath 2) ∂(target.pathLaw : Measure _),
      ¬ Bornology.IsBounded (Set.range f) ∧
        ContinuousAt (fun s : ℝ => ballClock f s) r := by
  filter_upwards [ae_unbounded_range_anisotropicBrownianTarget target,
    ae_continuousAt_ballClock_anisotropicBrownianTarget target hr] with f hf hc
  exact ⟨hf, hc⟩

end MatedCRT
