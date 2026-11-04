import MatedCRT.Proofs.Sec4.ConvergenceDivisible.UnitOscillationMax
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Process.FiniteDimensionalLaws

/-! # Law of the recentered Brownian shift -/

namespace MatedCRT

open MeasureTheory ProbabilityTheory MarkovProcess
open scoped NNReal

/-- The canonical continuous-path Brownian motion has the standard
finite-dimensional Brownian laws. -/
theorem canonical_isPreBrownianReal :
    IsPreBrownianReal (fun (t : ℝ≥0) (w : ContinuousPath ℝ) => w t)
      (brownianMotion 0) := by
  apply ProbabilityTheory.HasIndepIncrements.isPreBrownianReal_of_hasLaw
  · intro t
    simpa using (isBrownianReal_brownianMotion 0).hasLaw_eval t
  · simpa [ProbabilityTheory.HasIndepIncrements, MarkovProcess.HasIndepIncrements] using
      hasIndepIncrements_brownianMotion 0

/-- The centered future increments and the original canonical process have
the same law as functions of time. -/
theorem brownian_centered_shift_identDistrib (s : ℝ≥0) :
    IdentDistrib (fun (w : ContinuousPath ℝ) (t : ℝ≥0) => w (s + t) - w s)
      (fun (w : ContinuousPath ℝ) (t : ℝ≥0) => w t) (brownianMotion 0) (brownianMotion 0) := by
  let X : ℝ≥0 → ContinuousPath ℝ → ℝ := fun t w => w (s + t) - w s
  let Y : ℝ≥0 → ContinuousPath ℝ → ℝ := fun t w => w t
  have hX : AEMeasurable (fun (w : ContinuousPath ℝ) t => X t w) (brownianMotion 0) := by
    apply Measurable.aemeasurable
    exact Measurable.of_eval fun t =>
      (ContinuousPath.measurable_coordinateProcess (s + t)).sub
        (ContinuousPath.measurable_coordinateProcess s)
  have hY : AEMeasurable (fun (w : ContinuousPath ℝ) t => Y t w) (brownianMotion 0) := by
    apply Measurable.aemeasurable
    exact Measurable.of_eval fun t => ContinuousPath.measurable_coordinateProcess t
  apply (identDistrib_iff_forall_finset_identDistrib hX hY).mpr
  intro I
  exact (canonical_isPreBrownianReal.shift s |>.hasLaw I).identDistrib
    (canonical_isPreBrownianReal.hasLaw I)

end MatedCRT
