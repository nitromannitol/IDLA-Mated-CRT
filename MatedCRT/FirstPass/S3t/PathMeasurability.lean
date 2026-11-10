import MatedCRT.FirstPass.S3t.Defs
import MarkovProcess.Path.ExitTimeShift

/-!
# Stopped occupation on the continuous-path carrier (fp-S3t-four-binder, z8)

Answer 46(a3) of `notes/fp-gaps/CHATGPT-216-idla-hdet-truncated-gaps-PRO.md` (sections 1 and 2, lines 423-549): the stopped
occupation `∫_{(0, min (T, τ_D)]} g(w_t) dt` is Borel on the path space `ContinuousPath ℂ = C(ℝ≥0, ℂ)`, with its Borel
σ-algebra `MarkovProcess.ContinuousPath.instMeasurableSpace`, where `τ_D` is the exit time of the open set `D`
(Duplantier–Sheffield truncated occupation; potential-theoretic exit time of Armitage–Gardiner).
The exit time is Borel on path space by `MarkovProcess.ContinuousPath.measurable_exitTime`.
-/

open MeasureTheory Set Filter Topology MarkovProcess
open _root_.HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.TruncatedLaws

/-- The stopped occupation `∫_{(0, min (T, τ_D)]} g(w_t) dt` of a continuous path `w : ContinuousPath ℂ`
(the carrier on which the Brownian side `planarBrownianMotion` is a measure). -/
noncomputable def stoppedOccupationC (D : Set ℂ) (T : ℝ) (g : ℂ → ℝ) (w : ContinuousPath ℂ) : ℝ :=
  stoppedOccupation D T g w

/-- On `ContinuousPath ℂ` the Harmonic-Balls exit time `pathExitTime` is MarkovProcess's `ContinuousPath.exitTime`. -/
theorem pathExitTime_coe_eq_exitTime (D : Set ℂ) (w : ContinuousPath ℂ) :
    pathExitTime D (w : ℝ≥0 → ℂ) = MarkovProcess.ContinuousPath.exitTime D w := rfl

/-- The exit time of an open set is a Borel function on the continuous-path carrier
(`MarkovProcess.ContinuousPath.measurable_exitTime`, `Path/ExitTimeShift.lean:115`). -/
theorem measurable_pathExitTime_continuousPath {D : Set ℂ} (hD : IsOpen D) :
    Measurable (fun w : ContinuousPath ℂ => pathExitTime D (w : ℝ≥0 → ℂ)) :=
  MarkovProcess.ContinuousPath.measurable_exitTime D hD

/-- Borel measurability of the stopped occupation of an open set `D` on the continuous-path carrier, for a continuous
integrand `g`. Proof as `MatedCRT.TruncatedLaws.measurable_stoppedOccupation_interpolatedWalk` (Integrate.lean:112):
Carathéodory (continuity in the time variable, measurability in the path) and Fubini on `ℝ × ContinuousPath ℂ`. -/
theorem measurable_stoppedOccupationC {D : Set ℂ} (hD : IsOpen D) {g : ℂ → ℝ} (hg : Continuous g) (T : ℝ) :
    Measurable (stoppedOccupationC D T g) := by
  have hu : Measurable (fun w : ContinuousPath ℂ =>
      (min (ENNReal.ofReal T) (pathExitTime D (w : ℝ≥0 → ℂ))).toReal) :=
    ENNReal.measurable_toReal.comp (measurable_const.min (measurable_pathExitTime_continuousPath hD))
  have hG : Measurable (Function.uncurry fun (t : ℝ) (w : ContinuousPath ℂ) => g (w t.toNNReal)) :=
    measurable_uncurry_of_continuous_of_measurable
      (fun w => hg.comp (w.continuous.comp continuous_real_toNNReal))
      (fun t => hg.measurable.comp (continuous_eval_const t.toNNReal).measurable)
  set E : Set (ℝ × ContinuousPath ℂ) :=
    {q | 0 < q.1} ∩ {q | q.1 ≤ (min (ENNReal.ofReal T) (pathExitTime D (q.2 : ℝ≥0 → ℂ))).toReal} with hE
  have hEm : MeasurableSet E :=
    (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_le measurable_fst (hu.comp measurable_snd))
  have hsm : StronglyMeasurable (fun w : ContinuousPath ℂ => ∫ t : ℝ,
      E.indicator (Function.uncurry fun (t : ℝ) (w : ContinuousPath ℂ) => g (w t.toNNReal)) (t, w)) :=
    StronglyMeasurable.integral_prod_left' (hG.indicator hEm).stronglyMeasurable
  have heq : stoppedOccupationC D T g = fun w : ContinuousPath ℂ => ∫ t : ℝ,
      E.indicator (Function.uncurry fun (t : ℝ) (w : ContinuousPath ℂ) => g (w t.toNNReal)) (t, w) := by
    funext w
    unfold stoppedOccupationC stoppedOccupation
    rw [← integral_indicator measurableSet_Ioc]
    congr 1
  rw [heq]
  exact hsm.measurable

#print axioms measurable_stoppedOccupationC

end MatedCRT.TruncatedLaws
