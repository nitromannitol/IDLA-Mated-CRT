import MatedCRT.FirstPass.Derived.BrownianExitKernelContinuity
import MatedCRT.FirstPass.Derived.UniformStartStoppedBM
import LatticeProb.Bonanno.BouRabeeGwynne.ContinuousExitProperties
import LatticeProb.Bonanno.BouRabeeGwynne.StoppedBrownianMeasurable

/-! Identification of the planar and Euclidean Brownian exit clocks. -/

set_option autoImplicit false

open MeasureTheory Set HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

namespace MatedCRT.BrownianExitLawIdentification

open TargetLawTemplateEvent StopAtExitCmp BouRabeeGwynne

/-- Reading a translated planar path in Euclidean coordinates preserves its first exit time. -/
theorem continuousExitTime_complexPathToEuc (U : Set ℂ) (z : ℂ)
    (b : ContinuousPath ℂ) :
    continuousExitTime (Complex.orthonormalBasisOneI.repr '' U)
      (Complex.orthonormalBasisOneI.repr z) (complexPathToEuc b) =
      ContinuousPath.exitTime U (translatePath z b) := by
  have hmem (t : ℝ≥0) :
      Complex.orthonormalBasisOneI.repr z + complexPathToEuc b t ∉
          Complex.orthonormalBasisOneI.repr '' U ↔ translatePath z b t ∉ U := by
    rw [complexPathToEuc_apply, ← map_add, add_comm, translatePath_apply]
    apply not_congr
    constructor
    · rintro ⟨x, hx, heq⟩
      exact Complex.orthonormalBasisOneI.repr.injective heq ▸ hx
    · intro hx
      exact ⟨_, hx, rfl⟩
  rw [continuousExitTime, ContinuousPath.exitTime]
  apply le_antisymm
  · apply le_sInf
    rintro s ⟨t, rfl, ht⟩
    exact iInf_le_of_le ⟨t, (hmem t).2 ht⟩ le_rfl
  · apply le_iInf
    rintro ⟨t, ht⟩
    exact sInf_le ⟨t, rfl, (hmem t).1 ht⟩

/-- The stopped Euclidean Brownian endpoint has the planar first-exit law in coordinates. -/
theorem stoppedBrownianLaw_endPoint_eq (U : Set ℂ) (hU : IsOpen U) (z : ℂ)
    (μ : Measure (BrownianPath 2)) (hμ : IsStandardBrownianLaw μ) :
    (stoppedBrownianLaw (Complex.orthonormalBasisOneI.repr '' U)
      (Complex.orthonormalBasisOneI.repr z) μ).map CurveSpace.endPoint =
      ((planarBrownianExitProbability U hU z : ProbabilityMeasure ℂ) : Measure ℂ).map
        Complex.orthonormalBasisOneI.repr := by
  have hV : IsOpen (Complex.orthonormalBasisOneI.repr '' U) :=
    Complex.orthonormalBasisOneI.repr.toHomeomorph.isOpenMap U hU
  have hf : Measurable (fun ω : ContinuousPath ℂ =>
      ω ((ContinuousPath.exitTime U ω).toNNReal)) := by
    simpa using ContinuousPath.measurable_eval_untopD_stoppingTime
      (ContinuousPath.exitTime U) (ContinuousPath.isStoppingTime_exitTime U hU)
  rw [stoppedBrownianLaw,
    Measure.map_map CurveSpace.continuous_endPoint.measurable
      (measurable_stoppedBrownianCurve hV _), eq_map_complexPathToEuc hμ,
    Measure.map_map (CurveSpace.continuous_endPoint.measurable.comp
      (measurable_stoppedBrownianCurve hV _)) measurable_complexPathToEuc]
  change _ = ((planarBrownianMotion z).map (fun ω =>
    ω ((ContinuousPath.exitTime U ω).toNNReal))).map Complex.orthonormalBasisOneI.repr
  rw [Measure.map_map Complex.orthonormalBasisOneI.repr.continuous.measurable hf,
    ← map_translatePath_planarBrownianMotion z,
    Measure.map_map (Complex.orthonormalBasisOneI.repr.continuous.measurable.comp hf)
      (translatePath z).measurable]
  congr 1
  funext b
  simp only [Function.comp_apply, stoppedBrownianCurve_endPoint,
    continuousExitTime_complexPathToEuc, complexPathToEuc_apply,
    translatePath_apply, map_add, add_comm]

end MatedCRT.BrownianExitLawIdentification
