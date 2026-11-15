import MatedCRT.FirstPass.Derived.AreaCellContinuousExitCurveLaw
import LatticeProb.Topology.CurveSpaceComparison

/-! # Source-space laws of continuous area-cell exit curves -/

set_option autoImplicit false
noncomputable section

namespace MatedCRT

open MeasureTheory HarmonicBalls LatticeProb
open LatticeProb.ReparamDistanceIsometry LatticeProb.UnboundedRayIntervalIntegrand

/-- Relabelling any area-cell trajectory measure by integer vertices preserves
its continuously stopped curve law in the source curve space. -/
theorem areaCell_sourceContinuousExitCurve_law
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (c : ℤ → ℤ → ℕ)
    {m : ℝ} (hm : 0 ≤ m) (a : ℝ) {U : Set ℂ} (hU : IsOpen U)
    (P : Measure (ℕ → (areaCellConfig h hε c).cells)) :
    P.map (fun y => CurveSpaceComparison.isometryEquiv 2
      (normalizedPrefixCurve
        (ConstantStepInterpolation.continuousPlanePath m
          (fun n => a • areaCellRepresentative h hε c (y n)))
        (continuousExitTime (Complex.orthonormalBasisOneI.repr.symm ⁻¹' U) 0
          (ConstantStepInterpolation.continuousPlanePath m
            (fun n => a • areaCellRepresentative h hε c (y n)))).toNNReal)) =
    (P.map (fun y n => (euclideanCellEquiv h hε).symm (y n))).map
      (fun x => CurveSpaceComparison.isometryEquiv 2
        (normalizedPrefixCurve
          (complexToEuclideanPath (a • interpPathCM (vertexPoint ε η) hm x))
          (pathExitTime U (a • interpPathCM (vertexPoint ε η) hm x)).toNNReal)) := by
  let e : ℤ ≃ (areaCellConfig h hε c).cells := euclideanCellEquiv h hε
  let _ : Countable (areaCellConfig h hε c).cells := Countable.of_equiv ℤ e
  have he : Measurable (fun y : ℕ → (areaCellConfig h hε c).cells =>
      fun n => (euclideanCellEquiv h hε).symm (y n)) := by
    change Measurable (fun y : ℕ → (areaCellConfig h hε c).cells =>
      fun n => e.symm (y n))
    apply Measurable.of_eval
    intro n
    exact (measurable_of_countable e.symm).comp (measurable_pi_apply n)
  have hp : Measurable (fun x : ℕ → ℤ =>
      a • interpPathCM (vertexPoint ε η) hm x) :=
    ((continuous_interpPathCM (vertexPoint ε η) hm).const_smul a).measurable
  have hg := (CurveSpaceComparison.isometryEquiv 2).continuous.measurable.comp
    ((measurable_paperNormalizedExitCurve hU).comp hp)
  change Measurable (fun x : ℕ → ℤ => CurveSpaceComparison.isometryEquiv 2
    (normalizedPrefixCurve
      (complexToEuclideanPath (a • interpPathCM (vertexPoint ε η) hm x))
      (pathExitTime U (a • interpPathCM (vertexPoint ε η) hm x)).toNNReal)) at hg
  rw [Measure.map_map hg he]
  congr 1
  funext y
  have heq := areaCell_scaled_normalizedExitCurve_eq h hε c hm a
    (fun n => e.symm (y n)) U
  change normalizedPrefixCurve
      (ConstantStepInterpolation.continuousPlanePath m
        (fun n => a • areaCellRepresentative h hε c (e (e.symm (y n)))))
      (continuousExitTime (Complex.orthonormalBasisOneI.repr.symm ⁻¹' U) 0
        (ConstantStepInterpolation.continuousPlanePath m
          (fun n => a • areaCellRepresentative h hε c (e (e.symm (y n)))))).toNNReal =
    normalizedPrefixCurve
      (complexToEuclideanPath (a • interpPathCM (vertexPoint ε η) hm (fun n => e.symm (y n))))
      (pathExitTime U (a • interpPathCM (vertexPoint ε η) hm (fun n => e.symm (y n)))).toNNReal at heq
  simp only [Equiv.apply_symm_apply] at heq
  exact congrArg (CurveSpaceComparison.isometryEquiv 2) heq

end MatedCRT
end
