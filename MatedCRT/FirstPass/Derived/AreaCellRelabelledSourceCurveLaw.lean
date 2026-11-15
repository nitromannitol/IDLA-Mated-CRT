import MatedCRT.FirstPass.Derived.AreaCellSourceContinuousCurveLaw

/-! # Continuous exit-curve laws under area-cell relabelling -/

set_option autoImplicit false
noncomputable section

namespace MatedCRT

open MeasureTheory HarmonicBalls LatticeProb
open LatticeProb.ReparamDistanceIsometry LatticeProb.UnboundedRayIntervalIntegrand

/-- Relabelling an integer path measure by its area cells preserves the
continuously stopped curve law in the source curve space. -/
theorem areaCell_relabelled_sourceContinuousExitCurve_law
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (c : ℤ → ℤ → ℕ)
    {m : ℝ} (hm : 0 ≤ m) (a : ℝ) {U : Set ℂ} (hU : IsOpen U)
    (Q : Measure (ℕ → ℤ)) :
    (Q.map (fun x n => euclideanCellEquiv h hε (x n))).map
      (fun y => CurveSpaceComparison.isometryEquiv 2
        (normalizedPrefixCurve
          (ConstantStepInterpolation.continuousPlanePath m
            (fun n => a • areaCellRepresentative h hε c (y n)))
          (continuousExitTime (Complex.orthonormalBasisOneI.repr.symm ⁻¹' U) 0
            (ConstantStepInterpolation.continuousPlanePath m
              (fun n => a • areaCellRepresentative h hε c (y n)))).toNNReal)) =
    Q.map (fun x => CurveSpaceComparison.isometryEquiv 2
      (normalizedPrefixCurve
        (complexToEuclideanPath (a • interpPathCM (vertexPoint ε η) hm x))
        (pathExitTime U (a • interpPathCM (vertexPoint ε η) hm x)).toNNReal)) := by
  let e : ℤ ≃ (areaCellConfig h hε c).cells := euclideanCellEquiv h hε
  let _ : Countable (areaCellConfig h hε c).cells := Countable.of_equiv ℤ e
  have hf : Measurable (fun x : ℕ → ℤ => fun n => e (x n)) := by
    apply Measurable.of_eval
    intro n
    exact (measurable_of_countable e).comp (measurable_pi_apply n)
  have hg : Measurable (fun y : ℕ → (areaCellConfig h hε c).cells =>
      fun n => e.symm (y n)) := by
    apply Measurable.of_eval
    intro n
    exact (measurable_of_countable e.symm).comp (measurable_pi_apply n)
  have hmap : ((Q.map (fun x n => e (x n))).map (fun y n => e.symm (y n))) = Q := by
    rw [Measure.map_map hg hf]
    simp only [Function.comp_def, Equiv.symm_apply_apply]
    have hid : (fun x : ℕ → ℤ => fun n => x n) = id := by
      funext x n
      rfl
    rw [hid, Measure.map_id]
  have hsource := areaCell_sourceContinuousExitCurve_law h hε c hm a hU
    (Q.map (fun x n => e (x n)))
  have hmap' : ((Q.map (fun x n => euclideanCellEquiv h hε (x n))).map
      (fun y n => (euclideanCellEquiv h hε).symm (y n))) = Q := hmap
  apply hsource.trans
  exact congrArg (fun P : Measure (ℕ → ℤ) => P.map (fun x =>
    CurveSpaceComparison.isometryEquiv 2 (normalizedPrefixCurve
      (complexToEuclideanPath (a • interpPathCM (vertexPoint ε η) hm x))
      (pathExitTime U (a • interpPathCM (vertexPoint ε η) hm x)).toNNReal))) hmap'

end MatedCRT
end
