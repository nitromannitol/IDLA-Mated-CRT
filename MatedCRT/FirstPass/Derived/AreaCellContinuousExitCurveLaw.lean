import MatedCRT.FirstPass.Derived.AreaCellNormalizedExitCurve
import MatedCRT.FirstPass.Derived.AreaCellNestedPathLaw

/-! # Continuous exit curves on area-cell trajectories -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace MatedCRT

open MeasureTheory HarmonicBalls LatticeProb
open LatticeProb.ReparamDistanceIsometry LatticeProb.UnboundedRayIntervalIntegrand

/-- The normalized continuous exit curve is measurable on cell trajectories. -/
theorem measurable_areaCell_continuousExitCurve
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (c : ℤ → ℤ → ℕ)
    {m : ℝ} (hm : 0 ≤ m) (a : ℝ) {U : Set ℂ} (hU : IsOpen U) :
    Measurable (fun y : ℕ → (areaCellConfig h hε c).cells =>
      normalizedPrefixCurve
        (ConstantStepInterpolation.continuousPlanePath m
          (fun n => a • areaCellRepresentative h hε c (y n)))
        (continuousExitTime (Complex.orthonormalBasisOneI.repr.symm ⁻¹' U) 0
          (ConstantStepInterpolation.continuousPlanePath m
            (fun n => a • areaCellRepresentative h hε c (y n)))).toNNReal) := by
  let e : ℤ ≃ (areaCellConfig h hε c).cells := euclideanCellEquiv h hε
  let _ : Countable (areaCellConfig h hε c).cells := Countable.of_equiv ℤ e
  have hl : Measurable (fun y : ℕ → (areaCellConfig h hε c).cells =>
      fun n => e.symm (y n)) := by
    apply Measurable.of_eval
    intro n
    exact (measurable_of_countable e.symm).comp (measurable_pi_apply n)
  have hc := (measurable_areaCell_scaled_normalizedExitCurve h hε c hm a hU).comp hl
  change Measurable (fun y : ℕ → (areaCellConfig h hε c).cells =>
      normalizedPrefixCurve
        (ConstantStepInterpolation.continuousPlanePath m
          (fun n => a • areaCellRepresentative h hε c (e (e.symm (y n)))))
        (continuousExitTime (Complex.orthonormalBasisOneI.repr.symm ⁻¹' U) 0
          (ConstantStepInterpolation.continuousPlanePath m
            (fun n => a • areaCellRepresentative h hε c (e (e.symm (y n)))))).toNNReal) at hc
  simpa only [Equiv.apply_symm_apply] using hc

/-- Relabelling integer paths by cells preserves the continuous exit-curve law. -/
theorem areaCell_continuousExitCurve_relabelled_law
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (c : ℤ → ℤ → ℕ)
    {m : ℝ} (hm : 0 ≤ m) (a : ℝ) {U : Set ℂ} (hU : IsOpen U)
    (Q : Measure (ℕ → ℤ)) :
    (Q.map (fun (x : ℕ → ℤ) (n : ℕ) =>
      (euclideanCellEquiv h hε (x n) : (areaCellConfig h hε c).cells))).map
      (fun y : ℕ → (areaCellConfig h hε c).cells => normalizedPrefixCurve
        (ConstantStepInterpolation.continuousPlanePath m
          (fun n => a • areaCellRepresentative h hε c (y n)))
        (continuousExitTime (Complex.orthonormalBasisOneI.repr.symm ⁻¹' U) 0
          (ConstantStepInterpolation.continuousPlanePath m
            (fun n => a • areaCellRepresentative h hε c (y n)))).toNNReal) =
    Q.map (fun x => normalizedPrefixCurve
      (complexToEuclideanPath (a • interpPathCM (vertexPoint ε η) hm x))
      (pathExitTime U (a • interpPathCM (vertexPoint ε η) hm x)).toNNReal) := by
  let e : ℤ ≃ (areaCellConfig h hε c).cells := euclideanCellEquiv h hε
  have he : Measurable (fun x : ℕ → ℤ => fun n => e (x n)) := by
    apply Measurable.of_eval
    intro n
    exact (measurable_of_countable e).comp (measurable_pi_apply n)
  have hmap := Measure.map_map (μ := Q)
    (measurable_areaCell_continuousExitCurve h hε c hm a hU) he
  calc
    _ = Q.map (fun x => normalizedPrefixCurve
        (ConstantStepInterpolation.continuousPlanePath m
          (fun n => a • areaCellRepresentative h hε c (e (x n))))
        (continuousExitTime (Complex.orthonormalBasisOneI.repr.symm ⁻¹' U) 0
          (ConstantStepInterpolation.continuousPlanePath m
            (fun n => a • areaCellRepresentative h hε c (e (x n))))).toNNReal) :=
      hmap
    _ = _ := areaCell_scaled_normalizedExitCurve_map h hε c hm a U Q

end MatedCRT
end
