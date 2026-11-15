import MatedCRT.FirstPass.Derived.AreaCellConstantStepLaw
import MatedCRT.FirstPass.Derived.AreaCellLaw

/-! # Laws of relabelled constant-step paths -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory ReflectedGMS ReflectedGMS.GMS
open LatticeProb.ConstantStepInterpolation LatticeProb.ReparamDistanceIsometry
open LatticeProb.CellConfigWalk

/-- Relabelling integer trajectories by their cells before interpolation gives
exactly the embedded integer-walk path law. -/
theorem areaCell_constantStepPath_nested_map
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (c : ℤ → ℤ → ℕ)
    {m : ℝ} (hm : 0 ≤ m) (Q : Measure (ℕ → ℤ)) :
    (Q.map (fun x n => euclideanCellEquiv h hε (x n))).map
      (fun y => continuousPlanePath m (fun n => areaCellRepresentative h hε c (y n))) =
    Q.map (fun x => complexToEuclideanPath (interpPathCM (vertexPoint ε η) hm x)) := by
  classical
  let e := euclideanCellEquiv h hε
  let H := areaCellConfig h hε c
  have hF : Measurable (fun x : ℕ → ℤ => fun n => e (x n)) := by
    let _ : Countable H.cells := Countable.of_equiv ℤ e
    apply Measurable.of_eval
    intro n
    exact (measurable_of_countable e).comp (measurable_pi_apply n)
  have hG : Measurable (fun y : ℕ → H.cells =>
      fun n => areaCellRepresentative h hε c (y n)) := by
    let _ : Countable H.cells := Countable.of_equiv ℤ e
    apply Measurable.of_eval
    intro n
    exact (measurable_of_countable (areaCellRepresentative h hε c)).comp
      (measurable_pi_apply n)
  have hT : Measurable (fun y : ℕ → H.cells =>
      continuousPlanePath m (fun n => areaCellRepresentative h hε c (y n))) :=
    measurable_constantStepPath _ hG m
  change (Q.map (fun x : ℕ → ℤ => fun n => e (x n))).map
    (fun y : ℕ → H.cells => continuousPlanePath m
      (fun n => areaCellRepresentative h hε c (y n))) = _
  calc
    _ = Q.map (fun x => continuousPlanePath m
        (fun n => areaCellRepresentative h hε c (e (x n)))) := by
      exact Measure.map_map hT hF
    _ = _ := areaCell_constantStepPath_map h hε c hm Q

end MatedCRT
end
