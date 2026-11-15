import MatedCRT.FirstPass.Derived.ShiftedBrownianCellLaw
import MatedCRT.FirstPass.Derived.ConeShiftedSelectedWalkLaw

/-! # Selected shifted walks from cell random walks -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory ReflectedGMS.GMS MatedCRTHarmonic.MatedCRT
open scoped NNReal

/-- Interpolating the inverse labels of any shifted cell walk gives the selected
Brownian-edge walk law at the corresponding selected starting cell. -/
theorem shiftedSelectedWalkLaw_eq_map_cellWalk
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (c : ℝ) (w : C(ℝ, ℝ × ℝ)) (x : ℂ) (m : ℝ≥0)
    (hlf : IsLocallyFinite ε ⟨fun t => w (t + c), w.continuous.comp (by fun_prop)⟩)
    (Q : Measure (ℕ → (shiftedAreaCellConfig h hε (c / ε)
      (bmEdgeCount ε (fun t => (w (t + c)).1) (fun t => (w (t + c)).2))).cells))
    (hQ : (shiftedAreaCellConfig h hε (c / ε)
      (bmEdgeCount ε (fun t => (w (t + c)).1) (fun t => (w (t + c)).2))).IsSRWLaw
      (shiftedEuclideanCellEquiv h hε (c / ε) (vertexOf ε (fun t => η (t + c)) x)) Q) :
    shiftedSelectedWalkLaw ε m c x η w =
      Q.map (fun p => interpPathCM (vertexPoint ε (fun t => η (t + c))) m.coe_nonneg
        (fun n => (shiftedEuclideanCellEquiv h hε (c / ε)).symm (p n))) := by
  let e := shiftedEuclideanCellEquiv h hε (c / ε)
  let k := vertexOf ε (fun t => η (t + c)) x
  let M := bmEdgeCount ε (fun t => (w (t + c)).1) (fun t => (w (t + c)).2)
  let C := shiftedAreaCellConfig h hε (c / ε) M
  let : Countable (Set.range (euclideanCell ε (fun t => η (t + ε * (c / ε)))
      (h.1.comp (continuous_id.add continuous_const)) hε)) := Countable.of_equiv ℤ e
  let : Countable C.cells := Countable.of_equiv ℤ e
  have hcanon : C.IsSRWLaw (e k) ((srwLaw M k).map (fun p n => e (p n))) :=
    shiftedAreaCellConfig_isSRWLaw_bmEdgeCount h hε (c / ε)
      ⟨fun t => w (t + c), w.continuous.comp (by fun_prop)⟩ hlf k
  have heq : Q = (srwLaw M k).map (fun p n => e (p n)) := hQ.unique hcanon
  have hemeas : Measurable (fun p : ℕ → ℤ => fun n => e (p n)) := by
    apply Measurable.of_eval
    intro n
    exact (measurable_of_countable e).comp (measurable_pi_apply n)
  have hinv : Measurable (fun p : ℕ → C.cells => fun n => e.symm (p n)) := by
    apply Measurable.of_eval
    intro n
    exact (measurable_of_countable (e.symm : C.cells → ℤ)).comp (measurable_pi_apply n)
  have hpath : Measurable (fun p : ℕ → C.cells =>
      interpPathCM (vertexPoint ε (fun t => η (t + c))) m.coe_nonneg
        (fun n => e.symm (p n))) :=
    (measurable_interpPathCM _ _).comp hinv
  change (srwLaw M k).map _ = Q.map (fun p : ℕ → C.cells =>
    interpPathCM (vertexPoint ε (fun t => η (t + c))) m.coe_nonneg
      (fun n => e.symm (p n)))
  rw [heq]
  have hmap := Measure.map_map (μ := srwLaw M k) hpath hemeas
  have hf : (fun p : ℕ → ℤ => interpPathCM (vertexPoint ε (fun t => η (t + c)))
      m.coe_nonneg (fun n => e.symm (e (p n)))) =
      interpPathCM (vertexPoint ε (fun t => η (t + c))) m.coe_nonneg := by
    funext p
    congr 1
    funext n
    exact e.symm_apply_apply (p n)
  change _ = (srwLaw M k).map (fun p : ℕ → ℤ =>
    interpPathCM (vertexPoint ε (fun t => η (t + c))) m.coe_nonneg
      (fun n => e.symm (e (p n)))) at hmap
  rw [hf] at hmap
  exact hmap.symm

end MatedCRT
end
