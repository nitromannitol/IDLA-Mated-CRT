import MatedCRT.FirstPass.Derived.ShiftedAreaCellConfig
import MatedCRT.FirstPass.Derived.JointShiftedMeshMultiplicity
import LatticeProb.Prob.EnumeratedCellCodeAEModification

/-! # Codes for shifted area-cell configurations -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set ReflectedGMS.GMS

/-- A matching almost-everywhere valid shifted area-cell configuration has an
almost-everywhere measurable code. The phase is measured in mesh units. -/
theorem aemeasurable_shiftedAreaCellConfig_code
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    {ε : ℝ} (hε : 0 < ε) (η : Ω → C(ℝ, ℂ)) (w : Ω → C(ℝ, ℝ × ℝ))
    (θ : Ω → ℝ) (μ : Ω → Measure ℂ) (H : Ω → CellConfig)
    (hη : Measurable η) (hw : Measurable w) (hθ : Measurable θ)
    (hH : ∀ᵐ ω ∂P, ∃ h : IsAreaParametrized (μ ω) (η ω),
      H ω = shiftedAreaCellConfig h hε (θ ω)
        (bmEdgeCount ε (fun t => (w ω (t + ε * θ ω)).1)
          (fun t => (w ω (t + ε * θ ω)).2)) ∧ (H ω).IsCellConfiguration) :
    AEMeasurable (fun ω => (H ω).code) P := by
  let e : C(ℂ, ReflectedGMS.Plane) :=
    ⟨Complex.orthonormalBasisOneI.repr, Complex.orthonormalBasisOneI.repr.continuous⟩
  let C : ℤ → Ω → Cell := fun k ω =>
    LatticeProb.shiftedCompactCell (e.comp (η ω)) ε (θ ω) k
  have hC : ∀ k, Measurable (C k) := by
    intro k
    exact (LatticeProb.continuous_shiftedCompactCell k).measurable.comp
      ((e.continuous_postcomp.measurable.comp hη).prodMk (measurable_const.prodMk hθ))
  have hceq : ∀ ω (h : IsAreaParametrized (μ ω) (η ω)) k,
      C k ω = shiftedEuclideanCellEquiv h hε (θ ω) k := by
    intro ω h k
    apply TopologicalSpace.NonemptyCompacts.ext
    change (LatticeProb.shiftedCompactCell (e.comp (η ω)) ε (θ ω) k :
      Set ReflectedGMS.Plane) =
      (euclideanCell ε (fun t => η ω (t + ε * θ ω))
        (h.1.comp (continuous_id.add continuous_const)) hε k : Set ReflectedGMS.Plane)
    rw [coe_euclideanCell, LatticeProb.coe_shiftedCompactCell]
    have ht := shiftedCompactCell_eq_cell_timeShift (η ω) hε.le (θ ω) k
    rw [LatticeProb.coe_shiftedCompactCell] at ht
    change Set.image (fun t => Complex.orthonormalBasisOneI.repr (η ω t)) _ = _
    simpa only [Set.image_image, Function.comp_def] using
      congrArg (Set.image Complex.orthonormalBasisOneI.repr) ht
  apply LatticeProb.aemeasurable_enumeratedCell_code_of_ae P H C
  · filter_upwards [hH] with ω ⟨h, heq, hvalid⟩
    refine ⟨hvalid, ?_⟩
    rw [heq]
    change Set.range (fun k => (shiftedEuclideanCellEquiv h hε (θ ω) k).1) = _
    congr 1
    funext k
    exact (hceq ω h k).symm
  · exact fun k => (hC k).aemeasurable
  · intro j k
    have harg : Measurable (fun ω => (w ω, (⟨ε, hε⟩ : {r : ℝ // 0 < r}), θ ω)) :=
      hw.prodMk (measurable_const.prodMk hθ)
    have hm := (measurable_bmEdgeCount_shiftedMesh j k).comp harg
    apply ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp hm).aemeasurable.congr
    filter_upwards [hH] with ω ⟨h, heq, _⟩
    rw [heq, hceq ω h j, hceq ω h k, shiftedAreaCellConfig_conductance]
    rfl

end MatedCRT
