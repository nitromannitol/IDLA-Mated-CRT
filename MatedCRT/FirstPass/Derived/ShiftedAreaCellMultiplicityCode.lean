import MatedCRT.FirstPass.Derived.ShiftedAreaCellCode

/-! # Codes of shifted area cells with measurable multiplicities -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set ReflectedGMS.GMS

/-- A valid shifted area-cell configuration has an almost-everywhere measurable
code when its labelled multiplicities are almost-everywhere measurable. -/
theorem aemeasurable_shiftedAreaCellConfig_code_of_multiplicity
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    {ε : ℝ} (hε : 0 < ε) (η : Ω → C(ℝ, ℂ))
    (θ : Ω → ℝ) (μ : Ω → Measure ℂ) (M : Ω → ℤ → ℤ → ℕ)
    (H : Ω → CellConfig) (hη : Measurable η) (hθ : Measurable θ)
    (hM : ∀ j k, AEMeasurable (fun ω => M ω j k) P)
    (hH : ∀ᵐ ω ∂P, ∃ h : IsAreaParametrized (μ ω) (η ω),
      H ω = shiftedAreaCellConfig h hε (θ ω) (M ω) ∧ (H ω).IsCellConfiguration) :
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
    apply (((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp_aemeasurable
      (hM j k))).congr
    filter_upwards [hH] with ω ⟨h, heq, _⟩
    rw [heq, hceq ω h j, hceq ω h k, shiftedAreaCellConfig_conductance]
    rfl

end MatedCRT
