import MatedCRT.FirstPass.Derived.AreaCellConfig

/-! # Cells containing the root of an area-parametrized curve -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set ReflectedGMS.GMS

/-- The cells immediately before and after time zero both contain the root. -/
theorem zero_mem_euclideanCell_zero_and_one {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε) (hη : η 0 = 0) :
    (0 : ReflectedGMS.Plane) ∈ (euclideanCell ε η h.1 hε 0 : Set ReflectedGMS.Plane) ∧
      (0 : ReflectedGMS.Plane) ∈ (euclideanCell ε η h.1 hε 1 : Set ReflectedGMS.Plane) := by
  constructor <;> rw [coe_euclideanCell]
  · refine ⟨0, ?_, by simp⟩
    refine ⟨0, ?_, hη⟩
    simp only [Int.cast_zero, zero_sub, mul_neg, mul_one, mul_zero, Set.mem_Icc]
    exact ⟨by linarith, le_rfl⟩
  · refine ⟨0, ?_, by simp⟩
    refine ⟨0, ?_, hη⟩
    simp only [Int.cast_one, sub_self, mul_zero, mul_one, Set.mem_Icc]
    exact ⟨le_rfl, hε.le⟩

/-- An area-parametrized curve has two distinct cells containing its root. -/
theorem exists_two_areaCellConfig_cells_containing_zero {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε) (hη : η 0 = 0)
    (m : ℤ → ℤ → ℕ) :
    ∃ A B : Cell, A ∈ (areaCellConfig h hε m).cells ∧
      B ∈ (areaCellConfig h hε m).cells ∧ A ≠ B ∧
      (0 : ReflectedGMS.Plane) ∈ (A : Set ReflectedGMS.Plane) ∧
      (0 : ReflectedGMS.Plane) ∈ (B : Set ReflectedGMS.Plane) := by
  refine ⟨euclideanCell ε η h.1 hε 0, euclideanCell ε η h.1 hε 1, ?_, ?_, ?_,
    zero_mem_euclideanCell_zero_and_one h hε hη⟩
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · intro heq
    have := euclideanCell_injective h hε heq
    norm_num at this

end MatedCRT
