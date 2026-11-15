import MatedCRT.FirstPass.Derived.AreaCellScaledLocalMesh

/-! # Buffered unit-ball diameter bounds for area cells -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Metric Set ReflectedGMS.GMS

/-- A domain radius margin and a unit-ball diameter bound supply the buffer
and scaled local mesh used for area-cell walk comparisons. -/
theorem areaCellConfig_unit_ball_buffer_and_scaled_local_mesh
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ) {a : ℝ} (ha : 0 < a)
    (Uc : Set ℂ) (r d : ℝ) (hU : Uc ⊆ ball 0 r) (hmargin : r + a * d ≤ a)
    (hd : ∀ k, (cell ε η k ∩ ball 0 1).Nonempty → diam (cell ε η k) ≤ d) :
    (∀ x ∈ (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc),
      closedBall x (a * d) ⊆ ball 0 a) ∧
    (∀ K : (areaCellConfig h hε m).cells,
      (∃ z ∈ (K.1 : Set ReflectedGMS.Plane), a • z ∈ ball 0 a) →
        diam (K.1 : Set ReflectedGMS.Plane) ≤ d) := by
  constructor
  · intro x hx
    have hxnorm : ‖x‖ < r := by
      have hx' := hU hx
      simpa only [mem_ball_zero_iff, Complex.orthonormalBasisOneI.repr.symm.norm_map] using hx'
    apply closedBall_subset_ball'
    rw [dist_zero_right]
    linarith
  · exact areaCellConfig_scaled_local_mesh_of_unit_ball_diam h hε m ha
      (ball 0 a) (Subset.rfl) d hd

end MatedCRT
