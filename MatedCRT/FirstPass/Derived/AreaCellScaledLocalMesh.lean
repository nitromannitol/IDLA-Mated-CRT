import MatedCRT.FirstPass.Derived.AreaCellDiameter

/-! # Scaled local diameter bounds for area cells -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Metric Set ReflectedGMS.GMS

/-- A unit-ball diameter estimate controls cells whose scaled image meets a
region contained in the ball of radius equal to the positive scale. -/
theorem areaCellConfig_scaled_local_mesh_of_unit_ball_diam
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ) {a : ℝ} (ha : 0 < a)
    (W : Set ReflectedGMS.Plane) (hW : W ⊆ ball 0 a) (d : ℝ)
    (hd : ∀ k, (cell ε η k ∩ ball 0 1).Nonempty → diam (cell ε η k) ≤ d) :
    ∀ K : (areaCellConfig h hε m).cells,
      (∃ z ∈ (K.1 : Set ReflectedGMS.Plane), a • z ∈ W) →
        diam (K.1 : Set ReflectedGMS.Plane) ≤ d := by
  intro K hK
  obtain ⟨z, hz, hzW⟩ := hK
  have hnorm : ‖z‖ < 1 := by
    have hscaled : ‖a • z‖ < a := by
      simpa only [mem_ball_zero_iff] using hW hzW
    rw [norm_smul, Real.norm_of_nonneg ha.le] at hscaled
    nlinarith
  have hd' : ∀ k ∈ cellVertices ε η
      (Complex.orthonormalBasisOneI.repr ⁻¹'
        (Complex.orthonormalBasisOneI.repr '' ball (0 : ℂ) 1)),
      diam (cell ε η k) ≤ d := by
    intro k hk
    apply hd k
    simpa only [Complex.orthonormalBasisOneI.repr.injective.preimage_image,
      cellVertices, mem_ofPred_eq] using hk
  apply areaCellConfig_diam_le_of_meeting h hε m
    (Complex.orthonormalBasisOneI.repr '' ball (0 : ℂ) 1) d hd' K
  refine ⟨z, hz, ?_⟩
  refine ⟨Complex.orthonormalBasisOneI.repr.symm z, ?_,
    Complex.orthonormalBasisOneI.repr.apply_symm_apply z⟩
  simpa only [mem_ball_zero_iff, Complex.orthonormalBasisOneI.repr.symm.norm_map] using hnorm

end MatedCRT
