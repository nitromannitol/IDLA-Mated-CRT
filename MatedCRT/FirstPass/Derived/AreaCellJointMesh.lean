import MatedCRT.FirstPass.Derived.AreaCellCompactMeasurable

/-! # Joint continuity of area cells -/

set_option autoImplicit false

namespace MatedCRT

/-- A Euclidean curve cell varies continuously with its curve and positive mesh. -/
theorem continuous_euclideanCell_joint (k : ℤ) :
    Continuous (fun p : C(ℝ, ℂ) × {ε : ℝ // 0 < ε} =>
      euclideanCell p.2.1 p.1 p.1.continuous p.2.2 k) := by
  let e : C(ℂ, ReflectedGMS.Plane) :=
    ⟨Complex.orthonormalBasisOneI.repr, Complex.orthonormalBasisOneI.repr.continuous⟩
  have hcont : Continuous (fun p : C(ℝ, ℂ) × {ε : ℝ // 0 < ε} =>
      LatticeProb.shiftedCompactCell (e.comp p.1) p.2.1 0 k) := by
    exact (LatticeProb.continuous_shiftedCompactCell k).comp
      ((e.continuous_postcomp.comp continuous_fst).prodMk
        ((continuous_subtype_val.comp continuous_snd).prodMk continuous_const))
  convert hcont using 1
  funext p
  apply TopologicalSpace.NonemptyCompacts.ext
  rw [coe_euclideanCell, LatticeProb.coe_shiftedCompactCell]
  have hle : p.2.1 * ((k : ℝ) - 1 + 0) ≤ p.2.1 * ((k : ℝ) + 0) := by
    apply mul_le_mul_of_nonneg_left _ p.2.2.le
    linarith
  rw [Set.uIcc_of_le hle]
  simp only [add_zero, ContinuousMap.coe_comp, Function.comp_apply, cell, Set.image_image]
  rfl

/-- A Euclidean curve cell is jointly measurable in its curve and positive mesh. -/
theorem measurable_euclideanCell_joint (k : ℤ) :
    Measurable (fun p : C(ℝ, ℂ) × {ε : ℝ // 0 < ε} =>
      euclideanCell p.2.1 p.1 p.1.continuous p.2.2 k) :=
  (continuous_euclideanCell_joint k).measurable

end MatedCRT
