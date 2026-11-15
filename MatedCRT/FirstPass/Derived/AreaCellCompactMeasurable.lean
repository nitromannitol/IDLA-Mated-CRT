import MatedCRT.FirstPass.Derived.AreaCellConfig
import LatticeProb.Topology.CompactCurveRange

/-! # Measurability of compact curve cells -/

set_option autoImplicit false

open Set

namespace MatedCRT

/-- A fixed positive-mesh Euclidean cell varies continuously with its curve. -/
theorem continuous_euclideanCell (ε : ℝ) (hε : 0 < ε) (k : ℤ) :
    Continuous (fun η : C(ℝ, ℂ) => euclideanCell ε η η.continuous hε k) := by
  let e : C(ℂ, ReflectedGMS.Plane) :=
    ⟨Complex.orthonormalBasisOneI.repr, Complex.orthonormalBasisOneI.repr.continuous⟩
  have hcont : Continuous (fun η : C(ℝ, ℂ) =>
      LatticeProb.shiftedCompactCell (e.comp η) ε 0 k) := by
    exact (LatticeProb.continuous_shiftedCompactCell k).comp
      (e.continuous_postcomp.prodMk (continuous_const.prodMk continuous_const))
  convert hcont using 1
  funext η
  apply TopologicalSpace.NonemptyCompacts.ext
  rw [coe_euclideanCell, LatticeProb.coe_shiftedCompactCell]
  have hle : ε * ((k : ℝ) - 1 + 0) ≤ ε * ((k : ℝ) + 0) := by
    apply mul_le_mul_of_nonneg_left _ hε.le
    linarith
  rw [uIcc_of_le hle]
  simp only [add_zero, ContinuousMap.coe_comp, Function.comp_apply, cell, Set.image_image]
  rfl

/-- A fixed positive-mesh Euclidean cell is a measurable function of its curve. -/
theorem measurable_euclideanCell (ε : ℝ) (hε : 0 < ε) (k : ℤ) :
    Measurable (fun η : C(ℝ, ℂ) => euclideanCell ε η η.continuous hε k) :=
  (continuous_euclideanCell ε hε k).measurable

end MatedCRT
