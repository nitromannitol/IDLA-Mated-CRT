import MatedCRT.Defs.Setting
import Mathlib.Analysis.Complex.Basic

/-! # Affine interpolation of embedded walks -/

set_option autoImplicit false

noncomputable section

open scoped NNReal

namespace MatedCRT

/-- The real-coordinate image of the embedded walk is the affine interpolation
of the real-coordinate images of its vertices. -/
theorem repr_interpolatedWalk (ε m : ℝ) (η : ℝ → ℂ) (x : ℕ → ℤ) (t : ℝ≥0) :
    Complex.orthonormalBasisOneI.repr (interpolatedWalk ε η m x t) =
      AffineMap.lineMap
        (Complex.orthonormalBasisOneI.repr (vertexPoint ε η (x ⌊m * t⌋₊)))
        (Complex.orthonormalBasisOneI.repr (vertexPoint ε η (x (⌊m * t⌋₊ + 1))))
        (m * t - ⌊m * t⌋₊) := by
  simp only [interpolatedWalk, AffineMap.lineMap_apply_module, ← Complex.real_smul,
    map_add, map_smul]

end MatedCRT

end
