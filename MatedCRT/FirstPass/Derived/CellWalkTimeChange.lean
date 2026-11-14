import MatedCRT.FirstPass.Derived.ComplexWalkAffineInterpolation
import MatedCRT.FirstPass.Derived.AreaCellRepresentative
import LatticeProb.Walk.CellConfigConstantStepComparison

/-! # Time change between embedded and cell walks -/

set_option autoImplicit false

noncomputable section

open ReflectedGMS ReflectedGMS.GMS
open scoped NNReal

namespace MatedCRT

/-- If the represented vertices agree, the cell walk follows the embedded walk
under an increasing time change matching their jump times. -/
theorem exists_orderIso_cellWalk_eq_repr_interpolatedWalk
    (H : CellConfig) (p : H.cells → Plane) (ω : ℕ → H.cells)
    (hpos : ∀ K, 0 < H.holding K) (hunb : H.JumpTimesUnbounded ω)
    {δ m : ℝ≥0} (hδ : 0 < δ) (hm : 0 < m)
    (ε : ℝ) (η : ℝ → ℂ) (x : ℕ → ℤ)
    (hanchor : ∀ n, Complex.orthonormalBasisOneI.repr (vertexPoint ε η (x n)) =
      (δ : ℝ) • p (ω n)) :
    ∃ φ : ℝ≥0 ≃o ℝ≥0,
      (∀ n, φ (LatticeProb.CellConfigInterpolation.scaledJumpTime H ω hpos δ n) =
        LatticeProb.ConstantStepInterpolation.knot m n) ∧
      ∀ t, H.interpolatedWalk p δ ω t =
        Complex.orthonormalBasisOneI.repr (interpolatedWalk ε η m x (φ t)) := by
  obtain ⟨φ, hφ, hwalk⟩ :=
    LatticeProb.CellConfigInterpolation.exists_orderIso_interpolatedWalk_eq_constantStep
      H p ω hpos hunb hδ hm
  refine ⟨φ, hφ, ?_⟩
  intro t
  rw [hwalk, repr_interpolatedWalk]
  simp only [LatticeProb.ConstantStepInterpolation.path, hanchor]


/-- Relabelling an integer walk by its area cells preserves its embedded
trajectory up to an increasing time change. -/
theorem exists_orderIso_areaCellWalk_eq_repr_interpolatedWalk
    {μ : MeasureTheory.Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε)
    (c : ℤ → ℤ → ℕ) (x : ℕ → ℤ)
    (hpos : ∀ K, 0 < (areaCellConfig h hε c).holding K)
    (hunb : (areaCellConfig h hε c).JumpTimesUnbounded
      (fun n => euclideanCellEquiv h hε (x n)))
    {m : ℝ≥0} (hm : 0 < m) :
    ∃ φ : ℝ≥0 ≃o ℝ≥0,
      (∀ n, φ (LatticeProb.CellConfigInterpolation.scaledJumpTime
        (areaCellConfig h hε c) (fun n => euclideanCellEquiv h hε (x n)) hpos 1 n) =
        LatticeProb.ConstantStepInterpolation.knot m n) ∧
      ∀ t, (areaCellConfig h hε c).interpolatedWalk
          (areaCellRepresentative h hε c) 1
          (fun n => euclideanCellEquiv h hε (x n)) t =
        Complex.orthonormalBasisOneI.repr (interpolatedWalk ε η m x (φ t)) := by
  apply exists_orderIso_cellWalk_eq_repr_interpolatedWalk
    (areaCellConfig h hε c) (areaCellRepresentative h hε c)
    (fun n => euclideanCellEquiv h hε (x n)) hpos hunb (by norm_num) hm ε η x
  intro n
  simpa using (areaCellRepresentative_equiv h hε c (x n)).symm

end MatedCRT

end
