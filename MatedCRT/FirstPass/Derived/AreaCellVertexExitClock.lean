import MatedCRT.FirstPass.Derived.AreaCellRepresentative
import LatticeProb.Walk.RelabelledHittingTrace

/-! # Exterior vertex clocks for area cells -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Set ReflectedGMS MatedCRTHarmonic.Markov

/-- A complex open domain remains open in Euclidean coordinates. -/
theorem isOpen_euclideanDomain {U : Set ℂ} (hU : IsOpen U) :
    IsOpen (Complex.orthonormalBasisOneI.repr.symm ⁻¹' U) :=
  Complex.orthonormalBasisOneI.repr.symm.continuous.isOpen_preimage _ hU

/-- A complex convex domain remains convex in Euclidean coordinates. -/
theorem convex_euclideanDomain {U : Set ℂ} (hU : Convex ℝ U) :
    Convex ℝ (Complex.orthonormalBasisOneI.repr.symm ⁻¹' U) :=
  hU.linear_preimage Complex.orthonormalBasisOneI.repr.symm.toLinearMap

/-- The exterior-vertex hitting time agrees for integer labels and their
Euclidean area-cell representatives, including an infinite hitting time. -/
theorem areaCell_exteriorVertex_hitTime_eq
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (c : ℤ → ℤ → ℕ) (a : ℝ)
    (U : Set ℂ) (x : ℕ → ℤ) :
    hitTime {K : (areaCellConfig h hε c).cells |
        a • areaCellRepresentative h hε c K ∉
          Complex.orthonormalBasisOneI.repr.symm ⁻¹' U}
      (fun n => euclideanCellEquiv h hε (x n)) =
    hitTime {k : ℤ | a • vertexPoint ε η k ∉ U} x := by
  refine (LatticeProb.hitTime_map (fun k : ℤ => euclideanCellEquiv h hε k)
    {K : (areaCellConfig h hε c).cells |
      a • areaCellRepresentative h hε c K ∉
        Complex.orthonormalBasisOneI.repr.symm ⁻¹' U} x).trans ?_
  apply congrArg (fun A : Set ℤ => hitTime A x)
  apply Set.ext
  intro k
  change Complex.orthonormalBasisOneI.repr.symm
      (a • areaCellRepresentative h hε c (euclideanCellEquiv h hε k)) ∉ U ↔
    a • vertexPoint ε η k ∉ U
  rw [areaCellRepresentative_equiv, ← map_smul,
    Complex.orthonormalBasisOneI.repr.symm_apply_apply]

end MatedCRT
end
