import MatedCRT.FirstPass.Derived.AreaCellVertexExitClock
import MatedCRT.FirstPass.Derived.AreaCellExitPrefixDistance

/-! # Stopping an embedded walk started outside a domain -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory HarmonicBalls MatedCRTHarmonic.Markov
open scoped NNReal ENNReal

/-- At an exterior initial vertex, both exit clocks vanish and the continuously
stopped ray equals the zero-length vertex prefix. -/
theorem areaCell_exterior_start_exit
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (c : ℤ → ℤ → ℕ)
    {m : ℝ} (hm : 0 ≤ m) (a : ℝ) (x : ℕ → ℤ) (U : Set ℂ)
    (hstart : a • vertexPoint ε η (x 0) ∉ U) :
    hitTime {K : (areaCellConfig h hε c).cells |
      a • areaCellRepresentative h hε c K ∉
        Complex.orthonormalBasisOneI.repr.symm ⁻¹' U}
      (fun n => euclideanCellEquiv h hε (x n)) = 0 ∧
    pathExitTime U (a • interpPathCM (vertexPoint ε η) hm x) = 0 ∧
    cmpEDist (stopAtExit U (a • interpPathCM (vertexPoint ε η) hm x))
      (fun t => (a • interpPathCM (vertexPoint ε η) hm x) (min t 0)) = 0 := by
  have hvertex : hitTime {k : ℤ | a • vertexPoint ε η k ∉ U} x = 0 :=
    hitTime_eq_zero_iff.mpr hstart
  have hzero : (a • interpPathCM (vertexPoint ε η) hm x) 0 =
      a • vertexPoint ε η (x 0) := by
    simp [interpPathFn, linInterp]
  have hexit : pathExitTime U (a • interpPathCM (vertexPoint ε η) hm x) = 0 := by
    apply le_antisymm _ bot_le
    apply sInf_le
    refine ⟨0, by simp, ?_⟩
    change (a • interpPathCM (vertexPoint ε η) hm x) 0 ∉ U
    rw [hzero]
    exact hstart
  refine ⟨(areaCell_exteriorVertex_hitTime_eq h hε c a U x).trans hvertex, hexit, ?_⟩
  have heq : stopAtExit U (a • interpPathCM (vertexPoint ε η) hm x) =
      fun t => (a • interpPathCM (vertexPoint ε η) hm x) (min t 0) := by
    funext t
    simp [stopAtExit, hexit]
  rw [heq]
  exact LatticeProb.ReparamEDist.reparamEDist_self _

end MatedCRT
end
