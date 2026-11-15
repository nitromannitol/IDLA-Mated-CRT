import MatedCRT.FirstPass.Derived.AreaCellVertexExitClock
import MatedCRT.FirstPass.Derived.AreaCellScaledPath

/-! # Continuous exit before an exterior vertex -/

set_option autoImplicit false
noncomputable section

namespace MatedCRT

open MeasureTheory ReflectedGMS MatedCRTHarmonic.Markov HarmonicBalls LatticeProb
open scoped NNReal ENNReal

/-- A finite exterior vertex is reached at its knot, so the continuous paper
exit occurs no later. The domain need not be open or convex. -/
theorem areaCell_paper_exitTime_le_vertex_knot
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (c : ℤ → ℤ → ℕ)
    {m : ℝ≥0} (hm : 0 < m) (a : ℝ) (x : ℕ → ℤ) (U : Set ℂ)
    {n : ℕ} (hn : hitTime {k : ℤ | a • vertexPoint ε η k ∉ U} x = n) :
    pathExitTime U (a • interpPathCM (vertexPoint ε η) (show 0 ≤ (m : ℝ) from m.2) x) ≤
      (ConstantStepInterpolation.knot m n : ℝ≥0∞) := by
  have hout : a • vertexPoint ε η (x n) ∉ U := (hitTime_eq_coe_iff.mp hn).1
  rw [← areaCell_scaled_continuousExitTime_eq (m := (m : ℝ)) h hε c m.2 a x U]
  apply continuousExitTime_le_of_not_mem
  simp only [zero_add, Set.mem_preimage]
  change Complex.orthonormalBasisOneI.repr.symm
    (ConstantStepInterpolation.path (m : ℝ)
      (fun j => a • areaCellRepresentative h hε c (euclideanCellEquiv h hε (x j)))
      (ConstantStepInterpolation.knot m n)) ∉ U
  rw [ConstantStepInterpolation.path_knot hm, areaCellRepresentative_equiv,
    ← map_smul, Complex.orthonormalBasisOneI.repr.symm_apply_apply]
  exact hout

end MatedCRT
end
