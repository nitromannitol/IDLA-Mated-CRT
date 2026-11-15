import MatedCRT.FirstPass.Derived.AreaCellVertexExitClock
import MatedCRT.FirstPass.Derived.AreaCellExitPrefixDistance
import LatticeProb.Walk.CellConfigContinuousExitClock

/-! # Paper exit curves and the final exterior edge -/

set_option autoImplicit false
noncomputable section

namespace MatedCRT

open MeasureTheory ReflectedGMS MatedCRTHarmonic.Markov HarmonicBalls LatticeProb
open scoped NNReal ENNReal

/-- For an interior start, the continuously stopped paper path is close to the
prefix ending at the first exterior vertex, controlled by the final two cells. -/
theorem areaCell_paper_exit_curve_le_final_edge
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (c : ℤ → ℤ → ℕ)
    (hc : (areaCellConfig h hε c).IsCellConfiguration)
    (hpos : ∀ K, 0 < (areaCellConfig h hε c).holding K)
    (x : ℕ → ℤ)
    (hunb : (areaCellConfig h hε c).JumpTimesUnbounded
      (fun n => euclideanCellEquiv h hε (x n)))
    (hadj : ∀ n, (areaCellConfig h hε c).Adj
      (euclideanCellEquiv h hε (x n)) (euclideanCellEquiv h hε (x (n + 1))))
    {a m : ℝ≥0} (ha : 0 < a) (hm : 0 < m) {U : Set ℂ}
    (hU : IsOpen U) (hconv : Convex ℝ U)
    (hstart : (a : ℝ) • vertexPoint ε η (x 0) ∈ U)
    (hfin : hitTime {k : ℤ | (a : ℝ) • vertexPoint ε η k ∉ U} x ≠ ⊤) :
    ∃ n : ℕ,
      hitTime {k : ℤ | (a : ℝ) • vertexPoint ε η k ∉ U} x = (n + 1 : ℕ) ∧
      pathExitTime U ((a : ℝ) • interpPathCM (vertexPoint ε η) m.2 x) ≠ ⊤ ∧
      cmpEDist (stopAtExit U ((a : ℝ) • interpPathCM (vertexPoint ε η) m.2 x))
        (fun t => ((a : ℝ) • interpPathCM (vertexPoint ε η) m.2 x)
          (min t (ConstantStepInterpolation.knot m (n + 1)))) ≤
        ENNReal.ofReal (2 * ((a : ℝ) *
          (Metric.diam (((euclideanCellEquiv h hε (x n)).1) : Set Plane) +
           Metric.diam (((euclideanCellEquiv h hε (x (n + 1))).1) : Set Plane)))) := by
  have hs : (a : ℝ) • areaCellRepresentative h hε c (euclideanCellEquiv h hε (x 0)) ∈
      Complex.orthonormalBasisOneI.repr.symm ⁻¹' U := by
    change Complex.orthonormalBasisOneI.repr.symm
      ((a : ℝ) • areaCellRepresentative h hε c (euclideanCellEquiv h hε (x 0))) ∈ U
    rw [areaCellRepresentative_equiv, ← map_smul,
      Complex.orthonormalBasisOneI.repr.symm_apply_apply]
    exact hstart
  have hf : hitTime {K : (areaCellConfig h hε c).cells |
      (a : ℝ) • areaCellRepresentative h hε c K ∉
        Complex.orthonormalBasisOneI.repr.symm ⁻¹' U}
      (fun n => euclideanCellEquiv h hε (x n)) ≠ ⊤ := by
    rw [areaCell_exteriorVertex_hitTime_eq]
    exact hfin
  obtain ⟨n, hn, he, hd⟩ := CellConfigInterpolation.edist_constantStep_exit_curve_le
    (areaCellConfig h hε c) hc (areaCellRepresentative h hε c)
    (areaCellRepresentative_mem h hε c) _ hpos hunb hadj ha hm
    (isOpen_euclideanDomain hU) (convex_euclideanDomain hconv) hs hf
  change LatticeProb.continuousExitTime _ _ _ ≠ ⊤ at he
  rw [areaCell_exteriorVertex_hitTime_eq] at hn
  rw [areaCell_scaled_continuousExitTime_eq (m := (m : ℝ)) h hε c m.2 (a : ℝ) x U] at he
  refine ⟨n, hn, he, ?_⟩
  exact le_of_eq_of_le
    (areaCell_exit_prefix_distance_eq (m := (m : ℝ)) h hε c m.2 (a : ℝ) x U
      (ConstantStepInterpolation.knot m (n + 1)) he) hd

end MatedCRT
end
