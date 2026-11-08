import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.WalkDiscrepancyBound
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.CellIntegral
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.WalkMeasurability

/-! Measurability and integrability of the quenched exit discrepancy. -/

namespace MatedCRT

open MeasureTheory Set Metric Filter Topology _root_.HarmonicBalls
open scoped NNReal

/-- For an interior starting cell the exit-value discrepancy is almost
surely measurable and integrable under the quenched walk law. -/
theorem srwLaw_sameWalkExitDiscrepancy_integrable
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {r : ℝ} (hr : 0 < r) (z : ℂ) (ψ : ℂ → ℝ) {H χ : ℝ≥0}
    (hψ : HolderOnWith H χ ψ (closedBall z r))
    {ε : ℝ} (hε : 0 < ε) (ω : Ω) (v : ℤ)
    (hlf : IsLocallyFiniteMult (S.mult ε ω))
    (hcons : ∀ k : ℤ, S.mult ε ω k (k + 1) ≠ 0) (hm : 0 < S.mε ε)
    (hη : Continuous (S.η ω))
    (hp : Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ))
    (hv : v ∈ interiorCellVertices ε (S.η ω) (ball z r)) :
    Integrable (sameWalkExitDiscrepancy S r z ψ ε ω) (srwLaw (S.mult ε ω) v) := by
  let μ := srwLaw (S.mult ε ω) v
  let g : (ℕ → ℤ) → ℝ := fun x =>
    |ψ (pathExitPosition (ball z r) (interpolatedWalk ε (S.η ω) (S.mε ε) x)) -
      ψ (ballRetraction z r (vertexPoint ε (S.η ω)
        (vExitPosition (interiorCellVertices ε (S.η ω) (ball z r)) x)))|
  have hg : Measurable g := by
    apply Measurable.abs
    apply Measurable.sub
    · exact measurable_exitPosition_interpolatedWalk ε (S.mε ε) (S.η ω)
    · exact (measurable_of_countable fun j : ℤ => ψ (ballRetraction z r
        (vertexPoint ε (S.η ω) j))).comp (measurable_vExitPosition _)
  have heq : sameWalkExitDiscrepancy S r z ψ ε ω =ᵐ[μ] g := by
    filter_upwards [srwLaw_ae_start (S.mult ε ω) v,
      srwLaw_ae_interpolatedWalk_exit_ball_lt_top (S.mult ε ω) hlf hcons hε hm hη hp z r v]
      with x hx hfin
    have hstart : interpolatedWalk ε (S.η ω) (S.mε ε) x 0 ∈ ball z r := by
      have hzero : interpolatedWalk ε (S.η ω) (S.mε ε) x 0 =
          vertexPoint ε (S.η ω) v := by simp [interpolatedWalk, hx]
      rw [hzero]
      exact Sec7.cell_subset_ball_of_mem_interiorCellVertices hη hv
        (Sec7.vertexPoint_mem_cell hε.le v)
    simp [sameWalkExitDiscrepancy, finiteDiscExitValue, hstart, hfin, g]
  have hmeas : AEStronglyMeasurable (sameWalkExitDiscrepancy S r z ψ ε ω) μ :=
    hg.aestronglyMeasurable.congr heq.symm
  apply Integrable.of_bound hmeas ((H : ℝ) * (2 * r) ^ (χ : ℝ))
  filter_upwards [srwLaw_ae_sameWalkExitDiscrepancy_le_disk_diameter S hr z ψ hψ hε ω v
    hlf hcons hm hη hp hv] with x hx
  simpa [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _), sameWalkExitDiscrepancy] using hx

end MatedCRT

#print axioms MatedCRT.srwLaw_sameWalkExitDiscrepancy_integrable
