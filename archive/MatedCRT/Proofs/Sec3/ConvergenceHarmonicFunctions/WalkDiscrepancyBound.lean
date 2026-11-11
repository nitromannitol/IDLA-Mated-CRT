import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.DiscrepancyBound
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.RateTailReduction

/-! Almost-sure boundedness of the walk's exit-value discrepancy. -/

namespace MatedCRT

open MeasureTheory Set Metric Filter Topology _root_.HarmonicBalls
open scoped NNReal

/-- For a walk started at an interior cell, the exit-value discrepancy is
almost surely bounded by the Hölder modulus at the disk diameter. -/
theorem srwLaw_ae_sameWalkExitDiscrepancy_le_disk_diameter
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {r : ℝ} (hr : 0 < r) (z : ℂ) (ψ : ℂ → ℝ) {H χ : ℝ≥0}
    (hψ : HolderOnWith H χ ψ (closedBall z r))
    {ε : ℝ} (hε : 0 < ε) (ω : Ω) (v : ℤ)
    (hlf : IsLocallyFiniteMult (S.mult ε ω))
    (hcons : ∀ k : ℤ, S.mult ε ω k (k + 1) ≠ 0) (hm : 0 < S.mε ε)
    (hη : Continuous (S.η ω))
    (hp : Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ))
    (hv : v ∈ interiorCellVertices ε (S.η ω) (ball z r)) :
    ∀ᵐ x ∂srwLaw (S.mult ε ω) v,
      sameWalkExitDiscrepancy S r z ψ ε ω x ≤ (H : ℝ) * (2 * r) ^ (χ : ℝ) := by
  filter_upwards [srwLaw_ae_start (S.mult ε ω) v,
    srwLaw_ae_interpolatedWalk_exit_ball_lt_top (S.mult ε ω) hlf hcons hε hm hη hp z r v]
    with x hx hfin
  have hstart : interpolatedWalk ε (S.η ω) (S.mε ε) x 0 ∈ ball z r := by
    have hzero : interpolatedWalk ε (S.η ω) (S.mε ε) x 0 =
        vertexPoint ε (S.η ω) v := by simp [interpolatedWalk, hx]
    rw [hzero]
    exact Sec7.cell_subset_ball_of_mem_interiorCellVertices hη hv
      (Sec7.vertexPoint_mem_cell hε.le v)
  exact sameWalkExitDiscrepancy_le_disk_diameter S hr z ψ hψ ε ω x hstart hfin

end MatedCRT

#print axioms MatedCRT.srwLaw_ae_sameWalkExitDiscrepancy_le_disk_diameter
