import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.RateDiscrepancy

/-! Uniform boundedness of the exit-value discrepancy. -/

namespace MatedCRT

open Set Metric HarmonicBalls
open scoped NNReal

/-- The two exit values lie on the closed disk, so their discrepancy is
bounded by the Hölder modulus at the diameter of the disk. -/
theorem sameWalkExitDiscrepancy_le_disk_diameter
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {r : ℝ} (hr : 0 < r) (z : ℂ) (ψ : ℂ → ℝ) {H χ : ℝ≥0}
    (hψ : HolderOnWith H χ ψ (closedBall z r))
    (ε : ℝ) (ω : Ω) (x : ℕ → ℤ)
    (hstart : interpolatedWalk ε (S.η ω) (S.mε ε) x 0 ∈ ball z r)
    (hfin : pathExitTime (ball z r) (interpolatedWalk ε (S.η ω) (S.mε ε) x) < ⊤) :
    sameWalkExitDiscrepancy S r z ψ ε ω x ≤ (H : ℝ) * (2 * r) ^ (χ : ℝ) := by
  let p := pathExitPosition (ball z r) (interpolatedWalk ε (S.η ω) (S.mε ε) x)
  let v := vertexPoint ε (S.η ω)
    (vExitPosition (interiorCellVertices ε (S.η ω) (ball z r)) x)
  have hp : p ∈ closedBall z r := by
    apply sphere_subset_closedBall
    apply frontier_ball_subset_sphere
    exact pathExitPosition_mem_frontier_of_continuous isOpen_ball
      (continuous_interpolatedWalk ε (S.mε ε) (S.η ω) x) hstart hfin
  have hv : ballRetraction z r v ∈ closedBall z r := ballRetraction_mem z hr v
  have hd : dist p (ballRetraction z r v) ≤ 2 * r := by
    have h := dist_le_diam_of_mem isBounded_closedBall hp hv
    exact h.trans (diam_closedBall hr.le)
  have hbound := hψ.dist_le_of_le hp hv hd
  simpa only [sameWalkExitDiscrepancy, finiteDiscExitValue, hstart, hfin, and_self,
    ↓reduceIte, Real.dist_eq, p, v] using hbound

end MatedCRT

#print axioms MatedCRT.sameWalkExitDiscrepancy_le_disk_diameter
