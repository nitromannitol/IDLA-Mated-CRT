import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.RetractionEstimate
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.WalkContinuity

/-! # Deterministic comparison of the two stopping locations -/

namespace MatedCRT

open Set Metric HarmonicBalls
open scoped NNReal

/-- On a path starting inside the disk with finite Euclidean exit time,
Hölder data bound the same-walk discrepancy by a power of the distance
between the two stopping locations. This is the deterministic step in
`LEMMA36-REPLACEMENT.md`, lines 393–398. -/
theorem sameWalkExitDiscrepancy_le_location_distance
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {r : ℝ} (hr : 0 < r) (z : ℂ) (ψ : ℂ → ℝ) {H χ : ℝ≥0}
    (hψ : HolderOnWith H χ ψ (closedBall z r))
    (ε : ℝ) (ω : Ω) (x : ℕ → ℤ)
    (hstart : interpolatedWalk ε (S.η ω) (S.mε ε) x 0 ∈ ball z r)
    (hfin : pathExitTime (ball z r) (interpolatedWalk ε (S.η ω) (S.mε ε) x) < ⊤) :
    sameWalkExitDiscrepancy S r z ψ ε ω x ≤
      (H : ℝ) * (2 * dist (pathExitPosition (ball z r)
          (interpolatedWalk ε (S.η ω) (S.mε ε) x))
        (vertexPoint ε (S.η ω)
          (vExitPosition (interiorCellVertices ε (S.η ω) (ball z r)) x))) ^ (χ : ℝ) := by
  let p := pathExitPosition (ball z r) (interpolatedWalk ε (S.η ω) (S.mε ε) x)
  let v := vertexPoint ε (S.η ω)
    (vExitPosition (interiorCellVertices ε (S.η ω) (ball z r)) x)
  have hp : p ∈ closedBall z r := by
    apply sphere_subset_closedBall
    apply frontier_ball_subset_sphere
    exact pathExitPosition_mem_frontier_of_continuous isOpen_ball
      (continuous_interpolatedWalk ε (S.mε ε) (S.η ω) x) hstart hfin
  have hd : dist p (ballRetraction z r v) ≤ 2 * dist p v := by
    have h := dist_ballRetraction_le hr z v p (mem_closedBall.mp hp)
    rw [ballRetraction_of_mem z hr hp, dist_comm (ballRetraction z r v) p,
      dist_comm v p] at h
    have heq : (1 + r / r) = (2 : ℝ) := by rw [div_self hr.ne']; norm_num
    simpa only [heq] using h
  have hbound := hψ.dist_le_of_le hp (ballRetraction_mem z hr v) hd
  simpa only [sameWalkExitDiscrepancy, finiteDiscExitValue, hstart, hfin, and_self,
    ↓reduceIte, Real.dist_eq, p, v] using hbound

/-- A discrepancy exceeding the Hölder threshold forces the two stopping
locations to be farther apart than the prescribed scale. -/
theorem location_distance_lt_of_sameWalkExitDiscrepancy_gt
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {r : ℝ} (hr : 0 < r) (z : ℂ) (ψ : ℂ → ℝ) {H χ : ℝ≥0}
    (hψ : HolderOnWith H χ ψ (closedBall z r))
    (ε : ℝ) (ω : Ω) (x : ℕ → ℤ) {s : ℝ}
    (hstart : interpolatedWalk ε (S.η ω) (S.mε ε) x 0 ∈ ball z r)
    (hfin : pathExitTime (ball z r) (interpolatedWalk ε (S.η ω) (S.mε ε) x) < ⊤)
    (hbad : (H : ℝ) * (2 * s) ^ (χ : ℝ) < sameWalkExitDiscrepancy S r z ψ ε ω x) :
    s < dist (pathExitPosition (ball z r) (interpolatedWalk ε (S.η ω) (S.mε ε) x))
      (vertexPoint ε (S.η ω)
        (vExitPosition (interiorCellVertices ε (S.η ω) (ball z r)) x)) := by
  by_contra hn
  have hd := le_of_not_gt hn
  have he := sameWalkExitDiscrepancy_le_location_distance S hr z ψ hψ ε ω x hstart hfin
  have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ 2 *
    dist (pathExitPosition (ball z r) (interpolatedWalk ε (S.η ω) (S.mε ε) x))
      (vertexPoint ε (S.η ω)
        (vExitPosition (interiorCellVertices ε (S.η ω) (ball z r)) x)))
    (mul_le_mul_of_nonneg_left hd (by norm_num : (0 : ℝ) ≤ 2)) χ.coe_nonneg
  have hmul := mul_le_mul_of_nonneg_left hpow H.coe_nonneg
  linarith

end MatedCRT
