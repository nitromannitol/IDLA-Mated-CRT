import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.BumpPotentialProbability

/-! Geometry for applying the small-bump potential estimate inside the unit disc. -/

namespace MatedCRT

open Set Metric

/-- A ball contained in the unit disc lies in the closed disc of radius two
around each of its points. -/
theorem ball_subset_closedBall_two_of_subset_unit {ρ r : ℝ} {z y : ℂ}
    (hρ : ρ < 1) (hball : ball z r ⊆ ball 0 ρ) (hy : y ∈ ball z r) :
    ball z r ⊆ closedBall y 2 := by
  intro w hw
  have hw0 := hball hw
  have hy0 := hball hy
  have hw' : dist w 0 < ρ := hw0
  have hy' : dist y 0 < ρ := hy0
  change dist w y ≤ 2
  have htri := dist_triangle w 0 y
  rw [dist_comm 0 y] at htri
  linarith

end MatedCRT
