import MatedCRT.Proofs.LBM.ExitTimeChange

/-! Geometric reduction of regular ball exit to an outward radial excursion. -/

namespace MatedCRT

open Filter Metric Set Topology HarmonicBalls MarkovProcess
open scoped InnerProductSpace ENNReal NNReal

/-- A positive outward radial increment at a point on a sphere leaves the closed ball. -/
theorem not_mem_closedBall_of_inner_sub_pos {z w x : ℂ} {r : ℝ}
    (hw : w ∈ sphere z r) (hx : 0 < ⟪w - z, x - w⟫_ℝ) :
    x ∉ closedBall z r := by
  have hnorm : ‖w - z‖ = r := by simpa [dist_eq_norm] using hw
  have hexpand := norm_add_sq_real (w - z) (x - w)
  have heq : w - z + (x - w) = x - z := by abel
  rw [heq, hnorm] at hexpand
  have hn : 0 ≤ ‖x - w‖ ^ 2 := sq_nonneg _
  intro hmem
  have hle : ‖x - z‖ ≤ r := by simpa [dist_eq_norm] using hmem
  have hnonneg : 0 ≤ ‖x - z‖ := norm_nonneg _
  nlinarith

/-- An outward radial excursion immediately after a sphere hit implies immediate
crossing of the closed ball. -/
theorem frequently_outside_closedBall_of_outward_radial_excursion
    {p : ℝ≥0 → ℂ} {z : ℂ} {r : ℝ} {τ : ℝ≥0}
    (hboundary : p τ ∈ sphere z r)
    (hexcursion : ∃ᶠ t in 𝓝[>] τ, 0 < ⟪p τ - z, p t - p τ⟫_ℝ) :
    ∃ᶠ t in 𝓝[>] τ, p t ∉ closedBall z r :=
  hexcursion.mono fun _ ht => not_mem_closedBall_of_inner_sub_pos hboundary ht

/-- An immediate outward radial excursion of the Brownian driver at its exit
implies regular exit for the normalized Liouville Brownian path. -/
theorem rescaledLBM_ball_regular_of_brownian_outward_radial_excursion
    {F : ContinuousPath ℂ → ℝ≥0 → ℝ} {b : ContinuousPath ℂ}
    {z : ℂ} {r : ℝ} (hF : IsTimeChangeClock (F b))
    (h0 : b 0 ∈ ball z r) (hfin : ContinuousPath.exitTime (ball z r) b < ⊤)
    {m : ℝ} (hm : 0 < m)
    (hexcursion : ∃ᶠ t in 𝓝[>] (ContinuousPath.exitTime (ball z r) b).toNNReal,
      0 < ⟪b (ContinuousPath.exitTime (ball z r) b).toNNReal - z,
        b t - b (ContinuousPath.exitTime (ball z r) b).toNNReal⟫_ℝ) :
    ∃ᶠ t in 𝓝[>] (pathExitTime (ball z r) (rescaledLBMPath F m b)).toNNReal,
      rescaledLBMPath F m b t ∉ closure (ball z r) := by
  have hboundary : b (ContinuousPath.exitTime (ball z r) b).toNNReal ∈ sphere z r :=
    frontier_ball_subset_sphere (ContinuousPath.coordinate_exitTime_mem_frontier
      (ball z r) isOpen_ball b h0 (ne_of_lt hfin))
  have hregular : ∃ᶠ t in 𝓝[>] (ContinuousPath.exitTime (ball z r) b).toNNReal,
      b t ∉ closure (ball z r) :=
    (frequently_outside_closedBall_of_outward_radial_excursion hboundary hexcursion).mono
      fun _ ht hmem => ht (closure_ball_subset_closedBall hmem)
  exact rescaledLBM_frequently_outside_closure_after_exit isOpen_ball hF h0 hfin hm hregular

end MatedCRT
