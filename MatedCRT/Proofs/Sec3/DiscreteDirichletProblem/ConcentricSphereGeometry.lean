import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.UniformPotentialHolder

/-! Radial comparison of concentric circles. -/

namespace MatedCRT

open Set Metric

/-- Every point on an inner circle has a radially aligned point on an outer
circle, at distance equal to the difference of their radii. -/
theorem exists_mem_concentric_sphere_dist {z y : ℂ} {r R : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) (hy : y ∈ sphere z r) :
    ∃ w ∈ sphere z R, dist y w = R - r := by
  have hynorm : ‖y - z‖ = r := by simpa [mem_sphere, dist_eq_norm] using hy
  let w : ℂ := z + (R / r) • (y - z)
  have hcoef : 0 ≤ R / r := div_nonneg (le_trans hr.le hrR) hr.le
  have hw : w ∈ sphere z R := by
    rw [mem_sphere, dist_eq_norm]
    simp only [w, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hcoef, hynorm]
    field_simp
  refine ⟨w, hw, ?_⟩
  have heq : y - w = (1 - R / r) • (y - z) := by
    dsimp only [w]
    rw [sub_smul, one_smul]
    abel
  rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs,
    abs_of_nonpos (by have : 1 ≤ R / r := (le_div_iff₀ hr).2 (by simpa using hrR); linarith), hynorm]
  field_simp
  ring

/-- A Hölder function which vanishes on an outer circle is small near a
concentric inner circle. -/
theorem abs_le_of_holder_concentric_spheres {z x y : ℂ} {r R δ C α : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) (hC : 0 ≤ C) (hα : 0 ≤ α)
    (hx : x ∈ closedBall z r) (hy : y ∈ sphere z r) (hxy : dist x y ≤ δ)
    (f : ℂ → ℝ) (hzero : ∀ w ∈ sphere z R, f w = 0)
    (hh : ∀ u ∈ closedBall z R, ∀ v ∈ closedBall z R,
      |f u - f v| ≤ C * ‖u - v‖ ^ α) :
    |f x| ≤ C * (δ + (R - r)) ^ α := by
  obtain ⟨w, hw, hyw⟩ := exists_mem_concentric_sphere_dist hr hrR hy
  have hxR : x ∈ closedBall z R := closedBall_subset_closedBall hrR hx
  have hwR : w ∈ closedBall z R := sphere_subset_closedBall hw
  have hdist : ‖x - w‖ ≤ δ + (R - r) := by
    rw [← dist_eq_norm]
    calc dist x w ≤ dist x y + dist y w := dist_triangle _ _ _
      _ ≤ δ + (R - r) := by linarith
  have hpow : ‖x - w‖ ^ α ≤ (δ + (R - r)) ^ α :=
    Real.rpow_le_rpow (norm_nonneg _) hdist hα
  have hb := hh x hxR w hwR
  rw [hzero w hw, sub_zero] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left hpow hC)

end MatedCRT

#print axioms MatedCRT.exists_mem_concentric_sphere_dist
