import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.BoundaryOscillationBarrier
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.ProjectedHarmonicSize

/-! Boundary-pair modulus from harmonic and exit-time barriers. -/

namespace MatedCRT

open Set Metric Filter Topology

/-- The ordinary expected-exit-time barrier vanishes on the Euclidean sphere
because its selected cell meets the vertex boundary. -/
theorem rescale_expectedExitTime_eq_zero_on_sphere
    {m : ℤ → ℤ → ℕ} {ε M r : ℝ} {η : ℝ → ℂ} {z y : ℂ}
    (hr : 0 < r) (hy : y ∈ sphere z r)
    (hcell : y ∈ cell ε η (vertexOf ε η y)) :
    M⁻¹ * (expectedExitTime m (interiorCellVertices ε η (ball z r))
      (vertexOf ε η y)).toReal = 0 := by
  have hb : vertexOf ε η y ∈ cellVertices ε η (frontier (ball z r)) := by
    refine ⟨y, hcell, ?_⟩
    simpa [frontier_ball z hr.ne'] using hy
  have hnot : vertexOf ε η y ∉ interiorCellVertices ε η (ball z r) := fun h => h.2 hb
  rw [expectedExitTime_eq_zero_of_not_mem m hnot, ENNReal.toReal_zero, mul_zero]

/-- If a harmonic comparison and a zero-boundary barrier are asymptotically
equicontinuous on the closed disk, their boundary-pair comparison gives the
same modulus for the original functions. -/
theorem boundary_pair_modulus_of_harmonic_and_barrier
    {z : ℂ} {r C : ℝ} (hC : 0 ≤ C) (u h q : ℕ → ℂ → ℝ)
    (hh : Tightness.IsAsymptoticallyEquicontinuousOn h (closedBall z r))
    (hq : Tightness.IsAsymptoticallyEquicontinuousOn q (closedBall z r))
    (hqbd : ∀ᶠ n in atTop, ∀ y ∈ sphere z r, q n y = 0)
    (hcomp : ∀ᶠ n in atTop, ∀ x ∈ closedBall z r, ∀ y ∈ sphere z r,
      |u n x - u n y| ≤ |h n x - h n y| + C * q n x) :
    ∀ k : ℝ, 0 < k → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in atTop,
      ∀ x ∈ closedBall z r, ∀ y ∈ sphere z r,
        ‖x - y‖ ≤ δ → |u n x - u n y| ≤ k := by
  intro k hk
  obtain ⟨δh, hδh, heh⟩ := hh (k / 2) (by positivity)
  obtain ⟨δq, hδq, heq⟩ := hq (k / (2 * (C + 1))) (by positivity)
  refine ⟨min δh δq, lt_min hδh hδq, ?_⟩
  filter_upwards [heh, heq, hqbd, hcomp] with n hhn hqn hbn hcn
  intro x hx y hy hxy
  have hhxy := hhn x hx y (sphere_subset_closedBall hy) (hxy.trans (min_le_left _ _))
  have hqxy := hqn x hx y (sphere_subset_closedBall hy) (hxy.trans (min_le_right _ _))
  rw [hbn y hy, sub_zero] at hqxy
  have hqbound : q n x ≤ k / (2 * (C + 1)) := (le_abs_self _).trans hqxy
  have hmul := mul_le_mul_of_nonneg_left hqbound hC
  have hrem : C * (k / (2 * (C + 1))) ≤ k / 2 := by
    have hp : 0 < 2 * (C + 1) := by positivity
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hp).2
    nlinarith
  linarith [hcn x hx y hy]

end MatedCRT

#print axioms MatedCRT.boundary_pair_modulus_of_harmonic_and_barrier
#print axioms MatedCRT.rescale_expectedExitTime_eq_zero_on_sphere
