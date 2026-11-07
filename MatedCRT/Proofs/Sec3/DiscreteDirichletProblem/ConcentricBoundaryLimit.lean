import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.ConcentricSphereGeometry
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.CountableUniformSubsequence

/-! Boundary decay from nested majorants and a uniform Hölder estimate. -/

namespace MatedCRT

open Set Metric Filter Topology

/-- A family of uniformly Hölder continuous functions vanishing on outer
circles is uniformly small near the inner circle for a sufficiently close
outer radius. -/
theorem exists_small_concentric_holder_boundary {z : ℂ} {r C α : ℝ}
    (hr : 0 < r) (hC : 0 ≤ C) (hα : 0 < α)
    (R : ℕ → ℝ) (hR : ∀ j, r < R j) (hRlim : Tendsto R atTop (𝓝 r))
    (f : ℕ → ℂ → ℝ)
    (hzero : ∀ j w, w ∈ sphere z (R j) → f j w = 0)
    (hh : ∀ j, ∀ u ∈ closedBall z (R j), ∀ v ∈ closedBall z (R j),
      |f j u - f j v| ≤ C * ‖u - v‖ ^ α) :
    ∀ k : ℝ, 0 < k → ∃ j δ, 0 < δ ∧
      ∀ x ∈ closedBall z r, ∀ y ∈ sphere z r, dist x y ≤ δ → |f j x| < k := by
  intro k hk
  have hp : Tendsto (fun s : ℝ => C * s ^ α) (𝓝 0) (𝓝 0) := by
    have h := (Real.continuousAt_rpow_const 0 α (Or.inr hα.le)).tendsto.const_mul C
    simpa [Real.zero_rpow hα.ne'] using h
  have hsmall : ∀ᶠ s : ℝ in 𝓝 0, C * s ^ α < k :=
    hp.eventually (Iio_mem_nhds hk)
  obtain ⟨d, hd, hball⟩ := Metric.mem_nhds_iff.mp hsmall
  have hd2 : d / 2 ∈ ball (0 : ℝ) d := by
    rw [mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by positivity : 0 < d / 2)]
    linarith
  have hbound : C * (d / 2) ^ α < k := hball hd2
  have hj : ∀ᶠ j in atTop, R j < r + d / 4 :=
    hRlim.eventually (Iio_mem_nhds (by linarith))
  obtain ⟨j, hj⟩ := hj.exists
  refine ⟨j, d / 4, by positivity, ?_⟩
  intro x hx y hy hxy
  have hb := abs_le_of_holder_concentric_spheres hr (hR j).le hC hα.le hx hy hxy
    (f j) (hzero j) (hh j)
  have hdist : d / 4 + (R j - r) ≤ d / 2 := by linarith
  have hnonneg : 0 ≤ d / 4 + (R j - r) := by linarith [hR j]
  exact (hb.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow hnonneg hdist hα.le) hC)).trans_lt hbound

/-- Countably many convergent upper barriers with uniformly Hölder limits
give boundary decay of the dominated sequence. -/
theorem boundary_decay_of_concentric_majorants {z : ℂ} {r C α : ℝ}
    (hr : 0 < r) (hC : 0 ≤ C) (hα : 0 < α)
    (R : ℕ → ℝ) (hR : ∀ j, r < R j) (hRlim : Tendsto R atTop (𝓝 r))
    (q : ℕ → ℂ → ℝ) (F : ℕ → ℕ → ℂ → ℝ) (f : ℕ → ℂ → ℝ)
    (hzero : ∀ j w, w ∈ sphere z (R j) → f j w = 0)
    (hh : ∀ j, ∀ u ∈ closedBall z (R j), ∀ v ∈ closedBall z (R j),
      |f j u - f j v| ≤ C * ‖u - v‖ ^ α)
    (hdom : ∀ j, ∀ᶠ n in atTop, ∀ x ∈ closedBall z r, q n x ≤ F j n x)
    (hconv : ∀ j, TendstoUniformlyOn (F j) (f j) atTop (closedBall z r)) :
    ∀ k : ℝ, 0 < k → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in atTop,
      ∀ x ∈ closedBall z r, ∀ y ∈ sphere z r, ‖x - y‖ ≤ δ → q n x ≤ k := by
  intro k hk
  obtain ⟨j, δ, hδ, hsmall⟩ := exists_small_concentric_holder_boundary hr hC hα
    R hR hRlim f hzero hh (k / 2) (by positivity)
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hdom j, (Metric.tendstoUniformlyOn_iff.mp (hconv j))
    (k / 2) (by positivity)] with n hn hc x hx y hy hxy
  have hd := hc x hx
  rw [Real.dist_eq, abs_sub_comm] at hd
  have hs := hsmall x hx y hy (by simpa [dist_eq_norm] using hxy)
  have h1 := le_abs_self (F j n x - f j x)
  have h2 := le_abs_self (f j x)
  linarith [hn x hx]

end MatedCRT

#print axioms MatedCRT.exists_small_concentric_holder_boundary
#print axioms MatedCRT.boundary_decay_of_concentric_majorants
