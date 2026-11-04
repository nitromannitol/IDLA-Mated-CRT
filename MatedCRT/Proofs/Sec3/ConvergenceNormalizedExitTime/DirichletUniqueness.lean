import HarmonicBalls.Proofs.SecA.ObstacleLeastSuperharmonicMajorant
import HarmonicBalls.Steps.Sec3.Basic

/-! Uniqueness for continuous distributional Dirichlet problems on discs. -/

namespace MatedCRT

open MeasureTheory Metric Filter Set Laplacian _root_.HarmonicBalls
open scoped ENNReal Topology

/-- Two functions with the same distributional Laplacian differ by a
distributionally harmonic function. -/
theorem hasLaplacian_sub_of_same {f g : ℂ → ℝ} {μpos μneg : Measure ℂ} {U : Set ℂ}
    (hf : HasLaplacian f μpos μneg U) (hg : HasLaplacian g μpos μneg U) :
    HasLaplacian (fun x => f x - g x) 0 0 U := by
  refine ⟨hf.1.sub hg.1, fun φ hφ => ⟨integrable_zero_measure, integrable_zero_measure, ?_⟩⟩
  obtain ⟨_, _, hf'⟩ := hf.2 φ hφ
  obtain ⟨_, _, hg'⟩ := hg.2 φ hφ
  have heq : (fun x => (f x - g x) * Δ φ x) =
      fun x => f x * Δ φ x - g x * Δ φ x := by
    funext x
    ring
  rw [heq, integral_sub (integrable_mul_laplacian_of_test hf.1 hφ)
    (integrable_mul_laplacian_of_test hg.1 hφ), hf', hg']
  simp

/-- A continuous, distributionally harmonic function with zero boundary
values is nonnegative throughout the disc. -/
theorem nonneg_of_hasLaplacian_zero_on_ball {f : ℂ → ℝ} {z : ℂ} {r : ℝ}
    (hcont : ContinuousOn f (closedBall z r)) (hlap : HasLaplacian f 0 0 (ball z r))
    (hbdry : ∀ x ∈ sphere z r, f x = 0) : ∀ x ∈ ball z r, 0 ≤ f x := by
  have hsuper : IsSuperharmonicOn (ball z r) f :=
    superharmonicOfLaplacianLEStep_holds _ _ isOpen_ball
      (hcont.mono ball_subset_closedBall) hlap.laplacianLE
  apply nonneg_of_lowerSemicontinuousOn_of_superMean hsuper.1
    (hsuper.localSuperMean isOpen_ball)
  intro ξ hξ ε hε
  have h := (hcont ξ (sphere_subset_closedBall hξ)).mono_left
    (nhdsWithin_mono ξ (ball_subset_closedBall (x := z) (ε := r)))
  rw [hbdry ξ hξ] at h
  exact h.eventually (lt_mem_nhds (neg_lt_zero.mpr hε))

/-- Continuous solutions of the same distributional Dirichlet problem on a
disc agree everywhere on the closed disc. -/
theorem eqOn_closedBall_of_hasLaplacian_eq {f g : ℂ → ℝ} {z : ℂ} {r : ℝ}
    {μpos μneg : Measure ℂ} (hf : ContinuousOn f (closedBall z r))
    (hg : ContinuousOn g (closedBall z r)) (hlf : HasLaplacian f μpos μneg (ball z r))
    (hlg : HasLaplacian g μpos μneg (ball z r))
    (hbdry : ∀ x ∈ sphere z r, f x = g x) : EqOn f g (closedBall z r) := by
  have hnonneg : ∀ x ∈ ball z r, 0 ≤ f x - g x :=
    nonneg_of_hasLaplacian_zero_on_ball (hf.sub hg) (hasLaplacian_sub_of_same hlf hlg)
      (fun x hx => sub_eq_zero.mpr (hbdry x hx))
  have hnonneg' : ∀ x ∈ ball z r, 0 ≤ g x - f x :=
    nonneg_of_hasLaplacian_zero_on_ball (hg.sub hf) (hasLaplacian_sub_of_same hlg hlf)
      (fun x hx => sub_eq_zero.mpr (hbdry x hx).symm)
  intro x hx
  by_cases hx' : x ∈ ball z r
  · linarith [hnonneg x hx', hnonneg' x hx']
  · apply hbdry x
    rw [mem_closedBall] at hx
    rw [mem_ball] at hx'
    rw [mem_sphere]
    exact le_antisymm hx (le_of_not_gt hx')

end MatedCRT
