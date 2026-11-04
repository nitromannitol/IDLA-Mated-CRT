import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.LaplacianTranslation

/-! Weak Laplacian of Green potentials on translated balls. -/

namespace MatedCRT

open MeasureTheory Metric Filter Topology Set Laplacian _root_.HarmonicBalls
open scoped ENNReal

/-- Translate the centered Green-potential Laplacian identity to any ball.
Continuity of the potential on the closed ball is stated separately, so this
applies to arbitrary locally finite source measures. -/
theorem ballGreenPotential_hasLaplacian_of_upper
    (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] {r r₀ β : ℝ} {z : ℂ}
    (hr : 0 < r) (hr₀ : 0 < r₀) (hβ : 0 < β)
    (hup : ∀ s, 0 < s → s < r₀ → ∀ x ∈ ball z r,
      μ (ball x s) ≤ ENNReal.ofReal (s ^ β))
    (hcont : ContinuousOn (fun x => ∫ y in ball z r,
      greenFunction (ball z r) x y ∂μ) (closedBall z r)) :
    HasLaplacian (fun x => ∫ y in ball z r, greenFunction (ball z r) x y ∂μ)
      0 μ (ball z r) := by
  let ν := Measure.map (fun w : ℂ => w - z) μ
  have hmap (a : ℂ) (s : ℝ) : ν (ball a s) = μ (ball (a + z) s) := by
    rw [Measure.map_apply (by fun_prop) measurableSet_ball, preimage_ball_sub_const]
  let : IsLocallyFiniteMeasure ν := ⟨fun x =>
    ⟨ball x 1, ball_mem_nhds x zero_lt_one, by rw [hmap]; exact measure_ball_lt_top⟩⟩
  have hup' : ∀ s, 0 < s → s < r₀ → ∀ x ∈ ball (0 : ℂ) r,
      ν (ball x s) ≤ ENNReal.ofReal (s ^ β) := by
    intro s hs hsr x hx
    rw [hmap]
    apply hup s hs hsr (x + z)
    simpa only [mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero] using hx
  have hq := greenPotentialBall_hasLaplacian_of_upper ν hr hr₀ hβ hup'
  have hO : (fun w : ℂ => w + z) ⁻¹' ball z r = ball 0 r := by
    ext w
    simp [mem_ball, dist_eq_norm]
  have hint (x : ℂ) : greenPotentialBall ν r x =
      ∫ y in ball z r, greenFunction (ball z r) (x + z) y ∂μ := by
    unfold greenPotentialBall
    have hf : (fun w : ℂ => w - z) = (Homeomorph.addRight (-z) : ℂ → ℂ) := by
      funext w
      simp [sub_eq_add_neg]
    change (∫ y in ball (0 : ℂ) r, greenFunction (ball 0 r) y x
      ∂Measure.map (fun w : ℂ => w - z) μ) = _
    rw [hf, (Homeomorph.addRight (-z)).isClosedEmbedding.setIntegral_map]
    change (∫ y in (fun w : ℂ => w - z) ⁻¹' ball (0 : ℂ) r,
      greenFunction (ball 0 r) (y - z) x ∂μ) = _
    rw [preimage_ball_sub_const, zero_add]
    apply setIntegral_congr_fun measurableSet_ball
    intro y hy
    change greenFunction (ball 0 r) (y - z) x = greenFunction (ball z r) (x + z) y
    rw [greenFunction_ball_comm]
    have hg := greenFunction_translate (ball z r) x (y - z) z
    simpa only [sub_add_cancel, hO] using hg.symm
  apply hasLaplacian_of_centered_translate _ hcont
  have heq : (fun x => ∫ y in ball z r, greenFunction (ball z r) (x + z) y ∂μ) =
      greenPotentialBall ν r := by
    funext x
    exact (hint x).symm
  rw [heq]
  exact hq

end MatedCRT
