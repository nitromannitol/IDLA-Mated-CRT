import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.LaplacianTranslation

/-! Identification of the normalized exit Green potential. -/

namespace MatedCRT

open MeasureTheory Metric Filter Topology Set Laplacian _root_.HarmonicBalls
open scoped ENNReal NNReal

/-- The continuum potential step in Lemma 3.7 follows from the exit-time
random-variable estimate in Lemma 2.17. -/
theorem normalizedExitPotentialStep_of_boundedExitTime
    (𝒮 : SpaceFillingSLEModel) (h217 : BoundedExitTimeRVStmt) :
    NormalizedExitPotentialStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS r z hr hball
  obtain ⟨β, hβ, hmass⟩ := ae_smallBallMass_all_small_radii h217 hγ hγ2 hρ hρ1
    S.P S.hC S.hcirc S.μ hS.isConeField
  filter_upwards [hmass, hS.isLQGMeasure,
    normalizedExitGreenPotential_ae_continuousOn 𝒮 h217 hγ hγ2 hρ hρ1 S hS hr hball]
      with ω hmassω hμ hcont
  let μ := S.μ ω
  let : IsLocallyFiniteMeasure μ := hμ.isLocallyFiniteMeasure
  let ν := Measure.map (fun w : ℂ => w - z) μ
  have hmap (a : ℂ) (s : ℝ) : ν (ball a s) = μ (ball (a + z) s) := by
    rw [Measure.map_apply (by fun_prop) measurableSet_ball, preimage_ball_sub_const]
  let : IsLocallyFiniteMeasure ν := ⟨fun x =>
    ⟨ball x 1, ball_mem_nhds x zero_lt_one, by rw [hmap]; exact measure_ball_lt_top⟩⟩
  obtain ⟨r₀, hr₀, hup⟩ := hmassω
  have hup' : ∀ s, 0 < s → s < r₀ → ∀ x ∈ ball (0 : ℂ) r,
      ν (ball x s) ≤ ENNReal.ofReal (s ^ β) := by
    intro s hs hsr x hx
    rw [hmap]
    apply hup s hs hsr (x + z) (hball ?_)
    simpa only [mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero] using hx
  have hq := greenPotentialBall_hasLaplacian_of_upper ν hr hr₀ hβ hup'
  have hc : 0 ≤ S.c₀ / 6 := div_nonneg S.c₀_nonneg (by norm_num)
  have hq' := hasLaplacian_const_mul_zero_left hq hc
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
  have hp : (fun x => normalizedExitGreenPotential S r z ω (x + z)) =
      fun x => S.c₀ / 6 * greenPotentialBall ν r x := by
    funext x
    unfold normalizedExitGreenPotential
    rw [hint]
  have hm : Measure.map (fun w : ℂ => w - z) (ENNReal.ofReal (S.c₀ / 6) • μ) =
      ENNReal.ofReal (S.c₀ / 6) • ν := by
    exact Measure.map_smul _ (by fun_prop)
  let : IsLocallyFiniteMeasure (ENNReal.ofReal (S.c₀ / 6) • μ) := by
    refine ⟨fun x => ?_⟩
    obtain ⟨s, hs, hfin⟩ := μ.finiteAt_nhds x
    refine ⟨s, hs, ?_⟩
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin
  have ht : HasLaplacian (fun x => normalizedExitGreenPotential S r z ω (x + z)) 0
      (Measure.map (fun w : ℂ => w - z) (ENNReal.ofReal (S.c₀ / 6) • μ)) (ball 0 r) := by
    rw [hp, hm]
    exact hq'
  refine ⟨hcont, hasLaplacian_of_centered_translate _ hcont ht, ?_⟩
  intro x hx
  exact normalizedExitGreenPotential_eq_zero_on_sphere S hx ω

end MatedCRT
