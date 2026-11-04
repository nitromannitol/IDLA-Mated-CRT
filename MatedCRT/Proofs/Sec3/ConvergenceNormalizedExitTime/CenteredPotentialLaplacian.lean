import HarmonicBalls.Proofs.Sec3.Basic

/-! Distributional Laplacian of a Green potential under upper growth. -/

namespace MatedCRT

open MeasureTheory Metric Filter Topology Set Laplacian HarmonicBalls
open scoped ENNReal NNReal

/-- The Green potential has Laplacian `-μ` when it is continuous and its
Green-kernel sections are integrable. This isolates the Fubini argument of
`HarmonicBalls.greenPotentialBallLaplacianStep_holds` from the two-sided
volume-growth assumption. -/
theorem greenPotentialBall_hasLaplacian_of_continuous_integrable
    (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] {R : ℝ} (hR : 0 < R)
    (hqc : ContinuousOn (greenPotentialBall μ R) (closedBall 0 R))
    (hI : ∀ x ∈ closedBall (0 : ℂ) R,
      Integrable (fun y => greenFunction (ball (0 : ℂ) R) y x)
        (μ.restrict (ball 0 R))) :
    HasLaplacian (greenPotentialBall μ R) 0 μ (ball 0 R) := by
  set q := greenPotentialBall μ R with hqdef
  refine ⟨(hqc.mono ball_subset_closedBall).locallyIntegrableOn measurableSet_ball, fun φ hφ => ?_⟩
  have hφc : Continuous φ := hφ.1.continuous
  refine ⟨integrable_zero_measure, hφc.integrable_of_hasCompactSupport hφ.2.1, ?_⟩
  rw [integral_zero_measure, zero_sub]
  set ν := μ.restrict (ball (0 : ℂ) R) with hνdef
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  set G : ℂ → ℂ → ℝ := fun y x => greenFunction (ball (0 : ℂ) R) y x with hGdef
  have hΔc : Continuous (Δ φ) := continuous_laplacian_of_contDiff (hφ.1.of_le (by norm_cast))
  have hΔ0 : ∀ x, x ∉ ball (0 : ℂ) R → Δ φ x = 0 := fun x hx =>
    laplacian_eq_zero_of_notMem_tsupport fun h => hx (hφ.2.2 h)
  have hΔi : Integrable (Δ φ) := hΔc.integrable_of_hasCompactSupport (hasCompactSupport_laplacian hφ.2.1)
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn hqc
  set f : ℂ → ℂ → ℝ := fun x y => G y x * Δ φ x with hfdef
  have hfm : Measurable (Function.uncurry f) :=
    ((measurable_greenFunction_ball_uncurry R).comp (measurable_snd.prodMk measurable_fst)).mul
      (hΔc.measurable.comp measurable_fst)
  have hG0 : ∀ y x, 0 ≤ G y x := fun y x => greenFunction_nonneg isBounded_ball y x
  have hprod : Integrable (Function.uncurry f) (volume.prod ν) := by
    refine (integrable_prod_iff hfm.aestronglyMeasurable).2 ⟨Eventually.of_forall fun x => ?_, ?_⟩
    · by_cases hx : x ∈ ball (0 : ℂ) R
      · show Integrable (fun y => greenFunction (ball (0 : ℂ) R) y x * Δ φ x) ν
        exact (hI x (ball_subset_closedBall hx)).mul_const _
      · have h0 : (fun y => Function.uncurry f (x, y)) = fun _ => 0 := by
          funext y
          simp [hfdef, hΔ0 x hx]
        rw [h0]
        exact integrable_zero _ _ _
    · refine Integrable.mono' (hΔi.norm.const_mul B)
        (hfm.norm.stronglyMeasurable.integral_prod_right' (ν := ν)).aestronglyMeasurable
        (Eventually.of_forall fun x => ?_)
      have hn : (fun y => ‖Function.uncurry f (x, y)‖) = fun y => G y x * ‖Δ φ x‖ := by
        funext y
        simp only [Function.uncurry_apply_pair, hfdef, norm_mul, Real.norm_of_nonneg (hG0 y x)]
      show ‖∫ y, ‖Function.uncurry f (x, y)‖ ∂ν‖ ≤ B * ‖Δ φ x‖
      rw [hn, integral_mul_const]
      by_cases hx : x ∈ ball (0 : ℂ) R
      · have hqx : ∫ y, G y x ∂ν = q x := rfl
        rw [hqx, norm_mul, norm_norm]
        exact mul_le_mul_of_nonneg_right (hB x (ball_subset_closedBall hx)) (norm_nonneg _)
      · rw [hΔ0 x hx]
        simp
  have h1 : ∫ x, q x * Δ φ x = ∫ x, ∫ y, f x y ∂ν := by
    congr 1
    funext x
    rw [integral_mul_const]
    rfl
  rw [h1, integral_integral_swap hprod]
  have h2 : ∀ᵐ y ∂ν, ∫ x, f x y = -φ y := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    have h := ((greenFunctionBall R hR y hy).1.2 φ hφ).2.2
    rw [integral_zero_measure, integral_dirac, zero_sub] at h
    exact h
  rw [integral_congr_ae h2, integral_neg]
  congr 1
  exact setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hφ.2.2 h)

/-- An upper power bound on small-ball masses suffices for the distributional
Green-potential identity on an origin-centered ball. -/
theorem greenPotentialBall_hasLaplacian_of_upper
    (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] {R r₀ β : ℝ}
    (hR : 0 < R) (hr₀ : 0 < r₀) (hβ : 0 < β)
    (hup : ∀ s, 0 < s → s < r₀ → ∀ x ∈ ball (0 : ℂ) R,
      μ (ball x s) ≤ ENNReal.ofReal (s ^ β)) :
    HasLaplacian (greenPotentialBall μ R) 0 μ (ball 0 R) := by
  obtain ⟨hI, hholder⟩ := greenPotential_ball_holder_of_upper hR hr₀ hβ hup
    (measure_ball_lt_top.ne : μ (ball (0 : ℂ) R) ≠ ⊤)
    (f := fun _ => (1 : ℝ)) (M := 1) (by fun_prop) (by norm_num)
    (Eventually.of_forall (fun _ => by simp))
  have hq : greenPotentialBall μ R =
      fun x => ∫ y in ball (0 : ℂ) R, greenFunction (ball 0 R) x y ∂μ := by
    funext x
    unfold greenPotentialBall
    congr 1
    funext y
    exact greenFunction_ball_comm R y x
  let C : ℝ≥0 := ⟨greenPotentialHolderConstant β r₀ (μ (ball (0 : ℂ) R)).toReal,
    greenPotentialHolderConstant_nonneg hβ hr₀ ENNReal.toReal_nonneg⟩
  let α : ℝ≥0 := ⟨greenPotentialHolderExponent β, (greenPotentialHolderExponent_pos hβ).le⟩
  have hh : HolderOnWith C α (greenPotentialBall μ R) (closedBall 0 R) := by
    rw [hq]
    apply holderOnWith_of_dist_le
    intro x hx y hy
    rw [Real.dist_eq, dist_eq_norm]
    change |(∫ w in ball (0 : ℂ) R, greenFunction (ball 0 R) x w ∂μ) -
      (∫ w in ball (0 : ℂ) R, greenFunction (ball 0 R) y w ∂μ)| ≤
      greenPotentialHolderConstant β r₀ (μ (ball (0 : ℂ) R)).toReal *
        ‖x - y‖ ^ greenPotentialHolderExponent β
    simpa only [mul_one] using hholder x hx y hy
  apply greenPotentialBall_hasLaplacian_of_continuous_integrable μ hR
    (hh.continuousOn (greenPotentialHolderExponent_pos hβ))
  intro x hx
  refine (hI x hx).congr ?_
  filter_upwards with y
  simpa only [mul_one] using greenFunction_ball_comm R x y

end MatedCRT
