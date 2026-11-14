import HarmonicBalls.Proofs.Sec6.PlanarBrownianGenerator
import HarmonicBalls.Proofs.Sec6.StoppedPotentialIntegrability
import HarmonicBalls.Proofs.Sec3.ConservationOfMassStep3
import MarkovProcess.Trajectory.DynkinStopping
import MarkovProcess.Trajectory.ExpectedExitTime

/-!
# Dynkin's formula at the exit time of a bounded domain for planar Brownian motion

Let `D ⊆ ℂ` be a bounded open set and let `τ_D` be the exit time of planar Brownian motion
`𝓑^x` from `D`.

* `lintegral_exitTime_planarBrownianMotion_lt_top`: `E_x τ_D < ∞`.
* `planarBrownianMotion_exit_dynkin`: for a smooth compactly supported `g : ℂ → ℝ`,
  `E_x g(𝓑_{τ_D}) - g(x) = ½ E_x ∫_0^{τ_D} Δg(𝓑_s) ds`.

Both follow from Dynkin's formula at bounded stopping times for the planar heat semigroup, whose
generator is `½ Δ` on smooth compactly supported functions, by letting the truncation level of
`τ_D ∧ n` tend to infinity (dominated convergence, with the integrable majorant `‖Δg‖_∞ τ_D`).
-/

open MeasureTheory Set Filter InnerProductSpace Laplacian MarkovProcess HarmonicBalls HarmonicBalls.Section6
open scoped ContDiff ENNReal NNReal Topology ZeroAtInfty

namespace MatedCRT.KilledOccupation

/-- A smooth compactly supported function equal to `-‖y‖² / 2` near a bounded set; its Laplacian
is `-2` on that set. -/
theorem exists_contDiff_hasCompactSupport_laplacian_eq_neg_two {U : Set ℂ}
    (hUb : Bornology.IsBounded U) :
    ∃ g : ℂ → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ ∀ x ∈ U, Δ g x = -2 := by
  obtain ⟨R, hR⟩ := hUb.subset_closedBall (0 : ℂ)
  let φ : ContDiffBump (0 : ℂ) := ⟨|R| + 1, |R| + 2, by positivity, by linarith⟩
  obtain ⟨F, hFdef⟩ : ∃ F : ℝ → ℝ, F = fun t ↦ (-1 / 2 : ℝ) * t := ⟨_, rfl⟩
  have hF : ContDiff ℝ ∞ F := hFdef ▸ contDiff_const.mul contDiff_id
  have hdF : deriv F = fun _ ↦ (-1 / 2 : ℝ) := by
    funext t
    have h : HasDerivAt F (-1 / 2 : ℝ) t := by
      rw [hFdef]
      simpa using (hasDerivAt_id t).const_mul (-1 / 2 : ℝ)
    exact h.deriv
  refine ⟨fun y ↦ φ y * F (‖y‖ ^ 2), φ.contDiff.mul (hF.comp (contDiff_norm_sq ℝ)),
    φ.hasCompactSupport.mul_right, fun x hx ↦ ?_⟩
  have hx' : x ∈ Metric.ball (0 : ℂ) (|R| + 1) := by
    have h := hR hx
    rw [Metric.mem_closedBall] at h
    rw [Metric.mem_ball]
    linarith [le_abs_self R]
  have heq : (fun y ↦ φ y * F (‖y‖ ^ 2)) =ᶠ[𝓝 x] fun y ↦ F (‖y‖ ^ 2) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hx'] with y hy
    rw [φ.one_of_mem_closedBall (Metric.ball_subset_closedBall hy), one_mul]
  rw [(laplacian_congr_nhds heq).eq_of_nhds, laplacian_comp_norm_sq hF, hdF]
  norm_num [deriv_const']

/-- **Finite mean exit time.** The exit time of planar Brownian motion from a bounded open set has
finite expectation from every starting point. -/
theorem lintegral_exitTime_planarBrownianMotion_lt_top {D : Set ℂ} (hD : IsOpen D)
    (hDb : Bornology.IsBounded D) (x : ℂ) :
    ∫⁻ p, ContinuousPath.exitTime D p ∂(planarBrownianMotion x) < ⊤ := by
  obtain ⟨g, hg, hgc, hΔ⟩ := exists_contDiff_hasCompactSupport_laplacian_eq_neg_two hDb
  obtain ⟨f, hfg, hgen⟩ := exists_planarBrownian_generator_eq_half_laplacian g hg hgc
  obtain ⟨M, hM⟩ := hgc.exists_bound_of_continuous hg.continuous
  have hLf : ∀ y ∈ D,
      (isFellerKernelSemigroup_planarHeatSemigroup.c0Semigroup.generator f) y ≤ -1 := by
    intro y hy
    rw [hgen y, hΔ y hy]
    norm_num
  have hm : ∀ y, -M ≤ (f : C₀(ℂ, ℝ)) y := by
    intro y
    rw [hfg y]
    exact (abs_le.mp (by simpa only [Real.norm_eq_abs] using hM y)).1
  rw [planarBrownianMotion_eq_continuousProcess]
  exact lt_of_le_of_lt
    (isFellerKernelSemigroup_planarHeatSemigroup.lintegral_exitTime_le
      isConservative_planarHeatSemigroup kolmogorovRegular_planarHeatSemigroup f D hD hLf hm x)
    ENNReal.ofReal_lt_top

/-- **Dynkin's formula at the exit time of a bounded domain.** For a smooth compactly supported
`g` and a bounded open `D`, `E_x g(𝓑_{τ_D}) - g(x) = ½ E_x ∫_0^{τ_D} Δg(𝓑_s) ds`. -/
theorem planarBrownianMotion_exit_dynkin {D : Set ℂ} (hD : IsOpen D)
    (hDb : Bornology.IsBounded D) {g : ℂ → ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (x : ℂ) :
    (∫ p, g (p ((ContinuousPath.exitTime D p).toNNReal)) ∂(planarBrownianMotion x)) - g x =
      (1 / 2 : ℝ) * ∫ p, (∫ s in (0 : ℝ)..((ContinuousPath.exitTime D p).toNNReal : ℝ),
        Δ g (p s.toNNReal)) ∂(planarBrownianMotion x) := by
  obtain ⟨f, hfg, hgen⟩ := exists_planarBrownian_generator_eq_half_laplacian g hg hgc
  obtain ⟨M, hM⟩ := hgc.exists_bound_of_continuous hg.continuous
  obtain ⟨A, hA⟩ := (hasCompactSupport_laplacian hgc).exists_bound_of_continuous
    (continuous_laplacian_of_contDiff (hg.of_le (by norm_num)))
  have hbd (y : ℂ) : ‖(1 / 2 : ℝ) * Δ g y‖ ≤ A := by
    calc ‖(1 / 2 : ℝ) * Δ g y‖ = (1 / 2) * ‖Δ g y‖ := by
          rw [norm_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      _ ≤ A := by linarith [hA y, norm_nonneg (Δ g y)]
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hbd 0)
  -- Dynkin's formula at the bounded stopping times `τ_D ∧ n`
  have hdyn (n : ℕ) :
      (∫ p, g (p (ContinuousPath.exitTimeTrunc D n p)) ∂(planarBrownianMotion x)) - g x =
        ∫ p, (∫ s in (0 : ℝ)..(ContinuousPath.exitTimeTrunc D n p : ℝ),
          (1 / 2 : ℝ) * Δ g (p s.toNNReal)) ∂(planarBrownianMotion x) := by
    have h := isFellerKernelSemigroup_planarHeatSemigroup.integral_eval_stoppingTime_sub_eq_integral_integral_generator
      isConservative_planarHeatSemigroup kolmogorovRegular_planarHeatSemigroup f
      (ContinuousPath.exitTimeTrunc D n) (ContinuousPath.isStoppingTime_exitTimeTrunc D hD n)
      (ContinuousPath.exitTimeTrunc_le D n) x
    rw [← planarBrownianMotion_eq_continuousProcess] at h
    simpa only [hfg, hgen] using h
  have hint (n : ℕ) : Integrable (fun p : ContinuousPath ℂ ↦
      ∫ s in (0 : ℝ)..(ContinuousPath.exitTimeTrunc D n p : ℝ),
        (1 / 2 : ℝ) * Δ g (p s.toNNReal)) (planarBrownianMotion x) := by
    have h := isFellerKernelSemigroup_planarHeatSemigroup.integrable_integral_generator_stoppingTime
      isConservative_planarHeatSemigroup f
      (ContinuousPath.exitTimeTrunc D n) (ContinuousPath.isStoppingTime_exitTimeTrunc D hD n)
      (ContinuousPath.exitTimeTrunc_le D n) x
    rw [← planarBrownianMotion_eq_continuousProcess] at h
    simpa only [hgen] using h
  have hfin := ae_planarBrownian_exitTime_bounded_lt_top x hDb
  have hτ := lintegral_exitTime_planarBrownianMotion_lt_top hD hDb x
  -- the drift terms converge, dominated by `A τ_D`
  have hRHS : Tendsto (fun n : ℕ ↦ ∫ p, (∫ s in (0 : ℝ)..(ContinuousPath.exitTimeTrunc D n p : ℝ),
        (1 / 2 : ℝ) * Δ g (p s.toNNReal)) ∂(planarBrownianMotion x)) atTop
      (𝓝 (∫ p, (∫ s in (0 : ℝ)..((ContinuousPath.exitTime D p).toNNReal : ℝ),
        (1 / 2 : ℝ) * Δ g (p s.toNNReal)) ∂(planarBrownianMotion x))) := by
    refine tendsto_integral_of_dominated_convergence
      (fun p ↦ A * (ContinuousPath.exitTime D p).toReal) (fun n ↦ (hint n).aestronglyMeasurable)
      ((integrable_toReal_of_lintegral_ne_top
        (ContinuousPath.measurable_exitTime D hD).aemeasurable hτ.ne).const_mul A) ?_ ?_
    · intro n
      filter_upwards [hfin] with p hp
      have hle : (ContinuousPath.exitTimeTrunc D n p : ℝ≥0∞) ≤ ContinuousPath.exitTime D p := by
        rw [ContinuousPath.coe_exitTimeTrunc_ennreal]
        exact min_le_left _ _
      have hle' : ContinuousPath.exitTimeTrunc D n p ≤ (ContinuousPath.exitTime D p).toNNReal := by
        have h := ENNReal.toNNReal_mono hp.ne hle
        rwa [ENNReal.toNNReal_coe] at h
      have hb : ∀ s ∈ Set.uIoc (0 : ℝ) (ContinuousPath.exitTimeTrunc D n p : ℝ),
          ‖(1 / 2 : ℝ) * Δ g (p s.toNNReal)‖ ≤ A := fun s _ ↦ hbd _
      calc ‖∫ s in (0 : ℝ)..(ContinuousPath.exitTimeTrunc D n p : ℝ),
            (1 / 2 : ℝ) * Δ g (p s.toNNReal)‖
          ≤ A * |(ContinuousPath.exitTimeTrunc D n p : ℝ) - 0| :=
            intervalIntegral.norm_integral_le_of_norm_le_const hb
        _ ≤ A * (ContinuousPath.exitTime D p).toReal := by
            rw [sub_zero, abs_of_nonneg (NNReal.coe_nonneg _), ← ENNReal.coe_toNNReal_eq_toReal]
            exact mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr hle') hA0
    · filter_upwards [hfin] with p hp
      obtain ⟨N, hN⟩ := exists_nat_ge (ContinuousPath.exitTime D p).toNNReal
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop N] with n hn
      have ht : ContinuousPath.exitTimeTrunc D n p = (ContinuousPath.exitTime D p).toNNReal := by
        apply ENNReal.coe_injective
        have hle' : ContinuousPath.exitTime D p ≤ ((n : ℝ≥0) : ℝ≥0∞) := by
          rw [← ENNReal.coe_toNNReal hp.ne, ENNReal.coe_le_coe]
          exact hN.trans (by exact_mod_cast hn)
        rw [ContinuousPath.coe_exitTimeTrunc_ennreal, min_eq_left hle', ENNReal.coe_toNNReal hp.ne]
      rw [ht]
  have hLHS := (tendsto_integral_exitTimeTrunc_of_bounded_measurable hD hDb hg.continuous.measurable
    hM x).sub_const (g x)
  rw [tendsto_nhds_unique (hLHS.congr hdyn) hRHS]
  simp only [intervalIntegral.integral_const_mul, integral_const_mul]

end MatedCRT.KilledOccupation
