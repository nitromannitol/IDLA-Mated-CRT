import MatedCRT.FirstPass.Derived.PlanarBrownianPoissonExit
import MatedCRT.FirstPass.Derived.PlanarBrownianDiscExitKernel
import HarmonicBalls.Proofs.Sec6.CompactHittingStopping
import MarkovProcess.Trajectory.ExitLaw

/-!
# The occupation identity of planar Brownian motion killed on exiting a disc, smooth tests

Let `D = B_r(z)`, `y ∈ D`, `τ` the exit time of planar Brownian motion `𝓑^y` from `D`, and `g` smooth
with compact support. Then

  `E_y ∫_0^τ g(𝓑_s) ds = 2 ∫ G_D(y, x) g(x) dx`,

with `G_D` the Green function of `D` (normalized by `ΔG_D(y, ·) = -δ_y`, zero off `D`).

Proof. By the Poisson identity before exit, the left side is `2 (U g(y) - E_y U g(𝓑_τ))`, with `U g` the
logarithmic potential. By Fubini, `E_y U g(𝓑_τ) = ∫ g(x) E_y N(𝓑_τ, x) dx`, and the exit average of the
Newtonian kernel is `N(y, x) - G_D(y, x)` for every `x` off the circle `∂D` with `x ≠ y`, a Lebesgue-null
exceptional set. Fubini applies because `𝓑_τ` lies on the circle almost surely and
`w ↦ ∫ |N(w, x)| |g(x)| dx`, a convolution of a locally integrable kernel with a continuous compactly
supported function, is continuous, hence bounded on the circle.
-/

open MeasureTheory Set Filter Metric Topology MarkovProcess HarmonicBalls HarmonicBalls.Section6
  ContinuousLinearMap
open scoped ContDiff Convolution

namespace MatedCRT.KilledOccupation

/-- For `g` continuous with compact support, `x ↦ N(w, x) g(x)` is integrable. -/
theorem integrable_newtonKernel_mul {g : ℂ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (w : ℂ) : Integrable (fun x => newtonKernel w x * g x) := by
  have h := (hgc.convolutionExists_right (lsmul ℝ ℝ) (locallyIntegrable_newtonKernel 0) hg w).comp_sub_left w
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only [lsmul_apply, smul_eq_mul, newtonKernel, zero_sub, norm_neg, sub_sub_cancel]

/-- `w ↦ ∫ |N(w, x)| |g(x)| dx` is continuous for `g` continuous with compact support. -/
theorem continuous_integral_norm_newtonKernel_mul {g : ℂ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) :
    Continuous fun w => ∫ x, ‖newtonKernel w x‖ * ‖g x‖ := by
  have hW : ∀ w, ((fun t => ‖newtonKernel 0 t‖) ⋆[lsmul ℝ ℝ, volume] (fun x => ‖g x‖)) w =
      ∫ x, ‖newtonKernel w x‖ * ‖g x‖ := by
    intro w
    have h : ∫ t, ‖newtonKernel w (w - t)‖ * ‖g (w - t)‖ = ∫ x, ‖newtonKernel w x‖ * ‖g x‖ :=
      integral_sub_left_eq_self (f := fun x => ‖newtonKernel w x‖ * ‖g x‖) (μ := volume) w
    rw [convolution_lsmul, ← h]
    congr 1
    funext t
    simp only [smul_eq_mul, newtonKernel, sub_sub_cancel, zero_sub, norm_neg]
  exact (hgc.norm.continuous_convolution_right (lsmul ℝ ℝ)
    (locallyIntegrableOn_univ.1 (locallyIntegrableOn_univ.2 (locallyIntegrable_newtonKernel 0)).norm)
    hg.norm).congr hW

/-- **Exit average of the logarithmic potential on a disc.** For `y ∈ B_r(z)` and `g` continuous with
compact support, `x ↦ (N(y, x) - G(y, x)) g(x)` is integrable and
`E_y U g(𝓑_τ) = ∫ (N(y, x) - G_{B_r(z)}(y, x)) g(x) dx`. -/
theorem integral_logPotential_exitTime_ball {z y : ℂ} {r : ℝ} (hy : y ∈ ball z r) {g : ℂ → ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    Integrable (fun x => (newtonKernel y x - greenFunction (ball z r) y x) * g x) ∧
    ∫ p, logPotential g (p ((ContinuousPath.exitTime (ball z r) p).toNNReal))
        ∂(planarBrownianMotion y) =
      ∫ x, (newtonKernel y x - greenFunction (ball z r) y x) * g x := by
  set P := planarBrownianMotion y with hPdef
  set e' : ContinuousPath ℂ → ℂ :=
    fun p => p ((ContinuousPath.exitTimeTop (ball z r) p).untopD 0) with he'def
  have he' : Measurable e' := ContinuousPath.measurable_eval_untopD_exitTimeTop _ isOpen_ball
  have hee : ∀ᵐ p ∂P, p ((ContinuousPath.exitTime (ball z r) p).toNNReal) = e' p := by
    filter_upwards [ae_planarBrownian_exitTime_bounded_lt_top y isBounded_ball] with p hp
    show _ = p ((ContinuousPath.exitTimeTop (ball z r) p).untopD 0)
    rw [ContinuousPath.untopD_exitTimeTop_eq_toNNReal _ p hp.ne]
  have hsph : ∀ᵐ p ∂P, e' p ∈ sphere z r := by
    filter_upwards [ae_planarBrownianMotion_pathExitPosition_mem_sphere hy, hee] with p hp hpe
    rwa [pathExitPosition_eq_eval_exitTime, hpe] at hp
  -- the Fubini integrand
  have hNm : Measurable fun q : ℂ × ℂ => newtonKernel q.1 q.2 := by
    unfold newtonKernel
    fun_prop
  have hmeas : Measurable fun q : ContinuousPath ℂ × ℂ => newtonKernel (e' q.1) q.2 * g q.2 := by
    have h1 : Measurable fun q : ContinuousPath ℂ × ℂ => newtonKernel (e' q.1) q.2 :=
      hNm.comp ((he'.comp measurable_fst).prodMk measurable_snd)
    have h2 : Measurable fun q : ContinuousPath ℂ × ℂ => g q.2 := hg.measurable.comp measurable_snd
    exact h1.mul h2
  have hWc := continuous_integral_norm_newtonKernel_mul hg hgc
  obtain ⟨C, hC⟩ := (isCompact_sphere z r).exists_bound_of_continuousOn hWc.continuousOn
  have hint : Integrable (fun q : ContinuousPath ℂ × ℂ => newtonKernel (e' q.1) q.2 * g q.2)
      (P.prod volume) := by
    rw [integrable_prod_iff hmeas.aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun p => integrable_newtonKernel_mul hg hgc (e' p), ?_⟩
    simp only [norm_mul]
    refine Integrable.of_bound (hWc.measurable.comp he').aestronglyMeasurable C ?_
    filter_upwards [hsph] with p hp
    exact hC _ hp
  have hswap := integral_integral_swap (μ := P) (ν := volume)
    (f := fun p x => newtonKernel (e' p) x * g x) hint
  -- the exit averages of the kernel, off a null set of poles
  have hnull : volume (sphere z r ∪ {y}) = 0 :=
    measure_union_null (Measure.addHaar_sphere volume z r) (measure_singleton y)
  have hae : (fun x => ∫ p, newtonKernel (e' p) x * g x ∂P) =ᵐ[volume]
      fun x => (newtonKernel y x - greenFunction (ball z r) y x) * g x := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with x hx
    have hcongr : (fun p => newtonKernel (p ((ContinuousPath.exitTime (ball z r) p).toNNReal)) x)
        =ᵐ[P] fun p => newtonKernel (e' p) x := by
      filter_upwards [hee] with p hp
      rw [hp]
    rw [integral_mul_const, ← integral_congr_ae hcongr,
      integral_newtonKernel_exitTime_ball hy (fun h => hx (Or.inl h)) (fun h => hx (Or.inr h))]
  refine ⟨(hint.integral_prod_right).congr hae, ?_⟩
  have hL : ∫ p, logPotential g (p ((ContinuousPath.exitTime (ball z r) p).toNNReal)) ∂P =
      ∫ p, ∫ x, newtonKernel (e' p) x * g x ∂volume ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [hee] with p hp
    rw [hp, logPotential]
  rw [hL, hswap]
  exact integral_congr_ae hae

/-- **Killed occupation identity for smooth tests (B6).** For `y ∈ B_r(z)` and `g` smooth with compact
support, `E_y ∫_0^τ g(𝓑_s) ds = 2 ∫ G_{B_r(z)}(y, x) g(x) dx`. -/
theorem integral_occupation_exitTime_ball_eq_greenFunction {z y : ℂ} {r : ℝ} (hy : y ∈ ball z r)
    {g : ℂ → ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    ∫ p, (∫ s in (0 : ℝ)..((ContinuousPath.exitTime (ball z r) p).toNNReal : ℝ), g (p s.toNNReal))
        ∂(planarBrownianMotion y) =
      2 * ∫ x, greenFunction (ball z r) y x * g x := by
  obtain ⟨hI, hE⟩ := integral_logPotential_exitTime_ball hy hg.continuous hgc
  rw [integral_occupation_exitTime_eq_logPotential isOpen_ball isBounded_ball hg hgc hy, hE,
    logPotential, ← integral_sub (integrable_newtonKernel_mul hg.continuous hgc y) hI]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  ring

end MatedCRT.KilledOccupation
