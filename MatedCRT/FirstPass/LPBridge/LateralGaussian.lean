import MatedCRT.FirstPass.LPBridge.WholePlaneGFFLateral
import MatedCRT.FirstPass.LPBridge.RotationalAverage

/-!
# Gaussianity of the lateral family of the whole-plane GFF (N2)

For a whole-plane GFF `(hC, hcirc)` and a test function `φ` supported in the unit disc, the lateral pairing
`hC φ - ∫ φ(x) h_{|x|}(0) dx` is a Gaussian process in `φ`. The proof replaces `φ` by its rotational average
`ψ = avgRot φ` (a radial test function, see `MatedCRT.RotationalAverage`): the radial integrals of `φ` and `ψ`
agree almost surely, and the radial pairing `hC ψ` equals the radial integral of `ψ` almost surely, because the
two have the same second moments (the GFF covariance `wholePlaneCov` averaged over rotations is the circle-average
kernel `C(|x|,|y|)`, Duplantier-Sheffield 2011, Section 3.1). Hence the lateral pairing is a finite linear
combination of pairings with test functions, which are Gaussian by definition of the GFF.
-/

noncomputable section

namespace MatedCRT.WholePlaneGFFLateral

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls
open MatedCRT.RotationalAverage

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- The maximum of `‖z‖` and `1` is positive, so that the logarithms in `wholePlaneCov` are defined. -/
lemma max_pos_one (z : ℂ) : 0 < max ‖z‖ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)

/-- Against a test function the logarithmic kernel is integrable: `y ↦ ψ y · wholePlaneCov x y` is integrable. -/
lemma integrable_test_mul_wholePlaneCov {ψ : ℂ → ℝ} (hψ : IsTestFunction Set.univ ψ) (x : ℂ) :
    Integrable (fun y : ℂ => ψ y * wholePlaneCov x y) := by
  have hψc : Integrable ψ := hψ.1.continuous.integrable_of_hasCompactSupport hψ.2.1
  have hlogM : Integrable (fun y : ℂ => ψ y * Real.log (max ‖y‖ 1)) := by
    refine Continuous.integrable_of_hasCompactSupport (hψ.1.continuous.mul
      (Continuous.log (continuous_norm.max continuous_const) fun y => (max_pos_one y).ne')) ?_
    exact hψ.2.1.mul_right
  have hlog : Integrable (fun y : ℂ => ψ y * Real.log ‖x - y‖) := by
    have hψx : IsTestFunction Set.univ (fun v : ℂ => ψ (x - v)) :=
      ⟨hψ.1.comp (contDiff_const.sub contDiff_id), hψ.2.1.comp_homeomorph (Homeomorph.subLeft x),
        Set.subset_univ _⟩
    have h := (integrable_test_mul_log_norm hψx).comp_sub_left x
    refine h.congr (ae_of_all _ fun y => ?_)
    simp
  have hsum : Integrable (fun y : ℂ => Real.log (max ‖x‖ 1) * ψ y + ψ y * Real.log (max ‖y‖ 1)
      - ψ y * Real.log ‖x - y‖) :=
    ((hψc.const_mul _).add hlogM).sub hlog
  have hne : ∀ᵐ y ∂(volume : Measure ℂ), y ≠ x := by
    rw [ae_iff]
    simp
  refine hsum.congr ?_
  filter_upwards [hne] with y hy
  have hxy : x - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
  unfold wholePlaneCov
  rw [Real.log_div (mul_pos (max_pos_one x) (max_pos_one y)).ne' (norm_ne_zero_iff.mpr hxy),
    Real.log_mul (max_pos_one x).ne' (max_pos_one y).ne']
  ring

/-- Rotational averaging of the logarithmic kernel: for a radial test function `ψ` and every `x`,
`∫ ψ(y) wholePlaneCov(x,y) dy = ∫ ψ(y) (log max(|x|,1) + log max(|y|,1) - log max(|x|,|y|)) dy`. -/
lemma integral_test_mul_wholePlaneCov {ψ : ℂ → ℝ} (hψ : IsTestFunction Set.univ ψ)
    (hψr : ∀ (θ : ℝ) (x : ℂ), ψ (rot θ x) = ψ x) (x : ℂ) :
    ∫ y, ψ y * wholePlaneCov x y = ∫ y, ψ y *
      (Real.log (max ‖x‖ 1) + Real.log (max ‖y‖ 1) - Real.log (max ‖x‖ ‖y‖)) := by
  have hm : Measurable (fun y : ℂ => wholePlaneCov x y) := by
    unfold wholePlaneCov
    fun_prop
  have h := integral_avgRot_mul (Φ := fun y => wholePlaneCov x y) (g := ψ) hm
    hψ.1.continuous.measurable hψr
    (by simpa only [mul_comm] using integrable_test_mul_wholePlaneCov hψ x)
  have hne0 : ∀ᵐ y ∂(volume : Measure ℂ), y ≠ 0 := by
    rw [ae_iff]
    simp
  calc ∫ y, ψ y * wholePlaneCov x y = ∫ y, wholePlaneCov x y * ψ y := by
        simp only [mul_comm]
    _ = ∫ y, avgRot (fun w => wholePlaneCov x w) y * ψ y := h.symm
    _ = ∫ y, ψ y * (Real.log (max ‖x‖ 1) + Real.log (max ‖y‖ 1) - Real.log (max ‖x‖ ‖y‖)) := by
        refine integral_congr_ae ?_
        filter_upwards [hne0] with y hy
        rw [avgRot_eq_circleAverage, circleAverage_wholePlaneCov (norm_pos_iff.mpr hy), mul_comm,
          max_comm ‖y‖ ‖x‖]

/-- The radial point of a rotated point is the radial point of the point. -/
lemma radialPoint_rot (θ : ℝ) (x : ℂ) : radialPoint (rot θ x) = radialPoint x := by
  have hz : rot θ x = 0 ↔ x = 0 := by
    rw [← norm_eq_zero, norm_rot, norm_eq_zero]
  simp only [radialPoint, hz, norm_rot]

/-- The radial integral of `φ` agrees almost surely with the radial integral of its rotational average. -/
theorem ae_radialIntegral_eq_avgRot {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc)
    {φ : ℂ → ℝ} (hφ : IsTestFunction (Metric.ball (0 : ℂ) 1) φ) :
    ∀ᵐ ω ∂P, ∫ x, φ x * hcirc ω ‖x‖ 0 = ∫ x, avgRot φ x * hcirc ω ‖x‖ 0 := by
  obtain ⟨F, hF, hFae⟩ := exists_ae_circle_version h
  have hφU : IsTestFunction Set.univ φ := ⟨hφ.1, hφ.2.1, Set.subset_univ _⟩
  have hint := (integrable_radial_one h hF hFae hφU).prod_right_ae
  filter_upwards [hint, ae_radialIntegral_eq hFae φ, ae_radialIntegral_eq hFae (avgRot φ)] with ω h1 h3 h4
  have hg : Measurable (fun x : ℂ => F ω (radialPoint x)) :=
    (F ω).continuous.measurable.comp measurable_radialPoint
  have key := integral_avgRot_mul (Φ := φ) (g := fun x => F ω (radialPoint x))
    hφ.1.continuous.measurable hg (fun θ x => by simp only [radialPoint_rot]) h1
  rw [h3, h4]
  exact key.symm

/-- Symmetry of the radial kernel `log max(|s|,1) + log max(|t|,1) - log max(|s|,|t|)`. -/
lemma radialKernel_comm (s t : ℝ) :
    Real.log (max s 1) + Real.log (max t 1) - Real.log (max s t)
      = Real.log (max t 1) + Real.log (max s 1) - Real.log (max t s) := by
  rw [max_comm t s]
  ring

/-- Second moment of a pairing with a radial test function: `E[hC(ψ)²] = ∫∫ ψ ψ C`. -/
theorem integral_pairing_sq_eq [IsProbabilityMeasure P] (h : IsWholePlaneGFF P hC hcirc)
    {ψ : ℂ → ℝ} (hψ : IsTestFunction Set.univ ψ) (hψr : ∀ (θ : ℝ) (x : ℂ), ψ (rot θ x) = ψ x) :
    ∫ ω, hC ω ψ * hC ω ψ ∂P = ∫ x, ψ x * ∫ y, ψ y *
      (Real.log (max ‖x‖ 1) + Real.log (max ‖y‖ 1) - Real.log (max ‖x‖ ‖y‖)) := by
  have hcov := h.covariance_eq (.pairing ψ) (.pairing ψ) hψ hψ
  have hmean : ∫ ω, hC ω ψ ∂P = 0 := h.integral_eq_zero (.pairing ψ) hψ
  have hYi : Integrable (fun ω => hC ω ψ) P := (memLp_two_pairing h hψ).integrable one_le_two
  have hXY : Integrable (fun ω => hC ω ψ * hC ω ψ) P :=
    ((memLp_two_pairing h hψ).integrable_sq).congr (ae_of_all _ fun ω => pow_two _)
  have hcov' : covariance (fun ω => hC ω ψ) (fun ω => hC ω ψ) P
      = ∫ x, ψ x * ∫ y, ψ y * wholePlaneCov x y := hcov
  rw [covariance_eq_integral_of_mean_zero hmean hYi hXY] at hcov'
  rw [hcov']
  congr 1
  funext x
  congr 1
  exact integral_test_mul_wholePlaneCov hψ hψr x

/-- The radial pairing with `hC ψ` integrates against the radial integral: `E[hC(ψ) L_ψ] = ∫∫ ψ ψ C`. -/
theorem integral_pairing_mul_radialIntegral [IsProbabilityMeasure P] (h : IsWholePlaneGFF P hC hcirc)
    {F : Ω → C(CircleParameter, ℝ)} (hF : Measurable F)
    (hFae : ∀ᵐ ω ∂P, ∀ p : CircleParameter, F ω p = hcirc ω (p.1 : ℝ) p.2)
    {ψ : ℂ → ℝ} (hψ : IsTestFunction Set.univ ψ) :
    ∫ ω, hC ω ψ * ∫ y, ψ y * F ω (radialPoint y) ∂volume ∂P = ∫ x, ψ x * ∫ y, ψ y *
      (Real.log (max ‖x‖ 1) + Real.log (max ‖y‖ 1) - Real.log (max ‖x‖ ‖y‖)) := by
  have hZm : Measurable (fun ω => hC ω ψ) := h.measurable_pairing ψ hψ
  have hmain := integrable_radial_mul h hF hFae hψ hZm (memLp_two_pairing h hψ) rfl
  have hI : Integrable (Function.uncurry fun ω y => hC ω ψ * (ψ y * F ω (radialPoint y)))
      (P.prod volume) :=
    hmain.congr (ae_of_all _ fun q => by dsimp only [Function.uncurry]; ring)
  have hsw : ∫ ω, ∫ y, hC ω ψ * (ψ y * F ω (radialPoint y)) ∂volume ∂P
      = ∫ y, ∫ ω, hC ω ψ * (ψ y * F ω (radialPoint y)) ∂P ∂volume :=
    integral_integral_swap hI
  have hne0 : ∀ᵐ y ∂(volume : Measure ℂ), y ≠ 0 := by
    rw [ae_iff]
    simp
  have hstep : ∀ y : ℂ, y ≠ 0 → ∫ ω, hC ω ψ * (ψ y * F ω (radialPoint y)) ∂P
      = ψ y * ∫ x, ψ x * (Real.log (max ‖x‖ 1) + Real.log (max ‖y‖ 1) - Real.log (max ‖x‖ ‖y‖)) := by
    intro y hy
    have hr : 0 < ‖y‖ := norm_pos_iff.mpr hy
    have hpt : ∀ᵐ ω ∂P, hC ω ψ * (ψ y * F ω (radialPoint y)) = ψ y * (hC ω ψ * hcirc ω ‖y‖ 0) := by
      filter_upwards [hFae] with ω hω
      have hrp : ((radialPoint y).1 : ℝ) = ‖y‖ := by simp [radialPoint, hy]
      rw [hω (radialPoint y), hrp, show (radialPoint y).2 = 0 from rfl]
      ring
    rw [integral_congr_ae hpt, integral_const_mul, integral_pairing_mul_circle h hψ hr]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    dsimp only
    rw [circleAverage_wholePlaneCov hr, max_comm ‖y‖ ‖x‖]
  calc ∫ ω, hC ω ψ * ∫ y, ψ y * F ω (radialPoint y) ∂volume ∂P
      = ∫ ω, ∫ y, hC ω ψ * (ψ y * F ω (radialPoint y)) ∂volume ∂P := by
        refine integral_congr_ae (ae_of_all _ fun ω => ?_)
        dsimp only
        rw [integral_const_mul]
    _ = ∫ y, ∫ ω, hC ω ψ * (ψ y * F ω (radialPoint y)) ∂P ∂volume := hsw
    _ = ∫ y, ψ y * ∫ x, ψ x * (Real.log (max ‖x‖ 1) + Real.log (max ‖y‖ 1) - Real.log (max ‖x‖ ‖y‖))
          ∂volume := by
        refine integral_congr_ae ?_
        filter_upwards [hne0] with y hy
        rw [hstep y hy]
    _ = ∫ x, ψ x * ∫ y, ψ y *
          (Real.log (max ‖x‖ 1) + Real.log (max ‖y‖ 1) - Real.log (max ‖x‖ ‖y‖)) := by
        congr 1
        funext u
        congr 1
        refine integral_congr_ae (ae_of_all _ fun v => ?_)
        dsimp only
        rw [radialKernel_comm ‖v‖ ‖u‖]

/-- The second moment of the radial integral of a radial test function, `E[L_ψ²] = ∫∫ ψ ψ C`. -/
theorem integral_radialIntegral_sq_eq [IsProbabilityMeasure P] (h : IsWholePlaneGFF P hC hcirc)
    {F : Ω → C(CircleParameter, ℝ)} (hF : Measurable F)
    (hFae : ∀ᵐ ω ∂P, ∀ p : CircleParameter, F ω p = hcirc ω (p.1 : ℝ) p.2)
    {ψ : ℂ → ℝ} (hψ : IsTestFunction (Metric.ball (0 : ℂ) 1) ψ) :
    ∫ ω, (∫ y, ψ y * F ω (radialPoint y) ∂volume) * (∫ y, ψ y * F ω (radialPoint y) ∂volume) ∂P
      = ∫ x, ψ x * ∫ y, ψ y *
        (Real.log (max ‖x‖ 1) + Real.log (max ‖y‖ 1) - Real.log (max ‖x‖ ‖y‖)) := by
  have hψU : IsTestFunction Set.univ ψ := ⟨hψ.1, hψ.2.1, Set.subset_univ _⟩
  have hcov := covariance_radialIntegral h hψ hψ
  rw [covariance_congr_ae (ae_radialIntegral_eq hFae ψ) (ae_radialIntegral_eq hFae ψ)] at hcov
  have hmean : ∫ ω, ∫ y, ψ y * F ω (radialPoint y) ∂volume ∂P = 0 :=
    integral_radialIntegral_eq_zero h hF hFae hψU
  have hYi : Integrable (fun ω => ∫ y, ψ y * F ω (radialPoint y) ∂volume) P :=
    (integrable_radial_one h hF hFae hψU).integral_prod_left
  have hT := integrable_radial_triple h hF hFae hψU hψU
  have hprod : ∀ ω, (∫ x, ψ x * F ω (radialPoint x)) * (∫ y, ψ y * F ω (radialPoint y)) =
      ∫ p : ℂ × ℂ, ψ p.1 * F ω (radialPoint p.1) * (ψ p.2 * F ω (radialPoint p.2))
        ∂(volume.prod volume) :=
    fun ω => (integral_prod_mul (fun x => ψ x * F ω (radialPoint x))
      (fun y => ψ y * F ω (radialPoint y))).symm
  have hXY : Integrable (fun ω => (∫ x, ψ x * F ω (radialPoint x)) *
      (∫ y, ψ y * F ω (radialPoint y))) P :=
    hT.integral_prod_left.congr (ae_of_all _ fun ω => (hprod ω).symm)
  rw [covariance_eq_integral_of_mean_zero hmean hYi hXY] at hcov
  have hrhs : ∫ x : ℂ, ∫ y : ℂ, ψ x * ψ y * (Real.log (max ‖x‖ 1) + Real.log (max ‖y‖ 1) - Real.log (max ‖x‖ ‖y‖))
      = ∫ x : ℂ, ψ x * ∫ y : ℂ, ψ y * (Real.log (max ‖x‖ 1) + Real.log (max ‖y‖ 1) - Real.log (max ‖x‖ ‖y‖)) := by
    congr 1
    funext x
    rw [← integral_const_mul]
    congr 1
    funext y
    ring
  rw [hrhs] at hcov
  exact hcov

/-- The radial pairing `hC ψ` equals the radial integral of a radial test function `ψ` almost surely:
both have the same first and second moments against the radial circle averages, and the second moment
of their difference vanishes. -/
theorem pairing_eq_radialIntegral_ae [IsProbabilityMeasure P] (h : IsWholePlaneGFF P hC hcirc)
    {F : Ω → C(CircleParameter, ℝ)} (hF : Measurable F)
    (hFae : ∀ᵐ ω ∂P, ∀ p : CircleParameter, F ω p = hcirc ω (p.1 : ℝ) p.2)
    {ψ : ℂ → ℝ} (hψ : IsTestFunction (Metric.ball (0 : ℂ) 1) ψ)
    (hψr : ∀ (θ : ℝ) (x : ℂ), ψ (rot θ x) = ψ x) :
    ∀ᵐ ω ∂P, hC ω ψ = ∫ y, ψ y * F ω (radialPoint y) ∂volume := by
  have hψU : IsTestFunction Set.univ ψ := ⟨hψ.1, hψ.2.1, Set.subset_univ _⟩
  have hZm : Measurable (fun ω => hC ω ψ) := h.measurable_pairing ψ hψU
  have hmain := integrable_radial_mul h hF hFae hψU hZm (memLp_two_pairing h hψU) rfl
  have hT := integrable_radial_triple h hF hFae hψU hψU
  have hprod : ∀ ω, (∫ x, ψ x * F ω (radialPoint x)) * (∫ y, ψ y * F ω (radialPoint y)) =
      ∫ p : ℂ × ℂ, ψ p.1 * F ω (radialPoint p.1) * (ψ p.2 * F ω (radialPoint p.2))
        ∂(volume.prod volume) :=
    fun ω => (integral_prod_mul (fun x => ψ x * F ω (radialPoint x))
      (fun y => ψ y * F ω (radialPoint y))).symm
  have hAi : Integrable (fun ω => hC ω ψ * hC ω ψ) P :=
    ((memLp_two_pairing h hψU).integrable_sq).congr (ae_of_all _ fun ω => pow_two _)
  have hALi : Integrable (fun ω => hC ω ψ * ∫ y, ψ y * F ω (radialPoint y) ∂volume) P :=
    hmain.integral_prod_left.congr (ae_of_all _ fun ω => by
      dsimp only
      rw [integral_mul_const]
      ring)
  have hLi : Integrable (fun ω => (∫ y, ψ y * F ω (radialPoint y) ∂volume) *
      (∫ y, ψ y * F ω (radialPoint y) ∂volume)) P :=
    hT.integral_prod_left.congr (ae_of_all _ fun ω => (hprod ω).symm)
  have hexp : ∀ ω, (hC ω ψ - ∫ y, ψ y * F ω (radialPoint y) ∂volume)
      * (hC ω ψ - ∫ y, ψ y * F ω (radialPoint y) ∂volume)
      = (hC ω ψ * hC ω ψ - 2 * (hC ω ψ * ∫ y, ψ y * F ω (radialPoint y) ∂volume))
        + (∫ y, ψ y * F ω (radialPoint y) ∂volume) * (∫ y, ψ y * F ω (radialPoint y) ∂volume) :=
    fun ω => by ring
  have hZi : Integrable (fun ω => (hC ω ψ - ∫ y, ψ y * F ω (radialPoint y) ∂volume)
      * (hC ω ψ - ∫ y, ψ y * F ω (radialPoint y) ∂volume)) P :=
    ((hAi.sub (hALi.const_mul 2)).add hLi).congr (ae_of_all _ fun ω => (hexp ω).symm)
  have hI1 : Integrable (fun ω => hC ω ψ * hC ω ψ - 2 * (hC ω ψ * ∫ y, ψ y * F ω (radialPoint y) ∂volume)) P :=
    hAi.sub (hALi.const_mul 2)
  have hzero : ∫ ω, (hC ω ψ - ∫ y, ψ y * F ω (radialPoint y) ∂volume)
      * (hC ω ψ - ∫ y, ψ y * F ω (radialPoint y) ∂volume) ∂P = 0 := by
    rw [integral_congr_ae (ae_of_all _ hexp), integral_add hI1 hLi, integral_sub hAi (hALi.const_mul 2),
      integral_const_mul, integral_pairing_sq_eq h hψU hψr,
      integral_pairing_mul_radialIntegral h hF hFae hψU, integral_radialIntegral_sq_eq h hF hFae hψ]
    ring
  have hz0 := (integral_eq_zero_iff_of_nonneg (fun ω => mul_self_nonneg _) hZi).mp hzero
  filter_upwards [hz0] with ω hω
  have h2 : (hC ω ψ - ∫ y, ψ y * F ω (radialPoint y) ∂volume)
      * (hC ω ψ - ∫ y, ψ y * F ω (radialPoint y) ∂volume) = 0 := hω
  exact sub_eq_zero.mp (mul_self_eq_zero.mp h2)


/-- The rotational average of a test function supported in the unit disc is one. -/
lemma isTestFunction_avgRot_ball {φ : ℂ → ℝ} (hφ : IsTestFunction (Metric.ball (0 : ℂ) 1) φ) :
    IsTestFunction (Metric.ball (0 : ℂ) 1) (avgRot φ) := by
  obtain ⟨h1, h2, h3⟩ := hφ
  exact avgRot_test h1 h2 h3

/-- **N2.** The lateral pairings `hC φ - ∫ φ(x) h_{|x|}(0) dx` of a whole-plane GFF, indexed by test
functions supported in the unit disc, form a Gaussian process. -/
theorem isGaussianProcess_lateral_ball [IsProbabilityMeasure P] (h : IsWholePlaneGFF P hC hcirc) :
    IsGaussianProcess (fun (φ : {φ : ℂ → ℝ // IsTestFunction (Metric.ball (0 : ℂ) 1) φ}) (ω : Ω) =>
      hC ω φ.1 - ∫ x, φ.1 x * hcirc ω ‖x‖ 0) P := by
  obtain ⟨F, hF, hFae⟩ := exists_ae_circle_version h
  have hU : ∀ {ψ : ℂ → ℝ}, IsTestFunction (Metric.ball (0 : ℂ) 1) ψ → IsTestFunction Set.univ ψ :=
    fun hψ => ⟨hψ.1, hψ.2.1, Set.subset_univ _⟩
  have hY : IsGaussianProcess (fun (φ : {φ : ℂ → ℝ // IsTestFunction (Metric.ball (0 : ℂ) 1) φ}) (ω : Ω) =>
      hC ω φ.1 - hC ω (avgRot φ.1)) P := by
    refine h.isGaussianProcess.of_isGaussianProcess (fun φ => ?_)
    classical
    have hψ := isTestFunction_avgRot_ball φ.2
    let a : GFFObservable.Admissible := ⟨GFFObservable.pairing φ.1, hU φ.2⟩
    let b : GFFObservable.Admissible := ⟨GFFObservable.pairing (avgRot φ.1), hU hψ⟩
    refine ⟨{a, b}, ContinuousLinearMap.proj ⟨a, Finset.mem_insert_self _ _⟩ -
      ContinuousLinearMap.proj ⟨b, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩, fun ω => ?_⟩
    simp [Finset.restrict, a, b, GFFObservable.eval]
  refine hY.congr (fun φ => ?_)
  filter_upwards [ae_radialIntegral_eq_avgRot h φ.2,
    pairing_eq_radialIntegral_ae h hF hFae (isTestFunction_avgRot_ball φ.2)
      (fun θ x => avgRot_rot φ.1 θ x),
    ae_radialIntegral_eq hFae (avgRot φ.1)] with ω h1 h2 h3
  rw [h1, h3, ← h2]

/-- **N2 (mean-zero form).** The lateral pairings `hC φ - ∫ φ(x) h_{|x|}(0) dx` of a whole-plane GFF, indexed by
mean-zero test functions supported in the unit disc, form a Gaussian process. -/
theorem isGaussianProcess_lateral [IsProbabilityMeasure P] (h : IsWholePlaneGFF P hC hcirc) :
    IsGaussianProcess (fun (φ : {φ : ℂ → ℝ // IsTestFunction (Metric.ball (0 : ℂ) 1) φ ∧ ∫ x, φ x = 0})
      (ω : Ω) => hC ω φ.1 - ∫ x, φ.1 x * hcirc ω ‖x‖ 0) P :=
  (isGaussianProcess_lateral_ball h).comp_right fun φ : {φ : ℂ → ℝ // IsTestFunction (Metric.ball (0 : ℂ) 1) φ ∧ ∫ x, φ x = 0} =>
    (⟨φ.1, φ.2.1⟩ : {φ : ℂ → ℝ // IsTestFunction (Metric.ball (0 : ℂ) 1) φ})

end MatedCRT.WholePlaneGFFLateral
