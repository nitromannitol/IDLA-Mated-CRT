import MarkovProcess.Examples.BrownianMotion
import HarmonicBalls.Defs.Brownian
import HarmonicBalls.Proofs.Brownian.PlanarHeatSemigroup
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.PathOccupationEnergy
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-! # Gaussian increments of planar Brownian motion -/

namespace MatedCRT

open MeasureTheory ProbabilityTheory MarkovProcess HarmonicBalls
open scoped NNReal ENNReal

/-- An increment of standard planar Brownian motion has the centered planar
Gaussian law with covariance equal to the elapsed time. -/
theorem planarBrownianMotion_map_increment (z : ℂ) (s t : ℝ≥0) (hst : s ≤ t) :
    (planarBrownianMotion z).map (fun b => b t - b s) = planarGaussian 0 (t - s) := by
  let F : ContinuousPath ℝ → ℝ := fun b => b t - b s
  let G : ContinuousPath ℝ × ContinuousPath ℝ → ℝ × ℝ := fun p => (F p.1, F p.2)
  have hF : Measurable F := by dsimp [F]; fun_prop
  have hG : Measurable G := (hF.comp measurable_fst).prodMk (hF.comp measurable_snd)
  have hC : Measurable (fun b : ContinuousPath ℂ => b t - b s) := by fun_prop
  have hcomm : (fun b : ContinuousPath ℂ => b t - b s) ∘ complexPathOfReIm =
      Complex.measurableEquivRealProd.symm ∘ G := by
    funext p
    apply Complex.ext <;> simp [G, F, complexPathOfReIm_apply]
  rw [planarBrownianMotion_apply, Measure.map_map hC measurable_complexPathOfReIm,
    hcomm, ← Measure.map_map Complex.measurableEquivRealProd.symm.measurable hG,
    show G = Prod.map F F from rfl, ← Measure.map_prod_map _ _ hF hF]
  simp only [F, brownianMotion_map_increment _ _ _ hst, planarGaussian,
    Complex.zero_re, Complex.zero_im]

/-- The expected Riesz kernel of a planar Brownian increment is the
corresponding integral against its centered planar Gaussian law. -/
theorem planarBrownianMotion_expected_increment_energy (z : ℂ) (s t : ℝ≥0)
    (hst : s ≤ t) (a : ℝ) :
    (∫⁻ b, rieszEnergyKernel a (b t) (b s) ∂(planarBrownianMotion z)) =
      ∫⁻ w, rieszEnergyKernel a w 0 ∂(planarGaussian 0 (t - s)) := by
  have hk : Measurable (fun w : ℂ => rieszEnergyKernel a w 0) :=
    (measurable_rieszEnergyKernel a).comp (measurable_id.prodMk measurable_const)
  have hinc : Measurable (fun b : ContinuousPath ℂ => b t - b s) := by fun_prop
  rw [← planarBrownianMotion_map_increment z s t hst, lintegral_map hk hinc]
  apply lintegral_congr
  intro b
  simp [rieszEnergyKernel, dist_eq_norm]

/-- The expected increment energy is symmetric in its two time arguments. -/
theorem planarBrownianMotion_expected_increment_energy_any_order (z : ℂ)
    (s t : ℝ≥0) (a : ℝ) :
    (∫⁻ b, rieszEnergyKernel a (b t) (b s) ∂(planarBrownianMotion z)) =
      ∫⁻ w, rieszEnergyKernel a w 0 ∂(planarGaussian 0 (max s t - min s t)) := by
  by_cases hst : s ≤ t
  · simpa [max_eq_right hst, min_eq_left hst] using
      planarBrownianMotion_expected_increment_energy z s t hst a
  · have hts : t ≤ s := le_of_not_ge hst
    have heq : (∫⁻ b, rieszEnergyKernel a (b t) (b s) ∂(planarBrownianMotion z)) =
        ∫⁻ b, rieszEnergyKernel a (b s) (b t) ∂(planarBrownianMotion z) := by
      apply lintegral_congr
      intro b
      simp only [rieszEnergyKernel, dist_comm]
    rw [heq]
    simpa [max_eq_left hts, min_eq_right hts] using
      planarBrownianMotion_expected_increment_energy z t s hts a

/-- A positive spatial dilation scales the Riesz kernel by the inverse
power of the dilation factor. -/
theorem rieszEnergyKernel_complex_positive_scale (a r : ℝ) (ha : 0 < a)
    (hr : 0 < r) (w : ℂ) :
    rieszEnergyKernel a ((r : ℂ) * w) 0 =
      ENNReal.ofReal (r ^ (-a)) * rieszEnergyKernel a w 0 := by
  by_cases hw : w = 0
  · subst w
    have hp : ENNReal.ofReal (r ^ (-a)) ≠ 0 :=
      ne_of_gt (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hr _))
    simp [rieszEnergyKernel, ha, hp]
  · have hz : (r : ℂ) * w ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne') hw
    simp only [rieszEnergyKernel, dist_eq_norm, sub_zero, norm_eq_zero, hw, hz,
      false_and, ↓reduceIte]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
      Real.mul_rpow hr.le (norm_nonneg w), ENNReal.ofReal_mul (Real.rpow_nonneg hr.le _)]

/-- Positive-time planar Gaussian Riesz moments scale by the inverse power
of the square root of the variance. -/
theorem planarGaussian_rieszEnergy_scale (a : ℝ) (ha : 0 < a)
    (t : ℝ≥0) (ht : 0 < t) :
    (∫⁻ w, rieszEnergyKernel a w 0 ∂(planarGaussian 0 t)) =
      ENNReal.ofReal ((Real.sqrt t) ^ (-a)) *
        ∫⁻ w, rieszEnergyKernel a w 0 ∂stdPlanarGaussian := by
  have hk : Measurable (fun w : ℂ => rieszEnergyKernel a w 0) :=
    (measurable_rieszEnergyKernel a).comp (measurable_id.prodMk measurable_const)
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr (by exact_mod_cast ht)
  rw [planarGaussian_eq_map_add_sqrt_mul 0 t, lintegral_map hk (by fun_prop)]
  simp_rw [zero_add, rieszEnergyKernel_complex_positive_scale a _ ha hs]
  exact lintegral_const_mul _ hk

/-- At distinct ordered times, expected Brownian increment energy has the
power-law factor `(t-s)^(-a/2)`. -/
theorem planarBrownianMotion_expected_increment_energy_scale (z : ℂ)
    (s t : ℝ≥0) (hst : s < t) (a : ℝ) (ha : 0 < a) :
    (∫⁻ b, rieszEnergyKernel a (b t) (b s) ∂(planarBrownianMotion z)) =
      ENNReal.ofReal (((t - s : ℝ≥0) : ℝ) ^ (-a / 2)) *
        ∫⁻ w, rieszEnergyKernel a w 0 ∂stdPlanarGaussian := by
  rw [planarBrownianMotion_expected_increment_energy z s t hst.le a,
    planarGaussian_rieszEnergy_scale a ha (t - s) (tsub_pos_iff_lt.mpr hst),
    Real.sqrt_eq_rpow, ← Real.rpow_mul (NNReal.coe_nonneg _)]
  congr 2
  ring

/-- The singular Riesz power is integrable on a bounded planar ball below
the planar dimension. -/
theorem integrableOn_planar_norm_rpow (a R : ℝ) (ha : a < 2) :
    IntegrableOn (fun w : ℂ => ‖w‖ ^ (-a)) (Metric.ball 0 R) volume := by
  have hm : Measurable (fun w : ℂ => ‖w‖ ^ (-a)) := by
    simp_rw [Real.rpow_def_of_nonneg (norm_nonneg _)]
    have hz : MeasurableSet {w : ℂ | ‖w‖ = 0} :=
      (measurableSet_singleton (0 : ℝ)).preimage (by fun_prop)
    apply Measurable.ite hz
    · split_ifs <;> fun_prop
    · fun_prop
  apply integrableOn_ball_of_norm_le_rpow (μ := volume) (C := 1) (α := a)
    (by norm_num : 1 ≤ Module.finrank ℝ ℂ)
  · simpa using ha
  · filter_upwards with w
    simp [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg w) _)]
  · exact hm.aestronglyMeasurable

/-- A nondegenerate Gaussian measure is bounded by a constant multiple of
Lebesgue measure, with the constant given by its density at the mean. -/
theorem gaussianReal_le_peak_smul_volume (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    gaussianReal m v ≤ ENNReal.ofReal ((Real.sqrt (2 * Real.pi * v))⁻¹) • volume := by
  rw [gaussianReal_of_var_ne_zero m hv, ← withDensity_const]
  apply withDensity_mono
  filter_upwards with x
  rw [gaussianPDF_def, gaussianPDFReal_def]
  apply ENNReal.ofReal_le_ofReal
  have he : Real.exp (-(x - m) ^ 2 / (2 * (v : ℝ))) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)
  calc
    (Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-(x - m) ^ 2 / (2 * (v : ℝ))) ≤
        (Real.sqrt (2 * Real.pi * v))⁻¹ * 1 :=
      mul_le_mul_of_nonneg_left he (inv_nonneg.mpr (Real.sqrt_nonneg _))
    _ = _ := mul_one _

/-- A nondegenerate planar Gaussian is bounded by a finite multiple of
planar Lebesgue measure. -/
theorem planarGaussian_le_peak_smul_volume (z : ℂ) (v : ℝ≥0) (hv : v ≠ 0) :
    planarGaussian z v ≤
      (ENNReal.ofReal ((Real.sqrt (2 * Real.pi * v))⁻¹) ^ 2) • volume := by
  let c : ℝ≥0∞ := ENNReal.ofReal ((Real.sqrt (2 * Real.pi * v))⁻¹)
  have hprod : (gaussianReal z.re v).prod (gaussianReal z.im v) ≤
      (c • (volume : Measure ℝ)).prod (c • (volume : Measure ℝ)) := by
    exact Measure.prod_mono (gaussianReal_le_peak_smul_volume z.re v hv)
      (gaussianReal_le_peak_smul_volume z.im v hv)
  have hm := Measure.map_mono hprod Complex.measurableEquivRealProd.symm.measurable
  rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
    Measure.map_smul _ Complex.measurableEquivRealProd.symm.measurable.aemeasurable] at hm
  have hvol : ((volume : Measure ℝ).prod volume).map Complex.measurableEquivRealProd.symm =
      (volume : Measure ℂ) := Complex.volume_preserving_equiv_real_prod.symm.map_eq
  rw [hvol] at hm
  simpa [planarGaussian, c, pow_two] using hm


/-- The standard planar Gaussian has finite Riesz energy of order below two. -/
theorem stdPlanarGaussian_riesz_moment_lt_top (a : ℝ) (ha : 0 < a) (ha2 : a < 2) :
    (∫⁻ w, rieszEnergyKernel a w 0 ∂stdPlanarGaussian) < ⊤ := by
  let B : Set ℂ := Metric.ball 0 1
  let K : ℂ → ℝ≥0∞ := fun w => rieszEnergyKernel a w 0
  have hlocal : (∫⁻ w in B, K w ∂volume) < ⊤ := by
    have h := (integrableOn_planar_norm_rpow a 1 ha2).lintegral_lt_top
    apply lt_of_le_of_lt _ h
    apply le_of_eq
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : ℂ))] with w hw
    simp [K, rieszEnergyKernel, dist_eq_norm, hw]
  have hlocal' : (∫⁻ w in B, K w ∂stdPlanarGaussian) < ⊤ := by
    have hbound := planarGaussian_le_peak_smul_volume 0 1 (by norm_num)
    have hle : (∫⁻ w in B, K w ∂stdPlanarGaussian) ≤
        ∫⁻ w in B, K w ∂((ENNReal.ofReal ((Real.sqrt (2 * Real.pi * (1 : ℝ≥0)))⁻¹) ^ 2) • volume) := by
      apply lintegral_mono' _ le_rfl
      exact Measure.restrict_mono (Set.Subset.rfl) hbound
    apply lt_of_le_of_lt hle
    rw [Measure.restrict_smul, lintegral_smul_measure]
    exact ENNReal.mul_lt_top (by finiteness) hlocal
  have hout : (∫⁻ w in Bᶜ, K w ∂stdPlanarGaussian) < ⊤ := by
    have hle : (∫⁻ w in Bᶜ, K w ∂stdPlanarGaussian) ≤
        ∫⁻ _ in Bᶜ, (1 : ℝ≥0∞) ∂stdPlanarGaussian := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (Metric.isOpen_ball.measurableSet.compl)] with w hw
      have hn : 1 ≤ ‖w‖ := by simpa [B, Metric.mem_ball, dist_eq_norm] using hw
      have hw0 : w ≠ 0 := by intro he; simp [he] at hn; norm_num at hn
      simp only [K, rieszEnergyKernel, dist_eq_norm, sub_zero, norm_eq_zero, hw0,
        false_and, ite_false]
      exact (ENNReal.ofReal_le_ofReal (Real.rpow_le_one_of_one_le_of_nonpos hn (neg_nonpos.mpr ha.le))).trans (by simp)
    exact lt_of_le_of_lt hle (by simp)
  rw [← lintegral_add_compl K (Metric.isOpen_ball.measurableSet)]
  exact ENNReal.add_lt_top.mpr ⟨hlocal', hout⟩


/-- Distinct-time planar Brownian increments have finite expected Riesz
energy for every order strictly between zero and two. -/
theorem planarBrownianMotion_expected_increment_energy_lt_top (z : ℂ)
    (s t : ℝ≥0) (hst : s ≠ t) (a : ℝ) (ha : 0 < a) (ha2 : a < 2) :
    (∫⁻ b, rieszEnergyKernel a (b t) (b s) ∂(planarBrownianMotion z)) < ⊤ := by
  rw [planarBrownianMotion_expected_increment_energy_any_order z s t a]
  have ht : 0 < max s t - min s t := by
    apply tsub_pos_iff_lt.mpr
    exact min_lt_max.mpr hst
  rw [planarGaussian_rieszEnergy_scale a ha _ ht]
  exact ENNReal.mul_lt_top (by finiteness) (stdPlanarGaussian_riesz_moment_lt_top a ha ha2)

/-- A one-dimensional Riesz power of order below one is locally integrable. -/
theorem integrableOn_real_norm_rpow (a R : ℝ) (ha : a < 1) :
    IntegrableOn (fun w : ℝ => ‖w‖ ^ (-a)) (Metric.ball 0 R) volume := by
  have hm : Measurable (fun w : ℝ => ‖w‖ ^ (-a)) := by
    simp_rw [Real.rpow_def_of_nonneg (norm_nonneg _)]
    have hz : MeasurableSet {w : ℝ | ‖w‖ = 0} :=
      (measurableSet_singleton (0 : ℝ)).preimage (by fun_prop)
    apply Measurable.ite hz
    · split_ifs <;> fun_prop
    · fun_prop
  apply integrableOn_ball_of_norm_le_rpow (μ := volume) (C := 1) (α := a)
    (by norm_num : 1 ≤ Module.finrank ℝ ℝ)
  · simpa using ha
  · filter_upwards with w
    simp only [Real.norm_eq_abs, one_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg w) _), le_refl]
  · exact hm.aestronglyMeasurable


/-- The one-dimensional time-difference singularity is integrable over a
finite time square for orders below one. -/
theorem time_difference_riesz_integral_lt_top (a T : ℝ) (ha : a < 1) :
    (∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ t in Set.Icc (0 : ℝ) T,
      ENNReal.ofReal (‖t - s‖ ^ (-a))) < ⊤ := by
  let R := |T| + 1
  let f : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (‖x‖ ^ (-a))
  have hf : Measurable f := by
    have hm : Measurable (fun w : ℝ => ‖w‖ ^ (-a)) := by
      simp_rw [Real.rpow_def_of_nonneg (norm_nonneg _)]
      have hz : MeasurableSet {w : ℝ | ‖w‖ = 0} :=
        (measurableSet_singleton (0 : ℝ)).preimage (by fun_prop)
      apply Measurable.ite hz
      · split_ifs <;> fun_prop
      · fun_prop
    exact hm.ennreal_ofReal
  have hfin : (∫⁻ x in Metric.ball (0 : ℝ) R, f x) < ⊤ :=
    (integrableOn_real_norm_rpow a R ha).lintegral_lt_top
  have hbound : ∀ s ∈ Set.Icc (0 : ℝ) T,
      (∫⁻ t in Set.Icc (0 : ℝ) T, f (t - s)) ≤
        ∫⁻ x in Metric.ball (0 : ℝ) R, f x := by
    intro s hs
    have hsub : Set.Icc (0 : ℝ) T ⊆ (fun t : ℝ => t + -s) ⁻¹' Metric.ball 0 R := by
      intro t ht
      simp only [Set.mem_preimage, Metric.mem_ball, Real.dist_eq, sub_zero, R]
      rw [abs_lt]
      constructor <;> linarith [le_abs_self T, hs.1, hs.2, ht.1, ht.2]
    calc
      (∫⁻ t in Set.Icc (0 : ℝ) T, f (t - s)) ≤
          ∫⁻ t in (fun t : ℝ => t + -s) ⁻¹' Metric.ball 0 R, f (t + -s) := by
        simp only [sub_eq_add_neg]
        exact lintegral_mono_set hsub
      _ = ∫⁻ x in Metric.ball (0 : ℝ) R, f x :=
        (measurePreserving_add_right volume (-s)).setLIntegral_comp_preimage
          Metric.isOpen_ball.measurableSet hf
  apply lt_of_le_of_lt _ (show (∫⁻ _ in Set.Icc (0 : ℝ) T,
    ∫⁻ x in Metric.ball (0 : ℝ) R, f x) < ⊤ by
      simpa using ENNReal.mul_lt_top hfin (show ENNReal.ofReal T < ⊤ by finiteness))
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  exact hbound s hs


/-- The two-time expected Riesz kernel depends on the absolute time difference. -/
theorem planarBrownianMotion_expected_increment_energy_abs (z : ℂ)
    (s t : ℝ≥0) (hst : s ≠ t) (a : ℝ) (ha : 0 < a) :
    (∫⁻ b, rieszEnergyKernel a (b t) (b s) ∂(planarBrownianMotion z)) =
      ENNReal.ofReal (‖(t : ℝ) - (s : ℝ)‖ ^ (-a / 2)) *
        ∫⁻ w, rieszEnergyKernel a w 0 ∂stdPlanarGaussian := by
  rw [planarBrownianMotion_expected_increment_energy_any_order z s t a]
  have ht : 0 < max s t - min s t := tsub_pos_iff_lt.mpr (min_lt_max.mpr hst)
  rw [planarGaussian_rieszEnergy_scale a ha _ ht, Real.sqrt_eq_rpow,
    ← Real.rpow_mul (NNReal.coe_nonneg _)]
  have hd : ((max s t - min s t : ℝ≥0) : ℝ) = ‖(t : ℝ) - (s : ℝ)‖ := by
    rw [NNReal.coe_sub (min_le_max : min s t ≤ max s t), NNReal.coe_max, NNReal.coe_min,
      max_sub_min_eq_abs, Real.norm_eq_abs, abs_sub_comm]
  rw [hd]
  congr 2
  ring


/-- The expected Riesz energy of planar Brownian increments is integrable
on every finite time square for orders below two. -/
theorem planarBrownianMotion_time_integrated_expected_energy_lt_top
    (z : ℂ) (T a : ℝ) (ha : 0 < a) (ha2 : a < 2) :
    (∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ t in Set.Icc (0 : ℝ) T,
      ∫⁻ b, rieszEnergyKernel a (b t.toNNReal) (b s.toNNReal)
        ∂(planarBrownianMotion z)) < ⊤ := by
  let c := ∫⁻ w, rieszEnergyKernel a w 0 ∂stdPlanarGaussian
  let f : ℝ × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal (‖p.2 - p.1‖ ^ (-(a / 2)))
  have hf : Measurable f := by
    have hm : Measurable (fun w : ℝ => ‖w‖ ^ (-(a / 2))) := by
      simp_rw [Real.rpow_def_of_nonneg (norm_nonneg _)]
      have hz : MeasurableSet {w : ℝ | ‖w‖ = 0} :=
        (measurableSet_singleton (0 : ℝ)).preimage (by fun_prop)
      apply Measurable.ite hz
      · split_ifs <;> fun_prop
      · fun_prop
    exact (hm.comp (measurable_snd.sub measurable_fst)).ennreal_ofReal
  have hpoint : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      (∫⁻ t in Set.Icc (0 : ℝ) T,
        ∫⁻ b, rieszEnergyKernel a (b t.toNNReal) (b s.toNNReal)
          ∂(planarBrownianMotion z)) =
      ∫⁻ t in Set.Icc (0 : ℝ) T, f (s,t) * c := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae (volume.ae_ne s)] with t ht hts
    have hne : s.toNNReal ≠ t.toNNReal := by
      intro he
      have hc := congrArg (fun x : ℝ≥0 => (x : ℝ)) he
      rw [Real.coe_toNNReal s hs.1, Real.coe_toNNReal t ht.1] at hc
      exact hts hc.symm
    rw [planarBrownianMotion_expected_increment_energy_abs z s.toNNReal t.toNNReal hne a ha,
      Real.coe_toNNReal s hs.1, Real.coe_toNNReal t ht.1]
    congr 3; ring
  have heq : (∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ t in Set.Icc (0 : ℝ) T,
      ∫⁻ b, rieszEnergyKernel a (b t.toNNReal) (b s.toNNReal)
        ∂(planarBrownianMotion z)) =
      (∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ t in Set.Icc (0 : ℝ) T, f (s,t)) * c := by
    rw [lintegral_congr_ae hpoint]
    calc
      _ = ∫⁻ s in Set.Icc (0 : ℝ) T, (∫⁻ t in Set.Icc (0 : ℝ) T, f (s,t)) * c := by
        apply lintegral_congr
        intro s
        exact lintegral_mul_const c (hf.comp (measurable_const.prodMk measurable_id))
      _ = _ := lintegral_mul_const c hf.lintegral_prod_right'
  rw [heq]
  exact ENNReal.mul_lt_top (time_difference_riesz_integral_lt_top (a / 2) T (by linarith))
    (stdPlanarGaussian_riesz_moment_lt_top a ha ha2)

end MatedCRT
