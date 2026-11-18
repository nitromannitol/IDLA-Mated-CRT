import MatedCRT.FirstPass.Derived.PlanarBrownianPointPolar

/-!
# A uniform lower bound after a fixed time for planar Brownian motion

Let `E m` be an increasing sequence of measurable path events whose union holds almost surely for
planar Brownian motion started from Lebesgue-almost every point. Then for every positive time `s`
there are `p > 0` and an index `m` such that, uniformly over starting points `u` in the closed unit
disc, the shifted path `θ_s b` lies in `E m` with probability at least `p`.

The proof is the simple Markov property at the fixed time `s` (`planarBrownianMotion_map_shift`):
the probability equals `∫ P^w(E m) dN(u, s I₂)(w)`, and the planar Gaussian with mean in the unit
disc dominates a constant multiple of Lebesgue measure on the disc (its density there is bounded
below), so monotone convergence on the disc concludes. No Harnack inequality and no continuity in
the starting point are used.

## Main results

* `smul_volume_restrict_le_gaussianReal`: lower bound of a real Gaussian on `[-1, 1]`.
* `smul_volume_restrict_closedBall_le_planarGaussian`: lower bound of a planar Gaussian on the
  closed unit disc, for a mean in that disc.
* `exists_pos_forall_closedBall_le_planarBrownianMotion_shift`: the uniform lower bound.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology Metric MarkovProcess
open scoped ENNReal NNReal

namespace MatedCRT.KilledOccupation

open _root_.HarmonicBalls

/-- A real Gaussian with mean in `[-1, 1]` and positive variance `v` dominates the constant
`(2πv)^{-1/2} e^{-4/(2v)}` times Lebesgue measure on `[-1, 1]`. -/
theorem smul_volume_restrict_le_gaussianReal {m : ℝ} (hm : |m| ≤ 1) {v : ℝ≥0} (hv : v ≠ 0) :
    ENNReal.ofReal ((Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-4 / (2 * v))) •
        (volume : Measure ℝ).restrict (Icc (-1) 1) ≤ gaussianReal m v := by
  have hv0 : (0 : ℝ) < v := by exact_mod_cast pos_iff_ne_zero.mpr hv
  rw [gaussianReal_of_var_ne_zero m hv, ← withDensity_const,
    ← withDensity_indicator measurableSet_Icc]
  apply withDensity_mono
  filter_upwards with x
  by_cases hx : x ∈ Icc (-1 : ℝ) 1
  · rw [indicator_of_mem hx, gaussianPDF_def, gaussianPDFReal_def]
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Real.sqrt_nonneg _))
    apply Real.exp_le_exp.mpr
    have habs : |x - m| ≤ 2 := by
      rw [abs_le] at hm ⊢
      constructor <;> linarith [hx.1, hx.2]
    have hsq : (x - m) ^ 2 ≤ 4 := by
      nlinarith [abs_nonneg (x - m), sq_abs (x - m)]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  · rw [indicator_of_notMem hx]
    exact zero_le

/-- A planar Gaussian with mean in the closed unit disc and positive variance `v` dominates a
positive constant times planar Lebesgue measure on the closed unit disc. -/
theorem smul_volume_restrict_closedBall_le_planarGaussian {u : ℂ}
    (hu : u ∈ closedBall (0 : ℂ) 1) {v : ℝ≥0} (hv : v ≠ 0) :
    ENNReal.ofReal ((Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-4 / (2 * v))) ^ 2 •
        (volume : Measure ℂ).restrict (closedBall 0 1) ≤ planarGaussian u v := by
  set c := ENNReal.ofReal ((Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-4 / (2 * v)))
  have hun : ‖u‖ ≤ 1 := by simpa using hu
  have hre : |u.re| ≤ 1 := (Complex.abs_re_le_norm u).trans hun
  have him : |u.im| ≤ 1 := (Complex.abs_im_le_norm u).trans hun
  have hprod := Measure.prod_mono (smul_volume_restrict_le_gaussianReal hre hv)
    (smul_volume_restrict_le_gaussianReal him hv)
  have hm := Measure.map_mono hprod Complex.measurableEquivRealProd.symm.measurable
  rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
    Measure.map_smul _ Complex.measurableEquivRealProd.symm.measurable.aemeasurable,
    Measure.prod_restrict] at hm
  let S : Set ℂ := {w | w.re ∈ Icc (-1 : ℝ) 1 ∧ w.im ∈ Icc (-1 : ℝ) 1}
  have hset : Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 =
      Complex.measurableEquivRealProd.symm ⁻¹' S := by
    ext p
    exact Iff.rfl
  rw [hset, ← MeasurableEquiv.restrict_map] at hm
  have hvol : ((volume : Measure ℝ).prod volume).map Complex.measurableEquivRealProd.symm =
      (volume : Measure ℂ) := Complex.volume_preserving_equiv_real_prod.symm.map_eq
  rw [hvol] at hm
  have hsub : closedBall (0 : ℂ) 1 ⊆ S := by
    intro w hw
    have hwn : ‖w‖ ≤ 1 := by simpa using hw
    exact ⟨abs_le.mp ((Complex.abs_re_le_norm w).trans hwn),
      abs_le.mp ((Complex.abs_im_le_norm w).trans hwn)⟩
  refine le_trans (Measure.le_iff'.2 fun A => ?_) hm
  rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul, pow_two]
  exact mul_le_mul' le_rfl (Measure.restrict_mono hsub le_rfl A)

/-- **Uniform lower bound after a fixed time.** Let `E m` be an increasing sequence of measurable
path events whose union holds almost surely for planar Brownian motion started from
Lebesgue-almost every point. For every positive time `s` there are `p > 0` and an index `m` such
that, for every start `u` in the closed unit disc, the path shifted by `s` lies in `E m` with
probability at least `p`. -/
theorem exists_pos_forall_closedBall_le_planarBrownianMotion_shift
    {E : ℕ → Set (ContinuousPath ℂ)} (hE : ∀ m, MeasurableSet (E m)) (hmono : Monotone E)
    (hfull : ∀ᵐ w ∂(volume : Measure ℂ), ∀ᵐ b ∂(planarBrownianMotion w), b ∈ ⋃ m, E m)
    {s : ℝ≥0} (hs : s ≠ 0) :
    ∃ p : ℝ≥0∞, 0 < p ∧ ∃ m, ∀ u ∈ closedBall (0 : ℂ) 1,
      p ≤ planarBrownianMotion u (ContinuousPath.shift s ⁻¹' E m) := by
  set c := ENNReal.ofReal ((Real.sqrt (2 * Real.pi * s))⁻¹ * Real.exp (-4 / (2 * s))) ^ 2
    with hc_def
  set K := closedBall (0 : ℂ) 1 with hK_def
  set g : ℕ → ℂ → ℝ≥0∞ := fun m w => planarBrownianMotion w (E m) with hg_def
  have hg : ∀ m, Measurable (g m) := fun m => Kernel.measurable_coe _ (hE m)
  have hgmono : Monotone g := fun m n hmn w => measure_mono (hmono hmn)
  have hsup : ∀ᵐ w ∂(volume.restrict K), ⨆ m, g m w = 1 := by
    refine ae_restrict_of_ae ?_
    filter_upwards [hfull] with w hw
    rw [hg_def]
    simp only
    rw [← hmono.measure_iUnion]
    rw [← prob_compl_eq_zero_iff (MeasurableSet.iUnion hE)]
    exact ae_iff.mp hw
  have hint : ⨆ m, ∫⁻ w in K, g m w = volume K := by
    rw [← lintegral_iSup hg hgmono, lintegral_congr_ae hsup, lintegral_one,
      Measure.restrict_apply_univ]
  have hKpos : 0 < volume K := measure_closedBall_pos volume (0 : ℂ) one_pos
  have hKfin : volume K ≠ ∞ := (measure_closedBall_lt_top (x := (0 : ℂ)) (r := 1)).ne
  have hhalf : volume K / 2 < ⨆ m, ∫⁻ w in K, g m w := by
    rw [hint]
    exact ENNReal.half_lt_self hKpos.ne' hKfin
  obtain ⟨m, hm⟩ := lt_iSup_iff.mp hhalf
  have hs0 : (0 : ℝ) < s := by exact_mod_cast pos_iff_ne_zero.mpr hs
  have hcpos : 0 < c := by
    refine ENNReal.pow_pos (ENNReal.ofReal_pos.mpr (mul_pos ?_ (Real.exp_pos _))) 2
    exact inv_pos.mpr (Real.sqrt_pos.mpr (by positivity))
  refine ⟨c * (volume K / 2), ENNReal.mul_pos hcpos.ne' (ENNReal.half_pos hKpos.ne').ne', m,
    fun u hu => ?_⟩
  have hshift := planarBrownianMotion_map_shift u s
  rw [← Measure.map_apply (ContinuousPath.continuous_shift_fixed s).measurable (hE m), hshift,
    Measure.bind_apply (hE m) planarBrownianMotion.measurable.aemeasurable]
  calc c * (volume K / 2) ≤ c * ∫⁻ w in K, g m w := mul_le_mul' le_rfl hm.le
    _ = ∫⁻ w, g m w ∂(c • (volume : Measure ℂ).restrict K) := by
      rw [lintegral_smul_measure, smul_eq_mul]
    _ ≤ ∫⁻ w, planarBrownianMotion w (E m) ∂(planarGaussian u s) :=
      lintegral_mono' (smul_volume_restrict_closedBall_le_planarGaussian hu hs) le_rfl

end MatedCRT.KilledOccupation
