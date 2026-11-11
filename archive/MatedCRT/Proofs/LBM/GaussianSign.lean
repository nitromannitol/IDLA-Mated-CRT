import MatedCRT.Proofs.LBM.BrownianExitBall

/-! Sign probabilities for the Gaussian marginals of Brownian motion. -/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Set HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

/-- A centred, nondegenerate real Gaussian distribution assigns half its mass
to either open half-line. -/
theorem gaussianReal_zero_measure_Ioi (v : ℝ≥0) (hv : v ≠ 0) :
    gaussianReal 0 v (Ioi 0) = 1 / 2 := by
  let μ := gaussianReal 0 v
  have hzero : μ {0} = 0 :=
    gaussianReal_absolutelyContinuous 0 hv (measure_singleton 0)
  have hsymm : μ (Ioi 0) = μ (Iio 0) := by
    have hmap : μ.map (fun x : ℝ => -x) = μ := by
      simpa [μ] using (gaussianReal_map_neg (μ := 0) (v := v))
    have h := congrArg (fun ν : Measure ℝ => ν (Ioi 0)) hmap
    rw [Measure.map_apply measurable_neg measurableSet_Ioi] at h
    have hpre : (fun x : ℝ => -x) ⁻¹' Ioi 0 = Iio 0 := by
      ext x
      simp
    rw [hpre] at h
    exact h.symm
  have hfull : μ (Ioi 0 ∪ Iio 0) = 1 := by
    have hae : ∀ᵐ x ∂μ, x ≠ 0 := by
      rw [ae_iff]
      simpa using hzero
    have heq : μ (Ioi 0 ∪ Iio 0) = μ univ := by
      apply measure_congr
      filter_upwards [hae] with x hx
      simp only [mem_union, mem_Ioi, mem_Iio, mem_univ]
      exact propext (iff_true_intro (lt_or_gt_of_ne hx).symm)
    simpa using heq
  have hsum : μ (Ioi 0) + μ (Iio 0) = 1 := by
    rw [← measure_union (by exact disjoint_left.mpr (by intro x hx hy; exact (not_lt_of_ge (mem_Ioi.mp hx).le) (mem_Iio.mp hy)))
      measurableSet_Iio]
    exact hfull
  rw [← hsymm] at hsum
  apply (ENNReal.eq_div_iff (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).2
  simpa only [two_mul] using hsum

/-- At each positive time the real coordinate of planar Brownian motion is
above its initial value with probability one half. -/
theorem planarBrownianMotion_real_increase_at_time (y : ℂ) (t : ℝ≥0) (ht : t ≠ 0) :
    planarBrownianMotion y {b | y.re < (b t).re} = 1 / 2 := by
  have heval : Measurable (fun b : ContinuousPath ℂ => (b t).re) :=
    Complex.measurable_re.comp (ContinuousPath.continuous_eval t).measurable
  have hsub : Measurable (fun x : ℝ => x - y.re) := by fun_prop
  have hmap : (planarBrownianMotion y).map (fun b => (b t).re - y.re) = gaussianReal 0 t := by
    rw [show (fun b : ContinuousPath ℂ => (b t).re - y.re) =
      (fun x : ℝ => x - y.re) ∘ (fun b : ContinuousPath ℂ => (b t).re) from rfl,
      ← Measure.map_map hsub heval, planarBrownianMotion_map_real_eval_from,
      gaussianReal_map_sub_const, sub_self]
  have h := congrArg (fun μ : Measure ℝ => μ (Ioi 0)) hmap
  have hmeas : Measurable (fun b : ContinuousPath ℂ => (b t).re - y.re) := by fun_prop
  rw [Measure.map_apply hmeas measurableSet_Ioi] at h
  have hpre : (fun b : ContinuousPath ℂ => (b t).re - y.re) ⁻¹' Ioi 0 =
      {b | y.re < (b t).re} := by
    ext b
    simp [sub_pos]
  rw [hpre] at h
  exact h.trans (gaussianReal_zero_measure_Ioi t ht)

end MatedCRT
