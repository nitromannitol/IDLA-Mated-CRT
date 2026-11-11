import MatedCRT.FirstPass.S2y.LateralBilin250

/-!
# L¹ convergence of the radial part of the lateral pairing

For `I_g(ω) = ∫ g(y) h_{|y|}(0) dy` with `g` bounded, measurable, supported in a fixed ball and tending to `0`
pointwise: `E|I_g| ≤ ∫ |g(y)| (1 + 3|log|y||) dy → 0` (Tonelli-type Fubini, `E|h_r(0)| ≤ 1 + 3|log r|`).
-/

open MeasureTheory ProbabilityTheory Filter Set Topology Real Metric HarmonicBalls

namespace MatedCRT.LQGMeasure

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Fubini integrability of `g(y) A_ω(y)` on `P ⊗ Leb` for a jointly measurable `A`, a bounded measurable `g`
supported in `closedBall 0 R`, with `y ↦ E A_y²` integrable on that ball. -/
lemma integrable_mul_prod_of_bdd [IsProbabilityMeasure P] {A : Ω → ℂ → ℝ}
    (hAm : Measurable (fun p : Ω × ℂ => A p.1 p.2)) {g : ℂ → ℝ} (hgm : Measurable g) {C R : ℝ} (hC0 : 0 ≤ C)
    (hgC : ∀ y, |g y| ≤ C) (hgR : ∀ y, y ∉ closedBall (0 : ℂ) R → g y = 0)
    (hAL2 : ∀ᵐ y ∂(volume.restrict (closedBall (0 : ℂ) R)), MemLp (fun ω => A ω y) 2 P)
    (hAint : IntegrableOn (fun y => ∫ ω, (A ω y) ^ 2 ∂P) (closedBall (0 : ℂ) R)) :
    Integrable (fun p : Ω × ℂ => g p.2 * A p.1 p.2) (P.prod (volume : Measure ℂ)) := by
  set B := closedBall (0 : ℂ) R with hBdef
  have hBm : MeasurableSet B := measurableSet_closedBall
  set ind : ℂ → ℝ := B.indicator fun _ => (1 : ℝ) with hind_def
  have hind : Integrable ind volume :=
    (integrableOn_const measure_closedBall_lt_top.ne).integrable_indicator hBm
  have hH : Integrable (fun p : Ω × ℂ => ind p.2 * A p.1 p.2 ^ 2) (P.prod (volume : Measure ℂ)) := by
    have hHm : Measurable (fun p : Ω × ℂ => ind p.2 * A p.1 p.2 ^ 2) :=
      ((measurable_const.indicator hBm).comp measurable_snd).mul (hAm.pow_const 2)
    refine (integrable_prod_iff' hHm.aestronglyMeasurable).2 ⟨?_, ?_⟩
    · have h1 : ∀ᵐ y ∂(volume : Measure ℂ), y ∈ B → Integrable (fun ω => ind y * A ω y ^ 2) P := by
        rw [← ae_restrict_iff' hBm]
        filter_upwards [hAL2, ae_restrict_mem hBm] with y hy hyB
        have hy2 := hy.integrable_sq
        refine (hy2.const_mul 1).congr (Eventually.of_forall fun ω => ?_)
        simp [hind_def, Set.indicator_of_mem hyB]
      filter_upwards [h1] with y hy
      by_cases hyB : y ∈ B
      · exact hy hyB
      · have : (fun ω => ind y * A ω y ^ 2) = fun _ => 0 := by
          funext ω; simp [hind_def, Set.indicator_of_notMem hyB]
        rw [this]; exact integrable_zero _ _ _
    · refine ((integrable_indicator_iff hBm).2 hAint).congr (Eventually.of_forall fun y => ?_)
      by_cases hyB : y ∈ B
      · simp [hind_def, Set.indicator_of_mem hyB, Real.norm_eq_abs, sq_abs]
      · simp [hind_def, Set.indicator_of_notMem hyB]
  have hG : Integrable (fun p : Ω × ℂ => (C / 2) * (1 * ind p.2) + (C / 2) * (ind p.2 * A p.1 p.2 ^ 2))
      (P.prod (volume : Measure ℂ)) :=
    ((Integrable.mul_prod (integrable_const (1 : ℝ)) hind).const_mul (C / 2)).add (hH.const_mul (C / 2))
  refine hG.mono' ?_ ?_
  · exact ((hgm.comp measurable_snd).mul hAm).aestronglyMeasurable
  · refine Eventually.of_forall fun p => ?_
    obtain ⟨ω, y⟩ := p
    by_cases hyB : y ∈ B
    · have hind1 : ind y = 1 := Set.indicator_of_mem hyB _
      simp only [hind1, one_mul, Real.norm_eq_abs, abs_mul]
      have hgy := hgC y
      nlinarith [mul_le_mul_of_nonneg_right hgy (abs_nonneg (A ω y)), mul_nonneg hC0 (sq_nonneg (|A ω y| - 1)),
        sq_abs (A ω y)]
    · have hgy : g y = 0 := hgR y hyB
      simp [hgy, hind_def, Set.indicator_of_notMem hyB]

/-- `|radialCov r r| ≤ 3 |log r|` for `r > 0`. -/
lemma abs_radialCov_self_le (r : ℝ) :
    |MatedCRT.Field.ConeRadial.radialCov r r| ≤ 3 * |Real.log r| := by
  have hm : |Real.log (max r 1)| ≤ |Real.log r| := by
    have := abs_log_max_le r 1
    rwa [Real.log_one, abs_zero, add_zero] at this
  have e : MatedCRT.Field.ConeRadial.radialCov r r =
      Real.log (max r 1) + Real.log (max r 1) - Real.log r := by
    unfold MatedCRT.Field.ConeRadial.radialCov; rw [max_self]
  rw [e]
  calc |Real.log (max r 1) + Real.log (max r 1) - Real.log r|
      ≤ |Real.log (max r 1) + Real.log (max r 1)| + |Real.log r| := abs_sub _ _
    _ ≤ (|Real.log (max r 1)| + |Real.log (max r 1)|) + |Real.log r| := by
        gcongr; exact abs_add_le _ _
    _ ≤ 3 * |Real.log r| := by linarith

/-- **L¹ convergence of the radial part (general form).** For a jointly measurable `A` with `A(·,y) = h_{|y|}(0)` a.s.
for `y ≠ 0`, and bounded measurable `g n` supported in `closedBall 0 R` tending to `0` pointwise,
`E|∫ g_n(y) A_ω(y) dy| → 0`. -/
theorem tendsto_integral_abs_radial_gen [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) {A : Ω → ℂ → ℝ}
    (hAm : Measurable (fun p : Ω × ℂ => A p.1 p.2))
    (hAeq : ∀ y : ℂ, y ≠ 0 → (fun ω => A ω y) =ᵐ[P] (fun ω => hcirc ω ‖y‖ 0))
    {g : ℕ → ℂ → ℝ} {R M : ℝ} (hgm : ∀ n, Measurable (g n))
    (hgM : ∀ n y, |g n y| ≤ M) (hgR : ∀ n y, y ∉ closedBall (0 : ℂ) R → g n y = 0)
    (hlim : ∀ y, Tendsto (fun n => g n y) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, |∫ y, g n y * A ω y| ∂P) atTop (𝓝 0) := by
  have hC0 : 0 ≤ M := (abs_nonneg _).trans (hgM 0 0)
  have hy0 : ∀ᵐ y ∂(volume : Measure ℂ), y ≠ 0 := by
    rw [ae_iff]; simp
  have hAL2 : ∀ᵐ y ∂(volume.restrict (closedBall (0 : ℂ) R)), MemLp (fun ω => A ω y) 2 P :=
    ae_restrict_of_ae (hy0.mono fun y hy =>
      (memLp_circle_zero h (norm_pos_iff.2 hy)).ae_eq (hAeq y hy).symm)
  have hcv : ∀ᵐ y ∂(volume.restrict (closedBall (0 : ℂ) R)),
      ∫ ω, (A ω y) ^ 2 ∂P = MatedCRT.Field.ConeRadial.radialCov ‖y‖ ‖y‖ :=
    ae_restrict_of_ae (hy0.mono fun y hy => by
      have e : (fun ω => (A ω y) ^ 2) =ᵐ[P] (fun ω => (hcirc ω ‖y‖ 0) ^ 2) :=
        (hAeq y hy).fun_comp (fun t : ℝ => t ^ 2)
      rw [integral_congr_ae e]
      exact integral_sq_circle_zero h (norm_pos_iff.2 hy))
  have hfB : IntegrableOn (fun y : ℂ => MatedCRT.Field.ConeRadial.radialCov ‖y‖ ‖y‖) (closedBall (0 : ℂ) R) := by
    have hdom : IntegrableOn (fun y : ℂ => 3 * |Real.log ‖y‖|) (closedBall (0 : ℂ) R) :=
      (((integrableOn_log_norm_ball (R + 1)).mono_set (closedBall_subset_ball (by linarith))).abs).const_mul 3
    have hmeas : Measurable (fun y : ℂ => MatedCRT.Field.ConeRadial.radialCov ‖y‖ ‖y‖) := by
      unfold MatedCRT.Field.ConeRadial.radialCov
      fun_prop
    refine Integrable.mono' hdom hmeas.aestronglyMeasurable ?_
    exact ae_restrict_of_ae (hy0.mono fun y _ => abs_radialCov_self_le ‖y‖)
  have hAint : IntegrableOn (fun y => ∫ ω, (A ω y) ^ 2 ∂P) (closedBall (0 : ℂ) R) :=
    hfB.congr_fun_ae (hcv.mono fun y hy => hy.symm)
  have hgn : ∀ n, Integrable (fun p : Ω × ℂ => g n p.2 * A p.1 p.2) (P.prod (volume : Measure ℂ)) :=
    fun n => integrable_mul_prod_of_bdd hAm (hgm n) hC0 (hgM n) (hgR n) hAL2 hAint
  have hAm' : Measurable (fun p : Ω × ℂ => |A p.1 p.2|) := continuous_abs.measurable.comp hAm
  have hAL2' : ∀ᵐ y ∂(volume.restrict (closedBall (0 : ℂ) R)), MemLp (fun ω => |A ω y|) 2 P :=
    hAL2.mono fun y hy => by simpa [Real.norm_eq_abs] using hy.norm
  have hAint' : IntegrableOn (fun y => ∫ ω, (|A ω y|) ^ 2 ∂P) (closedBall (0 : ℂ) R) := by
    simpa only [sq_abs] using hAint
  have hgabs : ∀ n, Integrable (fun p : Ω × ℂ => |g n p.2| * |A p.1 p.2|) (P.prod (volume : Measure ℂ)) :=
    fun n => integrable_mul_prod_of_bdd (A := fun ω y => |A ω y|) hAm' (g := fun y => |g n y|)
      (continuous_abs.measurable.comp (hgm n)) hC0 (fun y => by simpa [abs_abs] using hgM n y)
      (fun y hy => by simp [hgR n y hy]) hAL2' hAint'
  have hpt : ∀ n ω, |∫ y, g n y * A ω y| ≤ ∫ y, |g n y| * |A ω y| := fun n ω => by
    calc |∫ y, g n y * A ω y| = ‖∫ y, g n y * A ω y‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ y, ‖g n y * A ω y‖ := norm_integral_le_integral_norm _
      _ = ∫ y, |g n y| * |A ω y| := by simp only [Real.norm_eq_abs, abs_mul]
  have hstepA : ∀ n, ∫ ω, |∫ y, g n y * A ω y| ∂P ≤ ∫ y, |g n y| * ∫ ω, |A ω y| ∂P := fun n => by
    have hI1 : Integrable (fun ω => |∫ y, g n y * A ω y|) P := (Integrable.integral_prod_left (hgn n)).abs
    have hI2 : Integrable (fun ω => ∫ y, |g n y| * |A ω y|) P := Integrable.integral_prod_left (hgabs n)
    calc ∫ ω, |∫ y, g n y * A ω y| ∂P ≤ ∫ ω, (∫ y, |g n y| * |A ω y|) ∂P :=
          integral_mono hI1 hI2 (fun ω => hpt n ω)
      _ = ∫ y, ∫ ω, |g n y| * |A ω y| ∂P :=
          integral_integral_swap (f := fun ω y => |g n y| * |A ω y|) (hgabs n)
      _ = ∫ y, |g n y| * ∫ ω, |A ω y| ∂P := by simp only [integral_const_mul]
  -- pointwise bound by the Gaussian first absolute moment
  have hbdy : ∀ n, ∀ᵐ y ∂(volume : Measure ℂ),
      |g n y| * ∫ ω, |A ω y| ∂P ≤ |g n y| * (1 + 3 * |Real.log ‖y‖|) := by
    intro n
    filter_upwards [hy0] with y hy
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have e : ∫ ω, |A ω y| ∂P = ∫ ω, |hcirc ω ‖y‖ 0| ∂P :=
      integral_congr_ae ((hAeq y hy).fun_comp abs)
    rw [e]
    exact integral_abs_circle_zero_le h (norm_pos_iff.2 hy)
  -- dominating function on the ball
  have hdomB : IntegrableOn (fun y : ℂ => M + 3 * M * |Real.log ‖y‖|) (closedBall (0 : ℂ) R) :=
    (integrableOn_const measure_closedBall_lt_top.ne).add
      ((((integrableOn_log_norm_ball (R + 1)).mono_set (closedBall_subset_ball (by linarith))).abs).const_mul
        (3 * M))
  have hBm : MeasurableSet (closedBall (0 : ℂ) R) := measurableSet_closedBall
  have hbd_int : Integrable ((closedBall (0 : ℂ) R).indicator fun y : ℂ => M + 3 * M * |Real.log ‖y‖|) volume :=
    (integrable_indicator_iff hBm).2 hdomB
  have hmeasF : ∀ n, AEStronglyMeasurable (fun y : ℂ => |g n y| * (1 + 3 * |Real.log ‖y‖|)) volume := fun n =>
    ((continuous_abs.measurable.comp (hgm n)).mul (measurable_const.add (measurable_const.mul
      (continuous_abs.measurable.comp (Real.measurable_log.comp measurable_norm))))).aestronglyMeasurable
  have hbound : ∀ n, ∀ᵐ y ∂(volume : Measure ℂ),
      ‖|g n y| * (1 + 3 * |Real.log ‖y‖|)‖ ≤ (closedBall (0 : ℂ) R).indicator
        (fun y : ℂ => M + 3 * M * |Real.log ‖y‖|) y := by
    intro n
    refine Eventually.of_forall fun y => ?_
    by_cases hyB : y ∈ closedBall (0 : ℂ) R
    · rw [indicator_of_mem hyB, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (by positivity))]
      have h1 := hgM n y
      have h2 : 0 ≤ 3 * |Real.log ‖y‖| := by positivity
      nlinarith [mul_le_mul_of_nonneg_right h1 (by linarith : (0:ℝ) ≤ 1 + 3 * |Real.log ‖y‖|)]
    · rw [indicator_of_notMem hyB, hgR n y hyB]; simp
  have hDn : Tendsto (fun n => ∫ y, |g n y| * (1 + 3 * |Real.log ‖y‖|) ∂volume) atTop (𝓝 0) := by
    have hlimF : ∀ y : ℂ, Tendsto (fun n => |g n y| * (1 + 3 * |Real.log ‖y‖|)) atTop (𝓝 0) := fun y => by
      simpa using ((hlim y).abs).mul_const (1 + 3 * |Real.log ‖y‖|)
    have := tendsto_integral_of_dominated_convergence (μ := volume)
      ((closedBall (0 : ℂ) R).indicator fun y : ℂ => M + 3 * M * |Real.log ‖y‖|) hmeasF hbd_int hbound
      (Eventually.of_forall fun y => hlimF y)
    simpa using this
  have hbound_n : ∀ n, ∫ y, |g n y| * ∫ ω, |A ω y| ∂P ≤ ∫ y, |g n y| * (1 + 3 * |Real.log ‖y‖|) := by
    intro n
    have hIn : Integrable (fun y => |g n y| * ∫ ω, |A ω y| ∂P) volume := by
      have e : (fun y => |g n y| * ∫ ω, |A ω y| ∂P) = fun y => ∫ ω, |g n y| * |A ω y| ∂P := by
        funext y; rw [integral_const_mul]
      rw [e]; exact (hgabs n).integral_prod_right
    have hJn : Integrable (fun y => |g n y| * (1 + 3 * |Real.log ‖y‖|)) volume :=
      Integrable.mono' hbd_int (hmeasF n) (hbound n)
    exact integral_mono_ae hIn hJn (hbdy n)
  exact squeeze_zero (fun n => integral_nonneg fun ω => abs_nonneg _)
    (fun n => (hstepA n).trans (hbound_n n)) hDn

/-- **L¹ convergence of the radial part.** For bounded measurable `g n` supported in `closedBall 0 R` and tending to `0`
pointwise, `E|∫ g_n(y) h_{|y|}(0) dy| → 0`. -/
theorem tendsto_integral_abs_radial [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) {g : ℕ → ℂ → ℝ} {R M : ℝ} (hgm : ∀ n, Measurable (g n))
    (hgM : ∀ n y, |g n y| ≤ M) (hgR : ∀ n y, y ∉ closedBall (0 : ℂ) R → g n y = 0)
    (hlim : ∀ y, Tendsto (fun n => g n y) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, |∫ y, g n y * MatedCRT.CirclePairing.radialVersion hcirc ω ‖y‖| ∂P) atTop (𝓝 0) :=
  tendsto_integral_abs_radial_gen h
    ((MatedCRT.CirclePairing.measurable_radialVersion h.measurable_circle).comp
      (measurable_fst.prodMk measurable_snd.norm))
    (fun _ hy => radialVersion_ae_eq h (norm_pos_iff.2 hy)) hgm hgM hgR hlim

end MatedCRT.LQGMeasure
