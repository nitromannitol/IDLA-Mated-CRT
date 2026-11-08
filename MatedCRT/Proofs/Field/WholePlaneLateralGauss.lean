import MatedCRT.Proofs.Field.WholePlaneLateral
import MatedCRT.Proofs.Field.ConeLevelGaussian
import MatedCRT.Proofs.Field.ConeLevelIntegrable

/-!
# Gaussian level integrals of a radial process (eq:gff, circle level)

Let `W : ℝ → Ω → ℝ` be a radial process: `W u` is constant for `u ≤ 0`, `u ↦ W u ω` is a.s. continuous, `W u` lies
in a centred Gaussian linear space `M₀`, and `Cov(W_u, W_v) = min u v` for `u, v ≥ 0` (`IsRadialLevelData`). For a
circle `∂B_r(z)` with `0 < r < |z|` and `|z| + r < 1` (`InLevelRegion`), the circle average
`⨍_{∂B_r(z)} W_{-log|x|}` is a level integral over the circle parameter (`circleAverage_neg_log_eq_levelIntegral`),
hence (`levelIntegral_versions`) a.s. equal to a random variable `Y` in a centred Gaussian space containing `M₀`, with

* `Cov(W_u, Y) = ⨍_{∂B_r(z)} min(u, -log|x|)` for `u ≥ 0` (`radial_avg_cov_W`);
* `Cov(Y, Y') = ⨍_{∂B_{r'}(z')} ⨍_{∂B_r(z)} min(-log|x|, -log|y|)` for two such circles (`radial_avg_cov_pair`).

The statements only involve covariances, which are invariant under almost sure modification of the variables.
-/

namespace MatedCRT.Field

open MeasureTheory ProbabilityTheory Filter Topology Set Real Metric
open MatedCRT.Field.GaussClosure MatedCRT.Field.Level MatedCRT.Field.ConeRadial
open scoped NNReal

/-- The circle average of a function of `-log|x|` is the level integral over the circle parameter. -/
lemma circleAverage_neg_log_eq_levelIntegral (w : ℝ → ℝ) {r : ℝ} (_hr : 0 < r) (z : ℂ) (_hzr : r < ‖z‖) :
    Real.circleAverage (fun x => w (-Real.log ‖x‖)) z r =
      levelIntegral (volume.restrict (Ioc (0 : ℝ) (2 * π))) (fun _ => (2 * π)⁻¹)
        (fun θ => -Real.log ‖circleMap z r θ‖) w := by
  unfold Real.circleAverage levelIntegral
  rw [intervalIntegral.integral_of_le (by positivity), smul_eq_mul]
  simp only [integral_const_mul]

/-- A region circle: radius positive, the circle avoids `0`, and the closed disc lies in the unit disc. -/
def InLevelRegion (r : ℝ) (z : ℂ) : Prop := 0 < r ∧ r < ‖z‖ ∧ ‖z‖ + r < 1

lemma norm_circleMap_bounds {r : ℝ} (hr : 0 < r) (z : ℂ) (θ : ℝ) :
    ‖z‖ - r ≤ ‖circleMap z r θ‖ ∧ ‖circleMap z r θ‖ ≤ ‖z‖ + r := by
  have h2 : ‖circleMap z r θ - z‖ = r := by
    rw [circleMap_sub_center, norm_circleMap_zero, abs_of_pos hr]
  constructor
  · have h3 := norm_sub_norm_le z (circleMap z r θ)
    rw [norm_sub_rev] at h3
    linarith
  · have h3 := norm_add_le (circleMap z r θ - z) z
    rw [sub_add_cancel, h2] at h3
    linarith

lemma continuous_neg_log_circleMap {r : ℝ} (hr : 0 < r) (z : ℂ) (hzr : r < ‖z‖) :
    Continuous fun θ : ℝ => -Real.log ‖circleMap z r θ‖ := by
  have hne : ∀ θ : ℝ, ‖circleMap z r θ‖ ≠ 0 := fun θ => by
    have := (norm_circleMap_bounds hr z θ).1
    intro h
    linarith
  exact ((((continuous_circleMap z r).norm).log hne).neg)

/-- Abstract radial Gaussian data: `W` is constant on `(-∞, 0]`, a.s. continuous, measurable, all `W u` lie in the
centred Gaussian space `M₀`, and `Cov(W_u, W_v) = min(u, v)` for `u, v ≥ 0`. -/
structure IsRadialLevelData {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (W : ℝ → Ω → ℝ)
    (M₀ : Submodule ℝ (Ω → ℝ)) : Prop where
  meas : ∀ u, Measurable (W u)
  mem : ∀ u, W u ∈ M₀
  const_nonpos : ∀ u ≤ 0, W u = W 0
  cont : ∀ᵐ ω ∂P, Continuous fun u => W u ω
  cov : ∀ u v, 0 ≤ u → 0 ≤ v → covariance (W u) (W v) P = min u v

section Rep

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {W : ℝ → Ω → ℝ} {M₀ : Submodule ℝ (Ω → ℝ)}

/-- The circle level measure on the parameter `θ ∈ (0, 2π]`. -/
lemma continuous_on_circle_of_radial {r : ℝ} (hr : 0 < r) {z : ℂ} (hzr : r < ‖z‖) (w : ℝ → ℝ)
    (hw : Continuous w) :
    Continuous fun θ : ℝ => w (-Real.log ‖circleMap z r θ‖) :=
  hw.comp (continuous_neg_log_circleMap hr z hzr)

/-- **Gaussian level-integral representation of a radial circle average (raw form).** -/
theorem radial_level_rep (hW : IsRadialLevelData P W M₀) (hM₀ : IsCentredGaussianSpace P M₀)
    {r : ℝ} {z : ℂ} (hreg : InLevelRegion r z) :
    ∃ (T : ℕ → Ω → ℝ) (Y : Ω → ℝ), (∀ k, Measurable (T k)) ∧ (∀ k, IsAeLimitOf P M₀ (T k)) ∧ Measurable Y ∧
      (∀ᵐ ω ∂P, Tendsto (fun k => T k ω) atTop (𝓝 (Y ω))) ∧
      (∀ᵐ ω ∂P, Real.circleAverage (fun x => W (-Real.log ‖x‖) ω) z r = Y ω) ∧
      (∀ M' : Submodule ℝ (Ω → ℝ), IsCentredGaussianSpace P M' → M₀ ≤ M' → (∀ k, T k ∈ M') → Y ∈ M' →
        ∀ X ∈ M', Continuous (fun u => covariance X (W u) P) →
          Integrable (fun x => (2 * π)⁻¹ * covariance X
            (W (-Real.log ‖circleMap z r x‖)) P) (volume.restrict (Ioc (0 : ℝ) (2 * π))) →
          covariance X Y P = levelIntegral (volume.restrict (Ioc (0 : ℝ) (2 * π))) (fun _ => (2 * π)⁻¹)
            (fun θ => -Real.log ‖circleMap z r θ‖) (fun u => covariance X (W u) P)) := by
  obtain ⟨hr, hzr, -⟩ := hreg
  have hsc : Continuous fun θ : ℝ => -Real.log ‖circleMap z r θ‖ := continuous_neg_log_circleMap hr z hzr
  have hint : ∀ᵐ ω ∂P, Integrable (fun θ => (fun _ : ℝ => (2 * π)⁻¹) θ * W (-Real.log ‖circleMap z r θ‖) ω)
      (volume.restrict (Ioc (0 : ℝ) (2 * π))) := by
    filter_upwards [hW.cont] with ω hω
    have hc : Continuous fun θ : ℝ => (2 * π)⁻¹ * W (-Real.log ‖circleMap z r θ‖) ω :=
      continuous_const.mul (hω.comp hsc)
    exact (hc.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  obtain ⟨T, Y, hTm, hTlim, hYm, hconv, hrep, hform⟩ :=
    levelIntegral_versions hM₀ hW.mem hW.cont (integrable_const (2 * π)⁻¹) hsc.measurable hint
  refine ⟨T, Y, hTm, hTlim, hYm, hconv, ?_, ?_⟩
  · filter_upwards [hrep] with ω hω
    rw [← hω]
    exact circleAverage_neg_log_eq_levelIntegral (fun u => W u ω) hr z hzr
  · intro M' hM' hle hTM' hYM' X hX hcont hint'
    exact hform M' hM' hle hTM' hYM' X hX hcont hint'

end Rep

end MatedCRT.Field

namespace MatedCRT.Field

open MeasureTheory ProbabilityTheory Filter Topology Set Real Metric
open MatedCRT.Field.GaussClosure MatedCRT.Field.Level MatedCRT.Field.ConeRadial
open scoped NNReal

section Pair

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {W : ℝ → Ω → ℝ} {M₀ : Submodule ℝ (Ω → ℝ)}

/-- Points of a region circle have norm in `[|z| - r, |z| + r]`. -/
lemma region_norm_bounds {r : ℝ} {z x : ℂ} (hr : 0 < r) (hx : x ∈ sphere z |r|) :
    ‖z‖ - r ≤ ‖x‖ ∧ ‖x‖ ≤ ‖z‖ + r := by
  rw [mem_sphere_iff_norm, abs_of_pos hr] at hx
  constructor
  · have h := norm_sub_norm_le z x
    rw [norm_sub_rev] at h
    linarith
  · have h := norm_add_le (x - z) z
    rw [sub_add_cancel, hx] at h
    linarith

/-- On a region circle `-log|x| ≥ 0`. -/
lemma neg_log_nonneg_of_mem_sphere {r : ℝ} {z x : ℂ} (hreg : InLevelRegion r z) (hx : x ∈ sphere z |r|) :
    0 ≤ -Real.log ‖x‖ := by
  obtain ⟨hr, -, hz1⟩ := hreg
  have h := (region_norm_bounds hr hx).2
  have h1 : ‖x‖ ≤ 1 := by linarith [norm_nonneg z]
  exact neg_nonneg.2 (Real.log_nonpos (norm_nonneg _) h1)

/-- Continuity in the radial index of the circle average of `min(max u 0, -log|y|)`. -/
lemma continuous_circleAverage_min_max {r : ℝ} (hr : 0 < r) {z : ℂ} (hzr : r < ‖z‖) :
    Continuous fun u : ℝ => Real.circleAverage (fun y => min (max u 0) (-Real.log ‖y‖)) z r := by
  have hc := continuous_neg_log_circleMap hr z hzr
  have hf : Continuous (Function.uncurry fun (u : ℝ) (θ : ℝ) =>
      min (max u 0) (-Real.log ‖circleMap z r θ‖)) :=
    (continuous_fst.max continuous_const).min (hc.comp continuous_snd)
  unfold Real.circleAverage
  exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := (volume : Measure ℝ)) hf 0 (2 * π)).const_smul ((2 * π)⁻¹ : ℝ)

omit [IsProbabilityMeasure P] in
/-- Covariances of the radial process: `Cov(W_u, W_v) = min(max u 0, max v 0)` for all real `u, v`. -/
lemma cov_radial_level (hW : IsRadialLevelData P W M₀) (u v : ℝ) :
    covariance (W u) (W v) P = min (max u 0) (max v 0) := by
  have hu : W u = W (max u 0) := by
    rcases le_total u 0 with h | h
    · rw [hW.const_nonpos u h, max_eq_right h, hW.const_nonpos 0 le_rfl]
    · rw [max_eq_left h]
  have hv : W v = W (max v 0) := by
    rcases le_total v 0 with h | h
    · rw [hW.const_nonpos v h, max_eq_right h, hW.const_nonpos 0 le_rfl]
    · rw [max_eq_left h]
  rw [hu, hv, hW.cov _ _ (le_max_right _ _) (le_max_right _ _)]

/-- **The covariance of two region circle averages of the radial process** (joint Gaussian representation). -/
theorem radial_avg_cov_pair (hW : IsRadialLevelData P W M₀) (hM₀ : IsCentredGaussianSpace P M₀)
    {r r' : ℝ} {z z' : ℂ} (hreg : InLevelRegion r z) (hreg' : InLevelRegion r' z') :
    ∃ Y Y' : Ω → ℝ, Measurable Y ∧ Measurable Y' ∧
      (∀ᵐ ω ∂P, Real.circleAverage (fun x => W (-Real.log ‖x‖) ω) z r = Y ω) ∧
      (∀ᵐ ω ∂P, Real.circleAverage (fun x => W (-Real.log ‖x‖) ω) z' r' = Y' ω) ∧
      ∃ M : Submodule ℝ (Ω → ℝ), IsCentredGaussianSpace P M ∧ M₀ ≤ M ∧ Y ∈ M ∧ Y' ∈ M ∧
        covariance Y Y' P = Real.circleAverage
          (fun x => Real.circleAverage (fun y => min (-Real.log ‖x‖) (-Real.log ‖y‖)) z' r') z r := by
  obtain ⟨hr, hzr, hz1⟩ := hreg
  obtain ⟨hr', hzr', hz1'⟩ := hreg'
  have hreg : InLevelRegion r z := ⟨hr, hzr, hz1⟩
  have hreg' : InLevelRegion r' z' := ⟨hr', hzr', hz1'⟩
  obtain ⟨T, Y, hTm, hTlim, hYm, hconv, havg, hform⟩ := radial_level_rep hW hM₀ ⟨hr, hzr, hz1⟩
  obtain ⟨T', Y', hTm', hTlim', hYm', hconv', havg', hform'⟩ := radial_level_rep hW hM₀ ⟨hr', hzr', hz1'⟩
  -- the joint Gaussian space
  have hM1 := isCentredGaussianSpace_sup_span_range hM₀ T hTm hTlim
  have hmemT : ∀ k, T k ∈ (M₀ ⊔ Submodule.span ℝ (Set.range T) : Submodule ℝ (Ω → ℝ)) :=
    fun k => Submodule.mem_sup_right (Submodule.subset_span ⟨k, rfl⟩)
  have hM2 := isCentredGaussianSpace_sup_span hM1 hYm ⟨T, hmemT, hconv⟩
  have hle1 : M₀ ≤ (M₀ ⊔ Submodule.span ℝ (Set.range T) : Submodule ℝ (Ω → ℝ)) := le_sup_left
  have hle2 : (M₀ ⊔ Submodule.span ℝ (Set.range T) : Submodule ℝ (Ω → ℝ)) ≤
      (M₀ ⊔ Submodule.span ℝ (Set.range T) ⊔ Submodule.span ℝ {Y} : Submodule ℝ (Ω → ℝ)) := le_sup_left
  have hM2le : M₀ ≤ (M₀ ⊔ Submodule.span ℝ (Set.range T) ⊔ Submodule.span ℝ {Y} : Submodule ℝ (Ω → ℝ)) :=
    hle1.trans hle2
  have hT'lim : ∀ k, IsAeLimitOf P (M₀ ⊔ Submodule.span ℝ (Set.range T) ⊔ Submodule.span ℝ {Y} :
      Submodule ℝ (Ω → ℝ)) (T' k) :=
    fun k => (hTlim' k).mono (SetLike.coe_subset_coe.2 hM2le)
  have hM3 := isCentredGaussianSpace_sup_span_range
    hM2 T' hTm' hT'lim
  have hmemT' : ∀ k, T' k ∈ (M₀ ⊔ Submodule.span ℝ (Set.range T) ⊔ Submodule.span ℝ {Y} ⊔
      Submodule.span ℝ (Set.range T') : Submodule ℝ (Ω → ℝ)) :=
    fun k => Submodule.mem_sup_right (Submodule.subset_span ⟨k, rfl⟩)
  have hM4 := isCentredGaussianSpace_sup_span hM3 hYm' ⟨T', hmemT', hconv'⟩
  set M : Submodule ℝ (Ω → ℝ) := M₀ ⊔ Submodule.span ℝ (Set.range T) ⊔ Submodule.span ℝ {Y} ⊔
    Submodule.span ℝ (Set.range T') ⊔ Submodule.span ℝ {Y'} with hMdef
  have hMle : M₀ ≤ M := (hM2le.trans le_sup_left).trans le_sup_left
  have hYmem : Y ∈ M := Submodule.mem_sup_left (Submodule.mem_sup_left
    (Submodule.mem_sup_right (Submodule.mem_span_singleton_self Y)))
  have hY'mem : Y' ∈ M := Submodule.mem_sup_right (Submodule.mem_span_singleton_self Y')
  have hTmem' : ∀ k, T' k ∈ M := fun k => Submodule.mem_sup_left (Submodule.mem_sup_right
    (Submodule.subset_span ⟨k, rfl⟩))
  have hTmem : ∀ k, T k ∈ M := fun k => Submodule.mem_sup_left (Submodule.mem_sup_left
    (Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.subset_span ⟨k, rfl⟩))))
  -- covariances of `W u` with the second circle average
  have hF' : ∀ u : ℝ, covariance (W u) Y' P =
      Real.circleAverage (fun y => min (max u 0) (-Real.log ‖y‖)) z' r' := by
    intro u
    have key := hform' M hM4 hMle hTmem' hY'mem (W u) (hMle (hW.mem u))
      (by
        simp only [cov_radial_level hW]
        exact continuous_const.min (continuous_id.max continuous_const))
      (by
        simp only [cov_radial_level hW]
        have hc : Continuous fun x : ℝ => min (max u 0) (max (-Real.log ‖circleMap z' r' x‖) 0) :=
          continuous_const.min ((continuous_neg_log_circleMap hr' z' hzr').max continuous_const)
        exact ((hc.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self).const_mul _)
    rw [key, ← circleAverage_neg_log_eq_levelIntegral (fun v => covariance (W u) (W v) P) hr' z' hzr']
    refine Real.circleAverage_congr_sphere (fun x hx => ?_)
    simp only [cov_radial_level hW]
    rw [max_eq_left (neg_log_nonneg_of_mem_sphere hreg' hx)]
  -- the covariance of the two circle averages
  have hcovY : covariance Y' Y P = Real.circleAverage
      (fun x => Real.circleAverage (fun y => min (-Real.log ‖x‖) (-Real.log ‖y‖)) z' r') z r := by
    have hfun : ∀ u : ℝ, covariance Y' (W u) P =
        Real.circleAverage (fun y => min (max u 0) (-Real.log ‖y‖)) z' r' := fun u => by
      rw [covariance_comm _ _, hF' u]
    have hcontu : Continuous fun u : ℝ => covariance Y' (W u) P := by
      simp only [hfun]
      exact continuous_circleAverage_min_max hr' hzr'
    have hintx : Integrable (fun x : ℝ => (2 * π)⁻¹ * covariance Y' (W (-Real.log ‖circleMap z r x‖)) P)
        (volume.restrict (Ioc (0 : ℝ) (2 * π))) := by
      simp only [hfun]
      have hc : Continuous fun x : ℝ => Real.circleAverage
          (fun y => min (max (-Real.log ‖circleMap z r x‖) 0) (-Real.log ‖y‖)) z' r' :=
        (continuous_circleAverage_min_max hr' hzr').comp (continuous_neg_log_circleMap hr z hzr)
      exact ((continuous_const.mul hc).continuousOn.integrableOn_compact isCompact_Icc).mono_set
        Ioc_subset_Icc_self
    rw [hform M hM4 hMle hTmem hYmem Y' hY'mem hcontu hintx]
    rw [← circleAverage_neg_log_eq_levelIntegral (fun u => covariance Y' (W u) P) hr z hzr]
    refine Real.circleAverage_congr_sphere (fun x hx => ?_)
    simp only [hfun]
    rw [max_eq_left (neg_log_nonneg_of_mem_sphere hreg hx)]
  refine ⟨Y, Y', hYm, hYm', havg, havg', M, hM4, hMle, hYmem, hY'mem, ?_⟩
  rw [covariance_comm _ _]
  exact hcovY

end Pair

end MatedCRT.Field
