import MatedCRT.Proofs.Sec4.ConvergenceDivisible.ConeRadialOriginLimit
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.MaximumPrinciple

/-! # Positivity of cone scales from rescaled volume growth -/

namespace MatedCRT

open Filter Set MeasureTheory HarmonicBalls Metric Topology
open scoped ENNReal

/-- A measure rescaled by zero cannot satisfy volume growth on a nontrivial ball. -/
theorem not_volumeGrowth_rescaledMeasure_zero (μ : Measure ℂ) (b βm βp : ℝ) :
    ¬ VolumeGrowth (rescaledMeasure μ 0 b) (1 / 2) βm βp := by
  rintro ⟨_, _, r₀, hr₀, hV⟩
  let z : ℂ := (1 / 4 : ℝ)
  let r : ℝ := min (r₀ / 2) (1 / 8)
  have hr : 0 < r := by dsimp [r]; positivity
  have hrr : r < r₀ := by dsimp [r]; linarith [min_le_left (r₀ / 2) (1 / 8 : ℝ)]
  have hrz : r ≤ 1 / 8 := min_le_right _ _
  have hz : z ∈ ball (0 : ℂ) (1 / 2) := by
    norm_num [z, mem_ball, dist_eq_norm, Complex.norm_real]
  have hz0 : (0 : ℂ) ∉ ball z r := by
    simp only [mem_ball, dist_eq_norm, zero_sub, norm_neg]
    have : ‖z‖ = (1 / 4 : ℝ) := by norm_num [z, Complex.norm_real]
    linarith
  have hzero : rescaledMeasure μ 0 b (ball z r) = 0 := by
    unfold rescaledMeasure
    rw [Measure.smul_apply, Measure.map_apply (by fun_prop) measurableSet_ball]
    simp [hz0]
  have hbound := (hV r hr hrr z hz).1
  rw [hzero] at hbound
  have hpositive : 0 < ENNReal.ofReal (r ^ βm) :=
    ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hr _)
  exact (not_lt_of_ge hbound) hpositive

/-- Cone rescaling and volume growth force each cone scale radius to be
strictly positive, without an independent scale-radius assumption. -/
theorem MatedCRTEnv.IsValid.ae_coneScaleRadius_pos_of_scaling
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    (h27 : VolumeGrowthStmt) (hscale : ConeEnvironmentScalingStep 𝒮)
    {b : ℝ} (hb : 0 < b) :
    ∀ᵐ ω ∂S.P, 0 < coneScaleRadius γ (S.hcirc ω) b := by
  obtain ⟨S', hvalid, hP, _, _, hmeasure⟩ := hscale γ hγ hγ2 Ω S hS b hb
  have hlocal := hvalid.ae_volumeGrowth_inside_unit hγ hγ2 h27
    (R := (1 / 2 : ℝ)) (by norm_num)
  rw [hP] at hlocal
  filter_upwards [hlocal, hmeasure] with ω ⟨βm, βp, hv⟩ heq
  have hnonneg : 0 ≤ coneScaleRadius γ (S.hcirc ω) b := by
    apply Real.sSup_nonneg
    intro r hr
    exact hr.1.le
  have hne : coneScaleRadius γ (S.hcirc ω) b ≠ 0 := by
    intro hz
    apply not_volumeGrowth_rescaledMeasure_zero (S.μ ω) b βm βp
    simpa [heq, hz] using hv
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

/-- Cone scale radii at integer masses almost surely exhaust the plane. -/
theorem MatedCRTEnv.IsValid.ae_coneScaleRadius_exhaustion_of_scaling
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    (h27 : VolumeGrowthStmt) (hscale : ConeEnvironmentScalingStep 𝒮)
    (R : ℝ) : ∀ᵐ ω ∂S.P, ∃ n : ℕ,
      2 * R < coneScaleRadius γ (S.hcirc ω) ((n : ℝ) + 1) := by
  have hpositive (n : ℕ) : ∀ᵐ ω ∂S.P,
      0 < coneScaleRadius γ (S.hcirc ω) ((n : ℝ) + 1) :=
    hS.ae_coneScaleRadius_pos_of_scaling hγ hγ2 h27 hscale (by positivity)
  filter_upwards [hS.isQuantumCone.ae_radial_expression_tendsto_origin hγ hγ2,
    hS.isQuantumCone.ae_continuousOn_circle, ae_all_iff.mpr hpositive] with ω hzero hc hpos
  have hcircle : ContinuousOn (fun r : ℝ => S.hcirc ω r 0) (Ioi 0) :=
    hc.comp (continuous_id.prodMk continuous_const).continuousOn (fun r hr => ⟨hr, mem_univ _⟩)
  have hlog : ContinuousOn Real.log (Ioi 0) :=
    Real.continuousOn_log.mono (fun _ hr => ne_of_gt hr)
  have hcont : ContinuousOn (fun r : ℝ => S.hcirc ω r 0 + lqgQ γ * Real.log r) (Ioi 0) :=
    hcircle.add (continuousOn_const.mul hlog)
  have hlocal : ∀ M : ℝ, 0 < M →
      BddAbove ((fun r => S.hcirc ω r 0 + lqgQ γ * Real.log r) '' Ioc 0 M) :=
    fun M _ => bddAbove_image_Ioc_of_tendsto_atBot hcont hzero
  have ht := coneScaleRadius_tendsto_of_radial_bound hγ (S.hcirc ω) hlocal hpos
  obtain ⟨n, hn⟩ := ((tendsto_atTop.1 ht) (2 * R + 1)).exists
  exact ⟨n, by linarith⟩

/-- Local volume growth and cone scaling imply volume growth on any fixed ball. -/
theorem MatedCRTEnv.IsValid.ae_volumeGrowth_of_scaling
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    (h27 : VolumeGrowthStmt) (hscale : ConeEnvironmentScalingStep 𝒮)
    {R : ℝ} (hR : 0 < R) :
    ∀ᵐ ω ∂S.P, ∃ βminus βplus, VolumeGrowth (S.μ ω) R βminus βplus :=
  hS.ae_volumeGrowth_of_coneScaling hγ hγ2 h27 hscale hR
    (hS.ae_coneScaleRadius_exhaustion_of_scaling hγ hγ2 h27 hscale R)

/-- Cone scaling and volume growth imply the event-measurability step. -/
theorem convergenceDivisibleEventMeasurable_of_scaling
    (𝒮 : SpaceFillingSLEModel) (h27 : VolumeGrowthStmt)
    (hscale : ConeEnvironmentScalingStep 𝒮) :
    ConvergenceDivisibleEventMeasurableStep 𝒮 := by
  apply convergenceDivisibleEventMeasurable_of_volumeGrowth_inputs 𝒮
  intro γ hγ hγ2 Ω _ S hS R hR
  exact hS.ae_volumeGrowth_of_scaling hγ hγ2 h27 hscale hR

/-- Theorem 4.1 follows from subsequential convergence, volume growth,
and cone environment scaling. -/
theorem convergenceDivisible_of_scaling
    (𝒮 : SpaceFillingSLEModel) (h48 : SubsequentialPropertiesStmt 𝒮)
    (h46 : SubsequentialConvergenceStmt 𝒮) (h27 : VolumeGrowthStmt)
    (hscale : ConeEnvironmentScalingStep 𝒮) : ConvergenceDivisibleStmt 𝒮 :=
  convergenceDivisible_of_steps 𝒮 h48 h46 (obstacleLimitUniqueness 𝒮)
    (convergenceDivisibleEventMeasurable_of_scaling 𝒮 h27 hscale)

end MatedCRT
