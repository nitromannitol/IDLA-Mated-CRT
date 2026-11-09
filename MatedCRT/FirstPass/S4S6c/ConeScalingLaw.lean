import MatedCRT.FirstPass.Frozen.S4S6c
import MatedCRT.FirstPass.S4S6c.VolumeGrowthSet
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.ConeRadialOriginLimit
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.MaximumPrinciple
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.RescaledVolumeGrowth
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.VolumeGrowthInsideUnit
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.FromInputs

/-!
# Cone scaling in law: the volume-growth chain of Theorem 4.1 (q2, task fp-S4S6c)

These are the repaired versions of `ConeScalingPositivity.lean` (`ae_coneScaleRadius_pos_of_scaling`,
`ae_coneScaleRadius_exhaustion_of_scaling`, `ae_volumeGrowth_of_scaling`, `convergenceDivisibleEventMeasurable_of_scaling`)
and of `VolumeGrowthFromConeScaling.lean` (`ae_volumeGrowth_of_coneScaling`). The environment-based hypothesis
`ConeEnvironmentScalingStep` (FALSE, truth check 2026-11-09) is replaced by `FrozenConeScalingLaw`, which gives only:
`R_b > 0` almost surely and the law identity `b⁻¹ μ(R_b ·) ~ μ`. The volume transfer is the law transfer
`ae_mem_of_law_map_eq` of the event `{ν | ∃ βm βp, VolumeGrowth ν (1/2) βm βp}` (measurable by
`measurableSet_volumeGrowth_exists`). The validity of the rescaled environment is not used.
-/

namespace MatedCRT

open MeasureTheory Filter Metric Set HarmonicBalls
open scoped ENNReal

/-- The cone scale radii are almost surely positive, read off the frozen cone-scaling law. -/
theorem MatedCRTEnv.IsValid.ae_coneScaleRadius_pos_of_scalingLaw
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    (hcone : FrozenConeScalingLaw 𝒮) {b : ℝ} (hb : 0 < b) :
    ∀ᵐ ω ∂S.P, 0 < coneScaleRadius γ (S.hcirc ω) b :=
  (hcone γ hγ hγ2 Ω S hS b hb).1

/-- Cone scale radii at integer masses almost surely exhaust the plane (positivity from the frozen law). -/
theorem MatedCRTEnv.IsValid.ae_coneScaleRadius_exhaustion_of_scalingLaw
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    (hcone : FrozenConeScalingLaw 𝒮) (R : ℝ) : ∀ᵐ ω ∂S.P, ∃ n : ℕ,
      2 * R < coneScaleRadius γ (S.hcirc ω) ((n : ℝ) + 1) := by
  have hpositive (n : ℕ) : ∀ᵐ ω ∂S.P,
      0 < coneScaleRadius γ (S.hcirc ω) ((n : ℝ) + 1) :=
    hS.ae_coneScaleRadius_pos_of_scalingLaw hγ hγ2 hcone (by positivity)
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

/-- Volume growth of the rescaled LQG measure on the unit disk, almost surely, by the law transfer from `μ`. -/
theorem MatedCRTEnv.IsValid.ae_rescaled_volumeGrowth_of_scalingLaw
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    (h27 : VolumeGrowthStmt) (hcone : FrozenConeScalingLaw 𝒮) {b : ℝ} (hb : 0 < b) :
    ∀ᵐ ω ∂S.P, ∃ βm βp, VolumeGrowth
      (rescaledMeasure (S.μ ω) (coneScaleRadius γ (S.hcirc ω) b) b) (1 / 2) βm βp := by
  obtain ⟨-, -, hμ, hF, hlaw⟩ := hcone γ hγ hγ2 Ω S hS b hb
  have hμv : ∀ᵐ ω ∂S.P, ∃ βm βp, VolumeGrowth (S.μ ω) (1 / 2) βm βp :=
    hS.ae_volumeGrowth_inside_unit hγ hγ2 h27 (by norm_num)
  exact ae_mem_of_law_map_eq hμ hF hlaw (measurableSet_volumeGrowth_exists (1 / 2)) hμv

/-- Volume growth on every fixed ball, from the unit-disk estimate of the rescaled measures (frozen cone-scaling law). -/
theorem MatedCRTEnv.IsValid.ae_volumeGrowth_of_scalingLaw
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    (h27 : VolumeGrowthStmt) (hcone : FrozenConeScalingLaw 𝒮)
    {R : ℝ} (hR : 0 < R) :
    ∀ᵐ ω ∂S.P, ∃ βminus βplus, VolumeGrowth (S.μ ω) R βminus βplus := by
  have hlocal (n : ℕ) : ∀ᵐ ω ∂S.P, ∃ βm βp,
      VolumeGrowth (rescaledMeasure (S.μ ω)
        (coneScaleRadius γ (S.hcirc ω) ((n : ℝ) + 1)) ((n : ℝ) + 1)) (1 / 2) βm βp :=
    hS.ae_rescaled_volumeGrowth_of_scalingLaw hγ hγ2 h27 hcone (by positivity)
  filter_upwards [ae_all_iff.mpr hlocal,
    hS.ae_coneScaleRadius_exhaustion_of_scalingLaw hγ hγ2 hcone R] with ω hω hlargeω
  obtain ⟨n, hn⟩ := hlargeω
  obtain ⟨βm, βp, hv⟩ := hω n
  have hs : 0 < coneScaleRadius γ (S.hcirc ω) ((n : ℝ) + 1) := by linarith
  refine ⟨βm + 1, βp / 2, (volumeGrowth_of_rescaledMeasure hs (by positivity) hv).mono ?_⟩
  linarith

/-- The event-measurability step of Theorem 4.1 from the frozen cone-scaling law. -/
theorem convergenceDivisibleEventMeasurable_of_scalingLaw
    (𝒮 : SpaceFillingSLEModel) (h27 : VolumeGrowthStmt) (hcone : FrozenConeScalingLaw 𝒮) :
    ConvergenceDivisibleEventMeasurableStep 𝒮 := by
  apply convergenceDivisibleEventMeasurable_of_volumeGrowth_inputs 𝒮
  intro γ hγ hγ2 Ω _ S hS R hR
  exact hS.ae_volumeGrowth_of_scalingLaw hγ hγ2 h27 hcone hR

end MatedCRT
