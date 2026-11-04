import MatedCRT.Proofs.Sec4.ConvergenceDivisible.RadialBoundReduction

/-! # The radial drift condition at the origin -/

namespace MatedCRT

open Filter Set MeasureTheory HarmonicBalls Topology

/-- A sublinear perturbation of a strictly negative linear drift tends to
minus infinity. -/
theorem tendsto_atBot_of_sublinear_drift {B : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hB : Tendsto (fun t => B t / t) atTop (𝓝 0)) :
    Tendsto (fun t => B t - c * t) atTop atBot := by
  apply tendsto_atBot.2
  intro A
  have hsmall : ∀ᶠ t in atTop, B t / t < c / 2 :=
    hB.eventually (eventually_lt_nhds (by linarith : (0 : ℝ) < c / 2))
  filter_upwards [hsmall, eventually_ge_atTop (max 1 ((-A + 1) / (c / 2)))] with t ht hT
  have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hT)
  have hBt : B t < (c / 2) * t := (div_lt_iff₀ htpos).mp ht
  have htbig : (-A + 1) / (c / 2) ≤ t := (le_max_right _ _).trans hT
  have hc2 : 0 < c / 2 := by linarith
  have hlin : -A + 1 ≤ (c / 2) * t := by simpa [mul_comm] using (div_le_iff₀ hc2).mp htbig
  linarith

/-- Logarithmic time converts radial drift at infinity into the limit at
the origin for the circle-average embedding. -/
theorem radial_tendsto_atBot_of_log_time {γ : ℝ} {hcirc : ℝ → ℂ → ℝ}
    (htime : Tendsto (fun t : ℝ => hcirc (Real.exp (-t)) 0 - lqgQ γ * t) atTop atBot) :
    Tendsto (fun r : ℝ => hcirc r 0 + lqgQ γ * Real.log r) (𝓝[>] 0) atBot := by
  have hlog : Tendsto (fun r : ℝ => -Real.log r) (𝓝[>] 0) atTop :=
    tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  have h := htime.comp hlog
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  simp [Real.exp_log hr]

/-- The convergence-event step follows once the circle-average radial
expression has negative drift at the origin. -/
theorem convergenceDivisibleEventMeasurable_of_radial_drift
    (𝒮 : SpaceFillingSLEModel) (h27 : VolumeGrowthStmt)
    (hscale : ConeEnvironmentScalingStep 𝒮) (hpos : ConeScaleRadiusStep)
    (hdrift : ∀ (γ : ℝ), 0 < γ → γ < 2 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ᵐ ω ∂S.P, Tendsto (fun t : ℝ =>
        S.hcirc ω (Real.exp (-t)) 0 - lqgQ γ * t) atTop atBot) :
    ConvergenceDivisibleEventMeasurableStep 𝒮 := by
  apply convergenceDivisibleEventMeasurable_of_radial_bound 𝒮 h27 hscale hpos
  intro γ hγ hγ2 Ω _ S hS
  filter_upwards [hdrift γ hγ hγ2 Ω S hS, hS.isQuantumCone.ae_continuousOn_circle] with ω hd hc
  have hcircle : ContinuousOn (fun r : ℝ => S.hcirc ω r 0) (Ioi 0) :=
    hc.comp (continuous_id.prodMk continuous_const).continuousOn (fun r hr => ⟨hr, mem_univ _⟩)
  have hlog : ContinuousOn Real.log (Ioi 0) :=
    Real.continuousOn_log.mono (fun _ hr => ne_of_gt hr)
  have hcontinuous : ContinuousOn (fun r : ℝ => S.hcirc ω r 0 + lqgQ γ * Real.log r) (Ioi 0) :=
    hcircle.add (continuousOn_const.mul hlog)
  intro M _hM
  exact bddAbove_image_Ioc_of_tendsto_atBot hcontinuous (radial_tendsto_atBot_of_log_time hd)

/-- Sublinear growth of the Brownian part of the cone radial process gives
the negative drift needed for convergence-event measurability. -/
theorem convergenceDivisibleEventMeasurable_of_sublinear_radial
    (𝒮 : SpaceFillingSLEModel) (h27 : VolumeGrowthStmt)
    (hscale : ConeEnvironmentScalingStep 𝒮) (hpos : ConeScaleRadiusStep)
    (hsub : ∀ (γ : ℝ), 0 < γ → γ < 2 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ᵐ ω ∂S.P, Tendsto (fun t : ℝ =>
        (S.hcirc ω (Real.exp (-t)) 0 - γ * t) / t) atTop (𝓝 0)) :
    ConvergenceDivisibleEventMeasurableStep 𝒮 := by
  apply convergenceDivisibleEventMeasurable_of_radial_drift 𝒮 h27 hscale hpos
  intro γ hγ hγ2 Ω _ S hS
  have hq : 0 < lqgQ γ - γ := by
    have hid : lqgQ γ - γ = ((2 - γ) * (2 + γ)) / (2 * γ) := by
      unfold lqgQ
      field_simp
      ring
    rw [hid]
    positivity
  filter_upwards [hsub γ hγ hγ2 Ω S hS] with ω hω
  have ht := tendsto_atBot_of_sublinear_drift hq hω
  convert ht using 1
  ext t
  ring

end MatedCRT
