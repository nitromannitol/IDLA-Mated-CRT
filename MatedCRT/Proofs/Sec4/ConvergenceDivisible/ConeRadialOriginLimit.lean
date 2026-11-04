import MatedCRT.Proofs.Sec4.ConvergenceDivisible.PositiveConeScaleRadius

/-! # Radial asymptotics of a quantum cone at the origin -/

namespace MatedCRT

open Filter Set MeasureTheory HarmonicBalls MarkovProcess Topology
open scoped NNReal

/-- The centered inward radial process is sublinear at all real logarithmic times. -/
theorem IsQuantumCone.ae_radial_sublinear
    {Ω : Type} [MeasurableSpace Ω] {γ : ℝ} {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hcone : IsQuantumCone γ P hC hcirc) :
    ∀ᵐ ω ∂P, Tendsto (fun t : ℝ =>
      (hcirc ω (Real.exp (-t)) 0 - γ * t) / t) atTop (𝓝 0) := by
  have hB (a : ℝ) (ha : 0 < a) : ∀ᵐ w ∂brownianMotion 0,
      ∀ᶠ n : ℕ in atTop, ∀ t : ℝ≥0,
        (n : ℝ≥0) ≤ t → t ≤ (n : ℝ≥0) + 1 →
        |w t - w (n : ℝ≥0)| ≤ a * n :=
    brownian_oscillation_of_identDistrib_bound unitOscillationMax
      brownian_unit_max_integrable unitOscillationMax_nonneg
      unitOscillationMax_identDistrib le_unitOscillationMax ha
  have hk : ∀ k : ℕ, ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, ∀ t : ℝ≥0,
      (n : ℝ≥0) ≤ t → t ≤ (n : ℝ≥0) + 1 →
      |(hcirc ω (Real.exp (-(t : ℝ))) 0 - γ * t) -
        (hcirc ω (Real.exp (-(n : ℝ))) 0 - γ * n)| ≤
          (1 / ((k : ℝ) + 1)) * n := by
    intro k
    exact hcone.ae_radial_oscillation_of_brownian (hB _ (by positivity))
  filter_upwards [hcone.ae_radial_integer_sublinear, ae_all_iff.mpr hk] with ω hi ho
  apply tendsto_div_atTop_of_integer_and_oscillation hi
  intro ε hε
  obtain ⟨k, hkε⟩ := exists_nat_one_div_lt hε
  filter_upwards [ho k] with n hn t hnt htn
  have ht0 : 0 ≤ t := le_trans (Nat.cast_nonneg n) hnt
  let u : ℝ≥0 := ⟨t, ht0⟩
  have hun : (n : ℝ≥0) ≤ u := by exact_mod_cast hnt
  have hnu : u ≤ (n : ℝ≥0) + 1 := by exact_mod_cast htn
  exact (hn u hun hnu).trans (mul_le_mul_of_nonneg_right hkε.le (Nat.cast_nonneg n))

/-- The radial expression defining the cone scale radius tends to minus
infinity at the origin. -/
theorem IsQuantumCone.ae_radial_expression_tendsto_origin
    {Ω : Type} [MeasurableSpace Ω] {γ : ℝ} {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hcone : IsQuantumCone γ P hC hcirc) :
    ∀ᵐ ω ∂P, Tendsto (fun r : ℝ => hcirc ω r 0 + lqgQ γ * Real.log r)
      (𝓝[>] (0 : ℝ)) atBot := by
  have hq : 0 < lqgQ γ - γ := by
    have hid : lqgQ γ - γ = ((2 - γ) * (2 + γ)) / (2 * γ) := by
      unfold lqgQ
      field_simp
      ring
    rw [hid]
    positivity
  filter_upwards [hcone.ae_radial_sublinear] with ω hω
  apply radial_tendsto_atBot_of_log_time
  have ht := tendsto_atBot_of_sublinear_drift hq hω
  convert ht using 1
  ext t
  ring

/-- The event-measurability step follows from cone rescaling and the outward
radial limit; positivity of cone scale radii then follows pathwise. -/
theorem convergenceDivisibleEventMeasurable_of_outward_radial_limit
    (𝒮 : SpaceFillingSLEModel) (h27 : VolumeGrowthStmt)
    (hscale : ConeEnvironmentScalingStep 𝒮)
    (hout : ∀ (γ : ℝ), 0 < γ → γ < 2 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ᵐ ω ∂S.P, Tendsto (fun r : ℝ =>
        S.hcirc ω r 0 + lqgQ γ * Real.log r) atTop atTop) :
    ConvergenceDivisibleEventMeasurableStep 𝒮 := by
  apply convergenceDivisibleEventMeasurable_of_coneScaling 𝒮 h27 hscale
  intro γ hγ hγ2 Ω _ S hS R hR
  filter_upwards [hS.isQuantumCone.ae_radial_expression_tendsto_origin hγ hγ2,
    hout γ hγ hγ2 Ω S hS, hS.isQuantumCone.ae_continuousOn_circle] with ω hzero hinf hc
  have hcircle : ContinuousOn (fun r : ℝ => S.hcirc ω r 0) (Ioi 0) :=
    hc.comp (continuous_id.prodMk continuous_const).continuousOn (fun r hr => ⟨hr, mem_univ _⟩)
  have hlog : ContinuousOn Real.log (Ioi 0) :=
    Real.continuousOn_log.mono (fun _ hr => ne_of_gt hr)
  have hcont : ContinuousOn (fun r : ℝ => S.hcirc ω r 0 + lqgQ γ * Real.log r) (Ioi 0) :=
    hcircle.add (continuousOn_const.mul hlog)
  have hlocal : ∀ M : ℝ, 0 < M →
      BddAbove ((fun r => S.hcirc ω r 0 + lqgQ γ * Real.log r) '' Ioc 0 M) :=
    fun M _ => bddAbove_image_Ioc_of_tendsto_atBot hcont hzero
  have hpos : ∀ n : ℕ, 0 < coneScaleRadius γ (S.hcirc ω) ((n : ℝ) + 1) :=
    fun _ => coneScaleRadius_pos_of_radial_limits hcont hzero hinf
  have ht := coneScaleRadius_tendsto_of_radial_bound hγ (S.hcirc ω) hlocal hpos
  obtain ⟨n, hn⟩ := ((tendsto_atTop.1 ht) (2 * R + 1)).exists
  exact ⟨n, by linarith⟩

end MatedCRT
