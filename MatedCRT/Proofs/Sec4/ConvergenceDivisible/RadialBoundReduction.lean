import MatedCRT.Proofs.Sec4.ConvergenceDivisible.ConeScaleExhaustion

/-! # Radial conditions for cone-scale exhaustion -/

namespace MatedCRT

open Filter Set MeasureTheory HarmonicBalls Topology

/-- A continuous radial function which tends to minus infinity at the origin
is bounded above on each bounded positive interval. -/
theorem bddAbove_image_Ioc_of_tendsto_atBot
    {f : ℝ → ℝ} (hf : ContinuousOn f (Ioi 0))
    (hzero : Tendsto f (𝓝[>] (0 : ℝ)) atBot) {M : ℝ} :
    BddAbove (f '' Ioc 0 M) := by
  obtain ⟨δ, hδ, hδbound⟩ := exists_pos_of_eventually_nhdsGT ((tendsto_atBot.1 hzero) 0)
  have hc : ContinuousOn f (Icc δ M) := hf.mono fun x hx => lt_of_lt_of_le hδ hx.1
  obtain ⟨C, hC⟩ := IsCompact.bddAbove_image isCompact_Icc hc
  refine ⟨max C 0, ?_⟩
  rintro y ⟨r, ⟨hr0, hrM⟩, rfl⟩
  by_cases hrδ : r < δ
  · exact (hδbound r hr0 hrδ).trans (le_max_right C 0)
  · exact (hC ⟨r, ⟨le_of_not_gt hrδ, hrM⟩, rfl⟩).trans (le_max_left C 0)

/-- The event-measurability step follows from cone scaling, positivity of
the cone scale radii, and almost-sure boundedness above of the radial cone
expression on bounded intervals. -/
theorem convergenceDivisibleEventMeasurable_of_radial_bound
    (𝒮 : SpaceFillingSLEModel) (h27 : VolumeGrowthStmt)
    (hscale : ConeEnvironmentScalingStep 𝒮) (hpos : ConeScaleRadiusStep)
    (hbound : ∀ (γ : ℝ), 0 < γ → γ < 2 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ᵐ ω ∂S.P, ∀ M : ℝ, 0 < M →
        BddAbove ((fun r => S.hcirc ω r 0 + lqgQ γ * Real.log r) '' Ioc 0 M)) :
    ConvergenceDivisibleEventMeasurableStep 𝒮 := by
  apply convergenceDivisibleEventMeasurable_of_coneScaling 𝒮 h27 hscale
  intro γ hγ hγ2 Ω _ S hS R hR
  have hpositive (n : ℕ) : ∀ᵐ ω ∂S.P,
      0 < coneScaleRadius γ (S.hcirc ω) ((n : ℝ) + 1) :=
    (hpos γ hγ hγ2 Ω S.P S.hC S.hcirc S.μ hS.isConeField _ (by positivity)).2
  filter_upwards [hbound γ hγ hγ2 Ω S hS, ae_all_iff.mpr hpositive] with ω hb hp
  have ht := coneScaleRadius_tendsto_of_radial_bound hγ (S.hcirc ω) hb hp
  obtain ⟨n, hn⟩ := ((tendsto_atTop.1 ht) (2 * R + 1)).exists
  exact ⟨n, by linarith⟩

end MatedCRT
