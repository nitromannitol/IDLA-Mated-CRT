import MatedCRT.Proofs.Sec4.ConvergenceDivisible.RescaledVolumeGrowth
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.VolumeGrowthInsideUnit
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.FromInputs

/-! # Growth on large balls from cone rescaling -/

namespace MatedCRT

open MeasureTheory Filter Metric Set HarmonicBalls

/-- If the cone scale radii at positive integer masses are almost surely
unbounded, the unit-ball estimate transfers to every fixed ball. -/
theorem MatedCRTEnv.IsValid.ae_volumeGrowth_of_coneScaling
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    (h27 : VolumeGrowthStmt) (hscale : ConeEnvironmentScalingStep 𝒮)
    {R : ℝ} (hR : 0 < R)
    (hlarge : ∀ᵐ ω ∂S.P, ∃ n : ℕ,
      2 * R < coneScaleRadius γ (S.hcirc ω) ((n : ℝ) + 1)) :
    ∀ᵐ ω ∂S.P, ∃ βminus βplus, VolumeGrowth (S.μ ω) R βminus βplus := by
  classical
  let S' : ℕ → MatedCRTEnv Ω := fun n =>
    Classical.choose (hscale γ hγ hγ2 Ω S hS ((n : ℝ) + 1) (by positivity))
  have hspec (n : ℕ) :=
    Classical.choose_spec (hscale γ hγ hγ2 Ω S hS ((n : ℝ) + 1) (by positivity))
  have hlocal (n : ℕ) : ∀ᵐ ω ∂S.P, ∃ βm βp,
      VolumeGrowth (rescaledMeasure (S.μ ω)
        (coneScaleRadius γ (S.hcirc ω) ((n : ℝ) + 1)) ((n : ℝ) + 1))
        (1 / 2) βm βp := by
    have hv := (hspec n).1.ae_volumeGrowth_inside_unit hγ hγ2 h27
      (R := (1 / 2 : ℝ)) (by norm_num)
    change ∀ᵐ ω ∂(S' n).P, _ at hv
    rw [(hspec n).2.1] at hv
    filter_upwards [hv, (hspec n).2.2.2.2] with ω hω heq
    simpa [heq] using hω
  filter_upwards [ae_all_iff.mpr hlocal, hlarge] with ω hω hlargeω
  obtain ⟨n, hn⟩ := hlargeω
  obtain ⟨βm, βp, hv⟩ := hω n
  have hs : 0 < coneScaleRadius γ (S.hcirc ω) ((n : ℝ) + 1) := by linarith
  refine ⟨βm + 1, βp / 2, (volumeGrowth_of_rescaledMeasure hs (by positivity) hv).mono ?_⟩
  linarith

/-- Convergence-event measurability follows from cone rescaling, the local
ball-mass estimate and almost-sure exhaustion by cone scale radii. -/
theorem convergenceDivisibleEventMeasurable_of_coneScaling
    (𝒮 : SpaceFillingSLEModel) (h27 : VolumeGrowthStmt)
    (hscale : ConeEnvironmentScalingStep 𝒮)
    (hlarge : ∀ (γ : ℝ), 0 < γ → γ < 2 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ R : ℝ, 0 < R → ∀ᵐ ω ∂S.P, ∃ n : ℕ,
        2 * R < coneScaleRadius γ (S.hcirc ω) ((n : ℝ) + 1)) :
    ConvergenceDivisibleEventMeasurableStep 𝒮 := by
  apply convergenceDivisibleEventMeasurable_of_volumeGrowth_inputs 𝒮
  intro γ hγ hγ2 Ω _ S hS R hR
  exact hS.ae_volumeGrowth_of_coneScaling hγ hγ2 h27 hscale hR
    (hlarge γ hγ hγ2 Ω S hS R hR)

end MatedCRT
