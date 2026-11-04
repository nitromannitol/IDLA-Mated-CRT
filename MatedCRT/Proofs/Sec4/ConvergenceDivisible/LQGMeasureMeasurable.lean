import MatedCRT.Defs.Setting
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.ContinuousFieldMeasurable
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Measurability of LQG measure against continuous test functions -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal

/-- For each positive radius, the circle-average field has a jointly
measurable version agreeing simultaneously at all spatial points. -/
theorem MatedCRTEnv.IsValid.exists_measurable_circleAverage
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (r : ℝ) (hr : 0 < r) :
    ∃ g : Ω × ℂ → ℝ, Measurable g ∧
      ∀ᵐ ω ∂S.P, ∀ z, g (ω, z) = S.hcirc ω r z := by
  apply exists_jointlyMeasurable_of_ae_continuous S.P (fun ω z => S.hcirc ω r z)
  · intro z
    exact (hS.isQuantumCone.measurable_circle r z hr).aemeasurable
  · filter_upwards [hS.isQuantumCone.ae_continuousOn_circle] with ω hω
    exact hω.comp_continuous (continuous_const.prodMk continuous_id)
      (fun z => ⟨hr, mem_univ z⟩)

/-- The integral against the LQG measure of a compactly supported continuous
function is an almost-everywhere measurable random variable. -/
theorem MatedCRTEnv.IsValid.aemeasurable_lqg_integral
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (f : ℂ → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f) :
    AEMeasurable (fun ω => ∫ z, f z ∂(S.μ ω)) S.P := by
  apply aemeasurable_of_tendsto_metrizable_ae atTop
    (f := fun k ω => ∫ z, f z ∂(lqgApprox γ (S.hcirc ω) (dyadicScale k)))
  · intro k
    obtain ⟨g, hg, hgae⟩ := hS.exists_measurable_circleAverage (dyadicScale k) (dyadicScale_pos k)
    let a : ℝ := (dyadicScale k) ^ (γ ^ 2 / 2)
    let F : Ω × ℂ → ℝ := fun p => a * Real.exp (γ * g p) * f p.2
    have hF : Measurable F := (measurable_const.mul
      ((measurable_const.mul hg).exp)).mul (hf.measurable.comp measurable_snd)
    have hI : Measurable (fun ω => ∫ z, F (ω, z)) :=
      hF.stronglyMeasurable.integral_prod_right'.measurable
    apply hI.aemeasurable.congr
    filter_upwards [hgae] with ω hω
    have hden : Measurable (fun z => ENNReal.ofReal (a * Real.exp (γ * g (ω, z)))) :=
      (measurable_const.mul
        ((measurable_const.mul (hg.comp (measurable_const.prodMk measurable_id))).exp)).ennreal_ofReal
    have htop : ∀ᵐ z : ℂ ∂volume, ENNReal.ofReal (a * Real.exp (γ * g (ω, z))) < ∞ :=
      Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
    have heq : lqgApprox γ (S.hcirc ω) (dyadicScale k) =
        volume.withDensity (fun z => ENNReal.ofReal (a * Real.exp (γ * g (ω, z)))) := by
      unfold lqgApprox
      apply congrArg (Measure.withDensity volume)
      funext z
      rw [hω z]
    rw [heq, integral_withDensity_eq_integral_toReal_smul hden htop]
    apply integral_congr_ae
    filter_upwards [] with z
    have ha : 0 ≤ a := Real.rpow_nonneg (dyadicScale_pos k).le _
    simp [F, ENNReal.toReal_ofReal (mul_nonneg ha (Real.exp_pos _).le), smul_eq_mul]
  · filter_upwards [hS.isLQGMeasure] with ω hω
    exact hω.tendsto_integral f hf hfc

end MatedCRT
