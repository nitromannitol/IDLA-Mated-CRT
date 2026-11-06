import MatedCRT.Proofs.Sec4.ConvergenceDivisible.LQGMassMeasurable

/-! Measurability of integrals against the random LQG measure. -/

namespace MatedCRT

open MeasureTheory Filter

/-- A signed deterministic Borel function has an almost everywhere measurable
LQG integral when it is integrable almost surely. -/
theorem MatedCRTEnv.IsValid.aemeasurable_lqg_integral_of_ae_integrable
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (f : ℂ → ℝ) (hf : Measurable f)
    (hi : ∀ᵐ ω ∂S.P, Integrable f (S.μ ω)) :
    AEMeasurable (fun ω => ∫ x, f x ∂(S.μ ω)) S.P := by
  have hp := (hS.aemeasurable_lqg_lintegral (fun x => ENNReal.ofReal (f x))
    hf.ennreal_ofReal).ennreal_toReal
  have hn := (hS.aemeasurable_lqg_lintegral (fun x => ENNReal.ofReal (-f x))
    hf.neg.ennreal_ofReal).ennreal_toReal
  apply (hp.sub hn).congr
  filter_upwards [hi] with ω hω
  exact (integral_eq_lintegral_pos_part_sub_lintegral_neg_part hω).symm

end MatedCRT
