import MatedCRT.Proofs.Sec2.ConeFamilyMeasurable.RescaledFamily
import MatedCRT.Proofs.Sec1.ConeScaleRadius
import HarmonicBalls.Proofs.Sec6.MeasurePushforwardJoint

/-! # Measurability of randomly rescaled LQG measures -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal

/-- A measurable random dilation of a locally finite random measure is
measurable, including its constant mass rescaling. -/
theorem aemeasurable_rescaledMeasure
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {μ : Ω → Measure ℂ} {R : Ω → ℝ}
    (hμ : AEMeasurable μ P) (hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω))
    (hR : AEMeasurable R P) (b : ℝ) :
    AEMeasurable (fun ω => rescaledMeasure (μ ω) (R ω) b) P := by
  obtain ⟨ν, hν, hνloc, hνeq⟩ := Section6.exists_measurable_locallyFinite_rep hμ hloc
  let R' := hR.mk R
  have hf : Measurable (fun p : Ω × ℂ => ((R' p.1)⁻¹ : ℂ) * p.2) :=
    (measurable_inv.comp (Complex.measurable_ofReal.comp (hR.measurable_mk.comp measurable_fst))).mul measurable_snd
  have hmap : Measurable (fun ω => (ν ω).map (fun z => ((R' ω)⁻¹ : ℂ) * z)) :=
    Section6.measurable_map_of_locallyFinite hν hνloc hf
  have hsmul : Measurable (fun ω => ENNReal.ofReal b⁻¹ •
      (ν ω).map (fun z => ((R' ω)⁻¹ : ℂ) * z)) := by
    apply Measure.measurable_of_measurable_coe
    intro U hU
    simpa only [Measure.smul_apply, smul_eq_mul, Function.comp_apply] using
      ((Measure.measurable_coe hU).comp hmap).const_mul (ENNReal.ofReal b⁻¹)
  refine hsmul.aemeasurable.congr ?_
  filter_upwards [hνeq, hR.ae_eq_mk] with ω hνω hRω
  simp only [rescaledMeasure, R', ← hνω, ← hRω]

/-- The rescaled cone measure is measurable whenever the scale radius is
almost surely positive. -/
theorem IsConeField.aemeasurable_rescaledMeasure
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hcone : IsConeField γ P hC hcirc μ) (b : ℝ)
    (hR : ∀ᵐ ω ∂P, 0 < coneScaleRadius γ (hcirc ω) b) :
    AEMeasurable (fun ω => rescaledMeasure (μ ω) (coneScaleRadius γ (hcirc ω) b) b) P :=
  MatedCRT.aemeasurable_rescaledMeasure hcone.aemeasurable_lqgMeasure
    (hcone.2.2.mono fun _ h => h.isLocallyFiniteMeasure)
    (Sec1.aemeasurable_coneScaleRadius hcone.2.1 hR) b

end MatedCRT
