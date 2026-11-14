import MatedCRT.FirstPass.Derived.ConeDataLiftRescaled

/-!
# Joint scaling law for the environment curve and boundary lengths

The rescaled curve and boundary-length pair of a valid quantum cone environment have their
original joint law. The curve is viewed in the product measurable space of functions.
-/

set_option autoImplicit false

open MeasureTheory
open scoped NNReal

namespace MatedCRT

/-- The curve and boundary-length pair of a valid environment have a common joint scaling law. -/
theorem MatedCRTEnv.IsValid.map_rescaledCurve_boundaryPair {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ b : ℝ}
    (hS : S.IsValid 𝒮 γ) (hγ : 0 < γ) (hγ2 : γ < 2) (hb : 0 < b) :
    S.P.map (fun ω =>
      ((fun s => ((coneScaleRadius γ (S.hcirc ω) b : ℝ) : ℂ)⁻¹ * S.η ω (b * s)),
        rescaledPair b (S.bm ω))) = S.P.map (fun ω => (S.η ω, S.bm ω)) := by
  obtain ⟨V, V', hV, hC, hbm, htie, hV', hlaw, hae⟩ := hS.exists_coneDataLift hγ hγ2 hb
  have hid := hS.ae_coneDataLift_rescaled hγ hγ2 hb hV hC hbm htie hV' hlaw hae
  let f : MatedCRTHarmonic.MatedCRT.CouplingData → (ℝ → ℂ) × C(ℝ, ℝ × ℝ) :=
    fun v => (⇑v.η, v.bm)
  have hf : Measurable f := by
    refine (Measurable.of_eval fun t => ?_).prodMk
      MatedCRTHarmonic.MatedCRT.CouplingData.measurable_bm
    exact (continuous_eval_const t).measurable.comp
      MatedCRTHarmonic.MatedCRT.CouplingData.measurable_η
  have hmap := congrArg (fun μ => Measure.map f μ) hlaw
  rw [Measure.map_map hf hV', Measure.map_map hf hV] at hmap
  refine (Measure.map_congr ?_).trans (hmap.trans (Measure.map_congr ?_))
  · filter_upwards [hid] with ω hω
    exact Prod.ext hω.1.symm hω.2.1.symm
  · filter_upwards [htie] with ω hω
    exact Prod.ext hω.1 (hbm ω)

end MatedCRT
