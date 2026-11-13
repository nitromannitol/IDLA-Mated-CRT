import MatedCRT.FirstPass.Derived.ConeDataLiftRescaled
import MatedCRT.Proofs.Sec1.EnvironmentScaling

/-!
# The rescaled mating-of-trees step from the rescaled lift

For a valid environment `S` and `b > 0`, `MatedCRTEnv.IsValid.exists_coneDataLift` gives coupling
data `V` tied to `S` and a measurable `V'` with the law of `V` whose triple `(h', η', β')` is almost
surely the rescaled triple `(h_b, R_b⁻¹ η(b ·), b^{-1/2} β(b ·))` of `V` (Duplantier-Miller-Sheffield,
Prop. 4.13(i)). This file records:

* `ae_coneRescale_of_coneTriple_eq`: the curve and the boundary-length pair of such a `V'` are almost
  surely the Brownian rescalings `coneRescaleCurve R b` and `brownRescale b` of those of `V`, with the
  positive scale `R = coneScaleOfPair γ b (B, B')` read off the radial paths of `V`; these are the
  pathwise hypotheses of the transfer of a mating-of-trees coupling through its law;
* `rescaledMatingOfTreesStep_of_lift`: `RescaledMatingOfTreesStep 𝒮` holds as soon as every such
  rescaled lift of coupling data is again coupling data. The almost sure identities of the lift with
  the rescaled environment are `MatedCRTEnv.IsValid.ae_coneDataLift_rescaled`, and the assembly is
  `MatedCRTEnv.rescaledMatingOfTrees_of_lift`.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal

namespace MatedCRT

/-- **A rescaled lift is an almost sure Brownian rescaling of the data.** If the triple of `V'` is
almost surely the rescaled triple of `V`, then the scale `R = coneScaleOfPair γ b (B, B')` of the
radial paths of `V` is nonzero, and almost surely the curve of `V'` is `coneRescaleCurve R b` of the
curve of `V` and its boundary-length pair is `brownRescale b` of that of `V`. -/
theorem ae_coneRescale_of_coneTriple_eq {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ b : ℝ}
    {V V' : Ω → MatedCRTHarmonic.MatedCRT.CouplingData}
    (hae : ∀ᵐ ω ∂P, MatedCRTHarmonic.MatedCRT.CouplingData.coneTriple γ (V' ω) =
      coneRescaleOfQuad γ b (coneQuad (V ω))) :
    (∀ ω, coneScaleOfPair γ b ((V ω).B, (V ω).B') ≠ 0) ∧
      (∀ᵐ ω ∂P, (V' ω).η = MatedCRTHarmonic.MatedCRT.coneRescaleCurve
        (coneScaleOfPair γ b ((V ω).B, (V ω).B')) b (V ω).η) ∧
      ∀ᵐ ω ∂P, (V' ω).bm = MatedCRTHarmonic.MatedCRT.brownRescale b (V ω).bm :=
  ⟨fun _ => (Real.exp_pos _).ne', hae.mono fun _ h => congrArg (fun p => p.2.1) h,
    hae.mono fun _ h => congrArg (fun p => p.2.2) h⟩

/-- **The rescaled mating-of-trees step from rescaled lifts.** If, for `0 < γ < 2` and `b > 0`, every
measurable random element `V'` with the law of coupling data `V` whose triple is almost surely the
rescaled triple of `V` is again coupling data, then every valid environment satisfies
`RescaledMatingOfTreesStep`: the coordinates of the lift of `MatedCRTEnv.IsValid.exists_coneDataLift`
are the mating-of-trees coupling of the rescaled environment. -/
theorem rescaledMatingOfTreesStep_of_lift (𝒮 : SpaceFillingSLEModel)
    (hlift : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ b : ℝ, 0 < b → ∀ (Ω : Type) [MeasurableSpace Ω]
      (P : Measure Ω) (V V' : Ω → MatedCRTHarmonic.MatedCRT.CouplingData), Measurable V →
      MatedCRTHarmonic.MatedCRT.IsCouplingData γ P V → Measurable V' → P.map V' = P.map V →
      (∀ᵐ ω ∂P, MatedCRTHarmonic.MatedCRT.CouplingData.coneTriple γ (V' ω) =
        coneRescaleOfQuad γ b (coneQuad (V ω))) →
      MatedCRTHarmonic.MatedCRT.IsCouplingData γ P V') :
    RescaledMatingOfTreesStep 𝒮 := by
  intro γ hγ hγ2 Ω _ S hS b hb _ _ _ _ hpair _
  obtain ⟨V, V', hV, hC, hbm, htie, hV', hlaw, hae⟩ := hS.exists_coneDataLift hγ hγ2 hb
  exact MatedCRTEnv.rescaledMatingOfTrees_of_lift hb hV hbm
    (hlift γ hγ hγ2 b hb Ω S.P V V' hV hC hV' hlaw hae)
    (hS.ae_coneDataLift_rescaled hγ hγ2 hb hV hC hbm htie hV' hlaw hae) hpair

end MatedCRT
