import MatedCRT.FirstPass.SLERef.Similarity
import MatedCRT.FirstPass.Derived.SimilarityAssembly
import MatedCRT.FirstPass.Derived.SimilarityLawInvariance
import MatedCRT.FirstPass.Derived.SimilarityRescaledIndep
import MatedCRT.FirstPass.Derived.ConeScalingLawDerived
import MatedCRT.FirstPass.Derived.QuantumConeScalingDerived

/-!
# The corrected similarity transfer for a model with the normalized space-filling SLE law

`FPSimilarityTransferCorrected 𝒮` holds for every space-filling SLE model `𝒮` whose normalized law is given
(`HasNormalizedSLELaw 𝒮 ν`) and which is scale invariant (`SLEScaleInvarianceInput 𝒮`).  The proof assembles the
abstract identity in law of `SimilarityAssembly` from:

* the identity in law of the rescaled cone data `(circle averages, LQG measure)` with the unscaled cone data
  (`IsConeField.identDistrib_rescaledCircleMeasure`, from the scale invariance of the quantum cone and the dilation
  covariance of the LQG measure);
* the independence of the rescaled cone data and the scale radius `R_b` from the Lebesgue-area representative
  `ηL` (`indepFun_rescaledCone_of_indep`), since the rescaled data is a Borel function of the circle average process;
* the invariance of the law of `ηL` under the rescalings (`map_scaleRep_eq_of_law`);
* the Borel version `radiusDecoder` of the scale radius `R_b` of the circle average process.

The only inputs about the space-filling SLE are the law of its Lebesgue-area representative and its scale invariance.
-/

open MeasureTheory ProbabilityTheory HarmonicBalls

namespace MatedCRT.FirstPass.Derived

/-- The identity in law of the similarity transfer, for one quantum cone field, one scale and one space-filling SLE
(`𝓕` is declared before the ambient sigma-algebra `mΩ`, so that `mΩ` is the instance in the statement). -/
theorem similarityTransfer_core {𝒮 : SpaceFillingSLEModel} {ν : ℝ → Measure SLEPathCode}
    (hν : HasNormalizedSLELaw 𝒮 ν) (hsc : SLEScaleInvarianceInput 𝒮) {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} {𝓕 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} {η : Ω → ℝ → ℂ}
    {ηL : Ω → C(ℝ, ℂ)} (hcone : IsConeField γ P hC hcirc μ)
    (hη : @SpaceFillingSLEModel.IsSLE 𝒮 Ω mΩ P 𝓕 (16 / γ ^ 2) η) (hηL : Measurable ηL)
    (hrep : ∀ᵐ ω ∂P, IsLebesgueRepresentative (η ω) (ηL ω))
    (hind : IndepFun (fun ω => (circleProcess (hcirc ω), μ ω)) ηL P)
    (harea : ∀ᵐ ω ∂P, IsAreaParametrized (μ ω) (η ω)) {b : ℝ} (hb : 0 < b) :
    IdentDistrib
      (fun ω =>
        (circleProcess (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b),
         FPScaledMeasure (μ ω) (coneScaleRadius γ (hcirc ω) b) b,
         fun s : ℝ => ((coneScaleRadius γ (hcirc ω) b : ℝ) : ℂ)⁻¹ * η ω (b * s)))
      (fun ω => (circleProcess (hcirc ω), μ ω, η ω)) P P := by
  have hscale := quantumConeScalingInput_derived
  have hlqg := coneLQGScalingStep_of_scaling hscale
  have hP : IsProbabilityMeasure P := hcone.1
  have hκ : 4 < 16 / γ ^ 2 := by
    rw [lt_div_iff₀ (by positivity)]
    nlinarith
  have hid0 := hcone.identDistrib_rescaledCircleMeasure hγ0 hγ2 hscale hlqg hb
  have hs := hlqg γ hγ0 hγ2 Ω P hC hcirc μ hcone b hb
  have hρ := ae_radiusDecoder_eq hγ0 hγ2 hcone.2.1 b
  have hlf : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) := by
    have h : ∀ᵐ ω ∂P, IsLQGLimit γ (hcirc ω) (μ ω) := hcone.2.2
    exact h.mono fun _ hω => hω.isLocallyFiniteMeasure
  obtain ⟨Xt, hXtm, hXt⟩ := hid0.aemeasurable_fst
  let Rt : Ω → ℝ := fun ω => radiusDecoder γ b (circleProcess (hcirc ω))
  have hRtm : Measurable Rt :=
    (measurable_radiusDecoder γ b).comp hcone.2.1.measurable_circleProcess
  have hid : IdentDistrib (fun ω => ((Xt ω).1, (Xt ω).2)) (fun ω => (circleProcess (hcirc ω), μ ω)) P P :=
    (IdentDistrib.of_ae_eq hid0.aemeasurable_fst hXt).symm.trans hid0
  have hφ : Measurable (fun q : (Set.Ioi (0 : ℝ) × ℂ → ℝ) × Measure ℂ × ℝ => ((q.1, q.2.1), q.2.2)) :=
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp measurable_snd)
  have hZ := (indepFun_rescaledCone_of_indep hγ0 hγ2 hcone hlqg hb hind).comp hφ measurable_id
  have hindX : IndepFun (fun ω => (((Xt ω).1, (Xt ω).2), Rt ω)) ηL P := by
    refine hZ.congr ?_ (Filter.EventuallyEq.refl _ _)
    filter_upwards [hXt, hρ] with ω h1 h2
    exact Prod.ext (Prod.ext (congrArg Prod.fst h1) (congrArg Prod.snd h1)) h2.symm
  have hinv : ∀ a : ℝ, 0 < a → (P.map ηL).map (scaleRep a) = P.map ηL :=
    fun a ha => map_scaleRep_eq_of_law hν hsc hκ hη hηL hrep ha
  have hR0 : ∀ᵐ ω ∂P, 0 < Rt ω := by
    filter_upwards [hs, hρ] with ω h h2
    show 0 < radiusDecoder γ b (circleProcess (hcirc ω))
    rw [h2]
    exact h.1
  have hμ' : ∀ᵐ ω ∂P, (Xt ω).2 = FPScaledMeasure (μ ω) (Rt ω) b := by
    filter_upwards [hXt, hρ] with ω h1 h2
    have h1b := congrArg Prod.snd h1
    have h3 : Rt ω = coneScaleRadius γ (hcirc ω) b := h2
    rw [h3, ← h1b]
    rfl
  have hass := identDistrib_similarity_of_indep (c := fun ω => circleProcess (hcirc ω))
    (c' := fun ω => (Xt ω).1) (μ' := fun ω => (Xt ω).2) (R := Rt) hb hXtm hRtm hηL hid hindX hind
    hinv hR0 hμ' hlf hrep harea
  have hae : (fun ω => (circleProcess (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b),
        FPScaledMeasure (μ ω) (coneScaleRadius γ (hcirc ω) b) b,
        fun s : ℝ => ((coneScaleRadius γ (hcirc ω) b : ℝ) : ℂ)⁻¹ * η ω (b * s))) =ᵐ[P]
      (fun ω => ((Xt ω).1, (Xt ω).2, fun s : ℝ => ((Rt ω : ℝ) : ℂ)⁻¹ * η ω (b * s))) := by
    filter_upwards [hXt, hρ] with ω h1 h2
    have h3 : Rt ω = coneScaleRadius γ (hcirc ω) b := h2
    have h1a : circleProcess (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b) = (Xt ω).1 :=
      congrArg Prod.fst h1
    have h1b : rescaledMeasure (μ ω) (coneScaleRadius γ (hcirc ω) b) b = (Xt ω).2 := congrArg Prod.snd h1
    refine Prod.ext h1a (Prod.ext h1b ?_)
    funext s
    simp only [h3]
  exact (IdentDistrib.of_ae_eq (hass.aemeasurable_fst.congr hae.symm) hae).trans hass

/-- **The corrected similarity transfer**, from the normalized law and the scale invariance of the space-filling
SLE model. -/
theorem fpSimilarityTransferCorrected_of_law {𝒮 : SpaceFillingSLEModel} {ν : ℝ → Measure SLEPathCode}
    (hν : HasNormalizedSLELaw 𝒮 ν) (hsc : SLEScaleInvarianceInput 𝒮) :
    FPSimilarityTransferCorrected 𝒮 := by
  intro γ hγ0 hγ2 Ω mΩ P 𝓕 hC hcirc μ η ηL hcone hη _hG hηL hrep hind harea b hb
  exact similarityTransfer_core (mΩ := mΩ) (𝓕 := 𝓕) hν hsc hγ0 hγ2 hcone hη hηL hrep hind harea hb

end MatedCRT.FirstPass.Derived
