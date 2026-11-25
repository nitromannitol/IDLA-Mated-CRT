import MatedCRT.FirstPass.Derived.GMS21ZeroConeAnnulusRepair
import MatedCRT.FirstPass.Derived.GMS21Lemma33Cone
import MatedCRT.FirstPass.Derived.GMS21CanonicalTutteLP
import MatedCRT.FirstPass.Derived.ZeroConeLemmaA1Restricted
import MatedCRT.FirstPass.Derived.ZeroConeLemmaA1PosProof
import MatedCRT.FirstPass.Derived.ZeroConeCurveFactorProof
import MatedCRT.FirstPass.Derived.ZeroConeConfigCovarianceProof

/-!
# The premise `tutteLP` at the canonical model from Theorem 3.10 and the steps of Lemmas 3.3 and 3.5

Gwynne–Miller–Sheffield (arXiv:1705.11161), proof of Theorem 3.4, case 1. The form on annuli of Lemma 3.5 for the
shifted zero-cone configuration (`ZeroConeAnnulusLPForm`) follows from Theorem 3.10 of arXiv:1807.07515
(`GMSTheorem310`), the hypotheses of Proposition 3.1 with Lemma A.1 and Remark A.2 in the restricted form
`ZeroConeLemmaA1Pos`, and the named steps of the proof of Lemma 3.5; Lemma 3.3 for the local configurations
(`CouplingLocalConfigUMAC`) follows from its three inputs. Together with the couplings they give the premise
`tutteLP` of `CanonicalHypotheses` at the canonical model.

Main declarations:

* `GMS310Transfer.zeroConeAnnulusLPForm_of_theorem310_lemmaA1Pos`: `ZeroConeAnnulusLPForm` with the tail triviality
  of the zero cone from `ZeroConeLemmaA1Pos`.
* `tutteLP_canonical_of_theorem310_zeroConeSteps`: the premise `tutteLP` at the canonical model.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Metric Filter Topology HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

noncomputable section

namespace MatedCRT.GMS310Transfer

section ZeroCone

open MatedCRTHarmonic MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.GMS4b ReflectedGMS.GMS

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- **Lemma 3.5 of arXiv:1705.11161 in the annulus form, from Theorem 3.10 of arXiv:1807.07515 and Lemma A.1 in the
restricted form.** Under the hypotheses of `exists_zeroCone_config_gmsHypotheses_of_lemmaA1Pos`, the law of every
realization of the shifted zero-cone configuration satisfies the four hypotheses of Theorem 1.16 of
arXiv:1807.07515, so Theorem 3.10 applies to it; with the named steps of the proof of Lemma 3.5 this gives the
annulus form of the uniform-start invariance principle for the shifted zero-cone data at mesh `1/n`. -/
theorem zeroConeAnnulusLPForm_of_theorem310_lemmaA1Pos
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (hf : AEMeasurable (fun ω => coneField (X ω)
      (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω))) P)
    (hI : ZeroConeSpatialAverageInvariance D hγ) (h25 : GMSConditionTwoImpliesFive)
    (hA1 : ZeroConeLemmaA1Pos D hγ) (hcov : ZeroConeConfigCovariance D hγ)
    (hlaw : SpaceFillingSLESimilarityLaw D hγ) (hcurve : ZeroConeCurveFactorStep D hγ)
    (hphase : ZeroConePhaseFactorStep D hγ) (h310 : GMSTheorem310)
    (hreal : ZeroConeConfigRealizable D hγ) (hrot : ZeroConeConfigRotationInvariance D hγ)
    (hscale : ZeroConeWeightedMeshScaling D hγ)
    (hmeas : ZeroConeWeightedUniformErrorMeasurability D hγ) :
    ZeroConeAnnulusLPForm D hγ := by
  have hT := zeroConeTailTriviality_of_lemmaA1Pos D hγ hA1 hcov hlaw hcurve hphase
  refine zeroConeAnnulusLPForm_of_theorem310Form_code D hγ hf (fun G F hF => ?_) hreal hrot hscale hmeas
  have : IsProbabilityMeasure P := D.isProbabilityMeasure
  have : IsProbabilityMeasure ((P.prod zeroConePhase).map F) :=
    (Measure.isProbabilityMeasure_map_iff hF.2.2.1).2 inferInstance
  exact h310 _ (massTransport_map_of_zeroConeSpatialAverageInvariance D hγ hI h25 hF)
    (ergodicModuloScaling_map_of_zeroConeTailTriviality D hγ hT hF)
    (finiteExpectation_map_of_zeroConeConfigRealization D hγ hF)
    (connectedAlongLines_map_of_zeroConeConfigRealization D hγ hf hF)

end ZeroCone

end MatedCRT.GMS310Transfer

namespace MatedCRT

open ReflectedGMS.GMS MatedCRTHarmonic MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.GMS4b GMS310Transfer

/-- **The premise `tutteLP` at the canonical model from Theorem 3.10 and the steps of Lemmas 3.3 and 3.5**
(Gwynne–Miller–Sheffield, arXiv:1705.11161, proof of Theorem 3.4, case 1). If the couplings with code law `ν (16/γ²)`
exist, Theorem 3.10 of arXiv:1807.07515 holds, condition 2 implies condition 5 of its Appendix B, Lemma A.1 holds
for the circle-average embedding of the `0`-quantum cone and the normalized dilation by `2` of the whole-plane GFF
modulo `2πχ` is mixing (Remark A.2), every mating-of-trees coupling on `ℝ` satisfies the named steps of the proof of
Proposition 3.1 (the joint form of Lemma A.1, the Borel quantum-time curve and the covariant code of the weighted
cells) and of the proof of Lemma 3.5, and the three inputs of Lemma 3.3 hold for every `γ ∈ (0, 2)`, then
for every `γ ∈ (0, 2)` the canonical model has a valid environment whose walk and Brownian motion stopped at their
exits from `B_R(0)` are close in Lévy–Prokhorov distance from every selected start with probability tending to one. -/
theorem tutteLP_canonical_of_theorem310_zeroConeSteps (ν : ℝ → Measure SLEPathCode)
    (hcpl : ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∃ (P : Measure ℝ) (X X₀ hIG₀ : ℝ → Field) (B B' B₀ B₀' : ℝ≥0 → ℝ → ℝ) (U : ℝ → ℝ)
        (ηL η η₀ : ℝ → C(ℝ, ℂ)) (bm : ℝ → Path2),
        IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm ∧
        P.map (fun ω => slePathCode (ηL ω)) = ν (16 / γ ^ 2))
    (h310 : GMSTheorem310) (h25 : GMSConditionTwoImpliesFive)
    (hP31 : ∀ (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 2) {P : Measure ℝ} {X X₀ hIG₀ : ℝ → Field}
      {B B' B₀ B₀' : ℝ≥0 → ℝ → ℝ} {U : ℝ → ℝ} {ηL η η₀ : ℝ → C(ℝ, ℂ)} {bm : ℝ → Path2}
      (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm),
      AEMeasurable (fun ω => coneField (X ω) (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω))) P ∧
      ZeroConeSpatialAverageInvariance D hγ ∧ ZeroConeQuantumCurveCovariance D hγ ∧
      ZeroConeCellWeightCode D hγ ∧ SpaceFillingSLESimilarityLaw D hγ ∧ ZeroConeJointLemmaA1 D hγ ∧
      ZeroConePhaseFactorStep D hγ)
    (hA1 : ∀ (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 2),
      ZeroConeCircleAverageLemmaA1 γ hγ ∧ IGFieldDilationMixing γ hγ)
    (h35 : ∀ (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 2) {P : Measure ℝ} {X X₀ hIG₀ : ℝ → Field}
      {B B' B₀ B₀' : ℝ≥0 → ℝ → ℝ} {U : ℝ → ℝ} {ηL η η₀ : ℝ → C(ℝ, ℂ)} {bm : ℝ → Path2}
      (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm),
      ZeroConeConfigRealizable D hγ ∧ ZeroConeConfigRotationInvariance D hγ ∧
      ZeroConeWeightedMeshScaling D hγ ∧ ZeroConeWeightedUniformErrorMeasurability D hγ)
    (h1 : ∀ γ ∈ Ioo (0 : ℝ) 2, ConeAnnulusAreaLawEquivalence γ)
    (h2 : ∀ γ ∈ Ioo (0 : ℝ) 2, ConeOffsetDensity γ)
    (h3 : ∀ γ ∈ Ioo (0 : ℝ) 2, ConeConfigReconstruction γ) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ 𝒮₀ : SpaceFillingSLEModel, HasNormalizedSLELaw 𝒮₀ ν ∧
      ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (S₀ : MatedCRTEnv Ω₀), S₀.IsValid 𝒮₀ γ ∧
      ∃ η₀ : Ω₀ → C(ℝ, ℂ), Measurable η₀ ∧ (∀ᵐ ω ∂S₀.P, ⇑(η₀ ω) = S₀.η ω) ∧
      ∀ R ρ : ℝ, 0 < ρ → ρ < R → ∀ κ : ℝ, 0 < κ → ∀ θ : ℝ, 0 < θ →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          S₀.P.map (fun ω => (η₀ ω, S₀.mult (1 / (n : ℝ)) ω))
            (uniformStartSelectedLPData (1 / (n : ℝ)) ρ R κ)ᶜ ≤ ENNReal.ofReal θ :=
  tutteLP_canonical_of_zeroConeAnnulusLPForm_localConfig ν hcpl
    (fun γ hγ _ _ _ _ _ _ _ _ _ _ _ _ _ D => by
      obtain ⟨hf, hI, hQ, hK, hlaw, hJ, hphase⟩ := hP31 γ hγ D
      obtain ⟨hA1c, hmix⟩ := hA1 γ hγ
      obtain ⟨hreal, hrot, hscale, hmeas⟩ := h35 γ hγ D
      exact zeroConeAnnulusLPForm_of_theorem310_lemmaA1Pos D hγ hf hI h25 (zeroConeLemmaA1Pos D hγ hA1c hmix)
        (zeroConeConfigCovariance D hγ hQ hK) hlaw (zeroConeCurveFactorStep D hγ hJ) hphase h310
        hreal hrot hscale hmeas)
    (fun γ hγ _ _ _ _ _ _ _ _ _ _ _ _ _ D => forall_couplingLocalConfigUMAC_of_lemma33Inputs h1 h2 h3 γ hγ D)

end MatedCRT
