import MatedCRT.FirstPass.Derived.ReferenceConeEnvironmentWholePlaneFixedStart
import MatedCRT.FirstPass.Derived.ConeFieldSigmaCurveIndep
import MatedCRT.FirstPass.S5c.FieldRoute
import MatedCRT.FirstPass.SLERef.Reference

/-!
# Reference environments from mating-of-trees couplings and the fixed-start Liouville clock

`HasReferenceEnvironments 𝒮` asks, for every `γ ∈ (0, 2)`, for a valid mated-CRT environment on
the sample space `ℝ`. The limit-clock reference cone environment of a mating-of-trees coupling
(`exists_reference_cone_environment_limitClock_of_coupling_wholePlane_fixedStart`) is valid as soon
as

* the space-filling SLE model `𝒮` recognizes the curve of the coupling as an SLE against the
  σ-algebra of the cone field, and
* the dyadic Liouville clocks of the normalized whole-plane Gaussian free field converge from a
  fixed start, with a strictly increasing limit (Berestycki 2015, fixed starting point).

The σ-algebra of the cone field is contained in the ambient σ-algebra (the pairings of a quantum
cone are measurable) and is independent of the Lebesgue-parametrized curve of the coupling
(`indep_fieldSigma_igCurve_of_coupling`). Hence the first item may be asked of every such
σ-algebra, which removes all reference to the constructed environment from the hypotheses.

## Main statement

* `hasReferenceEnvironments_of_coupling_wholePlane_fixedStart`: `HasReferenceEnvironments 𝒮` from
  mating-of-trees couplings on `ℝ` whose curves `𝒮` recognizes as SLE against every independent
  sub-σ-algebra, and the fixed-start convergence and strict monotonicity of the whole-plane clock.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter HarmonicBalls MarkovProcess LQGMetric
open MatedCRTHarmonic MatedCRTHarmonic.MatedCRT
open scoped NNReal

namespace MatedCRT.Sec1

/-- **Reference environments from couplings and the fixed-start clock.** Let `𝒮` be a
space-filling SLE model. Suppose that for every `γ ∈ (0, 2)` there is a mating-of-trees coupling on
the sample space `ℝ` whose curve `𝒮` recognizes as an SLE with parameter `κ' = 16/γ²` against every
sub-σ-algebra independent of its Lebesgue-parametrized curve, and that, for every such `γ` and
every normalized whole-plane Gaussian free field with a jointly continuous, jointly measurable
version of its circle averages, from Lebesgue-almost every fixed start, almost surely for the joint
law of the field and planar Brownian motion, the dyadic approximating Liouville clocks are uniformly
Cauchy on every compact time interval, with a strictly increasing limit (Berestycki 2015, fixed
starting point). Then `𝒮` has reference environments. -/
theorem hasReferenceEnvironments_of_coupling_wholePlane_fixedStart (𝒮 : SpaceFillingSLEModel)
    (hcpl : ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∃ (P : Measure ℝ) (X X₀ hIG₀ : ℝ → Field) (B B' B₀ B₀' : ℝ≥0 → ℝ → ℝ) (U : ℝ → ℝ)
        (ηL η η₀ : ℝ → C(ℝ, ℂ)) (bm : ℝ → Path2),
        IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm ∧
        ∀ 𝓕 : MeasurableSpace ℝ, 𝓕 ≤ Real.measurableSpace →
          Indep 𝓕 (MeasurableSpace.comap ηL inferInstance) P →
          @SpaceFillingSLEModel.IsSLE 𝒮 ℝ Real.measurableSpace P 𝓕 (16 / γ ^ 2)
            (fun ω => ⇑(η ω)))
    (hfix : ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
        {Y' : Ω' → DistC} {c' : DistC → ℝ → ℂ → ℝ},
        IsNormalizedWPGFF Y' P' →
        (∀ r, 0 < r → ∀ z, ∀ᵐ ω' ∂P', c' (Y' ω') r z = LQGMetric.circleAvg (Y' ω') r z) →
        (∀ x, ContinuousOn (fun p : ℝ × ℂ => c' x p.1 p.2) (Ioi 0 ×ˢ univ)) →
        Measurable (fun q : (Ioi (0 : ℝ) × ℂ) × DistC => c' q.2 q.1.1 q.1.2) →
        ∀ T : ℝ≥0, ∀ᵐ y ∂(volume : Measure ℂ),
          ∀ᵐ p ∂(P'.prod (planarBrownianMotion y)),
            UniformCauchySeqOn
              (fun k t => lqgClockApprox γ (c' (Y' p.1)) (HarmonicBalls.dyadicScale k) p.2 t)
              atTop (Icc 0 T))
    (hfixsm : ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
        {Y' : Ω' → DistC} {c' : DistC → ℝ → ℂ → ℝ},
        IsNormalizedWPGFF Y' P' →
        (∀ r, 0 < r → ∀ z, ∀ᵐ ω' ∂P', c' (Y' ω') r z = LQGMetric.circleAvg (Y' ω') r z) →
        (∀ x, ContinuousOn (fun p : ℝ × ℂ => c' x p.1 p.2) (Ioi 0 ×ˢ univ)) →
        Measurable (fun q : (Ioi (0 : ℝ) × ℂ) × DistC => c' q.2 q.1.1 q.1.2) →
        ∀ᵐ y ∂(volume : Measure ℂ), ∀ᵐ p ∂(P'.prod (planarBrownianMotion y)),
          StrictMono (LatticeProb.limitAfterPositiveTimes
            fun k t => lqgClockApprox γ (c' (Y' p.1)) (HarmonicBalls.dyadicScale k) p.2 t)) :
    HasReferenceEnvironments 𝒮 := by
  intro γ hγ0 hγ2
  obtain ⟨P, X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, η, η₀, bm, D, hSLE⟩ := hcpl γ hγ0 hγ2
  obtain ⟨S, hP, -, hη, -, hcone, -, hmatch, hvalid⟩ :=
    exists_reference_cone_environment_limitClock_of_coupling_wholePlane_fixedStart D
      ⟨hγ0, hγ2⟩ 𝒮
  refine ⟨S, hvalid ?_ (fun {Ω'} _ {P'} _ {Y'} {c'} => hfix γ hγ0 hγ2)
    (fun {Ω'} _ {P'} _ {Y'} {c'} => hfixsm γ hγ0 hγ2)⟩
  have hD : IsMatingOfTreesCoupling γ S.P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm := by
    rw [hP]
    exact D
  have hrep : ∀ᵐ ω ∂S.P, ∀ φ : TestC, S.hC ω ⇑φ =
      coneField (X ω) (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)) φ :=
    hmatch.mono fun ω hω => hω.2
  have hind : Indep S.fieldSigma (MeasurableSpace.comap ηL inferInstance) P := by
    rw [← hP]
    exact indep_fieldSigma_igCurve_of_coupling (S := S) hγ0 hγ2 hD hrep
  have hle : S.fieldSigma ≤ Real.measurableSpace :=
    MatedCRT.S5c.fieldSigma_le_of_pairing_measurable S.hC hcone.measurable_pairing
  rw [hP, hη]
  exact hSLE S.fieldSigma hle hind

end MatedCRT.Sec1
