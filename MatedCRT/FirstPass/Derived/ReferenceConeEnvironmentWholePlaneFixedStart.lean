import MatedCRT.FirstPass.Derived.ReferenceConeEnvironmentWholePlaneClockStrict
import MatedCRT.FirstPass.Derived.WholePlaneClockStrictMonoFixedStart

/-!
# Reference cone environments: fixed-start whole-plane clock hypotheses

`exists_reference_cone_environment_limitClock_of_coupling_wholePlane_strictMono` reduces the
validity of the limit-clock reference cone environment of a mating-of-trees coupling to the SLE
property and two quenched statements about the dyadic clocks of a normalized whole-plane Gaussian
free field: almost surely in the field, from Lebesgue-almost every start, almost surely in the
path, (i) the dyadic clocks are locally uniformly Cauchy on discs avoiding the origin, and (ii) the
limiting clock is strictly increasing.

Here both are replaced by the form in which Berestycki (2015) proves them, for a **fixed** starting
point and almost surely for the joint law of the field and the Brownian path: from
Lebesgue-almost every start `y`, `(P' ⊗ P^y)`-almost surely, (i') the dyadic clocks are uniformly
Cauchy on every `[0, T]`, and (ii') the limiting clock is strictly increasing. The quenched forms
follow by Fubini's theorem (`ae_localUniformCauchy_wholePlane_of_fixedStart`,
`ae_strictMono_wholePlane_of_fixedStart`).

## Main statement

* `exists_reference_cone_environment_limitClock_of_coupling_wholePlane_fixedStart`.
-/

noncomputable section

open MeasureTheory Set Filter HarmonicBalls MarkovProcess LQGMetric
open MatedCRTHarmonic MatedCRTHarmonic.MatedCRT
open scoped NNReal

namespace MatedCRT.Sec1

/-- The limit-clock reference cone environment of a mating-of-trees coupling is valid as soon as the
curve is an SLE and, for every normalized whole-plane Gaussian free field and every jointly
continuous version of its circle averages, from Lebesgue-almost every fixed start, almost surely for
the joint law of the field and the Brownian path, the dyadic clocks are uniformly Cauchy on every
compact time interval and the limiting clock is strictly increasing (Berestycki 2015, fixed starting
point). -/
theorem exists_reference_cone_environment_limitClock_of_coupling_wholePlane_fixedStart
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (𝒮 : SpaceFillingSLEModel) :
    ∃ S : MatedCRTEnv Ω,
      S.P = P ∧ S.bm = bm ∧ S.η = (fun ω => ⇑(η ω)) ∧
      (∀ ω b, S.clock ω b = LatticeProb.limitAfterPositiveTimes
        (fun j => lqgClockApprox γ (S.hcirc ω) (HarmonicBalls.dyadicScale j) b)) ∧
      IsQuantumCone γ S.P S.hC S.hcirc ∧ IsLQGMeasure S.P γ S.hcirc S.μ ∧
      (∀ᵐ ω ∂S.P, ⇑(η ω) = S.η ω ∧ ∀ φ : TestC,
        S.hC ω ⇑φ = coneField (X ω)
          (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)) φ) ∧
      (𝒮.IsSLE S.P S.fieldSigma (16 / γ ^ 2) S.η →
        (∀ {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
            {Y' : Ω' → DistC} {c' : DistC → ℝ → ℂ → ℝ},
            IsNormalizedWPGFF Y' P' →
            (∀ r, 0 < r → ∀ z, ∀ᵐ ω' ∂P', c' (Y' ω') r z = LQGMetric.circleAvg (Y' ω') r z) →
            (∀ x, ContinuousOn (fun p : ℝ × ℂ => c' x p.1 p.2) (Ioi 0 ×ˢ univ)) →
            Measurable (fun q : (Ioi (0 : ℝ) × ℂ) × DistC => c' q.2 q.1.1 q.1.2) →
            ∀ T : ℝ≥0, ∀ᵐ y ∂(volume : Measure ℂ),
              ∀ᵐ p ∂(P'.prod (planarBrownianMotion y)),
                UniformCauchySeqOn
                  (fun k t => lqgClockApprox γ (c' (Y' p.1)) (HarmonicBalls.dyadicScale k) p.2 t)
                  atTop (Icc 0 T)) →
        (∀ {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
            {Y' : Ω' → DistC} {c' : DistC → ℝ → ℂ → ℝ},
            IsNormalizedWPGFF Y' P' →
            (∀ r, 0 < r → ∀ z, ∀ᵐ ω' ∂P', c' (Y' ω') r z = LQGMetric.circleAvg (Y' ω') r z) →
            (∀ x, ContinuousOn (fun p : ℝ × ℂ => c' x p.1 p.2) (Ioi 0 ×ˢ univ)) →
            Measurable (fun q : (Ioi (0 : ℝ) × ℂ) × DistC => c' q.2 q.1.1 q.1.2) →
            ∀ᵐ y ∂(volume : Measure ℂ), ∀ᵐ p ∂(P'.prod (planarBrownianMotion y)),
              StrictMono (LatticeProb.limitAfterPositiveTimes
                fun k t => lqgClockApprox γ (c' (Y' p.1)) (HarmonicBalls.dyadicScale k) p.2 t)) →
        S.IsValid 𝒮 γ) := by
  obtain ⟨S, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    exists_reference_cone_environment_limitClock_of_coupling_wholePlane_strictMono D hγ 𝒮
  refine ⟨S, h1, h2, h3, h4, h5, h6, h7, fun hSLE hfix hfixsm => h8 hSLE ?_ ?_⟩
  · intro Ω' _ P' _ Y' c' hG hc hcont hmeas
    exact ae_localUniformCauchy_wholePlane_of_fixedStart hG.1.measurable hcont hmeas
      (hfix hG hc hcont hmeas)
  · intro Ω' _ P' _ Y' c' hG hc hcont hmeas
    exact ae_strictMono_wholePlane_of_fixedStart hG.1.measurable hcont hmeas
      (hfix hG hc hcont hmeas) (hfixsm hG hc hcont hmeas)

end MatedCRT.Sec1
