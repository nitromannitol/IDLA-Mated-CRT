import MatedCRT.FirstPass.Derived.ClassLawAllStarts
import MatedCRT.FirstPass.Derived.HN5bOfExitClassLaws

/-!
# Lemma 7.4 without the stopped class laws as a hypothesis

Berestycki and Gwynne, *Random walks on mated-CRT planar maps and Liouville Brownian motion*
(arXiv:2003.10320), Lemma 7.4.

`randomWalkToLBMStmt_of_markovLimit_derived_hN5c` takes the stopped class laws of the limit as the hypothesis
`hN5c`.  That hypothesis is now a theorem: `ae_forall_map_stoppedExitCurve_eq_of_tendsto_law_interpWalkLaw`
gives the Brownian class law for every `z` and every radius `r > ‖z‖`, in particular for almost every `r`.

* `randomWalkToLBMStmt_of_markovLimit_derived_noHN5`: `h11` with the binder `hN5` of Lemma 7.4 discharged.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set Metric MarkovProcess
open _root_.HarmonicBalls _root_.MatedCRTHarmonic.MatedCRT
open scoped NNReal ENNReal BoundedContinuousFunction
open MatedCRT.FirstPass.Derived (LQGData LQGData.toMeasure)

namespace MatedCRT

/-- **`h11` with Lemma 7.4 proved.** `randomWalkToLBMStmt_of_markovLimit_derived_hN5c` with the hypothesis `hN5c`
(the Brownian law of the curve class of a subsequential limit of the interpolated walk laws, stopped at the exit from
almost every ball) proved from the uniform-start invariance principle. -/
theorem randomWalkToLBMStmt_of_markovLimit_derived_noHN5 {𝒮 : SpaceFillingSLEModel}
    {ν : ℝ → Measure SLEPathCode}
    (h1 : HasNormalizedSLELaw 𝒮 ν) (h2 : SLEModelClosureInput 𝒮) (hN4 : GMS21UniformStartInput 𝒮)
    (h10 : HasReferenceEnvironments 𝒮)
    (hN8' : ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
      ∀ E : Ω → LQGData, Measurable E → (∀ᵐ ω ∂S.P, LQGData.toMeasure (E ω) = S.μ ω) →
      ∀ᵐ d ∂(S.P.map fun ω => (LQGMetric.pairJ ⊤ (H ω), E ω)),
        IsMarkovTCBM (lbmPathLawField γ d.1) ∧ IsInvariantFor (lbmPathLawField γ d.1) (LQGData.toMeasure d.2))
    (hN9 : ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
      ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
      ∀ E : Ω → LQGData, Measurable E → ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ ν' : Measure (((LQGMetric.CoordJ → ℝ) × LQGData) × PathLawFamily), IsProbabilityMeasure ν' →
      (∀ f : (((LQGMetric.CoordJ → ℝ) × LQGData) × PathLawFamily) →ᵇ ℝ,
        Tendsto (fun n => ∫ ω, f ((LQGMetric.pairJ ⊤ (H ω), E ω), interpWalkLaw S η' (ε n) ω) ∂S.P) atTop
          (𝓝 (∫ p, f p ∂ν'))) →
      (∀ᵐ p ∂ν', ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ z, p.2 z = LatticeProb.timeScalePathKernel c (lbmPathLawField γ p.1.1) z) →
      ∃ c₀ : ℝ≥0, c₀ ≠ 0 ∧ ∀ᵐ p ∂ν', ∀ z, p.2 z = LatticeProb.timeScalePathKernel c₀ (lbmPathLawField γ p.1.1) z) :
    RandomWalkToLBMStmt 𝒮 := by
  obtain ⟨G, hGnull, hG⟩ := exists_matingRigidLEOn_full_derived
  have hEnvS := coneEnvironmentScalingUnderSLE_of_scaling 𝒮
    FirstPass.Derived.quantumConeScalingInput_derived h2.1 h2.2.1 h2.2.2
  have hU : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ G : Set MatedCRTHarmonic.MatedCRT.Path2,
      (∀ μ : Measure MatedCRTHarmonic.MatedCRT.Path2, MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ μ →
        μ Gᶜ = 0) ∧ MatingRigidLEOn G := fun γ hγ0 hγ2 => ⟨G, hGnull γ hγ0 hγ2, hG⟩
  have hN5c : ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
        ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
        ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
        ∀ ν₂ : Measure PathLawFamily, IsProbabilityMeasure ν₂ →
        (∀ f : PathLawFamily →ᵇ ℝ,
          Tendsto (fun n => ∫ ω, f (interpWalkLaw S η' (ε n) ω) ∂S.P) atTop (𝓝 (∫ P, f P ∂ν₂))) →
        ∀ᵐ P ∂ν₂, ∀ z : ℂ, ∀ᵐ r ∂(volume : Measure ℝ), ‖z‖ < r →
          ((P z : ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ)).map
            (MatedCRT.StopAtExitLevyProkhorov.stoppedExitCurve (ball (0 : ℂ) r)) =
          (planarBrownianMotion z).map
            (MatedCRT.StopAtExitLevyProkhorov.stoppedExitCurve (ball (0 : ℂ) r)) := by
    intro γ hγ hγ2 Ω _ S hS η' hη' hae ε hε0 hε ν₂ hν₂ hlaw
    filter_upwards [FirstPass.Derived.ae_forall_map_stoppedExitCurve_eq_of_tendsto_law_interpWalkLaw hEnvS hN4
      h1 h10 hU hγ hγ2 hS hη' hae hε0 hε hlaw] with P hP z
    exact Filter.Eventually.of_forall fun r hr => hP z r hr
  exact randomWalkToLBMStmt_of_markovLimit_derived_hN5c h1 h2 hN4 h10 hN8' hN5c hN9

end MatedCRT
