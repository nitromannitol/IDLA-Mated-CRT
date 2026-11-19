import MatedCRT.FirstPass.Derived.ExitReparamAssembly
import MatedCRT.FirstPass.Derived.HN5OfContinuousTimeChange
import MatedCRT.FirstPass.Derived.ConvergenceOfIDLAOfMarkovLimitHN5b

/-!
# Lemma 7.4 from the stopped class laws of the limit

Berestycki–Gwynne (2020), proof of Lemma 7.4.  A subsequential limit `P` of the interpolated walk laws is
identified with Brownian motion modulo time parametrization once, for every starting point `z`, the stopped
curve class at the first exit from the ball of radius `r` of `P z` has the planar Brownian law, for almost every
radius `r > ‖z‖`.  This is the explicit remaining statement `hN5c` below (a hypothesis of the theorems of this
file, not a new `Prop`); the passage from `hN5c` to the binder `hN5a` of `hN5_of_defines` is a theorem:

* the absence of flat intervals of `P z` is `ae_forall_apply_constantOnInterval_eq_zero_of_tendsto_law_interpWalkLaw`;
* the time-change coupling with strictly increasing `τ` is `ExitReparamAssembly.definesTimeChangedBM_of_exitClassLaws`.

* `hN5a_of_exitClassLaws`: the binder `hN5a` of `hN5_of_defines` from `hN5c`;
* `randomWalkToLBMStmt_of_markovLimit_derived_hN5c`: `h11` with `hN5` replaced by `hN5c`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Metric MarkovProcess
open _root_.HarmonicBalls _root_.MatedCRTHarmonic.MatedCRT
open scoped NNReal ENNReal BoundedContinuousFunction
open MatedCRT.FirstPass.Derived (LQGData LQGData.toMeasure)

namespace MatedCRT.FirstPass.Derived

/-- **The binder `hN5a` from the stopped class laws of the limit** (Berestycki–Gwynne (2020), Lemma 7.4).
The hypothesis `hN5c`: for almost every subsequential limit `P` of the interpolated walk laws, every `z` and
almost every radius `r > ‖z‖`, the law under `P z` of the path stopped at the first exit from `ball 0 r`
(taken modulo time parametrization) is that of planar Brownian motion from `z`. -/
theorem hN5a_of_exitClassLaws {𝒮 : SpaceFillingSLEModel} {ν : ℝ → Measure SLEPathCode}
    (hEnvS : ConeEnvironmentScalingStep 𝒮) (hN4 : GMS21UniformStartInput 𝒮)
    (hν : HasNormalizedSLELaw 𝒮 ν) (href : HasReferenceEnvironments 𝒮)
    (hU : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ G : Set MatedCRTHarmonic.MatedCRT.Path2,
      (∀ μ : Measure MatedCRTHarmonic.MatedCRT.Path2, MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ μ →
        μ Gᶜ = 0) ∧ MatingRigidLEOn G)
    (hN5c : ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
      ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ ν₂ : Measure PathLawFamily, IsProbabilityMeasure ν₂ →
      (∀ f : PathLawFamily →ᵇ ℝ,
        Tendsto (fun n => ∫ ω, f (interpWalkLaw S η' (ε n) ω) ∂S.P) atTop (𝓝 (∫ P, f P ∂ν₂))) →
      ∀ᵐ P ∂ν₂, ∀ z : ℂ, ∀ᵐ r ∂(volume : Measure ℝ), ‖z‖ < r →
        ((P z : ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ)).map
          (MatedCRT.StopAtExitLevyProkhorov.stoppedExitCurve (ball (0 : ℂ) r)) =
        (planarBrownianMotion z).map
          (MatedCRT.StopAtExitLevyProkhorov.stoppedExitCurve (ball (0 : ℂ) r))) :
    ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
      ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ ν₂ : Measure PathLawFamily, IsProbabilityMeasure ν₂ →
      (∀ f : PathLawFamily →ᵇ ℝ,
        Tendsto (fun n => ∫ ω, f (interpWalkLaw S η' (ε n) ω) ∂S.P) atTop (𝓝 (∫ P, f P ∂ν₂))) →
      ∀ᵐ P ∂ν₂, DefinesTimeChangedBM P := by
  intro γ hγ hγ2 Ω _ S hS η' hη' hae ε hε0 hε ν₂ hν₂ hlaw
  filter_upwards [hN5c γ hγ hγ2 Ω S hS η' hη' hae ε hε0 hε ν₂ hν₂ hlaw,
    ae_forall_apply_constantOnInterval_eq_zero_of_tendsto_law_interpWalkLaw hEnvS hN4 hν href hU hγ hγ2
      hS hη' hae hε0 hε hlaw] with P h1 h2
  exact MatedCRT.ExitReparamAssembly.definesTimeChangedBM_of_exitClassLaws P h2 h1

end MatedCRT.FirstPass.Derived

namespace MatedCRT

/-- **`h11` with Lemma 7.4 reduced to the stopped class laws of the limit.**
`randomWalkToLBMStmt_of_markovLimit_derived` with the premise `hN5` replaced by `hN5c`: for almost every
subsequential limit `P` of the interpolated walk laws, every `z` and almost every radius `r > ‖z‖`, the law
under `P z` of the stopped curve class at the first exit from `ball 0 r` is that of planar Brownian motion
from `z`.  Every other premise is unchanged. -/
theorem randomWalkToLBMStmt_of_markovLimit_derived_hN5c {𝒮 : SpaceFillingSLEModel}
    {ν : ℝ → Measure SLEPathCode}
    (h1 : HasNormalizedSLELaw 𝒮 ν) (h2 : SLEModelClosureInput 𝒮) (hN4 : GMS21UniformStartInput 𝒮)
    (h10 : HasReferenceEnvironments 𝒮)
    (hN8' : ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
      ∀ E : Ω → LQGData, Measurable E → (∀ᵐ ω ∂S.P, LQGData.toMeasure (E ω) = S.μ ω) →
      ∀ᵐ d ∂(S.P.map fun ω => (LQGMetric.pairJ ⊤ (H ω), E ω)),
        IsMarkovTCBM (lbmPathLawField γ d.1) ∧ IsInvariantFor (lbmPathLawField γ d.1) (LQGData.toMeasure d.2))
    (hN5c : ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
      ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ ν₂ : Measure PathLawFamily, IsProbabilityMeasure ν₂ →
      (∀ f : PathLawFamily →ᵇ ℝ,
        Tendsto (fun n => ∫ ω, f (interpWalkLaw S η' (ε n) ω) ∂S.P) atTop (𝓝 (∫ P, f P ∂ν₂))) →
      ∀ᵐ P ∂ν₂, ∀ z : ℂ, ∀ᵐ r ∂(volume : Measure ℝ), ‖z‖ < r →
        ((P z : ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ)).map
          (MatedCRT.StopAtExitLevyProkhorov.stoppedExitCurve (ball (0 : ℂ) r)) =
        (planarBrownianMotion z).map
          (MatedCRT.StopAtExitLevyProkhorov.stoppedExitCurve (ball (0 : ℂ) r)))
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
  exact randomWalkToLBMStmt_of_markovLimit_derived h1 h2 hN4 h10 hN8'
    (FirstPass.Derived.hN5_of_defines hEnvS hN4 h1 h10 hU
      (FirstPass.Derived.hN5a_of_exitClassLaws hEnvS hN4 h1 h10 hU hN5c)) hN9

end MatedCRT
