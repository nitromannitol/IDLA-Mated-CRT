import MatedCRT.FirstPass.Derived.HN5OfContinuousTimeChange
import MatedCRT.FirstPass.Derived.HN5OfDefinesTimeChange
import MatedCRT.FirstPass.Derived.ConvergenceOfIDLAOfMarkovLimit

/-!
# The convergence of the embedded random walk, with Lemma 7.4 reduced to a continuous time change

`randomWalkToLBMStmt_of_markovLimit_derived` takes the premise `hN5` (Berestycki–Gwynne (2020), Lemma 7.4:
every subsequential limit of the interpolated walk laws is almost surely a Markovian time change of Brownian
motion).  Its Markov half is a theorem (`MatedCRT.FirstPass.Derived.hN5_of_defines`) and the strict monotonicity of
the time change follows from the absence of flat intervals (`hN5a_of_continuousTimeChange`).  What remains is
`hN5b`: a subsequential limit is almost surely a continuous nondecreasing time change of Brownian motion
(from [GMS21, Theorem 3.4], the continuity of the passage to curves modulo time parametrization, and a coupling).
Every other premise is unchanged.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set MarkovProcess
open _root_.HarmonicBalls _root_.MatedCRTHarmonic.MatedCRT
open scoped NNReal ENNReal BoundedContinuousFunction
open MatedCRT.FirstPass.Derived (LQGData LQGData.toMeasure)

namespace MatedCRT

/-- **`h11` with Lemma 7.4 reduced to a continuous time change.**  `randomWalkToLBMStmt_of_markovLimit_derived`
with the premise `hN5` replaced by `hN5b`: a subsequential limit of the interpolated walk laws is almost surely a
continuous nondecreasing time change of Brownian motion (the definition `DefinesTimeChangedBM` with `Monotone`
in place of `StrictMono`). -/
theorem randomWalkToLBMStmt_of_markovLimit_derived_hN5b {𝒮 : SpaceFillingSLEModel}
    {ν : ℝ → Measure SLEPathCode}
    (h1 : HasNormalizedSLELaw 𝒮 ν) (h2 : SLEModelClosureInput 𝒮) (hN4 : GMS21UniformStartInput 𝒮)
    (h10 : HasReferenceEnvironments 𝒮)
    (hN8' : ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
      ∀ E : Ω → LQGData, Measurable E → (∀ᵐ ω ∂S.P, LQGData.toMeasure (E ω) = S.μ ω) →
      ∀ᵐ d ∂(S.P.map fun ω => (LQGMetric.pairJ ⊤ (H ω), E ω)),
        IsMarkovTCBM (lbmPathLawField γ d.1) ∧ IsInvariantFor (lbmPathLawField γ d.1) (LQGData.toMeasure d.2))
    (hN5b : ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
      ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ ν₂ : Measure PathLawFamily, IsProbabilityMeasure ν₂ →
      (∀ f : PathLawFamily →ᵇ ℝ,
        Tendsto (fun n => ∫ ω, f (interpWalkLaw S η' (ε n) ω) ∂S.P) atTop (𝓝 (∫ P, f P ∂ν₂))) →
      ∀ᵐ P ∂ν₂, ∀ z : ℂ, ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (Q : Measure Ω') (_ : IsProbabilityMeasure Q)
          (B X : Ω' → ContinuousPath ℂ) (τ : Ω' → ℝ≥0 → ℝ≥0),
        AEMeasurable B Q ∧ AEMeasurable X Q ∧ Q.map B = planarLaw z ∧
        (∀ᵐ ω ∂Q, Continuous (τ ω) ∧ Monotone (τ ω) ∧ τ ω 0 = 0 ∧ ∀ u, X ω u = B ω (τ ω u)) ∧
        (P z : Measure (ContinuousPath ℂ)) = Q.map X)
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
      (FirstPass.Derived.hN5a_of_continuousTimeChange hEnvS hN4 h1 h10 hU hN5b)) hN9

end MatedCRT
