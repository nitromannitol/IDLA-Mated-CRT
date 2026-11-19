import MatedCRT.FirstPass.Derived.RandomWalkToLBMStmtOfLQGData
import MatedCRT.FirstPass.Derived.RandomWalkToLBMStmtOfBG20
import MatedCRT.FirstPass.Derived.EnvironmentScalingHolds
import MatedCRT.FirstPass.Derived.QuantumConeScalingDerived
import MatedCRT.FirstPass.Derived.QuantumConeScalingDimension
import MatedCRT.FirstPass.LPBridge.BrownianOutwardExcursion

/-!
# Theorems 1.4 and 1.6 from the Markovian time-change structure of the limiting walk laws

The counted forms `closed_1_4_quantumConeScaling_coneDimension_bg20ref` and
`closed_1_6_quantumConeScaling_coneDimension_bg20ref` take the convergence of the embedded random walk to Liouville
Brownian motion on one reference environment (Berestycki–Gwynne (2020), Theorem 1.2; binder `hBGref`). Here that
binder is replaced by three inputs of the proof of Berestycki–Gwynne Theorem 1.2, with the LQG measure coordinatized
by `LQGData` (`randomWalkToLBMStmt_of_markovLimit_lqgData`):

* `hN8'`: for almost every value `d` of the data `(pairJ ⊤ H, E)`, the Liouville Brownian law field
  `lbmPathLawField γ d.1` is a Markovian time change of Brownian motion leaving `d.2.toMeasure = μ_h` invariant
  (Liouville Brownian motion is the time change of Brownian motion by its positive continuous additive functional with
  Revuz measure `μ_h`, Garban–Rhodes–Vargas; a literature input);
* `hN5`: every subsequential weak limit of the interpolated walk laws is almost surely a Markovian time change of
  Brownian motion (Berestycki–Gwynne (2020), Lemma 7.4);
* `hN9`: if almost surely the limiting family is a linear time change of the Liouville Brownian law field, the
  time-change constant is deterministic (Berestycki–Gwynne (2020), Lemma 7.18).

No other input is added. The remaining premises of `randomWalkToLBMStmt_of_markovLimit_lqgData` are supplied as in
`randomWalkToLBMStmt_of_bg20_reference`: the environment scaling `hEnvS` from the quantum cone scaling
(`coneEnvironmentScalingUnderSLE_of_scaling`, `quantumConeScalingInput_derived` and the SLE closure inputs `h2`), the
rigidity pair `hU` from `exists_matingRigidLEOn_full_derived`, and the outward excursion of Brownian motion at its
exit time `hexit` from `frozenBrownianOutwardExcursionAtExit_holds`.

## Main statements

* `randomWalkToLBMStmt_of_markovLimit_derived`: `RandomWalkToLBMStmt 𝒮` from `h1 h2 hN4 h10 hN8' hN5 hN9`.
* `closed_1_4_quantumConeScaling_coneDimension_markovLimit`,
  `closed_1_6_quantumConeScaling_coneDimension_markovLimit`: Theorems 1.4 and 1.6 in the counted forms
  `closed_1_4_quantumConeScaling_coneDimension` and `closed_1_6_quantumConeScaling_coneDimension`, with `h11`
  supplied from `hN8'`, `hN5`, `hN9`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set MarkovProcess
open _root_.HarmonicBalls _root_.MatedCRTHarmonic.MatedCRT
open scoped NNReal ENNReal BoundedContinuousFunction
open MatedCRT.FirstPass.Derived (LQGData LQGData.toMeasure)

namespace MatedCRT

/-- **Theorem 2.11 (Berestycki–Gwynne (2020), Theorem 1.2) from the Markovian time-change structure of the limiting
walk laws.** The convergence of the walk to Liouville Brownian motion (the binder `hBGref` of
`randomWalkToLBMStmt_of_bg20_reference`) is replaced by

* `hN8'`: Liouville Brownian motion is a Markovian time change of Brownian motion leaving `μ_h` invariant
  (Garban–Rhodes–Vargas; a literature input);
* `hN5`: subsequential limits of the walk laws are Markovian time changes of Brownian motion (Berestycki–Gwynne
  (2020), Lemma 7.4);
* `hN9`: the time-change constant of a limit is deterministic (Berestycki–Gwynne (2020), Lemma 7.18).

No other input is added: `hEnvS`, `hU` and `hexit` of `randomWalkToLBMStmt_of_markovLimit_lqgData` are supplied by
`coneEnvironmentScalingUnderSLE_of_scaling`, `exists_matingRigidLEOn_full_derived` and
`frozenBrownianOutwardExcursionAtExit_holds`. -/
theorem randomWalkToLBMStmt_of_markovLimit_derived {𝒮 : SpaceFillingSLEModel} {ν : ℝ → Measure SLEPathCode}
    (h1 : HasNormalizedSLELaw 𝒮 ν) (h2 : SLEModelClosureInput 𝒮) (hN4 : GMS21UniformStartInput 𝒮)
    (h10 : HasReferenceEnvironments 𝒮)
    (hN8' : ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
      ∀ E : Ω → LQGData, Measurable E → (∀ᵐ ω ∂S.P, LQGData.toMeasure (E ω) = S.μ ω) →
      ∀ᵐ d ∂(S.P.map fun ω => (LQGMetric.pairJ ⊤ (H ω), E ω)),
        IsMarkovTCBM (lbmPathLawField γ d.1) ∧ IsInvariantFor (lbmPathLawField γ d.1) (LQGData.toMeasure d.2))
    (hN5 : ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
      ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ ν₂ : Measure PathLawFamily, IsProbabilityMeasure ν₂ →
      (∀ f : PathLawFamily →ᵇ ℝ,
        Tendsto (fun n => ∫ ω, f (interpWalkLaw S η' (ε n) ω) ∂S.P) atTop (𝓝 (∫ P, f P ∂ν₂))) →
      ∀ᵐ P ∂ν₂, IsMarkovTCBM P)
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
  exact FirstPass.Derived.randomWalkToLBMStmt_of_markovLimit_lqgData
    (coneEnvironmentScalingUnderSLE_of_scaling 𝒮 FirstPass.Derived.quantumConeScalingInput_derived
      h2.1 h2.2.1 h2.2.2)
    hN4 h1 h10 (fun γ hγ0 hγ2 => ⟨G, hGnull γ hγ0 hγ2, hG⟩) frozenBrownianOutwardExcursionAtExit_holds
    hN8' hN5 hN9

/-- **Theorem 1.4** in the counted form `closed_1_4_quantumConeScaling_coneDimension`, with the convergence of the
embedded random walk to Liouville Brownian motion (`h11`) supplied by `randomWalkToLBMStmt_of_markovLimit_derived`.
The binder `hBGref` of `closed_1_4_quantumConeScaling_coneDimension_bg20ref` (Berestycki–Gwynne (2020),
Theorem 1.2) is replaced by `hN8'` (Liouville Brownian motion is a Markovian time change of Brownian motion leaving
`μ_h` invariant, Garban–Rhodes–Vargas; a literature input), `hN5` (Berestycki–Gwynne (2020), Lemma 7.4) and `hN9`
(Berestycki–Gwynne (2020), Lemma 7.18); no other input. Same conclusion. -/
theorem closed_1_4_quantumConeScaling_coneDimension_markovLimit
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (h1 : HasNormalizedSLELaw 𝒮 ν) (h2 : SLEModelClosureInput 𝒮)
    (hN4 : GMS21UniformStartInput 𝒮)
    (h10 : HasReferenceEnvironments 𝒮)
    (hN8' : ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
      ∀ E : Ω → LQGData, Measurable E → (∀ᵐ ω ∂S.P, LQGData.toMeasure (E ω) = S.μ ω) →
      ∀ᵐ d ∂(S.P.map fun ω => (LQGMetric.pairJ ⊤ (H ω), E ω)),
        IsMarkovTCBM (lbmPathLawField γ d.1) ∧ IsInvariantFor (lbmPathLawField γ d.1) (LQGData.toMeasure d.2))
    (hN5 : ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
      ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ ν₂ : Measure PathLawFamily, IsProbabilityMeasure ν₂ →
      (∀ f : PathLawFamily →ᵇ ℝ,
        Tendsto (fun n => ∫ ω, f (interpWalkLaw S η' (ε n) ω) ∂S.P) atTop (𝓝 (∫ P, f P ∂ν₂))) →
      ∀ᵐ P ∂ν₂, IsMarkovTCBM P)
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
    ConvergenceOfIDLAStmt 𝒮 :=
  closed_1_4_quantumConeScaling_coneDimension ν h1 h2 hN4 h10
    (randomWalkToLBMStmt_of_markovLimit_derived h1 h2 hN4 h10 hN8' hN5 hN9)

/-- **Theorem 1.6** in the counted form `closed_1_6_quantumConeScaling_coneDimension`, with the convergence of the
embedded random walk to Liouville Brownian motion (`h11`) supplied by `randomWalkToLBMStmt_of_markovLimit_derived`.
The binder `hBGref` of `closed_1_6_quantumConeScaling_coneDimension_bg20ref` (Berestycki–Gwynne (2020),
Theorem 1.2) is replaced by `hN8'` (Liouville Brownian motion is a Markovian time change of Brownian motion leaving
`μ_h` invariant, Garban–Rhodes–Vargas; a literature input), `hN5` (Berestycki–Gwynne (2020), Lemma 7.4) and `hN9`
(Berestycki–Gwynne (2020), Lemma 7.18); no other input. Same conclusion. -/
theorem closed_1_6_quantumConeScaling_coneDimension_markovLimit
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (h1 : HasNormalizedSLELaw 𝒮 ν) (h2 : SLEModelClosureInput 𝒮)
    (hN4 : GMS21UniformStartInput 𝒮)
    (h10 : HasReferenceEnvironments 𝒮)
    (hN8' : ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
      ∀ E : Ω → LQGData, Measurable E → (∀ᵐ ω ∂S.P, LQGData.toMeasure (E ω) = S.μ ω) →
      ∀ᵐ d ∂(S.P.map fun ω => (LQGMetric.pairJ ⊤ (H ω), E ω)),
        IsMarkovTCBM (lbmPathLawField γ d.1) ∧ IsInvariantFor (lbmPathLawField γ d.1) (LQGData.toMeasure d.2))
    (hN5 : ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
      ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ ν₂ : Measure PathLawFamily, IsProbabilityMeasure ν₂ →
      (∀ f : PathLawFamily →ᵇ ℝ,
        Tendsto (fun n => ∫ ω, f (interpWalkLaw S η' (ε n) ω) ∂S.P) atTop (𝓝 (∫ P, f P ∂ν₂))) →
      ∀ᵐ P ∂ν₂, IsMarkovTCBM P)
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
    ConvergenceOfDivSandpileStmt 𝒮 :=
  closed_1_6_quantumConeScaling_coneDimension ν h1 h2 hN4 h10
    (randomWalkToLBMStmt_of_markovLimit_derived h1 h2 hN4 h10 hN8' hN5 hN9)

end MatedCRT
