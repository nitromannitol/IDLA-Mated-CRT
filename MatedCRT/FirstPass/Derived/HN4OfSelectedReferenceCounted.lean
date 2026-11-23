import MatedCRT.FirstPass.Derived.HN8OfRevuzLintegralGlue
import MatedCRT.FirstPass.Derived.GMS21UniformStartOfSelectedCell

/-!
# Theorems 1.4 and 1.6 with the uniform-start invariance principle from Gwynne–Miller–Sheffield Theorem 3.4

The counted forms `closed_1_4_quantumConeScaling_coneDimension_markovLimit_noHN5_noHN8` and
`closed_1_6_quantumConeScaling_coneDimension_markovLimit_noHN5_noHN8` take the premises `h1 h2 hN4 h10 hN9`. Here
`hN4 : GMS21UniformStartInput 𝒮` is supplied by `gms21UniformStartInput_of_selected_reference` from `h1`, `h2` and
the premise `hTutte`: for each `0 < γ < 2`, one valid environment of a model with the normalized space-filling SLE law
`ν` whose (curve, edge multiplicities) law satisfies the selected-cell comparison of Gwynne–Miller–Sheffield
(arXiv:1705.11161), Theorem 3.4, plane case, at the cell masses `1/n` (`uniformStartSelectedData`).

## Main results

* `closed_1_4_quantumConeScaling_coneDimension_markovLimit_noHN5_noHN8_tutte`: Theorem 1.4 from
  `h1 h2 hTutte h10 hN9`.
* `closed_1_6_quantumConeScaling_coneDimension_markovLimit_noHN5_noHN8_tutte`: Theorem 1.6 from
  `h1 h2 hTutte h10 hN9`.
* `closed_1_4_quantumConeScaling_coneDimension_markovLimit_noHN5_noHN8_tutteBall`,
  `closed_1_6_quantumConeScaling_coneDimension_markovLimit_noHN5_noHN8_tutteBall`: the same with `hTutteBall`, the
  comparison of the walk and the Brownian motion stopped at their exits from the ball (`uniformStartSelectedBallData`)
  established in the proof of Gwynne–Miller–Sheffield, Theorem 3.4, case 1.
-/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory MarkovProcess Set Filter Topology Metric
open _root_.HarmonicBalls _root_.MatedCRTHarmonic.MatedCRT
open scoped NNReal ENNReal BoundedContinuousFunction
open MatedCRT.FirstPass.Derived (LQGData LQGData.toMeasure)

/-- **Theorem 1.4** in the counted form `closed_1_4_quantumConeScaling_coneDimension_markovLimit_noHN5_noHN8`, with
`hN4` supplied by `gms21UniformStartInput_of_selected_reference` from `h1`, `h2` and `hTutte` (Gwynne–Miller–Sheffield,
arXiv:1705.11161, Theorem 3.4, on one reference environment of the law `ν`). The premises are `h1 h2 hTutte h10 hN9`.
Same conclusion. -/
theorem closed_1_4_quantumConeScaling_coneDimension_markovLimit_noHN5_noHN8_tutte {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (h1 : HasNormalizedSLELaw 𝒮 ν) (h2 : SLEModelClosureInput 𝒮)
    (hTutte : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ 𝒮₀ : SpaceFillingSLEModel, HasNormalizedSLELaw 𝒮₀ ν ∧
      ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (S₀ : MatedCRTEnv Ω₀), S₀.IsValid 𝒮₀ γ ∧
      ∃ η₀ : Ω₀ → C(ℝ, ℂ), Measurable η₀ ∧ (∀ᵐ ω ∂S₀.P, ⇑(η₀ ω) = S₀.η ω) ∧
      ∀ R ρ : ℝ, 0 < ρ → ρ < R → ∀ κ : ℝ, 0 < κ → ∀ θ : ℝ, 0 < θ →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          S₀.P.map (fun ω => (η₀ ω, S₀.mult (1 / (n : ℝ)) ω))
            (uniformStartSelectedData (1 / (n : ℝ)) ρ R κ)ᶜ ≤ ENNReal.ofReal θ)
    (h10 : HasReferenceEnvironments 𝒮)
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
  closed_1_4_quantumConeScaling_coneDimension_markovLimit_noHN5_noHN8 ν h1 h2
    (gms21UniformStartInput_of_selected_reference h1 h2 hTutte) h10 hN9

/-- **Theorem 1.6** in the counted form `closed_1_6_quantumConeScaling_coneDimension_markovLimit_noHN5_noHN8`, with
`hN4` supplied by `gms21UniformStartInput_of_selected_reference` from `h1`, `h2` and `hTutte` (Gwynne–Miller–Sheffield,
arXiv:1705.11161, Theorem 3.4, on one reference environment of the law `ν`). The premises are `h1 h2 hTutte h10 hN9`.
Same conclusion. -/
theorem closed_1_6_quantumConeScaling_coneDimension_markovLimit_noHN5_noHN8_tutte {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (h1 : HasNormalizedSLELaw 𝒮 ν) (h2 : SLEModelClosureInput 𝒮)
    (hTutte : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ 𝒮₀ : SpaceFillingSLEModel, HasNormalizedSLELaw 𝒮₀ ν ∧
      ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (S₀ : MatedCRTEnv Ω₀), S₀.IsValid 𝒮₀ γ ∧
      ∃ η₀ : Ω₀ → C(ℝ, ℂ), Measurable η₀ ∧ (∀ᵐ ω ∂S₀.P, ⇑(η₀ ω) = S₀.η ω) ∧
      ∀ R ρ : ℝ, 0 < ρ → ρ < R → ∀ κ : ℝ, 0 < κ → ∀ θ : ℝ, 0 < θ →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          S₀.P.map (fun ω => (η₀ ω, S₀.mult (1 / (n : ℝ)) ω))
            (uniformStartSelectedData (1 / (n : ℝ)) ρ R κ)ᶜ ≤ ENNReal.ofReal θ)
    (h10 : HasReferenceEnvironments 𝒮)
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
  closed_1_6_quantumConeScaling_coneDimension_markovLimit_noHN5_noHN8 ν h1 h2
    (gms21UniformStartInput_of_selected_reference h1 h2 hTutte) h10 hN9

/-- **Theorem 1.4** in the counted form `closed_1_4_quantumConeScaling_coneDimension_markovLimit_noHN5_noHN8`, with
`hN4` supplied by `gms21UniformStartInput_of_selectedBall_reference` from `h1`, `h2` and `hTutteBall` (the comparison of the
stopped curves established in the proof of Gwynne–Miller–Sheffield, arXiv:1705.11161, Theorem 3.4, case 1, on one
reference environment of the law `ν`). The premises are `h1 h2 hTutteBall h10 hN9`.
Same conclusion. -/
theorem closed_1_4_quantumConeScaling_coneDimension_markovLimit_noHN5_noHN8_tutteBall {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (h1 : HasNormalizedSLELaw 𝒮 ν) (h2 : SLEModelClosureInput 𝒮)
    (hTutteBall : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ 𝒮₀ : SpaceFillingSLEModel, HasNormalizedSLELaw 𝒮₀ ν ∧
      ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (S₀ : MatedCRTEnv Ω₀), S₀.IsValid 𝒮₀ γ ∧
      ∃ η₀ : Ω₀ → C(ℝ, ℂ), Measurable η₀ ∧ (∀ᵐ ω ∂S₀.P, ⇑(η₀ ω) = S₀.η ω) ∧
      ∀ R ρ : ℝ, 0 < ρ → ρ < R → ∀ κ : ℝ, 0 < κ → ∀ θ : ℝ, 0 < θ →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          S₀.P.map (fun ω => (η₀ ω, S₀.mult (1 / (n : ℝ)) ω))
            (uniformStartSelectedBallData (1 / (n : ℝ)) ρ R κ)ᶜ ≤ ENNReal.ofReal θ)
    (h10 : HasReferenceEnvironments 𝒮)
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
  closed_1_4_quantumConeScaling_coneDimension_markovLimit_noHN5_noHN8 ν h1 h2
    (gms21UniformStartInput_of_selectedBall_reference h1 h2 hTutteBall) h10 hN9

/-- **Theorem 1.6** in the counted form `closed_1_6_quantumConeScaling_coneDimension_markovLimit_noHN5_noHN8`, with
`hN4` supplied by `gms21UniformStartInput_of_selectedBall_reference` from `h1`, `h2` and `hTutteBall` (the comparison of the
stopped curves established in the proof of Gwynne–Miller–Sheffield, arXiv:1705.11161, Theorem 3.4, case 1, on one
reference environment of the law `ν`). The premises are `h1 h2 hTutteBall h10 hN9`.
Same conclusion. -/
theorem closed_1_6_quantumConeScaling_coneDimension_markovLimit_noHN5_noHN8_tutteBall {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (h1 : HasNormalizedSLELaw 𝒮 ν) (h2 : SLEModelClosureInput 𝒮)
    (hTutteBall : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ 𝒮₀ : SpaceFillingSLEModel, HasNormalizedSLELaw 𝒮₀ ν ∧
      ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (S₀ : MatedCRTEnv Ω₀), S₀.IsValid 𝒮₀ γ ∧
      ∃ η₀ : Ω₀ → C(ℝ, ℂ), Measurable η₀ ∧ (∀ᵐ ω ∂S₀.P, ⇑(η₀ ω) = S₀.η ω) ∧
      ∀ R ρ : ℝ, 0 < ρ → ρ < R → ∀ κ : ℝ, 0 < κ → ∀ θ : ℝ, 0 < θ →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          S₀.P.map (fun ω => (η₀ ω, S₀.mult (1 / (n : ℝ)) ω))
            (uniformStartSelectedBallData (1 / (n : ℝ)) ρ R κ)ᶜ ≤ ENNReal.ofReal θ)
    (h10 : HasReferenceEnvironments 𝒮)
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
  closed_1_6_quantumConeScaling_coneDimension_markovLimit_noHN5_noHN8 ν h1 h2
    (gms21UniformStartInput_of_selectedBall_reference h1 h2 hTutteBall) h10 hN9

end MatedCRT
