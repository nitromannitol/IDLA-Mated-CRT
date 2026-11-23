import MatedCRT.FirstPass.Derived.CanonicalCountedFormsOneStart
import MatedCRT.FirstPass.Derived.HN4OfSelectedReferenceCounted
import MatedCRT.FirstPass.Derived.HN9OfChartField
import HarmonicBalls.Proofs.Potential.LQGClockOneStartSubcritical
import HarmonicBalls.Proofs.Potential.LQGClockExteriorClockConvergence

/-!
# Theorems 1.4 and 1.6 at the canonical model with the Gaussian Liouville clock statements proved

The two statements on the Liouville clock of the whole-plane GFF of `LatticeProb.Gauss` that give the reference
environments of the canonical model (`CanonicalCountedFormsOneStart`), at the insertion `α = 0`:

* the one-start event, for every `0 < γ < 2`: `gaussianClock_oneStart`, from
  `HarmonicBalls.ae_forall_rat_ae_dyadicIncrementLiminf_pos_of_lt_two` (the analogue of Berestycki 2015,
  Theorem 1.2), whose `dyadicIncrementLiminf` unfolds to the lower limit of the dyadic increments;
* the locally uniform limit of the dyadic clocks from every start: for `γ² < 2` by
  `HarmonicBalls.ae_exists_locally_uniform_limit_clock_nonpositive`. That theorem needs `γ² < 2` (its half-disc part
  rests on second moments of pair energies), so for `2 ≤ γ² < 4` the statement remains a premise
  (`gaussianClock_localLimit`, `hlocHigh`).

With the reductions of `hN4` to `hTutteLP` (`gms21UniformStartInput_of_selectedLP_reference`) and of `hN9` to
`BG20ChartFieldInput` (`hN9_of_bg20ChartField`), Theorems 1.4 and 1.6 at the canonical model follow from the
couplings, `hlocHigh`, `hTutteLP` and `BG20ChartFieldInput`.

## Main statements

* `gaussianClock_oneStart`, `gaussianClock_localLimit`: the two clock statements.
* `closed_1_4_quantumConeScaling_coneDimension_markovLimit_noHN5_noHN8_tutteLP_chartField`,
  `closed_1_6_quantumConeScaling_coneDimension_markovLimit_noHN5_noHN8_tutteLP_chartField`: the counted forms for an
  arbitrary model from `h1 h2 hTutteLP h10 hC`.
* `closed_1_4_quantumConeScaling_coneDimension_markovLimit_canonical_of_coupling_tutteLP_chartField`,
  `closed_1_6_quantumConeScaling_coneDimension_markovLimit_canonical_of_coupling_tutteLP_chartField`: the counted forms
  at the canonical model from `hcpl hlocHigh hTutteLP hC`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set MarkovProcess
open _root_.HarmonicBalls _root_.LQGMetric _root_.MatedCRTHarmonic _root_.MatedCRTHarmonic.MatedCRT
open scoped NNReal ENNReal BoundedContinuousFunction
open MatedCRT.FirstPass.Derived (LQGData LQGData.toMeasure)

namespace MatedCRT

/-- **Theorem 1.4 from `h1 h2 hTutteLP h10 hC`.** The counted form
`closed_1_4_quantumConeScaling_coneDimension_markovLimit_noHN5_noHN8` with `hN4` supplied by
`gms21UniformStartInput_of_selectedLP_reference` from `h1`, `h2` and `hTutteLP`, and `hN9` by `hN9_of_bg20ChartField`
from `BG20ChartFieldInput`. Same conclusion. -/
theorem closed_1_4_quantumConeScaling_coneDimension_markovLimit_noHN5_noHN8_tutteLP_chartField
    {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode)
    (h1 : HasNormalizedSLELaw 𝒮 ν) (h2 : SLEModelClosureInput 𝒮)
    (hTutteLP : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ 𝒮₀ : SpaceFillingSLEModel, HasNormalizedSLELaw 𝒮₀ ν ∧
      ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (S₀ : MatedCRTEnv Ω₀), S₀.IsValid 𝒮₀ γ ∧
      ∃ η₀ : Ω₀ → C(ℝ, ℂ), Measurable η₀ ∧ (∀ᵐ ω ∂S₀.P, ⇑(η₀ ω) = S₀.η ω) ∧
      ∀ R ρ : ℝ, 0 < ρ → ρ < R → ∀ κ : ℝ, 0 < κ → ∀ θ : ℝ, 0 < θ →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          S₀.P.map (fun ω => (η₀ ω, S₀.mult (1 / (n : ℝ)) ω))
            (uniformStartSelectedLPData (1 / (n : ℝ)) ρ R κ)ᶜ ≤ ENNReal.ofReal θ)
    (h10 : HasReferenceEnvironments 𝒮) (hC : BG20ChartFieldInput 𝒮) :
    ConvergenceOfIDLAStmt 𝒮 :=
  closed_1_4_quantumConeScaling_coneDimension_markovLimit_noHN5_noHN8 ν h1 h2
    (gms21UniformStartInput_of_selectedLP_reference h1 h2 hTutteLP) h10 (hN9_of_bg20ChartField hC)

/-- **Theorem 1.6 from `h1 h2 hTutteLP h10 hC`.** The counted form
`closed_1_6_quantumConeScaling_coneDimension_markovLimit_noHN5_noHN8` with `hN4` supplied by
`gms21UniformStartInput_of_selectedLP_reference` from `h1`, `h2` and `hTutteLP`, and `hN9` by `hN9_of_bg20ChartField`
from `BG20ChartFieldInput`. Same conclusion. -/
theorem closed_1_6_quantumConeScaling_coneDimension_markovLimit_noHN5_noHN8_tutteLP_chartField
    {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode)
    (h1 : HasNormalizedSLELaw 𝒮 ν) (h2 : SLEModelClosureInput 𝒮)
    (hTutteLP : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ 𝒮₀ : SpaceFillingSLEModel, HasNormalizedSLELaw 𝒮₀ ν ∧
      ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (S₀ : MatedCRTEnv Ω₀), S₀.IsValid 𝒮₀ γ ∧
      ∃ η₀ : Ω₀ → C(ℝ, ℂ), Measurable η₀ ∧ (∀ᵐ ω ∂S₀.P, ⇑(η₀ ω) = S₀.η ω) ∧
      ∀ R ρ : ℝ, 0 < ρ → ρ < R → ∀ κ : ℝ, 0 < κ → ∀ θ : ℝ, 0 < θ →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          S₀.P.map (fun ω => (η₀ ω, S₀.mult (1 / (n : ℝ)) ω))
            (uniformStartSelectedLPData (1 / (n : ℝ)) ρ R κ)ᶜ ≤ ENNReal.ofReal θ)
    (h10 : HasReferenceEnvironments 𝒮) (hC : BG20ChartFieldInput 𝒮) :
    ConvergenceOfDivSandpileStmt 𝒮 :=
  closed_1_6_quantumConeScaling_coneDimension_markovLimit_noHN5_noHN8 ν h1 h2
    (gms21UniformStartInput_of_selectedLP_reference h1 h2 hTutteLP) h10 (hN9_of_bg20ChartField hC)

end MatedCRT

namespace MatedCRT.FirstPass.Derived

/-- **The one-start event for every `0 < γ < 2`** at the insertion `0`: for every whole-plane GFF of
`LatticeProb.Gauss`, almost surely in the field, for all rationals `0 < a < b`, from the origin, almost surely the
lower limit of the dyadic increments `∫_a^b ε_k^{γ²/2} e^{γ h_{ε_k}(w_v)} dv` is positive
(`HarmonicBalls.ae_forall_rat_ae_dyadicIncrementLiminf_pos_of_lt_two`). -/
theorem gaussianClock_oneStart : ∀ γ : ℝ, 0 < γ → γ < 2 →
    ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
      {hcirc : Ω → ℝ → ℂ → ℝ}, LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc →
      ∀ᵐ ω ∂P, ∀ a b : ℚ, 0 < a → a < b → ∀ᵐ w ∂(planarBrownianMotion 0),
        0 < liminf (fun k => ENNReal.ofReal (∫ v in (a : ℝ)..(b : ℝ),
          HarmonicBalls.dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage 0 (hcirc ω) (HarmonicBalls.dyadicScale k)
              (w v.toNNReal)))) atTop := by
  intro γ hγ0 hγ2 Ω _ P hC hcirc hh
  exact HarmonicBalls.ae_forall_rat_ae_dyadicIncrementLiminf_pos_of_lt_two hh hγ0 hγ2 0

/-- **The locally uniform limit of the dyadic Liouville clocks** at the insertion `0`, for every `0 < γ < 2`: proved
for `γ² < 2` (`HarmonicBalls.ae_exists_locally_uniform_limit_clock_nonpositive`), and taken from `hlocHigh` for
`2 ≤ γ² < 4`. -/
theorem gaussianClock_localLimit
    (hlocHigh : ∀ γ : ℝ, 2 ≤ γ ^ 2 → γ < 2 →
        ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
          {hcirc : Ω → ℝ → ℂ → ℝ}, LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc → ∀ x : ℂ,
          ∀ᵐ q ∂(P.prod (planarBrownianMotion x)),
            ∃ F : ℝ≥0 → ℝ, Continuous F ∧ (∀ t, 0 ≤ F t) ∧ Monotone F ∧
              ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ t : ℝ≥0, t ≤ T →
                |(∫ s in (0 : ℝ)..(t : ℝ), HarmonicBalls.dyadicScale (n + 1) ^ (γ ^ 2 / 2) * Real.exp (γ *
                  LatticeProb.Gauss.fieldCircleAverage 0 (hcirc q.1) (HarmonicBalls.dyadicScale (n + 1))
                    (q.2 s.toNNReal))) - F t| < η) :
    ∀ γ : ℝ, 0 < γ → γ < 2 →
        ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
          {hcirc : Ω → ℝ → ℂ → ℝ}, LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc → ∀ x : ℂ,
          ∀ᵐ q ∂(P.prod (planarBrownianMotion x)),
            ∃ F : ℝ≥0 → ℝ, Continuous F ∧ (∀ t, 0 ≤ F t) ∧ Monotone F ∧
              ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ t : ℝ≥0, t ≤ T →
                |(∫ s in (0 : ℝ)..(t : ℝ), HarmonicBalls.dyadicScale (n + 1) ^ (γ ^ 2 / 2) * Real.exp (γ *
                  LatticeProb.Gauss.fieldCircleAverage 0 (hcirc q.1) (HarmonicBalls.dyadicScale (n + 1))
                    (q.2 s.toNNReal))) - F t| < η := by
  intro γ hγ0 hγ2 Ω _ P hC hcirc hh x
  by_cases hsq : γ ^ 2 < 2
  · exact HarmonicBalls.ae_exists_locally_uniform_limit_clock_nonpositive hh hγ0 hsq le_rfl x
  · exact hlocHigh γ (not_lt.1 hsq) hγ2 hh x

/-- **Theorem 1.4 at the canonical space-filling SLE model, from mating-of-trees couplings, `hTutteLP` and
`BG20ChartFieldInput`.** The counted form `closed_1_4_quantumConeScaling_coneDimension_markovLimit_noHN5_noHN8` at
`ProbeMi.canonicalSLEModel ν`, with
* `h1`, `h2` from the couplings (`hasNormalizedSLELaw_canonicalSLEModel_of_coupling`,
  `sleModelClosureInput_canonicalSLEModel_of_coupling`);
* `h10` from the couplings, `hfix` (`Sec1.wholePlane_fixedStart_uniformCauchy_of_localLimit`) and `hfixsm`
  (`Sec1.wholePlane_fixedStart_strictMono_of_oneStart`), these from the two Gaussian clock statements:
  the one-start event is `gaussianClock_oneStart` for every `γ ∈ (0, 2)`, the locally uniform limit is
  `gaussianClock_localLimit`, proved for `γ² < 2` and taken from `hlocHigh` for `2 ≤ γ² < 4`;
* `hN4` from `h1`, `h2` and `hTutteLP` (`gms21UniformStartInput_of_selectedLP_reference`);
* `hN9` from `BG20ChartFieldInput` (`hN9_of_bg20ChartField`).
Remaining premises: `hcpl` (couplings on `ℝ` with code law `ν (16/γ²)`), `hlocHigh` (the locally uniform limit of
the dyadic Liouville clocks for `√2 ≤ γ < 2`), `hTutteLP` and `hC`. -/
theorem closed_1_4_quantumConeScaling_coneDimension_markovLimit_canonical_of_coupling_tutteLP_chartField
    (ν : ℝ → Measure SLEPathCode)
    (hcpl : ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∃ (P : Measure ℝ) (X X₀ hIG₀ : ℝ → Field) (B B' B₀ B₀' : ℝ≥0 → ℝ → ℝ) (U : ℝ → ℝ)
        (ηL η η₀ : ℝ → C(ℝ, ℂ)) (bm : ℝ → Path2),
        IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm ∧
        P.map (fun ω => slePathCode (ηL ω)) = ν (16 / γ ^ 2))
    (hlocHigh : ∀ γ : ℝ, 2 ≤ γ ^ 2 → γ < 2 →
        ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
          {hcirc : Ω → ℝ → ℂ → ℝ}, LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc → ∀ x : ℂ,
          ∀ᵐ q ∂(P.prod (planarBrownianMotion x)),
            ∃ F : ℝ≥0 → ℝ, Continuous F ∧ (∀ t, 0 ≤ F t) ∧ Monotone F ∧
              ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ t : ℝ≥0, t ≤ T →
                |(∫ s in (0 : ℝ)..(t : ℝ), HarmonicBalls.dyadicScale (n + 1) ^ (γ ^ 2 / 2) * Real.exp (γ *
                  LatticeProb.Gauss.fieldCircleAverage 0 (hcirc q.1) (HarmonicBalls.dyadicScale (n + 1))
                    (q.2 s.toNNReal))) - F t| < η)
    (hTutteLP : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ 𝒮₀ : SpaceFillingSLEModel, HasNormalizedSLELaw 𝒮₀ ν ∧
      ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (S₀ : MatedCRTEnv Ω₀), S₀.IsValid 𝒮₀ γ ∧
      ∃ η₀ : Ω₀ → C(ℝ, ℂ), Measurable η₀ ∧ (∀ᵐ ω ∂S₀.P, ⇑(η₀ ω) = S₀.η ω) ∧
      ∀ R ρ : ℝ, 0 < ρ → ρ < R → ∀ κ : ℝ, 0 < κ → ∀ θ : ℝ, 0 < θ →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          S₀.P.map (fun ω => (η₀ ω, S₀.mult (1 / (n : ℝ)) ω))
            (uniformStartSelectedLPData (1 / (n : ℝ)) ρ R κ)ᶜ ≤ ENNReal.ofReal θ)
    (hC : BG20ChartFieldInput (ProbeMi.canonicalSLEModel ν)) :
    ConvergenceOfIDLAStmt (ProbeMi.canonicalSLEModel ν) :=
  closed_1_4_quantumConeScaling_coneDimension_markovLimit_noHN5_noHN8_canonical_of_coupling_localLimit_oneStart ν hcpl
    (gaussianClock_localLimit hlocHigh) gaussianClock_oneStart
    (gms21UniformStartInput_of_selectedLP_reference (hasNormalizedSLELaw_canonicalSLEModel_of_coupling hcpl)
      (sleModelClosureInput_canonicalSLEModel_of_coupling hcpl) hTutteLP)
    (hN9_of_bg20ChartField hC)

/-- **Theorem 1.6 at the canonical space-filling SLE model, from mating-of-trees couplings, `hTutteLP` and
`BG20ChartFieldInput`.** The counted form `closed_1_6_quantumConeScaling_coneDimension_markovLimit_noHN5_noHN8` at
`ProbeMi.canonicalSLEModel ν`, with
* `h1`, `h2` from the couplings (`hasNormalizedSLELaw_canonicalSLEModel_of_coupling`,
  `sleModelClosureInput_canonicalSLEModel_of_coupling`);
* `h10` from the couplings, `hfix` (`Sec1.wholePlane_fixedStart_uniformCauchy_of_localLimit`) and `hfixsm`
  (`Sec1.wholePlane_fixedStart_strictMono_of_oneStart`), these from the two Gaussian clock statements:
  the one-start event is `gaussianClock_oneStart` for every `γ ∈ (0, 2)`, the locally uniform limit is
  `gaussianClock_localLimit`, proved for `γ² < 2` and taken from `hlocHigh` for `2 ≤ γ² < 4`;
* `hN4` from `h1`, `h2` and `hTutteLP` (`gms21UniformStartInput_of_selectedLP_reference`);
* `hN9` from `BG20ChartFieldInput` (`hN9_of_bg20ChartField`).
Remaining premises: `hcpl` (couplings on `ℝ` with code law `ν (16/γ²)`), `hlocHigh` (the locally uniform limit of
the dyadic Liouville clocks for `√2 ≤ γ < 2`), `hTutteLP` and `hC`. -/
theorem closed_1_6_quantumConeScaling_coneDimension_markovLimit_canonical_of_coupling_tutteLP_chartField
    (ν : ℝ → Measure SLEPathCode)
    (hcpl : ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∃ (P : Measure ℝ) (X X₀ hIG₀ : ℝ → Field) (B B' B₀ B₀' : ℝ≥0 → ℝ → ℝ) (U : ℝ → ℝ)
        (ηL η η₀ : ℝ → C(ℝ, ℂ)) (bm : ℝ → Path2),
        IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm ∧
        P.map (fun ω => slePathCode (ηL ω)) = ν (16 / γ ^ 2))
    (hlocHigh : ∀ γ : ℝ, 2 ≤ γ ^ 2 → γ < 2 →
        ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
          {hcirc : Ω → ℝ → ℂ → ℝ}, LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc → ∀ x : ℂ,
          ∀ᵐ q ∂(P.prod (planarBrownianMotion x)),
            ∃ F : ℝ≥0 → ℝ, Continuous F ∧ (∀ t, 0 ≤ F t) ∧ Monotone F ∧
              ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ t : ℝ≥0, t ≤ T →
                |(∫ s in (0 : ℝ)..(t : ℝ), HarmonicBalls.dyadicScale (n + 1) ^ (γ ^ 2 / 2) * Real.exp (γ *
                  LatticeProb.Gauss.fieldCircleAverage 0 (hcirc q.1) (HarmonicBalls.dyadicScale (n + 1))
                    (q.2 s.toNNReal))) - F t| < η)
    (hTutteLP : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ 𝒮₀ : SpaceFillingSLEModel, HasNormalizedSLELaw 𝒮₀ ν ∧
      ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (S₀ : MatedCRTEnv Ω₀), S₀.IsValid 𝒮₀ γ ∧
      ∃ η₀ : Ω₀ → C(ℝ, ℂ), Measurable η₀ ∧ (∀ᵐ ω ∂S₀.P, ⇑(η₀ ω) = S₀.η ω) ∧
      ∀ R ρ : ℝ, 0 < ρ → ρ < R → ∀ κ : ℝ, 0 < κ → ∀ θ : ℝ, 0 < θ →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          S₀.P.map (fun ω => (η₀ ω, S₀.mult (1 / (n : ℝ)) ω))
            (uniformStartSelectedLPData (1 / (n : ℝ)) ρ R κ)ᶜ ≤ ENNReal.ofReal θ)
    (hC : BG20ChartFieldInput (ProbeMi.canonicalSLEModel ν)) :
    ConvergenceOfDivSandpileStmt (ProbeMi.canonicalSLEModel ν) :=
  closed_1_6_quantumConeScaling_coneDimension_markovLimit_noHN5_noHN8_canonical_of_coupling_localLimit_oneStart ν hcpl
    (gaussianClock_localLimit hlocHigh) gaussianClock_oneStart
    (gms21UniformStartInput_of_selectedLP_reference (hasNormalizedSLELaw_canonicalSLEModel_of_coupling hcpl)
      (sleModelClosureInput_canonicalSLEModel_of_coupling hcpl) hTutteLP)
    (hN9_of_bg20ChartField hC)

end MatedCRT.FirstPass.Derived
