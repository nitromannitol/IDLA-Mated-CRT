import MatedCRT.FirstPass.Derived.CanonicalCountedFormsOfCoupling
import HarmonicBalls.Proofs.Potential.LQGClockZeroInsertionConvergence

/-!
# Theorems 1.4 and 1.6 at the canonical model from couplings, `hTutteLP` and `BG20ChartFieldInput`

The locally uniform limit of the dyadic Liouville clocks of the whole-plane GFF of `LatticeProb.Gauss` at the
insertion `0` holds for every `0 < γ < 2` (`HarmonicBalls.ae_exists_locally_uniform_limit_clock_zero`), so the premise
`hlocHigh` of the canonical counted forms of `CanonicalCountedFormsOfCoupling` is a theorem
(`HarmonicBalls.forall_ae_exists_locally_uniform_limit_clock_zero_of_two_le_sq`).

## Main statements

* `gaussianClock_localLimit_of_lt_two`: the locally uniform limit for every `0 < γ < 2`, in the form of the premise
  `hloc` of `CanonicalCountedFormsOneStart`.
* `closed_1_4_quantumConeScaling_coneDimension_canonical_of_coupling_tutteLP_chartField`,
  `closed_1_6_quantumConeScaling_coneDimension_canonical_of_coupling_tutteLP_chartField`: Theorems 1.4 and 1.6 at the
  canonical model from `hcpl hTutteLP hC`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set MarkovProcess
open _root_.HarmonicBalls _root_.LQGMetric _root_.MatedCRTHarmonic _root_.MatedCRTHarmonic.MatedCRT
open scoped NNReal ENNReal BoundedContinuousFunction
open MatedCRT.FirstPass.Derived (LQGData LQGData.toMeasure)

namespace MatedCRT.FirstPass.Derived

/-- **The locally uniform limit of the dyadic Liouville clocks for every `0 < γ < 2`** at the insertion `0`: for every
whole-plane GFF of `LatticeProb.Gauss` and every start, almost surely for the joint law of the field and planar
Brownian motion, the dyadic clocks converge locally uniformly to a continuous, nonnegative, nondecreasing limit
(`HarmonicBalls.ae_exists_locally_uniform_limit_clock_zero`). -/
theorem gaussianClock_localLimit_of_lt_two : ∀ γ : ℝ, 0 < γ → γ < 2 →
    ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
      {hcirc : Ω → ℝ → ℂ → ℝ}, LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc → ∀ x : ℂ,
      ∀ᵐ q ∂(P.prod (planarBrownianMotion x)),
        ∃ F : ℝ≥0 → ℝ, Continuous F ∧ (∀ t, 0 ≤ F t) ∧ Monotone F ∧
          ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ t : ℝ≥0, t ≤ T →
            |(∫ s in (0 : ℝ)..(t : ℝ), HarmonicBalls.dyadicScale (n + 1) ^ (γ ^ 2 / 2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage 0 (hcirc q.1) (HarmonicBalls.dyadicScale (n + 1))
                (q.2 s.toNNReal))) - F t| < η := by
  intro γ hγ0 hγ2 Ω _ P hC hcirc hh x
  exact HarmonicBalls.ae_exists_locally_uniform_limit_clock_zero hh hγ0 hγ2 x

/-- **Theorem 1.4 at the canonical space-filling SLE model, from mating-of-trees couplings, `hTutteLP` and
`BG20ChartFieldInput`.** The form
`closed_1_4_quantumConeScaling_coneDimension_markovLimit_canonical_of_coupling_tutteLP_chartField` with its premise
`hlocHigh` (the locally uniform limit of the dyadic Liouville clocks for `√2 ≤ γ < 2`) supplied by
`HarmonicBalls.forall_ae_exists_locally_uniform_limit_clock_zero_of_two_le_sq`. Remaining premises: `hcpl`
(couplings on `ℝ` with code law `ν (16/γ²)`), `hTutteLP` and `hC`. -/
theorem closed_1_4_quantumConeScaling_coneDimension_canonical_of_coupling_tutteLP_chartField
    (ν : ℝ → Measure SLEPathCode)
    (hcpl : ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∃ (P : Measure ℝ) (X X₀ hIG₀ : ℝ → Field) (B B' B₀ B₀' : ℝ≥0 → ℝ → ℝ) (U : ℝ → ℝ)
        (ηL η η₀ : ℝ → C(ℝ, ℂ)) (bm : ℝ → Path2),
        IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm ∧
        P.map (fun ω => slePathCode (ηL ω)) = ν (16 / γ ^ 2))
    (hTutteLP : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ 𝒮₀ : SpaceFillingSLEModel, HasNormalizedSLELaw 𝒮₀ ν ∧
      ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (S₀ : MatedCRTEnv Ω₀), S₀.IsValid 𝒮₀ γ ∧
      ∃ η₀ : Ω₀ → C(ℝ, ℂ), Measurable η₀ ∧ (∀ᵐ ω ∂S₀.P, ⇑(η₀ ω) = S₀.η ω) ∧
      ∀ R ρ : ℝ, 0 < ρ → ρ < R → ∀ κ : ℝ, 0 < κ → ∀ θ : ℝ, 0 < θ →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          S₀.P.map (fun ω => (η₀ ω, S₀.mult (1 / (n : ℝ)) ω))
            (uniformStartSelectedLPData (1 / (n : ℝ)) ρ R κ)ᶜ ≤ ENNReal.ofReal θ)
    (hC : BG20ChartFieldInput (ProbeMi.canonicalSLEModel ν)) :
    ConvergenceOfIDLAStmt (ProbeMi.canonicalSLEModel ν) :=
  closed_1_4_quantumConeScaling_coneDimension_markovLimit_canonical_of_coupling_tutteLP_chartField ν hcpl
    HarmonicBalls.forall_ae_exists_locally_uniform_limit_clock_zero_of_two_le_sq hTutteLP hC

/-- **Theorem 1.6 at the canonical space-filling SLE model, from mating-of-trees couplings, `hTutteLP` and
`BG20ChartFieldInput`.** The form
`closed_1_6_quantumConeScaling_coneDimension_markovLimit_canonical_of_coupling_tutteLP_chartField` with its premise
`hlocHigh` (the locally uniform limit of the dyadic Liouville clocks for `√2 ≤ γ < 2`) supplied by
`HarmonicBalls.forall_ae_exists_locally_uniform_limit_clock_zero_of_two_le_sq`. Remaining premises: `hcpl`
(couplings on `ℝ` with code law `ν (16/γ²)`), `hTutteLP` and `hC`. -/
theorem closed_1_6_quantumConeScaling_coneDimension_canonical_of_coupling_tutteLP_chartField
    (ν : ℝ → Measure SLEPathCode)
    (hcpl : ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∃ (P : Measure ℝ) (X X₀ hIG₀ : ℝ → Field) (B B' B₀ B₀' : ℝ≥0 → ℝ → ℝ) (U : ℝ → ℝ)
        (ηL η η₀ : ℝ → C(ℝ, ℂ)) (bm : ℝ → Path2),
        IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm ∧
        P.map (fun ω => slePathCode (ηL ω)) = ν (16 / γ ^ 2))
    (hTutteLP : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ 𝒮₀ : SpaceFillingSLEModel, HasNormalizedSLELaw 𝒮₀ ν ∧
      ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (S₀ : MatedCRTEnv Ω₀), S₀.IsValid 𝒮₀ γ ∧
      ∃ η₀ : Ω₀ → C(ℝ, ℂ), Measurable η₀ ∧ (∀ᵐ ω ∂S₀.P, ⇑(η₀ ω) = S₀.η ω) ∧
      ∀ R ρ : ℝ, 0 < ρ → ρ < R → ∀ κ : ℝ, 0 < κ → ∀ θ : ℝ, 0 < θ →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          S₀.P.map (fun ω => (η₀ ω, S₀.mult (1 / (n : ℝ)) ω))
            (uniformStartSelectedLPData (1 / (n : ℝ)) ρ R κ)ᶜ ≤ ENNReal.ofReal θ)
    (hC : BG20ChartFieldInput (ProbeMi.canonicalSLEModel ν)) :
    ConvergenceOfDivSandpileStmt (ProbeMi.canonicalSLEModel ν) :=
  closed_1_6_quantumConeScaling_coneDimension_markovLimit_canonical_of_coupling_tutteLP_chartField ν hcpl
    HarmonicBalls.forall_ae_exists_locally_uniform_limit_clock_zero_of_two_le_sq hTutteLP hC

end MatedCRT.FirstPass.Derived
