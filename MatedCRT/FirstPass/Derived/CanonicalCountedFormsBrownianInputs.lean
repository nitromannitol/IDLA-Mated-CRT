import MatedCRT.FirstPass.Derived.CanonicalCountedFormsChartSteps
import MatedCRT.FirstPass.Derived.PlanarBMConePoints.Holds
import MatedCRT.FirstPass.Derived.WindowFrontierJordanTransfer
import MatedCRT.FirstPass.Derived.BrownianBeurling.BrownianBeurlingEstimateProof

/-!
# Theorems 1.4 and 1.6 at the canonical model with the Brownian inputs proved

The forms `closed_1_4_quantumConeScaling_coneDimension_canonical_of_coupling_tutteLP_chartSteps` and
`closed_1_6_quantumConeScaling_coneDimension_canonical_of_coupling_tutteLP_chartSteps`
(`CanonicalCountedFormsChartSteps.lean`) with three of their premises discharged: the window geometry
`hG` from the Jordan frontier of one curve per correlated Brownian pair
(`windowFrontierJordanInput_of_genuineCurve`), the cone points `hLG` of planar Brownian motion
(`planarBMNoTwoSidedConePoints`) and the Beurling estimate `hB`
(`MatedCRT.BrownianBeurling.brownianBeurlingEstimate`).

Remaining premises:
* `hcpl`: the mating-of-trees coupling (Duplantier–Miller–Sheffield, Theorem 1.9), not proved;
* `hTutteLP`: the comparison of the stopped curves of the walk and of the space-filling SLE
  (Gwynne–Miller–Sheffield, proof of Theorem 3.4, case 1), reduced by
  `tutteLP_canonical_of_theorem310_quenchedZeroCone_literature` to Theorem 3.10 of Gwynne–Miller–Sheffield,
  proved as `gmsTheorem310`, and the premises of the quenched zero-cone route;
* `hLQG`: the coordinate change of the LQG measure under conformal charts (`LQGMeasureChartStmt`), proved
  from the cited input `SheffieldWangEnvelope` by `lqgMeasureChartStmt_of_envelope`;
* `hJ`: the Jordan frontier of the windows for one curve per correlated Brownian pair
  (`WindowFrontierJordanGenuineCurve`), which rests on the same coupling as `hcpl`;
* `hDMS`: the past/future independence law of Duplantier–Miller–Sheffield, Theorem 1.9
  (`DMSIntrinsicPastFutureIndependenceLaw`), not proved;
* `hA`: the triple points of the space-filling SLE traversal
  (`CorrelatedBMTraversalTriplePointsNoContinuum`), not proved.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set Metric MarkovProcess
open _root_.HarmonicBalls _root_.LQGMetric _root_.MatedCRTHarmonic _root_.MatedCRTHarmonic.MatedCRT
open scoped NNReal ENNReal BoundedContinuousFunction

namespace MatedCRT.FirstPass.Derived

open MatedCRT.FirstPass.Derived (LQGData LQGData.toMeasure)

/-- **Theorem 1.4 at the canonical space-filling SLE model** from `hcpl`, `hTutteLP`, `hLQG`, `hJ`, `hDMS`
and `hA`. -/
theorem closed_1_4_quantumConeScaling_coneDimension_canonical_of_coupling_tutteLP_genuineCurve
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
    (hLQG : ∀ γ : ℝ, 0 < γ → γ < 2 → LQGMeasureChartStmt γ)
    (hJ : WindowFrontierJordanGenuineCurve) (hDMS : DMSIntrinsicPastFutureIndependenceLaw ν)
    (hA : CorrelatedBMTraversalTriplePointsNoContinuum) :
    ConvergenceOfIDLAStmt (ProbeMi.canonicalSLEModel ν) :=
  closed_1_4_quantumConeScaling_coneDimension_canonical_of_coupling_tutteLP_chartSteps ν hcpl hTutteLP hLQG
    (windowFrontierJordanInput_of_genuineCurve hJ _) hDMS planarBMNoTwoSidedConePoints hA
    MatedCRT.BrownianBeurling.brownianBeurlingEstimate

/-- **Theorem 1.6 at the canonical space-filling SLE model** from `hcpl`, `hTutteLP`, `hLQG`, `hJ`, `hDMS`
and `hA`. -/
theorem closed_1_6_quantumConeScaling_coneDimension_canonical_of_coupling_tutteLP_genuineCurve
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
    (hLQG : ∀ γ : ℝ, 0 < γ → γ < 2 → LQGMeasureChartStmt γ)
    (hJ : WindowFrontierJordanGenuineCurve) (hDMS : DMSIntrinsicPastFutureIndependenceLaw ν)
    (hA : CorrelatedBMTraversalTriplePointsNoContinuum) :
    ConvergenceOfDivSandpileStmt (ProbeMi.canonicalSLEModel ν) :=
  closed_1_6_quantumConeScaling_coneDimension_canonical_of_coupling_tutteLP_chartSteps ν hcpl hTutteLP hLQG
    (windowFrontierJordanInput_of_genuineCurve hJ _) hDMS planarBMNoTwoSidedConePoints hA
    MatedCRT.BrownianBeurling.brownianBeurlingEstimate

end MatedCRT.FirstPass.Derived
