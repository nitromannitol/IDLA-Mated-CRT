import MatedCRT.FirstPass.Derived.CanonicalCountedFormsOfCouplingClock
import MatedCRT.FirstPass.Derived.WindowChartBG
import MatedCRT.FirstPass.Derived.LevyConformalChartProof
import MatedCRT.FirstPass.Derived.ChartTransportRevuz
import MatedCRT.FirstPass.Derived.ChartFieldLBM
import MatedCRT.FirstPass.Derived.WindowChartBGIntrinsicIndependenceLaw
import MatedCRT.FirstPass.Derived.WindowChartBGFieldIntrinsic
import MatedCRT.FirstPass.Derived.WindowChartBGDiscreteLawIntrinsic
import MatedCRT.FirstPass.Derived.MatingOfTreesCellSideInputsProof
import MatedCRT.FirstPass.Derived.BG20FrozenWindowLawComparisonProof
import MatedCRT.FirstPass.Derived.JordanDomainExteriorRegularityProof
import MatedCRT.FirstPass.Derived.HN5Discharged
import MatedCRT.FirstPass.Derived.RandomWalkToLBMStmtOfBG20
import MatedCRT.FirstPass.Derived.EnvironmentScalingHolds
import MatedCRT.FirstPass.Derived.QuantumConeScalingDerived
import MatedCRT.FirstPass.Derived.GMS21UniformStartOfSelectedProkhorov

/-!
# Theorems 1.4 and 1.6 at the canonical model with the chart input derived

The counted forms of `CanonicalCountedFormsOfCouplingClock` take the chart input of the joint limit
`BG20ChartFieldInput (ProbeMi.canonicalSLEModel ν)` as the premise `hC`. This file derives `hC`
(`bg20ChartFieldInput_of_chartFieldLBMLimit_bg`) from the steps of its proof:

* Lévy's conformal invariance of planar Brownian motion (`LevyChart.levyConformalChartStmt`) and the transported Revuz
  measure (`chartTransportRevuzStmt_of_levyConformalChart`), with the coordinate change of the LQG measure
  (`LQGMeasureChartStmt γ`), give the coordinate change of Liouville Brownian motion
  (`chartFieldLBMLimitStmt_of_lqgMeasureChart_of_chartTransportRevuz`; Berestycki (2015), Theorem 1.3);
* the window geometry `WindowFrontierJordanInput` (the frontier of a window domain is a Jordan curve; Miller–Sheffield,
  *Imaginary geometry IV*);
* the independence of the windows for the inverse charts of Berestycki–Gwynne (2020), Lemma 7.21
  (`bg20ChartIndependenceInputBG_of_dmsIntrinsicLaw`), from Duplantier–Miller–Sheffield, Theorem 1.9
  (`DMSIntrinsicPastFutureIndependenceLaw ν`), the normalized law of the canonical model (from the couplings), the
  intrinsic chart field step (`bg20WindowFieldIntrinsicInput_of_windowFrontierJordan`), the intrinsic discrete window
  law step (`bg20DiscreteWindowLawIntrinsicInput_of_cellSideIdentity`) and the exterior regularity of Jordan domains
  (`jordanDomainExteriorRegularity`, from the Beurling estimate `BrownianBeurlingEstimate`);
* the intrinsic discrete window law step from the cell-side identity of the mated-CRT map
  (`matingOfTreesCellSideIdentity_of_literature`: Le Gall's theorem on two-sided cone points of planar Brownian motion,
  `PlanarBMNoTwoSidedConePoints`, and the triple points of the space-filling SLE traversal,
  `CorrelatedBMTraversalTriplePointsNoContinuum`) and the frozen window law comparison
  (`bg20FrozenWindowLawComparison`), whose inputs at the canonical model are the normalized law, the closure
  properties and the reference environments (from the couplings and the Gaussian Liouville clocks), the uniform-start
  invariance principle (from `hTutteLP`), the scaling of the cone environments (`quantumConeScalingInput_derived`),
  mating-of-trees rigidity (`exists_matingRigidLEOn_full_derived`), the time-change half of Berestycki–Gwynne (2020),
  Lemma 7.4 (`hN5a_of_exitClassLaws` with the Brownian class laws of
  `ae_forall_map_stoppedExitCurve_eq_of_tendsto_law_interpWalkLaw`), `WindowFrontierJordanInput` and the exterior
  regularity of Jordan domains.

## Main statements

* `bg20ChartFieldInput_canonical_of_chartSteps`: `BG20ChartFieldInput (ProbeMi.canonicalSLEModel ν)` from `hcpl`,
  `hTutteLP`, `LQGMeasureChartStmt`, `WindowFrontierJordanInput`, `DMSIntrinsicPastFutureIndependenceLaw ν`,
  `PlanarBMNoTwoSidedConePoints`, `CorrelatedBMTraversalTriplePointsNoContinuum` and `BrownianBeurlingEstimate`.
* `closed_1_4_quantumConeScaling_coneDimension_canonical_of_coupling_tutteLP_chartSteps`,
  `closed_1_6_quantumConeScaling_coneDimension_canonical_of_coupling_tutteLP_chartSteps`: Theorems 1.4 and 1.6 at the
  canonical model from these premises.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric MarkovProcess
open _root_.HarmonicBalls _root_.LQGMetric _root_.MatedCRTHarmonic _root_.MatedCRTHarmonic.MatedCRT
open scoped NNReal ENNReal BoundedContinuousFunction
open MatedCRT.FirstPass.Derived (LQGData LQGData.toMeasure)

namespace MatedCRT.FirstPass.Derived

/-- **The chart input of the joint limit at the canonical model from the steps of its proof.** For a family `ν` of
code laws such that every `γ ∈ (0, 2)` has a mating-of-trees coupling on `ℝ` with code law `ν (16/γ²)` (`hcpl`) and
reference environments with the selected Lévy–Prokhorov bound (`hTutteLP`), the chart input
`BG20ChartFieldInput (ProbeMi.canonicalSLEModel ν)` follows from the coordinate change of the LQG measure
(`LQGMeasureChartStmt γ` for `0 < γ < 2`), the window geometry (`WindowFrontierJordanInput`),
Duplantier–Miller–Sheffield, Theorem 1.9 (`DMSIntrinsicPastFutureIndependenceLaw ν`), Le Gall's theorem on two-sided
cone points (`PlanarBMNoTwoSidedConePoints`), the triple points of the space-filling SLE traversal
(`CorrelatedBMTraversalTriplePointsNoContinuum`) and the Beurling estimate (`BrownianBeurlingEstimate`). -/
theorem bg20ChartFieldInput_canonical_of_chartSteps
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
    (hG : WindowFrontierJordanInput (ProbeMi.canonicalSLEModel ν))
    (hDMS : DMSIntrinsicPastFutureIndependenceLaw ν)
    (hLG : PlanarBMNoTwoSidedConePoints) (hA : CorrelatedBMTraversalTriplePointsNoContinuum)
    (hB : BrownianBeurlingEstimate) :
    BG20ChartFieldInput (ProbeMi.canonicalSLEModel ν) := by
  have h1 : HasNormalizedSLELaw (ProbeMi.canonicalSLEModel ν) ν :=
    hasNormalizedSLELaw_canonicalSLEModel_of_coupling hcpl
  have h2 : SLEModelClosureInput (ProbeMi.canonicalSLEModel ν) :=
    sleModelClosureInput_canonicalSLEModel_of_coupling hcpl
  have hfix := Sec1.wholePlane_fixedStart_uniformCauchy_of_localLimit gaussianClock_localLimit_of_lt_two
  have h10 : HasReferenceEnvironments (ProbeMi.canonicalSLEModel ν) :=
    Sec1.hasReferenceEnvironments_canonical_of_coupling_wholePlane_fixedStart ν hcpl hfix
      (Sec1.wholePlane_fixedStart_strictMono_of_oneStart gaussianClock_oneStart hfix)
  have hN4 : GMS21UniformStartInput (ProbeMi.canonicalSLEModel ν) :=
    gms21UniformStartInput_of_selectedLP_reference h1 h2 hTutteLP
  obtain ⟨G, hGnull, hGrig⟩ := exists_matingRigidLEOn_full_derived
  have hU : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ G : Set MatedCRTHarmonic.MatedCRT.Path2,
      (∀ μ : Measure MatedCRTHarmonic.MatedCRT.Path2, MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ μ →
        μ Gᶜ = 0) ∧ MatingRigidLEOn G := fun γ hγ0 hγ2 => ⟨G, hGnull γ hγ0 hγ2, hGrig⟩
  have hEnvS := coneEnvironmentScalingUnderSLE_of_scaling (ProbeMi.canonicalSLEModel ν)
    quantumConeScalingInput_derived h2.1 h2.2.1 h2.2.2
  have hN5c : ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
        S.IsValid (ProbeMi.canonicalSLEModel ν) γ →
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
    filter_upwards [ae_forall_map_stoppedExitCurve_eq_of_tendsto_law_interpWalkLaw hEnvS hN4
      h1 h10 hU hγ hγ2 hS hη' hae hε0 hε hlaw] with P hP z
    exact Filter.Eventually.of_forall fun r hr => hP z r hr
  have hJ : JordanDomainExteriorRegularity := jordanDomainExteriorRegularity hB
  have hcmp : BG20FrozenWindowLawComparison (ProbeMi.canonicalSLEModel ν) :=
    bg20FrozenWindowLawComparison hEnvS hN4 h1 h10 hU (hN5a_of_exitClassLaws hEnvS hN4 h1 h10 hU hN5c) hG hJ
  have hcell : MatingOfTreesCellSideIdentity (ProbeMi.canonicalSLEModel ν) :=
    matingOfTreesCellSideIdentity_of_literature hLG hA
  have hI : BG20ChartIndependenceInputBG (ProbeMi.canonicalSLEModel ν) :=
    bg20ChartIndependenceInputBG_of_dmsIntrinsicLaw hDMS h1
      (bg20WindowFieldIntrinsicInput_of_windowFrontierJordan hG)
      (bg20DiscreteWindowLawIntrinsicInput_of_cellSideIdentity hcell hcmp) hJ
  exact bg20ChartFieldInput_of_chartFieldLBMLimit_bg LevyChart.levyConformalChartStmt
    (fun γ hγ hγ2 => chartFieldLBMLimitStmt_of_lqgMeasureChart_of_chartTransportRevuz (hLQG γ hγ hγ2)
      (chartTransportRevuzStmt_of_levyConformalChart hγ hγ2 LevyChart.levyConformalChartStmt))
    hG hI

/-- **Theorem 1.4 at the canonical space-filling SLE model, with the chart input derived.** The form
`closed_1_4_quantumConeScaling_coneDimension_canonical_of_coupling_tutteLP_chartField` with its premise
`hC : BG20ChartFieldInput (ProbeMi.canonicalSLEModel ν)` supplied by `bg20ChartFieldInput_canonical_of_chartSteps`.
Remaining premises: `hcpl`, `hTutteLP`, `hLQG` (the coordinate change of the LQG measure), `hG` (the window geometry),
`hDMS` (Duplantier–Miller–Sheffield, Theorem 1.9), `hLG` (Le Gall, two-sided cone points of planar Brownian motion),
`hA` (triple points of the space-filling SLE traversal) and `hB` (the Beurling estimate). -/
theorem closed_1_4_quantumConeScaling_coneDimension_canonical_of_coupling_tutteLP_chartSteps
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
    (hG : WindowFrontierJordanInput (ProbeMi.canonicalSLEModel ν))
    (hDMS : DMSIntrinsicPastFutureIndependenceLaw ν)
    (hLG : PlanarBMNoTwoSidedConePoints) (hA : CorrelatedBMTraversalTriplePointsNoContinuum)
    (hB : BrownianBeurlingEstimate) :
    ConvergenceOfIDLAStmt (ProbeMi.canonicalSLEModel ν) :=
  closed_1_4_quantumConeScaling_coneDimension_canonical_of_coupling_tutteLP_chartField ν hcpl hTutteLP
    (bg20ChartFieldInput_canonical_of_chartSteps ν hcpl hTutteLP hLQG hG hDMS hLG hA hB)

/-- **Theorem 1.6 at the canonical space-filling SLE model, with the chart input derived.** The form
`closed_1_6_quantumConeScaling_coneDimension_canonical_of_coupling_tutteLP_chartField` with its premise
`hC : BG20ChartFieldInput (ProbeMi.canonicalSLEModel ν)` supplied by `bg20ChartFieldInput_canonical_of_chartSteps`.
Remaining premises: `hcpl`, `hTutteLP`, `hLQG` (the coordinate change of the LQG measure), `hG` (the window geometry),
`hDMS` (Duplantier–Miller–Sheffield, Theorem 1.9), `hLG` (Le Gall, two-sided cone points of planar Brownian motion),
`hA` (triple points of the space-filling SLE traversal) and `hB` (the Beurling estimate). -/
theorem closed_1_6_quantumConeScaling_coneDimension_canonical_of_coupling_tutteLP_chartSteps
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
    (hG : WindowFrontierJordanInput (ProbeMi.canonicalSLEModel ν))
    (hDMS : DMSIntrinsicPastFutureIndependenceLaw ν)
    (hLG : PlanarBMNoTwoSidedConePoints) (hA : CorrelatedBMTraversalTriplePointsNoContinuum)
    (hB : BrownianBeurlingEstimate) :
    ConvergenceOfDivSandpileStmt (ProbeMi.canonicalSLEModel ν) :=
  closed_1_6_quantumConeScaling_coneDimension_canonical_of_coupling_tutteLP_chartField ν hcpl hTutteLP
    (bg20ChartFieldInput_canonical_of_chartSteps ν hcpl hTutteLP hLQG hG hDMS hLG hA hB)

end MatedCRT.FirstPass.Derived
