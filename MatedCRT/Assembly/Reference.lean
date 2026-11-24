import MatedCRT.Assembly.Remaining
import MatedCRT.Assembly.Canonical
import MatedCRT.FirstPass.Derived.GreenKernelUpperOfReference
import MatedCRT.FirstPass.Derived.ResistanceBoundOfReference
import MatedCRT.FirstPass.Derived.DiscreteHolderOfReference
import MatedCRT.FirstPass.Derived.MepsScalingOfLower
import MatedCRT.FirstPass.Derived.CoreGffLowerOfLemma69
import MatedCRT.FirstPass.S6j.ExitTimeLowerTail
import MatedCRT.FirstPass.Derived.RandomWalkToLBMStmtOfBG20
import MatedCRT.FirstPass.Derived.HN9OfChartField
import MatedCRT.Steps.Sec2.BoundedExitTimeRV
import MatedCRT.FirstPass.Derived.CanonicalHasReferenceEnvironments
import MatedCRT.FirstPass.Derived.WholePlaneClockFixedStartOfLocalLimit
import MatedCRT.FirstPass.Derived.WholePlaneClockStrictMonoOfOneStart
import MatedCRT.FirstPass.Derived.CanonicalCountedFormsOfCoupling
import MatedCRT.FirstPass.Derived.CanonicalCountedFormsOfCouplingClock
import MatedCRT.FirstPass.Derived.CanonicalInputsOfCoupling
import MatedCRT.FirstPass.Derived.GMS21UniformStartOfSelectedProkhorov

/-!
# The cited fields of `MainHypotheses` from reference environments

Five fields of `RemainingHypotheses 𝒮` (`MatedCRT/Assembly/Remaining.lean`) are cited results or literature inputs:
Theorem 2.11 (`randomWalkToLBM`), Lemmas 2.14 and 2.16 (`greenKernelUpperBound`, `greenKernelLowerBound`), the
scaling of the expected exit time (`mepsScaling`) and the corrected Lemma 3.2 (`discreteHolderContinuityCorrected`).
For a model `𝒮` with a normalized space-filling SLE law `ν`, the SLE closure inputs, valid environments on `ℝ`
(`HasReferenceEnvironments 𝒮`), the uniform-start invariance principle (`GMS21UniformStartInput 𝒮`) and the chart
forms of Berestycki-Gwynne, Lemmas 7.20 and 7.21 (`BG20ChartFieldInput 𝒮`), all five are theorems:

* Theorem 2.11: `randomWalkToLBMStmt_of_markovLimit_bg20ChartField`;
* Lemmas 2.14 and 2.16: `FirstPass.Derived.greenKernelUpperBoundStmt_of_reference` and
  `FirstPass.Derived.greenKernelLowerBoundStmt_of_reference`, with the full one-sided mating-rigid set
  `exists_matingRigidLEOn_full_derived`;
* the scaling of the expected exit time: `mepsScalingInput_of_lower`, with Lemma 2.18 from Lemma 2.14, Lemma 2.17
  from the volume growth, and the lower half of Berestycki-Gwynne (1.8) from Lemmas 2.14, 2.16 and
  Berestycki-Gwynne Lemma 6.9 (`FirstPass.Derived.mεCdf_lower_of_lemma69`,
  `ExitTimeLowerTail.exitTimeLowerTail_of_uniformStart`);
* the corrected Lemma 3.2: `FirstPass.Derived.frozenDiscreteHolderContinuityCorrected_of_reference`.

The remaining fields are the fifteen open steps collected in `OpenStepHypotheses 𝒮`. At the canonical model
`ProbeMi.canonicalSLEModel ν`, the law, the closure inputs, the reference environments and the uniform-start input
follow from the premises `CanonicalHypotheses ν` (`MatedCRT/Assembly/Canonical.lean`), so `MainHypotheses` holds at the
canonical model from `CanonicalHypotheses ν` and `OpenStepHypotheses`.

## Main statements

* `ReferenceHypotheses.toRemainingHypotheses`: `RemainingHypotheses 𝒮` from `ReferenceHypotheses 𝒮 ν`.
* `convergenceOfIDLA_of_reference`, `convergenceOfDivSandpile_of_reference`: Theorems 1.4 and 1.6 from
  `ReferenceHypotheses 𝒮 ν`.
* `mainHypotheses_canonical`: `MainHypotheses (ProbeMi.canonicalSLEModel ν)` from `CanonicalHypotheses ν` and
  `OpenStepHypotheses (ProbeMi.canonicalSLEModel ν)`.
-/

set_option autoImplicit false

open MeasureTheory

namespace MatedCRT

/-- The fifteen fields of `MainHypotheses 𝒮` that are open steps, with the same names and types. -/
structure OpenStepHypotheses (𝒮 : SpaceFillingSLEModel) : Prop where
  /-- Lemma 2.4: locality of the cone harmonic balls. -/
  coneHarmonicBallLocality : ConeHarmonicBallLocalityStep
  /-- Lemmas 2.4, 2.5, Theorems 1.4, 1.6: strict growth of the cone harmonic balls (`T' = T`, not in the
  paper). -/
  coneHarmonicBallStrictGrowth : ConeHarmonicBallStrictGrowthStep
  /-- Lemma 2.5, Theorems 1.4, 1.6: the half-ball family is a functional of the field. -/
  coneHalfBallFamilyFunctional : ConeHalfBallFamilyFunctionalStep
  /-- Lemma 3.5: interior estimate. Reduced (`dirichletInteriorStep_of_moduli`) to `DirichletPointwiseStep` and
  `DirichletDiscreteModulusStep`, which are open and not fields. -/
  dirichletInterior : DirichletInteriorStep 𝒮
  /-- Lemma 3.5: boundary estimate. -/
  dirichletBoundary : DirichletBoundaryStep 𝒮
  /-- Propositions 4.2 and 5.1: the least supersolution is strictly above the obstacle on the harmonic ball
  (eq:strictly-above-in-interior). Replaces `ObstacleClusterInnerApproximationStep`
  (`obstacleClusterInnerApproximation_of_strictGap`). -/
  harmonicBallStrictObstacleGap : HarmonicBallStrictObstacleGapStep 𝒮
  /-- Lemma 4.6 (corrected route): local compactness of the odometers. -/
  odometerLocalCompactnessCorrected : OdometerLocalCompactnessCorrectedStep 𝒮
  /-- Lemma 4.6 (corrected route): boundary upgrade. -/
  odometerBoundaryUpgradeCorrected : OdometerBoundaryUpgradeCorrectedStep 𝒮
  /-- Lemma 4.6: measurable selection of the subsequence. -/
  odometerMeasurableSelection : OdometerMeasurableSelectionStep 𝒮
  /-- Proposition 5.1: Lemma 5.3 on `V^ε(Λ_t)`, interior lower bound of the obstacle surplus. Not a field: `StoppedSurplusInteriorStep` is supplied by `stoppedSurplusInterior_of_gap` from the strict obstacle gap
  `harmonicBallStrictObstacleGap`, `mepsScaling` and the three named inputs below. -/
  stoppedSurplusPole : StoppedInterior.StoppedSurplusPoleStep 𝒮
  /-- Lemma 5.3 on `V^ε(Λ_t)`: the discrete-to-continuum geometry of the `δ`-interior. -/
  stoppedInteriorGeometry : StoppedInterior.StoppedInteriorGeometryStep 𝒮
  /-- Lemma 5.3 on `V^ε(Λ_t)`: measurability of the continuum margin on the random compact set. -/
  stoppedInteriorMeasurable : StoppedInterior.StoppedInteriorMeasurableStep 𝒮
  /-- Proposition 5.1: Lemma 5.3 on `V^ε(Λ_t)`, Green potential of the boundary layer `A \ Λ^ε_t`. -/
  stoppedLayerPotential : StoppedLayerPotentialStep 𝒮
  /-- Lemma 5.3 (through `meanValueSurplusStep_of_lower`): the lower surplus estimate. -/
  meanValueSurplusLower : MeanValueSurplusLowerStep 𝒮
  /-- **Lemma 3.4** (convergence of integrals of the Green function). Reduced by `integralConvergenceGreenFunction_of_steps` to the open LBM steps
  (not fields). Used by 3.3, 3.5 and the Section 5 stopped steps. -/
  integralConvergenceGreenFunction : IntegralConvergenceGreenFunctionStmt 𝒮

/-- A model `𝒮` with normalized space-filling SLE law `ν`, the SLE closure inputs, valid environments on `ℝ`, the
uniform-start invariance principle, the chart forms of Berestycki-Gwynne, Lemmas 7.20 and 7.21, and the open steps. -/
structure ReferenceHypotheses (𝒮 : SpaceFillingSLEModel) (ν : ℝ → Measure SLEPathCode) : Prop where
  /-- `𝒮` has the normalized space-filling SLE law `ν`. -/
  law : HasNormalizedSLELaw 𝒮 ν
  /-- The SLE closure inputs of the model (`SLEModelClosureInput`). -/
  sleModelClosure : SLEModelClosureInput 𝒮
  /-- The uniform-start invariance principle for the walk on the mated-CRT map (`GMS21UniformStartInput`). -/
  uniformStart : GMS21UniformStartInput 𝒮
  /-- Valid environments of `𝒮` on `ℝ` for every `0 < γ < 2`. -/
  referenceEnvironments : HasReferenceEnvironments 𝒮
  /-- The chart forms of Berestycki-Gwynne, Lemmas 7.20 and 7.21. -/
  chartField : BG20ChartFieldInput 𝒮
  /-- The open steps. -/
  steps : OpenStepHypotheses 𝒮

/-- `RemainingHypotheses 𝒮` from `ReferenceHypotheses 𝒮 ν`: the five cited fields are proved from the law, the
closure inputs, the reference environments, the uniform-start input and the chart forms. -/
theorem ReferenceHypotheses.toRemainingHypotheses {𝒮 : SpaceFillingSLEModel} {ν : ℝ → Measure SLEPathCode}
    (H : ReferenceHypotheses 𝒮 ν) : RemainingHypotheses 𝒮 := by
  obtain ⟨G, hGnull, hG⟩ := exists_matingRigidLEOn_full_derived
  have h12 : GreenKernelUpperBoundStmt 𝒮 :=
    FirstPass.Derived.greenKernelUpperBoundStmt_of_reference H.law H.referenceEnvironments hGnull hG
  have h13 : GreenKernelLowerBoundStmt 𝒮 :=
    FirstPass.Derived.greenKernelLowerBoundStmt_of_reference H.law H.law H.referenceEnvironments hGnull hG
  exact
  { randomWalkToLBM := randomWalkToLBMStmt_of_markovLimit_bg20ChartField H.law H.sleModelClosure H.uniformStart
      H.referenceEnvironments H.chartField
    greenKernelUpperBound := h12
    greenKernelLowerBound := h13
    mepsScaling := mepsScalingInput_of_lower (FirstPass.Derived.exitTimeUpperBoundStmt_of_greenKernelUpper h12)
      (boundedExitTimeRV_of_steps FirstPass.Derived.volumeGrowthStmt_holds)
      (FirstPass.Derived.mεCdf_lower_of_lemma69 h12 h13
        (ExitTimeLowerTail.exitTimeLowerTail_of_uniformStart H.uniformStart))
    sleModelClosure := H.sleModelClosure
    discreteHolderContinuityCorrected :=
      FirstPass.Derived.frozenDiscreteHolderContinuityCorrected_of_reference H.law H.referenceEnvironments
        (fun γ hγ0 hγ2 => ⟨G, hGnull γ hγ0 hγ2, hG⟩) (FirstPass.Derived.cellSizeEstimateStmt_holds 𝒮)
    coneHarmonicBallLocality := H.steps.coneHarmonicBallLocality
    coneHarmonicBallStrictGrowth := H.steps.coneHarmonicBallStrictGrowth
    coneHalfBallFamilyFunctional := H.steps.coneHalfBallFamilyFunctional
    dirichletInterior := H.steps.dirichletInterior
    dirichletBoundary := H.steps.dirichletBoundary
    harmonicBallStrictObstacleGap := H.steps.harmonicBallStrictObstacleGap
    odometerLocalCompactnessCorrected := H.steps.odometerLocalCompactnessCorrected
    odometerBoundaryUpgradeCorrected := H.steps.odometerBoundaryUpgradeCorrected
    odometerMeasurableSelection := H.steps.odometerMeasurableSelection
    stoppedSurplusPole := H.steps.stoppedSurplusPole
    stoppedInteriorGeometry := H.steps.stoppedInteriorGeometry
    stoppedInteriorMeasurable := H.steps.stoppedInteriorMeasurable
    stoppedLayerPotential := H.steps.stoppedLayerPotential
    meanValueSurplusLower := H.steps.meanValueSurplusLower
    integralConvergenceGreenFunction := H.steps.integralConvergenceGreenFunction }

/-- **Theorem 1.4** (convergence of IDLA) for every model, from `ReferenceHypotheses 𝒮 ν`. -/
theorem convergenceOfIDLA_of_reference (𝒮 : SpaceFillingSLEModel) (ν : ℝ → Measure SLEPathCode)
    (H : ReferenceHypotheses 𝒮 ν) : ConvergenceOfIDLAStmt 𝒮 :=
  convergenceOfIDLA_of_remaining 𝒮 H.toRemainingHypotheses

/-- **Theorem 1.6** (convergence of the divisible sandpile) for every model, from `ReferenceHypotheses 𝒮 ν`. -/
theorem convergenceOfDivSandpile_of_reference (𝒮 : SpaceFillingSLEModel) (ν : ℝ → Measure SLEPathCode)
    (H : ReferenceHypotheses 𝒮 ν) : ConvergenceOfDivSandpileStmt 𝒮 :=
  convergenceOfDivSandpile_of_remaining 𝒮 H.toRemainingHypotheses

/-- `ReferenceHypotheses` at the canonical model from `CanonicalHypotheses ν` and the open steps: the law and the
closure inputs from the mating-of-trees couplings, the reference environments from the couplings and the dyadic
Liouville clocks, and the uniform-start input from the couplings and `tutteLP`. -/
theorem referenceHypotheses_canonical (ν : ℝ → Measure SLEPathCode) (H : CanonicalHypotheses ν)
    (hS : OpenStepHypotheses (ProbeMi.canonicalSLEModel ν)) :
    ReferenceHypotheses (ProbeMi.canonicalSLEModel ν) ν :=
  have hfix := Sec1.wholePlane_fixedStart_uniformCauchy_of_localLimit
    FirstPass.Derived.gaussianClock_localLimit_of_lt_two
  { law := FirstPass.Derived.hasNormalizedSLELaw_canonicalSLEModel_of_coupling H.matingOfTreesCoupling
    sleModelClosure := FirstPass.Derived.sleModelClosureInput_canonicalSLEModel_of_coupling H.matingOfTreesCoupling
    uniformStart := gms21UniformStartInput_of_selectedLP_reference
      (FirstPass.Derived.hasNormalizedSLELaw_canonicalSLEModel_of_coupling H.matingOfTreesCoupling)
      (FirstPass.Derived.sleModelClosureInput_canonicalSLEModel_of_coupling H.matingOfTreesCoupling) H.tutteLP
    referenceEnvironments := Sec1.hasReferenceEnvironments_canonical_of_coupling_wholePlane_fixedStart ν
      H.matingOfTreesCoupling hfix
      (Sec1.wholePlane_fixedStart_strictMono_of_oneStart FirstPass.Derived.gaussianClock_oneStart hfix)
    chartField := H.chartField
    steps := hS }

/-- **The hypotheses of the main theorems at the canonical model**: `MainHypotheses (ProbeMi.canonicalSLEModel ν)`
from `CanonicalHypotheses ν` and the open steps. -/
theorem mainHypotheses_canonical (ν : ℝ → Measure SLEPathCode) (H : CanonicalHypotheses ν)
    (hS : OpenStepHypotheses (ProbeMi.canonicalSLEModel ν)) : MainHypotheses (ProbeMi.canonicalSLEModel ν) :=
  (referenceHypotheses_canonical ν H hS).toRemainingHypotheses.toMainHypotheses

end MatedCRT
