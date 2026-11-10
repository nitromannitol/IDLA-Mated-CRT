import MatedCRT.FirstPass.S5qd
import MatedCRT.FirstPass.Closure.Section3
import MatedCRT.FirstPass.S3i.LensClosed

/-!
# Proposition 5.1 with the certified reference model without its frozen truncated-laws conjunct (fp-S5-certified-core, z5)

`CertifiedReferenceModel ν 𝒮` (`FirstPass/SLERef/Certified.lean:54`) has eighteen conjuncts; conjunct 17 is the frozen
Prop `FrozenTruncatedQuenchedLawsFixedTime 𝒮` (line 71). The chain of Proposition 5.1 (`closed_5_1_canon_noCell_derived_closed`,
`FirstPass/S5qd.lean:192`) no longer projects that conjunct, but its hypothesis type still contains it. This file gives the
hypothesis type without it:

* `CertifiedReferenceModelCore ν 𝒮`: the seventeen other conjuncts, in the same order;
* `CertifiedReferenceModel.toCore`: the full model gives the core;
* core projections, the core variants of the Lemmas 3.3, 3.4, 3.5, 3.6 on the chain (their bodies are those of
  `closed_3_3`, `closed_3_4_hdetSwap`, `closed_3_5_hdetSwap`, `closed_3_6_corrected`, with the truncated quenched laws
  given by `MatedCRT.TruncatedLaws.truncatedQuenchedLawsFixedTime_of_inputs`, `FirstPass/S3t/BLEnvelopeClosure.lean:43`);
* `closed_5_1_canon_noCell_core`: Proposition 5.1 with `hC : CertifiedReferenceModelCore ν 𝒮`, every other binder as in
  `closed_5_1_canon_noCell_derived_closed`.

No new frozen Prop and no new hypothesis: the core is a strengthening of the hypothesis (fewer conjuncts), and the
conclusions are unchanged. Terminology: Armstrong–Kuusi–Mourrat for the obstacle problem; Berestycki–Gwynne for the BG20
Green bound; Duplantier–Sheffield for the LQG measure.
-/

open MeasureTheory Filter Topology Set Metric
open _root_.HarmonicBalls

namespace MatedCRT

/-- The certified reference model without its conjunct `FrozenTruncatedQuenchedLawsFixedTime 𝒮` (conjunct 17 of
`CertifiedReferenceModel`, `FirstPass/SLERef/Certified.lean:54`). The seventeen other conjuncts are in the same order. -/
def CertifiedReferenceModelCore (ν : ℝ → Measure SLEPathCode) (𝒮 : SpaceFillingSLEModel) : Prop :=
  HasNormalizedSLELaw 𝒮 ν ∧
  SLEModelClosureInput 𝒮 ∧
  MepsScalingInput 𝒮 ∧
  DegreeBoundInput 𝒮 ∧
  CellSizeEstimateStmt 𝒮 ∧
  CountingMeasureConvergenceStmt 𝒮 ∧
  DegreeMeasureConvergenceStmt 𝒮 ∧
  FrozenConeScalingLaw 𝒮 ∧
  FrozenLBMGreenOccupationRescaled 𝒮 ∧
  HasReferenceEnvironments 𝒮 ∧
  RandomWalkToLBMStmt 𝒮 ∧
  GreenKernelUpperBoundStmt 𝒮 ∧
  GreenKernelLowerBoundStmt 𝒮 ∧
  ExitTimeUpperBoundStmt 𝒮 ∧
  FrozenDiscreteHolderContinuityCorrected 𝒮 ∧
  BG20Prop51 𝒮 ∧
  FPSimilarityTransferCorrected 𝒮

/-- The full certified reference model gives the core one (the frozen conjunct 17 is dropped). -/
theorem CertifiedReferenceModel.toCore {ν : ℝ → Measure SLEPathCode} {𝒮 : SpaceFillingSLEModel}
    (h : CertifiedReferenceModel ν 𝒮) : CertifiedReferenceModelCore ν 𝒮 := by
  unfold CertifiedReferenceModel at h
  unfold CertifiedReferenceModelCore
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, _, h18⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h18⟩

namespace CertifiedReferenceModelCore

variable {ν : ℝ → Measure SLEPathCode} {𝒮 : SpaceFillingSLEModel}

theorem mepsScaling (h : CertifiedReferenceModelCore ν 𝒮) : MepsScalingInput 𝒮 := h.2.2.1

theorem cellSizeEstimate (h : CertifiedReferenceModelCore ν 𝒮) : CellSizeEstimateStmt 𝒮 := h.2.2.2.2.1

theorem degreeMeasureConvergence (h : CertifiedReferenceModelCore ν 𝒮) : DegreeMeasureConvergenceStmt 𝒮 :=
  h.2.2.2.2.2.2.1

theorem frozenConeScaling (h : CertifiedReferenceModelCore ν 𝒮) : FrozenConeScalingLaw 𝒮 :=
  h.2.2.2.2.2.2.2.1

theorem frozenLBMGreenOccupation (h : CertifiedReferenceModelCore ν 𝒮) : FrozenLBMGreenOccupationRescaled 𝒮 :=
  h.2.2.2.2.2.2.2.2.1

theorem randomWalkToLBM (h : CertifiedReferenceModelCore ν 𝒮) : RandomWalkToLBMStmt 𝒮 :=
  h.2.2.2.2.2.2.2.2.2.2.1

theorem greenKernelUpperBound (h : CertifiedReferenceModelCore ν 𝒮) : GreenKernelUpperBoundStmt 𝒮 :=
  h.2.2.2.2.2.2.2.2.2.2.2.1

theorem greenKernelLowerBound (h : CertifiedReferenceModelCore ν 𝒮) : GreenKernelLowerBoundStmt 𝒮 :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem exitTimeUpperBound (h : CertifiedReferenceModelCore ν 𝒮) : ExitTimeUpperBoundStmt 𝒮 :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem frozenDiscreteHolderContinuityCorrected (h : CertifiedReferenceModelCore ν 𝒮) :
    FrozenDiscreteHolderContinuityCorrected 𝒮 :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

end CertifiedReferenceModelCore

/-- The existence statement `FrozenCertifiedReferenceModelExists` (`FirstPass/SLERef/Certified.lean:80`) gives an
existence statement for the core. -/
theorem FrozenCertifiedReferenceModelExists.core (h : FrozenCertifiedReferenceModelExists) :
    ∃ (ν : ℝ → Measure SLEPathCode) (𝒮 : SpaceFillingSLEModel), CertifiedReferenceModelCore ν 𝒮 := by
  obtain ⟨ν, 𝒮, hC⟩ := h
  exact ⟨ν, 𝒮, hC.toCore⟩

end MatedCRT

namespace MatedCRT.FirstPassClosure

/-- Lemma 3.6 (corrected), core form: `closed_3_6_corrected` (`FirstPass/Closure/Section3.lean:57`) with the core
certified model. -/
theorem closed_3_6_corrected_core {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModelCore ν 𝒮) (hexc : FrozenBrownianOutwardExcursionAtExit) :
    CorrectedHarmonicConvergenceStmt 𝒮 :=
  MatedCRT.FirstPass36.firstPass_3_6_convergence_corrected (𝒮 := 𝒮) hC.randomWalkToLBM hC.cellSizeEstimate
    hC.mepsScaling hexc hC.frozenDiscreteHolderContinuityCorrected

/-- **Corrected Lemma 3.6, closed in the annealed form (core certified model).** The counted conclusion is the
conjunction of the convergence clause `CorrectedHarmonicConvergenceStmt` (`Draft/Section3HarmonicCorrected.lean:29`) and
the annealed same-walk clause `CorrectedHarmonicSameWalkAnnealedStmt` (`FirstPass/S3i/Statement.lean:39`). The Draft rate
clause `CorrectedHarmonicSameWalkRateStmt` (`Draft/Section3HarmonicCorrected.lean:68`) is not used. The proof is
`MatedCRT.FirstPass36.firstPass_3_6_closed` (`FirstPass/S3i/LensClosed.lean:31`), with the frozen inputs `h211`, `h28`,
`hm`, `h32` supplied by the core projections; `hexc` and `hBE` remain binders, since neither is a conjunct of
`CertifiedReferenceModel` (`FirstPass/SLERef/Certified.lean:54`). -/
theorem closed_3_6_annealed_core {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModelCore ν 𝒮) (hexc : FrozenBrownianOutwardExcursionAtExit)
    (hBE : MatedCRT.FirstPass36.FrozenOneSidedBoundaryContinuity 𝒮) :
    CorrectedHarmonicConvergenceStmt 𝒮 ∧ MatedCRT.FirstPass36.CorrectedHarmonicSameWalkAnnealedStmt 𝒮 :=
  MatedCRT.FirstPass36.firstPass_3_6_closed hC.randomWalkToLBM hC.cellSizeEstimate hC.mepsScaling hexc
    hC.frozenDiscreteHolderContinuityCorrected hBE

/-- Lemma 3.4 (integral convergence of the Green function), core form: `closed_3_4_hdetSwap`
(`FirstPass/HdetSwap.lean:65`) with the truncated quenched laws from the four-binder theorem
`MatedCRT.TruncatedLaws.truncatedQuenchedLawsFixedTime_of_inputs` (`FirstPass/S3t/BLEnvelopeClosure.lean:43`), which needs
no closure input. -/
theorem closed_3_4_core {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModelCore ν 𝒮) (h27 : VolumeGrowthStmt)
    (hexc : BrownianOutwardExcursionAtExitStep) : IntegralConvergenceGreenFunctionStmt 𝒮 :=
  MatedCRT.S3S4c.firstPass_3_4 (𝒮 := 𝒮) h27 hC.exitTimeUpperBound hC.mepsScaling hC.frozenLBMGreenOccupation
    (MatedCRT.TruncatedLaws.truncatedQuenchedLawsFixedTime_of_inputs hC.randomWalkToLBM hC.cellSizeEstimate
      hC.mepsScaling hexc)

/-- Lemma 3.3 (uniform convergence of the Green kernel), core form: `closed_3_3` (`FirstPass/Closure/Section3.lean:43`)
with its Lemma 3.4 input `closed_3_4_core`. -/
theorem closed_3_3_core {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModelCore ν 𝒮) (h27 : VolumeGrowthStmt) (hexc : FrozenBrownianOutwardExcursionAtExit) :
    UniformConvergenceGreenKernelStmt 𝒮 :=
  firstPass_3_3 (𝒮 := 𝒮) (h34 := closed_3_4_core ν hC h27 hexc) hC.degreeMeasureConvergence
    hC.greenKernelUpperBound hC.cellSizeEstimate h27 hC.exitTimeUpperBound hC.mepsScaling
    hC.frozenDiscreteHolderContinuityCorrected

/-- Lemma 3.5 (discrete Dirichlet problem, corrected), core form: `closed_3_5_hdetSwap` (`FirstPass/S5qd.lean:175`) with the
core certified model. -/
theorem closed_3_5_core {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModelCore ν 𝒮) (h27 : VolumeGrowthStmt) (hexc : FrozenBrownianOutwardExcursionAtExit) :
    DiscreteDirichletProblemCorrectedStmt 𝒮 :=
  firstPass_3_5_corrected (𝒮 := 𝒮) h27 hC.mepsScaling hC.degreeMeasureConvergence
    (closed_3_4_core ν hC h27 hexc) hC.greenKernelUpperBound hC.cellSizeEstimate hC.exitTimeUpperBound
    hC.frozenDiscreteHolderContinuityCorrected MatedCRT.FirstPass37.frozenFiniteDomainDirichletRepresentation_proved
    (closed_3_6_corrected_core ν hC hexc)

open _root_.HarmonicBalls MeasureTheory Set Filter Topology in
/-- **Proposition 5.1 (closure with the canonical BG20 Green bound and the proved cell adjacency), core form.** Same
conclusion and binders as `closed_5_1_canon_noCell_derived_closed` (`FirstPass/S5qd.lean:192`), with the hypothesis
`hC : CertifiedReferenceModel ν 𝒮` replaced by `hC : CertifiedReferenceModelCore ν 𝒮`, which omits the frozen conjunct
`FrozenTruncatedQuenchedLawsFixedTime 𝒮`. The Lemmas 3.3, 3.4, 3.5 on the chain are `closed_3_3_core`, `closed_3_4_core`,
`closed_3_5_core`. -/
theorem closed_5_1_canon_noCell_core {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModelCore ν 𝒮)
    -- FIRST-PASS FROZEN inputs
    (hμae : FrozenLQGMeasureFieldMeasurable 𝒮) (hSB : FrozenFiniteMeasureDiskStandardBorel)
    (hsup : FrozenLeastSupersolutionMemCone 𝒮)
    (hU : FrozenUniversalMeasurabilityOfAnalytic) (hexc : FrozenBrownianOutwardExcursionAtExit)
    (hG : FrozenGreenDiscPole) (hmodel : FPWholePlaneLQGModel) (hFL : FPConeWholePlaneFieldLaw)
    (hLoc : FPLQGMeasureLocality) (hpair : FPPairingLawIG4) (hmeasT : FrozenLQGTestIntegralMeasurable)
    (hstd : FrozenConeLogLocalCodeLawStd) (hmin : FrozenSuperharmonicMinimumPrinciple)
    (hGBC : FrozenGreenBallCentre) (hconf : FrozenHBInitialConfinement)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    -- TRUE steps (chat 180 §3)
    (hE1 : ConeCircleLawUniqueStep) (hE2 : ConeReferenceExistsStep)
    -- External input
    (hscale : QuantumConeScalingInput)
    -- gaps still typed by Stmts
    (h27 : VolumeGrowthStmt) (h22 : LQGMeasurePropertiesStmt)
    (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt)
    -- canonical Berestycki–Gwynne Green bound (replaces the cited Lemma 2.15 input `hG15`)
    (hcanon : FrozenBG20GreenCrudeCanonical 𝒮)
    -- cited gaps, typed by the frozen names (FirstPass/Frozen/S5Cited.lean)
    (h32 : ClusterOpenLaplacianStmt.{0}) (h611 : FrozenVeryGoodAnnulusHarnackType)
    (h82 : FrozenTypicalPointManyGoodScales) (hI2 : FrozenLQGVolumeGrowthAllScales)
    (hSup : LeastSupersolutionMemStmt.{0}) (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0}) (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : FrozenClusterBoundaryMeasureZero) (hEx : FrozenExistenceHarmonicBalls)
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}) (hProp56 : FrozenUniquenessHarmonicBalls)
    (hloc : FrozenHarmonicBallLocalSet) (hSC : FrozenClusterStrongCompatibility) :
    IDLALowerBoundStmt 𝒮 := by
  have hcell : FrozenAdjacentCellsMeetAe 𝒮 := MatedCRT.adjacentCellsMeetAeStep 𝒮
  have hG15 : GreenFunctionCrudeBoundStmt 𝒮 := MatedCRT.greenFunctionCrudeBound_of_canonical 𝒮 hcanon hcell
  have h35 : DiscreteDirichletProblemStmt 𝒮 :=
    MatedCRT.FirstPass35Bridge.discreteDirichletProblem_of_corrected hC.cellSizeEstimate
      (firstPass_2_13 (𝒮 := 𝒮) hcell) (closed_3_5_core ν hC h27 hexc)
  have h41 : ConvergenceDivisibleStmt 𝒮 :=
    firstPass_4_1_coneLaw hC.mepsScaling hC.degreeMeasureConvergence (closed_3_4_core ν hC h27 hexc)
      hC.greenKernelUpperBound hC.cellSizeEstimate h35 hC.exitTimeUpperBound h27
      hC.frozenDiscreteHolderContinuityCorrected hC.frozenConeScaling
  exact firstPass_5_1_derived_closed 𝒮 hμae hSB hsup h27 hC.cellSizeEstimate hE1 hE2 hscale h22 h24c
    hC.exitTimeUpperBound
    hU hC.mepsScaling hC.degreeMeasureConvergence hC.greenKernelUpperBound hC.randomWalkToLBM
    hC.frozenLBMGreenOccupation hexc h35 hC.frozenDiscreteHolderContinuityCorrected hC.frozenConeScaling
    hG hG15 hC.greenKernelLowerBound h41
    (closed_3_3_core ν hC h27 hexc)
    h32 h611 h82 hI2 hmodel hFL hLoc hpair hmeasT hstd hmin
    hGBC HarmonicBalls.greenFunctionBall hSup hCons hMono hCompat hBdry hEx hThm11 hProp56 hconf hK hloc hSC hE

#print axioms MatedCRT.CertifiedReferenceModel.toCore
#print axioms MatedCRT.FrozenCertifiedReferenceModelExists.core
#print axioms MatedCRT.FirstPassClosure.closed_3_3_core
#print axioms MatedCRT.FirstPassClosure.closed_3_5_core
#print axioms MatedCRT.FirstPassClosure.closed_5_1_canon_noCell_core
#print axioms MatedCRT.FirstPassClosure.closed_3_6_annealed_core

end MatedCRT.FirstPassClosure
