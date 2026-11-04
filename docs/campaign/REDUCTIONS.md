# REDUCTIONS: the current reduction of each numbered result

Checked by `MatedCRT/Audit/Reductions.lean`: one `example` per line below restates the reduction with exactly these
hypotheses, so a drift of a Draft statement, a reducing theorem or a step breaks the build. Paths are relative to
`MatedCRT/`; line numbers point at the `theorem` line, from the 2026-11-04 15:00Z tree (read from the environment by an
untracked probe). Proved steps are discharged and not listed. Format: result Stmt: reducing theorem (file:line) |
Draft: other numbered results used | External: literature inputs (MatedCRT/External) | Steps: open step Props (owner).

Owners: from STATUS.md, tasks/*.md and reports/*.md as of 2026-11-04 15:00Z. "cited" = a cited result of the paper,
used only as a hypothesis (Draft Stmt), never proved here. Since 028f2dc (x4) `AdjacentCellsMeetAeStep` is PROVED
(`adjacentCellsMeetAeStep`, Proofs/MatingOfTrees/AdjacentCells.lean:17, on Leonardo Bonanno's mating-of-trees bundle)
and is discharged everywhere.

## Proved (no hypotheses)
2.13 MaximumPrincipleStmt: maximumPrinciple_of_steps (Steps/Sec2/MaximumPrinciple.lean:22) + adjacentCellsMeetAeStep
6.3 AbelianIDLAStmt: AbelianIDLA.abelianIDLA (Proofs/Sec6/AbelianIDLA/Statement.lean:119)
6.6 AnnulusIterateStmt (cited, proved): annulusIterate (Proofs/Field/LawTransferComplete.lean:71; x4, d241056: Leo's
  lmLem3_1a + annulusGFFLawTransfer)
A.1 DiscreteDivergenceTheoremStmt: discreteDivergenceTheorem (Proofs/SecA/DiscreteDivergence.lean:54)
A.2-A.4: discreteBasicPropertiesGeneral, discreteLaplacianBoundGeneral, discreteConservationOfMassGeneral
  (Proofs/SecA/Statements.lean:62, 66, 71)

## Reduced
1.4 ConvergenceOfIDLAStmt: convergenceOfIDLA_of_steps (Steps/Sec1/Convergence.lean:206) | Draft: 8.1 | External: - |
  Steps: ConeEnvironmentScalingStep, HarmonicBallFamilyScalingStep, ConeScaleRadiusStep, ScaledClusterExitTimeStep (m1)
1.6 ConvergenceOfDivSandpileStmt: convergenceOfDivSandpile_of_steps (:237) | as 1.4
8.1 IDLAConstrainedConvergenceStmt: iDLAConstrainedConvergence_of_steps (Steps/Sec8/IDLAConstrainedConvergence.lean:27)
  | Draft: 4.2, 5.1, 6.1, 7.1 | External: - | Steps: -
2.3 ConeHarmonicBallsStmt: coneHarmonicBalls_of_steps (Steps/Sec2/ConeHarmonicBalls.lean:64) | Draft: 2.4, 2.5 |
  Steps: ConeFamilyAEMeasurableStep (A)
2.17 BoundedExitTimeRVStmt: boundedExitTimeRV_of_steps (Steps/Sec2/BoundedExitTimeRV.lean:26) | Draft: 2.7 (cited)
2.19 ExpectedExitTimeExplicitBoundStmt: expectedExitTimeExplicitBound_of_steps (Steps/Sec2/ExpectedExitTimeExplicit
  Bound.lean:44) after 2.17 | Draft: 2.7, 2.18 (both cited) | Steps: -
3.1 corrected (E-c1-4 D open; review-L32 N1, N3) DiscretePotentialTightnessCorrectedStmt: discretePotentialTightness_
  of_steps (Steps/Sec3/DiscretePotentialTightness.lean:192) | Steps: TightnessEquicontinuityStep, TightnessSelection
  Step (c1; both proved in UNTRACKED Proofs/Sec3/DiscretePotentialTightness/*). The Draft 3.1 has no reduction.
3.3 UniformConvergenceGreenKernelStmt: uniformConvergenceGreenKernel_of_steps (Steps/Sec3/UniformConvergenceGreenKernel
  .lean:50) | Draft: 2.10, 3.4, 2.14, 2.8, 3.1 (Draft, E-c1-4), 2.13 | Steps: GreenKernelInteriorStep,
  GreenKernelBoundaryStep (m1)
3.5 DiscreteDirichletProblemStmt: discreteDirichletProblem_of_steps (Steps/Sec3/DiscreteDirichletProblem.lean:98) |
  Draft: 3.6, 3.4, 3.1 corrected, 2.13, 2.19, 2.8; HB: HarmonicBalls.GreenPotentialHolderStmt (cited, HB Draft) |
  Steps: DirichletLimitStep, DirichletInteriorStep, DirichletBoundaryStep (m1)
3.6 ConvergenceHarmonicFunctionsStmt: convergenceHarmonicFunctions_of_steps (Steps/Sec3/ConvergenceHarmonicFunctions
  .lean:53) | Draft: 2.11, 2.8 (cited) | Steps: HarmonicPathExitStep, HarmonicExitCellStep (m2)
3.7 ConvergenceNormalizedExitTimeStmt: convergenceNormalizedExitTime_of_interior_discrete_boundary (Proofs/Sec3/
  ConvergenceNormalizedExitTime/OfInteriorBoundary.lean:10) | Draft: 3.3, 2.9, 2.19, 3.5, 3.1 (Draft, E-c1-4), 2.8,
  2.17 | Steps: NormalizedExitInteriorStep, DiscreteExitBoundaryStep (x1)
4.1 ConvergenceDivisibleStmt: convergenceDivisible_of_steps (Steps/Sec4/ConvergenceDivisible.lean:148), uniqueness by
  obstacleLimitUniqueness (Proofs/Sec4/ConvergenceDivisible/MaximumPrinciple.lean:166, x3) | Draft: 4.6, 4.8 |
  Steps: ConvergenceDivisibleEventMeasurableStep (x3; see F8)
4.2 DivSandpileLowerBoundStmt: divSandpileLowerBound_of_steps (Steps/Sec4/DivSandpileLowerBound.lean:48), with
  divSandpileOdometerComparison_of_cellsMeet (Proofs/Sec4/DivSandpileLowerBound/OdometerComparison.lean:100) |
  Draft: 4.1, 2.3, 2.13, 3.3, 2.8 (cited) | Steps: ObstacleClusterInnerApproximationStep (x3; E-x3-1)
4.3 DiscreteBasicPropertiesStmt: discreteBasicProperties_of_inputs (Proofs/Sec4/ObstacleSpecialization.lean:102) |
  Steps: BallInteriorConnectedStep (c1; E-c1-2)
4.4 corrected (E-c1-1) DiscreteLaplacianBoundCorrectedStmt: discreteLaplacianBoundCorrected_of_inputs (:110) | Steps:
  BallInteriorConnectedStep (c1). The Draft 4.4 (OPEN) has no reduction.
4.5 corrected (E-c1-1) DiscreteConservationOfMassCorrectedStmt: discreteConservationOfMassCorrected_of_inputs (:117) |
  as 4.4 corrected
4.6 SubsequentialConvergenceStmt: subsequentialConvergence_of_steps (Steps/Sec4/SubsequentialConvergence.lean:61) |
  Draft: 4.7, 4.4 (Draft, E-c1-1), 3.1 (Draft, E-c1-4), 3.5 | Steps: OdometerLocalCompactnessStep,
  OdometerBoundaryUpgradeStep, OdometerMeasurableSelectionStep (x3; E-x3-2)
4.7 EquiboundedStmt: equibounded_of_steps (Proofs/Sec4/Equibounded.lean:227) | Draft: 4.3, 2.17, 2.18 (cited) |
  External: MepsScalingInput (External/SLE.lean) | Steps: -
4.8 SubsequentialPropertiesStmt: subsequentialProperties_of_steps (Steps/Sec4/SubsequentialProperties.lean:58) |
  Draft: 3.3, 3.5, 3.7, 4.6, 4.3, 4.4 (Draft, E-c1-1), 2.13 | Steps: OdometerObstacleApproximationStep,
  OdometerDistributionalLimitStep (x3)
5.1 IDLALowerBoundStmt: iDLALowerBound_of_inputs (Proofs/Sec5/IDLALowerBound/Statement.lean:24), with
  discreteClusterInnerBound_of_steps (Steps/Sec5/IDLALowerBound.lean) | Draft: 2.7, 2.8 (cited), 5.3, 5.4, 4.1, 2.3,
  2.13, 3.3 | Steps: EnvSigmaMeasurableStep (c2; E-c2-1), ObstacleClusterInnerApproximationStep (x3),
  IDLALowerBoundStoppedStep (c2)
5.2 GeneralIDLALowerBoundStmt: generalIDLALowerBound_of_inputs (Proofs/Sec5/GeneralIDLALowerBound/Statement.lean:27) |
  Draft: 2.7, 2.8 (cited) | Steps: EnvSigmaMeasurableStep (c2; E-c2-1)
5.3 MeanValueInequalityStmt: meanValueInequality_of_surplus (Proofs/Sec5/MeanValueInequality/NormalizedStep.lean:85) |
  Draft: 4.4 corrected, 2.13, 4.1, 3.3, 2.18 (cited) | Steps: MeanValueSurplusStep (x1; E-x1-1)
5.4 LLowerBoundStmt: lLowerBound_of_adjacentCellsMeet (Proofs/Sec5/LLowerBound/OfEvents.lean:96) | Draft: 2.15, 2.16,
  2.9 (all cited) | Steps: -
6.1 IDLAUpperBoundStmt: IDLAUpperBound.iDLAUpperBound_of_steps (Proofs/Sec6/IDLAUpperBound/OfSteps.lean:183) |
  Draft: 6.10, 5.1 | Steps: BoundaryLayerMeasurableStep (c2; E-c2-3)
6.4 GoodAnnulusPrevalenceStmt: goodAnnulusPrevalence_of_restriction (Proofs/Sec6/GoodAnnulusPrevalence/ConeTransfer
  .lean:160) | Draft: 6.6 (proved), 6.5 | Steps: ConeMeanZeroRestrictionStep, GoodAnnulusEventLocalityStep (c4; the
  latter proved from CircleAverageModConstStep in UNTRACKED Locality.lean)
6.5 AnnulusHitStmt: annulusHit_of_steps (Steps/Sec6/AnnulusHit.lean:89) | Steps: WholePlaneLQGExistenceStep,
  ConeWholePlaneWeylComparisonStep, WholePlaneLQGCoordinateChangeStep, WholePlaneGoodAnnulusTightnessStep (c4)
6.7 ConstantOrderLowerBoundStmt: constantOrderLowerBound (Proofs/Sec6/ConstantOrderLowerBound/Statement.lean:17) |
  Draft: 6.8 (Draft, see F3), 2.7, 2.8, 2.19 | Steps: -
6.7 (b) ConstantOrderLowerBoundLogStmt: constantOrderLowerBoundLog (Proofs/Sec6/ConstantOrderLowerBound/LogLoss.lean:60)
  | Draft: 6.8 (b), 2.7, 2.8, 2.19 | Steps: -
6.8 (b) ConstantOrderLowerBoundDivLogStmt: constantOrderLowerBoundDiv_of_steps (Proofs/Sec6/ConstantOrderLowerBoundDiv/
  OfSteps.lean:198) | Draft: 2.16, 2.7, 2.8, 2.9, 6.4, 2.18, 2.19 | Steps: GoodScaleEventMeasurableStep (c4). The
  Draft 6.8 has no reduction.
6.9 local rate (E-c5-1) ChanceOfBeingAbsorbedLocalRateStmt: chanceOfBeingAbsorbedLocalRate (Proofs/Sec6/ChanceOfBeing
  Absorbed/Chernoff.lean:387) | Draft: 6.7 | Steps: -. The Draft 6.9 implies it but has no reduction.
6.9 (b) ChanceOfBeingAbsorbedLogLossStmt: chanceOfBeingAbsorbedLogLoss_of_steps (Proofs/Sec6/ChanceOfBeingAbsorbed/
  LogLoss.lean:22) | Draft: 6.7 (b) | Steps: -
6.10 IterativeBoundStmt: iterativeBound_of_div (Proofs/Sec6/IterativeBound/Statement.lean:48) through 6.7 (b), 6.9 (b)
  | Draft: 6.8 (b), 2.7, 2.8, 2.19 | Steps: -. Expanded (iterativeBound_of_inputs, :56): 2.16, 2.7, 2.8, 2.9, 6.4,
  2.18, 2.19 + GoodScaleEventMeasurableStep (c4)
7.1 DivSandpileUpperBoundStmt (example disabled, F6): divSandpileUpperBound_of_carved_inputs (Steps/Sec7/DivSandpile
  UpperBound.lean:164) | Draft: 2.3, 6.8 (Draft, F3), 2.7, 7.2 (Draft, REFUTED E-c3-2, F1), 4.1, 3.3, 2.8, 7.3, 7.4 |
  Steps: StoppedObstacleSetupStep, StoppedShellConfinementStep (x2)
7.2 corrected (E-c3-2) MassBoundOdometerAboveScaleStmt: massBoundOdometerAboveScale_of_draft (Steps/Sec7/MassBound
  Odometer.lean:158) | Draft: 2.16, 2.8, 4.4 (Draft, E-c1-1) | Steps: -. The Draft 7.2 is false (E-c3-2).
7.3 OdometerBoundMassStmt: odometerBoundMass_of_draft (Steps/Sec7/OdometerBoundMass.lean:175) | Draft: 4.4 (Draft) |
  Steps: -
7.4 CrudeUpperBoundStmt: crudeUpperBound_of_draft (Steps/Sec7/CrudeUpperBound.lean:83) | Draft: 4.4 (Draft) |
  External: DegreeBoundInput (External/SLE.lean) | Steps: -

## No committed reduction
Paper-owned: 2.4, 2.5, 2.6 (c5; 2.4's reduction is in UNTRACKED Steps/Sec2/ConeHarmonicBallsUpToFixedTime.lean), 3.4
(m2; partial 20a59de). Draft forms with only a corrected form reduced: 3.1 (E-c1-4), 4.4, 4.5 (E-c1-1), 6.8 (E-A10),
6.9 (E-c5-1), 7.2 (E-c3-2). Cited (hypotheses only): 2.2, 2.7, 2.8, 2.9, 2.10, 2.11, 2.14, 2.15, 2.16, 2.18, 3.2
((L2) ruling pending).

## Findings (consumers of false or open Draft forms; build issues)
F1. 7.1 consumes the Draft 7.2 `MassBoundOdometerStmt`, refuted by E-c3-2: vacuous until rerouted through
  `MassBoundOdometerAboveScaleStmt` (x2; c3's form needs `s ≥ ε^β`, enough for tex 3168-3192).
F2. The Draft 4.4 (OPEN, E-c1-1: false for large ε) is consumed by 4.6, 4.8, 7.2 corrected, 7.3, 7.4 (only its first
  conjunct, c3). Reroute to `DiscreteLaplacianBoundCorrectedStmt` (x3 for 4.6, 4.8; c3 for 7.2-7.4), or the operator
  replaces the Draft 4.4.
F3. E-A10 (b): 6.8 is proved only in the log form; the chain 6.8 (b) -> 6.7 (b) -> 6.9 (b) -> 6.10 is closed. Still on
  the Draft 6.8: the Draft-form 6.7, the 6.9 local rate and 7.1 (x2 needs a log-loss form of its 6.8 use).
F4. RESOLVED: `AdjacentCellsMeetAeStep` proved (x4, 028f2dc); dropped from 2.13, 4.2-4.5, 5.4, 6.7, 6.8, 6.10, 7.1-7.4.
F5. Working tree: Proofs/Sec4/ObstacleSpecialization.lean (4.3-4.5) and Steps/Sec6/GoodAnnulusPrevalence.lean (6.4
  steps) are modified and uncommitted; this audit was checked against the working tree (15:00Z).
F6. OPEN: `MatedCRT.Sec7.vertexPoint_mem_cell` is declared in Proofs/Sec7/DivSandpileUpperBound/CrudeCells.lean:11
  (x2) and Proofs/Sec7/MassBoundOdometer/Count.lean:28 (c3): the 7.1 and 7.2-7.4 modules cannot be imported together
  (Theorem 1.6 needs both). Fix: x2 or c3 renames (Proofs/Sec3/DiscretePotentialTightness/Cells.lean and
  Proofs/Sec6/ConstantOrderLowerBoundDiv/Geometry.lean have further copies; DUPLICATES.md).
F7. NEW: the Draft 3.1 (false for non-open D, E-c1-4) is consumed by 3.3 (m1), 3.7 (x1) and 4.6 (x3); 3.5 already
  uses the corrected form. Reroute to `DiscretePotentialTightnessCorrectedStmt` (its N3 clause asks the scales to lie
  in a deterministic polynomially summable sequence: consumers thin first), or the operator restates the Draft 3.1.
F8. 4.1: `ConvergenceDivisibleEventMeasurableStep` is reduced (x3, tracked) to unnamed hypotheses only: a.s. volume
  growth on every ball B_R (EventMeasurableOfVolumeGrowth.lean:13; Lemma 2.7 is drafted for the unit ball) or
  null-measurability of the cluster exit events (LocalExitReduction.lean:67, with Lemma 2.7). Still open.
F9. Untracked work not in this ledger: x3 Proofs/Sec4/DivSandpileLowerBound/OdometerComparisonProved.lean and
  ConvergenceDivisible/FromInputs.lean; c1 Proofs/Sec3/DiscretePotentialTightness/{Main, SelectionStep, Equicontinuity,
  ...}; c4 Proofs/Sec6/GoodAnnulusPrevalence/{Locality, EventCountable}; c5 Steps/Sec2/ConeHarmonicBallsUpToFixedTime.

## Counts (2026-11-04 15:00Z)
56 numbered results. Proved: 7 (2.13, 6.3, 6.6, A.1-A.4). Reduced (committed reduction, checked by an example): 34
(1.4, 1.6, 2.3, 2.17, 2.19, 3.1 corrected, 3.3, 3.5, 3.6, 3.7, 4.1-4.3, 4.4 corrected, 4.5 corrected, 4.6-4.8,
5.1-5.4, 6.1, 6.4, 6.5, 6.7 (Draft and (b)), 6.8 (b), 6.9 (local rate and (b)), 6.10, 7.1 (example disabled, F6),
7.2 corrected, 7.3, 7.4, 8.1). Of these, reduced to Draft Stmts and External inputs only (no open step): 11 (2.17,
2.19, 4.7, 5.4, 6.7, 6.9, 6.10, 7.2 corrected, 7.3, 7.4, 8.1); 5.4 rests on cited results only. Cited, hypotheses
only: 11. No committed reduction (paper-owned): 4 (2.4, 2.5, 2.6, 3.4). Distinct open step Props: 37 (A 1, c1 3,
m1 9, m2 2, x1 3, x3 7, c2 3, c4 7, x2 2). External inputs used: MepsScalingInput (4.7), DegreeBoundInput (7.4);
HB cited: GreenPotentialHolderStmt (3.5).
