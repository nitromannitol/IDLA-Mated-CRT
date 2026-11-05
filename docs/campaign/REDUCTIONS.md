# REDUCTIONS: the current reduction of each numbered result

Checked by `MatedCRT/Audit/Reductions.lean`: one `example` per line below restates the reduction with exactly these
hypotheses, so a drift of a Draft statement, a reducing theorem or a step breaks the build. Paths are relative to
`MatedCRT/`; line numbers point at the `theorem` line, from the 2026-11-05 00:40Z tree (read from the environment by
untracked probes). Proved steps are discharged and not listed. Format: result Stmt: reducing theorem (file:line) |
Draft: other numbered results used | External: literature inputs | Steps: open step Props (owner).

Owners: from STATUS.md, tasks/*.md and reports/*.md as of 2026-11-04 20:05Z. "cited" = a cited result of the paper,
used only as a hypothesis (Draft Stmt), never proved here. Proved and discharged everywhere: `AdjacentCellsMeetAeStep`
(x4, 028f2dc, Leonardo Bonanno's mating-of-trees bundle), the uniqueness steps of Theorem 4.1 (x3), the odometer
comparison of Proposition 4.2 (x3), `EnvSigmaMeasurableStep` is no longer needed (727dab9).

## Proved (no hypotheses)
2.13 MaximumPrincipleStmt: maximumPrinciple_of_steps (Steps/Sec2/MaximumPrinciple.lean:22) + adjacentCellsMeetAeStep
6.3 AbelianIDLAStmt: AbelianIDLA.abelianIDLA (Proofs/Sec6/AbelianIDLA/Statement.lean:119)
6.6 AnnulusIterateStmt (cited, proved): annulusIterate (Proofs/Field/LawTransferComplete.lean:71; x4, Leo's lmLem3_1a)
A.1 DiscreteDivergenceTheoremStmt: discreteDivergenceTheorem (Proofs/SecA/DiscreteDivergence.lean:54)
A.2-A.4: discreteBasicPropertiesGeneral, discreteLaplacianBoundGeneral, discreteConservationOfMassGeneral
  (Proofs/SecA/Statements.lean:62, 66, 71)

## Reduced
1.4 ConvergenceOfIDLAStmt: convergenceOfIDLA_of_steps (Steps/Sec1/Convergence.lean:206) | Draft: 8.1 | Steps:
  ConeEnvironmentScalingStep, HarmonicBallFamilyScalingStep, ConeScaleRadiusStep, ScaledClusterExitTimeStep (m1)
1.6 ConvergenceOfDivSandpileStmt: convergenceOfDivSandpile_of_steps (:237) | as 1.4
8.1 IDLAConstrainedConvergenceStmt: iDLAConstrainedConvergence_of_steps (Steps/Sec8/IDLAConstrainedConvergence.lean:27)
  | Draft: 4.2, 5.1, 6.1, 7.1 | Steps: -
2.2 LQGMeasurePropertiesStmt (cited): LQGMeasure.lqgMeasureProperties_of_steps (Proofs/Sec2/LQGMeasureProperties/
  Locality.lean:174; 102275a) | cited parts LQGMeasureNonAtomicPart, LQGMeasureDilationCovariancePart (Steps/Sec2/
  LQGMeasureProperties.lean:32, 86; NOT in External, F11) | Steps: ConeCircleAverageLocalityStep (:58)
2.3 ConeHarmonicBallsStmt: coneHarmonicBalls_of_inputs (Proofs/Sec2/ConeScaleInvarianceUpToFixedTime/Main.lean:61; c5,
  a0d10e4; NOT checked, F10) | Draft: 2.2 | External: QuantumConeScalingInput | Steps: the six steps of 2.4,
  ConeScaleRadiusPosStep, ConeRescaledCircleAEMeasurableStep, ConeHalfBallFamilyFunctionalStep (c5). Checked:
  coneHarmonicBalls_of_steps (Steps/Sec2/ConeHarmonicBalls.lean:64) from 2.4, 2.5 and ConeFamilyAEMeasurableStep
  (now derived, coneFamilyAEMeasurableStep_of_steps, Main.lean:30)
2.4 ConeHarmonicBallsUpToFixedTimeStmt: coneHarmonicBallsUpToFixedTime_of_steps (Steps/Sec2/ConeHarmonicBallsUpTo
  FixedTime.lean:278) | Steps: WholePlaneLogLQGExistenceStep, WholePlaneConeHarmonicBallsStep, WholePlaneHarmonicBalls
  SmallTimeStep, ConeRestrictionStep, ConeHarmonicBallLocalityStep, ConeHarmonicBallStrictGrowthStep (c5)
2.5 ConeScaleInvarianceUpToFixedTimeStmt (example disabled, F10): coneScaleInvarianceUpToFixedTime_of_inputs (Proofs/
  Sec2/ConeScaleInvarianceUpToFixedTime/Main.lean:21) | Draft: 2.2 | External: QuantumConeScalingInput | Steps:
  ConeScaleRadiusPosStep, ConeHarmonicBallStrictGrowthStep (E-c5-3), ConeRescaledCircleAEMeasurableStep,
  ConeHalfBallFamilyFunctionalStep (c5)
2.6 ConeScaleInvarianceStmt (example disabled, F10): coneScaleInvariance_of_inputs (Proofs/Sec2/ConeScaleInvariance/
  Main.lean:14) | Draft: 2.2 | External: QuantumConeScalingInput | Steps: ConeScaleRadiusPosStep,
  ConeRescaledCircleAEMeasurableStep, ConeHarmonicBallFunctionalStep (c5)
2.17 BoundedExitTimeRVStmt: boundedExitTimeRV_of_steps (Steps/Sec2/BoundedExitTimeRV.lean:26) | Draft: 2.7 (cited)
2.19 ExpectedExitTimeExplicitBoundStmt: expectedExitTimeExplicitBound_of_steps (Steps/Sec2/ExpectedExitTimeExplicit
  Bound.lean:44) after 2.17 | Draft: 2.7, 2.18 (both cited) | Steps: -
3.1 corrected (E-c1-4 D open; review-L32 N1, N3) DiscretePotentialTightnessCorrectedStmt: discretePotentialTightness_
  of_inputs (Proofs/Sec3/DiscretePotentialTightness/Main.lean:19) | Draft: 2.17, 2.18 | External: MepsScalingInput |
  awaiting (L2) ruling: DiscreteHolderContinuityCorrectedStep (corrected cited Lemma 3.2, review-L32) | Steps: -.
  The Draft 3.1 (false, E-c1-4) has no reduction.
3.3 UniformConvergenceGreenKernelStmt: uniformConvergenceGreenKernel_of_steps (Steps/Sec3/UniformConvergenceGreenKernel
  .lean:50) | Draft: 2.10, 3.4, 2.14, 2.8, 3.1 (Draft, F7), 2.13 | Steps: GreenKernelInteriorStep (m1),
  GreenKernelBoundaryStep (m1; PROVED, greenKernelBoundaryStep in Proofs/Sec3/UniformConvergenceGreenKernel/
  BoundaryStep.lean:16, not importable here, F12)
3.5 DiscreteDirichletProblemStmt: discreteDirichletProblem_of_steps (Steps/Sec3/DiscreteDirichletProblem.lean:98) |
  Draft: 3.6, 3.4, 3.1 corrected, 2.13, 2.19, 2.8; HB cited: HarmonicBalls.GreenPotentialHolderStmt | Steps:
  DirichletLimitStep, DirichletInteriorStep, DirichletBoundaryStep (m1)
3.6 ConvergenceHarmonicFunctionsStmt: convergenceHarmonicFunctions_of_steps (Steps/Sec3/ConvergenceHarmonicFunctions
  .lean:53) | Draft: 2.11, 2.8 (cited) | Steps: HarmonicPathExitStep, HarmonicExitCellStep (m2)
3.7 ConvergenceNormalizedExitTimeStmt: convergenceNormalizedExitTime_of_interior_discrete_boundary (Proofs/Sec3/
  ConvergenceNormalizedExitTime/OfInteriorBoundary.lean:10) | Draft: 3.3, 2.9, 2.19, 3.5, 3.1 (Draft, F7), 2.8, 2.17 |
  Steps: NormalizedExitInteriorStep, DiscreteExitBoundaryStep (x1)
4.1 ConvergenceDivisibleStmt: convergenceDivisible_of_scaling (Proofs/Sec4/ConvergenceDivisible/ConeScalingPositivity
  .lean:105) | Draft: 4.6, 4.8, 2.7 | Steps: ConeEnvironmentScalingStep (m1; shared with 1.4, 1.6). Also checked:
  convergenceDivisible_of_steps (Steps/Sec4/ConvergenceDivisible.lean:148) with ConvergenceDivisibleEventMeasurableStep.
4.2 DivSandpileLowerBoundStmt: divSandpileLowerBound_of_inputs (Proofs/Sec4/DivSandpileLowerBound/OdometerComparison
  Proved.lean:15) | Draft: 4.1, 2.3, 2.13, 3.3, 2.8 | Steps: ObstacleClusterInnerApproximationStep (x3; E-x3-1)
4.3 DiscreteBasicPropertiesStmt: discreteBasicProperties_of_inputs (Proofs/Sec4/ObstacleSpecialization.lean:102) |
  Steps: BallInteriorConnectedStep (c1; E-c1-2)
4.4 corrected (E-c1-1) DiscreteLaplacianBoundCorrectedStmt: discreteLaplacianBoundCorrected_of_inputs (:110) | Steps:
  BallInteriorConnectedStep (c1). The Draft 4.4 is false (Audit/CorrectedForms.lean not_discreteLaplacianBoundStmt).
4.5 corrected (E-c1-1) DiscreteConservationOfMassCorrectedStmt: discreteConservationOfMassCorrected_of_inputs (:117) |
  as 4.4 corrected (Draft 4.5 false: not_discreteConservationOfMassStmt)
4.6 SubsequentialConvergenceStmt: subsequentialConvergence_of_steps (Steps/Sec4/SubsequentialConvergence.lean:61) |
  Draft: 4.7, 4.4 (Draft, false, F2), 3.1 (Draft, F7), 3.5 | Steps: OdometerLocalCompactnessStep,
  OdometerBoundaryUpgradeStep, OdometerMeasurableSelectionStep (x3; E-x3-2)
4.7 EquiboundedStmt: equibounded_of_steps (Proofs/Sec4/Equibounded.lean:227) | Draft: 4.3, 2.17, 2.18 (cited) |
  External: MepsScalingInput | Steps: -
4.8 SubsequentialPropertiesStmt: subsequentialProperties_of_steps (Steps/Sec4/SubsequentialProperties.lean:58) |
  Draft: 3.3, 3.5, 3.7, 4.6, 4.3, 4.4 (Draft, false, F2), 2.13 | Steps: OdometerObstacleApproximationStep,
  OdometerDistributionalLimitStep (x3)
5.1 IDLALowerBoundStmt: iDLALowerBound_of_volumeGrowth_cellSize (Proofs/Measurability/EnvSigma.lean:223), with
  discreteClusterInnerBound_of_steps (Steps/Sec5/IDLALowerBound.lean:80) | Draft: 2.7, 2.8 (cited), 5.3, 5.4, 4.1,
  2.3, 2.13, 3.3 | Steps: ObstacleClusterInnerApproximationStep (x3), IDLALowerBoundStoppedStep (c2)
5.2 GeneralIDLALowerBoundStmt: generalIDLALowerBound_of_volumeGrowth_cellSize (Proofs/Measurability/EnvSigma.lean:217)
  | Draft: 2.7, 2.8 (cited) | Steps: - (E-c2-1 resolved without a step, 727dab9)
5.3 MeanValueInequalityStmt: meanValueInequality_of_surplus (Proofs/Sec5/MeanValueInequality/NormalizedStep.lean:85) |
  Draft: 4.4 corrected, 2.13, 4.1, 3.3, 2.18 (cited) | Steps: MeanValueSurplusStep (x1; E-x1-1)
5.4 LLowerBoundStmt: lLowerBound_of_inputs (Proofs/Sec5/LLowerBound/OfInputs.lean:14) | Draft: 2.15, 2.16, 2.9 (all
  cited) | Steps: -
6.1 IDLAUpperBoundStmt: IDLAUpperBound.iDLAUpperBound_of_steps (Proofs/Sec6/IDLAUpperBound/OfSteps.lean:183) |
  Draft: 6.10, 5.1 | Steps: BoundaryLayerMeasurableStep (c2; E-c2-3)
6.4 GoodAnnulusPrevalenceStmt: goodAnnulusPrevalence_of_annulusHit (Proofs/Sec6/GoodAnnulusPrevalence/Main.lean) |
  Draft: 6.5 (6.6 proved) | Steps: ConeMeanZeroRestrictionStep (Steps/Sec6/GoodAnnulusPrevalence.lean),
  CircleAverageModConstStep (:76) (c4)
6.5 AnnulusHitStmt: annulusHit_of_volumeTail (Proofs/Sec6/AnnulusHit/Main.lean:41) | Steps: WholePlaneLQGExistenceStep,
  ConeWholePlaneWeylComparisonStep, WholePlaneLQGCoordinateChangeStep, WholePlaneUpperVolumeTailStep (c4; IR-c4-1..4)
6.7 ConstantOrderLowerBoundStmt: constantOrderLowerBound (Proofs/Sec6/ConstantOrderLowerBound/Statement.lean:17) |
  Draft: 6.8 (Draft, F3), 2.7, 2.8, 2.19 | Steps: -
6.7 (b) ConstantOrderLowerBoundLogStmt: constantOrderLowerBoundLog (Proofs/Sec6/ConstantOrderLowerBound/LogLoss.lean:60)
  | Draft: 6.8 (b), 2.7, 2.8, 2.19 | Steps: -
6.8 (b) ConstantOrderLowerBoundDivLogStmt: constantOrderLowerBoundDiv_of_inputs (Proofs/Sec6/ConstantOrderLowerBoundDiv/
  Final.lean:26; c4, 29311ac) | Draft: 2.16, 2.7, 2.8, 2.9, 2.18, 6.4 | Steps: LQGMeasureFieldMeasurableStep (c2;
  Proofs/Measurability/GoodScale.lean:316). The Draft 6.8 has no reduction.
6.9 local rate (E-c5-1) ChanceOfBeingAbsorbedLocalRateStmt: chanceOfBeingAbsorbedLocalRate (Proofs/Sec6/ChanceOfBeing
  Absorbed/Chernoff.lean:387) | Draft: 6.7 | Steps: -. The Draft 6.9 implies it but has no reduction.
6.9 (b) ChanceOfBeingAbsorbedLogLossStmt: chanceOfBeingAbsorbedLogLoss_of_steps (Proofs/Sec6/ChanceOfBeingAbsorbed/
  LogLoss.lean:22) | Draft: 6.7 (b) | Steps: -
6.10 IterativeBoundStmt: iterativeBound_of_div (Proofs/Sec6/IterativeBound/Statement.lean:48) through 6.7 (b), 6.9 (b)
  | Draft: 6.8 (b), 2.7, 2.8, 2.19 | Steps: -. With 6.8 (b) expanded: 2.16, 2.7, 2.8, 2.9, 2.18, 2.19, 6.4 +
  LQGMeasureFieldMeasurableStep (c2). (iterativeBound_of_inputs, :56, still takes the false GoodScaleEventMeasurableStep.)
7.1 DivSandpileUpperBoundStmt (example disabled, F6): divSandpileUpperBound_of_carved_inputs (Steps/Sec7/DivSandpile
  UpperBound.lean:164) | Draft: 2.3, 6.8 (Draft, F3), 2.7, 7.2 (Draft, REFUTED E-c3-2, F1), 4.1, 3.3, 2.8, 7.3, 7.4 |
  Steps: StoppedObstacleSetupStep, StoppedShellConfinementStep (x2)
7.2 corrected (E-c3-2) MassBoundOdometerAboveScaleStmt: CorrectedForms.massBoundOdometerAboveScale_of_corrected
  (Audit/CorrectedForms.lean:257) | Draft: 2.16, 2.8, 4.4 corrected | Steps: -. The Draft 7.2 is false (E-c3-2).
7.3 OdometerBoundMassStmt: CorrectedForms.odometerBoundMass_of_corrected (:265) | Draft: 4.4 corrected | Steps: -
7.4 CrudeUpperBoundStmt: CorrectedForms.crudeUpperBound_of_corrected (:271) | Draft: 4.4 corrected | External:
  DegreeBoundInput | Steps: -

## No committed reduction
Paper-owned: 3.4 (m2; partial 20a59de and later). Draft forms with only a corrected form reduced: 3.1 (E-c1-4), 4.4,
4.5 (E-c1-1, false), 6.8 (E-A10), 6.9 (E-c5-1), 7.2 (E-c3-2). Cited (hypotheses only): 2.7, 2.8, 2.9, 2.10, 2.11, 2.14,
2.15, 2.16, 2.18, 3.2 ((L2) ruling pending).

## Findings (consumers of false or open Draft forms; build issues)
F1. 7.1 consumes the Draft 7.2, refuted by E-c3-2: vacuous until rerouted through `MassBoundOdometerAboveScaleStmt`
  (x2; `CorrectedForms.massBoundOdometerAboveScale_of_massBoundOdometer` gives Draft => corrected only).
F2. The Draft 4.4 is false (E-c1-1; `CorrectedForms.not_discreteLaplacianBoundStmt`). Remaining consumers: 4.6, 4.8 (x3)
  -> reroute to `DiscreteLaplacianBoundCorrectedStmt`. 7.2-7.4 are rerouted (CorrectedForms `_of_corrected`).
F3. E-A10 (b): 6.8 is proved only in the log form; the chain 6.8 (b) -> 6.7 (b) -> 6.9 (b) -> 6.10 is closed. Still on
  the Draft 6.8: the Draft-form 6.7, the 6.9 local rate and 7.1 (x2).
F5. Working tree: Proofs/Sec4/ObstacleSpecialization.lean (4.3-4.5) is modified and uncommitted; this audit was
  checked against the working tree (2026-11-05 00:40Z).
F6. OPEN: `MatedCRT.Sec7.vertexPoint_mem_cell` in Proofs/Sec7/DivSandpileUpperBound/CrudeCells.lean:11 (x2) and
  Proofs/Sec7/MassBoundOdometer/Count.lean:28 (c3): 7.1 cannot be imported with 7.2-7.4 (Theorem 1.6 needs both).
F7. The Draft 3.1 (false for non-open D, E-c1-4) is consumed by 3.3 (m1), 3.7 (x1), 4.6 (x3); 3.5 uses the corrected
  form. Reroute (the corrected N3 clause: scales in a deterministic polynomially summable sequence; thin first).
F10. NEW: `MatedCRT.rescaledMeasure` is declared in Steps/Sec1/Convergence.lean (1.4, 1.6) and in the module chain of
  Steps/Sec2/ConeScaleInvarianceUpToFixedTime.lean (c5): Theorems 1.4/1.6 and Lemmas 2.5/2.6 cannot be imported
  together (and 2.3 needs 2.5). One owner (m1 or c5) renames.
F11. NEW: Fact 2.2 is reduced to "parts" `LQGMeasureNonAtomicPart`, `LQGMeasureDilationCovariancePart` (cited facts,
  DS11) defined in Steps/Sec2/LQGMeasureProperties.lean:32, 86 (modified in the tree), not in MatedCRT/External: a
  literature input must be an External Prop admitted by the operator (owner of the split: de71d03, 102275a).
F12. NEW: `MatedCRT.harmonicAt_comp_add_const` is declared in Proofs/Sec3/ConvergenceNormalizedExitTime/
  HarmonicTranslation.lean:12 (x1) and Proofs/Sec3/UniformConvergenceGreenKernel/HarmonicTranslation.lean:18 (m1): 3.3's
  proved boundary step and 3.7 cannot be imported together (3.7 needs 3.3). x1 or m1 renames (DUPLICATES.md).
F13. RESOLVED for 6.8 (b) (c4, 29311ac): `GoodScaleEventMeasurableStep` is false as drafted (E-c2-4); 6.8 (b) now
  takes `LQGMeasureFieldMeasurableStep` instead. Still taking the false step: `iterativeBound_of_inputs`
  (Proofs/Sec6/IterativeBound/Statement.lean:56, c5), `constantOrderLowerBoundDiv_of_steps` and Assembly/Main.lean:209.
F14. NEW: Lemmas 2.4/2.5 (FROZEN) assert `T' = T`, which needs `ConeHarmonicBallStrictGrowthStep` (not in the paper):
  ESCALATIONS E-c5-3 (filed by A from reports/c5.md).
F9. Untracked work not in this ledger: Steps/Sec2/{CellSizeHalf, VolumeGrowthHalf} and Proofs/Sec2/{CellSizeHalf,
  VolumeGrowthHalf}/ (cited halves from Leo), Proofs/Sec4/{SubsequentialConvergence, SubsequentialProperties}/ (x3),
  Proofs/Sec2/ConeHarmonicBallsUpToFixedTime/, Proofs/Sec4/ConvergenceDivisible/ExternalConeScalePositivity, Assembly/.

## Counts (2026-11-05 00:40Z)
56 numbered results. Proved: 7 (2.13, 6.3, 6.6, A.1-A.4). Reduced (committed reduction; checked by an example except
2.5, 2.6 (F10), 2.3's best form (F10) and 7.1 (F6)): 38 (1.4, 1.6, 2.2 (cited), 2.3-2.6, 2.17, 2.19, 3.1 corrected,
3.3, 3.5-3.7, 4.1-4.3, 4.4 corrected, 4.5 corrected, 4.6-4.8, 5.1-5.4, 6.1, 6.4, 6.5, 6.7, 6.8 (b), 6.9, 6.10, 7.1,
7.2 corrected, 7.3, 7.4, 8.1). Of these, with no open step (Draft Stmts and External inputs only): 12 (2.17, 2.19,
4.7, 5.2, 5.4, 6.7, 6.9, 6.10, 7.2 corrected, 7.3, 7.4, 8.1); 5.2 and 5.4 rest on cited results only; 3.1 corrected
needs only the (L2)-pending corrected Lemma 3.2. Cited, hypotheses only: 10. No committed reduction: 1 (3.4).
Remaining inputs: External MepsScalingInput (3.1c, 4.7), DegreeBoundInput (7.4), QuantumConeScalingInput (2.3, 2.5,
2.6); HB cited GreenPotentialHolderStmt (3.5); cited parts outside External (2.2, F11); corrected cited 3.2 (L2).
Distinct open step Props (best reductions): 42 (c1 1, m1 8, m2 2, x1 3, x3 6, c2 3, c4 6, c5 10, x2 2, 2.2 split 1;
A 0: ConeFamilyAEMeasurableStep derived by c5).
