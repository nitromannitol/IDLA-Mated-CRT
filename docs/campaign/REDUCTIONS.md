# REDUCTIONS: the current reduction of each numbered result

Checked by `MatedCRT/Audit/Reductions.lean`. Its section `FinalForms` holds one `example` per result. Each example
restates the best committed reduction with exactly the hypotheses listed below. A drift of a Draft statement, of a
reducing theorem or of a step breaks the build. The examples above that section check earlier reductions which still
compile. Paths are relative to `MatedCRT/`. Line numbers point at the `theorem` line. They were read from the
environment on 2026-11-05 at 06:40Z, at HEAD 00649b2, by untracked probes (`Audit/LedgerProbeC1{a..d}`). Proved steps
are discharged and not listed.

Format: result Stmt: reducing theorem (file:line) | Draft: other numbered results used | External: literature
inputs | Steps: open step Props (owner). "cited" means a cited result of the paper. It is used only as a hypothesis
(a Draft Stmt) and never proved here. Owners are taken from tasks/*.md on 2026-11-05 10:30Z.

Re-sync c1 (2026-11-05), following worker A's ledger of 00:40Z. New since 71e9b96:
- 4.3, corrected 4.4 and corrected 4.5 are now unconditional (E-c1-2 resolved).
- 7.3 is proved, since corrected 4.4 is proved.
- 4.8 has no open step (7582c60).
- 7.1 no longer consumes the false Draft 7.2 (d17f14c).
- 3.7 no longer consumes the Draft 3.1 (980cf27).
- 4.6 consumes neither the Draft 3.1 nor the Draft 4.4.
- 4.1 and 4.2 have final forms (fb05dfd, ec0044b), and so does 5.1 (7fdfd3c).
- 2.3-2.6 and 6.1 have final forms (bddd0ce, Proofs/Sec2/Final.lean).
- The final forms of 6.4-6.10 are in 767b18a and Proofs/Sec6/ConstantOrderLowerBoundDiv/Final.lean.
- `ConeEnvironmentScalingStep` is reduced to inputs (0d13527).
- `LQGMeasureFieldMeasurableStep` and `GoodScaleEventMeasurableAEStep` are proved (e27e1bb, 00649b2).

## Proved (no hypotheses)
2.13 MaximumPrincipleStmt: maximumPrinciple_of_steps (Steps/Sec2/MaximumPrinciple.lean:22) + adjacentCellsMeetAeStep
4.3 DiscreteBasicPropertiesStmt: discreteBasicProperties (Proofs/Sec4/ObstacleSpecialization/Final.lean:28)
4.4 corrected (E-c1-1) DiscreteLaplacianBoundCorrectedStmt: discreteLaplacianBoundCorrected (:33). Draft 4.4 FALSE (Lean)
4.5 corrected (E-c1-1) DiscreteConservationOfMassCorrectedStmt: discreteConservationOfMassCorrected (:38). Draft FALSE (Lean)
6.3 AbelianIDLAStmt: AbelianIDLA.abelianIDLA (Proofs/Sec6/AbelianIDLA/Statement.lean:119)
6.6 AnnulusIterateStmt (cited, proved): annulusIterate (Proofs/Field/LawTransferComplete.lean:71; x4, Leo's lmLem3_1a)
7.3 OdometerBoundMassStmt: CorrectedForms.odometerBoundMass_of_corrected (Audit/CorrectedForms.lean:265) +
  discreteLaplacianBoundCorrected
A.1 DiscreteDivergenceTheoremStmt: discreteDivergenceTheorem (Proofs/SecA/DiscreteDivergence.lean:54)
A.2-A.4: discreteBasicPropertiesGeneral, discreteLaplacianBoundGeneral, discreteConservationOfMassGeneral
  (Proofs/SecA/Statements.lean:62, 66, 71)
Proved steps (discharged everywhere): AdjacentCellsMeetAeStep, LQGMeasureFieldMeasurableStep
(Proofs/Measurability/LQGMeasureField.lean:75), GoodScaleEventMeasurableAEStep (:110), OdometerObstacleApproximationStep
(Proofs/Sec4/SubsequentialProperties/ObstacleApproximation.lean:72), OdometerDistributionalLimitCorrectedStep (from 3.3,
Proofs/Sec4/SubsequentialProperties/Final.lean:31), ShellIterationStep (from MepsScalingInput, Proofs/Sec7/
DivSandpileUpperBound/ShellIterationOfMeshScaling.lean:13), DiscreteExitBoundaryStep (from 3.3, 3.5; Proofs/Sec3/
ConvergenceNormalizedExitTime/DiscreteBoundaryLayer.lean:133), BoundaryLayerMeasurableStep (Proofs/Sec2/Final.lean:94,
from Section 2 inputs), CircleAverageModConstStep (Proofs/Field/ConeCircleModConst.lean:367, f4f87aa).

## Reduced (final forms)
1.4 ConvergenceOfIDLAStmt: convergenceOfIDLA_of_bounds_coneSteps (Proofs/Sec1/Main.lean:70) with
  coneEnvironmentScalingStep_of_inputs (Proofs/Sec1/EnvironmentScaling.lean:184) | Draft: 4.2, 5.1, 6.1, 7.1, 2.2 |
  External: QuantumConeScalingInput, SLEScaleInvarianceInput, SLEReparametrizationInput, SLEIndepMonoInput; requested
  RescaledEnvironmentInput (IR-c1-1, F16) | Steps: ConeHarmonicBallStrictGrowthStep (E-c5-3),
  ConeHalfBallFamilyFunctionalStep (c5)
1.6 ConvergenceOfDivSandpileStmt: convergenceOfDivSandpile_of_bounds_coneSteps (:77) | as 1.4
8.1 IDLAConstrainedConvergenceStmt: iDLAConstrainedConvergence_of_steps (Steps/Sec8/IDLAConstrainedConvergence.lean:27)
  | Draft: 4.2, 5.1, 6.1, 7.1 | Steps: -
2.2 LQGMeasurePropertiesStmt (cited): LQGMeasure.lqgMeasureProperties_of_volumeGrowth (Proofs/Sec2/LQGMeasureProperties/
  NonAtomicScaling.lean:170) | Draft: 2.7 | cited part LQGMeasureNonDyadicDilationPart (DS11; not in External, F11) |
  External: QuantumConeScalingInput | Steps: ConeCircleAverageLocalityStep, LQGMeasure.ConeFieldScalingStep. Also
  lqgMeasureProperties_final (Proofs/Sec2/Final.lean:47) from the three parts NonAtomic, Locality, DilationCovariance
  (each derived: NonAtomicScaling.lean:160, Locality.lean:157, Main.lean:45)
2.3 ConeHarmonicBallsStmt: coneHarmonicBalls_final (Proofs/Sec2/Final.lean:83) | HB Drafts (HarmonicBallsDraftInputs:
  HB Thm 1.1, 5.5, Prop 5.6, Lemmas 3.1-3.5, Props 5.2, 5.3, Lemma 5.8) | Draft: 2.7, the three parts of 2.2 | External:
  QuantumConeScalingInput | Steps: WholePlaneLogLQGExistenceStep, ConeRestrictionStep, ConeHarmonicBallLocalityStep,
  ConeHarmonicBallStrictGrowthStep, ConeHalfBallFamilyFunctionalStep (c5)
2.4 ConeHarmonicBallsUpToFixedTimeStmt: coneHarmonicBallsUpToFixedTime_final (:60) | HB Drafts | Steps: the first four
  steps of 2.3 (c5)
2.5 ConeScaleInvarianceUpToFixedTimeStmt: coneScaleInvarianceUpToFixedTime_final (:67) | the three parts of 2.2 |
  External: QuantumConeScalingInput | Steps: ConeHarmonicBallStrictGrowthStep, ConeHalfBallFamilyFunctionalStep (c5)
2.6 ConeScaleInvarianceStmt: coneScaleInvariance_final (:75) | the three parts of 2.2 | External:
  QuantumConeScalingInput | Steps: ConeHarmonicBallFunctionalStep (c5; E-c3-3)
ConeFamilyAEMeasurableStep (step of 4.1, 4.2, 5.1; derived): coneFamilyAEMeasurable_final (:53) | Draft: 2.7, the parts
  of 2.2 | External: QuantumConeScalingInput | Steps: ConeHarmonicBallStrictGrowthStep
2.7 lower half VolumeGrowthLowerStmt, 2.8 upper half CellSizeUpperStmt (Leo): volumeGrowthLowerStmt_of_coupling,
  cellSizeUpperStmt_of_coupling (Proofs/Sec2/{VolumeGrowthHalf,CellSizeHalf}/Main.lean:56) | Steps:
  ConeWholePlaneCouplingStep
2.17 BoundedExitTimeRVStmt: boundedExitTimeRV_of_steps (Steps/Sec2/BoundedExitTimeRV.lean:26) | Draft: 2.7 (cited)
2.19 ExpectedExitTimeExplicitBoundStmt: expectedExitTimeExplicitBound_of_steps (Steps/Sec2/ExpectedExitTimeExplicit
  Bound.lean:44) after 2.17 | Draft: 2.7, 2.18 (both cited) | Steps: -
3.1 corrected (E-c1-4) DiscretePotentialTightnessCorrectedStmt: discretePotentialTightnessCorrected_of_inputs (Proofs/
  Sec3/DiscretePotentialTightness/Final.lean:25) | Draft: 2.7, 2.18 | External: MepsScalingInput | corrected cited 3.2
  DiscreteHolderContinuityCorrectedStep ((L2) ruling pending; E-chk-1; m1 from Leo) | Steps: -. The Draft 3.1 is
  FALSE (Lean, Audit/Refutations.lean:320)
3.3 UniformConvergenceGreenKernelStmt: uniformConvergenceGreenKernel_of_steps (Steps/Sec3/UniformConvergenceGreenKernel
  .lean:50; example DISABLED, F15) | Draft: 2.10, 3.4, 2.14, 2.8, 3.1 (Draft, false, F7), 2.13 | Steps:
  GreenKernelInteriorStep (c1.next), GreenKernelBoundaryStep (proved in Proofs/Sec3/UniformConvergenceGreenKernel/
  BoundaryStep.lean:16, F12)
3.5 DiscreteDirichletProblemStmt: discreteDirichletProblem_of_steps (Steps/Sec3/DiscreteDirichletProblem.lean:98) |
  Draft: 3.6, 3.4, 3.1 corrected, 2.13, 2.19, 2.8; HB cited: HarmonicBalls.GreenPotentialHolderStmt | Steps:
  DirichletLimitStep, DirichletInteriorStep, DirichletBoundaryStep (c1.next)
3.6 ConvergenceHarmonicFunctionsStmt: convergenceHarmonicFunctions_of_steps (Steps/Sec3/ConvergenceHarmonicFunctions
  .lean:53) | Draft: 2.11, 2.8 (cited) | Steps: HarmonicPathExitStep, HarmonicExitCellStep (m2/c2)
3.7 ConvergenceNormalizedExitTimeStmt: convergenceNormalizedExitTime_of_statements (Proofs/Sec3/ConvergenceNormalized
  ExitTime/DyadicModulus.lean:159; 980cf27) | Draft: 3.3, 3.5, 2.17, 2.18 | Steps: DiscretePotentialTightnessAeStep
  (E-c2-6; a.s. interior form of corrected 3.1, unowned)
4.1 ConvergenceDivisibleStmt: convergenceDivisible_final_of_coneFamily (Proofs/Sec4/ConvergenceDivisible/Final.lean:36)
  | Draft: 2.7, 2.18, 3.3, 3.5, 3.7, 2.4; corrected cited 3.2 | External: MepsScalingInput | Steps:
  ConeFamilyAEMeasurableStep (derived, above), OdometerLocalCompactnessCorrectedStep, OdometerBoundaryUpgradeCorrected
  Step, OdometerMeasurableSelectionStep (m4; E-x3-2)
4.2 DivSandpileLowerBoundStmt: divSandpileLowerBound_final (Proofs/Sec4/DivSandpileLowerBound/Final.lean:79) | Draft:
  4.1, 2.3, 2.4, 2.7, 2.8, 3.3 | Steps: ConeFamilyAEMeasurableStep, HarmonicBallStrictObstacleGapStep (m4; E-x3-1,
  E-c2-5)
4.6 SubsequentialConvergenceStmt: subsequentialConvergence_of_inputs (Proofs/Sec4/SubsequentialConvergence/Corrected
  .lean:87) | Draft: 2.7, 2.18, 3.5; corrected cited 3.2 | External: MepsScalingInput | Steps: the three odometer steps
  of 4.1 (m4)
4.7 EquiboundedStmt: equibounded_of_inputs (Proofs/Sec4/ObstacleSpecialization/Final.lean:48) | Draft: 2.7, 2.18 |
  External: MepsScalingInput | Steps: -
4.8 SubsequentialPropertiesStmt: subsequentialProperties_of_inputs (Proofs/Sec4/SubsequentialProperties/Final.lean:83) |
  Draft: 3.3, 3.5, 3.7 | Steps: -
5.1 IDLALowerBoundStmt: iDLALowerBound_final_of_strictGap (Proofs/Sec5/IDLALowerBound/Final.lean:48) | Draft: 2.7, 2.8,
  2.9, 2.15, 2.16, 2.18 (cited), 4.1, 2.3, 2.4, 3.3, 2.17 | Steps: ConeFamilyAEMeasurableStep, MeanValueSurplusLowerStep
  (E-c2-5), HarmonicBallStrictObstacleGapStep (E-x3-1), StoppedMeanValueInequalityStep, StoppedLLowerBoundStep (E-c1-5;
  operator ruling)
5.2 GeneralIDLALowerBoundStmt: generalIDLALowerBound_of_volumeGrowth_cellSize (Proofs/Measurability/EnvSigma.lean:217)
  | Draft: 2.7, 2.8 (cited) | Steps: -
5.3 MeanValueInequalityStmt: meanValueInequality_of_lower (Proofs/Sec5/MeanValueInequality/SurplusSteps.lean:237) |
  Draft: 4.1, 3.3, 2.17, 2.18 | Steps: MeanValueSurplusLowerStep (E-c2-5)
5.4 LLowerBoundStmt: lLowerBound_of_inputs (Proofs/Sec5/LLowerBound/OfInputs.lean:14) | Draft: 2.15, 2.16, 2.9 (all
  cited) | Steps: -
6.1 IDLAUpperBoundStmt: iDLAUpperBound_final (Proofs/Sec2/Final.lean:104) | Draft: 6.10, 5.1, 2.7, the parts of 2.2; HB
  Drafts | External: QuantumConeScalingInput | Steps: the four steps of 2.4 (c5)
6.4 GoodAnnulusPrevalenceStmt: goodAnnulusPrevalence_final (Proofs/Sec6/GoodAnnulusPrevalence/Main.lean:56) | Steps:
  WholePlaneLQGExistenceStep, ConeWholePlaneWeylComparisonStep, WholePlaneLQGCoordinateChangeStep,
  WholePlaneUpperVolumeTailStep, ConeMeanZeroRestrictionStep (c4). CircleAverageModConstStep PROVED (f4f87aa)
6.5 AnnulusHitStmt: annulusHit_final (:45) | Steps: the first four steps of 6.4 (c4)
6.7 ConstantOrderLowerBoundStmt: constantOrderLowerBound (Proofs/Sec6/ConstantOrderLowerBound/Statement.lean:17) |
  Draft: 6.8 (Draft, F3), 2.7, 2.8, 2.19 | Steps: -
6.7 (b) ConstantOrderLowerBoundLogStmt: constantOrderLowerBoundLog_final (Proofs/Sec6/ConstantOrderLowerBoundDiv/
  Final.lean:77) | Draft: 2.16, 2.7, 2.8, 2.9, 2.18 (cited) | Steps: the five open steps of 6.4 (c4)
6.8 (b) ConstantOrderLowerBoundDivLogStmt: constantOrderLowerBoundDivLog_final (:65) | as 6.7 (b). The Draft 6.8 has no
  reduction (E-A10)
6.9 local rate (E-c5-1) ChanceOfBeingAbsorbedLocalRateStmt: chanceOfBeingAbsorbedLocalRate (Proofs/Sec6/ChanceOf
  BeingAbsorbed/Chernoff.lean:386) | Draft: 6.7 | Steps: -. The Draft 6.9 implies it but has no reduction
6.9 (b) ChanceOfBeingAbsorbedLogLossStmt: chanceOfBeingAbsorbedLogLoss_final (:91) | as 6.7 (b)
6.10 IterativeBoundStmt: iterativeBound_final (:104) | as 6.7 (b). Relative to 6.8 (b): iterativeBound_of_div
  (Proofs/Sec6/IterativeBound/Statement.lean:46) | Draft: 6.8 (b), 2.7, 2.8, 2.19 | Steps: -
7.1 DivSandpileUpperBoundStmt: divSandpileUpperBound_of_meshScaling (Proofs/Sec7/DivSandpileUpperBound/ShellIteration
  OfMeshScaling.lean:43; d17f14c) | Draft: 2.3, 6.8 (b), 2.7, 7.2 corrected, 4.1, 3.3, 2.8, 7.3, 7.4 | External:
  MepsScalingInput | Steps: -
7.2 corrected (E-c3-2) MassBoundOdometerAboveScaleStmt: CorrectedForms.massBoundOdometerAboveScale_of_corrected
  (Audit/CorrectedForms.lean:257) + discreteLaplacianBoundCorrected | Draft: 2.16, 2.8 | Steps: -. Draft 7.2 FALSE
  (argument)
7.4 CrudeUpperBoundStmt: CorrectedForms.crudeUpperBound_of_corrected (:271) + discreteLaplacianBoundCorrected |
  External: DegreeBoundInput | Steps: -

## No committed reduction
Paper-owned: 3.4 (m2; partial). Draft forms with only a corrected form reduced: 3.1 (FALSE, Lean), 4.4 and 4.5
(FALSE, Lean), 6.8 (E-A10), 6.9 (E-c5-1), 7.2 (FALSE, argument). Cited, used as hypotheses only: 2.7, 2.8, 2.9, 2.10,
2.11, 2.14, 2.15, 2.16, 2.18, 3.2 (corrected form pending the (L2) ruling).

## Findings (consumers of false or open Draft forms; build issues)
F1. RESOLVED (d17f14c): 7.1 consumes the corrected 7.2 and 6.8 (b).
F2. RESOLVED: no final form consumes the Draft 4.4; corrected 4.4 is proved.
F3. E-A10 (b): 6.8 is proved only in the log form. On the Draft 6.8 there remain only the Draft-form 6.7 and the 6.9
  local rate. No final form of 1.4/1.6 needs them: 6.10 uses 6.8 (b).
F5. Working tree: Proofs/Sec4/ObstacleSpecialization.lean is modified and uncommitted (owner: c1's earlier task).
  The final forms of 4.3-4.5 live in the committed ObstacleSpecialization/Final.lean.
F6. RESOLVED for the final form: 7.1 (ShellIterationOfMeshScaling) and 7.2-7.4 (CorrectedForms) import together.
F7. The Draft 3.1 (FALSE, Lean) is still consumed by 3.3 (`uniformConvergenceGreenKernel_of_steps`; owner c1.next).
  3.7, 4.6 and 4.1 are rerouted (corrected 3.1 or its a.s. form). 3.5 uses the corrected form.
F11. Fact 2.2 rests on `LQGMeasureNonDyadicDilationPart` (cited, DS11), defined in Steps/Sec2/LQGMeasureProperties
  .lean:97 and not in MatedCRT/External. A literature input must be an External Prop admitted by the operator.
F12. `MatedCRT.harmonicAt_comp_add_const` is declared twice (3.3's BoundaryStep chain and 3.7's chain;
  DUPLICATES.md).
F13. RESOLVED: `LQGMeasureFieldMeasurableStep` is proved (e27e1bb). The false `GoodScaleEventMeasurableStep` is used
  only by non-final theorems (`iterativeBound_of_inputs`, Statement.lean:53).
F14. Lemmas 2.4/2.5 (FROZEN) assert `T' = T`, which needs `ConeHarmonicBallStrictGrowthStep` (E-c5-3). Every route to
  2.3-2.5, 4.1, 4.2, 5.1, 6.1 and 1.4 carries it.
F15. NEW: `MatedCRT.rescaledGreenKernel` is declared in Steps/Sec3/UniformConvergenceGreenKernel.lean:16 (Lemma 3.3,
  c1.next) and in Proofs/Sec4/SubsequentialProperties/ClusterContainment.lean:26 (4.8 chain, imported by
  Proofs/Sec4/ConvergenceDivisible/Final.lean). The reduction of 3.3 therefore cannot be imported with the final forms
  of 4.1, 4.2, 4.8 and 5.1, nor with those of 1.4/1.6. Its example is disabled. One owner must rename
  (DUPLICATES.md).
F16. NEW: `RescaledEnvironmentInput` (Proofs/Sec1/EnvironmentScaling.lean:75, requested IR-c1-1) is a literature-type
  input that is not in MatedCRT/External. It needs an operator ruling and A's move to External.

## Counts (2026-11-05 10:30Z)
56 numbered results.
- Proved: 11 (2.13, 4.3, corrected 4.4, corrected 4.5, 6.3, 6.6, 7.3, A.1-A.4).
- Reduced with a committed final form: 37 (1.4, 1.6, 2.2, 2.3-2.6, 2.17, 2.19, corrected 3.1, 3.3, 3.5-3.7, 4.1, 4.2,
  4.6-4.8, 5.1-5.4, 6.1, 6.4, 6.5, 6.7, 6.7 (b), 6.8 (b), 6.9 (rate and b), 6.10, 7.1, corrected 7.2, 7.4, 8.1). Each
  is checked by an example, except 3.3 (F15).
- Of these, with no open step: 14 (2.17, 2.19, corrected 3.1, 4.7, 4.8, 5.2, 5.4, 6.7, 6.9 rate, 6.10 relative to
  6.8 (b), 7.1, corrected 7.2, 7.4, 8.1). They need only Draft Stmts and External inputs.
- Cited, used as hypotheses only: 10. No committed reduction: 1 (3.4).
Remaining literature inputs:
- External: MepsScalingInput (3.1c, 4.1, 4.6, 4.7, 7.1), DegreeBoundInput (7.4), QuantumConeScalingInput (2.2, 2.3,
  2.5, 2.6, 6.1, 1.4), and the SLE inputs (1.4).
- Requested, not in External: RescaledEnvironmentInput (F16) and the cited part NonDyadicDilation (F11).
- HB cited: GreenPotentialHolderStmt (3.5) and HarmonicBallsDraftInputs (2.3, 2.4, 6.1).
- Corrected cited 3.2, pending (L2).
Open steps on the route to Theorems 1.4/1.6:
- Section 2 (c5): ConeHarmonicBallStrictGrowthStep, ConeHalfBallFamilyFunctionalStep, WholePlaneLogLQGExistenceStep,
  ConeRestrictionStep, ConeHarmonicBallLocalityStep, ConeCircleAverageLocalityStep, ConeFieldScalingStep.
- Section 3 (c1.next, m2/c2, unowned): GreenKernelInteriorStep, the three Dirichlet steps, HarmonicPathExitStep,
  HarmonicExitCellStep, DiscretePotentialTightnessAeStep.
- Section 4 (m4): the three odometer steps and HarmonicBallStrictObstacleGapStep.
- Section 5: MeanValueSurplusLowerStep, StoppedMeanValueInequalityStep, StoppedLLowerBoundStep.
- Section 6 (c4): the five open field steps (CircleAverageModConstStep proved, f4f87aa).
- Section 2 (Leo's halves of 2.7/2.8): ConeWholePlaneCouplingStep.
