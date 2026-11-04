# REDUCTIONS: the current reduction of each numbered result

Checked by `MatedCRT/Audit/Reductions.lean`: one `example` per line below restates the reduction with exactly these
hypotheses, so a drift of a Draft statement, a reducing theorem or a step breaks the build. Paths are relative to
`MatedCRT/`; line numbers point at the declaration (docstring start), from the 2026-11-04 10:00Z tree. Proved steps are
discharged and not listed. Format: result Stmt: reducing theorem (file:line) | Draft: other numbered results used |
External: literature inputs (MatedCRT/External) | Steps: open step Props (file:line, owner).

Owners: from STATUS.md and tasks/*.md as of 2026-11-04 10:00Z. "cited" = a cited result of the paper, used only as a
hypothesis (Draft Stmt), never proved here.

## Proved (no hypotheses)
6.3 AbelianIDLAStmt: AbelianIDLA.abelianIDLA (Proofs/Sec6/AbelianIDLA/Statement.lean:118)
A.1 DiscreteDivergenceTheoremStmt: discreteDivergenceTheorem (Proofs/SecA/DiscreteDivergence.lean:53)
A.2 DiscreteBasicPropertiesGeneralStmt: discreteBasicPropertiesGeneral (Proofs/SecA/Statements.lean:61)
A.3 DiscreteLaplacianBoundGeneralStmt: discreteLaplacianBoundGeneral (Proofs/SecA/Statements.lean:65)
A.4 DiscreteConservationOfMassGeneralStmt: discreteConservationOfMassGeneral (Proofs/SecA/Statements.lean:70)

## Reduced
2.3 ConeHarmonicBallsStmt: coneHarmonicBalls_of_steps (Steps/Sec2/ConeHarmonicBalls.lean:63) | Draft: 2.4, 2.5 |
  External: - | Steps: ConeFamilyAEMeasurableStep (Steps/Sec2/ConeHarmonicBalls.lean:25, A)
2.13 MaximumPrincipleStmt: maximumPrinciple_of_steps (Steps/Sec2/MaximumPrinciple.lean:20) | Draft: - | External: - |
  Steps: AdjacentCellsMeetAeStep (Steps/Infra/MatingOfTrees.lean:21, A; IR-A2, Leo port pending)
2.17 BoundedExitTimeRVStmt: boundedExitTimeRV_of_steps (Steps/Sec2/BoundedExitTimeRV.lean:25) | Draft: 2.7 (cited) |
  External: - | Steps: -
2.19 ExpectedExitTimeExplicitBoundStmt: expectedExitTimeExplicitBound_of_steps (Steps/Sec2/ExpectedExitTimeExplicitBound
  .lean:42) after 2.17 | Draft: 2.7, 2.18 (both cited) | External: - | Steps: -
4.1 ConvergenceDivisibleStmt: convergenceDivisible_of_steps (Steps/Sec4/ConvergenceDivisible.lean:146), with
  obstacleLimitUniqueness_of_steps (:73), obstacleLimitRegularity_of_steps (:48) | Draft: 4.6, 4.8 | External: - |
  Steps: MatedCRTScalingConstantPositiveStep (:42), ObstacleLimitMaximumPrincipleStep (:57),
  ConvergenceDivisibleEventMeasurableStep (:136) (all x3)
4.2 DivSandpileLowerBoundStmt: divSandpileLowerBound_of_steps (Steps/Sec4/DivSandpileLowerBound.lean:46), with
  divSandpileOdometerComparison_of_cellsMeet (Proofs/Sec4/DivSandpileLowerBound/OdometerComparison.lean:98) |
  Draft: 4.1, 2.3, 2.13, 3.3, 2.8 (cited) | External: - | Steps: ObstacleClusterInnerApproximationStep
  (Steps/Sec4/DivSandpileLowerBound.lean:18, x3), AdjacentCellsMeetAeStep (A)
4.3 DiscreteBasicPropertiesStmt: discreteBasicProperties_of_inputs (Proofs/Sec4/ObstacleSpecialization.lean:99) |
  Draft: - | External: - | Steps: BallInteriorConnectedStep (Steps/Sec4/ObstacleSpecialization.lean:515, c1; E-c1-2),
  AdjacentCellsMeetAeStep (A)
4.4 corrected (E-c1-1) DiscreteLaplacianBoundCorrectedStmt (Steps/Sec4/ObstacleSpecialization.lean:527):
  discreteLaplacianBoundCorrected_of_inputs (Proofs/Sec4/ObstacleSpecialization.lean:109) | Draft: - | External: - |
  Steps: BallInteriorConnectedStep (c1), AdjacentCellsMeetAeStep (A). The Draft 4.4 (OPEN) has no reduction.
4.5 corrected (E-c1-1) DiscreteConservationOfMassCorrectedStmt (Steps/Sec4/ObstacleSpecialization.lean:540):
  discreteConservationOfMassCorrected_of_inputs (Proofs/Sec4/ObstacleSpecialization.lean:116) | as 4.4 corrected.
4.6 SubsequentialConvergenceStmt: subsequentialConvergence_of_steps (Steps/Sec4/SubsequentialConvergence.lean:60) |
  Draft: 4.7, 4.4 (Draft, OPEN E-c1-1), 3.1, 3.5 | External: - | Steps: OdometerLocalCompactnessStep (:18),
  OdometerBoundaryUpgradeStep (:30), OdometerMeasurableSelectionStep (:44) (all x3)
4.7 EquiboundedStmt: equibounded_of_steps (Proofs/Sec4/Equibounded.lean:224) | Draft: 4.3, 2.17, 2.18 (cited) |
  External: MepsScalingInput (External/SLE.lean:61) | Steps: -
4.8 SubsequentialPropertiesStmt: subsequentialProperties_of_steps (Steps/Sec4/SubsequentialProperties.lean:56) |
  Draft: 3.3, 3.5, 3.7, 4.6, 4.3, 4.4 (Draft, OPEN E-c1-1), 2.13 | External: - | Steps:
  OdometerObstacleApproximationStep (:17), OdometerDistributionalLimitStep (:34) (both x3)
5.1 IDLALowerBoundStmt: iDLALowerBound_of_inputs (Proofs/Sec5/IDLALowerBound/Statement.lean:24), with
  discreteClusterInnerBound_of_steps (Steps/Sec5/IDLALowerBound.lean:80) | Draft: 2.7, 2.8 (cited), 5.3, 5.4, 4.1, 2.3,
  2.13, 3.3 | External: - | Steps: EnvSigmaMeasurableStep (c2), ObstacleClusterInnerApproximationStep (x3),
  IDLALowerBoundStoppedStep (Steps/Sec5/IDLALowerBound.lean:68, c2; not given by the printed proof)
5.2 GeneralIDLALowerBoundStmt: generalIDLALowerBound_of_inputs (Proofs/Sec5/GeneralIDLALowerBound/Statement.lean:25) |
  Draft: 2.7, 2.8 (cited) | External: - | Steps: EnvSigmaMeasurableStep (Steps/Sec5/GeneralIDLALowerBound.lean:102,
  c2; E-c2-1)
5.3 MeanValueInequalityStmt: meanValueInequality_of_steps (Steps/Sec5/MeanValueInequality.lean:47) | Draft: 4.4
  corrected, 2.13, 4.1, 3.3, 2.18 (cited) | External: - | Steps: MeanValueNormalizedStep (:26, x1)
5.4 LLowerBoundStmt: lLowerBound_of_local (Proofs/Sec5/LLowerBound/GreenSum.lean:162) | Draft: 2.15, 2.16, 2.9 (all
  cited) | External: - | Steps: LLowerBoundLocalStep (Proofs/Sec5/LLowerBound/GreenSum.lean:119, x1)
6.4 GoodAnnulusPrevalenceStmt: goodAnnulusPrevalence_of_steps (Steps/Sec6/GoodAnnulusPrevalence.lean:62) | Draft: 6.6,
  6.5 | External: - | Steps: AnnulusIterateConeTransferStep (:47), GoodAnnulusEventLocalityStep (:52) (c4; IR-c4-5/6)
6.5 AnnulusHitStmt: annulusHit_of_steps (Steps/Sec6/AnnulusHit.lean:86) | Draft: - | External: - | Steps:
  WholePlaneLQGExistenceStep (:36), ConeWholePlaneWeylComparisonStep (:43), WholePlaneLQGCoordinateChangeStep (:60),
  WholePlaneGoodAnnulusTightnessStep (:75) (all c4; IR-c4-1..4)
6.6 AnnulusIterateStmt (cited): annulusIterate_of_leo (Steps/Sec6/AnnulusIterate.lean:38; Leo's lmLem3_1a) | Draft: - |
  External: - | Steps: AnnulusGFFLawTransferStep (:18, x1; IR-x1-1)
6.7 ConstantOrderLowerBoundStmt: constantOrderLowerBound (Proofs/Sec6/ConstantOrderLowerBound/Statement.lean:14) |
  Draft: 6.8 (Draft form, see F3), 2.7, 2.8, 2.19 | External: - | Steps: AdjacentCellsMeetAeStep (A)
6.8 E-A10 (b) form ConstantOrderLowerBoundDivLogStmt (Steps/Sec6/ConstantOrderLowerBoundDiv.lean:28):
  constantOrderLowerBoundDiv_of_steps (Proofs/Sec6/ConstantOrderLowerBoundDiv/OfSteps.lean:196) | Draft: 2.16, 2.7,
  2.8, 2.9, 6.4, 2.18, 2.19 | External: - | Steps: GoodScaleEventMeasurableStep (Steps/Sec6/ConstantOrderLowerBoundDiv
  .lean:63, c4), AdjacentCellsMeetAeStep (A). The Draft 6.8 has no reduction.
6.9 local-rate form (E-c5-1) ChanceOfBeingAbsorbedLocalRateStmt (Steps/Sec6/ChanceOfBeingAbsorbed.lean:32):
  chanceOfBeingAbsorbedLocalRate (Proofs/Sec6/ChanceOfBeingAbsorbed/Chernoff.lean:386) | Draft: 6.7 | External: - |
  Steps: -. The Draft 6.9 implies it (ChanceOfBeingAbsorbedStmt.localRate) but has no reduction.
6.7 E-A10 (b) form ConstantOrderLowerBoundLogStmt: constantOrderLowerBoundLog (Proofs/Sec6/ConstantOrderLowerBound/
  LogLoss.lean; c5, 746a5f1) | Draft: 6.8 (b), 2.7, 2.8, 2.19 | External: - | Steps: AdjacentCellsMeetAeStep (A)
6.9 E-A10 (b) form ChanceOfBeingAbsorbedLogLossStmt (Steps/Sec6/IterativeBound.lean:71):
  chanceOfBeingAbsorbedLogLoss_of_steps (Proofs/Sec6/ChanceOfBeingAbsorbed/LogLoss.lean:20) | Draft: 6.7 (b) |
  External: - | Steps: -
6.10 IterativeBoundStmt: iterativeBound_of_div (Proofs/Sec6/IterativeBound/Statement.lean:46), through 6.7 (b), 6.9 (b)
  and AdjacentCellsMeetAeStep.probTendsToOne (:37) | Draft: 6.8 (b), 2.7, 2.8, 2.19 | External: - |
  Steps: AdjacentCellsMeetAeStep (A). With 6.8 (b) expanded (iterativeBound_of_inputs, :53): 2.16, 2.7, 2.8, 2.9, 6.4,
  2.18, 2.19, GoodScaleEventMeasurableStep (c4), AdjacentCellsMeetAeStep (A)
7.1 DivSandpileUpperBoundStmt (example disabled, F6): divSandpileUpperBound_of_carved_steps (Steps/Sec7/DivSandpileUpperBound.lean:135) |
  Draft: 2.3, 6.8 (Draft), 2.7, 7.2 (Draft, REFUTED E-c3-2, see F1), 4.1, 3.3, 2.8, 7.3, 7.4 | External: - | Steps:
  StoppedObstacleSetupStep (:43), StoppedShellConfinementStep (:52) (both x2), AdjacentCellsMeetAeStep (A)
7.2 corrected (E-c3-2) MassBoundOdometerAboveScaleStmt (Steps/Sec7/MassBoundOdometer.lean:47):
  massBoundOdometerAboveScale_of_draft (:155) | Draft: 2.16, 2.8, 4.4 (Draft, OPEN E-c1-1) | External: - | Steps:
  AdjacentCellsMeetAeStep (A). The Draft 7.2 is false (E-c3-2).
7.3 OdometerBoundMassStmt: odometerBoundMass_of_draft (Steps/Sec7/OdometerBoundMass.lean:174) | Draft: 4.4 (Draft,
  OPEN E-c1-1) | External: - | Steps: AdjacentCellsMeetAeStep (A)
7.4 CrudeUpperBoundStmt: crudeUpperBound_of_draft (Steps/Sec7/CrudeUpperBound.lean:81) | Draft: 4.4 (Draft, OPEN
  E-c1-1) | External: DegreeBoundInput (External/SLE.lean:68) | Steps: AdjacentCellsMeetAeStep (A)

## No committed reduction
Paper-owned: 1.4, 1.6 (m1), 2.4, 2.5, 2.6 (A.next), 3.1, 3.3, 3.4, 3.5, 3.6, 3.7 (m1, m2; Steps/Sec3 untracked),
5.1 (c2.next), 6.1 (c2.next), 8.1 (m1); Draft forms 4.4, 4.5 (E-c1-1), 6.8 (E-A10), 6.9 (E-c5-1), 7.2 (E-c3-2).
Cited (hypotheses only): 2.2, 2.7, 2.8, 2.9, 2.10, 2.11, 2.14, 2.15, 2.16, 2.18, 3.2 ((L2) open).

## Findings (consumers of false or open Draft forms)
F1. 7.1 consumes the Draft 7.2 `MassBoundOdometerStmt`, refuted by E-c3-2: the 7.1 reduction is vacuous until it is
  rerouted through `MassBoundOdometerAboveScaleStmt` (x2; c3's corrected form needs `s ≥ ε^β`, enough for tex 3168-3192).
F2. The Draft 4.4 `DiscreteLaplacianBoundStmt` (OPEN, E-c1-1: false for large ε) is consumed by 4.6, 4.8, 7.2
  corrected, 7.3, 7.4 (through stoppedOdometerLaplacianStep_of_draft). Reroute to `DiscreteLaplacianBoundCorrectedStmt`
  (owners x3 for 4.6, 4.8; c3 for 7.2-7.4; c3: only the first conjunct is used), or the operator replaces the Draft 4.4.
F3. E-A10 (b): 6.8 is proved only in the log form. The chain 6.8 (b) -> 6.7 (b) -> 6.9 (b) -> 6.10 is CLOSED (c5,
  746a5f1). Still on the Draft 6.8 (no log loss): the Draft-form 6.7 (`constantOrderLowerBound`), 6.9 local rate
  (`chanceOfBeingAbsorbedLocalRate_of_div`) and 7.1 (x2: needs a log-loss form of its 6.8 use).
F4. IR-A2 has two Props: `AdjacentCellsMeetAeStep` (a.s., all ε; A) and `AdjacentCellsMeetStep` (probability -> 1,
  vertices of V^ε(B_ρ); c5). The first implies the second (`AdjacentCellsMeetAeStep.probTendsToOne`, c5), so every
  reduction above rests on the a.s. form.
F5. Proofs/Sec4/ObstacleSpecialization.lean (4.3-4.5, c1) is modified in the working tree; this audit was lc-checked
  against the working tree (2026-11-04 14:20Z). The same holds for Steps/Sec6/ConstantOrderLowerBound.lean and
  Proofs/Sec6/IterativeBound/Statement.lean (c5, log-loss rework of 6.7 in progress).
F6. Name clash: `MatedCRT.Sec7.vertexPoint_mem_cell` is declared in Proofs/Sec7/DivSandpileUpperBound/CrudeCells.lean
  (x2, imported by Steps/Sec7/DivSandpileUpperBound through Interior/ShellGeometry) and in
  Proofs/Sec7/MassBoundOdometer/Count.lean (c3): the modules of 7.1 and 7.2 cannot be imported together
  ("environment already contains"), so no file can use both (Theorem 1.6 needs both). Fix: x2 renames or reuses c3's
  lemma. The 7.1 example is commented out in Audit/Reductions.lean until then (it passed lc at 09:57Z).

## Counts (2026-11-04 14:20Z)
56 numbered results. Proved: 5 (6.3, A.1-A.4). Reduced (committed reduction, checked by an example): 27 (2.3, 2.13,
2.17, 2.19, 4.1-4.3, 4.4 corrected, 4.5 corrected, 4.6-4.8, 5.1-5.4, 6.4-6.6, 6.7 (Draft and (b)), 6.8 (b), 6.9 (local rate and (b)),
6.10, 7.1 (example disabled, F6), 7.2 corrected, 7.3, 7.4). Of these, reduced to Draft Stmts and External inputs only,
with no open step: 4 (2.17, 2.19, 4.7, 6.9 in both forms). Cited results, used only as hypotheses: 11. No committed reduction
(paper-owned): 13 (1.4, 1.6, 2.4, 2.5, 2.6, 3.1, 3.3-3.7, 6.1, 8.1); the Draft forms of 4.4, 4.5, 6.8, 6.9, 7.2 have
only their corrected forms reduced. Distinct open step Props: 26 (A 2, x3 9, c1 1, c2 2, x1 3, c4 7, x2 2), of which
AdjacentCellsMeetAeStep (IR-A2, a literature input to move to External) is used directly by 2.13, 4.2, 4.3,
4.4 corrected, 4.5 corrected, 6.7, 6.8 (b), 6.10, 7.1, 7.2 corrected, 7.3, 7.4. External inputs used: MepsScalingInput
(4.7), DegreeBoundInput (7.4).
