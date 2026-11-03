# FROZEN pending operator approval

Draft statements of "Internal DLA on mated-CRT maps" (arXiv:2211.04891), after the corrections [C1]-[C5]
(docs/campaign/CORRECTIONS.md; review-C, inbox 13:55 UTC) and the statement-fidelity fixes (S1)-(S7) (review-S, inbox
14:05 UTC), written by worker A on 2026-11-03. Format: result, Lean `def`, file:line, corrections/fixes applied, status.
FROZEN = not to be edited without operator approval. The definitions in MatedCRT/Defs that a frozen statement unfolds to
are frozen with it, except `IsGoodAnnulusEvent` (Defs/Setting.lean, open with 6.4-6.10) and `IsObstacleSetting`
(Defs/Sandpile.lean, open with A.2-A.4). OPEN/UNFROZEN statements may still change (escalation named).

1.4 ConvergenceOfIDLAStmt, MatedCRT/Draft/Section1.lean:45, (S5), FROZEN
1.6 ConvergenceOfDivSandpileStmt, MatedCRT/Draft/Section1.lean:56, -, FROZEN
2.2 LQGMeasurePropertiesStmt, MatedCRT/Draft/Section2.lean:39, E-A6 (cited; stated for the affine maps used), FROZEN
2.3 ConeHarmonicBallsStmt, MatedCRT/Draft/Section2.lean:56, -, FROZEN
2.4 ConeHarmonicBallsUpToFixedTimeStmt, MatedCRT/Draft/Section2.lean:66, -, FROZEN
2.5 ConeScaleInvarianceUpToFixedTimeStmt, MatedCRT/Draft/Section2.lean:88, (S1), FROZEN
2.6 ConeScaleInvarianceStmt, MatedCRT/Draft/Section2.lean:108, (S1), FROZEN
2.7 VolumeGrowthStmt, MatedCRT/Draft/Section2.lean:121, -, FROZEN
2.8 CellSizeEstimateStmt, MatedCRT/Draft/Section2.lean:131, -, FROZEN
2.9 CountingMeasureConvergenceStmt, MatedCRT/Draft/Section2.lean:143, -, FROZEN
2.10 DegreeMeasureConvergenceStmt, MatedCRT/Draft/Section2.lean:157, -, FROZEN
2.11 RandomWalkToLBMStmt, MatedCRT/Draft/Section2.lean:169, -, FROZEN
2.13 MaximumPrincipleStmt, MatedCRT/Draft/Section2.lean:183, [C2], FROZEN
2.14 GreenKernelUpperBoundStmt, MatedCRT/Draft/Section2.lean:191, -, FROZEN
2.15 GreenFunctionCrudeBoundStmt, MatedCRT/Draft/Section2.lean:201, -, FROZEN
2.16 GreenKernelLowerBoundStmt, MatedCRT/Draft/Section2.lean:212, -, FROZEN
2.17 BoundedExitTimeRVStmt, MatedCRT/Draft/Section2.lean:227, -, FROZEN
2.18 ExitTimeUpperBoundStmt, MatedCRT/Draft/Section2.lean:239, -, FROZEN
2.19 ExpectedExitTimeExplicitBoundStmt, MatedCRT/Draft/Section2.lean:260, -, FROZEN
3.1 DiscretePotentialTightnessStmt, MatedCRT/Draft/Section3.lean:42, [C3] (S6), FROZEN
3.2 DiscreteHolderContinuityStmt, MatedCRT/Draft/Section3.lean:76, -, FROZEN
3.3 UniformConvergenceGreenKernelStmt, MatedCRT/Draft/Section3.lean:97, [C1], FROZEN
3.4 IntegralConvergenceGreenFunctionStmt, MatedCRT/Draft/Section3.lean:113, [C1], FROZEN
3.5 DiscreteDirichletProblemStmt, MatedCRT/Draft/Section3.lean:136, [C1] (S2), FROZEN
3.6 ConvergenceHarmonicFunctionsStmt, MatedCRT/Draft/Section3.lean:161, (S2), FROZEN
3.7 ConvergenceNormalizedExitTimeStmt, MatedCRT/Draft/Section3.lean:177, [C1], FROZEN
4.1 ConvergenceDivisibleStmt, MatedCRT/Draft/Section4.lean:38, [C1], FROZEN
4.2 DivSandpileLowerBoundStmt, MatedCRT/Draft/Section4.lean:49, -, FROZEN
4.3 DiscreteBasicPropertiesStmt, MatedCRT/Draft/Section4.lean:60, -, FROZEN
4.4 DiscreteLaplacianBoundStmt, MatedCRT/Draft/Section4.lean:73, -, OPEN (E-c1-1: 0 ∈ Λ^ε_t fails when 0 ∉ V^ε(B_ρ)\V^ε(∂B_ρ))
4.5 DiscreteConservationOfMassStmt, MatedCRT/Draft/Section4.lean:89, -, OPEN (E-c1-1)
4.6 SubsequentialConvergenceStmt, MatedCRT/Draft/Section4.lean:104, -, FROZEN
4.7 EquiboundedStmt, MatedCRT/Draft/Section4.lean:121, -, FROZEN
4.8 SubsequentialPropertiesStmt, MatedCRT/Draft/Section4.lean:139, [C1] (S3), FROZEN
5.1 IDLALowerBoundStmt, MatedCRT/Draft/Section5.lean:27, (S5), FROZEN
5.2 GeneralIDLALowerBoundStmt, MatedCRT/Draft/Section5.lean:47, (S5), FROZEN
5.3 MeanValueInequalityStmt, MatedCRT/Draft/Section5.lean:67, [C4], FROZEN
5.4 LLowerBoundStmt, MatedCRT/Draft/Section5.lean:85, [C4], FROZEN
6.1 IDLAUpperBoundStmt, MatedCRT/Draft/Section6.lean:31, (S5), FROZEN
6.3 AbelianIDLAStmt, MatedCRT/Draft/Section6.lean:46, -, FROZEN
6.4 GoodAnnulusPrevalenceStmt, MatedCRT/Draft/Section6.lean:60, [C5] provisional, UNFROZEN (E-A10)
6.5 AnnulusHitStmt, MatedCRT/Draft/Section6.lean:72, [C5] provisional, (S5) inner measure, UNFROZEN (E-A10)
6.6 AnnulusIterateStmt, MatedCRT/Draft/Section6.lean:88, -, UNFROZEN (E-A10)
6.7 ConstantOrderLowerBoundStmt, MatedCRT/Draft/Section6.lean:102, -, UNFROZEN (E-A10)
6.8 ConstantOrderLowerBoundDivStmt, MatedCRT/Draft/Section6.lean:121, -, UNFROZEN (E-A10)
6.9 ChanceOfBeingAbsorbedStmt, MatedCRT/Draft/Section6.lean:140, -, UNFROZEN (E-A10)
6.10 IterativeBoundStmt, MatedCRT/Draft/Section6.lean:162, (S5), UNFROZEN (E-A10)
7.1 DivSandpileUpperBoundStmt, MatedCRT/Draft/Section7.lean:22, -, FROZEN
7.2 MassBoundOdometerStmt, MatedCRT/Draft/Section7.lean:34, -, FROZEN
7.3 OdometerBoundMassStmt, MatedCRT/Draft/Section7.lean:46, -, FROZEN
7.4 CrudeUpperBoundStmt, MatedCRT/Draft/Section7.lean:66, (S4) applied, OPEN (E-c3-1: gap at i = 0, points of cl(Λ^ε_t) \ Λ^ε_t dropped)
8.1 IDLAConstrainedConvergenceStmt, MatedCRT/Draft/Section8.lean:20, (S5), FROZEN
A.1 DiscreteDivergenceTheoremStmt, MatedCRT/Draft/SectionA.lean:25, -, FROZEN (proved, 18d5dd0)
A.2 DiscreteBasicPropertiesGeneralStmt, MatedCRT/Draft/SectionA.lean:32, -, OPEN (E-c1-2: IsObstacleSetting.connected)
A.3 DiscreteLaplacianBoundGeneralStmt, MatedCRT/Draft/SectionA.lean:43, -, OPEN (E-c1-2)
A.4 DiscreteConservationOfMassGeneralStmt, MatedCRT/Draft/SectionA.lean:54, -, OPEN (E-c1-2)

## Literature inputs (MatedCRT/External), pending the operator's source check (INPUT-REQUESTS.md IR-A3)
External/SLE.lean: SLEScaleInvarianceInput, SLEReparametrizationInput, SLEIndepMonoInput, MepsScalingInput,
DegreeBoundInput, SpaceFillingSLEPathInput (theorem numbers unverified). External/QuantumCone.lean: QuantumConeScalingInput.
