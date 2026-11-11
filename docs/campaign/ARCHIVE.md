# Archive of unreachable MatedCRT code (operator decision 89b)

Moved with git mv from MatedCRT/ to archive/ (repository root, not built by the lakefile: lean_lib MatedCRT, globs andSubmodules MatedCRT).
Rule: a file moves only if no counted closure or README route imports it, it is not named in a file of tasks/, it is tracked, it is not under MatedCRT/FirstPass/Frozen or MatedCRT/External, and it was not modified or committed after 2026-11-11 00:05:14 UTC.
Each batch was followed by lb of every counted closure module; a batch that failed was moved back and not committed.

Restore R1 (2026-11-11): the batch B12 had archived nine files that the closure modules MatedCRT.FirstPass.Closure.Final22, Final23 and Final14Full import, directly or transitively (Final22 imports S2y/LateralAssembly250 and S2y/ConeCircleAbsApprox; the other seven are imported by those). They were moved back with git mv to their MatedCRT/ paths and are listed in the section "Restored (R1)" below. The batch table keeps the historical moves.
Root rule, recomputed at HEAD before any further move: the roots are every MatedCRT/FirstPass/Closure/*.lean file and every file containing `closed_`; a file may move only if it is outside the import closure of these roots. At HEAD after R1 the closure of the 22 Closure files is 1455 files, and every tracked MatedCRT .lean file has all its MatedCRT imports present (0 dangling imports).

| old path | new path | batch |
|---|---|---|
| MatedCRT/Audit/ActualAnnulusBarrierComponents.lean | archive/MatedCRT/Audit/ActualAnnulusBarrierComponents.lean | B02 |
| MatedCRT/Audit/AnnulusBarrierResidualLedger.lean | archive/MatedCRT/Audit/AnnulusBarrierResidualLedger.lean | B02 |
| MatedCRT/Audit/InsertionScalingComponents.lean | archive/MatedCRT/Audit/InsertionScalingComponents.lean | B02 |
| MatedCRT/Audit/RepresentedConeStateLaw.lean | archive/MatedCRT/Audit/RepresentedConeStateLaw.lean | B02 |
| MatedCRT/Defs/GaussianMultiplicativeChaos.lean | archive/MatedCRT/Defs/GaussianMultiplicativeChaos.lean | B03 |
| MatedCRT/Defs/LogCorrelatedField.lean | archive/MatedCRT/Defs/LogCorrelatedField.lean | B03 |
| MatedCRT/Defs/RandomMeasureConvergence.lean | archive/MatedCRT/Defs/RandomMeasureConvergence.lean | B03 |
| MatedCRT/FirstPass/Main/Axioms.lean | archive/MatedCRT/FirstPass/Main/Axioms.lean | B04 |
| MatedCRT/FirstPass/S1c/Axioms.lean | archive/MatedCRT/FirstPass/S1c/Axioms.lean | B05 |
| MatedCRT/FirstPass/S1c/FinalAxioms.lean | archive/MatedCRT/FirstPass/S1c/FinalAxioms.lean | B05 |
| MatedCRT/FirstPass/S1d/FinalAxioms.lean | archive/MatedCRT/FirstPass/S1d/FinalAxioms.lean | B06 |
| MatedCRT/FirstPass/S1d/JointBridge.lean | archive/MatedCRT/FirstPass/S1d/JointBridge.lean | B06 |
| MatedCRT/FirstPass/S2VG/Wrappers.lean | archive/MatedCRT/FirstPass/S2VG/Wrappers.lean | B07 |
| MatedCRT/FirstPass/S2g/Assembly24Axioms.lean | archive/MatedCRT/FirstPass/S2g/Assembly24Axioms.lean | B08 |
| MatedCRT/FirstPass/S2g/FullImageAxioms.lean | archive/MatedCRT/FirstPass/S2g/FullImageAxioms.lean | B08 |
| MatedCRT/FirstPass/S2g/HVGoodAxioms.lean | archive/MatedCRT/FirstPass/S2g/HVGoodAxioms.lean | B08 |
| MatedCRT/FirstPass/S2g/LawAxioms.lean | archive/MatedCRT/FirstPass/S2g/LawAxioms.lean | B08 |
| MatedCRT/FirstPass/S2h/ConeNullHull.lean | archive/MatedCRT/FirstPass/S2h/ConeNullHull.lean | B09 |
| MatedCRT/FirstPass/S2h/LogPathwise.lean | archive/MatedCRT/FirstPass/S2h/LogPathwise.lean | B09 |
| MatedCRT/FirstPass/S2h/LogScale.lean | archive/MatedCRT/FirstPass/S2h/LogScale.lean | B09 |
| MatedCRT/FirstPass/S2h/LogZero.lean | archive/MatedCRT/FirstPass/S2h/LogZero.lean | B09 |
| MatedCRT/FirstPass/S2h/PlateauCode.lean | archive/MatedCRT/FirstPass/S2h/PlateauCode.lean | B09 |
| MatedCRT/FirstPass/S2h/PlateauLaw.lean | archive/MatedCRT/FirstPass/S2h/PlateauLaw.lean | B09 |
| MatedCRT/FirstPass/S2h/PlateauNull.lean | archive/MatedCRT/FirstPass/S2h/PlateauNull.lean | B09 |
| MatedCRT/FirstPass/S2h/PlateauRawZero.lean | archive/MatedCRT/FirstPass/S2h/PlateauRawZero.lean | B09 |
| MatedCRT/FirstPass/S2h/PlateauTransfer.lean | archive/MatedCRT/FirstPass/S2h/PlateauTransfer.lean | B09 |
| MatedCRT/FirstPass/S2h/ScaledField.lean | archive/MatedCRT/FirstPass/S2h/ScaledField.lean | B09 |
| MatedCRT/FirstPass/S2k/BorelTransfer.lean | archive/MatedCRT/FirstPass/S2k/BorelTransfer.lean | B10 |
| MatedCRT/FirstPass/S2k/PlateauClosure.lean | archive/MatedCRT/FirstPass/S2k/PlateauClosure.lean | B10 |
| MatedCRT/FirstPass/S2k/PlateauTonelli.lean | archive/MatedCRT/FirstPass/S2k/PlateauTonelli.lean | B10 |
| MatedCRT/FirstPass/S2x/ConeHarmonicBallLocality.lean | archive/MatedCRT/FirstPass/S2x/ConeHarmonicBallLocality.lean | B11 |
| MatedCRT/FirstPass/S2x/ConeHarmonicBallLocalityBorel.lean | archive/MatedCRT/FirstPass/S2x/ConeHarmonicBallLocalityBorel.lean | B11 |
| MatedCRT/FirstPass/S2x/ConeHarmonicBallLocalityL.lean | archive/MatedCRT/FirstPass/S2x/ConeHarmonicBallLocalityL.lean | B11 |
| MatedCRT/FirstPass/S2x/ConeHarmonicBallLocalityUniv.lean | archive/MatedCRT/FirstPass/S2x/ConeHarmonicBallLocalityUniv.lean | B11 |
| MatedCRT/FirstPass/S2x/ConeScaleRadiusPosLimit.lean | archive/MatedCRT/FirstPass/S2x/ConeScaleRadiusPosLimit.lean | B11 |
| MatedCRT/FirstPass/S2y/CircleAvgRadialCont250.lean | archive/MatedCRT/FirstPass/S2y/CircleAvgRadialCont250.lean | B12 |
| MatedCRT/FirstPass/S2y/CirclePointVersion250.lean | archive/MatedCRT/FirstPass/S2y/CirclePointVersion250.lean | B12 |
| MatedCRT/FirstPass/S2y/ConeCircleAbsApprox.lean | archive/MatedCRT/FirstPass/S2y/ConeCircleAbsApprox.lean | B12 |
| MatedCRT/FirstPass/S2y/ConeCircleAverage.lean | archive/MatedCRT/FirstPass/S2y/ConeCircleAverage.lean | B12 |
| MatedCRT/FirstPass/S2y/LateralAssembly250.lean | archive/MatedCRT/FirstPass/S2y/LateralAssembly250.lean | B12 |
| MatedCRT/FirstPass/S2y/LateralInMeasure250.lean | archive/MatedCRT/FirstPass/S2y/LateralInMeasure250.lean | B12 |
| MatedCRT/FirstPass/S2y/LateralL1Limit250.lean | archive/MatedCRT/FirstPass/S2y/LateralL1Limit250.lean | B12 |
| MatedCRT/FirstPass/S2y/LateralL2Limit250.lean | archive/MatedCRT/FirstPass/S2y/LateralL2Limit250.lean | B12 |
| MatedCRT/FirstPass/S2y/RadialProcCont250.lean | archive/MatedCRT/FirstPass/S2y/RadialProcCont250.lean | B12 |
| MatedCRT/FirstPass/S2y/RadialProcL4Ae250.lean | archive/MatedCRT/FirstPass/S2y/RadialProcL4Ae250.lean | B12 |
| MatedCRT/FirstPass/S3i/LensExcursion.lean | archive/MatedCRT/FirstPass/S3i/LensExcursion.lean | B13 |
| MatedCRT/FirstPass/S3t/PathContinuity.lean | archive/MatedCRT/FirstPass/S3t/PathContinuity.lean | B14 |
| MatedCRT/FirstPass/S4S5b/Axioms.lean | archive/MatedCRT/FirstPass/S4S5b/Axioms.lean | B15 |
| MatedCRT/FirstPass/S4S5b/AxiomsWeyl.lean | archive/MatedCRT/FirstPass/S4S5b/AxiomsWeyl.lean | B15 |
| MatedCRT/FirstPass/S5S6S7/Axioms.lean | archive/MatedCRT/FirstPass/S5S6S7/Axioms.lean | B17 |
| MatedCRT/FirstPass/S5c/B2Family.lean | archive/MatedCRT/FirstPass/S5c/B2Family.lean | B18 |
| MatedCRT/FirstPass/S5c/Compact.lean | archive/MatedCRT/FirstPass/S5c/Compact.lean | B18 |
| MatedCRT/FirstPass/S5c/Continuum.lean | archive/MatedCRT/FirstPass/S5c/Continuum.lean | B18 |
| MatedCRT/FirstPass/S5c/Floor.lean | archive/MatedCRT/FirstPass/S5c/Floor.lean | B18 |
| MatedCRT/FirstPass/S5c/FloorFamily.lean | archive/MatedCRT/FirstPass/S5c/FloorFamily.lean | B18 |
| MatedCRT/FirstPass/S5c/GreenGood.lean | archive/MatedCRT/FirstPass/S5c/GreenGood.lean | B18 |
| MatedCRT/FirstPass/S5c/InfDistRat.lean | archive/MatedCRT/FirstPass/S5c/InfDistRat.lean | B18 |
| MatedCRT/FirstPass/S5c/OuterCriterion.lean | archive/MatedCRT/FirstPass/S5c/OuterCriterion.lean | B18 |
| MatedCRT/FirstPass/S5c/Pole.lean | archive/MatedCRT/FirstPass/S5c/Pole.lean | B18 |
| MatedCRT/FirstPass/S5c/ProbFamily.lean | archive/MatedCRT/FirstPass/S5c/ProbFamily.lean | B18 |
| MatedCRT/FirstPass/S5c/ProfileCoding.lean | archive/MatedCRT/FirstPass/S5c/ProfileCoding.lean | B18 |
| MatedCRT/FirstPass/S5c/Superharmonic.lean | archive/MatedCRT/FirstPass/S5c/Superharmonic.lean | B18 |
| MatedCRT/FirstPass/S5d/CellInterior.lean | archive/MatedCRT/FirstPass/S5d/CellInterior.lean | B19 |
| MatedCRT/FirstPass/S6b/Axioms.lean | archive/MatedCRT/FirstPass/S6b/Axioms.lean | B20 |
| MatedCRT/FirstPass/S6h/StateInputs.lean | archive/MatedCRT/FirstPass/S6h/StateInputs.lean | B21 |
| MatedCRT/FirstPass/S6r/MeshPrep.lean | archive/MatedCRT/FirstPass/S6r/MeshPrep.lean | B23 |
| MatedCRT/FirstPass/S6r/MeshPrepFirst.lean | archive/MatedCRT/FirstPass/S6r/MeshPrepFirst.lean | B23 |
| MatedCRT/FirstPass/S6r/MeshPrepSecond.lean | archive/MatedCRT/FirstPass/S6r/MeshPrepSecond.lean | B23 |
| MatedCRT/Proofs/Defs/JointMeasureCharacterization.lean | archive/MatedCRT/Proofs/Defs/JointMeasureCharacterization.lean | B24 |
| MatedCRT/Proofs/Field/WholePlaneLQGCont.lean | archive/MatedCRT/Proofs/Field/WholePlaneLQGCont.lean | B25 |
| MatedCRT/Proofs/Field/WholePlaneWeyl.lean | archive/MatedCRT/Proofs/Field/WholePlaneWeyl.lean | B25 |
| MatedCRT/Proofs/IDLA/JointConvergence.lean | archive/MatedCRT/Proofs/IDLA/JointConvergence.lean | B26 |
| MatedCRT/Proofs/LBM/BrownianPositiveExcursion.lean | archive/MatedCRT/Proofs/LBM/BrownianPositiveExcursion.lean | B28 |
| MatedCRT/Proofs/LBM/GaussianSign.lean | archive/MatedCRT/Proofs/LBM/GaussianSign.lean | B28 |
| MatedCRT/Proofs/Sandpile/ClusterIdentityCorrected.lean | archive/MatedCRT/Proofs/Sandpile/ClusterIdentityCorrected.lean | B30 |
| MatedCRT/Proofs/Sandpile/Properties.lean | archive/MatedCRT/Proofs/Sandpile/Properties.lean | B30 |
| MatedCRT/Proofs/Sandpile/StoppedEquation.lean | archive/MatedCRT/Proofs/Sandpile/StoppedEquation.lean | B30 |
| MatedCRT/Proofs/Sec2/ConeFamilyMeasurable/CitedInputs.lean | archive/MatedCRT/Proofs/Sec2/ConeFamilyMeasurable/CitedInputs.lean | B32 |
| MatedCRT/Proofs/Sec2/ConeFamilyMeasurable/ContactTransfer.lean | archive/MatedCRT/Proofs/Sec2/ConeFamilyMeasurable/ContactTransfer.lean | B32 |
| MatedCRT/Proofs/Sec2/ConeFamilyMeasurable/GlobalCompatibility.lean | archive/MatedCRT/Proofs/Sec2/ConeFamilyMeasurable/GlobalCompatibility.lean | B32 |
| MatedCRT/Proofs/Sec2/ConeFamilyMeasurable/GlobalFamily.lean | archive/MatedCRT/Proofs/Sec2/ConeFamilyMeasurable/GlobalFamily.lean | B32 |
| MatedCRT/Proofs/Sec2/ConeFamilyMeasurable/JointRadialLaw.lean | archive/MatedCRT/Proofs/Sec2/ConeFamilyMeasurable/JointRadialLaw.lean | B32 |
| MatedCRT/Proofs/Sec2/ConeFamilyMeasurable/WholePlaneFamily.lean | archive/MatedCRT/Proofs/Sec2/ConeFamilyMeasurable/WholePlaneFamily.lean | B32 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/ActualAnnulusBarrier.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/ActualAnnulusBarrier.lean | B35 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/DisconnectionKernelMeasurability.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/DisconnectionKernelMeasurability.lean | B35 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/DisconnectionStateMeasurability.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/DisconnectionStateMeasurability.lean | B35 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/EnvSigmaSaturation.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/EnvSigmaSaturation.lean | B35 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSAnnealedEventual.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSAnnealedEventual.lean | B35 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSAnnealedRate.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSAnnealedRate.lean | B35 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSMeanGoodEvent.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSMeanGoodEvent.lean | B35 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSTailGoodEvent.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSTailGoodEvent.lean | B35 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/LocallyFiniteRadialChain.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/LocallyFiniteRadialChain.lean | B35 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/NestedHitOrder.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/NestedHitOrder.lean | B35 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/RateExponents.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/RateExponents.lean | B35 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/StartingCellEventual.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/StartingCellEventual.lean | B35 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/StartingCellInterior.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/StartingCellInterior.lean | B35 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/UniformCellSizeProof.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/UniformCellSizeProof.lean | B35 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/VertexModulus.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/VertexModulus.lean | B35 |
| MatedCRT/Proofs/Sec3/ConvergenceNormalizedExitTime/CenteredBoundaryProbability.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceNormalizedExitTime/CenteredBoundaryProbability.lean | B36 |
| MatedCRT/Proofs/Sec3/ConvergenceNormalizedExitTime/RemoveSingularity.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceNormalizedExitTime/RemoveSingularity.lean | B36 |
| MatedCRT/Proofs/Sec3/ConvergenceNormalizedExitTime/WeightedPotentialHolder.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceNormalizedExitTime/WeightedPotentialHolder.lean | B36 |
| MatedCRT/Proofs/Sec3/DiscreteDirichletProblem/BoundaryDecayMeasurable.lean | archive/MatedCRT/Proofs/Sec3/DiscreteDirichletProblem/BoundaryDecayMeasurable.lean | B37 |
| MatedCRT/Proofs/Sec3/DiscreteDirichletProblem/BoundaryDecayProbability.lean | archive/MatedCRT/Proofs/Sec3/DiscreteDirichletProblem/BoundaryDecayProbability.lean | B37 |
| MatedCRT/Proofs/Sec3/DiscreteDirichletProblem/BoundaryPairMeasurable.lean | archive/MatedCRT/Proofs/Sec3/DiscreteDirichletProblem/BoundaryPairMeasurable.lean | B37 |
| MatedCRT/Proofs/Sec3/DiscreteDirichletProblem/CorrectedFromFrozen.lean | archive/MatedCRT/Proofs/Sec3/DiscreteDirichletProblem/CorrectedFromFrozen.lean | B37 |
| MatedCRT/Proofs/Sec3/DiscreteDirichletProblem/CorrectedHarmonicPrepared.lean | archive/MatedCRT/Proofs/Sec3/DiscreteDirichletProblem/CorrectedHarmonicPrepared.lean | B37 |
| MatedCRT/Proofs/Sec3/DiscreteDirichletProblem/ExitBoundaryUniformLimit.lean | archive/MatedCRT/Proofs/Sec3/DiscreteDirichletProblem/ExitBoundaryUniformLimit.lean | B37 |
| MatedCRT/Proofs/Sec3/DiscreteDirichletProblem/HarmonicBoundaryReduction.lean | archive/MatedCRT/Proofs/Sec3/DiscreteDirichletProblem/HarmonicBoundaryReduction.lean | B37 |
| MatedCRT/Proofs/Sec3/DiscreteDirichletProblem/ModulusFromBounds.lean | archive/MatedCRT/Proofs/Sec3/DiscreteDirichletProblem/ModulusFromBounds.lean | B37 |
| MatedCRT/Proofs/Sec3/DiscreteDirichletProblem/PreparedBarrierAssembly.lean | archive/MatedCRT/Proofs/Sec3/DiscreteDirichletProblem/PreparedBarrierAssembly.lean | B37 |
| MatedCRT/Proofs/Sec3/DiscreteDirichletProblem/PreparedBoundedLaplacian.lean | archive/MatedCRT/Proofs/Sec3/DiscreteDirichletProblem/PreparedBoundedLaplacian.lean | B37 |
| MatedCRT/Proofs/Sec3/DiscreteDirichletProblem/ProjectedBoundaryDecay.lean | archive/MatedCRT/Proofs/Sec3/DiscreteDirichletProblem/ProjectedBoundaryDecay.lean | B37 |
| MatedCRT/Proofs/Sec3/DiscreteDirichletProblem/ProjectedBoundaryReduction.lean | archive/MatedCRT/Proofs/Sec3/DiscreteDirichletProblem/ProjectedBoundaryReduction.lean | B37 |
| MatedCRT/Proofs/Sec3/DiscreteDirichletProblem/ProjectedInteriorVersion.lean | archive/MatedCRT/Proofs/Sec3/DiscreteDirichletProblem/ProjectedInteriorVersion.lean | B37 |
| MatedCRT/Proofs/Sec3/DiscretePotentialTightness/PreparedLocalSelection.lean | archive/MatedCRT/Proofs/Sec3/DiscretePotentialTightness/PreparedLocalSelection.lean | B38 |
| MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/BrownianOccupationGMC.lean | archive/MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/BrownianOccupationGMC.lean | B39 |
| MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/ClockGMCNormalization.lean | archive/MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/ClockGMCNormalization.lean | B39 |
| MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/ConditionalMassBound.lean | archive/MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/ConditionalMassBound.lean | B39 |
| MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/DirichletCircleMeasurable.lean | archive/MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/DirichletCircleMeasurable.lean | B39 |
| MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/DirichletGMCExpectation.lean | archive/MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/DirichletGMCExpectation.lean | B39 |
| MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/GMCExpectation.lean | archive/MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/GMCExpectation.lean | B39 |
| MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/GMCVersionComparison.lean | archive/MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/GMCVersionComparison.lean | B39 |
| MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/GaussianNormalization.lean | archive/MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/GaussianNormalization.lean | B39 |
| MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/JointL1Convergence.lean | archive/MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/JointL1Convergence.lean | B39 |
| MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/JointMassConvergence.lean | archive/MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/JointMassConvergence.lean | B39 |
| MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/JointOccupationMeasurable.lean | archive/MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/JointOccupationMeasurable.lean | B39 |
| MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/KilledOccupationContinuity.lean | archive/MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/KilledOccupationContinuity.lean | B39 |
| MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/L1Expectation.lean | archive/MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/L1Expectation.lean | B39 |
| MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/OccupationDensity.lean | archive/MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/OccupationDensity.lean | B39 |
| MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/OccupationEnergyIsometry.lean | archive/MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/OccupationEnergyIsometry.lean | B39 |
| MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/OccupationExitReduction.lean | archive/MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/OccupationExitReduction.lean | B39 |
| MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/OccupationMassExpectation.lean | archive/MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/OccupationMassExpectation.lean | B39 |
| MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/PathOccupationEnergy.lean | archive/MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/PathOccupationEnergy.lean | B39 |
| MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/PlanarBrownianIncrement.lean | archive/MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/PlanarBrownianIncrement.lean | B39 |
| MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/RegularizedOccupationLimit.lean | archive/MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/RegularizedOccupationLimit.lean | B39 |
| MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/WholePlaneCircleVariance.lean | archive/MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/WholePlaneCircleVariance.lean | B39 |
| MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/WholePlaneClockExpectation.lean | archive/MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/WholePlaneClockExpectation.lean | B39 |
| MatedCRT/Proofs/Sec3/UniformConvergenceGreenKernel/LocalCompactness.lean | archive/MatedCRT/Proofs/Sec3/UniformConvergenceGreenKernel/LocalCompactness.lean | B40 |
| MatedCRT/Proofs/Sec3/UniformConvergenceGreenKernel/PreparedLocalCompactness.lean | archive/MatedCRT/Proofs/Sec3/UniformConvergenceGreenKernel/PreparedLocalCompactness.lean | B40 |
| MatedCRT/Proofs/Sec3/UniformConvergenceGreenKernel/PreparedRandomCompactness.lean | archive/MatedCRT/Proofs/Sec3/UniformConvergenceGreenKernel/PreparedRandomCompactness.lean | B40 |
| MatedCRT/Proofs/Sec4/ConvergenceDivisible/CorrectedPreparedLocalExit.lean | archive/MatedCRT/Proofs/Sec4/ConvergenceDivisible/CorrectedPreparedLocalExit.lean | B42 |
| MatedCRT/Proofs/Sec4/ConvergenceDivisible/LocalClusterMonotone.lean | archive/MatedCRT/Proofs/Sec4/ConvergenceDivisible/LocalClusterMonotone.lean | B42 |
| MatedCRT/Proofs/Sec4/ConvergenceDivisible/LocalExitCompatibility.lean | archive/MatedCRT/Proofs/Sec4/ConvergenceDivisible/LocalExitCompatibility.lean | B42 |
| MatedCRT/Proofs/Sec4/ConvergenceDivisible/PreparedEventMeasurability.lean | archive/MatedCRT/Proofs/Sec4/ConvergenceDivisible/PreparedEventMeasurability.lean | B42 |
| MatedCRT/Proofs/Sec4/ConvergenceDivisible/PreparedIdentification.lean | archive/MatedCRT/Proofs/Sec4/ConvergenceDivisible/PreparedIdentification.lean | B42 |
| MatedCRT/Proofs/Sec4/ConvergenceDivisible/PreparedPathwiseMeasurability.lean | archive/MatedCRT/Proofs/Sec4/ConvergenceDivisible/PreparedPathwiseMeasurability.lean | B42 |
| MatedCRT/Proofs/Sec4/ConvergenceDivisible/PreparedPropertiesEventMeasurability.lean | archive/MatedCRT/Proofs/Sec4/ConvergenceDivisible/PreparedPropertiesEventMeasurability.lean | B42 |
| MatedCRT/Proofs/Sec4/DivSandpileLowerBound/ApproximateCoverage.lean | archive/MatedCRT/Proofs/Sec4/DivSandpileLowerBound/ApproximateCoverage.lean | B43 |
| MatedCRT/Proofs/Sec4/DivSandpileLowerBound/ClusterJumpTimes.lean | archive/MatedCRT/Proofs/Sec4/DivSandpileLowerBound/ClusterJumpTimes.lean | B43 |
| MatedCRT/Proofs/Sec4/DivSandpileLowerBound/CorrectedClusterComparison.lean | archive/MatedCRT/Proofs/Sec4/DivSandpileLowerBound/CorrectedClusterComparison.lean | B43 |
| MatedCRT/Proofs/Sec4/DivSandpileLowerBound/CorrectedClusterProbability.lean | archive/MatedCRT/Proofs/Sec4/DivSandpileLowerBound/CorrectedClusterProbability.lean | B43 |
| MatedCRT/Proofs/Sec4/DivSandpileLowerBound/CorrectedClusterRegular.lean | archive/MatedCRT/Proofs/Sec4/DivSandpileLowerBound/CorrectedClusterRegular.lean | B43 |
| MatedCRT/Proofs/Sec4/DivSandpileLowerBound/CorrectedOdometerConsistency.lean | archive/MatedCRT/Proofs/Sec4/DivSandpileLowerBound/CorrectedOdometerConsistency.lean | B43 |
| MatedCRT/Proofs/Sec4/DivSandpileLowerBound/StrictGapCounterexample.lean | archive/MatedCRT/Proofs/Sec4/DivSandpileLowerBound/StrictGapCounterexample.lean | B43 |
| MatedCRT/Proofs/Sec4/DivSandpileLowerBound/StrictGapDirichletCoordinates.lean | archive/MatedCRT/Proofs/Sec4/DivSandpileLowerBound/StrictGapDirichletCoordinates.lean | B43 |
| MatedCRT/Proofs/Sec4/DivSandpileLowerBound/StrictGapLocalLaw.lean | archive/MatedCRT/Proofs/Sec4/DivSandpileLowerBound/StrictGapLocalLaw.lean | B43 |
| MatedCRT/Proofs/Sec4/DivSandpileLowerBound/StrictGapPairingTransport.lean | archive/MatedCRT/Proofs/Sec4/DivSandpileLowerBound/StrictGapPairingTransport.lean | B43 |
| MatedCRT/Proofs/Sec4/ObstacleSpecialization/SmallMesh.lean | archive/MatedCRT/Proofs/Sec4/ObstacleSpecialization/SmallMesh.lean | B44 |
| MatedCRT/Proofs/Sec4/SubsequentialConvergence/PreparedRegularity.lean | archive/MatedCRT/Proofs/Sec4/SubsequentialConvergence/PreparedRegularity.lean | B45 |
| MatedCRT/Proofs/Sec6/ExitTimeScaleInvariance/Obstruction.lean | archive/MatedCRT/Proofs/Sec6/ExitTimeScaleInvariance/Obstruction.lean | B51 |
| MatedCRT/Proofs/Sec7/DivSandpileUpperBound/BudgetBootstrap.lean | archive/MatedCRT/Proofs/Sec7/DivSandpileUpperBound/BudgetBootstrap.lean | B53 |
| MatedCRT/Proofs/Sec7/DivSandpileUpperBound/CrudeInputs.lean | archive/MatedCRT/Proofs/Sec7/DivSandpileUpperBound/CrudeInputs.lean | B53 |
| MatedCRT/Proofs/Sec7/DivSandpileUpperBound/DyadicHorizonLimit.lean | archive/MatedCRT/Proofs/Sec7/DivSandpileUpperBound/DyadicHorizonLimit.lean | B53 |
| MatedCRT/Proofs/Sec7/DivSandpileUpperBound/DyadicRescaledBounds.lean | archive/MatedCRT/Proofs/Sec7/DivSandpileUpperBound/DyadicRescaledBounds.lean | B53 |
| MatedCRT/Proofs/Sec7/DivSandpileUpperBound/ExitMeasurable.lean | archive/MatedCRT/Proofs/Sec7/DivSandpileUpperBound/ExitMeasurable.lean | B53 |
| MatedCRT/Proofs/Sec7/DivSandpileUpperBound/FiniteStopping.lean | archive/MatedCRT/Proofs/Sec7/DivSandpileUpperBound/FiniteStopping.lean | B53 |
| MatedCRT/Proofs/Sec7/DivSandpileUpperBound/InitialDyadicBudget.lean | archive/MatedCRT/Proofs/Sec7/DivSandpileUpperBound/InitialDyadicBudget.lean | B53 |
| MatedCRT/Proofs/Sec7/DivSandpileUpperBound/InitialShellCutoffOfScaling.lean | archive/MatedCRT/Proofs/Sec7/DivSandpileUpperBound/InitialShellCutoffOfScaling.lean | B53 |
| MatedCRT/Proofs/Sec7/DivSandpileUpperBound/LocalizedShellIteration.lean | archive/MatedCRT/Proofs/Sec7/DivSandpileUpperBound/LocalizedShellIteration.lean | B53 |
| MatedCRT/Proofs/Sec7/DivSandpileUpperBound/LogBudgetBootstrap.lean | archive/MatedCRT/Proofs/Sec7/DivSandpileUpperBound/LogBudgetBootstrap.lean | B53 |
| MatedCRT/Proofs/Sec7/DivSandpileUpperBound/LogBudgetLimit.lean | archive/MatedCRT/Proofs/Sec7/DivSandpileUpperBound/LogBudgetLimit.lean | B53 |
| MatedCRT/Proofs/Sec7/DivSandpileUpperBound/LogHalvingBootstrap.lean | archive/MatedCRT/Proofs/Sec7/DivSandpileUpperBound/LogHalvingBootstrap.lean | B53 |
| MatedCRT/Proofs/Sec7/DivSandpileUpperBound/LogShellIterationEvents.lean | archive/MatedCRT/Proofs/Sec7/DivSandpileUpperBound/LogShellIterationEvents.lean | B53 |
| MatedCRT/Proofs/Sec7/DivSandpileUpperBound/LogSurvival.lean | archive/MatedCRT/Proofs/Sec7/DivSandpileUpperBound/LogSurvival.lean | B53 |
| MatedCRT/Proofs/Sec7/DivSandpileUpperBound/PolynomialBootstrap.lean | archive/MatedCRT/Proofs/Sec7/DivSandpileUpperBound/PolynomialBootstrap.lean | B53 |
| MatedCRT/Proofs/Sec7/DivSandpileUpperBound/RepeatedHalving.lean | archive/MatedCRT/Proofs/Sec7/DivSandpileUpperBound/RepeatedHalving.lean | B53 |
| MatedCRT/Proofs/Sec7/DivSandpileUpperBound/RpowBudget.lean | archive/MatedCRT/Proofs/Sec7/DivSandpileUpperBound/RpowBudget.lean | B53 |
| MatedCRT/Proofs/Sec7/DivSandpileUpperBound/ShellIterationEvents.lean | archive/MatedCRT/Proofs/Sec7/DivSandpileUpperBound/ShellIterationEvents.lean | B53 |
| MatedCRT/Proofs/Sec7/DivSandpileUpperBound/ShellIterationOfScaling.lean | archive/MatedCRT/Proofs/Sec7/DivSandpileUpperBound/ShellIterationOfScaling.lean | B53 |
| MatedCRT/Proofs/Sec7/DivSandpileUpperBound/ShiftedBootstrap.lean | archive/MatedCRT/Proofs/Sec7/DivSandpileUpperBound/ShiftedBootstrap.lean | B53 |
| MatedCRT/Proofs/Sec7/DivSandpileUpperBound/TotalBudgetLimit.lean | archive/MatedCRT/Proofs/Sec7/DivSandpileUpperBound/TotalBudgetLimit.lean | B53 |
| MatedCRT/Proposed/Berestycki2017.lean | archive/MatedCRT/Proposed/Berestycki2017.lean | B55 |

## Restored (R1)

Moved back with git mv from archive/ to MatedCRT/ (the batch B12 row above gives the old path). Each is imported by MatedCRT.FirstPass.Closure.Final22, Final23 or Final14Full, directly or transitively.

| archive path (before R1) | MatedCRT path (after R1) | restored by |
|---|---|---|
| archive/MatedCRT/FirstPass/S2y/CircleAvgRadialCont250.lean | MatedCRT/FirstPass/S2y/CircleAvgRadialCont250.lean | R1 |
| archive/MatedCRT/FirstPass/S2y/ConeCircleAbsApprox.lean | MatedCRT/FirstPass/S2y/ConeCircleAbsApprox.lean | R1 |
| archive/MatedCRT/FirstPass/S2y/ConeCircleAverage.lean | MatedCRT/FirstPass/S2y/ConeCircleAverage.lean | R1 |
| archive/MatedCRT/FirstPass/S2y/LateralAssembly250.lean | MatedCRT/FirstPass/S2y/LateralAssembly250.lean | R1 |
| archive/MatedCRT/FirstPass/S2y/LateralInMeasure250.lean | MatedCRT/FirstPass/S2y/LateralInMeasure250.lean | R1 |
| archive/MatedCRT/FirstPass/S2y/LateralL1Limit250.lean | MatedCRT/FirstPass/S2y/LateralL1Limit250.lean | R1 |
| archive/MatedCRT/FirstPass/S2y/LateralL2Limit250.lean | MatedCRT/FirstPass/S2y/LateralL2Limit250.lean | R1 |
| archive/MatedCRT/FirstPass/S2y/RadialProcCont250.lean | MatedCRT/FirstPass/S2y/RadialProcCont250.lean | R1 |
| archive/MatedCRT/FirstPass/S2y/RadialProcL4Ae250.lean | MatedCRT/FirstPass/S2y/RadialProcL4Ae250.lean | R1 |

## Batch F (build failures)

Moved with git mv from MatedCRT/ to archive/ (same relative path). Each file is a tracked module that fails to build at HEAD in the whole-library build `lb MatedCRT` (log logs/lb/051401-2018640.log), and none of the three is in the import closure of a root. The roots are the 22 MatedCRT/FirstPass/Closure/*.lean files, every live file containing `closed_`, MatedCRT/FirstPass/Main.lean, MatedCRT/FirstPass/LIClosed68Y.lean, and the module paths named in README.md and docs/campaign/PHASE2-INVENTORY.md. No live module imports any of the three except S5s.lean, which is itself moved.

| old path | new path | first error (lb MatedCRT) | reason unreachable |
|---|---|---|---|
| MatedCRT/FirstPass/S5c/ClusterInclusion.lean | archive/MatedCRT/FirstPass/S5c/ClusterInclusion.lean | :45:56 application type mismatch: `hmeas` has type `Measurable` where `AEMeasurable` is expected | not reached from any root; no live module imports it (EntryTimes.lean:14 names one of its lemmas in a comment) |
| MatedCRT/FirstPass/S5s/Copies.lean | archive/MatedCRT/FirstPass/S5s/Copies.lean | :1803:42 unknown identifier `subset_ball_of_lt_clusterExitTime` | not reached from any root; imported only by S5s.lean |
| MatedCRT/FirstPass/S5s.lean | archive/MatedCRT/FirstPass/S5s.lean | no own error; it imports MatedCRT.FirstPass.S5s.Copies, which fails | not reached from any root; imports only Copies |

Other entries of the same whole-library build are not tracked modules: 16 are untracked probe or axiom-check files (for example MatedCRT/Audit/RefutationsProbe.lean, MatedCRT/Proofs/IDLA/NamesY2.lean); 11 name modules that are archived or have no file, and are imported by untracked IntegralConvergenceGreenFunction/*AxiomsY5.lean files (for example JointL1AxiomsY5.lean imports ...JointL1Convergence and ...ConditionalMassBound, which are archived). Those untracked files are left in place.

## Batch G (dev artifacts)

Moved with git mv from MatedCRT/ to archive/ (same relative path), task p2-clean-h1. Each file name contains `Test`, the dev-artifact pattern of the hygiene table (a) in reports/z9-hygiene-h1.txt. For each file: no Lean file under MatedCRT/ imports it (working tree, untracked files included), no active task file in tasks/ names it, and it is not reachable from the library root MatedCRT.lean, the 22 FirstPass/Closure modules, any */Main.lean, the closed_ declarations or the names of README.md and PHASE2-INVENTORY.md. Build check after the moves: lb +MatedCRT, the 22 Closure modules and +MatedCRT.FirstPass.Main, all pass (log notes/z9-scripts/lb-batchG.txt, LB_RC=0).

| old path | new path | importers | owner | reachable from roots |
|---|---|---|---|---|
| MatedCRT/FirstPass/S4S6c/TestBridge.lean | archive/MatedCRT/FirstPass/S4S6c/TestBridge.lean | none | none | no |
| MatedCRT/FirstPass/S4S6c/TestProduct.lean | archive/MatedCRT/FirstPass/S4S6c/TestProduct.lean | none | none | no |
| MatedCRT/FirstPass/S6r/OneTest/ExitQHone.lean | archive/MatedCRT/FirstPass/S6r/OneTest/ExitQHone.lean | none | none | no; its path is named in a docstring of MatedCRT/FirstPass/S6r/Shells/ChoiceStopped.lean (lines 8, 130), not an import |

## Rule R2 (2026-11-11), batches B13 onward

Decision of lead li (standing delegation, task p2-archive-batches-2). The date condition of the rule above (not committed after 2026-11-11 00:05:14 UTC) is replaced by the following. A tracked `MatedCRT/**/*.lean` file outside the import closure of the roots of `docs/campaign/ARCHIVE-RECHECK.md` may move if:

(a) every commit touching it after 2026-11-11 00:05:14 UTC is comment-only for that file: every line changed by `git diff -U0 <c>^ <c> -- <file>` lies inside a comment or docstring;
(b) it is not named in a `tasks/*.md` file modified on 2026-11-11;
(c) it has no uncommitted edits;
(d) no file that stays under `MatedCRT/` imports it (iterated: a file moves once its importers have moved);
(e) it is not listed in `notes/hyg-A.txt`, `hyg-B.txt`, `hyg-C.txt`, `stale-1.txt` or `stale-1b.txt` while z9, z10 or z11 report IN_PROGRESS. Such files form a final batch once all three read DONE (bounded wait 40 min, then left in place and reported).

Each batch is `git mv`ed from `MatedCRT/` to `archive/MatedCRT/` in import order (importers first, at most 40 files), checked for imports of its own modules from files under `MatedCRT/`, and committed alone with its rows below.

| old path | new path | batch |
|---|---|---|
| MatedCRT/Audit/Main.lean | archive/MatedCRT/Audit/Main.lean | B13 |
| MatedCRT/Audit/Sec3PointwiseRates.lean | archive/MatedCRT/Audit/Sec3PointwiseRates.lean | B13 |
| MatedCRT/FirstPass/S2i.lean | archive/MatedCRT/FirstPass/S2i.lean | B13 |
| MatedCRT/FirstPass/S2l.lean | archive/MatedCRT/FirstPass/S2l.lean | B13 |
| MatedCRT/FirstPass/S2y.lean | archive/MatedCRT/FirstPass/S2y.lean | B13 |
| MatedCRT/FirstPass/S3h.lean | archive/MatedCRT/FirstPass/S3h.lean | B13 |
| MatedCRT/FirstPass/S5e.lean | archive/MatedCRT/FirstPass/S5e.lean | B13 |
| MatedCRT/FirstPass/S5n.lean | archive/MatedCRT/FirstPass/S5n.lean | B13 |
| MatedCRT/FirstPass/S5p.lean | archive/MatedCRT/FirstPass/S5p.lean | B13 |
| MatedCRT/FirstPass/S6b.lean | archive/MatedCRT/FirstPass/S6b.lean | B13 |
| MatedCRT/FirstPass/S6e.lean | archive/MatedCRT/FirstPass/S6e.lean | B13 |
| MatedCRT/FirstPass/S6g.lean | archive/MatedCRT/FirstPass/S6g.lean | B13 |
| MatedCRT/FirstPass/LPBridge/LQGExistence.lean | archive/MatedCRT/FirstPass/LPBridge/LQGExistence.lean | B13 |
| MatedCRT/FirstPass/S2g/Assembly24.lean | archive/MatedCRT/FirstPass/S2g/Assembly24.lean | B13 |
| MatedCRT/FirstPass/S2g/FamilyLocal.lean | archive/MatedCRT/FirstPass/S2g/FamilyLocal.lean | B13 |
| MatedCRT/FirstPass/S2g/HVGood.lean | archive/MatedCRT/FirstPass/S2g/HVGood.lean | B13 |
| MatedCRT/FirstPass/S2g/LawCoded25.lean | archive/MatedCRT/FirstPass/S2g/LawCoded25.lean | B13 |
| MatedCRT/FirstPass/S2g/Locality.lean | archive/MatedCRT/FirstPass/S2g/Locality.lean | B13 |
| MatedCRT/FirstPass/S2g/Section6CanonicalAxioms.lean | archive/MatedCRT/FirstPass/S2g/Section6CanonicalAxioms.lean | B13 |
| MatedCRT/FirstPass/S2g/Transfer.lean | archive/MatedCRT/FirstPass/S2g/Transfer.lean | B13 |
| MatedCRT/FirstPass/S2x/ConeScaleRadiusPos.lean | archive/MatedCRT/FirstPass/S2x/ConeScaleRadiusPos.lean | B13 |
| MatedCRT/FirstPass/S3S4b/TruncatedLawsBridge.lean | archive/MatedCRT/FirstPass/S3S4b/TruncatedLawsBridge.lean | B13 |
| MatedCRT/FirstPass/S4S6c/AbsorbedChernoffTail.lean | archive/MatedCRT/FirstPass/S4S6c/AbsorbedChernoffTail.lean | B13 |
| MatedCRT/FirstPass/S4S6c/Amplification68.lean | archive/MatedCRT/FirstPass/S4S6c/Amplification68.lean | B13 |
| MatedCRT/FirstPass/S4S6c/CGRCYInst68.lean | archive/MatedCRT/FirstPass/S4S6c/CGRCYInst68.lean | B13 |
| MatedCRT/FirstPass/S4S6c/CGRCYK2Inst68.lean | archive/MatedCRT/FirstPass/S4S6c/CGRCYK2Inst68.lean | B13 |
| MatedCRT/FirstPass/S4S6c/CGResVol68.lean | archive/MatedCRT/FirstPass/S4S6c/CGResVol68.lean | B13 |
| MatedCRT/FirstPass/S4S6c/Closed6x68Le.lean | archive/MatedCRT/FirstPass/S4S6c/Closed6x68Le.lean | B13 |
| MatedCRT/FirstPass/S4S6c/CountingExitAlphaCore68.lean | archive/MatedCRT/FirstPass/S4S6c/CountingExitAlphaCore68.lean | B13 |
| MatedCRT/FirstPass/S4S6c/CoverMinorantAE.lean | archive/MatedCRT/FirstPass/S4S6c/CoverMinorantAE.lean | B13 |
| MatedCRT/FirstPass/S4S6c/Exponents.lean | archive/MatedCRT/FirstPass/S4S6c/Exponents.lean | B13 |
| MatedCRT/FirstPass/S4S6c/GoodRadii.lean | archive/MatedCRT/FirstPass/S4S6c/GoodRadii.lean | B13 |
| MatedCRT/FirstPass/S4S6c/HoneCover68.lean | archive/MatedCRT/FirstPass/S4S6c/HoneCover68.lean | B13 |
| MatedCRT/FirstPass/S4S6c/LayerCrossing68.lean | archive/MatedCRT/FirstPass/S4S6c/LayerCrossing68.lean | B13 |
| MatedCRT/FirstPass/S4S6c/MeshExitPw68.lean | archive/MatedCRT/FirstPass/S4S6c/MeshExitPw68.lean | B13 |
| MatedCRT/FirstPass/S4S6c/NextExitTime.lean | archive/MatedCRT/FirstPass/S4S6c/NextExitTime.lean | B13 |
| MatedCRT/FirstPass/S4S6c/Redesign68S9.lean | archive/MatedCRT/FirstPass/S4S6c/Redesign68S9.lean | B13 |
| MatedCRT/FirstPass/S4S6c/ShellOrderLoc68.lean | archive/MatedCRT/FirstPass/S4S6c/ShellOrderLoc68.lean | B13 |
| MatedCRT/FirstPass/S4S6c/ShellSmallR68.lean | archive/MatedCRT/FirstPass/S4S6c/ShellSmallR68.lean | B13 |
| MatedCRT/FirstPass/S4S6c/Uniform68LogRadius2.lean | archive/MatedCRT/FirstPass/S4S6c/Uniform68LogRadius2.lean | B13 |
| MatedCRT/FirstPass/S2z.lean | archive/MatedCRT/FirstPass/S2z.lean | B14 |
| MatedCRT/FirstPass/S2g/PlateauZero.lean | archive/MatedCRT/FirstPass/S2g/PlateauZero.lean | B14 |
| MatedCRT/FirstPass/S4S6c/AbsorbedChernoff69.lean | archive/MatedCRT/FirstPass/S4S6c/AbsorbedChernoff69.lean | B14 |
| MatedCRT/FirstPass/S4S6c/AmplifiedBound.lean | archive/MatedCRT/FirstPass/S4S6c/AmplifiedBound.lean | B14 |
| MatedCRT/FirstPass/S4S6c/CGRCXLeCore68.lean | archive/MatedCRT/FirstPass/S4S6c/CGRCXLeCore68.lean | B14 |
| MatedCRT/FirstPass/S4S6c/CellSize68.lean | archive/MatedCRT/FirstPass/S4S6c/CellSize68.lean | B14 |
| MatedCRT/FirstPass/S4S6c/ShellBallLoc68.lean | archive/MatedCRT/FirstPass/S4S6c/ShellBallLoc68.lean | B14 |
| MatedCRT/FirstPass/S4S6c/ShellChainCGRCXLe68.lean | archive/MatedCRT/FirstPass/S4S6c/ShellChainCGRCXLe68.lean | B14 |
| MatedCRT/FirstPass/S4S6c/Uniform68LogRadius.lean | archive/MatedCRT/FirstPass/S4S6c/Uniform68LogRadius.lean | B14 |
| MatedCRT/FirstPass/S4S6c/Uniform68Monotone.lean | archive/MatedCRT/FirstPass/S4S6c/Uniform68Monotone.lean | B14 |
| MatedCRT/FirstPass/S4S6c/Uniform68Params.lean | archive/MatedCRT/FirstPass/S4S6c/Uniform68Params.lean | B14 |
| MatedCRT/FirstPass/S4S6c/Uniform68PointEvents.lean | archive/MatedCRT/FirstPass/S4S6c/Uniform68PointEvents.lean | B14 |
| MatedCRT/FirstPass/S4S6c/UniformLayer68.lean | archive/MatedCRT/FirstPass/S4S6c/UniformLayer68.lean | B14 |
| MatedCRT/FirstPass/S4S6c/VolumeCountable68.lean | archive/MatedCRT/FirstPass/S4S6c/VolumeCountable68.lean | B14 |
| MatedCRT/FirstPass/S4S6c/WalkExitW.lean | archive/MatedCRT/FirstPass/S4S6c/WalkExitW.lean | B14 |
| MatedCRT/FirstPass/S4S6c/WindowUniform68.lean | archive/MatedCRT/FirstPass/S4S6c/WindowUniform68.lean | B14 |
| MatedCRT/FirstPass/S4d/Final42e.lean | archive/MatedCRT/FirstPass/S4d/Final42e.lean | B14 |
| MatedCRT/FirstPass/S5c/B2Bad.lean | archive/MatedCRT/FirstPass/S5c/B2Bad.lean | B14 |
| MatedCRT/FirstPass/S5c/DensityFloor.lean | archive/MatedCRT/FirstPass/S5c/DensityFloor.lean | B14 |
| MatedCRT/FirstPass/S5c/FloorEventually.lean | archive/MatedCRT/FirstPass/S5c/FloorEventually.lean | B14 |
| MatedCRT/FirstPass/S5c/HmemCell.lean | archive/MatedCRT/FirstPass/S5c/HmemCell.lean | B14 |
| MatedCRT/FirstPass/S5c/NullContainment.lean | archive/MatedCRT/FirstPass/S5c/NullContainment.lean | B14 |
| MatedCRT/FirstPass/S5c/ProbLocalize.lean | archive/MatedCRT/FirstPass/S5c/ProbLocalize.lean | B14 |
| MatedCRT/FirstPass/S5c/StoppedInterior.lean | archive/MatedCRT/FirstPass/S5c/StoppedInterior.lean | B14 |
| MatedCRT/FirstPass/S5c/TendsOneOnOfSubseq.lean | archive/MatedCRT/FirstPass/S5c/TendsOneOnOfSubseq.lean | B14 |
| MatedCRT/FirstPass/S5d/ClusterFromPoint.lean | archive/MatedCRT/FirstPass/S5d/ClusterFromPoint.lean | B14 |
| MatedCRT/FirstPass/S5d/KillingComponent.lean | archive/MatedCRT/FirstPass/S5d/KillingComponent.lean | B14 |
| MatedCRT/FirstPass/S5d/StoppedSecondGreen.lean | archive/MatedCRT/FirstPass/S5d/StoppedSecondGreen.lean | B14 |
| MatedCRT/FirstPass/S6e/DdSources.lean | archive/MatedCRT/FirstPass/S6e/DdSources.lean | B14 |
| MatedCRT/FirstPass/S6e/UniversalEvent.lean | archive/MatedCRT/FirstPass/S6e/UniversalEvent.lean | B14 |
| MatedCRT/FirstPass/S6j/Radius.lean | archive/MatedCRT/FirstPass/S6j/Radius.lean | B14 |
| MatedCRT/FirstPass/S6m/State.lean | archive/MatedCRT/FirstPass/S6m/State.lean | B14 |
| MatedCRT/FirstPass/S6r/GoodAnnulusMeas.lean | archive/MatedCRT/FirstPass/S6r/GoodAnnulusMeas.lean | B14 |
| MatedCRT/Proofs/MatingOfTrees/CountableMeshContactTraces.lean | archive/MatedCRT/Proofs/MatingOfTrees/CountableMeshContactTraces.lean | B14 |
| MatedCRT/Proofs/Sec1/EnvironmentScaling/CanonicalEntranceKernels.lean | archive/MatedCRT/Proofs/Sec1/EnvironmentScaling/CanonicalEntranceKernels.lean | B14 |
| MatedCRT/Proofs/Sec1/EnvironmentScaling/ClockLimitBorel.lean | archive/MatedCRT/Proofs/Sec1/EnvironmentScaling/ClockLimitBorel.lean | B14 |
| MatedCRT/Proofs/Sec1/EnvironmentScaling/ConeAreaLimit.lean | archive/MatedCRT/Proofs/Sec1/EnvironmentScaling/ConeAreaLimit.lean | B14 |
| MatedCRT/Proofs/Sec1/EnvironmentScaling/CouplingLift.lean | archive/MatedCRT/Proofs/Sec1/EnvironmentScaling/CouplingLift.lean | B14 |
| MatedCRT/Proofs/Sec1/EnvironmentScaling/CurveAreaRecovery.lean | archive/MatedCRT/Proofs/Sec1/EnvironmentScaling/CurveAreaRecovery.lean | B14 |
| MatedCRT/Proofs/Sec1/EnvironmentScaling/FieldVersionTransport.lean | archive/MatedCRT/Proofs/Sec1/EnvironmentScaling/FieldVersionTransport.lean | B14 |
| MatedCRT/FirstPass/LICGRCXLe68.lean | archive/MatedCRT/FirstPass/LICGRCXLe68.lean | B15 |
| MatedCRT/FirstPass/S4S6c/Uniform68Point.lean | archive/MatedCRT/FirstPass/S4S6c/Uniform68Point.lean | B15 |
| MatedCRT/FirstPass/S4S6c/Uniform68Radius.lean | archive/MatedCRT/FirstPass/S4S6c/Uniform68Radius.lean | B15 |
| MatedCRT/FirstPass/S5c/FloorMono.lean | archive/MatedCRT/FirstPass/S5c/FloorMono.lean | B15 |
| MatedCRT/FirstPass/S5c/ProbLimit.lean | archive/MatedCRT/FirstPass/S5c/ProbLimit.lean | B15 |
| MatedCRT/FirstPass/S5c/SubseqCriterion.lean | archive/MatedCRT/FirstPass/S5c/SubseqCriterion.lean | B15 |
| MatedCRT/FirstPass/S6j/StateGood.lean | archive/MatedCRT/FirstPass/S6j/StateGood.lean | B15 |
| MatedCRT/Proofs/MatingOfTrees/ConnectedCellTraces.lean | archive/MatedCRT/Proofs/MatingOfTrees/ConnectedCellTraces.lean | B15 |
| MatedCRT/Proofs/Sec1/EnvironmentScaling/AllStartsClock.lean | archive/MatedCRT/Proofs/Sec1/EnvironmentScaling/AllStartsClock.lean | B15 |
| MatedCRT/Proofs/Sec1/EnvironmentScaling/AreaScaling.lean | archive/MatedCRT/Proofs/Sec1/EnvironmentScaling/AreaScaling.lean | B15 |
| MatedCRT/Proofs/Sec1/EnvironmentScaling/IGUniformShift.lean | archive/MatedCRT/Proofs/Sec1/EnvironmentScaling/IGUniformShift.lean | B15 |
| MatedCRT/Proofs/Sec1/EnvironmentScaling/MeasurableRadialIntegrals.lean | archive/MatedCRT/Proofs/Sec1/EnvironmentScaling/MeasurableRadialIntegrals.lean | B15 |
| MatedCRT/Proofs/Sec1/EnvironmentScaling/PostLastZeroTransfer.lean | archive/MatedCRT/Proofs/Sec1/EnvironmentScaling/PostLastZeroTransfer.lean | B15 |
| MatedCRT/Proofs/Sec1/EnvironmentScaling/PostLastZeroWeakLimit.lean | archive/MatedCRT/Proofs/Sec1/EnvironmentScaling/PostLastZeroWeakLimit.lean | B15 |
| MatedCRT/Proofs/Sec1/EnvironmentScaling/RepresentedCircleCodeLaw.lean | archive/MatedCRT/Proofs/Sec1/EnvironmentScaling/RepresentedCircleCodeLaw.lean | B15 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/AnnulusEnvelopeProof.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/AnnulusEnvelopeProof.lean | B15 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/CorrectedFromAssembly.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/CorrectedFromAssembly.lean | B15 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSJointGoodEvent.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSJointGoodEvent.lean | B15 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/PointwiseEnvelopeMean.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/PointwiseEnvelopeMean.lean | B15 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/PointwiseEnvelopeTail.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/PointwiseEnvelopeTail.lean | B15 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/SameWalkAssemblyAe.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/SameWalkAssemblyAe.lean | B15 |
| MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/DirichletStoppedClockRepair.lean | archive/MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/DirichletStoppedClockRepair.lean | B15 |
| MatedCRT/Proofs/Sec5/EarlierTimeCover.lean | archive/MatedCRT/Proofs/Sec5/EarlierTimeCover.lean | B15 |
| MatedCRT/Proofs/Sec5/StoppedInteriorGeometryMeasurable.lean | archive/MatedCRT/Proofs/Sec5/StoppedInteriorGeometryMeasurable.lean | B15 |
| MatedCRT/Proofs/Sec5/StoppedLayerPotentialReduction.lean | archive/MatedCRT/Proofs/Sec5/StoppedLayerPotentialReduction.lean | B15 |
| MatedCRT/Proofs/Sec5/StoppedMarginProducerAssembly.lean | archive/MatedCRT/Proofs/Sec5/StoppedMarginProducerAssembly.lean | B15 |
| MatedCRT/Proofs/Sec5/StoppedPoleInnerDegreeMoments.lean | archive/MatedCRT/Proofs/Sec5/StoppedPoleInnerDegreeMoments.lean | B15 |
| MatedCRT/FirstPass/S4S6c/Uniform68Band.lean | archive/MatedCRT/FirstPass/S4S6c/Uniform68Band.lean | B15 |
| MatedCRT/FirstPass/S4S6c/Uniform68Local.lean | archive/MatedCRT/FirstPass/S4S6c/Uniform68Local.lean | B15 |
| MatedCRT/FirstPass/S5c/Scaling.lean | archive/MatedCRT/FirstPass/S5c/Scaling.lean | B15 |
| MatedCRT/Proofs/MatingOfTrees/AdjacentContactWitnesses.lean | archive/MatedCRT/Proofs/MatingOfTrees/AdjacentContactWitnesses.lean | B15 |
| MatedCRT/Proofs/Sec1/EnvironmentScaling/Clock.lean | archive/MatedCRT/Proofs/Sec1/EnvironmentScaling/Clock.lean | B15 |
| MatedCRT/Proofs/Sec1/EnvironmentScaling/CountableObservableIdentification.lean | archive/MatedCRT/Proofs/Sec1/EnvironmentScaling/CountableObservableIdentification.lean | B15 |
| MatedCRT/Proofs/Sec1/EnvironmentScaling/PostLastZeroShiftedLaw.lean | archive/MatedCRT/Proofs/Sec1/EnvironmentScaling/PostLastZeroShiftedLaw.lean | B15 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/AnnealedTailRate.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/AnnealedTailRate.lean | B15 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSCellAnnulusEvent.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSCellAnnulusEvent.lean | B15 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSEventualRate.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSEventualRate.lean | B15 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSMeanEventual.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSMeanEventual.lean | B15 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/SameWalkRatesAe.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/SameWalkRatesAe.lean | B15 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/UniformCellSizeMeasurable.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/UniformCellSizeMeasurable.lean | B15 |
| MatedCRT/FirstPass/S4S6c/Uniform68Events.lean | archive/MatedCRT/FirstPass/S4S6c/Uniform68Events.lean | B16 |
| MatedCRT/FirstPass/S4S6c/Uniform68Inputs.lean | archive/MatedCRT/FirstPass/S4S6c/Uniform68Inputs.lean | B16 |
| MatedCRT/Proofs/MatingOfTrees/BrownianAdjacencyExcursions.lean | archive/MatedCRT/Proofs/MatingOfTrees/BrownianAdjacencyExcursions.lean | B16 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/AnnealedTailAE.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/AnnealedTailAE.lean | B16 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSCellSizeMeasurable.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSCellSizeMeasurable.lean | B16 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSFixedScale.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSFixedScale.lean | B16 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSMeanRates.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSMeanRates.lean | B16 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/WalkDiscrepancyZero.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/WalkDiscrepancyZero.lean | B16 |
| MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/DirichletClockTransfer.lean | archive/MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/DirichletClockTransfer.lean | B16 |
| MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/StoppedClockDenseLimit.lean | archive/MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/StoppedClockDenseLimit.lean | B16 |
| MatedCRT/Proofs/Sec5/FieldCircleVersionProof.lean | archive/MatedCRT/Proofs/Sec5/FieldCircleVersionProof.lean | B16 |
| MatedCRT/Proofs/Sec5/StoppedInteriorGeometryProof.lean | archive/MatedCRT/Proofs/Sec5/StoppedInteriorGeometryProof.lean | B16 |
| MatedCRT/Proofs/Sec5/StoppedMarginStepAssembly.lean | archive/MatedCRT/Proofs/Sec5/StoppedMarginStepAssembly.lean | B16 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/AnnealedTail.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/AnnealedTail.lean | B16 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/BrownianMinimumUnique.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/BrownianMinimumUnique.lean | B16 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSCellSizeEvent.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSCellSizeEvent.lean | B16 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSCutoffMean.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSCutoffMean.lean | B16 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSDiskMargin.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSDiskMargin.lean | B16 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/MesoscopicMeanRates.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/MesoscopicMeanRates.lean | B16 |
| MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/LocalKilledInverseConvergence.lean | archive/MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/LocalKilledInverseConvergence.lean | B16 |
| MatedCRT/Proofs/Sec5/StoppedActualMarginCode.lean | archive/MatedCRT/Proofs/Sec5/StoppedActualMarginCode.lean | B16 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/BrownianMinimum.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/BrownianMinimum.lean | B16 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSCutoffTail.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSCutoffTail.lean | B16 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSUniformRate.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSUniformRate.lean | B16 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/MesoscopicMeanScale.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/MesoscopicMeanScale.lean | B16 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/WalkDiscrepancyMoment.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/WalkDiscrepancyMoment.lean | B16 |
| MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/KilledInverseConvergence.lean | archive/MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/KilledInverseConvergence.lean | B16 |
| MatedCRT/Proofs/Sec5/StoppedActualValueVersions.lean | archive/MatedCRT/Proofs/Sec5/StoppedActualValueVersions.lean | B16 |
| MatedCRT/Proofs/Sec5/StoppedRationalMembership.lean | archive/MatedCRT/Proofs/Sec5/StoppedRationalMembership.lean | B16 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSMesoscopicRate.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSMesoscopicRate.lean | B16 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSUniformDistance.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSUniformDistance.lean | B16 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/WalkDiscrepancyMeasurable.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/WalkDiscrepancyMeasurable.lean | B16 |
| MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/ApproxClockOccupation.lean | archive/MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/ApproxClockOccupation.lean | B16 |
| MatedCRT/Proofs/Sec5/StoppedActualSurplus.lean | archive/MatedCRT/Proofs/Sec5/StoppedActualSurplus.lean | B16 |
| MatedCRT/Proofs/Sec5/StoppedCompactCode.lean | archive/MatedCRT/Proofs/Sec5/StoppedCompactCode.lean | B16 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSRateAtDistance.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSRateAtDistance.lean | B16 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSUniformGeometry.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSUniformGeometry.lean | B16 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/RateFromAnnulus.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/RateFromAnnulus.lean | B16 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/WalkDiscrepancyBound.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/WalkDiscrepancyBound.lean | B16 |
| MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/ClockOccupationSubstitution.lean | archive/MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/ClockOccupationSubstitution.lean | B16 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/DiscrepancyBound.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/DiscrepancyBound.lean | B17 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSMesoscopicHit.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSMesoscopicHit.lean | B17 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/RateAtDistance.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/RateAtDistance.lean | B17 |
| MatedCRT/Proofs/Sec5/StoppedMarginValueVersions.lean | archive/MatedCRT/Proofs/Sec5/StoppedMarginValueVersions.lean | B17 |
| MatedCRT/Proofs/Sec1/EnvironmentScaling/PrestonPolishTransfer.lean | archive/MatedCRT/Proofs/Sec1/EnvironmentScaling/PrestonPolishTransfer.lean | B17 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/DiscreteExitExcursion.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/DiscreteExitExcursion.lean | B17 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSBoundaryCellHit.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSBoundaryCellHit.lean | B17 |
| MatedCRT/Proofs/Sec5/StoppedMarginContinuousDecoder.lean | archive/MatedCRT/Proofs/Sec5/StoppedMarginContinuousDecoder.lean | B17 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/BoundaryCellAnnulusGeometry.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/BoundaryCellAnnulusGeometry.lean | B17 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/FirstBoundaryExcursion.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/FirstBoundaryExcursion.lean | B17 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSDyadicBoundaryHit.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSDyadicBoundaryHit.lean | B17 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/AdmissibleAnnulusScales.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/AdmissibleAnnulusScales.lean | B17 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/FirstBoundaryEdge.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/FirstBoundaryEdge.lean | B17 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/RateTailReduction.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/RateTailReduction.lean | B17 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/RestartExcursionProbability.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/RestartExcursionProbability.lean | B17 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/DyadicAnnulusScales.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/DyadicAnnulusScales.lean | B17 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/EnteringEdgeAlternative.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/EnteringEdgeAlternative.lean | B17 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/ExcursionRestartReduction.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/ExcursionRestartReduction.lean | B17 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/RateDiscrepancy.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/RateDiscrepancy.lean | B17 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/RestartExcursionOrder.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/RestartExcursionOrder.lean | B17 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/RestartCellInterior.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/RestartCellInterior.lean | B17 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/RestartEnlargedDisk.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/RestartEnlargedDisk.lean | B17 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/PrehitInterior.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/PrehitInterior.lean | B17 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/RestartFiniteCircleHit.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/RestartFiniteCircleHit.lean | B17 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/ExcursionHitOrder.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/ExcursionHitOrder.lean | B17 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/FiniteCircleHit.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/FiniteCircleHit.lean | B17 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/EnlargedBoundaryExit.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/EnlargedBoundaryExit.lean | B17 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/EnteringEdgeExit.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/EnteringEdgeExit.lean | B17 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/ShiftInterpolation.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/ShiftInterpolation.lean | B17 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/EnteringEdge.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/EnteringEdge.lean | B17 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/RestartSphereOrder.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/RestartSphereOrder.lean | B17 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/ExcursionInterpolation.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/ExcursionInterpolation.lean | B17 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSBoundaryHit.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSBoundaryHit.lean | B17 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/RestartDependentEvent.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/RestartDependentEvent.lean | B17 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/BoundaryCellGeometry.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/BoundaryCellGeometry.lean | B17 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/BoundarySurvival.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/BoundarySurvival.lean | B17 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSSafeSurvival.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSSafeSurvival.lean | B17 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSAnnulusSurvival.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSAnnulusSurvival.lean | B17 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/SafeRadialWalk.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/SafeRadialWalk.lean | B17 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/AnnulusPolynomialBound.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/AnnulusPolynomialBound.lean | B17 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/AnnulusPowerDecay.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/AnnulusPowerDecay.lean | B18 |
| MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/MesoscopicCutoff.lean | archive/MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/MesoscopicCutoff.lean | B18 |
| MatedCRT/Audit/PlateauScalingResiduals.lean | archive/MatedCRT/Audit/PlateauScalingResiduals.lean | B19 |
| MatedCRT/Audit/Reductions.lean | archive/MatedCRT/Audit/Reductions.lean | B19 |
| MatedCRT/FirstPass/S2h.lean | archive/MatedCRT/FirstPass/S2h.lean | B19 |
| MatedCRT/FirstPass/S34d.lean | archive/MatedCRT/FirstPass/S34d.lean | B19 |
| MatedCRT/FirstPass/S7y.lean | archive/MatedCRT/FirstPass/S7y.lean | B19 |
| MatedCRT/FirstPass/S2x/BrownianNegativeDrift.lean | archive/MatedCRT/FirstPass/S2x/BrownianNegativeDrift.lean | B19 |
| MatedCRT/FirstPass/S3t/PathMeasurability.lean | archive/MatedCRT/FirstPass/S3t/PathMeasurability.lean | B19 |
| MatedCRT/FirstPass/S4S6c/B1GoodEnvSplitG68.lean | archive/MatedCRT/FirstPass/S4S6c/B1GoodEnvSplitG68.lean | B19 |
| MatedCRT/FirstPass/S4S6c/CoverMinorantMeasurable.lean | archive/MatedCRT/FirstPass/S4S6c/CoverMinorantMeasurable.lean | B19 |
| MatedCRT/FirstPass/S4S6c/LocalWindow68.lean | archive/MatedCRT/FirstPass/S4S6c/LocalWindow68.lean | B19 |
| MatedCRT/FirstPass/S5c/EntranceLevel.lean | archive/MatedCRT/FirstPass/S5c/EntranceLevel.lean | B19 |
| MatedCRT/FirstPass/S5c/MassEvent.lean | archive/MatedCRT/FirstPass/S5c/MassEvent.lean | B19 |
| MatedCRT/FirstPass/SLERef/Corrected.lean | archive/MatedCRT/FirstPass/SLERef/Corrected.lean | B19 |
| MatedCRT/Proofs/Sec1/EnvironmentScaling/BrownianContinuousVersion.lean | archive/MatedCRT/Proofs/Sec1/EnvironmentScaling/BrownianContinuousVersion.lean | B19 |
| MatedCRT/Proofs/Sec4/Prop42Closure/InsertionHarmonicRemainder.lean | archive/MatedCRT/Proofs/Sec4/Prop42Closure/InsertionHarmonicRemainder.lean | B19 |
| MatedCRT/Audit/LocalDirichletProjectionComponents.lean | archive/MatedCRT/Audit/LocalDirichletProjectionComponents.lean | B19 |
| MatedCRT/FirstPass/S2h/CertSuperBack.lean | archive/MatedCRT/FirstPass/S2h/CertSuperBack.lean | B19 |
| MatedCRT/FirstPass/S2h/LeastSuper.lean | archive/MatedCRT/FirstPass/S2h/LeastSuper.lean | B19 |
| MatedCRT/FirstPass/S4S6c/CoverMinorant.lean | archive/MatedCRT/FirstPass/S4S6c/CoverMinorant.lean | B19 |
| MatedCRT/FirstPass/S5c/EntranceAtoms.lean | archive/MatedCRT/FirstPass/S5c/EntranceAtoms.lean | B19 |
| MatedCRT/FirstPass/S7y/Final.lean | archive/MatedCRT/FirstPass/S7y/Final.lean | B19 |
| MatedCRT/Proofs/Sec1/EnvironmentScaling/FieldCircleScaling.lean | archive/MatedCRT/Proofs/Sec1/EnvironmentScaling/FieldCircleScaling.lean | B19 |
| MatedCRT/Proofs/Sec2/CellSizeHalf/Main.lean | archive/MatedCRT/Proofs/Sec2/CellSizeHalf/Main.lean | B19 |
| MatedCRT/Proofs/Sec2/VolumeGrowthHalf/Main.lean | archive/MatedCRT/Proofs/Sec2/VolumeGrowthHalf/Main.lean | B19 |
| MatedCRT/Proofs/Sec4/ConvergenceDivisible/Final.lean | archive/MatedCRT/Proofs/Sec4/ConvergenceDivisible/Final.lean | B19 |
| MatedCRT/Proofs/Sec6/ChanceOfBeingAbsorbed/Statement.lean | archive/MatedCRT/Proofs/Sec6/ChanceOfBeingAbsorbed/Statement.lean | B19 |
| MatedCRT/FirstPass/S2h/CertDense.lean | archive/MatedCRT/FirstPass/S2h/CertDense.lean | B19 |
| MatedCRT/FirstPass/S5c/NewMass.lean | archive/MatedCRT/FirstPass/S5c/NewMass.lean | B19 |
| MatedCRT/FirstPass/S5c/ScaleNull.lean | archive/MatedCRT/FirstPass/S5c/ScaleNull.lean | B19 |
| MatedCRT/FirstPass/S7y/OfSteps.lean | archive/MatedCRT/FirstPass/S7y/OfSteps.lean | B19 |
| MatedCRT/Proofs/Sec2/CellSizeHalf/CellModel.lean | archive/MatedCRT/Proofs/Sec2/CellSizeHalf/CellModel.lean | B19 |
| MatedCRT/Proofs/Sec2/VolumeGrowthHalf/Domination.lean | archive/MatedCRT/Proofs/Sec2/VolumeGrowthHalf/Domination.lean | B19 |
| MatedCRT/Proofs/Sec2/VolumeGrowthHalf/WholePlane.lean | archive/MatedCRT/Proofs/Sec2/VolumeGrowthHalf/WholePlane.lean | B19 |
| MatedCRT/Proofs/Sec4/ConvergenceDivisible/CorrectedInputs.lean | archive/MatedCRT/Proofs/Sec4/ConvergenceDivisible/CorrectedInputs.lean | B19 |
| MatedCRT/Proofs/Sec4/ConvergenceDivisible/OdometerSelection.lean | archive/MatedCRT/Proofs/Sec4/ConvergenceDivisible/OdometerSelection.lean | B19 |
| MatedCRT/Proofs/Sec4/Prop42Closure/InsertionDirichletProjection.lean | archive/MatedCRT/Proofs/Sec4/Prop42Closure/InsertionDirichletProjection.lean | B19 |
| MatedCRT/Proofs/Sec4/Prop42Closure/InsertionLocalCircleRecovery.lean | archive/MatedCRT/Proofs/Sec4/Prop42Closure/InsertionLocalCircleRecovery.lean | B19 |
| MatedCRT/Proofs/Sec4/Prop42Closure/InsertionScalingLawAssembly.lean | archive/MatedCRT/Proofs/Sec4/Prop42Closure/InsertionScalingLawAssembly.lean | B19 |
| MatedCRT/Proofs/Sec4/SubsequentialConvergence/PreparedSelection.lean | archive/MatedCRT/Proofs/Sec4/SubsequentialConvergence/PreparedSelection.lean | B19 |
| MatedCRT/FirstPass/S2h/CertBack.lean | archive/MatedCRT/FirstPass/S2h/CertBack.lean | B19 |
| MatedCRT/FirstPass/S2h/CertCode.lean | archive/MatedCRT/FirstPass/S2h/CertCode.lean | B20 |
| MatedCRT/FirstPass/S7y/Stmt.lean | archive/MatedCRT/FirstPass/S7y/Stmt.lean | B20 |
| MatedCRT/FirstPass/S7y/Vertex.lean | archive/MatedCRT/FirstPass/S7y/Vertex.lean | B20 |
| MatedCRT/Proofs/Sec4/ConvergenceDivisible/OdometerSelectionDetLimit.lean | archive/MatedCRT/Proofs/Sec4/ConvergenceDivisible/OdometerSelectionDetLimit.lean | B20 |
| MatedCRT/Proofs/Sec4/ConvergenceDivisible/OdometerSelectionDetStage.lean | archive/MatedCRT/Proofs/Sec4/ConvergenceDivisible/OdometerSelectionDetStage.lean | B20 |
| MatedCRT/Proofs/Sec4/ConvergenceDivisible/OdometerSelectionProxy.lean | archive/MatedCRT/Proofs/Sec4/ConvergenceDivisible/OdometerSelectionProxy.lean | B20 |
| MatedCRT/Proofs/Sec4/Prop42Closure/InsertionCoordinateExtensionProof.lean | archive/MatedCRT/Proofs/Sec4/Prop42Closure/InsertionCoordinateExtensionProof.lean | B20 |
| MatedCRT/FirstPass/S2h/CertForward2.lean | archive/MatedCRT/FirstPass/S2h/CertForward2.lean | B20 |
| MatedCRT/FirstPass/S7y/Core.lean | archive/MatedCRT/FirstPass/S7y/Core.lean | B20 |
| MatedCRT/Proofs/Sec4/ConvergenceDivisible/EnvSigmaDeviation.lean | archive/MatedCRT/Proofs/Sec4/ConvergenceDivisible/EnvSigmaDeviation.lean | B20 |
| MatedCRT/Proofs/Sec4/ConvergenceDivisible/OdometerSelectionHolder.lean | archive/MatedCRT/Proofs/Sec4/ConvergenceDivisible/OdometerSelectionHolder.lean | B20 |
| MatedCRT/Proofs/Sec4/ConvergenceDivisible/OdometerSelectionRecursion.lean | archive/MatedCRT/Proofs/Sec4/ConvergenceDivisible/OdometerSelectionRecursion.lean | B20 |
| MatedCRT/Proofs/Sec4/Prop42Closure/InsertionAffineMeasureTransport.lean | archive/MatedCRT/Proofs/Sec4/Prop42Closure/InsertionAffineMeasureTransport.lean | B20 |
| MatedCRT/Proofs/Sec4/Prop42Closure/InsertionNormalizedCircleLaw.lean | archive/MatedCRT/Proofs/Sec4/Prop42Closure/InsertionNormalizedCircleLaw.lean | B20 |
| MatedCRT/FirstPass/S2h/CertForward.lean | archive/MatedCRT/FirstPass/S2h/CertForward.lean | B20 |
| MatedCRT/Proofs/Sec4/ConvergenceDivisible/HolderNets.lean | archive/MatedCRT/Proofs/Sec4/ConvergenceDivisible/HolderNets.lean | B20 |
| MatedCRT/Proofs/Sec4/ConvergenceDivisible/OdometerSelectionMeasurable.lean | archive/MatedCRT/Proofs/Sec4/ConvergenceDivisible/OdometerSelectionMeasurable.lean | B20 |
| MatedCRT/Proofs/Sec4/Prop42Closure/InsertionAffineCircleLaw.lean | archive/MatedCRT/Proofs/Sec4/Prop42Closure/InsertionAffineCircleLaw.lean | B20 |
| MatedCRT/FirstPass/S2h/CertMoment.lean | archive/MatedCRT/FirstPass/S2h/CertMoment.lean | B20 |
| MatedCRT/Proofs/Sec4/Prop42Closure/InsertionDyadicDecoder.lean | archive/MatedCRT/Proofs/Sec4/Prop42Closure/InsertionDyadicDecoder.lean | B20 |
| MatedCRT/FirstPass/S2h/CertCharged.lean | archive/MatedCRT/FirstPass/S2h/CertCharged.lean | B20 |
| MatedCRT/FirstPass/S2h/CutoffUnion.lean | archive/MatedCRT/FirstPass/S2h/CutoffUnion.lean | B20 |
| MatedCRT/FirstPass/S2h/MeasurableIntegral.lean | archive/MatedCRT/FirstPass/S2h/MeasurableIntegral.lean | B20 |
| MatedCRT/FirstPass/S2h/CertSets.lean | archive/MatedCRT/FirstPass/S2h/CertSets.lean | B20 |
| MatedCRT/FirstPass/S2h/Cutoff.lean | archive/MatedCRT/FirstPass/S2h/Cutoff.lean | B20 |
| MatedCRT/FirstPass/S2h/CertRel.lean | archive/MatedCRT/FirstPass/S2h/CertRel.lean | B20 |
