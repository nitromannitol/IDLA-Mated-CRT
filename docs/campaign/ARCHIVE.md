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
