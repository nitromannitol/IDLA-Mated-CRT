# Status check of the Frozen and External Props against FROZEN-PROVENANCE.md

Canonical source: `docs/campaign/FROZEN-PROVENANCE.md`. This file records, for every `Prop` defined in `MatedCRT/FirstPass/Frozen/*.lean` (25 files) and `MatedCRT/External/*.lean` (2 files), the status word written in its docstring and the verdict of its provenance row.

Method. The docstring status of a Prop is the word of the first "Truth check" or "Truth-checked" phrase in its own docstring; failing that, a `TRUE`, `FALSE` or `UNRESOLVED` word followed by "as typed"; `PENDING TRUTH CHECK` gives `none`; a `Retired:` marker gives `RETIRED`; otherwise `none`. `UNRESOLVED` is read as `UNSURE`, as the provenance file does. A row is MATCH when the docstring status equals the provenance verdict (`none` also covers PENDING).

## Counts

| Rows | MATCH | MISMATCH | no provenance row |
|---:|---:|---:|---:|
| 82 | 82 | 0 | 0 |

Scope: 80 Props in `Frozen/` and `External/`, plus two provenance rows (81, 82) whose Props are defined in `MatedCRT/FirstPass/S3i/` and are listed for completeness.

## Mismatches and wording changes

* Verdict mismatches: none.
* External Props (`QuantumConeScalingInput`, `SLEScaleInvarianceInput`, `SLEReparametrizationInput`, `SLEIndepMonoInput`, `MepsScalingInput`, `DegreeBoundInput`): docstring status `none`, provenance `none`, all MATCH. No External file was edited.
* Props with no provenance row: none.
* Wording fixed by this check (docstring only; canonical status word plus pointer to the provenance file): FrozenDiscreteHolderContinuityCorrected (docstring said UNRESOLVED); FrozenTruncatedQuenchedLawsFixedTime (docstring said UNRESOLVED); FrozenBerestyckiGwynneConeBallMass (docstring said lowercase pending).

## Table

| # | Prop | file:line | docstring status | provenance verdict | MATCH/MISMATCH |
|---:|---|---|---|---|---|
| 1 | FrozenAdjacentCellsMeetAe | FirstPass/Frozen/S1S2S8SA.lean:16 | TRUE | TRUE | MATCH |
| 2 | FrozenConeHarmonicBallFunctional | FirstPass/Frozen/S1S2S8SA.lean:23 | RETIRED | RETIRED | MATCH |
| 3 | FrozenConeRadialDivergence | FirstPass/Frozen/S1c.lean:18 | FALSE | FALSE | MATCH |
| 4 | FrozenUniversalMeasurabilityOfAnalytic | FirstPass/Frozen/S1c.lean:25 | TRUE | TRUE | MATCH |
| 5 | FrozenLQGTestIntegralMeasurable | FirstPass/Frozen/S1c.lean:31 | TRUE | TRUE | MATCH |
| 6 | FrozenDiskGreenNonnegCont | FirstPass/Frozen/S1c.lean:38 | TRUE | TRUE | MATCH |
| 7 | FrozenConeRadialDivergenceCorrected | FirstPass/Frozen/S1cDivergence.lean:17 | TRUE | TRUE | MATCH |
| 8 | ConeEnvironmentScalingUnderSLE | FirstPass/Frozen/S1d.lean:15 | TRUE | TRUE | MATCH |
| 9 | FrozenWholePlaneLogLQGExistence | FirstPass/Frozen/S2b.lean:16 | TRUE | TRUE | MATCH |
| 10 | FrozenConeRestriction | FirstPass/Frozen/S2b.lean:20 | TRUE | TRUE | MATCH |
| 11 | FrozenConeHarmonicBallLocality | FirstPass/Frozen/S2b.lean:24 | TRUE | TRUE | MATCH |
| 12 | FrozenConeHalfBallFamilyMeasurable | FirstPass/Frozen/S2b.lean:29 | RETIRED | RETIRED | MATCH |
| 13 | FrozenSuperharmonicMinimumPrinciple | FirstPass/Frozen/S2g.lean:19 | TRUE | TRUE | MATCH |
| 14 | FrozenGreenDiscPole | FirstPass/Frozen/S2g.lean:27 | TRUE | TRUE | MATCH |
| 15 | FrozenGreenBallCentre | FirstPass/Frozen/S2g.lean:33 | TRUE | TRUE | MATCH |
| 16 | FrozenHBInitialConfinement | FirstPass/Frozen/S2g.lean:40 | TRUE | TRUE | MATCH |
| 17 | FrozenConeLogLocalCodeLawStd | FirstPass/Frozen/S2g.lean:48 | TRUE | TRUE | MATCH |
| 18 | FrozenConeLogLocalCodeLaw | FirstPass/Frozen/S2h.lean:16 | TRUE | TRUE | MATCH |
| 19 | LeastSupersolutionMemOfVolumeGrowthStmt | FirstPass/Frozen/S2h.lean:27 | TRUE | TRUE | MATCH |
| 20 | FrozenWholePlaneLQGScaling | FirstPass/Frozen/S2h.lean:34 | TRUE | TRUE | MATCH |
| 21 | ConeCircleLawUniqueStep | FirstPass/Frozen/S2i.lean:16 | TRUE | TRUE | MATCH |
| 22 | ConeReferenceExistsStep | FirstPass/Frozen/S2i.lean:27 | TRUE | TRUE | MATCH |
| 23 | FrozenLusinCompactContinuity | FirstPass/Frozen/S2k.lean:14 | TRUE | TRUE | MATCH |
| 24 | FrozenInsertionCoordinateRule | FirstPass/Frozen/S2k.lean:23 | TRUE | TRUE | MATCH |
| 25 | FrozenLQGMeasureExistenceInsertion | FirstPass/Frozen/S2m.lean:14 | TRUE | TRUE | MATCH |
| 26 | FrozenDiscreteHolderContinuityCorrected | FirstPass/Frozen/S3S4.lean:16 | UNSURE (docstring said UNRESOLVED) | UNSURE | MATCH |
| 27 | FrozenBrownianOutwardExcursionAtExit | FirstPass/Frozen/S3S4.lean:22 | TRUE | TRUE | MATCH |
| 28 | FrozenConeEnvironmentScaling | FirstPass/Frozen/S3S4.lean:27 | FALSE | FALSE | MATCH |
| 29 | FrozenLBMGreenOccupation | FirstPass/Frozen/S3S4b.lean:19 | RETIRED | RETIRED | MATCH |
| 30 | FrozenTruncatedDetFixedTime | FirstPass/Frozen/S3S4b.lean:23 | RETIRED | RETIRED | MATCH |
| 31 | FrozenFiniteDomainDirichletRepresentation | FirstPass/Frozen/S3S4b.lean:28 | TRUE | TRUE | MATCH |
| 32 | FrozenLBMGreenOccupationRescaled | FirstPass/Frozen/S3S4b.lean:51 | none | none | MATCH |
| 33 | FrozenTruncatedQuenchedLawsFixedTime | FirstPass/Frozen/S3S4b.lean:65 | UNSURE (docstring said UNRESOLVED) | UNSURE | MATCH |
| 34 | BG20Prop51 | FirstPass/Frozen/S3c.lean:20 | TRUE | TRUE | MATCH |
| 35 | BG20Prop51Ref | FirstPass/Frozen/S3c.lean:32 | FALSE | FALSE | MATCH |
| 36 | FPPairingLawIG4 | FirstPass/Frozen/S4S5b.lean:18 | TRUE | TRUE | MATCH |
| 37 | FPWholePlaneLQGModel | FirstPass/Frozen/S4S5b.lean:29 | TRUE | TRUE | MATCH |
| 38 | FPConeWholePlaneFieldLaw | FirstPass/Frozen/S4S5b.lean:33 | TRUE | TRUE | MATCH |
| 39 | FPLQGMeasureLocality | FirstPass/Frozen/S4S5b.lean:38 | TRUE | TRUE | MATCH |
| 40 | FrozenConeScalingLaw | FirstPass/Frozen/S4S6c.lean:18 | none | none | MATCH |
| 41 | FrozenLQGMeasureFieldMeasurable | FirstPass/Frozen/S4S6c.lean:30 | none | none | MATCH |
| 42 | FrozenProperEta | FirstPass/Frozen/S4S6c.lean:36 | RETIRED | RETIRED | MATCH |
| 43 | FrozenPunctureConnected | FirstPass/Frozen/S4d.lean:16 | TRUE | TRUE | MATCH |
| 44 | ConeRescaledMeasureIsConeFieldInput | FirstPass/Frozen/S4d2.lean:16 | TRUE | TRUE | MATCH |
| 45 | FrozenBG20GreenCrudeCanonical | FirstPass/Frozen/S5BG56.lean:18 | TRUE | TRUE | MATCH |
| 46 | FrozenBerestyckiGwynneConeBallMass | FirstPass/Frozen/S5Cited.lean:28 | PENDING TRUTH CHECK (docstring said lowercase pending) | none | MATCH |
| 47 | FrozenGreenFunctionCrudeBound | FirstPass/Frozen/S5Cited.lean:33 | TRUE | TRUE | MATCH |
| 48 | FrozenLQGVolumeGrowthAllScales | FirstPass/Frozen/S5Cited.lean:39 | TRUE | TRUE | MATCH |
| 49 | FrozenVeryGoodAnnulusHarnackType | FirstPass/Frozen/S5Cited.lean:44 | TRUE | TRUE | MATCH |
| 50 | FrozenTypicalPointManyGoodScales | FirstPass/Frozen/S5Cited.lean:49 | TRUE | TRUE | MATCH |
| 51 | FrozenClusterBoundaryMeasureZero | FirstPass/Frozen/S5Cited.lean:54 | TRUE | TRUE | MATCH |
| 52 | FrozenExistenceHarmonicBalls | FirstPass/Frozen/S5Cited.lean:59 | TRUE | TRUE | MATCH |
| 53 | FrozenUniquenessHarmonicBalls | FirstPass/Frozen/S5Cited.lean:64 | TRUE | TRUE | MATCH |
| 54 | FrozenHarmonicBallLocalSet | FirstPass/Frozen/S5Cited.lean:69 | TRUE | TRUE | MATCH |
| 55 | FrozenClusterStrongCompatibility | FirstPass/Frozen/S5Cited.lean:74 | TRUE | TRUE | MATCH |
| 56 | FPWholePlaneLQGExistence | FirstPass/Frozen/S5S6S7.lean:13 | none | none | MATCH |
| 57 | FPConeWholePlaneWeylComparison | FirstPass/Frozen/S5S6S7.lean:16 | RETIRED | RETIRED | MATCH |
| 58 | FPWholePlaneLQGCoordinateChange | FirstPass/Frozen/S5S6S7.lean:19 | none | none | MATCH |
| 59 | FPWholePlaneUpperVolumeTail | FirstPass/Frozen/S5S6S7.lean:23 | TRUE | TRUE | MATCH |
| 60 | FPConeMeanZeroRestriction | FirstPass/Frozen/S5S6S7.lean:28 | TRUE | TRUE | MATCH |
| 61 | FPFirstHitVisits | FirstPass/Frozen/S5c.lean:13 | TRUE | TRUE | MATCH |
| 62 | FPGreenBallContinuousOffPole | FirstPass/Frozen/S5c.lean:19 | RETIRED | RETIRED | MATCH |
| 63 | FPGreenBallPoleLimit | FirstPass/Frozen/S5c.lean:25 | RETIRED | RETIRED | MATCH |
| 64 | FPStrongMinimumPrinciple | FirstPass/Frozen/S5c.lean:33 | TRUE | TRUE | MATCH |
| 65 | graphSetDisconnects | FirstPass/Frozen/S5cSec9.lean:18 | none | none | MATCH |
| 66 | walkSetDisconnectsBeforeHit | FirstPass/Frozen/S5cSec9.lean:24 | none | none | MATCH |
| 67 | FPLBMExitTimePositiveFinite | FirstPass/Frozen/S5cSec9.lean:28 | none | none | MATCH |
| 68 | FPEmbeddedWalkExitTail | FirstPass/Frozen/S5cSec9.lean:34 | none | none | MATCH |
| 69 | FPLogPotentialSmall | FirstPass/Frozen/S5cSec9.lean:42 | none | none | MATCH |
| 70 | FPFiniteAnnulusDisconnection | FirstPass/Frozen/S5cSec9.lean:49 | none | none | MATCH |
| 71 | FPSimilarityTransfer | FirstPass/Frozen/S5cSimilarity.lean:24 | FALSE | FALSE | MATCH |
| 72 | FrozenLeastSupersolutionMemCone | FirstPass/Frozen/S5k.lean:15 | TRUE | TRUE | MATCH |
| 73 | FrozenFiniteMeasureDiskStandardBorel | FirstPass/Frozen/S5k.lean:23 | TRUE | TRUE | MATCH |
| 74 | SLEReferenceExistsInput | FirstPass/Frozen/SLERef.lean:22 | UNSURE | UNSURE | MATCH |
| 75 | QuantumConeScalingInput | External/QuantumCone.lean:16 | none | none | MATCH |
| 76 | SLEScaleInvarianceInput | External/SLE.lean:24 | none | none | MATCH |
| 77 | SLEReparametrizationInput | External/SLE.lean:33 | none | none | MATCH |
| 78 | SLEIndepMonoInput | External/SLE.lean:43 | none | none | MATCH |
| 79 | MepsScalingInput | External/SLE.lean:50 | none | none | MATCH |
| 80 | DegreeBoundInput | External/SLE.lean:57 | none | none | MATCH |
| 81 | FrozenOneSidedBoundaryContinuity | FirstPass/S3i/Frozen.lean:44 (outside Frozen/) | FALSE | FALSE | MATCH |
| 82 | FrozenOneSidedBoundaryContinuityFloored | FirstPass/S3i/FrozenFloored.lean:34 (outside Frozen/) | PENDING TRUTH CHECK | none | MATCH |
